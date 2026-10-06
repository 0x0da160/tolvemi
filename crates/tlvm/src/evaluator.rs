//! 実行（設計書 §7、§8.4、§18.3）。
//!
//! 評価そのものは Verus で検証した `tlvm_verified::pipeline::run_checked_json` が行う。
//! 実行する中間表現は compile 時に検証済みの lexer・parser・名前解決・型検査が作ったもの
//! （`TypedProgram::verified`）。ここにあるのは検証されていない接着部分だけである：
//! - 復号済みの入力値を検証済み評価器の値表現に移す
//! - 結果を `RunResult` の envelope に写す
//!
//! 検証済み評価器は、プログラムが整形式であることと入力値の型を自分で検査してから実行し、
//! 返した値が spec の評価の唯一の結果であること、出力文字列がその値の正準 JSON であることを
//! 証明済みである。

use crate::checker::TypedProgram;
use crate::profiles::{ExecutionProfile, HostPolicy};
use crate::values::{TypedValue, Value, V};
use num_bigint::BigInt;
use std::rc::Rc;
use tlvm_verified::bigint::Int;
use tlvm_verified::eval::{Limits, Resource, Stop};
use tlvm_verified::pipeline::{run_checked_json, Output};
use tlvm_verified::value::Value as EV;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum RunResult {
    Completed { output: String, steps: u64, allocated_nodes: u64 },
    ResourceExhausted { kind: &'static str, observed: u64, limit: u64 },
    HostAborted(String),
    InternalFault(String),
}

fn bits(n: &BigInt) -> u64 {
    n.magnitude().bits()
}

// ---------------------------------------------------------------- 値の変換

/// 入力値を検証済み評価器の値表現へ移す（深い値でも再帰しない）。
fn to_ev(v: &V) -> Rc<EV> {
    enum Job<'a> {
        Visit(&'a V),
        Some,
        Pair,
        List(usize),
    }
    let mut jobs = vec![Job::Visit(v)];
    let mut out: Vec<Rc<EV>> = vec![];
    while let Some(j) = jobs.pop() {
        match j {
            Job::Visit(x) => match &**x {
                Value::Int(n) => out.push(Rc::new(EV::Int(Int { n: n.clone() }))),
                Value::Bool(b) => out.push(Rc::new(EV::Bool(*b))),
                Value::Unit => out.push(Rc::new(EV::Unit)),
                Value::None => out.push(Rc::new(EV::None)),
                Value::Some(a) => {
                    jobs.push(Job::Some);
                    jobs.push(Job::Visit(a));
                }
                Value::Pair(a, b) => {
                    jobs.push(Job::Pair);
                    jobs.push(Job::Visit(b));
                    jobs.push(Job::Visit(a));
                }
                Value::Nil | Value::Cons(..) => {
                    let mut cells = vec![];
                    let mut cur = x;
                    while let Value::Cons(h, t) = &**cur {
                        cells.push(h);
                        cur = t;
                    }
                    jobs.push(Job::List(cells.len()));
                    for h in cells.into_iter().rev() {
                        jobs.push(Job::Visit(h));
                    }
                }
            },
            Job::Some => {
                let a = out.pop().unwrap();
                out.push(Rc::new(EV::Some(a)));
            }
            Job::Pair => {
                let b = out.pop().unwrap();
                let a = out.pop().unwrap();
                out.push(Rc::new(EV::Pair(a, b)));
            }
            Job::List(n) => {
                let items = out.split_off(out.len() - n);
                let mut l = Rc::new(EV::Nil);
                for h in items.into_iter().rev() {
                    l = Rc::new(EV::Cons(h, l));
                }
                out.push(l);
            }
        }
    }
    out.pop().unwrap()
}

/// 深い cons 列の解放で再帰しないよう、所有している尾を順に外して解放する。
fn release(v: Rc<EV>) {
    let mut stack = vec![v];
    while let Some(rc) = stack.pop() {
        if let Ok(x) = Rc::try_unwrap(rc) {
            match x {
                EV::Some(a) => stack.push(a),
                EV::Pair(a, b) | EV::Cons(a, b) => {
                    stack.push(a);
                    stack.push(b);
                }
                _ => {}
            }
        }
    }
}

fn input_bits_over(v: &V, limit: u64) -> Option<u64> {
    let mut stack = vec![v.clone()];
    while let Some(x) = stack.pop() {
        match &*x {
            Value::Int(n) => {
                if bits(n) > limit {
                    return Some(bits(n));
                }
            }
            Value::Some(a) => stack.push(a.clone()),
            Value::Pair(a, b) | Value::Cons(a, b) => {
                stack.push(b.clone());
                stack.push(a.clone());
            }
            _ => {}
        }
    }
    None
}

/// run(typed_program, decoded_input, execution_profile, host_policy)。
/// 入力型の不一致は API misuse なので InternalFault ではなく Err で返す。
pub fn run(prog: &TypedProgram, input: &TypedValue, p: &ExecutionProfile, host: &HostPolicy) -> Result<RunResult, String> {
    if input.ty != prog.input_type {
        return Err(format!("入力型 {} が entry の入力型 {} と一致しない", input.ty, prog.input_type));
    }
    if let Some(b) = input_bits_over(&input.value, p.integer_bits) {
        return Ok(RunResult::ResourceExhausted { kind: "IntegerBits", observed: b, limit: p.integer_bits });
    }
    let Some(vp) = prog.verified.as_ref() else {
        return Ok(RunResult::InternalFault("no-verified-program".into()));
    };
    let eprog = &vp.0;
    let lim = Limits {
        steps: p.steps.min(u64::MAX - 1),
        integer_bits: p.integer_bits,
        allocated_nodes: p.allocated_nodes.min(u64::MAX - 1),
        max_depth: (host.max_eval_depth as u64).min(u64::MAX - 1),
    };
    let iv = to_ev(&input.value);
    let r = match run_checked_json(eprog, iv.clone(), lim) {
        Output::NotWellFormed => RunResult::InternalFault("verified-check-rejected-program".into()),
        Output::InputTypeMismatch => RunResult::InternalFault("verified-check-rejected-input".into()),
        Output::Ran(Err(Stop::Exhausted(kind, observed, limit)), _, _) => {
            let kind = match kind {
                Resource::Steps => "Steps",
                Resource::IntegerBits => "IntegerBits",
                Resource::AllocatedNodes => "AllocatedNodes",
            };
            RunResult::ResourceExhausted { kind, observed, limit }
        }
        Output::Ran(Err(Stop::HostDepth), _, _) => RunResult::HostAborted("eval-depth".into()),
        Output::Ran(Err(Stop::Fault), _, _) => RunResult::InternalFault("stuck".into()),
        Output::Ran(Ok(out), steps, alloc) => {
            if out.len() as u64 > p.output_bytes {
                RunResult::ResourceExhausted { kind: "OutputBytes", observed: p.output_bytes + 1, limit: p.output_bytes }
            } else {
                RunResult::Completed { output: out, steps, allocated_nodes: alloc }
            }
        }
    };
    release(iv);
    Ok(r)
}
