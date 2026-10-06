//! 実行（設計書 §7、§8.4、§18.3）。
//!
//! 入力の復号と評価は Verus で検証した `tlvm_verified::pipeline::run_input_json` が行う。
//! 実行する中間表現は compile 時に検証済みの lexer・parser・名前解決・型検査が作ったもの
//! （`TypedProgram::verified`）で、入力値は入力 JSON の文字列を検証済みの復号器で読み直したもの。
//! ここにあるのは検証されていない接着部分（結果を `RunResult` の envelope に写す）だけである。
//!
//! 検証済み部品は、プログラムが整形式であることを自分で検査し、入力を spec の `input_val` どおりに
//! 復号してから実行する。返した値が spec の評価の唯一の結果であること、出力文字列がその値の
//! 正準 JSON であること、Fault（spec の行き詰まり）で終わらないことを証明済みである。

use crate::checker::TypedProgram;
use crate::profiles::{ExecutionProfile, HostPolicy};
use crate::values::{TypedValue, Value, V};
use num_bigint::BigInt;
use tlvm_verified::eval::{Limits, Resource, Stop};
use tlvm_verified::pipeline::{run_input_json, InputRun};

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
    if input.text.len() >= 0x1000_0000 {
        return Ok(RunResult::InternalFault("input-too-long-for-verified-decoder".into()));
    }
    let r = match run_input_json(eprog, &input.text, input.json_depth, lim) {
        InputRun::NotWellFormed => RunResult::InternalFault("verified-check-rejected-program".into()),
        InputRun::InputRejected => RunResult::InternalFault("verified-decoder-rejected-input".into()),
        InputRun::Ran(Err(Stop::Exhausted(kind, observed, limit)), _, _) => {
            let kind = match kind {
                Resource::Steps => "Steps",
                Resource::IntegerBits => "IntegerBits",
                Resource::AllocatedNodes => "AllocatedNodes",
            };
            RunResult::ResourceExhausted { kind, observed, limit }
        }
        InputRun::Ran(Err(Stop::HostDepth), _, _) => RunResult::HostAborted("eval-depth".into()),
        // 型付きプログラムでは起きないことを証明済み（pipeline::run_input_json）
        InputRun::Ran(Err(Stop::Fault), _, _) => RunResult::InternalFault("stuck".into()),
        InputRun::Ran(Ok(out), steps, alloc) => {
            if out.len() as u64 > p.output_bytes {
                RunResult::ResourceExhausted { kind: "OutputBytes", observed: p.output_bytes + 1, limit: p.output_bytes }
            } else {
                RunResult::Completed { output: out, steps, allocated_nodes: alloc }
            }
        }
    };
    Ok(r)
}
