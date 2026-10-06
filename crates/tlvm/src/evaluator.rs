//! 実行（設計書 §7、§8.4、§18.3）。
//!
//! 評価そのものは Verus で検証した `tlvm_verified::pipeline::run_checked` が行う。
//! ここにあるのは検証されていない接着部分だけである：
//! - 型検査済みの表面 AST を、名前を添字に置き換えた中間表現（`EExpr`）に下ろす
//! - 復号済みの入力値を検証済み評価器の値表現に移す
//! - 結果を `RunResult` の envelope に写す
//!
//! 検証済み評価器は、プログラムが整形式であることと入力値の型を自分で検査してから実行し、
//! 返した値が spec の評価の唯一の結果であること、出力文字列がその値の正準 JSON であることを
//! 証明済みである。

use crate::checker::TypedProgram;
use crate::profiles::{ExecutionProfile, HostPolicy};
use crate::syntax::*;
use crate::values::{TypedValue, Value, V};
use num_bigint::BigInt;
use std::collections::HashMap;
use std::rc::Rc;
use tlvm_verified::bigint::Int;
use tlvm_verified::eval::{Limits, Resource, Stop};
use tlvm_verified::ir::{EExpr, EFunc, EProg};
use tlvm_verified::pipeline::{run_checked_json, Output};
use tlvm_verified::spec::{Builtin, Ty as STy};
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

// ---------------------------------------------------------------- 中間表現への変換

fn lower_ty(t: &Ty) -> STy {
    match t.tag() {
        TyTag::Int => STy::Int,
        TyTag::Bool => STy::Bool,
        TyTag::Unit => STy::Unit,
        TyTag::List => STy::List(Box::new(lower_ty(&t.arg(0)))),
        TyTag::Option => STy::Option(Box::new(lower_ty(&t.arg(0)))),
        TyTag::Pair => STy::Pair(Box::new(lower_ty(&t.arg(0))), Box::new(lower_ty(&t.arg(1)))),
        TyTag::Error => unreachable!("accepted program has no ErrorType"),
    }
}

fn builtin(name: &str) -> Builtin {
    match name {
        "add" => Builtin::Add,
        "sub" => Builtin::Sub,
        "mul" => Builtin::Mul,
        "neg" => Builtin::Neg,
        "lt" => Builtin::Lt,
        "le" => Builtin::Le,
        "eq" => Builtin::Eq,
        "mod" => Builtin::Mod,
        "fst" => Builtin::Fst,
        "snd" => Builtin::Snd,
        "cons" => Builtin::Cons,
        "concat" => Builtin::Concat,
        "reverse" => Builtin::Reverse,
        "length" => Builtin::Length,
        _ => unreachable!("unknown builtin {name}"),
    }
}

/// 名前を添字に置き換える。変数名は全体で一つの表に登録するので、同じ名前は同じ添字になる。
struct Lower<'a> {
    funcs: HashMap<&'a str, usize>,
    vars: HashMap<&'a str, usize>,
}

impl<'a> Lower<'a> {
    fn var(&mut self, name: &'a str) -> usize {
        let n = self.vars.len();
        *self.vars.entry(name).or_insert(n)
    }

    fn exprs(&mut self, es: &'a [Expr]) -> Vec<EExpr> {
        es.iter().map(|e| self.expr(e)).collect()
    }

    fn expr(&mut self, e: &'a Expr) -> EExpr {
        let b = |x: EExpr| Box::new(x);
        match &e.kind {
            ExprKind::Int(n) => EExpr::Int(Int { n: n.clone() }),
            ExprKind::Bool(v) => EExpr::Bool(*v),
            ExprKind::Unit => EExpr::Unit,
            ExprKind::Var(n) => EExpr::Var(self.var(n)),
            ExprKind::List { element_type, items } => EExpr::List(lower_ty(&Ty::of(element_type)), self.exprs(items)),
            ExprKind::Some(x) => EExpr::Some(b(self.expr(x))),
            ExprKind::None(t) => EExpr::None(lower_ty(&Ty::of(t))),
            ExprKind::Pair(x, y) => EExpr::Pair(b(self.expr(x)), b(self.expr(y))),
            ExprKind::Call { callee, args, builtin: true, .. } => EExpr::Builtin(builtin(callee), self.exprs(args)),
            ExprKind::Call { callee, args, .. } => EExpr::Call(self.funcs[callee.as_str()], self.exprs(args)),
            ExprKind::Let { name, value, body, .. } => {
                let x = self.var(name);
                EExpr::Let(x, b(self.expr(value)), b(self.expr(body)))
            }
            ExprKind::If(c, t, f) => EExpr::If(b(self.expr(c)), b(self.expr(t)), b(self.expr(f))),
            ExprKind::Fold { list, init, acc, item, body, .. } => {
                let (a, i) = (self.var(acc), self.var(item));
                EExpr::Fold(b(self.expr(list)), b(self.expr(init)), a, i, b(self.expr(body)))
            }
        }
    }
}

pub fn lower(prog: &TypedProgram) -> EProg {
    let fns: Vec<&FnDecl> = prog.program.functions().collect();
    let mut l = Lower { funcs: fns.iter().enumerate().map(|(i, f)| (f.name.as_str(), i)).collect(), vars: HashMap::new() };
    let funcs = fns
        .iter()
        .map(|f| EFunc {
            params: f.params.iter().map(|p| (l.var(&p.name), lower_ty(&Ty::of(&p.ty)))).collect(),
            ret: lower_ty(&Ty::of(&f.return_type)),
            body: l.expr(&f.body),
        })
        .collect();
    EProg {
        funcs,
        rank: fns.iter().map(|f| prog.rank.get(&f.name).copied().unwrap_or(usize::MAX)).collect(),
        entry: l.funcs[prog.entry.as_str()],
    }
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
    let eprog = lower(prog);
    let lim = Limits {
        steps: p.steps.min(u64::MAX - 1),
        integer_bits: p.integer_bits,
        allocated_nodes: p.allocated_nodes.min(u64::MAX - 1),
        max_depth: (host.max_eval_depth as u64).min(u64::MAX - 1),
    };
    let iv = to_ev(&input.value);
    let r = match run_checked_json(&eprog, iv.clone(), lim) {
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
