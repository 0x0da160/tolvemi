//! 参照評価器（設計書 §7、§8.4、§18.3）。
//!
//! 左から右の call-by-value。execution-v1 の参照 step・AllocatedNodeCount・整数 bit 長を
//! 規範どおりに計数し、上限超過は ResourceExhausted として返す。

use crate::checker::TypedProgram;
use crate::profiles::{ExecutionProfile, HostPolicy};
use crate::syntax::*;
use crate::values::{encode_value, TypedValue, Value, V};
use num_bigint::BigInt;
use num_integer::Integer;
use num_traits::Signed;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum RunResult {
    Completed { output: String, steps: u64, allocated_nodes: u64 },
    ResourceExhausted { kind: &'static str, observed: u64, limit: u64 },
    HostAborted(String),
    InternalFault(String),
}

enum Stop {
    Exhausted(&'static str, u64, u64),
    Host(String),
}

type R<T> = Result<T, Stop>;

fn bits(n: &BigInt) -> u64 {
    n.magnitude().bits()
}

struct Machine<'a> {
    prog: &'a TypedProgram,
    p: &'a ExecutionProfile,
    host: &'a HostPolicy,
    steps: u64,
    alloc: u64,
    depth: usize,
    env: Vec<(&'a str, V)>,
}

impl<'a> Machine<'a> {
    fn step(&mut self) -> R<()> {
        if self.steps + 1 > self.p.steps {
            return Err(Stop::Exhausted("Steps", self.steps + 1, self.p.steps));
        }
        self.steps += 1;
        Ok(())
    }

    /// 新規整数／cons／pair／some node の確保（step → bit → 割当数の順に判定）。
    fn allocate(&mut self, int: Option<&BigInt>) -> R<()> {
        if self.steps + 1 > self.p.steps {
            return Err(Stop::Exhausted("Steps", self.steps + 1, self.p.steps));
        }
        if let Some(n) = int {
            let b = bits(n);
            if b > self.p.integer_bits {
                return Err(Stop::Exhausted("IntegerBits", b, self.p.integer_bits));
            }
        }
        if self.alloc + 1 > self.p.allocated_nodes {
            return Err(Stop::Exhausted("AllocatedNodes", self.alloc + 1, self.p.allocated_nodes));
        }
        self.steps += 1;
        self.alloc += 1;
        Ok(())
    }

    fn int(&mut self, n: BigInt) -> R<V> {
        self.allocate(Some(&n))?;
        Ok(V::new(Value::Int(n)))
    }

    fn lookup(&self, name: &str) -> V {
        self.env.iter().rev().find(|(n, _)| *n == name).map(|(_, v)| v.clone()).expect("bound variable")
    }

    /// 関数本体を新しい環境で評価する（入場 step は呼出し側で数える）。
    fn call_body(&mut self, f: &'a FnDecl, args: Vec<V>) -> R<V> {
        let saved = std::mem::take(&mut self.env);
        self.env = f.params.iter().map(|p| p.name.as_str()).zip(args).collect();
        let r = self.eval(&f.body);
        self.env = saved;
        r
    }

    fn eval(&mut self, e: &'a Expr) -> R<V> {
        self.step()?; // 式 node の評価開始
        self.depth += 1;
        if self.depth > self.host.max_eval_depth {
            return Err(Stop::Host("eval-depth".into()));
        }
        let r = self.eval_inner(e);
        self.depth -= 1;
        r
    }

    fn eval_inner(&mut self, e: &'a Expr) -> R<V> {
        match &e.kind {
            ExprKind::Var(n) => Ok(self.lookup(n)),
            ExprKind::Int(n) => self.int(n.clone()),
            ExprKind::Bool(b) => Ok(V::new(Value::Bool(*b))),
            ExprKind::Unit => Ok(V::new(Value::Unit)),
            ExprKind::None(_) => Ok(V::new(Value::None)),
            ExprKind::Call { callee, args, builtin, .. } => {
                let mut vs = Vec::with_capacity(args.len());
                for a in args {
                    vs.push(self.eval(a)?);
                }
                self.step()?; // 組込みの適用開始、またはユーザー関数本体への入場
                if *builtin {
                    self.builtin(callee, vs)
                } else {
                    let f = self.prog.function(callee);
                    self.call_body(f, vs)
                }
            }
            ExprKind::Let { name, value, body, .. } => {
                let v = self.eval(value)?;
                self.env.push((name, v));
                let r = self.eval(body);
                self.env.pop();
                r
            }
            ExprKind::If(c, t, f) => {
                let cv = self.eval(c)?;
                let b = matches!(*cv, Value::Bool(true));
                self.eval(if b { t } else { f })
            }
            ExprKind::Fold { list, init, acc, item, body, .. } => {
                let mut cur = self.eval(list)?;
                let mut accv = self.eval(init)?;
                loop {
                    self.step()?; // spine cursor の読取り
                    let (h, t) = match &*cur {
                        Value::Cons(h, t) => (h.clone(), t.clone()),
                        _ => return Ok(accv),
                    };
                    self.env.push((acc, accv));
                    self.env.push((item, h));
                    let r = self.eval(body);
                    self.env.pop();
                    self.env.pop();
                    accv = r?;
                    cur = t;
                }
            }
            ExprKind::List { items, .. } => {
                let mut refs = Vec::with_capacity(items.len());
                for i in items {
                    refs.push(self.eval(i)?);
                    self.step()?; // 一時要素参照の push
                }
                let mut out = V::new(Value::Nil);
                while let Some(v) = refs.pop() {
                    self.step()?; // pop
                    self.allocate(None)?;
                    out = V::new(Value::Cons(v, out));
                }
                Ok(out)
            }
            ExprKind::Some(v) => {
                let x = self.eval(v)?;
                self.allocate(None)?;
                Ok(V::new(Value::Some(x)))
            }
            ExprKind::Pair(a, b) => {
                let x = self.eval(a)?;
                let y = self.eval(b)?;
                self.allocate(None)?;
                Ok(V::new(Value::Pair(x, y)))
            }
        }
    }

    fn builtin(&mut self, name: &str, a: Vec<V>) -> R<V> {
        let int = |v: &V| match &**v {
            Value::Int(n) => n.clone(),
            _ => unreachable!("typed program"),
        };
        match name {
            "add" => self.int(int(&a[0]) + int(&a[1])),
            "sub" => self.int(int(&a[0]) - int(&a[1])),
            "mul" => self.int(int(&a[0]) * int(&a[1])),
            "neg" => self.int(-int(&a[0])),
            "lt" => Ok(V::new(Value::Bool(int(&a[0]) < int(&a[1])))),
            "le" => Ok(V::new(Value::Bool(int(&a[0]) <= int(&a[1])))),
            "eq" => Ok(V::new(Value::Bool(self.equal(&a[0], &a[1])?))),
            "fst" | "snd" => match &*a[0] {
                Value::Pair(l, r) => Ok(if name == "fst" { l.clone() } else { r.clone() }),
                _ => unreachable!("typed program"),
            },
            "mod" => {
                let (x, y) = (int(&a[0]), int(&a[1]));
                if !y.is_positive() {
                    return Ok(V::new(Value::None));
                }
                let r = self.int(x.mod_floor(&y))?;
                self.allocate(None)?;
                Ok(V::new(Value::Some(r)))
            }
            "cons" => {
                self.allocate(None)?;
                Ok(V::new(Value::Cons(a[0].clone(), a[1].clone())))
            }
            "concat" => {
                let mut refs = vec![];
                let mut cur = a[0].clone();
                loop {
                    self.step()?; // セル読取り
                    let next = match &*cur {
                        Value::Cons(h, t) => {
                            refs.push(h.clone());
                            t.clone()
                        }
                        _ => break,
                    };
                    self.step()?; // push
                    cur = next;
                }
                let mut out = a[1].clone();
                while let Some(v) = refs.pop() {
                    self.step()?; // pop
                    self.allocate(None)?;
                    out = V::new(Value::Cons(v, out));
                }
                Ok(out)
            }
            "reverse" => {
                let mut out = V::new(Value::Nil);
                let mut cur = a[0].clone();
                loop {
                    self.step()?;
                    let next = match &*cur {
                        Value::Cons(h, t) => {
                            self.allocate(None)?;
                            out = V::new(Value::Cons(h.clone(), out));
                            t.clone()
                        }
                        _ => return Ok(out),
                    };
                    cur = next;
                }
            }
            "length" => {
                let mut n: u64 = 0;
                let mut cur = a[0].clone();
                loop {
                    self.step()?;
                    let next = match &*cur {
                        Value::Cons(_, t) => t.clone(),
                        _ => break,
                    };
                    n += 1;
                    cur = next;
                }
                self.int(BigInt::from(n))
            }
            _ => unreachable!("unknown builtin {name}"),
        }
    }

    /// 構造的等値。共有 pointer 一致による短絡はしない。
    fn equal(&mut self, x: &V, y: &V) -> R<bool> {
        let mut todo: Vec<(bool, V, V)> = vec![(false, x.clone(), y.clone())]; // (spine?, a, b)
        while let Some((spine, a, b)) = todo.pop() {
            self.step()?;
            if spine {
                match (&*a, &*b) {
                    (Value::Nil, Value::Nil) => {}
                    (Value::Cons(h1, t1), Value::Cons(h2, t2)) => {
                        todo.push((true, t1.clone(), t2.clone()));
                        todo.push((false, h1.clone(), h2.clone()));
                    }
                    _ => return Ok(false),
                }
                continue;
            }
            match (&*a, &*b) {
                (Value::Int(m), Value::Int(n)) => {
                    if m != n {
                        return Ok(false);
                    }
                }
                (Value::Bool(m), Value::Bool(n)) => {
                    if m != n {
                        return Ok(false);
                    }
                }
                (Value::Unit, Value::Unit) | (Value::None, Value::None) => {}
                (Value::Some(p), Value::Some(q)) => todo.push((false, p.clone(), q.clone())),
                (Value::Pair(l1, r1), Value::Pair(l2, r2)) => {
                    todo.push((false, r1.clone(), r2.clone()));
                    todo.push((false, l1.clone(), l2.clone()));
                }
                (Value::Nil | Value::Cons(..), Value::Nil | Value::Cons(..)) => todo.push((true, a.clone(), b.clone())),
                _ => return Ok(false),
            }
        }
        Ok(true)
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
/// 入力型の不一致は API misuse なので panic せず InternalFault ではなく Err で返す。
pub fn run(prog: &TypedProgram, input: &TypedValue, p: &ExecutionProfile, host: &HostPolicy) -> Result<RunResult, String> {
    if input.ty != prog.input_type {
        return Err(format!("入力型 {} が entry の入力型 {} と一致しない", input.ty, prog.input_type));
    }
    if let Some(b) = input_bits_over(&input.value, p.integer_bits) {
        return Ok(RunResult::ResourceExhausted { kind: "IntegerBits", observed: b, limit: p.integer_bits });
    }
    let mut m = Machine { prog, p, host, steps: 0, alloc: 0, depth: 0, env: vec![] };
    let f = prog.function(&prog.entry);
    let r = m.step().and_then(|_| m.call_body(f, vec![input.value.clone()]));
    Ok(match r {
        Err(Stop::Exhausted(kind, observed, limit)) => RunResult::ResourceExhausted { kind, observed, limit },
        Err(Stop::Host(reason)) => RunResult::HostAborted(reason),
        Ok(v) => {
            let out = encode_value(&v);
            if out.len() as u64 > p.output_bytes {
                RunResult::ResourceExhausted { kind: "OutputBytes", observed: p.output_bytes + 1, limit: p.output_bytes }
            } else {
                RunResult::Completed { output: out, steps: m.steps, allocated_nodes: m.alloc }
            }
        }
    })
}
