//! 検証済みの参照評価器（設計書 §7、§8.4、§18.3 と §11.2 の 8）。
//!
//! crates/tlvm の旧評価器と同じ順序で step・AllocatedNodes・整数 bit 長を数える。
//! 証明する性質：
//! - 評価器が値 w を返したなら、spec の燃料付き評価でも同じ式が w に評価される（`evals_to`）。
//! - 評価器は必ず停止する（各再帰・各反復で step を一つ以上消費し、step には上限がある）。
//! 資源上限による打ち切り（`Stop`）は spec の評価と無関係に起こりうる。

use crate::bigint::Int;
use crate::bigstep::*;
use crate::ir::*;
use crate::spec::*;
use crate::value::*;
use std::rc::Rc;
use vstd::prelude::*;

verus! {

pub enum Resource {
    Steps,
    IntegerBits,
    AllocatedNodes,
}

pub enum Stop {
    /// 資源上限（種類、観測値、上限）
    Exhausted(Resource, u64, u64),
    /// host-policy の評価入れ子深さ上限
    HostDepth,
    /// 型付きプログラムでは起きない行き詰まり（spec の Stuck に当たる）
    Fault,
}

/// 結果が Fault（spec の行き詰まりに当たる停止）であること。
pub open spec fn is_fault<T>(r: Result<T, Stop>) -> bool {
    r is Err && r->Err_0 is Fault
}

pub struct Limits {
    pub steps: u64,
    pub integer_bits: u64,
    pub allocated_nodes: u64,
    pub max_depth: u64,
}

pub open spec fn limits_ok(l: Limits) -> bool {
    l.steps < u64::MAX && l.allocated_nodes < u64::MAX && l.max_depth < u64::MAX
}

pub struct Machine {
    pub lim: Limits,
    pub steps: u64,
    pub alloc: u64,
    pub depth: u64,
    pub env: Vec<(usize, Rc<Value>)>,
}

pub open spec fn inv(m: Machine) -> bool {
    &&& limits_ok(m.lim)
    &&& m.steps <= m.lim.steps
    &&& m.alloc <= m.lim.allocated_nodes
    &&& m.depth <= m.lim.max_depth
}

/// 呼出しの前後で保たれる関係（環境と深さは元に戻り、step は減らない）。
pub open spec fn frame(a: Machine, b: Machine) -> bool {
    &&& inv(b)
    &&& b.lim == a.lim
    &&& b.steps >= a.steps
    &&& b.depth == a.depth
    &&& b.env@ == a.env@
}

pub proof fn rev_snoc(s: Seq<Val>, j: int)
    requires
        0 <= j < s.len(),
    ensures
        rev(s.subrange(0, j + 1)) == seq![s[j]] + rev(s.subrange(0, j)),
{
    assert(rev(s.subrange(0, j + 1)) =~= seq![s[j]] + rev(s.subrange(0, j)));
}

impl Machine {
    fn step(&mut self) -> (r: Result<(), Stop>)
        requires
            inv(*self),
        ensures
            frame(*old(self), *final(self)),
            final(self).alloc == old(self).alloc,
            r is Ok ==> final(self).steps == old(self).steps + 1,
            !is_fault(r),
    {
        if self.steps >= self.lim.steps {
            return Err(Stop::Exhausted(Resource::Steps, self.steps + 1, self.lim.steps));
        }
        self.steps = self.steps + 1;
        Ok(())
    }

    /// 新規整数／cons／pair／some node の確保（step → bit → 割当数の順に判定）。
    fn allocate(&mut self, bits: Option<u64>) -> (r: Result<(), Stop>)
        requires
            inv(*self),
        ensures
            frame(*old(self), *final(self)),
            r is Ok ==> final(self).steps == old(self).steps + 1,
            !is_fault(r),
    {
        if self.steps >= self.lim.steps {
            return Err(Stop::Exhausted(Resource::Steps, self.steps + 1, self.lim.steps));
        }
        match bits {
            Some(b) => if b > self.lim.integer_bits {
                return Err(Stop::Exhausted(Resource::IntegerBits, b, self.lim.integer_bits));
            },
            None => {},
        }
        if self.alloc >= self.lim.allocated_nodes {
            return Err(Stop::Exhausted(Resource::AllocatedNodes, self.alloc + 1, self.lim.allocated_nodes));
        }
        self.steps = self.steps + 1;
        self.alloc = self.alloc + 1;
        Ok(())
    }

    fn int(&mut self, n: Int) -> (r: Result<Rc<Value>, Stop>)
        requires
            inv(*self),
        ensures
            frame(*old(self), *final(self)),
            r is Ok ==> view_val(*r->Ok_0) == Val::Int(n@),
            !is_fault(r),
    {
        let b = n.bits();
        self.allocate(Some(b))?;
        Ok(Rc::new(Value::Int(n)))
    }

    pub fn eval(&mut self, p: &EProg, e: &EExpr) -> (r: Result<Rc<Value>, Stop>)
        requires
            inv(*self),
        ensures
            frame(*old(self), *final(self)),
            r is Ok ==> final(self).steps > old(self).steps,
            r is Ok ==> evals_to(view_prog(*p), env_view(old(self).env@), view_expr(*e), view_val(*r->Ok_0)),
            is_fault(r) ==> fails(view_prog(*p), env_view(old(self).env@), view_expr(*e)),
        decreases self.lim.steps - self.steps, 0nat,
    {
        self.step()?;  // 式 node の評価開始
        if self.depth >= self.lim.max_depth {
            return Err(Stop::HostDepth);
        }
        self.depth = self.depth + 1;
        let r = self.eval_inner(p, e);
        self.depth = self.depth - 1;
        r
    }

    fn eval_inner(&mut self, p: &EProg, e: &EExpr) -> (r: Result<Rc<Value>, Stop>)
        requires
            inv(*self),
        ensures
            frame(*old(self), *final(self)),
            r is Ok ==> evals_to(view_prog(*p), env_view(old(self).env@), view_expr(*e), view_val(*r->Ok_0)),
            is_fault(r) ==> fails(view_prog(*p), env_view(old(self).env@), view_expr(*e)),
        decreases self.lim.steps - self.steps, 2nat,
    {
        let ghost pp = view_prog(dr(p));
        let ghost env = env_view(self.env@);
        match e {
            EExpr::Var(x) => match lookup(&self.env, *x) {
                Some(v) => {
                    proof {
                        bs_var(pp, env, *x as nat);
                    }
                    Ok(v)
                },
                None => {
                    proof {
                        fl_var(pp, env, *x as nat);
                    }
                    Err(Stop::Fault)
                },
            },
            EExpr::Int(n) => {
                let r = self.int(n.copy());
                proof {
                    bs_leaf(pp, env, view_expr(dr(e)));
                }
                r
            },
            EExpr::Bool(b) => {
                proof {
                    bs_leaf(pp, env, view_expr(dr(e)));
                }
                Ok(Rc::new(Value::Bool(*b)))
            },
            EExpr::Unit => {
                proof {
                    bs_leaf(pp, env, view_expr(dr(e)));
                }
                Ok(Rc::new(Value::Unit))
            },
            EExpr::None(_) => {
                proof {
                    bs_leaf(pp, env, view_expr(dr(e)));
                }
                Ok(Rc::new(Value::None))
            },
            EExpr::Some(x) => {
                let v = match self.eval(p, x) {
                    Ok(v) => v,
                    Err(s) => {
                        proof {
                            if is_fault(Err::<(), Stop>(s)) {
                                fl_some(pp, env, view_expr(*dr(x)));
                            }
                        }
                        return Err(s);
                    },
                };
                self.allocate(None)?;
                proof {
                    bs_some(pp, env, view_expr(*dr(x)), vv(v));
                }
                Ok(Rc::new(Value::Some(v)))
            },
            EExpr::Pair(a, b) => {
                let va = match self.eval(p, a) {
                    Ok(v) => v,
                    Err(s) => {
                        proof {
                            if is_fault(Err::<(), Stop>(s)) {
                                fl_pair(pp, env, view_expr(*dr(a)), view_expr(*dr(b)));
                            }
                        }
                        return Err(s);
                    },
                };
                let vb = match self.eval(p, b) {
                    Ok(v) => v,
                    Err(s) => {
                        proof {
                            if is_fault(Err::<(), Stop>(s)) {
                                fl_pair(pp, env, view_expr(*dr(a)), view_expr(*dr(b)));
                            }
                        }
                        return Err(s);
                    },
                };
                self.allocate(None)?;
                proof {
                    bs_pair(pp, env, view_expr(*dr(a)), view_expr(*dr(b)), vv(va), vv(vb));
                }
                Ok(Rc::new(Value::Pair(va, vb)))
            },
            EExpr::Builtin(b, es) => {
                let vs = match self.eval_args(p, es, false) {
                    Ok(vs) => vs,
                    Err(s) => {
                        proof {
                            if is_fault(Err::<(), Stop>(s)) {
                                fl_builtin(pp, env, *b, view_exprs(dr(es)), Seq::empty());
                            }
                        }
                        return Err(s);
                    },
                };
                self.step()?;  // 組込みの適用開始
                let ghost vsv = view_vals(vs@);
                let r = self.builtin(*b, vs);
                proof {
                    if r is Ok {
                        bs_builtin(pp, env, *b, view_exprs(dr(es)), vsv, vv(r->Ok_0));
                    }
                    if is_fault(r) {
                        fl_builtin(pp, env, *b, view_exprs(dr(es)), vsv);
                    }
                }
                r
            },
            EExpr::Call(g, es) => {
                let vs = match self.eval_args(p, es, false) {
                    Ok(vs) => vs,
                    Err(s) => {
                        proof {
                            if is_fault(Err::<(), Stop>(s)) {
                                fl_call(pp, env, *g as nat, view_exprs(dr(es)), Seq::empty());
                            }
                        }
                        return Err(s);
                    },
                };
                self.step()?;  // ユーザー関数本体への入場
                let ghost vsv = view_vals(vs@);
                let r = self.call_body(p, *g, vs);
                proof {
                    if r is Ok {
                        bs_call(pp, env, *g as nat, view_exprs(dr(es)), vsv, vv(r->Ok_0));
                    }
                    if is_fault(r) {
                        assert(vsv.len() == vs@.len());
                        fl_call(pp, env, *g as nat, view_exprs(dr(es)), vsv);
                    }
                }
                r
            },
            EExpr::Let(x, a, b) => {
                let va = match self.eval(p, a) {
                    Ok(v) => v,
                    Err(s) => {
                        proof {
                            if is_fault(Err::<(), Stop>(s)) {
                                fl_let(pp, env, *x as nat, view_expr(*dr(a)), view_expr(*dr(b)), Val::Unit);
                            }
                        }
                        return Err(s);
                    },
                };
                let ghost before = self.env@;
                self.env.push((*x, va.clone()));
                proof {
                    env_view_push(before, *x, va);
                }
                let r = self.eval(p, b);
                self.env.pop();
                proof {
                    assert(self.env@ =~= before);
                    if r is Ok {
                        bs_let(pp, env, *x as nat, view_expr(*dr(a)), view_expr(*dr(b)), vv(va), vv(r->Ok_0));
                    }
                    if is_fault(r) {
                        fl_let(pp, env, *x as nat, view_expr(*dr(a)), view_expr(*dr(b)), vv(va));
                    }
                }
                r
            },
            EExpr::If(c, a, b) => {
                let cv = match self.eval(p, c) {
                    Ok(v) => v,
                    Err(s) => {
                        proof {
                            if is_fault(Err::<(), Stop>(s)) {
                                fl_if(pp, env, view_expr(*dr(c)), view_expr(*dr(a)), view_expr(*dr(b)), Val::Unit);
                            }
                        }
                        return Err(s);
                    },
                };
                match &*cv {
                    Value::Bool(bv) => {
                        let r = if *bv {
                            self.eval(p, a)
                        } else {
                            self.eval(p, b)
                        };
                        proof {
                            if r is Ok {
                                bs_if(pp, env, view_expr(*dr(c)), view_expr(*dr(a)), view_expr(*dr(b)), *bv, vv(r->Ok_0));
                            }
                            if is_fault(r) {
                                fl_if(pp, env, view_expr(*dr(c)), view_expr(*dr(a)), view_expr(*dr(b)), vv(cv));
                            }
                        }
                        r
                    },
                    _ => {
                        proof {
                            assert(!(vv(cv) is Bool));
                            fl_if(pp, env, view_expr(*dr(c)), view_expr(*dr(a)), view_expr(*dr(b)), vv(cv));
                        }
                        Err(Stop::Fault)
                    },
                }
            },
            EExpr::List(t, es) => {
                let _ = t;
                let mut vs = match self.eval_args(p, es, true) {
                    Ok(vs) => vs,
                    Err(s) => {
                        proof {
                            if is_fault(Err::<(), Stop>(s)) {
                                fl_list(pp, env, dr(t), view_exprs(dr(es)));
                            }
                        }
                        return Err(s);
                    },
                };
                let ghost all = vs@;
                let ghost vsv = view_vals(vs@);
                let mut out = Rc::new(Value::Nil);
                loop
                    invariant
                        inv(*self),
                        frame(*old(self), *self),
                        vs@.len() <= all.len(),
                        vs@ == all.subrange(0, vs@.len() as int),
                        vsv == view_vals(all),
                        is_list(*out),
                        spine(*out) == vsv.subrange(vs@.len() as int, all.len() as int),
                    ensures
                        vs@.len() == 0,
                    decreases vs@.len(),
                {
                    match vs.pop() {
                        Some(v) => {
                            self.step()?;  // 一時要素参照の pop
                            self.allocate(None)?;
                            let ghost k = vs@.len();
                            proof {
                                assert(vv(v) == vsv[k as int]);
                                spine_cons(v, out);
                                assert(seq![vsv[k as int]] + vsv.subrange(k as int + 1, all.len() as int)
                                    =~= vsv.subrange(k as int, all.len() as int));
                            }
                            out = Rc::new(Value::Cons(v, out));
                        },
                        None => break,
                    }
                }
                proof {
                    assert(vsv.subrange(0, all.len() as int) =~= vsv);
                    bs_list(pp, env, dr(t), view_exprs(dr(es)), vsv);
                }
                Ok(out)
            },
            EExpr::Fold(xs, init, acc, item, body) => {
                let ghost xse = view_expr(*dr(xs));
                let ghost ie = view_expr(*dr(init));
                let ghost bodye = view_expr(*dr(body));
                let xv = match self.eval(p, xs) {
                    Ok(v) => v,
                    Err(s) => {
                        proof {
                            if is_fault(Err::<(), Stop>(s)) {
                                fl_fold(pp, env, xse, ie, *acc as nat, *item as nat, bodye, Val::Unit, Val::Unit);
                            }
                        }
                        return Err(s);
                    },
                };
                let av = match self.eval(p, init) {
                    Ok(v) => v,
                    Err(s) => {
                        proof {
                            if is_fault(Err::<(), Stop>(s)) {
                                fl_fold(pp, env, xse, ie, *acc as nat, *item as nat, bodye, vv(xv), Val::Unit);
                            }
                        }
                        return Err(s);
                    },
                };
                if !(match &*xv {
                    Value::Nil => true,
                    Value::Cons(_, _) => true,
                    _ => false,
                }) {
                    proof {
                        assert(!(vv(xv) is List));
                        fl_fold(pp, env, xse, ie, *acc as nat, *item as nat, bodye, vv(xv), vv(av));
                    }
                    return Err(Stop::Fault);
                }
                let ghost whole = view_expr(dr(e));
                proof {
                    assert(whole == Expr::Fold(Box::new(xse), Box::new(ie), *acc as nat, *item as nat, Box::new(bodye)));
                }
                let ghost items = sp(xv);
                let ghost bodyv = view_expr(*dr(body));
                let ghost base = self.env@;
                let ghost mut accs: Seq<Val> = seq![vv(av)];
                let mut cur = xv.clone();
                let mut a = av;
                loop
                    invariant
                        inv(*self),
                        frame(*old(self), *self),
                        self.env@ == base,
                        base == old(self).env@,
                        env == env_view(base),
                        pp == view_prog(*p),
                        bodyv == view_expr(**body),
                        items == spine(*xv),
                        vv(xv) == Val::List(items),
                        evals_to(pp, env, xse, Val::List(items)),
                        evals_to(pp, env, ie, accs[0]),
                        xse == view_expr(**xs),
                        whole == view_expr(*e),
                        whole == Expr::Fold(Box::new(xse), Box::new(ie), *acc as nat, *item as nat, Box::new(bodye)),
                        ie == view_expr(**init),
                        bodye == bodyv,
                        accs.len() >= 1,
                        accs.len() - 1 <= items.len(),
                        accs.last() == view_val(*a),
                        accs[0] == view_val(*av),
                        spine(*cur) == items.subrange(accs.len() - 1, items.len() as int),
                        forall|k: int|
                            0 <= k < accs.len() - 1 ==> evals_to(
                                pp,
                                #[trigger] env.insert(*acc as nat, accs[k]).insert(*item as nat, items[k]),
                                bodyv,
                                accs[k + 1],
                            ),
                    ensures
                        !(*cur is Cons),
                    decreases self.lim.steps - self.steps,
                {
                    self.step()?;  // spine cursor の読取り
                    let (h, t) = match &*cur {
                        Value::Cons(h, t) => (h.clone(), t.clone()),
                        _ => break,
                    };
                    let ghost j = accs.len() - 1;
                    proof {
                        spine_step(items, j, h, t);
                    }
                    self.env.push((*acc, a));
                    self.env.push((*item, h.clone()));
                    proof {
                        env_view_push(base, *acc, a);
                        env_view_push(base.push((*acc, a)), *item, h);
                        assert(self.env@ == base.push((*acc, a)).push((*item, h)));
                        assert(env_view(base) == env);
                        assert(env_view(self.env@) == env.insert(*acc as nat, vv(a)).insert(*item as nat, vv(h)));
                        assert(vv(a) == accs[j]);
                        assert(vv(h) == items[j]);
                    }
                    let ghost env2 = env_view(self.env@);
                    let r = self.eval(p, body);
                    self.env.pop();
                    self.env.pop();
                    proof {
                        assert(self.env@ =~= base);
                    }
                    let v = match r {
                        Ok(v) => v,
                        Err(s) => {
                            proof {
                                if is_fault(Err::<(), Stop>(s)) {
                                    assert(env2 == env.insert(*acc as nat, accs[j]).insert(*item as nat, items[j]));
                                    fl_fold_steps(pp, env, *acc as nat, *item as nat, bodyv, items, accs, j as nat);
                                    fl_fold(pp, env, xse, ie, *acc as nat, *item as nat, bodye, vv(xv), accs[0]);
                                }
                            }
                            return Err(s);
                        },
                    };
                    proof {
                        assert(evals_to(pp, env2, bodyv, vv(v)));
                        assert(evals_to(pp, env.insert(*acc as nat, accs[j]).insert(*item as nat, items[j]), bodyv, vv(v)));
                        accs = accs.push(vv(v));
                        assert(accs[j] == vv(a));
                    }
                    a = v;
                    cur = t;
                }
                proof {
                    let j = accs.len() - 1;
                    spine_end(cur);
                    assert(j == items.len());
                    fold_from_each(pp, env, *acc as nat, *item as nat, bodyv, items, accs, 0);
                    bs_fold(pp, env, view_expr(*dr(xs)), view_expr(*dr(init)), *acc as nat, *item as nat, bodyv, items, vv(av), vv(a));
                }
                Ok(a)
            },
        }
    }

    /// 引数を左から右へ評価する。`push_step` はリスト式の一時要素参照の push を数える。
    fn eval_args(&mut self, p: &EProg, es: &Vec<EExpr>, push_step: bool) -> (r: Result<Vec<Rc<Value>>, Stop>)
        requires
            inv(*self),
        ensures
            frame(*old(self), *final(self)),
            r is Ok ==> r->Ok_0@.len() == es@.len() && args_to(
                view_prog(*p),
                env_view(old(self).env@),
                view_exprs(*es),
                0,
                view_vals(r->Ok_0@),
            ),
            is_fault(r) ==> args_fail(view_prog(*p), env_view(old(self).env@), view_exprs(*es), 0),
        decreases self.lim.steps - self.steps, 1nat,
    {
        let ghost pp = view_prog(dr(p));
        let ghost env = env_view(self.env@);
        let ghost esv = view_exprs(dr(es));
        let mut vs: Vec<Rc<Value>> = Vec::new();
        let mut i = 0;
        while i < es.len()
            invariant
                inv(*self),
                frame(*old(self), *self),
                env == env_view(self.env@),
                pp == view_prog(*p),
                i <= es@.len(),
                vs@.len() == i,
                esv == view_exprs(*es),
                forall|k: int| 0 <= k < i ==> evals_to(pp, env, #[trigger] esv[k], view_val(*vs@[k])),
            decreases es@.len() - i,
        {
            let v = match self.eval(p, &es[i]) {
                Ok(v) => v,
                Err(s) => {
                    proof {
                        if is_fault(Err::<(), Stop>(s)) {
                            assert(esv[i as int] == view_expr(es@[i as int]));
                            fl_args(pp, env, esv, i as nat);
                        }
                    }
                    return Err(s);
                },
            };
            proof {
                assert(esv[i as int] == view_expr(es@[i as int]));
                assert(evals_to(pp, env, esv[i as int], vv(v)));
            }
            if push_step {
                self.step()?;
            }
            let ghost old_vs = vs@;
            vs.push(v);
            proof {
                assert forall|k: int| 0 <= k < i + 1 implies evals_to(pp, env, #[trigger] esv[k], view_val(*vs@[k])) by {
                    if k < i {
                        assert(vs@[k] == old_vs[k]);
                    }
                }
            }
            i = i + 1;
        }
        proof {
            let vsv = view_vals(vs@);
            assert forall|k: int| 0 <= k < esv.len() implies evals_to(pp, env, #[trigger] esv[k], vsv[k]) by {}
            args_from_each(pp, env, esv, vsv, 0);
            assert(vsv.subrange(0, vsv.len() as int) =~= vsv);
        }
        Ok(vs)
    }

    /// ユーザー関数本体を新しい環境で評価する（入場 step は呼出し側で数える）。
    fn call_body(&mut self, p: &EProg, g: usize, args: Vec<Rc<Value>>) -> (r: Result<Rc<Value>, Stop>)
        requires
            inv(*self),
        ensures
            frame(*old(self), *final(self)),
            r is Ok ==> g < p.funcs@.len() && args@.len() == view_prog(*p).funcs[g as int].params.len()
                && evals_to(
                view_prog(*p),
                bind(view_prog(*p).funcs[g as int].params, view_vals(args@), args@.len()),
                view_prog(*p).funcs[g as int].body,
                view_val(*r->Ok_0),
            ),
            is_fault(r) ==> !(g < view_prog(*p).funcs.len() && args@.len() == view_prog(*p).funcs[g as int].params.len())
                || fails(
                view_prog(*p),
                bind(view_prog(*p).funcs[g as int].params, view_vals(args@), args@.len()),
                view_prog(*p).funcs[g as int].body,
            ),
        decreases self.lim.steps - self.steps, 1nat,
    {
        if g >= p.funcs.len() {
            return Err(Stop::Fault);
        }
        let f = &p.funcs[g];
        if args.len() != f.params.len() {
            return Err(Stop::Fault);
        }
        let ghost params = view_params(f.params@);
        let ghost vsv = view_vals(args@);
        let mut env2: Vec<(usize, Rc<Value>)> = Vec::new();
        let mut k = 0;
        while k < args.len()
            invariant
                k <= args@.len(),
                args@.len() == f.params@.len(),
                params == view_params(f.params@),
                vsv == view_vals(args@),
                env_view(env2@) == bind(params, vsv, k as nat),
            decreases args@.len() - k,
        {
            let ghost before = env2@;
            env2.push((f.params[k].0, args[k].clone()));
            proof {
                env_view_push(before, f.params@[k as int].0, args@[k as int]);
            }
            k = k + 1;
        }
        std::mem::swap(&mut self.env, &mut env2);
        let r = self.eval(p, &f.body);
        std::mem::swap(&mut self.env, &mut env2);
        r
    }

    fn builtin(&mut self, b: Builtin, a: Vec<Rc<Value>>) -> (r: Result<Rc<Value>, Stop>)
        requires
            inv(*self),
        ensures
            frame(*old(self), *final(self)),
            r is Ok ==> apply(b, view_vals(a@)) == Res::Done(view_val(*r->Ok_0)),
            is_fault(r) ==> !(apply(b, view_vals(a@)) is Done),
    {
        if a.len() == 2 {
            match b {
                Builtin::Eq => {
                    let r = self.equal(&a[0], &a[1])?;
                    return Ok(Rc::new(Value::Bool(r)));
                },
                Builtin::Cons => {
                    if !(match &*a[1] {
                        Value::Nil => true,
                        Value::Cons(_, _) => true,
                        _ => false,
                    }) {
                        return Err(Stop::Fault);
                    }
                    self.allocate(None)?;
                    proof {
                        spine_cons(a@[0], a@[1]);
                    }
                    return Ok(Rc::new(Value::Cons(a[0].clone(), a[1].clone())));
                },
                Builtin::Concat => {
                    if !(match &*a[0] {
                        Value::Nil => true,
                        Value::Cons(_, _) => true,
                        _ => false,
                    }) || !(match &*a[1] {
                        Value::Nil => true,
                        Value::Cons(_, _) => true,
                        _ => false,
                    }) {
                        return Err(Stop::Fault);
                    }
                    return self.concat(&a[0], &a[1]);
                },
                _ => {},
            }
            match (&*a[0], &*a[1]) {
                (Value::Int(x), Value::Int(y)) => match b {
                    Builtin::Add => self.int(x.add(y)),
                    Builtin::Sub => self.int(x.sub(y)),
                    Builtin::Mul => self.int(x.mul(y)),
                    Builtin::Lt => Ok(Rc::new(Value::Bool(x.lt(y)))),
                    Builtin::Le => Ok(Rc::new(Value::Bool(x.le(y)))),
                    Builtin::Mod => {
                        if !y.is_positive() {
                            return Ok(Rc::new(Value::None));
                        }
                        let r = self.int(x.mod_pos(y))?;
                        self.allocate(None)?;
                        Ok(Rc::new(Value::Some(r)))
                    },
                    _ => Err(Stop::Fault),
                },
                _ => Err(Stop::Fault),
            }
        } else if a.len() == 1 {
            match (b, &*a[0]) {
                (Builtin::Neg, Value::Int(x)) => self.int(x.neg()),
                (Builtin::Fst, Value::Pair(l, _)) => Ok(l.clone()),
                (Builtin::Snd, Value::Pair(_, r)) => Ok(r.clone()),
                (Builtin::Reverse, Value::Nil) | (Builtin::Reverse, Value::Cons(_, _)) => self.reverse(&a[0]),
                (Builtin::Length, Value::Nil) | (Builtin::Length, Value::Cons(_, _)) => self.length(&a[0]),
                _ => Err(Stop::Fault),
            }
        } else {
            Err(Stop::Fault)
        }
    }

    fn concat(&mut self, a0: &Rc<Value>, a1: &Rc<Value>) -> (r: Result<Rc<Value>, Stop>)
        requires
            inv(*self),
            is_list(**a1),
        ensures
            frame(*old(self), *final(self)),
            r is Ok ==> is_list(*r->Ok_0) && spine(*r->Ok_0) == spine(**a0) + spine(**a1),
            !is_fault(r),
    {
        let mut refs: Vec<Rc<Value>> = Vec::new();
        let mut cur = a0.clone();
        loop
            invariant
                inv(*self),
                frame(*old(self), *self),
                view_vals(refs@) + spine(*cur) == spine(**a0),
            ensures
                !(*cur is Cons),
            decreases self.lim.steps - self.steps,
        {
            self.step()?;  // セル読取り
            let next = match &*cur {
                Value::Cons(h, t) => {
                    proof {
                        spine_cons(dr(h), dr(t));
                        assert(view_vals(refs@.push(dr(h))) + sp(dr(t)) =~= view_vals(refs@) + sp(cur));
                    }
                    refs.push(h.clone());
                    t.clone()
                },
                _ => break,
            };
            self.step()?;  // push
            cur = next;
        }
        proof {
            spine_end(cur);
            assert(view_vals(refs@) =~= sp(dr(a0)));
        }
        let ghost all = refs@;
        let ghost sv = view_vals(all);
        let mut out = a1.clone();
        loop
            invariant
                inv(*self),
                frame(*old(self), *self),
                refs@.len() <= all.len(),
                refs@ == all.subrange(0, refs@.len() as int),
                sv == view_vals(all),
                sv == spine(**a0),
                is_list(*out),
                spine(*out) == sv.subrange(refs@.len() as int, all.len() as int) + spine(**a1),
            ensures
                refs@.len() == 0,
            decreases refs@.len(),
        {
            match refs.pop() {
                Some(v) => {
                    self.step()?;  // pop
                    self.allocate(None)?;
                    let ghost k = refs@.len();
                    proof {
                        assert(vv(v) == sv[k as int]);
                        spine_cons(v, out);
                        assert(seq![sv[k as int]] + (sv.subrange(k as int + 1, all.len() as int) + sp(dr(a1)))
                            =~= sv.subrange(k as int, all.len() as int) + sp(dr(a1)));
                    }
                    out = Rc::new(Value::Cons(v, out));
                },
                None => break,
            }
        }
        proof {
            assert(sv.subrange(0, all.len() as int) =~= sv);
        }
        Ok(out)
    }

    fn reverse(&mut self, a0: &Rc<Value>) -> (r: Result<Rc<Value>, Stop>)
        requires
            inv(*self),
        ensures
            frame(*old(self), *final(self)),
            r is Ok ==> view_val(*r->Ok_0) == Val::List(rev(spine(**a0))),
            !is_fault(r),
    {
        let ghost s = sp(dr(a0));
        let ghost mut j: int = 0;
        let mut out = Rc::new(Value::Nil);
        let mut cur = a0.clone();
        proof {
            assert(rev(s.subrange(0, 0)) =~= Seq::<Val>::empty());
            assert(s.subrange(0, s.len() as int) =~= s);
        }
        loop
            invariant
                inv(*self),
                frame(*old(self), *self),
                s == spine(**a0),
                0 <= j <= s.len(),
                spine(*cur) == s.subrange(j, s.len() as int),
                is_list(*out),
                spine(*out) == rev(s.subrange(0, j)),
            decreases self.lim.steps - self.steps,
        {
            self.step()?;
            let (h, t) = match &*cur {
                Value::Cons(h, t) => (h.clone(), t.clone()),
                _ => {
                    proof {
                        spine_end(cur);
                        assert(sp(cur).len() == 0);
                        assert(s.subrange(j, s.len() as int).len() == s.len() - j);
                        assert(j == s.len());
                        assert(s.subrange(0, j) =~= s);
                    }
                    return Ok(out);
                },
            };
            self.allocate(None)?;
            proof {
                spine_step(s, j, h, t);
                rev_snoc(s, j);
                spine_cons(h, out);
                j = j + 1;
            }
            out = Rc::new(Value::Cons(h, out));
            cur = t;
        }
    }

    fn length(&mut self, a0: &Rc<Value>) -> (r: Result<Rc<Value>, Stop>)
        requires
            inv(*self),
        ensures
            frame(*old(self), *final(self)),
            r is Ok ==> view_val(*r->Ok_0) == Val::Int(spine(**a0).len() as int),
            !is_fault(r),
    {
        let ghost s = sp(dr(a0));
        let ghost start = self.steps;
        let mut n: u64 = 0;
        let mut cur = a0.clone();
        proof {
            assert(s.subrange(0, s.len() as int) =~= s);
        }
        loop
            invariant
                inv(*self),
                frame(*old(self), *self),
                start == old(self).steps,
                s == spine(**a0),
                n <= s.len(),
                n <= self.steps - start,
                spine(*cur) == s.subrange(n as int, s.len() as int),
            ensures
                !(*cur is Cons),
            decreases self.lim.steps - self.steps,
        {
            self.step()?;
            let next = match &*cur {
                Value::Cons(h, t) => {
                    let _ = h;
                    proof {
                        spine_step(s, n as int, dr(h), dr(t));
                    }
                    t.clone()
                },
                _ => break,
            };
            n = n + 1;
            cur = next;
        }
        proof {
            spine_end(cur);
        }
        self.int(Int::from_u64(n))
    }

    /// 構造的等値。共有 pointer 一致による短絡はしない。
    fn equal(&mut self, x: &Rc<Value>, y: &Rc<Value>) -> (r: Result<bool, Stop>)
        requires
            inv(*self),
        ensures
            frame(*old(self), *final(self)),
            r is Ok ==> r->Ok_0 == (view_val(**x) == view_val(**y)),
            !is_fault(r),
        decreases self.lim.steps - self.steps, 0nat,
    {
        self.step()?;
        match (&**x, &**y) {
            (Value::Int(m), Value::Int(n)) => Ok(m.eq(n)),
            (Value::Bool(m), Value::Bool(n)) => Ok(*m == *n),
            (Value::Unit, Value::Unit) => Ok(true),
            (Value::None, Value::None) => Ok(true),
            (Value::Some(a), Value::Some(b)) => self.equal(a, b),
            (Value::Pair(l1, r1), Value::Pair(l2, r2)) => {
                if !self.equal(l1, l2)? {
                    return Ok(false);
                }
                self.equal(r1, r2)
            },
            (Value::Nil, Value::Nil) | (Value::Nil, Value::Cons(_, _)) | (Value::Cons(_, _), Value::Nil) | (
                Value::Cons(_, _),
                Value::Cons(_, _),
            ) => self.equal_spine(x, y),
            _ => Ok(false),
        }
    }

    fn equal_spine(&mut self, x: &Rc<Value>, y: &Rc<Value>) -> (r: Result<bool, Stop>)
        requires
            inv(*self),
        ensures
            frame(*old(self), *final(self)),
            r is Ok ==> r->Ok_0 == (spine(**x) == spine(**y)),
            !is_fault(r),
        decreases self.lim.steps - self.steps, 1nat,
    {
        let mut a = x.clone();
        let mut b = y.clone();
        loop
            invariant
                inv(*self),
                frame(*old(self), *self),
                (spine(**x) == spine(**y)) == (spine(*a) == spine(*b)),
            decreases self.lim.steps - self.steps,
        {
            self.step()?;
            let (na, nb) = match (&*a, &*b) {
                (Value::Cons(h1, t1), Value::Cons(h2, t2)) => {
                    let same = self.equal(h1, h2)?;
                    proof {
                        spine_cons(dr(h1), dr(t1));
                        spine_cons(dr(h2), dr(t2));
                        if same {
                            assert(sp(a) == sp(b) <==> sp(dr(t1)) == sp(dr(t2))) by {
                                if sp(a) == sp(b) {
                                    assert(sp(dr(t1)) =~= sp(a).subrange(1, sp(a).len() as int));
                                    assert(sp(dr(t2)) =~= sp(b).subrange(1, sp(b).len() as int));
                                }
                            }
                        } else {
                            assert(sp(a)[0] != sp(b)[0]);
                        }
                    }
                    if !same {
                        return Ok(false);
                    }
                    (t1.clone(), t2.clone())
                },
                (Value::Cons(_, _), _) | (_, Value::Cons(_, _)) => return Ok(false),
                _ => return Ok(true),
            };
            a = na;
            b = nb;
        }
    }
}

pub fn new_machine(lim: Limits) -> (m: Machine)
    requires
        limits_ok(lim),
    ensures
        inv(m),
        m.lim == lim,
        m.env@.len() == 0,
{
    Machine { lim, steps: 0, alloc: 0, depth: 0, env: Vec::new() }
}

/// entry 関数を入力値に適用する。値を返したなら spec の `eval_entry` も同じ値になる。
pub fn run(p: &EProg, input: Rc<Value>, lim: Limits) -> (r: (Result<Rc<Value>, Stop>, u64, u64))
    requires
        limits_ok(lim),
    ensures
        r.0 is Ok ==> p.entry < p.funcs@.len() && exists|n: nat|
            #[trigger] eval_entry(view_prog(*p), n, view_val(*input)) == Res::Done(view_val(*r.0->Ok_0)),
        is_fault(r.0) && p.entry < p.funcs@.len() && view_prog(*p).funcs[p.entry as int].params.len() == 1
            ==> forall|n: nat| !(#[trigger] eval_entry(view_prog(*p), n, view_val(*input)) is Done),
{
    let mut m = new_machine(lim);
    let ghost iv = vv(input);
    let r = match m.step() {
        Err(s) => Err(s),
        Ok(()) => {
            let mut args = Vec::new();
            args.push(input);
            proof {
                assert(view_vals(args@) =~= seq![iv]);
            }
            let r = m.call_body(p, p.entry, args);
            proof {
                let pp = view_prog(dr(p));
                if is_fault(r) && p.entry < p.funcs@.len() && pp.funcs[p.entry as int].params.len() == 1 {
                    let f = pp.funcs[p.entry as int];
                    assert(fails(pp, bind(f.params, seq![iv], 1), f.body));
                    assert forall|n: nat| !(#[trigger] eval_entry(pp, n, iv) is Done) by {
                        assert(eval_entry(pp, n, iv) == eval(pp, n, bind(f.params, seq![iv], 1), f.body));
                    }
                }
            }
            r
        },
    };
    proof {
        if r is Ok {
            let pp = view_prog(dr(p));
            let f = pp.funcs[p.entry as int];
            let w = vv(r->Ok_0);
            let n = choose|n: nat| #[trigger] eval(pp, n, bind(f.params, seq![iv], 1), f.body) == Res::Done(w);
            assert(eval_entry(pp, n, iv) == Res::Done(w));
        }
    }
    (r, m.steps, m.alloc)
}

} // verus!
