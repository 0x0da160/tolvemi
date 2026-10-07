//! proof 層（設計書 §11.2）：燃料単調性、決定性、停止性と型安全性。
//!
//! 主定理 `entry_total`：整形式プログラム（`wf`）の entry に入力型の値を与えると、
//! ある燃料で評価は必ず `Done` になり、結果は出力型を持つ。`Stuck`（型エラーによる
//! 行き詰まり）は起きず、燃料さえ足りれば停止する。`eval_deterministic` により結果は
//! 燃料に依らず一意。`assume` と `external_body` は使っていない。

use crate::spec::*;
use vstd::prelude::*;

verus! {

// ------------------------------------------------------------------ 燃料単調性と決定性

/// 燃料 n で OutOfFuel 以外の結果が出れば、より多い燃料でも同じ結果になる。
pub proof fn mono(p: Prog, n: nat, m: nat, env: Map<nat, Val>, e: Expr)
    requires
        n <= m,
    ensures
        !(eval(p, n, env, e) is OutOfFuel) ==> eval(p, m, env, e) == eval(p, n, env, e),
    decreases n,
{
    if n > 0 {
        let f = (n - 1) as nat;
        let g = (m - 1) as nat;
        match e {
            Expr::List(_, es) => mono_args(p, f, g, env, es, 0),
            Expr::Some(x) => mono(p, f, g, env, *x),
            Expr::Pair(a, b) => {
                mono(p, f, g, env, *a);
                mono(p, f, g, env, *b);
            },
            Expr::Builtin(_, es) => mono_args(p, f, g, env, es, 0),
            Expr::Call(gi, es) => {
                mono_args(p, f, g, env, es, 0);
                match eval_args(p, f, env, es, 0) {
                    ResSeq::Done(vs) => if gi < p.funcs.len() {
                        mono(p, f, g, bind(p.funcs[gi as int].params, vs, vs.len()), p.funcs[gi as int].body);
                    },
                    _ => {},
                }
            },
            Expr::Let(x, a, b) => {
                mono(p, f, g, env, *a);
                match eval(p, f, env, *a) {
                    Res::Done(v) => mono(p, f, g, env.insert(x, v), *b),
                    _ => {},
                }
            },
            Expr::If(c, a, b) => {
                mono(p, f, g, env, *c);
                mono(p, f, g, env, *a);
                mono(p, f, g, env, *b);
            },
            Expr::Fold(xs, init, acc, item, body) => {
                mono(p, f, g, env, *xs);
                mono(p, f, g, env, *init);
                match (eval(p, f, env, *xs), eval(p, f, env, *init)) {
                    (Res::Done(Val::List(s)), Res::Done(v0)) => mono_fold(p, f, g, env, acc, item, *body, s, 0, v0),
                    _ => {},
                }
            },
            Expr::Match(m, nb, x, sm) => {
                mono(p, f, g, env, *m);
                mono(p, f, g, env, *nb);
                match eval(p, f, env, *m) {
                    Res::Done(Val::Some(v)) => mono(p, f, g, env.insert(x, *v), *sm),
                    _ => {},
                }
            },
            _ => {},
        }
    }
}

pub proof fn mono_args(p: Prog, n: nat, m: nat, env: Map<nat, Val>, es: Seq<Expr>, i: nat)
    requires
        n <= m,
    ensures
        !(eval_args(p, n, env, es, i) is OutOfFuel) ==> eval_args(p, m, env, es, i) == eval_args(p, n, env, es, i),
    decreases n,
{
    if n > 0 && i < es.len() {
        let f = (n - 1) as nat;
        let g = (m - 1) as nat;
        mono(p, f, g, env, es[i as int]);
        mono_args(p, f, g, env, es, i + 1);
    }
}

pub proof fn mono_fold(
    p: Prog,
    n: nat,
    m: nat,
    env: Map<nat, Val>,
    acc: nat,
    item: nat,
    body: Expr,
    items: Seq<Val>,
    j: nat,
    a: Val,
)
    requires
        n <= m,
    ensures
        !(eval_fold(p, n, env, acc, item, body, items, j, a) is OutOfFuel) ==> eval_fold(
            p,
            m,
            env,
            acc,
            item,
            body,
            items,
            j,
            a,
        ) == eval_fold(p, n, env, acc, item, body, items, j, a),
    decreases n,
{
    if n > 0 && j < items.len() {
        let f = (n - 1) as nat;
        let g = (m - 1) as nat;
        let env2 = env.insert(acc, a).insert(item, items[j as int]);
        mono(p, f, g, env2, body);
        match eval(p, f, env2, body) {
            Res::Done(v) => mono_fold(p, f, g, env, acc, item, body, items, j + 1, v),
            _ => {},
        }
    }
}

/// 決定性：どの燃料で得た結果も（OutOfFuel でなければ）一致する。
pub proof fn eval_deterministic(p: Prog, n: nat, m: nat, env: Map<nat, Val>, e: Expr)
    ensures
        !(eval(p, n, env, e) is OutOfFuel) && !(eval(p, m, env, e) is OutOfFuel) ==> eval(p, n, env, e) == eval(
            p,
            m,
            env,
            e,
        ),
{
    if n <= m {
        mono(p, n, m, env, e);
    } else {
        mono(p, m, n, env, e);
    }
}

// ------------------------------------------------------------------ リストの型

pub proof fn list_type_iff(s: Seq<Val>, t: Ty, i: nat)
    ensures
        list_type(s, t, i) <==> forall|k: int| i <= k < s.len() ==> #[trigger] val_type(s[k], t),
    decreases s.len() - i,
{
    if i < s.len() {
        list_type_iff(s, t, i + 1);
        if forall|k: int| i <= k < s.len() ==> #[trigger] val_type(s[k], t) {
            assert(val_type(s[i as int], t));
        }
        if list_type(s, t, i) {
            assert forall|k: int| i <= k < s.len() implies #[trigger] val_type(s[k], t) by {
                if k > i {
                    assert(list_type(s, t, i + 1));
                }
            }
        }
    }
}

/// リスト値の型付けは要素ごとの型付けと同値。
pub proof fn val_type_list(s: Seq<Val>, t: Ty)
    ensures
        val_type(Val::List(s), Ty::List(Box::new(t))) <==> forall|k: int| 0 <= k < s.len() ==> #[trigger] val_type(s[k], t),
{
    list_type_iff(s, t, 0);
}

// ------------------------------------------------------------------ 環境

/// 実行時環境が型環境に適合する。
pub open spec fn env_ok(env: Map<nat, Val>, ctx: Map<nat, Ty>) -> bool {
    forall|x: nat| #[trigger] ctx.contains_key(x) ==> env.contains_key(x) && val_type(env[x], ctx[x])
}

pub proof fn env_ok_insert(env: Map<nat, Val>, ctx: Map<nat, Ty>, x: nat, v: Val, t: Ty)
    requires
        env_ok(env, ctx),
        val_type(v, t),
    ensures
        env_ok(env.insert(x, v), ctx.insert(x, t)),
{
    assert forall|y: nat| #[trigger] ctx.insert(x, t).contains_key(y) implies env.insert(x, v).contains_key(y)
        && val_type(env.insert(x, v)[y], ctx.insert(x, t)[y]) by {
        if y != x {
            assert(ctx.contains_key(y));
        }
    }
}

pub proof fn bind_ok(params: Seq<(nat, Ty)>, vs: Seq<Val>, n: nat)
    requires
        n <= params.len(),
        n <= vs.len(),
        forall|k: int| 0 <= k < n ==> val_type(#[trigger] vs[k], params[k].1),
    ensures
        env_ok(bind(params, vs, n), param_ctx(params, n)),
    decreases n,
{
    if n > 0 {
        bind_ok(params, vs, (n - 1) as nat);
        assert(val_type(vs[n - 1], params[n - 1].1));
        env_ok_insert(
            bind(params, vs, (n - 1) as nat),
            param_ctx(params, (n - 1) as nat),
            params[n - 1].0,
            vs[n - 1],
            params[n - 1].1,
        );
    }
}

// ------------------------------------------------------------------ 組込み

pub open spec fn max(a: nat, b: nat) -> nat {
    if a >= b { a } else { b }
}

/// 正の除数に対する剰余は非負で除数未満（§7.4 の mod）。
pub proof fn mod_bounds(x: int, y: int)
    requires
        y > 0,
    ensures
        0 <= x % y < y,
        x == y * (x / y) + x % y,
{
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(x, y);
    vstd::arithmetic::div_mod::lemma_mod_bound(x, y);
}

pub proof fn apply_sound(b: Builtin, ts: Seq<Ty>, vs: Seq<Val>)
    requires
        builtin_type(b, ts) is Some,
        vs.len() == ts.len(),
        forall|k: int| 0 <= k < vs.len() ==> val_type(#[trigger] vs[k], ts[k]),
    ensures
        apply(b, vs) is Done,
        val_type(apply(b, vs)->Done_0, builtin_type(b, ts)->Some_0),
{
    assert(val_type(vs[0], ts[0]));
    if vs.len() == 2 {
        assert(val_type(vs[1], ts[1]));
        match b {
            Builtin::Cons => {
                let s = vs[1]->List_0;
                let r = seq![vs[0]] + s;
                val_type_list(s, ts[0]);
                val_type_list(r, ts[0]);
                assert forall|i: int| 0 <= i < r.len() implies #[trigger] val_type(r[i], ts[0]) by {
                    if i > 0 {
                        assert(r[i] == s[i - 1]);
                    }
                }
            },
            Builtin::Concat => {
                let s = vs[0]->List_0;
                let u = vs[1]->List_0;
                let r = s + u;
                let te = *ts[0]->List_0;
                assert(ts[0] == Ty::List(Box::new(te)));
                val_type_list(s, te);
                val_type_list(u, te);
                val_type_list(r, te);
                assert forall|i: int| 0 <= i < r.len() implies #[trigger] val_type(r[i], te) by {
                    if i < s.len() {
                        assert(r[i] == s[i]);
                    } else {
                        assert(r[i] == u[i - s.len()]);
                    }
                }
            },
            Builtin::Add | Builtin::Sub | Builtin::Mul => {
                assert(vs[0] is Int && vs[1] is Int);
            },
            Builtin::Lt | Builtin::Le | Builtin::Eq => {},
            Builtin::Mod => {
                assert(vs[0] is Int && vs[1] is Int);
                assert(val_type(Val::Int(vs[0]->Int_0 % vs[1]->Int_0), Ty::Int));
            },
            _ => {},
        }
    } else {
        match b {
            Builtin::Neg => {
                assert(vs[0] is Int);
            },
            Builtin::Fst => {
                assert(vs[0] is Pair);
                assert(val_type(*vs[0]->Pair_0, *ts[0]->Pair_0));
            },
            Builtin::Snd => {
                assert(vs[0] is Pair);
                assert(val_type(*vs[0]->Pair_1, *ts[0]->Pair_1));
            },
            Builtin::Length => {
                assert(vs[0] is List);
            },
            Builtin::Uncons => {
                let s = vs[0]->List_0;
                let te = *ts[0]->List_0;
                assert(ts[0] == Ty::List(Box::new(te)));
                val_type_list(s, te);
                if s.len() > 0 {
                    let u = s.drop_first();
                    val_type_list(u, te);
                    assert forall|i: int| 0 <= i < u.len() implies #[trigger] val_type(u[i], te) by {
                        assert(u[i] == s[i + 1]);
                    }
                    assert(val_type(s[0], te));
                    assert(val_type(Val::List(u), ts[0]));
                }
            },
            Builtin::Reverse => {
                let s = vs[0]->List_0;
                let r = rev(s);
                let te = *ts[0]->List_0;
                assert(ts[0] == Ty::List(Box::new(te)));
                val_type_list(s, te);
                val_type_list(r, te);
                assert forall|i: int| 0 <= i < r.len() implies #[trigger] val_type(r[i], te) by {
                    assert(r[i] == s[s.len() - 1 - i]);
                }
            },
            _ => {},
        }
    }
}

// ------------------------------------------------------------------ 停止性と型安全性

/// 型の付いた式は、適合する環境で必ず値に評価され、その値は式の型を持つ。
/// 証拠として燃料と値を返す。帰納法は（ランク、式、0）の辞書式順序。
#[verifier::rlimit(100)]
pub proof fn total(p: Prog, r: nat, ctx: Map<nat, Ty>, env: Map<nat, Val>, e: Expr) -> (res: (nat, Val))
    requires
        wf(p),
        env_ok(env, ctx),
        ty_expr(p, r, ctx, e) is Some,
    ensures
        eval(p, res.0, env, e) == Res::Done(res.1),
        val_type(res.1, ty_expr(p, r, ctx, e)->Some_0),
    decreases r, e, 0nat,
{
    match e {
        Expr::Int(n) => (1, Val::Int(n)),
        Expr::Bool(b) => (1, Val::Bool(b)),
        Expr::Unit => (1, Val::Unit),
        Expr::None(_) => (1, Val::None),
        Expr::Var(x) => {
            assert(ctx.contains_key(x));
            (1, env[x])
        },
        Expr::List(t, es) => {
            let (n, vs) = total_args(p, r, ctx, env, es, 0);
            let ts = ty_args(p, r, ctx, es, 0)->Some_0;
            assert forall|i: int| 0 <= i < vs.len() implies #[trigger] val_type(vs[i], t) by {
                assert(ts[i] == t);
            }
            val_type_list(vs, t);
            (n + 1, Val::List(vs))
        },
        Expr::Some(x) => {
            let (n, v) = total(p, r, ctx, env, *x);
            (n + 1, Val::Some(Box::new(v)))
        },
        Expr::Pair(a, b) => {
            let (n1, va) = total(p, r, ctx, env, *a);
            let (n2, vb) = total(p, r, ctx, env, *b);
            let n = max(n1, n2);
            mono(p, n1, n, env, *a);
            mono(p, n2, n, env, *b);
            (n + 1, Val::Pair(Box::new(va), Box::new(vb)))
        },
        Expr::Builtin(b, es) => {
            let (n, vs) = total_args(p, r, ctx, env, es, 0);
            let ts = ty_args(p, r, ctx, es, 0)->Some_0;
            apply_sound(b, ts, vs);
            (n + 1, apply(b, vs)->Done_0)
        },
        Expr::Call(g, es) => {
            let (n1, vs) = total_args(p, r, ctx, env, es, 0);
            let ts = ty_args(p, r, ctx, es, 0)->Some_0;
            let fun = p.funcs[g as int];
            assert forall|k: int| 0 <= k < vs.len() implies val_type(#[trigger] vs[k], fun.params[k].1) by {
                assert(ts[k] == fun.params[k].1);
            }
            bind_ok(fun.params, vs, vs.len());
            let ctx2 = param_ctx(fun.params, fun.params.len());
            let env2 = bind(fun.params, vs, vs.len());
            assert(ty_expr(p, p.rank[g as int], ctx2, fun.body) == Some(fun.ret));
            let (n2, w) = total(p, p.rank[g as int], ctx2, env2, fun.body);
            let n = max(n1, n2);
            mono_args(p, n1, n, env, es, 0);
            mono(p, n2, n, env2, fun.body);
            (n + 1, w)
        },
        Expr::Let(x, a, b) => {
            let (n1, va) = total(p, r, ctx, env, *a);
            let ta = ty_expr(p, r, ctx, *a)->Some_0;
            env_ok_insert(env, ctx, x, va, ta);
            let (n2, vb) = total(p, r, ctx.insert(x, ta), env.insert(x, va), *b);
            let n = max(n1, n2);
            mono(p, n1, n, env, *a);
            mono(p, n2, n, env.insert(x, va), *b);
            (n + 1, vb)
        },
        Expr::If(c, a, b) => {
            let (n1, vc) = total(p, r, ctx, env, *c);
            let (n2, v) = if vc == Val::Bool(true) {
                total(p, r, ctx, env, *a)
            } else {
                total(p, r, ctx, env, *b)
            };
            let n = max(n1, n2);
            mono(p, n1, n, env, *c);
            mono(p, n2, n, env, *a);
            mono(p, n2, n, env, *b);
            (n + 1, v)
        },
        Expr::Fold(xs, init, acc, item, body) => {
            let (n1, vx) = total(p, r, ctx, env, *xs);
            let (n2, v0) = total(p, r, ctx, env, *init);
            let tx = ty_expr(p, r, ctx, *xs)->Some_0;
            let ta = ty_expr(p, r, ctx, *init)->Some_0;
            let te = *tx->List_0;
            let s = vx->List_0;
            assert(tx == Ty::List(Box::new(te)));
            val_type_list(s, te);
            let (n3, w) = total_fold(p, r, ctx, env, acc, item, *body, ta, te, s, 0, v0);
            let n = max(max(n1, n2), n3);
            mono(p, n1, n, env, *xs);
            mono(p, n2, n, env, *init);
            mono_fold(p, n3, n, env, acc, item, *body, s, 0, v0);
            (n + 1, w)
        },
        Expr::Match(m, nb, x, sm) => {
            let (n1, vm) = total(p, r, ctx, env, *m);
            let tm = ty_expr(p, r, ctx, *m)->Some_0;
            let te = *tm->Option_0;
            assert(tm == Ty::Option(Box::new(te)));
            match vm {
                Val::Some(v) => {
                    env_ok_insert(env, ctx, x, *v, te);
                    let (n2, w) = total(p, r, ctx.insert(x, te), env.insert(x, *v), *sm);
                    let n = max(n1, n2);
                    mono(p, n1, n, env, *m);
                    mono(p, n2, n, env.insert(x, *v), *sm);
                    (n + 1, w)
                },
                _ => {
                    assert(vm is None);
                    let (n2, w) = total(p, r, ctx, env, *nb);
                    let n = max(n1, n2);
                    mono(p, n1, n, env, *m);
                    mono(p, n2, n, env, *nb);
                    (n + 1, w)
                },
            }
        },
    }
}

pub proof fn total_args(p: Prog, r: nat, ctx: Map<nat, Ty>, env: Map<nat, Val>, es: Seq<Expr>, i: nat) -> (res: (
    nat,
    Seq<Val>,
))
    requires
        wf(p),
        env_ok(env, ctx),
        ty_args(p, r, ctx, es, i) is Some,
    ensures
        eval_args(p, res.0, env, es, i) == ResSeq::Done(res.1),
        res.1.len() == ty_args(p, r, ctx, es, i)->Some_0.len(),
        forall|k: int| 0 <= k < res.1.len() ==> val_type(#[trigger] res.1[k], ty_args(p, r, ctx, es, i)->Some_0[k]),
    decreases r, es, es.len() - i,
{
    if i >= es.len() {
        (1, Seq::empty())
    } else {
        let (n1, v) = total(p, r, ctx, env, es[i as int]);
        let (n2, vs) = total_args(p, r, ctx, env, es, i + 1);
        let n = max(n1, n2);
        mono(p, n1, n, env, es[i as int]);
        mono_args(p, n2, n, env, es, i + 1);
        let out = seq![v] + vs;
        let ts = ty_args(p, r, ctx, es, i)->Some_0;
        let t0 = ty_expr(p, r, ctx, es[i as int])->Some_0;
        let ts1 = ty_args(p, r, ctx, es, i + 1)->Some_0;
        assert(ts == seq![t0] + ts1);
        assert forall|k: int| 0 <= k < out.len() implies val_type(#[trigger] out[k], ts[k]) by {
            if k > 0 {
                assert(out[k] == vs[k - 1]);
                assert(ts[k] == ts1[k - 1]);
            }
        }
        (n + 1, out)
    }
}

pub proof fn total_fold(
    p: Prog,
    r: nat,
    ctx: Map<nat, Ty>,
    env: Map<nat, Val>,
    acc: nat,
    item: nat,
    body: Expr,
    ta: Ty,
    te: Ty,
    items: Seq<Val>,
    j: nat,
    a: Val,
) -> (res: (nat, Val))
    requires
        wf(p),
        env_ok(env, ctx),
        ty_expr(p, r, ctx.insert(acc, ta).insert(item, te), body) == Some(ta),
        val_type(a, ta),
        forall|k: int| 0 <= k < items.len() ==> val_type(#[trigger] items[k], te),
    ensures
        eval_fold(p, res.0, env, acc, item, body, items, j, a) == Res::Done(res.1),
        val_type(res.1, ta),
    decreases r, body, items.len() - j,
{
    if j >= items.len() {
        (1, a)
    } else {
        let x = items[j as int];
        env_ok_insert(env, ctx, acc, a, ta);
        env_ok_insert(env.insert(acc, a), ctx.insert(acc, ta), item, x, te);
        let env2 = env.insert(acc, a).insert(item, x);
        let (n1, v) = total(p, r, ctx.insert(acc, ta).insert(item, te), env2, body);
        let (n2, w) = total_fold(p, r, ctx, env, acc, item, body, ta, te, items, j + 1, v);
        let n = max(n1, n2);
        mono(p, n1, n, env2, body);
        mono_fold(p, n2, n, env, acc, item, body, items, j + 1, v);
        (n + 1, w)
    }
}

// ------------------------------------------------------------------ 主定理

/// 整形式プログラムの entry は、入力型の任意の値に対して停止し、出力型の値を返す。
pub proof fn entry_total(p: Prog, v: Val)
    requires
        wf(p),
        val_type(v, p.funcs[p.entry as int].params[0].1),
    ensures
        exists|n: nat, w: Val|
            #![trigger eval_entry(p, n, v), val_type(w, p.funcs[p.entry as int].ret)]
            eval_entry(p, n, v) == Res::Done(w) && val_type(w, p.funcs[p.entry as int].ret),
{
    let f = p.funcs[p.entry as int];
    bind_ok(f.params, seq![v], 1);
    let ctx = param_ctx(f.params, f.params.len());
    assert(ty_expr(p, p.rank[p.entry as int], ctx, f.body) == Some(f.ret));
    let (n, w) = total(p, p.rank[p.entry as int], ctx, bind(f.params, seq![v], 1), f.body);
    assert(eval_entry(p, n, v) == Res::Done(w));
}

/// entry の結果は燃料に依らず一意。
pub proof fn entry_deterministic(p: Prog, n: nat, m: nat, v: Val)
    ensures
        !(eval_entry(p, n, v) is OutOfFuel) && !(eval_entry(p, m, v) is OutOfFuel) ==> eval_entry(p, n, v)
            == eval_entry(p, m, v),
{
    let f = p.funcs[p.entry as int];
    eval_deterministic(p, n, m, bind(f.params, seq![v], 1), f.body);
}

} // verus!

verus! {

// ------------------------------------------------------------------ 非空虚性の確認

/// `wf` が充足可能であることの具体例：`fn twice(x: Int) -> Int { add(x, x) }`、
/// `fn main(x: Int) -> Int { twice(x) }`、`entry main`。
pub open spec fn example() -> Prog {
    let twice = Func {
        params: seq![(0nat, Ty::Int)],
        ret: Ty::Int,
        body: Expr::Builtin(Builtin::Add, seq![Expr::Var(0), Expr::Var(0)]),
    };
    let main = Func { params: seq![(0nat, Ty::Int)], ret: Ty::Int, body: Expr::Call(0, seq![Expr::Var(0)]) };
    Prog { funcs: seq![twice, main], rank: seq![0nat, 1nat], entry: 1 }
}

pub proof fn example_wf()
    ensures
        wf(example()),
        eval_entry(example(), 10, Val::Int(21)) == Res::Done(Val::Int(42)),
{
    let p = example();
    let ctx = param_ctx(p.funcs[0].params, 1);
    assert(ctx.contains_key(0) && ctx[0] == Ty::Int);
    assert(ty_expr(p, 0, ctx, Expr::Var(0)) == Some(Ty::Int));
    assert(ty_expr(p, 1, ctx, Expr::Var(0)) == Some(Ty::Int));
    assert(seq![Expr::Var(0), Expr::Var(0)][1] == Expr::Var(0));
    assert(ty_args(p, 0, ctx, seq![Expr::Var(0), Expr::Var(0)], 2) == Some(Seq::<Ty>::empty()));
    assert(seq![Ty::Int] + Seq::<Ty>::empty() =~= seq![Ty::Int]);
    assert(seq![Ty::Int] + seq![Ty::Int] =~= seq![Ty::Int, Ty::Int]);
    assert(ty_args(p, 0, ctx, seq![Expr::Var(0), Expr::Var(0)], 1) == Some(seq![Ty::Int]));
    assert(ty_args(p, 0, ctx, seq![Expr::Var(0), Expr::Var(0)], 0) == Some(seq![Ty::Int, Ty::Int]));
    assert(ty_args(p, 1, ctx, seq![Expr::Var(0)], 1) == Some(Seq::<Ty>::empty()));
    assert(ty_args(p, 1, ctx, seq![Expr::Var(0)], 0) == Some(seq![Ty::Int]));
    assert forall|g: int| 0 <= g < p.funcs.len() implies #[trigger] ty_expr(
        p,
        p.rank[g],
        param_ctx(p.funcs[g].params, p.funcs[g].params.len()),
        p.funcs[g].body,
    ) == Some(p.funcs[g].ret) by {}
    reveal_with_fuel(eval, 6);
    reveal_with_fuel(eval_args, 6);
}

} // verus!
