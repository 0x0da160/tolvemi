//! sort_by の意味（段階 1b・SH1 の第三部）。
//!
//! 核の書換え sort_collect は、外側の畳み込みで要素 e を一つずつ取り、内側の畳み込みで整列済みの列へ
//! 挿入し、最後に reverse で向きを戻す形である。内側の本体 sort_inner は、鍵の枠・出力・置いたかどうかの
//! 状態を項ごとに更新する。書換えの値は sortspec.rs の sort_vals（挿入の手順、OD-3）に一致する。
//! 源の SortBy（xsem.rs）も同じ値になり、型は書換えの型と一致する。
//! 鍵の式 k は、束縛の名前 acc・e・st・y を含まない（absent）ことを仮定する。束縛の新しさは names_ok で仮定する。

use crate::bigstep::*;
use crate::fold_meaning::*;
use crate::proof::*;
use crate::records_proof::*;
use crate::sortspec::*;
use crate::spec::*;
use crate::xmeaning::*;
use crate::xsem::*;
use crate::xtyping::*;
use vstd::prelude::*;

verus! {

// ------------------------------------------------------------------ 式の組み立て

pub open spec fn pfst(e: Expr) -> Expr {
    Expr::Builtin(Builtin::Fst, seq![e])
}

pub open spec fn psnd(e: Expr) -> Expr {
    Expr::Builtin(Builtin::Snd, seq![e])
}

pub open spec fn cons_e(a: Expr, b: Expr) -> Expr {
    Expr::Builtin(Builtin::Cons, seq![a, b])
}

pub open spec fn pair_e(a: Expr, b: Expr) -> Expr {
    Expr::Pair(Box::new(a), Box::new(b))
}

/// 内側の畳み込みの状態の型：(鍵の枠, (出力, 置いたか))。
pub open spec fn state_ty(s: Ty) -> Ty {
    Ty::Pair(
        Box::new(Ty::Option(Box::new(Ty::Int))),
        Box::new(Ty::Pair(Box::new(Ty::List(Box::new(s))), Box::new(Ty::Bool))),
    )
}

/// 内側の畳み込みの初期状態：(None, ([], false))。
pub open spec fn init_state(t: Ty) -> Expr {
    pair_e(Expr::None(Ty::Int), pair_e(Expr::List(t, Seq::empty()), Expr::Bool(false)))
}

/// 状態の置いたかどうか。
pub open spec fn sort_cond(st: nat) -> Expr {
    psnd(psnd(Expr::Var(st)))
}

/// 置いた後：出力に項 y を積み、置いたままにする。
pub open spec fn sort_placed(st: nat, y: nat) -> Expr {
    pair_e(pfst(Expr::Var(st)), pair_e(cons_e(Expr::Var(y), pfst(psnd(Expr::Var(st)))), Expr::Bool(true)))
}

/// まだ置いていない（鍵の比較が真）：項 y の前に e を置く。
pub open spec fn sort_before(e: nat, st: nat, y: nat) -> Expr {
    pair_e(
        pfst(Expr::Var(st)),
        pair_e(cons_e(Expr::Var(y), cons_e(Expr::Var(e), pfst(psnd(Expr::Var(st))))), Expr::Bool(true)),
    )
}

/// まだ置いていない（鍵の比較が偽）：項 y を積むだけ。
pub open spec fn sort_after(st: nat, y: nat) -> Expr {
    pair_e(pfst(Expr::Var(st)), pair_e(cons_e(Expr::Var(y), pfst(psnd(Expr::Var(st)))), Expr::Bool(false)))
}

pub open spec fn sort_lt(e: nat, st: nat, y: nat, ky: nat, ke: nat) -> Expr {
    Expr::If(
        Box::new(Expr::Builtin(Builtin::Lt, seq![Expr::Var(ke), Expr::Var(ky)])),
        Box::new(sort_before(e, st, y)),
        Box::new(sort_after(st, y)),
    )
}

/// 枠が None なら、e の鍵 ky を枠に残す。Some なら鍵を比べる。
pub open spec fn sort_match(e: nat, st: nat, y: nat, ky: nat, ke: nat) -> Expr {
    Expr::Match(
        Box::new(pfst(Expr::Var(st))),
        Box::new(pair_e(Expr::Some(Box::new(Expr::Var(ky))), psnd(Expr::Var(st)))),
        ke,
        Box::new(sort_lt(e, st, y, ky, ke)),
    )
}

/// 置いていない場合：項 y の鍵を求めてから比べる。
pub open spec fn sort_fresh(e: nat, st: nat, y: nat, ky: nat, ke: nat, x: nat, k: Expr) -> Expr {
    Expr::Let(
        ky,
        Box::new(Expr::Let(x, Box::new(Expr::Var(y)), Box::new(k))),
        Box::new(sort_match(e, st, y, ky, ke)),
    )
}

/// 内側の本体：状態 st に項 y を一つ処理する。鍵は k を x に束縛して求める。
pub open spec fn sort_inner(e: nat, st: nat, y: nat, ky: nat, ke: nat, x: nat, k: Expr) -> Expr {
    Expr::If(
        Box::new(sort_cond(st)),
        Box::new(sort_placed(st, y)),
        Box::new(sort_fresh(e, st, y, ky, ke, x, k)),
    )
}

/// 置いたかどうかで出力の向きをそろえる（置いていなければ e を末尾に足す）。
pub open spec fn sort_rev(e: nat, rb: nat) -> Expr {
    Expr::If(
        Box::new(psnd(psnd(Expr::Var(rb)))),
        Box::new(pfst(psnd(Expr::Var(rb)))),
        Box::new(cons_e(Expr::Var(e), pfst(psnd(Expr::Var(rb))))),
    )
}

/// 外側の本体：要素 e を、内側の畳み込みで整列済みの列 acc へ挿入し、reverse で向きを戻す。
pub open spec fn sort_body(t: Ty, acc: nat, e: nat, st: nat, y: nat, ky: nat, ke: nat, rb: nat, x: nat, k: Expr) -> Expr {
    Expr::Let(
        rb,
        Box::new(Expr::Fold(
            Box::new(cons_e(Expr::Var(e), Expr::Var(acc))),
            Box::new(init_state(t)),
            st,
            y,
            Box::new(sort_inner(e, st, y, ky, ke, x, k)),
        )),
        Box::new(Expr::Builtin(Builtin::Reverse, seq![sort_rev(e, rb)])),
    )
}

/// sort_by の核の書換え：fold(xs, [], |acc, e| sort_body)。
pub open spec fn sort_collect(
    xs: Expr,
    t: Ty,
    acc: nat,
    e: nat,
    st: nat,
    y: nat,
    ky: nat,
    ke: nat,
    rb: nat,
    x: nat,
    k: Expr,
) -> Expr {
    Expr::Fold(
        Box::new(xs),
        Box::new(Expr::List(t, Seq::empty())),
        acc,
        e,
        Box::new(sort_body(t, acc, e, st, y, ky, ke, rb, x, k)),
    )
}

/// 束縛の名前が互いに異なる（内側の本体に要る分）。
pub open spec fn names_inner(acc: nat, e: nat, st: nat, y: nat, ky: nat, ke: nat, x: nat) -> bool {
    acc != e && acc != x && e != st && e != y && e != ky && e != ke && e != x && st != y && st != ky && st != ke
        && st != x && y != ky && y != ke && y != x && ky != ke
}

/// 束縛の名前が互いに異なる（外側の rb を含む）。
pub open spec fn names_ok(acc: nat, e: nat, st: nat, y: nat, ky: nat, ke: nat, rb: nat, x: nat) -> bool {
    names_inner(acc, e, st, y, ky, ke, x) && e != rb
}

/// 鍵の式は、列 s の各要素について、その鍵に評価される（x に要素の値を束縛して）。
pub open spec fn keyed(p: Prog, env: Map<nat, Val>, x: nat, k: Expr, s: Seq<(Val, int)>) -> bool {
    forall|m: int| 0 <= m < s.len() ==> evals_to(p, #[trigger] env.insert(x, s[m].0), k, Val::Int(s[m].1))
}

// ------------------------------------------------------------------ 評価の部品

/// 引数が一つの列：e が v に評価されれば、(e) は (v) に評価される。
proof fn args_one(p: Prog, env: Map<nat, Val>, e: Expr, v: Val)
    requires
        evals_to(p, env, e, v),
    ensures
        args_to(p, env, seq![e], 0, seq![v]),
{
    let es = seq![e];
    let vs = seq![v];
    assert forall|j: int| 0 <= j < es.len() implies evals_to(p, env, #[trigger] es[j], vs[j]) by {
        assert(es[j] == e && vs[j] == v);
    }
    args_from_each(p, env, es, vs, 0);
    assert(vs.subrange(0, vs.len() as int) =~= vs);
}

/// 引数が二つの列。
proof fn args_two(p: Prog, env: Map<nat, Val>, e1: Expr, e2: Expr, v1: Val, v2: Val)
    requires
        evals_to(p, env, e1, v1),
        evals_to(p, env, e2, v2),
    ensures
        args_to(p, env, seq![e1, e2], 0, seq![v1, v2]),
{
    let es = seq![e1, e2];
    let vs = seq![v1, v2];
    assert forall|j: int| 0 <= j < es.len() implies evals_to(p, env, #[trigger] es[j], vs[j]) by {
        if j == 0 {
            assert(es[j] == e1 && vs[j] == v1);
        } else {
            assert(es[j] == e2 && vs[j] == v2);
        }
    }
    args_from_each(p, env, es, vs, 0);
    assert(vs.subrange(0, vs.len() as int) =~= vs);
}

/// 一項の組み込みの評価。
proof fn bs_unary(p: Prog, env: Map<nat, Val>, b: Builtin, e: Expr, v: Val, w: Val)
    requires
        evals_to(p, env, e, v),
        apply(b, seq![v]) == Res::Done(w),
    ensures
        evals_to(p, env, Expr::Builtin(b, seq![e]), w),
{
    args_one(p, env, e, v);
    bs_builtin(p, env, b, seq![e], seq![v], w);
}

/// 二項の組み込みの評価。
proof fn bs_binary(p: Prog, env: Map<nat, Val>, b: Builtin, e1: Expr, e2: Expr, v1: Val, v2: Val, w: Val)
    requires
        evals_to(p, env, e1, v1),
        evals_to(p, env, e2, v2),
        apply(b, seq![v1, v2]) == Res::Done(w),
    ensures
        evals_to(p, env, Expr::Builtin(b, seq![e1, e2]), w),
{
    args_two(p, env, e1, e2, v1, v2);
    bs_builtin(p, env, b, seq![e1, e2], seq![v1, v2], w);
}

/// 状態の変数の取り出し：env[st] が (a, (lst, pl)) なら、枠・出力・置いたかどうかが取り出せる。
proof fn state_parts(p: Prog, env: Map<nat, Val>, st: nat, a: Val, lst: Seq<Val>, pl: bool)
    requires
        env.contains_key(st),
        env[st] == Val::Pair(Box::new(a), Box::new(Val::Pair(Box::new(Val::List(lst)), Box::new(Val::Bool(pl))))),
    ensures
        evals_to(p, env, pfst(Expr::Var(st)), a),
        evals_to(p, env, psnd(Expr::Var(st)), Val::Pair(Box::new(Val::List(lst)), Box::new(Val::Bool(pl)))),
        evals_to(p, env, pfst(psnd(Expr::Var(st))), Val::List(lst)),
        evals_to(p, env, psnd(psnd(Expr::Var(st))), Val::Bool(pl)),
{
    let rest = Val::Pair(Box::new(Val::List(lst)), Box::new(Val::Bool(pl)));
    let sv = env[st];
    bs_var(p, env, st);
    assert(apply(Builtin::Fst, seq![sv]) == Res::Done(a));
    bs_unary(p, env, Builtin::Fst, Expr::Var(st), sv, a);
    assert(apply(Builtin::Snd, seq![sv]) == Res::Done(rest));
    bs_unary(p, env, Builtin::Snd, Expr::Var(st), sv, rest);
    assert(apply(Builtin::Fst, seq![rest]) == Res::Done(Val::List(lst)));
    bs_unary(p, env, Builtin::Fst, psnd(Expr::Var(st)), rest, Val::List(lst));
    assert(apply(Builtin::Snd, seq![rest]) == Res::Done(Val::Bool(pl)));
    bs_unary(p, env, Builtin::Snd, psnd(Expr::Var(st)), rest, Val::Bool(pl));
}

/// 鍵の式は、束縛 acc・e・st・y を含まないので、それらを加えても同じ値に評価される。
proof fn key_env(
    p: Prog,
    env: Map<nat, Val>,
    acc: nat,
    a: Val,
    e: nat,
    ev: Val,
    st: nat,
    sv: Val,
    y: nat,
    yv: Val,
    x: nat,
    k: Expr,
    w: Val,
)
    requires
        acc != x,
        e != x,
        st != x,
        y != x,
        absent(acc, k),
        absent(e, k),
        absent(st, k),
        absent(y, k),
        evals_to(p, env.insert(x, yv), k, w),
    ensures
        evals_to(p, env.insert(acc, a).insert(e, ev).insert(st, sv).insert(y, yv).insert(x, yv), k, w),
{
    evals_absent_ins(p, env, k, acc, a, x, yv, w);
    evals_absent_ins(p, env.insert(acc, a), k, e, ev, x, yv, w);
    evals_absent_ins(p, env.insert(acc, a).insert(e, ev), k, st, sv, x, yv, w);
    evals_absent_ins(p, env.insert(acc, a).insert(e, ev).insert(st, sv), k, y, yv, x, yv, w);
}

/// 初期状態の評価：(None, ([], false))。
proof fn init_eval(p: Prog, env: Map<nat, Val>, t: Ty)
    ensures
        evals_to(
            p,
            env,
            init_state(t),
            Val::Pair(Box::new(Val::None), Box::new(Val::Pair(Box::new(Val::List(Seq::empty())), Box::new(Val::Bool(false))))),
        ),
{
    bs_leaf(p, env, Expr::None(Ty::Int));
    bs_nil(p, env, t);
    bs_leaf(p, env, Expr::Bool(false));
    bs_pair(
        p,
        env,
        Expr::List(t, Seq::empty()),
        Expr::Bool(false),
        Val::List(Seq::empty()),
        Val::Bool(false),
    );
    bs_pair(
        p,
        env,
        Expr::None(Ty::Int),
        pair_e(Expr::List(t, Seq::empty()), Expr::Bool(false)),
        Val::None,
        Val::Pair(Box::new(Val::List(Seq::empty())), Box::new(Val::Bool(false))),
    );
}

// ------------------------------------------------------------------ 内側の一段

/// 内側の一段（最初の項は e 自身）：状態は初期状態で、e の鍵 ep.1 を枠に残す。
proof fn inner_zero(
    p: Prog,
    env: Map<nat, Val>,
    acc: nat,
    a: Val,
    ep: (Val, int),
    s: Seq<(Val, int)>,
    e: nat,
    st: nat,
    y: nat,
    ky: nat,
    ke: nat,
    x: nat,
    k: Expr,
)
    requires
        names_inner(acc, e, st, y, ky, ke, x),
        absent(acc, k),
        absent(e, k),
        absent(st, k),
        absent(y, k),
        evals_to(p, env.insert(x, ep.0), k, Val::Int(ep.1)),
    ensures
        evals_to(
            p,
            env.insert(acc, a).insert(e, ep.0).insert(st, inner_val(ep, s, 0)).insert(y, ep.0),
            sort_inner(e, st, y, ky, ke, x, k),
            inner_val(ep, s, 1),
        ),
{
    reveal_with_fuel(out_ins, 1);
    let emp = Val::List(Seq::<Val>::empty());
    let st0 = inner_val(ep, s, 0);
    let env_b = env.insert(acc, a).insert(e, ep.0).insert(st, st0).insert(y, ep.0);
    let w = inner_val(ep, s, 1);
    assert(st0 == Val::Pair(Box::new(Val::None), Box::new(Val::Pair(Box::new(emp), Box::new(Val::Bool(false))))));
    assert(out_ins(ep, s, 0) == (Seq::<Val>::empty(), false));
    assert(w == Val::Pair(
        Box::new(Val::Some(Box::new(Val::Int(ep.1)))),
        Box::new(Val::Pair(Box::new(emp), Box::new(Val::Bool(false)))),
    ));
    assert(env_b.contains_key(st) && env_b[st] == st0);
    state_parts(p, env_b, st, Val::None, Seq::<Val>::empty(), false);
    key_env(p, env, acc, a, e, ep.0, st, st0, y, ep.0, x, k, Val::Int(ep.1));
    bs_var(p, env_b, y);
    bs_let(p, env_b, x, Expr::Var(y), k, ep.0, Val::Int(ep.1));
    let env_m = env_b.insert(ky, Val::Int(ep.1));
    assert(env_m.contains_key(st) && env_m[st] == st0);
    state_parts(p, env_m, st, Val::None, Seq::<Val>::empty(), false);
    assert(env_m.contains_key(ky) && env_m[ky] == Val::Int(ep.1));
    bs_var(p, env_m, ky);
    bs_some(p, env_m, Expr::Var(ky), Val::Int(ep.1));
    bs_pair(
        p,
        env_m,
        Expr::Some(Box::new(Expr::Var(ky))),
        psnd(Expr::Var(st)),
        Val::Some(Box::new(Val::Int(ep.1))),
        Val::Pair(Box::new(emp), Box::new(Val::Bool(false))),
    );
    bs_match(
        p,
        env_m,
        pfst(Expr::Var(st)),
        pair_e(Expr::Some(Box::new(Expr::Var(ky))), psnd(Expr::Var(st))),
        ke,
        sort_lt(e, st, y, ky, ke),
        Val::None,
        w,
    );
    bs_let(p, env_b, ky, Expr::Let(x, Box::new(Expr::Var(y)), Box::new(k)), sort_match(e, st, y, ky, ke), Val::Int(ep.1), w);
    bs_if(p, env_b, sort_cond(st), sort_placed(st, y), sort_fresh(e, st, y, ky, ke, x, k), false, w);
}

/// 内側の一段（項 s[q]）：状態は inner_val(ep, s, q + 1)。項の鍵は s[q].1。
proof fn inner_pos(
    p: Prog,
    env: Map<nat, Val>,
    acc: nat,
    a: Val,
    ep: (Val, int),
    s: Seq<(Val, int)>,
    q: nat,
    e: nat,
    st: nat,
    y: nat,
    ky: nat,
    ke: nat,
    x: nat,
    k: Expr,
)
    requires
        q < s.len(),
        names_inner(acc, e, st, y, ky, ke, x),
        absent(acc, k),
        absent(e, k),
        absent(st, k),
        absent(y, k),
        evals_to(p, env.insert(x, s[q as int].0), k, Val::Int(s[q as int].1)),
    ensures
        evals_to(
            p,
            env.insert(acc, a).insert(e, ep.0).insert(st, inner_val(ep, s, q + 1)).insert(y, s[q as int].0),
            sort_inner(e, st, y, ky, ke, x, k),
            inner_val(ep, s, q + 2),
        ),
{
    reveal_with_fuel(out_ins, 1);
    let t = s[q as int];
    let o = out_ins(ep, s, q).0;
    let pl = out_ins(ep, s, q).1;
    let stv = inner_val(ep, s, q + 1);
    let w = inner_val(ep, s, q + 2);
    let env_b = env.insert(acc, a).insert(e, ep.0).insert(st, stv).insert(y, t.0);
    assert(stv == Val::Pair(
        Box::new(Val::Some(Box::new(Val::Int(ep.1)))),
        Box::new(Val::Pair(Box::new(Val::List(o)), Box::new(Val::Bool(pl)))),
    ));
    assert(env_b.contains_key(st) && env_b[st] == stv);
    state_parts(p, env_b, st, Val::Some(Box::new(Val::Int(ep.1))), o, pl);
    assert(env_b.contains_key(e) && env_b[e] == ep.0);
    bs_var(p, env_b, y);
    bs_var(p, env_b, e);
    key_env(p, env, acc, a, e, ep.0, st, stv, y, t.0, x, k, Val::Int(t.1));
    if pl {
        assert(out_ins(ep, s, q + 1) == (seq![t.0] + o, true));
        assert(w == Val::Pair(
            Box::new(Val::Some(Box::new(Val::Int(ep.1)))),
            Box::new(Val::Pair(Box::new(Val::List(seq![t.0] + o)), Box::new(Val::Bool(true)))),
        ));
        bs_binary(
            p,
            env_b,
            Builtin::Cons,
            Expr::Var(y),
            pfst(psnd(Expr::Var(st))),
            t.0,
            Val::List(o),
            Val::List(seq![t.0] + o),
        );
        bs_leaf(p, env_b, Expr::Bool(true));
        bs_pair(
            p,
            env_b,
            cons_e(Expr::Var(y), pfst(psnd(Expr::Var(st)))),
            Expr::Bool(true),
            Val::List(seq![t.0] + o),
            Val::Bool(true),
        );
        bs_pair(
            p,
            env_b,
            pfst(Expr::Var(st)),
            pair_e(cons_e(Expr::Var(y), pfst(psnd(Expr::Var(st)))), Expr::Bool(true)),
            Val::Some(Box::new(Val::Int(ep.1))),
            Val::Pair(Box::new(Val::List(seq![t.0] + o)), Box::new(Val::Bool(true))),
        );
        bs_if(p, env_b, sort_cond(st), sort_placed(st, y), sort_fresh(e, st, y, ky, ke, x, k), true, w);
    } else {
        bs_let(p, env_b, x, Expr::Var(y), k, t.0, Val::Int(t.1));
        let env_m = env_b.insert(ky, Val::Int(t.1));
        assert(env_m.contains_key(st) && env_m[st] == stv);
        state_parts(p, env_m, st, Val::Some(Box::new(Val::Int(ep.1))), o, pl);
        assert(env_m.contains_key(ky) && env_m[ky] == Val::Int(t.1));
        let env_s = env_m.insert(ke, Val::Int(ep.1));
        assert(env_s.contains_key(ke) && env_s[ke] == Val::Int(ep.1));
        assert(env_s.contains_key(st) && env_s[st] == stv);
        assert(env_s.contains_key(e) && env_s[e] == ep.0);
        assert(env_s.contains_key(y) && env_s[y] == t.0);
        assert(env_s.contains_key(ky) && env_s[ky] == Val::Int(t.1));
        state_parts(p, env_s, st, Val::Some(Box::new(Val::Int(ep.1))), o, pl);
        bs_var(p, env_s, e);
        bs_var(p, env_s, y);
        bs_var(p, env_s, ke);
        bs_var(p, env_s, ky);
        bs_binary(
            p,
            env_s,
            Builtin::Lt,
            Expr::Var(ke),
            Expr::Var(ky),
            Val::Int(ep.1),
            Val::Int(t.1),
            Val::Bool(ep.1 < t.1),
        );
        if ep.1 < t.1 {
            assert(out_ins(ep, s, q + 1) == (seq![t.0, ep.0] + o, true));
            assert(w == Val::Pair(
                Box::new(Val::Some(Box::new(Val::Int(ep.1)))),
                Box::new(Val::Pair(Box::new(Val::List(seq![t.0, ep.0] + o)), Box::new(Val::Bool(true)))),
            ));
            assert(seq![t.0] + (seq![ep.0] + o) =~= seq![t.0, ep.0] + o);
            bs_binary(
                p,
                env_s,
                Builtin::Cons,
                Expr::Var(e),
                pfst(psnd(Expr::Var(st))),
                ep.0,
                Val::List(o),
                Val::List(seq![ep.0] + o),
            );
            bs_binary(
                p,
                env_s,
                Builtin::Cons,
                Expr::Var(y),
                cons_e(Expr::Var(e), pfst(psnd(Expr::Var(st)))),
                t.0,
                Val::List(seq![ep.0] + o),
                Val::List(seq![t.0] + (seq![ep.0] + o)),
            );
            bs_leaf(p, env_s, Expr::Bool(true));
            bs_pair(
                p,
                env_s,
                cons_e(Expr::Var(y), cons_e(Expr::Var(e), pfst(psnd(Expr::Var(st))))),
                Expr::Bool(true),
                Val::List(seq![t.0] + (seq![ep.0] + o)),
                Val::Bool(true),
            );
            bs_pair(
                p,
                env_s,
                pfst(Expr::Var(st)),
                pair_e(cons_e(Expr::Var(y), cons_e(Expr::Var(e), pfst(psnd(Expr::Var(st))))), Expr::Bool(true)),
                Val::Some(Box::new(Val::Int(ep.1))),
                Val::Pair(Box::new(Val::List(seq![t.0] + (seq![ep.0] + o))), Box::new(Val::Bool(true))),
            );
            bs_if(
                p,
                env_s,
                Expr::Builtin(Builtin::Lt, seq![Expr::Var(ke), Expr::Var(ky)]),
                sort_before(e, st, y),
                sort_after(st, y),
                true,
                w,
            );
        } else {
            assert(out_ins(ep, s, q + 1) == (seq![t.0] + o, false));
            assert(w == Val::Pair(
                Box::new(Val::Some(Box::new(Val::Int(ep.1)))),
                Box::new(Val::Pair(Box::new(Val::List(seq![t.0] + o)), Box::new(Val::Bool(false)))),
            ));
            bs_leaf(p, env_s, Expr::Bool(false));
            bs_binary(
                p,
                env_s,
                Builtin::Cons,
                Expr::Var(y),
                pfst(psnd(Expr::Var(st))),
                t.0,
                Val::List(o),
                Val::List(seq![t.0] + o),
            );
            bs_pair(
                p,
                env_s,
                cons_e(Expr::Var(y), pfst(psnd(Expr::Var(st)))),
                Expr::Bool(false),
                Val::List(seq![t.0] + o),
                Val::Bool(false),
            );
            bs_pair(
                p,
                env_s,
                pfst(Expr::Var(st)),
                pair_e(cons_e(Expr::Var(y), pfst(psnd(Expr::Var(st)))), Expr::Bool(false)),
                Val::Some(Box::new(Val::Int(ep.1))),
                Val::Pair(Box::new(Val::List(seq![t.0] + o)), Box::new(Val::Bool(false))),
            );
            bs_if(
                p,
                env_s,
                Expr::Builtin(Builtin::Lt, seq![Expr::Var(ke), Expr::Var(ky)]),
                sort_before(e, st, y),
                sort_after(st, y),
                false,
                w,
            );
        }
        bs_match(
            p,
            env_m,
            pfst(Expr::Var(st)),
            pair_e(Expr::Some(Box::new(Expr::Var(ky))), psnd(Expr::Var(st))),
            ke,
            sort_lt(e, st, y, ky, ke),
            Val::Some(Box::new(Val::Int(ep.1))),
            w,
        );
        bs_let(p, env_b, ky, Expr::Let(x, Box::new(Expr::Var(y)), Box::new(k)), sort_match(e, st, y, ky, ke), Val::Int(t.1), w);
        bs_if(p, env_b, sort_cond(st), sort_placed(st, y), sort_fresh(e, st, y, ky, ke, x, k), false, w);
    }
}

// ------------------------------------------------------------------ 鍵の列の保存

/// 挿入の結果も鍵の式は正しい（挿入した要素 e の鍵は仮定にある）。
proof fn keyed_ins(p: Prog, env: Map<nat, Val>, x: nat, k: Expr, s: Seq<(Val, int)>, e: (Val, int))
    requires
        keyed(p, env, x, k, s),
        evals_to(p, env.insert(x, e.0), k, Val::Int(e.1)),
    ensures
        keyed(p, env, x, k, ins_sorted(s, e)),
    decreases s.len(),
{
    reveal_with_fuel(ins_sorted, 2);
    let r = ins_sorted(s, e);
    if s.len() == 0 {
        assert(r =~= seq![e]);
        assert forall|m: int| 0 <= m < r.len() implies evals_to(p, #[trigger] env.insert(x, r[m].0), k, Val::Int(r[m].1)) by {
            assert(r[m] == e);
        }
    } else if e.1 < s[0].1 {
        assert(r =~= seq![e] + s);
        assert forall|m: int| 0 <= m < r.len() implies evals_to(p, #[trigger] env.insert(x, r[m].0), k, Val::Int(r[m].1)) by {
            if m == 0 {
                assert(r[m] == e);
            } else {
                assert(r[m] == s[m - 1]);
            }
        }
    } else {
        let d = s.drop_first();
        assert(s =~= seq![s[0]] + d);
        assert forall|m: int| 0 <= m < d.len() implies evals_to(p, #[trigger] env.insert(x, d[m].0), k, Val::Int(d[m].1)) by {
            assert(d[m] == s[m + 1]);
        }
        keyed_ins(p, env, x, k, d, e);
        assert(r =~= seq![s[0]] + ins_sorted(d, e));
        assert forall|m: int| 0 <= m < r.len() implies evals_to(p, #[trigger] env.insert(x, r[m].0), k, Val::Int(r[m].1)) by {
            if m == 0 {
                assert(r[m] == s[0]);
            } else {
                assert(r[m] == ins_sorted(d, e)[m - 1]);
            }
        }
    }
}

/// 整列の途中の列（先頭 i 個）も鍵の式は正しい。
pub proof fn keyed_prefix(p: Prog, env: Map<nat, Val>, x: nat, k: Expr, zp: Seq<(Val, int)>, i: nat)
    requires
        i <= zp.len(),
        keyed(p, env, x, k, zp),
    ensures
        keyed(p, env, x, k, sort_prefix(zp, i)),
    decreases i,
{
    reveal_with_fuel(sort_prefix, 2);
    if i > 0 {
        let q = (i - 1) as nat;
        keyed_prefix(p, env, x, k, zp, q);
        assert(evals_to(p, env.insert(x, zp[q as int].0), k, Val::Int(zp[q as int].1)));
        assert(sort_prefix(zp, i) == ins_sorted(sort_prefix(zp, q), zp[q as int]));
        keyed_ins(p, env, x, k, sort_prefix(zp, q), zp[q as int]);
    }
}

// ------------------------------------------------------------------ 外側の一段

/// 外側の一段（要素 zp[i]）：整列済みの列 s = sort_prefix(zp, i) へ zp[i] を挿入する。
pub proof fn outer_step(
    p: Prog,
    env: Map<nat, Val>,
    acc: nat,
    e: nat,
    st: nat,
    y: nat,
    ky: nat,
    ke: nat,
    rb: nat,
    x: nat,
    k: Expr,
    t: Ty,
    zp: Seq<(Val, int)>,
    i: nat,
)
    requires
        names_ok(acc, e, st, y, ky, ke, rb, x),
        absent(acc, k),
        absent(e, k),
        absent(st, k),
        absent(y, k),
        i < zp.len(),
        keyed(p, env, x, k, zp),
        keyed(p, env, x, k, sort_prefix(zp, i)),
    ensures
        evals_to(
            p,
            env.insert(acc, Val::List(pvals(sort_prefix(zp, i)))).insert(e, zp[i as int].0),
            sort_body(t, acc, e, st, y, ky, ke, rb, x, k),
            Val::List(pvals(sort_prefix(zp, i + 1))),
        ),
{
    reveal_with_fuel(sort_prefix, 2);
    reveal_with_fuel(out_ins, 1);
    let ep = zp[i as int];
    let s = sort_prefix(zp, i);
    let m = s.len();
    let accv = Val::List(pvals(s));
    let env_o = env.insert(acc, accv).insert(e, ep.0);
    let zs = seq![ep.0] + pvals(s);
    let innerv = Seq::new((m + 2) as nat, |j: int| inner_val(ep, s, j as nat));
    let fe = Expr::Fold(
        Box::new(cons_e(Expr::Var(e), Expr::Var(acc))),
        Box::new(init_state(t)),
        st,
        y,
        Box::new(sort_inner(e, st, y, ky, ke, x, k)),
    );
    assert(zs.len() == m + 1);
    assert(sort_prefix(zp, i + 1) == ins_sorted(s, ep));
    assert(evals_to(p, env.insert(x, ep.0), k, Val::Int(ep.1)));
    assert(env_o.contains_key(acc) && env_o[acc] == accv);
    assert(env_o.contains_key(e) && env_o[e] == ep.0);
    bs_var(p, env_o, e);
    bs_var(p, env_o, acc);
    assert(apply(Builtin::Cons, seq![ep.0, accv]) == Res::Done(Val::List(zs)));
    bs_binary(p, env_o, Builtin::Cons, Expr::Var(e), Expr::Var(acc), ep.0, accv, Val::List(zs));
    init_eval(p, env_o, t);
    assert(innerv.len() == zs.len() + 1);
    assert(innerv[0] == inner_val(ep, s, 0));
    assert forall|j: int| 0 <= j < zs.len() implies evals_to(
        p,
        env_o.insert(st, innerv[j]).insert(y, zs[j]),
        sort_inner(e, st, y, ky, ke, x, k),
        innerv[j + 1],
    ) by {
        if j == 0 {
            assert(zs[0] == ep.0);
            assert(innerv[0] == inner_val(ep, s, 0));
            assert(innerv[1] == inner_val(ep, s, 1));
            inner_zero(p, env, acc, accv, ep, s, e, st, y, ky, ke, x, k);
        } else {
            let q = (j - 1) as nat;
            assert(zs[j] == s[q as int].0);
            assert(innerv[j] == inner_val(ep, s, q + 1));
            assert(innerv[j + 1] == inner_val(ep, s, q + 2));
            assert(evals_to(p, env.insert(x, s[q as int].0), k, Val::Int(s[q as int].1)));
            inner_pos(p, env, acc, accv, ep, s, q, e, st, y, ky, ke, x, k);
        }
    }
    fold_expr_to(
        p,
        env_o,
        cons_e(Expr::Var(e), Expr::Var(acc)),
        init_state(t),
        st,
        y,
        sort_inner(e, st, y, ky, ke, x, k),
        zs,
        innerv,
    );
    assert(innerv[zs.len() as int] == inner_val(ep, s, (m + 1) as nat));
    let vr = inner_val(ep, s, (m + 1) as nat);
    let o = out_ins(ep, s, m).0;
    let pl = out_ins(ep, s, m).1;
    assert(vr == Val::Pair(
        Box::new(Val::Some(Box::new(Val::Int(ep.1)))),
        Box::new(Val::Pair(Box::new(Val::List(o)), Box::new(Val::Bool(pl)))),
    ));
    out_ins_inv(ep, s, m);
    assert(s.subrange(0, m as int) =~= s);
    let env_r = env_o.insert(rb, vr);
    assert(env_r.contains_key(rb) && env_r[rb] == vr);
    state_parts(p, env_r, rb, Val::Some(Box::new(Val::Int(ep.1))), o, pl);
    assert(env_r.contains_key(e) && env_r[e] == ep.0);
    bs_var(p, env_r, e);
    if pl {
        bs_if(
            p,
            env_r,
            psnd(psnd(Expr::Var(rb))),
            pfst(psnd(Expr::Var(rb))),
            cons_e(Expr::Var(e), pfst(psnd(Expr::Var(rb)))),
            true,
            Val::List(o),
        );
        bs_unary(p, env_r, Builtin::Reverse, sort_rev(e, rb), Val::List(o), Val::List(rev(o)));
        bs_let(p, env_o, rb, fe, Expr::Builtin(Builtin::Reverse, seq![sort_rev(e, rb)]), vr, Val::List(rev(o)));
        assert(rev(o) =~= pvals(sort_prefix(zp, i + 1)));
    } else {
        bs_binary(
            p,
            env_r,
            Builtin::Cons,
            Expr::Var(e),
            pfst(psnd(Expr::Var(rb))),
            ep.0,
            Val::List(o),
            Val::List(seq![ep.0] + o),
        );
        bs_if(
            p,
            env_r,
            psnd(psnd(Expr::Var(rb))),
            pfst(psnd(Expr::Var(rb))),
            cons_e(Expr::Var(e), pfst(psnd(Expr::Var(rb)))),
            false,
            Val::List(seq![ep.0] + o),
        );
        bs_unary(p, env_r, Builtin::Reverse, sort_rev(e, rb), Val::List(seq![ep.0] + o), Val::List(rev(seq![ep.0] + o)));
        bs_let(
            p,
            env_o,
            rb,
            fe,
            Expr::Builtin(Builtin::Reverse, seq![sort_rev(e, rb)]),
            vr,
            Val::List(rev(seq![ep.0] + o)),
        );
        ins_all_le(s, ep);
        pvals_snoc(s, ep);
        rev_cons(ep.0, o);
        assert(rev(o) =~= pvals(s));
        assert(rev(seq![ep.0] + o) =~= pvals(sort_prefix(zp, i + 1)));
    }
}

// ------------------------------------------------------------------ 整数の値の列

/// 整数の鍵の列を、整数の値の列にする。
pub open spec fn int_vals(keys: Seq<int>) -> Seq<Val> {
    Seq::new(keys.len(), |i: int| Val::Int(keys[i]))
}

/// 整数の値の列は、もとの整数の列に戻る。
proof fn int_vals_seq(keys: Seq<int>)
    ensures
        int_seq(int_vals(keys)) == Some(keys),
{
    let vs = int_vals(keys);
    assert(vs.len() == keys.len());
    assert forall|i: int| 0 <= i < keys.len() implies vs[i] == Val::Int(keys[i]) by {
    }
    assert forall|i: int| 0 <= i < vs.len() implies int_of_val(#[trigger] vs[i]) is Some by {
        assert(vs[i] == Val::Int(keys[i]));
    }
    assert(int_seq(vs) == Some(Seq::new(vs.len(), |i: int| int_of_val(vs[i])->Some_0)));
    assert(Seq::new(vs.len(), |i: int| int_of_val(vs[i])->Some_0) =~= keys);
}

// ------------------------------------------------------------------ 核の書換えの意味

/// 核の書換えの意味：列 xs が items に、鍵の式 k が各要素について（x に値を束縛して）keys に評価されれば、
/// 核の書換え sort_collect は sort_vals(items, keys) に評価される。
pub proof fn sort_core_meaning(
    p: Prog,
    env: Map<nat, Val>,
    xs: Expr,
    t: Ty,
    acc: nat,
    e: nat,
    st: nat,
    y: nat,
    ky: nat,
    ke: nat,
    rb: nat,
    x: nat,
    k: Expr,
    items: Seq<Val>,
    keys: Seq<int>,
)
    requires
        names_ok(acc, e, st, y, ky, ke, rb, x),
        absent(acc, k),
        absent(e, k),
        absent(st, k),
        absent(y, k),
        keys.len() == items.len(),
        evals_to(p, env, xs, Val::List(items)),
        keyed(p, env, x, k, zip_keys(items, keys)),
    ensures
        evals_to(p, env, sort_collect(xs, t, acc, e, st, y, ky, ke, rb, x, k), Val::List(sort_vals(items, keys))),
{
    reveal_with_fuel(sort_prefix, 1);
    let zp = zip_keys(items, keys);
    let n = items.len();
    let accs = Seq::new(n + 1, |i: int| Val::List(pvals(sort_prefix(zp, i as nat))));
    assert(zp.len() == n);
    assert(accs.len() == items.len() + 1);
    assert(sort_vals(items, keys) == pvals(sort_prefix(zp, n)));
    assert(sort_prefix(zp, 0) =~= Seq::<(Val, int)>::empty());
    assert(pvals(Seq::<(Val, int)>::empty()) =~= Seq::<Val>::empty());
    assert(accs[0] == Val::List(Seq::<Val>::empty()));
    assert(accs[n as int] == Val::List(pvals(sort_prefix(zp, n))));
    assert forall|i: int| 0 <= i < n implies evals_to(
        p,
        #[trigger] env.insert(acc, accs[i]).insert(e, items[i]),
        sort_body(t, acc, e, st, y, ky, ke, rb, x, k),
        accs[i + 1],
    ) by {
        assert(zp[i].0 == items[i]);
        assert(accs[i] == Val::List(pvals(sort_prefix(zp, i as nat))));
        assert(accs[i + 1] == Val::List(pvals(sort_prefix(zp, (i + 1) as nat))));
        keyed_prefix(p, env, x, k, zp, i as nat);
        outer_step(p, env, acc, e, st, y, ky, ke, rb, x, k, t, zp, i as nat);
    }
    bs_nil(p, env, t);
    fold_expr_to(
        p,
        env,
        xs,
        Expr::List(t, Seq::empty()),
        acc,
        e,
        sort_body(t, acc, e, st, y, ky, ke, rb, x, k),
        items,
        accs,
    );
}

/// 源の sort_by の意味：列 xs が items に、鍵の式 k が各要素について keys に評価されれば、
/// 源の sort_by（XExpr::SortBy）は sort_vals(items, keys) に評価される。
pub proof fn sort_source(p: Prog, env: Map<nat, Val>, xs: Expr, x: nat, k: Expr, items: Seq<Val>, keys: Seq<int>)
    requires
        keys.len() == items.len(),
        evals_to(p, env, xs, Val::List(items)),
        keyed(p, env, x, k, zip_keys(items, keys)),
    ensures
        xevals_to(
            embed_prog(p),
            env,
            XExpr::SortBy(Box::new(embed(xs)), x, Box::new(embed(k))),
            Val::List(sort_vals(items, keys)),
        ),
{
    let zp = zip_keys(items, keys);
    let gv = int_vals(keys);
    assert(zp.len() == items.len());
    assert(gv.len() == items.len());
    assert forall|m: int| 0 <= m < items.len() implies evals_to(p, #[trigger] env.insert(x, items[m]), k, gv[m]) by {
        assert(evals_to(p, env.insert(x, zp[m].0), k, Val::Int(zp[m].1)));
        assert(zp[m].0 == items[m]);
        assert(zp[m].1 == keys[m]);
        assert(gv[m] == Val::Int(keys[m]));
    }
    xmap_from_each(p, env, x, k, items, gv, 0);
    let n1 = choose|n: nat| #[trigger] eval(p, n, env, xs) == Res::Done(Val::List(items));
    let n2 = choose|n: nat|
        #[trigger] xmap(embed_prog(p), n, env, x, embed(k), items, 0) == ResSeq::Done(gv.subrange(0, gv.len() as int));
    let n = max(n1, n2);
    lift(p, n1, n, env, xs);
    embed_eval(p, n, env, xs);
    xmap_mono(p, n2, n, env, x, k, items, 0);
    assert(gv.subrange(0, gv.len() as int) =~= gv);
    int_vals_seq(keys);
    assert(xeval(
        embed_prog(p),
        n + 1,
        env,
        XExpr::SortBy(Box::new(embed(xs)), x, Box::new(embed(k))),
    ) == Res::Done(Val::List(sort_vals(items, keys))));
}

/// sort_by の意味（源と核）：同じ前提から、源の sort_by と核の書換えは、同じ列 sort_vals(items, keys) に評価される。
pub proof fn sort_meaning(
    p: Prog,
    env: Map<nat, Val>,
    xs: Expr,
    t: Ty,
    acc: nat,
    e: nat,
    st: nat,
    y: nat,
    ky: nat,
    ke: nat,
    rb: nat,
    x: nat,
    k: Expr,
    items: Seq<Val>,
    keys: Seq<int>,
)
    requires
        names_ok(acc, e, st, y, ky, ke, rb, x),
        absent(acc, k),
        absent(e, k),
        absent(st, k),
        absent(y, k),
        keys.len() == items.len(),
        evals_to(p, env, xs, Val::List(items)),
        keyed(p, env, x, k, zip_keys(items, keys)),
    ensures
        xevals_to(
            embed_prog(p),
            env,
            XExpr::SortBy(Box::new(embed(xs)), x, Box::new(embed(k))),
            Val::List(sort_vals(items, keys)),
        ),
        evals_to(p, env, sort_collect(xs, t, acc, e, st, y, ky, ke, rb, x, k), Val::List(sort_vals(items, keys))),
{
    sort_source(p, env, xs, x, k, items, keys);
    sort_core_meaning(p, env, xs, t, acc, e, st, y, ky, ke, rb, x, k, items, keys);
}

// ------------------------------------------------------------------ 型の部品

/// 変数の型。
proof fn var_ty(p: Prog, r: nat, ctx: Map<nat, Ty>, v: nat, t: Ty)
    requires
        ctx.contains_key(v),
        ctx[v] == t,
    ensures
        ty_expr(p, r, ctx, Expr::Var(v)) == Some(t),
{
    reveal_with_fuel(ty_expr, 1);
}

/// Some の型。
proof fn some_ty(p: Prog, r: nat, ctx: Map<nat, Ty>, a: Expr, t: Ty)
    requires
        ty_expr(p, r, ctx, a) == Some(t),
    ensures
        ty_expr(p, r, ctx, Expr::Some(Box::new(a))) == Some(Ty::Option(Box::new(t))),
{
    reveal_with_fuel(ty_expr, 1);
}

/// 対の型。
proof fn pair_ty(p: Prog, r: nat, ctx: Map<nat, Ty>, a: Expr, b: Expr, ta: Ty, tb: Ty)
    requires
        ty_expr(p, r, ctx, a) == Some(ta),
        ty_expr(p, r, ctx, b) == Some(tb),
    ensures
        ty_expr(p, r, ctx, pair_e(a, b)) == Some(Ty::Pair(Box::new(ta), Box::new(tb))),
{
    reveal_with_fuel(ty_expr, 1);
}

/// 第一成分の取り出しの型。
proof fn fst_ty(p: Prog, r: nat, ctx: Map<nat, Ty>, a: Expr, ta: Ty, tb: Ty)
    requires
        ty_expr(p, r, ctx, a) == Some(Ty::Pair(Box::new(ta), Box::new(tb))),
    ensures
        ty_expr(p, r, ctx, pfst(a)) == Some(ta),
{
    reveal_with_fuel(ty_expr, 3);
    reveal_with_fuel(ty_args, 2);
    let pt = Ty::Pair(Box::new(ta), Box::new(tb));
    assert(ty_args(p, r, ctx, seq![a], 0) == Some(seq![pt]));
    assert(builtin_type(Builtin::Fst, seq![pt]) == Some(ta));
}

/// 第二成分の取り出しの型。
proof fn snd_ty(p: Prog, r: nat, ctx: Map<nat, Ty>, a: Expr, ta: Ty, tb: Ty)
    requires
        ty_expr(p, r, ctx, a) == Some(Ty::Pair(Box::new(ta), Box::new(tb))),
    ensures
        ty_expr(p, r, ctx, psnd(a)) == Some(tb),
{
    reveal_with_fuel(ty_expr, 3);
    reveal_with_fuel(ty_args, 2);
    let pt = Ty::Pair(Box::new(ta), Box::new(tb));
    assert(ty_args(p, r, ctx, seq![a], 0) == Some(seq![pt]));
    assert(builtin_type(Builtin::Snd, seq![pt]) == Some(tb));
}

/// 整数の比較の型。
proof fn lt_ty(p: Prog, r: nat, ctx: Map<nat, Ty>, a: Expr, b: Expr)
    requires
        ty_expr(p, r, ctx, a) == Some(Ty::Int),
        ty_expr(p, r, ctx, b) == Some(Ty::Int),
    ensures
        ty_expr(p, r, ctx, Expr::Builtin(Builtin::Lt, seq![a, b])) == Some(Ty::Bool),
{
    reveal_with_fuel(ty_expr, 3);
    reveal_with_fuel(ty_args, 3);
    assert(ty_args(p, r, ctx, seq![a, b], 1) == Some(seq![Ty::Int]));
    assert(ty_args(p, r, ctx, seq![a, b], 0) == Some(seq![Ty::Int, Ty::Int]));
    assert(builtin_type(Builtin::Lt, seq![Ty::Int, Ty::Int]) == Some(Ty::Bool));
}

/// 条件式の型。
proof fn if_ty(p: Prog, r: nat, ctx: Map<nat, Ty>, c: Expr, a: Expr, b: Expr, t: Ty)
    requires
        ty_expr(p, r, ctx, c) == Some(Ty::Bool),
        ty_expr(p, r, ctx, a) == Some(t),
        ty_expr(p, r, ctx, b) == Some(t),
    ensures
        ty_expr(p, r, ctx, Expr::If(Box::new(c), Box::new(a), Box::new(b))) == Some(t),
{
    reveal_with_fuel(ty_expr, 1);
}

/// let の型。
proof fn let_ty(p: Prog, r: nat, ctx: Map<nat, Ty>, x: nat, a: Expr, b: Expr, ta: Ty, tb: Ty)
    requires
        ty_expr(p, r, ctx, a) == Some(ta),
        ty_expr(p, r, ctx.insert(x, ta), b) == Some(tb),
    ensures
        ty_expr(p, r, ctx, Expr::Let(x, Box::new(a), Box::new(b))) == Some(tb),
{
    reveal_with_fuel(ty_expr, 1);
}

/// match の型（Some の枝は中身を x に束縛する）。
proof fn match_ty(p: Prog, r: nat, ctx: Map<nat, Ty>, m: Expr, n: Expr, x: nat, sm: Expr, ta: Ty, tn: Ty)
    requires
        ty_expr(p, r, ctx, m) == Some(Ty::Option(Box::new(ta))),
        ty_expr(p, r, ctx, n) == Some(tn),
        ty_expr(p, r, ctx.insert(x, ta), sm) == Some(tn),
    ensures
        ty_expr(p, r, ctx, Expr::Match(Box::new(m), Box::new(n), x, Box::new(sm))) == Some(tn),
{
    reveal_with_fuel(ty_expr, 1);
}

/// 内側の畳み込みの初期状態の型。
proof fn init_typing(p: Prog, r: nat, ctx: Map<nat, Ty>, s: Ty)
    ensures
        ty_expr(p, r, ctx, init_state(s)) == Some(state_ty(s)),
{
    reveal_with_fuel(ty_expr, 1);
    ty_nil(p, r, ctx, s);
    let lt = Ty::List(Box::new(s));
    let rt = Ty::Pair(Box::new(lt), Box::new(Ty::Bool));
    assert(ty_expr(p, r, ctx, Expr::None(Ty::Int)) == Some(Ty::Option(Box::new(Ty::Int))));
    assert(ty_expr(p, r, ctx, Expr::Bool(false)) == Some(Ty::Bool));
    pair_ty(p, r, ctx, Expr::List(s, Seq::empty()), Expr::Bool(false), lt, Ty::Bool);
    pair_ty(
        p,
        r,
        ctx,
        Expr::None(Ty::Int),
        pair_e(Expr::List(s, Seq::empty()), Expr::Bool(false)),
        Ty::Option(Box::new(Ty::Int)),
        rt,
    );
    assert(state_ty(s) == Ty::Pair(Box::new(Ty::Option(Box::new(Ty::Int))), Box::new(rt)));
}

/// 鍵の式の型：束縛 acc・e・st・y を加えても、鍵の型は変わらない（absent）。
proof fn key_ty(
    p: Prog,
    r: nat,
    ctx: Map<nat, Ty>,
    k: Expr,
    acc: nat,
    e: nat,
    st: nat,
    y: nat,
    x: nat,
    s: Ty,
    lt: Ty,
    sst: Ty,
)
    requires
        acc != x,
        e != x,
        st != x,
        y != x,
        absent(acc, k),
        absent(e, k),
        absent(st, k),
        absent(y, k),
        ty_expr(p, r, ctx.insert(x, s), k) == Some(Ty::Int),
    ensures
        ty_expr(p, r, ctx.insert(acc, lt).insert(e, s).insert(st, sst).insert(y, s).insert(x, s), k) == Some(Ty::Int),
{
    let c0 = ctx.insert(x, s);
    ty_absent(p, r, c0.insert(acc, lt).insert(e, s).insert(st, sst), k, y, s);
    ty_absent(p, r, c0.insert(acc, lt).insert(e, s), k, st, sst);
    ty_absent(p, r, c0.insert(acc, lt), k, e, s);
    ty_absent(p, r, c0, k, acc, lt);
    assert(ctx.insert(acc, lt).insert(e, s).insert(st, sst).insert(y, s).insert(x, s) =~= c0.insert(acc, lt).insert(
        e,
        s,
    ).insert(st, sst).insert(y, s));
}

/// 鍵の比較の型（置く前）：ke と ky は Int、e と y は s、st は状態。
proof fn sort_lt_typing(p: Prog, r: nat, c: Map<nat, Ty>, s: Ty, e: nat, st: nat, y: nat, ky: nat, ke: nat)
    requires
        c.contains_key(ke),
        c[ke] == Ty::Int,
        c.contains_key(ky),
        c[ky] == Ty::Int,
        c.contains_key(e),
        c[e] == s,
        c.contains_key(st),
        c[st] == state_ty(s),
        c.contains_key(y),
        c[y] == s,
    ensures
        ty_expr(p, r, c, sort_lt(e, st, y, ky, ke)) == Some(state_ty(s)),
{
    reveal_with_fuel(ty_expr, 1);
    let lt = Ty::List(Box::new(s));
    let ot = Ty::Option(Box::new(Ty::Int));
    let rt = Ty::Pair(Box::new(lt), Box::new(Ty::Bool));
    assert(state_ty(s) == Ty::Pair(Box::new(ot), Box::new(rt)));
    var_ty(p, r, c, st, state_ty(s));
    fst_ty(p, r, c, Expr::Var(st), ot, rt);
    snd_ty(p, r, c, Expr::Var(st), ot, rt);
    fst_ty(p, r, c, psnd(Expr::Var(st)), lt, Ty::Bool);
    var_ty(p, r, c, e, s);
    var_ty(p, r, c, y, s);
    ty_cons(p, r, c, Expr::Var(e), pfst(psnd(Expr::Var(st))), s);
    ty_cons(p, r, c, Expr::Var(y), cons_e(Expr::Var(e), pfst(psnd(Expr::Var(st)))), s);
    ty_cons(p, r, c, Expr::Var(y), pfst(psnd(Expr::Var(st))), s);
    assert(ty_expr(p, r, c, Expr::Bool(true)) == Some(Ty::Bool));
    assert(ty_expr(p, r, c, Expr::Bool(false)) == Some(Ty::Bool));
    pair_ty(
        p,
        r,
        c,
        cons_e(Expr::Var(y), cons_e(Expr::Var(e), pfst(psnd(Expr::Var(st))))),
        Expr::Bool(true),
        lt,
        Ty::Bool,
    );
    pair_ty(
        p,
        r,
        c,
        pfst(Expr::Var(st)),
        pair_e(cons_e(Expr::Var(y), cons_e(Expr::Var(e), pfst(psnd(Expr::Var(st))))), Expr::Bool(true)),
        ot,
        rt,
    );
    pair_ty(p, r, c, cons_e(Expr::Var(y), pfst(psnd(Expr::Var(st)))), Expr::Bool(false), lt, Ty::Bool);
    pair_ty(
        p,
        r,
        c,
        pfst(Expr::Var(st)),
        pair_e(cons_e(Expr::Var(y), pfst(psnd(Expr::Var(st)))), Expr::Bool(false)),
        ot,
        rt,
    );
    var_ty(p, r, c, ke, Ty::Int);
    var_ty(p, r, c, ky, Ty::Int);
    lt_ty(p, r, c, Expr::Var(ke), Expr::Var(ky));
    if_ty(
        p,
        r,
        c,
        Expr::Builtin(Builtin::Lt, seq![Expr::Var(ke), Expr::Var(ky)]),
        sort_before(e, st, y),
        sort_after(st, y),
        state_ty(s),
    );
}

/// 鍵の照合の型：枠が None なら e の鍵 ky を残し、Some なら鍵を比べる（置いていない場合の一部）。
proof fn sort_match_typing(p: Prog, r: nat, ci: Map<nat, Ty>, s: Ty, e: nat, st: nat, y: nat, ky: nat, ke: nat)
    requires
        e != ky,
        e != ke,
        st != ky,
        st != ke,
        y != ky,
        y != ke,
        ky != ke,
        ci.contains_key(e),
        ci[e] == s,
        ci.contains_key(st),
        ci[st] == state_ty(s),
        ci.contains_key(y),
        ci[y] == s,
    ensures
        ty_expr(p, r, ci.insert(ky, Ty::Int), sort_match(e, st, y, ky, ke)) == Some(state_ty(s)),
{
    reveal_with_fuel(ty_expr, 1);
    let cm = ci.insert(ky, Ty::Int);
    let lt = Ty::List(Box::new(s));
    let ot = Ty::Option(Box::new(Ty::Int));
    let rt = Ty::Pair(Box::new(lt), Box::new(Ty::Bool));
    assert(state_ty(s) == Ty::Pair(Box::new(ot), Box::new(rt)));
    var_ty(p, r, cm, st, state_ty(s));
    fst_ty(p, r, cm, Expr::Var(st), ot, rt);
    var_ty(p, r, cm, ky, Ty::Int);
    some_ty(p, r, cm, Expr::Var(ky), Ty::Int);
    snd_ty(p, r, cm, Expr::Var(st), ot, rt);
    pair_ty(p, r, cm, Expr::Some(Box::new(Expr::Var(ky))), psnd(Expr::Var(st)), ot, rt);
    sort_lt_typing(p, r, cm.insert(ke, Ty::Int), s, e, st, y, ky, ke);
    match_ty(
        p,
        r,
        cm,
        pfst(Expr::Var(st)),
        pair_e(Expr::Some(Box::new(Expr::Var(ky))), psnd(Expr::Var(st))),
        ke,
        sort_lt(e, st, y, ky, ke),
        Ty::Int,
        state_ty(s),
    );
}

/// 内側の本体の型（状態は state_ty(s)、要素 y と e は s）。鍵の式は ci に x を足した下で Int。
proof fn inner_typing(
    p: Prog,
    r: nat,
    ci: Map<nat, Ty>,
    s: Ty,
    e: nat,
    st: nat,
    y: nat,
    ky: nat,
    ke: nat,
    x: nat,
    k: Expr,
)
    requires
        e != st,
        e != y,
        e != ky,
        e != ke,
        st != y,
        st != ky,
        st != ke,
        y != ky,
        y != ke,
        ky != ke,
        ci.contains_key(e),
        ci[e] == s,
        ci.contains_key(st),
        ci[st] == state_ty(s),
        ci.contains_key(y),
        ci[y] == s,
        ty_expr(p, r, ci.insert(x, s), k) == Some(Ty::Int),
    ensures
        ty_expr(p, r, ci, sort_inner(e, st, y, ky, ke, x, k)) == Some(state_ty(s)),
{
    reveal_with_fuel(ty_expr, 1);
    let lt = Ty::List(Box::new(s));
    let ot = Ty::Option(Box::new(Ty::Int));
    let rt = Ty::Pair(Box::new(lt), Box::new(Ty::Bool));
    assert(state_ty(s) == Ty::Pair(Box::new(ot), Box::new(rt)));
    // 置いたかどうか（sort_cond）は Bool
    var_ty(p, r, ci, st, state_ty(s));
    fst_ty(p, r, ci, Expr::Var(st), ot, rt);
    snd_ty(p, r, ci, Expr::Var(st), ot, rt);
    fst_ty(p, r, ci, psnd(Expr::Var(st)), lt, Ty::Bool);
    snd_ty(p, r, ci, psnd(Expr::Var(st)), lt, Ty::Bool);
    // 置いた後
    var_ty(p, r, ci, y, s);
    ty_cons(p, r, ci, Expr::Var(y), pfst(psnd(Expr::Var(st))), s);
    assert(ty_expr(p, r, ci, Expr::Bool(true)) == Some(Ty::Bool));
    pair_ty(p, r, ci, cons_e(Expr::Var(y), pfst(psnd(Expr::Var(st)))), Expr::Bool(true), lt, Ty::Bool);
    pair_ty(
        p,
        r,
        ci,
        pfst(Expr::Var(st)),
        pair_e(cons_e(Expr::Var(y), pfst(psnd(Expr::Var(st)))), Expr::Bool(true)),
        ot,
        rt,
    );
    // 置いていない場合：鍵を求めて枠と比べる
    sort_match_typing(p, r, ci, s, e, st, y, ky, ke);
    let_ty(p, r, ci, x, Expr::Var(y), k, s, Ty::Int);
    let_ty(
        p,
        r,
        ci,
        ky,
        Expr::Let(x, Box::new(Expr::Var(y)), Box::new(k)),
        sort_match(e, st, y, ky, ke),
        Ty::Int,
        state_ty(s),
    );
    if_ty(p, r, ci, sort_cond(st), sort_placed(st, y), sort_fresh(e, st, y, ky, ke, x, k), state_ty(s));
}

/// 向きをそろえる式の型：置いたなら出力の列、置いていないなら e を出力の先頭に足した列。どちらも List(s)。
proof fn rev_typing(p: Prog, r: nat, ctx: Map<nat, Ty>, e: nat, rb: nat, s: Ty)
    requires
        ctx.contains_key(e),
        ctx[e] == s,
        ctx.contains_key(rb),
        ctx[rb] == state_ty(s),
    ensures
        ty_expr(p, r, ctx, sort_rev(e, rb)) == Some(Ty::List(Box::new(s))),
{
    reveal_with_fuel(ty_expr, 1);
    let lt = Ty::List(Box::new(s));
    let ot = Ty::Option(Box::new(Ty::Int));
    let rt = Ty::Pair(Box::new(lt), Box::new(Ty::Bool));
    assert(state_ty(s) == Ty::Pair(Box::new(ot), Box::new(rt)));
    var_ty(p, r, ctx, rb, state_ty(s));
    snd_ty(p, r, ctx, Expr::Var(rb), ot, rt);
    fst_ty(p, r, ctx, psnd(Expr::Var(rb)), lt, Ty::Bool);
    snd_ty(p, r, ctx, psnd(Expr::Var(rb)), lt, Ty::Bool);
    var_ty(p, r, ctx, e, s);
    ty_cons(p, r, ctx, Expr::Var(e), pfst(psnd(Expr::Var(rb))), s);
    if_ty(
        p,
        r,
        ctx,
        psnd(psnd(Expr::Var(rb))),
        pfst(psnd(Expr::Var(rb))),
        cons_e(Expr::Var(e), pfst(psnd(Expr::Var(rb)))),
        lt,
    );
}

/// 外側の本体の型：内側の畳み込みと向きそろえは、出力の型 List(s) を与える。
proof fn body_typing(
    p: Prog,
    r: nat,
    ctx: Map<nat, Ty>,
    s: Ty,
    acc: nat,
    e: nat,
    st: nat,
    y: nat,
    ky: nat,
    ke: nat,
    rb: nat,
    x: nat,
    k: Expr,
)
    requires
        names_ok(acc, e, st, y, ky, ke, rb, x),
        absent(acc, k),
        absent(e, k),
        absent(st, k),
        absent(y, k),
        ty_expr(p, r, ctx.insert(x, s), k) == Some(Ty::Int),
    ensures
        ty_expr(p, r, ctx.insert(acc, Ty::List(Box::new(s))).insert(e, s), sort_body(s, acc, e, st, y, ky, ke, rb, x, k))
            == Some(Ty::List(Box::new(s))),
{
    let lt = Ty::List(Box::new(s));
    let sst = state_ty(s);
    let co = ctx.insert(acc, lt).insert(e, s);
    let ci = co.insert(st, sst).insert(y, s);
    key_ty(p, r, ctx, k, acc, e, st, y, x, s, lt, sst);
    init_typing(p, r, co, s);
    var_ty(p, r, co, e, s);
    var_ty(p, r, co, acc, lt);
    ty_cons(p, r, co, Expr::Var(e), Expr::Var(acc), s);
    inner_typing(p, r, ci, s, e, st, y, ky, ke, x, k);
    fold_typing(
        p,
        r,
        co,
        cons_e(Expr::Var(e), Expr::Var(acc)),
        init_state(s),
        st,
        y,
        sort_inner(e, st, y, ky, ke, x, k),
        s,
        sst,
    );
    rev_typing(p, r, co.insert(rb, sst), e, rb, s);
    ty_reverse(p, r, co.insert(rb, sst), sort_rev(e, rb), s);
    let_ty(
        p,
        r,
        co,
        rb,
        Expr::Fold(
            Box::new(cons_e(Expr::Var(e), Expr::Var(acc))),
            Box::new(init_state(s)),
            st,
            y,
            Box::new(sort_inner(e, st, y, ky, ke, x, k)),
        ),
        Expr::Builtin(Builtin::Reverse, seq![sort_rev(e, rb)]),
        sst,
        lt,
    );
}

/// sort_by の型（源と核）：xs が List(s)、鍵の式が Int なら、核の書換えと源の sort_by は List(s) の型を持つ。
pub proof fn sort_typing(
    p: Prog,
    r: nat,
    ctx: Map<nat, Ty>,
    xs: Expr,
    s: Ty,
    acc: nat,
    e: nat,
    st: nat,
    y: nat,
    ky: nat,
    ke: nat,
    rb: nat,
    x: nat,
    k: Expr,
)
    requires
        names_ok(acc, e, st, y, ky, ke, rb, x),
        absent(acc, k),
        absent(e, k),
        absent(st, k),
        absent(y, k),
        ty_expr(p, r, ctx, xs) == Some(Ty::List(Box::new(s))),
        ty_expr(p, r, ctx.insert(x, s), k) == Some(Ty::Int),
    ensures
        ty_expr(p, r, ctx, sort_collect(xs, s, acc, e, st, y, ky, ke, rb, x, k)) == Some(Ty::List(Box::new(s))),
        ty_x(embed_prog(p), r, ctx, XExpr::SortBy(Box::new(embed(xs)), x, Box::new(embed(k))))
            == Some(Ty::List(Box::new(s))),
{
    let lt = Ty::List(Box::new(s));
    body_typing(p, r, ctx, s, acc, e, st, y, ky, ke, rb, x, k);
    ty_nil(p, r, ctx, s);
    fold_typing(
        p,
        r,
        ctx,
        xs,
        Expr::List(s, Seq::empty()),
        acc,
        e,
        sort_body(s, acc, e, st, y, ky, ke, rb, x, k),
        s,
        lt,
    );
    ty_embed(p, r, ctx, xs);
    ty_embed(p, r, ctx.insert(x, s), k);
    reveal_with_fuel(ty_x, 1);
}

} // verus!
