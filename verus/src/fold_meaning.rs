//! 畳み込みで集める形の意味（段階 0・SH6）。
//!
//! 写像の形 `reverse(fold(xs, [], |acc, item| Cons(g, acc)))` が、各要素の g の値の列に評価されることを示す。
//! g は累積値の名前 acc を含まない（`absent(acc, g)`）。束縛の新しさ（SH5）は各 rewrite でこれを示す。

use crate::bigstep::*;
use crate::records_proof::*;
use crate::spec::*;
use vstd::prelude::*;

verus! {

/// 畳み込みの本体 `Cons(g, acc)`：要素の値 g を累積値の先頭に加える。
pub open spec fn cons_body(g: Expr, acc: nat) -> Expr {
    Expr::Builtin(Builtin::Cons, seq![g, Expr::Var(acc)])
}

/// 写像の形：`fold(xs, [], |acc, item| Cons(g, acc))` の結果を reverse したもの。
pub open spec fn map_collect(xs: Expr, t: Ty, acc: nat, item: nat, g: Expr) -> Expr {
    Expr::Builtin(
        Builtin::Reverse,
        seq![Expr::Fold(Box::new(xs), Box::new(Expr::List(t, Seq::empty())), acc, item, Box::new(cons_body(g, acc)))],
    )
}

/// 先頭 k 個の値を逆順に並べた列（k 番目の値が先頭に来る）。
pub open spec fn rev_pref(gv: Seq<Val>, k: nat) -> Seq<Val>
    decreases k,
{
    if k == 0 {
        Seq::empty()
    } else {
        seq![gv[(k - 1) as int]] + rev_pref(gv, (k - 1) as nat)
    }
}

pub proof fn rev_pref_len(gv: Seq<Val>, k: nat)
    ensures
        rev_pref(gv, k).len() == k,
    decreases k,
{
    if k > 0 {
        rev_pref_len(gv, (k - 1) as nat);
    }
}

pub proof fn rev_pref_index(gv: Seq<Val>, k: nat, i: nat)
    requires
        k <= gv.len(),
        i < k,
    ensures
        rev_pref(gv, k)[i as int] == gv[(k - 1 - i) as int],
    decreases k,
{
    rev_pref_len(gv, (k - 1) as nat);
    if i > 0 {
        rev_pref_index(gv, (k - 1) as nat, (i - 1) as nat);
    }
}

/// 列全体の長さまでの rev_pref は、列の reverse に一致する。
pub proof fn rev_pref_full(gv: Seq<Val>)
    ensures
        rev_pref(gv, gv.len() as nat) =~= rev(gv),
{
    let n = gv.len() as nat;
    rev_pref_len(gv, n);
    assert forall|i: int| 0 <= i < n implies rev_pref(gv, n)[i] == rev(gv)[i] by {
        rev_pref_index(gv, n, i as nat);
    }
    assert(rev_pref(gv, n) =~= rev(gv));
}

/// reverse を二度かけると元に戻る。
pub proof fn rev_rev(gv: Seq<Val>)
    ensures
        rev(rev(gv)) =~= gv,
{
    assert(rev(rev(gv)).len() == gv.len());
    assert forall|i: int| 0 <= i < gv.len() implies rev(rev(gv))[i] == gv[i] by {
        assert(rev(gv)[gv.len() - 1 - i] == gv[gv.len() - 1 - (gv.len() - 1 - i)]);
    }
    assert(rev(rev(gv)) =~= gv);
}

/// 段の本体 `Cons(g, acc)` は、累積値 List(rev_pref(gv, k)) を List(rev_pref(gv, k + 1)) に変える。
pub proof fn collect_step(
    p: Prog,
    env: Map<nat, Val>,
    acc: nat,
    item: nat,
    g: Expr,
    gv: Seq<Val>,
    items: Seq<Val>,
    k: nat,
)
    requires
        acc != item,
        absent(acc, g),
        gv.len() == items.len(),
        k < items.len(),
        evals_to(p, env.insert(item, items[k as int]), g, gv[k as int]),
    ensures
        evals_to(
            p,
            env.insert(acc, Val::List(rev_pref(gv, k))).insert(item, items[k as int]),
            cons_body(g, acc),
            Val::List(rev_pref(gv, k + 1)),
        ),
{
    let a = Val::List(rev_pref(gv, k));
    let x = gv[k as int];
    let env1 = env.insert(item, items[k as int]);
    let env2 = env.insert(acc, a).insert(item, items[k as int]);
    assert(env2 =~= env1.insert(acc, a));
    let n1 = choose|n: nat| #[trigger] eval(p, n, env1, g) == Res::Done(x);
    eval_absent(p, n1, env1, g, acc, a);
    assert(eval(p, n1, env2, g) == Res::Done(x));
    assert(evals_to(p, env2, g, x));
    assert(env2.contains_key(acc) && env2[acc] == a);
    bs_var(p, env2, acc);
    let es = seq![g, Expr::Var(acc)];
    let vs = seq![x, a];
    assert forall|j: int| 0 <= j < es.len() implies evals_to(p, env2, #[trigger] es[j], vs[j]) by {
        if j == 0 {
            assert(es[j] == g && vs[j] == x);
        } else {
            assert(j == 1 && es[j] == Expr::Var(acc) && vs[j] == a);
        }
    }
    args_from_each(p, env2, es, vs, 0);
    assert(vs.subrange(0, vs.len() as int) =~= vs);
    reveal_with_fuel(rev_pref, 2);
    assert(rev_pref(gv, k + 1) =~= seq![x] + rev_pref(gv, k));
    assert(apply(Builtin::Cons, vs) == Res::Done(Val::List(rev_pref(gv, k + 1))));
    bs_builtin(p, env2, Builtin::Cons, es, vs, Val::List(rev_pref(gv, k + 1)));
}

/// 写像の形の意味：各要素を束縛したときの g の値が gv[k] なら、map_collect は List(gv) に評価される。
pub proof fn collect_map(
    p: Prog,
    env: Map<nat, Val>,
    xs: Expr,
    t: Ty,
    acc: nat,
    item: nat,
    g: Expr,
    items: Seq<Val>,
    gv: Seq<Val>,
)
    requires
        acc != item,
        absent(acc, g),
        gv.len() == items.len(),
        evals_to(p, env, xs, Val::List(items)),
        forall|k: int|
            0 <= k < items.len() ==> evals_to(p, #[trigger] env.insert(item, items[k]), g, gv[k]),
    ensures
        evals_to(p, env, map_collect(xs, t, acc, item, g), Val::List(gv)),
{
    let n = items.len();
    let body = cons_body(g, acc);
    let accs = Seq::new(n + 1, |k: int| Val::List(rev_pref(gv, k as nat)));
    reveal_with_fuel(rev_pref, 1);
    assert(accs[0] == Val::List(Seq::<Val>::empty()));
    assert forall|k: int| 0 <= k < n implies evals_to(
        p,
        #[trigger] env.insert(acc, accs[k]).insert(item, items[k]),
        body,
        accs[k + 1],
    ) by {
        collect_step(p, env, acc, item, g, gv, items, k as nat);
    }
    fold_from_each(p, env, acc, item, body, items, accs, 0);
    let nil = Expr::List(t, Seq::empty());
    let v0 = Val::List(Seq::<Val>::empty());
    args_from_each(p, env, Seq::<Expr>::empty(), Seq::<Val>::empty(), 0);
    assert(Seq::<Val>::empty().subrange(0, 0) =~= Seq::<Val>::empty());
    bs_list(p, env, t, Seq::<Expr>::empty(), Seq::<Val>::empty());
    assert(evals_to(p, env, nil, v0));
    let w = accs[n as int];
    bs_fold(p, env, xs, nil, acc, item, body, items, v0, w);
    let fe = Expr::Fold(Box::new(xs), Box::new(nil), acc, item, Box::new(body));
    assert(evals_to(p, env, fe, w));
    rev_pref_full(gv);
    assert(w == Val::List(rev(gv)));
    let rv = Val::List(rev(gv));
    assert forall|j: int| 0 <= j < seq![fe].len() implies evals_to(p, env, #[trigger] seq![fe][j], seq![rv][j]) by {
        assert(seq![fe][j] == fe && seq![rv][j] == rv);
    }
    args_from_each(p, env, seq![fe], seq![rv], 0);
    assert(seq![rv].subrange(0, 1) =~= seq![rv]);
    let rr = Val::List(rev(rev(gv)));
    assert(apply(Builtin::Reverse, seq![rv]) == Res::Done(rr));
    bs_builtin(p, env, Builtin::Reverse, seq![fe], seq![rv], rr);
    rev_rev(gv);
    assert(rr == Val::List(gv));
    assert(evals_to(p, env, map_collect(xs, t, acc, item, g), rr));
}

} // verus!
