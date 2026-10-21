//! 畳み込みで集める形の意味（段階 0・SH6）。
//!
//! 畳み込みの形は四つ：cons で集めて reverse する写像（map）、その絞り込み（filter）、
//! 短絡する if の畳み込み（any と all）、最初の一致を残す選択（find）。
//! 本体の式は名前 acc を含まない（`absent(acc, c)`）ことを仮定する。束縛の新しさ（SH5）は各 rewrite でこれを示す。
//! 各形の評価は、段ごとの本体の評価から `fold_expr_to` で組み立てる。

use crate::bigstep::*;
use crate::records_proof::*;
use crate::spec::*;
use vstd::prelude::*;

verus! {

// ------------------------------------------------------------------ 共通の部品

/// acc への束縛を変えても、acc を含まない式 e の評価は変わらない（item への束縛は保つ）。
pub proof fn evals_absent_ins(
    p: Prog,
    env: Map<nat, Val>,
    e: Expr,
    acc: nat,
    a: Val,
    item: nat,
    u: Val,
    w: Val,
)
    requires
        acc != item,
        absent(acc, e),
        evals_to(p, env.insert(item, u), e, w),
    ensures
        evals_to(p, env.insert(acc, a).insert(item, u), e, w),
{
    let env1 = env.insert(item, u);
    let n1 = choose|n: nat| #[trigger] eval(p, n, env1, e) == Res::Done(w);
    eval_absent(p, n1, env1, e, acc, a);
    assert(env.insert(acc, a).insert(item, u) =~= env1.insert(acc, a));
    assert(eval(p, n1, env.insert(acc, a).insert(item, u), e) == Res::Done(w));
}

/// 畳み込み式の評価：xs が items に、init が accs[0] に評価され、各段の本体が accs[k + 1] に評価されれば、
/// 畳み込み式は accs の最後に評価される。
pub proof fn fold_expr_to(
    p: Prog,
    env: Map<nat, Val>,
    xs: Expr,
    init: Expr,
    acc: nat,
    item: nat,
    body: Expr,
    items: Seq<Val>,
    accs: Seq<Val>,
)
    requires
        accs.len() == items.len() + 1,
        evals_to(p, env, xs, Val::List(items)),
        evals_to(p, env, init, accs[0]),
        forall|k: int|
            0 <= k < items.len() ==> evals_to(
                p,
                #[trigger] env.insert(acc, accs[k]).insert(item, items[k]),
                body,
                accs[k + 1],
            ),
    ensures
        evals_to(
            p,
            env,
            Expr::Fold(Box::new(xs), Box::new(init), acc, item, Box::new(body)),
            accs[items.len() as int],
        ),
{
    fold_from_each(p, env, acc, item, body, items, accs, 0);
    bs_fold(p, env, xs, init, acc, item, body, items, accs[0], accs[items.len() as int]);
}

/// reverse の評価：e が List(s) に評価されれば、reverse(e) は List(rev(s)) に評価される。
pub proof fn bs_reverse(p: Prog, env: Map<nat, Val>, e: Expr, s: Seq<Val>)
    requires
        evals_to(p, env, e, Val::List(s)),
    ensures
        evals_to(p, env, Expr::Builtin(Builtin::Reverse, seq![e]), Val::List(rev(s))),
{
    let vs = seq![Val::List(s)];
    assert forall|j: int| 0 <= j < vs.len() implies evals_to(p, env, #[trigger] seq![e][j], vs[j]) by {
        assert(seq![e][j] == e);
    }
    args_from_each(p, env, seq![e], vs, 0);
    assert(vs.subrange(0, vs.len() as int) =~= vs);
    assert(apply(Builtin::Reverse, vs) == Res::Done(Val::List(rev(s))));
    bs_builtin(p, env, Builtin::Reverse, seq![e], vs, Val::List(rev(s)));
}

/// 空リストの評価。
pub proof fn bs_nil(p: Prog, env: Map<nat, Val>, t: Ty)
    ensures
        evals_to(p, env, Expr::List(t, Seq::empty()), Val::List(Seq::empty())),
{
    args_from_each(p, env, Seq::<Expr>::empty(), Seq::<Val>::empty(), 0);
    assert(Seq::<Val>::empty().subrange(0, 0) =~= Seq::<Val>::empty());
    bs_list(p, env, t, Seq::<Expr>::empty(), Seq::<Val>::empty());
}

// ------------------------------------------------------------------ 写像：cons で集めて reverse する

/// 本体 `Cons(g, acc)`：要素の値 g を累積値の先頭に加える。
pub open spec fn cons_body(g: Expr, acc: nat) -> Expr {
    Expr::Builtin(Builtin::Cons, seq![g, Expr::Var(acc)])
}

/// 写像の形：`reverse(fold(xs, [], |acc, item| Cons(g, acc)))`。
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

/// 末尾への追加の reverse は、先頭への追加に一致する。
pub proof fn rev_snoc_val(s: Seq<Val>, x: Val)
    ensures
        rev(s + seq![x]) =~= seq![x] + rev(s),
{
    let t = s + seq![x];
    assert(rev(t).len() == t.len());
    assert((seq![x] + rev(s)).len() == t.len());
    assert forall|i: int| 0 <= i < t.len() implies rev(t)[i] == (seq![x] + rev(s))[i] by {
        if i == 0 {
            assert(t[t.len() - 1] == x);
        } else {
            assert(t[t.len() - 1 - i] == s[s.len() - i]);
            assert(rev(s)[i - 1] == s[s.len() - i]);
        }
    }
    assert(rev(t) =~= seq![x] + rev(s));
}

/// 本体の一段：累積値 List(rev_pref(gv, k)) に要素の値 gv[k] を加え、List(rev_pref(gv, k + 1)) に変える。
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
    reveal_with_fuel(rev_pref, 2);
    let a = Val::List(rev_pref(gv, k));
    let x = gv[k as int];
    let env2 = env.insert(acc, a).insert(item, items[k as int]);
    evals_absent_ins(p, env, g, acc, a, item, items[k as int], x);
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
    assert(rev_pref(gv, k + 1) =~= seq![x] + rev_pref(gv, k));
    assert(apply(Builtin::Cons, vs) == Res::Done(Val::List(rev_pref(gv, k + 1))));
    bs_builtin(p, env2, Builtin::Cons, es, vs, Val::List(rev_pref(gv, k + 1)));
}

/// 写像の意味：各要素を束縛したときの g の値が gv[k] なら、map_collect は List(gv) に評価される。
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
    let accs = Seq::new(n + 1, |k: int| Val::List(rev_pref(gv, k as nat)));
    reveal_with_fuel(rev_pref, 1);
    assert(accs[0] == Val::List(Seq::<Val>::empty()));
    assert forall|k: int| 0 <= k < n implies evals_to(
        p,
        #[trigger] env.insert(acc, accs[k]).insert(item, items[k]),
        cons_body(g, acc),
        accs[k + 1],
    ) by {
        collect_step(p, env, acc, item, g, gv, items, k as nat);
    }
    bs_nil(p, env, t);
    fold_expr_to(p, env, xs, Expr::List(t, Seq::empty()), acc, item, cons_body(g, acc), items, accs);
    assert(accs[n as int] == Val::List(rev_pref(gv, n)));
    rev_pref_full(gv);
    assert(rev_pref(gv, n) =~= rev(gv));
    let fe = Expr::Fold(Box::new(xs), Box::new(Expr::List(t, Seq::empty())), acc, item, Box::new(cons_body(g, acc)));
    bs_reverse(p, env, fe, rev_pref(gv, n));
    rev_rev(gv);
    assert(rev(rev_pref(gv, n)) =~= gv);
}

// ------------------------------------------------------------------ 絞り込み：述語が真の要素だけ cons して reverse する

/// 先頭 k 個のうち述語が真の要素を、先頭から順に並べた列。
pub open spec fn kept(items: Seq<Val>, keep: Seq<bool>, k: nat) -> Seq<Val>
    decreases k,
{
    if k == 0 {
        Seq::empty()
    } else if keep[(k - 1) as int] {
        kept(items, keep, (k - 1) as nat) + seq![items[(k - 1) as int]]
    } else {
        kept(items, keep, (k - 1) as nat)
    }
}

/// 絞り込みの本体 `if c then Cons(item, acc) else acc`。
pub open spec fn filter_body(c: Expr, acc: nat, item: nat) -> Expr {
    Expr::If(
        Box::new(c),
        Box::new(Expr::Builtin(Builtin::Cons, seq![Expr::Var(item), Expr::Var(acc)])),
        Box::new(Expr::Var(acc)),
    )
}

/// 絞り込みの形：`reverse(fold(xs, [], |acc, item| filter_body))`。
pub open spec fn filter_collect(xs: Expr, t: Ty, acc: nat, item: nat, c: Expr) -> Expr {
    Expr::Builtin(
        Builtin::Reverse,
        seq![Expr::Fold(Box::new(xs), Box::new(Expr::List(t, Seq::empty())), acc, item, Box::new(filter_body(c, acc, item)))],
    )
}

/// 絞り込みの一段：累積値 List(rev(kept(k))) は、要素 k を見て List(rev(kept(k + 1))) に変わる。
pub proof fn filter_step(
    p: Prog,
    env: Map<nat, Val>,
    acc: nat,
    item: nat,
    c: Expr,
    items: Seq<Val>,
    keep: Seq<bool>,
    k: nat,
)
    requires
        acc != item,
        absent(acc, c),
        keep.len() == items.len(),
        k < items.len(),
        evals_to(p, env.insert(item, items[k as int]), c, Val::Bool(keep[k as int])),
    ensures
        evals_to(
            p,
            env.insert(acc, Val::List(rev(kept(items, keep, k)))).insert(item, items[k as int]),
            filter_body(c, acc, item),
            Val::List(rev(kept(items, keep, k + 1))),
        ),
{
    reveal_with_fuel(kept, 2);
    let a = Val::List(rev(kept(items, keep, k)));
    let u = items[k as int];
    let env2 = env.insert(acc, a).insert(item, u);
    let cons_e = Expr::Builtin(Builtin::Cons, seq![Expr::Var(item), Expr::Var(acc)]);
    evals_absent_ins(p, env, c, acc, a, item, u, Val::Bool(keep[k as int]));
    assert(env2.contains_key(acc) && env2[acc] == a);
    assert(env2.contains_key(item) && env2[item] == u);
    bs_var(p, env2, acc);
    bs_var(p, env2, item);
    if keep[k as int] {
        let es = seq![Expr::Var(item), Expr::Var(acc)];
        let vs = seq![u, a];
        assert forall|j: int| 0 <= j < es.len() implies evals_to(p, env2, #[trigger] es[j], vs[j]) by {
            if j == 0 {
                assert(es[j] == Expr::Var(item) && vs[j] == u);
            } else {
                assert(j == 1 && es[j] == Expr::Var(acc) && vs[j] == a);
            }
        }
        args_from_each(p, env2, es, vs, 0);
        assert(vs.subrange(0, vs.len() as int) =~= vs);
        assert(kept(items, keep, k + 1) =~= kept(items, keep, k) + seq![u]);
        rev_snoc_val(kept(items, keep, k), u);
        assert(rev(kept(items, keep, k + 1)) =~= seq![u] + rev(kept(items, keep, k)));
        assert(apply(Builtin::Cons, vs) == Res::Done(Val::List(rev(kept(items, keep, k + 1)))));
        bs_builtin(p, env2, Builtin::Cons, es, vs, Val::List(rev(kept(items, keep, k + 1))));
    } else {
        assert(kept(items, keep, k + 1) =~= kept(items, keep, k));
    }
    bs_if(p, env2, c, cons_e, Expr::Var(acc), keep[k as int], Val::List(rev(kept(items, keep, k + 1))));
}

/// 絞り込みの意味：各要素の述語の値が keep[k] なら、filter_collect は List(kept(items, keep, n)) に評価される。
pub proof fn filter_meaning(
    p: Prog,
    env: Map<nat, Val>,
    xs: Expr,
    t: Ty,
    acc: nat,
    item: nat,
    c: Expr,
    items: Seq<Val>,
    keep: Seq<bool>,
)
    requires
        acc != item,
        absent(acc, c),
        keep.len() == items.len(),
        evals_to(p, env, xs, Val::List(items)),
        forall|k: int|
            0 <= k < items.len() ==> evals_to(p, #[trigger] env.insert(item, items[k]), c, Val::Bool(keep[k])),
    ensures
        evals_to(p, env, filter_collect(xs, t, acc, item, c), Val::List(kept(items, keep, items.len() as nat))),
{
    reveal_with_fuel(kept, 1);
    let n = items.len();
    let accs = Seq::new(n + 1, |k: int| Val::List(rev(kept(items, keep, k as nat))));
    assert(kept(items, keep, 0) =~= Seq::<Val>::empty());
    assert(rev(Seq::<Val>::empty()) =~= Seq::<Val>::empty());
    assert(accs[0] == Val::List(Seq::<Val>::empty()));
    assert forall|k: int| 0 <= k < n implies evals_to(
        p,
        #[trigger] env.insert(acc, accs[k]).insert(item, items[k]),
        filter_body(c, acc, item),
        accs[k + 1],
    ) by {
        filter_step(p, env, acc, item, c, items, keep, k as nat);
    }
    bs_nil(p, env, t);
    fold_expr_to(p, env, xs, Expr::List(t, Seq::empty()), acc, item, filter_body(c, acc, item), items, accs);
    assert(accs[n as int] == Val::List(rev(kept(items, keep, n))));
    let fe = Expr::Fold(
        Box::new(xs),
        Box::new(Expr::List(t, Seq::empty())),
        acc,
        item,
        Box::new(filter_body(c, acc, item)),
    );
    bs_reverse(p, env, fe, rev(kept(items, keep, n)));
    rev_rev(kept(items, keep, n));
    assert(rev(rev(kept(items, keep, n))) =~= kept(items, keep, n));
}

// ------------------------------------------------------------------ 短絡する if の畳み込み：any と all

/// 先頭 k 個のどれかが真。
pub open spec fn any_k(keep: Seq<bool>, k: nat) -> bool
    decreases k,
{
    if k == 0 {
        false
    } else {
        any_k(keep, (k - 1) as nat) || keep[(k - 1) as int]
    }
}

/// 先頭 k 個がすべて真。
pub open spec fn all_k(keep: Seq<bool>, k: nat) -> bool
    decreases k,
{
    if k == 0 {
        true
    } else {
        all_k(keep, (k - 1) as nat) && keep[(k - 1) as int]
    }
}

/// 本体 `if acc then b1 else b2` の一段：累積値 Bool(bs[k]) で選ばれた枝が Bool(bs[k + 1]) に評価されれば、
/// 本体全体も Bool(bs[k + 1]) に評価される。選ばれなかった枝は評価しなくてよい。
pub proof fn bool_step(
    p: Prog,
    env: Map<nat, Val>,
    acc: nat,
    item: nat,
    b1: Expr,
    b2: Expr,
    items: Seq<Val>,
    bs: Seq<bool>,
    k: nat,
)
    requires
        acc != item,
        bs.len() == items.len() + 1,
        k < items.len(),
        evals_to(
            p,
            env.insert(acc, Val::Bool(bs[k as int])).insert(item, items[k as int]),
            if bs[k as int] { b1 } else { b2 },
            Val::Bool(bs[k as int + 1]),
        ),
    ensures
        evals_to(
            p,
            env.insert(acc, Val::Bool(bs[k as int])).insert(item, items[k as int]),
            Expr::If(Box::new(Expr::Var(acc)), Box::new(b1), Box::new(b2)),
            Val::Bool(bs[k as int + 1]),
        ),
{
    let env2 = env.insert(acc, Val::Bool(bs[k as int])).insert(item, items[k as int]);
    assert(env2.contains_key(acc) && env2[acc] == Val::Bool(bs[k as int]));
    bs_var(p, env2, acc);
    bs_if(p, env2, Expr::Var(acc), b1, b2, bs[k as int], Val::Bool(bs[k as int + 1]));
}

/// 短絡する if の畳み込み：累積値 Bool(bs[k]) の各段で選ばれた枝の評価が Bool(bs[k + 1]) なら、
/// 畳み込みは Bool(bs[n]) に評価される。
pub proof fn bool_fold(
    p: Prog,
    env: Map<nat, Val>,
    xs: Expr,
    init: Expr,
    acc: nat,
    item: nat,
    b1: Expr,
    b2: Expr,
    items: Seq<Val>,
    bs: Seq<bool>,
)
    requires
        acc != item,
        bs.len() == items.len() + 1,
        evals_to(p, env, xs, Val::List(items)),
        evals_to(p, env, init, Val::Bool(bs[0])),
        forall|k: int|
            0 <= k < items.len() ==> evals_to(
                p,
                #[trigger] env.insert(acc, Val::Bool(bs[k])).insert(item, items[k]),
                if bs[k] { b1 } else { b2 },
                Val::Bool(bs[k + 1]),
            ),
    ensures
        evals_to(
            p,
            env,
            Expr::Fold(
                Box::new(xs),
                Box::new(init),
                acc,
                item,
                Box::new(Expr::If(Box::new(Expr::Var(acc)), Box::new(b1), Box::new(b2))),
            ),
            Val::Bool(bs[items.len() as int]),
        ),
{
    let body = Expr::If(Box::new(Expr::Var(acc)), Box::new(b1), Box::new(b2));
    let accs = Seq::new(items.len() + 1, |k: int| Val::Bool(bs[k]));
    assert(accs[0] == Val::Bool(bs[0]));
    assert forall|k: int| 0 <= k < items.len() implies evals_to(
        p,
        #[trigger] env.insert(acc, accs[k]).insert(item, items[k]),
        body,
        accs[k + 1],
    ) by {
        bool_step(p, env, acc, item, b1, b2, items, bs, k as nat);
    }
    fold_expr_to(p, env, xs, init, acc, item, body, items, accs);
}

/// any の形：`fold(xs, false, |acc, item| if acc then true else c)`。
pub open spec fn any_fold(xs: Expr, acc: nat, item: nat, c: Expr) -> Expr {
    Expr::Fold(
        Box::new(xs),
        Box::new(Expr::Bool(false)),
        acc,
        item,
        Box::new(Expr::If(Box::new(Expr::Var(acc)), Box::new(Expr::Bool(true)), Box::new(c))),
    )
}

/// any の意味：真になった後の要素では c を評価しない（短絡）。
pub proof fn any_meaning(
    p: Prog,
    env: Map<nat, Val>,
    xs: Expr,
    acc: nat,
    item: nat,
    c: Expr,
    items: Seq<Val>,
    keep: Seq<bool>,
)
    requires
        acc != item,
        absent(acc, c),
        keep.len() == items.len(),
        evals_to(p, env, xs, Val::List(items)),
        forall|k: int|
            0 <= k < items.len() && !any_k(keep, k as nat) ==> evals_to(
                p,
                #[trigger] env.insert(item, items[k]),
                c,
                Val::Bool(keep[k]),
            ),
    ensures
        evals_to(p, env, any_fold(xs, acc, item, c), Val::Bool(any_k(keep, items.len() as nat))),
{
    reveal_with_fuel(any_k, 2);
    let n = items.len();
    let bs = Seq::new(n + 1, |k: int| any_k(keep, k as nat));
    assert(bs[0] == false);
    assert forall|k: int| 0 <= k < n implies evals_to(
        p,
        #[trigger] env.insert(acc, Val::Bool(bs[k])).insert(item, items[k]),
        if bs[k] { Expr::Bool(true) } else { c },
        Val::Bool(bs[k + 1]),
    ) by {
        let env2 = env.insert(acc, Val::Bool(bs[k])).insert(item, items[k]);
        assert(bs[k + 1] == (bs[k] || keep[k]));
        if bs[k] {
            bs_leaf(p, env2, Expr::Bool(true));
        } else {
            evals_absent_ins(p, env, c, acc, Val::Bool(bs[k]), item, items[k], Val::Bool(keep[k]));
        }
    }
    bs_leaf(p, env, Expr::Bool(false));
    bool_fold(p, env, xs, Expr::Bool(false), acc, item, Expr::Bool(true), c, items, bs);
}

/// all の形：`fold(xs, true, |acc, item| if acc then c else false)`。
pub open spec fn all_fold(xs: Expr, acc: nat, item: nat, c: Expr) -> Expr {
    Expr::Fold(
        Box::new(xs),
        Box::new(Expr::Bool(true)),
        acc,
        item,
        Box::new(Expr::If(Box::new(Expr::Var(acc)), Box::new(c), Box::new(Expr::Bool(false)))),
    )
}

/// all の意味：偽になった後の要素では c を評価しない（短絡）。
pub proof fn all_meaning(
    p: Prog,
    env: Map<nat, Val>,
    xs: Expr,
    acc: nat,
    item: nat,
    c: Expr,
    items: Seq<Val>,
    keep: Seq<bool>,
)
    requires
        acc != item,
        absent(acc, c),
        keep.len() == items.len(),
        evals_to(p, env, xs, Val::List(items)),
        forall|k: int|
            0 <= k < items.len() && all_k(keep, k as nat) ==> evals_to(
                p,
                #[trigger] env.insert(item, items[k]),
                c,
                Val::Bool(keep[k]),
            ),
    ensures
        evals_to(p, env, all_fold(xs, acc, item, c), Val::Bool(all_k(keep, items.len() as nat))),
{
    reveal_with_fuel(all_k, 2);
    let n = items.len();
    let bs = Seq::new(n + 1, |k: int| all_k(keep, k as nat));
    assert(bs[0] == true);
    assert forall|k: int| 0 <= k < n implies evals_to(
        p,
        #[trigger] env.insert(acc, Val::Bool(bs[k])).insert(item, items[k]),
        if bs[k] { c } else { Expr::Bool(false) },
        Val::Bool(bs[k + 1]),
    ) by {
        let env2 = env.insert(acc, Val::Bool(bs[k])).insert(item, items[k]);
        assert(bs[k + 1] == (bs[k] && keep[k]));
        if bs[k] {
            evals_absent_ins(p, env, c, acc, Val::Bool(bs[k]), item, items[k], Val::Bool(keep[k]));
        } else {
            bs_leaf(p, env2, Expr::Bool(false));
        }
    }
    bs_leaf(p, env, Expr::Bool(true));
    bool_fold(p, env, xs, Expr::Bool(true), acc, item, c, Expr::Bool(false), items, bs);
}

// ------------------------------------------------------------------ 最初の一致を残す選択：find

/// 先頭 k 個のうち最初に述語を満たした要素（Some）。無ければ None。
pub open spec fn first_k(items: Seq<Val>, keep: Seq<bool>, k: nat) -> Val
    decreases k,
{
    if k == 0 {
        Val::None
    } else if first_k(items, keep, (k - 1) as nat) is Some {
        first_k(items, keep, (k - 1) as nat)
    } else if keep[(k - 1) as int] {
        Val::Some(Box::new(items[(k - 1) as int]))
    } else {
        Val::None
    }
}

/// 選択の本体：acc が Some ならそれを残し、None なら item が述語を満たすときだけ Some(item) にする。
pub open spec fn select_body(c: Expr, t: Ty, acc: nat, item: nat, x: nat) -> Expr {
    Expr::Match(
        Box::new(Expr::Var(acc)),
        Box::new(Expr::If(Box::new(c), Box::new(Expr::Some(Box::new(Expr::Var(item)))), Box::new(Expr::None(t)))),
        x,
        Box::new(Expr::Some(Box::new(Expr::Var(x)))),
    )
}

/// 選択の形：`fold(xs, None, |acc, item| select_body)`。
pub open spec fn find_fold(xs: Expr, t: Ty, acc: nat, item: nat, c: Expr, x: nat) -> Expr {
    Expr::Fold(Box::new(xs), Box::new(Expr::None(t)), acc, item, Box::new(select_body(c, t, acc, item, x)))
}

pub proof fn first_k_opt(items: Seq<Val>, keep: Seq<bool>, k: nat)
    ensures
        first_k(items, keep, k) is None || first_k(items, keep, k) is Some,
    decreases k,
{
    reveal_with_fuel(first_k, 1);
    if k > 0 {
        first_k_opt(items, keep, (k - 1) as nat);
    }
}

/// 選択の一段：acc が Some ならそのまま残し、None なら item を見て Some(item) か None にする。
pub proof fn select_step(
    p: Prog,
    env: Map<nat, Val>,
    acc: nat,
    item: nat,
    c: Expr,
    t: Ty,
    x: nat,
    items: Seq<Val>,
    keep: Seq<bool>,
    k: nat,
)
    requires
        acc != item,
        absent(acc, c),
        keep.len() == items.len(),
        k < items.len(),
        first_k(items, keep, k) is None ==> evals_to(
            p,
            env.insert(item, items[k as int]),
            c,
            Val::Bool(keep[k as int]),
        ),
    ensures
        evals_to(
            p,
            env.insert(acc, first_k(items, keep, k)).insert(item, items[k as int]),
            select_body(c, t, acc, item, x),
            first_k(items, keep, k + 1),
        ),
{
    reveal_with_fuel(first_k, 2);
    first_k_opt(items, keep, k);
    let a = first_k(items, keep, k);
    let u = items[k as int];
    let env2 = env.insert(acc, a).insert(item, u);
    let w = first_k(items, keep, k + 1);
    let nb = Expr::If(Box::new(c), Box::new(Expr::Some(Box::new(Expr::Var(item)))), Box::new(Expr::None(t)));
    let sm = Expr::Some(Box::new(Expr::Var(x)));
    assert(env2.contains_key(acc) && env2[acc] == a);
    bs_var(p, env2, acc);
    if a is Some {
        let v = *a->Some_0;
        let env3 = env2.insert(x, v);
        assert(env3.contains_key(x) && env3[x] == v);
        bs_var(p, env3, x);
        bs_some(p, env3, Expr::Var(x), v);
        assert(a == Val::Some(Box::new(v)));
        assert(w == a);
        bs_match(p, env2, Expr::Var(acc), nb, x, sm, a, w);
    } else {
        assert(a is None);
        evals_absent_ins(p, env, c, acc, a, item, u, Val::Bool(keep[k as int]));
        if keep[k as int] {
            bs_var(p, env2, item);
            bs_some(p, env2, Expr::Var(item), u);
            assert(w == Val::Some(Box::new(u)));
        } else {
            bs_leaf(p, env2, Expr::None(t));
            assert(w == Val::None);
        }
        bs_if(p, env2, c, Expr::Some(Box::new(Expr::Var(item))), Expr::None(t), keep[k as int], w);
        bs_match(p, env2, Expr::Var(acc), nb, x, sm, a, w);
    }
}

/// 選択の意味：各要素の述語の値は、それまでに一致が無いときにだけ要る。畳み込みは first_k(items, keep, n) に評価される。
pub proof fn find_meaning(
    p: Prog,
    env: Map<nat, Val>,
    xs: Expr,
    t: Ty,
    acc: nat,
    item: nat,
    x: nat,
    c: Expr,
    items: Seq<Val>,
    keep: Seq<bool>,
)
    requires
        acc != item,
        absent(acc, c),
        keep.len() == items.len(),
        evals_to(p, env, xs, Val::List(items)),
        forall|k: int|
            0 <= k < items.len() && first_k(items, keep, k as nat) is None ==> evals_to(
                p,
                #[trigger] env.insert(item, items[k]),
                c,
                Val::Bool(keep[k]),
            ),
    ensures
        evals_to(p, env, find_fold(xs, t, acc, item, c, x), first_k(items, keep, items.len() as nat)),
{
    reveal_with_fuel(first_k, 1);
    let n = items.len();
    let body = select_body(c, t, acc, item, x);
    let accs = Seq::new(n + 1, |k: int| first_k(items, keep, k as nat));
    assert(accs[0] == Val::None);
    assert forall|k: int| 0 <= k < n implies evals_to(
        p,
        #[trigger] env.insert(acc, accs[k]).insert(item, items[k]),
        body,
        accs[k + 1],
    ) by {
        select_step(p, env, acc, item, c, t, x, items, keep, k as nat);
    }
    bs_leaf(p, env, Expr::None(t));
    fold_expr_to(p, env, xs, Expr::None(t), acc, item, body, items, accs);
}

} // verus!
