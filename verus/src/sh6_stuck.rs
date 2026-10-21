//! SH6：hof の形ごとの行き詰まりの仮定の証明（段階 1b）。
//!
//! simulation.rs の行き詰まりの模擬（SH4）は、map・filter・find の行き詰まりの仮定（`ob_map_stuck`・`ob_filter_stuck`・
//! `ob_find_stuck`）を名前つきの仮定として受け取る。ここでは書換えの形の仮定 `hof_shapes`（sh6_obligations.rs）から
//! それらを示す（`sh6_ob_stuck`）。SH4 の仮定の全体 `sim_ok` は、構造の仮定 `sim_prog`・`homomorphic` と `hof_shapes`
//! から成り立つ（`sh6_sim_ok`）。
//!
//! any・all・sort_by の行き詰まりの仮定（`ob_any_stuck`・`ob_all_stuck`・`ob_sort_by_stuck`）は、現在の書換えで
//! 成り立つ範囲で述べて示す。源が行き詰まるのに写しが値を返す場合が残る（隙間）。隙間では写しの値を示す。
//! - any・all：最後の要素で述語が真偽でない値 v を返すと、源（xany・xall）は行き詰まるが、写しは v に評価される
//!   （畳み込みの累積値になる。`any_gap`・`all_gap`）。それより前の要素なら、次の要素の if で写しも行き詰まる。
//! - sort_by：要素が一つで鍵が整数でないと、源は行き詰まるが（int_seq の検査）、写しは [u] に評価される
//!   （鍵を比べない。`sort_gap`）。要素が二つ以上なら、整数でない鍵は挿入の比較（Lt）で写しも行き詰まる。
//! 隙間は型の付いたプログラムでは起きない（sh6_safe.rs）。

use crate::bigstep::*;
use crate::fold_meaning::*;
use crate::proof::*;
use crate::records_proof::*;
use crate::sh6_obligations::*;
use crate::simulation::*;
use crate::sortmeaning::*;
use crate::sortspec::*;
use crate::spec::*;
use crate::xsem::*;
use vstd::prelude::*;

verus! {

// ------------------------------------------------------------------ 燃料の選び方

/// 燃料 n で行き詰まれば、evals_stuck。
pub proof fn stuck_with(p: Prog, env: Map<nat, Val>, e: Expr, n: nat)
    requires
        eval(p, n, env, e) == Res::Stuck,
    ensures
        evals_stuck(p, env, e),
{
    assert(eval(p, n, env, e) == Res::Stuck);
}

/// 行き詰まる燃料を選ぶ。それ以上のどの燃料でも行き詰まる。
pub proof fn stuck_fuel(p: Prog, env: Map<nat, Val>, e: Expr) -> (n: nat)
    requires
        evals_stuck(p, env, e),
    ensures
        n > 0,
        forall|m: nat| n <= m ==> #[trigger] eval(p, m, env, e) == Res::Stuck,
{
    let n = choose|n: nat| #[trigger] eval(p, n, env, e) == Res::Stuck;
    assert forall|m: nat| n <= m implies #[trigger] eval(p, m, env, e) == Res::Stuck by {
        mono(p, n, m, env, e);
    }
    n
}

/// 値に評価される燃料を選ぶ。それ以上のどの燃料でも同じ値。
pub proof fn done_fuel(p: Prog, env: Map<nat, Val>, e: Expr, v: Val) -> (n: nat)
    requires
        evals_to(p, env, e, v),
    ensures
        n > 0,
        forall|m: nat| n <= m ==> #[trigger] eval(p, m, env, e) == Res::Done(v),
{
    let n = choose|n: nat| #[trigger] eval(p, n, env, e) == Res::Done(v);
    assert forall|m: nat| n <= m implies #[trigger] eval(p, m, env, e) == Res::Done(v) by {
        mono(p, n, m, env, e);
    }
    n
}

/// 値に評価される式は行き詰まらない（決定性）。
pub proof fn done_not_stuck(p: Prog, env: Map<nat, Val>, e: Expr, v: Val)
    requires
        evals_to(p, env, e, v),
    ensures
        !evals_stuck(p, env, e),
{
    if evals_stuck(p, env, e) {
        let n1 = choose|n: nat| #[trigger] eval(p, n, env, e) == Res::Done(v);
        let n2 = choose|n: nat| #[trigger] eval(p, n, env, e) == Res::Stuck;
        eval_deterministic(p, n1, n2, env, e);
    }
}

// ------------------------------------------------------------------ 行き詰まりの伝播（核の式）

pub proof fn let_stuck_a(p: Prog, env: Map<nat, Val>, x: nat, a: Expr, b: Expr)
    requires
        evals_stuck(p, env, a),
    ensures
        evals_stuck(p, env, Expr::Let(x, Box::new(a), Box::new(b))),
{
    let n = stuck_fuel(p, env, a);
    assert(eval(p, n, env, a) == Res::Stuck);
    stuck_with(p, env, Expr::Let(x, Box::new(a), Box::new(b)), n + 1);
}

pub proof fn let_stuck_b(p: Prog, env: Map<nat, Val>, x: nat, a: Expr, b: Expr, va: Val)
    requires
        evals_to(p, env, a, va),
        evals_stuck(p, env.insert(x, va), b),
    ensures
        evals_stuck(p, env, Expr::Let(x, Box::new(a), Box::new(b))),
{
    let n1 = done_fuel(p, env, a, va);
    let n2 = stuck_fuel(p, env.insert(x, va), b);
    let n = n1 + n2;
    assert(eval(p, n, env, a) == Res::Done(va));
    assert(eval(p, n, env.insert(x, va), b) == Res::Stuck);
    stuck_with(p, env, Expr::Let(x, Box::new(a), Box::new(b)), n + 1);
}

pub proof fn if_stuck_c(p: Prog, env: Map<nat, Val>, c: Expr, a: Expr, b: Expr)
    requires
        evals_stuck(p, env, c),
    ensures
        evals_stuck(p, env, Expr::If(Box::new(c), Box::new(a), Box::new(b))),
{
    let n = stuck_fuel(p, env, c);
    assert(eval(p, n, env, c) == Res::Stuck);
    stuck_with(p, env, Expr::If(Box::new(c), Box::new(a), Box::new(b)), n + 1);
}

pub proof fn if_nonbool(p: Prog, env: Map<nat, Val>, c: Expr, a: Expr, b: Expr, v: Val)
    requires
        evals_to(p, env, c, v),
        !(v is Bool),
    ensures
        evals_stuck(p, env, Expr::If(Box::new(c), Box::new(a), Box::new(b))),
{
    let n = done_fuel(p, env, c, v);
    assert(eval(p, n, env, c) == Res::Done(v));
    stuck_with(p, env, Expr::If(Box::new(c), Box::new(a), Box::new(b)), n + 1);
}

pub proof fn if_stuck_br(p: Prog, env: Map<nat, Val>, c: Expr, a: Expr, b: Expr, cv: bool)
    requires
        evals_to(p, env, c, Val::Bool(cv)),
        evals_stuck(p, env, if cv { a } else { b }),
    ensures
        evals_stuck(p, env, Expr::If(Box::new(c), Box::new(a), Box::new(b))),
{
    let br = if cv { a } else { b };
    let n1 = done_fuel(p, env, c, Val::Bool(cv));
    let n2 = stuck_fuel(p, env, br);
    let n = n1 + n2;
    assert(eval(p, n, env, c) == Res::Done(Val::Bool(cv)));
    assert(eval(p, n, env, br) == Res::Stuck);
    stuck_with(p, env, Expr::If(Box::new(c), Box::new(a), Box::new(b)), n + 1);
}

pub proof fn match_stuck_none(p: Prog, env: Map<nat, Val>, m: Expr, nb: Expr, x: nat, sm: Expr)
    requires
        evals_to(p, env, m, Val::None),
        evals_stuck(p, env, nb),
    ensures
        evals_stuck(p, env, Expr::Match(Box::new(m), Box::new(nb), x, Box::new(sm))),
{
    let n1 = done_fuel(p, env, m, Val::None);
    let n2 = stuck_fuel(p, env, nb);
    let n = n1 + n2;
    assert(eval(p, n, env, m) == Res::Done(Val::None));
    assert(eval(p, n, env, nb) == Res::Stuck);
    stuck_with(p, env, Expr::Match(Box::new(m), Box::new(nb), x, Box::new(sm)), n + 1);
}

pub proof fn match_stuck_some(p: Prog, env: Map<nat, Val>, m: Expr, nb: Expr, x: nat, sm: Expr, w: Val)
    requires
        evals_to(p, env, m, Val::Some(Box::new(w))),
        evals_stuck(p, env.insert(x, w), sm),
    ensures
        evals_stuck(p, env, Expr::Match(Box::new(m), Box::new(nb), x, Box::new(sm))),
{
    let n1 = done_fuel(p, env, m, Val::Some(Box::new(w)));
    let n2 = stuck_fuel(p, env.insert(x, w), sm);
    let n = n1 + n2;
    assert(eval(p, n, env, m) == Res::Done(Val::Some(Box::new(w))));
    assert(eval(p, n, env.insert(x, w), sm) == Res::Stuck);
    stuck_with(p, env, Expr::Match(Box::new(m), Box::new(nb), x, Box::new(sm)), n + 1);
}

/// 最初の引数が行き詰まれば、組込みの呼出しも行き詰まる。
pub proof fn builtin_stuck_first(p: Prog, env: Map<nat, Val>, b: Builtin, es: Seq<Expr>)
    requires
        es.len() > 0,
        evals_stuck(p, env, es[0]),
    ensures
        evals_stuck(p, env, Expr::Builtin(b, es)),
{
    let n = stuck_fuel(p, env, es[0]);
    assert(eval(p, n, env, es[0]) == Res::Stuck);
    assert(eval_args(p, n + 1, env, es, 0) == ResSeq::Stuck);
    stuck_with(p, env, Expr::Builtin(b, es), n + 2);
}

/// 引数が値に評価され、組込みの意味が行き詰まれば、呼出しも行き詰まる。
pub proof fn builtin_stuck_apply(p: Prog, env: Map<nat, Val>, b: Builtin, es: Seq<Expr>, vs: Seq<Val>)
    requires
        args_to(p, env, es, 0, vs),
        apply(b, vs) == Res::Stuck,
    ensures
        evals_stuck(p, env, Expr::Builtin(b, es)),
{
    let n = choose|n: nat| #[trigger] eval_args(p, n, env, es, 0) == ResSeq::Done(vs);
    stuck_with(p, env, Expr::Builtin(b, es), n + 1);
}

/// 畳み込みの段の列が、ある燃料で行き詰まる。
pub open spec fn fold_stuck(
    p: Prog,
    env: Map<nat, Val>,
    acc: nat,
    item: nat,
    body: Expr,
    items: Seq<Val>,
    j: nat,
    a: Val,
) -> bool {
    exists|n: nat| #[trigger] eval_fold(p, n, env, acc, item, body, items, j, a) == Res::Stuck
}

/// 列の式が行き詰まるかリストでなければ、畳み込みも行き詰まる。
pub proof fn fold_stuck_xs(p: Prog, env: Map<nat, Val>, xs: Expr, init: Expr, acc: nat, item: nat, body: Expr)
    requires
        list_fails(p, env, xs),
    ensures
        evals_stuck(p, env, Expr::Fold(Box::new(xs), Box::new(init), acc, item, Box::new(body))),
{
    let fe = Expr::Fold(Box::new(xs), Box::new(init), acc, item, Box::new(body));
    if evals_stuck(p, env, xs) {
        let n = stuck_fuel(p, env, xs);
        assert(eval(p, n, env, xs) == Res::Stuck);
        stuck_with(p, env, fe, n + 1);
    } else {
        let v = choose|v: Val| #![trigger evals_to(p, env, xs, v)] evals_to(p, env, xs, v) && !(v is List);
        let n = done_fuel(p, env, xs, v);
        assert(eval(p, n, env, xs) == Res::Done(v));
        stuck_with(p, env, fe, n + 1);
    }
}

/// 段 j から stop - 1 までの本体が accs[k + 1] に評価され、段 stop の本体が行き詰まれば、段の列は行き詰まる。
pub proof fn fold_stuck_steps(
    p: Prog,
    env: Map<nat, Val>,
    acc: nat,
    item: nat,
    body: Expr,
    items: Seq<Val>,
    accs: Seq<Val>,
    stop: nat,
    j: nat,
)
    requires
        j <= stop,
        stop < items.len(),
        accs.len() == stop + 1,
        forall|k: int|
            j <= k < stop ==> evals_to(
                p,
                #[trigger] env.insert(acc, accs[k]).insert(item, items[k]),
                body,
                accs[k + 1],
            ),
        evals_stuck(p, env.insert(acc, accs[stop as int]).insert(item, items[stop as int]), body),
    ensures
        fold_stuck(p, env, acc, item, body, items, j, accs[j as int]),
    decreases stop - j,
{
    let env2 = env.insert(acc, accs[j as int]).insert(item, items[j as int]);
    if j == stop {
        let n = stuck_fuel(p, env2, body);
        assert(eval(p, n, env2, body) == Res::Stuck);
        assert(eval_fold(p, n + 1, env, acc, item, body, items, j, accs[j as int]) == Res::Stuck);
    } else {
        fold_stuck_steps(p, env, acc, item, body, items, accs, stop, j + 1);
        let a1 = accs[(j + 1) as int];
        let n2 = choose|n: nat| #[trigger] eval_fold(p, n, env, acc, item, body, items, j + 1, a1) == Res::Stuck;
        assert(evals_to(p, env2, body, a1));
        let n1 = done_fuel(p, env2, body, a1);
        let n = n1 + n2;
        assert(eval(p, n, env2, body) == Res::Done(a1));
        mono_fold(p, n2, n, env, acc, item, body, items, j + 1, a1);
        assert(eval_fold(p, n + 1, env, acc, item, body, items, j, accs[j as int]) == Res::Stuck);
    }
}

/// 列が items に、初期値が v0 に評価され、段の列が行き詰まれば、畳み込みも行き詰まる。
pub proof fn fold_stuck_expr(
    p: Prog,
    env: Map<nat, Val>,
    xs: Expr,
    init: Expr,
    acc: nat,
    item: nat,
    body: Expr,
    items: Seq<Val>,
    v0: Val,
)
    requires
        evals_to(p, env, xs, Val::List(items)),
        evals_to(p, env, init, v0),
        fold_stuck(p, env, acc, item, body, items, 0, v0),
    ensures
        evals_stuck(p, env, Expr::Fold(Box::new(xs), Box::new(init), acc, item, Box::new(body))),
{
    let fe = Expr::Fold(Box::new(xs), Box::new(init), acc, item, Box::new(body));
    let n1 = done_fuel(p, env, xs, Val::List(items));
    let n2 = done_fuel(p, env, init, v0);
    let n3 = choose|n: nat| #[trigger] eval_fold(p, n, env, acc, item, body, items, 0, v0) == Res::Stuck;
    let n = n1 + n2 + n3;
    assert(eval(p, n, env, xs) == Res::Done(Val::List(items)));
    assert(eval(p, n, env, init) == Res::Done(v0));
    mono_fold(p, n3, n, env, acc, item, body, items, 0, v0);
    stuck_with(p, env, fe, n + 1);
}

/// acc を含まない式の評価は、acc への束縛を加えても変わらない（item への束縛は保つ。どの結果でも）。
pub proof fn eval_absent_ins(p: Prog, n: nat, env: Map<nat, Val>, e: Expr, acc: nat, a: Val, item: nat, u: Val)
    requires
        acc != item,
        absent(acc, e),
    ensures
        eval(p, n, env.insert(acc, a).insert(item, u), e) == eval(p, n, env.insert(item, u), e),
{
    eval_absent(p, n, env.insert(item, u), e, acc, a);
    assert(env.insert(acc, a).insert(item, u) =~= env.insert(item, u).insert(acc, a));
}

pub proof fn stuck_absent_ins(p: Prog, env: Map<nat, Val>, e: Expr, acc: nat, a: Val, item: nat, u: Val)
    requires
        acc != item,
        absent(acc, e),
        evals_stuck(p, env.insert(item, u), e),
    ensures
        evals_stuck(p, env.insert(acc, a).insert(item, u), e),
{
    let n = choose|n: nat| #[trigger] eval(p, n, env.insert(item, u), e) == Res::Stuck;
    eval_absent_ins(p, n, env, e, acc, a, item, u);
    stuck_with(p, env.insert(acc, a).insert(item, u), e, n);
}

// ------------------------------------------------------------------ map・filter・find の行き詰まり

pub proof fn map_stuck_list(p: Prog, rw: spec_fn(XExpr) -> Expr, env: Map<nat, Val>, xs: XExpr, x: nat, c: XExpr)
    requires
        hof_shapes(rw),
        list_fails(p, env, rw(xs)),
    ensures
        evals_stuck(p, env, rw(XExpr::Map(Box::new(xs), x, Box::new(c)))),
{
    let (t, acc) = map_names(rw, xs, x, c);
    let body = cons_body(rw(c), acc);
    let fe = Expr::Fold(Box::new(rw(xs)), Box::new(Expr::List(t, Seq::empty())), acc, x, Box::new(body));
    fold_stuck_xs(p, env, rw(xs), Expr::List(t, Seq::empty()), acc, x, body);
    assert(seq![fe][0] == fe);
    builtin_stuck_first(p, env, Builtin::Reverse, seq![fe]);
}

pub proof fn map_stuck_elem(
    p: Prog,
    rw: spec_fn(XExpr) -> Expr,
    env: Map<nat, Val>,
    xs: XExpr,
    x: nat,
    c: XExpr,
    items: Seq<Val>,
    stop: nat,
)
    requires
        hof_shapes(rw),
        evals_to(p, env, rw(xs), Val::List(items)),
        map_stuck(p, rw, env, x, c, items, 0, stop),
    ensures
        evals_stuck(p, env, rw(XExpr::Map(Box::new(xs), x, Box::new(c)))),
{
    reveal_with_fuel(rev_pref, 1);
    let (t, acc) = map_names(rw, xs, x, c);
    let body = cons_body(rw(c), acc);
    let gv = Seq::new(
        items.len(),
        |k: int|
            choose|v: Val|
                #![trigger evals_to(p, env.insert(x, items[k]), rw(c), v)]
                evals_to(p, env.insert(x, items[k]), rw(c), v),
    );
    let accs = Seq::new(stop + 1, |k: int| Val::List(rev_pref(gv, k as nat)));
    assert forall|k: int| 0 <= k < stop implies evals_to(
        p,
        #[trigger] env.insert(acc, accs[k]).insert(x, items[k]),
        body,
        accs[k + 1],
    ) by {
        assert(has_value(p, env.insert(x, items[k]), rw(c)));
        assert(evals_to(p, env.insert(x, items[k]), rw(c), gv[k]));
        collect_step(p, env, acc, x, rw(c), gv, items, k as nat);
    }
    let u = items[stop as int];
    let env2 = env.insert(acc, accs[stop as int]).insert(x, u);
    stuck_absent_ins(p, env, rw(c), acc, accs[stop as int], x, u);
    assert(seq![rw(c), Expr::Var(acc)][0] == rw(c));
    builtin_stuck_first(p, env2, Builtin::Cons, seq![rw(c), Expr::Var(acc)]);
    fold_stuck_steps(p, env, acc, x, body, items, accs, stop, 0);
    bs_nil(p, env, t);
    assert(accs[0] == Val::List(Seq::<Val>::empty()));
    fold_stuck_expr(p, env, rw(xs), Expr::List(t, Seq::empty()), acc, x, body, items, accs[0]);
    let fe = Expr::Fold(Box::new(rw(xs)), Box::new(Expr::List(t, Seq::empty())), acc, x, Box::new(body));
    assert(seq![fe][0] == fe);
    builtin_stuck_first(p, env, Builtin::Reverse, seq![fe]);
}

pub proof fn filter_stuck_list(p: Prog, rw: spec_fn(XExpr) -> Expr, env: Map<nat, Val>, xs: XExpr, x: nat, c: XExpr)
    requires
        hof_shapes(rw),
        list_fails(p, env, rw(xs)),
    ensures
        evals_stuck(p, env, rw(XExpr::Filter(Box::new(xs), x, Box::new(c)))),
{
    let (t, acc) = filter_names(rw, xs, x, c);
    let body = filter_body(rw(c), acc, x);
    let fe = Expr::Fold(Box::new(rw(xs)), Box::new(Expr::List(t, Seq::empty())), acc, x, Box::new(body));
    fold_stuck_xs(p, env, rw(xs), Expr::List(t, Seq::empty()), acc, x, body);
    assert(seq![fe][0] == fe);
    builtin_stuck_first(p, env, Builtin::Reverse, seq![fe]);
}

/// 述語が真偽を返さなければ（行き詰まるか真偽でない値）、acc を加えた環境で if c ... は行き詰まる。
pub proof fn if_pred_fails(
    p: Prog,
    env: Map<nat, Val>,
    c: Expr,
    acc: nat,
    a: Val,
    item: nat,
    u: Val,
    th: Expr,
    el: Expr,
)
    requires
        acc != item,
        absent(acc, c),
        pred_fails(p, env.insert(item, u), c),
    ensures
        evals_stuck(p, env.insert(acc, a).insert(item, u), Expr::If(Box::new(c), Box::new(th), Box::new(el))),
{
    let env2 = env.insert(acc, a).insert(item, u);
    if evals_stuck(p, env.insert(item, u), c) {
        stuck_absent_ins(p, env, c, acc, a, item, u);
        if_stuck_c(p, env2, c, th, el);
    } else {
        let v = choose|v: Val| #![trigger evals_to(p, env.insert(item, u), c, v)] evals_to(p, env.insert(item, u), c, v) && !(v is Bool);
        evals_absent_ins(p, env, c, acc, a, item, u, v);
        if_nonbool(p, env2, c, th, el, v);
    }
}

pub proof fn filter_stuck_elem(
    p: Prog,
    rw: spec_fn(XExpr) -> Expr,
    env: Map<nat, Val>,
    xs: XExpr,
    x: nat,
    c: XExpr,
    items: Seq<Val>,
    stop: nat,
)
    requires
        hof_shapes(rw),
        evals_to(p, env, rw(xs), Val::List(items)),
        filter_stuck(p, rw, env, x, c, items, 0, stop),
    ensures
        evals_stuck(p, env, rw(XExpr::Filter(Box::new(xs), x, Box::new(c)))),
{
    reveal_with_fuel(kept, 1);
    let (t, acc) = filter_names(rw, xs, x, c);
    let body = filter_body(rw(c), acc, x);
    let keep = Seq::new(
        items.len(),
        |k: int|
            choose|b: bool|
                #![trigger evals_to(p, env.insert(x, items[k]), rw(c), Val::Bool(b))]
                evals_to(p, env.insert(x, items[k]), rw(c), Val::Bool(b)),
    );
    let accs = Seq::new(stop + 1, |k: int| Val::List(rev(kept(items, keep, k as nat))));
    assert forall|k: int| 0 <= k < stop implies evals_to(
        p,
        #[trigger] env.insert(acc, accs[k]).insert(x, items[k]),
        body,
        accs[k + 1],
    ) by {
        assert(has_bool(p, env.insert(x, items[k]), rw(c)));
        assert(evals_to(p, env.insert(x, items[k]), rw(c), Val::Bool(keep[k])));
        filter_step(p, env, acc, x, rw(c), items, keep, k as nat);
    }
    let u = items[stop as int];
    let cons_x = Expr::Builtin(Builtin::Cons, seq![Expr::Var(x), Expr::Var(acc)]);
    if_pred_fails(p, env, rw(c), acc, accs[stop as int], x, u, cons_x, Expr::Var(acc));
    fold_stuck_steps(p, env, acc, x, body, items, accs, stop, 0);
    bs_nil(p, env, t);
    assert(rev(Seq::<Val>::empty()) =~= Seq::<Val>::empty());
    assert(accs[0] == Val::List(Seq::<Val>::empty()));
    fold_stuck_expr(p, env, rw(xs), Expr::List(t, Seq::empty()), acc, x, body, items, accs[0]);
    let fe = Expr::Fold(Box::new(rw(xs)), Box::new(Expr::List(t, Seq::empty())), acc, x, Box::new(body));
    assert(seq![fe][0] == fe);
    builtin_stuck_first(p, env, Builtin::Reverse, seq![fe]);
}

pub proof fn find_stuck_list(p: Prog, rw: spec_fn(XExpr) -> Expr, env: Map<nat, Val>, xs: XExpr, x: nat, c: XExpr)
    requires
        hof_shapes(rw),
        list_fails(p, env, rw(xs)),
    ensures
        evals_stuck(p, env, rw(XExpr::Find(Box::new(xs), x, Box::new(c)))),
{
    let (t, acc, y) = find_names(rw, xs, x, c);
    fold_stuck_xs(p, env, rw(xs), Expr::None(t), acc, x, select_body(rw(c), t, acc, x, y));
}

pub proof fn find_stuck_elem(
    p: Prog,
    rw: spec_fn(XExpr) -> Expr,
    env: Map<nat, Val>,
    xs: XExpr,
    x: nat,
    c: XExpr,
    items: Seq<Val>,
    stop: nat,
)
    requires
        hof_shapes(rw),
        evals_to(p, env, rw(xs), Val::List(items)),
        find_stuck(p, rw, env, x, c, items, 0, stop),
    ensures
        evals_stuck(p, env, rw(XExpr::Find(Box::new(xs), x, Box::new(c)))),
{
    let (t, acc, y) = find_names(rw, xs, x, c);
    let body = select_body(rw(c), t, acc, x, y);
    let n = items.len() as nat;
    let keep = mark(n, stop);
    let accs = Seq::new(stop + 1, |k: int| Val::None);
    assert forall|k: int| 0 <= k < stop implies evals_to(
        p,
        #[trigger] env.insert(acc, accs[k]).insert(x, items[k]),
        body,
        accs[k + 1],
    ) by {
        first_k_mark(items, stop, k as nat);
        first_k_mark(items, stop, (k + 1) as nat);
        assert(keep[k] == false);
        assert(evals_to(p, env.insert(x, items[k]), rw(c), Val::Bool(false)));
        select_step(p, env, acc, x, rw(c), t, y, items, keep, k as nat);
    }
    let u = items[stop as int];
    let env2 = env.insert(acc, Val::None).insert(x, u);
    let nb = Expr::If(Box::new(rw(c)), Box::new(Expr::Some(Box::new(Expr::Var(x)))), Box::new(Expr::None(t)));
    if_pred_fails(p, env, rw(c), acc, Val::None, x, u, Expr::Some(Box::new(Expr::Var(x))), Expr::None(t));
    assert(env2.contains_key(acc) && env2[acc] == Val::None);
    bs_var(p, env2, acc);
    match_stuck_none(p, env2, Expr::Var(acc), nb, y, Expr::Some(Box::new(Expr::Var(y))));
    assert(accs[stop as int] == Val::None);
    fold_stuck_steps(p, env, acc, x, body, items, accs, stop, 0);
    bs_leaf(p, env, Expr::None(t));
    fold_stuck_expr(p, env, rw(xs), Expr::None(t), acc, x, body, items, Val::None);
}

pub proof fn ob_map_stuck_holds(p: Prog, rw: spec_fn(XExpr) -> Expr)
    requires
        hof_shapes(rw),
    ensures
        ob_map_stuck(p, rw),
{
    assert forall|env: Map<nat, Val>, xs: XExpr, x: nat, c: XExpr|
        #![trigger evals_stuck(p, env, rw(XExpr::Map(Box::new(xs), x, Box::new(c))))]
        list_fails(p, env, rw(xs)) implies evals_stuck(p, env, rw(XExpr::Map(Box::new(xs), x, Box::new(c)))) by {
        map_stuck_list(p, rw, env, xs, x, c);
    }
    assert forall|env: Map<nat, Val>, xs: XExpr, x: nat, c: XExpr, items: Seq<Val>, stop: nat|
        #![trigger evals_stuck(p, env, rw(XExpr::Map(Box::new(xs), x, Box::new(c)))), map_stuck(p, rw, env, x, c, items, 0, stop)]
        evals_to(p, env, rw(xs), Val::List(items)) && map_stuck(p, rw, env, x, c, items, 0, stop) implies evals_stuck(
            p,
            env,
            rw(XExpr::Map(Box::new(xs), x, Box::new(c))),
        ) by {
        map_stuck_elem(p, rw, env, xs, x, c, items, stop);
    }
}

pub proof fn ob_filter_stuck_holds(p: Prog, rw: spec_fn(XExpr) -> Expr)
    requires
        hof_shapes(rw),
    ensures
        ob_filter_stuck(p, rw),
{
    assert forall|env: Map<nat, Val>, xs: XExpr, x: nat, c: XExpr|
        #![trigger evals_stuck(p, env, rw(XExpr::Filter(Box::new(xs), x, Box::new(c))))]
        list_fails(p, env, rw(xs)) implies evals_stuck(p, env, rw(XExpr::Filter(Box::new(xs), x, Box::new(c)))) by {
        filter_stuck_list(p, rw, env, xs, x, c);
    }
    assert forall|env: Map<nat, Val>, xs: XExpr, x: nat, c: XExpr, items: Seq<Val>, stop: nat|
        #![trigger evals_stuck(p, env, rw(XExpr::Filter(Box::new(xs), x, Box::new(c)))), filter_stuck(p, rw, env, x, c, items, 0, stop)]
        evals_to(p, env, rw(xs), Val::List(items)) && filter_stuck(p, rw, env, x, c, items, 0, stop) implies evals_stuck(
            p,
            env,
            rw(XExpr::Filter(Box::new(xs), x, Box::new(c))),
        ) by {
        filter_stuck_elem(p, rw, env, xs, x, c, items, stop);
    }
}

pub proof fn ob_find_stuck_holds(p: Prog, rw: spec_fn(XExpr) -> Expr)
    requires
        hof_shapes(rw),
    ensures
        ob_find_stuck(p, rw),
{
    assert forall|env: Map<nat, Val>, xs: XExpr, x: nat, c: XExpr|
        #![trigger evals_stuck(p, env, rw(XExpr::Find(Box::new(xs), x, Box::new(c))))]
        list_fails(p, env, rw(xs)) implies evals_stuck(p, env, rw(XExpr::Find(Box::new(xs), x, Box::new(c)))) by {
        find_stuck_list(p, rw, env, xs, x, c);
    }
    assert forall|env: Map<nat, Val>, xs: XExpr, x: nat, c: XExpr, items: Seq<Val>, stop: nat|
        #![trigger evals_stuck(p, env, rw(XExpr::Find(Box::new(xs), x, Box::new(c)))), find_stuck(p, rw, env, x, c, items, 0, stop)]
        evals_to(p, env, rw(xs), Val::List(items)) && find_stuck(p, rw, env, x, c, items, 0, stop) implies evals_stuck(
            p,
            env,
            rw(XExpr::Find(Box::new(xs), x, Box::new(c))),
        ) by {
        find_stuck_elem(p, rw, env, xs, x, c, items, stop);
    }
}

// ------------------------------------------------------------------ any・all の行き詰まり

/// any・all の述語の止まり方：行き詰まるか、最後の要素でなければ真偽でない値に評価される。
/// 最後の要素で真偽でない値を返す場合は含めない（写しは値に評価される。any_gap・all_gap）。
pub open spec fn pred_fails_mid(p: Prog, env: Map<nat, Val>, e: Expr, last: bool) -> bool {
    evals_stuck(p, env, e) || (!last && exists|v: Val|
        #![trigger evals_to(p, env, e, v)]
        evals_to(p, env, e, v) && !(v is Bool))
}

/// any の止まり方：j から stop - 1 までの述語は偽に評価され、stop の述語は pred_fails_mid。
pub open spec fn any_stuck(
    p: Prog,
    rw: spec_fn(XExpr) -> Expr,
    env: Map<nat, Val>,
    x: nat,
    c: XExpr,
    items: Seq<Val>,
    j: nat,
    stop: nat,
) -> bool {
    &&& j <= stop
    &&& stop < items.len()
    &&& forall|k: int| j <= k < stop ==> evals_to(p, #[trigger] env.insert(x, items[k]), rw(c), Val::Bool(false))
    &&& pred_fails_mid(p, env.insert(x, items[stop as int]), rw(c), stop + 1 == items.len())
}

/// all の止まり方：j から stop - 1 までの述語は真に評価され、stop の述語は pred_fails_mid。
pub open spec fn all_stuck(
    p: Prog,
    rw: spec_fn(XExpr) -> Expr,
    env: Map<nat, Val>,
    x: nat,
    c: XExpr,
    items: Seq<Val>,
    j: nat,
    stop: nat,
) -> bool {
    &&& j <= stop
    &&& stop < items.len()
    &&& forall|k: int| j <= k < stop ==> evals_to(p, #[trigger] env.insert(x, items[k]), rw(c), Val::Bool(true))
    &&& pred_fails_mid(p, env.insert(x, items[stop as int]), rw(c), stop + 1 == items.len())
}

/// any の行き詰まり：列の式が行き詰まるかリストでなければ、写しも行き詰まる。列が items に評価され、
/// 要素 stop で any_stuck なら、写しも行き詰まる（ob-any-stuck）。
pub open spec fn ob_any_stuck(p: Prog, rw: spec_fn(XExpr) -> Expr) -> bool {
    &&& forall|env: Map<nat, Val>, xs: XExpr, x: nat, c: XExpr|
        #![trigger evals_stuck(p, env, rw(XExpr::Any(Box::new(xs), x, Box::new(c))))]
        list_fails(p, env, rw(xs)) ==> evals_stuck(p, env, rw(XExpr::Any(Box::new(xs), x, Box::new(c))))
    &&& forall|env: Map<nat, Val>, xs: XExpr, x: nat, c: XExpr, items: Seq<Val>, stop: nat|
        #![trigger evals_stuck(p, env, rw(XExpr::Any(Box::new(xs), x, Box::new(c)))), any_stuck(p, rw, env, x, c, items, 0, stop)]
        evals_to(p, env, rw(xs), Val::List(items)) && any_stuck(p, rw, env, x, c, items, 0, stop)
            ==> evals_stuck(p, env, rw(XExpr::Any(Box::new(xs), x, Box::new(c))))
}

/// all の行き詰まり（ob-all-stuck）。any と同じ形。
pub open spec fn ob_all_stuck(p: Prog, rw: spec_fn(XExpr) -> Expr) -> bool {
    &&& forall|env: Map<nat, Val>, xs: XExpr, x: nat, c: XExpr|
        #![trigger evals_stuck(p, env, rw(XExpr::All(Box::new(xs), x, Box::new(c))))]
        list_fails(p, env, rw(xs)) ==> evals_stuck(p, env, rw(XExpr::All(Box::new(xs), x, Box::new(c))))
    &&& forall|env: Map<nat, Val>, xs: XExpr, x: nat, c: XExpr, items: Seq<Val>, stop: nat|
        #![trigger evals_stuck(p, env, rw(XExpr::All(Box::new(xs), x, Box::new(c)))), all_stuck(p, rw, env, x, c, items, 0, stop)]
        evals_to(p, env, rw(xs), Val::List(items)) && all_stuck(p, rw, env, x, c, items, 0, stop)
            ==> evals_stuck(p, env, rw(XExpr::All(Box::new(xs), x, Box::new(c))))
}

/// 本体 `if acc then b1 else b2` の一段：累積値 Bool(cv) で選ばれた枝が w に評価されれば、本体も w に評価される。
pub proof fn if_acc_step(
    p: Prog,
    env: Map<nat, Val>,
    acc: nat,
    cv: bool,
    item: nat,
    u: Val,
    b1: Expr,
    b2: Expr,
    w: Val,
)
    requires
        acc != item,
        evals_to(p, env.insert(acc, Val::Bool(cv)).insert(item, u), if cv { b1 } else { b2 }, w),
    ensures
        evals_to(
            p,
            env.insert(acc, Val::Bool(cv)).insert(item, u),
            Expr::If(Box::new(Expr::Var(acc)), Box::new(b1), Box::new(b2)),
            w,
        ),
{
    let env2 = env.insert(acc, Val::Bool(cv)).insert(item, u);
    assert(env2.contains_key(acc) && env2[acc] == Val::Bool(cv));
    bs_var(p, env2, acc);
    bs_if(p, env2, Expr::Var(acc), b1, b2, cv, w);
}

/// 同じ形で、選ばれた枝が行き詰まれば、本体も行き詰まる。
pub proof fn if_acc_stuck(p: Prog, env: Map<nat, Val>, acc: nat, cv: bool, item: nat, u: Val, b1: Expr, b2: Expr)
    requires
        acc != item,
        evals_stuck(p, env.insert(acc, Val::Bool(cv)).insert(item, u), if cv { b1 } else { b2 }),
    ensures
        evals_stuck(
            p,
            env.insert(acc, Val::Bool(cv)).insert(item, u),
            Expr::If(Box::new(Expr::Var(acc)), Box::new(b1), Box::new(b2)),
        ),
{
    let env2 = env.insert(acc, Val::Bool(cv)).insert(item, u);
    assert(env2.contains_key(acc) && env2[acc] == Val::Bool(cv));
    bs_var(p, env2, acc);
    if_stuck_br(p, env2, Expr::Var(acc), b1, b2, cv);
}

/// 累積値が真偽でない値 v なら、本体 `if acc then ... else ...` は行き詰まる。
pub proof fn if_acc_nonbool(p: Prog, env: Map<nat, Val>, acc: nat, v: Val, item: nat, u: Val, b1: Expr, b2: Expr)
    requires
        acc != item,
        !(v is Bool),
    ensures
        evals_stuck(p, env.insert(acc, v).insert(item, u), Expr::If(Box::new(Expr::Var(acc)), Box::new(b1), Box::new(b2))),
{
    let env2 = env.insert(acc, v).insert(item, u);
    assert(env2.contains_key(acc) && env2[acc] == v);
    bs_var(p, env2, acc);
    if_nonbool(p, env2, Expr::Var(acc), b1, b2, v);
}

/// 短絡する if の畳み込み（any は cv = false、all は cv = true）の行き詰まり：stop より前の述語は Bool(cv)、
/// stop の述語は pred_fails_mid。本体は cv のとき c を選ぶ形 `if acc then b1 else b2`（選ばれる枝が c）。
pub proof fn bool_fold_stuck(
    p: Prog,
    env: Map<nat, Val>,
    xs: Expr,
    acc: nat,
    item: nat,
    c: Expr,
    cv: bool,
    b1: Expr,
    b2: Expr,
    items: Seq<Val>,
    stop: nat,
)
    requires
        acc != item,
        absent(acc, c),
        (if cv { b1 } else { b2 }) == c,
        evals_to(p, env, xs, Val::List(items)),
        stop < items.len(),
        forall|k: int| 0 <= k < stop ==> evals_to(p, #[trigger] env.insert(item, items[k]), c, Val::Bool(cv)),
        pred_fails_mid(p, env.insert(item, items[stop as int]), c, stop + 1 == items.len()),
    ensures
        evals_stuck(
            p,
            env,
            Expr::Fold(
                Box::new(xs),
                Box::new(Expr::Bool(cv)),
                acc,
                item,
                Box::new(Expr::If(Box::new(Expr::Var(acc)), Box::new(b1), Box::new(b2))),
            ),
        ),
{
    let body = Expr::If(Box::new(Expr::Var(acc)), Box::new(b1), Box::new(b2));
    let a0 = Val::Bool(cv);
    let u = items[stop as int];
    assert forall|k: int| 0 <= k < stop implies evals_to(p, #[trigger] env.insert(acc, a0).insert(item, items[k]), body, a0) by {
        evals_absent_ins(p, env, c, acc, a0, item, items[k], a0);
        if_acc_step(p, env, acc, cv, item, items[k], b1, b2, a0);
    }
    bs_leaf(p, env, Expr::Bool(cv));
    if evals_stuck(p, env.insert(item, u), c) {
        let accs = Seq::new(stop + 1, |k: int| a0);
        stuck_absent_ins(p, env, c, acc, a0, item, u);
        if_acc_stuck(p, env, acc, cv, item, u, b1, b2);
        assert forall|k: int| 0 <= k < stop implies evals_to(
            p,
            #[trigger] env.insert(acc, accs[k]).insert(item, items[k]),
            body,
            accs[k + 1],
        ) by {
            assert(accs[k] == a0 && accs[k + 1] == a0);
            assert(evals_to(p, env.insert(acc, a0).insert(item, items[k]), body, a0));
        }
        fold_stuck_steps(p, env, acc, item, body, items, accs, stop, 0);
        fold_stuck_expr(p, env, xs, Expr::Bool(cv), acc, item, body, items, a0);
    } else {
        let v = choose|v: Val| #![trigger evals_to(p, env.insert(item, u), c, v)] evals_to(p, env.insert(item, u), c, v) && !(v is Bool);
        assert(stop + 1 < items.len());
        let accs = Seq::new(stop + 2, |k: int| if k <= stop { a0 } else { v });
        evals_absent_ins(p, env, c, acc, a0, item, u, v);
        if_acc_step(p, env, acc, cv, item, u, b1, b2, v);
        if_acc_nonbool(p, env, acc, v, item, items[(stop + 1) as int], b1, b2);
        assert forall|k: int| 0 <= k < stop + 1 implies evals_to(
            p,
            #[trigger] env.insert(acc, accs[k]).insert(item, items[k]),
            body,
            accs[k + 1],
        ) by {
            if k < stop {
                assert(accs[k] == a0 && accs[k + 1] == a0);
                assert(evals_to(p, env.insert(acc, a0).insert(item, items[k]), body, a0));
            } else {
                assert(k == stop);
                assert(accs[k] == a0 && accs[k + 1] == v);
            }
        }
        assert(accs[(stop + 1) as int] == v);
        fold_stuck_steps(p, env, acc, item, body, items, accs, stop + 1, 0);
        fold_stuck_expr(p, env, xs, Expr::Bool(cv), acc, item, body, items, a0);
    }
}

pub proof fn ob_any_stuck_holds(p: Prog, rw: spec_fn(XExpr) -> Expr)
    requires
        hof_shapes(rw),
    ensures
        ob_any_stuck(p, rw),
{
    assert forall|env: Map<nat, Val>, xs: XExpr, x: nat, c: XExpr|
        #![trigger evals_stuck(p, env, rw(XExpr::Any(Box::new(xs), x, Box::new(c))))]
        list_fails(p, env, rw(xs)) implies evals_stuck(p, env, rw(XExpr::Any(Box::new(xs), x, Box::new(c)))) by {
        let acc = any_names(rw, xs, x, c);
        fold_stuck_xs(
            p,
            env,
            rw(xs),
            Expr::Bool(false),
            acc,
            x,
            Expr::If(Box::new(Expr::Var(acc)), Box::new(Expr::Bool(true)), Box::new(rw(c))),
        );
    }
    assert forall|env: Map<nat, Val>, xs: XExpr, x: nat, c: XExpr, items: Seq<Val>, stop: nat|
        #![trigger evals_stuck(p, env, rw(XExpr::Any(Box::new(xs), x, Box::new(c)))), any_stuck(p, rw, env, x, c, items, 0, stop)]
        evals_to(p, env, rw(xs), Val::List(items)) && any_stuck(p, rw, env, x, c, items, 0, stop) implies evals_stuck(
            p,
            env,
            rw(XExpr::Any(Box::new(xs), x, Box::new(c))),
        ) by {
        let acc = any_names(rw, xs, x, c);
        bool_fold_stuck(p, env, rw(xs), acc, x, rw(c), false, Expr::Bool(true), rw(c), items, stop);
    }
}

pub proof fn ob_all_stuck_holds(p: Prog, rw: spec_fn(XExpr) -> Expr)
    requires
        hof_shapes(rw),
    ensures
        ob_all_stuck(p, rw),
{
    assert forall|env: Map<nat, Val>, xs: XExpr, x: nat, c: XExpr|
        #![trigger evals_stuck(p, env, rw(XExpr::All(Box::new(xs), x, Box::new(c))))]
        list_fails(p, env, rw(xs)) implies evals_stuck(p, env, rw(XExpr::All(Box::new(xs), x, Box::new(c)))) by {
        let acc = all_names(rw, xs, x, c);
        fold_stuck_xs(
            p,
            env,
            rw(xs),
            Expr::Bool(true),
            acc,
            x,
            Expr::If(Box::new(Expr::Var(acc)), Box::new(rw(c)), Box::new(Expr::Bool(false))),
        );
    }
    assert forall|env: Map<nat, Val>, xs: XExpr, x: nat, c: XExpr, items: Seq<Val>, stop: nat|
        #![trigger evals_stuck(p, env, rw(XExpr::All(Box::new(xs), x, Box::new(c)))), all_stuck(p, rw, env, x, c, items, 0, stop)]
        evals_to(p, env, rw(xs), Val::List(items)) && all_stuck(p, rw, env, x, c, items, 0, stop) implies evals_stuck(
            p,
            env,
            rw(XExpr::All(Box::new(xs), x, Box::new(c))),
        ) by {
        let acc = all_names(rw, xs, x, c);
        bool_fold_stuck(p, env, rw(xs), acc, x, rw(c), true, rw(c), Expr::Bool(false), items, stop);
    }
}

/// 短絡する if の畳み込みの最後の要素：それより前の述語が Bool(cv)、最後の述語が値 v なら、畳み込みは v。
pub proof fn bool_fold_last(
    p: Prog,
    env: Map<nat, Val>,
    xs: Expr,
    acc: nat,
    item: nat,
    c: Expr,
    cv: bool,
    b1: Expr,
    b2: Expr,
    items: Seq<Val>,
    v: Val,
)
    requires
        acc != item,
        absent(acc, c),
        (if cv { b1 } else { b2 }) == c,
        evals_to(p, env, xs, Val::List(items)),
        items.len() > 0,
        forall|k: int| 0 <= k < items.len() - 1 ==> evals_to(p, #[trigger] env.insert(item, items[k]), c, Val::Bool(cv)),
        evals_to(p, env.insert(item, items[items.len() - 1]), c, v),
    ensures
        evals_to(
            p,
            env,
            Expr::Fold(
                Box::new(xs),
                Box::new(Expr::Bool(cv)),
                acc,
                item,
                Box::new(Expr::If(Box::new(Expr::Var(acc)), Box::new(b1), Box::new(b2))),
            ),
            v,
        ),
{
    let body = Expr::If(Box::new(Expr::Var(acc)), Box::new(b1), Box::new(b2));
    let a0 = Val::Bool(cv);
    let n = items.len();
    let accs = Seq::new(n + 1, |k: int| if k < n { a0 } else { v });
    assert forall|k: int| 0 <= k < n implies evals_to(
        p,
        #[trigger] env.insert(acc, accs[k]).insert(item, items[k]),
        body,
        accs[k + 1],
    ) by {
        assert(accs[k] == a0);
        if k < n - 1 {
            assert(accs[k + 1] == a0);
            evals_absent_ins(p, env, c, acc, a0, item, items[k], a0);
            if_acc_step(p, env, acc, cv, item, items[k], b1, b2, a0);
        } else {
            assert(k == n - 1);
            assert(accs[k + 1] == v);
            evals_absent_ins(p, env, c, acc, a0, item, items[k], v);
            if_acc_step(p, env, acc, cv, item, items[k], b1, b2, v);
        }
    }
    bs_leaf(p, env, Expr::Bool(cv));
    assert(accs[0] == a0);
    assert(accs[n as int] == v);
    fold_expr_to(p, env, xs, Expr::Bool(cv), acc, item, body, items, accs);
}

/// any の隙間：最後の要素の述語が値 v を返せば（それより前は偽）、写しの any は v に評価され、行き詰まらない。
/// v が真偽でないとき、源の xany は行き詰まる。
pub proof fn any_gap(
    p: Prog,
    rw: spec_fn(XExpr) -> Expr,
    env: Map<nat, Val>,
    xs: XExpr,
    x: nat,
    c: XExpr,
    items: Seq<Val>,
    v: Val,
)
    requires
        hof_shapes(rw),
        evals_to(p, env, rw(xs), Val::List(items)),
        items.len() > 0,
        forall|k: int| 0 <= k < items.len() - 1 ==> evals_to(p, #[trigger] env.insert(x, items[k]), rw(c), Val::Bool(false)),
        evals_to(p, env.insert(x, items[items.len() - 1]), rw(c), v),
    ensures
        evals_to(p, env, rw(XExpr::Any(Box::new(xs), x, Box::new(c))), v),
        !evals_stuck(p, env, rw(XExpr::Any(Box::new(xs), x, Box::new(c)))),
{
    let acc = any_names(rw, xs, x, c);
    bool_fold_last(p, env, rw(xs), acc, x, rw(c), false, Expr::Bool(true), rw(c), items, v);
    done_not_stuck(p, env, rw(XExpr::Any(Box::new(xs), x, Box::new(c))), v);
}

/// all の隙間：最後の要素の述語が値 v を返せば（それより前は真）、写しの all は v に評価され、行き詰まらない。
pub proof fn all_gap(
    p: Prog,
    rw: spec_fn(XExpr) -> Expr,
    env: Map<nat, Val>,
    xs: XExpr,
    x: nat,
    c: XExpr,
    items: Seq<Val>,
    v: Val,
)
    requires
        hof_shapes(rw),
        evals_to(p, env, rw(xs), Val::List(items)),
        items.len() > 0,
        forall|k: int| 0 <= k < items.len() - 1 ==> evals_to(p, #[trigger] env.insert(x, items[k]), rw(c), Val::Bool(true)),
        evals_to(p, env.insert(x, items[items.len() - 1]), rw(c), v),
    ensures
        evals_to(p, env, rw(XExpr::All(Box::new(xs), x, Box::new(c))), v),
        !evals_stuck(p, env, rw(XExpr::All(Box::new(xs), x, Box::new(c)))),
{
    let acc = all_names(rw, xs, x, c);
    bool_fold_last(p, env, rw(xs), acc, x, rw(c), true, rw(c), Expr::Bool(false), items, v);
    done_not_stuck(p, env, rw(XExpr::All(Box::new(xs), x, Box::new(c))), v);
}


// ------------------------------------------------------------------ sort_by の行き詰まり

/// e は、ある燃料で整数に評価される。
pub open spec fn has_int(p: Prog, env: Map<nat, Val>, e: Expr) -> bool {
    exists|i: int| #![trigger evals_to(p, env, e, Val::Int(i))] evals_to(p, env, e, Val::Int(i))
}

/// sort_by の止まり方（鍵の行き詰まり）：j から stop - 1 までの鍵は整数に評価され、stop の鍵は行き詰まる。
pub open spec fn sort_stuck(
    p: Prog,
    rw: spec_fn(XExpr) -> Expr,
    env: Map<nat, Val>,
    x: nat,
    k: XExpr,
    items: Seq<Val>,
    j: nat,
    stop: nat,
) -> bool {
    &&& j <= stop
    &&& stop < items.len()
    &&& forall|m: int| j <= m < stop ==> has_int(p, #[trigger] env.insert(x, items[m]), rw(k))
    &&& evals_stuck(p, env.insert(x, items[stop as int]), rw(k))
}

/// sort_by の止まり方（整数でない鍵）：j から bad - 1 までの鍵は整数に、bad の鍵は整数でない値に評価される。
/// bad = 0 なら、要素が二つ以上あり、要素 1 の鍵は値に評価されるか行き詰まる（要素が一つの場合は含めない。sort_gap）。
pub open spec fn sort_bad(
    p: Prog,
    rw: spec_fn(XExpr) -> Expr,
    env: Map<nat, Val>,
    x: nat,
    k: XExpr,
    items: Seq<Val>,
    j: nat,
    bad: nat,
) -> bool {
    &&& j <= bad
    &&& bad < items.len()
    &&& forall|m: int| j <= m < bad ==> has_int(p, #[trigger] env.insert(x, items[m]), rw(k))
    &&& exists|v: Val|
        #![trigger evals_to(p, env.insert(x, items[bad as int]), rw(k), v)]
        evals_to(p, env.insert(x, items[bad as int]), rw(k), v) && !(v is Int)
    &&& bad == 0 ==> items.len() >= 2 && (has_value(p, env.insert(x, items[1]), rw(k)) || evals_stuck(
        p,
        env.insert(x, items[1]),
        rw(k),
    ))
}

/// sort_by の行き詰まり：列の式が行き詰まるかリストでなければ、写しも行き詰まる。列が items に評価され、
/// sort_stuck（鍵が行き詰まる）か sort_bad（整数でない鍵を比べる）なら、写しも行き詰まる（ob-sort-by-stuck）。
pub open spec fn ob_sort_by_stuck(p: Prog, rw: spec_fn(XExpr) -> Expr) -> bool {
    &&& forall|env: Map<nat, Val>, xs: XExpr, x: nat, k: XExpr|
        #![trigger evals_stuck(p, env, rw(XExpr::SortBy(Box::new(xs), x, Box::new(k))))]
        list_fails(p, env, rw(xs)) ==> evals_stuck(p, env, rw(XExpr::SortBy(Box::new(xs), x, Box::new(k))))
    &&& forall|env: Map<nat, Val>, xs: XExpr, x: nat, k: XExpr, items: Seq<Val>, stop: nat|
        #![trigger evals_stuck(p, env, rw(XExpr::SortBy(Box::new(xs), x, Box::new(k)))), sort_stuck(p, rw, env, x, k, items, 0, stop)]
        evals_to(p, env, rw(xs), Val::List(items)) && sort_stuck(p, rw, env, x, k, items, 0, stop)
            ==> evals_stuck(p, env, rw(XExpr::SortBy(Box::new(xs), x, Box::new(k))))
    &&& forall|env: Map<nat, Val>, xs: XExpr, x: nat, k: XExpr, items: Seq<Val>, bad: nat|
        #![trigger evals_stuck(p, env, rw(XExpr::SortBy(Box::new(xs), x, Box::new(k)))), sort_bad(p, rw, env, x, k, items, 0, bad)]
        evals_to(p, env, rw(xs), Val::List(items)) && sort_bad(p, rw, env, x, k, items, 0, bad)
            ==> evals_stuck(p, env, rw(XExpr::SortBy(Box::new(xs), x, Box::new(k))))
}

/// 内側の畳み込みの初期状態の値 (None, ([], false))。
pub open spec fn state0() -> Val {
    Val::Pair(
        Box::new(Val::None),
        Box::new(Val::Pair(Box::new(Val::List(Seq::empty())), Box::new(Val::Bool(false)))),
    )
}

/// 内側の一段目の後の状態 (Some(v), ([], false))。鍵の値 v は整数でなくてもよい。
pub open spec fn state1(v: Val) -> Val {
    Val::Pair(
        Box::new(Val::Some(Box::new(v))),
        Box::new(Val::Pair(Box::new(Val::List(Seq::empty())), Box::new(Val::Bool(false)))),
    )
}

pub proof fn ins_sorted_len(s: Seq<(Val, int)>, e: (Val, int))
    ensures
        ins_sorted(s, e).len() == s.len() + 1,
    decreases s.len(),
{
    reveal_with_fuel(ins_sorted, 1);
    if s.len() > 0 && !(e.1 < s[0].1) {
        ins_sorted_len(s.drop_first(), e);
    }
}

pub proof fn sort_prefix_len(zp: Seq<(Val, int)>, i: nat)
    requires
        i <= zp.len(),
    ensures
        sort_prefix(zp, i).len() == i,
    decreases i,
{
    reveal_with_fuel(sort_prefix, 1);
    if i > 0 {
        sort_prefix_len(zp, (i - 1) as nat);
        ins_sorted_len(sort_prefix(zp, (i - 1) as nat), zp[i - 1]);
    }
}

/// 一引数の組込み：e が v に評価され、意味が w なら、呼出しは w に評価される。
pub proof fn unary_to(p: Prog, env: Map<nat, Val>, b: Builtin, e: Expr, v: Val, w: Val)
    requires
        evals_to(p, env, e, v),
        apply(b, seq![v]) == Res::Done(w),
    ensures
        evals_to(p, env, Expr::Builtin(b, seq![e]), w),
{
    let es = seq![e];
    let vs = seq![v];
    assert forall|j: int| 0 <= j < es.len() implies evals_to(p, env, #[trigger] es[j], vs[j]) by {
        assert(es[j] == e && vs[j] == v);
    }
    args_from_each(p, env, es, vs, 0);
    assert(vs.subrange(0, vs.len() as int) =~= vs);
    bs_builtin(p, env, b, es, vs, w);
}

/// 二引数の列：e1・e2 が v1・v2 に評価されれば、引数の列は (v1, v2) に評価される。
pub proof fn args_two_to(p: Prog, env: Map<nat, Val>, e1: Expr, e2: Expr, v1: Val, v2: Val)
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

/// 二引数の組込み。
pub proof fn binary_to(p: Prog, env: Map<nat, Val>, b: Builtin, e1: Expr, e2: Expr, v1: Val, v2: Val, w: Val)
    requires
        evals_to(p, env, e1, v1),
        evals_to(p, env, e2, v2),
        apply(b, seq![v1, v2]) == Res::Done(w),
    ensures
        evals_to(p, env, Expr::Builtin(b, seq![e1, e2]), w),
{
    args_two_to(p, env, e1, e2, v1, v2);
    bs_builtin(p, env, b, seq![e1, e2], seq![v1, v2], w);
}

/// 状態の変数の取り出し（sortmeaning.rs の state_parts と同じ）。
pub proof fn state_of(p: Prog, env: Map<nat, Val>, st: nat, a: Val, lst: Seq<Val>, pl: bool)
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
    unary_to(p, env, Builtin::Fst, Expr::Var(st), sv, a);
    assert(apply(Builtin::Snd, seq![sv]) == Res::Done(rest));
    unary_to(p, env, Builtin::Snd, Expr::Var(st), sv, rest);
    assert(apply(Builtin::Fst, seq![rest]) == Res::Done(Val::List(lst)));
    unary_to(p, env, Builtin::Fst, psnd(Expr::Var(st)), rest, Val::List(lst));
    assert(apply(Builtin::Snd, seq![rest]) == Res::Done(Val::Bool(pl)));
    unary_to(p, env, Builtin::Snd, psnd(Expr::Var(st)), rest, Val::Bool(pl));
}

/// 初期状態の評価（sortmeaning.rs の init_eval と同じ）。
pub proof fn state0_eval(p: Prog, env: Map<nat, Val>, t: Ty)
    ensures
        evals_to(p, env, init_state(t), state0()),
{
    bs_leaf(p, env, Expr::None(Ty::Int));
    bs_nil(p, env, t);
    bs_leaf(p, env, Expr::Bool(false));
    bs_pair(p, env, Expr::List(t, Seq::empty()), Expr::Bool(false), Val::List(Seq::empty()), Val::Bool(false));
    bs_pair(
        p,
        env,
        Expr::None(Ty::Int),
        pair_e(Expr::List(t, Seq::empty()), Expr::Bool(false)),
        Val::None,
        Val::Pair(Box::new(Val::List(Seq::empty())), Box::new(Val::Bool(false))),
    );
}

/// 鍵の式の評価は、束縛 acc・e・st・y を加えても変わらない（どの燃料、どの結果でも）。
pub proof fn key_eval_absent(
    p: Prog,
    n: nat,
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
    xv: Val,
    k: Expr,
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
    ensures
        eval(p, n, env.insert(acc, a).insert(e, ev).insert(st, sv).insert(y, yv).insert(x, xv), k) == eval(
            p,
            n,
            env.insert(x, xv),
            k,
        ),
{
    let e0 = env.insert(x, xv);
    eval_absent(p, n, e0.insert(acc, a).insert(e, ev).insert(st, sv), k, y, yv);
    eval_absent(p, n, e0.insert(acc, a).insert(e, ev), k, st, sv);
    eval_absent(p, n, e0.insert(acc, a), k, e, ev);
    eval_absent(p, n, e0, k, acc, a);
    assert(env.insert(acc, a).insert(e, ev).insert(st, sv).insert(y, yv).insert(x, xv) =~= e0.insert(acc, a).insert(
        e,
        ev,
    ).insert(st, sv).insert(y, yv));
}

pub proof fn key_to(
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
    xv: Val,
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
        evals_to(p, env.insert(x, xv), k, w),
    ensures
        evals_to(p, env.insert(acc, a).insert(e, ev).insert(st, sv).insert(y, yv).insert(x, xv), k, w),
{
    let n = choose|n: nat| #[trigger] eval(p, n, env.insert(x, xv), k) == Res::Done(w);
    key_eval_absent(p, n, env, acc, a, e, ev, st, sv, y, yv, x, xv, k);
    assert(eval(p, n, env.insert(acc, a).insert(e, ev).insert(st, sv).insert(y, yv).insert(x, xv), k) == Res::Done(w));
}

pub proof fn key_stuck(
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
    xv: Val,
    k: Expr,
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
        evals_stuck(p, env.insert(x, xv), k),
    ensures
        evals_stuck(p, env.insert(acc, a).insert(e, ev).insert(st, sv).insert(y, yv).insert(x, xv), k),
{
    let n = choose|n: nat| #[trigger] eval(p, n, env.insert(x, xv), k) == Res::Stuck;
    key_eval_absent(p, n, env, acc, a, e, ev, st, sv, y, yv, x, xv, k);
    stuck_with(p, env.insert(acc, a).insert(e, ev).insert(st, sv).insert(y, yv).insert(x, xv), k, n);
}

/// 内側の一段目（項は e 自身、状態は初期状態）：鍵が値 v に評価されれば、状態は state1(v)。
pub proof fn inner_first(
    p: Prog,
    env: Map<nat, Val>,
    acc: nat,
    a: Val,
    e: nat,
    u: Val,
    st: nat,
    y: nat,
    ky: nat,
    ke: nat,
    x: nat,
    k: Expr,
    v: Val,
)
    requires
        names_inner(acc, e, st, y, ky, ke, x),
        absent(acc, k),
        absent(e, k),
        absent(st, k),
        absent(y, k),
        evals_to(p, env.insert(x, u), k, v),
    ensures
        evals_to(
            p,
            env.insert(acc, a).insert(e, u).insert(st, state0()).insert(y, u),
            sort_inner(e, st, y, ky, ke, x, k),
            state1(v),
        ),
{
    let emp = Seq::<Val>::empty();
    let rest = Val::Pair(Box::new(Val::List(emp)), Box::new(Val::Bool(false)));
    let env_b = env.insert(acc, a).insert(e, u).insert(st, state0()).insert(y, u);
    assert(env_b.contains_key(st) && env_b[st] == state0());
    state_of(p, env_b, st, Val::None, emp, false);
    key_to(p, env, acc, a, e, u, st, state0(), y, u, x, u, k, v);
    assert(env_b.contains_key(y) && env_b[y] == u);
    bs_var(p, env_b, y);
    bs_let(p, env_b, x, Expr::Var(y), k, u, v);
    let env_m = env_b.insert(ky, v);
    assert(env_m.contains_key(st) && env_m[st] == state0());
    state_of(p, env_m, st, Val::None, emp, false);
    assert(env_m.contains_key(ky) && env_m[ky] == v);
    bs_var(p, env_m, ky);
    bs_some(p, env_m, Expr::Var(ky), v);
    bs_pair(p, env_m, Expr::Some(Box::new(Expr::Var(ky))), psnd(Expr::Var(st)), Val::Some(Box::new(v)), rest);
    bs_match(
        p,
        env_m,
        pfst(Expr::Var(st)),
        pair_e(Expr::Some(Box::new(Expr::Var(ky))), psnd(Expr::Var(st))),
        ke,
        sort_lt(e, st, y, ky, ke),
        Val::None,
        state1(v),
    );
    bs_let(p, env_b, ky, Expr::Let(x, Box::new(Expr::Var(y)), Box::new(k)), sort_match(e, st, y, ky, ke), v, state1(v));
    bs_if(p, env_b, sort_cond(st), sort_placed(st, y), sort_fresh(e, st, y, ky, ke, x, k), false, state1(v));
}

/// 内側の一段目の行き詰まり：鍵が行き詰まれば、内側の本体も行き詰まる。
pub proof fn inner_first_stuck(
    p: Prog,
    env: Map<nat, Val>,
    acc: nat,
    a: Val,
    e: nat,
    u: Val,
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
        evals_stuck(p, env.insert(x, u), k),
    ensures
        evals_stuck(p, env.insert(acc, a).insert(e, u).insert(st, state0()).insert(y, u), sort_inner(e, st, y, ky, ke, x, k)),
{
    let emp = Seq::<Val>::empty();
    let env_b = env.insert(acc, a).insert(e, u).insert(st, state0()).insert(y, u);
    assert(env_b.contains_key(st) && env_b[st] == state0());
    state_of(p, env_b, st, Val::None, emp, false);
    key_stuck(p, env, acc, a, e, u, st, state0(), y, u, x, u, k);
    assert(env_b.contains_key(y) && env_b[y] == u);
    bs_var(p, env_b, y);
    let_stuck_b(p, env_b, x, Expr::Var(y), k, u);
    let_stuck_a(p, env_b, ky, Expr::Let(x, Box::new(Expr::Var(y)), Box::new(k)), sort_match(e, st, y, ky, ke));
    if_stuck_br(p, env_b, sort_cond(st), sort_placed(st, y), sort_fresh(e, st, y, ky, ke, x, k), false);
}

/// 内側の二段目の行き詰まり：状態 state1(w) で項 u2 の鍵が値 v2 に評価され、w と v2 の両方が整数ではなければ、
/// 比較 Lt(w, v2) で行き詰まる。
pub proof fn inner_second_stuck(
    p: Prog,
    env: Map<nat, Val>,
    acc: nat,
    a: Val,
    e: nat,
    ev: Val,
    st: nat,
    y: nat,
    ky: nat,
    ke: nat,
    x: nat,
    k: Expr,
    w: Val,
    u2: Val,
    v2: Val,
)
    requires
        names_inner(acc, e, st, y, ky, ke, x),
        absent(acc, k),
        absent(e, k),
        absent(st, k),
        absent(y, k),
        evals_to(p, env.insert(x, u2), k, v2),
        !(w is Int && v2 is Int),
    ensures
        evals_stuck(
            p,
            env.insert(acc, a).insert(e, ev).insert(st, state1(w)).insert(y, u2),
            sort_inner(e, st, y, ky, ke, x, k),
        ),
{
    let emp = Seq::<Val>::empty();
    let env_b = env.insert(acc, a).insert(e, ev).insert(st, state1(w)).insert(y, u2);
    assert(env_b.contains_key(st) && env_b[st] == state1(w));
    state_of(p, env_b, st, Val::Some(Box::new(w)), emp, false);
    key_to(p, env, acc, a, e, ev, st, state1(w), y, u2, x, u2, k, v2);
    assert(env_b.contains_key(y) && env_b[y] == u2);
    bs_var(p, env_b, y);
    bs_let(p, env_b, x, Expr::Var(y), k, u2, v2);
    let env_m = env_b.insert(ky, v2);
    assert(env_m.contains_key(st) && env_m[st] == state1(w));
    state_of(p, env_m, st, Val::Some(Box::new(w)), emp, false);
    let env_k = env_m.insert(ke, w);
    assert(env_k.contains_key(ke) && env_k[ke] == w);
    assert(env_k.contains_key(ky) && env_k[ky] == v2);
    bs_var(p, env_k, ke);
    bs_var(p, env_k, ky);
    args_two_to(p, env_k, Expr::Var(ke), Expr::Var(ky), w, v2);
    assert(apply(Builtin::Lt, seq![w, v2]) == Res::Stuck);
    builtin_stuck_apply(p, env_k, Builtin::Lt, seq![Expr::Var(ke), Expr::Var(ky)], seq![w, v2]);
    if_stuck_c(
        p,
        env_k,
        Expr::Builtin(Builtin::Lt, seq![Expr::Var(ke), Expr::Var(ky)]),
        sort_before(e, st, y),
        sort_after(st, y),
    );
    match_stuck_some(
        p,
        env_m,
        pfst(Expr::Var(st)),
        pair_e(Expr::Some(Box::new(Expr::Var(ky))), psnd(Expr::Var(st))),
        ke,
        sort_lt(e, st, y, ky, ke),
        w,
    );
    let_stuck_b(p, env_b, ky, Expr::Let(x, Box::new(Expr::Var(y)), Box::new(k)), sort_match(e, st, y, ky, ke), v2);
    if_stuck_br(p, env_b, sort_cond(st), sort_placed(st, y), sort_fresh(e, st, y, ky, ke, x, k), false);
}

/// 外側の段の入口：acc の値 List(pv)、e の値 u のとき、cons(e, acc) は [u] + pv、初期状態は state0()。
pub proof fn outer_entry(p: Prog, env: Map<nat, Val>, t: Ty, acc: nat, pv: Seq<Val>, e: nat, u: Val)
    requires
        acc != e,
    ensures
        evals_to(
            p,
            env.insert(acc, Val::List(pv)).insert(e, u),
            cons_e(Expr::Var(e), Expr::Var(acc)),
            Val::List(seq![u] + pv),
        ),
        evals_to(p, env.insert(acc, Val::List(pv)).insert(e, u), init_state(t), state0()),
{
    let env_o = env.insert(acc, Val::List(pv)).insert(e, u);
    assert(env_o.contains_key(acc) && env_o[acc] == Val::List(pv));
    assert(env_o.contains_key(e) && env_o[e] == u);
    bs_var(p, env_o, e);
    bs_var(p, env_o, acc);
    assert(apply(Builtin::Cons, seq![u, Val::List(pv)]) == Res::Done(Val::List(seq![u] + pv)));
    binary_to(p, env_o, Builtin::Cons, Expr::Var(e), Expr::Var(acc), u, Val::List(pv), Val::List(seq![u] + pv));
    state0_eval(p, env_o, t);
}

/// 外側の本体の行き詰まり：内側の畳み込みの段の列が行き詰まれば、本体（Let rb = fold ...）も行き詰まる。
pub proof fn body_stuck(
    p: Prog,
    env: Map<nat, Val>,
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
    zs: Seq<Val>,
    s0: Val,
)
    requires
        evals_to(p, env, cons_e(Expr::Var(e), Expr::Var(acc)), Val::List(zs)),
        evals_to(p, env, init_state(t), s0),
        fold_stuck(p, env, st, y, sort_inner(e, st, y, ky, ke, x, k), zs, 0, s0),
    ensures
        evals_stuck(p, env, sort_body(t, acc, e, st, y, ky, ke, rb, x, k)),
{
    let fe = Expr::Fold(
        Box::new(cons_e(Expr::Var(e), Expr::Var(acc))),
        Box::new(init_state(t)),
        st,
        y,
        Box::new(sort_inner(e, st, y, ky, ke, x, k)),
    );
    fold_stuck_expr(
        p,
        env,
        cons_e(Expr::Var(e), Expr::Var(acc)),
        init_state(t),
        st,
        y,
        sort_inner(e, st, y, ky, ke, x, k),
        zs,
        s0,
    );
    let_stuck_a(p, env, rb, fe, Expr::Builtin(Builtin::Reverse, seq![sort_rev(e, rb)]));
}

/// 外側の一段目（acc は空）：鍵が値 v に評価されれば（整数でなくても）、本体は [u] に評価される（鍵を比べない）。
pub proof fn outer_first(
    p: Prog,
    env: Map<nat, Val>,
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
    u: Val,
    v: Val,
)
    requires
        names_ok(acc, e, st, y, ky, ke, rb, x),
        absent(acc, k),
        absent(e, k),
        absent(st, k),
        absent(y, k),
        evals_to(p, env.insert(x, u), k, v),
    ensures
        evals_to(
            p,
            env.insert(acc, Val::List(Seq::empty())).insert(e, u),
            sort_body(t, acc, e, st, y, ky, ke, rb, x, k),
            Val::List(seq![u]),
        ),
{
    let emp = Seq::<Val>::empty();
    let env_o = env.insert(acc, Val::List(emp)).insert(e, u);
    outer_entry(p, env, t, acc, emp, e, u);
    let zs = seq![u] + emp;
    assert(zs =~= seq![u]);
    let inner = sort_inner(e, st, y, ky, ke, x, k);
    let iaccs = seq![state0(), state1(v)];
    inner_first(p, env, acc, Val::List(emp), e, u, st, y, ky, ke, x, k, v);
    assert forall|j: int| 0 <= j < zs.len() implies evals_to(
        p,
        #[trigger] env_o.insert(st, iaccs[j]).insert(y, zs[j]),
        inner,
        iaccs[j + 1],
    ) by {
        assert(j == 0);
        assert(zs[0] == u && iaccs[0] == state0() && iaccs[1] == state1(v));
    }
    fold_expr_to(p, env_o, cons_e(Expr::Var(e), Expr::Var(acc)), init_state(t), st, y, inner, zs, iaccs);
    let fe = Expr::Fold(Box::new(cons_e(Expr::Var(e), Expr::Var(acc))), Box::new(init_state(t)), st, y, Box::new(inner));
    assert(iaccs[zs.len() as int] == state1(v));
    let env_r = env_o.insert(rb, state1(v));
    assert(env_r.contains_key(rb) && env_r[rb] == state1(v));
    state_of(p, env_r, rb, Val::Some(Box::new(v)), emp, false);
    assert(env_r.contains_key(e) && env_r[e] == u);
    bs_var(p, env_r, e);
    assert(seq![u] + emp =~= seq![u]);
    assert(apply(Builtin::Cons, seq![u, Val::List(emp)]) == Res::Done(Val::List(seq![u])));
    binary_to(p, env_r, Builtin::Cons, Expr::Var(e), pfst(psnd(Expr::Var(rb))), u, Val::List(emp), Val::List(seq![u]));
    bs_if(
        p,
        env_r,
        psnd(psnd(Expr::Var(rb))),
        pfst(psnd(Expr::Var(rb))),
        cons_e(Expr::Var(e), pfst(psnd(Expr::Var(rb)))),
        false,
        Val::List(seq![u]),
    );
    assert(rev(seq![u]) =~= seq![u]);
    assert(apply(Builtin::Reverse, seq![Val::List(seq![u])]) == Res::Done(Val::List(seq![u])));
    unary_to(p, env_r, Builtin::Reverse, sort_rev(e, rb), Val::List(seq![u]), Val::List(seq![u]));
    bs_let(p, env_o, rb, fe, Expr::Builtin(Builtin::Reverse, seq![sort_rev(e, rb)]), state1(v), Val::List(seq![u]));
}

/// 鍵が整数の先頭 m 個の外側の段（sortmeaning.rs の outer_step）：累積値は整列済みの先頭の値の列。
pub proof fn sort_prefix_steps(
    p: Prog,
    env: Map<nat, Val>,
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
    m: nat,
) -> (r: (Seq<(Val, int)>, Seq<Val>))
    requires
        names_ok(acc, e, st, y, ky, ke, rb, x),
        absent(acc, k),
        absent(e, k),
        absent(st, k),
        absent(y, k),
        m <= items.len(),
        forall|i: int| 0 <= i < m ==> has_int(p, #[trigger] env.insert(x, items[i]), k),
    ensures
        r.0.len() == m,
        forall|i: int| 0 <= i < m ==> #[trigger] r.0[i].0 == items[i],
        keyed(p, env, x, k, r.0),
        r.1.len() == m + 1,
        r.1[0] == Val::List(Seq::empty()),
        forall|i: int| 0 <= i <= m ==> #[trigger] r.1[i] == Val::List(pvals(sort_prefix(r.0, i as nat))),
        forall|i: int|
            0 <= i < m ==> evals_to(
                p,
                #[trigger] env.insert(acc, r.1[i]).insert(e, items[i]),
                sort_body(t, acc, e, st, y, ky, ke, rb, x, k),
                r.1[i + 1],
            ),
{
    reveal_with_fuel(sort_prefix, 1);
    let keys = Seq::new(
        m,
        |i: int|
            choose|z: int|
                #![trigger evals_to(p, env.insert(x, items[i]), k, Val::Int(z))]
                evals_to(p, env.insert(x, items[i]), k, Val::Int(z)),
    );
    let pre = items.subrange(0, m as int);
    let zp = zip_keys(pre, keys);
    assert forall|i: int| 0 <= i < zp.len() implies evals_to(
        p,
        #[trigger] env.insert(x, zp[i].0),
        k,
        Val::Int(zp[i].1),
    ) by {
        assert(zp[i].0 == items[i]);
        assert(zp[i].1 == keys[i]);
        assert(has_int(p, env.insert(x, items[i]), k));
    }
    assert(keyed(p, env, x, k, zp));
    let accs = Seq::new(m + 1, |i: int| Val::List(pvals(sort_prefix(zp, i as nat))));
    assert(sort_prefix(zp, 0) =~= Seq::<(Val, int)>::empty());
    assert(pvals(Seq::<(Val, int)>::empty()) =~= Seq::<Val>::empty());
    assert forall|i: int| 0 <= i < m implies evals_to(
        p,
        #[trigger] env.insert(acc, accs[i]).insert(e, items[i]),
        sort_body(t, acc, e, st, y, ky, ke, rb, x, k),
        accs[i + 1],
    ) by {
        assert(zp[i].0 == items[i]);
        keyed_prefix(p, env, x, k, zp, i as nat);
        outer_step(p, env, acc, e, st, y, ky, ke, rb, x, k, t, zp, i as nat);
    }
    (zp, accs)
}

pub proof fn sort_stuck_list(p: Prog, rw: spec_fn(XExpr) -> Expr, env: Map<nat, Val>, xs: XExpr, x: nat, k: XExpr)
    requires
        hof_shapes(rw),
        list_fails(p, env, rw(xs)),
    ensures
        evals_stuck(p, env, rw(XExpr::SortBy(Box::new(xs), x, Box::new(k)))),
{
    let (t, acc, e, st, y, ky, ke, rb) = sort_names(rw, xs, x, k);
    fold_stuck_xs(
        p,
        env,
        rw(xs),
        Expr::List(t, Seq::empty()),
        acc,
        e,
        sort_body(t, acc, e, st, y, ky, ke, rb, x, rw(k)),
    );
}

pub proof fn sort_stuck_elem(
    p: Prog,
    rw: spec_fn(XExpr) -> Expr,
    env: Map<nat, Val>,
    xs: XExpr,
    x: nat,
    k: XExpr,
    items: Seq<Val>,
    stop: nat,
)
    requires
        hof_shapes(rw),
        evals_to(p, env, rw(xs), Val::List(items)),
        sort_stuck(p, rw, env, x, k, items, 0, stop),
    ensures
        evals_stuck(p, env, rw(XExpr::SortBy(Box::new(xs), x, Box::new(k)))),
{
    let (t, acc, e, st, y, ky, ke, rb) = sort_names(rw, xs, x, k);
    let g = rw(k);
    let body = sort_body(t, acc, e, st, y, ky, ke, rb, x, g);
    let inner = sort_inner(e, st, y, ky, ke, x, g);
    let (zp, accs) = sort_prefix_steps(p, env, t, acc, e, st, y, ky, ke, rb, x, g, items, stop);
    let u = items[stop as int];
    let pv = pvals(sort_prefix(zp, stop));
    assert(accs[stop as int] == Val::List(pv));
    let env_o = env.insert(acc, Val::List(pv)).insert(e, u);
    outer_entry(p, env, t, acc, pv, e, u);
    let zs = seq![u] + pv;
    assert(zs[0] == u);
    inner_first_stuck(p, env, acc, Val::List(pv), e, u, st, y, ky, ke, x, g);
    let iaccs = seq![state0()];
    assert(iaccs[0] == state0());
    fold_stuck_steps(p, env_o, st, y, inner, zs, iaccs, 0, 0);
    body_stuck(p, env_o, t, acc, e, st, y, ky, ke, rb, x, g, zs, state0());
    fold_stuck_steps(p, env, acc, e, body, items, accs, stop, 0);
    bs_nil(p, env, t);
    fold_stuck_expr(p, env, rw(xs), Expr::List(t, Seq::empty()), acc, e, body, items, accs[0]);
}

pub proof fn sort_bad_elem(
    p: Prog,
    rw: spec_fn(XExpr) -> Expr,
    env: Map<nat, Val>,
    xs: XExpr,
    x: nat,
    k: XExpr,
    items: Seq<Val>,
    bad: nat,
)
    requires
        hof_shapes(rw),
        evals_to(p, env, rw(xs), Val::List(items)),
        sort_bad(p, rw, env, x, k, items, 0, bad),
    ensures
        evals_stuck(p, env, rw(XExpr::SortBy(Box::new(xs), x, Box::new(k)))),
{
    let (t, acc, e, st, y, ky, ke, rb) = sort_names(rw, xs, x, k);
    let g = rw(k);
    let body = sort_body(t, acc, e, st, y, ky, ke, rb, x, g);
    let inner = sort_inner(e, st, y, ky, ke, x, g);
    let ub = items[bad as int];
    let vb = choose|v: Val| #![trigger evals_to(p, env.insert(x, ub), g, v)] evals_to(p, env.insert(x, ub), g, v) && !(v is Int);
    if bad > 0 {
        let (zp, accs) = sort_prefix_steps(p, env, t, acc, e, st, y, ky, ke, rb, x, g, items, bad);
        let s = sort_prefix(zp, bad);
        let pv = pvals(s);
        sort_prefix_len(zp, bad);
        keyed_prefix(p, env, x, g, zp, bad);
        assert(evals_to(p, env.insert(x, s[0].0), g, Val::Int(s[0].1)));
        assert(accs[bad as int] == Val::List(pv));
        let env_o = env.insert(acc, Val::List(pv)).insert(e, ub);
        outer_entry(p, env, t, acc, pv, e, ub);
        let zs = seq![ub] + pv;
        assert(zs[0] == ub);
        assert(zs[1] == s[0].0);
        inner_first(p, env, acc, Val::List(pv), e, ub, st, y, ky, ke, x, g, vb);
        inner_second_stuck(p, env, acc, Val::List(pv), e, ub, st, y, ky, ke, x, g, vb, s[0].0, Val::Int(s[0].1));
        let iaccs = seq![state0(), state1(vb)];
        assert forall|j: int| 0 <= j < 1 implies evals_to(
            p,
            #[trigger] env_o.insert(st, iaccs[j]).insert(y, zs[j]),
            inner,
            iaccs[j + 1],
        ) by {
            assert(j == 0);
            assert(iaccs[0] == state0() && iaccs[1] == state1(vb));
        }
        assert(iaccs[1] == state1(vb));
        fold_stuck_steps(p, env_o, st, y, inner, zs, iaccs, 1, 0);
        body_stuck(p, env_o, t, acc, e, st, y, ky, ke, rb, x, g, zs, state0());
        fold_stuck_steps(p, env, acc, e, body, items, accs, bad, 0);
        bs_nil(p, env, t);
        fold_stuck_expr(p, env, rw(xs), Expr::List(t, Seq::empty()), acc, e, body, items, accs[0]);
    } else {
        let u0 = items[0];
        let u1 = items[1];
        let emp = Seq::<Val>::empty();
        outer_first(p, env, t, acc, e, st, y, ky, ke, rb, x, g, u0, vb);
        let accs = seq![Val::List(emp), Val::List(seq![u0])];
        let pv = seq![u0];
        let env_o = env.insert(acc, Val::List(pv)).insert(e, u1);
        outer_entry(p, env, t, acc, pv, e, u1);
        let zs = seq![u1] + pv;
        assert(zs[0] == u1 && zs[1] == u0);
        if evals_stuck(p, env.insert(x, u1), g) {
            inner_first_stuck(p, env, acc, Val::List(pv), e, u1, st, y, ky, ke, x, g);
            let iaccs = seq![state0()];
            assert(iaccs[0] == state0());
            fold_stuck_steps(p, env_o, st, y, inner, zs, iaccs, 0, 0);
        } else {
            assert(has_value(p, env.insert(x, u1), g));
            let w = choose|w: Val| #![trigger evals_to(p, env.insert(x, u1), g, w)] evals_to(p, env.insert(x, u1), g, w);
            inner_first(p, env, acc, Val::List(pv), e, u1, st, y, ky, ke, x, g, w);
            inner_second_stuck(p, env, acc, Val::List(pv), e, u1, st, y, ky, ke, x, g, w, u0, vb);
            let iaccs = seq![state0(), state1(w)];
            assert forall|j: int| 0 <= j < 1 implies evals_to(
                p,
                #[trigger] env_o.insert(st, iaccs[j]).insert(y, zs[j]),
                inner,
                iaccs[j + 1],
            ) by {
                assert(j == 0);
                assert(iaccs[0] == state0() && iaccs[1] == state1(w));
            }
            assert(iaccs[1] == state1(w));
            fold_stuck_steps(p, env_o, st, y, inner, zs, iaccs, 1, 0);
        }
        body_stuck(p, env_o, t, acc, e, st, y, ky, ke, rb, x, g, zs, state0());
        assert forall|i: int| 0 <= i < 1 implies evals_to(
            p,
            #[trigger] env.insert(acc, accs[i]).insert(e, items[i]),
            body,
            accs[i + 1],
        ) by {
            assert(i == 0);
            assert(accs[0] == Val::List(emp) && accs[1] == Val::List(seq![u0]));
        }
        assert(accs[1] == Val::List(pv));
        fold_stuck_steps(p, env, acc, e, body, items, accs, 1, 0);
        bs_nil(p, env, t);
        fold_stuck_expr(p, env, rw(xs), Expr::List(t, Seq::empty()), acc, e, body, items, accs[0]);
    }
}

pub proof fn ob_sort_by_stuck_holds(p: Prog, rw: spec_fn(XExpr) -> Expr)
    requires
        hof_shapes(rw),
    ensures
        ob_sort_by_stuck(p, rw),
{
    assert forall|env: Map<nat, Val>, xs: XExpr, x: nat, k: XExpr|
        #![trigger evals_stuck(p, env, rw(XExpr::SortBy(Box::new(xs), x, Box::new(k))))]
        list_fails(p, env, rw(xs)) implies evals_stuck(p, env, rw(XExpr::SortBy(Box::new(xs), x, Box::new(k)))) by {
        sort_stuck_list(p, rw, env, xs, x, k);
    }
    assert forall|env: Map<nat, Val>, xs: XExpr, x: nat, k: XExpr, items: Seq<Val>, stop: nat|
        #![trigger evals_stuck(p, env, rw(XExpr::SortBy(Box::new(xs), x, Box::new(k)))), sort_stuck(p, rw, env, x, k, items, 0, stop)]
        evals_to(p, env, rw(xs), Val::List(items)) && sort_stuck(p, rw, env, x, k, items, 0, stop) implies evals_stuck(
            p,
            env,
            rw(XExpr::SortBy(Box::new(xs), x, Box::new(k))),
        ) by {
        sort_stuck_elem(p, rw, env, xs, x, k, items, stop);
    }
    assert forall|env: Map<nat, Val>, xs: XExpr, x: nat, k: XExpr, items: Seq<Val>, bad: nat|
        #![trigger evals_stuck(p, env, rw(XExpr::SortBy(Box::new(xs), x, Box::new(k)))), sort_bad(p, rw, env, x, k, items, 0, bad)]
        evals_to(p, env, rw(xs), Val::List(items)) && sort_bad(p, rw, env, x, k, items, 0, bad) implies evals_stuck(
            p,
            env,
            rw(XExpr::SortBy(Box::new(xs), x, Box::new(k))),
        ) by {
        sort_bad_elem(p, rw, env, xs, x, k, items, bad);
    }
}

/// sort_by の隙間：要素が一つ（u）なら、鍵の値 v が整数でなくても、写しは [u] に評価され、行き詰まらない。
/// 源は鍵の値の列 [v] を int_seq で検査するので、v が整数でなければ行き詰まる。
pub proof fn sort_gap(
    p: Prog,
    rw: spec_fn(XExpr) -> Expr,
    env: Map<nat, Val>,
    xs: XExpr,
    x: nat,
    k: XExpr,
    u: Val,
    v: Val,
)
    requires
        hof_shapes(rw),
        evals_to(p, env, rw(xs), Val::List(seq![u])),
        evals_to(p, env.insert(x, u), rw(k), v),
    ensures
        evals_to(p, env, rw(XExpr::SortBy(Box::new(xs), x, Box::new(k))), Val::List(seq![u])),
        !evals_stuck(p, env, rw(XExpr::SortBy(Box::new(xs), x, Box::new(k)))),
{
    let (t, acc, e, st, y, ky, ke, rb) = sort_names(rw, xs, x, k);
    let items = seq![u];
    let body = sort_body(t, acc, e, st, y, ky, ke, rb, x, rw(k));
    outer_first(p, env, t, acc, e, st, y, ky, ke, rb, x, rw(k), u, v);
    let accs = seq![Val::List(Seq::<Val>::empty()), Val::List(seq![u])];
    assert forall|i: int| 0 <= i < items.len() implies evals_to(
        p,
        #[trigger] env.insert(acc, accs[i]).insert(e, items[i]),
        body,
        accs[i + 1],
    ) by {
        assert(i == 0);
        assert(items[0] == u && accs[0] == Val::List(Seq::<Val>::empty()) && accs[1] == Val::List(seq![u]));
    }
    bs_nil(p, env, t);
    assert(accs[0] == Val::List(Seq::<Val>::empty()));
    assert(accs[items.len() as int] == Val::List(seq![u]));
    fold_expr_to(p, env, rw(xs), Expr::List(t, Seq::empty()), acc, e, body, items, accs);
    done_not_stuck(p, env, rw(XExpr::SortBy(Box::new(xs), x, Box::new(k))), Val::List(seq![u]));
}

// ------------------------------------------------------------------ まとめ

/// SH6 の行き詰まりの側：書換えが hof の形を持てば（hof_shapes）、六つの行き詰まりの仮定が成り立つ。
pub proof fn sh6_ob_stuck(p: Prog, rw: spec_fn(XExpr) -> Expr)
    requires
        hof_shapes(rw),
    ensures
        ob_map_stuck(p, rw),
        ob_filter_stuck(p, rw),
        ob_find_stuck(p, rw),
        ob_any_stuck(p, rw),
        ob_all_stuck(p, rw),
        ob_sort_by_stuck(p, rw),
{
    ob_map_stuck_holds(p, rw);
    ob_filter_stuck_holds(p, rw);
    ob_find_stuck_holds(p, rw);
    ob_any_stuck_holds(p, rw);
    ob_all_stuck_holds(p, rw);
    ob_sort_by_stuck_holds(p, rw);
}

/// SH4 の仮定の全体 sim_ok は、構造の仮定（sim_prog・homomorphic）と書換えの形の仮定 hof_shapes から成り立つ。
pub proof fn sh6_sim_ok(xp: XProg, p: Prog, rw: spec_fn(XExpr) -> Expr)
    requires
        sim_prog(xp, p, rw),
        homomorphic(rw),
        hof_shapes(rw),
    ensures
        sim_ok(xp, p, rw),
{
    sh6_ob_done(p, rw);
    sh6_ob_stuck(p, rw);
}


// ------------------------------------------------------------------ 隙間の具体例（filter・find と同じ形の仮定は成り立たない）

/// any の止まり方を filter・find と同じ形（stop の述語は pred_fails）で述べたもの。
pub open spec fn any_stuck_full(
    p: Prog,
    rw: spec_fn(XExpr) -> Expr,
    env: Map<nat, Val>,
    x: nat,
    c: XExpr,
    items: Seq<Val>,
    j: nat,
    stop: nat,
) -> bool {
    &&& j <= stop
    &&& stop < items.len()
    &&& forall|k: int| j <= k < stop ==> evals_to(p, #[trigger] env.insert(x, items[k]), rw(c), Val::Bool(false))
    &&& pred_fails(p, env.insert(x, items[stop as int]), rw(c))
}

/// all の止まり方を filter・find と同じ形で述べたもの。
pub open spec fn all_stuck_full(
    p: Prog,
    rw: spec_fn(XExpr) -> Expr,
    env: Map<nat, Val>,
    x: nat,
    c: XExpr,
    items: Seq<Val>,
    j: nat,
    stop: nat,
) -> bool {
    &&& j <= stop
    &&& stop < items.len()
    &&& forall|k: int| j <= k < stop ==> evals_to(p, #[trigger] env.insert(x, items[k]), rw(c), Val::Bool(true))
    &&& pred_fails(p, env.insert(x, items[stop as int]), rw(c))
}

/// any の行き詰まりの仮定を filter・find と同じ形で述べたもの。現在の書換えでは成り立たない（any_full_fails）。
pub open spec fn ob_any_stuck_full(p: Prog, rw: spec_fn(XExpr) -> Expr) -> bool {
    forall|env: Map<nat, Val>, xs: XExpr, x: nat, c: XExpr, items: Seq<Val>, stop: nat|
        #![trigger evals_stuck(p, env, rw(XExpr::Any(Box::new(xs), x, Box::new(c)))), any_stuck_full(p, rw, env, x, c, items, 0, stop)]
        evals_to(p, env, rw(xs), Val::List(items)) && any_stuck_full(p, rw, env, x, c, items, 0, stop)
            ==> evals_stuck(p, env, rw(XExpr::Any(Box::new(xs), x, Box::new(c))))
}

/// all の行き詰まりの仮定を filter・find と同じ形で述べたもの。現在の書換えでは成り立たない（all_full_fails）。
pub open spec fn ob_all_stuck_full(p: Prog, rw: spec_fn(XExpr) -> Expr) -> bool {
    forall|env: Map<nat, Val>, xs: XExpr, x: nat, c: XExpr, items: Seq<Val>, stop: nat|
        #![trigger evals_stuck(p, env, rw(XExpr::All(Box::new(xs), x, Box::new(c)))), all_stuck_full(p, rw, env, x, c, items, 0, stop)]
        evals_to(p, env, rw(xs), Val::List(items)) && all_stuck_full(p, rw, env, x, c, items, 0, stop)
            ==> evals_stuck(p, env, rw(XExpr::All(Box::new(xs), x, Box::new(c))))
}

/// sort_by の行き詰まりの仮定を、源の int_seq の検査と同じ形で述べたもの（鍵の値がすべて出て、整数でない値がある）。
/// 現在の書換えでは成り立たない（sort_full_fails）。
pub open spec fn ob_sort_by_stuck_full(p: Prog, rw: spec_fn(XExpr) -> Expr) -> bool {
    forall|env: Map<nat, Val>, xs: XExpr, x: nat, k: XExpr, items: Seq<Val>, kv: Seq<Val>|
        #![trigger evals_stuck(p, env, rw(XExpr::SortBy(Box::new(xs), x, Box::new(k)))), map_ok(p, rw, env, x, k, items, kv, 0)]
        evals_to(p, env, rw(xs), Val::List(items)) && map_ok(p, rw, env, x, k, items, kv, 0) && int_seq(kv) is None
            ==> evals_stuck(p, env, rw(XExpr::SortBy(Box::new(xs), x, Box::new(k))))
}

/// 要素が () 一つのリスト。
pub open spec fn unit_list() -> XExpr {
    XExpr::List(Ty::Unit, seq![XExpr::Unit])
}

/// [()] の評価：源は燃料 3 で、写しはある燃料で List([()]) になる。
pub proof fn unit_list_evals(xp: XProg, p: Prog, rw: spec_fn(XExpr) -> Expr, env: Map<nat, Val>)
    requires
        homomorphic(rw),
    ensures
        xeval(xp, 3, env, unit_list()) == Res::Done(Val::List(seq![Val::Unit])),
        evals_to(p, env, rw(unit_list()), Val::List(seq![Val::Unit])),
{
    let es = seq![XExpr::Unit];
    let vs = seq![Val::Unit];
    assert(es[0] == XExpr::Unit);
    assert(xeval(xp, 1, env, XExpr::Unit) == Res::Done(Val::Unit));
    assert(xeval_args(xp, 1, env, es, 1) == ResSeq::Done(Seq::<Val>::empty()));
    assert(seq![Val::Unit] + Seq::<Val>::empty() =~= vs);
    assert(xeval_args(xp, 2, env, es, 0) == ResSeq::Done(vs));
    assert(xeval(xp, 3, env, unit_list()) == Res::Done(Val::List(vs)));
    let ces = rw_args(rw, es);
    assert(rw(XExpr::Unit) == Expr::Unit);
    assert(ces.len() == 1 && ces[0] == Expr::Unit);
    assert(rw(unit_list()) == Expr::List(erase_ty(Ty::Unit), ces));
    bs_leaf(p, env, Expr::Unit);
    assert forall|j: int| 0 <= j < ces.len() implies evals_to(p, env, #[trigger] ces[j], vs[j]) by {
        assert(j == 0);
    }
    args_from_each(p, env, ces, vs, 0);
    assert(vs.subrange(0, vs.len() as int) =~= vs);
    bs_list(p, env, erase_ty(Ty::Unit), ces, vs);
}

/// 隙間の具体例（any）：any([()], |x| 1) は、源では燃料 4 で行き詰まり、写しは Int(1) に評価される。
/// したがって filter・find と同じ形の仮定 ob_any_stuck_full は成り立たない。
pub proof fn any_full_fails(xp: XProg, p: Prog, rw: spec_fn(XExpr) -> Expr, x: nat)
    requires
        hof_shapes(rw),
        homomorphic(rw),
    ensures
        xeval(xp, 4, Map::empty(), XExpr::Any(Box::new(unit_list()), x, Box::new(XExpr::Int(1)))) == Res::Stuck,
        evals_to(p, Map::empty(), rw(XExpr::Any(Box::new(unit_list()), x, Box::new(XExpr::Int(1)))), Val::Int(1)),
        !ob_any_stuck_full(p, rw),
{
    let env = Map::<nat, Val>::empty();
    let xs = unit_list();
    let c = XExpr::Int(1);
    let items = seq![Val::Unit];
    let ex = XExpr::Any(Box::new(xs), x, Box::new(c));
    unit_list_evals(xp, p, rw, env);
    assert(items[0] == Val::Unit);
    assert(xeval(xp, 2, env.insert(x, Val::Unit), c) == Res::Done(Val::Int(1)));
    assert(xany(xp, 3, env, x, c, items, 0) == Res::Stuck);
    assert(xeval(xp, 4, env, ex) == Res::Stuck);
    assert(rw(c) == Expr::Int(1));
    bs_leaf(p, env.insert(x, Val::Unit), Expr::Int(1));
    assert(evals_to(p, env.insert(x, items[0]), rw(c), Val::Int(1)));
    any_gap(p, rw, env, xs, x, c, items, Val::Int(1));
    assert(pred_fails(p, env.insert(x, items[0]), rw(c)));
    assert(any_stuck_full(p, rw, env, x, c, items, 0, 0));
    if ob_any_stuck_full(p, rw) {
        assert(evals_stuck(p, env, rw(ex)));
    }
}

/// 隙間の具体例（all）：all([()], |x| 1) は、源では燃料 4 で行き詰まり、写しは Int(1) に評価される。
pub proof fn all_full_fails(xp: XProg, p: Prog, rw: spec_fn(XExpr) -> Expr, x: nat)
    requires
        hof_shapes(rw),
        homomorphic(rw),
    ensures
        xeval(xp, 4, Map::empty(), XExpr::All(Box::new(unit_list()), x, Box::new(XExpr::Int(1)))) == Res::Stuck,
        evals_to(p, Map::empty(), rw(XExpr::All(Box::new(unit_list()), x, Box::new(XExpr::Int(1)))), Val::Int(1)),
        !ob_all_stuck_full(p, rw),
{
    let env = Map::<nat, Val>::empty();
    let xs = unit_list();
    let c = XExpr::Int(1);
    let items = seq![Val::Unit];
    let ex = XExpr::All(Box::new(xs), x, Box::new(c));
    unit_list_evals(xp, p, rw, env);
    assert(items[0] == Val::Unit);
    assert(xeval(xp, 2, env.insert(x, Val::Unit), c) == Res::Done(Val::Int(1)));
    assert(xall(xp, 3, env, x, c, items, 0) == Res::Stuck);
    assert(xeval(xp, 4, env, ex) == Res::Stuck);
    assert(rw(c) == Expr::Int(1));
    bs_leaf(p, env.insert(x, Val::Unit), Expr::Int(1));
    assert(evals_to(p, env.insert(x, items[0]), rw(c), Val::Int(1)));
    all_gap(p, rw, env, xs, x, c, items, Val::Int(1));
    assert(pred_fails(p, env.insert(x, items[0]), rw(c)));
    assert(all_stuck_full(p, rw, env, x, c, items, 0, 0));
    if ob_all_stuck_full(p, rw) {
        assert(evals_stuck(p, env, rw(ex)));
    }
}

/// 隙間の具体例（sort_by）：sort_by([()], |x| ()) は、源では燃料 4 で行き詰まり（鍵 () は整数でない）、
/// 写しは [()] に評価される。したがって ob_sort_by_stuck_full は成り立たない。
pub proof fn sort_full_fails(xp: XProg, p: Prog, rw: spec_fn(XExpr) -> Expr, x: nat)
    requires
        hof_shapes(rw),
        homomorphic(rw),
    ensures
        xeval(xp, 4, Map::empty(), XExpr::SortBy(Box::new(unit_list()), x, Box::new(XExpr::Unit))) == Res::Stuck,
        evals_to(
            p,
            Map::empty(),
            rw(XExpr::SortBy(Box::new(unit_list()), x, Box::new(XExpr::Unit))),
            Val::List(seq![Val::Unit]),
        ),
        !ob_sort_by_stuck_full(p, rw),
{
    let env = Map::<nat, Val>::empty();
    let xs = unit_list();
    let k = XExpr::Unit;
    let items = seq![Val::Unit];
    let kv = seq![Val::Unit];
    let ex = XExpr::SortBy(Box::new(xs), x, Box::new(k));
    unit_list_evals(xp, p, rw, env);
    assert(items[0] == Val::Unit);
    assert(xeval(xp, 2, env.insert(x, Val::Unit), k) == Res::Done(Val::Unit));
    assert(xmap(xp, 2, env, x, k, items, 1) == ResSeq::Done(Seq::<Val>::empty()));
    assert(seq![Val::Unit] + Seq::<Val>::empty() =~= kv);
    assert(xmap(xp, 3, env, x, k, items, 0) == ResSeq::Done(kv));
    assert(!(int_of_val(kv[0]) is Some));
    assert(int_seq(kv) is None);
    assert(xeval(xp, 4, env, ex) == Res::Stuck);
    assert(rw(k) == Expr::Unit);
    bs_leaf(p, env.insert(x, Val::Unit), Expr::Unit);
    sort_gap(p, rw, env, xs, x, k, Val::Unit, Val::Unit);
    assert(map_ok(p, rw, env, x, k, items, kv, 0)) by {
        assert forall|m: int| 0 <= m < items.len() implies evals_to(
            p,
            #[trigger] env.insert(x, items[m]),
            rw(k),
            kv[m - (0nat as int)],
        ) by {
            assert(m == 0);
        }
    }
    if ob_sort_by_stuck_full(p, rw) {
        assert(evals_stuck(p, env, rw(ex)));
    }
}

} // verus!
