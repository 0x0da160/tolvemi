//! 燃料付き評価 `eval` から導いた大ステップ規則。
//!
//! `evals_to(p, env, e, v)` は「ある燃料で e が v に評価される」。exec の評価器は
//! 燃料を数えず、ここにある規則を組み合わせて自分の結果が spec の評価と一致することを示す。

use crate::proof::*;
use crate::spec::*;
use vstd::prelude::*;

verus! {

pub open spec fn evals_to(p: Prog, env: Map<nat, Val>, e: Expr, v: Val) -> bool {
    exists|n: nat| #[trigger] eval(p, n, env, e) == Res::Done(v)
}

pub open spec fn args_to(p: Prog, env: Map<nat, Val>, es: Seq<Expr>, i: nat, vs: Seq<Val>) -> bool {
    exists|n: nat| #[trigger] eval_args(p, n, env, es, i) == ResSeq::Done(vs)
}

pub open spec fn fold_to(
    p: Prog,
    env: Map<nat, Val>,
    acc: nat,
    item: nat,
    body: Expr,
    items: Seq<Val>,
    j: nat,
    a: Val,
    w: Val,
) -> bool {
    exists|n: nat| #[trigger] eval_fold(p, n, env, acc, item, body, items, j, a) == Res::Done(w)
}

/// 二つの燃料証拠を大きい方に揃える。
pub proof fn lift(p: Prog, n: nat, m: nat, env: Map<nat, Val>, e: Expr)
    requires
        n <= m,
        eval(p, n, env, e) is Done,
    ensures
        eval(p, m, env, e) == eval(p, n, env, e),
{
    mono(p, n, m, env, e);
}

pub proof fn bs_leaf(p: Prog, env: Map<nat, Val>, e: Expr)
    requires
        e is Int || e is Bool || e is Unit || e is None,
    ensures
        evals_to(
            p,
            env,
            e,
            match e {
                Expr::Int(n) => Val::Int(n),
                Expr::Bool(b) => Val::Bool(b),
                Expr::Unit => Val::Unit,
                _ => Val::None,
            },
        ),
{
    assert(eval(p, 1, env, e) is Done);
}

pub proof fn bs_var(p: Prog, env: Map<nat, Val>, x: nat)
    requires
        env.contains_key(x),
    ensures
        evals_to(p, env, Expr::Var(x), env[x]),
{
    assert(eval(p, 1, env, Expr::Var(x)) == Res::Done(env[x]));
}

pub proof fn bs_some(p: Prog, env: Map<nat, Val>, x: Expr, v: Val)
    requires
        evals_to(p, env, x, v),
    ensures
        evals_to(p, env, Expr::Some(Box::new(x)), Val::Some(Box::new(v))),
{
    let n = choose|n: nat| #[trigger] eval(p, n, env, x) == Res::Done(v);
    assert(eval(p, n + 1, env, Expr::Some(Box::new(x))) == Res::Done(Val::Some(Box::new(v))));
}

pub proof fn bs_pair(p: Prog, env: Map<nat, Val>, a: Expr, b: Expr, va: Val, vb: Val)
    requires
        evals_to(p, env, a, va),
        evals_to(p, env, b, vb),
    ensures
        evals_to(p, env, Expr::Pair(Box::new(a), Box::new(b)), Val::Pair(Box::new(va), Box::new(vb))),
{
    let n1 = choose|n: nat| #[trigger] eval(p, n, env, a) == Res::Done(va);
    let n2 = choose|n: nat| #[trigger] eval(p, n, env, b) == Res::Done(vb);
    let n = max(n1, n2);
    lift(p, n1, n, env, a);
    lift(p, n2, n, env, b);
    let e = Expr::Pair(Box::new(a), Box::new(b));
    assert(eval(p, n + 1, env, e) == Res::Done(Val::Pair(Box::new(va), Box::new(vb))));
}

pub proof fn bs_list(p: Prog, env: Map<nat, Val>, t: Ty, es: Seq<Expr>, vs: Seq<Val>)
    requires
        args_to(p, env, es, 0, vs),
    ensures
        evals_to(p, env, Expr::List(t, es), Val::List(vs)),
{
    let n = choose|n: nat| #[trigger] eval_args(p, n, env, es, 0) == ResSeq::Done(vs);
    assert(eval(p, n + 1, env, Expr::List(t, es)) == Res::Done(Val::List(vs)));
}

pub proof fn bs_builtin(p: Prog, env: Map<nat, Val>, b: Builtin, es: Seq<Expr>, vs: Seq<Val>, w: Val)
    requires
        args_to(p, env, es, 0, vs),
        apply(b, vs) == Res::Done(w),
    ensures
        evals_to(p, env, Expr::Builtin(b, es), w),
{
    let n = choose|n: nat| #[trigger] eval_args(p, n, env, es, 0) == ResSeq::Done(vs);
    assert(eval(p, n + 1, env, Expr::Builtin(b, es)) == Res::Done(w));
}

pub proof fn bs_call(p: Prog, env: Map<nat, Val>, g: nat, es: Seq<Expr>, vs: Seq<Val>, w: Val)
    requires
        args_to(p, env, es, 0, vs),
        g < p.funcs.len(),
        vs.len() == p.funcs[g as int].params.len(),
        evals_to(p, bind(p.funcs[g as int].params, vs, vs.len()), p.funcs[g as int].body, w),
    ensures
        evals_to(p, env, Expr::Call(g, es), w),
{
    let env2 = bind(p.funcs[g as int].params, vs, vs.len());
    let body = p.funcs[g as int].body;
    let n1 = choose|n: nat| #[trigger] eval_args(p, n, env, es, 0) == ResSeq::Done(vs);
    let n2 = choose|n: nat| #[trigger] eval(p, n, env2, body) == Res::Done(w);
    let n = max(n1, n2);
    mono_args(p, n1, n, env, es, 0);
    lift(p, n2, n, env2, body);
    assert(eval(p, n + 1, env, Expr::Call(g, es)) == Res::Done(w));
}

pub proof fn bs_let(p: Prog, env: Map<nat, Val>, x: nat, a: Expr, b: Expr, va: Val, w: Val)
    requires
        evals_to(p, env, a, va),
        evals_to(p, env.insert(x, va), b, w),
    ensures
        evals_to(p, env, Expr::Let(x, Box::new(a), Box::new(b)), w),
{
    let n1 = choose|n: nat| #[trigger] eval(p, n, env, a) == Res::Done(va);
    let n2 = choose|n: nat| #[trigger] eval(p, n, env.insert(x, va), b) == Res::Done(w);
    let n = max(n1, n2);
    lift(p, n1, n, env, a);
    lift(p, n2, n, env.insert(x, va), b);
    assert(eval(p, n + 1, env, Expr::Let(x, Box::new(a), Box::new(b))) == Res::Done(w));
}

pub proof fn bs_if(p: Prog, env: Map<nat, Val>, c: Expr, a: Expr, b: Expr, cv: bool, w: Val)
    requires
        evals_to(p, env, c, Val::Bool(cv)),
        evals_to(p, env, if cv { a } else { b }, w),
    ensures
        evals_to(p, env, Expr::If(Box::new(c), Box::new(a), Box::new(b)), w),
{
    let br = if cv { a } else { b };
    let n1 = choose|n: nat| #[trigger] eval(p, n, env, c) == Res::Done(Val::Bool(cv));
    let n2 = choose|n: nat| #[trigger] eval(p, n, env, br) == Res::Done(w);
    let n = max(n1, n2);
    lift(p, n1, n, env, c);
    lift(p, n2, n, env, br);
    assert(eval(p, n + 1, env, Expr::If(Box::new(c), Box::new(a), Box::new(b))) == Res::Done(w));
}

pub proof fn bs_fold(
    p: Prog,
    env: Map<nat, Val>,
    xs: Expr,
    init: Expr,
    acc: nat,
    item: nat,
    body: Expr,
    s: Seq<Val>,
    v0: Val,
    w: Val,
)
    requires
        evals_to(p, env, xs, Val::List(s)),
        evals_to(p, env, init, v0),
        fold_to(p, env, acc, item, body, s, 0, v0, w),
    ensures
        evals_to(p, env, Expr::Fold(Box::new(xs), Box::new(init), acc, item, Box::new(body)), w),
{
    let n1 = choose|n: nat| #[trigger] eval(p, n, env, xs) == Res::Done(Val::List(s));
    let n2 = choose|n: nat| #[trigger] eval(p, n, env, init) == Res::Done(v0);
    let n3 = choose|n: nat| #[trigger] eval_fold(p, n, env, acc, item, body, s, 0, v0) == Res::Done(w);
    let n = max(max(n1, n2), n3);
    lift(p, n1, n, env, xs);
    lift(p, n2, n, env, init);
    mono_fold(p, n3, n, env, acc, item, body, s, 0, v0);
    let e = Expr::Fold(Box::new(xs), Box::new(init), acc, item, Box::new(body));
    assert(eval(p, n + 1, env, e) == Res::Done(w));
}

/// 各引数が値に評価されれば、引数列は値列に評価される（後ろから組み立てる）。
pub proof fn args_from_each(p: Prog, env: Map<nat, Val>, es: Seq<Expr>, vs: Seq<Val>, i: nat)
    requires
        vs.len() == es.len(),
        i <= es.len(),
        forall|k: int| 0 <= k < es.len() ==> evals_to(p, env, #[trigger] es[k], vs[k]),
    ensures
        args_to(p, env, es, i, vs.subrange(i as int, vs.len() as int)),
    decreases es.len() - i,
{
    if i == es.len() {
        assert(eval_args(p, 1, env, es, i) == ResSeq::Done(Seq::<Val>::empty()));
        assert(vs.subrange(i as int, vs.len() as int) =~= Seq::<Val>::empty());
    } else {
        args_from_each(p, env, es, vs, i + 1);
        let rest = vs.subrange((i + 1) as int, vs.len() as int);
        assert(evals_to(p, env, es[i as int], vs[i as int]));
        let n1 = choose|n: nat| #[trigger] eval(p, n, env, es[i as int]) == Res::Done(vs[i as int]);
        let n2 = choose|n: nat| #[trigger] eval_args(p, n, env, es, i + 1) == ResSeq::Done(rest);
        let n = max(n1, n2);
        lift(p, n1, n, env, es[i as int]);
        mono_args(p, n2, n, env, es, i + 1);
        assert(seq![vs[i as int]] + rest =~= vs.subrange(i as int, vs.len() as int));
        assert(eval_args(p, n + 1, env, es, i) == ResSeq::Done(vs.subrange(i as int, vs.len() as int)));
    }
}

/// 各段の本体評価が成り立てば、畳み込み全体が成り立つ（後ろから組み立てる）。
pub proof fn fold_from_each(
    p: Prog,
    env: Map<nat, Val>,
    acc: nat,
    item: nat,
    body: Expr,
    items: Seq<Val>,
    accs: Seq<Val>,
    j: nat,
)
    requires
        accs.len() == items.len() + 1,
        j <= items.len(),
        forall|k: int|
            0 <= k < items.len() ==> evals_to(
                p,
                #[trigger] env.insert(acc, accs[k]).insert(item, items[k]),
                body,
                accs[k + 1],
            ),
    ensures
        fold_to(p, env, acc, item, body, items, j, accs[j as int], accs[items.len() as int]),
    decreases items.len() - j,
{
    let w = accs[items.len() as int];
    if j == items.len() {
        assert(eval_fold(p, 1, env, acc, item, body, items, j, w) == Res::Done(w));
    } else {
        fold_from_each(p, env, acc, item, body, items, accs, j + 1);
        let env2 = env.insert(acc, accs[j as int]).insert(item, items[j as int]);
        assert(evals_to(p, env2, body, accs[(j + 1) as int]));
        let n1 = choose|n: nat| #[trigger] eval(p, n, env2, body) == Res::Done(accs[(j + 1) as int]);
        let n2 = choose|n: nat|
            #[trigger] eval_fold(p, n, env, acc, item, body, items, j + 1, accs[(j + 1) as int]) == Res::Done(w);
        let n = max(n1, n2);
        lift(p, n1, n, env2, body);
        mono_fold(p, n2, n, env, acc, item, body, items, j + 1, accs[(j + 1) as int]);
        assert(eval_fold(p, n + 1, env, acc, item, body, items, j, accs[j as int]) == Res::Done(w));
    }
}

// ------------------------------------------------------------------ 行き詰まりの伝播

/// どの燃料でも Done にならない（Stuck か燃料切れ）。exec 評価器の Fault はこれに当たる。
pub open spec fn fails(p: Prog, env: Map<nat, Val>, e: Expr) -> bool {
    forall|n: nat| !(#[trigger] eval(p, n, env, e) is Done)
}

pub open spec fn args_fail(p: Prog, env: Map<nat, Val>, es: Seq<Expr>, i: nat) -> bool {
    forall|n: nat| !(#[trigger] eval_args(p, n, env, es, i) is Done)
}

pub open spec fn fold_fail(
    p: Prog,
    env: Map<nat, Val>,
    acc: nat,
    item: nat,
    body: Expr,
    items: Seq<Val>,
    j: nat,
    a: Val,
) -> bool {
    forall|n: nat| !(#[trigger] eval_fold(p, n, env, acc, item, body, items, j, a) is Done)
}

/// evals_to の値は、Done になるどの燃料でも同じ。
pub proof fn same(p: Prog, n: nat, env: Map<nat, Val>, e: Expr, v: Val)
    requires
        evals_to(p, env, e, v),
        eval(p, n, env, e) is Done,
    ensures
        eval(p, n, env, e) == Res::Done(v),
{
    let m = choose|m: nat| #[trigger] eval(p, m, env, e) == Res::Done(v);
    eval_deterministic(p, n, m, env, e);
}

pub proof fn same_args(p: Prog, n: nat, env: Map<nat, Val>, es: Seq<Expr>, vs: Seq<Val>)
    requires
        args_to(p, env, es, 0, vs),
        eval_args(p, n, env, es, 0) is Done,
    ensures
        eval_args(p, n, env, es, 0) == ResSeq::Done(vs),
{
    let m = choose|m: nat| #[trigger] eval_args(p, m, env, es, 0) == ResSeq::Done(vs);
    if n <= m {
        mono_args(p, n, m, env, es, 0);
    } else {
        mono_args(p, m, n, env, es, 0);
    }
}

pub proof fn fl_var(p: Prog, env: Map<nat, Val>, x: nat)
    requires
        !env.contains_key(x),
    ensures
        fails(p, env, Expr::Var(x)),
{
    assert forall|n: nat| !(#[trigger] eval(p, n, env, Expr::Var(x)) is Done) by {}
}

pub proof fn fl_some(p: Prog, env: Map<nat, Val>, x: Expr)
    requires
        fails(p, env, x),
    ensures
        fails(p, env, Expr::Some(Box::new(x))),
{
    assert forall|n: nat| !(#[trigger] eval(p, n, env, Expr::Some(Box::new(x))) is Done) by {
        if n > 0 {
            assert(!(eval(p, (n - 1) as nat, env, x) is Done));
        }
    }
}

pub proof fn fl_pair(p: Prog, env: Map<nat, Val>, a: Expr, b: Expr)
    requires
        fails(p, env, a) || fails(p, env, b),
    ensures
        fails(p, env, Expr::Pair(Box::new(a), Box::new(b))),
{
    assert forall|n: nat| !(#[trigger] eval(p, n, env, Expr::Pair(Box::new(a), Box::new(b))) is Done) by {
        if n > 0 {
            assert(!(eval(p, (n - 1) as nat, env, a) is Done) || !(eval(p, (n - 1) as nat, env, b) is Done));
        }
    }
}

pub proof fn fl_list(p: Prog, env: Map<nat, Val>, t: Ty, es: Seq<Expr>)
    requires
        args_fail(p, env, es, 0),
    ensures
        fails(p, env, Expr::List(t, es)),
{
    assert forall|n: nat| !(#[trigger] eval(p, n, env, Expr::List(t, es)) is Done) by {
        if n > 0 {
            assert(!(eval_args(p, (n - 1) as nat, env, es, 0) is Done));
        }
    }
}

/// 引数 es[i] が行き詰まれば、引数列全体も行き詰まる。
pub proof fn fl_args(p: Prog, env: Map<nat, Val>, es: Seq<Expr>, i: nat)
    requires
        i < es.len(),
        fails(p, env, es[i as int]),
    ensures
        args_fail(p, env, es, 0),
    decreases i,
{
    assert forall|n: nat| !(#[trigger] eval_args(p, n, env, es, i) is Done) by {
        if n > 0 {
            assert(!(eval(p, (n - 1) as nat, env, es[i as int]) is Done));
        }
    }
    fl_args_back(p, env, es, i);
}

proof fn fl_args_back(p: Prog, env: Map<nat, Val>, es: Seq<Expr>, i: nat)
    requires
        i < es.len(),
        args_fail(p, env, es, i),
    ensures
        args_fail(p, env, es, 0),
    decreases i,
{
    if i > 0 {
        let k = (i - 1) as nat;
        assert forall|n: nat| !(#[trigger] eval_args(p, n, env, es, k) is Done) by {
            if n > 0 {
                assert(!(eval_args(p, (n - 1) as nat, env, es, i) is Done));
            }
        }
        fl_args_back(p, env, es, k);
    }
}

pub proof fn fl_builtin(p: Prog, env: Map<nat, Val>, b: Builtin, es: Seq<Expr>, vs: Seq<Val>)
    requires
        args_fail(p, env, es, 0) || (args_to(p, env, es, 0, vs) && !(apply(b, vs) is Done)),
    ensures
        fails(p, env, Expr::Builtin(b, es)),
{
    assert forall|n: nat| !(#[trigger] eval(p, n, env, Expr::Builtin(b, es)) is Done) by {
        if n > 0 {
            let f = (n - 1) as nat;
            if eval_args(p, f, env, es, 0) is Done {
                same_args(p, f, env, es, vs);
            }
        }
    }
}

pub proof fn fl_call(p: Prog, env: Map<nat, Val>, g: nat, es: Seq<Expr>, vs: Seq<Val>)
    requires
        args_fail(p, env, es, 0) || (args_to(p, env, es, 0, vs) && (!(g < p.funcs.len() && vs.len()
            == p.funcs[g as int].params.len()) || fails(
            p,
            bind(p.funcs[g as int].params, vs, vs.len()),
            p.funcs[g as int].body,
        ))),
    ensures
        fails(p, env, Expr::Call(g, es)),
{
    assert forall|n: nat| !(#[trigger] eval(p, n, env, Expr::Call(g, es)) is Done) by {
        if n > 0 {
            let f = (n - 1) as nat;
            if eval_args(p, f, env, es, 0) is Done {
                same_args(p, f, env, es, vs);
                if g < p.funcs.len() && vs.len() == p.funcs[g as int].params.len() {
                    assert(!(eval(p, f, bind(p.funcs[g as int].params, vs, vs.len()), p.funcs[g as int].body) is Done));
                }
            }
        }
    }
}

pub proof fn fl_let(p: Prog, env: Map<nat, Val>, x: nat, a: Expr, b: Expr, va: Val)
    requires
        fails(p, env, a) || (evals_to(p, env, a, va) && fails(p, env.insert(x, va), b)),
    ensures
        fails(p, env, Expr::Let(x, Box::new(a), Box::new(b))),
{
    assert forall|n: nat| !(#[trigger] eval(p, n, env, Expr::Let(x, Box::new(a), Box::new(b))) is Done) by {
        if n > 0 {
            let f = (n - 1) as nat;
            if eval(p, f, env, a) is Done {
                same(p, f, env, a, va);
                assert(!(eval(p, f, env.insert(x, va), b) is Done));
            }
        }
    }
}

pub proof fn fl_if(p: Prog, env: Map<nat, Val>, c: Expr, a: Expr, b: Expr, cv: Val)
    requires
        fails(p, env, c) || (evals_to(p, env, c, cv) && (!(cv is Bool) || (cv == Val::Bool(true) && fails(
            p,
            env,
            a,
        )) || (cv == Val::Bool(false) && fails(p, env, b)))),
    ensures
        fails(p, env, Expr::If(Box::new(c), Box::new(a), Box::new(b))),
{
    assert forall|n: nat| !(#[trigger] eval(p, n, env, Expr::If(Box::new(c), Box::new(a), Box::new(b))) is Done) by {
        if n > 0 {
            let f = (n - 1) as nat;
            if eval(p, f, env, c) is Done {
                same(p, f, env, c, cv);
                assert(!(eval(p, f, env, a) is Done) || !(cv == Val::Bool(true)));
                assert(!(eval(p, f, env, b) is Done) || !(cv == Val::Bool(false)));
            }
        }
    }
}

/// 畳み込み：リスト式・初期値・各段の本体のどれかが行き詰まれば全体も行き詰まる。
pub proof fn fl_fold(
    p: Prog,
    env: Map<nat, Val>,
    xs: Expr,
    init: Expr,
    acc: nat,
    item: nat,
    body: Expr,
    xv: Val,
    v0: Val,
)
    requires
        fails(p, env, xs) || (evals_to(p, env, xs, xv) && (!(xv is List) || fails(p, env, init) || (evals_to(
            p,
            env,
            init,
            v0,
        ) && fold_fail(p, env, acc, item, body, xv->List_0, 0, v0)))),
    ensures
        fails(p, env, Expr::Fold(Box::new(xs), Box::new(init), acc, item, Box::new(body))),
{
    let e = Expr::Fold(Box::new(xs), Box::new(init), acc, item, Box::new(body));
    assert forall|n: nat| !(#[trigger] eval(p, n, env, e) is Done) by {
        if n > 0 {
            let f = (n - 1) as nat;
            if eval(p, f, env, xs) is Done {
                same(p, f, env, xs, xv);
                if xv is List && eval(p, f, env, init) is Done {
                    same(p, f, env, init, v0);
                    assert(!(eval_fold(p, f, env, acc, item, body, xv->List_0, 0, v0) is Done));
                }
            }
        }
    }
}

/// 本体が段 j で行き詰まり、それより前の段は値に評価されたなら、畳み込みは段 0 から行き詰まる。
pub proof fn fl_fold_steps(
    p: Prog,
    env: Map<nat, Val>,
    acc: nat,
    item: nat,
    body: Expr,
    items: Seq<Val>,
    accs: Seq<Val>,
    j: nat,
)
    requires
        j < items.len(),
        accs.len() == j + 1,
        fails(p, env.insert(acc, accs[j as int]).insert(item, items[j as int]), body),
        forall|k: int|
            0 <= k < j ==> evals_to(
                p,
                #[trigger] env.insert(acc, accs[k]).insert(item, items[k]),
                body,
                accs[k + 1],
            ),
    ensures
        fold_fail(p, env, acc, item, body, items, 0, accs[0]),
{
    let env2 = env.insert(acc, accs[j as int]).insert(item, items[j as int]);
    assert forall|n: nat| !(#[trigger] eval_fold(p, n, env, acc, item, body, items, j, accs[j as int]) is Done) by {
        if n > 0 {
            assert(!(eval(p, (n - 1) as nat, env2, body) is Done));
        }
    }
    fl_fold_back(p, env, acc, item, body, items, accs, j);
}

proof fn fl_fold_back(
    p: Prog,
    env: Map<nat, Val>,
    acc: nat,
    item: nat,
    body: Expr,
    items: Seq<Val>,
    accs: Seq<Val>,
    j: nat,
)
    requires
        j < items.len(),
        j < accs.len(),
        fold_fail(p, env, acc, item, body, items, j, accs[j as int]),
        forall|k: int|
            0 <= k < j ==> evals_to(
                p,
                #[trigger] env.insert(acc, accs[k]).insert(item, items[k]),
                body,
                accs[k + 1],
            ),
    ensures
        fold_fail(p, env, acc, item, body, items, 0, accs[0]),
    decreases j,
{
    if j > 0 {
        let k = (j - 1) as nat;
        let env2 = env.insert(acc, accs[k as int]).insert(item, items[k as int]);
        assert(evals_to(p, env2, body, accs[j as int]));
        assert forall|n: nat| !(#[trigger] eval_fold(p, n, env, acc, item, body, items, k, accs[k as int]) is Done) by {
            if n > 0 {
                let f = (n - 1) as nat;
                if eval(p, f, env2, body) is Done {
                    same(p, f, env2, body, accs[j as int]);
                    assert(!(eval_fold(p, f, env, acc, item, body, items, j, accs[j as int]) is Done));
                }
            }
        }
        fl_fold_back(p, env, acc, item, body, items, accs, k);
    }
}

} // verus!
