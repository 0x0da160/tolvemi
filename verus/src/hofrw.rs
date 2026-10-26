//! 書換えの写しの spec（段階 1b・書換えの形の仮定の、hof の部分の証明、DECISION-23「書換えを Verus で書く」）。
//!
//! 源の式 `XExpr` から核の式 `Expr` への写し `rw_tb(tb, e)` を spec で定める。`tb` は hof の束縛名 x から
//! 要素の型への表（checker が hof の node に付けた型の写し。`hof.rs` の `HofTypes` に当たる）。構成子の写しは
//! 構造どおりで、型の注釈は erase_ty で消す。hof の形は hof.rs の lower と同じ形（fold_meaning.rs の map_collect・
//! filter_collect・any_fold・all_fold・find_fold と、sortmeaning.rs の sort_collect）。導入する名前は、束縛名 x と
//! 本体の写しの名前のどれよりも大きく取る（`hof_base`）。
//!
//! ここで示すこと：この写しは `homomorphic` と `hof_shapes` を満たす（sh6_obligations.rs と simulation.rs の仮定）。
//! したがって、写しを使う SH4・SH6 の定理は、この写しについては仮定なしに成り立つ。
//! 扱わないこと：この写しを exec で実装し、Rust の hof.rs の出力と一致させること（段階 1b の残り）。

use crate::fold_meaning::*;
use crate::fresh::*;
use crate::proof::*;
use crate::records_proof::*;
use crate::sh6_obligations::*;
use crate::simulation::*;
use crate::sortmeaning::*;
use crate::spec::*;
use crate::xsem::*;
use vstd::prelude::*;

verus! {

/// hof の束縛名 x の要素の型（表に無ければ Int。表が正しい源では起きない）。
pub open spec fn hof_ann(tb: Map<nat, Ty>, x: nat) -> Ty {
    if tb.contains_key(x) {
        tb[x]
    } else {
        Ty::Int
    }
}

/// 写しの導入する名前の基準：束縛名 x より大きく、写した本体 g のどの名前より大きい。
pub open spec fn hof_base(x: nat, g: Expr) -> nat {
    max(x + 1, top(g))
}

// ------------------------------------------------------------------ 写し

/// 源の式の列の写し（i から先）。
pub open spec fn rw_tb_args(tb: Map<nat, Ty>, es: Seq<XExpr>, i: nat) -> Seq<Expr>
    decreases es, es.len() - i,
{
    if i >= es.len() {
        Seq::empty()
    } else {
        seq![rw_tb(tb, es[i as int])] + rw_tb_args(tb, es, i + 1)
    }
}

/// 源の式の写し。hof の形は、写した本体 g に対して `hof_base(x, g)` から名前を取る。
pub open spec fn rw_tb(tb: Map<nat, Ty>, e: XExpr) -> Expr
    decreases e, 0nat,
{
    match e {
        XExpr::Int(n) => Expr::Int(n),
        XExpr::Bool(b) => Expr::Bool(b),
        XExpr::Unit => Expr::Unit,
        XExpr::Char(c) => Expr::Char(c),
        XExpr::Var(x) => Expr::Var(x),
        XExpr::List(t, es) => Expr::List(erase_ty(t), rw_tb_args(tb, es, 0)),
        XExpr::Some(a) => Expr::Some(Box::new(rw_tb(tb, *a))),
        XExpr::None(t) => Expr::None(erase_ty(t)),
        XExpr::Pair(a, b) => Expr::Pair(Box::new(rw_tb(tb, *a)), Box::new(rw_tb(tb, *b))),
        XExpr::Builtin(b, es) => Expr::Builtin(b, rw_tb_args(tb, es, 0)),
        XExpr::Call(g, es) => Expr::Call(g, rw_tb_args(tb, es, 0)),
        XExpr::Let(x, a, b) => Expr::Let(x, Box::new(rw_tb(tb, *a)), Box::new(rw_tb(tb, *b))),
        XExpr::If(c, a, b) => Expr::If(Box::new(rw_tb(tb, *c)), Box::new(rw_tb(tb, *a)), Box::new(rw_tb(tb, *b))),
        XExpr::Fold(xs, init, acc, item, body) => Expr::Fold(
            Box::new(rw_tb(tb, *xs)),
            Box::new(rw_tb(tb, *init)),
            acc,
            item,
            Box::new(rw_tb(tb, *body)),
        ),
        XExpr::Match(m, nb, x, sm) => Expr::Match(
            Box::new(rw_tb(tb, *m)),
            Box::new(rw_tb(tb, *nb)),
            x,
            Box::new(rw_tb(tb, *sm)),
        ),
        XExpr::Inj(ok, t, u, a) => Expr::Inj(ok, erase_ty(t), erase_ty(u), Box::new(rw_tb(tb, *a))),
        XExpr::MatchR(m, x, a, y, b) => Expr::MatchR(
            Box::new(rw_tb(tb, *m)),
            x,
            Box::new(rw_tb(tb, *a)),
            y,
            Box::new(rw_tb(tb, *b)),
        ),
        XExpr::Map(xs, x, c) => {
            let g = rw_tb(tb, *c);
            map_collect(rw_tb(tb, *xs), erase_ty(hof_ann(tb, x)), hof_base(x, g), x, g)
        },
        XExpr::Filter(xs, x, c) => {
            let g = rw_tb(tb, *c);
            filter_collect(rw_tb(tb, *xs), erase_ty(hof_ann(tb, x)), hof_base(x, g), x, g)
        },
        XExpr::Any(xs, x, c) => {
            let g = rw_tb(tb, *c);
            any_fold(rw_tb(tb, *xs), hof_base(x, g), x, g)
        },
        XExpr::All(xs, x, c) => {
            let g = rw_tb(tb, *c);
            all_fold(rw_tb(tb, *xs), hof_base(x, g), x, g)
        },
        XExpr::Find(xs, x, c) => {
            let g = rw_tb(tb, *c);
            let b = hof_base(x, g);
            find_fold(rw_tb(tb, *xs), erase_ty(hof_ann(tb, x)), b, x, g, b + 1)
        },
        XExpr::SortBy(xs, x, k) => {
            let g = rw_tb(tb, *k);
            let b = hof_base(x, g);
            sort_collect(
                rw_tb(tb, *xs),
                erase_ty(hof_ann(tb, x)),
                b,
                b + 1,
                b + 2,
                b + 3,
                b + 4,
                b + 5,
                b + 6,
                x,
                g,
            )
        },
    }
}

// ------------------------------------------------------------------ 導入する名前の新しさ

/// g の名前の上限 top(g) 以上の名前は、g に現れない。
pub proof fn tb_absent_above(m: nat, g: Expr)
    requires
        top(g) <= m,
    ensures
        absent(m, g),
{
    top_below(g);
    below_absent(top(g), m, g);
}

/// 導入する名前の基準は、束縛名 x と違い、本体の写し g に現れない。
pub proof fn tb_base_fresh(x: nat, g: Expr)
    ensures
        hof_base(x, g) != x,
        absent(hof_base(x, g), g),
        absent(hof_base(x, g) + 1, g),
        absent(hof_base(x, g) + 2, g),
        absent(hof_base(x, g) + 3, g),
{
    tb_absent_above(hof_base(x, g), g);
    tb_absent_above(hof_base(x, g) + 1, g);
    tb_absent_above(hof_base(x, g) + 2, g);
    tb_absent_above(hof_base(x, g) + 3, g);
}

// ------------------------------------------------------------------ 列の写し

/// 列の写しは、要素ごとの写しの並びに等しい（simulation.rs の rw_args の形）。
pub proof fn tb_args_eq(tb: Map<nat, Ty>, es: Seq<XExpr>, i: nat)
    requires
        i <= es.len(),
    ensures
        rw_tb_args(tb, es, i) =~= Seq::new((es.len() - i) as nat, |k: int| rw_tb(tb, es[i + k])),
    decreases es.len() - i,
{
    if i < es.len() {
        tb_args_eq(tb, es, i + 1);
        let n = (es.len() - i) as nat;
        let rest = Seq::new((es.len() - i - 1) as nat, |k: int| rw_tb(tb, es[i + 1 + k]));
        assert(rw_tb_args(tb, es, i) =~= seq![rw_tb(tb, es[i as int])] + rw_tb_args(tb, es, i + 1));
        assert(rw_tb_args(tb, es, i + 1) =~= rest);
        assert(seq![rw_tb(tb, es[i as int])] + rest =~= Seq::new(n, |k: int| rw_tb(tb, es[i + k])));
    }
}

/// 写しの列（simulation.rs の rw_args）は、rw_tb_args に等しい。rw は rw_tb と一致する関数。
pub proof fn tb_args_rw(tb: Map<nat, Ty>, rw: spec_fn(XExpr) -> Expr, es: Seq<XExpr>)
    requires
        forall|e: XExpr| #[trigger] rw(e) == rw_tb(tb, e),
    ensures
        rw_args(rw, es) =~= rw_tb_args(tb, es, 0),
{
    tb_args_eq(tb, es, 0);
    assert(rw_args(rw, es) =~= Seq::new(es.len(), |k: int| rw_tb(tb, es[k])));
}

// ------------------------------------------------------------------ 形の仮定の証明

/// 写しは `homomorphic` を満たす（核の形は構造どおり、呼出しと列は要素ごとの写し）。
pub proof fn tb_homomorphic(tb: Map<nat, Ty>, rw: spec_fn(XExpr) -> Expr)
    requires
        forall|e: XExpr| #[trigger] rw(e) == rw_tb(tb, e),
    ensures
        homomorphic(rw),
{
    reveal_with_fuel(rw_tb, 1);
    assert forall|n: int| #[trigger] rw(XExpr::Int(n)) == Expr::Int(n) by {}
    assert forall|b: bool| #[trigger] rw(XExpr::Bool(b)) == Expr::Bool(b) by {}
    assert(rw(XExpr::Unit) == Expr::Unit);
    assert forall|c: int| #[trigger] rw(XExpr::Char(c)) == Expr::Char(c) by {}
    assert forall|x: nat| #[trigger] rw(XExpr::Var(x)) == Expr::Var(x) by {}
    assert forall|t: Ty, es: Seq<XExpr>| #[trigger] rw(XExpr::List(t, es)) == Expr::List(erase_ty(t), rw_args(rw, es))
        by {
        tb_args_rw(tb, rw, es);
    }
    assert forall|a: XExpr| #[trigger] rw(XExpr::Some(Box::new(a))) == Expr::Some(Box::new(rw(a))) by {}
    assert forall|t: Ty| #[trigger] rw(XExpr::None(t)) == Expr::None(erase_ty(t)) by {}
    assert forall|a: XExpr, b: XExpr|
        #[trigger] rw(XExpr::Pair(Box::new(a), Box::new(b))) == Expr::Pair(Box::new(rw(a)), Box::new(rw(b))) by {}
    assert forall|bi: Builtin, es: Seq<XExpr>| #[trigger] rw(XExpr::Builtin(bi, es)) == Expr::Builtin(
        bi,
        rw_args(rw, es),
    ) by {
        tb_args_rw(tb, rw, es);
    }
    assert forall|g: nat, es: Seq<XExpr>| #[trigger] rw(XExpr::Call(g, es)) == Expr::Call(g, rw_args(rw, es)) by {
        tb_args_rw(tb, rw, es);
    }
    assert forall|x: nat, a: XExpr, b: XExpr|
        #[trigger] rw(XExpr::Let(x, Box::new(a), Box::new(b))) == Expr::Let(x, Box::new(rw(a)), Box::new(rw(b))) by {}
    assert forall|c: XExpr, a: XExpr, b: XExpr|
        #[trigger] rw(XExpr::If(Box::new(c), Box::new(a), Box::new(b))) == Expr::If(
            Box::new(rw(c)),
            Box::new(rw(a)),
            Box::new(rw(b)),
        ) by {}
    assert forall|xs: XExpr, init: XExpr, acc: nat, item: nat, body: XExpr|
        #[trigger] rw(XExpr::Fold(Box::new(xs), Box::new(init), acc, item, Box::new(body))) == Expr::Fold(
            Box::new(rw(xs)),
            Box::new(rw(init)),
            acc,
            item,
            Box::new(rw(body)),
        ) by {}
    assert forall|m: XExpr, nb: XExpr, x: nat, sm: XExpr|
        #[trigger] rw(XExpr::Match(Box::new(m), Box::new(nb), x, Box::new(sm))) == Expr::Match(
            Box::new(rw(m)),
            Box::new(rw(nb)),
            x,
            Box::new(rw(sm)),
        ) by {}
    assert forall|ok: bool, t: Ty, u: Ty, a: XExpr|
        #[trigger] rw(XExpr::Inj(ok, t, u, Box::new(a))) == Expr::Inj(ok, erase_ty(t), erase_ty(u), Box::new(rw(a)))
        by {}
    assert forall|m: XExpr, x: nat, a: XExpr, y: nat, b: XExpr|
        #[trigger] rw(XExpr::MatchR(Box::new(m), x, Box::new(a), y, Box::new(b))) == Expr::MatchR(
            Box::new(rw(m)),
            x,
            Box::new(rw(a)),
            y,
            Box::new(rw(b)),
        ) by {}
}

/// 写しは `hof_shapes` を満たす 形ごとの証明。導入する名前は hof_base（束縛名と本体の名前より大きい）、列の注釈は erase_ty。

/// Map の写しは map_form を満たす。
pub proof fn tb_map_shape(tb: Map<nat, Ty>, rw: spec_fn(XExpr) -> Expr, xs: XExpr, x: nat, c: XExpr)
    requires
        forall|e: XExpr| #[trigger] rw(e) == rw_tb(tb, e),
    ensures
        map_form(rw, xs, x, c),
{
    reveal_with_fuel(rw_tb, 1);
    let g = rw_tb(tb, c);
    let b = hof_base(x, g);
    tb_base_fresh(x, g);
    assert(rw(XExpr::Map(Box::new(xs), x, Box::new(c))) == map_collect(rw(xs), erase_ty(hof_ann(tb, x)), hof_base(x, g), x, g));
}

/// Filter の写しは filter_form を満たす。
pub proof fn tb_filter_shape(tb: Map<nat, Ty>, rw: spec_fn(XExpr) -> Expr, xs: XExpr, x: nat, c: XExpr)
    requires
        forall|e: XExpr| #[trigger] rw(e) == rw_tb(tb, e),
    ensures
        filter_form(rw, xs, x, c),
{
    reveal_with_fuel(rw_tb, 1);
    let g = rw_tb(tb, c);
    let b = hof_base(x, g);
    tb_base_fresh(x, g);
    assert(rw(XExpr::Filter(Box::new(xs), x, Box::new(c))) == filter_collect(rw(xs), erase_ty(hof_ann(tb, x)), hof_base(x, g), x, g));
}

/// Any の写しは any_form を満たす。
pub proof fn tb_any_shape(tb: Map<nat, Ty>, rw: spec_fn(XExpr) -> Expr, xs: XExpr, x: nat, c: XExpr)
    requires
        forall|e: XExpr| #[trigger] rw(e) == rw_tb(tb, e),
    ensures
        any_form(rw, xs, x, c),
{
    reveal_with_fuel(rw_tb, 1);
    let g = rw_tb(tb, c);
    let b = hof_base(x, g);
    tb_base_fresh(x, g);
    assert(rw(XExpr::Any(Box::new(xs), x, Box::new(c))) == any_fold(rw(xs), hof_base(x, g), x, g));
}

/// All の写しは all_form を満たす。
pub proof fn tb_all_shape(tb: Map<nat, Ty>, rw: spec_fn(XExpr) -> Expr, xs: XExpr, x: nat, c: XExpr)
    requires
        forall|e: XExpr| #[trigger] rw(e) == rw_tb(tb, e),
    ensures
        all_form(rw, xs, x, c),
{
    reveal_with_fuel(rw_tb, 1);
    let g = rw_tb(tb, c);
    let b = hof_base(x, g);
    tb_base_fresh(x, g);
    assert(rw(XExpr::All(Box::new(xs), x, Box::new(c))) == all_fold(rw(xs), hof_base(x, g), x, g));
}

/// Find の写しは find_form を満たす。
pub proof fn tb_find_shape(tb: Map<nat, Ty>, rw: spec_fn(XExpr) -> Expr, xs: XExpr, x: nat, c: XExpr)
    requires
        forall|e: XExpr| #[trigger] rw(e) == rw_tb(tb, e),
    ensures
        find_form(rw, xs, x, c),
{
    reveal_with_fuel(rw_tb, 1);
    let g = rw_tb(tb, c);
    let b = hof_base(x, g);
    tb_base_fresh(x, g);
    assert(rw(XExpr::Find(Box::new(xs), x, Box::new(c))) == find_fold(rw(xs), erase_ty(hof_ann(tb, x)), b, x, g, b + 1));
}

/// 写しは `hof_shapes` を満たす。
pub proof fn tb_sort_shape(tb: Map<nat, Ty>, rw: spec_fn(XExpr) -> Expr, xs: XExpr, x: nat, k: XExpr)
    requires
        forall|e: XExpr| #[trigger] rw(e) == rw_tb(tb, e),
    ensures
        sort_form(rw, xs, x, k),
{
    reveal_with_fuel(rw_tb, 1);
    let g = rw_tb(tb, k);
    let b = hof_base(x, g);
    tb_base_fresh(x, g);
    assert(rw(XExpr::SortBy(Box::new(xs), x, Box::new(k))) == sort_collect(
        rw(xs),
        erase_ty(hof_ann(tb, x)),
        b,
        b + 1,
        b + 2,
        b + 3,
        b + 4,
        b + 5,
        b + 6,
        x,
        g,
    ));
}

/// 写しは `hof_shapes` を満たす（六つの形それぞれについて）。
pub proof fn tb_hof_shapes(tb: Map<nat, Ty>, rw: spec_fn(XExpr) -> Expr)
    requires
        forall|e: XExpr| #[trigger] rw(e) == rw_tb(tb, e),
    ensures
        hof_shapes(rw),
{
    assert forall|xs: XExpr, x: nat, c: XExpr| #[trigger] map_form(rw, xs, x, c) by {
        tb_map_shape(tb, rw, xs, x, c);
    }
    assert forall|xs: XExpr, x: nat, c: XExpr| #[trigger] filter_form(rw, xs, x, c) by {
        tb_filter_shape(tb, rw, xs, x, c);
    }
    assert forall|xs: XExpr, x: nat, c: XExpr| #[trigger] any_form(rw, xs, x, c) by {
        tb_any_shape(tb, rw, xs, x, c);
    }
    assert forall|xs: XExpr, x: nat, c: XExpr| #[trigger] all_form(rw, xs, x, c) by {
        tb_all_shape(tb, rw, xs, x, c);
    }
    assert forall|xs: XExpr, x: nat, c: XExpr| #[trigger] find_form(rw, xs, x, c) by {
        tb_find_shape(tb, rw, xs, x, c);
    }
    assert forall|xs: XExpr, x: nat, k: XExpr| #[trigger] sort_form(rw, xs, x, k) by {
        tb_sort_shape(tb, rw, xs, x, k);
    }
}

} // verus!
