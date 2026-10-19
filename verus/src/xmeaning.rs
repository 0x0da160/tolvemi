//! 源の写像の意味（段階 1b・SH1 の第二部）。
//!
//! 源の map（`XExpr::Map`、xsem.rs）は、核の書換え（fold_meaning.rs の `map_collect`）と同じ値に評価される。
//! 両者の前提は同じ：列 xs の値 items と、要素ごとの本体の値 gv[k]。
//! 核の側は本体が累積値の名前 acc を含まない（absent）ことを仮定する。源の側はそれを要しない。

use crate::bigstep::*;
use crate::fold_meaning::*;
use crate::proof::*;
use crate::records_proof::*;
use crate::spec::*;
use crate::xsem::*;
use vstd::prelude::*;

verus! {

/// 源の式が値 v に評価される（ある燃料で）。
pub open spec fn xevals_to(xp: XProg, env: Map<nat, Val>, e: XExpr, v: Val) -> bool {
    exists|n: nat| #[trigger] xeval(xp, n, env, e) == Res::Done(v)
}

/// 本体が核の写しのとき、源の map の評価は燃料を増やしても変わらない。
proof fn xmap_mono(p: Prog, n: nat, m: nat, env: Map<nat, Val>, x: nat, g: Expr, items: Seq<Val>, j: nat)
    requires
        n <= m,
        xmap(embed_prog(p), n, env, x, embed(g), items, j) is Done,
    ensures
        xmap(embed_prog(p), m, env, x, embed(g), items, j) == xmap(embed_prog(p), n, env, x, embed(g), items, j),
    decreases items.len() - j,
{
    if j < items.len() {
        let env2 = env.insert(x, items[j as int]);
        let f = (n - 1) as nat;
        let fm = (m - 1) as nat;
        assert(n > 0);
        embed_eval(p, f, env2, g);
        assert(eval(p, f, env2, g) is Done);
        lift(p, f, fm, env2, g);
        embed_eval(p, fm, env2, g);
        assert(xmap(embed_prog(p), f, env, x, embed(g), items, j + 1) is Done);
        xmap_mono(p, f, fm, env, x, g, items, j + 1);
    }
}

/// 要素ごとの本体の値 gv[j..] から、源の map は gv[j..] を返す（燃料の存在）。
proof fn xmap_from_each(p: Prog, env: Map<nat, Val>, x: nat, g: Expr, items: Seq<Val>, gv: Seq<Val>, j: nat)
    requires
        gv.len() == items.len(),
        j <= items.len(),
        forall|k: int|
            0 <= k < items.len() ==> evals_to(p, #[trigger] env.insert(x, items[k]), g, gv[k]),
    ensures
        exists|n: nat|
            #[trigger] xmap(embed_prog(p), n, env, x, embed(g), items, j) == ResSeq::Done(
                gv.subrange(j as int, gv.len() as int),
            ),
    decreases items.len() - j,
{
    if j == items.len() {
        assert(xmap(embed_prog(p), 1, env, x, embed(g), items, j) == ResSeq::Done(Seq::<Val>::empty()));
        assert(gv.subrange(j as int, gv.len() as int) =~= Seq::<Val>::empty());
    } else {
        xmap_from_each(p, env, x, g, items, gv, j + 1);
        let env2 = env.insert(x, items[j as int]);
        let n1 = choose|n: nat| #[trigger] eval(p, n, env2, g) == Res::Done(gv[j as int]);
        let n2 = choose|n: nat|
            #[trigger] xmap(embed_prog(p), n, env, x, embed(g), items, j + 1) == ResSeq::Done(
                gv.subrange((j + 1) as int, gv.len() as int),
            );
        let n = max(n1, n2);
        lift(p, n1, n, env2, g);
        embed_eval(p, n, env2, g);
        xmap_mono(p, n2, n, env, x, g, items, j + 1);
        assert(seq![gv[j as int]] + gv.subrange((j + 1) as int, gv.len() as int) =~= gv.subrange(
            j as int,
            gv.len() as int,
        ));
        assert(xmap(embed_prog(p), n + 1, env, x, embed(g), items, j) == ResSeq::Done(
            gv.subrange(j as int, gv.len() as int),
        ));
    }
}

/// 源の map の意味：列 xs が items に、要素ごとの本体が gv[k] に評価されれば、源の map は List(gv) に評価される。
pub proof fn map_source(p: Prog, env: Map<nat, Val>, xs: Expr, x: nat, g: Expr, items: Seq<Val>, gv: Seq<Val>)
    requires
        gv.len() == items.len(),
        evals_to(p, env, xs, Val::List(items)),
        forall|k: int|
            0 <= k < items.len() ==> evals_to(p, #[trigger] env.insert(x, items[k]), g, gv[k]),
    ensures
        xevals_to(
            embed_prog(p),
            env,
            XExpr::Map(Box::new(embed(xs)), x, Box::new(embed(g))),
            Val::List(gv),
        ),
{
    xmap_from_each(p, env, x, g, items, gv, 0);
    let n1 = choose|n: nat| #[trigger] eval(p, n, env, xs) == Res::Done(Val::List(items));
    let n2 = choose|n: nat|
        #[trigger] xmap(embed_prog(p), n, env, x, embed(g), items, 0) == ResSeq::Done(
            gv.subrange(0, gv.len() as int),
        );
    let n = max(n1, n2);
    lift(p, n1, n, env, xs);
    embed_eval(p, n, env, xs);
    xmap_mono(p, n2, n, env, x, g, items, 0);
    assert(gv.subrange(0, gv.len() as int) =~= gv);
    assert(xeval(
        embed_prog(p),
        n + 1,
        env,
        XExpr::Map(Box::new(embed(xs)), x, Box::new(embed(g))),
    ) == Res::Done(Val::List(gv)));
}

/// 写像の意味（核の書換えとの一致）：源の map と核の書換え map_collect は、同じ前提から同じ値 List(gv) に評価される。
pub proof fn map_meaning(
    p: Prog,
    env: Map<nat, Val>,
    xs: Expr,
    t: Ty,
    acc: nat,
    x: nat,
    g: Expr,
    items: Seq<Val>,
    gv: Seq<Val>,
)
    requires
        acc != x,
        absent(acc, g),
        gv.len() == items.len(),
        evals_to(p, env, xs, Val::List(items)),
        forall|k: int|
            0 <= k < items.len() ==> evals_to(p, #[trigger] env.insert(x, items[k]), g, gv[k]),
    ensures
        xevals_to(
            embed_prog(p),
            env,
            XExpr::Map(Box::new(embed(xs)), x, Box::new(embed(g))),
            Val::List(gv),
        ),
        evals_to(p, env, map_collect(xs, t, acc, x, g), Val::List(gv)),
{
    map_source(p, env, xs, x, g, items, gv);
    collect_map(p, env, xs, t, acc, x, g, items, gv);
}

// ------------------------------------------------------------------ 持ち上げと絞り込み

/// 源の式の評価は、燃料を増やしても変わらない（核の lift を写したもの）。
pub proof fn xlift(p: Prog, n: nat, m: nat, env: Map<nat, Val>, e: Expr)
    requires
        n <= m,
        xeval(embed_prog(p), n, env, embed(e)) is Done,
    ensures
        xeval(embed_prog(p), m, env, embed(e)) == xeval(embed_prog(p), n, env, embed(e)),
{
    embed_eval(p, n, env, e);
    lift(p, n, m, env, e);
    embed_eval(p, m, env, e);
}

/// 要素 j 以降で述語が真の要素を、順に並べた列。kept(j) と合わせると全体の kept(n) になる。
pub open spec fn kept_from(items: Seq<Val>, keep: Seq<bool>, j: nat) -> Seq<Val>
    decreases items.len() - j,
{
    if j >= items.len() {
        Seq::empty()
    } else if keep[j as int] {
        seq![items[j as int]] + kept_from(items, keep, j + 1)
    } else {
        kept_from(items, keep, j + 1)
    }
}

/// 先頭 kept(j) と残り kept_from(j) を合わせると、全体の kept(n) になる。
proof fn kept_split(items: Seq<Val>, keep: Seq<bool>, j: nat)
    requires
        keep.len() == items.len(),
        j <= items.len(),
    ensures
        kept(items, keep, j) + kept_from(items, keep, j) == kept(items, keep, items.len() as nat),
    decreases items.len() - j,
{
    reveal_with_fuel(kept, 1);
    reveal_with_fuel(kept_from, 1);
    if j < items.len() {
        kept_split(items, keep, j + 1);
        if keep[j as int] {
            assert(kept(items, keep, j + 1) =~= kept(items, keep, j) + seq![items[j as int]]);
            assert(kept_from(items, keep, j) =~= seq![items[j as int]] + kept_from(items, keep, j + 1));
        } else {
            assert(kept(items, keep, j + 1) =~= kept(items, keep, j));
            assert(kept_from(items, keep, j) =~= kept_from(items, keep, j + 1));
        }
        assert(kept(items, keep, j) + kept_from(items, keep, j) =~= kept(items, keep, j + 1) + kept_from(
            items,
            keep,
            j + 1,
        ));
    } else {
        assert(kept_from(items, keep, j) =~= Seq::<Val>::empty());
    }
}

/// 絞り込みの源の評価の単調性：成功した評価は、燃料を増やしても同じ結果になる。
proof fn xfilter_mono(p: Prog, n: nat, m: nat, env: Map<nat, Val>, x: nat, c: Expr, items: Seq<Val>, j: nat)
    requires
        n <= m,
        xfilter(embed_prog(p), n, env, x, embed(c), items, j) is Done,
    ensures
        xfilter(embed_prog(p), m, env, x, embed(c), items, j) == xfilter(embed_prog(p), n, env, x, embed(c), items, j),
    decreases items.len() - j,
{
    if j < items.len() {
        let env2 = env.insert(x, items[j as int]);
        let f = (n - 1) as nat;
        let fm = (m - 1) as nat;
        assert(n > 0);
        assert(xeval(embed_prog(p), f, env2, embed(c)) is Done);
        assert(xfilter(embed_prog(p), f, env, x, embed(c), items, j + 1) is Done);
        xlift(p, f, fm, env2, c);
        xfilter_mono(p, f, fm, env, x, c, items, j + 1);
    }
}

/// 絞り込みの燃料の存在：要素ごとの述語の値 keep[k] から、源の filter は kept_from(j) を返す。
proof fn xfilter_from_each(p: Prog, env: Map<nat, Val>, x: nat, c: Expr, items: Seq<Val>, keep: Seq<bool>, j: nat)
    requires
        keep.len() == items.len(),
        j <= items.len(),
        forall|k: int|
            0 <= k < items.len() ==> evals_to(p, #[trigger] env.insert(x, items[k]), c, Val::Bool(keep[k])),
    ensures
        exists|n: nat|
            #[trigger] xfilter(embed_prog(p), n, env, x, embed(c), items, j) == ResSeq::Done(
                kept_from(items, keep, j),
            ),
    decreases items.len() - j,
{
    reveal_with_fuel(kept_from, 1);
    if j == items.len() {
        assert(kept_from(items, keep, j) =~= Seq::<Val>::empty());
        assert(xfilter(embed_prog(p), 1, env, x, embed(c), items, j) == ResSeq::Done(Seq::<Val>::empty()));
    } else {
        xfilter_from_each(p, env, x, c, items, keep, j + 1);
        let env2 = env.insert(x, items[j as int]);
        assert(evals_to(p, env2, c, Val::Bool(keep[j as int])));
        let n1 = choose|n: nat| #[trigger] eval(p, n, env2, c) == Res::Done(Val::Bool(keep[j as int]));
        let n2 = choose|n: nat|
            #[trigger] xfilter(embed_prog(p), n, env, x, embed(c), items, j + 1) == ResSeq::Done(
                kept_from(items, keep, j + 1),
            );
        let n = max(n1, n2);
        lift(p, n1, n, env2, c);
        embed_eval(p, n, env2, c);
        xfilter_mono(p, n2, n, env, x, c, items, j + 1);
        if keep[j as int] {
            assert(kept_from(items, keep, j) =~= seq![items[j as int]] + kept_from(items, keep, j + 1));
        } else {
            assert(kept_from(items, keep, j) =~= kept_from(items, keep, j + 1));
        }
        assert(xfilter(embed_prog(p), n + 1, env, x, embed(c), items, j) == ResSeq::Done(
            kept_from(items, keep, j),
        ));
    }
}

/// 絞り込みの源の意味：述語の値が核と同じなら、源の filter は out に評価される（out は kept_from(0)）。
proof fn filter_source(
    p: Prog,
    env: Map<nat, Val>,
    xs: Expr,
    x: nat,
    c: Expr,
    items: Seq<Val>,
    keep: Seq<bool>,
    out: Seq<Val>,
)
    requires
        keep.len() == items.len(),
        out == kept_from(items, keep, 0),
        evals_to(p, env, xs, Val::List(items)),
        forall|k: int|
            0 <= k < items.len() ==> evals_to(p, #[trigger] env.insert(x, items[k]), c, Val::Bool(keep[k])),
    ensures
        xevals_to(embed_prog(p), env, XExpr::Filter(Box::new(embed(xs)), x, Box::new(embed(c))), Val::List(out)),
{
    xfilter_from_each(p, env, x, c, items, keep, 0);
    let n1 = choose|n: nat| #[trigger] eval(p, n, env, xs) == Res::Done(Val::List(items));
    let n2 = choose|n: nat|
        #[trigger] xfilter(embed_prog(p), n, env, x, embed(c), items, 0) == ResSeq::Done(kept_from(items, keep, 0));
    let n = max(n1, n2);
    lift(p, n1, n, env, xs);
    embed_eval(p, n, env, xs);
    xfilter_mono(p, n2, n, env, x, c, items, 0);
    assert(xeval(embed_prog(p), n + 1, env, XExpr::Filter(Box::new(embed(xs)), x, Box::new(embed(c)))) == Res::Done(
        Val::List(out),
    ));
}

/// 絞り込みの意味（核の書換えとの一致）：源の filter と filter_collect は、同じ前提から同じ列に評価される。
pub proof fn filter_meaning_x(
    p: Prog,
    env: Map<nat, Val>,
    xs: Expr,
    t: Ty,
    acc: nat,
    x: nat,
    c: Expr,
    items: Seq<Val>,
    keep: Seq<bool>,
)
    requires
        acc != x,
        absent(acc, c),
        keep.len() == items.len(),
        evals_to(p, env, xs, Val::List(items)),
        forall|k: int|
            0 <= k < items.len() ==> evals_to(p, #[trigger] env.insert(x, items[k]), c, Val::Bool(keep[k])),
    ensures
        xevals_to(
            embed_prog(p),
            env,
            XExpr::Filter(Box::new(embed(xs)), x, Box::new(embed(c))),
            Val::List(kept(items, keep, items.len() as nat)),
        ),
        evals_to(p, env, filter_collect(xs, t, acc, x, c), Val::List(kept(items, keep, items.len() as nat))),
{
    reveal_with_fuel(kept, 1);
    kept_split(items, keep, 0);
    assert(kept(items, keep, 0) =~= Seq::<Val>::empty());
    assert(kept_from(items, keep, 0) =~= kept(items, keep, items.len() as nat));
    filter_source(p, env, xs, x, c, items, keep, kept(items, keep, items.len() as nat));
    filter_meaning(p, env, xs, t, acc, x, c, items, keep);
}

} // verus!
