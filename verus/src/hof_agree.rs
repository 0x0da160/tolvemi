//! HofTypes の写し（hof_types.rs）と検証済みの型付け規則との一致：hof の六つの形（SH1）。
//!
//! - 源の型付け `ty_x`（xtyping.rs）との一致：項目は `ty_x` が束縛に与える型（列の要素の型）と、その下での
//!   本体の型で、checker が形に返す型は `ty_x` の型と同じ（`hof_agrees`）。
//! - 書換えの型との一致：項目の型を注釈に入れた書換え（fold_meaning.rs・sortmeaning.rs の形）は、核の型付け
//!   `ty_expr` で形の型の消去（`derase`）を持つ（`hof_rw_agrees`）。
//!
//! loop と辞書の操作の形は `ty_x` にないので、一致はそれぞれの書換えの核の型で示す（loop_types.rs、dict_types.rs）。

use crate::fold_meaning::*;
use crate::hof_types::*;
use crate::input::*;
use crate::records_proof::*;
use crate::sortmeaning::*;
use crate::spec::*;
use crate::xsem::*;
use crate::xtyping::*;
use vstd::prelude::*;

verus! {

// ------------------------------------------------------------------ 一致（hof の六つの形と ty_x）

/// 源の hof の形（xsem.rs の XExpr）。
pub open spec fn x_hof(op: HofOp, xs: XExpr, x: nat, c: XExpr) -> XExpr {
    match op {
        HofOp::Map => XExpr::Map(Box::new(xs), x, Box::new(c)),
        HofOp::Filter => XExpr::Filter(Box::new(xs), x, Box::new(c)),
        HofOp::Any => XExpr::Any(Box::new(xs), x, Box::new(c)),
        HofOp::All => XExpr::All(Box::new(xs), x, Box::new(c)),
        HofOp::Find => XExpr::Find(Box::new(xs), x, Box::new(c)),
        HofOp::SortBy => XExpr::SortBy(Box::new(xs), x, Box::new(c)),
    }
}

/// 源の hof の形の被演算子の型を、検証済みの源の型付け `ty_x` で求めたもの：列の型と、束縛 x に `binder_ty` を
/// 与えた本体の型。列の型が List でないとき checker は束縛に ErrorType を与えるが、そのとき本体の型によらず
/// 項目はなく形の型も ErrorType なので（`hof_list_bad`）、本体の型を None と置く。
pub open spec fn x_operands(
    xp: XProg,
    r: nat,
    ctx: Map<nat, Ty>,
    op: HofOp,
    xs: XExpr,
    x: nat,
    c: XExpr,
) -> Seq<Option<Ty>> {
    let t0 = ty_x(xp, r, ctx, xs);
    match binder_ty(Form::Hof(op), t0) {
        Some(a) => seq![t0, ty_x(xp, r, ctx.insert(x, a), c)],
        None => seq![t0, None],
    }
}

/// 列の型が List でなければ、本体の型によらず、形の型は ErrorType で、表に項目はない。
pub proof fn hof_list_bad(op: HofOp, t0: Option<Ty>, bt: Option<Ty>)
    requires
        binder_ty(Form::Hof(op), t0) is None,
    ensures
        form_ty(Form::Hof(op), seq![t0, bt]) is None,
        hof_entry(Form::Hof(op), seq![t0, bt]) is None,
{
    let ts = seq![t0, bt];
    assert(ts[0] == t0 && ts[1] == bt);
}

/// 一致（hof の六つの形）：checker が形に返す型は `ty_x` の型と同じ。項目があるのは `ty_x` が形に型を付ける
/// ときだけで、項目は `ty_x` が束縛 x に与える型（列の要素の型）と、その下での本体の型。
pub proof fn hof_agrees(xp: XProg, r: nat, ctx: Map<nat, Ty>, op: HofOp, xs: XExpr, x: nat, c: XExpr)
    ensures
        form_ty(Form::Hof(op), x_operands(xp, r, ctx, op, xs, x, c)) == ty_x(xp, r, ctx, x_hof(op, xs, x, c)),
        hof_entry(Form::Hof(op), x_operands(xp, r, ctx, op, xs, x, c)) is Some <==> ty_x(
            xp,
            r,
            ctx,
            x_hof(op, xs, x, c),
        ) is Some,
        ty_x(xp, r, ctx, x_hof(op, xs, x, c)) is Some ==> {
            &&& ty_x(xp, r, ctx, xs) is Some
            &&& ty_x(xp, r, ctx, xs)->Some_0 is List
            &&& ty_x(xp, r, ctx.insert(x, *ty_x(xp, r, ctx, xs)->Some_0->List_0), c) is Some
            &&& hof_entry(Form::Hof(op), x_operands(xp, r, ctx, op, xs, x, c)) == Some(
                (
                    *ty_x(xp, r, ctx, xs)->Some_0->List_0,
                    ty_x(xp, r, ctx.insert(x, *ty_x(xp, r, ctx, xs)->Some_0->List_0), c)->Some_0,
                ),
            )
        },
{
    let t0 = ty_x(xp, r, ctx, xs);
    let ts = x_operands(xp, r, ctx, op, xs, x, c);
    match t0 {
        Some(Ty::List(a)) => {
            let bt = ty_x(xp, r, ctx.insert(x, *a), c);
            assert(ts == seq![t0, bt]);
            assert(ts[0] == t0 && ts[1] == bt);
            match op {
                HofOp::Map => assert(ty_x(xp, r, ctx, XExpr::Map(Box::new(xs), x, Box::new(c))) == match bt {
                    Some(tc) => Some(Ty::List(Box::new(tc))),
                    None => None,
                }),
                HofOp::Filter => assert(ty_x(xp, r, ctx, XExpr::Filter(Box::new(xs), x, Box::new(c))) == if bt == Some(
                    Ty::Bool,
                ) {
                    t0
                } else {
                    None
                }),
                HofOp::Any => assert(ty_x(xp, r, ctx, XExpr::Any(Box::new(xs), x, Box::new(c))) == if bt == Some(
                    Ty::Bool,
                ) {
                    Some(Ty::Bool)
                } else {
                    None
                }),
                HofOp::All => assert(ty_x(xp, r, ctx, XExpr::All(Box::new(xs), x, Box::new(c))) == if bt == Some(
                    Ty::Bool,
                ) {
                    Some(Ty::Bool)
                } else {
                    None
                }),
                HofOp::Find => assert(ty_x(xp, r, ctx, XExpr::Find(Box::new(xs), x, Box::new(c))) == if bt == Some(
                    Ty::Bool,
                ) {
                    Some(Ty::Option(a))
                } else {
                    None
                }),
                HofOp::SortBy => assert(ty_x(xp, r, ctx, XExpr::SortBy(Box::new(xs), x, Box::new(c))) == if bt
                    == Some(Ty::Int) {
                    t0
                } else {
                    None
                }),
            }
        },
        _ => {
            assert(ts == seq![t0, None::<Ty>]);
            hof_list_bad(op, t0, None);
            match op {
                HofOp::Map => assert(ty_x(xp, r, ctx, XExpr::Map(Box::new(xs), x, Box::new(c))) is None),
                HofOp::Filter => assert(ty_x(xp, r, ctx, XExpr::Filter(Box::new(xs), x, Box::new(c))) is None),
                HofOp::Any => assert(ty_x(xp, r, ctx, XExpr::Any(Box::new(xs), x, Box::new(c))) is None),
                HofOp::All => assert(ty_x(xp, r, ctx, XExpr::All(Box::new(xs), x, Box::new(c))) is None),
                HofOp::Find => assert(ty_x(xp, r, ctx, XExpr::Find(Box::new(xs), x, Box::new(c))) is None),
                HofOp::SortBy => assert(ty_x(xp, r, ctx, XExpr::SortBy(Box::new(xs), x, Box::new(c))) is None),
            }
        },
    }
}

// ------------------------------------------------------------------ 一致（hof の書換えと ty_expr）

/// 書換えが注釈に入れる項目の型（hof.rs の `Lower::expr`）：map は本体の型 b（`list<B>()`）、filter・find・sort_by は
/// 要素の型 a（`list<A>()`、`none<A>()`）。any・all は注釈を使わない（a を返しておく）。
pub open spec fn hof_note(op: HofOp, a: Ty, b: Ty) -> Ty {
    match op {
        HofOp::Map => b,
        _ => a,
    }
}

/// 書換えが導入する名前の数（hof.rs の `fresh` の呼出しの数）。
pub open spec fn hof_names(op: HofOp) -> nat {
    match op {
        HofOp::Find => 2,
        HofOp::SortBy => 7,
        _ => 1,
    }
}

/// hof の形の核の書換え（hof.rs の `Lower::expr`。形は fold_meaning.rs と sortmeaning.rs）。t は注釈の型、ns は
/// 導入する名前（`fresh` の順：acc、find の y、sort_by の e・st・y・ky・ke・r）。
pub open spec fn hof_rw(op: HofOp, xs: Expr, x: nat, c: Expr, t: Ty, ns: Seq<nat>) -> Expr {
    match op {
        HofOp::Map => map_collect(xs, t, ns[0], x, c),
        HofOp::Filter => filter_collect(xs, t, ns[0], x, c),
        HofOp::Any => any_fold(xs, ns[0], x, c),
        HofOp::All => all_fold(xs, ns[0], x, c),
        HofOp::Find => find_fold(xs, t, ns[0], x, c, ns[1]),
        HofOp::SortBy => sort_collect(xs, t, ns[0], ns[1], ns[2], ns[3], ns[4], ns[5], ns[6], x, c),
    }
}

/// 導入する名前は互いに異なり、束縛 x と異なり、本体 c に現れない（hof.rs の `fresh` はプログラムのどの名前とも
/// 重ならない名前を返す）。
pub open spec fn fresh_names(ns: Seq<nat>, x: nat, c: Expr) -> bool {
    &&& forall|i: int, j: int| 0 <= i < j < ns.len() ==> ns[i] != ns[j]
    &&& forall|i: int| 0 <= i < ns.len() ==> ns[i] != x && absent(ns[i], c)
}

/// 消去は List・Option・Pair・Result の上で成分ごと。Dict<K, V> は List<Pair<K, V>> に、Int・Bool はそのまま。
pub proof fn derase_parts(a: Ty, b: Ty)
    ensures
        derase(Ty::List(Box::new(a))) == Ty::List(Box::new(derase(a))),
        derase(Ty::Option(Box::new(a))) == Ty::Option(Box::new(derase(a))),
        derase(Ty::Pair(Box::new(a), Box::new(b))) == Ty::Pair(Box::new(derase(a)), Box::new(derase(b))),
        derase(Ty::Result(Box::new(a), Box::new(b))) == Ty::Result(Box::new(derase(a)), Box::new(derase(b))),
        derase(Ty::Dict(Box::new(a), Box::new(b))) == Ty::List(
            Box::new(Ty::Pair(Box::new(derase(a)), Box::new(derase(b)))),
        ),
        derase(Ty::Int) == Ty::Int,
        derase(Ty::Bool) == Ty::Bool,
{
    reveal_with_fuel(derase, 2);
}

/// 一致（hof の書換え）：被演算子の核の型が checker の型の消去なら（列は消去した列の型、本体は束縛 x を項目の
/// 要素の型の消去にした下で本体の型の消去）、項目の型を注釈に入れた書換えは、核の型付け `ty_expr` で形の型の
/// 消去を持つ。
pub proof fn hof_rw_agrees(
    p: Prog,
    r: nat,
    ctx: Map<nat, Ty>,
    op: HofOp,
    xs: Expr,
    x: nat,
    c: Expr,
    ns: Seq<nat>,
    ts: Seq<Option<Ty>>,
)
    requires
        hof_entry(Form::Hof(op), ts) is Some,
        ns.len() == hof_names(op),
        fresh_names(ns, x, c),
        ty_expr(p, r, ctx, xs) == Some(derase(ts[0]->Some_0)),
        ty_expr(p, r, ctx.insert(x, derase(hof_entry(Form::Hof(op), ts)->Some_0.0)), c) == Some(
            derase(ts[1]->Some_0),
        ),
    ensures
        ty_expr(
            p,
            r,
            ctx,
            hof_rw(
                op,
                xs,
                x,
                c,
                derase(hof_note(op, hof_entry(Form::Hof(op), ts)->Some_0.0, hof_entry(Form::Hof(op), ts)->Some_0.1)),
                ns,
            ),
        ) == Some(derase(form_ty(Form::Hof(op), ts)->Some_0)),
{
    let a = hof_entry(Form::Hof(op), ts)->Some_0.0;
    let bt = hof_entry(Form::Hof(op), ts)->Some_0.1;
    assert(ts[0] == Some(Ty::List(Box::new(a))));
    assert(ts[1] == Some(bt));
    derase_parts(a, bt);
    let s = derase(a);
    let acc = ns[0];
    assert(acc != x && absent(acc, c));
    match op {
        HofOp::Map => {
            map_typing(p, r, ctx, xs, s, derase(bt), acc, x, c);
        },
        HofOp::Filter => {
            filter_typing(p, r, ctx, xs, s, acc, x, c);
        },
        HofOp::Any => {
            any_typing(p, r, ctx, xs, s, acc, x, c);
        },
        HofOp::All => {
            all_typing(p, r, ctx, xs, s, acc, x, c);
        },
        HofOp::Find => {
            find_typing(p, r, ctx, xs, s, acc, x, ns[1], c);
        },
        HofOp::SortBy => {
            assert(ns[0] != ns[1] && ns[0] != ns[2] && ns[0] != ns[3] && ns[0] != ns[4] && ns[0] != ns[5]);
            assert(ns[1] != ns[2] && ns[1] != ns[3] && ns[1] != ns[4] && ns[1] != ns[5] && ns[1] != ns[6]);
            assert(ns[2] != ns[3] && ns[2] != ns[4] && ns[2] != ns[5]);
            assert(ns[3] != ns[4] && ns[3] != ns[5] && ns[4] != ns[5]);
            assert(ns[1] != x && ns[2] != x && ns[3] != x);
            assert(absent(ns[1], c) && absent(ns[2], c) && absent(ns[3], c));
            sort_typing(p, r, ctx, xs, s, ns[0], ns[1], ns[2], ns[3], ns[4], ns[5], ns[6], x, c);
        },
    }
}

} // verus!
