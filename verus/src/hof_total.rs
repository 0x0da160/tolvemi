//! HofTypes の写し（hof_types.rs）の全域性（SH1）：書換えが表を引く形に、項目が無いことはない。
//!
//! - 形ごと：checker が形に型を返すなら表に項目があり、項目があるのは型を返すときだけ（`hof_entry_total`）。
//!   hof の六つの形、loop、辞書の九つの操作のどれでも。
//! - 式ごと：`ty_x` で型の付く源の式の中の、どの hof の形にも項目がある（`entries_total`）。書換え（hof.rs の
//!   `Lower::expr`）が表を引いて項目が無く、形をそのまま残すことはない。
//!
//! loop と辞書の操作は源の型付け `ty_x` にないので、式ごとの全域性は crates/tlvm/tests/hof_types.rs で確かめる
//! （試験であって証明ではない）。

use crate::hof_agree::*;
use crate::hof_types::*;
use crate::spec::*;
use crate::xsem::*;
use crate::xtyping::*;
use vstd::prelude::*;

verus! {

// ------------------------------------------------------------------ 全域性（形ごと）

/// 全域性（形ごと）：checker が形に型を返すなら表に項目がある。項目があるのは型を返すときだけ。
/// 項目があれば被演算子の型はどれも ErrorType でない。
pub proof fn hof_entry_total(f: Form, ts: Seq<Option<Ty>>)
    ensures
        form_ty(f, ts) is Some <==> hof_entry(f, ts) is Some,
        hof_entry(f, ts) is Some ==> ts.len() == operands(f) && forall|i: int| 0 <= i < ts.len() ==> #[trigger] ts[i] is Some,
{
    if ts.len() == operands(f) {
        match f {
            Form::Hof(op) => {},
            Form::Loop => {},
            Form::Dict(op) => {
                if hof_entry(f, ts) is Some {
                    assert forall|i: int| 0 <= i < ts.len() implies #[trigger] ts[i] is Some by {
                        if op is From {
                        } else {
                            assert(i == 0 || i == 1 || i == 2);
                        }
                    }
                }
            },
        }
    }
}

// ------------------------------------------------------------------ 全域性（式ごと）

/// 源の式 e の中の hof の形すべてに、表の項目がある（それぞれの形の文脈と、`ty_x` による被演算子の型で）。
/// 束縛の下の部分式は、束縛の型が決まるときだけ見る（決まらなければ e に型は付かない）。
pub open spec fn entries_in(xp: XProg, r: nat, ctx: Map<nat, Ty>, e: XExpr) -> bool
    decreases e, 0nat,
{
    match e {
        XExpr::List(_, es) => entries_args(xp, r, ctx, es, 0),
        XExpr::Some(a) => entries_in(xp, r, ctx, *a),
        XExpr::Pair(a, b) => entries_in(xp, r, ctx, *a) && entries_in(xp, r, ctx, *b),
        XExpr::Builtin(_, es) => entries_args(xp, r, ctx, es, 0),
        XExpr::Call(_, es) => entries_args(xp, r, ctx, es, 0),
        XExpr::Let(x, a, b) => entries_in(xp, r, ctx, *a) && match ty_x(xp, r, ctx, *a) {
            Some(ta) => entries_in(xp, r, ctx.insert(x, ta), *b),
            None => true,
        },
        XExpr::If(c, a, b) => entries_in(xp, r, ctx, *c) && entries_in(xp, r, ctx, *a) && entries_in(xp, r, ctx, *b),
        XExpr::Fold(xs, init, acc, item, body) => entries_in(xp, r, ctx, *xs) && entries_in(xp, r, ctx, *init)
            && match (ty_x(xp, r, ctx, *xs), ty_x(xp, r, ctx, *init)) {
            (Some(Ty::List(s)), Some(ta)) => entries_in(xp, r, ctx.insert(acc, ta).insert(item, *s), *body),
            _ => true,
        },
        XExpr::Match(m, n, x, sm) => entries_in(xp, r, ctx, *m) && entries_in(xp, r, ctx, *n) && match ty_x(
            xp,
            r,
            ctx,
            *m,
        ) {
            Some(Ty::Option(t)) => entries_in(xp, r, ctx.insert(x, *t), *sm),
            _ => true,
        },
        XExpr::Inj(_, _, _, a) => entries_in(xp, r, ctx, *a),
        XExpr::MatchR(m, x, a, y, b) => entries_in(xp, r, ctx, *m) && match ty_x(xp, r, ctx, *m) {
            Some(Ty::Result(t, u)) => entries_in(xp, r, ctx.insert(x, *t), *a) && entries_in(
                xp,
                r,
                ctx.insert(y, *u),
                *b,
            ),
            _ => true,
        },
        XExpr::Map(xs, x, c) => hof_entry(Form::Hof(HofOp::Map), x_operands(xp, r, ctx, HofOp::Map, *xs, x, *c)) is Some
            && entries_in(xp, r, ctx, *xs) && match ty_x(xp, r, ctx, *xs) {
            Some(Ty::List(a)) => entries_in(xp, r, ctx.insert(x, *a), *c),
            _ => true,
        },
        XExpr::Filter(xs, x, c) => hof_entry(
            Form::Hof(HofOp::Filter),
            x_operands(xp, r, ctx, HofOp::Filter, *xs, x, *c),
        ) is Some && entries_in(xp, r, ctx, *xs) && match ty_x(xp, r, ctx, *xs) {
            Some(Ty::List(a)) => entries_in(xp, r, ctx.insert(x, *a), *c),
            _ => true,
        },
        XExpr::Any(xs, x, c) => hof_entry(Form::Hof(HofOp::Any), x_operands(xp, r, ctx, HofOp::Any, *xs, x, *c)) is Some
            && entries_in(xp, r, ctx, *xs) && match ty_x(xp, r, ctx, *xs) {
            Some(Ty::List(a)) => entries_in(xp, r, ctx.insert(x, *a), *c),
            _ => true,
        },
        XExpr::All(xs, x, c) => hof_entry(Form::Hof(HofOp::All), x_operands(xp, r, ctx, HofOp::All, *xs, x, *c)) is Some
            && entries_in(xp, r, ctx, *xs) && match ty_x(xp, r, ctx, *xs) {
            Some(Ty::List(a)) => entries_in(xp, r, ctx.insert(x, *a), *c),
            _ => true,
        },
        XExpr::Find(xs, x, c) => hof_entry(Form::Hof(HofOp::Find), x_operands(xp, r, ctx, HofOp::Find, *xs, x, *c)) is Some
            && entries_in(xp, r, ctx, *xs) && match ty_x(xp, r, ctx, *xs) {
            Some(Ty::List(a)) => entries_in(xp, r, ctx.insert(x, *a), *c),
            _ => true,
        },
        XExpr::SortBy(xs, x, c) => hof_entry(
            Form::Hof(HofOp::SortBy),
            x_operands(xp, r, ctx, HofOp::SortBy, *xs, x, *c),
        ) is Some && entries_in(xp, r, ctx, *xs) && match ty_x(xp, r, ctx, *xs) {
            Some(Ty::List(a)) => entries_in(xp, r, ctx.insert(x, *a), *c),
            _ => true,
        },
        _ => true,
    }
}

/// es[i..] の中の hof の形すべてに、表の項目がある。
pub open spec fn entries_args(xp: XProg, r: nat, ctx: Map<nat, Ty>, es: Seq<XExpr>, i: nat) -> bool
    decreases es, es.len() - i,
{
    if i >= es.len() {
        true
    } else {
        entries_in(xp, r, ctx, es[i as int]) && entries_args(xp, r, ctx, es, i + 1)
    }
}

/// hof の形の一段：形に型が付けば、項目があり、列と本体（要素の型の下で）に型が付く。
proof fn hof_step(xp: XProg, r: nat, ctx: Map<nat, Ty>, op: HofOp, xs: XExpr, x: nat, c: XExpr)
    requires
        ty_x(xp, r, ctx, x_hof(op, xs, x, c)) is Some,
    ensures
        hof_entry(Form::Hof(op), x_operands(xp, r, ctx, op, xs, x, c)) is Some,
        ty_x(xp, r, ctx, xs) is Some,
        ty_x(xp, r, ctx, xs)->Some_0 is List,
        ty_x(xp, r, ctx.insert(x, *ty_x(xp, r, ctx, xs)->Some_0->List_0), c) is Some,
{
    hof_agrees(xp, r, ctx, op, xs, x, c);
}

/// 全域性（式ごと）：`ty_x` で型の付く源の式の中の、どの hof の形にも表の項目がある。書換え（hof.rs の
/// `Lower::expr`）が表を引いて項目が無く、形をそのまま残すことはない。
pub proof fn entries_total(xp: XProg, r: nat, ctx: Map<nat, Ty>, e: XExpr)
    requires
        ty_x(xp, r, ctx, e) is Some,
    ensures
        entries_in(xp, r, ctx, e),
    decreases e, 0nat,
{
    match e {
        XExpr::List(_, es) => entries_args_total(xp, r, ctx, es, 0),
        XExpr::Some(a) => entries_total(xp, r, ctx, *a),
        XExpr::Pair(a, b) => {
            entries_total(xp, r, ctx, *a);
            entries_total(xp, r, ctx, *b);
        },
        XExpr::Builtin(_, es) => entries_args_total(xp, r, ctx, es, 0),
        XExpr::Call(_, es) => entries_args_total(xp, r, ctx, es, 0),
        XExpr::Let(x, a, b) => {
            entries_total(xp, r, ctx, *a);
            entries_total(xp, r, ctx.insert(x, ty_x(xp, r, ctx, *a)->Some_0), *b);
        },
        XExpr::If(c, a, b) => {
            entries_total(xp, r, ctx, *c);
            entries_total(xp, r, ctx, *a);
            entries_total(xp, r, ctx, *b);
        },
        XExpr::Fold(xs, init, acc, item, body) => {
            entries_total(xp, r, ctx, *xs);
            entries_total(xp, r, ctx, *init);
            let tx = ty_x(xp, r, ctx, *xs)->Some_0;
            let ta = ty_x(xp, r, ctx, *init)->Some_0;
            entries_total(xp, r, ctx.insert(acc, ta).insert(item, *tx->List_0), *body);
        },
        XExpr::Match(m, n, x, sm) => {
            entries_total(xp, r, ctx, *m);
            entries_total(xp, r, ctx, *n);
            let tm = ty_x(xp, r, ctx, *m)->Some_0;
            entries_total(xp, r, ctx.insert(x, *tm->Option_0), *sm);
        },
        XExpr::Inj(_, _, _, a) => entries_total(xp, r, ctx, *a),
        XExpr::MatchR(m, x, a, y, b) => {
            entries_total(xp, r, ctx, *m);
            let tm = ty_x(xp, r, ctx, *m)->Some_0;
            entries_total(xp, r, ctx.insert(x, *tm->Result_0), *a);
            entries_total(xp, r, ctx.insert(y, *tm->Result_1), *b);
        },
        XExpr::Map(xs, x, c) => {
            assert(x_hof(HofOp::Map, *xs, x, *c) == e);
            hof_step(xp, r, ctx, HofOp::Map, *xs, x, *c);
            entries_total(xp, r, ctx, *xs);
            entries_total(xp, r, ctx.insert(x, *ty_x(xp, r, ctx, *xs)->Some_0->List_0), *c);
        },
        XExpr::Filter(xs, x, c) => {
            assert(x_hof(HofOp::Filter, *xs, x, *c) == e);
            hof_step(xp, r, ctx, HofOp::Filter, *xs, x, *c);
            entries_total(xp, r, ctx, *xs);
            entries_total(xp, r, ctx.insert(x, *ty_x(xp, r, ctx, *xs)->Some_0->List_0), *c);
        },
        XExpr::Any(xs, x, c) => {
            assert(x_hof(HofOp::Any, *xs, x, *c) == e);
            hof_step(xp, r, ctx, HofOp::Any, *xs, x, *c);
            entries_total(xp, r, ctx, *xs);
            entries_total(xp, r, ctx.insert(x, *ty_x(xp, r, ctx, *xs)->Some_0->List_0), *c);
        },
        XExpr::All(xs, x, c) => {
            assert(x_hof(HofOp::All, *xs, x, *c) == e);
            hof_step(xp, r, ctx, HofOp::All, *xs, x, *c);
            entries_total(xp, r, ctx, *xs);
            entries_total(xp, r, ctx.insert(x, *ty_x(xp, r, ctx, *xs)->Some_0->List_0), *c);
        },
        XExpr::Find(xs, x, c) => {
            assert(x_hof(HofOp::Find, *xs, x, *c) == e);
            hof_step(xp, r, ctx, HofOp::Find, *xs, x, *c);
            entries_total(xp, r, ctx, *xs);
            entries_total(xp, r, ctx.insert(x, *ty_x(xp, r, ctx, *xs)->Some_0->List_0), *c);
        },
        XExpr::SortBy(xs, x, c) => {
            assert(x_hof(HofOp::SortBy, *xs, x, *c) == e);
            hof_step(xp, r, ctx, HofOp::SortBy, *xs, x, *c);
            entries_total(xp, r, ctx, *xs);
            entries_total(xp, r, ctx.insert(x, *ty_x(xp, r, ctx, *xs)->Some_0->List_0), *c);
        },
        _ => {},
    }
}

/// 引数の列の全域性：es[i..] に型が付けば、その中のどの hof の形にも項目がある。
pub proof fn entries_args_total(xp: XProg, r: nat, ctx: Map<nat, Ty>, es: Seq<XExpr>, i: nat)
    requires
        ty_args_x(xp, r, ctx, es, i) is Some,
    ensures
        entries_args(xp, r, ctx, es, i),
    decreases es, es.len() - i,
{
    if i < es.len() {
        entries_total(xp, r, ctx, es[i as int]);
        entries_args_total(xp, r, ctx, es, i + 1);
    }
}

} // verus!
