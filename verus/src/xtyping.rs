//! 源の型（段階 1b・SH1 の第二部）。
//!
//! 源の型付け `ty_x` は、核の型付け `ty_expr`（spec.rs）と同じ規則に、hof の形の規則を加えたもの。
//! 核の式の源の写しは、核と同じ型になる（`ty_embed`）。hof の形の核の書換えは、
//! 源の形と同じ型になる（`map_typing` など）。書換えの型が源の型と一致するので、型安全性は核の側にそのまま及ぶ。

use crate::bigstep::*;
use crate::fold_meaning::*;
use crate::proof::*;
use crate::records_proof::*;
use crate::spec::*;
use crate::xmeaning::*;
use crate::xsem::*;
use vstd::prelude::*;

verus! {

/// 源の式の型。核の ty_expr と同じ規則に、hof の形（map・filter・any・all・find）を加える。
pub open spec fn ty_x(xp: XProg, r: nat, ctx: Map<nat, Ty>, e: XExpr) -> Option<Ty>
    decreases e, 0nat,
{
    match e {
        XExpr::Int(_) => Some(Ty::Int),
        XExpr::Bool(_) => Some(Ty::Bool),
        XExpr::Unit => Some(Ty::Unit),
        XExpr::Char(c) => if scalar(c) { Some(Ty::Char) } else { None },
        XExpr::Var(x) => if ctx.contains_key(x) { Some(ctx[x]) } else { None },
        XExpr::List(t, es) => match ty_args_x(xp, r, ctx, es, 0) {
            Some(ts) => if forall|k: int| 0 <= k < ts.len() ==> #[trigger] ts[k] == t {
                Some(Ty::List(Box::new(t)))
            } else {
                None
            },
            None => None,
        },
        XExpr::Some(x) => match ty_x(xp, r, ctx, *x) {
            Some(t) => Some(Ty::Option(Box::new(t))),
            None => None,
        },
        XExpr::None(t) => Some(Ty::Option(Box::new(t))),
        XExpr::Pair(a, b) => match (ty_x(xp, r, ctx, *a), ty_x(xp, r, ctx, *b)) {
            (Some(ta), Some(tb)) => Some(Ty::Pair(Box::new(ta), Box::new(tb))),
            _ => None,
        },
        XExpr::Builtin(b, es) => match ty_args_x(xp, r, ctx, es, 0) {
            Some(ts) => builtin_type(b, ts),
            None => None,
        },
        XExpr::Call(g, es) => match ty_args_x(xp, r, ctx, es, 0) {
            Some(ts) => if g < xp.funcs.len() && g < xp.rank.len() && (xp.rank[g as int] < r || (g < xp.rec.len()
                && xp.rec[g as int])) && ts.len() == xp.funcs[g as int].params.len() && forall|k: int|
                0 <= k < ts.len() ==> #[trigger] ts[k] == xp.funcs[g as int].params[k].1 {
                Some(xp.funcs[g as int].ret)
            } else {
                None
            },
            None => None,
        },
        XExpr::Let(x, a, b) => match ty_x(xp, r, ctx, *a) {
            Some(ta) => ty_x(xp, r, ctx.insert(x, ta), *b),
            None => None,
        },
        XExpr::If(c, a, b) => match (ty_x(xp, r, ctx, *c), ty_x(xp, r, ctx, *a), ty_x(xp, r, ctx, *b)) {
            (Some(tc), Some(ta), Some(tb)) => if tc == Ty::Bool && ta == tb { Some(ta) } else { None },
            _ => None,
        },
        XExpr::Fold(xs, init, acc, item, body) => match (ty_x(xp, r, ctx, *xs), ty_x(xp, r, ctx, *init)) {
            (Some(tx), Some(ta)) => if tx is List && ty_x(xp, r, ctx.insert(acc, ta).insert(item, *tx->List_0), *body)
                == Some(ta) {
                Some(ta)
            } else {
                None
            },
            _ => None,
        },
        XExpr::Match(m, n, x, sm) => match (ty_x(xp, r, ctx, *m), ty_x(xp, r, ctx, *n)) {
            (Some(tm), Some(tn)) => if tm is Option && ty_x(xp, r, ctx.insert(x, *tm->Option_0), *sm) == Some(tn) {
                Some(tn)
            } else {
                None
            },
            _ => None,
        },
        XExpr::Inj(ok, t, u, x) => match ty_x(xp, r, ctx, *x) {
            Some(tx) => if tx == (if ok { t } else { u }) {
                Some(Ty::Result(Box::new(t), Box::new(u)))
            } else {
                None
            },
            None => None,
        },
        XExpr::MatchR(m, x, a, y, b) => match ty_x(xp, r, ctx, *m) {
            Some(tm) => if tm is Result {
                match ty_x(xp, r, ctx.insert(x, *tm->Result_0), *a) {
                    Some(ta) => if ty_x(xp, r, ctx.insert(y, *tm->Result_1), *b) == Some(ta) {
                        Some(ta)
                    } else {
                        None
                    },
                    None => None,
                }
            } else {
                None
            },
            None => None,
        },
        // hof：map(xs, |x| body) の型は List(body の型)。
        XExpr::Map(xs, x, c) => match ty_x(xp, r, ctx, *xs) {
            Some(tx) => if tx is List {
                match ty_x(xp, r, ctx.insert(x, *tx->List_0), *c) {
                    Some(tc) => Some(Ty::List(Box::new(tc))),
                    None => None,
                }
            } else {
                None
            },
            None => None,
        },
        // hof：filter(xs, |x| c) の型は xs の型。c は Bool。
        XExpr::Filter(xs, x, c) => match ty_x(xp, r, ctx, *xs) {
            Some(tx) => if tx is List && ty_x(xp, r, ctx.insert(x, *tx->List_0), *c) == Some(Ty::Bool) {
                Some(tx)
            } else {
                None
            },
            None => None,
        },
        // hof：any・all は Bool。
        XExpr::Any(xs, x, c) => match ty_x(xp, r, ctx, *xs) {
            Some(tx) => if tx is List && ty_x(xp, r, ctx.insert(x, *tx->List_0), *c) == Some(Ty::Bool) {
                Some(Ty::Bool)
            } else {
                None
            },
            None => None,
        },
        XExpr::All(xs, x, c) => match ty_x(xp, r, ctx, *xs) {
            Some(tx) => if tx is List && ty_x(xp, r, ctx.insert(x, *tx->List_0), *c) == Some(Ty::Bool) {
                Some(Ty::Bool)
            } else {
                None
            },
            None => None,
        },
        // hof：find は Option(要素の型)。
        XExpr::Find(xs, x, c) => match ty_x(xp, r, ctx, *xs) {
            Some(tx) => if tx is List && ty_x(xp, r, ctx.insert(x, *tx->List_0), *c) == Some(Ty::Bool) {
                Some(Ty::Option(Box::new(*tx->List_0)))
            } else {
                None
            },
            None => None,
        },
        XExpr::SortBy(xs, x, k) => match ty_x(xp, r, ctx, *xs) {
            Some(tx) => if tx is List && ty_x(xp, r, ctx.insert(x, *tx->List_0), *k) == Some(Ty::Int) {
                Some(tx)
            } else {
                None
            },
            None => None,
        },
    }
}

/// es[i..] の源の型列。
pub open spec fn ty_args_x(xp: XProg, r: nat, ctx: Map<nat, Ty>, es: Seq<XExpr>, i: nat) -> Option<Seq<Ty>>
    decreases es, es.len() - i,
{
    if i >= es.len() {
        Some(Seq::empty())
    } else {
        match (ty_x(xp, r, ctx, es[i as int]), ty_args_x(xp, r, ctx, es, i + 1)) {
            (Some(t), Some(ts)) => Some(seq![t] + ts),
            _ => None,
        }
    }
}

// ------------------------------------------------------------------ 核の式の写しの型

/// 核の式の源の写しは、核と同じ型になる（保存性の型版）。
pub proof fn ty_embed(p: Prog, r: nat, ctx: Map<nat, Ty>, e: Expr)
    ensures
        ty_x(embed_prog(p), r, ctx, embed(e)) == ty_expr(p, r, ctx, e),
    decreases e, 0nat,
{
    match e {
        Expr::Int(_) => {},
        Expr::Bool(_) => {},
        Expr::Unit => {},
        Expr::Char(_) => {},
        Expr::Var(_) => {},
        Expr::None(_) => {},
        Expr::List(_, es) => ty_args_embed(p, r, ctx, es, 0),
        Expr::Some(a) => ty_embed(p, r, ctx, *a),
        Expr::Pair(a, b) => {
            ty_embed(p, r, ctx, *a);
            ty_embed(p, r, ctx, *b);
        },
        Expr::Builtin(_, es) => ty_args_embed(p, r, ctx, es, 0),
        Expr::Call(_, es) => ty_args_embed(p, r, ctx, es, 0),
        Expr::Let(x, a, b) => {
            ty_embed(p, r, ctx, *a);
            match ty_expr(p, r, ctx, *a) {
                Some(ta) => ty_embed(p, r, ctx.insert(x, ta), *b),
                None => {},
            }
        },
        Expr::If(c, a, b) => {
            ty_embed(p, r, ctx, *c);
            ty_embed(p, r, ctx, *a);
            ty_embed(p, r, ctx, *b);
        },
        Expr::Fold(xs, init, acc, item, body) => {
            ty_embed(p, r, ctx, *xs);
            ty_embed(p, r, ctx, *init);
            match (ty_expr(p, r, ctx, *xs), ty_expr(p, r, ctx, *init)) {
                (Some(tx), Some(ta)) => if tx is List {
                    ty_embed(p, r, ctx.insert(acc, ta).insert(item, *tx->List_0), *body);
                },
                _ => {},
            }
        },
        Expr::Match(m, nb, x, sm) => {
            ty_embed(p, r, ctx, *m);
            ty_embed(p, r, ctx, *nb);
            match (ty_expr(p, r, ctx, *m), ty_expr(p, r, ctx, *nb)) {
                (Some(tm), Some(_)) => if tm is Option {
                    ty_embed(p, r, ctx.insert(x, *tm->Option_0), *sm);
                },
                _ => {},
            }
        },
        Expr::Inj(_, _, _, a) => ty_embed(p, r, ctx, *a),
        Expr::MatchR(m, x, a, y, b) => {
            ty_embed(p, r, ctx, *m);
            match ty_expr(p, r, ctx, *m) {
                Some(tm) => if tm is Result {
                    ty_embed(p, r, ctx.insert(x, *tm->Result_0), *a);
                    ty_embed(p, r, ctx.insert(y, *tm->Result_1), *b);
                },
                None => {},
            }
        },
    }
}

/// 引数列の源の型は、核の型と同じ（写しの添字は元の式の添字と同じ）。
proof fn ty_args_embed(p: Prog, r: nat, ctx: Map<nat, Ty>, es: Seq<Expr>, i: nat)
    ensures
        ty_args_x(embed_prog(p), r, ctx, embed_args(es, 0), i) == ty_args(p, r, ctx, es, i),
    decreases es, es.len() - i,
{
    embed_args_len(es, 0);
    if i < es.len() {
        embed_args_at(es, 0, i);
        ty_embed(p, r, ctx, es[i as int]);
        ty_args_embed(p, r, ctx, es, i + 1);
    }
}

// ------------------------------------------------------------------ 核の書換えの型（源の型と一致）

/// 畳み込みの型：xs が List(s)、init が ta、本体が ctx に acc:ta と item:s を足した下で ta なら、畳み込みは ta。
pub proof fn fold_typing(
    p: Prog,
    r: nat,
    ctx: Map<nat, Ty>,
    xs: Expr,
    init: Expr,
    acc: nat,
    item: nat,
    body: Expr,
    s: Ty,
    ta: Ty,
)
    requires
        ty_expr(p, r, ctx, xs) == Some(Ty::List(Box::new(s))),
        ty_expr(p, r, ctx, init) == Some(ta),
        ty_expr(p, r, ctx.insert(acc, ta).insert(item, s), body) == Some(ta),
    ensures
        ty_expr(p, r, ctx, Expr::Fold(Box::new(xs), Box::new(init), acc, item, Box::new(body))) == Some(ta),
{
    reveal_with_fuel(ty_expr, 3);
}

/// 空の列の型：List(t, [])。
pub proof fn ty_nil(p: Prog, r: nat, ctx: Map<nat, Ty>, t: Ty)
    ensures
        ty_expr(p, r, ctx, Expr::List(t, Seq::empty())) == Some(Ty::List(Box::new(t))),
{
    reveal_with_fuel(ty_expr, 3);
    reveal_with_fuel(ty_args, 2);
    assert(Seq::<Expr>::empty().len() == 0);
    assert(ty_args(p, r, ctx, Seq::<Expr>::empty(), 0) == Some(Seq::<Ty>::empty()));
}

/// cons の型：先頭が t、後ろが List(t) なら、cons は List(t)。
pub proof fn ty_cons(p: Prog, r: nat, ctx: Map<nat, Ty>, a: Expr, b: Expr, t: Ty)
    requires
        ty_expr(p, r, ctx, a) == Some(t),
        ty_expr(p, r, ctx, b) == Some(Ty::List(Box::new(t))),
    ensures
        ty_expr(p, r, ctx, Expr::Builtin(Builtin::Cons, seq![a, b])) == Some(Ty::List(Box::new(t))),
{
    reveal_with_fuel(ty_expr, 3);
    reveal_with_fuel(ty_args, 3);
    let lt = Ty::List(Box::new(t));
    assert(ty_args(p, r, ctx, seq![a, b], 1) == Some(seq![lt]));
    assert(ty_args(p, r, ctx, seq![a, b], 0) == Some(seq![t, lt]));
}

/// reverse の型：List(t) の列の reverse は List(t)。
pub proof fn ty_reverse(p: Prog, r: nat, ctx: Map<nat, Ty>, e: Expr, t: Ty)
    requires
        ty_expr(p, r, ctx, e) == Some(Ty::List(Box::new(t))),
    ensures
        ty_expr(p, r, ctx, Expr::Builtin(Builtin::Reverse, seq![e])) == Some(Ty::List(Box::new(t))),
{
    reveal_with_fuel(ty_expr, 3);
    reveal_with_fuel(ty_args, 2);
    assert(ty_args(p, r, ctx, seq![e], 0) == Some(seq![Ty::List(Box::new(t))]));
}

/// 写像：map_collect の型は List(t)。源の map の型（body が t、xs が List(s)）と同じ。
pub proof fn map_typing(p: Prog, r: nat, ctx: Map<nat, Ty>, xs: Expr, s: Ty, t: Ty, acc: nat, x: nat, g: Expr)
    requires
        acc != x,
        absent(acc, g),
        ty_expr(p, r, ctx, xs) == Some(Ty::List(Box::new(s))),
        ty_expr(p, r, ctx.insert(x, s), g) == Some(t),
    ensures
        ty_expr(p, r, ctx, map_collect(xs, t, acc, x, g)) == Some(Ty::List(Box::new(t))),
        ty_x(embed_prog(p), r, ctx, XExpr::Map(Box::new(embed(xs)), x, Box::new(embed(g))))
            == Some(Ty::List(Box::new(t))),
{
    reveal_with_fuel(ty_expr, 3);
    let lt = Ty::List(Box::new(t));
    let ctx2 = ctx.insert(acc, lt).insert(x, s);
    assert(ctx.insert(x, s).insert(acc, lt) =~= ctx2);
    ty_absent(p, r, ctx.insert(x, s), g, acc, lt);
    assert(ty_expr(p, r, ctx2, g) == Some(t));
    assert(ctx2.contains_key(acc) && ctx2[acc] == lt);
    assert(ty_expr(p, r, ctx2, Expr::Var(acc)) == Some(lt));
    ty_cons(p, r, ctx2, g, Expr::Var(acc), t);
    ty_nil(p, r, ctx, t);
    fold_typing(p, r, ctx, xs, Expr::List(t, Seq::empty()), acc, x, cons_body(g, acc), s, lt);
    ty_reverse(
        p,
        r,
        ctx,
        Expr::Fold(Box::new(xs), Box::new(Expr::List(t, Seq::empty())), acc, x, Box::new(cons_body(g, acc))),
        t,
    );
    ty_embed(p, r, ctx, xs);
    ty_embed(p, r, ctx.insert(x, s), g);
}

/// 絞り込み：filter_collect の型は List(s)。源の filter の型（xs が List(s)、述語が Bool）と同じ。
pub proof fn filter_typing(p: Prog, r: nat, ctx: Map<nat, Ty>, xs: Expr, s: Ty, acc: nat, x: nat, c: Expr)
    requires
        acc != x,
        absent(acc, c),
        ty_expr(p, r, ctx, xs) == Some(Ty::List(Box::new(s))),
        ty_expr(p, r, ctx.insert(x, s), c) == Some(Ty::Bool),
    ensures
        ty_expr(p, r, ctx, filter_collect(xs, s, acc, x, c)) == Some(Ty::List(Box::new(s))),
        ty_x(embed_prog(p), r, ctx, XExpr::Filter(Box::new(embed(xs)), x, Box::new(embed(c))))
            == Some(Ty::List(Box::new(s))),
{
    reveal_with_fuel(ty_expr, 3);
    let ls = Ty::List(Box::new(s));
    let ctx2 = ctx.insert(acc, ls).insert(x, s);
    assert(ctx.insert(x, s).insert(acc, ls) =~= ctx2);
    ty_absent(p, r, ctx.insert(x, s), c, acc, ls);
    assert(ty_expr(p, r, ctx2, c) == Some(Ty::Bool));
    assert(ty_expr(p, r, ctx2, Expr::Var(x)) == Some(s));
    assert(ty_expr(p, r, ctx2, Expr::Var(acc)) == Some(ls));
    ty_cons(p, r, ctx2, Expr::Var(x), Expr::Var(acc), s);
    assert(ty_expr(p, r, ctx2, filter_body(c, acc, x)) == Some(ls));
    ty_nil(p, r, ctx, s);
    fold_typing(p, r, ctx, xs, Expr::List(s, Seq::empty()), acc, x, filter_body(c, acc, x), s, ls);
    ty_reverse(
        p,
        r,
        ctx,
        Expr::Fold(Box::new(xs), Box::new(Expr::List(s, Seq::empty())), acc, x, Box::new(filter_body(c, acc, x))),
        s,
    );
    ty_embed(p, r, ctx, xs);
    ty_embed(p, r, ctx.insert(x, s), c);
}

/// any の型：any_fold の型は Bool。源の any と同じ。
pub proof fn any_typing(p: Prog, r: nat, ctx: Map<nat, Ty>, xs: Expr, s: Ty, acc: nat, x: nat, c: Expr)
    requires
        acc != x,
        absent(acc, c),
        ty_expr(p, r, ctx, xs) == Some(Ty::List(Box::new(s))),
        ty_expr(p, r, ctx.insert(x, s), c) == Some(Ty::Bool),
    ensures
        ty_expr(p, r, ctx, any_fold(xs, acc, x, c)) == Some(Ty::Bool),
        ty_x(embed_prog(p), r, ctx, XExpr::Any(Box::new(embed(xs)), x, Box::new(embed(c)))) == Some(Ty::Bool),
{
    reveal_with_fuel(ty_expr, 3);
    let ctx2 = ctx.insert(acc, Ty::Bool).insert(x, s);
    assert(ctx.insert(x, s).insert(acc, Ty::Bool) =~= ctx2);
    ty_absent(p, r, ctx.insert(x, s), c, acc, Ty::Bool);
    assert(ty_expr(p, r, ctx2, Expr::Var(acc)) == Some(Ty::Bool));
    assert(ty_expr(p, r, ctx2, c) == Some(Ty::Bool));
    assert(ty_expr(p, r, ctx2, Expr::If(Box::new(Expr::Var(acc)), Box::new(Expr::Bool(true)), Box::new(c))) == Some(
        Ty::Bool,
    ));
    fold_typing(
        p,
        r,
        ctx,
        xs,
        Expr::Bool(false),
        acc,
        x,
        Expr::If(Box::new(Expr::Var(acc)), Box::new(Expr::Bool(true)), Box::new(c)),
        s,
        Ty::Bool,
    );
    ty_embed(p, r, ctx, xs);
    ty_embed(p, r, ctx.insert(x, s), c);
}

/// all の型：all_fold の型は Bool。源の all と同じ。
pub proof fn all_typing(p: Prog, r: nat, ctx: Map<nat, Ty>, xs: Expr, s: Ty, acc: nat, x: nat, c: Expr)
    requires
        acc != x,
        absent(acc, c),
        ty_expr(p, r, ctx, xs) == Some(Ty::List(Box::new(s))),
        ty_expr(p, r, ctx.insert(x, s), c) == Some(Ty::Bool),
    ensures
        ty_expr(p, r, ctx, all_fold(xs, acc, x, c)) == Some(Ty::Bool),
        ty_x(embed_prog(p), r, ctx, XExpr::All(Box::new(embed(xs)), x, Box::new(embed(c)))) == Some(Ty::Bool),
{
    reveal_with_fuel(ty_expr, 3);
    let ctx2 = ctx.insert(acc, Ty::Bool).insert(x, s);
    assert(ctx.insert(x, s).insert(acc, Ty::Bool) =~= ctx2);
    ty_absent(p, r, ctx.insert(x, s), c, acc, Ty::Bool);
    assert(ty_expr(p, r, ctx2, Expr::Var(acc)) == Some(Ty::Bool));
    assert(ty_expr(p, r, ctx2, c) == Some(Ty::Bool));
    assert(ty_expr(p, r, ctx2, Expr::If(Box::new(Expr::Var(acc)), Box::new(c), Box::new(Expr::Bool(false)))) == Some(
        Ty::Bool,
    ));
    fold_typing(
        p,
        r,
        ctx,
        xs,
        Expr::Bool(true),
        acc,
        x,
        Expr::If(Box::new(Expr::Var(acc)), Box::new(c), Box::new(Expr::Bool(false))),
        s,
        Ty::Bool,
    );
    ty_embed(p, r, ctx, xs);
    ty_embed(p, r, ctx.insert(x, s), c);
}

/// 選択：find_fold の型は Option(t)。源の find（要素の型 t）と同じ。
pub proof fn find_typing(p: Prog, r: nat, ctx: Map<nat, Ty>, xs: Expr, t: Ty, acc: nat, item: nat, x: nat, c: Expr)
    requires
        acc != item,
        absent(acc, c),
        ty_expr(p, r, ctx, xs) == Some(Ty::List(Box::new(t))),
        ty_expr(p, r, ctx.insert(item, t), c) == Some(Ty::Bool),
    ensures
        ty_expr(p, r, ctx, find_fold(xs, t, acc, item, c, x)) == Some(Ty::Option(Box::new(t))),
        ty_x(embed_prog(p), r, ctx, XExpr::Find(Box::new(embed(xs)), item, Box::new(embed(c))))
            == Some(Ty::Option(Box::new(t))),
{
    reveal_with_fuel(ty_expr, 3);
    let ot = Ty::Option(Box::new(t));
    let ctx2 = ctx.insert(acc, ot).insert(item, t);
    assert(ctx.insert(item, t).insert(acc, ot) =~= ctx2);
    ty_absent(p, r, ctx.insert(item, t), c, acc, ot);
    assert(ty_expr(p, r, ctx2, c) == Some(Ty::Bool));
    assert(ty_expr(p, r, ctx2, Expr::Var(acc)) == Some(ot));
    assert(ty_expr(p, r, ctx2, Expr::Some(Box::new(Expr::Var(item)))) == Some(ot));
    assert(ty_expr(p, r, ctx2, Expr::None(t)) == Some(ot));
    assert(ty_expr(p, r, ctx2, Expr::If(Box::new(c), Box::new(Expr::Some(Box::new(Expr::Var(item)))), Box::new(
        Expr::None(t),
    ))) == Some(ot));
    assert(ty_expr(p, r, ctx2.insert(x, t), Expr::Some(Box::new(Expr::Var(x)))) == Some(ot));
    assert(ty_expr(p, r, ctx2, select_body(c, t, acc, item, x)) == Some(ot));
    assert(ty_expr(p, r, ctx, Expr::None(t)) == Some(ot));
    fold_typing(p, r, ctx, xs, Expr::None(t), acc, item, select_body(c, t, acc, item, x), t, ot);
    ty_embed(p, r, ctx, xs);
    ty_embed(p, r, ctx.insert(item, t), c);
}

} // verus!
