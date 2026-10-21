//! SH6：型の付いた書換えでは、源は行き詰まらない（段階 1b・SH6 の第三部）。
//!
//! SH4 の行き詰まりの模擬（simulation.rs の `sim_expr_stuck`・`sh4_same_result`）は、any・all・sort_by を含まない
//! プログラム（`no_open_hof_prog`）に限る。sh6_stuck.rs が示すとおり、any・all・sort_by では、源が行き詰まっても写しが
//! 値を返す場合が残る（隙間。`any_gap`・`all_gap`・`sort_gap`）。filter・find と同じ形の仮定は成り立たない
//! （`any_full_fails`・`all_full_fails`・`sort_full_fails`）。
//!
//! 隙間は型の付いたプログラムでは起きない。ここでは、書換え後のプログラムが整形式（`wf`。検証済みの型検査が書換え後の
//! ソースに課す条件）で、入力が entry の引数の型を持つなら、源はどの燃料でも行き詰まらないことを示す（`sh6_source_safe`）。
//! 証明は燃料についての帰納法である。源の値は SH4 の模擬（`sim_expr`）で写しの値になり、その型は型保存（`sound`）で
//! 決まる。hof の形では、写しの型から子の写しの型を取り出す（`map_inv` から `sort_inv`。書換えの形 `hof_shapes` による）。
//! `sh6_same_result` は、`sh4_same_result` の行き詰まりの場合を、no_open_hof のプログラムか、型の付いたプログラム
//! （このとき源は行き詰まらないので、行き詰まりの場合は起きない）に広げる。`sh6_typed_same` は、型の付いたプログラムで
//! 源の OutOfFuel でない結果は値で、写しも同じ値を返すことをまとめる。

use crate::bigstep::*;
use crate::fold_meaning::*;
use crate::proof::*;
use crate::records_proof::*;
use crate::sh6_obligations::*;
use crate::sh6_stuck::*;
use crate::simulation::*;
use crate::sortmeaning::*;
use crate::sortspec::*;
use crate::spec::*;
use crate::xsem::*;
use crate::xtyping::*;
use vstd::prelude::*;

verus! {

// ------------------------------------------------------------------ 型から値の形

/// Bool の型の値は真偽。
pub proof fn bool_of_ty(v: Val)
    requires
        val_type(v, Ty::Bool),
    ensures
        v is Bool,
{
}

/// Int の型の値は整数。
pub proof fn int_of_ty(v: Val)
    requires
        val_type(v, Ty::Int),
    ensures
        v is Int,
{
}

/// List(s) の型の値はリストで、各要素は s の型を持つ。
pub proof fn list_of_ty(v: Val, s: Ty)
    requires
        val_type(v, Ty::List(Box::new(s))),
    ensures
        v is List,
        forall|k: int| 0 <= k < v->List_0.len() ==> #[trigger] val_type(v->List_0[k], s),
{
    assert(v is List);
    val_type_list(v->List_0, s);
}

/// Option(te) の型の値は、None か、te の型の値の Some。
pub proof fn opt_of_ty(v: Val, te: Ty)
    requires
        val_type(v, Ty::Option(Box::new(te))),
    ensures
        v is None || (v is Some && val_type(*v->Some_0, te)),
{
}

/// Result(tl, tr) の型の値は、tl の型の値の Ok か、tr の型の値の Err。
pub proof fn res_of_ty(v: Val, tl: Ty, tr: Ty)
    requires
        val_type(v, Ty::Result(Box::new(tl), Box::new(tr))),
    ensures
        (v is Ok && val_type(*v->Ok_0, tl)) || (v is Err && val_type(*v->Err_0, tr)),
{
}

// ------------------------------------------------------------------ 型の取り出し（核の式の一段）

/// 引数一つの組込み：型が付けば、引数に型が付き、組込みの型はその型から決まる。
pub proof fn ty_arg1_inv(p: Prog, r: nat, ctx: Map<nat, Ty>, b: Builtin, a: Expr)
    requires
        ty_expr(p, r, ctx, Expr::Builtin(b, seq![a])) is Some,
    ensures
        ty_expr(p, r, ctx, a) is Some,
        ty_expr(p, r, ctx, Expr::Builtin(b, seq![a])) == builtin_type(b, seq![ty_expr(p, r, ctx, a)->Some_0]),
{
    let es = seq![a];
    assert(es[0] == a);
    assert(ty_args(p, r, ctx, es, 0) is Some);
    assert(ty_args(p, r, ctx, es, 1) == Some(Seq::<Ty>::empty()));
    let t0 = ty_expr(p, r, ctx, a)->Some_0;
    assert(ty_args(p, r, ctx, es, 0) == Some(seq![t0] + Seq::<Ty>::empty()));
    assert(seq![t0] + Seq::<Ty>::empty() =~= seq![t0]);
}

/// 引数二つの組込み。
pub proof fn ty_arg2_inv(p: Prog, r: nat, ctx: Map<nat, Ty>, b: Builtin, a1: Expr, a2: Expr)
    requires
        ty_expr(p, r, ctx, Expr::Builtin(b, seq![a1, a2])) is Some,
    ensures
        ty_expr(p, r, ctx, a1) is Some,
        ty_expr(p, r, ctx, a2) is Some,
        ty_expr(p, r, ctx, Expr::Builtin(b, seq![a1, a2])) == builtin_type(
            b,
            seq![ty_expr(p, r, ctx, a1)->Some_0, ty_expr(p, r, ctx, a2)->Some_0],
        ),
{
    let es = seq![a1, a2];
    assert(es[0] == a1 && es[1] == a2);
    assert(ty_args(p, r, ctx, es, 0) is Some);
    assert(ty_args(p, r, ctx, es, 1) is Some);
    assert(ty_args(p, r, ctx, es, 2) == Some(Seq::<Ty>::empty()));
    let t1 = ty_expr(p, r, ctx, a1)->Some_0;
    let t2 = ty_expr(p, r, ctx, a2)->Some_0;
    assert(ty_args(p, r, ctx, es, 1) == Some(seq![t2] + Seq::<Ty>::empty()));
    assert(seq![t2] + Seq::<Ty>::empty() =~= seq![t2]);
    assert(ty_args(p, r, ctx, es, 0) == Some(seq![t1] + seq![t2]));
    assert(seq![t1] + seq![t2] =~= seq![t1, t2]);
}

/// 畳み込み：型が付けば、列は List(te)、初期値は ta、本体は acc:ta と item:te を足した文脈で ta。
pub proof fn ty_fold_inv(p: Prog, r: nat, ctx: Map<nat, Ty>, xs: Expr, init: Expr, acc: nat, item: nat, body: Expr) -> (tt: (
    Ty,
    Ty,
))
    requires
        ty_expr(p, r, ctx, Expr::Fold(Box::new(xs), Box::new(init), acc, item, Box::new(body))) is Some,
    ensures
        ty_expr(p, r, ctx, xs) == Some(Ty::List(Box::new(tt.0))),
        ty_expr(p, r, ctx, init) == Some(tt.1),
        ty_expr(p, r, ctx.insert(acc, tt.1).insert(item, tt.0), body) == Some(tt.1),
        ty_expr(p, r, ctx, Expr::Fold(Box::new(xs), Box::new(init), acc, item, Box::new(body))) == Some(tt.1),
{
    assert(ty_expr(p, r, ctx, xs) is Some && ty_expr(p, r, ctx, init) is Some);
    let tx = ty_expr(p, r, ctx, xs)->Some_0;
    let ta = ty_expr(p, r, ctx, init)->Some_0;
    assert(tx is List);
    let te = *tx->List_0;
    assert(tx == Ty::List(Box::new(te)));
    (te, ta)
}

/// if：型が付けば、条件は Bool、二つの枝は同じ型。
pub proof fn ty_if_inv(p: Prog, r: nat, ctx: Map<nat, Ty>, c: Expr, a: Expr, b: Expr)
    requires
        ty_expr(p, r, ctx, Expr::If(Box::new(c), Box::new(a), Box::new(b))) is Some,
    ensures
        ty_expr(p, r, ctx, c) == Some(Ty::Bool),
        ty_expr(p, r, ctx, a) is Some,
        ty_expr(p, r, ctx, b) == ty_expr(p, r, ctx, a),
        ty_expr(p, r, ctx, Expr::If(Box::new(c), Box::new(a), Box::new(b))) == ty_expr(p, r, ctx, a),
{
}

/// let：型が付けば、束縛する式に型が付き、本体はその型を足した文脈で let と同じ型。
pub proof fn ty_let_inv(p: Prog, r: nat, ctx: Map<nat, Ty>, x: nat, a: Expr, b: Expr)
    requires
        ty_expr(p, r, ctx, Expr::Let(x, Box::new(a), Box::new(b))) is Some,
    ensures
        ty_expr(p, r, ctx, a) is Some,
        ty_expr(p, r, ctx.insert(x, ty_expr(p, r, ctx, a)->Some_0), b) == ty_expr(
            p,
            r,
            ctx,
            Expr::Let(x, Box::new(a), Box::new(b)),
        ),
{
}

/// match_option：型が付けば、調べる式は Option(te)、二つの枝は同じ型。
pub proof fn ty_match_inv(p: Prog, r: nat, ctx: Map<nat, Ty>, m: Expr, nb: Expr, x: nat, sm: Expr) -> (te: Ty)
    requires
        ty_expr(p, r, ctx, Expr::Match(Box::new(m), Box::new(nb), x, Box::new(sm))) is Some,
    ensures
        ty_expr(p, r, ctx, m) == Some(Ty::Option(Box::new(te))),
        ty_expr(p, r, ctx, nb) is Some,
        ty_expr(p, r, ctx.insert(x, te), sm) == ty_expr(p, r, ctx, nb),
        ty_expr(p, r, ctx, Expr::Match(Box::new(m), Box::new(nb), x, Box::new(sm))) == ty_expr(p, r, ctx, nb),
{
    assert(ty_expr(p, r, ctx, m) is Some && ty_expr(p, r, ctx, nb) is Some);
    let tm = ty_expr(p, r, ctx, m)->Some_0;
    assert(tm is Option);
    let te = *tm->Option_0;
    assert(tm == Ty::Option(Box::new(te)));
    te
}

/// match_result：型が付けば、調べる式は Result(tl, tr)、二つの枝はそれぞれの文脈で型が付く。
pub proof fn ty_matchr_inv(p: Prog, r: nat, ctx: Map<nat, Ty>, m: Expr, x: nat, a: Expr, y: nat, b: Expr) -> (tt: (
    Ty,
    Ty,
))
    requires
        ty_expr(p, r, ctx, Expr::MatchR(Box::new(m), x, Box::new(a), y, Box::new(b))) is Some,
    ensures
        ty_expr(p, r, ctx, m) == Some(Ty::Result(Box::new(tt.0), Box::new(tt.1))),
        ty_expr(p, r, ctx.insert(x, tt.0), a) is Some,
        ty_expr(p, r, ctx.insert(y, tt.1), b) is Some,
{
    assert(ty_expr(p, r, ctx, m) is Some);
    let tm = ty_expr(p, r, ctx, m)->Some_0;
    assert(tm is Result);
    let tl = *tm->Result_0;
    let tr = *tm->Result_1;
    assert(tm == Ty::Result(Box::new(tl), Box::new(tr)));
    (tl, tr)
}

/// 本体の文脈：acc が c に現れず acc != x なら、acc:ta と x:s を足した文脈での c の型は、x:s だけを足した文脈での型。
pub proof fn body_ctx(p: Prog, r: nat, ctx: Map<nat, Ty>, acc: nat, ta: Ty, x: nat, s: Ty, c: Expr)
    requires
        acc != x,
        absent(acc, c),
    ensures
        ty_expr(p, r, ctx.insert(acc, ta).insert(x, s), c) == ty_expr(p, r, ctx.insert(x, s), c),
{
    assert(ctx.insert(x, s).insert(acc, ta) =~= ctx.insert(acc, ta).insert(x, s));
    ty_absent(p, r, ctx.insert(x, s), c, acc, ta);
}

// ------------------------------------------------------------------ hof の形の写しの型から子の型

/// map の写し：型が付けば、列は List(s)、本体は x:s の文脈で型が付く。
pub proof fn map_inv(p: Prog, r: nat, ctx: Map<nat, Ty>, xs: Expr, t: Ty, acc: nat, x: nat, g: Expr) -> (s: Ty)
    requires
        acc != x,
        absent(acc, g),
        ty_expr(p, r, ctx, map_collect(xs, t, acc, x, g)) is Some,
    ensures
        ty_expr(p, r, ctx, xs) == Some(Ty::List(Box::new(s))),
        ty_expr(p, r, ctx.insert(x, s), g) is Some,
{
    let fe = Expr::Fold(Box::new(xs), Box::new(Expr::List(t, Seq::empty())), acc, x, Box::new(cons_body(g, acc)));
    assert(map_collect(xs, t, acc, x, g) == Expr::Builtin(Builtin::Reverse, seq![fe]));
    ty_arg1_inv(p, r, ctx, Builtin::Reverse, fe);
    let (s, ta) = ty_fold_inv(p, r, ctx, xs, Expr::List(t, Seq::empty()), acc, x, cons_body(g, acc));
    let c2 = ctx.insert(acc, ta).insert(x, s);
    assert(cons_body(g, acc) == Expr::Builtin(Builtin::Cons, seq![g, Expr::Var(acc)]));
    ty_arg2_inv(p, r, c2, Builtin::Cons, g, Expr::Var(acc));
    body_ctx(p, r, ctx, acc, ta, x, s, g);
    s
}

/// filter の写し：型が付けば、列は List(s)、述語は x:s の文脈で Bool。
pub proof fn filter_inv(p: Prog, r: nat, ctx: Map<nat, Ty>, xs: Expr, t: Ty, acc: nat, x: nat, c: Expr) -> (s: Ty)
    requires
        acc != x,
        absent(acc, c),
        ty_expr(p, r, ctx, filter_collect(xs, t, acc, x, c)) is Some,
    ensures
        ty_expr(p, r, ctx, xs) == Some(Ty::List(Box::new(s))),
        ty_expr(p, r, ctx.insert(x, s), c) == Some(Ty::Bool),
{
    let fe = Expr::Fold(Box::new(xs), Box::new(Expr::List(t, Seq::empty())), acc, x, Box::new(filter_body(c, acc, x)));
    assert(filter_collect(xs, t, acc, x, c) == Expr::Builtin(Builtin::Reverse, seq![fe]));
    ty_arg1_inv(p, r, ctx, Builtin::Reverse, fe);
    let (s, ta) = ty_fold_inv(p, r, ctx, xs, Expr::List(t, Seq::empty()), acc, x, filter_body(c, acc, x));
    let c2 = ctx.insert(acc, ta).insert(x, s);
    ty_if_inv(p, r, c2, c, Expr::Builtin(Builtin::Cons, seq![Expr::Var(x), Expr::Var(acc)]), Expr::Var(acc));
    body_ctx(p, r, ctx, acc, ta, x, s, c);
    s
}

/// any の写し：型が付けば、列は List(s)、述語は x:s の文脈で Bool。
pub proof fn any_inv(p: Prog, r: nat, ctx: Map<nat, Ty>, xs: Expr, acc: nat, x: nat, c: Expr) -> (s: Ty)
    requires
        acc != x,
        absent(acc, c),
        ty_expr(p, r, ctx, any_fold(xs, acc, x, c)) is Some,
    ensures
        ty_expr(p, r, ctx, xs) == Some(Ty::List(Box::new(s))),
        ty_expr(p, r, ctx.insert(x, s), c) == Some(Ty::Bool),
{
    let body = Expr::If(Box::new(Expr::Var(acc)), Box::new(Expr::Bool(true)), Box::new(c));
    let (s, ta) = ty_fold_inv(p, r, ctx, xs, Expr::Bool(false), acc, x, body);
    let c2 = ctx.insert(acc, ta).insert(x, s);
    ty_if_inv(p, r, c2, Expr::Var(acc), Expr::Bool(true), c);
    assert(ty_expr(p, r, c2, Expr::Bool(true)) == Some(Ty::Bool));
    body_ctx(p, r, ctx, acc, ta, x, s, c);
    s
}

/// all の写し：型が付けば、列は List(s)、述語は x:s の文脈で Bool。
pub proof fn all_inv(p: Prog, r: nat, ctx: Map<nat, Ty>, xs: Expr, acc: nat, x: nat, c: Expr) -> (s: Ty)
    requires
        acc != x,
        absent(acc, c),
        ty_expr(p, r, ctx, all_fold(xs, acc, x, c)) is Some,
    ensures
        ty_expr(p, r, ctx, xs) == Some(Ty::List(Box::new(s))),
        ty_expr(p, r, ctx.insert(x, s), c) == Some(Ty::Bool),
{
    let body = Expr::If(Box::new(Expr::Var(acc)), Box::new(c), Box::new(Expr::Bool(false)));
    let (s, ta) = ty_fold_inv(p, r, ctx, xs, Expr::Bool(true), acc, x, body);
    let c2 = ctx.insert(acc, ta).insert(x, s);
    ty_if_inv(p, r, c2, Expr::Var(acc), c, Expr::Bool(false));
    assert(ty_expr(p, r, c2, Expr::Bool(false)) == Some(Ty::Bool));
    body_ctx(p, r, ctx, acc, ta, x, s, c);
    s
}

/// find の写し：型が付けば、列は List(s)、述語は x:s の文脈で Bool（y は match の束縛の名前）。
pub proof fn find_inv(p: Prog, r: nat, ctx: Map<nat, Ty>, xs: Expr, t: Ty, acc: nat, x: nat, c: Expr, y: nat) -> (s: Ty)
    requires
        acc != x,
        absent(acc, c),
        ty_expr(p, r, ctx, find_fold(xs, t, acc, x, c, y)) is Some,
    ensures
        ty_expr(p, r, ctx, xs) == Some(Ty::List(Box::new(s))),
        ty_expr(p, r, ctx.insert(x, s), c) == Some(Ty::Bool),
{
    let (s, ta) = ty_fold_inv(p, r, ctx, xs, Expr::None(t), acc, x, select_body(c, t, acc, x, y));
    let c2 = ctx.insert(acc, ta).insert(x, s);
    let nb = Expr::If(Box::new(c), Box::new(Expr::Some(Box::new(Expr::Var(x)))), Box::new(Expr::None(t)));
    assert(select_body(c, t, acc, x, y) == Expr::Match(
        Box::new(Expr::Var(acc)),
        Box::new(nb),
        y,
        Box::new(Expr::Some(Box::new(Expr::Var(y)))),
    ));
    let _ = ty_match_inv(p, r, c2, Expr::Var(acc), nb, y, Expr::Some(Box::new(Expr::Var(y))));
    ty_if_inv(p, r, c2, c, Expr::Some(Box::new(Expr::Var(x))), Expr::None(t));
    body_ctx(p, r, ctx, acc, ta, x, s, c);
    s
}

/// sort_by の写し：型が付けば、列は List(s)、鍵は x:s の文脈で Int（挿入の比較 Lt が鍵を Int に限る）。
pub proof fn sort_inv(
    p: Prog,
    r: nat,
    ctx: Map<nat, Ty>,
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
) -> (s: Ty)
    requires
        names_ok(acc, e, st, y, ky, ke, rb, x),
        absent(acc, k),
        absent(e, k),
        absent(st, k),
        absent(y, k),
        ty_expr(p, r, ctx, sort_collect(xs, t, acc, e, st, y, ky, ke, rb, x, k)) is Some,
    ensures
        ty_expr(p, r, ctx, xs) == Some(Ty::List(Box::new(s))),
        ty_expr(p, r, ctx.insert(x, s), k) == Some(Ty::Int),
{
    let body = sort_body(t, acc, e, st, y, ky, ke, rb, x, k);
    let (s, ta) = ty_fold_inv(p, r, ctx, xs, Expr::List(t, Seq::empty()), acc, e, body);
    ty_nil(p, r, ctx, t);
    let lt = Ty::List(Box::new(t));
    assert(ta == lt);
    let c1 = ctx.insert(acc, lt).insert(e, s);
    // 外側の本体：let rb = fold(cons(e, acc), init_state, |st, y| sort_inner) in reverse(sort_rev)
    let ys = cons_e(Expr::Var(e), Expr::Var(acc));
    let inner = sort_inner(e, st, y, ky, ke, x, k);
    let ife = Expr::Fold(Box::new(ys), Box::new(init_state(t)), st, y, Box::new(inner));
    let tail = Expr::Builtin(Builtin::Reverse, seq![sort_rev(e, rb)]);
    assert(body == Expr::Let(rb, Box::new(ife), Box::new(tail)));
    ty_let_inv(p, r, c1, rb, ife, tail);
    let (s2, tsi) = ty_fold_inv(p, r, c1, ys, init_state(t), st, y, inner);
    // cons(e, acc) の型：e は s、acc は List(t) なので、t == s で、内側の項 y も s。
    ty_arg2_inv(p, r, c1, Builtin::Cons, Expr::Var(e), Expr::Var(acc));
    assert(c1.contains_key(e) && c1[e] == s);
    assert(c1.contains_key(acc) && c1[acc] == lt);
    assert(ty_expr(p, r, c1, Expr::Var(e)) == Some(s));
    assert(ty_expr(p, r, c1, Expr::Var(acc)) == Some(lt));
    assert(lt == Ty::List(Box::new(s)));
    assert(s2 == s);
    let c2 = c1.insert(st, tsi).insert(y, s);
    // 内側の本体：if 置いた then … else sort_fresh
    let fresh = sort_fresh(e, st, y, ky, ke, x, k);
    assert(inner == Expr::If(Box::new(sort_cond(st)), Box::new(sort_placed(st, y)), Box::new(fresh)));
    ty_if_inv(p, r, c2, sort_cond(st), sort_placed(st, y), fresh);
    // sort_fresh：let ky = (let x = y in k) in sort_match
    let kl = Expr::Let(x, Box::new(Expr::Var(y)), Box::new(k));
    let sm = sort_match(e, st, y, ky, ke);
    assert(fresh == Expr::Let(ky, Box::new(kl), Box::new(sm)));
    ty_let_inv(p, r, c2, ky, kl, sm);
    ty_let_inv(p, r, c2, x, Expr::Var(y), k);
    assert(c2.contains_key(y) && c2[y] == s);
    assert(ty_expr(p, r, c2, Expr::Var(y)) == Some(s));
    let tk = ty_expr(p, r, c2, kl)->Some_0;
    assert(ty_expr(p, r, c2.insert(x, s), k) == Some(tk));
    // sort_match：match fst(st) { None => …, Some(ke) => sort_lt }
    let c3 = c2.insert(ky, tk);
    let nb = pair_e(Expr::Some(Box::new(Expr::Var(ky))), psnd(Expr::Var(st)));
    let lte = sort_lt(e, st, y, ky, ke);
    assert(sm == Expr::Match(Box::new(pfst(Expr::Var(st))), Box::new(nb), ke, Box::new(lte)));
    let te2 = ty_match_inv(p, r, c3, pfst(Expr::Var(st)), nb, ke, lte);
    let c4 = c3.insert(ke, te2);
    // sort_lt：if lt(ke, ky) then … else …。Lt の型は Int と Int。
    let cmp = Expr::Builtin(Builtin::Lt, seq![Expr::Var(ke), Expr::Var(ky)]);
    assert(lte == Expr::If(Box::new(cmp), Box::new(sort_before(e, st, y)), Box::new(sort_after(st, y))));
    ty_if_inv(p, r, c4, cmp, sort_before(e, st, y), sort_after(st, y));
    ty_arg2_inv(p, r, c4, Builtin::Lt, Expr::Var(ke), Expr::Var(ky));
    assert(c4.contains_key(ky) && c4[ky] == tk);
    assert(ty_expr(p, r, c4, Expr::Var(ky)) == Some(tk));
    assert(tk == Ty::Int);
    // 導入した名前 acc・e・st・y を除く（鍵に現れない）。
    let c0 = ctx.insert(x, s);
    assert(c2.insert(x, s) =~= c0.insert(acc, lt).insert(e, s).insert(st, tsi).insert(y, s));
    ty_absent(p, r, c0.insert(acc, lt).insert(e, s).insert(st, tsi), k, y, s);
    ty_absent(p, r, c0.insert(acc, lt).insert(e, s), k, st, tsi);
    ty_absent(p, r, c0.insert(acc, lt), k, e, s);
    ty_absent(p, r, c0, k, acc, lt);
    s
}

// ------------------------------------------------------------------ 源の値の型（模擬と型保存）

/// 源の式が値 v に評価されれば、v は写しの型を持つ（sim_expr で写しも v になり、sound で型が決まる）。
pub proof fn xval_typed(
    xp: XProg,
    p: Prog,
    rw: spec_fn(XExpr) -> Expr,
    n: nat,
    r: nat,
    ctx: Map<nat, Ty>,
    env: Map<nat, Val>,
    e: XExpr,
    v: Val,
)
    requires
        sim_ok(xp, p, rw),
        wf(p),
        env_ok(env, ctx),
        ty_expr(p, r, ctx, rw(e)) is Some,
        xeval(xp, n, env, e) == Res::Done(v),
    ensures
        val_type(v, ty_expr(p, r, ctx, rw(e))->Some_0),
{
    sim_expr(xp, p, rw, n, env, e, v);
    let m = choose|m: nat| #[trigger] eval(p, m, env, rw(e)) == Res::Done(v);
    sound(p, m, r, ctx, env, rw(e), v);
}

/// 引数列の模擬（simulation.rs の sim_args と同じ。あちらは非公開）。
pub proof fn sim_args6(
    xp: XProg,
    p: Prog,
    rw: spec_fn(XExpr) -> Expr,
    n: nat,
    env: Map<nat, Val>,
    es: Seq<XExpr>,
    i: nat,
    vs: Seq<Val>,
)
    requires
        sim_ok(xp, p, rw),
        xeval_args(xp, n, env, es, i) == ResSeq::Done(vs),
    ensures
        args_to(p, env, rw_args(rw, es), i, vs),
    decreases n,
{
    if n > 0 && i < es.len() {
        let f = (n - 1) as nat;
        match xeval(xp, f, env, es[i as int]) {
            Res::Done(v) => match xeval_args(xp, f, env, es, i + 1) {
                ResSeq::Done(vs2) => {
                    sim_expr(xp, p, rw, f, env, es[i as int], v);
                    sim_args6(xp, p, rw, f, env, es, i + 1, vs2);
                    let m1 = choose|m: nat| #[trigger] eval(p, m, env, rw(es[i as int])) == Res::Done(v);
                    let m2 = choose|m: nat| #[trigger] eval_args(p, m, env, rw_args(rw, es), i + 1) == ResSeq::Done(vs2);
                    let mm = (max(m1, m2) + 1) as nat;
                    mono(p, m1, (mm - 1) as nat, env, rw(es[i as int]));
                    mono_args(p, m2, (mm - 1) as nat, env, rw_args(rw, es), i + 1);
                    assert(rw_args(rw, es)[i as int] == rw(es[i as int]));
                    assert(eval_args(p, mm, env, rw_args(rw, es), i) == ResSeq::Done(vs));
                },
                _ => {},
            },
            _ => {},
        }
    } else if n > 0 {
        assert(eval_args(p, 1, env, rw_args(rw, es), i) == ResSeq::Done(Seq::<Val>::empty()));
    }
}

/// 源の引数列が vs に評価されれば、vs の各値は写しの引数の型を持つ。
pub proof fn xargs_typed(
    xp: XProg,
    p: Prog,
    rw: spec_fn(XExpr) -> Expr,
    n: nat,
    r: nat,
    ctx: Map<nat, Ty>,
    env: Map<nat, Val>,
    es: Seq<XExpr>,
    vs: Seq<Val>,
)
    requires
        sim_ok(xp, p, rw),
        wf(p),
        env_ok(env, ctx),
        ty_args(p, r, ctx, rw_args(rw, es), 0) is Some,
        xeval_args(xp, n, env, es, 0) == ResSeq::Done(vs),
    ensures
        vs.len() == ty_args(p, r, ctx, rw_args(rw, es), 0)->Some_0.len(),
        forall|k: int| 0 <= k < vs.len() ==> val_type(#[trigger] vs[k], ty_args(p, r, ctx, rw_args(rw, es), 0)->Some_0[k]),
{
    sim_args6(xp, p, rw, n, env, es, 0, vs);
    let m = choose|m: nat| #[trigger] eval_args(p, m, env, rw_args(rw, es), 0) == ResSeq::Done(vs);
    sound_args(p, m, r, ctx, env, rw_args(rw, es), 0, vs);
}

/// 引数の名前が同じなら、束縛の環境は同じ（simulation.rs の bind_names_eq と同じ。あちらは非公開）。
pub proof fn bind_names_eq6(p1: Seq<(nat, Ty)>, p2: Seq<(nat, Ty)>, vs: Seq<Val>, n: nat)
    requires
        p1.len() == p2.len(),
        forall|k: int| 0 <= k < p1.len() ==> #[trigger] p1[k].0 == p2[k].0,
    ensures
        bind(p1, vs, n) == bind(p2, vs, n),
    decreases n,
{
    if n > 0 {
        bind_names_eq6(p1, p2, vs, (n - 1) as nat);
    }
}

/// map の列の値の型：源の xmap が vs を返せば、vs の各値は本体の写しの型 t を持つ。
pub proof fn xmap_typed(
    xp: XProg,
    p: Prog,
    rw: spec_fn(XExpr) -> Expr,
    n: nat,
    r: nat,
    ctx: Map<nat, Ty>,
    env: Map<nat, Val>,
    x: nat,
    c: XExpr,
    s: Ty,
    t: Ty,
    items: Seq<Val>,
    j: nat,
    vs: Seq<Val>,
)
    requires
        sim_ok(xp, p, rw),
        wf(p),
        env_ok(env, ctx),
        ty_expr(p, r, ctx.insert(x, s), rw(c)) == Some(t),
        forall|k: int| 0 <= k < items.len() ==> val_type(#[trigger] items[k], s),
        xmap(xp, n, env, x, c, items, j) == ResSeq::Done(vs),
    ensures
        forall|i: int| 0 <= i < vs.len() ==> val_type(#[trigger] vs[i], t),
    decreases n,
{
    if n > 0 && j < items.len() {
        let f = (n - 1) as nat;
        let env2 = env.insert(x, items[j as int]);
        match xeval(xp, f, env2, c) {
            Res::Done(v) => match xmap(xp, f, env, x, c, items, j + 1) {
                ResSeq::Done(vs2) => {
                    env_ok_insert(env, ctx, x, items[j as int], s);
                    xval_typed(xp, p, rw, f, r, ctx.insert(x, s), env2, c, v);
                    xmap_typed(xp, p, rw, f, r, ctx, env, x, c, s, t, items, j + 1, vs2);
                    assert(vs == seq![v] + vs2);
                    assert forall|i: int| 0 <= i < vs.len() implies val_type(#[trigger] vs[i], t) by {
                        if i > 0 {
                            assert(vs[i] == vs2[i - 1]);
                        }
                    }
                },
                _ => {},
            },
            _ => {},
        }
    }
}

// ------------------------------------------------------------------ 源の安全性（燃料で帰納）

/// 源の式の安全性：写しに型が付き、環境が型の文脈に適合すれば、源の式はどの燃料でも行き詰まらない。
/// 帰納の順は (n, 1)。形ごとの補題と列の補題は (n, 0)。
pub proof fn xsafe(
    xp: XProg,
    p: Prog,
    rw: spec_fn(XExpr) -> Expr,
    n: nat,
    r: nat,
    ctx: Map<nat, Ty>,
    env: Map<nat, Val>,
    e: XExpr,
)
    requires
        sim_ok(xp, p, rw),
        hof_shapes(rw),
        wf(p),
        env_ok(env, ctx),
        ty_expr(p, r, ctx, rw(e)) is Some,
    ensures
        xeval(xp, n, env, e) != Res::Stuck,
    decreases n, 1nat,
{
    if n > 0 {
        let f = (n - 1) as nat;
        match e {
            XExpr::Var(x) => {
                assert(rw(e) == Expr::Var(x));
                assert(ctx.contains_key(x));
            },
            XExpr::List(t, es) => {
                assert(rw(e) == Expr::List(erase_ty(t), rw_args(rw, es)));
                xsafe_args(xp, p, rw, f, r, ctx, env, es, 0);
            },
            XExpr::Some(a) => {
                assert(rw(e) == Expr::Some(Box::new(rw(*a))));
                xsafe(xp, p, rw, f, r, ctx, env, *a);
            },
            XExpr::Pair(a, b) => {
                assert(rw(e) == Expr::Pair(Box::new(rw(*a)), Box::new(rw(*b))));
                xsafe(xp, p, rw, f, r, ctx, env, *a);
                xsafe(xp, p, rw, f, r, ctx, env, *b);
            },
            XExpr::Builtin(_, _) => xsafe_builtin(xp, p, rw, n, r, ctx, env, e),
            XExpr::Call(_, _) => xsafe_call(xp, p, rw, n, r, ctx, env, e),
            XExpr::Let(_, _, _) => xsafe_let(xp, p, rw, n, r, ctx, env, e),
            XExpr::If(_, _, _) => xsafe_if(xp, p, rw, n, r, ctx, env, e),
            XExpr::Fold(_, _, _, _, _) => xsafe_fold_node(xp, p, rw, n, r, ctx, env, e),
            XExpr::Match(_, _, _, _) => xsafe_match(xp, p, rw, n, r, ctx, env, e),
            XExpr::Inj(ok, t, u, a) => {
                assert(rw(e) == Expr::Inj(ok, erase_ty(t), erase_ty(u), Box::new(rw(*a))));
                xsafe(xp, p, rw, f, r, ctx, env, *a);
            },
            XExpr::MatchR(_, _, _, _, _) => xsafe_matchr(xp, p, rw, n, r, ctx, env, e),
            XExpr::Map(_, _, _) => xsafe_map_node(xp, p, rw, n, r, ctx, env, e),
            XExpr::Filter(_, _, _) => xsafe_filter_node(xp, p, rw, n, r, ctx, env, e),
            XExpr::Any(_, _, _) => xsafe_any_node(xp, p, rw, n, r, ctx, env, e),
            XExpr::All(_, _, _) => xsafe_all_node(xp, p, rw, n, r, ctx, env, e),
            XExpr::Find(_, _, _) => xsafe_find_node(xp, p, rw, n, r, ctx, env, e),
            XExpr::SortBy(_, _, _) => xsafe_sort_node(xp, p, rw, n, r, ctx, env, e),
            _ => {},
        }
    }
}

/// 引数列 es[i..] の安全性。
pub proof fn xsafe_args(
    xp: XProg,
    p: Prog,
    rw: spec_fn(XExpr) -> Expr,
    n: nat,
    r: nat,
    ctx: Map<nat, Ty>,
    env: Map<nat, Val>,
    es: Seq<XExpr>,
    i: nat,
)
    requires
        sim_ok(xp, p, rw),
        hof_shapes(rw),
        wf(p),
        env_ok(env, ctx),
        ty_args(p, r, ctx, rw_args(rw, es), i) is Some,
    ensures
        xeval_args(xp, n, env, es, i) != ResSeq::Stuck,
    decreases n, 0nat,
{
    if n > 0 && i < es.len() {
        let f = (n - 1) as nat;
        let ces = rw_args(rw, es);
        assert(ces.len() == es.len());
        assert(ces[i as int] == rw(es[i as int]));
        assert(ty_expr(p, r, ctx, ces[i as int]) is Some && ty_args(p, r, ctx, ces, i + 1) is Some);
        xsafe(xp, p, rw, f, r, ctx, env, es[i as int]);
        xsafe_args(xp, p, rw, f, r, ctx, env, es, i + 1);
    }
}

/// 畳み込みの安全性：累積値は ta、要素は te の型を持つ。
pub proof fn xsafe_fold(
    xp: XProg,
    p: Prog,
    rw: spec_fn(XExpr) -> Expr,
    n: nat,
    r: nat,
    ctx: Map<nat, Ty>,
    env: Map<nat, Val>,
    acc: nat,
    item: nat,
    body: XExpr,
    ta: Ty,
    te: Ty,
    items: Seq<Val>,
    j: nat,
    a: Val,
)
    requires
        sim_ok(xp, p, rw),
        hof_shapes(rw),
        wf(p),
        env_ok(env, ctx),
        ty_expr(p, r, ctx.insert(acc, ta).insert(item, te), rw(body)) == Some(ta),
        val_type(a, ta),
        forall|k: int| 0 <= k < items.len() ==> val_type(#[trigger] items[k], te),
    ensures
        xeval_fold(xp, n, env, acc, item, body, items, j, a) != Res::Stuck,
    decreases n, 0nat,
{
    if n > 0 && j < items.len() {
        let f = (n - 1) as nat;
        let w = items[j as int];
        env_ok_insert(env, ctx, acc, a, ta);
        env_ok_insert(env.insert(acc, a), ctx.insert(acc, ta), item, w, te);
        let env2 = env.insert(acc, a).insert(item, w);
        let ctx2 = ctx.insert(acc, ta).insert(item, te);
        xsafe(xp, p, rw, f, r, ctx2, env2, body);
        match xeval(xp, f, env2, body) {
            Res::Done(v) => {
                xval_typed(xp, p, rw, f, r, ctx2, env2, body, v);
                xsafe_fold(xp, p, rw, f, r, ctx, env, acc, item, body, ta, te, items, j + 1, v);
            },
            _ => {},
        }
    }
}

/// map の列の安全性。
pub proof fn xsafe_xmap(
    xp: XProg,
    p: Prog,
    rw: spec_fn(XExpr) -> Expr,
    n: nat,
    r: nat,
    ctx: Map<nat, Ty>,
    env: Map<nat, Val>,
    x: nat,
    c: XExpr,
    s: Ty,
    items: Seq<Val>,
    j: nat,
)
    requires
        sim_ok(xp, p, rw),
        hof_shapes(rw),
        wf(p),
        env_ok(env, ctx),
        ty_expr(p, r, ctx.insert(x, s), rw(c)) is Some,
        forall|k: int| 0 <= k < items.len() ==> val_type(#[trigger] items[k], s),
    ensures
        xmap(xp, n, env, x, c, items, j) != ResSeq::Stuck,
    decreases n, 0nat,
{
    if n > 0 && j < items.len() {
        let f = (n - 1) as nat;
        env_ok_insert(env, ctx, x, items[j as int], s);
        xsafe(xp, p, rw, f, r, ctx.insert(x, s), env.insert(x, items[j as int]), c);
        xsafe_xmap(xp, p, rw, f, r, ctx, env, x, c, s, items, j + 1);
    }
}

/// filter の列の安全性：述語は Bool の型を持つので、値は真偽。
pub proof fn xsafe_xfilter(
    xp: XProg,
    p: Prog,
    rw: spec_fn(XExpr) -> Expr,
    n: nat,
    r: nat,
    ctx: Map<nat, Ty>,
    env: Map<nat, Val>,
    x: nat,
    c: XExpr,
    s: Ty,
    items: Seq<Val>,
    j: nat,
)
    requires
        sim_ok(xp, p, rw),
        hof_shapes(rw),
        wf(p),
        env_ok(env, ctx),
        ty_expr(p, r, ctx.insert(x, s), rw(c)) == Some(Ty::Bool),
        forall|k: int| 0 <= k < items.len() ==> val_type(#[trigger] items[k], s),
    ensures
        xfilter(xp, n, env, x, c, items, j) != ResSeq::Stuck,
    decreases n, 0nat,
{
    if n > 0 && j < items.len() {
        let f = (n - 1) as nat;
        let env2 = env.insert(x, items[j as int]);
        env_ok_insert(env, ctx, x, items[j as int], s);
        xsafe(xp, p, rw, f, r, ctx.insert(x, s), env2, c);
        xsafe_xfilter(xp, p, rw, f, r, ctx, env, x, c, s, items, j + 1);
        match xeval(xp, f, env2, c) {
            Res::Done(v) => {
                xval_typed(xp, p, rw, f, r, ctx.insert(x, s), env2, c, v);
                bool_of_ty(v);
            },
            _ => {},
        }
    }
}

/// any の列の安全性。
pub proof fn xsafe_xany(
    xp: XProg,
    p: Prog,
    rw: spec_fn(XExpr) -> Expr,
    n: nat,
    r: nat,
    ctx: Map<nat, Ty>,
    env: Map<nat, Val>,
    x: nat,
    c: XExpr,
    s: Ty,
    items: Seq<Val>,
    j: nat,
)
    requires
        sim_ok(xp, p, rw),
        hof_shapes(rw),
        wf(p),
        env_ok(env, ctx),
        ty_expr(p, r, ctx.insert(x, s), rw(c)) == Some(Ty::Bool),
        forall|k: int| 0 <= k < items.len() ==> val_type(#[trigger] items[k], s),
    ensures
        xany(xp, n, env, x, c, items, j) != Res::Stuck,
    decreases n, 0nat,
{
    if n > 0 && j < items.len() {
        let f = (n - 1) as nat;
        let env2 = env.insert(x, items[j as int]);
        env_ok_insert(env, ctx, x, items[j as int], s);
        xsafe(xp, p, rw, f, r, ctx.insert(x, s), env2, c);
        xsafe_xany(xp, p, rw, f, r, ctx, env, x, c, s, items, j + 1);
        match xeval(xp, f, env2, c) {
            Res::Done(v) => {
                xval_typed(xp, p, rw, f, r, ctx.insert(x, s), env2, c, v);
                bool_of_ty(v);
            },
            _ => {},
        }
    }
}

/// all の列の安全性。
pub proof fn xsafe_xall(
    xp: XProg,
    p: Prog,
    rw: spec_fn(XExpr) -> Expr,
    n: nat,
    r: nat,
    ctx: Map<nat, Ty>,
    env: Map<nat, Val>,
    x: nat,
    c: XExpr,
    s: Ty,
    items: Seq<Val>,
    j: nat,
)
    requires
        sim_ok(xp, p, rw),
        hof_shapes(rw),
        wf(p),
        env_ok(env, ctx),
        ty_expr(p, r, ctx.insert(x, s), rw(c)) == Some(Ty::Bool),
        forall|k: int| 0 <= k < items.len() ==> val_type(#[trigger] items[k], s),
    ensures
        xall(xp, n, env, x, c, items, j) != Res::Stuck,
    decreases n, 0nat,
{
    if n > 0 && j < items.len() {
        let f = (n - 1) as nat;
        let env2 = env.insert(x, items[j as int]);
        env_ok_insert(env, ctx, x, items[j as int], s);
        xsafe(xp, p, rw, f, r, ctx.insert(x, s), env2, c);
        xsafe_xall(xp, p, rw, f, r, ctx, env, x, c, s, items, j + 1);
        match xeval(xp, f, env2, c) {
            Res::Done(v) => {
                xval_typed(xp, p, rw, f, r, ctx.insert(x, s), env2, c, v);
                bool_of_ty(v);
            },
            _ => {},
        }
    }
}

/// find の列の安全性。
pub proof fn xsafe_xfind(
    xp: XProg,
    p: Prog,
    rw: spec_fn(XExpr) -> Expr,
    n: nat,
    r: nat,
    ctx: Map<nat, Ty>,
    env: Map<nat, Val>,
    x: nat,
    c: XExpr,
    s: Ty,
    items: Seq<Val>,
    j: nat,
)
    requires
        sim_ok(xp, p, rw),
        hof_shapes(rw),
        wf(p),
        env_ok(env, ctx),
        ty_expr(p, r, ctx.insert(x, s), rw(c)) == Some(Ty::Bool),
        forall|k: int| 0 <= k < items.len() ==> val_type(#[trigger] items[k], s),
    ensures
        xfind(xp, n, env, x, c, items, j) != Res::Stuck,
    decreases n, 0nat,
{
    if n > 0 && j < items.len() {
        let f = (n - 1) as nat;
        let env2 = env.insert(x, items[j as int]);
        env_ok_insert(env, ctx, x, items[j as int], s);
        xsafe(xp, p, rw, f, r, ctx.insert(x, s), env2, c);
        xsafe_xfind(xp, p, rw, f, r, ctx, env, x, c, s, items, j + 1);
        match xeval(xp, f, env2, c) {
            Res::Done(v) => {
                xval_typed(xp, p, rw, f, r, ctx.insert(x, s), env2, c, v);
                bool_of_ty(v);
            },
            _ => {},
        }
    }
}

// 形ごとの安全性（帰納の順は (n, 0)）。

pub proof fn xsafe_builtin(
    xp: XProg,
    p: Prog,
    rw: spec_fn(XExpr) -> Expr,
    n: nat,
    r: nat,
    ctx: Map<nat, Ty>,
    env: Map<nat, Val>,
    e: XExpr,
)
    requires
        sim_ok(xp, p, rw),
        hof_shapes(rw),
        wf(p),
        env_ok(env, ctx),
        ty_expr(p, r, ctx, rw(e)) is Some,
        e is Builtin,
        n > 0,
    ensures
        xeval(xp, n, env, e) != Res::Stuck,
    decreases n, 0nat,
{
    let f = (n - 1) as nat;
    match e {
        XExpr::Builtin(bi, es) => {
            let ces = rw_args(rw, es);
            assert(rw(e) == Expr::Builtin(bi, ces));
            assert(ty_args(p, r, ctx, ces, 0) is Some);
            let ts = ty_args(p, r, ctx, ces, 0)->Some_0;
            assert(builtin_type(bi, ts) is Some);
            xsafe_args(xp, p, rw, f, r, ctx, env, es, 0);
            match xeval_args(xp, f, env, es, 0) {
                ResSeq::Done(vs) => {
                    xargs_typed(xp, p, rw, f, r, ctx, env, es, vs);
                    apply_sound(bi, ts, vs);
                },
                _ => {},
            }
        },
        _ => {},
    }
}

pub proof fn xsafe_call(
    xp: XProg,
    p: Prog,
    rw: spec_fn(XExpr) -> Expr,
    n: nat,
    r: nat,
    ctx: Map<nat, Ty>,
    env: Map<nat, Val>,
    e: XExpr,
)
    requires
        sim_ok(xp, p, rw),
        hof_shapes(rw),
        wf(p),
        env_ok(env, ctx),
        ty_expr(p, r, ctx, rw(e)) is Some,
        e is Call,
        n > 0,
    ensures
        xeval(xp, n, env, e) != Res::Stuck,
    decreases n, 0nat,
{
    let f = (n - 1) as nat;
    match e {
        XExpr::Call(g, es) => {
            let ces = rw_args(rw, es);
            assert(rw(e) == Expr::Call(g, ces));
            assert(ty_args(p, r, ctx, ces, 0) is Some);
            let ts = ty_args(p, r, ctx, ces, 0)->Some_0;
            xsafe_args(xp, p, rw, f, r, ctx, env, es, 0);
            match xeval_args(xp, f, env, es, 0) {
                ResSeq::Done(vs) => {
                    xargs_typed(xp, p, rw, f, r, ctx, env, es, vs);
                    assert(g < p.funcs.len() && ts.len() == p.funcs[g as int].params.len());
                    assert(forall|k: int| 0 <= k < ts.len() ==> #[trigger] ts[k] == p.funcs[g as int].params[k].1);
                    assert(p.funcs.len() == xp.funcs.len());
                    assert(erase_sig(xp.funcs[g as int], p.funcs[g as int]));
                    let fp = p.funcs[g as int];
                    let fx = xp.funcs[g as int];
                    assert(vs.len() == fx.params.len());
                    assert forall|k: int| 0 <= k < vs.len() implies val_type(#[trigger] vs[k], fp.params[k].1) by {
                        assert(ts[k] == fp.params[k].1);
                    }
                    bind_ok(fp.params, vs, vs.len());
                    bind_names_eq6(fp.params, fx.params, vs, vs.len());
                    assert(ty_expr(
                        p,
                        p.rank[g as int],
                        param_ctx(p.funcs[g as int].params, p.funcs[g as int].params.len()),
                        p.funcs[g as int].body,
                    ) == Some(p.funcs[g as int].ret));
                    assert(p.funcs[g as int].body == rw(xp.funcs[g as int].body));
                    xsafe(
                        xp,
                        p,
                        rw,
                        f,
                        p.rank[g as int],
                        param_ctx(fp.params, fp.params.len()),
                        bind(fx.params, vs, vs.len()),
                        fx.body,
                    );
                },
                _ => {},
            }
        },
        _ => {},
    }
}

pub proof fn xsafe_let(
    xp: XProg,
    p: Prog,
    rw: spec_fn(XExpr) -> Expr,
    n: nat,
    r: nat,
    ctx: Map<nat, Ty>,
    env: Map<nat, Val>,
    e: XExpr,
)
    requires
        sim_ok(xp, p, rw),
        hof_shapes(rw),
        wf(p),
        env_ok(env, ctx),
        ty_expr(p, r, ctx, rw(e)) is Some,
        e is Let,
        n > 0,
    ensures
        xeval(xp, n, env, e) != Res::Stuck,
    decreases n, 0nat,
{
    let f = (n - 1) as nat;
    match e {
        XExpr::Let(x, a, b) => {
            assert(rw(e) == Expr::Let(x, Box::new(rw(*a)), Box::new(rw(*b))));
            ty_let_inv(p, r, ctx, x, rw(*a), rw(*b));
            let ta = ty_expr(p, r, ctx, rw(*a))->Some_0;
            xsafe(xp, p, rw, f, r, ctx, env, *a);
            match xeval(xp, f, env, *a) {
                Res::Done(va) => {
                    xval_typed(xp, p, rw, f, r, ctx, env, *a, va);
                    env_ok_insert(env, ctx, x, va, ta);
                    xsafe(xp, p, rw, f, r, ctx.insert(x, ta), env.insert(x, va), *b);
                },
                _ => {},
            }
        },
        _ => {},
    }
}

pub proof fn xsafe_if(
    xp: XProg,
    p: Prog,
    rw: spec_fn(XExpr) -> Expr,
    n: nat,
    r: nat,
    ctx: Map<nat, Ty>,
    env: Map<nat, Val>,
    e: XExpr,
)
    requires
        sim_ok(xp, p, rw),
        hof_shapes(rw),
        wf(p),
        env_ok(env, ctx),
        ty_expr(p, r, ctx, rw(e)) is Some,
        e is If,
        n > 0,
    ensures
        xeval(xp, n, env, e) != Res::Stuck,
    decreases n, 0nat,
{
    let f = (n - 1) as nat;
    match e {
        XExpr::If(c, a, b) => {
            assert(rw(e) == Expr::If(Box::new(rw(*c)), Box::new(rw(*a)), Box::new(rw(*b))));
            ty_if_inv(p, r, ctx, rw(*c), rw(*a), rw(*b));
            xsafe(xp, p, rw, f, r, ctx, env, *c);
            match xeval(xp, f, env, *c) {
                Res::Done(vc) => {
                    xval_typed(xp, p, rw, f, r, ctx, env, *c, vc);
                    bool_of_ty(vc);
                    xsafe(xp, p, rw, f, r, ctx, env, *a);
                    xsafe(xp, p, rw, f, r, ctx, env, *b);
                },
                _ => {},
            }
        },
        _ => {},
    }
}

pub proof fn xsafe_fold_node(
    xp: XProg,
    p: Prog,
    rw: spec_fn(XExpr) -> Expr,
    n: nat,
    r: nat,
    ctx: Map<nat, Ty>,
    env: Map<nat, Val>,
    e: XExpr,
)
    requires
        sim_ok(xp, p, rw),
        hof_shapes(rw),
        wf(p),
        env_ok(env, ctx),
        ty_expr(p, r, ctx, rw(e)) is Some,
        e is Fold,
        n > 0,
    ensures
        xeval(xp, n, env, e) != Res::Stuck,
    decreases n, 0nat,
{
    let f = (n - 1) as nat;
    match e {
        XExpr::Fold(xs, init, acc, item, body) => {
            assert(rw(e) == Expr::Fold(Box::new(rw(*xs)), Box::new(rw(*init)), acc, item, Box::new(rw(*body))));
            let (te, ta) = ty_fold_inv(p, r, ctx, rw(*xs), rw(*init), acc, item, rw(*body));
            xsafe(xp, p, rw, f, r, ctx, env, *xs);
            match xeval(xp, f, env, *xs) {
                Res::Done(vx) => {
                    xval_typed(xp, p, rw, f, r, ctx, env, *xs, vx);
                    list_of_ty(vx, te);
                    xsafe(xp, p, rw, f, r, ctx, env, *init);
                    match xeval(xp, f, env, *init) {
                        Res::Done(v0) => {
                            xval_typed(xp, p, rw, f, r, ctx, env, *init, v0);
                            xsafe_fold(xp, p, rw, f, r, ctx, env, acc, item, *body, ta, te, vx->List_0, 0, v0);
                        },
                        _ => {},
                    }
                },
                _ => {},
            }
        },
        _ => {},
    }
}

pub proof fn xsafe_match(
    xp: XProg,
    p: Prog,
    rw: spec_fn(XExpr) -> Expr,
    n: nat,
    r: nat,
    ctx: Map<nat, Ty>,
    env: Map<nat, Val>,
    e: XExpr,
)
    requires
        sim_ok(xp, p, rw),
        hof_shapes(rw),
        wf(p),
        env_ok(env, ctx),
        ty_expr(p, r, ctx, rw(e)) is Some,
        e is Match,
        n > 0,
    ensures
        xeval(xp, n, env, e) != Res::Stuck,
    decreases n, 0nat,
{
    let f = (n - 1) as nat;
    match e {
        XExpr::Match(m, nb, x, sm) => {
            assert(rw(e) == Expr::Match(Box::new(rw(*m)), Box::new(rw(*nb)), x, Box::new(rw(*sm))));
            let te = ty_match_inv(p, r, ctx, rw(*m), rw(*nb), x, rw(*sm));
            xsafe(xp, p, rw, f, r, ctx, env, *m);
            match xeval(xp, f, env, *m) {
                Res::Done(vm) => {
                    xval_typed(xp, p, rw, f, r, ctx, env, *m, vm);
                    opt_of_ty(vm, te);
                    xsafe(xp, p, rw, f, r, ctx, env, *nb);
                    if vm is Some {
                        env_ok_insert(env, ctx, x, *vm->Some_0, te);
                        xsafe(xp, p, rw, f, r, ctx.insert(x, te), env.insert(x, *vm->Some_0), *sm);
                    }
                },
                _ => {},
            }
        },
        _ => {},
    }
}

pub proof fn xsafe_matchr(
    xp: XProg,
    p: Prog,
    rw: spec_fn(XExpr) -> Expr,
    n: nat,
    r: nat,
    ctx: Map<nat, Ty>,
    env: Map<nat, Val>,
    e: XExpr,
)
    requires
        sim_ok(xp, p, rw),
        hof_shapes(rw),
        wf(p),
        env_ok(env, ctx),
        ty_expr(p, r, ctx, rw(e)) is Some,
        e is MatchR,
        n > 0,
    ensures
        xeval(xp, n, env, e) != Res::Stuck,
    decreases n, 0nat,
{
    let f = (n - 1) as nat;
    match e {
        XExpr::MatchR(m, x, a, y, b) => {
            assert(rw(e) == Expr::MatchR(Box::new(rw(*m)), x, Box::new(rw(*a)), y, Box::new(rw(*b))));
            let (tl, tr) = ty_matchr_inv(p, r, ctx, rw(*m), x, rw(*a), y, rw(*b));
            xsafe(xp, p, rw, f, r, ctx, env, *m);
            match xeval(xp, f, env, *m) {
                Res::Done(vm) => {
                    xval_typed(xp, p, rw, f, r, ctx, env, *m, vm);
                    res_of_ty(vm, tl, tr);
                    if vm is Ok {
                        env_ok_insert(env, ctx, x, *vm->Ok_0, tl);
                        xsafe(xp, p, rw, f, r, ctx.insert(x, tl), env.insert(x, *vm->Ok_0), *a);
                    } else {
                        env_ok_insert(env, ctx, y, *vm->Err_0, tr);
                        xsafe(xp, p, rw, f, r, ctx.insert(y, tr), env.insert(y, *vm->Err_0), *b);
                    }
                },
                _ => {},
            }
        },
        _ => {},
    }
}

pub proof fn xsafe_map_node(
    xp: XProg,
    p: Prog,
    rw: spec_fn(XExpr) -> Expr,
    n: nat,
    r: nat,
    ctx: Map<nat, Ty>,
    env: Map<nat, Val>,
    e: XExpr,
)
    requires
        sim_ok(xp, p, rw),
        hof_shapes(rw),
        wf(p),
        env_ok(env, ctx),
        ty_expr(p, r, ctx, rw(e)) is Some,
        e is Map,
        n > 0,
    ensures
        xeval(xp, n, env, e) != Res::Stuck,
    decreases n, 0nat,
{
    let f = (n - 1) as nat;
    match e {
        XExpr::Map(xs, x, c) => {
            let (t, acc) = map_names(rw, *xs, x, *c);
            let s = map_inv(p, r, ctx, rw(*xs), t, acc, x, rw(*c));
            xsafe(xp, p, rw, f, r, ctx, env, *xs);
            match xeval(xp, f, env, *xs) {
                Res::Done(vx) => {
                    xval_typed(xp, p, rw, f, r, ctx, env, *xs, vx);
                    list_of_ty(vx, s);
                    xsafe_xmap(xp, p, rw, f, r, ctx, env, x, *c, s, vx->List_0, 0);
                },
                _ => {},
            }
        },
        _ => {},
    }
}

pub proof fn xsafe_filter_node(
    xp: XProg,
    p: Prog,
    rw: spec_fn(XExpr) -> Expr,
    n: nat,
    r: nat,
    ctx: Map<nat, Ty>,
    env: Map<nat, Val>,
    e: XExpr,
)
    requires
        sim_ok(xp, p, rw),
        hof_shapes(rw),
        wf(p),
        env_ok(env, ctx),
        ty_expr(p, r, ctx, rw(e)) is Some,
        e is Filter,
        n > 0,
    ensures
        xeval(xp, n, env, e) != Res::Stuck,
    decreases n, 0nat,
{
    let f = (n - 1) as nat;
    match e {
        XExpr::Filter(xs, x, c) => {
            let (t, acc) = filter_names(rw, *xs, x, *c);
            let s = filter_inv(p, r, ctx, rw(*xs), t, acc, x, rw(*c));
            xsafe(xp, p, rw, f, r, ctx, env, *xs);
            match xeval(xp, f, env, *xs) {
                Res::Done(vx) => {
                    xval_typed(xp, p, rw, f, r, ctx, env, *xs, vx);
                    list_of_ty(vx, s);
                    xsafe_xfilter(xp, p, rw, f, r, ctx, env, x, *c, s, vx->List_0, 0);
                },
                _ => {},
            }
        },
        _ => {},
    }
}

pub proof fn xsafe_any_node(
    xp: XProg,
    p: Prog,
    rw: spec_fn(XExpr) -> Expr,
    n: nat,
    r: nat,
    ctx: Map<nat, Ty>,
    env: Map<nat, Val>,
    e: XExpr,
)
    requires
        sim_ok(xp, p, rw),
        hof_shapes(rw),
        wf(p),
        env_ok(env, ctx),
        ty_expr(p, r, ctx, rw(e)) is Some,
        e is Any,
        n > 0,
    ensures
        xeval(xp, n, env, e) != Res::Stuck,
    decreases n, 0nat,
{
    let f = (n - 1) as nat;
    match e {
        XExpr::Any(xs, x, c) => {
            let acc = any_names(rw, *xs, x, *c);
            let s = any_inv(p, r, ctx, rw(*xs), acc, x, rw(*c));
            xsafe(xp, p, rw, f, r, ctx, env, *xs);
            match xeval(xp, f, env, *xs) {
                Res::Done(vx) => {
                    xval_typed(xp, p, rw, f, r, ctx, env, *xs, vx);
                    list_of_ty(vx, s);
                    xsafe_xany(xp, p, rw, f, r, ctx, env, x, *c, s, vx->List_0, 0);
                },
                _ => {},
            }
        },
        _ => {},
    }
}

pub proof fn xsafe_all_node(
    xp: XProg,
    p: Prog,
    rw: spec_fn(XExpr) -> Expr,
    n: nat,
    r: nat,
    ctx: Map<nat, Ty>,
    env: Map<nat, Val>,
    e: XExpr,
)
    requires
        sim_ok(xp, p, rw),
        hof_shapes(rw),
        wf(p),
        env_ok(env, ctx),
        ty_expr(p, r, ctx, rw(e)) is Some,
        e is All,
        n > 0,
    ensures
        xeval(xp, n, env, e) != Res::Stuck,
    decreases n, 0nat,
{
    let f = (n - 1) as nat;
    match e {
        XExpr::All(xs, x, c) => {
            let acc = all_names(rw, *xs, x, *c);
            let s = all_inv(p, r, ctx, rw(*xs), acc, x, rw(*c));
            xsafe(xp, p, rw, f, r, ctx, env, *xs);
            match xeval(xp, f, env, *xs) {
                Res::Done(vx) => {
                    xval_typed(xp, p, rw, f, r, ctx, env, *xs, vx);
                    list_of_ty(vx, s);
                    xsafe_xall(xp, p, rw, f, r, ctx, env, x, *c, s, vx->List_0, 0);
                },
                _ => {},
            }
        },
        _ => {},
    }
}

pub proof fn xsafe_find_node(
    xp: XProg,
    p: Prog,
    rw: spec_fn(XExpr) -> Expr,
    n: nat,
    r: nat,
    ctx: Map<nat, Ty>,
    env: Map<nat, Val>,
    e: XExpr,
)
    requires
        sim_ok(xp, p, rw),
        hof_shapes(rw),
        wf(p),
        env_ok(env, ctx),
        ty_expr(p, r, ctx, rw(e)) is Some,
        e is Find,
        n > 0,
    ensures
        xeval(xp, n, env, e) != Res::Stuck,
    decreases n, 0nat,
{
    let f = (n - 1) as nat;
    match e {
        XExpr::Find(xs, x, c) => {
            let (t, acc, y) = find_names(rw, *xs, x, *c);
            let s = find_inv(p, r, ctx, rw(*xs), t, acc, x, rw(*c), y);
            xsafe(xp, p, rw, f, r, ctx, env, *xs);
            match xeval(xp, f, env, *xs) {
                Res::Done(vx) => {
                    xval_typed(xp, p, rw, f, r, ctx, env, *xs, vx);
                    list_of_ty(vx, s);
                    xsafe_xfind(xp, p, rw, f, r, ctx, env, x, *c, s, vx->List_0, 0);
                },
                _ => {},
            }
        },
        _ => {},
    }
}

pub proof fn xsafe_sort_node(
    xp: XProg,
    p: Prog,
    rw: spec_fn(XExpr) -> Expr,
    n: nat,
    r: nat,
    ctx: Map<nat, Ty>,
    env: Map<nat, Val>,
    e: XExpr,
)
    requires
        sim_ok(xp, p, rw),
        hof_shapes(rw),
        wf(p),
        env_ok(env, ctx),
        ty_expr(p, r, ctx, rw(e)) is Some,
        e is SortBy,
        n > 0,
    ensures
        xeval(xp, n, env, e) != Res::Stuck,
    decreases n, 0nat,
{
    let f = (n - 1) as nat;
    match e {
        XExpr::SortBy(xs, x, k) => {
            let (t, acc, e2, st, y, ky, ke, rb) = sort_names(rw, *xs, x, *k);
            let s = sort_inv(p, r, ctx, rw(*xs), t, acc, e2, st, y, ky, ke, rb, x, rw(*k));
            xsafe(xp, p, rw, f, r, ctx, env, *xs);
            match xeval(xp, f, env, *xs) {
                Res::Done(vx) => {
                    xval_typed(xp, p, rw, f, r, ctx, env, *xs, vx);
                    list_of_ty(vx, s);
                    let items = vx->List_0;
                    xsafe_xmap(xp, p, rw, f, r, ctx, env, x, *k, s, items, 0);
                    match xmap(xp, f, env, x, *k, items, 0) {
                        ResSeq::Done(kv) => {
                            xmap_typed(xp, p, rw, f, r, ctx, env, x, *k, s, Ty::Int, items, 0, kv);
                            assert forall|i: int| 0 <= i < kv.len() implies int_of_val(#[trigger] kv[i]) is Some by {
                                int_of_ty(kv[i]);
                            }
                            assert(int_seq(kv) is Some);
                        },
                        _ => {},
                    }
                },
                _ => {},
            }
        },
        _ => {},
    }
}

// ------------------------------------------------------------------ 主の定理

/// SH6 の源の安全性：書換え後のプログラムが整形式（wf）で、入力が entry の引数の型を持つなら、源の entry は
/// どの燃料でも行き詰まらない（any・all・sort_by を含むプログラムでも）。
pub proof fn sh6_source_safe(xp: XProg, p: Prog, rw: spec_fn(XExpr) -> Expr, n: nat, v: Val)
    requires
        sim_prog(xp, p, rw),
        homomorphic(rw),
        hof_shapes(rw),
        wf(p),
        val_type(v, p.funcs[p.entry as int].params[0].1),
    ensures
        xp.entry < xp.funcs.len(),
        xeval_entry(xp, n, v) != Res::Stuck,
{
    sh6_sim_ok(xp, p, rw);
    assert(xp.entry < xp.funcs.len());
    let fx = xp.funcs[xp.entry as int];
    let fp = p.funcs[p.entry as int];
    assert(erase_sig(xp.funcs[xp.entry as int], p.funcs[p.entry as int]));
    bind_names_eq6(fp.params, fx.params, seq![v], 1);
    let vs = seq![v];
    assert forall|k: int| 0 <= k < 1 implies val_type(#[trigger] vs[k], fp.params[k].1) by {
        assert(k == 0);
    }
    bind_ok(fp.params, vs, 1);
    assert(ty_expr(
        p,
        p.rank[p.entry as int],
        param_ctx(p.funcs[p.entry as int].params, p.funcs[p.entry as int].params.len()),
        p.funcs[p.entry as int].body,
    ) == Some(p.funcs[p.entry as int].ret));
    assert(fp.body == rw(fx.body));
    xsafe(xp, p, rw, n, p.rank[p.entry as int], param_ctx(fp.params, 1), bind(fx.params, vs, 1), fx.body);
}

/// SH6 の結果の一致：sh4_same_result の行き詰まりの場合を広げたもの。源の entry が燃料 n で結果 r（Done か Stuck）を
/// 返すなら、書換え後の entry も r を返し（燃料の存在）、非 OutOfFuel の結果はすべて r に等しい。Stuck の場合は、
/// any・all・sort_by を含まないプログラム（SH4）か、書換え後のプログラムが整形式で入力が型を持つ場合
/// （このとき源は行き詰まらない。sh6_source_safe）。
pub proof fn sh6_same_result(xp: XProg, p: Prog, rw: spec_fn(XExpr) -> Expr, n: nat, v: Val, r: Res)
    requires
        sim_prog(xp, p, rw),
        homomorphic(rw),
        hof_shapes(rw),
        xp.entry < xp.funcs.len(),
        xeval_entry(xp, n, v) == r,
        r is Done || r is Stuck,
        r is Stuck ==> no_open_hof_prog(xp) || (wf(p) && val_type(v, p.funcs[p.entry as int].params[0].1)),
    ensures
        exists|m: nat| #[trigger] eval_entry(p, m, v) == r,
        forall|m: nat| !(#[trigger] eval_entry(p, m, v) is OutOfFuel) ==> eval_entry(p, m, v) == r,
{
    sh6_sim_ok(xp, p, rw);
    if r is Stuck && !no_open_hof_prog(xp) {
        sh6_source_safe(xp, p, rw, n, v);
        assert(false);
    } else {
        sh4_same_result(xp, p, rw, n, v, r);
    }
}

/// 型の付いたプログラムでの一致：書換え後のプログラムが整形式で入力が型を持つなら、源の entry の OutOfFuel でない
/// 結果は値で、書換え後の entry もその値を返す（燃料の存在）。書換え後の非 OutOfFuel の結果はすべてその値。
pub proof fn sh6_typed_same(xp: XProg, p: Prog, rw: spec_fn(XExpr) -> Expr, n: nat, v: Val)
    requires
        sim_prog(xp, p, rw),
        homomorphic(rw),
        hof_shapes(rw),
        wf(p),
        val_type(v, p.funcs[p.entry as int].params[0].1),
        !(xeval_entry(xp, n, v) is OutOfFuel),
    ensures
        xeval_entry(xp, n, v) is Done,
        exists|m: nat| #[trigger] eval_entry(p, m, v) == xeval_entry(xp, n, v),
        forall|m: nat| !(#[trigger] eval_entry(p, m, v) is OutOfFuel) ==> eval_entry(p, m, v) == xeval_entry(xp, n, v),
{
    sh6_source_safe(xp, p, rw, n, v);
    sh6_same_result(xp, p, rw, n, v, xeval_entry(xp, n, v));
}

} // verus!
