//! 辞書の操作の書換えの型と、HofTypes の項目の一致（SH1）。
//!
//! dict.rs の `Lower::dict_op` の書換え（九つの操作と、dict_put・dict_from が使う `put`）を核の式に写し
//! （`dict_rw`）、表の項目 (K, V) を注釈（`list<K>()`、`list<V>()`、`none<V>()`、`list<Pair<K, V>>()`）に入れた
//! 書換えが、核の型付け `ty_expr` で形の型（checker.rs の `call` の辞書の腕が返す型）の消去を持つことを示す
//! （`dict_rw_agrees`）。辞書の操作の形は源の型付け `ty_x` にないので、一致はこの書換えの型で述べる。
//! 写しの形と名前の順は crates/tlvm/tests/hof_types.rs で Rust の書換えの出力と一字ずつ比べる。

use crate::hof_agree::*;
use crate::hof_types::*;
use crate::input::*;
use crate::loop_types::*;
use crate::records_proof::*;
use crate::sortmeaning::*;
use crate::spec::*;
use crate::xtyping::*;
use vstd::prelude::*;

verus! {

// ------------------------------------------------------------------ 式と型の部品

pub open spec fn un_e(b: Builtin, a: Expr) -> Expr {
    Expr::Builtin(b, seq![a])
}

/// 辞書の要素の型 Pair<K, V>。
pub open spec fn en_ty(k: Ty, v: Ty) -> Ty {
    Ty::Pair(Box::new(k), Box::new(v))
}

/// 消去した辞書の型 List<Pair<K, V>>。
pub open spec fn dl_ty(k: Ty, v: Ty) -> Ty {
    Ty::List(Box::new(en_ty(k, v)))
}

/// PUT の走査の状態の型 Pair<List<Pair<K, V>>, Bool>（書き出した列（逆順）と、鍵があったか）。
pub open spec fn put_st(k: Ty, v: Ty) -> Ty {
    Ty::Pair(Box::new(dl_ty(k, v)), Box::new(Ty::Bool))
}

/// eq の型：二つの引数が同じ型なら Bool。
pub proof fn t_eq(p: Prog, r: nat, ctx: Map<nat, Ty>, a1: Expr, a2: Expr, t: Ty)
    requires
        ty_expr(p, r, ctx, a1) == Some(t),
        ty_expr(p, r, ctx, a2) == Some(t),
    ensures
        ty_expr(p, r, ctx, bin_e(Builtin::Eq, a1, a2)) == Some(Ty::Bool),
{
    let ts = seq![t, t];
    assert(ts.len() == 2 && ts[0] == t && ts[1] == t);
    t_bin(p, r, ctx, Builtin::Eq, a1, a2, t, t, Ty::Bool);
}

/// reverse と length の型：列の型 List<T> の式なら、reverse は List<T>、length は Int。
pub proof fn t_list1(p: Prog, r: nat, ctx: Map<nat, Ty>, a: Expr, t: Ty)
    requires
        ty_expr(p, r, ctx, a) == Some(Ty::List(Box::new(t))),
    ensures
        ty_expr(p, r, ctx, un_e(Builtin::Reverse, a)) == Some(Ty::List(Box::new(t))),
        ty_expr(p, r, ctx, un_e(Builtin::Length, a)) == Some(Ty::Int),
{
    let lt = Ty::List(Box::new(t));
    assert(seq![lt].len() == 1 && seq![lt][0] == lt);
    t_un(p, r, ctx, Builtin::Reverse, a, lt, lt);
    t_un(p, r, ctx, Builtin::Length, a, lt, Ty::Int);
}

// ------------------------------------------------------------------ 書換えの写し（dict.rs の Lower::dict_op）

/// PUT(d, kk, vv)（dict.rs の `put`。en は注釈の要素の型、rn・acc・e は `fresh` の順の名前）：
/// let r = fold(d, pair(list<E>(), false), |acc, e| if(eq(fst(e), kk), pair(cons(pair(kk, vv), fst(acc)), true),
/// pair(cons(e, fst(acc)), snd(acc)))) in reverse(if(snd(r), fst(r), cons(pair(kk, vv), fst(r))))。
pub open spec fn put_rw(d: Expr, kk: nat, vv: nat, en: Ty, rn: nat, acc: nat, e: nat) -> Expr {
    let new = pair_e(var_e(kk), var_e(vv));
    let same = bin_e(Builtin::Eq, pfst(var_e(e)), var_e(kk));
    let replaced = pair_e(cons_e(new, pfst(var_e(acc))), Expr::Bool(true));
    let kept = pair_e(cons_e(var_e(e), pfst(var_e(acc))), psnd(var_e(acc)));
    let scan = fold_e(d, pair_e(Expr::List(en, Seq::empty()), Expr::Bool(false)), acc, e, if_e(same, replaced, kept));
    let done = un_e(Builtin::Reverse, if_e(psnd(var_e(rn)), pfst(var_e(rn)), cons_e(new, pfst(var_e(rn)))));
    let_e(rn, scan, done)
}

/// dict_get・dict_has・dict_remove の走査（dd・kk は辞書と鍵を束縛した名前、acc・e は fold の名前）：
/// get は fold(dd, none<V>(), |acc, e| if(eq(fst(e), kk), some(snd(e)), acc))、has は
/// fold(dd, false, |acc, e| if(acc, true, eq(fst(e), kk)))、remove は
/// reverse(fold(dd, list<E>(), |acc, e| if(eq(fst(e), kk), acc, cons(e, acc))))。
pub open spec fn scan_rw(op: DictOp, dd: nat, kk: nat, v: Ty, en: Ty, acc: nat, e: nat) -> Expr {
    let same = bin_e(Builtin::Eq, pfst(var_e(e)), var_e(kk));
    match op {
        DictOp::Get => fold_e(var_e(dd), Expr::None(v), acc, e, if_e(same, some_e(psnd(var_e(e))), var_e(acc))),
        DictOp::Has => fold_e(var_e(dd), Expr::Bool(false), acc, e, if_e(var_e(acc), Expr::Bool(true), same)),
        _ => un_e(
            Builtin::Reverse,
            fold_e(var_e(dd), Expr::List(en, Seq::empty()), acc, e, if_e(same, var_e(acc), cons_e(var_e(e), var_e(acc)))),
        ),
    }
}

/// 書換えが導入する名前の数（dict.rs の `fresh` の呼出しの数）。
pub open spec fn dict_names(op: DictOp) -> nat {
    match op {
        DictOp::Size | DictOp::Entries => 0,
        DictOp::Keys | DictOp::Values => 2,
        DictOp::Get | DictOp::Has | DictOp::Remove => 4,
        DictOp::Put => 6,
        DictOp::From => 7,
    }
}

/// 導入する名前は互いに異なり、どの引数にも現れない（`fresh` はプログラムのどの名前とも重ならない名前を返す）。
pub open spec fn dict_fresh(ns: Seq<nat>, args: Seq<Expr>) -> bool {
    &&& forall|i: int, j: int| 0 <= i < j < ns.len() ==> ns[i] != ns[j]
    &&& forall|i: int, j: int| 0 <= i < ns.len() && 0 <= j < args.len() ==> #[trigger] absent(ns[i], args[j])
}

/// 辞書の操作 op(args) の核の書換え（dict.rs の `dict_op`）。k、v は注釈の鍵と値の型、ns は導入する名前
/// （`fresh` の順。keys・values は acc・e、from は acc・p・kk・vv と put の r・acc・e、get・has・remove は
/// dd・kk・acc・e、put は dd・kk・vv と put の r・acc・e）。
pub open spec fn dict_rw(op: DictOp, args: Seq<Expr>, k: Ty, v: Ty, ns: Seq<nat>) -> Expr {
    let en = en_ty(k, v);
    match op {
        DictOp::Size => un_e(Builtin::Length, args[0]),
        DictOp::Entries => args[0],
        DictOp::Keys => un_e(
            Builtin::Reverse,
            fold_e(args[0], Expr::List(k, Seq::empty()), ns[0], ns[1], cons_e(pfst(var_e(ns[1])), var_e(ns[0]))),
        ),
        DictOp::Values => un_e(
            Builtin::Reverse,
            fold_e(args[0], Expr::List(v, Seq::empty()), ns[0], ns[1], cons_e(psnd(var_e(ns[1])), var_e(ns[0]))),
        ),
        DictOp::From => fold_e(
            args[0],
            Expr::List(en, Seq::empty()),
            ns[0],
            ns[1],
            let_e(
                ns[2],
                pfst(var_e(ns[1])),
                let_e(ns[3], psnd(var_e(ns[1])), put_rw(var_e(ns[0]), ns[2], ns[3], en, ns[4], ns[5], ns[6])),
            ),
        ),
        DictOp::Put => let_e(
            ns[0],
            args[0],
            let_e(ns[1], args[1], let_e(ns[2], args[2], put_rw(var_e(ns[0]), ns[1], ns[2], en, ns[3], ns[4], ns[5]))),
        ),
        _ => let_e(ns[0], args[0], let_e(ns[1], args[1], scan_rw(op, ns[0], ns[1], v, en, ns[2], ns[3]))),
    }
}

// ------------------------------------------------------------------ 書換えの型

/// PUT の型：d が List<Pair<K, V>>、kk が K、vv が V で、r・acc・e が互いに異なり kk・vv と異なれば、
/// List<Pair<K, V>>。
pub proof fn put_typing(
    p: Prog,
    r: nat,
    c: Map<nat, Ty>,
    d: Expr,
    kk: nat,
    vv: nat,
    k: Ty,
    v: Ty,
    rn: nat,
    acc: nat,
    e: nat,
)
    requires
        ty_expr(p, r, c, d) == Some(dl_ty(k, v)),
        has(c, kk, k),
        has(c, vv, v),
        rn != acc && rn != e && acc != e,
        kk != acc && kk != e && kk != rn,
        vv != acc && vv != e && vv != rn,
    ensures
        ty_expr(p, r, c, put_rw(d, kk, vv, en_ty(k, v), rn, acc, e)) == Some(dl_ty(k, v)),
{
    let en = en_ty(k, v);
    let dt = dl_ty(k, v);
    let at = put_st(k, v);
    let new = pair_e(var_e(kk), var_e(vv));
    // 初期状態 pair(list<E>(), false)
    ty_nil(p, r, c, en);
    let init = pair_e(Expr::List(en, Seq::empty()), Expr::Bool(false));
    t_pair_e(p, r, c, Expr::List(en, Seq::empty()), Expr::Bool(false), dt, Ty::Bool);
    // 走査の一歩（acc は状態、e は要素）
    let cb = c.insert(acc, at).insert(e, en);
    t_var(p, r, cb, e, en);
    t_proj(p, r, cb, var_e(e), k, v);
    t_var(p, r, cb, kk, k);
    t_eq(p, r, cb, pfst(var_e(e)), var_e(kk), k);
    t_var(p, r, cb, vv, v);
    t_pair_e(p, r, cb, var_e(kk), var_e(vv), k, v);
    t_var(p, r, cb, acc, at);
    t_proj(p, r, cb, var_e(acc), dt, Ty::Bool);
    ty_cons(p, r, cb, new, pfst(var_e(acc)), en);
    t_pair_e(p, r, cb, cons_e(new, pfst(var_e(acc))), Expr::Bool(true), dt, Ty::Bool);
    ty_cons(p, r, cb, var_e(e), pfst(var_e(acc)), en);
    t_pair_e(p, r, cb, cons_e(var_e(e), pfst(var_e(acc))), psnd(var_e(acc)), dt, Ty::Bool);
    let same = bin_e(Builtin::Eq, pfst(var_e(e)), var_e(kk));
    let replaced = pair_e(cons_e(new, pfst(var_e(acc))), Expr::Bool(true));
    let kept = pair_e(cons_e(var_e(e), pfst(var_e(acc))), psnd(var_e(acc)));
    t_if(p, r, cb, same, replaced, kept, at);
    fold_typing(p, r, c, d, init, acc, e, if_e(same, replaced, kept), en, at);
    let scan = fold_e(d, init, acc, e, if_e(same, replaced, kept));
    // 走査の後（r は状態）
    let cr = c.insert(rn, at);
    t_var(p, r, cr, rn, at);
    t_proj(p, r, cr, var_e(rn), dt, Ty::Bool);
    t_var(p, r, cr, kk, k);
    t_var(p, r, cr, vv, v);
    t_pair_e(p, r, cr, var_e(kk), var_e(vv), k, v);
    ty_cons(p, r, cr, new, pfst(var_e(rn)), en);
    let fin = if_e(psnd(var_e(rn)), pfst(var_e(rn)), cons_e(new, pfst(var_e(rn))));
    t_if(p, r, cr, psnd(var_e(rn)), pfst(var_e(rn)), cons_e(new, pfst(var_e(rn))), dt);
    t_list1(p, r, cr, fin, en);
    t_let(p, r, c, rn, scan, un_e(Builtin::Reverse, fin), at, dt);
}

/// dict_get・dict_has・dict_remove の走査の結果の型：Option<V>、Bool、List<Pair<K, V>>。
pub open spec fn scan_res(op: DictOp, k: Ty, v: Ty) -> Ty {
    match op {
        DictOp::Get => Ty::Option(Box::new(v)),
        DictOp::Has => Ty::Bool,
        _ => dl_ty(k, v),
    }
}

/// 走査の型：dd が List<Pair<K, V>>、kk が K で、acc・e が互いに異なり kk と異なれば、`scan_res`。
pub proof fn scan_typing(p: Prog, r: nat, c: Map<nat, Ty>, op: DictOp, dd: nat, kk: nat, k: Ty, v: Ty, acc: nat, e: nat)
    requires
        op is Get || op is Has || op is Remove,
        has(c, dd, dl_ty(k, v)),
        has(c, kk, k),
        acc != e && kk != acc && kk != e,
    ensures
        ty_expr(p, r, c, scan_rw(op, dd, kk, v, en_ty(k, v), acc, e)) == Some(scan_res(op, k, v)),
{
    let en = en_ty(k, v);
    let dt = dl_ty(k, v);
    let rt = scan_res(op, k, v);
    let cb = c.insert(acc, rt).insert(e, en);
    t_var(p, r, c, dd, dt);
    t_var(p, r, cb, e, en);
    t_proj(p, r, cb, var_e(e), k, v);
    t_var(p, r, cb, kk, k);
    t_eq(p, r, cb, pfst(var_e(e)), var_e(kk), k);
    t_var(p, r, cb, acc, rt);
    let same = bin_e(Builtin::Eq, pfst(var_e(e)), var_e(kk));
    match op {
        DictOp::Get => {
            assert(ty_expr(p, r, cb, some_e(psnd(var_e(e)))) == Some(Ty::Option(Box::new(v))));
            t_if(p, r, cb, same, some_e(psnd(var_e(e))), var_e(acc), rt);
            assert(ty_expr(p, r, c, Expr::None(v)) == Some(rt));
            fold_typing(p, r, c, var_e(dd), Expr::None(v), acc, e, if_e(same, some_e(psnd(var_e(e))), var_e(acc)), en, rt);
        },
        DictOp::Has => {
            t_if(p, r, cb, var_e(acc), Expr::Bool(true), same, Ty::Bool);
            fold_typing(p, r, c, var_e(dd), Expr::Bool(false), acc, e, if_e(var_e(acc), Expr::Bool(true), same), en, Ty::Bool);
        },
        _ => {
            ty_cons(p, r, cb, var_e(e), var_e(acc), en);
            t_if(p, r, cb, same, var_e(acc), cons_e(var_e(e), var_e(acc)), dt);
            ty_nil(p, r, c, en);
            let body = if_e(same, var_e(acc), cons_e(var_e(e), var_e(acc)));
            fold_typing(p, r, c, var_e(dd), Expr::List(en, Seq::empty()), acc, e, body, en, dt);
            t_list1(p, r, c, fold_e(var_e(dd), Expr::List(en, Seq::empty()), acc, e, body), en);
        },
    }
}

/// 辞書の操作の項目の形：項目 (k, v) は第 1 引数の型の鍵と値の型（dict_from は List<Pair<K, V>>、ほかは
/// Dict<K, V>）で、鍵と値の引数の型はそれぞれ k と v、形の型は `dict_result`。
pub proof fn dict_entry_shape(op: DictOp, ts: Seq<Option<Ty>>)
    requires
        hof_entry(Form::Dict(op), ts) is Some,
    ensures
        ts.len() == operands(Form::Dict(op)),
        op is From ==> ts[0] == Some(
            Ty::List(Box::new(en_ty(hof_entry(Form::Dict(op), ts)->Some_0.0, hof_entry(Form::Dict(op), ts)->Some_0.1))),
        ),
        !(op is From) ==> ts[0] == Some(
            Ty::Dict(Box::new(hof_entry(Form::Dict(op), ts)->Some_0.0), Box::new(hof_entry(Form::Dict(op), ts)->Some_0.1)),
        ),
        ts.len() >= 2 ==> ts[1] == Some(hof_entry(Form::Dict(op), ts)->Some_0.0),
        ts.len() == 3 ==> ts[2] == Some(hof_entry(Form::Dict(op), ts)->Some_0.1),
        form_ty(Form::Dict(op), ts) == Some(
            dict_result(op, hof_entry(Form::Dict(op), ts)->Some_0.0, hof_entry(Form::Dict(op), ts)->Some_0.1),
        ),
{
}

/// 一致（辞書の操作）：引数の核の型が checker の型の消去なら（第 1 引数は辞書の型の消去 List<Pair<K, V>>、鍵と値の
/// 引数は K と V の消去）、項目 (K, V)（の消去）を注釈に入れた書換えは、核の型付けで形の型の消去を持つ。
pub proof fn dict_rw_agrees(
    p: Prog,
    r: nat,
    ctx: Map<nat, Ty>,
    op: DictOp,
    args: Seq<Expr>,
    ns: Seq<nat>,
    ts: Seq<Option<Ty>>,
)
    requires
        hof_entry(Form::Dict(op), ts) is Some,
        args.len() == ts.len(),
        ns.len() == dict_names(op),
        dict_fresh(ns, args),
        forall|i: int| 0 <= i < args.len() ==> ty_expr(p, r, ctx, #[trigger] args[i]) == Some(derase(ts[i]->Some_0)),
    ensures
        ty_expr(
            p,
            r,
            ctx,
            dict_rw(
                op,
                args,
                derase(hof_entry(Form::Dict(op), ts)->Some_0.0),
                derase(hof_entry(Form::Dict(op), ts)->Some_0.1),
                ns,
            ),
        ) == Some(derase(form_ty(Form::Dict(op), ts)->Some_0)),
{
    dict_entry_shape(op, ts);
    let k0 = hof_entry(Form::Dict(op), ts)->Some_0.0;
    let v0 = hof_entry(Form::Dict(op), ts)->Some_0.1;
    derase_parts(k0, v0);
    derase_parts(v0, k0);
    derase_parts(en_ty(k0, v0), v0);
    let k = derase(k0);
    let v = derase(v0);
    let en = en_ty(k, v);
    let dt = dl_ty(k, v);
    let res = derase(dict_result(op, k0, v0));
    assert(derase(form_ty(Form::Dict(op), ts)->Some_0) == res);
    // 第 1 引数は List<Pair<K, V>>（dict_from は List<Pair<K, V>> の、ほかは Dict<K, V> の消去）
    assert(ty_expr(p, r, ctx, args[0]) == Some(derase(ts[0]->Some_0)));
    assert(derase(ts[0]->Some_0) == dt);
    match op {
        DictOp::Size => {
            t_list1(p, r, ctx, args[0], en);
        },
        DictOp::Entries => {},
        DictOp::Keys => {
            let (acc, e) = (ns[0], ns[1]);
            assert(acc != e);
            let lk = Ty::List(Box::new(k));
            let cb = ctx.insert(acc, lk).insert(e, en);
            t_var(p, r, cb, e, en);
            t_proj(p, r, cb, var_e(e), k, v);
            t_var(p, r, cb, acc, lk);
            ty_cons(p, r, cb, pfst(var_e(e)), var_e(acc), k);
            ty_nil(p, r, ctx, k);
            let body = cons_e(pfst(var_e(e)), var_e(acc));
            fold_typing(p, r, ctx, args[0], Expr::List(k, Seq::empty()), acc, e, body, en, lk);
            t_list1(p, r, ctx, fold_e(args[0], Expr::List(k, Seq::empty()), acc, e, body), k);
        },
        DictOp::Values => {
            let (acc, e) = (ns[0], ns[1]);
            assert(acc != e);
            let lv = Ty::List(Box::new(v));
            let cb = ctx.insert(acc, lv).insert(e, en);
            t_var(p, r, cb, e, en);
            t_proj(p, r, cb, var_e(e), k, v);
            t_var(p, r, cb, acc, lv);
            ty_cons(p, r, cb, psnd(var_e(e)), var_e(acc), v);
            ty_nil(p, r, ctx, v);
            let body = cons_e(psnd(var_e(e)), var_e(acc));
            fold_typing(p, r, ctx, args[0], Expr::List(v, Seq::empty()), acc, e, body, en, lv);
            t_list1(p, r, ctx, fold_e(args[0], Expr::List(v, Seq::empty()), acc, e, body), v);
        },
        DictOp::From => {
            let (acc, pn, kk, vv) = (ns[0], ns[1], ns[2], ns[3]);
            assert(acc != pn && acc != kk && acc != vv && pn != kk && pn != vv && kk != vv);
            assert(ns[4] != ns[5] && ns[4] != ns[6] && ns[5] != ns[6]);
            assert(kk != ns[4] && kk != ns[5] && kk != ns[6] && vv != ns[4] && vv != ns[5] && vv != ns[6]);
            let cb = ctx.insert(acc, dt).insert(pn, en);
            t_var(p, r, cb, pn, en);
            t_proj(p, r, cb, var_e(pn), k, v);
            let c2 = cb.insert(kk, k);
            t_var(p, r, c2, pn, en);
            t_proj(p, r, c2, var_e(pn), k, v);
            let c3 = c2.insert(vv, v);
            t_var(p, r, c3, acc, dt);
            put_typing(p, r, c3, var_e(acc), kk, vv, k, v, ns[4], ns[5], ns[6]);
            let put = put_rw(var_e(acc), kk, vv, en, ns[4], ns[5], ns[6]);
            t_let(p, r, c2, vv, psnd(var_e(pn)), put, v, dt);
            let body = let_e(kk, pfst(var_e(pn)), let_e(vv, psnd(var_e(pn)), put));
            t_let(p, r, cb, kk, pfst(var_e(pn)), let_e(vv, psnd(var_e(pn)), put), k, dt);
            ty_nil(p, r, ctx, en);
            fold_typing(p, r, ctx, args[0], Expr::List(en, Seq::empty()), acc, pn, body, en, dt);
        },
        DictOp::Put => {
            let (dd, kk, vv) = (ns[0], ns[1], ns[2]);
            assert(dd != kk && dd != vv && kk != vv);
            assert(ns[3] != ns[4] && ns[3] != ns[5] && ns[4] != ns[5]);
            assert(kk != ns[3] && kk != ns[4] && kk != ns[5] && vv != ns[3] && vv != ns[4] && vv != ns[5]);
            assert(ty_expr(p, r, ctx, args[1]) == Some(derase(ts[1]->Some_0)));
            assert(ty_expr(p, r, ctx, args[2]) == Some(derase(ts[2]->Some_0)));
            // 鍵と値の式は、先に束縛した名前を含まない
            assert(absent(dd, args[1]) && absent(dd, args[2]) && absent(kk, args[2]));
            let c1 = ctx.insert(dd, dt);
            ty_absent(p, r, ctx, args[1], dd, dt);
            ty_absent(p, r, ctx, args[2], dd, dt);
            let c2 = c1.insert(kk, k);
            ty_absent(p, r, c1, args[2], kk, k);
            let c3 = c2.insert(vv, v);
            t_var(p, r, c3, dd, dt);
            put_typing(p, r, c3, var_e(dd), kk, vv, k, v, ns[3], ns[4], ns[5]);
            let put = put_rw(var_e(dd), kk, vv, en, ns[3], ns[4], ns[5]);
            t_let(p, r, c2, vv, args[2], put, v, dt);
            t_let(p, r, c1, kk, args[1], let_e(vv, args[2], put), k, dt);
            t_let(p, r, ctx, dd, args[0], let_e(kk, args[1], let_e(vv, args[2], put)), dt, dt);
        },
        _ => {
            // dict_get・dict_has・dict_remove
            let (dd, kk, acc, e) = (ns[0], ns[1], ns[2], ns[3]);
            assert(dd != kk && acc != e && kk != acc && kk != e);
            assert(ty_expr(p, r, ctx, args[1]) == Some(derase(ts[1]->Some_0)));
            assert(absent(dd, args[1]));
            let c1 = ctx.insert(dd, dt);
            ty_absent(p, r, ctx, args[1], dd, dt);
            let c2 = c1.insert(kk, k);
            scan_typing(p, r, c2, op, dd, kk, k, v, acc, e);
            assert(scan_res(op, k, v) == res);
            let scan = scan_rw(op, dd, kk, v, en, acc, e);
            t_let(p, r, c1, kk, args[1], scan, k, res);
            t_let(p, r, ctx, dd, args[0], let_e(kk, args[1], scan), dt, res);
        },
    }
}

} // verus!
