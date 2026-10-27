//! 辞書の操作の書換えの exec 実装（段階 1b、DECISION-43）：dict_types.rs の `dict_rw` と、その部品 `put_rw`・
//! `scan_rw` の写しを、検証済みの exec の木（ir.rs の EExpr）の上で組み立てる。組立ての結果の写し（view_expr）は
//! spec の形に等しい。hofex.rs の書換えと同じ作りである。
//!
//! 導入する名前は被演算子の名前の上限 b（三つの top の最大）の次から b+1, b+2, ... と取る（fresh_ns）。
//! dict_fresh（名前は互いに異なり、被演算子に現れない）はこの取り方で成り立つ（dict_fresh_ns）。加算は検査つき。
//! 桁あふれは None を返す（書換えの拒否）。呼出し側（Rust の接着）は None を、資源の上限による拒否として扱う。
//! k・v は注釈に入れる型で、消去した型（erase_x の結果）を与える。
//!
//! 扱わないこと：Rust の辞書の操作（dict.rs の `Lower::dict_op`）との対応、被演算子の型の出どころ（checker の
//! HofTypes）、辞書の操作の意味（xsem に辞書の形はない）。

use crate::dict_types::*;
use crate::fresh::*;
use crate::hof_agree::*;
use crate::hof_types::*;
use crate::hofex::*;
use crate::input::*;
use crate::ir::*;
use crate::loop_types::*;
use crate::proof::*;
use crate::records_proof::*;
use crate::sortmeaning::*;
use crate::spec::*;
use crate::xtyping::*;
use vstd::prelude::*;

verus! {

// ------------------------------------------------------------------ 写しの部品

/// dict_rw が読む被演算子の列（arity は operands(Form::Dict(op))）。
pub open spec fn dict_args(op: DictOp, a0: Expr, a1: Expr, a2: Expr) -> Seq<Expr> {
    match op {
        DictOp::Put => seq![a0, a1, a2],
        DictOp::Get | DictOp::Remove | DictOp::Has => seq![a0, a1],
        _ => seq![a0],
    }
}

/// 被演算子の名前の上限（三つの top の最大）。
pub open spec fn dict_top(a0: Expr, a1: Expr, a2: Expr) -> nat {
    max(top(a0), max(top(a1), top(a2)))
}

/// 導入する名前：上限 b の次から n 個（b+1, ..., b+n）。
pub open spec fn fresh_ns(b: nat, n: nat) -> Seq<nat> {
    Seq::new(n, |i: int| (b as int + 1 + i) as nat)
}

/// 鍵と値の変数の対 pair(var(kk), var(vv))（put_rw の新しい要素）。
pub fn entry_x(kk: usize, vv: usize) -> (r: EExpr)
    ensures
        view_expr(r) == pair_e(var_e(kk as nat), var_e(vv as nat)),
{
    pair_x(var_x(kk), var_x(vv))
}

// ------------------------------------------------------------------ 名前と被演算子の性質

/// 名前 x が b+1 以上なら、top(e) ≤ b の式 e に現れない。
proof fn fresh_absent(b: nat, x: nat, e: Expr)
    requires
        top(e) <= b,
        b + 1 <= x,
    ensures
        absent(x, e),
{
    top_below(e);
    below_mono(top(e), b + 1, e);
    below_absent(b + 1, x, e);
}

/// 被演算子の列の要素は a0・a1・a2 のどれか。
proof fn dict_args_member(op: DictOp, a0: Expr, a1: Expr, a2: Expr, j: int)
    requires
        0 <= j < dict_args(op, a0, a1, a2).len(),
    ensures
        dict_args(op, a0, a1, a2)[j] == a0 || dict_args(op, a0, a1, a2)[j] == a1 || dict_args(op, a0, a1, a2)[j] == a2,
{
    match op {
        DictOp::Put => {
            assert(j == 0 || j == 1 || j == 2);
        },
        DictOp::Get | DictOp::Remove | DictOp::Has => {
            assert(j == 0 || j == 1);
        },
        _ => {
            assert(j == 0);
        },
    }
}

/// 被演算子の列の要素の名前の上限は、三つの上限の最大より小さいか等しい。
proof fn dict_args_top(op: DictOp, a0: Expr, a1: Expr, a2: Expr, j: int)
    requires
        0 <= j < dict_args(op, a0, a1, a2).len(),
    ensures
        top(dict_args(op, a0, a1, a2)[j]) <= dict_top(a0, a1, a2),
{
    dict_args_member(op, a0, a1, a2, j);
}

/// 被演算子の列の長さは、辞書の操作の被演算子の数（operands）。
proof fn dict_args_len(op: DictOp, a0: Expr, a1: Expr, a2: Expr)
    ensures
        dict_args(op, a0, a1, a2).len() == operands(Form::Dict(op)),
{
    match op {
        DictOp::Put => {},
        DictOp::Get | DictOp::Remove | DictOp::Has => {},
        _ => {},
    }
}

/// 導入する名前は、被演算子のどの名前とも重ならず、互いに異なる（dict_fresh）。
pub proof fn dict_fresh_ns(op: DictOp, a0: Expr, a1: Expr, a2: Expr)
    ensures
        dict_fresh(fresh_ns(dict_top(a0, a1, a2), dict_names(op)), dict_args(op, a0, a1, a2)),
{
    let b = dict_top(a0, a1, a2);
    let ns = fresh_ns(b, dict_names(op));
    let args = dict_args(op, a0, a1, a2);
    assert forall|i: int, j: int| 0 <= i < j < ns.len() implies ns[i] != ns[j] by {
        assert(ns[i] == (b as int + 1 + i) as nat);
        assert(ns[j] == (b as int + 1 + j) as nat);
    };
    assert forall|i: int, j: int| 0 <= i < ns.len() && 0 <= j < args.len() implies absent(ns[i], args[j]) by {
        assert(ns[i] == (b as int + 1 + i) as nat);
        dict_args_top(op, a0, a1, a2, j);
        fresh_absent(b, ns[i], args[j]);
    };
}

// ------------------------------------------------------------------ 書換えの写し（dict_types.rs の形）

/// PUT の写し（put_rw）：d は消去した辞書、en は要素の型、rn・acc・e は導入する名前。
pub fn put_rw_x(d: EExpr, kk: usize, vv: usize, en: Ty, rn: usize, acc: usize, e: usize) -> (r: EExpr)
    ensures
        view_expr(r) == put_rw(view_expr(d), kk as nat, vv as nat, en, rn as nat, acc as nat, e as nat),
{
    let same = bi2_x(Builtin::Eq, fst_x(var_x(e)), var_x(kk));
    let replaced = pair_x(cons_x(entry_x(kk, vv), fst_x(var_x(acc))), bool_x(true));
    let kept = pair_x(cons_x(var_x(e), fst_x(var_x(acc))), snd_x(var_x(acc)));
    let scan = fold_x(d, pair_x(nil_x(en), bool_x(false)), acc, e, if_x(same, replaced, kept));
    let fin = if_x(snd_x(var_x(rn)), fst_x(var_x(rn)), cons_x(entry_x(kk, vv), fst_x(var_x(rn))));
    let_x(rn, scan, reverse_x(fin))
}

/// dict_get・dict_has・dict_remove の走査（scan_rw）：dd と kk は辞書と鍵を束縛した名前、acc と e は fold の名前。
pub fn scan_rw_x(op: DictOp, dd: usize, kk: usize, v: Ty, en: Ty, acc: usize, e: usize) -> (r: EExpr)
    ensures
        view_expr(r) == scan_rw(op, dd as nat, kk as nat, v, en, acc as nat, e as nat),
{
    match op {
        DictOp::Get => {
            let same = bi2_x(Builtin::Eq, fst_x(var_x(e)), var_x(kk));
            fold_x(var_x(dd), none_x(v), acc, e, if_x(same, some_x(snd_x(var_x(e))), var_x(acc)))
        },
        DictOp::Has => {
            let same = bi2_x(Builtin::Eq, fst_x(var_x(e)), var_x(kk));
            fold_x(var_x(dd), bool_x(false), acc, e, if_x(var_x(acc), bool_x(true), same))
        },
        _ => {
            let same = bi2_x(Builtin::Eq, fst_x(var_x(e)), var_x(kk));
            let keep = cons_x(var_x(e), var_x(acc));
            reverse_x(fold_x(var_x(dd), nil_x(en), acc, e, if_x(same, var_x(acc), keep)))
        },
    }
}

/// 辞書の操作 op(a0, a1, a2) の書換え（dict_rw）。導入する名前は fresh_ns の名前。上限の加算が桁あふれした
/// ときだけ None を返す。k と v は注釈に入れる消去した型。
pub fn dict_rw_x(op: DictOp, a0: EExpr, a1: EExpr, a2: EExpr, k: Ty, v: Ty) -> (r: Option<EExpr>)
    ensures
        match r {
            Some(out) => view_expr(out) == dict_rw(
                op,
                dict_args(op, view_expr(a0), view_expr(a1), view_expr(a2)),
                k,
                v,
                fresh_ns(dict_top(view_expr(a0), view_expr(a1), view_expr(a2)), dict_names(op)),
            ),
            None => true,
        },
{
    let t0 = top_e(&a0);
    let t1 = top_e(&a1);
    let t2 = top_e(&a2);
    let b = match max_o(t0, max_o(t1, t2)) {
        Some(x) => x,
        None => return None,
    };
    if b > usize::MAX - 7 {
        return None;
    }
    let n0 = b + 1;
    let n1 = b + 2;
    let n2 = b + 3;
    let n3 = b + 4;
    let n4 = b + 5;
    let n5 = b + 6;
    let n6 = b + 7;
    let en = Ty::Pair(Box::new(ty_clone(&k)), Box::new(ty_clone(&v)));
    match op {
        DictOp::Size => Some(bi1_x(Builtin::Length, a0)),
        DictOp::Entries => Some(a0),
        DictOp::Keys => {
            let body = cons_x(fst_x(var_x(n1)), var_x(n0));
            Some(reverse_x(fold_x(a0, nil_x(k), n0, n1, body)))
        },
        DictOp::Values => {
            let body = cons_x(snd_x(var_x(n1)), var_x(n0));
            Some(reverse_x(fold_x(a0, nil_x(v), n0, n1, body)))
        },
        DictOp::From => {
            let en2 = ty_clone(&en);
            let put = put_rw_x(var_x(n0), n2, n3, en, n4, n5, n6);
            let body = let_x(n2, fst_x(var_x(n1)), let_x(n3, snd_x(var_x(n1)), put));
            Some(fold_x(a0, nil_x(en2), n0, n1, body))
        },
        DictOp::Put => {
            let put = put_rw_x(var_x(n0), n1, n2, en, n3, n4, n5);
            Some(let_x(n0, a0, let_x(n1, a1, let_x(n2, a2, put))))
        },
        _ => Some(let_x(n0, a0, let_x(n1, a1, scan_rw_x(op, n0, n1, v, en, n2, n3)))),
    }
}

// ------------------------------------------------------------------ 書換えの型

/// 書換えの型（dict_rw_agrees の導入する名前の版）：被演算子が項目の型 ts を持てば、fresh_ns の名前の下の書換えは
/// 形の型の消去を持つ。dict_rw_x の出力 out は view_expr(out) がこの書換えに等しいので、同じ型を持つ。
pub proof fn dict_rw_fresh_agrees(
    p: Prog,
    r: nat,
    ctx: Map<nat, Ty>,
    op: DictOp,
    a0: Expr,
    a1: Expr,
    a2: Expr,
    ts: Seq<Option<Ty>>,
)
    requires
        hof_entry(Form::Dict(op), ts) is Some,
        forall|i: int| 0 <= i < dict_args(op, a0, a1, a2).len() ==> ty_expr(p, r, ctx, #[trigger] dict_args(op, a0, a1, a2)[i]) == Some(derase(ts[i]->Some_0)),
    ensures
        ty_expr(
            p,
            r,
            ctx,
            dict_rw(
                op,
                dict_args(op, a0, a1, a2),
                derase(hof_entry(Form::Dict(op), ts)->Some_0.0),
                derase(hof_entry(Form::Dict(op), ts)->Some_0.1),
                fresh_ns(dict_top(a0, a1, a2), dict_names(op)),
            ),
        ) == Some(derase(form_ty(Form::Dict(op), ts)->Some_0)),
{
    dict_entry_shape(op, ts);
    dict_args_len(op, a0, a1, a2);
    dict_fresh_ns(op, a0, a1, a2);
    dict_rw_agrees(p, r, ctx, op, dict_args(op, a0, a1, a2), fresh_ns(dict_top(a0, a1, a2), dict_names(op)), ts);
}

} // verus!
