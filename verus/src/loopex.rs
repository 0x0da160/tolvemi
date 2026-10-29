//! 反復（loop）の書換えの exec 実装（段階 1b、DECISION-43）：loop_types.rs の `loop_rw` を、検証済みの exec の木
//! （ir.rs の EExpr）の上で組み立てる。組立ての結果の写し（view_expr）は spec の `loop_rw` に等しい。dictex.rs と同じ作りである。
//!
//! 導入する名前（44 個）は、束縛 s、max、本体の名前の上限 b（loop_top）の次から b+1, b+2, ... と取る（fresh_ns）。
//! loop_names（名前は互いに異なり、s と異なり、max と本体に現れない）はこの取り方で成り立つ（loop_names_fresh）。
//! 加算は検査つき。桁あふれは None を返す（書換えの拒否）。段の幅の 16 の冪は、16 の 15 乗（2^60）までが u64 に収まる。
//!
//! 扱わないこと：Rust の反復の書換え（hof.rs の `Lower::loop_`）との対応、被演算子の型の出どころ（checker の HofTypes）、
//! 反復の意味（xsem に反復の形がない）。k・v と同じく、注釈の型 S は消去した型を与える。

use crate::bigint::*;
use crate::dictex::*;
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

// ------------------------------------------------------------------ 名前と上限

/// 導入する名前の上限：束縛 s の次と、max と本体の名前の上限の大きい方（hof_base と同じ取り方）。
pub open spec fn loop_top(s: nat, mx: Expr, body: Expr) -> nat {
    max(s + 1, max(top(mx), top(body)))
}

/// 名前 b+1+k（0 ≤ k < 44）。spec の fresh_ns の k 番目と一致する。
fn nm(b: usize, k: usize) -> (r: usize)
    requires
        b as nat + 44 <= usize::MAX as nat,
        k < 44,
    ensures
        r as nat == b as nat + 1 + k as nat,
{
    b + 1 + k
}

/// 導入する名前は loop_names を満たす（取り方が上限の次からなので）。
proof fn loop_names_fresh(s: nat, mx: Expr, body: Expr)
    ensures
        loop_names(fresh_ns(loop_top(s, mx, body), 44), s, mx, body),
{
    let b = loop_top(s, mx, body);
    let ns = fresh_ns(b, 44);
    assert(top(mx) <= b);
    assert(top(body) <= b);
    assert(s < b);
    assert forall|i: int, j: int| 0 <= i < j < 44 implies ns[i] != ns[j] by {
        assert(ns[i] == (b as int + 1 + i) as nat);
        assert(ns[j] == (b as int + 1 + j) as nat);
    };
    assert forall|i: int| 0 <= i < 44 implies ns[i] != s && absent(ns[i], mx) && absent(ns[i], body) by {
        assert(ns[i] == (b as int + 1 + i) as nat);
        fresh_absent(b, ns[i], mx);
        fresh_absent(b, ns[i], body);
    };
}

// ------------------------------------------------------------------ 式の組立て（spec の形と一致）

/// 整数の定数（u64 の値）。
pub fn int_x(n: u64) -> (r: EExpr)
    ensures
        view_expr(r) == Expr::Int(n as int),
{
    EExpr::Int(Int::from_u64(n))
}

/// 和の入れ（inj_e の exec 版）：ok<S, S>(a)（ok が真）、または err<S, S>(a)。
pub fn inj_x(ok: bool, t: Ty, a: EExpr) -> (r: EExpr)
    ensures
        view_expr(r) == inj_e(ok, t, view_expr(a)),
{
    EExpr::Inj(ok, ty_clone(&t), t, Box::new(a))
}

/// 和の照合（matchr_e の exec 版）。
pub fn matchr_x(m: EExpr, x: usize, a: EExpr, y: usize, b: EExpr) -> (r: EExpr)
    ensures
        view_expr(r) == matchr_e(view_expr(m), x as nat, view_expr(a), y as nat, view_expr(b)),
{
    EExpr::MatchR(Box::new(m), x, Box::new(a), y, Box::new(b))
}

/// 16 の k 乗（k ≤ 15）。段の幅は 16 の冪で、最大の 16 の 15 乗（2^60）は u64 に収まる。
fn pow16_x(k: usize) -> (r: u64)
    requires
        k <= 15,
    ensures
        r as int == pow16(k as nat),
{
    proof {
        reveal_with_fuel(pow16, 16);
    }
    match k {
        0 => 1,
        1 => 16,
        2 => 256,
        3 => 4096,
        4 => 65536,
        5 => 1048576,
        6 => 16777216,
        7 => 268435456,
        8 => 4294967296,
        9 => 68719476736,
        10 => 1099511627776,
        11 => 17592186044416,
        12 => 281474976710656,
        13 => 4503599627370496,
        14 => 72057594037927936,
        _ => 1152921504606846976,
    }
}

// ------------------------------------------------------------------ 段（loop_types.rs の形）

/// 段 j の初期状態の名前（level_prev の exec 版、j ≤ 14）。
fn level_prev_x(b: usize, j: usize) -> (r: usize)
    requires
        b as nat + 44 <= usize::MAX as nat,
        j <= 14,
    ensures
        r as nat == level_prev(fresh_ns(b as nat, 44), j as nat),
{
    if j == 0 {
        nm(b, 40)
    } else {
        nm(b, 1 + 2 * j)
    }
}

/// 残りの歩 sub(m, fst(a))（remaining の exec 版）。
fn remaining_x(b: usize, a: usize) -> (r: EExpr)
    requires
        b as nat + 44 <= usize::MAX as nat,
    ensures
        view_expr(r) == remaining(fresh_ns(b as nat, 44), a as nat),
{
    bi2_x(Builtin::Sub, var_x(nm(b, 0)), fst_x(var_x(a)))
}

/// 段 j が辿る列（level_list の exec 版、j ≤ 14）。
fn level_list_x(b: usize, j: usize) -> (r: EExpr)
    requires
        b as nat + 44 <= usize::MAX as nat,
        j <= 14,
    ensures
        view_expr(r) == level_list(fresh_ns(b as nat, 44), j as nat),
{
    let w = pow16_x(15 - j);
    if j == 0 {
        if_x(bi2_x(Builtin::Lt, int_x(w), var_x(nm(b, 0))), var_x(nm(b, 1)), var_x(nm(b, 2)))
    } else {
        let prev = level_prev_x(b, j);
        let deep = if_x(bi2_x(Builtin::Lt, int_x(w), remaining_x(b, prev)), var_x(nm(b, 1)), var_x(nm(b, 2)));
        if_x(bi2_x(Builtin::Lt, fst_x(var_x(prev)), var_x(nm(b, 0))), deep, var_x(nm(b, 41)))
    }
}

/// 一番内側の段の一歩（loop_step の exec 版）。
fn loop_step_x(b: usize, s: usize, body: EExpr, st: Ty) -> (r: EExpr)
    requires
        b as nat + 44 <= usize::MAX as nat,
    ensures
        view_expr(r) == loop_step(fresh_ns(b as nat, 44), s as nat, view_expr(body), st),
{
    let st1 = ty_clone(&st);
    let st2 = ty_clone(&st);
    let inner = match_x(
        body,
        inj_x(false, st1, var_x(s)),
        nm(b, 36),
        inj_x(true, st2, var_x(nm(b, 36))),
    );
    matchr_x(var_x(nm(b, 34)), s, inner, nm(b, 37), inj_x(false, st, var_x(nm(b, 37))))
}

/// 一番内側の段（loop_inner の exec 版）。
fn loop_inner_x(b: usize, s: usize, body: EExpr, st: Ty) -> (r: EExpr)
    requires
        b as nat + 44 <= usize::MAX as nat,
    ensures
        view_expr(r) == loop_inner(fresh_ns(b as nat, 44), s as nat, view_expr(body), st),
{
    let a = nm(b, 31);
    let step = loop_step_x(b, s, body, st);
    let chunk = fold_x(
        bi2_x(Builtin::Range, int_x(0), var_x(nm(b, 33))),
        snd_x(var_x(a)),
        nm(b, 34),
        nm(b, 35),
        step,
    );
    let sum = bi2_x(Builtin::Add, fst_x(var_x(a)), var_x(nm(b, 33)));
    let counted = pair_x(
        matchr_x(var_x(nm(b, 38)), nm(b, 39), sum, nm(b, 39), var_x(nm(b, 0))),
        var_x(nm(b, 38)),
    );
    let_x(
        nm(b, 33),
        bi2_x(Builtin::Min, int_x(16), remaining_x(b, a)),
        let_x(nm(b, 38), chunk, counted),
    )
}

/// 段 j（0 ≤ j ≤ 15）の入れ子（loop_level の exec 版）。段 15 は一番内側の段。
fn loop_level_x(b: usize, j: usize, s: usize, body: EExpr, st: Ty) -> (r: EExpr)
    requires
        b as nat + 44 <= usize::MAX as nat,
        j <= 15,
    ensures
        view_expr(r) == loop_level(j as nat, fresh_ns(b as nat, 44), s as nat, view_expr(body), st),
    decreases 15 - j,
{
    if j >= 15 {
        loop_inner_x(b, s, body, st)
    } else {
        let list = level_list_x(b, j);
        let prev = level_prev_x(b, j);
        let inner = loop_level_x(b, j + 1, s, body, st);
        fold_x(list, var_x(prev), nm(b, 3 + 2 * j), nm(b, 4 + 2 * j), inner)
    }
}

// ------------------------------------------------------------------ 書換え（loop_rw の exec 版）

/// loop(init, max, |s| e) の書換え（loop_rw の exec 版）。導入する名前は fresh_ns(loop_top(s, max, body), 44) の名前。
/// 名前の上限の加算が桁あふれしたときだけ None を返す。st は注釈の型 S（消去したもの）。
pub fn loop_rw_x(init: EExpr, mx: EExpr, s: usize, body: EExpr, st: Ty) -> (r: Option<EExpr>)
    ensures
        match r {
            Some(out) => view_expr(out) == loop_rw(
                view_expr(init),
                view_expr(mx),
                s as nat,
                view_expr(body),
                st,
                fresh_ns(loop_top(s as nat, view_expr(mx), view_expr(body)), 44),
            ),
            None => true,
        },
{
    let tm = top_e(&mx);
    let tb = top_e(&body);
    let t = match max_o(tm, tb) {
        Some(x) => x,
        None => return None,
    };
    if s == usize::MAX {
        return None;
    }
    let s1 = s + 1;
    let b = if s1 >= t { s1 } else { t };
    if b > usize::MAX - 44 {
        return None;
    }
    let st_init = ty_clone(&st);
    let st_lvl = ty_clone(&st);
    let result = let_x(
        nm(b, 42),
        loop_level_x(b, 0, s, body, st_lvl),
        matchr_x(snd_x(var_x(nm(b, 42))), nm(b, 43), none_x(st), nm(b, 37), some_x(var_x(nm(b, 37)))),
    );
    Some(let_x(
        nm(b, 40),
        pair_x(int_x(0), inj_x(true, st_init, init)),
        let_x(
            nm(b, 0),
            mx,
            let_x(
                nm(b, 1),
                bi2_x(Builtin::Range, int_x(0), int_x(16)),
                let_x(nm(b, 2), bi2_x(Builtin::Range, int_x(0), int_x(1)), let_x(nm(b, 41), nil_x(Ty::Int), result)),
            ),
        ),
    ))
}

// ------------------------------------------------------------------ 書換えの型

/// 反復の型（loop_rw_agrees の導入する名前の版）：項目の型 ts を持つ被演算子の下で、fresh_ns の名前の書換えは
/// 形の型 Option<S> の消去を持つ。loop_rw_x の出力 out は view_expr(out) がこの書換えに等しいので、同じ型を持つ。
pub proof fn loop_rw_fresh_agrees(
    p: Prog,
    r: nat,
    ctx: Map<nat, Ty>,
    init: Expr,
    mx: Expr,
    s: nat,
    body: Expr,
    ts: Seq<Option<Ty>>,
)
    requires
        hof_entry(Form::Loop, ts) is Some,
        ty_expr(p, r, ctx, init) == Some(derase(ts[0]->Some_0)),
        ty_expr(p, r, ctx, mx) == Some(derase(ts[1]->Some_0)),
        ty_expr(p, r, ctx.insert(s, derase(hof_entry(Form::Loop, ts)->Some_0.0)), body) == Some(
            derase(ts[2]->Some_0),
        ),
    ensures
        ty_expr(
            p,
            r,
            ctx,
            loop_rw(
                init,
                mx,
                s,
                body,
                derase(hof_entry(Form::Loop, ts)->Some_0.0),
                fresh_ns(loop_top(s, mx, body), 44),
            ),
        ) == Some(derase(form_ty(Form::Loop, ts)->Some_0)),
{
    loop_names_fresh(s, mx, body);
    loop_rw_agrees(p, r, ctx, init, mx, s, body, fresh_ns(loop_top(s, mx, body), 44), ts);
}

} // verus!
