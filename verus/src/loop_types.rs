//! loop の書換えの型と、HofTypes の項目の一致（SH1）。
//!
//! hof.rs の `Lower::loop_` の書換え（外側の 15 段と一番内側の段の fold の入れ子）を核の式に写し（`loop_rw`）、
//! 表の項目 (S, Option<S>) の S を注釈（`ok<S, S>`・`err<S, S>`・`none<S>`）に入れた書換えが、核の型付け `ty_expr`
//! で形の型 Option<S> の消去を持つことを示す（`loop_rw_agrees`）。loop の形は源の型付け `ty_x` にないので、
//! 一致はこの書換えの型で述べる。注釈の型は init の型のほかにない（`loop_rw_note`）。
//! 写しの形と名前の順は crates/tlvm/tests/loop.rs の `doubling_lowered`（Rust の書換えの出力と一字ずつ比べる）と
//! 同じで、名前 ns[k] はそこでの hof{k+1}。

use crate::hof_agree::*;
use crate::hof_types::*;
use crate::input::*;
use crate::records_proof::*;
use crate::sortmeaning::*;
use crate::spec::*;
use crate::xtyping::*;
use vstd::prelude::*;

verus! {

// ------------------------------------------------------------------ 式の組み立て

pub open spec fn var_e(x: nat) -> Expr {
    Expr::Var(x)
}

pub open spec fn bin_e(b: Builtin, a: Expr, c: Expr) -> Expr {
    Expr::Builtin(b, seq![a, c])
}

pub open spec fn let_e(x: nat, a: Expr, b: Expr) -> Expr {
    Expr::Let(x, Box::new(a), Box::new(b))
}

pub open spec fn if_e(c: Expr, a: Expr, b: Expr) -> Expr {
    Expr::If(Box::new(c), Box::new(a), Box::new(b))
}

pub open spec fn fold_e(xs: Expr, init: Expr, acc: nat, item: nat, body: Expr) -> Expr {
    Expr::Fold(Box::new(xs), Box::new(init), acc, item, Box::new(body))
}

pub open spec fn match_e(m: Expr, n: Expr, x: nat, sm: Expr) -> Expr {
    Expr::Match(Box::new(m), Box::new(n), x, Box::new(sm))
}

pub open spec fn matchr_e(m: Expr, x: nat, a: Expr, y: nat, b: Expr) -> Expr {
    Expr::MatchR(Box::new(m), x, Box::new(a), y, Box::new(b))
}

/// `ok<S, S>(a)`（true）と `err<S, S>(a)`（false）。
pub open spec fn inj_e(ok: bool, s: Ty, a: Expr) -> Expr {
    Expr::Inj(ok, s, s, Box::new(a))
}

pub open spec fn some_e(a: Expr) -> Expr {
    Expr::Some(Box::new(a))
}

// ------------------------------------------------------------------ 型の部品

/// 文脈 c で名前 x の型は t。
pub open spec fn has(c: Map<nat, Ty>, x: nat, t: Ty) -> bool {
    c.contains_key(x) && c[x] == t
}

pub open spec fn rs_ty(s: Ty) -> Ty {
    Ty::Result(Box::new(s), Box::new(s))
}

/// loop の状態の型 Pair<Int, Result<S, S>>（本体を評価した回数と、続行中 ok・止まった err）。
pub open spec fn st_ty(s: Ty) -> Ty {
    Ty::Pair(Box::new(Ty::Int), Box::new(rs_ty(s)))
}

pub open spec fn li_ty() -> Ty {
    Ty::List(Box::new(Ty::Int))
}

pub proof fn t_var(p: Prog, r: nat, ctx: Map<nat, Ty>, x: nat, t: Ty)
    requires
        has(ctx, x, t),
    ensures
        ty_expr(p, r, ctx, var_e(x)) == Some(t),
{
}

/// 一引数の組込みの型。
pub proof fn t_un(p: Prog, r: nat, ctx: Map<nat, Ty>, b: Builtin, a: Expr, ta: Ty, t: Ty)
    requires
        ty_expr(p, r, ctx, a) == Some(ta),
        builtin_type(b, seq![ta]) == Some(t),
    ensures
        ty_expr(p, r, ctx, Expr::Builtin(b, seq![a])) == Some(t),
{
    reveal_with_fuel(ty_args, 2);
    let es = seq![a];
    assert(es[0] == a);
    assert(ty_args(p, r, ctx, es, 1) == Some(Seq::<Ty>::empty()));
    assert(seq![ta] + Seq::<Ty>::empty() =~= seq![ta]);
    assert(ty_args(p, r, ctx, es, 0) == Some(seq![ta]));
}

/// 二引数の組込みの型。
pub proof fn t_bin(p: Prog, r: nat, ctx: Map<nat, Ty>, b: Builtin, a1: Expr, a2: Expr, t1: Ty, t2: Ty, t: Ty)
    requires
        ty_expr(p, r, ctx, a1) == Some(t1),
        ty_expr(p, r, ctx, a2) == Some(t2),
        builtin_type(b, seq![t1, t2]) == Some(t),
    ensures
        ty_expr(p, r, ctx, bin_e(b, a1, a2)) == Some(t),
{
    reveal_with_fuel(ty_args, 3);
    let es = seq![a1, a2];
    assert(es[0] == a1 && es[1] == a2);
    assert(ty_args(p, r, ctx, es, 2) == Some(Seq::<Ty>::empty()));
    assert(seq![t2] + Seq::<Ty>::empty() =~= seq![t2]);
    assert(ty_args(p, r, ctx, es, 1) == Some(seq![t2]));
    assert(seq![t1] + seq![t2] =~= seq![t1, t2]);
    assert(ty_args(p, r, ctx, es, 0) == Some(seq![t1, t2]));
}

/// fst と snd の型。
pub proof fn t_proj(p: Prog, r: nat, ctx: Map<nat, Ty>, a: Expr, ta: Ty, tb: Ty)
    requires
        ty_expr(p, r, ctx, a) == Some(Ty::Pair(Box::new(ta), Box::new(tb))),
    ensures
        ty_expr(p, r, ctx, pfst(a)) == Some(ta),
        ty_expr(p, r, ctx, psnd(a)) == Some(tb),
{
    let pt = Ty::Pair(Box::new(ta), Box::new(tb));
    assert(seq![pt].len() == 1 && seq![pt][0] == pt);
    t_un(p, r, ctx, Builtin::Fst, a, pt, ta);
    t_un(p, r, ctx, Builtin::Snd, a, pt, tb);
}

/// 整数の二項の組込み（sub・add・min は Int、lt は Bool、range は List<Int>）の型。
pub proof fn t_int2(p: Prog, r: nat, ctx: Map<nat, Ty>, a1: Expr, a2: Expr)
    requires
        ty_expr(p, r, ctx, a1) == Some(Ty::Int),
        ty_expr(p, r, ctx, a2) == Some(Ty::Int),
    ensures
        ty_expr(p, r, ctx, bin_e(Builtin::Sub, a1, a2)) == Some(Ty::Int),
        ty_expr(p, r, ctx, bin_e(Builtin::Add, a1, a2)) == Some(Ty::Int),
        ty_expr(p, r, ctx, bin_e(Builtin::Min, a1, a2)) == Some(Ty::Int),
        ty_expr(p, r, ctx, bin_e(Builtin::Lt, a1, a2)) == Some(Ty::Bool),
        ty_expr(p, r, ctx, bin_e(Builtin::Range, a1, a2)) == Some(li_ty()),
{
    let ts = seq![Ty::Int, Ty::Int];
    assert(ts.len() == 2 && ts[0] == Ty::Int && ts[1] == Ty::Int);
    t_bin(p, r, ctx, Builtin::Sub, a1, a2, Ty::Int, Ty::Int, Ty::Int);
    t_bin(p, r, ctx, Builtin::Add, a1, a2, Ty::Int, Ty::Int, Ty::Int);
    t_bin(p, r, ctx, Builtin::Min, a1, a2, Ty::Int, Ty::Int, Ty::Int);
    t_bin(p, r, ctx, Builtin::Lt, a1, a2, Ty::Int, Ty::Int, Ty::Bool);
    t_bin(p, r, ctx, Builtin::Range, a1, a2, Ty::Int, Ty::Int, li_ty());
}

pub proof fn t_let(p: Prog, r: nat, ctx: Map<nat, Ty>, x: nat, a: Expr, b: Expr, ta: Ty, tb: Ty)
    requires
        ty_expr(p, r, ctx, a) == Some(ta),
        ty_expr(p, r, ctx.insert(x, ta), b) == Some(tb),
    ensures
        ty_expr(p, r, ctx, let_e(x, a, b)) == Some(tb),
{
}

pub proof fn t_if(p: Prog, r: nat, ctx: Map<nat, Ty>, c: Expr, a: Expr, b: Expr, t: Ty)
    requires
        ty_expr(p, r, ctx, c) == Some(Ty::Bool),
        ty_expr(p, r, ctx, a) == Some(t),
        ty_expr(p, r, ctx, b) == Some(t),
    ensures
        ty_expr(p, r, ctx, if_e(c, a, b)) == Some(t),
{
}

pub proof fn t_match(p: Prog, r: nat, ctx: Map<nat, Ty>, m: Expr, n: Expr, x: nat, sm: Expr, ta: Ty, tn: Ty)
    requires
        ty_expr(p, r, ctx, m) == Some(Ty::Option(Box::new(ta))),
        ty_expr(p, r, ctx, n) == Some(tn),
        ty_expr(p, r, ctx.insert(x, ta), sm) == Some(tn),
    ensures
        ty_expr(p, r, ctx, match_e(m, n, x, sm)) == Some(tn),
{
}

pub proof fn t_matchr(p: Prog, r: nat, ctx: Map<nat, Ty>, m: Expr, x: nat, a: Expr, y: nat, b: Expr, t: Ty, u: Ty, ta: Ty)
    requires
        ty_expr(p, r, ctx, m) == Some(Ty::Result(Box::new(t), Box::new(u))),
        ty_expr(p, r, ctx.insert(x, t), a) == Some(ta),
        ty_expr(p, r, ctx.insert(y, u), b) == Some(ta),
    ensures
        ty_expr(p, r, ctx, matchr_e(m, x, a, y, b)) == Some(ta),
{
}

pub proof fn t_inj(p: Prog, r: nat, ctx: Map<nat, Ty>, ok: bool, s: Ty, a: Expr)
    requires
        ty_expr(p, r, ctx, a) == Some(s),
    ensures
        ty_expr(p, r, ctx, inj_e(ok, s, a)) == Some(rs_ty(s)),
{
}

pub proof fn t_pair_e(p: Prog, r: nat, ctx: Map<nat, Ty>, a: Expr, b: Expr, ta: Ty, tb: Ty)
    requires
        ty_expr(p, r, ctx, a) == Some(ta),
        ty_expr(p, r, ctx, b) == Some(tb),
    ensures
        ty_expr(p, r, ctx, pair_e(a, b)) == Some(Ty::Pair(Box::new(ta), Box::new(tb))),
{
}

// ------------------------------------------------------------------ 束縛の列を足した文脈

/// ctx に束縛の列 bs を順に足した文脈。
pub open spec fn ext(ctx: Map<nat, Ty>, bs: Seq<(nat, Ty)>) -> Map<nat, Ty>
    decreases bs.len(),
{
    if bs.len() == 0 {
        ctx
    } else {
        ext(ctx, bs.drop_last()).insert(bs.last().0, bs.last().1)
    }
}

pub proof fn ext_push(ctx: Map<nat, Ty>, bs: Seq<(nat, Ty)>, x: nat, t: Ty)
    ensures
        ext(ctx, bs.push((x, t))) == ext(ctx, bs).insert(x, t),
{
    assert(bs.push((x, t)).drop_last() =~= bs);
    assert(bs.push((x, t)).last() == (x, t));
}

/// 列の名前がどれも s と違えば、s の束縛は列の前に移せる。
pub proof fn ext_comm(ctx: Map<nat, Ty>, bs: Seq<(nat, Ty)>, s: nat, t: Ty)
    requires
        forall|k: int| 0 <= k < bs.len() ==> (#[trigger] bs[k]).0 != s,
    ensures
        ext(ctx, bs).insert(s, t) == ext(ctx.insert(s, t), bs),
    decreases bs.len(),
{
    if bs.len() > 0 {
        let bs1 = bs.drop_last();
        assert forall|k: int| 0 <= k < bs1.len() implies (#[trigger] bs1[k]).0 != s by {
            assert(bs1[k] == bs[k]);
        }
        ext_comm(ctx, bs1, s, t);
        let last = bs[bs.len() - 1];
        assert(bs.last() == last);
        assert(last.0 != s);
        assert(ext(ctx, bs1).insert(last.0, last.1).insert(s, t) =~= ext(ctx, bs1).insert(s, t).insert(
            last.0,
            last.1,
        ));
    }
}

/// 列の名前がどれも e に現れなければ、列を足した文脈での e の型は、足す前の型と同じ。
pub proof fn ext_absent(p: Prog, r: nat, ctx: Map<nat, Ty>, bs: Seq<(nat, Ty)>, e: Expr)
    requires
        forall|k: int| 0 <= k < bs.len() ==> absent((#[trigger] bs[k]).0, e),
    ensures
        ty_expr(p, r, ext(ctx, bs), e) == ty_expr(p, r, ctx, e),
    decreases bs.len(),
{
    if bs.len() > 0 {
        let bs1 = bs.drop_last();
        assert forall|k: int| 0 <= k < bs1.len() implies absent((#[trigger] bs1[k]).0, e) by {
            assert(bs1[k] == bs[k]);
        }
        let last = bs[bs.len() - 1];
        assert(bs.last() == last);
        ty_absent(p, r, ext(ctx, bs1), e, last.0, last.1);
        ext_absent(p, r, ctx, bs1, e);
    }
}

/// 列の名前がどれも s と違い、本体に現れなければ、列を足して s を束縛した文脈での本体の型は、ctx に s だけを
/// 束縛した文脈での型と同じ。
pub proof fn ext_body(p: Prog, r: nat, ctx: Map<nat, Ty>, bs: Seq<(nat, Ty)>, s: nat, t: Ty, e: Expr)
    requires
        forall|k: int| 0 <= k < bs.len() ==> (#[trigger] bs[k]).0 != s && absent(bs[k].0, e),
    ensures
        ty_expr(p, r, ext(ctx, bs).insert(s, t), e) == ty_expr(p, r, ctx.insert(s, t), e),
{
    assert forall|k: int| 0 <= k < bs.len() implies (#[trigger] bs[k]).0 != s by {}
    assert forall|k: int| 0 <= k < bs.len() implies absent((#[trigger] bs[k]).0, e) by {}
    ext_comm(ctx, bs, s, t);
    ext_absent(p, r, ctx.insert(s, t), bs, e);
}

// ------------------------------------------------------------------ 書換えの写し（hof.rs の Lower::loop_）

/// 16 の k 乗。段 j（0〜14）の 1 要素が受け持つ歩の数は LOOP_BASE^(LOOP_LEVELS - 1 - j) = 16^(15 - j)。
pub open spec fn pow16(k: nat) -> int
    decreases k,
{
    if k == 0 {
        1
    } else {
        16 * pow16((k - 1) as nat)
    }
}

/// 書換えが導入する 44 個の名前（hof.rs の `loop_` の `fresh` の順）：0 m（max の値）、1 rg、2 one、
/// 3 + 2j と 4 + 2j は外側の段 j（0〜14）の acc と item、33 n、34 acc、35 i、36 s2、37 d、38 res、39 x、40 s0、
/// 41 nil、42 fr、43 r。互いに異なり、束縛 s と異なり、max と本体に現れない（`fresh` はプログラムのどの名前とも
/// 重ならない）。
pub open spec fn loop_names(ns: Seq<nat>, s: nat, max: Expr, body: Expr) -> bool {
    &&& ns.len() == 44
    &&& forall|i: int, j: int| 0 <= i < j < 44 ==> ns[i] != ns[j]
    &&& forall|i: int| 0 <= i < 44 ==> ns[i] != s && absent(ns[i], max) && absent(ns[i], body)
}

/// 残りの歩 sub(m, fst(a))。
pub open spec fn remaining(ns: Seq<nat>, a: nat) -> Expr {
    bin_e(Builtin::Sub, var_e(ns[0]), pfst(var_e(a)))
}

/// 段 j の初期状態の名前：段 0 は s0、段 j（1〜15）は段 j - 1 の acc。
pub open spec fn level_prev(ns: Seq<nat>, j: nat) -> nat {
    if j == 0 {
        ns[40]
    } else {
        ns[(1 + 2 * j) as int]
    }
}

/// 段 j（0〜14）が辿る列：段 0 は if(lt(16^15, m), rg, one)、段 j（1〜14）は
/// if(lt(fst(prev), m), if(lt(16^(15 - j), sub(m, fst(prev))), rg, one), nil)。
pub open spec fn level_list(ns: Seq<nat>, j: nat) -> Expr {
    let width = Expr::Int(pow16((15 - j) as nat));
    if j == 0 {
        if_e(bin_e(Builtin::Lt, width, var_e(ns[0])), var_e(ns[1]), var_e(ns[2]))
    } else {
        let prev = level_prev(ns, j);
        if_e(
            bin_e(Builtin::Lt, pfst(var_e(prev)), var_e(ns[0])),
            if_e(bin_e(Builtin::Lt, width, remaining(ns, prev)), var_e(ns[1]), var_e(ns[2])),
            var_e(ns[41]),
        )
    }
}

/// 一番内側の段の一歩：match_result(acc, |s| match_option(e, err<S, S>(s), |s2| ok<S, S>(s2)), |d| err<S, S>(d))。
pub open spec fn loop_step(ns: Seq<nat>, s: nat, body: Expr, st: Ty) -> Expr {
    matchr_e(
        var_e(ns[34]),
        s,
        match_e(body, inj_e(false, st, var_e(s)), ns[36], inj_e(true, st, var_e(ns[36]))),
        ns[37],
        inj_e(false, st, var_e(ns[37])),
    )
}

/// 一番内側の段（a は段 14 の acc）：let n = min(16, sub(m, fst(a))) in
/// let res = fold(range(0, n), snd(a), |acc, i| 一歩) in pair(match_result(res, |x| add(fst(a), n), |x| m), res)。
pub open spec fn loop_inner(ns: Seq<nat>, s: nat, body: Expr, st: Ty) -> Expr {
    let a = ns[31];
    let chunk = fold_e(
        bin_e(Builtin::Range, Expr::Int(0), var_e(ns[33])),
        psnd(var_e(a)),
        ns[34],
        ns[35],
        loop_step(ns, s, body, st),
    );
    let counted = pair_e(
        matchr_e(var_e(ns[38]), ns[39], bin_e(Builtin::Add, pfst(var_e(a)), var_e(ns[33])), ns[39], var_e(ns[0])),
        var_e(ns[38]),
    );
    let_e(ns[33], bin_e(Builtin::Min, Expr::Int(16), remaining(ns, a)), let_e(ns[38], chunk, counted))
}

/// 段 j（0〜15）：段 j（0〜14）は fold(level_list, prev, |acc_j, item_j| 段 j + 1)、段 15 は一番内側の段。
pub open spec fn loop_level(j: nat, ns: Seq<nat>, s: nat, body: Expr, st: Ty) -> Expr
    decreases 15 - j,
{
    if j >= 15 {
        loop_inner(ns, s, body, st)
    } else {
        fold_e(
            level_list(ns, j),
            var_e(level_prev(ns, j)),
            ns[(3 + 2 * j) as int],
            ns[(4 + 2 * j) as int],
            loop_level(j + 1, ns, s, body, st),
        )
    }
}

/// loop(init, max, |s| e) の書換え（st は注釈の型 S）：let s0 = pair(0, ok<S, S>(init)) in let m = max in
/// let rg = range(0, 16) in let one = range(0, 1) in let nil = list<Int>() in
/// let fr = 段 0 in match_result(snd(fr), |r| none<S>(), |d| some(d))。
pub open spec fn loop_rw(init: Expr, max: Expr, s: nat, body: Expr, st: Ty, ns: Seq<nat>) -> Expr {
    let result = let_e(
        ns[42],
        loop_level(0, ns, s, body, st),
        matchr_e(psnd(var_e(ns[42])), ns[43], Expr::None(st), ns[37], some_e(var_e(ns[37]))),
    );
    let_e(
        ns[40],
        pair_e(Expr::Int(0), inj_e(true, st, init)),
        let_e(
            ns[0],
            max,
            let_e(
                ns[1],
                bin_e(Builtin::Range, Expr::Int(0), Expr::Int(16)),
                let_e(
                    ns[2],
                    bin_e(Builtin::Range, Expr::Int(0), Expr::Int(1)),
                    let_e(ns[41], Expr::List(Ty::Int, Seq::empty()), result),
                ),
            ),
        ),
    )
}

// ------------------------------------------------------------------ 書換えの型

/// 段の文脈の条件：ext(b, bs) で m は Int、rg・one・nil は List<Int>、段 j の初期状態は状態の型。列 bs の名前は
/// 束縛 s と違い、本体に現れない。
pub open spec fn level_ctx(ns: Seq<nat>, s: nat, body: Expr, st: Ty, b: Map<nat, Ty>, bs: Seq<(nat, Ty)>, j: nat) -> bool {
    &&& forall|k: int| 0 <= k < bs.len() ==> (#[trigger] bs[k]).0 != s && absent(bs[k].0, body)
    &&& has(ext(b, bs), ns[0], Ty::Int)
    &&& has(ext(b, bs), ns[1], li_ty())
    &&& has(ext(b, bs), ns[2], li_ty())
    &&& has(ext(b, bs), ns[41], li_ty())
    &&& has(ext(b, bs), level_prev(ns, j), st_ty(st))
}

/// 一番内側の段の一歩の型：acc が Result<S, S>、本体が s : S の下で Option<S> なら Result<S, S>。
proof fn step_typing(p: Prog, r: nat, ns: Seq<nat>, s: nat, max: Expr, body: Expr, st: Ty, b: Map<nat, Ty>, bs: Seq<(nat, Ty)>)
    requires
        loop_names(ns, s, max, body),
        forall|k: int| 0 <= k < bs.len() ==> (#[trigger] bs[k]).0 != s && absent(bs[k].0, body),
        ty_expr(p, r, b.insert(s, st), body) == Some(Ty::Option(Box::new(st))),
        has(ext(b, bs), ns[34], rs_ty(st)),
    ensures
        ty_expr(p, r, ext(b, bs), loop_step(ns, s, body, st)) == Some(rs_ty(st)),
{
    let c = ext(b, bs);
    let cs = c.insert(s, st);
    ext_body(p, r, b, bs, s, st, body);
    assert(ty_expr(p, r, cs, body) == Some(Ty::Option(Box::new(st))));
    t_var(p, r, cs, s, st);
    t_inj(p, r, cs, false, st, var_e(s));
    t_var(p, r, cs.insert(ns[36], st), ns[36], st);
    t_inj(p, r, cs.insert(ns[36], st), true, st, var_e(ns[36]));
    t_match(
        p,
        r,
        cs,
        body,
        inj_e(false, st, var_e(s)),
        ns[36],
        inj_e(true, st, var_e(ns[36])),
        st,
        rs_ty(st),
    );
    t_var(p, r, c.insert(ns[37], st), ns[37], st);
    t_inj(p, r, c.insert(ns[37], st), false, st, var_e(ns[37]));
    t_var(p, r, c, ns[34], rs_ty(st));
    t_matchr(
        p,
        r,
        c,
        var_e(ns[34]),
        s,
        match_e(body, inj_e(false, st, var_e(s)), ns[36], inj_e(true, st, var_e(ns[36]))),
        ns[37],
        inj_e(false, st, var_e(ns[37])),
        st,
        st,
        rs_ty(st),
    );
}

/// 一番内側の段の型：段 14 の acc が状態の型、m が Int なら、状態の型。
proof fn inner_typing(p: Prog, r: nat, ns: Seq<nat>, s: nat, max: Expr, body: Expr, st: Ty, b: Map<nat, Ty>, bs: Seq<(nat, Ty)>)
    requires
        loop_names(ns, s, max, body),
        forall|k: int| 0 <= k < bs.len() ==> (#[trigger] bs[k]).0 != s && absent(bs[k].0, body),
        ty_expr(p, r, b.insert(s, st), body) == Some(Ty::Option(Box::new(st))),
        has(ext(b, bs), ns[0], Ty::Int),
        has(ext(b, bs), ns[31], st_ty(st)),
    ensures
        ty_expr(p, r, ext(b, bs), loop_inner(ns, s, body, st)) == Some(st_ty(st)),
{
    let a = ns[31];
    let c = ext(b, bs);
    let rt = rs_ty(st);
    let pt = st_ty(st);
    // let n = min(16, sub(m, fst(a)))
    t_var(p, r, c, a, pt);
    t_proj(p, r, c, var_e(a), Ty::Int, rt);
    t_var(p, r, c, ns[0], Ty::Int);
    t_int2(p, r, c, var_e(ns[0]), pfst(var_e(a)));
    t_int2(p, r, c, Expr::Int(16), remaining(ns, a));
    let bs1 = bs.push((ns[33], Ty::Int));
    ext_push(b, bs, ns[33], Ty::Int);
    let c1 = ext(b, bs1);
    assert(c1 == c.insert(ns[33], Ty::Int));
    // let res = fold(range(0, n), snd(a), |acc, i| 一歩)
    t_var(p, r, c1, ns[33], Ty::Int);
    t_int2(p, r, c1, Expr::Int(0), var_e(ns[33]));
    t_var(p, r, c1, a, pt);
    t_proj(p, r, c1, var_e(a), Ty::Int, rt);
    let bs2 = bs1.push((ns[34], rt));
    let bs3 = bs2.push((ns[35], Ty::Int));
    ext_push(b, bs1, ns[34], rt);
    ext_push(b, bs2, ns[35], Ty::Int);
    assert(ext(b, bs3) == c1.insert(ns[34], rt).insert(ns[35], Ty::Int));
    assert forall|k: int| 0 <= k < bs3.len() implies (#[trigger] bs3[k]).0 != s && absent(bs3[k].0, body) by {
        if k < bs.len() {
            assert(bs3[k] == bs[k]);
        } else if k == bs.len() {
            assert(bs3[k] == (ns[33], Ty::Int));
        } else if k == bs.len() + 1 {
            assert(bs3[k] == (ns[34], rt));
        } else {
            assert(bs3[k] == (ns[35], Ty::Int));
        }
    }
    step_typing(p, r, ns, s, max, body, st, b, bs3);
    fold_typing(
        p,
        r,
        c1,
        bin_e(Builtin::Range, Expr::Int(0), var_e(ns[33])),
        psnd(var_e(a)),
        ns[34],
        ns[35],
        loop_step(ns, s, body, st),
        Ty::Int,
        rt,
    );
    let chunk = fold_e(
        bin_e(Builtin::Range, Expr::Int(0), var_e(ns[33])),
        psnd(var_e(a)),
        ns[34],
        ns[35],
        loop_step(ns, s, body, st),
    );
    // pair(match_result(res, |x| add(fst(a), n), |x| m), res)
    let c2 = c1.insert(ns[38], rt);
    let c3 = c2.insert(ns[39], st);
    t_var(p, r, c3, a, pt);
    t_proj(p, r, c3, var_e(a), Ty::Int, rt);
    t_var(p, r, c3, ns[33], Ty::Int);
    t_int2(p, r, c3, pfst(var_e(a)), var_e(ns[33]));
    t_var(p, r, c3, ns[0], Ty::Int);
    t_var(p, r, c2, ns[38], rt);
    t_matchr(
        p,
        r,
        c2,
        var_e(ns[38]),
        ns[39],
        bin_e(Builtin::Add, pfst(var_e(a)), var_e(ns[33])),
        ns[39],
        var_e(ns[0]),
        st,
        st,
        Ty::Int,
    );
    t_pair_e(
        p,
        r,
        c2,
        matchr_e(var_e(ns[38]), ns[39], bin_e(Builtin::Add, pfst(var_e(a)), var_e(ns[33])), ns[39], var_e(ns[0])),
        var_e(ns[38]),
        Ty::Int,
        rt,
    );
    let counted = pair_e(
        matchr_e(var_e(ns[38]), ns[39], bin_e(Builtin::Add, pfst(var_e(a)), var_e(ns[33])), ns[39], var_e(ns[0])),
        var_e(ns[38]),
    );
    t_let(p, r, c1, ns[38], chunk, counted, rt, pt);
    t_let(p, r, c, ns[33], bin_e(Builtin::Min, Expr::Int(16), remaining(ns, a)), let_e(ns[38], chunk, counted), Ty::Int, pt);
}

/// 段 j（0〜15）の型：段の文脈の条件の下で、状態の型。
proof fn level_typing(
    p: Prog,
    r: nat,
    j: nat,
    ns: Seq<nat>,
    s: nat,
    max: Expr,
    body: Expr,
    st: Ty,
    b: Map<nat, Ty>,
    bs: Seq<(nat, Ty)>,
)
    requires
        j <= 15,
        loop_names(ns, s, max, body),
        ty_expr(p, r, b.insert(s, st), body) == Some(Ty::Option(Box::new(st))),
        level_ctx(ns, s, body, st, b, bs, j),
    ensures
        ty_expr(p, r, ext(b, bs), loop_level(j, ns, s, body, st)) == Some(st_ty(st)),
    decreases 15 - j,
{
    let c = ext(b, bs);
    let pt = st_ty(st);
    if j >= 15 {
        assert(level_prev(ns, j) == ns[31]);
        inner_typing(p, r, ns, s, max, body, st, b, bs);
    } else {
        let a = ns[(3 + 2 * j) as int];
        let i = ns[(4 + 2 * j) as int];
        let prev = level_prev(ns, j);
        // 辿る列は List<Int>
        t_var(p, r, c, ns[0], Ty::Int);
        t_var(p, r, c, ns[1], li_ty());
        t_var(p, r, c, ns[2], li_ty());
        t_var(p, r, c, prev, pt);
        let width = Expr::Int(pow16((15 - j) as nat));
        if j == 0 {
            t_int2(p, r, c, width, var_e(ns[0]));
            t_if(p, r, c, bin_e(Builtin::Lt, width, var_e(ns[0])), var_e(ns[1]), var_e(ns[2]), li_ty());
        } else {
            t_var(p, r, c, ns[41], li_ty());
            t_proj(p, r, c, var_e(prev), Ty::Int, rs_ty(st));
            t_int2(p, r, c, var_e(ns[0]), pfst(var_e(prev)));
            t_int2(p, r, c, width, remaining(ns, prev));
            t_int2(p, r, c, pfst(var_e(prev)), var_e(ns[0]));
            t_if(p, r, c, bin_e(Builtin::Lt, width, remaining(ns, prev)), var_e(ns[1]), var_e(ns[2]), li_ty());
            t_if(
                p,
                r,
                c,
                bin_e(Builtin::Lt, pfst(var_e(prev)), var_e(ns[0])),
                if_e(bin_e(Builtin::Lt, width, remaining(ns, prev)), var_e(ns[1]), var_e(ns[2])),
                var_e(ns[41]),
                li_ty(),
            );
        }
        assert(ty_expr(p, r, c, level_list(ns, j)) == Some(li_ty()));
        // 段 j + 1 の文脈
        let bs1 = bs.push((a, pt));
        let bs2 = bs1.push((i, Ty::Int));
        ext_push(b, bs, a, pt);
        ext_push(b, bs1, i, Ty::Int);
        assert(ext(b, bs2) == c.insert(a, pt).insert(i, Ty::Int));
        assert(level_prev(ns, j + 1) == a);
        assert forall|k: int| 0 <= k < bs2.len() implies (#[trigger] bs2[k]).0 != s && absent(bs2[k].0, body) by {
            if k < bs.len() {
                assert(bs2[k] == bs[k]);
            } else if k == bs.len() {
                assert(bs2[k] == (a, pt));
            } else {
                assert(bs2[k] == (i, Ty::Int));
            }
        }
        assert(level_ctx(ns, s, body, st, b, bs2, j + 1));
        level_typing(p, r, j + 1, ns, s, max, body, st, b, bs2);
        fold_typing(
            p,
            r,
            c,
            level_list(ns, j),
            var_e(prev),
            a,
            i,
            loop_level(j + 1, ns, s, body, st),
            Ty::Int,
            pt,
        );
    }
}

/// loop の項目の形：第一の成分は init の型 S、第二の成分は本体の型 Option<S> で、形の型と同じ。max は Int。
pub proof fn loop_entry_shape(ts: Seq<Option<Ty>>)
    requires
        hof_entry(Form::Loop, ts) is Some,
    ensures
        hof_entry(Form::Loop, ts)->Some_0.1 == Ty::Option(Box::new(hof_entry(Form::Loop, ts)->Some_0.0)),
        form_ty(Form::Loop, ts) == Some(hof_entry(Form::Loop, ts)->Some_0.1),
        ts[0] == Some(hof_entry(Form::Loop, ts)->Some_0.0),
        ts[1] == Some(Ty::Int),
        ts[2] == Some(hof_entry(Form::Loop, ts)->Some_0.1),
{
}

/// 一致（loop）：被演算子の核の型が checker の型の消去なら（init は S の消去、max は Int、本体は束縛 s を S の消去に
/// した下で Option<S> の消去）、項目の S（の消去）を注釈に入れた書換えは、核の型付けで形の型 Option<S> の消去を持つ。
pub proof fn loop_rw_agrees(
    p: Prog,
    r: nat,
    ctx: Map<nat, Ty>,
    init: Expr,
    max: Expr,
    s: nat,
    body: Expr,
    ns: Seq<nat>,
    ts: Seq<Option<Ty>>,
)
    requires
        hof_entry(Form::Loop, ts) is Some,
        loop_names(ns, s, max, body),
        ty_expr(p, r, ctx, init) == Some(derase(ts[0]->Some_0)),
        ty_expr(p, r, ctx, max) == Some(derase(ts[1]->Some_0)),
        ty_expr(p, r, ctx.insert(s, derase(hof_entry(Form::Loop, ts)->Some_0.0)), body) == Some(
            derase(ts[2]->Some_0),
        ),
    ensures
        ty_expr(p, r, ctx, loop_rw(init, max, s, body, derase(hof_entry(Form::Loop, ts)->Some_0.0), ns)) == Some(
            derase(form_ty(Form::Loop, ts)->Some_0),
        ),
{
    loop_entry_shape(ts);
    let st0 = hof_entry(Form::Loop, ts)->Some_0.0;
    derase_parts(st0, st0);
    let st = derase(st0);
    let rt = rs_ty(st);
    let pt = st_ty(st);
    assert(derase(ts[2]->Some_0) == Ty::Option(Box::new(st)));
    assert(derase(form_ty(Form::Loop, ts)->Some_0) == Ty::Option(Box::new(st)));
    // let s0 = pair(0, ok<S, S>(init))
    t_inj(p, r, ctx, true, st, init);
    t_pair_e(p, r, ctx, Expr::Int(0), inj_e(true, st, init), Ty::Int, rt);
    // let m = max（s0 は max に現れない）
    let d0 = ctx.insert(ns[40], pt);
    ty_absent(p, r, ctx, max, ns[40], pt);
    // rg、one、nil
    let d1 = d0.insert(ns[0], Ty::Int);
    t_int2(p, r, d1, Expr::Int(0), Expr::Int(16));
    let d2 = d1.insert(ns[1], li_ty());
    t_int2(p, r, d2, Expr::Int(0), Expr::Int(1));
    let d3 = d2.insert(ns[2], li_ty());
    ty_nil(p, r, d3, Ty::Int);
    let d4 = d3.insert(ns[41], li_ty());
    // d4 は ctx に束縛の列 bs を足した文脈
    let bs = seq![(ns[40], pt), (ns[0], Ty::Int), (ns[1], li_ty()), (ns[2], li_ty()), (ns[41], li_ty())];
    let e = Seq::<(nat, Ty)>::empty();
    ext_push(ctx, e, ns[40], pt);
    ext_push(ctx, e.push((ns[40], pt)), ns[0], Ty::Int);
    ext_push(ctx, e.push((ns[40], pt)).push((ns[0], Ty::Int)), ns[1], li_ty());
    ext_push(ctx, e.push((ns[40], pt)).push((ns[0], Ty::Int)).push((ns[1], li_ty())), ns[2], li_ty());
    ext_push(
        ctx,
        e.push((ns[40], pt)).push((ns[0], Ty::Int)).push((ns[1], li_ty())).push((ns[2], li_ty())),
        ns[41],
        li_ty(),
    );
    assert(e.push((ns[40], pt)).push((ns[0], Ty::Int)).push((ns[1], li_ty())).push((ns[2], li_ty())).push(
        (ns[41], li_ty()),
    ) =~= bs);
    assert(ext(ctx, e) == ctx);
    assert(ext(ctx, bs) == d4);
    assert forall|k: int| 0 <= k < bs.len() implies (#[trigger] bs[k]).0 != s && absent(bs[k].0, body) by {
        assert(k == 0 || k == 1 || k == 2 || k == 3 || k == 4);
    }
    assert(level_prev(ns, 0) == ns[40]);
    assert(level_ctx(ns, s, body, st, ctx, bs, 0));
    level_typing(p, r, 0, ns, s, max, body, st, ctx, bs);
    // let fr = 段 0 in match_result(snd(fr), |r| none<S>(), |d| some(d))
    let d5 = d4.insert(ns[42], pt);
    t_var(p, r, d5, ns[42], pt);
    t_proj(p, r, d5, var_e(ns[42]), Ty::Int, rt);
    t_var(p, r, d5.insert(ns[37], st), ns[37], st);
    t_matchr(
        p,
        r,
        d5,
        psnd(var_e(ns[42])),
        ns[43],
        Expr::None(st),
        ns[37],
        some_e(var_e(ns[37])),
        st,
        st,
        Ty::Option(Box::new(st)),
    );
    let ot = Ty::Option(Box::new(st));
    let result = let_e(
        ns[42],
        loop_level(0, ns, s, body, st),
        matchr_e(psnd(var_e(ns[42])), ns[43], Expr::None(st), ns[37], some_e(var_e(ns[37]))),
    );
    t_let(
        p,
        r,
        d4,
        ns[42],
        loop_level(0, ns, s, body, st),
        matchr_e(psnd(var_e(ns[42])), ns[43], Expr::None(st), ns[37], some_e(var_e(ns[37]))),
        pt,
        ot,
    );
    t_let(p, r, d3, ns[41], Expr::List(Ty::Int, Seq::empty()), result, li_ty(), ot);
    let r3 = let_e(ns[41], Expr::List(Ty::Int, Seq::empty()), result);
    t_let(p, r, d2, ns[2], bin_e(Builtin::Range, Expr::Int(0), Expr::Int(1)), r3, li_ty(), ot);
    let r2 = let_e(ns[2], bin_e(Builtin::Range, Expr::Int(0), Expr::Int(1)), r3);
    t_let(p, r, d1, ns[1], bin_e(Builtin::Range, Expr::Int(0), Expr::Int(16)), r2, li_ty(), ot);
    let r1 = let_e(ns[1], bin_e(Builtin::Range, Expr::Int(0), Expr::Int(16)), r2);
    t_let(p, r, d0, ns[0], max, r1, Ty::Int, ot);
    t_let(p, r, ctx, ns[40], pair_e(Expr::Int(0), inj_e(true, st, init)), let_e(ns[0], max, r1), pt, ot);
}

/// 注釈の型は一つに決まる：書換えに型が付くなら、注釈の型は init の核の型。
pub proof fn loop_rw_note(p: Prog, r: nat, ctx: Map<nat, Ty>, init: Expr, max: Expr, s: nat, body: Expr, t: Ty, ns: Seq<nat>)
    requires
        ty_expr(p, r, ctx, loop_rw(init, max, s, body, t, ns)) is Some,
    ensures
        ty_expr(p, r, ctx, init) == Some(t),
{
    let e0 = pair_e(Expr::Int(0), inj_e(true, t, init));
    assert(ty_expr(p, r, ctx, e0) is Some);
    assert(ty_expr(p, r, ctx, inj_e(true, t, init)) is Some);
}

} // verus!
