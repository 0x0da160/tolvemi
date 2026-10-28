//! 段階 3 の直和型（DECISION-43、sum-route）：源の直和型の値（records_meaning.rs の RVal::Sum）と、その核の写し
//! （resolve.rs の構築子 rctor と、直和型の match の鎖 smatch_from）が一致することの補題。
//!
//! 構築子 k の値は vsum_from(k, n, 0, pv)（層 k より前は Err、層 k で Ok、最後の構築子は中身そのもの）。
//! 鎖は層 j ごとに被験式を調べ、値が層 j の構築子なら層 j の枝、そうでなければ Err の側の鎖（層 j + 1）を評価する。
//! 層 l < k の Err の束縛は位置 p0 + l（p0 は scope の長さ）、層 k の Ok の束縛は位置 p0 + k に入る（chain_env）。
//!
//! 証明：assume・admit・external_body なし。

use crate::bigstep::*;
use crate::records_meaning::*;
use crate::records_proof::*;
use crate::resolve::*;
use crate::spec::*;
use crate::syntax::{Spat, Sx};
use vstd::prelude::*;

verus! {

// ------------------------------------------------------------------ 定義

/// 空の名前を j 個足した scope（smatch_from の層 j の scope）。
pub open spec fn pushn(sc: Seq<Seq<char>>, j: nat) -> Seq<Seq<char>>
    decreases j,
{
    if j == 0 {
        sc
    } else {
        pushn(sc, (j - 1) as nat).push(Seq::empty())
    }
}

/// 構築子の値の中身（字段が無ければ Unit、あれば字段の値の写し rval）。構築子の値の字段の列 us に対する。
pub open spec fn pay_val(us: Seq<Val>) -> Val {
    if us.len() == 0 {
        Val::Unit
    } else {
        rval(us)
    }
}

/// 層 k の枝（smatch_from が層 k で使う枝）：束縛する名前の列（字段の名前）と、本体の Sx。枝が無ければ None。
pub open spec fn lay_sel(ents: Seq<Seq<char>>, arms: Seq<(Spat, Sx)>, k: nat) -> Option<(Seq<Seq<char>>, Sx)> {
    match layer_idx(ents, k, arms) {
        Some(ka) => if ka < arms.len() {
            match arm_binds_or_empty(arms[ka as int].0) {
                Some(bs) => Some((bs, arms[ka as int].1)),
                None => None,
            }
        } else {
            None
        },
        None => None,
    }
}

/// 層 k の本体の核の式（smatch_from の層 k の rx）。枝の束縛が正しくなければ None。
pub open spec fn lay_body(fs: Seq<Seq<char>>, tb: Seq<(Seq<char>, Option<Ty>, Seq<Seq<char>>, Option<Ty>)>, sc0: Seq<Seq<char>>, ents: Seq<Seq<char>>, arms: Seq<(Spat, Sx)>, k: nat) -> Option<Expr> {
    match lay_sel(ents, arms, k) {
        Some((bs, sx)) => if !arm_ok(bs) || !binds_fresh(pushn(sc0, k), bs) {
            None
        } else {
            rx(fs, tb, false, arm_scope(pushn(sc0, k), bs), sx)
        },
        None => None,
    }
}

/// 層 k の枝の式（smatch_from が層 k で作る、字段を束縛した本体）。被験式の値の位置は sc0.len() + k。
pub open spec fn lay_wrap(fs: Seq<Seq<char>>, tb: Seq<(Seq<char>, Option<Ty>, Seq<Seq<char>>, Option<Ty>)>, sc0: Seq<Seq<char>>, ents: Seq<Seq<char>>, arms: Seq<(Spat, Sx)>, k: nat) -> Option<Expr> {
    match lay_sel(ents, arms, k) {
        Some((bs, _)) => match lay_body(fs, tb, sc0, ents, arms, k) {
            Some(body) => Some(arm_wrap(sc0.len() + k, bs, body)),
            None => None,
        },
        None => None,
    }
}

/// 鎖の評価の環境（層 j から層 k まで）。層 l（j <= l < k）の Err の束縛は位置 p0 + l に、層 l + 1 から先の値。
/// 層 k の Ok の束縛は位置 p0 + k に、中身の値 pv。
pub open spec fn chain_env(cenv: Map<nat, Val>, p0: nat, j: nat, k: nat, n: nat, pv: Val) -> Map<nat, Val>
    decreases k - j,
{
    if j >= k {
        cenv.insert(p0 + k, pv)
    } else {
        chain_env(cenv.insert(p0 + j, vsum_from(k, n, j + 1, pv)), p0, j + 1, k, n, pv)
    }
}

/// 字段の束縛の環境：位置 pos + 1 + i（i から先）に値 vs[i]（arm_wrap の Let の列と同じ位置）。
pub open spec fn fenv(cenv: Map<nat, Val>, pos: nat, vs: Seq<Val>, i: nat) -> Map<nat, Val>
    decreases vs.len() - i,
{
    if i >= vs.len() {
        cenv
    } else {
        fenv(cenv.insert(pos + 1 + i, vs[i as int]), pos, vs, i + 1)
    }
}

/// 枝の本体の核の式が解決する（smatch_from の層の rx が Some）。
pub open spec fn body_is_some(fs: Seq<Seq<char>>, tb: Seq<(Seq<char>, Option<Ty>, Seq<Seq<char>>, Option<Ty>)>, sc: Seq<Seq<char>>, bs: Seq<Seq<char>>, sx: Sx) -> bool {
    rx(fs, tb, false, arm_scope(sc, bs), sx) is Some
}

/// 枝の字段の名前の位置（枝の本体の scope で、字段の値が束縛される位置）：字段が二つ以上なら p + 1 + i（arm_wrap の射影の位置）、
/// 一つなら字段の値そのものの位置 p（arm_scope が名前を p に置く）、無ければ空。
pub open spec fn arm_ids(p: nat, bs: Seq<Seq<char>>) -> Seq<nat> {
    if bs.len() >= 2 {
        Seq::new(bs.len(), |i: int| (p + 1 + i) as nat)
    } else if bs.len() == 1 {
        seq![p]
    } else {
        Seq::empty()
    }
}

// ------------------------------------------------------------------ 補題

/// pushn の一段：層 j + 1 の scope は、層 j の scope に空の名前を一つ足したもの。
pub proof fn pushn_succ(sc: Seq<Seq<char>>, j: nat)
    ensures
        pushn(sc, j + 1) == pushn(sc, j).push(Seq::empty()),
{
    assert(pushn(sc, j + 1) == pushn(sc, (j + 1 - 1) as nat).push(Seq::empty()));
    assert((j + 1 - 1) as nat == j);
}

/// pushn の長さ。
pub proof fn pushn_len(sc: Seq<Seq<char>>, j: nat)
    ensures
        pushn(sc, j).len() == sc.len() + j,
    decreases j,
{
    if j > 0 {
        pushn_len(sc, (j - 1) as nat);
        pushn_succ(sc, (j - 1) as nat);
    }
}

/// 核の構築子の値（inj_from）の評価：層 j から、構築子 k（構築子は n 個）の値 v を作る式は、vsum_from(k, n, j, v) に評価される。
pub proof fn inj_eval(p: Prog, env: Map<nat, Val>, t: Ty, n: nat, k: nat, j: nat, pe: Expr, v: Val)
    requires
        j <= k,
        k < n,
        inj_from(t, n, k, j, pe) is Some,
        evals_to(p, env, pe, v),
    ensures
        evals_to(p, env, inj_from(t, n, k, j, pe)->Some_0, vsum_from(k, n, j, v)),
    decreases k - j,
{
    reveal_with_fuel(inj_from, 2);
    reveal_with_fuel(vsum_from, 2);
    if j >= k {
        if k + 1 < n {
            let u = pay_at(t, n, k)->Some_0;
            let vt = tail_ty(t, k + 1)->Some_0;
            assert(inj_from(t, n, k, j, pe) == Some(Expr::Inj(true, u, vt, Box::new(pe))));
            bs_inj(p, env, true, u, vt, pe, v);
        } else {
            assert(inj_from(t, n, k, j, pe) == Some(pe));
        }
    } else {
        let u = pay_at(t, n, j)->Some_0;
        let vt = tail_ty(t, j + 1)->Some_0;
        let x = inj_from(t, n, k, j + 1, pe)->Some_0;
        assert(inj_from(t, n, k, j + 1, pe) is Some);
        assert(inj_from(t, n, k, j, pe) == Some(Expr::Inj(false, u, vt, Box::new(x))));
        inj_eval(p, env, t, n, k, j + 1, pe, v);
        bs_inj(p, env, false, u, vt, x, vsum_from(k, n, j + 1, v));
    }
}

/// 構築子への呼出し（rctor）の評価：字段の式が値 us に評価されるなら、構築子の値は vsum_from(k, n, 0, pay_val(us)) に評価される。
pub proof fn ctor_sound(p: Prog, env: Map<nat, Val>, tb: Seq<(Seq<char>, Option<Ty>, Seq<Seq<char>>, Option<Ty>)>, c: Seq<char>, xs: Seq<Expr>, us: Seq<Val>, i: nat, k: nat, e: Expr)
    requires
        rctor(tb, false, c, xs) == Some(e),
        vlook(tb, c) == Some((i, k, xs.len())),
        fields_to(p, env, xs, us),
    ensures
        evals_to(p, env, e, vsum_from(k, tb[i as int].2.len(), 0, pay_val(us))),
{
    let n = tb[i as int].2.len();
    assert(k < n);
    let t = tb[i as int].1->Some_0;
    assert(tb[i as int].1 is Some);
    assert(e == inj_from(t, n, k, 0, pay_nested(xs))->Some_0);
    if xs.len() == 0 {
        assert(pay_nested(xs) == Expr::Unit);
        bs_leaf(p, env, Expr::Unit);
        assert(pay_val(us) == Val::Unit);
    } else {
        assert(pay_nested(xs) == rbuild(xs));
        rbuild_fwd(p, env, xs, us);
        assert(pay_val(us) == rval(us));
    }
    inj_eval(p, env, t, n, k, 0, pay_nested(xs), pay_val(us));
}

/// 字段の束縛（arm_wrap の Let の列）の評価：字段の値の写し rval(vs) を位置 pos に持つ環境で、字段を束縛した本体は本体の値に評価される。
pub proof fn binds_sound(p: Prog, cenv: Map<nat, Val>, pos: nat, vs: Seq<Val>, i: nat, body: Expr, w: Val)
    requires
        vs.len() >= 1,
        i <= vs.len(),
        cenv.contains_key(pos),
        cenv[pos] == rval(vs),
        evals_to(p, fenv(cenv, pos, vs, i), body, w),
    ensures
        evals_to(p, cenv, binds_lets(pos, vs.len(), i, body), w),
    decreases vs.len() - i,
{
    reveal_with_fuel(binds_lets, 2);
    if i >= vs.len() {
        assert(binds_lets(pos, vs.len(), i, body) == body);
        assert(fenv(cenv, pos, vs, i) == cenv);
    } else {
        let m = vs.len();
        bs_var(p, cenv, pos);
        rfield_eval(p, cenv, Expr::Var(pos), vs, i);
        let cenv2 = cenv.insert(pos + 1 + i, vs[i as int]);
        assert(pos + 1 + i != pos);
        assert(cenv2.contains_key(pos) && cenv2[pos] == rval(vs));
        assert(fenv(cenv2, pos, vs, i + 1) == fenv(cenv, pos, vs, i));
        binds_sound(p, cenv2, pos, vs, i + 1, body, w);
        assert(binds_lets(pos, m, i, body) == Expr::Let(pos + 1 + i, Box::new(rfield(Expr::Var(pos), i, m)), Box::new(binds_lets(pos, m, i + 1, body))));
        bs_let(p, cenv, pos + 1 + i, rfield(Expr::Var(pos), i, m), binds_lets(pos, m, i + 1, body), vs[i as int], w);
    }
}

/// 枝の式（arm_wrap）の評価：字段が二つ以上なら字段を束縛して本体を評価し、そうでなければ本体そのものを評価する。
pub proof fn arm_wrap_sound(p: Prog, cenv: Map<nat, Val>, pos: nat, bs: Seq<Seq<char>>, body: Expr, vs: Seq<Val>, w: Val)
    requires
        bs.len() >= 2 ==> vs.len() == bs.len(),
        bs.len() >= 2 ==> cenv.contains_key(pos) && cenv[pos] == rval(vs),
        bs.len() >= 2 ==> evals_to(p, fenv(cenv, pos, vs, 0), body, w),
        bs.len() < 2 ==> evals_to(p, cenv, body, w),
    ensures
        evals_to(p, cenv, arm_wrap(pos, bs, body), w),
{
    if bs.len() >= 2 {
        assert(arm_wrap(pos, bs, body) == binds_lets(pos, bs.len(), 0, body));
        binds_sound(p, cenv, pos, vs, 0, body, w);
    } else {
        assert(arm_wrap(pos, bs, body) == body);
    }
}

/// 鎖の定理（層 j から）：smatch_from の結果 c は、被験式 s が層 j で vsum_from(k, n, j, pv) に評価され（j <= k < n）、
/// 層 k の枝の式（lay_wrap）が chain_env の環境で w に評価されるなら、w に評価される。
pub proof fn smatch_chain(p: Prog, fs: Seq<Seq<char>>, tb: Seq<(Seq<char>, Option<Ty>, Seq<Seq<char>>, Option<Ty>)>, sc0: Seq<Seq<char>>, ents: Seq<Seq<char>>, arms: Seq<(Spat, Sx)>, j: nat, s: Expr, c: Expr, cenv: Map<nat, Val>, k: nat, pv: Val, w: Val)
    requires
        j <= k < ents.len(),
        smatch_from(fs, tb, false, pushn(sc0, j), ents, arms, j, s) == Some(c),
        evals_to(p, cenv, s, vsum_from(k, ents.len(), j, pv)),
        lay_wrap(fs, tb, sc0, ents, arms, k) is Some,
        evals_to(p, chain_env(cenv, sc0.len(), j, k, ents.len(), pv), lay_wrap(fs, tb, sc0, ents, arms, k)->Some_0, w),
    ensures
        evals_to(p, cenv, c, w),
    decreases k - j,
{
    reveal_with_fuel(smatch_from, 2);
    reveal_with_fuel(chain_env, 2);
    reveal_with_fuel(vsum_from, 2);
    pushn_len(sc0, j);
    let n = ents.len();
    let sc = pushn(sc0, j);
    assert(layer_idx(ents, j, arms) is Some) by {
        if layer_idx(ents, j, arms) is None {
            assert(smatch_from(fs, tb, false, sc, ents, arms, j, s) is None);
        }
    }
    let ka = layer_idx(ents, j, arms)->Some_0;
    assert(ka < arms.len()) by {
        if ka >= arms.len() {
            assert(smatch_from(fs, tb, false, sc, ents, arms, j, s) is None);
        }
    }
    assert(arm_binds_or_empty(arms[ka as int].0) is Some) by {
        if arm_binds_or_empty(arms[ka as int].0) is None {
            assert(smatch_from(fs, tb, false, sc, ents, arms, j, s) is None);
        }
    }
    let bs = arm_binds_or_empty(arms[ka as int].0)->Some_0;
    assert(lay_sel(ents, arms, j) == Some((bs, arms[ka as int].1)));
    assert(body_is_some(fs, tb, sc, bs, arms[ka as int].1)) by {
        if !body_is_some(fs, tb, sc, bs, arms[ka as int].1) {
            assert(smatch_from(fs, tb, false, sc, ents, arms, j, s) is None);
        }
    }
    let bo = rx(fs, tb, false, arm_scope(sc, bs), arms[ka as int].1)->Some_0;
    let aw = arm_wrap(sc.len(), bs, bo);
    assert(sc.len() == sc0.len() + j);
    if j == k {
        assert(lay_body(fs, tb, sc0, ents, arms, k) == Some(bo));
        assert(lay_wrap(fs, tb, sc0, ents, arms, k) == Some(aw));
        assert(chain_env(cenv, sc0.len(), k, k, n, pv) == cenv.insert(sc0.len() + k, pv));
        assert(cenv.insert(sc0.len() + k, pv) == cenv.insert(sc.len(), pv));
        if j + 1 == n {
            assert(vsum_from(k, n, k, pv) == pv);
            assert(smatch_from(fs, tb, false, sc, ents, arms, j, s) == Some(Expr::Let(sc.len(), Box::new(s), Box::new(aw))));
            bs_let(p, cenv, sc.len(), s, aw, pv, w);
        } else {
            assert(vsum_from(k, n, k, pv) == Val::Ok(Box::new(pv)));
            let rest = smatch_from(fs, tb, false, sc.push(Seq::empty()), ents, arms, j + 1, Expr::Var(sc.len())) ->Some_0;
            assert(smatch_from(fs, tb, false, sc, ents, arms, j, s) == Some(Expr::MatchR(Box::new(s), sc.len(), Box::new(aw), sc.len(), Box::new(rest))));
            bs_matchr(p, cenv, s, sc.len(), aw, sc.len(), rest, Val::Ok(Box::new(pv)), w);
        }
    } else {
        // 層 j は Err の側に進む：被験式の値は Err（層 j + 1 から先の値）
        let inner = vsum_from(k, n, j + 1, pv);
        assert(vsum_from(k, n, j, pv) == Val::Err(Box::new(inner)));
        let rest = smatch_from(fs, tb, false, sc.push(Seq::empty()), ents, arms, j + 1, Expr::Var(sc.len())) ->Some_0;
        assert(smatch_from(fs, tb, false, sc, ents, arms, j, s) == Some(Expr::MatchR(Box::new(s), sc.len(), Box::new(aw), sc.len(), Box::new(rest))));
        pushn_succ(sc0, j);
        assert(pushn(sc0, j + 1) == sc.push(Seq::empty()));
        let cenv2 = cenv.insert(sc.len(), inner);
        assert(chain_env(cenv, sc0.len(), j, k, n, pv) == chain_env(cenv2, sc0.len(), j + 1, k, n, pv));
        bs_var(p, cenv2, sc.len());
        assert(cenv2[sc.len()] == inner);
        smatch_chain(p, fs, tb, sc0, ents, arms, j + 1, Expr::Var(sc.len()), rest, cenv2, k, pv, w);
        bs_matchr(p, cenv, s, sc.len(), aw, sc.len(), rest, Val::Err(Box::new(inner)), w);
    }
}

/// pushn は下の名前を変えない（n が元の scope の中にあれば、その名前は同じ）。
pub proof fn pushn_index(sc: Seq<Seq<char>>, j: nat, n: nat)
    requires
        n < sc.len(),
    ensures
        pushn(sc, j)[n as int] == sc[n as int],
    decreases j,
{
    if j > 0 {
        pushn_index(sc, (j - 1) as nat, n);
        pushn_succ(sc, (j - 1) as nat);
        pushn_len(sc, (j - 1) as nat);
        assert(pushn(sc, j) == pushn(sc, (j - 1) as nat).push(Seq::empty()));
    }
}

/// 鎖の環境は位置 p0 より下の名前を変えない（chain_env は位置 p0 以上にだけ足す）。
pub proof fn chain_env_keep(cenv: Map<nat, Val>, p0: nat, j: nat, k: nat, n: nat, pv: Val, q: nat)
    requires
        q < p0,
    ensures
        chain_env(cenv, p0, j, k, n, pv).contains_key(q) == cenv.contains_key(q),
        cenv.contains_key(q) ==> chain_env(cenv, p0, j, k, n, pv)[q] == cenv[q],
    decreases k - j,
{
    reveal_with_fuel(chain_env, 2);
    if j < k {
        chain_env_keep(cenv.insert(p0 + j, vsum_from(k, n, j + 1, pv)), p0, j + 1, k, n, pv, q);
    }
}

/// 鎖の環境の位置 p0 + k は、層 k の Ok の中身 pv を持つ（j <= k）。
pub proof fn chain_env_at(cenv: Map<nat, Val>, p0: nat, j: nat, k: nat, n: nat, pv: Val)
    requires
        j <= k,
    ensures
        chain_env(cenv, p0, j, k, n, pv).contains_key(p0 + k),
        chain_env(cenv, p0, j, k, n, pv)[p0 + k] == pv,
    decreases k - j,
{
    reveal_with_fuel(chain_env, 2);
    if j < k {
        chain_env_at(cenv.insert(p0 + j, vsum_from(k, n, j + 1, pv)), p0, j + 1, k, n, pv);
    }
}

/// 核の構築子の式（inj_from）は、中身の式 pe が位置 n を参照も束縛もしないなら、位置 n を参照も束縛もしない。
pub proof fn absent_inj(n: nat, t: Ty, m: nat, k: nat, j: nat, pe: Expr, e: Expr)
    requires
        inj_from(t, m, k, j, pe) == Some(e),
        absent(n, pe),
    ensures
        absent(n, e),
    decreases k - j,
{
    reveal_with_fuel(inj_from, 2);
    reveal_with_fuel(absent, 2);
    if j < k {
        assert(inj_from(t, m, k, j + 1, pe) is Some);
        absent_inj(n, t, m, k, j + 1, pe, inj_from(t, m, k, j + 1, pe)->Some_0);
    }
}

/// 直和型の鎖の下端：層 k（j <= k < n）の枝の式は、鎖（smatch_from）が値を持つなら、枝の選び方（lay_body）が Some である。
pub proof fn lay_body_some(fs: Seq<Seq<char>>, tb: Seq<(Seq<char>, Option<Ty>, Seq<Seq<char>>, Option<Ty>)>, sc0: Seq<Seq<char>>, ents: Seq<Seq<char>>, arms: Seq<(Spat, Sx)>, j: nat, s: Expr, c: Expr, k: nat)
    requires
        j <= k < ents.len(),
        smatch_from(fs, tb, false, pushn(sc0, j), ents, arms, j, s) == Some(c),
    ensures
        lay_body(fs, tb, sc0, ents, arms, k) is Some,
    decreases ents.len() - j,
{
    reveal_with_fuel(smatch_from, 2);
    let sc = pushn(sc0, j);
    assert(layer_idx(ents, j, arms) is Some) by {
        if layer_idx(ents, j, arms) is None {
            assert(smatch_from(fs, tb, false, sc, ents, arms, j, s) is None);
        }
    }
    let ka = layer_idx(ents, j, arms)->Some_0;
    assert(ka < arms.len()) by {
        if ka >= arms.len() {
            assert(smatch_from(fs, tb, false, sc, ents, arms, j, s) is None);
        }
    }
    assert(arm_binds_or_empty(arms[ka as int].0) is Some) by {
        if arm_binds_or_empty(arms[ka as int].0) is None {
            assert(smatch_from(fs, tb, false, sc, ents, arms, j, s) is None);
        }
    }
    let bs = arm_binds_or_empty(arms[ka as int].0)->Some_0;
    assert(lay_sel(ents, arms, j) == Some((bs, arms[ka as int].1)));
    assert(arm_ok(bs) && binds_fresh(sc, bs)) by {
        if !(arm_ok(bs) && binds_fresh(sc, bs)) {
            assert(smatch_from(fs, tb, false, sc, ents, arms, j, s) is None);
        }
    }
    assert(rx(fs, tb, false, arm_scope(sc, bs), arms[ka as int].1) is Some) by {
        if rx(fs, tb, false, arm_scope(sc, bs), arms[ka as int].1) is None {
            assert(smatch_from(fs, tb, false, sc, ents, arms, j, s) is None);
        }
    }
    if j == k {
        assert(lay_body(fs, tb, sc0, ents, arms, k) is Some);
    } else {
        assert(j + 1 < ents.len());
        let rest = smatch_from(fs, tb, false, sc.push(Seq::empty()), ents, arms, j + 1, Expr::Var(sc.len()))->Some_0;
        assert(smatch_from(fs, tb, false, sc.push(Seq::empty()), ents, arms, j + 1, Expr::Var(sc.len())) is Some) by {
            if smatch_from(fs, tb, false, sc.push(Seq::empty()), ents, arms, j + 1, Expr::Var(sc.len())) is None {
                assert(smatch_from(fs, tb, false, sc, ents, arms, j, s) is None);
            }
        }
        pushn_succ(sc0, j);
        assert(pushn(sc0, j + 1) == sc.push(Seq::empty()));
        lay_body_some(fs, tb, sc0, ents, arms, j + 1, Expr::Var(sc.len()), rest, k);
    }
}

} // verus!
