//! 段階 2 の S4b：名前解決（rx、印なし）が源の意味（rmean、S4a）を保つこと（順方向の部分正しさ）。
//!
//! 源の式 Sx の腕（Int、Bool、Unit、Chr、Str、None、Some、List、Var、Pair、Fld、Rec、If、Let、Match、Fold、Builtin、Call）を、字段を位置で書いた RExpr に写す（rsrc）。
//! 写しは rx と同じ scope で名前を解決する（記録の基の深い scope は rx と同じ判定 deep_rec で決める）。
//! 宣言の字段の列は pdecl（0、1、…）。定理 `resolve_sound`：rx が核の式 c を返し、rsrc が源の式 r を返し、
//! rmean(r) が値 v を持つなら、c は vof(v) に評価される。持ち主の型は見ない（部分正しさ）。
//! 他の Sx の腕は rsrc が None なので、定理は何も述べない。印つき（tagged）は扱わない。
//! 呼出しは呼出し先の本体を深さ dep まで埋め込む。循環する呼出し（rec の関数）は、どの深さでも None なので、定理は何も述べない。
//!
//! 証明：assume・admit・external_body なし。

use crate::bigstep::*;
use crate::proof::*;
use crate::records_exec::*;
use crate::records_meaning::*;
use crate::records_proof::*;
use crate::resolve::*;
use crate::spec::*;
use crate::sums_commute::*;
use crate::syntax::{Sd, Spat, Sx};
use vstd::prelude::*;

verus! {

// ------------------------------------------------------------------ 定義

/// 字段の位置の列：宣言の n 個の字段を 0、1、…、n-1 とする（源の字段は宣言の中の位置で書く）。
pub open spec fn pdecl(n: nat) -> Seq<nat> {
    Seq::new(n, |j: int| j as nat)
}

/// 核の環境と源の環境：源の環境にある名前ごとに、核の環境にあり、その値が源の値の写しである。
pub open spec fn envrel(cenv: Map<nat, Val>, renv: Map<nat, RVal>) -> bool {
    forall|k: nat| #[trigger] renv.contains_key(k) ==> cenv.contains_key(k) && cenv[k] == vof(renv[k])
}

/// 源の環境の名前は、すべて scope の長さより下にある（let・呼出し・枝で足す名前の位置は scope の長さ）。
/// 直和型の枝の鎖は、位置 sc.len() 以上に束縛を足すので、源の環境の名前と混ざらないためにこれを使う。
pub open spec fn renv_below(renv: Map<nat, RVal>, sc: Seq<Seq<char>>) -> bool {
    forall|k: nat| #[trigger] renv.contains_key(k) ==> k < sc.len()
}

/// `_` だけの直和型の match（any_arms）の式。
pub open spec fn any_sm(e: Sx) -> bool {
    match e {
        Sx::SumMatch(_, arms) => any_arms(arms),
        _ => false,
    }
}

/// 関数の表の対応：核の関数の列 p.funcs は、関数の宣言の列 fds を印なしで解決したものである（resolve_t の関数の表）。
/// 名前の表は fds の名前で、呼出しの番号 g は fds[g] と p.funcs[g] を指す。
pub open spec fn funcs_ok(p: Prog, fs: Seq<Seq<char>>, tb: Seq<(Seq<char>, Option<Ty>, Seq<Seq<char>>, Option<Ty>)>, fds: Seq<Sd>) -> bool {
    fs == names_of(fds) && rfuncs(fs, tb, false, fds, fds.len()) == Some(p.funcs)
}

/// rfuncs の列の長さは n。
proof fn rfuncs_len(fs: Seq<Seq<char>>, tb: Seq<(Seq<char>, Option<Ty>, Seq<Seq<char>>, Option<Ty>)>, ds: Seq<Sd>, n: nat, funcs: Seq<Func>)
    requires
        n <= ds.len(),
        rfuncs(fs, tb, false, ds, n) == Some(funcs),
    ensures
        funcs.len() == n,
    decreases n,
{
    if n > 0 {
        reveal_with_fuel(rfuncs, 1);
        assert(rfuncs(fs, tb, false, ds, (n - 1) as nat) is Some && rfunc(fs, tb, false, ds[(n - 1) as int]) is Some);
        let a = rfuncs(fs, tb, false, ds, (n - 1) as nat)->Some_0;
        rfuncs_len(fs, tb, ds, (n - 1) as nat, a);
    }
}

/// rfuncs の g 番目：それは宣言 ds[g] の関数の解決である。
proof fn rfuncs_at(fs: Seq<Seq<char>>, tb: Seq<(Seq<char>, Option<Ty>, Seq<Seq<char>>, Option<Ty>)>, ds: Seq<Sd>, n: nat, funcs: Seq<Func>, g: nat)
    requires
        n <= ds.len(),
        rfuncs(fs, tb, false, ds, n) == Some(funcs),
        g < n,
    ensures
        rfunc(fs, tb, false, ds[g as int]) == Some(funcs[g as int]),
    decreases n,
{
    reveal_with_fuel(rfuncs, 1);
    assert(rfuncs(fs, tb, false, ds, (n - 1) as nat) is Some && rfunc(fs, tb, false, ds[(n - 1) as int]) is Some);
    let a = rfuncs(fs, tb, false, ds, (n - 1) as nat)->Some_0;
    let f = rfunc(fs, tb, false, ds[(n - 1) as int])->Some_0;
    assert(funcs == a.push(f));
    rfuncs_len(fs, tb, ds, (n - 1) as nat, a);
    if g + 1 == n {
        assert(funcs[g as int] == f);
    } else {
        rfuncs_at(fs, tb, ds, (n - 1) as nat, a, g);
        assert(funcs[g as int] == a[g as int]);
    }
}

/// 関数の表の g 番目：fds[g] は関数の宣言で、その解決（字段の列と本体）は核の g 番目に等しい。
proof fn funcs_at(p: Prog, fs: Seq<Seq<char>>, tb: Seq<(Seq<char>, Option<Ty>, Seq<Seq<char>>, Option<Ty>)>, fds: Seq<Sd>, g: nat)
    requires
        funcs_ok(p, fs, tb, fds),
        g < fds.len(),
    ensures
        p.funcs.len() == fds.len(),
        fds[g as int] is Fn,
        match fds[g as int] {
            Sd::Fn(_, ps, _, b) => p.funcs[g as int].params == rparams(ps, tb, false) && rx(fs, tb, false, pnames(ps), b) == Some(p.funcs[g as int].body),
            _ => false,
        },
{
    rfuncs_len(fs, tb, fds, fds.len(), p.funcs);
    rfuncs_at(fs, tb, fds, fds.len(), p.funcs, g);
    match fds[g as int] {
        Sd::Fn(_, ps, _, b) => {
            assert(rx(fs, tb, false, pnames(ps), b) is Some);
            assert(p.funcs[g as int].params == rparams(ps, tb, false));
            assert(rx(fs, tb, false, pnames(ps), b) == Some(p.funcs[g as int].body));
        },
        _ => {},
    }
}

/// 呼出しの束縛：核の bind（引数の写し）と源の rbind（引数の値）は、位置 i < n で envrel の対応にある。
proof fn envrel_bind(params: Seq<(nat, Ty)>, vs: Seq<RVal>, n: nat)
    requires
        n <= vs.len(),
        n <= params.len(),
        forall|i: nat| i < n ==> params[i as int].0 == i,
    ensures
        envrel(bind(params, vofs(vs, 0), n), rbind(vs, n)),
    decreases n,
{
    vofs_len(vs, 0);
    if n > 0 {
        envrel_bind(params, vs, (n - 1) as nat);
        vofs_at(vs, (n - 1) as nat);
        envrel_ins(bind(params, vofs(vs, 0), (n - 1) as nat), rbind(vs, (n - 1) as nat), (n - 1) as nat, vs[(n - 1) as int]);
        assert(bind(params, vofs(vs, 0), n) == bind(params, vofs(vs, 0), (n - 1) as nat).insert(params[(n - 1) as int].0, vofs(vs, 0)[(n - 1) as int]));
        assert(rbind(vs, n) == rbind(vs, (n - 1) as nat).insert((n - 1) as nat, vs[(n - 1) as int]));
    }
}

/// 源の式の写し（位置で書いた字段）。resolve.rs の rx の記録の腕と同じ名前の解決を
/// 写す。rx が拒否する形（字段の重複、未知の字段、空の宣言）は、ここでは拒否しない（rx が None なら定理は空）。
/// let の番号は rx と同じく sc.len()。記録の基は rx で解決して深さ（deep_rec）を決め、字段の式はその scope で写す。
/// 呼出しは、呼出し先の本体を深さ dep まで写す（dep が 0 の呼出しは None）。循環する呼出しは、どの深さでも None になる。
pub open spec fn rsrc(fs: Seq<Seq<char>>, tb: Seq<(Seq<char>, Option<Ty>, Seq<Seq<char>>, Option<Ty>)>, fds: Seq<Sd>, dep: nat, sc: Seq<Seq<char>>, e: Sx) -> Option<RExpr>
    decreases dep, e, 0nat,
{
    match e {
        Sx::Int(n) => Some(RExpr::Int(n)),
        Sx::Bool(b) => Some(RExpr::Bool(b)),
        Sx::Chr(c) => Some(RExpr::Char(c as u32 as int)),
        Sx::None(t) => match to_ty(t, tb, false) {
            Some(_) => Some(RExpr::None),
            None => None,
        },
        Sx::Some(a) => match rsrc(fs, tb, fds, dep, sc, *a) {
            Some(r) => Some(RExpr::Some(Box::new(r))),
            None => None,
        },
        Sx::Unit => Some(RExpr::Unit),
        Sx::Var(x) => if x.len() == 0 {
            None
        } else {
            match idx(sc, x, 0) {
                Some(k) => Some(RExpr::Var(k)),
                // 局所の名前でないもの：字段のない構築子。
                None => rsrc_ctor(tb, x, Seq::empty()),
            }
        },
        Sx::Pair(a, b) => match (rsrc(fs, tb, fds, dep, sc, *a), rsrc(fs, tb, fds, dep, sc, *b)) {
            (Some(u), Some(w)) => Some(RExpr::Pair(Box::new(u), Box::new(w))),
            _ => None,
        },
        Sx::Fld(a, fls) => match rsrc(fs, tb, fds, dep, sc, *a) {
            Some(r) => rsrc_chain(tb, fds, dep, r, fls, 0),
            None => None,
        },
        Sx::Rec(r, fls, base) => match idx(tnames(tb), r, 0) {
            Some(k) => match base {
                None => match rsrc_ws(fs, tb, fds, dep, sc, tb[k as int].2, fls, 0) {
                    Some(ws) => Some(RExpr::Rec(pdecl(tb[k as int].2.len()), ws, None)),
                    None => None,
                },
                Some(b) => match (rsrc(fs, tb, fds, dep, sc, *b), rx(fs, tb, false, sc, *b)) {
                    (Some(br), Some(bx)) => {
                        let sc2 = scope2(sc, deep_rec(Some(bx), tb[k as int].2, fls));
                        match rsrc_ws(fs, tb, fds, dep, sc2, tb[k as int].2, fls, 0) {
                            Some(ws) => Some(RExpr::Rec(pdecl(tb[k as int].2.len()), ws, Some(Box::new(br)))),
                            None => None,
                        }
                    },
                    _ => None,
                },
            },
            None => None,
        },
        Sx::If(c, a, b) => match (rsrc(fs, tb, fds, dep, sc, *c), rsrc(fs, tb, fds, dep, sc, *a), rsrc(fs, tb, fds, dep, sc, *b)) {
            (Some(x), Some(y), Some(z)) => Some(RExpr::If(Box::new(x), Box::new(y), Box::new(z))),
            _ => None,
        },
        Sx::Let(x, a, b) => if idx(sc, x, 0) is Some {
            None
        } else {
            match (rsrc(fs, tb, fds, dep, sc, *a), rsrc(fs, tb, fds, dep, sc.push(x), *b)) {
                (Some(ra), Some(rb)) => Some(RExpr::Let(sc.len(), Box::new(ra), Box::new(rb))),
                _ => None,
            }
        },
        Sx::Match(m, nb, x, sb) => if idx(sc, x, 0) is Some {
            None
        } else {
            match (rsrc(fs, tb, fds, dep, sc, *m), rsrc(fs, tb, fds, dep, sc, *nb), rsrc(fs, tb, fds, dep, sc.push(x), *sb)) {
                (Some(rm), Some(rn), Some(rb)) => Some(RExpr::Match(Box::new(rm), Box::new(rn), sc.len(), Box::new(rb))),
                _ => None,
            }
        },
        Sx::List(ty, es) => match (to_ty(ty, tb, false), rsrcs(fs, tb, fds, dep, sc, es, 0)) {
            (Some(_), Some(rs)) => Some(RExpr::List(rs)),
            _ => None,
        },
        Sx::Str(w) => Some(RExpr::List(rstrs(w))),
        Sx::Fold(l, i, a, x, b) => if a == x || idx(sc, a, 0) is Some || idx(sc, x, 0) is Some {
            None
        } else {
            match (rsrc(fs, tb, fds, dep, sc, *l), rsrc(fs, tb, fds, dep, sc, *i), rsrc(fs, tb, fds, dep, sc.push(a).push(x), *b)) {
                (Some(rl), Some(ri), Some(rb)) => Some(RExpr::Fold(Box::new(rl), Box::new(ri), sc.len(), sc.len() + 1, Box::new(rb))),
                _ => None,
            }
        },
        Sx::Builtin(b, es) => match rsrcs(fs, tb, fds, dep, sc, es, 0) {
            Some(rs) => Some(RExpr::Builtin(b, rs)),
            None => None,
        },
        Sx::Call(f, es) => match idx(fs, f, 0) {
            Some(g) => if dep == 0 {
                None
            } else if g < fds.len() {
                match fds[g as int] {
                    Sd::Fn(_, ps, _, b) => match (rsrc(fs, tb, fds, (dep - 1) as nat, pnames(ps), b), rsrcs(fs, tb, fds, dep, sc, es, 0)) {
                        (Some(rb), Some(rs)) => Some(RExpr::Call(Box::new(rb), ps.len(), rs)),
                        _ => None,
                    },
                    _ => None,
                }
            } else {
                None
            },
            // 関数でない名前への呼出しは構築子（字段が一つ以上）。
            None => if es.len() == 0 {
                None
            } else {
                match rsrcs(fs, tb, fds, dep, sc, es, 0) {
                    Some(rs) => rsrc_ctor(tb, f, rs),
                    None => None,
                }
            },
        },
        // 直和型の match：`_` だけの枝は let（被験式を位置 sc.len() に束縛）、それ以外は層ごとの枝（rsrc_layers）。
        Sx::SumMatch(m, arms) => if any_arms(arms) {
            match (rsrc(fs, tb, fds, dep, sc, *m), rsrc(fs, tb, fds, dep, sc.push(Seq::empty()), arms[0].1)) {
                (Some(rm), Some(rb)) => Some(RExpr::Let(sc.len(), Box::new(rm), Box::new(rb))),
                _ => None,
            }
        } else {
            match arms_sum(tb, arms) {
                Some(i) => match (rsrc(fs, tb, fds, dep, sc, *m), rsrc_layers(fs, tb, fds, dep, sc, tb[i as int].2, arms, 0)) {
                    (Some(rm), Some(es)) => Some(RExpr::SMatch(Box::new(rm), es)),
                    _ => None,
                },
                None => None,
            }
        },
        _ => None,
    }
}

/// 構築子 c の値の写し（字段の式の列 rs）：構築子の項目を名前表で引き、字段の数が合えば、構築子の番号と直和型の構築子の数。
pub open spec fn rsrc_ctor(tb: Seq<(Seq<char>, Option<Ty>, Seq<Seq<char>>, Option<Ty>)>, c: Seq<char>, rs: Seq<RExpr>) -> Option<RExpr> {
    match vlook(tb, c) {
        Some((i, k, m)) => if m != rs.len() || k >= tb[i as int].2.len() {
            None
        } else {
            Some(RExpr::Ctor(k, tb[i as int].2.len(), rs))
        },
        None => None,
    }
}

/// 直和型の枝の源の写し（層 j）：層 j の枝は smatch_from と同じ選び方（layer_idx）で、名前の位置（arm_ids）と本体の写しを返す。
/// 本体は pushn(sc0, j) の scope で写す（核の層 j の rx と同じ）。
pub open spec fn rsrc_layer(fs: Seq<Seq<char>>, tb: Seq<(Seq<char>, Option<Ty>, Seq<Seq<char>>, Option<Ty>)>, fds: Seq<Sd>, dep: nat, sc0: Seq<Seq<char>>, ents: Seq<Seq<char>>, arms: Seq<(Spat, Sx)>, j: nat) -> Option<(Seq<nat>, RExpr)>
    decreases dep, arms, 0nat,
{
    match layer_idx(ents, j, arms) {
        Some(ka) => if ka >= arms.len() {
            None
        } else {
            match arm_binds_or_empty(arms[ka as int].0) {
                Some(bs) => if !arm_ok(bs) || !binds_fresh(pushn(sc0, j), bs) {
                    None
                } else {
                    match rsrc(fs, tb, fds, dep, arm_scope(pushn(sc0, j), bs), arms[ka as int].1) {
                        Some(body) => Some((arm_ids(sc0.len() + j, bs), body)),
                        None => None,
                    }
                },
                None => None,
            }
        },
        None => None,
    }
}

/// 直和型の枝の源の写し（層 j から先）：層の順の rsrc_layer の並び。どれか一つでも写せなければ None（核の smatch_from と同じ）。
pub open spec fn rsrc_layers(fs: Seq<Seq<char>>, tb: Seq<(Seq<char>, Option<Ty>, Seq<Seq<char>>, Option<Ty>)>, fds: Seq<Sd>, dep: nat, sc0: Seq<Seq<char>>, ents: Seq<Seq<char>>, arms: Seq<(Spat, Sx)>, j: nat) -> Option<Seq<(Seq<nat>, RExpr)>>
    decreases dep, arms, ents.len() - j,
{
    if j >= ents.len() {
        Some(Seq::empty())
    } else {
        match (rsrc_layer(fs, tb, fds, dep, sc0, ents, arms, j), rsrc_layers(fs, tb, fds, dep, sc0, ents, arms, j + 1)) {
            (Some(ent), Some(rest)) => Some(seq![ent] + rest),
            _ => None,
        }
    }
}

/// 式の列の写し（位置 i から先）：rxs と同じ形で、要素ごとに rsrc を取る。
pub open spec fn rsrcs(fs: Seq<Seq<char>>, tb: Seq<(Seq<char>, Option<Ty>, Seq<Seq<char>>, Option<Ty>)>, fds: Seq<Sd>, dep: nat, sc: Seq<Seq<char>>, es: Seq<Sx>, i: nat) -> Option<Seq<RExpr>>
    decreases dep, es, es.len() - i,
{
    if i >= es.len() {
        Some(Seq::empty())
    } else {
        match (rsrc(fs, tb, fds, dep, sc, es[i as int]), rsrcs(fs, tb, fds, dep, sc, es, i + 1)) {
            (Some(r), Some(rs)) => Some(seq![r] + rs),
            _ => None,
        }
    }
}

/// 文字列の写し：文字の式の列（rx の str_exprs と同じ形）。
pub open spec fn rstrs(w: Seq<char>) -> Seq<RExpr> {
    Seq::new(w.len(), |i: int| RExpr::Char(w[i] as u32 as int))
}

/// 字段の列の写し（i から先）：字段 f の位置 idx(decl, f) と、その式の写し。
pub open spec fn rsrc_ws(fs: Seq<Seq<char>>, tb: Seq<(Seq<char>, Option<Ty>, Seq<Seq<char>>, Option<Ty>)>, fds: Seq<Sd>, dep: nat, sc: Seq<Seq<char>>, decl: Seq<Seq<char>>, fls: Seq<(Seq<char>, Sx)>, i: nat) -> Option<Seq<(nat, RExpr)>>
    decreases dep, fls, fls.len() - i,
{
    if i >= fls.len() {
        Some(Seq::empty())
    } else {
        match (idx(decl, fls[i as int].0, 0), rsrc(fs, tb, fds, dep, sc, fls[i as int].1)) {
            (Some(j), Some(r)) => match rsrc_ws(fs, tb, fds, dep, sc, decl, fls, i + 1) {
                Some(ws) => Some(seq![(j, r)] + ws),
                None => None,
            },
            _ => None,
        }
    }
}

/// 参照の鎖 e.f1…fk の写し（resolve.rs の fld_chain と同じ持ち主の引き方）。
pub open spec fn rsrc_chain(tb: Seq<(Seq<char>, Option<Ty>, Seq<Seq<char>>, Option<Ty>)>, fds: Seq<Sd>, dep: nat, r: RExpr, fls: Seq<Seq<char>>, i: nat) -> Option<RExpr>
    decreases dep, fls.len() - i,
{
    if i >= fls.len() {
        Some(r)
    } else {
        match owner_pos(tb, fls[i as int], 0) {
            Some((p, n)) => rsrc_chain(tb, fds, dep, RExpr::Fld(Box::new(r), pdecl(n), p), fls, i + 1),
            None => None,
        }
    }
}

// ------------------------------------------------------------------ 位置と写し

/// 位置の列 base + j（j < n）の中の名前 f の位置は f - base。
proof fn pos_range(n: nat, base: nat, f: nat)
    requires
        base <= f < base + n,
    ensures
        pos(Seq::new(n, |j: int| (base + j) as nat), f) == Some((f - base) as nat),
    decreases n,
{
    reveal_with_fuel(pos, 2);
    let d = Seq::new(n, |j: int| (base + j) as nat);
    if f != base {
        let t = d.drop_first();
        assert(t =~= Seq::new((n - 1) as nat, |j: int| (base + 1 + j) as nat));
        pos_range((n - 1) as nat, base + 1, f);
    }
}

/// 字段の位置 q（q < n）の名前は位置 q である（pdecl の位置）。
proof fn pos_pdecl(n: nat, q: nat)
    requires
        q < n,
    ensures
        pos(pdecl(n), q) == Some(q),
{
    assert(pdecl(n) =~= Seq::new(n, |j: int| (0 + j) as nat));
    pos_range(n, 0, q);
}

/// vofs の長さと各位置。
proof fn vofs_props(vs: Seq<RVal>, i: nat)
    requires
        i <= vs.len(),
    ensures
        vofs(vs, i).len() == vs.len() - i,
        forall|q: int| i <= q < vs.len() ==> #[trigger] vofs(vs, i)[q - i] == vof(vs[q]),
    decreases vs.len() - i,
{
    if i < vs.len() {
        vofs_props(vs, i + 1);
        reveal_with_fuel(vofs, 2);
        assert forall|q: int| i <= q < vs.len() implies #[trigger] vofs(vs, i)[q - i] == vof(vs[q]) by {
            if q == i as int {
                assert(vofs(vs, i)[0] == vof(vs[i as int]));
            } else {
                vstd::seq::lemma_seq_add_index2(seq![vof(vs[i as int])], vofs(vs, i + 1), q - i);
                assert(seq![vof(vs[i as int])].len() == 1);
                assert(vofs(vs, i + 1)[q - (i as int + 1)] == vof(vs[q]));
                assert(vofs(vs, i)[q - i] == vofs(vs, i + 1)[q - i - 1]);
            }
        }
    }
}

/// 書いていない位置の数が 0 であることは、すべての位置が書いてあることと同じ。
proof fn nmissing_iff(u: Seq<Option<Expr>>)
    ensures
        nmissing(u) == 0 <==> (forall|q: int| 0 <= q < u.len() ==> #[trigger] u[q] is Some),
    decreases u.len(),
{
    reveal_with_fuel(nmissing, 2);
    if u.len() > 0 {
        let last = (u.len() - 1) as int;
        nmissing_iff(u.drop_last());
        assert(u.drop_last().len() == u.len() - 1);
        assert forall|q: int| 0 <= q < u.len() - 1 implies #[trigger] u.drop_last()[q] == u[q] by {}
        if u[last] is None {
            assert(!(forall|q: int| 0 <= q < u.len() ==> #[trigger] u[q] is Some)) by {
                if forall|q: int| 0 <= q < u.len() ==> #[trigger] u[q] is Some {
                    assert(u[last] is Some);
                }
            }
        } else {
            assert(nmissing(u) == nmissing(u.drop_last()));
            if forall|q: int| 0 <= q < u.len() - 1 ==> #[trigger] u.drop_last()[q] is Some {
                assert forall|q: int| 0 <= q < u.len() implies #[trigger] u[q] is Some by {
                    if q < last {
                        assert(u.drop_last()[q] == u[q]);
                    } else {
                        assert(u[last] is Some);
                    }
                }
            }
            if forall|q: int| 0 <= q < u.len() ==> #[trigger] u[q] is Some {
                assert forall|q: int| 0 <= q < u.len() - 1 implies #[trigger] u.drop_last()[q] is Some by {
                    assert(u.drop_last()[q] == u[q]);
                }
            }
        }
    }
}

// ------------------------------------------------------------------ 字段の参照と束縛の新しさ

/// snds は、変数 x が現れない式に対して x を参照しない。
proof fn absent_snds(x: nat, e: Expr, i: nat)
    requires
        absent(x, e),
    ensures
        absent(x, snds(e, i)),
    decreases i,
{
    reveal_with_fuel(snds, 2);
    reveal_with_fuel(absent, 2);
    reveal_with_fuel(absent_args, 2);
    if i > 0 {
        let es = seq![e];
        assert(es[0] == e);
        let e1 = Expr::Builtin(Builtin::Snd, es);
        assert(absent_args(x, es, 0));
        assert(absent(x, e1));
        absent_snds(x, e1, (i - 1) as nat);
    }
}

/// 字段の参照も、変数 x が現れない式に対して x を参照しない。
proof fn absent_rfield(x: nat, e: Expr, i: nat, n: nat)
    requires
        absent(x, e),
    ensures
        absent(x, rfield(e, i, n)),
{
    reveal_with_fuel(absent, 2);
    reveal_with_fuel(absent_args, 2);
    absent_snds(x, e, i);
    if i + 1 < n {
        let es = seq![snds(e, i)];
        assert(es[0] == snds(e, i));
        assert(absent_args(x, es, 0));
        assert(absent(x, Expr::Builtin(Builtin::Fst, es)));
    }
}

/// 参照の鎖（fld_chain）も、変数 x が現れない式から始めれば、その結果に x は現れない。
proof fn absent_chain(tb: Seq<(Seq<char>, Option<Ty>, Seq<Seq<char>>, Option<Ty>)>, fds: Seq<Sd>, dep: nat, x: nat, e: Expr, fls: Seq<Seq<char>>, i: nat, c: Expr)
    requires
        absent(x, e),
        fld_chain(tb, e, fls, i) == Some(c),
    ensures
        absent(x, c),
    decreases dep, fls.len() - i,
{
    reveal_with_fuel(fld_chain, 2);
    if i < fls.len() {
        if let Some((pp, n)) = owner_pos(tb, fls[i as int], 0) {
            absent_rfield(x, e, pp, n);
            absent_chain(tb, fds, dep, x, rfield(e, pp, n), fls, i + 1, c);
        }
    }
}

/// 字段の式の列（rbuild）は、要素ごとに位置 n を参照も束縛もしないなら、全体も参照も束縛もしない。
proof fn absent_rbuild(n: nat, es: Seq<Expr>)
    requires
        es.len() >= 1,
        forall|j: int| 0 <= j < es.len() ==> absent(n, #[trigger] es[j]),
    ensures
        absent(n, rbuild(es)),
    decreases es.len(),
{
    reveal_with_fuel(rbuild, 2);
    reveal_with_fuel(absent, 2);
    if es.len() > 1 {
        let rest = es.drop_first();
        assert forall|j: int| 0 <= j < rest.len() implies absent(n, #[trigger] rest[j]) by {
            assert(rest[j] == es[j + 1]);
        }
        absent_rbuild(n, rest);
    }
}

/// 書いた字段と基の式（fill）は、書いた式と基が位置 n を参照も束縛もしないなら、要素ごとにそうである。
proof fn absent_fill(n: nat, u: Seq<Option<Expr>>, b: Expr)
    requires
        absent(n, b),
        forall|j: int| 0 <= j < u.len() ==> (#[trigger] u[j]) is Some ==> absent(n, u[j]->Some_0),
    ensures
        forall|j: int| 0 <= j < u.len() ==> absent(n, #[trigger] fill(u, b)[j]),
{
    assert forall|j: int| 0 <= j < u.len() implies absent(n, #[trigger] fill(u, b)[j]) by {
        if u[j] is Some {
            assert(fill(u, b)[j] == u[j]->Some_0);
        } else {
            assert(fill(u, b)[j] == rfield(b, j as nat, u.len()));
            absent_rfield(n, b, j as nat, u.len());
        }
    }
}

/// 更新の式（rupdate）は、書いた式と基が位置 n を参照も束縛もせず、基の束縛の位置 x が n と違うなら、n を参照も束縛もしない。
proof fn absent_rupdate(n: nat, u: Seq<Option<Expr>>, b: Expr, x: nat)
    requires
        n != x,
        u.len() >= 1,
        absent(n, b),
        forall|j: int| 0 <= j < u.len() ==> (#[trigger] u[j]) is Some ==> absent(n, u[j]->Some_0),
    ensures
        absent(n, rupdate(u, b, x)),
{
    reveal_with_fuel(absent, 2);
    reveal_with_fuel(rupdate, 1);
    if b is Var || nmissing(u) <= 1 {
        absent_fill(n, u, b);
        absent_rbuild(n, fill(u, b));
    } else {
        assert(absent(n, Expr::Var(x)));
        absent_fill(n, u, Expr::Var(x));
        absent_rbuild(n, fill(u, Expr::Var(x)));
    }
}

/// 字段の書込み（rec_upd）は、書いた式が位置 n を参照も束縛もしないなら、書き終えた式もそうである。字段の式は absent_at で示す。
#[verifier::rlimit(50)]
proof fn absent_rec_upd(fs: Seq<Seq<char>>, tb: Seq<(Seq<char>, Option<Ty>, Seq<Seq<char>>, Option<Ty>)>, fds: Seq<Sd>, dep: nat, t: Seq<Seq<char>>, n: nat, decl: Seq<Seq<char>>, fls: Seq<(Seq<char>, Sx)>, i: nat, u: Seq<Option<Expr>>, uf: Seq<Option<Expr>>)
    requires
        n < t.len(),
        t[n as int] == Seq::<char>::empty(),
        u.len() == decl.len(),
        rec_upd(fs, tb, false, t, decl, fls, i, u) == Some(uf),
        forall|j: int| 0 <= j < u.len() ==> (#[trigger] u[j]) is Some ==> absent(n, u[j]->Some_0),
        forall|k: int| i <= k < fls.len() ==> rsrc(fs, tb, fds, dep, t, #[trigger] fls[k].1) is Some,
    ensures
        uf.len() == u.len(),
        forall|j: int| 0 <= j < uf.len() ==> (#[trigger] uf[j]) is Some ==> absent(n, uf[j]->Some_0),
    decreases dep, fls, fls.len() - i,
{
    reveal_with_fuel(rec_upd, 2);
    if i < fls.len() {
        if let Some(j) = idx(decl, fls[i as int].0, 0) {
            idx_props(decl, fls[i as int].0, 0);
            if u[j as int] is None {
                if let Some(x) = rx(fs, tb, false, t, fls[i as int].1) {
                    absent_at(fs, tb, fds, dep, t, n, fls[i as int].1, x);
                    let u2 = u.update(j as int, Some(x));
                    assert forall|m: int| 0 <= m < u2.len() && (#[trigger] u2[m]) is Some implies absent(n, u2[m]->Some_0) by {
                        if m != j as int {
                            assert(u2[m] == u[m]);
                        }
                    }
                    absent_rec_upd(fs, tb, fds, dep, t, n, decl, fls, i + 1, u2, uf);
                }
            }
        }
    }
}

/// 字段の列の rsrc_ws が Some なら、各字段の式は写せる（rsrc が Some）。
proof fn rsrc_ws_some(fs: Seq<Seq<char>>, tb: Seq<(Seq<char>, Option<Ty>, Seq<Seq<char>>, Option<Ty>)>, fds: Seq<Sd>, dep: nat, sc: Seq<Seq<char>>, decl: Seq<Seq<char>>, fls: Seq<(Seq<char>, Sx)>)
    requires
        rsrc_ws(fs, tb, fds, dep, sc, decl, fls, 0) is Some,
    ensures
        forall|k: int| 0 <= k < fls.len() ==> rsrc(fs, tb, fds, dep, sc, #[trigger] fls[k].1) is Some,
{
    let ws = rsrc_ws(fs, tb, fds, dep, sc, decl, fls, 0)->Some_0;
    rsrc_ws_at(fs, tb, fds, dep, sc, decl, fls, 0, ws);
    assert forall|k: int| 0 <= k < fls.len() implies rsrc(fs, tb, fds, dep, sc, #[trigger] fls[k].1) is Some by {
        assert(idx(decl, fls[k].0, 0) == idx(decl, fls[k].0, 0));
    }
}

/// 印なしの記録の構築（基がない）は、書いていない字段がなく、書いた式がすべて位置 n を参照も束縛もしないなら、位置 n を参照も束縛もしない。
#[verifier::rlimit(50)]
proof fn absent_rec_none(fs: Seq<Seq<char>>, tb: Seq<(Seq<char>, Option<Ty>, Seq<Seq<char>>, Option<Ty>)>, fds: Seq<Sd>, dep: nat, t: Seq<Seq<char>>, n: nat, decl: Seq<Seq<char>>, fls: Seq<(Seq<char>, Sx)>, u: Seq<Option<Expr>>, c: Expr)
    requires
        n < t.len(),
        t[n as int] == Seq::<char>::empty(),
        decl.len() > 0,
        rsrc_ws(fs, tb, fds, dep, t, decl, fls, 0) is Some,
        rec_upd(fs, tb, false, t, decl, fls, 0, none_upd(decl.len())) == Some(u),
        rrecord(u, None, t.len()) == Ok(c),
    ensures
        absent(n, c),
    decreases dep, fls, fls.len() + 1,
{
    rsrc_ws_some(fs, tb, fds, dep, t, decl, fls);
    absent_rec_upd(fs, tb, fds, dep, t, n, decl, fls, 0, none_upd(decl.len()), u);
    assert(nmissing(u) == 0);
    nmissing_zero(u);
    assert forall|j: int| 0 <= j < crate::records_exec::written(u).len() implies absent(n, #[trigger] crate::records_exec::written(u)[j]) by {
        assert(crate::records_exec::written(u)[j] == u[j]->Some_0);
    }
    absent_rbuild(n, crate::records_exec::written(u));
    assert(c == rbuild(crate::records_exec::written(u)));
}

/// 印なしの記録の構築（基がある）は、基と更新の x が位置 n を参照も束縛もせず、書いた式がすべて位置 n を参照も束縛もしないなら、位置 n を参照も束縛もしない。
#[verifier::rlimit(50)]
proof fn absent_rec_some(fs: Seq<Seq<char>>, tb: Seq<(Seq<char>, Option<Ty>, Seq<Seq<char>>, Option<Ty>)>, fds: Seq<Sd>, dep: nat, t2: Seq<Seq<char>>, n: nat, decl: Seq<Seq<char>>, fls: Seq<(Seq<char>, Sx)>, bx: Expr, x: nat, u: Seq<Option<Expr>>, c: Expr)
    requires
        n < t2.len(),
        t2[n as int] == Seq::<char>::empty(),
        n != x,
        decl.len() > 0,
        absent(n, bx),
        rsrc_ws(fs, tb, fds, dep, t2, decl, fls, 0) is Some,
        rec_upd(fs, tb, false, t2, decl, fls, 0, none_upd(decl.len())) == Some(u),
        rrecord(u, Some(bx), x) == Ok(c),
    ensures
        absent(n, c),
    decreases dep, fls, fls.len() + 1,
{
    rsrc_ws_some(fs, tb, fds, dep, t2, decl, fls);
    absent_rec_upd(fs, tb, fds, dep, t2, n, decl, fls, 0, none_upd(decl.len()), u);
    absent_rupdate(n, u, bx, x);
    assert(c == rupdate(u, bx, x));
}

/// rx の基なしの記録の腕を展開する：字段の名前は宣言にあり、印なしの rec_expr が c を返す。
#[verifier::rlimit(50)]
proof fn rx_rec_none(fs: Seq<Seq<char>>, tb: Seq<(Seq<char>, Option<Ty>, Seq<Seq<char>>, Option<Ty>)>, t: Seq<Seq<char>>, r: Seq<char>, fls: Seq<(Seq<char>, Sx)>, c: Expr)
    requires
        rx(fs, tb, false, t, Sx::Rec(r, fls, None)) == Some(c),
    ensures
        idx(tnames(tb), r, 0) is Some,
        is_rec_slot(tb[idx(tnames(tb), r, 0)->Some_0 as int].2),
        rec_expr(fs, tb, false, t, tb[idx(tnames(tb), r, 0)->Some_0 as int].2, fls, None) == Some(c),
{
    reveal_with_fuel(rx, 2);
    reveal_with_fuel(rec_t, 2);
}

/// rx の基ありの記録の腕を展開する：基は bx に解決し、印なしの rec_expr が c を返す。
#[verifier::rlimit(50)]
proof fn rx_rec_some(fs: Seq<Seq<char>>, tb: Seq<(Seq<char>, Option<Ty>, Seq<Seq<char>>, Option<Ty>)>, t: Seq<Seq<char>>, r: Seq<char>, fls: Seq<(Seq<char>, Sx)>, b: Sx, bx: Expr, c: Expr)
    requires
        rx(fs, tb, false, t, Sx::Rec(r, fls, Some(Box::new(b)))) == Some(c),
        rx(fs, tb, false, t, b) == Some(bx),
    ensures
        idx(tnames(tb), r, 0) is Some,
        is_rec_slot(tb[idx(tnames(tb), r, 0)->Some_0 as int].2),
        rec_expr(fs, tb, false, t, tb[idx(tnames(tb), r, 0)->Some_0 as int].2, fls, Some(bx)) == Some(c),
{
    reveal_with_fuel(rx, 2);
    reveal_with_fuel(rec_t, 2);
}

/// 基なしの記録の字段の写し（rsrc）は、字段の列の rsrc_ws が Some である。
#[verifier::rlimit(50)]
proof fn rsrc_rec_none(fs: Seq<Seq<char>>, tb: Seq<(Seq<char>, Option<Ty>, Seq<Seq<char>>, Option<Ty>)>, fds: Seq<Sd>, dep: nat, t: Seq<Seq<char>>, r: Seq<char>, fls: Seq<(Seq<char>, Sx)>, k: nat)
    requires
        idx(tnames(tb), r, 0) == Some(k),
        rsrc(fs, tb, fds, dep, t, Sx::Rec(r, fls, None)) is Some,
    ensures
        rsrc_ws(fs, tb, fds, dep, t, tb[k as int].2, fls, 0) is Some,
{
    reveal_with_fuel(rsrc, 2);
}

/// 基ありの記録の写し（rsrc）は、基の写しが Some で、基の scope での字段の列の rsrc_ws が Some である。
#[verifier::rlimit(50)]
proof fn rsrc_rec_some(fs: Seq<Seq<char>>, tb: Seq<(Seq<char>, Option<Ty>, Seq<Seq<char>>, Option<Ty>)>, fds: Seq<Sd>, dep: nat, t: Seq<Seq<char>>, r: Seq<char>, fls: Seq<(Seq<char>, Sx)>, b: Sx, bx: Expr, k: nat)
    requires
        idx(tnames(tb), r, 0) == Some(k),
        rx(fs, tb, false, t, b) == Some(bx),
        rsrc(fs, tb, fds, dep, t, Sx::Rec(r, fls, Some(Box::new(b)))) is Some,
    ensures
        rsrc(fs, tb, fds, dep, t, b) is Some,
        rsrc_ws(fs, tb, fds, dep, scope2(t, deep_rec(Some(bx), tb[k as int].2, fls)), tb[k as int].2, fls, 0) is Some,
{
    reveal_with_fuel(rsrc, 2);
}

/// 印なしの記録の値（基なし）から、書き終えた字段の列 u を取り出す：rrecord は、その構築が c であることを示す。
#[verifier::rlimit(50)]
proof fn rec_expr_none_upd(fs: Seq<Seq<char>>, tb: Seq<(Seq<char>, Option<Ty>, Seq<Seq<char>>, Option<Ty>)>, t: Seq<Seq<char>>, decl: Seq<Seq<char>>, fls: Seq<(Seq<char>, Sx)>, c: Expr) -> (u: Seq<Option<Expr>>)
    requires
        rec_expr(fs, tb, false, t, decl, fls, None) == Some(c),
    ensures
        rec_upd(fs, tb, false, t, decl, fls, 0, none_upd(decl.len())) == Some(u),
        rrecord(u, None, t.len()) == Ok(c),
{
    reveal_with_fuel(rec_expr, 2);
    assert(rec_upd(fs, tb, false, t, decl, fls, 0, none_upd(decl.len())) is Some);
    rec_upd(fs, tb, false, t, decl, fls, 0, none_upd(decl.len()))->Some_0
}

/// 印なしの記録の値（基あり）から、書き終えた字段の列 u を取り出す：rrecord は、更新の式が c であることを示す。
#[verifier::rlimit(50)]
proof fn rec_expr_some_upd(fs: Seq<Seq<char>>, tb: Seq<(Seq<char>, Option<Ty>, Seq<Seq<char>>, Option<Ty>)>, t: Seq<Seq<char>>, decl: Seq<Seq<char>>, fls: Seq<(Seq<char>, Sx)>, bx: Expr, c: Expr) -> (u: Seq<Option<Expr>>)
    requires
        rec_expr(fs, tb, false, t, decl, fls, Some(bx)) == Some(c),
    ensures
        rec_upd(fs, tb, false, scope2(t, deep_rec(Some(bx), decl, fls)), decl, fls, 0, none_upd(decl.len())) == Some(u),
        rrecord(u, Some(bx), t.len()) == Ok(c),
{
    reveal_with_fuel(rec_expr, 2);
    assert(rec_upd(fs, tb, false, scope2(t, deep_rec(Some(bx), decl, fls)), decl, fls, 0, none_upd(decl.len())) is Some);
    rec_upd(fs, tb, false, scope2(t, deep_rec(Some(bx), decl, fls)), decl, fls, 0, none_upd(decl.len()))->Some_0
}

/// 記録の構築（rx の Rec の腕）は、位置 n を参照も束縛もしない。字段と基は、同じ scope で absent_at が示す。
#[verifier::rlimit(50)]
proof fn absent_rec(fs: Seq<Seq<char>>, tb: Seq<(Seq<char>, Option<Ty>, Seq<Seq<char>>, Option<Ty>)>, fds: Seq<Sd>, dep: nat, t: Seq<Seq<char>>, n: nat, e: Sx, c: Expr)
    requires
        n < t.len(),
        t[n as int] == Seq::<char>::empty(),
        e is Rec,
        rx(fs, tb, false, t, e) == Some(c),
        rsrc(fs, tb, fds, dep, t, e) is Some,
    ensures
        absent(n, c),
    decreases dep, e, 0nat,
{
    if let Sx::Rec(r, fls, base) = e {
        match base {
            None => {
                rx_rec_none(fs, tb, t, r, fls, c);
                let k = idx(tnames(tb), r, 0)->Some_0;
                let decl = tb[k as int].2;
                assert(e == Sx::Rec(r, fls, None));
                rsrc_rec_none(fs, tb, fds, dep, t, r, fls, k);
                let u = rec_expr_none_upd(fs, tb, t, decl, fls, c);
                absent_rec_none(fs, tb, fds, dep, t, n, decl, fls, u, c);
            },
            Some(b) => {
                if let Some(bx) = rx(fs, tb, false, t, *b) {
                    assert(e == Sx::Rec(r, fls, Some(Box::new(*b))));
                    rx_rec_some(fs, tb, t, r, fls, *b, bx, c);
                    let k = idx(tnames(tb), r, 0)->Some_0;
                    let decl = tb[k as int].2;
                    rsrc_rec_some(fs, tb, fds, dep, t, r, fls, *b, bx, k);
                    absent_at(fs, tb, fds, dep, t, n, *b, bx);
                    let sc2 = scope2(t, deep_rec(Some(bx), decl, fls));
                    assert(n < sc2.len() && sc2[n as int] == Seq::<char>::empty());
                    let u = rec_expr_some_upd(fs, tb, t, decl, fls, bx, c);
                    absent_rec_some(fs, tb, fds, dep, sc2, n, decl, fls, bx, t.len(), u, c);
                }
            },
        }
    }
}

/// 名前 n の位置が空の名前である scope（t[n] は空）で解決した式は、その位置を参照も束縛もしない。
/// 深い scope の空の名前の位置が、字段の式に現れないことを示す。記録の構築（rx の Rec の腕）は、absent_rec が示す。let は、束縛の名前（sc.len()）が n と違うので、その位置を覆わない。
#[verifier::rlimit(50)]
proof fn absent_at(fs: Seq<Seq<char>>, tb: Seq<(Seq<char>, Option<Ty>, Seq<Seq<char>>, Option<Ty>)>, fds: Seq<Sd>, dep: nat, t: Seq<Seq<char>>, n: nat, e: Sx, c: Expr)
    requires
        n < t.len(),
        t[n as int] == Seq::<char>::empty(),
        rx(fs, tb, false, t, e) == Some(c),
        rsrc(fs, tb, fds, dep, t, e) is Some,
    ensures
        absent(n, c),
    decreases dep, e, 1nat,
{
    reveal_with_fuel(rx, 2);
    reveal_with_fuel(rsrc, 1);
    reveal_with_fuel(absent, 2);
    match e {
        Sx::Var(x) => {
            assert(x.len() != 0);
            if idx(t, x, 0) is Some {
                idx_props(t, x, 0);
                let k = idx(t, x, 0)->Some_0;
                assert(t[k as int] == x);
                assert(k != n);
                assert(c == Expr::Var(k));
            } else {
                assert(rctor(tb, false, x, Seq::empty()) == Some(c));
                absent_ctor(tb, n, x, Seq::empty(), c);
            }
        },
        Sx::Pair(a, b) => {
            if let Some(ca) = rx(fs, tb, false, t, *a) {
                if let Some(cb) = rx(fs, tb, false, t, *b) {
                    assert(rsrc(fs, tb, fds, dep, t, *a) is Some && rsrc(fs, tb, fds, dep, t, *b) is Some);
                    absent_at(fs, tb, fds, dep, t, n, *a, ca);
                    absent_at(fs, tb, fds, dep, t, n, *b, cb);
                }
            }
        },
        Sx::Fld(a, fls) => {
            if let Some(ca) = rx(fs, tb, false, t, *a) {
                assert(rsrc(fs, tb, fds, dep, t, *a) is Some);
                absent_at(fs, tb, fds, dep, t, n, *a, ca);
                absent_chain(tb, fds, dep, n, ca, fls, 0, c);
            }
        },
        Sx::Some(a) => {
            if let Some(ca) = rx(fs, tb, false, t, *a) {
                assert(rsrc(fs, tb, fds, dep, t, *a) is Some);
                absent_at(fs, tb, fds, dep, t, n, *a, ca);
            }
        },
        Sx::Let(..) => absent_at_let(fs, tb, fds, dep, t, n, e, c),
        Sx::Match(..) => absent_at_match(fs, tb, fds, dep, t, n, e, c),
        Sx::List(..) => absent_at_list(fs, tb, fds, dep, t, n, e, c),
        Sx::Str(w) => absent_at_str(n, c, w),
        Sx::Fold(..) => absent_at_fold(fs, tb, fds, dep, t, n, e, c),
        Sx::Builtin(..) => absent_at_builtin(fs, tb, fds, dep, t, n, e, c),
        Sx::Call(..) => absent_at_call(fs, tb, fds, dep, t, n, e, c),
        Sx::If(q, a, b) => {
            if let Some(cq) = rx(fs, tb, false, t, *q) {
                if let Some(ca) = rx(fs, tb, false, t, *a) {
                    if let Some(cb) = rx(fs, tb, false, t, *b) {
                        assert(rsrc(fs, tb, fds, dep, t, *q) is Some && rsrc(fs, tb, fds, dep, t, *a) is Some && rsrc(fs, tb, fds, dep, t, *b) is Some);
                        absent_at(fs, tb, fds, dep, t, n, *q, cq);
                        absent_at(fs, tb, fds, dep, t, n, *a, ca);
                        absent_at(fs, tb, fds, dep, t, n, *b, cb);
                    }
                }
            }
        },
        Sx::Rec(..) => absent_rec(fs, tb, fds, dep, t, n, e, c),
        Sx::SumMatch(..) => absent_at_sum(fs, tb, fds, dep, t, n, e, c),
        _ => {},
    }
}

/// match の腕の名前の位置：走査する式と各枝は、位置 n を参照も束縛もしない。some の枝の scope は一つ長く、位置 n は同じ。
/// 束縛の名前は sc.len() で、n とは違う（absent_at_let と同じ）。
#[verifier::rlimit(50)]
proof fn absent_at_match(fs: Seq<Seq<char>>, tb: Seq<(Seq<char>, Option<Ty>, Seq<Seq<char>>, Option<Ty>)>, fds: Seq<Sd>, dep: nat, t: Seq<Seq<char>>, n: nat, e: Sx, c: Expr)
    requires
        n < t.len(),
        t[n as int] == Seq::<char>::empty(),
        e is Match,
        rx(fs, tb, false, t, e) == Some(c),
        rsrc(fs, tb, fds, dep, t, e) is Some,
    ensures
        absent(n, c),
    decreases dep, e, 0nat,
{
    reveal_with_fuel(rx, 2);
    reveal_with_fuel(rsrc, 1);
    reveal_with_fuel(absent, 2);
    match e {
        Sx::Match(m, nb, x, sb) => {
            assert(idx(t, x, 0) is None);
            if let Some(cm) = rx(fs, tb, false, t, *m) {
                if let Some(cn) = rx(fs, tb, false, t, *nb) {
                    if let Some(cb) = rx(fs, tb, false, t.push(x), *sb) {
                        assert(rsrc(fs, tb, fds, dep, t, *m) is Some && rsrc(fs, tb, fds, dep, t, *nb) is Some && rsrc(fs, tb, fds, dep, t.push(x), *sb) is Some);
                        absent_at(fs, tb, fds, dep, t, n, *m, cm);
                        absent_at(fs, tb, fds, dep, t, n, *nb, cn);
                        assert(t.push(x)[n as int] == t[n as int]);
                        absent_at(fs, tb, fds, dep, t.push(x), n, *sb, cb);
                        assert(c == Expr::Match(Box::new(cm), Box::new(cn), t.len(), Box::new(cb)));
                        assert(t.len() != n);
                    }
                }
            }
        },
        _ => {},
    }
}

/// let の腕の名前の位置：束縛の式と本体は、位置 n を参照も束縛もしない。本体は scope に名前 x を足して解決するが、
/// その位置 n は変わらず、束縛の名前は sc.len() で n と違う。absent_at の let の腕を、単独の補題に分ける。
proof fn absent_at_let(fs: Seq<Seq<char>>, tb: Seq<(Seq<char>, Option<Ty>, Seq<Seq<char>>, Option<Ty>)>, fds: Seq<Sd>, dep: nat, t: Seq<Seq<char>>, n: nat, e: Sx, c: Expr)
    requires
        n < t.len(),
        t[n as int] == Seq::<char>::empty(),
        e is Let,
        rx(fs, tb, false, t, e) == Some(c),
        rsrc(fs, tb, fds, dep, t, e) is Some,
    ensures
        absent(n, c),
    decreases dep, e, 0nat,
{
    reveal_with_fuel(rx, 2);
    reveal_with_fuel(rsrc, 1);
    reveal_with_fuel(absent, 2);
    match e {
        Sx::Let(x, a, b) => {
            assert(idx(t, x, 0) is None);
            if let Some(ca) = rx(fs, tb, false, t, *a) {
                if let Some(cb) = rx(fs, tb, false, t.push(x), *b) {
                    assert(rsrc(fs, tb, fds, dep, t, *a) is Some && rsrc(fs, tb, fds, dep, t.push(x), *b) is Some);
                    absent_at(fs, tb, fds, dep, t, n, *a, ca);
                    assert(t.push(x)[n as int] == t[n as int]);
                    absent_at(fs, tb, fds, dep, t.push(x), n, *b, cb);
                    assert(c == Expr::Let(t.len(), Box::new(ca), Box::new(cb)));
                    assert(t.len() != n);
                }
            }
        },
        _ => {},
    }
}

/// 式の列の要素（位置 i から先）は、位置 n を参照も束縛もしない（absent_args の要素ごとの形）。
proof fn absent_args_elts(n: nat, es: Seq<Expr>, i: nat)
    requires
        absent_args(n, es, i),
    ensures
        forall|j: int| (i as int) <= j < es.len() ==> absent(n, #[trigger] es[j]),
    decreases es.len() - i,
{
    reveal_with_fuel(absent_args, 1);
    if i < es.len() {
        absent_args_elts(n, es, i + 1);
    }
}

/// 字段の式の列の pay_nested（字段が無ければ Unit、あれば rbuild）は、位置 n を参照も束縛もしないなら、そうである。
proof fn absent_pay_nested(n: nat, xs: Seq<Expr>)
    requires
        absent_args(n, xs, 0),
    ensures
        absent(n, pay_nested(xs)),
{
    reveal_with_fuel(absent, 1);
    if xs.len() > 0 {
        absent_args_elts(n, xs, 0);
        absent_rbuild(n, xs);
    }
}

/// 構築子の式（rctor）は、字段の式が位置 n を参照も束縛もしないなら、位置 n を参照も束縛もしない。
proof fn absent_ctor(tb: Seq<(Seq<char>, Option<Ty>, Seq<Seq<char>>, Option<Ty>)>, n: nat, cn: Seq<char>, xs: Seq<Expr>, c: Expr)
    requires
        rctor(tb, false, cn, xs) == Some(c),
        absent_args(n, xs, 0),
    ensures
        absent(n, c),
{
    absent_pay_nested(n, xs);
    assert(vlook(tb, cn) is Some) by {
        if vlook(tb, cn) is None {
            assert(rctor(tb, false, cn, xs) is None);
        }
    }
    let vl = vlook(tb, cn)->Some_0;
    let i = vl.0;
    let k = vl.1;
    assert(tb[i as int].1 is Some) by {
        if tb[i as int].1 is None {
            assert(rctor(tb, false, cn, xs) is None);
        }
    }
    let t = tb[i as int].1->Some_0;
    assert(inj_from(t, tb[i as int].2.len(), k, 0, pay_nested(xs)) == Some(c));
    absent_inj(n, t, tb[i as int].2.len(), k, 0, pay_nested(xs), c);
}

/// binds_lets（字段の束縛の列）は、位置 n より上の位置 p に字段を束縛し、その本体が n を参照も束縛もしないなら、そうである。
proof fn absent_binds_lets(n: nat, p: nat, m: nat, j: nat, body: Expr)
    requires
        n < p,
        absent(n, body),
    ensures
        absent(n, binds_lets(p, m, j, body)),
    decreases m - j,
{
    reveal_with_fuel(binds_lets, 2);
    reveal_with_fuel(absent, 2);
    if j < m {
        absent_binds_lets(n, p, m, j + 1, body);
        absent_rfield(n, Expr::Var(p), j, m);
    }
}

/// 枝の本体の式（arm_wrap）は、位置 p が n より上で、本体が n を参照も束縛もしないなら、そうである。
proof fn absent_arm_wrap(n: nat, p: nat, bs: Seq<Seq<char>>, body: Expr)
    requires
        n < p,
        absent(n, body),
    ensures
        absent(n, arm_wrap(p, bs, body)),
{
    reveal_with_fuel(arm_wrap, 1);
    if bs.len() >= 2 {
        absent_binds_lets(n, p, bs.len(), 0, body);
    }
}

/// 直和型の鎖（層 j から）は、被験式 s と各層の枝の本体が位置 n を参照も束縛もしないなら、結果も参照も束縛もしない。
/// 層 j の枝の本体（rsrc の写し）は、枝の scope で absent_at に当てる。層 j の束縛の位置 sc.len() は n と違う。
proof fn absent_layers(fs: Seq<Seq<char>>, tb: Seq<(Seq<char>, Option<Ty>, Seq<Seq<char>>, Option<Ty>)>, fds: Seq<Sd>, dep: nat, t: Seq<Seq<char>>, n: nat, ents: Seq<Seq<char>>, arms: Seq<(Spat, Sx)>, j: nat, s: Expr, c: Expr)
    requires
        n < t.len(),
        t[n as int] == Seq::<char>::empty(),
        j < ents.len(),
        absent(n, s),
        rsrc_layers(fs, tb, fds, dep, t, ents, arms, j) is Some,
        smatch_from(fs, tb, false, pushn(t, j), ents, arms, j, s) == Some(c),
    ensures
        absent(n, c),
    decreases dep, arms, ents.len() - j,
{
    reveal_with_fuel(smatch_from, 2);
    reveal_with_fuel(absent, 2);
    reveal_with_fuel(pushn, 1);
    reveal_with_fuel(rsrc_layers, 1);
    reveal_with_fuel(rsrc_layer, 1);
    pushn_len(t, j);
    pushn_index(t, j, n);
    let sc = pushn(t, j);
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
    let bo = rx(fs, tb, false, arm_scope(sc, bs), arms[ka as int].1)->Some_0;
    // 層 j の枝の写し（rsrc_layer）と、その次の層の写し（rsrc_layers）
    assert(rsrc_layer(fs, tb, fds, dep, t, ents, arms, j) is Some && rsrc_layers(fs, tb, fds, dep, t, ents, arms, j + 1) is Some);
    assert(rsrc(fs, tb, fds, dep, arm_scope(sc, bs), arms[ka as int].1) is Some);
    // 枝の scope の位置 n は、外側の scope の位置 n（空の名前）と同じ
    arm_scope_props(sc, bs);
    pushn_index(t, j, n);
    assert(arm_scope(sc, bs)[n as int] == sc[n as int]);
    assert(sc[n as int] == t[n as int]);
    absent_at(fs, tb, fds, dep, arm_scope(sc, bs), n, arms[ka as int].1, bo);
    absent_arm_wrap(n, sc.len(), bs, bo);
    let aw = arm_wrap(sc.len(), bs, bo);
    assert(sc.len() != n);
    if j + 1 == ents.len() {
        assert(smatch_from(fs, tb, false, sc, ents, arms, j, s) == Some(Expr::Let(sc.len(), Box::new(s), Box::new(aw))));
    } else {
        let rest = smatch_from(fs, tb, false, sc.push(Seq::empty()), ents, arms, j + 1, Expr::Var(sc.len()))->Some_0;
        assert(smatch_from(fs, tb, false, sc.push(Seq::empty()), ents, arms, j + 1, Expr::Var(sc.len())) is Some) by {
            if smatch_from(fs, tb, false, sc.push(Seq::empty()), ents, arms, j + 1, Expr::Var(sc.len())) is None {
                assert(smatch_from(fs, tb, false, sc, ents, arms, j, s) is None);
            }
        }
        pushn_succ(t, j);
        assert(pushn(t, j + 1) == sc.push(Seq::empty()));
        assert(rsrc_layers(fs, tb, fds, dep, t, ents, arms, j + 1) is Some);
        absent_layers(fs, tb, fds, dep, t, n, ents, arms, j + 1, Expr::Var(sc.len()), rest);
        assert(smatch_from(fs, tb, false, sc, ents, arms, j, s) == Some(Expr::MatchR(Box::new(s), sc.len(), Box::new(aw), sc.len(), Box::new(rest))));
    }
}

/// 直和型の match の腕の名前の位置：`_` だけの枝は let（被験式と本体）、それ以外は層の鎖（absent_layers）。位置 n を参照も束縛もしない。
#[verifier::rlimit(50)]
proof fn absent_at_sum(fs: Seq<Seq<char>>, tb: Seq<(Seq<char>, Option<Ty>, Seq<Seq<char>>, Option<Ty>)>, fds: Seq<Sd>, dep: nat, t: Seq<Seq<char>>, n: nat, e: Sx, c: Expr)
    requires
        n < t.len(),
        t[n as int] == Seq::<char>::empty(),
        e is SumMatch,
        rx(fs, tb, false, t, e) == Some(c),
        rsrc(fs, tb, fds, dep, t, e) is Some,
    ensures
        absent(n, c),
    decreases dep, e, 0nat,
{
    reveal_with_fuel(rx, 2);
    reveal_with_fuel(rsrc, 1);
    reveal_with_fuel(absent, 2);
    match e {
        Sx::SumMatch(m, arms) => {
            if any_arms(arms) {
                assert(rx(fs, tb, false, t, *m) is Some);
                let cm = rx(fs, tb, false, t, *m)->Some_0;
                assert(rx(fs, tb, false, t.push(Seq::empty()), arms[0].1) is Some);
                let cb = rx(fs, tb, false, t.push(Seq::empty()), arms[0].1)->Some_0;
                assert(c == Expr::Let(t.len(), Box::new(cm), Box::new(cb)));
                assert(rsrc(fs, tb, fds, dep, t, *m) is Some && rsrc(fs, tb, fds, dep, t.push(Seq::empty()), arms[0].1) is Some);
                absent_at(fs, tb, fds, dep, t, n, *m, cm);
                assert(t.push(Seq::empty())[n as int] == t[n as int]);
                absent_at(fs, tb, fds, dep, t.push(Seq::empty()), n, arms[0].1, cb);
                assert(t.len() != n);
            } else {
                assert(arms_sum(tb, arms) is Some) by {
                    if arms_sum(tb, arms) is None {
                        assert(rx(fs, tb, false, t, e) is None);
                    }
                }
                let i = arms_sum(tb, arms)->Some_0;
                assert(rx(fs, tb, false, t, *m) is Some) by {
                    if rx(fs, tb, false, t, *m) is None {
                        assert(rx(fs, tb, false, t, e) is None);
                    }
                }
                let cm = rx(fs, tb, false, t, *m)->Some_0;
                assert(rsrc(fs, tb, fds, dep, t, *m) is Some) by {
                    if rsrc(fs, tb, fds, dep, t, *m) is None {
                        assert(rsrc(fs, tb, fds, dep, t, e) is None);
                    }
                }
                assert(rsrc_layers(fs, tb, fds, dep, t, tb[i as int].2, arms, 0) is Some) by {
                    if rsrc_layers(fs, tb, fds, dep, t, tb[i as int].2, arms, 0) is None {
                        assert(rsrc(fs, tb, fds, dep, t, e) is None);
                    }
                }
                absent_at(fs, tb, fds, dep, t, n, *m, cm);
                assert(smatch_from(fs, tb, false, t, tb[i as int].2, arms, 0, cm) == Some(c));
                absent_layers(fs, tb, fds, dep, t, n, tb[i as int].2, arms, 0, cm, c);
            }
        },
        _ => {},
    }
}

// ------------------------------------------------------------------ 字段の列（rec_upd の性質）

/// 書いた式の解決の場：基を let で束縛するとき（深い）は空の名前を一つ足す（rec_expr と同じ）。
pub open spec fn scope2(sc: Seq<Seq<char>>, deep: bool) -> Seq<Seq<char>> {
    if deep { sc.push(Seq::empty()) } else { sc }
}

/// rec_expr の深い scope の条件（基が変数でなく、書いていない字段が二つ以上ある：rupdate の let と同じ）。
pub open spec fn deep_rec(bx: Option<Expr>, decl: Seq<Seq<char>>, fls: Seq<(Seq<char>, Sx)>) -> bool {
    match bx {
        Some(b) => !(b is Var) && decl.len() >= fls.len() + 2,
        None => false,
    }
}

/// 持ち主の位置は、持ち主の字段の数より小さい。
proof fn owner_pos_lt(tb: Seq<(Seq<char>, Option<Ty>, Seq<Seq<char>>, Option<Ty>)>, fds: Seq<Sd>, dep: nat, f: Seq<char>, k: nat)
    ensures
        owner_pos(tb, f, k) matches Some((p, n)) ==> p < n,
    decreases dep, tb.len() - k,
{
    reveal_with_fuel(owner_pos, 2);
    if k < tb.len() {
        idx_props(tb[k as int].2, f, 0);
        if idx(tb[k as int].2, f, 0) is None {
            owner_pos_lt(tb, fds, dep, f, k + 1);
        }
    }
}

/// 変数 x が現れない式は、x の値を差し替えても同じ値に評価される（eval_absent を評価の存在へ写す）。
proof fn eval_transfer(p: Prog, cenv: Map<nat, Val>, x: nat, w: Val, e: Expr, v: Val)
    requires
        absent(x, e),
        evals_to(p, cenv, e, v),
    ensures
        evals_to(p, cenv.insert(x, w), e, v),
{
    let n = choose|n: nat| #[trigger] eval(p, n, cenv, e) == Res::Done(v);
    eval_absent(p, n, cenv, e, x, w);
    assert(eval(p, n, cenv.insert(x, w), e) == Res::Done(v));
}

/// rec_upd の成功の性質（字段 i から先）。u は書く前の列、uf は書いた後の列（字段の位置は宣言の中の位置）。
proof fn upd_spec(fs: Seq<Seq<char>>, tb: Seq<(Seq<char>, Option<Ty>, Seq<Seq<char>>, Option<Ty>)>, fds: Seq<Sd>, dep: nat, sc: Seq<Seq<char>>, decl: Seq<Seq<char>>, fls: Seq<(Seq<char>, Sx)>, i: nat, u: Seq<Option<Expr>>, uf: Seq<Option<Expr>>)
    requires
        u.len() == decl.len(),
        rec_upd(fs, tb, false, sc, decl, fls, i, u) == Some(uf),
    ensures
        uf.len() == u.len(),
        forall|q: int| 0 <= q < u.len() && (#[trigger] u[q]) is Some ==> uf[q] == u[q],
        forall|k: int| i <= k < fls.len() ==> exists|j: nat| #[trigger] idx(decl, fls[k].0, 0) == Some(j) && (j as int) < uf.len() && rx(fs, tb, false, sc, fls[k].1) is Some && uf[j as int] == rx(fs, tb, false, sc, fls[k].1),
        forall|q: int| 0 <= q < uf.len() && (#[trigger] uf[q]) is Some ==> (q < u.len() && u[q] is Some) || exists|k: int| i <= k < fls.len() && idx(decl, fls[k].0, 0) == Some(q as nat),
    decreases dep, fls, fls.len() - i,
{
    reveal_with_fuel(rec_upd, 2);
    if i < fls.len() {
        match idx(decl, fls[i as int].0, 0) {
            Some(j) => {
                idx_props(decl, fls[i as int].0, 0);
                if u[j as int] is None {
                    match rx(fs, tb, false, sc, fls[i as int].1) {
                        Some(x) => {
                            let u2 = u.update(j as int, Some(x));
                            assert(u2.len() == u.len());
                            upd_spec(fs, tb, fds, dep, sc, decl, fls, i + 1, u2, uf);
                            assert(u2[j as int] == Some(x));
                            assert forall|q: int| 0 <= q < u.len() && (#[trigger] u[q]) is Some implies uf[q] == u[q] by {
                                assert(q != j as int);
                                assert(u2[q] == u[q]);
                            }
                            assert forall|k: int| i <= k < fls.len() implies exists|jj: nat| #[trigger] idx(decl, fls[k].0, 0) == Some(jj) && (jj as int) < uf.len() && rx(fs, tb, false, sc, fls[k].1) is Some && uf[jj as int] == rx(fs, tb, false, sc, fls[k].1) by {
                                if k == i as int {
                                    assert(idx(decl, fls[i as int].0, 0) == Some(j));
                                    assert(rx(fs, tb, false, sc, fls[k].1) == Some(x));
                                    assert(uf[j as int] == Some(x));
                                } else {
                                    assert(i + 1 <= k < fls.len());
                                }
                            }
                            assert forall|q: int| 0 <= q < uf.len() && (#[trigger] uf[q]) is Some implies (q < u.len() && u[q] is Some) || exists|k: int| i <= k < fls.len() && idx(decl, fls[k].0, 0) == Some(q as nat) by {
                                if q == j as int {
                                    assert(idx(decl, fls[i as int].0, 0) == Some(q as nat));
                                } else {
                                    assert(u2[q] == u[q]);
                                }
                            }
                        },
                        None => {},
                    }
                }
            },
            None => {},
        }
    }
}

/// 字段の列の写し（i から先）は、字段と同じ数で、各字段の位置と式の写しを持つ。
proof fn rsrc_ws_at(fs: Seq<Seq<char>>, tb: Seq<(Seq<char>, Option<Ty>, Seq<Seq<char>>, Option<Ty>)>, fds: Seq<Sd>, dep: nat, sc: Seq<Seq<char>>, decl: Seq<Seq<char>>, fls: Seq<(Seq<char>, Sx)>, i: nat, ws: Seq<(nat, RExpr)>)
    requires
        i <= fls.len(),
        rsrc_ws(fs, tb, fds, dep, sc, decl, fls, i) == Some(ws),
    ensures
        ws.len() == fls.len() - i,
        forall|k: int| i <= k < fls.len() ==> idx(decl, #[trigger] fls[k].0, 0) == Some(ws[k - i as int].0) && rsrc(fs, tb, fds, dep, sc, fls[k].1) == Some(ws[k - i as int].1),
    decreases dep, fls.len() - i,
{
    reveal_with_fuel(rsrc_ws, 2);
    if i < fls.len() {
        match idx(decl, fls[i as int].0, 0) {
            Some(j) => match rsrc(fs, tb, fds, dep, sc, fls[i as int].1) {
                Some(r) => match rsrc_ws(fs, tb, fds, dep, sc, decl, fls, i + 1) {
                    Some(ws2) => {
                        rsrc_ws_at(fs, tb, fds, dep, sc, decl, fls, i + 1, ws2);
                        assert(ws == seq![(j, r)] + ws2);
                        assert forall|k: int| i <= k < fls.len() implies idx(decl, #[trigger] fls[k].0, 0) == Some(ws[k - i as int].0) && rsrc(fs, tb, fds, dep, sc, fls[k].1) == Some(ws[k - i as int].1) by {
                            if k == i as int {
                                assert(ws[0] == (j, r));
                            } else {
                                vstd::seq::lemma_seq_add_index2(seq![(j, r)], ws2, k - i as int);
                                assert(ws2[k - (i as int + 1)] == ws[k - i as int]);
                            }
                        }
                    },
                    None => {},
                },
                None => {},
            },
            None => {},
        }
    }
}

/// 書いた字段の位置は、写しの地図にある名前と一致する（字段 q が書いてある ⟺ 地図に名前 q がある）。
proof fn pos_contains(fs: Seq<Seq<char>>, tb: Seq<(Seq<char>, Option<Ty>, Seq<Seq<char>>, Option<Ty>)>, fds: Seq<Sd>, dep: nat, sc: Seq<Seq<char>>, decl: Seq<Seq<char>>, fls: Seq<(Seq<char>, Sx)>, deep: bool, uf: Seq<Option<Expr>>, ws: Seq<(nat, RExpr)>, renv: Map<nat, RVal>, m: Map<nat, RVal>, q: int)
    requires
        rec_upd(fs, tb, false, scope2(sc, deep), decl, fls, 0, none_upd(decl.len())) == Some(uf),
        rsrc_ws(fs, tb, fds, dep, scope2(sc, deep), decl, fls, 0) == Some(ws),
        wmap(renv, ws, 0) == Some(m),
        0 <= q < decl.len(),
    ensures
        uf.len() == decl.len(),
        (0 <= q < uf.len() && (#[trigger] uf[q]) is Some) <==> m.contains_key(q as nat),
{
    upd_spec(fs, tb, fds, dep, scope2(sc, deep), decl, fls, 0, none_upd(decl.len()), uf);
    rsrc_ws_at(fs, tb, fds, dep, scope2(sc, deep), decl, fls, 0, ws);
    assert(none_upd(decl.len())[q] is None);
    if uf[q] is Some {
        assert(exists|k: int| 0 <= k < fls.len() && idx(decl, fls[k].0, 0) == Some(q as nat));
        let k = choose|k: int| 0 <= k < fls.len() && idx(decl, fls[k].0, 0) == Some(q as nat);
        assert(ws[k].0 == q as nat);
        wmap_get(renv, ws, 0, m, k);
    }
    if m.contains_key(q as nat) {
        wmap_dom(renv, ws, 0, m, q as nat);
        let k = choose|k: int| 0 <= k < ws.len() && ws[k].0 == q as nat;
        assert(ws.len() == fls.len());
        assert(idx(decl, fls[k].0, 0) == Some(ws[k].0));
        assert(exists|j: nat| #[trigger] idx(decl, fls[k].0, 0) == Some(j) && (j as int) < uf.len() && rx(fs, tb, false, scope2(sc, deep), fls[k].1) is Some && uf[j as int] == rx(fs, tb, false, scope2(sc, deep), fls[k].1));
        assert(uf[q] is Some);
    }
}

/// 書いた字段の式は、その字段の値を写す（字段の解決の定理を、字段の式に使う）。
/// 基を let で束縛する深い scope では、字段の式は基の名前（sc.len()）を参照も束縛もしない。
#[verifier::rlimit(100)]
proof fn fields_at(p: Prog, fs: Seq<Seq<char>>, tb: Seq<(Seq<char>, Option<Ty>, Seq<Seq<char>>, Option<Ty>)>, fds: Seq<Sd>, dep: nat, sc: Seq<Seq<char>>, decl: Seq<Seq<char>>, fls: Seq<(Seq<char>, Sx)>, cenv: Map<nat, Val>, renv: Map<nat, RVal>, deep: bool, uf: Seq<Option<Expr>>, ws: Seq<(nat, RExpr)>, m: Map<nat, RVal>, q: int)
    requires
        funcs_ok(p, fs, tb, fds),
        envrel(cenv, renv),
        renv_below(renv, sc),
        rec_upd(fs, tb, false, scope2(sc, deep), decl, fls, 0, none_upd(decl.len())) == Some(uf),
        rsrc_ws(fs, tb, fds, dep, scope2(sc, deep), decl, fls, 0) == Some(ws),
        wmap(renv, ws, 0) == Some(m),
        uf.len() == decl.len(),
        0 <= q < uf.len(),
        uf[q] is Some,
    ensures
        evals_to(p, cenv, uf[q]->Some_0, vof(m[q as nat])),
        deep ==> absent(sc.len(), uf[q]->Some_0),
    decreases dep, fls, 0nat,
{
    upd_spec(fs, tb, fds, dep, scope2(sc, deep), decl, fls, 0, none_upd(decl.len()), uf);
    rsrc_ws_at(fs, tb, fds, dep, scope2(sc, deep), decl, fls, 0, ws);
    assert(exists|k: int| 0 <= k < fls.len() && idx(decl, fls[k].0, 0) == Some(q as nat));
    let k = choose|k: int| 0 <= k < fls.len() && idx(decl, fls[k].0, 0) == Some(q as nat);
    assert(exists|j: nat| #[trigger] idx(decl, fls[k].0, 0) == Some(j) && (j as int) < uf.len() && rx(fs, tb, false, scope2(sc, deep), fls[k].1) is Some && uf[j as int] == rx(fs, tb, false, scope2(sc, deep), fls[k].1));
    let x = uf[q]->Some_0;
    assert(rx(fs, tb, false, scope2(sc, deep), fls[k].1) == Some(x));
    let rk = ws[k].1;
    assert(ws[k].0 == q as nat);
    assert(rsrc(fs, tb, fds, dep, scope2(sc, deep), fls[k].1) == Some(rk));
    wmap_get(renv, ws, 0, m, k);
    let vk = rmean(renv, rk)->Some_0;
    assert(m[q as nat] == vk);
    below_scope2(renv, sc, deep);
    resolve_sound(p, fs, tb, fds, dep, scope2(sc, deep), fls[k].1, cenv, renv, x, rk, vk);
    if deep {
        assert(scope2(sc, deep) == sc.push(Seq::<char>::empty()));
        assert(scope2(sc, deep)[sc.len() as int] == Seq::<char>::empty());
        absent_at(fs, tb, fds, dep, scope2(sc, deep), sc.len(), fls[k].1, x);
    }
}

// ------------------------------------------------------------------ 値の組み立て

/// 書いた式（uf の Some）は字段の値を、書いていない位置（None）は基の字段を写す。rbuild_fwd の使い方。
proof fn fill_sound(p: Prog, env: Map<nat, Val>, uf: Seq<Option<Expr>>, bxe: Expr, bs: Seq<RVal>, vs: Seq<RVal>)
    requires
        uf.len() >= 1,
        bs.len() == uf.len(),
        vs.len() == uf.len(),
        forall|q: int| 0 <= q < uf.len() && (#[trigger] uf[q]) is Some ==> evals_to(p, env, uf[q]->Some_0, vof(vs[q])),
        forall|q: int| 0 <= q < uf.len() && (#[trigger] uf[q]) is None ==> vs[q] == bs[q],
        (exists|q: int| 0 <= q < uf.len() && (#[trigger] uf[q]) is None) ==> evals_to(p, env, bxe, rval(vofs(bs, 0))),
    ensures
        evals_to(p, env, rbuild(fill(uf, bxe)), rval(vofs(vs, 0))),
{
    let n = uf.len();
    vofs_props(vs, 0);
    vofs_props(bs, 0);
    let es = fill(uf, bxe);
    assert(es.len() == n);
    assert(vofs(vs, 0).len() == n);
    assert(vofs(bs, 0).len() == n);
    assert forall|q: int| 0 <= q < es.len() implies evals_to(p, env, #[trigger] es[q], vofs(vs, 0)[q]) by {
        vofs_at0(vs, q);
        if uf[q] is Some {
            assert(es[q] == uf[q]->Some_0);
        } else {
            assert(es[q] == rfield(bxe, q as nat, n));
            assert(evals_to(p, env, bxe, rval(vofs(bs, 0))));
            rfield_eval(p, env, bxe, vofs(bs, 0), q as nat);
            vofs_at0(bs, q);
            assert(vs[q] == bs[q]);
            assert(rfield(bxe, q as nat, vofs(bs, 0).len()) == rfield(bxe, q as nat, n));
        }
    }
    rbuild_fwd(p, env, es, vofs(vs, 0));
}

/// 基のない記録の値：vs は宣言の位置の値の列（vof(Rec(vs)) の展開）。
proof fn vof_rec(vs: Seq<RVal>)
    requires
        vs.len() >= 1,
    ensures
        vof(RVal::Rec(vs)) == rval(vofs(vs, 0)),
{
    reveal_with_fuel(vof, 2);
}

// ------------------------------------------------------------------ 参照の鎖（e.f1…fk）

/// 鎖の下端：鎖の結果が値を持つなら、下端も値を持つ。
proof fn chain_inner(tb: Seq<(Seq<char>, Option<Ty>, Seq<Seq<char>>, Option<Ty>)>, fds: Seq<Sd>, dep: nat, renv: Map<nat, RVal>, r: RExpr, fls: Seq<Seq<char>>, i: nat, rr: RExpr)
    requires
        rsrc_chain(tb, fds, dep, r, fls, i) == Some(rr),
        rmean(renv, rr) is Some,
    ensures
        rmean(renv, r) is Some,
    decreases dep, fls.len() - i,
{
    reveal_with_fuel(rsrc_chain, 2);
    reveal_with_fuel(rmean, 2);
    if i < fls.len() {
        if let Some((pp, n)) = owner_pos(tb, fls[i as int], 0) {
            chain_inner(tb, fds, dep, renv, RExpr::Fld(Box::new(r), pdecl(n), pp), fls, i + 1, rr);
        }
    }
}

/// 一段の参照（e.f）：下端の値 rv の字段 pp の参照は、その字段の値の写しを持つ。
proof fn fld_step(p: Prog, cenv: Map<nat, Val>, renv: Map<nat, RVal>, r: RExpr, x: Expr, rv: RVal, n: nat, pp: nat)
    requires
        rmean(renv, r) == Some(rv),
        evals_to(p, cenv, x, vof(rv)),
        pp < n,
    ensures
        forall|v1: RVal| #[trigger] rmean(renv, RExpr::Fld(Box::new(r), pdecl(n), pp)) == Some(v1) ==> evals_to(p, cenv, rfield(x, pp, n), vof(v1)),
{
    reveal_with_fuel(rmean, 2);
    pos_pdecl(n, pp);
    assert forall|v1: RVal| #[trigger] rmean(renv, RExpr::Fld(Box::new(r), pdecl(n), pp)) == Some(v1) implies evals_to(p, cenv, rfield(x, pp, n), vof(v1)) by {
        match rv {
            RVal::Rec(vs) => {
                assert(vs.len() == n);
                vofs_props(vs, 0);
                vof_rec(vs);
                rfield_eval(p, cenv, x, vofs(vs, 0), pp);
                vofs_at0(vs, pp as int);
                assert(rfield(x, pp, vofs(vs, 0).len()) == rfield(x, pp, n));
            },
            _ => {},
        }
    }
}

/// 鎖の意味：下端の値を持ち、鎖の結果が値 v を持つなら、鎖の展開 c は vof(v) に評価される。
proof fn chain_sound(p: Prog, cenv: Map<nat, Val>, tb: Seq<(Seq<char>, Option<Ty>, Seq<Seq<char>>, Option<Ty>)>, fds: Seq<Sd>, dep: nat, renv: Map<nat, RVal>, r: RExpr, x: Expr, rv: RVal, fls: Seq<Seq<char>>, i: nat, rr: RExpr, c: Expr, v: RVal)
    requires
        rmean(renv, r) == Some(rv),
        evals_to(p, cenv, x, vof(rv)),
        rsrc_chain(tb, fds, dep, r, fls, i) == Some(rr),
        fld_chain(tb, x, fls, i) == Some(c),
        rmean(renv, rr) == Some(v),
    ensures
        evals_to(p, cenv, c, vof(v)),
    decreases dep, fls.len() - i,
{
    reveal_with_fuel(rsrc_chain, 2);
    reveal_with_fuel(fld_chain, 2);
    if i < fls.len() {
        if let Some((pp, n)) = owner_pos(tb, fls[i as int], 0) {
            owner_pos_lt(tb, fds, dep, fls[i as int], 0);
            let r1 = RExpr::Fld(Box::new(r), pdecl(n), pp);
            let x1 = rfield(x, pp, n);
            chain_inner(tb, fds, dep, renv, r1, fls, i + 1, rr);
            let v1 = rmean(renv, r1)->Some_0;
            assert(rmean(renv, r1) == Some(v1));
            fld_step(p, cenv, renv, r, x, rv, n, pp);
            assert(evals_to(p, cenv, x1, vof(v1)));
            chain_sound(p, cenv, tb, fds, dep, renv, r1, x1, v1, fls, i + 1, rr, c, v);
        }
    }
}

// ------------------------------------------------------------------ 記録の腕

/// 基のない記録（全部書いた構築）：字段の値を写す。
proof fn rec_none_arm(p: Prog, fs: Seq<Seq<char>>, tb: Seq<(Seq<char>, Option<Ty>, Seq<Seq<char>>, Option<Ty>)>, fds: Seq<Sd>, dep: nat, sc: Seq<Seq<char>>, decl: Seq<Seq<char>>, fls: Seq<(Seq<char>, Sx)>, cenv: Map<nat, Val>, renv: Map<nat, RVal>, c: Expr, uf: Seq<Option<Expr>>, ws: Seq<(nat, RExpr)>, v: RVal)
    requires
        funcs_ok(p, fs, tb, fds),
        envrel(cenv, renv),
        renv_below(renv, sc),
        decl.len() >= 1,
        rec_upd(fs, tb, false, sc, decl, fls, 0, none_upd(decl.len())) == Some(uf),
        rrecord(uf, None, sc.len()) == Ok(c),
        rsrc_ws(fs, tb, fds, dep, sc, decl, fls, 0) == Some(ws),
        rmean(renv, RExpr::Rec(pdecl(decl.len()), ws, None)) == Some(v),
    ensures
        evals_to(p, cenv, c, vof(v)),
    decreases dep, fls, 1nat,
{
    reveal_with_fuel(rmean, 2);
    let n = decl.len();
    upd_spec(fs, tb, fds, dep, sc, decl, fls, 0, none_upd(n), uf);
    nmissing_none(n);
    rec_upd_count(fs, tb, false, sc, decl, fls, 0, none_upd(n));
    assert(nmissing(uf) == 0);
    assert(c == rbuild(crate::records_exec::written(uf)));
    nmissing_iff(uf);
    assert(wmap(renv, ws, 0) is Some);
    let m = wmap(renv, ws, 0)->Some_0;
    assert(wmap(renv, ws, 0) == Some(m));
    let vs = place(pdecl(n), m, Seq::empty());
    assert(vs.len() == n);
    assert(v == RVal::Rec(vs));
    assert forall|q: int| 0 <= q < uf.len() implies (#[trigger] uf[q]) is Some by {
        assert(nmissing(uf) == 0);
    }
    assert forall|q: int| 0 <= q < uf.len() && (#[trigger] uf[q]) is Some implies evals_to(p, cenv, uf[q]->Some_0, vof(vs[q])) by {
        pos_contains(fs, tb, fds, dep, sc, decl, fls, false, uf, ws, renv, m, q);
        fields_at(p, fs, tb, fds, dep, sc, decl, fls, cenv, renv, false, uf, ws, m, q);
        assert(vs[q] == m[q as nat]);
    }
    fill_sound(p, cenv, uf, Expr::Unit, vs, vs);
    assert(fill(uf, Expr::Unit) =~= crate::records_exec::written(uf));
    assert(rbuild(fill(uf, Expr::Unit)) == rbuild(crate::records_exec::written(uf)));
    vof_rec(vs);
}

/// 基のある記録：欠けた字段があるので、源の構築は基の字段を見る（その形を取り出す）。
proof fn base_split(fs: Seq<Seq<char>>, tb: Seq<(Seq<char>, Option<Ty>, Seq<Seq<char>>, Option<Ty>)>, fds: Seq<Sd>, dep: nat, sc: Seq<Seq<char>>, decl: Seq<Seq<char>>, fls: Seq<(Seq<char>, Sx)>, bx: Expr, c: Expr, renv: Map<nat, RVal>, ws: Seq<(nat, RExpr)>, br: RExpr, uf: Seq<Option<Expr>>, v: RVal)
    requires
        decl.len() >= 1,
        rec_upd(fs, tb, false, scope2(sc, deep_rec(Some(bx), decl, fls)), decl, fls, 0, none_upd(decl.len())) == Some(uf),
        rrecord(uf, Some(bx), sc.len()) == Ok(c),
        rsrc_ws(fs, tb, fds, dep, scope2(sc, deep_rec(Some(bx), decl, fls)), decl, fls, 0) == Some(ws),
        rmean(renv, RExpr::Rec(pdecl(decl.len()), ws, Some(Box::new(br)))) == Some(v),
    ensures
        exists|bs: Seq<RVal>| rmean(renv, br) == Some(RVal::Rec(bs)) && bs.len() == decl.len(),
{
    reveal_with_fuel(rmean, 2);
    let n = decl.len();
    let deep = deep_rec(Some(bx), decl, fls);
    upd_spec(fs, tb, fds, dep, scope2(sc, deep), decl, fls, 0, none_upd(n), uf);
    nmissing_none(n);
    rec_upd_count(fs, tb, false, scope2(sc, deep), decl, fls, 0, none_upd(n));
    assert(nmissing(uf) != 0);
    nmissing_iff(uf);
    assert(exists|q: int| 0 <= q < uf.len() && (#[trigger] uf[q]) is None) by {
        assert(!(forall|q: int| 0 <= q < uf.len() ==> (#[trigger] uf[q]) is Some)) by {
            if forall|q: int| 0 <= q < uf.len() ==> (#[trigger] uf[q]) is Some {
                assert(nmissing(uf) == 0);
            }
        }
    }
    let q0 = choose|q: int| 0 <= q < uf.len() && (#[trigger] uf[q]) is None;
    assert(wmap(renv, ws, 0) is Some);
    let m = wmap(renv, ws, 0)->Some_0;
    assert(wmap(renv, ws, 0) == Some(m));
    pos_contains(fs, tb, fds, dep, sc, decl, fls, deep, uf, ws, renv, m, q0);
    assert(!m.contains_key(q0 as nat));
    assert(pdecl(n)[q0] == q0 as nat);
    assert(rmean(renv, br) is Some);
    let bs = rmean(renv, br)->Some_0->Rec_0;
    assert(rmean(renv, br) == Some(RVal::Rec(bs)));
    assert(bs.len() == n);
    assert(exists|bs2: Seq<RVal>| rmean(renv, br) == Some(RVal::Rec(bs2)) && bs2.len() == n) by {
        assert(rmean(renv, br) == Some(RVal::Rec(bs)) && bs.len() == n);
    }
}

/// 基のある記録の展開：欠けた字段は基の字段で埋まる（rupdate の二つの形、深い scope の有無）。
proof fn rec_some_arm(p: Prog, fs: Seq<Seq<char>>, tb: Seq<(Seq<char>, Option<Ty>, Seq<Seq<char>>, Option<Ty>)>, fds: Seq<Sd>, dep: nat, sc: Seq<Seq<char>>, decl: Seq<Seq<char>>, fls: Seq<(Seq<char>, Sx)>, cenv: Map<nat, Val>, renv: Map<nat, RVal>, bx: Expr, br: RExpr, bs: Seq<RVal>, c: Expr, uf: Seq<Option<Expr>>, ws: Seq<(nat, RExpr)>, v: RVal)
    requires
        funcs_ok(p, fs, tb, fds),
        envrel(cenv, renv),
        renv_below(renv, sc),
        decl.len() >= 1,
        bs.len() == decl.len(),
        rec_upd(fs, tb, false, scope2(sc, deep_rec(Some(bx), decl, fls)), decl, fls, 0, none_upd(decl.len())) == Some(uf),
        rrecord(uf, Some(bx), sc.len()) == Ok(c),
        rsrc_ws(fs, tb, fds, dep, scope2(sc, deep_rec(Some(bx), decl, fls)), decl, fls, 0) == Some(ws),
        rmean(renv, RExpr::Rec(pdecl(decl.len()), ws, Some(Box::new(br)))) == Some(v),
        rmean(renv, br) == Some(RVal::Rec(bs)),
        evals_to(p, cenv, bx, vof(RVal::Rec(bs))),
    ensures
        evals_to(p, cenv, c, vof(v)),
    decreases dep, fls, 1nat,
{
    reveal_with_fuel(rmean, 2);
    reveal_with_fuel(vof, 2);
    let n = decl.len();
    let deep = deep_rec(Some(bx), decl, fls);
    upd_spec(fs, tb, fds, dep, scope2(sc, deep), decl, fls, 0, none_upd(n), uf);
    nmissing_none(n);
    rec_upd_count(fs, tb, false, scope2(sc, deep), decl, fls, 0, none_upd(n));
    assert(nmissing(uf) != 0);
    nmissing_iff(uf);
    assert(exists|q: int| 0 <= q < uf.len() && (#[trigger] uf[q]) is None) by {
        assert(!(forall|q: int| 0 <= q < uf.len() ==> (#[trigger] uf[q]) is Some)) by {
            if forall|q: int| 0 <= q < uf.len() ==> (#[trigger] uf[q]) is Some {
                assert(nmissing(uf) == 0);
            }
        }
    }
    let q0 = choose|q: int| 0 <= q < uf.len() && (#[trigger] uf[q]) is None;
    assert(wmap(renv, ws, 0) is Some);
    let m = wmap(renv, ws, 0)->Some_0;
    assert(wmap(renv, ws, 0) == Some(m));
    pos_contains(fs, tb, fds, dep, sc, decl, fls, deep, uf, ws, renv, m, q0);
    assert(!m.contains_key(q0 as nat));
    assert(pdecl(n)[q0] == q0 as nat);
    let vs = place(pdecl(n), m, bs);
    assert(vs.len() == n);
    assert(v == RVal::Rec(vs));
    assert(vs.len() >= 1);
    vof_rec(vs);
    vofs_props(vs, 0);
    vofs_props(bs, 0);
    let w0 = vof(RVal::Rec(bs));
    vof_rec(bs);
    assert(w0 == rval(vofs(bs, 0)));
    assert forall|q: int| 0 <= q < uf.len() && (#[trigger] uf[q]) is Some implies evals_to(p, cenv, uf[q]->Some_0, vof(vs[q])) && (deep ==> absent(sc.len(), uf[q]->Some_0)) by {
        pos_contains(fs, tb, fds, dep, sc, decl, fls, deep, uf, ws, renv, m, q);
        fields_at(p, fs, tb, fds, dep, sc, decl, fls, cenv, renv, deep, uf, ws, m, q);
        assert(vs[q] == m[q as nat]);
    }
    assert forall|q: int| 0 <= q < uf.len() && (#[trigger] uf[q]) is None implies vs[q] == bs[q] by {
        pos_contains(fs, tb, fds, dep, sc, decl, fls, deep, uf, ws, renv, m, q);
        assert(!m.contains_key(q as nat));
        assert(vs[q] == bs[q]);
    }
    if !deep {
        assert(c == rbuild(fill(uf, bx)));
        fill_sound(p, cenv, uf, bx, bs, vs);
    } else {
        let k0 = sc.len();
        let cenv2 = cenv.insert(k0, w0);
        assert(c == Expr::Let(k0, Box::new(bx), Box::new(rbuild(fill(uf, Expr::Var(k0))))));
        assert forall|q: int| 0 <= q < uf.len() && (#[trigger] uf[q]) is Some implies evals_to(p, cenv2, uf[q]->Some_0, vof(vs[q])) by {
            pos_contains(fs, tb, fds, dep, sc, decl, fls, deep, uf, ws, renv, m, q);
            fields_at(p, fs, tb, fds, dep, sc, decl, fls, cenv, renv, deep, uf, ws, m, q);
            assert(vs[q] == m[q as nat]);
            eval_transfer(p, cenv, k0, w0, uf[q]->Some_0, vof(vs[q]));
        }
        bs_var(p, cenv2, k0);
        assert(cenv2[k0] == w0);
        assert(evals_to(p, cenv2, Expr::Var(k0), rval(vofs(bs, 0))));
        fill_sound(p, cenv2, uf, Expr::Var(k0), bs, vs);
        bs_let(p, cenv, k0, bx, rbuild(fill(uf, Expr::Var(k0))), w0, vof(v));
    }
}

// ------------------------------------------------------------------ 名前解決の定理

/// 字段の値の列の一つの写し：vofs(vs, 0) の q 番目は vof(vs[q])。
proof fn vofs_at0(vs: Seq<RVal>, q: int)
    requires
        0 <= q < vs.len(),
    ensures
        vofs(vs, 0)[q] == vof(vs[q]),
{
    vofs_props(vs, 0);
    assert(vofs(vs, 0)[q - 0] == vof(vs[q]));
    assert(q - 0 == q);
}

/// 核の環境と源の環境の関係は、同じ名前に同じ値（写し）を足しても保たれる（let の束縛）。
proof fn envrel_ins(cenv: Map<nat, Val>, renv: Map<nat, RVal>, k: nat, va: RVal)
    requires
        envrel(cenv, renv),
    ensures
        envrel(cenv.insert(k, vof(va)), renv.insert(k, va)),
{
    assert forall|j: nat| #[trigger] renv.insert(k, va).contains_key(j) implies cenv.insert(k, vof(va)).contains_key(j) && cenv.insert(k, vof(va))[j] == vof(renv.insert(k, va)[j]) by {
        if j != k {
            assert(renv.contains_key(j));
            assert(cenv.contains_key(j) && cenv[j] == vof(renv[j]));
        }
    }
}

/// 鎖の環境（位置 p0 から上に束縛を足す）は、位置 p0 より下の名前だけを持つ源の環境と、なお対応する。
proof fn envrel_chain(cenv: Map<nat, Val>, renv: Map<nat, RVal>, p0: nat, j: nat, k: nat, n: nat, pv: Val)
    requires
        envrel(cenv, renv),
        forall|q: nat| #[trigger] renv.contains_key(q) ==> q < p0,
    ensures
        envrel(chain_env(cenv, p0, j, k, n, pv), renv),
{
    assert forall|q: nat| #[trigger] renv.contains_key(q) implies chain_env(cenv, p0, j, k, n, pv).contains_key(q) && chain_env(cenv, p0, j, k, n, pv)[q] == vof(renv[q]) by {
        chain_env_keep(cenv, p0, j, k, n, pv, q);
        assert(cenv.contains_key(q) && cenv[q] == vof(renv[q]));
    }
}

/// 一つの名前（位置 pos、値 va）を源の環境に足す。核の環境の位置 pos に、その値 vof(va) が既にあるなら、対応は保たれる。
proof fn envrel_one(cenv: Map<nat, Val>, renv: Map<nat, RVal>, pos: nat, va: RVal)
    requires
        envrel(cenv, renv),
        cenv.contains_key(pos),
        cenv[pos] == vof(va),
    ensures
        envrel(cenv, renv.insert(pos, va)),
{
    assert forall|q: nat| #[trigger] renv.insert(pos, va).contains_key(q) implies cenv.contains_key(q) && cenv[q] == vof(renv.insert(pos, va)[q]) by {
        if q != pos {
            assert(renv.contains_key(q));
        }
    }
}

/// 枝の字段の束縛（sbind）と核の字段の束縛（fenv）は、同じ位置（pos + 1 + i）に同じ値を足すので、対応は保たれる。
proof fn envrel_fenv(cenv: Map<nat, Val>, renv: Map<nat, RVal>, pos: nat, vs: Seq<RVal>, ids: Seq<nat>, i: nat)
    requires
        envrel(cenv, renv),
        ids.len() == vs.len(),
        forall|q: int| 0 <= q < ids.len() ==> ids[q] == pos + 1 + q,
    ensures
        envrel(fenv(cenv, pos, vofs(vs, 0), i), sbind(renv, ids, vs, i)),
    decreases vs.len() - i,
{
    reveal_with_fuel(fenv, 1);
    reveal_with_fuel(sbind, 1);
    vofs_len(vs, 0);
    if i < vs.len() {
        vofs_at0(vs, i as int);
        envrel_ins(cenv, renv, ids[i as int], vs[i as int]);
        assert(cenv.insert(ids[i as int], vof(vs[i as int])) =~= cenv.insert(pos + 1 + i, vofs(vs, 0)[i as int]));
        envrel_fenv(cenv.insert(ids[i as int], vof(vs[i as int])), renv.insert(ids[i as int], vs[i as int]), pos, vs, ids, i + 1);
    }
}

/// 源の環境の名前は、scope の長さより下にある（scope を足しても、長さが増えるだけなので保たれる）。
proof fn below_mono(renv: Map<nat, RVal>, sc: Seq<Seq<char>>, sc2: Seq<Seq<char>>)
    requires
        renv_below(renv, sc),
        sc.len() <= sc2.len(),
    ensures
        renv_below(renv, sc2),
{
}

/// 名前 k（scope の長さ）に値を足し、scope に名前を一つ足す（let・match の some の枝・fold の累積）。
proof fn below_push(renv: Map<nat, RVal>, sc: Seq<Seq<char>>, x: Seq<char>, k: nat, va: RVal)
    requires
        renv_below(renv, sc),
        k == sc.len(),
    ensures
        renv_below(renv.insert(k, va), sc.push(x)),
{
    assert forall|q: nat| #[trigger] renv.insert(k, va).contains_key(q) implies q < sc.push(x).len() by {
        if q != k {
            assert(renv.contains_key(q));
        }
    }
}

/// 字段の束縛（sbind）は、名前の位置が scope の内側なら、源の環境の名前を scope の内側に保つ。
proof fn below_sbind(renv: Map<nat, RVal>, sc: Seq<Seq<char>>, ids: Seq<nat>, vs: Seq<RVal>, i: nat)
    requires
        renv_below(renv, sc),
        forall|q: int| 0 <= q < ids.len() ==> ids[q] < sc.len(),
    ensures
        renv_below(sbind(renv, ids, vs, i), sc),
    decreases ids.len() - i,
{
    reveal_with_fuel(sbind, 1);
    if i < ids.len() && i < vs.len() {
        assert(renv_below(renv.insert(ids[i as int], vs[i as int]), sc)) by {
            assert forall|q: nat| #[trigger] renv.insert(ids[i as int], vs[i as int]).contains_key(q) implies q < sc.len() by {
                if q != ids[i as int] {
                    assert(renv.contains_key(q));
                }
            }
        }
        below_sbind(renv.insert(ids[i as int], vs[i as int]), sc, ids, vs, i + 1);
    }
}

/// 呼出しの環境（rbind）の名前は、引数の数 m より下にある。
proof fn rbind_below(vs: Seq<RVal>, m: nat)
    ensures
        forall|q: nat| #[trigger] rbind(vs, m).contains_key(q) ==> q < m,
    decreases m,
{
    reveal_with_fuel(rbind, 1);
    if m > 0 && m <= vs.len() {
        rbind_below(vs, (m - 1) as nat);
        assert forall|q: nat| #[trigger] rbind(vs, m).contains_key(q) implies q < m by {
            if q != (m - 1) as nat {
                assert(rbind(vs, (m - 1) as nat).contains_key(q));
                assert(q < (m - 1) as nat);
            }
        }
    }
}

/// 源の環境の名前は、scope2（基を let で束縛する深い scope）で足されても、scope の長さより下にある。
proof fn below_scope2(renv: Map<nat, RVal>, sc: Seq<Seq<char>>, deep: bool)
    requires
        renv_below(renv, sc),
    ensures
        renv_below(renv, scope2(sc, deep)),
{
}

/// 直和型の値の写し（vof）は、字段の写しの列（pay_val）に対する構築子の鎖の値と同じ。
proof fn vof_sum(k: nat, n: nat, vs: Seq<RVal>)
    ensures
        vof(RVal::Sum(k, n, vs)) == vsum_from(k, n, 0, pay_val(vofs(vs, 0))),
{
    reveal_with_fuel(vof, 1);
    vofs_len(vs, 0);
    if vs.len() == 0 {
        reveal_with_fuel(vofs, 1);
    }
}

/// 直和型の枝の写し（層 j から）の長さは、層の数（ents.len() - j）と同じ。
proof fn rsrc_layers_len(fs: Seq<Seq<char>>, tb: Seq<(Seq<char>, Option<Ty>, Seq<Seq<char>>, Option<Ty>)>, fds: Seq<Sd>, dep: nat, sc0: Seq<Seq<char>>, ents: Seq<Seq<char>>, arms: Seq<(Spat, Sx)>, j: nat, es: Seq<(Seq<nat>, RExpr)>)
    requires
        j <= ents.len(),
        rsrc_layers(fs, tb, fds, dep, sc0, ents, arms, j) == Some(es),
    ensures
        es.len() == ents.len() - j,
    decreases ents.len() - j,
{
    reveal_with_fuel(rsrc_layers, 1);
    if j < ents.len() {
        assert(rsrc_layer(fs, tb, fds, dep, sc0, ents, arms, j) is Some && rsrc_layers(fs, tb, fds, dep, sc0, ents, arms, j + 1) is Some);
        let rest = rsrc_layers(fs, tb, fds, dep, sc0, ents, arms, j + 1)->Some_0;
        rsrc_layers_len(fs, tb, fds, dep, sc0, ents, arms, j + 1, rest);
    }
}

/// 直和型の枝の写し（層 j から）の層 k（j <= k < ents.len()）は、その層の rsrc_layer が返す枝の組である。
proof fn rsrc_layers_at(fs: Seq<Seq<char>>, tb: Seq<(Seq<char>, Option<Ty>, Seq<Seq<char>>, Option<Ty>)>, fds: Seq<Sd>, dep: nat, sc0: Seq<Seq<char>>, ents: Seq<Seq<char>>, arms: Seq<(Spat, Sx)>, j: nat, es: Seq<(Seq<nat>, RExpr)>, k: nat)
    requires
        j <= k < ents.len(),
        rsrc_layers(fs, tb, fds, dep, sc0, ents, arms, j) == Some(es),
    ensures
        rsrc_layer(fs, tb, fds, dep, sc0, ents, arms, k) == Some(es[(k - j) as int]),
    decreases ents.len() - j,
{
    reveal_with_fuel(rsrc_layers, 1);
    rsrc_layers_len(fs, tb, fds, dep, sc0, ents, arms, j, es);
    assert(rsrc_layer(fs, tb, fds, dep, sc0, ents, arms, j) is Some && rsrc_layers(fs, tb, fds, dep, sc0, ents, arms, j + 1) is Some);
    let ent = rsrc_layer(fs, tb, fds, dep, sc0, ents, arms, j)->Some_0;
    let rest = rsrc_layers(fs, tb, fds, dep, sc0, ents, arms, j + 1)->Some_0;
    assert(es == seq![ent] + rest);
    if j == k {
        assert(es[0] == ent);
    } else {
        rsrc_layers_at(fs, tb, fds, dep, sc0, ents, arms, j + 1, rest, k);
        vstd::seq::lemma_seq_add_index2(seq![ent], rest, (k - j) as int);
    }
}

/// 枝の本体の scope：外側の名前は変わらず、字段が二つ以上なら字段の数だけ長い（字段が一つ以下なら一つ長い）。
proof fn arm_scope_props(sc: Seq<Seq<char>>, bs: Seq<Seq<char>>)
    ensures
        arm_scope(sc, bs).len() >= sc.len() + 1,
        bs.len() >= 2 ==> arm_scope(sc, bs).len() == sc.len() + 1 + bs.len(),
        forall|q: int| 0 <= q < sc.len() ==> arm_scope(sc, bs)[q] == sc[q],
{
    assert forall|q: int| 0 <= q < sc.len() implies arm_scope(sc, bs)[q] == sc[q] by {
        if bs.len() >= 2 {
            vstd::seq::lemma_seq_add_index1(sc.push(Seq::empty()), bs, q);
        }
    }
}

/// 字段の式の列：要素ごとに vof(vs[j]) に評価されれば、写した値の列 vofs(vs, 0) の字段の式の列（fields_to）である。
proof fn fields_of(p: Prog, cenv: Map<nat, Val>, ces: Seq<Expr>, vs: Seq<RVal>)
    requires
        ces.len() == vs.len(),
        forall|j: nat| j < ces.len() ==> evals_to(p, cenv, #[trigger] ces[j as int], vof(vs[j as int])),
    ensures
        fields_to(p, cenv, ces, vofs(vs, 0)),
{
    vofs_len(vs, 0);
    assert forall|k: int| 0 <= k < ces.len() implies evals_to(p, cenv, #[trigger] ces[k], vofs(vs, 0)[k]) by {
        vofs_at0(vs, k);
        let j = k as nat;
        assert(j < ces.len());
        assert(evals_to(p, cenv, ces[j as int], vof(vs[j as int])));
    }
}

/// 名前表の項目の番号（vlook_from の結果の最初の成分）は、名前表の長さより小さい。
proof fn vlook_lt(tb: Seq<(Seq<char>, Option<Ty>, Seq<Seq<char>>, Option<Ty>)>, c: Seq<char>, i: nat)
    ensures
        vlook_from(tb, c, i) matches Some((j, _, _)) ==> j < tb.len(),
    decreases tb.len() - i,
{
    reveal_with_fuel(vlook_from, 1);
    if i < tb.len() {
        if vidx(tb[i as int].2, c, 0) is None {
            vlook_lt(tb, c, i + 1);
        }
    }
}

/// rsrc_ctor が Some なら、構築子は名前表の項目 i の k 番目で、字段の数 m は字段の式の列の長さ、写しは Ctor(k, n, rs)。
proof fn rsrc_ctor_inv(tb: Seq<(Seq<char>, Option<Ty>, Seq<Seq<char>>, Option<Ty>)>, c: Seq<char>, rs: Seq<RExpr>, r: RExpr) -> (ikm: (nat, nat, nat))
    requires
        rsrc_ctor(tb, c, rs) == Some(r),
    ensures
        vlook(tb, c) == Some(ikm),
        ikm.0 < tb.len(),
        ikm.2 == rs.len(),
        ikm.1 < tb[ikm.0 as int].2.len(),
        r == RExpr::Ctor(ikm.1, tb[ikm.0 as int].2.len(), rs),
{
    assert(vlook(tb, c) is Some) by {
        if vlook(tb, c) is None {
            assert(rsrc_ctor(tb, c, rs) is None);
        }
    }
    let ikm = vlook(tb, c)->Some_0;
    assert(vlook(tb, c) == Some(ikm));
    vlook_lt(tb, c, 0);
    ikm
}

/// 名前解決の定理の変数の腕と、書いた式の腕の振り分け。
/// 定理：rx が c を返し、rsrc が r を返し、rmean(r) が v なら、c は vof(v) に評価される（部分正しさ、印なし）。
pub proof fn resolve_sound(p: Prog, fs: Seq<Seq<char>>, tb: Seq<(Seq<char>, Option<Ty>, Seq<Seq<char>>, Option<Ty>)>, fds: Seq<Sd>, dep: nat, sc: Seq<Seq<char>>, e: Sx, cenv: Map<nat, Val>, renv: Map<nat, RVal>, c: Expr, r: RExpr, v: RVal)
    requires
        funcs_ok(p, fs, tb, fds),
        envrel(cenv, renv),
        renv_below(renv, sc),
        rx(fs, tb, false, sc, e) == Some(c),
        rsrc(fs, tb, fds, dep, sc, e) == Some(r),
        rmean(renv, r) == Some(v),
    ensures
        evals_to(p, cenv, c, vof(v)),
    decreases dep, e, 2nat,
{
    reveal_with_fuel(rx, 2);
    reveal_with_fuel(rsrc, 2);
    reveal_with_fuel(rmean, 2);
    reveal_with_fuel(vof, 2);
    match e {
        Sx::Int(n) => {
            bs_leaf(p, cenv, Expr::Int(n));
        },
        Sx::Bool(b) => {
            bs_leaf(p, cenv, Expr::Bool(b));
        },
        Sx::Unit => {
            bs_leaf(p, cenv, Expr::Unit);
        },
        Sx::Chr(ch) => {
            bs_leaf(p, cenv, Expr::Char(ch as u32 as int));
        },
        Sx::None(_) => {
            assert(c is None);
            assert(r == RExpr::None);
            assert(v == RVal::None);
            bs_leaf(p, cenv, c);
        },
        Sx::Some(..) => some_arm(p, fs, tb, fds, dep, sc, e, cenv, renv, c, r, v),
        Sx::Var(x) => {
            assert(x.len() != 0);
            if idx(sc, x, 0) is Some {
                let k = idx(sc, x, 0)->Some_0;
                assert(c == Expr::Var(k));
                assert(r == RExpr::Var(k));
                assert(renv.contains_key(k));
                assert(cenv.contains_key(k) && cenv[k] == vof(renv[k]));
                bs_var(p, cenv, k);
            } else {
                ctor_var_arm(p, fs, tb, fds, dep, sc, e, cenv, renv, c, r, v);
            }
        },
        Sx::Pair(..) => pair_arm(p, fs, tb, fds, dep, sc, e, cenv, renv, c, r, v),
        Sx::Fld(..) => fld_arm(p, fs, tb, fds, dep, sc, e, cenv, renv, c, r, v),
        Sx::If(..) => if_arm(p, fs, tb, fds, dep, sc, e, cenv, renv, c, r, v),
        Sx::Let(..) => let_arm(p, fs, tb, fds, dep, sc, e, cenv, renv, c, r, v),
        Sx::Match(..) => match_arm(p, fs, tb, fds, dep, sc, e, cenv, renv, c, r, v),
        Sx::List(..) => list_arm(p, fs, tb, fds, dep, sc, e, cenv, renv, c, r, v),
        Sx::Str(..) => str_arm(p, fs, tb, fds, dep, sc, e, cenv, renv, c, r, v),
        Sx::Fold(..) => fold_arm(p, fs, tb, fds, dep, sc, e, cenv, renv, c, r, v),
        Sx::Builtin(..) => builtin_arm(p, fs, tb, fds, dep, sc, e, cenv, renv, c, r, v),
        Sx::Call(f, _) => {
            if idx(fs, f, 0) is Some {
                call_arm(p, fs, tb, fds, dep, sc, e, cenv, renv, c, r, v);
            } else {
                ctor_call_arm(p, fs, tb, fds, dep, sc, e, cenv, renv, c, r, v);
            }
        },
        Sx::Rec(_, _, None) => rec_none_top(p, fs, tb, fds, dep, sc, e, cenv, renv, c, r, v),
        Sx::Rec(_, _, Some(_)) => rec_some_top(p, fs, tb, fds, dep, sc, e, cenv, renv, c, r, v),
        Sx::SumMatch(..) => {
            if any_sm(e) {
                sum_any_arm(p, fs, tb, fds, dep, sc, e, cenv, renv, c, r, v);
            } else {
                sum_layer_arm(p, fs, tb, fds, dep, sc, e, cenv, renv, c, r, v);
            }
        },
        _ => {},
    }
}

/// 対の腕：成分の定理と bs_pair。
proof fn pair_arm(p: Prog, fs: Seq<Seq<char>>, tb: Seq<(Seq<char>, Option<Ty>, Seq<Seq<char>>, Option<Ty>)>, fds: Seq<Sd>, dep: nat, sc: Seq<Seq<char>>, e: Sx, cenv: Map<nat, Val>, renv: Map<nat, RVal>, c: Expr, r: RExpr, v: RVal)
    requires
        funcs_ok(p, fs, tb, fds),
        envrel(cenv, renv),
        e is Pair,
        renv_below(renv, sc),
        rx(fs, tb, false, sc, e) == Some(c),
        rsrc(fs, tb, fds, dep, sc, e) == Some(r),
        rmean(renv, r) == Some(v),
    ensures
        evals_to(p, cenv, c, vof(v)),
    decreases dep, e, 1nat,
{
    reveal_with_fuel(rx, 2);
    reveal_with_fuel(rsrc, 2);
    reveal_with_fuel(rmean, 2);
    reveal_with_fuel(vof, 2);
    match e {
        Sx::Pair(a, b) => {
            assert(rx(fs, tb, false, sc, *a) is Some && rx(fs, tb, false, sc, *b) is Some);
            let x = rx(fs, tb, false, sc, *a)->Some_0;
            let y = rx(fs, tb, false, sc, *b)->Some_0;
            assert(c == Expr::Pair(Box::new(x), Box::new(y)));
            assert(rsrc(fs, tb, fds, dep, sc, *a) is Some && rsrc(fs, tb, fds, dep, sc, *b) is Some);
            let ra = rsrc(fs, tb, fds, dep, sc, *a)->Some_0;
            let rb = rsrc(fs, tb, fds, dep, sc, *b)->Some_0;
            assert(r == RExpr::Pair(Box::new(ra), Box::new(rb)));
            assert(rmean(renv, ra) is Some && rmean(renv, rb) is Some);
            let va = rmean(renv, ra)->Some_0;
            let vb = rmean(renv, rb)->Some_0;
            assert(v == RVal::Pair(Box::new(va), Box::new(vb)));
            resolve_sound(p, fs, tb, fds, dep, sc, *a, cenv, renv, x, ra, va);
            resolve_sound(p, fs, tb, fds, dep, sc, *b, cenv, renv, y, rb, vb);
            bs_pair(p, cenv, x, y, vof(va), vof(vb));
        },
        _ => {},
    }
}

/// if の腕：条件の定理で真偽値を得て、選んだ枝の定理と bs_if。枝の選び方は rmean の if の腕と同じ。
proof fn if_arm(p: Prog, fs: Seq<Seq<char>>, tb: Seq<(Seq<char>, Option<Ty>, Seq<Seq<char>>, Option<Ty>)>, fds: Seq<Sd>, dep: nat, sc: Seq<Seq<char>>, e: Sx, cenv: Map<nat, Val>, renv: Map<nat, RVal>, c: Expr, r: RExpr, v: RVal)
    requires
        funcs_ok(p, fs, tb, fds),
        envrel(cenv, renv),
        e is If,
        renv_below(renv, sc),
        rx(fs, tb, false, sc, e) == Some(c),
        rsrc(fs, tb, fds, dep, sc, e) == Some(r),
        rmean(renv, r) == Some(v),
    ensures
        evals_to(p, cenv, c, vof(v)),
    decreases dep, e, 1nat,
{
    reveal_with_fuel(rx, 1);
    reveal_with_fuel(rsrc, 1);
    reveal_with_fuel(rmean, 1);
    reveal_with_fuel(vof, 1);
    match e {
        Sx::If(q, a, b) => {
            assert(rx(fs, tb, false, sc, *q) is Some && rx(fs, tb, false, sc, *a) is Some && rx(fs, tb, false, sc, *b) is Some);
            let x = rx(fs, tb, false, sc, *q)->Some_0;
            let y = rx(fs, tb, false, sc, *a)->Some_0;
            let z = rx(fs, tb, false, sc, *b)->Some_0;
            assert(c == Expr::If(Box::new(x), Box::new(y), Box::new(z)));
            assert(rsrc(fs, tb, fds, dep, sc, *q) is Some && rsrc(fs, tb, fds, dep, sc, *a) is Some && rsrc(fs, tb, fds, dep, sc, *b) is Some);
            let rq = rsrc(fs, tb, fds, dep, sc, *q)->Some_0;
            let ra = rsrc(fs, tb, fds, dep, sc, *a)->Some_0;
            let rb = rsrc(fs, tb, fds, dep, sc, *b)->Some_0;
            assert(r == RExpr::If(Box::new(rq), Box::new(ra), Box::new(rb)));
            assert(rmean(renv, rq) is Some);
            let vq = rmean(renv, rq)->Some_0;
            resolve_sound(p, fs, tb, fds, dep, sc, *q, cenv, renv, x, rq, vq);
            match vq {
                RVal::Bool(true) => {
                    assert(rmean(renv, ra) == Some(v));
                    resolve_sound(p, fs, tb, fds, dep, sc, *a, cenv, renv, y, ra, v);
                    assert(vof(vq) == Val::Bool(true));
                    bs_if(p, cenv, x, y, z, true, vof(v));
                },
                RVal::Bool(false) => {
                    assert(rmean(renv, rb) == Some(v));
                    resolve_sound(p, fs, tb, fds, dep, sc, *b, cenv, renv, z, rb, v);
                    assert(vof(vq) == Val::Bool(false));
                    bs_if(p, cenv, x, y, z, false, vof(v));
                },
                _ => {
                    assert(false);
                },
            }
        },
        _ => {},
    }
}

/// let の腕：束縛の式の定理と、本体の定理（名前は sc.len() の位置、環境はその名前に値を足す）。
/// 本体は scope に名前 x を足して解決し、その位置は sc.len() なので、環境の名前 sc.len() に値を足して読む。
#[verifier::rlimit(100)]
#[verifier::rlimit(50)]
proof fn let_arm(p: Prog, fs: Seq<Seq<char>>, tb: Seq<(Seq<char>, Option<Ty>, Seq<Seq<char>>, Option<Ty>)>, fds: Seq<Sd>, dep: nat, sc: Seq<Seq<char>>, e: Sx, cenv: Map<nat, Val>, renv: Map<nat, RVal>, c: Expr, r: RExpr, v: RVal)
    requires
        funcs_ok(p, fs, tb, fds),
        envrel(cenv, renv),
        e is Let,
        renv_below(renv, sc),
        rx(fs, tb, false, sc, e) == Some(c),
        rsrc(fs, tb, fds, dep, sc, e) == Some(r),
        rmean(renv, r) == Some(v),
    ensures
        evals_to(p, cenv, c, vof(v)),
    decreases dep, e, 1nat,
{
    reveal_with_fuel(rx, 1);
    reveal_with_fuel(rsrc, 1);
    reveal_with_fuel(rmean, 1);
    reveal_with_fuel(vof, 1);
    match e {
        Sx::Let(x, a, b) => {
            assert(rx(fs, tb, false, sc, *a) is Some && rx(fs, tb, false, sc.push(x), *b) is Some);
            let ca = rx(fs, tb, false, sc, *a)->Some_0;
            let cb = rx(fs, tb, false, sc.push(x), *b)->Some_0;
            assert(c == Expr::Let(sc.len(), Box::new(ca), Box::new(cb)));
            assert(rsrc(fs, tb, fds, dep, sc, *a) is Some && rsrc(fs, tb, fds, dep, sc.push(x), *b) is Some);
            let ra = rsrc(fs, tb, fds, dep, sc, *a)->Some_0;
            let rb = rsrc(fs, tb, fds, dep, sc.push(x), *b)->Some_0;
            assert(r == RExpr::Let(sc.len(), Box::new(ra), Box::new(rb)));
            assert(rmean(renv, ra) is Some);
            let va = rmean(renv, ra)->Some_0;
            assert(rmean(renv.insert(sc.len(), va), rb) == Some(v));
            resolve_sound(p, fs, tb, fds, dep, sc, *a, cenv, renv, ca, ra, va);
            envrel_ins(cenv, renv, sc.len(), va);
            below_push(renv, sc, x, sc.len(), va);
            resolve_sound(p, fs, tb, fds, dep, sc.push(x), *b, cenv.insert(sc.len(), vof(va)), renv.insert(sc.len(), va), cb, rb, v);
            bs_let(p, cenv, sc.len(), ca, cb, vof(va), vof(v));
        },
        _ => {},
    }
}

/// match の腕（Option の match）：走査する式の定理と、none か some の枝の定理と bs_match。
/// some の枝は名前 x を sc.len() の位置に束縛し、環境はその名前に値を足す（let の腕と同じ）。
proof fn match_arm(p: Prog, fs: Seq<Seq<char>>, tb: Seq<(Seq<char>, Option<Ty>, Seq<Seq<char>>, Option<Ty>)>, fds: Seq<Sd>, dep: nat, sc: Seq<Seq<char>>, e: Sx, cenv: Map<nat, Val>, renv: Map<nat, RVal>, c: Expr, r: RExpr, v: RVal)
    requires
        funcs_ok(p, fs, tb, fds),
        envrel(cenv, renv),
        e is Match,
        renv_below(renv, sc),
        rx(fs, tb, false, sc, e) == Some(c),
        rsrc(fs, tb, fds, dep, sc, e) == Some(r),
        rmean(renv, r) == Some(v),
    ensures
        evals_to(p, cenv, c, vof(v)),
    decreases dep, e, 1nat,
{
    reveal_with_fuel(rx, 1);
    reveal_with_fuel(rsrc, 1);
    reveal_with_fuel(rmean, 1);
    reveal_with_fuel(vof, 1);
    match e {
        Sx::Match(m, nb, x, sb) => {
            assert(idx(sc, x, 0) is None);
            assert(rx(fs, tb, false, sc, *m) is Some && rx(fs, tb, false, sc, *nb) is Some && rx(fs, tb, false, sc.push(x), *sb) is Some);
            let cm = rx(fs, tb, false, sc, *m)->Some_0;
            let cn = rx(fs, tb, false, sc, *nb)->Some_0;
            let cb = rx(fs, tb, false, sc.push(x), *sb)->Some_0;
            assert(c == Expr::Match(Box::new(cm), Box::new(cn), sc.len(), Box::new(cb)));
            assert(rsrc(fs, tb, fds, dep, sc, *m) is Some && rsrc(fs, tb, fds, dep, sc, *nb) is Some && rsrc(fs, tb, fds, dep, sc.push(x), *sb) is Some);
            let rm = rsrc(fs, tb, fds, dep, sc, *m)->Some_0;
            let rn = rsrc(fs, tb, fds, dep, sc, *nb)->Some_0;
            let rb = rsrc(fs, tb, fds, dep, sc.push(x), *sb)->Some_0;
            assert(r == RExpr::Match(Box::new(rm), Box::new(rn), sc.len(), Box::new(rb)));
            assert(rmean(renv, rm) is Some);
            let mv = rmean(renv, rm)->Some_0;
            assert(rmean(renv, rm) == Some(mv));
            resolve_sound(p, fs, tb, fds, dep, sc, *m, cenv, renv, cm, rm, mv);
            match mv {
                RVal::None => {
                    assert(rmean(renv, rn) == Some(v));
                    resolve_sound(p, fs, tb, fds, dep, sc, *nb, cenv, renv, cn, rn, v);
                    bs_match(p, cenv, cm, cn, sc.len(), cb, vof(mv), vof(v));
                },
                RVal::Some(w) => {
                    assert(rmean(renv.insert(sc.len(), *w), rb) == Some(v));
                    envrel_ins(cenv, renv, sc.len(), *w);
                    below_push(renv, sc, x, sc.len(), *w);
                    resolve_sound(p, fs, tb, fds, dep, sc.push(x), *sb, cenv.insert(sc.len(), vof(*w)), renv.insert(sc.len(), *w), cb, rb, v);
                    bs_match(p, cenv, cm, cn, sc.len(), cb, vof(mv), vof(v));
                },
                _ => {
                    assert(false);
                },
            }
        },
        _ => {},
    }
}

/// rxs の位置 i からの列：列の k 番目は、源の位置 i + k の式の写し（rx と同じ scope）。
proof fn rxs_at(fs: Seq<Seq<char>>, tb: Seq<(Seq<char>, Option<Ty>, Seq<Seq<char>>, Option<Ty>)>, fds: Seq<Sd>, dep: nat, sc: Seq<Seq<char>>, es: Seq<Sx>, i: nat, ces: Seq<Expr>)
    requires
        i <= es.len(),
        rxs(fs, tb, false, sc, es, i) == Some(ces),
    ensures
        ces.len() as int == es.len() as int - i as int,
        forall|k: nat| k < ces.len() ==> rx(fs, tb, false, sc, #[trigger] es[(i + k) as int]) == Some(ces[k as int]),
    decreases dep, es.len() - i,
{
    reveal_with_fuel(rxs, 1);
    if i < es.len() {
        assert(rx(fs, tb, false, sc, es[i as int]) is Some && rxs(fs, tb, false, sc, es, i + 1) is Some);
        let x = rx(fs, tb, false, sc, es[i as int])->Some_0;
        let xs = rxs(fs, tb, false, sc, es, i + 1)->Some_0;
        assert(ces == seq![x] + xs);
        rxs_at(fs, tb, fds, dep, sc, es, i + 1, xs);
        assert forall|k: nat| k < ces.len() implies rx(fs, tb, false, sc, #[trigger] es[(i + k) as int]) == Some(ces[k as int]) by {
            if k == 0 {
                assert(ces[0] == x);
            } else {
                assert(rx(fs, tb, false, sc, es[((i + 1) + (k - 1)) as int]) == Some(xs[(k - 1) as int]));
                assert(ces[k as int] == xs[(k - 1) as int]);
            }
        }
    } else {
        assert(ces == Seq::<Expr>::empty());
    }
}

/// rsrcs の位置 i からの列：列の k 番目は、源の位置 i + k の式の写し。
proof fn rsrcs_at(fs: Seq<Seq<char>>, tb: Seq<(Seq<char>, Option<Ty>, Seq<Seq<char>>, Option<Ty>)>, fds: Seq<Sd>, dep: nat, sc: Seq<Seq<char>>, es: Seq<Sx>, i: nat, rs: Seq<RExpr>)
    requires
        i <= es.len(),
        rsrcs(fs, tb, fds, dep, sc, es, i) == Some(rs),
    ensures
        rs.len() as int == es.len() as int - i as int,
        forall|k: nat| k < rs.len() ==> rsrc(fs, tb, fds, dep, sc, #[trigger] es[(i + k) as int]) == Some(rs[k as int]),
    decreases dep, es.len() - i,
{
    reveal_with_fuel(rsrcs, 1);
    if i < es.len() {
        assert(rsrc(fs, tb, fds, dep, sc, es[i as int]) is Some && rsrcs(fs, tb, fds, dep, sc, es, i + 1) is Some);
        let r = rsrc(fs, tb, fds, dep, sc, es[i as int])->Some_0;
        let rr = rsrcs(fs, tb, fds, dep, sc, es, i + 1)->Some_0;
        assert(rs == seq![r] + rr);
        rsrcs_at(fs, tb, fds, dep, sc, es, i + 1, rr);
        assert forall|k: nat| k < rs.len() implies rsrc(fs, tb, fds, dep, sc, #[trigger] es[(i + k) as int]) == Some(rs[k as int]) by {
            if k == 0 {
                assert(rs[0] == r);
            } else {
                assert(rsrc(fs, tb, fds, dep, sc, es[((i + 1) + (k - 1)) as int]) == Some(rr[(k - 1) as int]));
                assert(rs[k as int] == rr[(k - 1) as int]);
            }
        }
    } else {
        assert(rs == Seq::<RExpr>::empty());
    }
}

/// rmeans の位置 i からの列：列の k 番目は、位置 i + k の式の意味。
proof fn rmeans_at(env: Map<nat, RVal>, rs: Seq<RExpr>, i: nat, vs: Seq<RVal>)
    requires
        i <= rs.len(),
        rmeans(env, rs, i) == Some(vs),
    ensures
        vs.len() as int == rs.len() as int - i as int,
        forall|k: nat| k < vs.len() ==> rmean(env, #[trigger] rs[(i + k) as int]) == Some(vs[k as int]),
    decreases rs.len() - i,
{
    reveal_with_fuel(rmeans, 1);
    if i < rs.len() {
        assert(rmean(env, rs[i as int]) is Some && rmeans(env, rs, i + 1) is Some);
        let v = rmean(env, rs[i as int])->Some_0;
        let vv = rmeans(env, rs, i + 1)->Some_0;
        assert(vs == seq![v] + vv);
        rmeans_at(env, rs, i + 1, vv);
        assert forall|k: nat| k < vs.len() implies rmean(env, #[trigger] rs[(i + k) as int]) == Some(vs[k as int]) by {
            if k == 0 {
                assert(vs[0] == v);
            } else {
                assert(rmean(env, rs[((i + 1) + (k - 1)) as int]) == Some(vv[(k - 1) as int]));
                assert(vs[k as int] == vv[(k - 1) as int]);
            }
        }
    } else {
        assert(vs == Seq::<RVal>::empty());
    }
}

/// 列の要素ごとの定理：k から先の要素 j は、核の式 ces[j] が vof(vs[j]) に評価される（resolve_sound を要素に当てる）。
proof fn list_elts(p: Prog, fs: Seq<Seq<char>>, tb: Seq<(Seq<char>, Option<Ty>, Seq<Seq<char>>, Option<Ty>)>, fds: Seq<Sd>, dep: nat, sc: Seq<Seq<char>>, es: Seq<Sx>, cenv: Map<nat, Val>, renv: Map<nat, RVal>, ces: Seq<Expr>, rs: Seq<RExpr>, vs: Seq<RVal>, k: nat)
    requires
        funcs_ok(p, fs, tb, fds),
        envrel(cenv, renv),
        renv_below(renv, sc),
        ces.len() == es.len(),
        rs.len() == es.len(),
        vs.len() == es.len(),
        forall|j: nat| j < es.len() ==> rx(fs, tb, false, sc, #[trigger] es[j as int]) == Some(ces[j as int]),
        forall|j: nat| j < es.len() ==> rsrc(fs, tb, fds, dep, sc, #[trigger] es[j as int]) == Some(rs[j as int]),
        forall|j: nat| j < es.len() ==> rmean(renv, #[trigger] rs[j as int]) == Some(vs[j as int]),
    ensures
        forall|j: nat| k <= j < es.len() ==> evals_to(p, cenv, #[trigger] ces[j as int], vof(vs[j as int])),
    decreases dep, es, es.len() - k,
{
    if k < es.len() {
        resolve_sound(p, fs, tb, fds, dep, sc, es[k as int], cenv, renv, ces[k as int], rs[k as int], vs[k as int]);
        list_elts(p, fs, tb, fds, dep, sc, es, cenv, renv, ces, rs, vs, k + 1);
    }
}

/// 引数の列：要素 j（k から先）が vof(vs[j]) に評価されれば、位置 k からの引数の列は vofs(vs, k) に評価される。
proof fn args_of(p: Prog, env: Map<nat, Val>, ces: Seq<Expr>, vs: Seq<RVal>, k: nat)
    requires
        ces.len() == vs.len(),
        forall|j: nat| k <= j < ces.len() ==> evals_to(p, env, #[trigger] ces[j as int], vof(vs[j as int])),
    ensures
        args_to(p, env, ces, k, vofs(vs, k)),
    decreases ces.len() - k,
{
    reveal_with_fuel(vofs, 1);
    reveal_with_fuel(eval_args, 1);
    if k >= ces.len() {
        assert(eval_args(p, 1, env, ces, k) == ResSeq::Done(Seq::<Val>::empty()));
        assert(vofs(vs, k) == Seq::<Val>::empty());
    } else {
        args_of(p, env, ces, vs, k + 1);
        assert(evals_to(p, env, ces[k as int], vof(vs[k as int])));
        assert(args_to(p, env, ces, k + 1, vofs(vs, k + 1)));
        let n1 = choose|n: nat| #[trigger] eval(p, n, env, ces[k as int]) == Res::Done(vof(vs[k as int]));
        let n2 = choose|n: nat| #[trigger] eval_args(p, n, env, ces, k + 1) == ResSeq::Done(vofs(vs, k + 1));
        let n = max(n1, n2);
        lift(p, n1, n, env, ces[k as int]);
        mono_args(p, n2, n, env, ces, k + 1);
        assert(eval_args(p, n + 1, env, ces, k) == ResSeq::Done(seq![vof(vs[k as int])] + vofs(vs, k + 1)));
        assert(vofs(vs, k) == seq![vof(vs[k as int])] + vofs(vs, k + 1));
    }
}

/// 要素ごとの名前の位置：k から先の要素 j は、位置 n を参照も束縛もしない（absent_at を要素に当てる）。
proof fn absent_at_elts(fs: Seq<Seq<char>>, tb: Seq<(Seq<char>, Option<Ty>, Seq<Seq<char>>, Option<Ty>)>, fds: Seq<Sd>, dep: nat, t: Seq<Seq<char>>, n: nat, es: Seq<Sx>, ces: Seq<Expr>, k: nat)
    requires
        n < t.len(),
        t[n as int] == Seq::<char>::empty(),
        ces.len() == es.len(),
        forall|j: nat| j < es.len() ==> rx(fs, tb, false, t, #[trigger] es[j as int]) == Some(ces[j as int]),
        forall|j: nat| j < es.len() ==> rsrc(fs, tb, fds, dep, t, #[trigger] es[j as int]) is Some,
    ensures
        forall|j: nat| k <= j < es.len() ==> absent(n, #[trigger] ces[j as int]),
    decreases dep, es, es.len() - k,
{
    if k < es.len() {
        absent_at(fs, tb, fds, dep, t, n, es[k as int], ces[k as int]);
        absent_at_elts(fs, tb, fds, dep, t, n, es, ces, k + 1);
    }
}

/// 引数の列の名前の位置：要素ごとに absent なら、列の absent_args は真。
proof fn absent_all(n: nat, ces: Seq<Expr>, k: nat)
    requires
        forall|j: nat| k <= j < ces.len() ==> absent(n, #[trigger] ces[j as int]),
    ensures
        absent_args(n, ces, k),
    decreases ces.len() - k,
{
    reveal_with_fuel(absent_args, 1);
    if k < ces.len() {
        absent_all(n, ces, k + 1);
    }
}

/// List の腕の名前の位置：要素の式（rx の列）は位置 n を参照も束縛もしない。
proof fn absent_at_list(fs: Seq<Seq<char>>, tb: Seq<(Seq<char>, Option<Ty>, Seq<Seq<char>>, Option<Ty>)>, fds: Seq<Sd>, dep: nat, t: Seq<Seq<char>>, n: nat, e: Sx, c: Expr)
    requires
        n < t.len(),
        t[n as int] == Seq::<char>::empty(),
        e is List,
        rx(fs, tb, false, t, e) == Some(c),
        rsrc(fs, tb, fds, dep, t, e) is Some,
    ensures
        absent(n, c),
    decreases dep, e, 0nat,
{
    reveal_with_fuel(rx, 1);
    reveal_with_fuel(rsrc, 1);
    reveal_with_fuel(absent, 1);
    match e {
        Sx::List(ty, es) => {
            assert(to_ty(ty, tb, false) is Some && rxs(fs, tb, false, t, es, 0) is Some);
            let u = to_ty(ty, tb, false)->Some_0;
            let ces = rxs(fs, tb, false, t, es, 0)->Some_0;
            assert(c == Expr::List(u, ces));
            assert(rsrcs(fs, tb, fds, dep, t, es, 0) is Some);
            let rs = rsrcs(fs, tb, fds, dep, t, es, 0)->Some_0;
            rxs_at(fs, tb, fds, dep, t, es, 0, ces);
            rsrcs_at(fs, tb, fds, dep, t, es, 0, rs);
            assert forall|j: nat| j < es.len() implies rx(fs, tb, false, t, #[trigger] es[j as int]) == Some(ces[j as int]) by {
                assert(rx(fs, tb, false, t, es[(0 + j) as int]) == Some(ces[j as int]));
            }
            assert forall|j: nat| j < es.len() implies rsrc(fs, tb, fds, dep, t, #[trigger] es[j as int]) is Some by {
                assert(rsrc(fs, tb, fds, dep, t, es[(0 + j) as int]) == Some(rs[j as int]));
            }
            absent_at_elts(fs, tb, fds, dep, t, n, es, ces, 0);
            absent_all(n, ces, 0);
        },
        _ => {},
    }
}

/// 文字列の名前の位置：文字の式は参照も束縛もしない。
proof fn absent_at_str(n: nat, c: Expr, w: Seq<char>)
    requires
        c == Expr::List(Ty::Char, str_exprs(w)),
    ensures
        absent(n, c),
{
    reveal_with_fuel(absent, 1);
    assert forall|j: nat| j < str_exprs(w).len() implies absent(n, #[trigger] str_exprs(w)[j as int]) by {
        assert(str_exprs(w)[j as int] == Expr::Char(w[j as int] as u32 as int));
    }
    absent_all(n, str_exprs(w), 0);
}

/// list の腕：要素ごとの定理（list_elts）と引数の列（args_of）と bs_list。要素の写しは位置 0 からの列。
proof fn list_arm(p: Prog, fs: Seq<Seq<char>>, tb: Seq<(Seq<char>, Option<Ty>, Seq<Seq<char>>, Option<Ty>)>, fds: Seq<Sd>, dep: nat, sc: Seq<Seq<char>>, e: Sx, cenv: Map<nat, Val>, renv: Map<nat, RVal>, c: Expr, r: RExpr, v: RVal)
    requires
        funcs_ok(p, fs, tb, fds),
        envrel(cenv, renv),
        e is List,
        renv_below(renv, sc),
        rx(fs, tb, false, sc, e) == Some(c),
        rsrc(fs, tb, fds, dep, sc, e) == Some(r),
        rmean(renv, r) == Some(v),
    ensures
        evals_to(p, cenv, c, vof(v)),
    decreases dep, e, 1nat,
{
    reveal_with_fuel(rx, 1);
    reveal_with_fuel(rsrc, 1);
    reveal_with_fuel(rmean, 1);
    reveal_with_fuel(vof, 1);
    match e {
        Sx::List(ty, es) => {
            assert(to_ty(ty, tb, false) is Some && rxs(fs, tb, false, sc, es, 0) is Some);
            let u = to_ty(ty, tb, false)->Some_0;
            let ces = rxs(fs, tb, false, sc, es, 0)->Some_0;
            assert(c == Expr::List(u, ces));
            assert(rsrcs(fs, tb, fds, dep, sc, es, 0) is Some);
            let rs = rsrcs(fs, tb, fds, dep, sc, es, 0)->Some_0;
            assert(r == RExpr::List(rs));
            assert(rmeans(renv, rs, 0) is Some);
            let vs = rmeans(renv, rs, 0)->Some_0;
            assert(v == RVal::List(vs));
            rxs_at(fs, tb, fds, dep, sc, es, 0, ces);
            rsrcs_at(fs, tb, fds, dep, sc, es, 0, rs);
            rmeans_at(renv, rs, 0, vs);
            assert forall|j: nat| j < es.len() implies rx(fs, tb, false, sc, #[trigger] es[j as int]) == Some(ces[j as int]) by {
                assert(rx(fs, tb, false, sc, es[(0 + j) as int]) == Some(ces[j as int]));
            }
            assert forall|j: nat| j < es.len() implies rsrc(fs, tb, fds, dep, sc, #[trigger] es[j as int]) == Some(rs[j as int]) by {
                assert(rsrc(fs, tb, fds, dep, sc, es[(0 + j) as int]) == Some(rs[j as int]));
            }
            assert forall|j: nat| j < es.len() implies rmean(renv, #[trigger] rs[j as int]) == Some(vs[j as int]) by {
                assert(rmean(renv, rs[(0 + j) as int]) == Some(vs[j as int]));
            }
            list_elts(p, fs, tb, fds, dep, sc, es, cenv, renv, ces, rs, vs, 0);
            args_of(p, cenv, ces, vs, 0);
            bs_list(p, cenv, u, ces, vofs(vs, 0));
        },
        _ => {},
    }
}

/// str の腕：文字列は文字の式の列（str_exprs）に評価される。各文字は bs_leaf で値を持つ。
proof fn str_arm(p: Prog, fs: Seq<Seq<char>>, tb: Seq<(Seq<char>, Option<Ty>, Seq<Seq<char>>, Option<Ty>)>, fds: Seq<Sd>, dep: nat, sc: Seq<Seq<char>>, e: Sx, cenv: Map<nat, Val>, renv: Map<nat, RVal>, c: Expr, r: RExpr, v: RVal)
    requires
        funcs_ok(p, fs, tb, fds),
        envrel(cenv, renv),
        e is Str,
        rx(fs, tb, false, sc, e) == Some(c),
        rsrc(fs, tb, fds, dep, sc, e) == Some(r),
        rmean(renv, r) == Some(v),
    ensures
        evals_to(p, cenv, c, vof(v)),
    decreases dep, e, 1nat,
{
    reveal_with_fuel(rx, 1);
    reveal_with_fuel(rsrc, 1);
    reveal_with_fuel(rmean, 1);
    reveal_with_fuel(vof, 1);
    match e {
        Sx::Str(w) => {
            assert(c == Expr::List(Ty::Char, str_exprs(w)));
            assert(r == RExpr::List(rstrs(w)));
            assert(rmeans(renv, rstrs(w), 0) is Some);
            let vs = rmeans(renv, rstrs(w), 0)->Some_0;
            assert(v == RVal::List(vs));
            rmeans_at(renv, rstrs(w), 0, vs);
            assert(vs.len() == w.len());
            assert forall|j: nat| j < vs.len() implies vs[j as int] == RVal::Char(w[j as int] as u32 as int) by {
                assert(rstrs(w)[j as int] == RExpr::Char(w[j as int] as u32 as int));
                assert(rmean(renv, rstrs(w)[(0 + j) as int]) == Some(vs[j as int]));
            }
            assert forall|j: nat| j < str_exprs(w).len() implies evals_to(p, cenv, #[trigger] str_exprs(w)[j as int], vof(vs[j as int])) by {
                assert(str_exprs(w)[j as int] == Expr::Char(w[j as int] as u32 as int));
                bs_leaf(p, cenv, Expr::Char(w[j as int] as u32 as int));
            }
            args_of(p, cenv, str_exprs(w), vs, 0);
            bs_list(p, cenv, Ty::Char, str_exprs(w), vofs(vs, 0));
        },
        _ => {},
    }
}

/// vofs の長さ：位置 i から先の要素の数。
proof fn vofs_len(vs: Seq<RVal>, i: nat)
    requires
        i <= vs.len(),
    ensures
        vofs(vs, i).len() as int == vs.len() as int - i as int,
    decreases vs.len() - i,
{
    reveal_with_fuel(vofs, 1);
    if i < vs.len() {
        vofs_len(vs, i + 1);
    }
}

/// vofs の k 番目（位置 i から数えて k - i 番目）は、源の要素 k の写し。
proof fn vofs_index(vs: Seq<RVal>, i: nat, k: nat)
    requires
        i <= k,
        k < vs.len(),
    ensures
        vofs(vs, i)[(k - i) as int] == vof(vs[k as int]),
    decreases vs.len() - i,
{
    reveal_with_fuel(vofs, 1);
    assert(vofs(vs, i) == seq![vof(vs[i as int])] + vofs(vs, i + 1));
    if i < k {
        vofs_index(vs, i + 1, k);
        vofs_len(vs, i + 1);
        assert(vofs(vs, i)[(k - i) as int] == vofs(vs, i + 1)[(k - i - 1) as int]);
    } else {
        assert(vofs(vs, i)[0] == vof(vs[i as int]));
    }
}

/// 位置 0 からの vofs の k 番目は、源の要素 k の写し。
proof fn vofs_at(vs: Seq<RVal>, k: nat)
    requires
        k < vs.len(),
    ensures
        vofs(vs, 0)[k as int] == vof(vs[k as int]),
{
    vofs_index(vs, 0, k);
}

/// 写しの逆：rof が源の値 w を返すなら、w の写しは核の値 v に等しい。
proof fn rof_vof(v: Val, w: RVal)
    requires
        rof(v) == Some(w),
    ensures
        vof(w) == v,
    decreases v, 0nat,
{
    reveal_with_fuel(rof, 1);
    reveal_with_fuel(vof, 1);
    match v {
        Val::Some(a) => {
            assert(rof(*a) is Some);
            let wa = rof(*a)->Some_0;
            assert(w == RVal::Some(Box::new(wa)));
            rof_vof(*a, wa);
        },
        Val::Pair(a, b) => {
            assert(rof(*a) is Some && rof(*b) is Some);
            let wa = rof(*a)->Some_0;
            let wb = rof(*b)->Some_0;
            assert(w == RVal::Pair(Box::new(wa), Box::new(wb)));
            rof_vof(*a, wa);
            rof_vof(*b, wb);
        },
        Val::List(vs) => {
            assert(rofs(vs, 0) is Some);
            let ws = rofs(vs, 0)->Some_0;
            assert(w == RVal::List(ws));
            rofs_elts(vs, 0, ws);
            vofs_eq(ws, vs);
        },
        _ => {},
    }
}

/// 核の値の列の写し：rofs が源の値の列 ws を返すなら、ws は残りの要素と同じ長さで、要素 k の写しは vs[i + k] に等しい。
proof fn rofs_elts(vs: Seq<Val>, i: nat, ws: Seq<RVal>)
    requires
        i <= vs.len(),
        rofs(vs, i) == Some(ws),
    ensures
        ws.len() as int == vs.len() as int - i as int,
        forall|k: nat| k < ws.len() ==> vof(#[trigger] ws[k as int]) == vs[(i + k) as int],
    decreases vs, vs.len() - i,
{
    reveal_with_fuel(rofs, 1);
    if i >= vs.len() {
        assert(ws == Seq::<RVal>::empty());
    } else {
        assert(rof(vs[i as int]) is Some && rofs(vs, i + 1) is Some);
        let w = rof(vs[i as int])->Some_0;
        let ws1 = rofs(vs, i + 1)->Some_0;
        assert(ws == seq![w] + ws1);
        rof_vof(vs[i as int], w);
        rofs_elts(vs, i + 1, ws1);
        assert forall|k: nat| k < ws.len() implies vof(#[trigger] ws[k as int]) == vs[(i + k) as int] by {
            if k == 0 {
                assert(ws[0] == w);
            } else {
                assert(ws[k as int] == ws1[(k - 1) as int]);
            }
        }
    }
}

/// 写しの列：要素ごとに写しが一致する源の値の列は、vofs で核の値の列に戻る。
proof fn vofs_eq(ws: Seq<RVal>, vs: Seq<Val>)
    requires
        ws.len() == vs.len(),
        forall|k: nat| k < ws.len() ==> vof(#[trigger] ws[k as int]) == vs[k as int],
    ensures
        vofs(ws, 0) == vs,
{
    vofs_len(ws, 0);
    assert forall|k: int| 0 <= k < vs.len() implies vofs(ws, 0)[k] == vs[k] by {
        vofs_at(ws, k as nat);
    }
    assert(vofs(ws, 0) =~= vs);
}

/// raccs の性質：列の長さは残りの要素の数より一つ多く、初めは a。段 k の累積は、要素 j + k で本体を評価した値。
proof fn raccs_props(env: Map<nat, RVal>, acc: nat, item: nat, body: RExpr, items: Seq<RVal>, j: nat, a: RVal, accs: Seq<RVal>)
    requires
        j <= items.len(),
        raccs(env, acc, item, body, items, j, a) == Some(accs),
    ensures
        accs.len() as int == items.len() as int - j as int + 1,
        accs[0] == a,
        forall|k: nat| (k as int) < (items.len() as int - j as int) ==> rmean(env.insert(acc, #[trigger] accs[k as int]).insert(item, items[(j + k) as int]), body) == Some(accs[(k + 1) as int]),
    decreases body, items.len() - j,
{
    reveal_with_fuel(raccs, 1);
    if j < items.len() {
        let v = rmean(env.insert(acc, a).insert(item, items[j as int]), body)->Some_0;
        assert(rmean(env.insert(acc, a).insert(item, items[j as int]), body) == Some(v));
        let rest = raccs(env, acc, item, body, items, j + 1, v)->Some_0;
        assert(accs == seq![a] + rest);
        raccs_props(env, acc, item, body, items, j + 1, v, rest);
        assert(rest[0] == v);
        assert forall|k: nat| (k as int) < (items.len() as int - j as int) implies rmean(env.insert(acc, #[trigger] accs[k as int]).insert(item, items[(j + k) as int]), body) == Some(accs[(k + 1) as int]) by {
            if k == 0 {
                assert(accs[0] == a);
                assert(accs[1] == rest[0]);
            } else {
                assert(accs[k as int] == rest[(k - 1) as int]);
                assert(accs[(k + 1) as int] == rest[k as int]);
                assert(rmean(env.insert(acc, rest[(k - 1) as int]).insert(item, items[((j + 1) + (k - 1)) as int]), body) == Some(rest[k as int]));
            }
        }
    } else {
        assert(accs == seq![a]);
    }
}

/// Fold の腕の名前の位置：累積と要素の名前は sc.len() と sc.len() + 1（n と違う）。列、初期値、本体は n を参照も束縛もしない。
proof fn absent_at_fold(fs: Seq<Seq<char>>, tb: Seq<(Seq<char>, Option<Ty>, Seq<Seq<char>>, Option<Ty>)>, fds: Seq<Sd>, dep: nat, t: Seq<Seq<char>>, n: nat, e: Sx, c: Expr)
    requires
        n < t.len(),
        t[n as int] == Seq::<char>::empty(),
        e is Fold,
        rx(fs, tb, false, t, e) == Some(c),
        rsrc(fs, tb, fds, dep, t, e) is Some,
    ensures
        absent(n, c),
    decreases dep, e, 0nat,
{
    reveal_with_fuel(rx, 1);
    reveal_with_fuel(rsrc, 1);
    reveal_with_fuel(absent, 1);
    match e {
        Sx::Fold(l, i, a, x, b) => {
            assert(a != x && idx(t, a, 0) is None && idx(t, x, 0) is None);
            assert(rx(fs, tb, false, t, *l) is Some && rx(fs, tb, false, t, *i) is Some && rx(fs, tb, false, t.push(a).push(x), *b) is Some);
            let cl = rx(fs, tb, false, t, *l)->Some_0;
            let ci = rx(fs, tb, false, t, *i)->Some_0;
            let cb = rx(fs, tb, false, t.push(a).push(x), *b)->Some_0;
            assert(c == Expr::Fold(Box::new(cl), Box::new(ci), t.len(), t.len() + 1, Box::new(cb)));
            assert(rsrc(fs, tb, fds, dep, t, *l) is Some && rsrc(fs, tb, fds, dep, t, *i) is Some && rsrc(fs, tb, fds, dep, t.push(a).push(x), *b) is Some);
            assert(t.push(a)[n as int] == t[n as int]);
            assert(t.push(a).push(x)[n as int] == t[n as int]);
            absent_at(fs, tb, fds, dep, t, n, *l, cl);
            absent_at(fs, tb, fds, dep, t, n, *i, ci);
            absent_at(fs, tb, fds, dep, t.push(a).push(x), n, *b, cb);
            assert(t.len() != n);
            assert(t.len() + 1 != n);
        },
        _ => {},
    }
}

/// fold の腕：列と初期値の定理（resolve_sound）、累積の列（raccs）の各段の本体の定理（resolve_sound を段に当てる）、
/// fold_from_each と bs_fold。累積と要素の名前は sc.len() と sc.len() + 1（rx と同じ番号）。
proof fn fold_arm(p: Prog, fs: Seq<Seq<char>>, tb: Seq<(Seq<char>, Option<Ty>, Seq<Seq<char>>, Option<Ty>)>, fds: Seq<Sd>, dep: nat, sc: Seq<Seq<char>>, e: Sx, cenv: Map<nat, Val>, renv: Map<nat, RVal>, c: Expr, r: RExpr, v: RVal)
    requires
        funcs_ok(p, fs, tb, fds),
        envrel(cenv, renv),
        e is Fold,
        renv_below(renv, sc),
        rx(fs, tb, false, sc, e) == Some(c),
        rsrc(fs, tb, fds, dep, sc, e) == Some(r),
        rmean(renv, r) == Some(v),
    ensures
        evals_to(p, cenv, c, vof(v)),
    decreases dep, e, 1nat,
{
    reveal_with_fuel(rx, 1);
    reveal_with_fuel(rsrc, 1);
    reveal_with_fuel(rmean, 1);
    reveal_with_fuel(vof, 1);
    match e {
        Sx::Fold(l, i, a, x, b) => {
            assert(a != x && idx(sc, a, 0) is None && idx(sc, x, 0) is None);
            assert(rx(fs, tb, false, sc, *l) is Some && rx(fs, tb, false, sc, *i) is Some && rx(fs, tb, false, sc.push(a).push(x), *b) is Some);
            let cl = rx(fs, tb, false, sc, *l)->Some_0;
            let ci = rx(fs, tb, false, sc, *i)->Some_0;
            let cb = rx(fs, tb, false, sc.push(a).push(x), *b)->Some_0;
            assert(c == Expr::Fold(Box::new(cl), Box::new(ci), sc.len(), sc.len() + 1, Box::new(cb)));
            assert(rsrc(fs, tb, fds, dep, sc, *l) is Some && rsrc(fs, tb, fds, dep, sc, *i) is Some && rsrc(fs, tb, fds, dep, sc.push(a).push(x), *b) is Some);
            let rl = rsrc(fs, tb, fds, dep, sc, *l)->Some_0;
            let ri = rsrc(fs, tb, fds, dep, sc, *i)->Some_0;
            let rb = rsrc(fs, tb, fds, dep, sc.push(a).push(x), *b)->Some_0;
            assert(r == RExpr::Fold(Box::new(rl), Box::new(ri), sc.len(), sc.len() + 1, Box::new(rb)));
            assert(rmean(renv, rl) is Some);
            let ml = rmean(renv, rl)->Some_0;
            assert(ml is List);
            let items = ml->List_0;
            assert(rmean(renv, ri) is Some);
            let init = rmean(renv, ri)->Some_0;
            assert(raccs(renv, sc.len(), sc.len() + 1, rb, items, 0, init) is Some);
            let accs = raccs(renv, sc.len(), sc.len() + 1, rb, items, 0, init)->Some_0;
            assert(v == accs[(accs.len() - 1) as int]);
            resolve_sound(p, fs, tb, fds, dep, sc, *l, cenv, renv, cl, rl, ml);
            resolve_sound(p, fs, tb, fds, dep, sc, *i, cenv, renv, ci, ri, init);
            raccs_props(renv, sc.len(), sc.len() + 1, rb, items, 0, init, accs);
            assert forall|k: nat| (k as int) < items.len() implies evals_to(p, cenv.insert(sc.len(), vof(accs[k as int])).insert(sc.len() + 1, vof(items[k as int])), cb, vof(accs[(k + 1) as int])) by {
                envrel_ins(cenv, renv, sc.len(), accs[k as int]);
                envrel_ins(cenv.insert(sc.len(), vof(accs[k as int])), renv.insert(sc.len(), accs[k as int]), sc.len() + 1, items[k as int]);
                below_push(renv, sc, a, sc.len(), accs[k as int]);
                below_push(renv.insert(sc.len(), accs[k as int]), sc.push(a), x, sc.len() + 1, items[k as int]);
                assert(rmean(renv.insert(sc.len(), accs[k as int]).insert(sc.len() + 1, items[k as int]), rb) == Some(accs[(k + 1) as int]));
                resolve_sound(p, fs, tb, fds, dep, sc.push(a).push(x), *b, cenv.insert(sc.len(), vof(accs[k as int])).insert(sc.len() + 1, vof(items[k as int])), renv.insert(sc.len(), accs[k as int]).insert(sc.len() + 1, items[k as int]), cb, rb, accs[(k + 1) as int]);
            }
            vofs_len(accs, 0);
            vofs_len(items, 0);
            assert(vofs(accs, 0).len() == items.len() + 1);
            assert forall|k: int| 0 <= k < vofs(items, 0).len() implies evals_to(p, cenv.insert(sc.len(), vofs(accs, 0)[k]).insert(sc.len() + 1, vofs(items, 0)[k]), cb, vofs(accs, 0)[k + 1]) by {
                vofs_at(accs, k as nat);
                vofs_at(accs, (k + 1) as nat);
                vofs_at(items, k as nat);
                assert(evals_to(p, cenv.insert(sc.len(), vof(accs[k])).insert(sc.len() + 1, vof(items[k])), cb, vof(accs[k + 1])));
            }
            fold_from_each(p, cenv, sc.len(), sc.len() + 1, cb, vofs(items, 0), vofs(accs, 0), 0);
            vofs_at(accs, 0);
            vofs_at(accs, items.len());
            assert(accs[items.len() as int] == v);
            assert(vofs(accs, 0)[0] == vof(init));
            assert(vof(ml) == Val::List(vofs(items, 0)));
            bs_fold(p, cenv, cl, ci, sc.len(), sc.len() + 1, cb, vofs(items, 0), vof(init), vof(v));
        },
        _ => {},
    }
}

/// 組込みの名前の位置：引数の式（rx の列）は位置 n を参照も束縛もしない（List の腕と同じ）。
proof fn absent_at_builtin(fs: Seq<Seq<char>>, tb: Seq<(Seq<char>, Option<Ty>, Seq<Seq<char>>, Option<Ty>)>, fds: Seq<Sd>, dep: nat, t: Seq<Seq<char>>, n: nat, e: Sx, c: Expr)
    requires
        n < t.len(),
        t[n as int] == Seq::<char>::empty(),
        e is Builtin,
        rx(fs, tb, false, t, e) == Some(c),
        rsrc(fs, tb, fds, dep, t, e) is Some,
    ensures
        absent(n, c),
    decreases dep, e, 0nat,
{
    reveal_with_fuel(rx, 1);
    reveal_with_fuel(rsrc, 1);
    reveal_with_fuel(absent, 1);
    match e {
        Sx::Builtin(b, es) => {
            assert(rxs(fs, tb, false, t, es, 0) is Some);
            let ces = rxs(fs, tb, false, t, es, 0)->Some_0;
            assert(c == Expr::Builtin(b, ces));
            assert(rsrcs(fs, tb, fds, dep, t, es, 0) is Some);
            let rs = rsrcs(fs, tb, fds, dep, t, es, 0)->Some_0;
            rxs_at(fs, tb, fds, dep, t, es, 0, ces);
            rsrcs_at(fs, tb, fds, dep, t, es, 0, rs);
            assert forall|j: nat| j < es.len() implies rx(fs, tb, false, t, #[trigger] es[j as int]) == Some(ces[j as int]) by {
                assert(rx(fs, tb, false, t, es[(0 + j) as int]) == Some(ces[j as int]));
            }
            assert forall|j: nat| j < es.len() implies rsrc(fs, tb, fds, dep, t, #[trigger] es[j as int]) is Some by {
                assert(rsrc(fs, tb, fds, dep, t, es[(0 + j) as int]) == Some(rs[j as int]));
            }
            absent_at_elts(fs, tb, fds, dep, t, n, es, ces, 0);
            absent_all(n, ces, 0);
        },
        _ => {},
    }
}

/// 組込みの腕：引数の式の定理（list_elts と args_of）と bs_builtin。核の組込みの結果 w は rof で源の値 v に写り、その写しは w に等しい（rof_vof）。
proof fn builtin_arm(p: Prog, fs: Seq<Seq<char>>, tb: Seq<(Seq<char>, Option<Ty>, Seq<Seq<char>>, Option<Ty>)>, fds: Seq<Sd>, dep: nat, sc: Seq<Seq<char>>, e: Sx, cenv: Map<nat, Val>, renv: Map<nat, RVal>, c: Expr, r: RExpr, v: RVal)
    requires
        funcs_ok(p, fs, tb, fds),
        envrel(cenv, renv),
        e is Builtin,
        renv_below(renv, sc),
        rx(fs, tb, false, sc, e) == Some(c),
        rsrc(fs, tb, fds, dep, sc, e) == Some(r),
        rmean(renv, r) == Some(v),
    ensures
        evals_to(p, cenv, c, vof(v)),
    decreases dep, e, 1nat,
{
    reveal_with_fuel(rx, 1);
    reveal_with_fuel(rsrc, 1);
    reveal_with_fuel(rmean, 1);
    match e {
        Sx::Builtin(b, es) => {
            assert(rxs(fs, tb, false, sc, es, 0) is Some);
            let ces = rxs(fs, tb, false, sc, es, 0)->Some_0;
            assert(c == Expr::Builtin(b, ces));
            assert(rsrcs(fs, tb, fds, dep, sc, es, 0) is Some);
            let rs = rsrcs(fs, tb, fds, dep, sc, es, 0)->Some_0;
            assert(r == RExpr::Builtin(b, rs));
            assert(rmeans(renv, rs, 0) is Some);
            let vs = rmeans(renv, rs, 0)->Some_0;
            assert(rapply(b, vs) == Some(v));
            assert(apply(b, vofs(vs, 0)) is Done);
            let w = apply(b, vofs(vs, 0))->Done_0;
            assert(rof(w) == Some(v));
            rof_vof(w, v);
            rxs_at(fs, tb, fds, dep, sc, es, 0, ces);
            rsrcs_at(fs, tb, fds, dep, sc, es, 0, rs);
            rmeans_at(renv, rs, 0, vs);
            assert forall|j: nat| j < es.len() implies rx(fs, tb, false, sc, #[trigger] es[j as int]) == Some(ces[j as int]) by {
                assert(rx(fs, tb, false, sc, es[(0 + j) as int]) == Some(ces[j as int]));
            }
            assert forall|j: nat| j < es.len() implies rsrc(fs, tb, fds, dep, sc, #[trigger] es[j as int]) == Some(rs[j as int]) by {
                assert(rsrc(fs, tb, fds, dep, sc, es[(0 + j) as int]) == Some(rs[j as int]));
            }
            assert forall|j: nat| j < es.len() implies rmean(renv, #[trigger] rs[j as int]) == Some(vs[j as int]) by {
                assert(rmean(renv, rs[(0 + j) as int]) == Some(vs[j as int]));
            }
            list_elts(p, fs, tb, fds, dep, sc, es, cenv, renv, ces, rs, vs, 0);
            args_of(p, cenv, ces, vs, 0);
            bs_builtin(p, cenv, b, ces, vofs(vs, 0), w);
            assert(vof(v) == w);
        },
        _ => {},
    }
}

/// 呼出しの腕：引数は list_elts と args_of で評価し、呼出し先の本体は深さを一つ減らした resolve_sound で、bs_call でつなぐ。
proof fn call_arm(p: Prog, fs: Seq<Seq<char>>, tb: Seq<(Seq<char>, Option<Ty>, Seq<Seq<char>>, Option<Ty>)>, fds: Seq<Sd>, dep: nat, sc: Seq<Seq<char>>, e: Sx, cenv: Map<nat, Val>, renv: Map<nat, RVal>, c: Expr, r: RExpr, v: RVal)
    requires
        funcs_ok(p, fs, tb, fds),
        envrel(cenv, renv),
        e is Call,
        idx(fs, e->Call_0, 0) is Some,
        renv_below(renv, sc),
        rx(fs, tb, false, sc, e) == Some(c),
        rsrc(fs, tb, fds, dep, sc, e) == Some(r),
        rmean(renv, r) == Some(v),
    ensures
        evals_to(p, cenv, c, vof(v)),
    decreases dep, e, 1nat,
{
    reveal_with_fuel(rx, 1);
    reveal_with_fuel(rsrc, 1);
    reveal_with_fuel(rmean, 1);
    match e {
        Sx::Call(f, es) => {
            assert(idx(fs, f, 0) is Some && rxs(fs, tb, false, sc, es, 0) is Some);
            let g = idx(fs, f, 0)->Some_0;
            let ces = rxs(fs, tb, false, sc, es, 0)->Some_0;
            assert(c == Expr::Call(g, ces));
            assert(dep != 0 && g < fds.len());
            assert(fds[g as int] is Fn);
            match fds[g as int] {
                Sd::Fn(_, ps, _, b) => {
                    assert(rsrc(fs, tb, fds, (dep - 1) as nat, pnames(ps), b) is Some && rsrcs(fs, tb, fds, dep, sc, es, 0) is Some);
                    let rb = rsrc(fs, tb, fds, (dep - 1) as nat, pnames(ps), b)->Some_0;
                    let rs = rsrcs(fs, tb, fds, dep, sc, es, 0)->Some_0;
                    assert(r == RExpr::Call(Box::new(rb), ps.len(), rs));
                    assert(rmeans(renv, rs, 0) is Some);
                    let vs = rmeans(renv, rs, 0)->Some_0;
                    assert(vs.len() == ps.len());
                    assert(rmean(rbind(vs, ps.len()), rb) == Some(v));
                    assert(pnames(ps).len() == ps.len());
                    assert(renv_below(rbind(vs, ps.len()), pnames(ps))) by {
                        rbind_below(vs, ps.len());
                    }
                    funcs_at(p, fs, tb, fds, g);
                    assert(g < p.funcs.len());
                    assert(p.funcs[g as int].params == rparams(ps, tb, false));
                    assert(rx(fs, tb, false, pnames(ps), b) == Some(p.funcs[g as int].body));
                    assert(p.funcs[g as int].params.len() == ps.len());
                    rxs_at(fs, tb, fds, dep, sc, es, 0, ces);
                    rsrcs_at(fs, tb, fds, dep, sc, es, 0, rs);
                    rmeans_at(renv, rs, 0, vs);
                    assert forall|j: nat| j < es.len() implies rx(fs, tb, false, sc, #[trigger] es[j as int]) == Some(ces[j as int]) by {
                        assert(rx(fs, tb, false, sc, es[(0 + j) as int]) == Some(ces[j as int]));
                    }
                    assert forall|j: nat| j < es.len() implies rsrc(fs, tb, fds, dep, sc, #[trigger] es[j as int]) == Some(rs[j as int]) by {
                        assert(rsrc(fs, tb, fds, dep, sc, es[(0 + j) as int]) == Some(rs[j as int]));
                    }
                    assert forall|j: nat| j < es.len() implies rmean(renv, #[trigger] rs[j as int]) == Some(vs[j as int]) by {
                        assert(rmean(renv, rs[(0 + j) as int]) == Some(vs[j as int]));
                    }
                    list_elts(p, fs, tb, fds, dep, sc, es, cenv, renv, ces, rs, vs, 0);
                    args_of(p, cenv, ces, vs, 0);
                    assert forall|i: nat| i < ps.len() implies p.funcs[g as int].params[i as int].0 == i by {
                        assert(p.funcs[g as int].params == rparams(ps, tb, false));
                    }
                    vofs_len(vs, 0);
                    assert(vofs(vs, 0).len() == ps.len());
                    envrel_bind(p.funcs[g as int].params, vs, ps.len());
                    resolve_sound(p, fs, tb, fds, (dep - 1) as nat, pnames(ps), b, bind(p.funcs[g as int].params, vofs(vs, 0), ps.len()), rbind(vs, ps.len()), p.funcs[g as int].body, rb, v);
                    bs_call(p, cenv, g, ces, vofs(vs, 0), vof(v));
                },
                _ => {},
            }
        },
        _ => {},
    }
}

/// 呼出しの腕の名前の位置：引数の式は位置 n を参照も束縛もしない（核の呼出しの本体は引数だけを見る）。
proof fn absent_at_call(fs: Seq<Seq<char>>, tb: Seq<(Seq<char>, Option<Ty>, Seq<Seq<char>>, Option<Ty>)>, fds: Seq<Sd>, dep: nat, t: Seq<Seq<char>>, n: nat, e: Sx, c: Expr)
    requires
        n < t.len(),
        t[n as int] == Seq::<char>::empty(),
        e is Call,
        rx(fs, tb, false, t, e) == Some(c),
        rsrc(fs, tb, fds, dep, t, e) is Some,
    ensures
        absent(n, c),
    decreases dep, e, 0nat,
{
    reveal_with_fuel(rx, 1);
    reveal_with_fuel(rsrc, 1);
    reveal_with_fuel(absent, 1);
    match e {
        Sx::Call(f, es) => {
            if idx(fs, f, 0) is None {
                // 関数でない名前への呼出しは構築子（字段の式は位置 n を参照も束縛もしない）。
                assert(rxs(fs, tb, false, t, es, 0) is Some);
                let ces = rxs(fs, tb, false, t, es, 0)->Some_0;
                assert(rctor(tb, false, f, ces) == Some(c));
                assert(rsrcs(fs, tb, fds, dep, t, es, 0) is Some) by {
                    if rsrcs(fs, tb, fds, dep, t, es, 0) is None {
                        assert(rsrc(fs, tb, fds, dep, t, e) is None);
                    }
                }
                let rs = rsrcs(fs, tb, fds, dep, t, es, 0)->Some_0;
                rxs_at(fs, tb, fds, dep, t, es, 0, ces);
                rsrcs_at(fs, tb, fds, dep, t, es, 0, rs);
                assert forall|j: nat| j < es.len() implies rx(fs, tb, false, t, #[trigger] es[j as int]) == Some(ces[j as int]) by {
                    assert(rx(fs, tb, false, t, es[(0 + j) as int]) == Some(ces[j as int]));
                }
                assert forall|j: nat| j < es.len() implies rsrc(fs, tb, fds, dep, t, #[trigger] es[j as int]) is Some by {
                    assert(rsrc(fs, tb, fds, dep, t, es[(0 + j) as int]) == Some(rs[j as int]));
                }
                absent_at_elts(fs, tb, fds, dep, t, n, es, ces, 0);
                absent_all(n, ces, 0);
                absent_ctor(tb, n, f, ces, c);
            } else {
                assert(rxs(fs, tb, false, t, es, 0) is Some);
                let g = idx(fs, f, 0)->Some_0;
                let ces = rxs(fs, tb, false, t, es, 0)->Some_0;
                assert(c == Expr::Call(g, ces));
                assert(dep != 0 && g < fds.len());
                assert(fds[g as int] is Fn);
                match fds[g as int] {
                    Sd::Fn(_, ps, _, b) => {
                        assert(rsrcs(fs, tb, fds, dep, t, es, 0) is Some);
                        let rs = rsrcs(fs, tb, fds, dep, t, es, 0)->Some_0;
                        rxs_at(fs, tb, fds, dep, t, es, 0, ces);
                        rsrcs_at(fs, tb, fds, dep, t, es, 0, rs);
                        assert forall|j: nat| j < es.len() implies rx(fs, tb, false, t, #[trigger] es[j as int]) == Some(ces[j as int]) by {
                            assert(rx(fs, tb, false, t, es[(0 + j) as int]) == Some(ces[j as int]));
                        }
                        assert forall|j: nat| j < es.len() implies rsrc(fs, tb, fds, dep, t, #[trigger] es[j as int]) is Some by {
                            assert(rsrc(fs, tb, fds, dep, t, es[(0 + j) as int]) == Some(rs[j as int]));
                        }
                        absent_at_elts(fs, tb, fds, dep, t, n, es, ces, 0);
                        absent_all(n, ces, 0);
                    },
                    _ => {},
                }
            }
        },
        _ => {},
    }
}

/// some の腕：中の式の定理と bs_some。
proof fn some_arm(p: Prog, fs: Seq<Seq<char>>, tb: Seq<(Seq<char>, Option<Ty>, Seq<Seq<char>>, Option<Ty>)>, fds: Seq<Sd>, dep: nat, sc: Seq<Seq<char>>, e: Sx, cenv: Map<nat, Val>, renv: Map<nat, RVal>, c: Expr, r: RExpr, v: RVal)
    requires
        funcs_ok(p, fs, tb, fds),
        envrel(cenv, renv),
        e is Some,
        renv_below(renv, sc),
        rx(fs, tb, false, sc, e) == Some(c),
        rsrc(fs, tb, fds, dep, sc, e) == Some(r),
        rmean(renv, r) == Some(v),
    ensures
        evals_to(p, cenv, c, vof(v)),
    decreases dep, e, 1nat,
{
    reveal_with_fuel(rx, 2);
    reveal_with_fuel(rsrc, 2);
    reveal_with_fuel(rmean, 2);
    reveal_with_fuel(vof, 2);
    match e {
        Sx::Some(a) => {
            assert(rx(fs, tb, false, sc, *a) is Some);
            let x = rx(fs, tb, false, sc, *a)->Some_0;
            assert(c == Expr::Some(Box::new(x)));
            assert(rsrc(fs, tb, fds, dep, sc, *a) is Some);
            let ra = rsrc(fs, tb, fds, dep, sc, *a)->Some_0;
            assert(r == RExpr::Some(Box::new(ra)));
            assert(rmean(renv, ra) is Some);
            let va = rmean(renv, ra)->Some_0;
            assert(v == RVal::Some(Box::new(va)));
            resolve_sound(p, fs, tb, fds, dep, sc, *a, cenv, renv, x, ra, va);
            bs_some(p, cenv, x, vof(va));
        },
        _ => {},
    }
}

/// 参照の腕：下端（基）の定理と鎖の定理。
proof fn fld_arm(p: Prog, fs: Seq<Seq<char>>, tb: Seq<(Seq<char>, Option<Ty>, Seq<Seq<char>>, Option<Ty>)>, fds: Seq<Sd>, dep: nat, sc: Seq<Seq<char>>, e: Sx, cenv: Map<nat, Val>, renv: Map<nat, RVal>, c: Expr, r: RExpr, v: RVal)
    requires
        funcs_ok(p, fs, tb, fds),
        envrel(cenv, renv),
        e is Fld,
        renv_below(renv, sc),
        rx(fs, tb, false, sc, e) == Some(c),
        rsrc(fs, tb, fds, dep, sc, e) == Some(r),
        rmean(renv, r) == Some(v),
    ensures
        evals_to(p, cenv, c, vof(v)),
    decreases dep, e, 1nat,
{
    reveal_with_fuel(rx, 2);
    reveal_with_fuel(rsrc, 2);
    reveal_with_fuel(rmean, 2);
    reveal_with_fuel(vof, 2);
    match e {
        Sx::Fld(a, fls) => {
            assert(rx(fs, tb, false, sc, *a) is Some);
            let x = rx(fs, tb, false, sc, *a)->Some_0;
            assert(rsrc(fs, tb, fds, dep, sc, *a) is Some);
            let ra = rsrc(fs, tb, fds, dep, sc, *a)->Some_0;
            chain_inner(tb, fds, dep, renv, ra, fls, 0, r);
            let rv = rmean(renv, ra)->Some_0;
            assert(rmean(renv, ra) == Some(rv));
            resolve_sound(p, fs, tb, fds, dep, sc, *a, cenv, renv, x, ra, rv);
            chain_sound(p, cenv, tb, fds, dep, renv, ra, x, rv, fls, 0, r, c, v);
        },
        _ => {},
    }
}

/// 基なしの記録の腕（全部書いた構築）：字段の列の解決と、字段の定理（rec_none_arm）。
proof fn rec_none_top(p: Prog, fs: Seq<Seq<char>>, tb: Seq<(Seq<char>, Option<Ty>, Seq<Seq<char>>, Option<Ty>)>, fds: Seq<Sd>, dep: nat, sc: Seq<Seq<char>>, e: Sx, cenv: Map<nat, Val>, renv: Map<nat, RVal>, c: Expr, r: RExpr, v: RVal)
    requires
        funcs_ok(p, fs, tb, fds),
        envrel(cenv, renv),
        renv_below(renv, sc),
        e matches Sx::Rec(_, _, None),
        rx(fs, tb, false, sc, e) == Some(c),
        rsrc(fs, tb, fds, dep, sc, e) == Some(r),
        rmean(renv, r) == Some(v),
    ensures
        evals_to(p, cenv, c, vof(v)),
    decreases dep, e, 1nat,
{
    reveal_with_fuel(rx, 2);
    reveal_with_fuel(rsrc, 2);
    reveal_with_fuel(rmean, 2);
    reveal_with_fuel(vof, 2);
    reveal_with_fuel(rec_t, 2);
    reveal_with_fuel(rec_expr, 2);
    reveal_with_fuel(rsrc_ws, 2);
    match e {
        Sx::Rec(rn, fls, _) => {
            assert(idx(tnames(tb), rn, 0) is Some);
            let k = idx(tnames(tb), rn, 0)->Some_0;
            assert(tb[k as int].2.len() != 0);
            let decl = tb[k as int].2;
            let n = decl.len();
            assert(rsrc_ws(fs, tb, fds, dep, sc, decl, fls, 0) is Some);
            let ws = rsrc_ws(fs, tb, fds, dep, sc, decl, fls, 0)->Some_0;
            assert(rec_expr(fs, tb, false, sc, decl, fls, None) == Some(c));
            assert(rec_upd(fs, tb, false, sc, decl, fls, 0, none_upd(n)) is Some);
            let uf = rec_upd(fs, tb, false, sc, decl, fls, 0, none_upd(n))->Some_0;
            assert(rrecord(uf, None, sc.len()) == Ok(c));
            assert(r == RExpr::Rec(pdecl(n), ws, None));
            rec_none_arm(p, fs, tb, fds, dep, sc, decl, fls, cenv, renv, c, uf, ws, v);
        },
        _ => {},
    }
}

/// 基ありの記録の腕：基を解決して形を取り出し、基の定理と字段の定理を使う（rec_some_arm）。
/// 字段の写しは、基の解決の深さ（rx と同じ deep_rec）の scope で行う。
#[verifier::rlimit(100)]
proof fn rec_some_top(p: Prog, fs: Seq<Seq<char>>, tb: Seq<(Seq<char>, Option<Ty>, Seq<Seq<char>>, Option<Ty>)>, fds: Seq<Sd>, dep: nat, sc: Seq<Seq<char>>, e: Sx, cenv: Map<nat, Val>, renv: Map<nat, RVal>, c: Expr, r: RExpr, v: RVal)
    requires
        funcs_ok(p, fs, tb, fds),
        envrel(cenv, renv),
        renv_below(renv, sc),
        e matches Sx::Rec(_, _, Some(_)),
        rx(fs, tb, false, sc, e) == Some(c),
        rsrc(fs, tb, fds, dep, sc, e) == Some(r),
        rmean(renv, r) == Some(v),
    ensures
        evals_to(p, cenv, c, vof(v)),
    decreases dep, e, 1nat,
{
    reveal_with_fuel(rx, 2);
    reveal_with_fuel(rsrc, 2);
    reveal_with_fuel(rec_t, 2);
    reveal_with_fuel(rec_expr, 2);
    match e {
        Sx::Rec(rn, fls, Some(b)) => {
            assert(idx(tnames(tb), rn, 0) is Some);
            let k = idx(tnames(tb), rn, 0)->Some_0;
            assert(tb[k as int].2.len() != 0);
            let decl = tb[k as int].2;
            let n = decl.len();
            assert(rx(fs, tb, false, sc, *b) is Some);
            let bx = rx(fs, tb, false, sc, *b)->Some_0;
            assert(rsrc(fs, tb, fds, dep, sc, *b) is Some);
            let br = rsrc(fs, tb, fds, dep, sc, *b)->Some_0;
            let deep = deep_rec(Some(bx), decl, fls);
            assert(rsrc_ws(fs, tb, fds, dep, scope2(sc, deep), decl, fls, 0) is Some);
            let ws = rsrc_ws(fs, tb, fds, dep, scope2(sc, deep), decl, fls, 0)->Some_0;
            assert(rec_expr(fs, tb, false, sc, decl, fls, Some(bx)) == Some(c));
            assert(rec_upd(fs, tb, false, scope2(sc, deep), decl, fls, 0, none_upd(n)) is Some);
            let uf = rec_upd(fs, tb, false, scope2(sc, deep), decl, fls, 0, none_upd(n))->Some_0;
            assert(rrecord(uf, Some(bx), sc.len()) == Ok(c));
            assert(r == RExpr::Rec(pdecl(n), ws, Some(Box::new(br))));
            assert(e == Sx::Rec(rn, fls, Some(Box::new(*b))));
            rec_some_tail(p, fs, tb, fds, dep, sc, e, rn, fls, *b, cenv, renv, c, r, v, decl, bx, br, uf, ws);
        },
        _ => {},
    }
}

/// 基ありの記録の腕の後半：基の形を取り出し、基の定理（resolve_sound）と字段の定理（rec_some_arm）を使う。
proof fn rec_some_tail(p: Prog, fs: Seq<Seq<char>>, tb: Seq<(Seq<char>, Option<Ty>, Seq<Seq<char>>, Option<Ty>)>, fds: Seq<Sd>, dep: nat, sc: Seq<Seq<char>>, e: Sx, rn: Seq<char>, fls: Seq<(Seq<char>, Sx)>, bsx: Sx, cenv: Map<nat, Val>, renv: Map<nat, RVal>, c: Expr, r: RExpr, v: RVal, decl: Seq<Seq<char>>, bx: Expr, br: RExpr, uf: Seq<Option<Expr>>, ws: Seq<(nat, RExpr)>)
    requires
        funcs_ok(p, fs, tb, fds),
        envrel(cenv, renv),
        renv_below(renv, sc),
        e == Sx::Rec(rn, fls, Some(Box::new(bsx))),
        rx(fs, tb, false, sc, bsx) == Some(bx),
        rsrc(fs, tb, fds, dep, sc, bsx) == Some(br),
        decl.len() >= 1,
        rec_upd(fs, tb, false, scope2(sc, deep_rec(Some(bx), decl, fls)), decl, fls, 0, none_upd(decl.len())) == Some(uf),
        rrecord(uf, Some(bx), sc.len()) == Ok(c),
        rsrc_ws(fs, tb, fds, dep, scope2(sc, deep_rec(Some(bx), decl, fls)), decl, fls, 0) == Some(ws),
        r == RExpr::Rec(pdecl(decl.len()), ws, Some(Box::new(br))),
        rmean(renv, r) == Some(v),
    ensures
        evals_to(p, cenv, c, vof(v)),
    decreases dep, e, 0nat,
{
    match e {
        Sx::Rec(_, fls2, Some(b)) => {
            assert(*b == bsx);
            assert(fls2 == fls);
            let n = decl.len();
            base_split(fs, tb, fds, dep, sc, decl, fls, bx, c, renv, ws, br, uf, v);
            let bs = choose|bs: Seq<RVal>| rmean(renv, br) == Some(RVal::Rec(bs)) && bs.len() == n;
            resolve_sound(p, fs, tb, fds, dep, sc, *b, cenv, renv, bx, br, RVal::Rec(bs));
            rec_some_arm(p, fs, tb, fds, dep, sc, decl, fls2, cenv, renv, bx, br, bs, c, uf, ws, v);
        },
        _ => {},
    }
}

/// 字段のない構築子の名前（局所の名前でない変数）の腕：rctor は字段のない構築子の値を作り、ctor_sound でその値に評価される。
/// 変数の腕（局所の名前）と振り分けるため、名前は局所の scope に無いことを仮定する。
proof fn ctor_var_arm(p: Prog, fs: Seq<Seq<char>>, tb: Seq<(Seq<char>, Option<Ty>, Seq<Seq<char>>, Option<Ty>)>, fds: Seq<Sd>, dep: nat, sc: Seq<Seq<char>>, e: Sx, cenv: Map<nat, Val>, renv: Map<nat, RVal>, c: Expr, r: RExpr, v: RVal)
    requires
        e is Var,
        idx(sc, e->Var_0, 0) is None,
        rx(fs, tb, false, sc, e) == Some(c),
        rsrc(fs, tb, fds, dep, sc, e) == Some(r),
        rmean(renv, r) == Some(v),
    ensures
        evals_to(p, cenv, c, vof(v)),
{
    reveal_with_fuel(rx, 1);
    reveal_with_fuel(rsrc, 1);
    reveal_with_fuel(rmean, 1);
    reveal_with_fuel(rmeans, 1);
    reveal_with_fuel(vof, 1);
    match e {
        Sx::Var(x) => {
            assert(rctor(tb, false, x, Seq::empty()) == Some(c));
            assert(rsrc_ctor(tb, x, Seq::empty()) == Some(r));
            let ikm = rsrc_ctor_inv(tb, x, Seq::empty(), r);
            assert(vlook(tb, x) == Some((ikm.0, ikm.1, Seq::<Expr>::empty().len())));
            assert(r == RExpr::Ctor(ikm.1, tb[ikm.0 as int].2.len(), Seq::<RExpr>::empty()));
            assert(rmeans(renv, Seq::<RExpr>::empty(), 0) == Some(Seq::<RVal>::empty()));
            assert(rmean(renv, r) == Some(RVal::Sum(ikm.1, tb[ikm.0 as int].2.len(), Seq::<RVal>::empty())));
            assert(v == RVal::Sum(ikm.1, tb[ikm.0 as int].2.len(), Seq::<RVal>::empty()));
            assert(fields_to(p, cenv, Seq::<Expr>::empty(), Seq::<Val>::empty()));
            ctor_sound(p, cenv, tb, x, Seq::empty(), Seq::empty(), ikm.0, ikm.1, c);
            assert(vof(v) == vsum_from(ikm.1, tb[ikm.0 as int].2.len(), 0, Val::Unit));
        },
        _ => {},
    }
}

/// 字段のある構築子への呼出しの腕：字段の式は list_elts で値に評価し、構築子の値は ctor_sound でその値に評価される。
#[verifier::rlimit(50)]
proof fn ctor_call_arm(p: Prog, fs: Seq<Seq<char>>, tb: Seq<(Seq<char>, Option<Ty>, Seq<Seq<char>>, Option<Ty>)>, fds: Seq<Sd>, dep: nat, sc: Seq<Seq<char>>, e: Sx, cenv: Map<nat, Val>, renv: Map<nat, RVal>, c: Expr, r: RExpr, v: RVal)
    requires
        funcs_ok(p, fs, tb, fds),
        envrel(cenv, renv),
        e is Call,
        idx(fs, e->Call_0, 0) is None,
        renv_below(renv, sc),
        rx(fs, tb, false, sc, e) == Some(c),
        rsrc(fs, tb, fds, dep, sc, e) == Some(r),
        rmean(renv, r) == Some(v),
    ensures
        evals_to(p, cenv, c, vof(v)),
    decreases dep, e, 1nat,
{
    reveal_with_fuel(rx, 1);
    reveal_with_fuel(rsrc, 1);
    reveal_with_fuel(rmean, 1);
    reveal_with_fuel(vof, 1);
    match e {
        Sx::Call(f, es) => {
            assert(idx(fs, f, 0) is None);
            assert(rxs(fs, tb, false, sc, es, 0) is Some);
            let ces = rxs(fs, tb, false, sc, es, 0)->Some_0;
            assert(rctor(tb, false, f, ces) == Some(c));
            assert(rsrcs(fs, tb, fds, dep, sc, es, 0) is Some);
            let rs = rsrcs(fs, tb, fds, dep, sc, es, 0)->Some_0;
            assert(rsrc_ctor(tb, f, rs) == Some(r));
            let ikm = rsrc_ctor_inv(tb, f, rs, r);
            assert(rmeans(renv, rs, 0) is Some);
            let vs = rmeans(renv, rs, 0)->Some_0;
            assert(v == RVal::Sum(ikm.1, tb[ikm.0 as int].2.len(), vs));
            rxs_at(fs, tb, fds, dep, sc, es, 0, ces);
            rsrcs_at(fs, tb, fds, dep, sc, es, 0, rs);
            rmeans_at(renv, rs, 0, vs);
            assert(ces.len() == es.len() && rs.len() == es.len() && vs.len() == es.len());
            assert(ces.len() == ikm.2);
            assert forall|j: nat| j < es.len() implies rx(fs, tb, false, sc, #[trigger] es[j as int]) == Some(ces[j as int]) by {
                assert(rx(fs, tb, false, sc, es[(0 + j) as int]) == Some(ces[j as int]));
            }
            assert forall|j: nat| j < es.len() implies rsrc(fs, tb, fds, dep, sc, #[trigger] es[j as int]) == Some(rs[j as int]) by {
                assert(rsrc(fs, tb, fds, dep, sc, es[(0 + j) as int]) == Some(rs[j as int]));
            }
            assert forall|j: nat| j < es.len() implies rmean(renv, #[trigger] rs[j as int]) == Some(vs[j as int]) by {
                assert(rmean(renv, rs[(0 + j) as int]) == Some(vs[j as int]));
            }
            list_elts(p, fs, tb, fds, dep, sc, es, cenv, renv, ces, rs, vs, 0);
            fields_of(p, cenv, ces, vs);
            assert(vlook(tb, f) == Some((ikm.0, ikm.1, ces.len())));
            ctor_sound(p, cenv, tb, f, ces, vofs(vs, 0), ikm.0, ikm.1, c);
            vof_sum(ikm.1, tb[ikm.0 as int].2.len(), vs);
        },
        _ => {},
    }
}

/// `_` だけの match の本体（any_top）が c を返すなら、枝の本体は解決でき、c はその let の形である。
proof fn any_top_let(fs: Seq<Seq<char>>, tb: Seq<(Seq<char>, Option<Ty>, Seq<Seq<char>>, Option<Ty>)>, tagged: bool, sc: Seq<Seq<char>>, arms: Seq<(Spat, Sx)>, rm: Expr, c: Expr)
    requires
        any_top(fs, tb, tagged, sc, arms, rm) == Some(c),
    ensures
        arms.len() == 1,
        rx(fs, tb, tagged, sc.push(Seq::empty()), arms[0].1) is Some,
        c == Expr::Let(sc.len(), Box::new(rm), Box::new(rx(fs, tb, tagged, sc.push(Seq::empty()), arms[0].1)->Some_0)),
{
    reveal_with_fuel(any_top, 1);
}

/// `_` だけの直和型の match の腕：被験式を let で位置 sc.len() に束縛し、`_` の枝の本体を空の名前を足した scope で解決する（let の腕と同じ）。
#[verifier::rlimit(50)]
proof fn sum_any_arm(p: Prog, fs: Seq<Seq<char>>, tb: Seq<(Seq<char>, Option<Ty>, Seq<Seq<char>>, Option<Ty>)>, fds: Seq<Sd>, dep: nat, sc: Seq<Seq<char>>, e: Sx, cenv: Map<nat, Val>, renv: Map<nat, RVal>, c: Expr, r: RExpr, v: RVal)
    requires
        funcs_ok(p, fs, tb, fds),
        envrel(cenv, renv),
        any_sm(e),
        renv_below(renv, sc),
        rx(fs, tb, false, sc, e) == Some(c),
        rsrc(fs, tb, fds, dep, sc, e) == Some(r),
        rmean(renv, r) == Some(v),
    ensures
        evals_to(p, cenv, c, vof(v)),
    decreases dep, e, 1nat,
{
    reveal_with_fuel(rx, 1);
    reveal_with_fuel(any_top, 1);
    reveal_with_fuel(rsrc, 1);
    reveal_with_fuel(rmean, 1);
    reveal_with_fuel(vof, 1);
    match e {
        Sx::SumMatch(m, arms) => {
            assert(any_arms(arms));
            assert(rx(fs, tb, false, sc, *m) is Some);
            let cm = rx(fs, tb, false, sc, *m)->Some_0;
            assert(any_top(fs, tb, false, sc, arms, cm) == Some(c));
            any_top_let(fs, tb, false, sc, arms, cm, c);
            let cb = rx(fs, tb, false, sc.push(Seq::empty()), arms[0].1)->Some_0;
            assert(c == Expr::Let(sc.len(), Box::new(cm), Box::new(cb)));
            assert(rsrc(fs, tb, fds, dep, sc, *m) is Some && rsrc(fs, tb, fds, dep, sc.push(Seq::empty()), arms[0].1) is Some);
            let rm = rsrc(fs, tb, fds, dep, sc, *m)->Some_0;
            let rb = rsrc(fs, tb, fds, dep, sc.push(Seq::empty()), arms[0].1)->Some_0;
            assert(r == RExpr::Let(sc.len(), Box::new(rm), Box::new(rb)));
            assert(rmean(renv, rm) is Some);
            let mv = rmean(renv, rm)->Some_0;
            assert(rmean(renv.insert(sc.len(), mv), rb) == Some(v));
            resolve_sound(p, fs, tb, fds, dep, sc, *m, cenv, renv, cm, rm, mv);
            envrel_ins(cenv, renv, sc.len(), mv);
            below_push(renv, sc, Seq::empty(), sc.len(), mv);
            resolve_sound(p, fs, tb, fds, dep, sc.push(Seq::empty()), arms[0].1, cenv.insert(sc.len(), vof(mv)), renv.insert(sc.len(), mv), cb, rb, v);
            bs_let(p, cenv, sc.len(), cm, cb, vof(mv), vof(v));
        },
        _ => {},
    }
}

/// 直和型の match の腕（`_` だけでない）：被験式の定理で構築子の値 Sum(k, n, vs) を得て、層 k の枝の本体を解決し、
/// arm_wrap_sound で枝の式を示し、smatch_chain で核の鎖（層 0 から層 k まで降りる）に評価されることを示す。
#[verifier::rlimit(300)]
proof fn sum_layer_arm(p: Prog, fs: Seq<Seq<char>>, tb: Seq<(Seq<char>, Option<Ty>, Seq<Seq<char>>, Option<Ty>)>, fds: Seq<Sd>, dep: nat, sc: Seq<Seq<char>>, e: Sx, cenv: Map<nat, Val>, renv: Map<nat, RVal>, c: Expr, r: RExpr, v: RVal)
    requires
        funcs_ok(p, fs, tb, fds),
        envrel(cenv, renv),
        e is SumMatch,
        !any_sm(e),
        renv_below(renv, sc),
        rx(fs, tb, false, sc, e) == Some(c),
        rsrc(fs, tb, fds, dep, sc, e) == Some(r),
        rmean(renv, r) == Some(v),
    ensures
        evals_to(p, cenv, c, vof(v)),
    decreases dep, e, 1nat,
{
    reveal_with_fuel(rx, 1);
    reveal_with_fuel(rsrc, 1);
    reveal_with_fuel(rmean, 1);
    reveal_with_fuel(vof, 1);
    reveal_with_fuel(pushn, 1);
    reveal_with_fuel(smatch_top, 1);
    match e {
        Sx::SumMatch(m, arms) => {
            assert(!any_arms(arms));
            assert(arms_sum(tb, arms) is Some) by {
                if arms_sum(tb, arms) is None {
                    assert(rx(fs, tb, false, sc, e) is None);
                }
            }
            let i = arms_sum(tb, arms)->Some_0;
            let ents = tb[i as int].2;
            assert(rx(fs, tb, false, sc, *m) is Some) by {
                if rx(fs, tb, false, sc, *m) is None {
                    assert(rx(fs, tb, false, sc, e) is None);
                }
            }
            let cm = rx(fs, tb, false, sc, *m)->Some_0;
            assert(smatch_top(fs, tb, false, sc, arms, i, cm) == Some(c));
            assert(smatch_from(fs, tb, false, sc, ents, arms, 0, cm) == Some(c));
            assert(rsrc(fs, tb, fds, dep, sc, *m) is Some) by {
                if rsrc(fs, tb, fds, dep, sc, *m) is None {
                    assert(rsrc(fs, tb, fds, dep, sc, e) is None);
                }
            }
            let rm = rsrc(fs, tb, fds, dep, sc, *m)->Some_0;
            assert(rsrc_layers(fs, tb, fds, dep, sc, ents, arms, 0) is Some) by {
                if rsrc_layers(fs, tb, fds, dep, sc, ents, arms, 0) is None {
                    assert(rsrc(fs, tb, fds, dep, sc, e) is None);
                }
            }
            let es = rsrc_layers(fs, tb, fds, dep, sc, ents, arms, 0)->Some_0;
            assert(r == RExpr::SMatch(Box::new(rm), es));
            assert(rmean(renv, rm) is Some);
            let mv = rmean(renv, rm)->Some_0;
            assert(mv is Sum) by {
                if !(mv is Sum) {
                    assert(rmean(renv, r) is None);
                }
            }
            let k = mv->Sum_0;
            let n = mv->Sum_1;
            let vs = mv->Sum_2;
            rsrc_layers_len(fs, tb, fds, dep, sc, ents, arms, 0, es);
            assert(n == es.len() && k < n);
            assert(n == ents.len());
            assert(smatch_arm(renv, es, k, vs) == Some(v));
            assert(k < es.len());
            let ent = es[k as int];
            let ids = ent.0;
            let body = ent.1;
            assert(ids.len() == 0 || ids.len() == vs.len());
            assert(rmean(sbind(renv, ids, vs, 0), body) == Some(v));
            rsrc_layers_at(fs, tb, fds, dep, sc, ents, arms, 0, es, k);
            assert(rsrc_layer(fs, tb, fds, dep, sc, ents, arms, k) == Some(ent));
            // 被験式の定理：構築子の値は、層 0 から k までの鎖の値に評価される。
            resolve_sound(p, fs, tb, fds, dep, sc, *m, cenv, renv, cm, rm, mv);
            vof_sum(k, n, vs);
            let pv = pay_val(vofs(vs, 0));
            assert(vof(mv) == vsum_from(k, ents.len(), 0, pv));
            // 層 k の枝の式（核）と源の本体
            lay_body_some(fs, tb, sc, ents, arms, 0, cm, c, k);
            assert(layer_idx(ents, k, arms) is Some) by {
                if layer_idx(ents, k, arms) is None {
                    assert(lay_sel(ents, arms, k) is None);
                }
            }
            let ka = layer_idx(ents, k, arms)->Some_0;
            assert(ka < arms.len());
            assert(arm_binds_or_empty(arms[ka as int].0) is Some);
            let bs = arm_binds_or_empty(arms[ka as int].0)->Some_0;
            assert(lay_sel(ents, arms, k) == Some((bs, arms[ka as int].1)));
            assert(arm_ok(bs) && binds_fresh(pushn(sc, k), bs));
            assert(rx(fs, tb, false, arm_scope(pushn(sc, k), bs), arms[ka as int].1) is Some);
            let bo = rx(fs, tb, false, arm_scope(pushn(sc, k), bs), arms[ka as int].1)->Some_0;
            assert(lay_body(fs, tb, sc, ents, arms, k) == Some(bo));
            assert(lay_wrap(fs, tb, sc, ents, arms, k) == Some(arm_wrap(sc.len() + k, bs, bo)));
            assert(ids == arm_ids(sc.len() + k, bs));
            assert(rsrc(fs, tb, fds, dep, arm_scope(pushn(sc, k), bs), arms[ka as int].1) == Some(body));
            // 位置と環境
            pushn_len(sc, k);
            arm_scope_props(pushn(sc, k), bs);
            let pos = sc.len() + k;
            let sc1 = arm_scope(pushn(sc, k), bs);
            assert(sc1.len() >= pos + 1);
            envrel_chain(cenv, renv, sc.len(), 0, k, ents.len(), pv);
            chain_env_at(cenv, sc.len(), 0, k, ents.len(), pv);
            let cch = chain_env(cenv, sc.len(), 0, k, ents.len(), pv);
            assert(cch.contains_key(pos) && cch[pos] == pv);
            vofs_len(vs, 0);
            below_mono(renv, sc, sc1);
            if bs.len() >= 2 {
                assert(ids == Seq::new(bs.len(), |i: int| (pos + 1 + i) as nat));
                assert(ids.len() == bs.len());
                assert(ids.len() == vs.len());
                assert forall|q: int| 0 <= q < ids.len() implies ids[q] == pos + 1 + q by {
                    assert(ids[q] == (pos + 1 + q) as nat);
                }
                assert forall|q: int| 0 <= q < ids.len() implies ids[q] < sc1.len() by {
                    assert(ids[q] == pos + 1 + q);
                }
                assert(pv == rval(vofs(vs, 0)));
                envrel_fenv(cch, renv, pos, vs, ids, 0);
                below_sbind(renv, sc1, ids, vs, 0);
                resolve_sound(p, fs, tb, fds, dep, sc1, arms[ka as int].1, fenv(cch, pos, vofs(vs, 0), 0), sbind(renv, ids, vs, 0), bo, body, v);
                arm_wrap_sound(p, cch, pos, bs, bo, vofs(vs, 0), vof(v));
                smatch_chain(p, fs, tb, sc, ents, arms, 0, cm, c, cenv, k, pv, vof(v));
            } else if bs.len() == 1 {
                assert(ids == seq![pos]);
                assert(vs.len() == 1);
                vofs_at0(vs, 0);
                reveal_with_fuel(rval, 1);
                assert(pv == vof(vs[0]));
                envrel_one(cch, renv, pos, vs[0]);
                reveal_with_fuel(sbind, 2);
                assert(sbind(renv, ids, vs, 0) == renv.insert(pos, vs[0]));
                below_sbind(renv, sc1, ids, vs, 0);
                resolve_sound(p, fs, tb, fds, dep, sc1, arms[ka as int].1, cch, sbind(renv, ids, vs, 0), bo, body, v);
                arm_wrap_sound(p, cch, pos, bs, bo, vofs(vs, 0), vof(v));
                smatch_chain(p, fs, tb, sc, ents, arms, 0, cm, c, cenv, k, pv, vof(v));
            } else {
                assert(ids.len() == 0);
                reveal_with_fuel(sbind, 1);
                assert(sbind(renv, ids, vs, 0) == renv);
                resolve_sound(p, fs, tb, fds, dep, sc1, arms[ka as int].1, cch, renv, bo, body, v);
                arm_wrap_sound(p, cch, pos, bs, bo, vofs(vs, 0), vof(v));
                smatch_chain(p, fs, tb, sc, ents, arms, 0, cm, c, cenv, k, pv, vof(v));
            }
        },
        _ => {},
    }
}

} // verus!
