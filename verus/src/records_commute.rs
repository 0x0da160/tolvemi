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
use crate::syntax::{Sd, Sx};
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

/// 源の式の写し（位置で書いた字段）。resolve.rs の rx の記録の腕と同じ名前の解決（空の名前は拒否）を
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
                None => None,
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
        Sx::Call(f, es) => if dep == 0 {
            None
        } else {
            match idx(fs, f, 0) {
                Some(g) => if g < fds.len() {
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
                None => None,
            }
        },
        _ => None,
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

/// pair の値を持つ式の成分（records_proof の un_eval と同じ証明）。
proof fn fst_snd(p: Prog, env: Map<nat, Val>, e: Expr, v: Val)
    requires
        evals_to(p, env, e, v),
        v is Pair,
    ensures
        evals_to(p, env, Expr::Builtin(Builtin::Fst, seq![e]), *v->Pair_0),
        evals_to(p, env, Expr::Builtin(Builtin::Snd, seq![e]), *v->Pair_1),
{
    let n = choose|n: nat| #[trigger] eval(p, n, env, e) == Res::Done(v);
    assert(n > 0);
    let es = seq![e];
    assert(es[0] == e);
    assert(eval_args(p, n, env, es, 1) == ResSeq::Done(Seq::<Val>::empty()));
    assert(seq![v] + Seq::<Val>::empty() =~= seq![v]);
    assert(eval_args(p, n + 1, env, es, 0) == ResSeq::Done(seq![v]));
    assert(eval(p, n + 2, env, Expr::Builtin(Builtin::Fst, es)) == Res::Done(*v->Pair_0));
    assert(eval(p, n + 2, env, Expr::Builtin(Builtin::Snd, es)) == Res::Done(*v->Pair_1));
}

/// 字段の参照の評価（型に依らない）：e が字段の値の列の展開 rval(vs) を持てば、rfield(e, i, n) は
/// i 番目の字段の値を持つ。
pub proof fn rfield_eval(p: Prog, env: Map<nat, Val>, e: Expr, vs: Seq<Val>, i: nat)
    requires
        vs.len() >= 1,
        i < vs.len(),
        evals_to(p, env, e, rval(vs)),
    ensures
        evals_to(p, env, rfield(e, i, vs.len()), vs[i as int]),
    decreases i,
{
    reveal_with_fuel(snds, 2);
    reveal_with_fuel(rval, 2);
    let n = vs.len();
    if n == 1 {
        assert(rval(vs) == vs[0]);
        assert(snds(e, 0) == e);
    } else {
        let us = vs.drop_first();
        assert(us.len() == n - 1);
        assert(rval(vs) == Val::Pair(Box::new(vs[0]), Box::new(rval(us))));
        assert(rval(vs) is Pair);
        assert(*rval(vs)->Pair_0 == vs[0]);
        assert(*rval(vs)->Pair_1 == rval(us));
        fst_snd(p, env, e, rval(vs));
        if i == 0 {
            assert(rfield(e, 0, n) == Expr::Builtin(Builtin::Fst, seq![e]));
        } else {
            let e1 = Expr::Builtin(Builtin::Snd, seq![e]);
            assert(snds(e, i) == snds(e1, (i - 1) as nat));
            assert(rfield(e, i, n) == rfield(e1, (i - 1) as nat, us.len()));
            rfield_eval(p, env, e1, us, (i - 1) as nat);
            assert(us[(i - 1) as int] == vs[i as int]);
        }
    }
}

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

/// 名前 n の位置が空の名前である scope（t[n] は空）で解決した式は、その位置を参照も束縛もしない。
/// 深い scope の空の名前の位置が、字段の式に現れないことを示す。記録の構築（rx の Rec の腕）は、空の名前が
/// ある scope では拒否されるので、ここには現れない。let は、束縛の名前（sc.len()）が n と違うので、その位置を覆わない。
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
            assert(idx(t, x, 0) is Some);
            idx_props(t, x, 0);
            let k = idx(t, x, 0)->Some_0;
            assert(t[k as int] == x);
            assert(k != n);
            assert(c == Expr::Var(k));
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
        Sx::Rec(r, fls, base) => {
            if idx(t, Seq::empty(), 0) is None {
                idx_props(t, Seq::empty(), 0);
                assert(t[n as int] != Seq::<char>::empty());
            }
        },
        // 直和型の枝は rsrc が写さない（None）。要求の rsrc is Some に反する。
        Sx::SumMatch(..) => {
            assert(rsrc(fs, tb, fds, dep, t, e) is None);
        },
        _ => {},
    }
}

/// match の腕の名前の位置：走査する式と各枝は、位置 n を参照も束縛もしない。some の枝の scope は一つ長く、位置 n は同じ。
/// 束縛の名前は sc.len() で、n とは違う（absent_at_let と同じ）。
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

/// 名前解決の定理の変数の腕と、書いた式の腕の振り分け。
/// 定理：rx が c を返し、rsrc が r を返し、rmean(r) が v なら、c は vof(v) に評価される（部分正しさ、印なし）。
pub proof fn resolve_sound(p: Prog, fs: Seq<Seq<char>>, tb: Seq<(Seq<char>, Option<Ty>, Seq<Seq<char>>, Option<Ty>)>, fds: Seq<Sd>, dep: nat, sc: Seq<Seq<char>>, e: Sx, cenv: Map<nat, Val>, renv: Map<nat, RVal>, c: Expr, r: RExpr, v: RVal)
    requires
        funcs_ok(p, fs, tb, fds),
        envrel(cenv, renv),
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
            assert(idx(sc, x, 0) is Some);
            let k = idx(sc, x, 0)->Some_0;
            assert(c == Expr::Var(k));
            assert(r == RExpr::Var(k));
            assert(renv.contains_key(k));
            assert(cenv.contains_key(k) && cenv[k] == vof(renv[k]));
            bs_var(p, cenv, k);
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
        Sx::Call(..) => call_arm(p, fs, tb, fds, dep, sc, e, cenv, renv, c, r, v),
        Sx::Rec(_, _, None) => rec_none_top(p, fs, tb, fds, dep, sc, e, cenv, renv, c, r, v),
        Sx::Rec(_, _, Some(_)) => rec_some_top(p, fs, tb, fds, dep, sc, e, cenv, renv, c, r, v),
        _ => {},
    }
}

/// 対の腕：成分の定理と bs_pair。
proof fn pair_arm(p: Prog, fs: Seq<Seq<char>>, tb: Seq<(Seq<char>, Option<Ty>, Seq<Seq<char>>, Option<Ty>)>, fds: Seq<Sd>, dep: nat, sc: Seq<Seq<char>>, e: Sx, cenv: Map<nat, Val>, renv: Map<nat, RVal>, c: Expr, r: RExpr, v: RVal)
    requires
        funcs_ok(p, fs, tb, fds),
        envrel(cenv, renv),
        e is Pair,
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
proof fn let_arm(p: Prog, fs: Seq<Seq<char>>, tb: Seq<(Seq<char>, Option<Ty>, Seq<Seq<char>>, Option<Ty>)>, fds: Seq<Sd>, dep: nat, sc: Seq<Seq<char>>, e: Sx, cenv: Map<nat, Val>, renv: Map<nat, RVal>, c: Expr, r: RExpr, v: RVal)
    requires
        funcs_ok(p, fs, tb, fds),
        envrel(cenv, renv),
        e is Let,
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
            assert(idx(fs, f, 0) is Some && rxs(fs, tb, false, t, es, 0) is Some);
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
            assert(idx(sc, Seq::empty(), 0) is None);
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
            assert(idx(sc, Seq::empty(), 0) is None);
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

} // verus!
