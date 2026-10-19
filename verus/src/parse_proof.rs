//! parser の健全性・完全性（設計書 §11.2 の 1）と formatter の AST 保存性・冪等性（2）。

use crate::spec::*;
use crate::syntax::*;
use crate::syntax_proof::*;
use vstd::prelude::*;

verus! {

pub open spec fn suf(ts: Seq<Tok>, i: nat) -> Seq<Tok> {
    ts.subrange(i as int, ts.len() as int)
}

/// 式の直後に来てよい token 列（変数の直後の `(` は呼出し、文脈キーワードの直後の `<` は型引数と読まれる）。
pub open spec fn nf(k: Seq<Tok>) -> bool {
    k.len() == 0 || (k[0] != Tok::Sym('(') && k[0] != Tok::Sym('<') && k[0] != Tok::Sym('{'))
}

pub open spec fn not_sym(t: Tok) -> bool {
    !(t is Sym)
}

/// 列の分割：suf(ts, i) == a + b なら a は位置 i から並び、その後ろは b。
pub proof fn hd(ts: Seq<Tok>, i: nat, a: Seq<Tok>, b: Seq<Tok>)
    requires
        i <= ts.len(),
        suf(ts, i) == a + b,
    ensures
        i + a.len() <= ts.len(),
        ts.len() == i + a.len() + b.len(),
        suf(ts, i + a.len()) == b,
        forall|j: int| 0 <= j < a.len() ==> ts[i + j] == #[trigger] a[j],
        a.len() > 0 ==> ts[i as int] == a[0],
        a.len() > 1 ==> ts[(i + 1) as int] == a[1],
        a.len() > 2 ==> ts[(i + 2) as int] == a[2],
{
    let s = suf(ts, i);
    assert(s.len() == a.len() + b.len());
    assert forall|j: int| 0 <= j < a.len() implies ts[i + j] == #[trigger] a[j] by {
        assert(s[j] == ts[i + j]);
        assert((a + b)[j] == a[j]);
    }
    assert(suf(ts, i + a.len()) =~= b) by {
        assert forall|j: int| 0 <= j < b.len() implies suf(ts, i + a.len())[j] == b[j] by {
            assert(s[a.len() + j] == ts[i + a.len() + j]);
            assert((a + b)[a.len() + j] == b[j]);
        }
    }
}

/// 位置 i から n 個の token を前に出す。
pub proof fn pre(ts: Seq<Tok>, i: nat, n: nat)
    requires
        i + n <= ts.len(),
    ensures
        suf(ts, i) == ts.subrange(i as int, (i + n) as int) + suf(ts, i + n),
{
    assert(suf(ts, i) =~= ts.subrange(i as int, (i + n) as int) + suf(ts, i + n));
}

// ------------------------------------------------------------------ token 写像の継続の分離

pub proof fn tt_app(t: Ty, k: Seq<Tok>)
    ensures
        tt(t, k) == tt(t, Seq::empty()) + k,
        tt(t, Seq::empty()).len() > 0,
        tt(t, Seq::empty())[0] is Kw,
    decreases t,
{
    let z = Seq::<Tok>::empty();
    match t {
        Ty::List(a) => {
            tt_app(*a, seq![Tok::Sym('>')] + k);
            tt_app(*a, seq![Tok::Sym('>')] + z);
        },
        Ty::Option(a) => {
            tt_app(*a, seq![Tok::Sym('>')] + k);
            tt_app(*a, seq![Tok::Sym('>')] + z);
        },
        Ty::Pair(a, b) | Ty::Result(a, b) => {
            tt_app(*b, seq![Tok::Sym('>')] + k);
            tt_app(*b, seq![Tok::Sym('>')] + z);
            tt_app(*a, seq![Tok::Sym(',')] + tt(*b, seq![Tok::Sym('>')] + k));
            tt_app(*a, seq![Tok::Sym(',')] + tt(*b, seq![Tok::Sym('>')] + z));
        },
        _ => {},
    }
    assert(tt(t, k) =~= tt(t, z) + k);
}

/// 名前の token は記号でない。
pub proof fn word_ns(x: Seq<char>)
    ensures
        not_sym(word_tok(x)),
{
}

/// レコード式の base と閉じ括弧の結合。
pub proof fn rtail_app(ne: bool, b: Option<Box<Sx>>, k: Seq<Tok>)
    ensures
        rtail(ne, b, k) == rtail(ne, b, Seq::<Tok>::empty()) + k,
    decreases b, 0nat,
{
    if let Some(x) = b {
        te_app(*x, seq![Tok::Sym('}')] + k);
        te_app(*x, seq![Tok::Sym('}')]);
        assert(te(*x, seq![Tok::Sym('}')] + k) =~= te(*x, seq![Tok::Sym('}')]) + k);
    }
    assert(rtail(ne, b, k) =~= rtail(ne, b, Seq::<Tok>::empty()) + k);
}

/// レコード式の field の並び fs[i..] の結合。
pub proof fn tfe_app(fs: Seq<(Seq<char>, Sx)>, i: nat, tail: Seq<Tok>)
    ensures
        tfe(fs, i, tail) == tfe(fs, i, Seq::<Tok>::empty()) + tail,
        i < fs.len() ==> tfe(fs, i, Seq::<Tok>::empty()).len() > 0 && not_sym(tfe(fs, i, Seq::<Tok>::empty())[0]),
    decreases fs, fs.len() - i,
{
    let z = Seq::<Tok>::empty();
    if i < fs.len() {
        let x = fs[i as int];
        word_ns(x.0);
        if i + 1 == fs.len() {
            te_app(x.1, tail);
            te_app(x.1, z);
        } else {
            tfe_app(fs, i + 1, tail);
            tfe_app(fs, i + 1, z);
            te_app(x.1, seq![Tok::Sym(',')] + tfe(fs, i + 1, tail));
            te_app(x.1, seq![Tok::Sym(',')] + tfe(fs, i + 1, z));
        }
    }
    assert(tfe(fs, i, tail) =~= tfe(fs, i, z) + tail);
}

/// 型の字段の並び fs[i..] の結合。
pub proof fn tfd_app(fs: Seq<(Seq<char>, Ty)>, i: nat, tc: bool, tail: Seq<Tok>)
    ensures
        tfd(fs, i, tc, tail) == tfd(fs, i, tc, Seq::<Tok>::empty()) + tail,
    decreases fs, fs.len() - i,
{
    let z = Seq::<Tok>::empty();
    if i < fs.len() {
        let x = fs[i as int];
        if i + 1 == fs.len() {
            if tc {
                tt_app(x.1, seq![Tok::Sym(',')] + tail);
                tt_app(x.1, seq![Tok::Sym(',')]);
            } else {
                tt_app(x.1, tail);
                tt_app(x.1, z);
            }
        } else {
            tfd_app(fs, i + 1, tc, tail);
            tfd_app(fs, i + 1, tc, z);
            tt_app(x.1, seq![Tok::Sym(',')] + tfd(fs, i + 1, tc, tail));
            tt_app(x.1, seq![Tok::Sym(',')] + tfd(fs, i + 1, tc, z));
        }
    }
    assert(tfd(fs, i, tc, tail) =~= tfd(fs, i, tc, z) + tail);
}

/// 先頭の字段を一つ取った並びの後ろ（位置を一つ進める）。
pub proof fn tfe_shift(x: (Seq<char>, Sx), fs: Seq<(Seq<char>, Sx)>, i: nat, tail: Seq<Tok>)
    ensures
        tfe(seq![x] + fs, i + 1, tail) == tfe(fs, i, tail),
    decreases fs.len() - i,
{
    let s = seq![x] + fs;
    if i < fs.len() {
        assert(s[(i + 1) as int] == fs[i as int]);
        if i + 1 < fs.len() {
            tfe_shift(x, fs, i + 1, tail);
        }
    }
}

pub proof fn tfd_shift(x: (Seq<char>, Ty), fs: Seq<(Seq<char>, Ty)>, i: nat, tc: bool, tail: Seq<Tok>)
    ensures
        tfd(seq![x] + fs, i + 1, tc, tail) == tfd(fs, i, tc, tail),
    decreases fs.len() - i,
{
    let s = seq![x] + fs;
    if i < fs.len() {
        assert(s[(i + 1) as int] == fs[i as int]);
        if i + 1 < fs.len() {
            tfd_shift(x, fs, i + 1, tc, tail);
        }
    }
}

pub proof fn bfs_shift(x: (Seq<char>, Sx), fs: Seq<(Seq<char>, Sx)>, i: nat, d: nat, td: nat)
    ensures
        bfs(seq![x] + fs, i + 1, d, td) == bfs(fs, i, d, td),
    decreases fs.len() - i,
{
    let s = seq![x] + fs;
    if i < fs.len() {
        assert(s[(i + 1) as int] == fs[i as int]);
        bfs_shift(x, fs, i + 1, d, td);
    }
}

pub proof fn bfds_shift(x: (Seq<char>, Ty), fs: Seq<(Seq<char>, Ty)>, i: nat, td: nat)
    ensures
        bfds(seq![x] + fs, i + 1, td) == bfds(fs, i, td),
    decreases fs.len() - i,
{
    let s = seq![x] + fs;
    if i < fs.len() {
        assert(s[(i + 1) as int] == fs[i as int]);
        bfds_shift(x, fs, i + 1, td);
    }
}

pub proof fn te_app(e: Sx, k: Seq<Tok>)
    ensures
        te(e, k) == te(e, Seq::empty()) + k,
        te(e, Seq::empty()).len() > 0,
        not_sym(te(e, Seq::empty())[0]),
    decreases e, 1nat,
{
    let z = Seq::<Tok>::empty();
    match e {
        Sx::List(t, es) => {
            targs_app(es, 0, k);
            targs_app(es, 0, z);
            tt_app(t, seq![Tok::Sym('>'), Tok::Sym('(')] + targs(es, 0, k));
            tt_app(t, seq![Tok::Sym('>'), Tok::Sym('(')] + targs(es, 0, z));
        },
        Sx::Some(a) => {
            te_app(*a, seq![Tok::Sym(')')] + k);
            te_app(*a, seq![Tok::Sym(')')] + z);
        },
        Sx::None(t) => {
            tt_app(t, seq![Tok::Sym('>'), Tok::Sym('('), Tok::Sym(')')] + k);
            tt_app(t, seq![Tok::Sym('>'), Tok::Sym('('), Tok::Sym(')')] + z);
        },
        Sx::Pair(a, b) => {
            te_app(*b, seq![Tok::Sym(')')] + k);
            te_app(*b, seq![Tok::Sym(')')] + z);
            te_app(*a, seq![Tok::Sym(',')] + te(*b, seq![Tok::Sym(')')] + k));
            te_app(*a, seq![Tok::Sym(',')] + te(*b, seq![Tok::Sym(')')] + z));
        },
        Sx::Builtin(_, es) => {
            targs_app(es, 0, k);
            targs_app(es, 0, z);
        },
        Sx::Call(_, es) => {
            targs_app(es, 0, k);
            targs_app(es, 0, z);
        },
        Sx::Var(x) => word_ns(x),
        Sx::Let(x, a, b) => {
            word_ns(x);
            te_app(*b, k);
            te_app(*a, seq![Tok::Kw(Kw::In)] + te(*b, k));
            te_app(*a, seq![Tok::Kw(Kw::In)] + te(*b, z));
        },
        Sx::If(..) => te_app_if(e, k),
        Sx::Fold(..) => te_app_fold(e, k),
        Sx::Match(..) => te_app_match(e, k),
        Sx::Inj(ok, t, u, a) => {
            let ka = seq![Tok::Sym(')')] + k;
            let za = seq![Tok::Sym(')')] + z;
            te_app(*a, ka);
            te_app(*a, za);
            let ku = seq![Tok::Sym('>'), Tok::Sym('(')] + te(*a, ka);
            let zu = seq![Tok::Sym('>'), Tok::Sym('(')] + te(*a, za);
            tt_app(u, ku);
            tt_app(u, zu);
            tt_app(t, seq![Tok::Sym(',')] + tt(u, ku));
            tt_app(t, seq![Tok::Sym(',')] + tt(u, zu));
        },
        Sx::MatchR(..) => te_app_matchr(e, k),
        Sx::Fld(..) => te_app_fld(e, k),
        Sx::Rec(..) => te_app_rec(e, k),
        _ => {},
    }
    assert(te(e, k) =~= te(e, z) + k);
}

proof fn te_app_fld(e: Sx, k: Seq<Tok>)
    requires
        e is Fld,
    ensures
        te(e, k) == te(e, Seq::empty()) + k,
        te(e, Seq::empty()).len() > 0,
        not_sym(te(e, Seq::empty())[0]),
    decreases e, 0nat,
{
    let z = Seq::<Tok>::empty();
    if let Sx::Fld(a, fs) = e {
        tdots_app(fs, k);
        tdots_app(fs, z);
        te_app(*a, tdots(fs, k));
        te_app(*a, tdots(fs, z));
        assert(te(e, k) =~= te(e, z) + k);
    }
}

proof fn te_app_rec(e: Sx, k: Seq<Tok>)
    requires
        e is Rec,
    ensures
        te(e, k) == te(e, Seq::empty()) + k,
        te(e, Seq::empty()).len() > 0,
        not_sym(te(e, Seq::empty())[0]),
    decreases e, 0nat,
{
    let z = Seq::<Tok>::empty();
    if let Sx::Rec(r, fs, b) = e {
        rtail_app(fs.len() > 0, b, k);
        rtail_app(fs.len() > 0, b, z);
        tfe_app(fs, 0, rtail(fs.len() > 0, b, k));
        tfe_app(fs, 0, rtail(fs.len() > 0, b, z));
        word_ns(r);
        assert(te(e, k) =~= te(e, z) + k);
    }
}

proof fn te_app_matchr(e: Sx, k: Seq<Tok>)
    requires
        e is MatchR,
    ensures
        te(e, k) == te(e, Seq::empty()) + k,
        te(e, Seq::empty()).len() > 0,
        not_sym(te(e, Seq::empty())[0]),
    decreases e, 0nat,
{
    let z = Seq::<Tok>::empty();
    if let Sx::MatchR(m, x, a, y, b) = e {
        let kb = seq![Tok::Sym(')')] + k;
        let zb = seq![Tok::Sym(')')] + z;
        let my = seq![Tok::Sym(','), Tok::Sym('|'), word_tok(y), Tok::Sym('|')];
        let mx = seq![Tok::Sym(','), Tok::Sym('|'), word_tok(x), Tok::Sym('|')];
        te_app(*b, kb);
        te_app(*b, zb);
        te_app(*a, my + te(*b, kb));
        te_app(*a, my + te(*b, zb));
        te_app(*m, mx + te(*a, my + te(*b, kb)));
        te_app(*m, mx + te(*a, my + te(*b, zb)));
    }
    assert(te(e, k) =~= te(e, z) + k);
}

proof fn te_app_if(e: Sx, k: Seq<Tok>)
    requires
        e is If,
    ensures
        te(e, k) == te(e, Seq::empty()) + k,
        te(e, Seq::empty()).len() > 0,
        not_sym(te(e, Seq::empty())[0]),
    decreases e, 0nat,
{
    let z = Seq::<Tok>::empty();
    if let Sx::If(c, a, b) = e {
        let kb = seq![Tok::Sym(')')] + k;
        let zb = seq![Tok::Sym(')')] + z;
        te_app(*b, kb);
        te_app(*b, zb);
        te_app(*a, seq![Tok::Sym(',')] + te(*b, kb));
        te_app(*a, seq![Tok::Sym(',')] + te(*b, zb));
        te_app(*c, seq![Tok::Sym(',')] + te(*a, seq![Tok::Sym(',')] + te(*b, kb)));
        te_app(*c, seq![Tok::Sym(',')] + te(*a, seq![Tok::Sym(',')] + te(*b, zb)));
    }
    assert(te(e, k) =~= te(e, z) + k);
}

proof fn te_app_fold(e: Sx, k: Seq<Tok>)
    requires
        e is Fold,
    ensures
        te(e, k) == te(e, Seq::empty()) + k,
        te(e, Seq::empty()).len() > 0,
        not_sym(te(e, Seq::empty())[0]),
    decreases e, 0nat,
{
    let z = Seq::<Tok>::empty();
    if let Sx::Fold(l, i, a, x, b) = e {
        let kb = seq![Tok::Sym(')')] + k;
        let zb = seq![Tok::Sym(')')] + z;
        let mid = seq![Tok::Sym(','), Tok::Sym('|'), word_tok(a), Tok::Sym(','), word_tok(x), Tok::Sym('|')];
        te_app(*b, kb);
        te_app(*b, zb);
        te_app(*i, mid + te(*b, kb));
        te_app(*i, mid + te(*b, zb));
        te_app(*l, seq![Tok::Sym(',')] + te(*i, mid + te(*b, kb)));
        te_app(*l, seq![Tok::Sym(',')] + te(*i, mid + te(*b, zb)));
    }
    assert(te(e, k) =~= te(e, z) + k);
}

proof fn te_app_match(e: Sx, k: Seq<Tok>)
    requires
        e is Match,
    ensures
        te(e, k) == te(e, Seq::empty()) + k,
        te(e, Seq::empty()).len() > 0,
        not_sym(te(e, Seq::empty())[0]),
    decreases e, 0nat,
{
    let z = Seq::<Tok>::empty();
    if let Sx::Match(m, n, x, b) = e {
        let kb = seq![Tok::Sym(')')] + k;
        let zb = seq![Tok::Sym(')')] + z;
        let mid = seq![Tok::Sym(','), Tok::Sym('|'), word_tok(x), Tok::Sym('|')];
        te_app(*b, kb);
        te_app(*b, zb);
        te_app(*n, mid + te(*b, kb));
        te_app(*n, mid + te(*b, zb));
        te_app(*m, seq![Tok::Sym(',')] + te(*n, mid + te(*b, kb)));
        te_app(*m, seq![Tok::Sym(',')] + te(*n, mid + te(*b, zb)));
    }
    assert(te(e, k) =~= te(e, z) + k);
}

pub proof fn targs_app(es: Seq<Sx>, i: nat, k: Seq<Tok>)
    ensures
        targs(es, i, k) == targs(es, i, Seq::empty()) + k,
        targs(es, i, Seq::empty()).len() > 0,
        i < es.len() ==> not_sym(targs(es, i, Seq::empty())[0]),
    decreases es, es.len() - i,
{
    let z = Seq::<Tok>::empty();
    if i >= es.len() {
    } else if i + 1 == es.len() {
        te_app(es[i as int], seq![Tok::Sym(')')] + k);
        te_app(es[i as int], seq![Tok::Sym(')')] + z);
    } else {
        targs_app(es, i + 1, k);
        te_app(es[i as int], seq![Tok::Sym(',')] + targs(es, i + 1, k));
        te_app(es[i as int], seq![Tok::Sym(',')] + targs(es, i + 1, z));
    }
    assert(targs(es, i, k) =~= targs(es, i, z) + k);
}

pub proof fn tps_app(ps: Seq<(Seq<char>, Ty)>, i: nat, k: Seq<Tok>)
    ensures
        tps(ps, i, k) == tps(ps, i, Seq::empty()) + k,
        tps(ps, i, Seq::empty()).len() > 0,
    decreases ps.len() - i,
{
    let z = Seq::<Tok>::empty();
    if i < ps.len() {
        if i + 1 == ps.len() {
            tt_app(ps[i as int].1, seq![Tok::Sym(')')] + k);
            tt_app(ps[i as int].1, seq![Tok::Sym(')')] + z);
        } else {
            tps_app(ps, i + 1, k);
            tt_app(ps[i as int].1, seq![Tok::Sym(',')] + tps(ps, i + 1, k));
            tt_app(ps[i as int].1, seq![Tok::Sym(',')] + tps(ps, i + 1, z));
        }
    }
    assert(tps(ps, i, k) =~= tps(ps, i, z) + k);
}

/// 型の並びの後ろの結合。
pub proof fn tts_app(ps: Seq<Ty>, i: nat, k: Seq<Tok>)
    ensures
        tts(ps, i, k) == tts(ps, i, Seq::<Tok>::empty()) + k,
    decreases ps.len() - i,
{
    let z = Seq::<Tok>::empty();
    if i < ps.len() {
        if i + 1 == ps.len() {
            tt_app(ps[i as int], k);
            tt_app(ps[i as int], z);
        } else {
            tts_app(ps, i + 1, k);
            tt_app(ps[i as int], seq![Tok::Sym(',')] + tts(ps, i + 1, k));
            tt_app(ps[i as int], seq![Tok::Sym(',')] + tts(ps, i + 1, z));
        }
    }
    assert(tts(ps, i, k) =~= tts(ps, i, z) + k);
}

/// 構築子の中身の結合。
pub proof fn tpay_app(ps: Seq<Ty>, k: Seq<Tok>)
    ensures
        tpay(ps, k) == tpay(ps, Seq::<Tok>::empty()) + k,
{
    let z = Seq::<Tok>::empty();
    if ps.len() > 0 {
        tts_app(ps, 0, seq![Tok::Sym(')')] + k);
        tts_app(ps, 0, seq![Tok::Sym(')')]);
        assert(seq![Tok::Sym(')')] + z =~= seq![Tok::Sym(')')]);
    }
    assert(tpay(ps, k) =~= tpay(ps, z) + k);
}

/// 直和型の構築子の並びの結合。
pub proof fn tvars_app(vs: Seq<(Seq<char>, Seq<Ty>)>, i: nat, k: Seq<Tok>)
    ensures
        tvars(vs, i, k) == tvars(vs, i, Seq::<Tok>::empty()) + k,
    decreases vs.len() - i,
{
    let z = Seq::<Tok>::empty();
    if i < vs.len() {
        if i + 1 == vs.len() {
            tpay_app(vs[i as int].1, k);
            tpay_app(vs[i as int].1, z);
        } else {
            tvars_app(vs, i + 1, k);
            tpay_app(vs[i as int].1, seq![Tok::Sym('|')] + tvars(vs, i + 1, k));
            tpay_app(vs[i as int].1, seq![Tok::Sym('|')] + tvars(vs, i + 1, z));
        }
    }
    assert(tvars(vs, i, k) =~= tvars(vs, i, z) + k);
}

/// 先頭の型を一つ取った並びの後ろ（位置を一つ進める）。
pub proof fn tts_shift(x: Ty, ps: Seq<Ty>, i: nat, k: Seq<Tok>)
    ensures
        tts(seq![x] + ps, i + 1, k) == tts(ps, i, k),
    decreases ps.len() - i,
{
    let s = seq![x] + ps;
    if i < ps.len() {
        assert(s[(i + 1) as int] == ps[i as int]);
        if i + 1 < ps.len() {
            tts_shift(x, ps, i + 1, k);
        }
    }
}

/// 先頭の構築子を一つ取った並びの後ろ（位置を一つ進める）。
pub proof fn tvars_shift(x: (Seq<char>, Seq<Ty>), vs: Seq<(Seq<char>, Seq<Ty>)>, i: nat, k: Seq<Tok>)
    ensures
        tvars(seq![x] + vs, i + 1, k) == tvars(vs, i, k),
    decreases vs.len() - i,
{
    let s = seq![x] + vs;
    if i < vs.len() {
        assert(s[(i + 1) as int] == vs[i as int]);
        if i + 1 < vs.len() {
            tvars_shift(x, vs, i + 1, k);
        }
    }
}

pub proof fn bts_shift(x: Ty, ps: Seq<Ty>, i: nat, td: nat)
    ensures
        bts(seq![x] + ps, i + 1, td) == bts(ps, i, td),
    decreases ps.len() - i,
{
    let s = seq![x] + ps;
    if i < ps.len() {
        assert(s[(i + 1) as int] == ps[i as int]);
        bts_shift(x, ps, i + 1, td);
    }
}

pub proof fn bvars_shift(x: (Seq<char>, Seq<Ty>), vs: Seq<(Seq<char>, Seq<Ty>)>, i: nat, td: nat)
    ensures
        bvars(seq![x] + vs, i + 1, td) == bvars(vs, i, td),
    decreases vs.len() - i,
{
    let s = seq![x] + vs;
    if i < vs.len() {
        assert(s[(i + 1) as int] == vs[i as int]);
        bvars_shift(x, vs, i + 1, td);
    }
}

pub proof fn tdecl_app(x: Sd, k: Seq<Tok>)
    ensures
        tdecl(x, k) == tdecl(x, Seq::empty()) + k,
        tdecl(x, Seq::empty()).len() > 0,
        tdecl(x, k)[0] == Tok::Kw(Kw::Fn) || tdecl(x, k)[0] == Tok::Kw(Kw::Entry) || tdecl(x, k)[0] == Tok::Id(tyw()),
{
    let z = Seq::<Tok>::empty();
    match x {
        Sd::Fn(f, ps, r, b) => {
            te_app(b, k);
            tt_app(r, seq![Tok::Sym('=')] + te(b, k));
            tt_app(r, seq![Tok::Sym('=')] + te(b, z));
            tps_app(ps, 0, seq![Tok::Arrow] + tt(r, seq![Tok::Sym('=')] + te(b, k)));
            tps_app(ps, 0, seq![Tok::Arrow] + tt(r, seq![Tok::Sym('=')] + te(b, z)));
        },
        Sd::RecTy(r, fs, tc) => {
            tfd_app(fs, 0, tc, seq![Tok::Sym('}')] + k);
            tfd_app(fs, 0, tc, seq![Tok::Sym('}')]);
            assert(tdecl(x, k) =~= tdecl(x, z) + k);
        },
        Sd::Sum(r, vs) => {
            tvars_app(vs, 0, k);
            assert(tdecl(x, k) =~= tdecl(x, z) + k);
        },
        _ => {},
    }
    assert(tdecl(x, k) =~= tdecl(x, z) + k);
}

/// 継続 k が suf(ts, i) の末尾なら、k は位置 len - |k| から始まる。
pub proof fn at_end(ts: Seq<Tok>, i: nat, s: Seq<Tok>, k: Seq<Tok>)
    requires
        i <= ts.len(),
        suf(ts, i) == s + k,
    ensures
        ts.len() - k.len() == i + s.len(),
        suf(ts, (ts.len() - k.len()) as nat) == k,
{
    hd(ts, i, s, k);
}

// ------------------------------------------------------------------ 完全性

pub proof fn pt_complete(ts: Seq<Tok>, i: nat, d: nat, t: Ty, k: Seq<Tok>)
    requires
        i <= ts.len(),
        suf(ts, i) == tt(t, k),
        bt(t, d),
    ensures
        pt(ts, i, d) == Some((t, (ts.len() - k.len()) as nat)),
    decreases t,
{
    let d1 = (d - 1) as nat;
    let z = Seq::<Tok>::empty();
    match t {
        Ty::List(a) => if *a == Ty::Char {
            hd(ts, i, seq![Tok::Kw(Kw::TString)], k);
        } else {
            let k1 = seq![Tok::Sym('>')] + k;
            hd(ts, i, seq![Tok::Kw(Kw::TList), Tok::Sym('<')], tt(*a, k1));
            pt_complete(ts, i + 2, d1, *a, k1);
            tt_app(*a, k1);
            at_end(ts, i + 2, tt(*a, z), k1);
            hd(ts, (ts.len() - k1.len()) as nat, seq![Tok::Sym('>')], k);
        },
        Ty::Option(a) => {
            let k1 = seq![Tok::Sym('>')] + k;
            hd(ts, i, seq![Tok::Kw(Kw::TOption), Tok::Sym('<')], tt(*a, k1));
            pt_complete(ts, i + 2, d1, *a, k1);
            tt_app(*a, k1);
            at_end(ts, i + 2, tt(*a, z), k1);
            hd(ts, (ts.len() - k1.len()) as nat, seq![Tok::Sym('>')], k);
        },
        Ty::Pair(a, b) => {
            let kb = seq![Tok::Sym('>')] + k;
            let ka = seq![Tok::Sym(',')] + tt(*b, kb);
            hd(ts, i, seq![Tok::Kw(Kw::TPair), Tok::Sym('<')], tt(*a, ka));
            pt_complete(ts, i + 2, d1, *a, ka);
            tt_app(*a, ka);
            at_end(ts, i + 2, tt(*a, z), ka);
            let j = (ts.len() - ka.len()) as nat;
            hd(ts, j, seq![Tok::Sym(',')], tt(*b, kb));
            pt_complete(ts, j + 1, d1, *b, kb);
            tt_app(*b, kb);
            at_end(ts, j + 1, tt(*b, z), kb);
            hd(ts, (ts.len() - kb.len()) as nat, seq![Tok::Sym('>')], k);
        },
        Ty::Result(a, b) => {
            let kb = seq![Tok::Sym('>')] + k;
            let ka = seq![Tok::Sym(',')] + tt(*b, kb);
            hd(ts, i, seq![Tok::Kw(Kw::TResult), Tok::Sym('<')], tt(*a, ka));
            pt_complete(ts, i + 2, d1, *a, ka);
            tt_app(*a, ka);
            at_end(ts, i + 2, tt(*a, z), ka);
            let j = (ts.len() - ka.len()) as nat;
            hd(ts, j, seq![Tok::Sym(',')], tt(*b, kb));
            pt_complete(ts, j + 1, d1, *b, kb);
            tt_app(*b, kb);
            at_end(ts, j + 1, tt(*b, z), kb);
            hd(ts, (ts.len() - kb.len()) as nat, seq![Tok::Sym('>')], k);
        },
        Ty::Int => hd(ts, i, seq![Tok::Kw(Kw::TInt)], k),
        Ty::Bool => hd(ts, i, seq![Tok::Kw(Kw::TBool)], k),
        Ty::Unit => hd(ts, i, seq![Tok::Kw(Kw::TUnit)], k),
        Ty::Char => hd(ts, i, seq![Tok::Kw(Kw::TChar)], k),
    }
}

/// 式の完全性の共通の前提（後置の有無によらない部分）。
pub open spec fn pre_base(ts: Seq<Tok>, i: nat, d: nat, td: nat, e: Sx, k: Seq<Tok>) -> bool {
    &&& i <= ts.len()
    &&& suf(ts, i) == te(e, k)
    &&& bx(e, d, td)
    &&& nf(k)
}

/// 基本の式（後置を含まない）の完全性の前提。Fld は pp の結果にならない。
pub open spec fn pp_pre(ts: Seq<Tok>, i: nat, d: nat, td: nat, e: Sx, k: Seq<Tok>) -> bool {
    pre_base(ts, i, d, td, e, k) && !(e is Fld)
}

/// 式 e の後ろに k が続く。e の末尾に後置 `.` が付きうるなら、k は `.` で始まらない（Int は付かない）。
pub open spec fn no_dot(k: Seq<Tok>) -> bool {
    k.len() == 0 || k[0] != Tok::Sym('.')
}

/// 式の完全性（後置を含む）の前提。後置 `.f` の並びは、k が `.` で始まらず、末尾が整数でないときだけ、k の手前で止まる。
pub open spec fn pe_pre(ts: Seq<Tok>, i: nat, d: nat, td: nat, e: Sx, k: Seq<Tok>) -> bool {
    pre_base(ts, i, d, td, e, k) && (no_dot(k) || ends_int(e))
}

/// `.IDENT` の並びの先頭：fs が空でなければ、tdots は `.` と名前の token で始まる。
pub proof fn tdots_cons(fs: Seq<Seq<char>>, k: Seq<Tok>)
    requires
        fs.len() > 0,
    ensures
        tdots(fs, k) == seq![Tok::Sym('.'), word_tok(fs[0])] + tdots(fs.subrange(1, fs.len() as int), k),
{
}

pub proof fn tdots_app(fs: Seq<Seq<char>>, k: Seq<Tok>)
    ensures
        tdots(fs, k) == tdots(fs, Seq::<Tok>::empty()) + k,
    decreases fs.len(),
{
    if fs.len() > 0 {
        let rest = fs.subrange(1, fs.len() as int);
        tdots_app(rest, k);
        tdots_app(rest, Seq::<Tok>::empty());
        tdots_cons(fs, k);
        tdots_cons(fs, Seq::<Tok>::empty());
        assert(tdots(fs, k) =~= tdots(fs, Seq::<Tok>::empty()) + k);
    }
}

/// 字段の並び fs[j] の位置の名前と式は、深さ内の IDENT と式。
pub proof fn bfs_at(fs: Seq<(Seq<char>, Sx)>, j: nat, d: nat, td: nat)
    requires
        j < fs.len(),
        bfs(fs, j, d, td),
    ensures
        ident_ok(fs[j as int].0),
        bx(fs[j as int].1, d, td),
        bfs(fs, j + 1, d, td),
{
}

/// 型の字段の並び fs[j] の位置の名前と型は、IDENT と深さ内の型。
pub proof fn bfds_at(fs: Seq<(Seq<char>, Ty)>, j: nat, td: nat)
    requires
        j < fs.len(),
        bfds(fs, j, td),
    ensures
        ident_ok(fs[j as int].0),
        bt(fs[j as int].1, td),
        bfds(fs, j + 1, td),
{
}

/// 字段が一つだけの並びは、名前と式が深さ内なら健全。
pub proof fn bfs_one(f: Seq<char>, v: Sx, d: nat, td: nat)
    requires
        ident_ok(f),
        bx(v, d, td),
    ensures
        bfs(seq![(f, v)], 0, d, td),
{
    reveal_with_fuel(bfs, 1);
    assert(bfs(seq![(f, v)], 1, d, td));
}

/// 型の字段が一つだけの並びは、名前と型が深さ内なら健全。
pub proof fn bfds_one(f: Seq<char>, t: Ty, td: nat)
    requires
        ident_ok(f),
        bt(t, td),
    ensures
        bfds(seq![(f, t)], 0, td),
{
    reveal_with_fuel(bfds, 1);
    assert(bfds(seq![(f, t)], 1, td));
}

/// レコード式の base の後ろの閉じ部分の先頭（base があれば `,`、なければ `}`）。
pub proof fn rtail_lead(b: Option<Box<Sx>>, k: Seq<Tok>)
    ensures
        rtail(true, b, k).len() > 0,
        rtail(true, b, k)[0] == Tok::Sym(',') || rtail(true, b, k)[0] == Tok::Sym('}'),
{
    match b {
        Some(x) => {
            assert(rtail(true, b, k) == seq![Tok::Sym(',')] + seq![Tok::Sym('.'), Tok::Sym('.')] + te(*x, seq![Tok::Sym('}')] + k));
        },
        None => {},
    }
}

/// 字段 fs[i] の先頭の token（名前と `:`）。
pub proof fn tfe_head(fs: Seq<(Seq<char>, Sx)>, i: nat, tail: Seq<Tok>)
    requires
        i < fs.len(),
    ensures
        tfe(fs, i, tail) == seq![word_tok(fs[i as int].0), Tok::Sym(':')] + te(
            fs[i as int].1,
            if i + 1 == fs.len() {
                tail
            } else {
                seq![Tok::Sym(',')] + tfe(fs, i + 1, tail)
            },
        ),
{
}

pub proof fn tfd_head(fs: Seq<(Seq<char>, Ty)>, i: nat, tc: bool, tail: Seq<Tok>)
    requires
        i < fs.len(),
    ensures
        tfd(fs, i, tc, tail) == seq![word_tok(fs[i as int].0), Tok::Sym(':')] + tt(
            fs[i as int].1,
            if i + 1 == fs.len() {
                if tc {
                    seq![Tok::Sym(',')] + tail
                } else {
                    tail
                }
            } else {
                seq![Tok::Sym(',')] + tfd(fs, i + 1, tc, tail)
            },
        ),
{
}

/// 名前の列の並び：`.IDENT` の列の後ろが k で、k は `.` で始まらないなら、pfs は並びを最大に読む。
pub proof fn pfs_complete(ts: Seq<Tok>, j: nat, fs: Seq<Seq<char>>, k: Seq<Tok>)
    requires
        j <= ts.len(),
        suf(ts, j) == tdots(fs, k),
        nms(fs),
        no_dot(k),
    ensures
        pfs(ts, j) == (fs, (ts.len() - k.len()) as nat),
    decreases fs.len(),
{
    if fs.len() == 0 {
        assert(suf(ts, j) == k);
        hd(ts, j, Seq::<Tok>::empty(), k);
        if j < ts.len() {
            assert(ts[j as int] == k[0]);
        }
    } else {
        let f = fs[0];
        let rest = fs.subrange(1, fs.len() as int);
        tdots_cons(fs, k);
        assert(nms(fs) && ident_ok(f));
        hd(ts, j, seq![Tok::Sym('.'), word_tok(f)], tdots(rest, k));
        assert(word_tok(f) == Tok::Id(f));
        assert(idt(ts, j + 1) == Some(f));
        pfs_complete(ts, j + 2, rest, k);
        assert(seq![f] + rest =~= fs);
    }
}

/// `.IDENT` の列の健全性：読んだ並びは token 列に戻り、名前はすべて IDENT。
pub open spec fn pfs_post(ts: Seq<Tok>, j: nat) -> bool {
    let r = pfs(ts, j);
    j <= r.1 && r.1 <= ts.len() && suf(ts, j) == tdots(r.0, suf(ts, r.1)) && nms(r.0) && ((j + 1 < ts.len() && sym(ts, j, '.') && idt(ts, j + 1) is Some) ==> r.0.len() > 0)
}

pub proof fn pfs_sound(ts: Seq<Tok>, j: nat)
    requires
        j <= ts.len(),
    ensures
        pfs_post(ts, j),
    decreases ts.len() - j,
{
    if j + 1 < ts.len() && sym(ts, j, '.') && idt(ts, j + 1) is Some {
        let f = idt(ts, j + 1)->Some_0;
        assert(ts[j as int] == Tok::Sym('.'));
        assert(ts[(j + 1) as int] == Tok::Id(f));
        assert(ident_ok(f));
        assert(word_tok(f) == Tok::Id(f));
        pfs_sound(ts, j + 2);
        let r2 = pfs(ts, j + 2);
        pfx1(ts, j);
        pfx1(ts, j + 1);
        assert(suf(ts, j) =~= seq![Tok::Sym('.'), word_tok(f)] + suf(ts, j + 2));
        assert(pfs(ts, j) == (seq![f] + r2.0, r2.1));
        tdots_cons(seq![f] + r2.0, suf(ts, r2.1));
        assert((seq![f] + r2.0).subrange(1, (seq![f] + r2.0).len() as int) =~= r2.0);
        assert(suf(ts, j) == tdots(seq![f] + r2.0, suf(ts, r2.1)));
    } else {
        assert(pfs(ts, j) == (Seq::<Seq<char>>::empty(), j));
    }
}

/// 式の完全性（後置を含む）。後置 `.IDENT` の並びは、基本の式の後ろに続く形として読む。
pub proof fn pe_complete(ts: Seq<Tok>, i: nat, d: nat, td: nat, e: Sx, k: Seq<Tok>)
    requires
        pe_pre(ts, i, d, td, e, k),
    ensures
        pe(ts, i, d, td) == Some((e, (ts.len() - k.len()) as nat)),
    decreases d, 4nat, e,
{
    match e {
        Sx::Fld(a, fs) => {
            let k2 = tdots(fs, k);
            tdots_app(fs, k);
            tdots_cons(fs, k);
            assert(!ends_int(e));
            assert(no_dot(k));
            assert(te(e, k) == te(*a, k2));
            te_app(*a, k2);
            pp_complete(ts, i, d, td, *a, k2);
            let j = (ts.len() - k2.len()) as nat;
            at_end(ts, i, te(*a, Seq::<Tok>::empty()), k2);
            hd(ts, j, seq![Tok::Sym('.'), word_tok(fs[0])], tdots(fs.subrange(1, fs.len() as int), k));
            assert(word_tok(fs[0]) == Tok::Id(fs[0]));
            assert(idt(ts, j + 1) == Some(fs[0]));
            pfs_complete(ts, j, fs, k);
            assert(pe(ts, i, d, td) == Some((e, (ts.len() - k.len()) as nat)));
        },
        _ => {
            pp_complete(ts, i, d, td, e, k);
            te_app(e, k);
            at_end(ts, i, te(e, Seq::<Tok>::empty()), k);
            let j = (ts.len() - k.len()) as nat;
            if ends_int(e) {
                reveal_with_fuel(ends_int, 1);
                assert(!recv_ok(e));
            } else {
                assert(no_dot(k));
                if k.len() > 0 {
                    hd(ts, j, k, Seq::<Tok>::empty());
                }
            }
            assert(pe(ts, i, d, td) == Some((e, j)));
        },
    }
}

/// レコード式の base（`..` の後ろの式と `}`）。e はその式の全体。字段と base は深さ d - 1 で読む。
proof fn rec_base_complete(ts: Seq<Tok>, i: nat, d: nat, td: nat, e: Sx, r: Seq<char>, fs: Seq<(Seq<char>, Sx)>, b: Option<Box<Sx>>, k: Seq<Tok>)
    requires
        d > 0,
        e == Sx::Rec(r, fs, b),
        b is Some,
        i <= ts.len(),
        bopt(b, (d - 1) as nat, td),
        suf(ts, i) == seq![Tok::Sym('.'), Tok::Sym('.')] + te(*b->Some_0, seq![Tok::Sym('}')] + k),
    ensures
        prest(ts, i, (d - 1) as nat, td) == Some((Seq::<(Seq<char>, Sx)>::empty(), b, (ts.len() - k.len()) as nat)),
    decreases d, 0nat, e,
{
    let d1 = (d - 1) as nat;
    let x = *b->Some_0;
    let kb = seq![Tok::Sym('}')] + k;
    hd(ts, i, seq![Tok::Sym('.'), Tok::Sym('.')], te(x, kb));
    pe_complete(ts, i + 2, d1, td, x, kb);
    te_app(x, kb);
    at_end(ts, i + 2, te(x, Seq::<Tok>::empty()), kb);
    let p = (ts.len() - kb.len()) as nat;
    hd(ts, p, seq![Tok::Sym('}')], k);
    assert(Some(Box::new(x)) == b);
    assert(prest(ts, i, d1, td) == Some((Seq::<(Seq<char>, Sx)>::empty(), Some(Box::new(x)), (p + 1) as nat)));
}

/// レコード式の字段 fs[j..] を、位置 i から読む。最後の字段の後ろは tl（`, .. base }` か `}`）。d はレコード式の深さで、字段と base は d - 1 で読む。
proof fn rec_fields_complete(ts: Seq<Tok>, i: nat, d: nat, td: nat, e: Sx, r: Seq<char>, fs: Seq<(Seq<char>, Sx)>, b: Option<Box<Sx>>, j: nat, k: Seq<Tok>)
    requires
        d > 0,
        e == Sx::Rec(r, fs, b),
        j < fs.len(),
        i <= ts.len(),
        bfs(fs, j, (d - 1) as nat, td),
        bopt(b, (d - 1) as nat, td),
        suf(ts, i) == tfe(fs, j, rtail(true, b, k)),
    ensures
        prest(ts, i, (d - 1) as nat, td) == Some((fs.subrange(j as int, fs.len() as int), b, (ts.len() - k.len()) as nat)),
    decreases d, 1nat, e, fs.len() - j,
{
    let d1 = (d - 1) as nat;
    let tl = rtail(true, b, k);
    let f = fs[j as int];
    bfs_at(fs, j, d1, td);
    rtail_lead(b, k);
    let last = j + 1 == fs.len();
    let t = if last {
        tl
    } else {
        seq![Tok::Sym(',')] + tfe(fs, j + 1, tl)
    };
    tfe_head(fs, j, tl);
    assert(tfe(fs, j, tl) == seq![word_tok(f.0), Tok::Sym(':')] + te(f.1, t));
    hd(ts, i, seq![word_tok(f.0), Tok::Sym(':')], te(f.1, t));
    assert(word_tok(f.0) == Tok::Id(f.0));
    assert(idt(ts, i) == Some(f.0));
    assert(t.len() > 0 && (t[0] == Tok::Sym(',') || t[0] == Tok::Sym('}')));
    assert(nf(t) && no_dot(t));
    pe_complete(ts, i + 2, d1, td, f.1, t);
    te_app(f.1, t);
    at_end(ts, i + 2, te(f.1, Seq::<Tok>::empty()), t);
    let p = (ts.len() - t.len()) as nat;
    assert(p > i);
    if last {
        match b {
            None => {
                assert(tl == seq![Tok::Sym('}')] + k);
                hd(ts, p, seq![Tok::Sym('}')], k);
                assert(prest(ts, i, d1, td) == Some((seq![(f.0, f.1)], None, (p + 1) as nat)));
                assert(fs.subrange(j as int, fs.len() as int) =~= seq![f]);
            },
            Some(x) => {
                assert(tl == seq![Tok::Sym(',')] + (seq![Tok::Sym('.'), Tok::Sym('.')] + te(*x, seq![Tok::Sym('}')] + k)));
                hd(ts, p, seq![Tok::Sym(',')], seq![Tok::Sym('.'), Tok::Sym('.')] + te(*x, seq![Tok::Sym('}')] + k));
                rec_base_complete(ts, p + 1, d, td, e, r, fs, b, k);
                assert(fs.subrange(j as int, fs.len() as int) =~= seq![f] + Seq::<(Seq<char>, Sx)>::empty());
            },
        }
    } else {
        hd(ts, p, seq![Tok::Sym(',')], tfe(fs, j + 1, tl));
        rec_fields_complete(ts, p + 1, d, td, e, r, fs, b, j + 1, k);
        assert(seq![f] + fs.subrange((j + 1) as int, fs.len() as int) =~= fs.subrange(j as int, fs.len() as int));
    }
}

/// レコード式の完全性。`R {` の後ろが本体の形（rec_head）であることを示し、本体を読む。
proof fn pp_complete_rec(ts: Seq<Tok>, i: nat, d: nat, td: nat, e: Sx, k: Seq<Tok>)
    requires
        pp_pre(ts, i, d, td, e, k),
        e is Rec,
    ensures
        pp(ts, i, d, td) == Some((e, (ts.len() - k.len()) as nat)),
    decreases d, 2nat, e,
{
    if let Sx::Rec(r, fs, b) = e {
        let d1 = (d - 1) as nat;
        let tl = rtail(fs.len() > 0, b, k);
        assert(bx(e, d, td));
        assert(te(e, k) == seq![word_tok(r), Tok::Sym('{')] + tfe(fs, 0, tl));
        hd(ts, i, seq![word_tok(r), Tok::Sym('{')], tfe(fs, 0, tl));
        assert(word_tok(r) == Tok::Id(r));
        assert(ident_ok(r));
        if fs.len() > 0 {
            tfe_head(fs, 0, tl);
            bfs_at(fs, 0, d1, td);
            hd(ts, i + 2, seq![word_tok(fs[0].0), Tok::Sym(':')], te(
                fs[0].1,
                if 0 + 1 == fs.len() {
                    tl
                } else {
                    seq![Tok::Sym(',')] + tfe(fs, 1, tl)
                },
            ));
            assert(word_tok(fs[0].0) == Tok::Id(fs[0].0));
            assert(idt(ts, i + 2) == Some(fs[0].0));
            rec_fields_complete(ts, i + 2, d, td, e, r, fs, b, 0, k);
            assert(fs.subrange(0, fs.len() as int) =~= fs);
            reveal_with_fuel(prec, 1);
            reveal_with_fuel(pp, 1);
            assert(prec(ts, i + 2, d1, td) == Some((fs, b, (ts.len() - k.len()) as nat)));
            assert(pp(ts, i, d, td) == Some((e, (ts.len() - k.len()) as nat)));
        } else {
            assert(tfe(fs, 0, tl) == tl);
            assert(fs =~= Seq::<(Seq<char>, Sx)>::empty());
            match b {
                None => {
                    assert(tl == seq![Tok::Sym('}')] + k);
                    hd(ts, i + 2, seq![Tok::Sym('}')], k);
                    reveal_with_fuel(prec, 1);
                    reveal_with_fuel(pp, 1);
                    assert(prec(ts, i + 2, d1, td) == Some((fs, b, (ts.len() - k.len()) as nat)));
                    assert(pp(ts, i, d, td) == Some((e, (ts.len() - k.len()) as nat)));
                },
                Some(x) => {
                    assert(tl == seq![Tok::Sym('.'), Tok::Sym('.')] + te(*x, seq![Tok::Sym('}')] + k));
                    hd(ts, i + 2, seq![Tok::Sym('.'), Tok::Sym('.')], te(*x, seq![Tok::Sym('}')] + k));
                    rec_base_complete(ts, i + 2, d, td, e, r, fs, b, k);
                    reveal_with_fuel(prec, 1);
                    reveal_with_fuel(pp, 1);
                    assert(prec(ts, i + 2, d1, td) == Some((fs, b, (ts.len() - k.len()) as nat)));
                    assert(pp(ts, i, d, td) == Some((e, (ts.len() - k.len()) as nat)));
                },
            }
        }
    }
}

/// 型の字段の並び fs[j..] を、位置 i から読む（閉じ括弧は tail に含む）。
proof fn pfds_complete(ts: Seq<Tok>, i: nat, td: nat, fs: Seq<(Seq<char>, Ty)>, j: nat, tc: bool, k: Seq<Tok>)
    requires
        j < fs.len(),
        i <= ts.len(),
        bfds(fs, j, td),
        suf(ts, i) == tfd(fs, j, tc, seq![Tok::Sym('}')] + k),
    ensures
        pfds(ts, i, td) == Some((fs.subrange(j as int, fs.len() as int), tc, (ts.len() - k.len()) as nat)),
    decreases fs.len() - j,
{
    let kb = seq![Tok::Sym('}')] + k;
    let f = fs[j as int];
    bfds_at(fs, j, td);
    let last = j + 1 == fs.len();
    let t = if last {
        if tc {
            seq![Tok::Sym(',')] + kb
        } else {
            kb
        }
    } else {
        seq![Tok::Sym(',')] + tfd(fs, j + 1, tc, kb)
    };
    tfd_head(fs, j, tc, kb);
    assert(tfd(fs, j, tc, kb) == seq![word_tok(f.0), Tok::Sym(':')] + tt(f.1, t));
    hd(ts, i, seq![word_tok(f.0), Tok::Sym(':')], tt(f.1, t));
    assert(word_tok(f.0) == Tok::Id(f.0));
    assert(idt(ts, i) == Some(f.0));
    pt_complete(ts, i + 2, td, f.1, t);
    tt_app(f.1, t);
    at_end(ts, i + 2, tt(f.1, Seq::<Tok>::empty()), t);
    let p = (ts.len() - t.len()) as nat;
    assert(p > i);
    if last {
        if tc {
            hd(ts, p, seq![Tok::Sym(',')], kb);
            hd(ts, p + 1, seq![Tok::Sym('}')], k);
            assert(fs.subrange(j as int, fs.len() as int) =~= seq![f]);
        } else {
            hd(ts, p, seq![Tok::Sym('}')], k);
        }
    } else {
        hd(ts, p, seq![Tok::Sym(',')], tfd(fs, j + 1, tc, kb));
        tfd_head(fs, j + 1, tc, kb);
        hd(ts, p + 1, seq![word_tok(fs[(j + 1) as int].0), Tok::Sym(':')], tt(
            fs[(j + 1) as int].1,
            if j + 2 == fs.len() {
                if tc {
                    seq![Tok::Sym(',')] + kb
                } else {
                    kb
                }
            } else {
                seq![Tok::Sym(',')] + tfd(fs, j + 2, tc, kb)
            },
        ));
        assert(word_tok(fs[(j + 1) as int].0) == Tok::Id(fs[(j + 1) as int].0));
        pfds_complete(ts, p + 1, td, fs, j + 1, tc, k);
        assert(seq![f] + fs.subrange((j + 1) as int, fs.len() as int) =~= fs.subrange(j as int, fs.len() as int));
    }
}

/// 基本の式の完全性（後置を含まない）。Let は本体の後ろに後置が付かないことを要する。
pub proof fn pp_complete(ts: Seq<Tok>, i: nat, d: nat, td: nat, e: Sx, k: Seq<Tok>)
    requires
        pp_pre(ts, i, d, td, e, k),
        e is Let ==> (no_dot(k) || ends_int(e)),
    ensures
        pp(ts, i, d, td) == Some((e, (ts.len() - k.len()) as nat)),
    decreases d, 3nat, e,
{
    match e {
        Sx::Int(n) => hd(ts, i, seq![Tok::Int(n)], k),
        Sx::Chr(c) => hd(ts, i, seq![Tok::Chr(c)], k),
        Sx::Str(w) => hd(ts, i, seq![Tok::Str(w)], k),
        Sx::Bool(b) => hd(ts, i, seq![Tok::Kw(if b { Kw::True } else { Kw::False })], k),
        Sx::Unit => hd(ts, i, seq![Tok::Kw(Kw::Unit)], k),
        Sx::Var(x) => {
            hd(ts, i, seq![word_tok(x)], k);
            if kw_of(x) is Some {
                kw_inv(x);
            }
            if k.len() > 0 {
                assert(k =~= seq![k[0]] + k.subrange(1, k.len() as int));
                hd(ts, i + 1, seq![k[0]], k.subrange(1, k.len() as int));
            }
        },
        Sx::List(..) => pp_complete_list(ts, i, d, td, e, k),
        Sx::Some(..) => pp_complete_some(ts, i, d, td, e, k),
        Sx::None(..) => pp_complete_none(ts, i, d, td, e, k),
        Sx::Pair(..) => pp_complete_pair(ts, i, d, td, e, k),
        Sx::Builtin(..) => pp_complete_builtin(ts, i, d, td, e, k),
        Sx::Call(..) => pp_complete_call(ts, i, d, td, e, k),
        Sx::Let(..) => pp_complete_let(ts, i, d, td, e, k),
        Sx::If(..) => pp_complete_if(ts, i, d, td, e, k),
        Sx::Fold(..) => pp_complete_fold(ts, i, d, td, e, k),
        Sx::Match(..) => pp_complete_match(ts, i, d, td, e, k),
        Sx::Inj(..) => pp_complete_inj(ts, i, d, td, e, k),
        Sx::MatchR(..) => pp_complete_matchr(ts, i, d, td, e, k),
        Sx::Fld(..) => {},
        Sx::Rec(..) => pp_complete_rec(ts, i, d, td, e, k),
    }
}

proof fn pp_complete_inj(ts: Seq<Tok>, i: nat, d: nat, td: nat, e: Sx, k: Seq<Tok>)
    requires
        pp_pre(ts, i, d, td, e, k),
        e is Inj,
    ensures
        pp(ts, i, d, td) == Some((e, (ts.len() - k.len()) as nat)),
    decreases d, 2nat, e,
{
    if let Sx::Inj(ok, t, u, a) = e {
        let z = Seq::<Tok>::empty();
        let d1 = (d - 1) as nat;
        let kw = if ok { Kw::Ok } else { Kw::Err };
        let ka = seq![Tok::Sym(')')] + k;
        let ku = seq![Tok::Sym('>'), Tok::Sym('(')] + te(*a, ka);
        let kt = seq![Tok::Sym(',')] + tt(u, ku);
        hd(ts, i, seq![Tok::Kw(kw), Tok::Sym('<')], tt(t, kt));
        pt_complete(ts, i + 2, td, t, kt);
        tt_app(t, kt);
        at_end(ts, i + 2, tt(t, z), kt);
        let j = (ts.len() - kt.len()) as nat;
        hd(ts, j, seq![Tok::Sym(',')], tt(u, ku));
        pt_complete(ts, j + 1, td, u, ku);
        tt_app(u, ku);
        at_end(ts, j + 1, tt(u, z), ku);
        let m = (ts.len() - ku.len()) as nat;
        hd(ts, m, seq![Tok::Sym('>'), Tok::Sym('(')], te(*a, ka));
        pe_complete(ts, m + 2, d1, td, *a, ka);
        te_app(*a, ka);
        at_end(ts, m + 2, te(*a, z), ka);
        hd(ts, (ts.len() - ka.len()) as nat, seq![Tok::Sym(')')], k);
    }
}

proof fn pp_complete_matchr(ts: Seq<Tok>, i: nat, d: nat, td: nat, e: Sx, k: Seq<Tok>)
    requires
        pp_pre(ts, i, d, td, e, k),
        e is MatchR,
    ensures
        pp(ts, i, d, td) == Some((e, (ts.len() - k.len()) as nat)),
    decreases d, 2nat, e,
{
    if let Sx::MatchR(m, x, a, y, b) = e {
        let z = Seq::<Tok>::empty();
        let d1 = (d - 1) as nat;
        let kb = seq![Tok::Sym(')')] + k;
        let my = seq![Tok::Sym(','), Tok::Sym('|'), word_tok(y), Tok::Sym('|')];
        let mx = seq![Tok::Sym(','), Tok::Sym('|'), word_tok(x), Tok::Sym('|')];
        let ka = my + te(*b, kb);
        let km = mx + te(*a, ka);
        hd(ts, i, seq![Tok::Kw(Kw::MatchResult), Tok::Sym('(')], te(*m, km));
        pe_complete(ts, i + 2, d1, td, *m, km);
        te_app(*m, km);
        at_end(ts, i + 2, te(*m, z), km);
        let j = (ts.len() - km.len()) as nat;
        hd(ts, j, mx, te(*a, ka));
        assert(ts[j + 0 as int] == mx[0]);
        assert(ts[j + 1 as int] == mx[1]);
        assert(ts[j + 2 as int] == mx[2]);
        assert(ts[j + 3 as int] == mx[3]);
        bdt_word(ts, j + 2, x);
        assert(ka[0] == Tok::Sym(','));
        pe_complete(ts, j + 4, d1, td, *a, ka);
        te_app(*a, ka);
        at_end(ts, j + 4, te(*a, z), ka);
        let q = (ts.len() - ka.len()) as nat;
        hd(ts, q, my, te(*b, kb));
        assert(ts[q + 0 as int] == my[0]);
        assert(ts[q + 1 as int] == my[1]);
        assert(ts[q + 2 as int] == my[2]);
        assert(ts[q + 3 as int] == my[3]);
        bdt_word(ts, q + 2, y);
        pe_complete(ts, q + 4, d1, td, *b, kb);
        te_app(*b, kb);
        at_end(ts, q + 4, te(*b, z), kb);
        hd(ts, (ts.len() - kb.len()) as nat, seq![Tok::Sym(')')], k);
    }
}

proof fn pp_complete_list(ts: Seq<Tok>, i: nat, d: nat, td: nat, e: Sx, k: Seq<Tok>)
    requires
        pp_pre(ts, i, d, td, e, k),
        e is List,
    ensures
        pp(ts, i, d, td) == Some((e, (ts.len() - k.len()) as nat)),
    decreases d, 2nat, e,
{
    if let Sx::List(t, es) = e {
        let z = Seq::<Tok>::empty();
        let ka = seq![Tok::Sym('>'), Tok::Sym('(')] + targs(es, 0, k);
        hd(ts, i, seq![Tok::Kw(Kw::List), Tok::Sym('<')], tt(t, ka));
        pt_complete(ts, i + 2, td, t, ka);
        tt_app(t, ka);
        at_end(ts, i + 2, tt(t, z), ka);
        let j = (ts.len() - ka.len()) as nat;
        hd(ts, j, seq![Tok::Sym('>'), Tok::Sym('(')], targs(es, 0, k));
        pargs_complete(ts, j + 2, (d - 1) as nat, td, es, k);
    }
}

proof fn pp_complete_some(ts: Seq<Tok>, i: nat, d: nat, td: nat, e: Sx, k: Seq<Tok>)
    requires
        pp_pre(ts, i, d, td, e, k),
        e is Some,
    ensures
        pp(ts, i, d, td) == Some((e, (ts.len() - k.len()) as nat)),
    decreases d, 2nat, e,
{
    if let Sx::Some(a) = e {
        let z = Seq::<Tok>::empty();
        let ka = seq![Tok::Sym(')')] + k;
        hd(ts, i, seq![Tok::Kw(Kw::Some), Tok::Sym('(')], te(*a, ka));
        pe_complete(ts, i + 2, (d - 1) as nat, td, *a, ka);
        te_app(*a, ka);
        at_end(ts, i + 2, te(*a, z), ka);
        hd(ts, (ts.len() - ka.len()) as nat, seq![Tok::Sym(')')], k);
    }
}

proof fn pp_complete_none(ts: Seq<Tok>, i: nat, d: nat, td: nat, e: Sx, k: Seq<Tok>)
    requires
        pp_pre(ts, i, d, td, e, k),
        e is None,
    ensures
        pp(ts, i, d, td) == Some((e, (ts.len() - k.len()) as nat)),
    decreases d, 2nat, e,
{
    if let Sx::None(t) = e {
        let z = Seq::<Tok>::empty();
        let ka = seq![Tok::Sym('>'), Tok::Sym('('), Tok::Sym(')')] + k;
        hd(ts, i, seq![Tok::Kw(Kw::None), Tok::Sym('<')], tt(t, ka));
        pt_complete(ts, i + 2, td, t, ka);
        tt_app(t, ka);
        at_end(ts, i + 2, tt(t, z), ka);
        let j = (ts.len() - ka.len()) as nat;
        hd(ts, j, seq![Tok::Sym('>'), Tok::Sym('('), Tok::Sym(')')], k);
        assert(ts[j + 0 as int] == Tok::Sym('>'));
        assert(ts[j + 1 as int] == Tok::Sym('('));
        assert(ts[j + 2 as int] == Tok::Sym(')'));
    }
}

proof fn pp_complete_pair(ts: Seq<Tok>, i: nat, d: nat, td: nat, e: Sx, k: Seq<Tok>)
    requires
        pp_pre(ts, i, d, td, e, k),
        e is Pair,
    ensures
        pp(ts, i, d, td) == Some((e, (ts.len() - k.len()) as nat)),
    decreases d, 2nat, e,
{
    if let Sx::Pair(a, b) = e {
        let z = Seq::<Tok>::empty();
        let d1 = (d - 1) as nat;
        let kb = seq![Tok::Sym(')')] + k;
        let ka = seq![Tok::Sym(',')] + te(*b, kb);
        hd(ts, i, seq![Tok::Kw(Kw::Pair), Tok::Sym('(')], te(*a, ka));
        pe_complete(ts, i + 2, d1, td, *a, ka);
        te_app(*a, ka);
        at_end(ts, i + 2, te(*a, z), ka);
        let j = (ts.len() - ka.len()) as nat;
        hd(ts, j, seq![Tok::Sym(',')], te(*b, kb));
        pe_complete(ts, j + 1, d1, td, *b, kb);
        te_app(*b, kb);
        at_end(ts, j + 1, te(*b, z), kb);
        hd(ts, (ts.len() - kb.len()) as nat, seq![Tok::Sym(')')], k);
    }
}

proof fn pp_complete_builtin(ts: Seq<Tok>, i: nat, d: nat, td: nat, e: Sx, k: Seq<Tok>)
    requires
        pp_pre(ts, i, d, td, e, k),
        e is Builtin,
    ensures
        pp(ts, i, d, td) == Some((e, (ts.len() - k.len()) as nat)),
    decreases d, 2nat, e,
{
    if let Sx::Builtin(b, es) = e {
        hd(ts, i, seq![Tok::Kw(bkw(b)), Tok::Sym('(')], targs(es, 0, k));
        pargs_complete(ts, i + 2, (d - 1) as nat, td, es, k);
        assert(kw_b(bkw(b)) == Some(b));
    }
}

proof fn pp_complete_call(ts: Seq<Tok>, i: nat, d: nat, td: nat, e: Sx, k: Seq<Tok>)
    requires
        pp_pre(ts, i, d, td, e, k),
        e is Call,
    ensures
        pp(ts, i, d, td) == Some((e, (ts.len() - k.len()) as nat)),
    decreases d, 2nat, e,
{
    if let Sx::Call(f, es) = e {
        hd(ts, i, seq![Tok::Id(f), Tok::Sym('(')], targs(es, 0, k));
        pargs_complete(ts, i + 2, (d - 1) as nat, td, es, k);
    }
}

proof fn pp_complete_let(ts: Seq<Tok>, i: nat, d: nat, td: nat, e: Sx, k: Seq<Tok>)
    requires
        pp_pre(ts, i, d, td, e, k),
        no_dot(k) || ends_int(e),
        e is Let,
    ensures
        pp(ts, i, d, td) == Some((e, (ts.len() - k.len()) as nat)),
    decreases d, 2nat, e,
{
    if let Sx::Let(x, a, b) = e {
        let z = Seq::<Tok>::empty();
        let d1 = (d - 1) as nat;
        let ka = seq![Tok::Kw(Kw::In)] + te(*b, k);
        hd(ts, i, seq![Tok::Kw(Kw::Let), word_tok(x), Tok::Sym('=')], te(*a, ka));
        bdt_word(ts, i + 1, x);
        pe_complete(ts, i + 3, d1, td, *a, ka);
        te_app(*a, ka);
        at_end(ts, i + 3, te(*a, z), ka);
        let j = (ts.len() - ka.len()) as nat;
        hd(ts, j, seq![Tok::Kw(Kw::In)], te(*b, k));
        pe_complete(ts, j + 1, d1, td, *b, k);
    }
}

proof fn pp_complete_if(ts: Seq<Tok>, i: nat, d: nat, td: nat, e: Sx, k: Seq<Tok>)
    requires
        pp_pre(ts, i, d, td, e, k),
        e is If,
    ensures
        pp(ts, i, d, td) == Some((e, (ts.len() - k.len()) as nat)),
    decreases d, 2nat, e,
{
    if let Sx::If(c, a, b) = e {
        let z = Seq::<Tok>::empty();
        let d1 = (d - 1) as nat;
        let kb = seq![Tok::Sym(')')] + k;
        let ka = seq![Tok::Sym(',')] + te(*b, kb);
        let kc = seq![Tok::Sym(',')] + te(*a, ka);
        hd(ts, i, seq![Tok::Kw(Kw::If), Tok::Sym('(')], te(*c, kc));
        pe_complete(ts, i + 2, d1, td, *c, kc);
        te_app(*c, kc);
        at_end(ts, i + 2, te(*c, z), kc);
        let j = (ts.len() - kc.len()) as nat;
        hd(ts, j, seq![Tok::Sym(',')], te(*a, ka));
        pe_complete(ts, j + 1, d1, td, *a, ka);
        te_app(*a, ka);
        at_end(ts, j + 1, te(*a, z), ka);
        let m = (ts.len() - ka.len()) as nat;
        hd(ts, m, seq![Tok::Sym(',')], te(*b, kb));
        pe_complete(ts, m + 1, d1, td, *b, kb);
        te_app(*b, kb);
        at_end(ts, m + 1, te(*b, z), kb);
        hd(ts, (ts.len() - kb.len()) as nat, seq![Tok::Sym(')')], k);
    }
}

proof fn pp_complete_fold(ts: Seq<Tok>, i: nat, d: nat, td: nat, e: Sx, k: Seq<Tok>)
    requires
        pp_pre(ts, i, d, td, e, k),
        e is Fold,
    ensures
        pp(ts, i, d, td) == Some((e, (ts.len() - k.len()) as nat)),
    decreases d, 2nat, e,
{
    if let Sx::Fold(l, n, a, x, b) = e {
        let z = Seq::<Tok>::empty();
        let d1 = (d - 1) as nat;
        let kb = seq![Tok::Sym(')')] + k;
        let mid = seq![Tok::Sym(','), Tok::Sym('|'), word_tok(a), Tok::Sym(','), word_tok(x), Tok::Sym('|')];
        let kn = mid + te(*b, kb);
        let kl = seq![Tok::Sym(',')] + te(*n, kn);
        hd(ts, i, seq![Tok::Kw(Kw::Fold), Tok::Sym('(')], te(*l, kl));
        pe_complete(ts, i + 2, d1, td, *l, kl);
        te_app(*l, kl);
        at_end(ts, i + 2, te(*l, z), kl);
        let j = (ts.len() - kl.len()) as nat;
        hd(ts, j, seq![Tok::Sym(',')], te(*n, kn));
        assert(kn[0] == Tok::Sym(','));
        pe_complete(ts, j + 1, d1, td, *n, kn);
        te_app(*n, kn);
        at_end(ts, j + 1, te(*n, z), kn);
        let m = (ts.len() - kn.len()) as nat;
        hd(ts, m, mid, te(*b, kb));
        assert(ts[m + 0 as int] == mid[0]);
        assert(ts[m + 1 as int] == mid[1]);
        assert(ts[m + 2 as int] == mid[2]);
        assert(ts[m + 3 as int] == mid[3]);
        assert(ts[m + 4 as int] == mid[4]);
        assert(ts[m + 5 as int] == mid[5]);
        bdt_word(ts, m + 2, a);
        bdt_word(ts, m + 4, x);
        pe_complete(ts, m + 6, d1, td, *b, kb);
        te_app(*b, kb);
        at_end(ts, m + 6, te(*b, z), kb);
        hd(ts, (ts.len() - kb.len()) as nat, seq![Tok::Sym(')')], k);
    }
}

proof fn pp_complete_match(ts: Seq<Tok>, i: nat, d: nat, td: nat, e: Sx, k: Seq<Tok>)
    requires
        pp_pre(ts, i, d, td, e, k),
        e is Match,
    ensures
        pp(ts, i, d, td) == Some((e, (ts.len() - k.len()) as nat)),
    decreases d, 2nat, e,
{
    if let Sx::Match(m, n, x, b) = e {
        let z = Seq::<Tok>::empty();
        let d1 = (d - 1) as nat;
        let kb = seq![Tok::Sym(')')] + k;
        let mid = seq![Tok::Sym(','), Tok::Sym('|'), word_tok(x), Tok::Sym('|')];
        let kn = mid + te(*b, kb);
        let km = seq![Tok::Sym(',')] + te(*n, kn);
        hd(ts, i, seq![Tok::Kw(Kw::MatchOption), Tok::Sym('(')], te(*m, km));
        pe_complete(ts, i + 2, d1, td, *m, km);
        te_app(*m, km);
        at_end(ts, i + 2, te(*m, z), km);
        let j = (ts.len() - km.len()) as nat;
        hd(ts, j, seq![Tok::Sym(',')], te(*n, kn));
        assert(kn[0] == Tok::Sym(','));
        pe_complete(ts, j + 1, d1, td, *n, kn);
        te_app(*n, kn);
        at_end(ts, j + 1, te(*n, z), kn);
        let q = (ts.len() - kn.len()) as nat;
        hd(ts, q, mid, te(*b, kb));
        assert(ts[q + 0 as int] == mid[0]);
        assert(ts[q + 1 as int] == mid[1]);
        assert(ts[q + 2 as int] == mid[2]);
        assert(ts[q + 3 as int] == mid[3]);
        bdt_word(ts, q + 2, x);
        pe_complete(ts, q + 4, d1, td, *b, kb);
        te_app(*b, kb);
        at_end(ts, q + 4, te(*b, z), kb);
        hd(ts, (ts.len() - kb.len()) as nat, seq![Tok::Sym(')')], k);
    }
}

pub proof fn pargs_complete(ts: Seq<Tok>, i: nat, d: nat, td: nat, es: Seq<Sx>, k: Seq<Tok>)
    requires
        i <= ts.len(),
        suf(ts, i) == targs(es, 0, k),
        bxs(es, 0, d, td),
    ensures
        pargs(ts, i, d, td) == Some((es, (ts.len() - k.len()) as nat)),
    decreases d, 6nat, es, es.len() + 1,
{
    if es.len() == 0 {
        hd(ts, i, seq![Tok::Sym(')')], k);
        assert(es =~= Seq::<Sx>::empty());
    } else {
        targs_app(es, 0, Seq::empty());
        targs_app(es, 0, k);
        hd(ts, i, targs(es, 0, Seq::empty()), k);
        assert(ts[i as int] == targs(es, 0, Seq::empty())[0]);
        pargs1_complete(ts, i, d, td, es, 0, k);
        assert(es.subrange(0, es.len() as int) =~= es);
    }
}

pub proof fn pargs1_complete(ts: Seq<Tok>, i: nat, d: nat, td: nat, es: Seq<Sx>, j: nat, k: Seq<Tok>)
    requires
        i <= ts.len(),
        j < es.len(),
        suf(ts, i) == targs(es, j, k),
        bxs(es, j, d, td),
    ensures
        pargs1(ts, i, d, td) == Some((es.subrange(j as int, es.len() as int), (ts.len() - k.len()) as nat)),
    decreases d, 5nat, es, es.len() - j,
{
    let z = Seq::<Tok>::empty();
    let e = es[j as int];
    if j + 1 == es.len() {
        let ka = seq![Tok::Sym(')')] + k;
        pe_complete(ts, i, d, td, e, ka);
        te_app(e, ka);
        at_end(ts, i, te(e, z), ka);
        hd(ts, (ts.len() - ka.len()) as nat, seq![Tok::Sym(')')], k);
        assert(es.subrange(j as int, es.len() as int) =~= seq![e]);
    } else {
        let ka = seq![Tok::Sym(',')] + targs(es, j + 1, k);
        pe_complete(ts, i, d, td, e, ka);
        te_app(e, ka);
        at_end(ts, i, te(e, z), ka);
        let m = (ts.len() - ka.len()) as nat;
        hd(ts, m, seq![Tok::Sym(',')], targs(es, j + 1, k));
        pargs1_complete(ts, m + 1, d, td, es, j + 1, k);
        assert(es.subrange(j as int, es.len() as int) =~= seq![e] + es.subrange((j + 1) as int, es.len() as int));
    }
}

pub proof fn pparams1_complete(ts: Seq<Tok>, i: nat, td: nat, ps: Seq<(Seq<char>, Ty)>, j: nat, k: Seq<Tok>)
    requires
        i <= ts.len(),
        j < ps.len(),
        suf(ts, i) == tps(ps, j, k),
        bps(ps, j, td),
    ensures
        pparams1(ts, i, td) == Some((ps.subrange(j as int, ps.len() as int), (ts.len() - k.len()) as nat)),
    decreases ps.len() - j,
{
    let z = Seq::<Tok>::empty();
    let (x, t) = ps[j as int];
    let kt = if j + 1 == ps.len() {
        seq![Tok::Sym(')')] + k
    } else {
        seq![Tok::Sym(',')] + tps(ps, j + 1, k)
    };
    hd(ts, i, seq![word_tok(x), Tok::Sym(':')], tt(t, kt));
    bdt_word(ts, i, x);
    pt_complete(ts, i + 2, td, t, kt);
    tt_app(t, kt);
    at_end(ts, i + 2, tt(t, z), kt);
    let m = (ts.len() - kt.len()) as nat;
    if j + 1 == ps.len() {
        hd(ts, m, seq![Tok::Sym(')')], k);
        assert(ps.subrange(j as int, ps.len() as int) =~= seq![(x, t)]);
    } else {
        hd(ts, m, seq![Tok::Sym(',')], tps(ps, j + 1, k));
        pparams1_complete(ts, m + 1, td, ps, j + 1, k);
        assert(ps.subrange(j as int, ps.len() as int) =~= seq![(x, t)] + ps.subrange((j + 1) as int, ps.len() as int));
    }
}

pub proof fn pparams_complete(ts: Seq<Tok>, i: nat, td: nat, ps: Seq<(Seq<char>, Ty)>, k: Seq<Tok>)
    requires
        i <= ts.len(),
        suf(ts, i) == tps(ps, 0, k),
        bps(ps, 0, td),
    ensures
        pparams(ts, i, td) == Some((ps, (ts.len() - k.len()) as nat)),
{
    if ps.len() == 0 {
        hd(ts, i, seq![Tok::Sym(')')], k);
        assert(ps =~= Seq::<(Seq<char>, Ty)>::empty());
    } else {
        let kt = if 1 == ps.len() {
            seq![Tok::Sym(')')] + k
        } else {
            seq![Tok::Sym(',')] + tps(ps, 1, k)
        };
        hd(ts, i, seq![word_tok(ps[0].0), Tok::Sym(':')], tt(ps[0].1, kt));
        pparams1_complete(ts, i, td, ps, 0, k);
        assert(ps.subrange(0, ps.len() as int) =~= ps);
    }
}

/// 宣言の後ろの token 列は、直和の区切り `|` と型の区切り `,` で始まらない（空でもよい）。
pub open spec fn no_sep(k: Seq<Tok>) -> bool {
    k.len() == 0 || (k[0] != Tok::Sym('|') && k[0] != Tok::Sym(','))
}

/// 型の並び ps[j..] を位置 i から読む（閉じ括弧は k に含み、k は `,` で始まらない）。
pub proof fn ptys_complete(ts: Seq<Tok>, i: nat, td: nat, ps: Seq<Ty>, j: nat, k: Seq<Tok>)
    requires
        j < ps.len(),
        i <= ts.len(),
        bts(ps, j, td),
        suf(ts, i) == tts(ps, j, k),
        no_sep(k),
    ensures
        ptys(ts, i, td) == Some((ps.subrange(j as int, ps.len() as int), (ts.len() - k.len()) as nat)),
    decreases ps.len() - j,
{
    bts_at(ps, j, td);
    let t = ps[j as int];
    let last = j + 1 == ps.len();
    let kt = if last { k } else { seq![Tok::Sym(',')] + tts(ps, j + 1, k) };
    tts_head(ps, j, k);
    tt_app(t, kt);
    pt_complete(ts, i, td, t, kt);
    at_end(ts, i, tt(t, Seq::<Tok>::empty()), kt);
    let p = (ts.len() - kt.len()) as nat;
    assert(i < p);
    if last {
        assert(!sym(ts, p, ','));
        assert(ps.subrange(j as int, ps.len() as int) =~= seq![t]);
    } else {
        hd(ts, p, seq![Tok::Sym(',')], tts(ps, j + 1, k));
        ptys_complete(ts, p + 1, td, ps, j + 1, k);
        assert(ps.subrange(j as int, ps.len() as int) =~= seq![t] + ps.subrange((j + 1) as int, ps.len() as int));
    }
}

/// 構築子 `C` か `C(T, ...)` を位置 i から読む（後ろの続き k。中身が空なら k は `(` で始まらない）。
pub proof fn pvar_complete(ts: Seq<Tok>, i: nat, td: nat, c: Seq<char>, ps: Seq<Ty>, k: Seq<Tok>)
    requires
        i <= ts.len(),
        cname_ok(c),
        bts(ps, 0, td),
        suf(ts, i) == seq![Tok::Id(c)] + tpay(ps, k),
        nf(k),
    ensures
        pvar(ts, i, td) == Some((c, ps, (ts.len() - k.len()) as nat)),
        i < (ts.len() - k.len()) as nat,
        suf(ts, (ts.len() - k.len()) as nat) == k,
{
    tpay_app(ps, k);
    hd(ts, i, seq![Tok::Id(c)], tpay(ps, k));
    assert(idt(ts, i) == Some(c));
    assert(cidt(ts, i) == Some(c));
    if ps.len() == 0 {
        assert(tpay(ps, k) == k);
        assert(ps =~= Seq::<Ty>::empty());
        if k.len() > 0 {
            pfx1(ts, i + 1);
            assert(k[0] == ts[(i + 1) as int]);
        }
        assert(!sym(ts, i + 1, '('));
        assert((ts.len() - k.len()) as nat == i + 1);
        assert(suf(ts, (ts.len() - k.len()) as nat) == k);
    } else {
        let kc = seq![Tok::Sym(')')] + k;
        assert(seq![Tok::Id(c)] + tpay(ps, k) =~= seq![Tok::Id(c), Tok::Sym('(')] + tts(ps, 0, kc));
        hd(ts, i, seq![Tok::Id(c), Tok::Sym('(')], tts(ps, 0, kc));
        ptys_complete(ts, i + 2, td, ps, 0, kc);
        assert(ps.subrange(0, ps.len() as int) =~= ps);
        tts_app(ps, 0, kc);
        at_end(ts, i + 2, tts(ps, 0, Seq::<Tok>::empty()), kc);
        hd(ts, (ts.len() - kc.len()) as nat, seq![Tok::Sym(')')], k);
        assert(sym(ts, (ts.len() - kc.len()) as nat, ')'));
        assert((ts.len() - k.len()) as nat == (ts.len() - kc.len()) as nat + 1);
        assert(suf(ts, (ts.len() - k.len()) as nat) == k);
    }
}

/// 直和型の構築子の並び vs[j..] を位置 i から読む（後ろの続き k は `|` で始まらない）。
pub proof fn pvars_complete(ts: Seq<Tok>, i: nat, td: nat, vs: Seq<(Seq<char>, Seq<Ty>)>, j: nat, k: Seq<Tok>)
    requires
        j < vs.len(),
        i <= ts.len(),
        bvars(vs, j, td),
        suf(ts, i) == tvars(vs, j, k),
        nf(k),
        no_sep(k),
    ensures
        pvars(ts, i, td) == Some((vs.subrange(j as int, vs.len() as int), (ts.len() - k.len()) as nat)),
    decreases vs.len() - j,
{
    bvars_at(vs, j, td);
    let x = vs[j as int];
    let last = j + 1 == vs.len();
    let kv = if last { k } else { seq![Tok::Sym('|')] + tvars(vs, j + 1, k) };
    tvars_head(vs, j, k);
    assert(word_tok(x.0) == Tok::Id(x.0));
    assert(nf(kv)) by {
        if !last {
            assert(kv[0] == Tok::Sym('|'));
        }
    }
    pvar_complete(ts, i, td, x.0, x.1, kv);
    let p = (ts.len() - kv.len()) as nat;
    if last {
        assert(!sym(ts, p, '|'));
        assert(vs.subrange(j as int, vs.len() as int) =~= seq![x]);
    } else {
        hd(ts, p, seq![Tok::Sym('|')], tvars(vs, j + 1, k));
        pvars_complete(ts, p + 1, td, vs, j + 1, k);
        assert(vs.subrange(j as int, vs.len() as int) =~= seq![x] + vs.subrange((j + 1) as int, vs.len() as int));
    }
}

pub proof fn pd_complete(ts: Seq<Tok>, i: nat, d: nat, td: nat, x: Sd, k: Seq<Tok>)
    requires
        i <= ts.len(),
        suf(ts, i) == tdecl(x, k),
        bd(x, d, td),
        nf(k),
        no_dot(k),
        no_sep(k),
    ensures
        pd(ts, i, d, td) == Some((x, (ts.len() - k.len()) as nat)),
{
    let z = Seq::<Tok>::empty();
    match x {
        Sd::Fn(f, ps, r, b) => {
            let kb = te(b, k);
            let kr = seq![Tok::Sym('=')] + kb;
            let kp = seq![Tok::Arrow] + tt(r, kr);
            hd(ts, i, seq![Tok::Kw(Kw::Fn), Tok::Id(f), Tok::Sym('(')], tps(ps, 0, kp));
            assert(idt(ts, i + 1) == Some(f));
            pparams_complete(ts, i + 3, td, ps, kp);
            tps_app(ps, 0, kp);
            at_end(ts, i + 3, tps(ps, 0, z), kp);
            let j = (ts.len() - kp.len()) as nat;
            hd(ts, j, seq![Tok::Arrow], tt(r, kr));
            pt_complete(ts, j + 1, td, r, kr);
            tt_app(r, kr);
            at_end(ts, j + 1, tt(r, z), kr);
            let m = (ts.len() - kr.len()) as nat;
            hd(ts, m, seq![Tok::Sym('=')], kb);
            pe_complete(ts, m + 1, d, td, b, k);
        },
        Sd::Entry(n) => {
            hd(ts, i, seq![Tok::Kw(Kw::Entry), Tok::Id(n)], k);
            assert(idt(ts, i + 1) == Some(n));
        },
        Sd::RecTy(r, fs, tc) => {
            let kb = seq![Tok::Sym('}')] + k;
            hd(ts, i, seq![Tok::Id(tyw()), word_tok(r), Tok::Sym('='), Tok::Sym('{')], tfd(fs, 0, tc, kb));
            assert(word_tok(r) == Tok::Id(r));
            assert(idt(ts, i + 1) == Some(r));
            pfds_complete(ts, i + 4, td, fs, 0, tc, k);
            assert(fs.subrange(0, fs.len() as int) =~= fs);
        },
        Sd::Sum(r, vs) => {
            hd(ts, i, seq![Tok::Id(tyw()), word_tok(r), Tok::Sym('=')], tvars(vs, 0, k));
            assert(word_tok(r) == Tok::Id(r));
            assert(idt(ts, i + 1) == Some(r));
            tvars_head(vs, 0, k);
            assert(word_tok(vs[0].0) == Tok::Id(vs[0].0));
            let tv = tvars(vs, 0, k);
            assert(suf(ts, (i + 3) as nat) == tv);
            assert(tv[0] == Tok::Id(vs[0].0));
            pfx1(ts, i + 3);
            assert(suf(ts, (i + 3) as nat)[0] == ts[(i + 3) as int]);
            assert(ts[(i + 3) as int] == Tok::Id(vs[0].0));
            assert(!sym(ts, i + 3, '{'));
            pvars_complete(ts, i + 3, td, vs, 0, k);
            assert(vs.subrange(0, vs.len() as int) =~= vs);
        },
    }
}

pub proof fn pds_complete(ts: Seq<Tok>, i: nat, d: nat, td: nat, p: Seq<Sd>, j: nat)
    requires
        i <= ts.len(),
        j <= p.len(),
        suf(ts, i) == tds(p, j),
        bds(p, j, d, td),
    ensures
        pds(ts, i, d, td) == Some(p.subrange(j as int, p.len() as int)),
    decreases p.len() - j,
{
    if j >= p.len() {
        assert(suf(ts, i).len() == 0);
        assert(p.subrange(j as int, p.len() as int) =~= Seq::<Sd>::empty());
    } else {
        let k = tds(p, j + 1);
        reveal_with_fuel(tds, 1);
        if j + 1 < p.len() {
            tdecl_app(p[(j + 1) as int], tds(p, j + 2));
            assert(k == tdecl(p[(j + 1) as int], tds(p, j + 2)));
        } else {
            assert(k.len() == 0);
        }
        assert(no_dot(k));
        assert(no_sep(k));
        tdecl_app(p[j as int], k);
        pd_complete(ts, i, d, td, p[j as int], k);
        at_end(ts, i, tdecl(p[j as int], Seq::empty()), k);
        pds_complete(ts, (ts.len() - k.len()) as nat, d, td, p, j + 1);
        assert(p.subrange(j as int, p.len() as int) =~= seq![p[j as int]] + p.subrange((j + 1) as int, p.len() as int));
    }
}

// ------------------------------------------------------------------ 健全性

pub proof fn pfx(ts: Seq<Tok>, i: nat, a: Seq<Tok>)
    requires
        i + a.len() <= ts.len(),
        forall|j: int| 0 <= j < a.len() ==> ts[i + j] == #[trigger] a[j],
    ensures
        suf(ts, i) == a + suf(ts, i + a.len()),
{
    assert forall|j: int| 0 <= j < suf(ts, i).len() implies suf(ts, i)[j] == (a + suf(ts, i + a.len()))[j] by {
        if j < a.len() {
            assert(ts[i + j] == a[j]);
        } else {
            assert(suf(ts, i + a.len())[j - a.len()] == ts[i + j]);
        }
    }
    assert(suf(ts, i) =~= a + suf(ts, i + a.len()));
}

pub proof fn pfx1(ts: Seq<Tok>, i: nat)
    requires
        i < ts.len(),
    ensures
        suf(ts, i) == seq![ts[i as int]] + suf(ts, i + 1),
{
    pfx(ts, i, seq![ts[i as int]]);
}

/// 名前の token：位置 i が word_tok(x) で x が名前なら、bdt は x を返す。
pub proof fn bdt_word(ts: Seq<Tok>, i: nat, x: Seq<char>)
    requires
        i < ts.len(),
        ts[i as int] == word_tok(x),
        name_ok(x),
    ensures
        bdt(ts, i) == Some(x),
{
    if kw_of(x) is Some {
        kw_inv(x);
    }
}

/// bdt が返す名前は、その位置の token の綴りで、名前として正しい。
pub proof fn bdt_sound(ts: Seq<Tok>, i: nat)
    requires
        bdt(ts, i) is Some,
    ensures
        i < ts.len(),
        ts[i as int] == word_tok(bdt(ts, i)->Some_0),
        name_ok(bdt(ts, i)->Some_0),
{
    if let Tok::Kw(k) = ts[i as int] {
        kw_word(k);
    }
}

/// 位置 i の文脈キーワードは変数として読まれない（直後が `(` か `<`）。
pub open spec fn nv(ts: Seq<Tok>, i: nat) -> bool {
    !(ts[i as int] is Kw && soft(ts[i as int]->Kw_0) && !sym(ts, i + 1, '(') && !sym(ts, i + 1, '<'))
}

pub proof fn targs_shift(e: Sx, es: Seq<Sx>, i: nat, k: Seq<Tok>)
    ensures
        targs(seq![e] + es, i + 1, k) == targs(es, i, k),
    decreases es.len() - i,
{
    let s = seq![e] + es;
    if i < es.len() {
        assert(s[(i + 1) as int] == es[i as int]);
        if i + 1 < es.len() {
            targs_shift(e, es, i + 1, k);
        }
    }
}

pub proof fn bxs_shift(e: Sx, es: Seq<Sx>, i: nat, d: nat, td: nat)
    ensures
        bxs(seq![e] + es, i + 1, d, td) == bxs(es, i, d, td),
    decreases es.len() - i,
{
    let s = seq![e] + es;
    if i < es.len() {
        assert(s[(i + 1) as int] == es[i as int]);
        bxs_shift(e, es, i + 1, d, td);
    }
}

pub proof fn tps_shift(x: (Seq<char>, Ty), ps: Seq<(Seq<char>, Ty)>, i: nat, k: Seq<Tok>)
    ensures
        tps(seq![x] + ps, i + 1, k) == tps(ps, i, k),
    decreases ps.len() - i,
{
    let s = seq![x] + ps;
    if i < ps.len() {
        assert(s[(i + 1) as int] == ps[i as int]);
        if i + 1 < ps.len() {
            tps_shift(x, ps, i + 1, k);
        }
    }
}

pub proof fn bps_shift(x: (Seq<char>, Ty), ps: Seq<(Seq<char>, Ty)>, i: nat, td: nat)
    ensures
        bps(seq![x] + ps, i + 1, td) == bps(ps, i, td),
    decreases ps.len() - i,
{
    let s = seq![x] + ps;
    if i < ps.len() {
        assert(s[(i + 1) as int] == ps[i as int]);
        bps_shift(x, ps, i + 1, td);
    }
}

pub proof fn tds_shift(x: Sd, p: Seq<Sd>, i: nat)
    ensures
        tds(seq![x] + p, i + 1) == tds(p, i),
    decreases p.len() - i,
{
    let s = seq![x] + p;
    if i < p.len() {
        assert(s[(i + 1) as int] == p[i as int]);
        tds_shift(x, p, i + 1);
    }
}

pub proof fn bds_shift(x: Sd, p: Seq<Sd>, i: nat, d: nat, td: nat)
    ensures
        bds(seq![x] + p, i + 1, d, td) == bds(p, i, d, td),
    decreases p.len() - i,
{
    let s = seq![x] + p;
    if i < p.len() {
        assert(s[(i + 1) as int] == p[i as int]);
        bds_shift(x, p, i + 1, d, td);
    }
}

pub open spec fn pt_post(ts: Seq<Tok>, i: nat, d: nat) -> bool {
    match pt(ts, i, d) {
        Some((t, j)) => i < j <= ts.len() && suf(ts, i) == tt(t, suf(ts, j)) && bt(t, d),
        None => true,
    }
}

pub proof fn pt_sound(ts: Seq<Tok>, i: nat, d: nat)
    ensures
        pt_post(ts, i, d),
    decreases d,
{
    if d > 0 && i < ts.len() {
        let d1 = (d - 1) as nat;
        pfx1(ts, i);
        match ts[i as int] {
            Tok::Kw(Kw::TList) | Tok::Kw(Kw::TOption) => {
                if sym(ts, i + 1, '<') {
                    pt_sound(ts, i + 2, d1);
                    if let Some((a, j)) = pt(ts, i + 2, d1) {
                        if sym(ts, j, '>') && pt(ts, i, d) is Some {
                            pfx1(ts, i + 1);
                            pfx1(ts, j);
                            let t = pt(ts, i, d)->Some_0.0;
                            assert(suf(ts, i) =~= tt(t, suf(ts, j + 1)));
                        }
                    }
                }
            },
            Tok::Kw(Kw::TPair) | Tok::Kw(Kw::TResult) => {
                if sym(ts, i + 1, '<') {
                    pt_sound(ts, i + 2, d1);
                    if let Some((a, j)) = pt(ts, i + 2, d1) {
                        if sym(ts, j, ',') {
                            pt_sound(ts, j + 1, d1);
                            if let Some((b, m)) = pt(ts, j + 1, d1) {
                                if sym(ts, m, '>') {
                                    pfx1(ts, i + 1);
                                    pfx1(ts, j);
                                    pfx1(ts, m);
                                    let t = pt(ts, i, d)->Some_0.0;
                                    assert(suf(ts, i) =~= tt(t, suf(ts, m + 1)));
                                }
                            }
                        }
                    }
                }
            },
            _ => {},
        }
    }
}

pub open spec fn pp_post(ts: Seq<Tok>, i: nat, d: nat, td: nat) -> bool {
    match pp(ts, i, d, td) {
        Some((e, j)) => i < j <= ts.len() && suf(ts, i) == te(e, suf(ts, j)) && bx(e, d, td),
        None => true,
    }
}

pub open spec fn pargs_post(ts: Seq<Tok>, i: nat, d: nat, td: nat) -> bool {
    match pargs(ts, i, d, td) {
        Some((es, j)) => i < j <= ts.len() && suf(ts, i) == targs(es, 0, suf(ts, j)) && bxs(es, 0, d, td),
        None => true,
    }
}

pub open spec fn pargs1_post(ts: Seq<Tok>, i: nat, d: nat, td: nat) -> bool {
    match pargs1(ts, i, d, td) {
        Some((es, j)) => i < j <= ts.len() && es.len() >= 1 && suf(ts, i) == targs(es, 0, suf(ts, j))
            && bxs(es, 0, d, td),
        None => true,
    }
}

pub open spec fn pe_post(ts: Seq<Tok>, i: nat, d: nat, td: nat) -> bool {
    match pe(ts, i, d, td) {
        Some((e, j)) => i < j <= ts.len() && suf(ts, i) == te(e, suf(ts, j)) && bx(e, d, td),
        None => true,
    }
}

/// 式の健全性（後置を含む）。基本の式の結果に `.f` の並びが続けば、Fld として受ける。
pub proof fn pe_sound(ts: Seq<Tok>, i: nat, d: nat, td: nat)
    ensures
        pe_post(ts, i, d, td),
    decreases d, 2nat, 0nat,
{
    pp_sound(ts, i, d, td);
    if let Some((e, j)) = pp(ts, i, d, td) {
        assert(pp_post(ts, i, d, td));
        if recv_ok(e) && j + 1 < ts.len() && sym(ts, j, '.') && idt(ts, j + 1) is Some {
            pfs_sound(ts, j);
            let r = pfs(ts, j);
            assert(pe(ts, i, d, td) == Some((Sx::Fld(Box::new(e), r.0), r.1)));
            assert(te(Sx::Fld(Box::new(e), r.0), suf(ts, r.1)) == te(e, tdots(r.0, suf(ts, r.1))));
            assert(suf(ts, i) == te(e, suf(ts, j)));
            assert(bx(Sx::Fld(Box::new(e), r.0), d, td));
        } else {
            assert(pe(ts, i, d, td) == Some((e, j)));
        }
    }
}

pub open spec fn prest_post(ts: Seq<Tok>, i: nat, d: nat, td: nat) -> bool {
    match prest(ts, i, d, td) {
        Some((fs, b, j)) => i < j <= ts.len() && (fs.len() > 0 || b is Some) && suf(ts, i) == tfe(
            fs,
            0,
            rtail(fs.len() > 0, b, suf(ts, j)),
        ) && bfs(fs, 0, d, td) && bopt(b, d, td),
        None => true,
    }
}

pub open spec fn prec_post(ts: Seq<Tok>, i: nat, d: nat, td: nat) -> bool {
    match prec(ts, i, d, td) {
        Some((fs, b, j)) => i < j <= ts.len() && suf(ts, i) == tfe(
            fs,
            0,
            rtail(fs.len() > 0, b, suf(ts, j)),
        ) && bfs(fs, 0, d, td) && bopt(b, d, td),
        None => true,
    }
}

/// レコード式の字段の並びと base の健全性（位置 i から）。
pub proof fn prest_sound(ts: Seq<Tok>, i: nat, d: nat, td: nat)
    requires
        i <= ts.len(),
    ensures
        prest_post(ts, i, d, td),
    decreases d, 3nat, ts.len() - i,
{
    reveal_with_fuel(prest, 1);
    reveal_with_fuel(tfe, 1);
    reveal_with_fuel(bfs, 1);
    reveal_with_fuel(bopt, 1);
    if sym(ts, i, '.') && sym(ts, i + 1, '.') {
        pe_sound(ts, i + 2, d, td);
        if let Some((b, j)) = pe(ts, i + 2, d, td) {
            assert(pe_post(ts, i + 2, d, td));
            if sym(ts, j, '}') {
                pfx1(ts, i);
                pfx1(ts, i + 1);
                pfx1(ts, j);
                assert(prest(ts, i, d, td) == Some((Seq::<(Seq<char>, Sx)>::empty(), Some(Box::new(b)), (j + 1) as nat)));
                assert(suf(ts, i) =~= seq![Tok::Sym('.'), Tok::Sym('.')] + te(b, seq![Tok::Sym('}')] + suf(ts, j + 1)));
                assert(prest_post(ts, i, d, td));
            } else {
                assert(prest(ts, i, d, td) is None);
                assert(prest_post(ts, i, d, td));
            }
        } else {
            assert(prest(ts, i, d, td) is None);
            assert(prest_post(ts, i, d, td));
        }
    } else if idt(ts, i) is Some && sym(ts, i + 1, ':') {
        let f = idt(ts, i)->Some_0;
        assert(ident_ok(f));
        assert(ts[i as int] == Tok::Id(f));
        assert(word_tok(f) == Tok::Id(f));
        pfx1(ts, i);
        pfx1(ts, i + 1);
        pe_sound(ts, i + 2, d, td);
        if let Some((v, j)) = pe(ts, i + 2, d, td) {
            assert(pe_post(ts, i + 2, d, td));
            assert(suf(ts, i) =~= seq![word_tok(f), Tok::Sym(':')] + suf(ts, i + 2));
            if sym(ts, j, '}') {
                pfx1(ts, j);
                assert(prest(ts, i, d, td) == Some((seq![(f, v)], None, (j + 1) as nat)));
                tfe_head(seq![(f, v)], 0, seq![Tok::Sym('}')] + suf(ts, j + 1));
                assert(suf(ts, i) =~= tfe(seq![(f, v)], 0, rtail(true, None, suf(ts, j + 1))));
                assert(bx(v, d, td));
                assert(i < (j + 1) as nat);
                assert((j + 1) as nat <= ts.len());
                bfs_one(f, v, d, td);
                assert(bopt(None, d, td));
                assert(prest_post(ts, i, d, td));
            } else if sym(ts, j, ',') && i < j {
                pfx1(ts, j);
                prest_sound(ts, j + 1, d, td);
                assert(prest_post(ts, j + 1, d, td));
                if let Some((fs2, b2, m)) = prest(ts, j + 1, d, td) {
                    assert(prest(ts, i, d, td) == Some((seq![(f, v)] + fs2, b2, m)));
                    let s = seq![(f, v)] + fs2;
                    let tl = rtail(true, b2, suf(ts, m));
                    tfe_head(s, 0, tl);
                    assert(s[0] == (f, v));
                    if fs2.len() == 0 {
                        assert(b2 is Some);
                        assert(tfe(fs2, 0, rtail(false, b2, suf(ts, m))) == rtail(false, b2, suf(ts, m)));
                        assert(suf(ts, j) =~= seq![Tok::Sym(',')] + rtail(false, b2, suf(ts, m)));
                        assert(rtail(true, b2, suf(ts, m)) =~= seq![Tok::Sym(',')] + rtail(false, b2, suf(ts, m)));
                    } else {
                        tfe_shift((f, v), fs2, 0, tl);
                        assert(tfe(s, 1, tl) == tfe(fs2, 0, tl));
                    }
                    assert(suf(ts, i) =~= tfe(s, 0, tl));
                    bfs_shift((f, v), fs2, 0, d, td);
                    assert(bx(v, d, td));
                    assert(prest_post(ts, i, d, td));
                } else {
                    assert(prest(ts, i, d, td) is None);
                    assert(prest_post(ts, i, d, td));
                }
            } else {
                assert(prest(ts, i, d, td) is None);
                assert(prest_post(ts, i, d, td));
            }
        } else {
            assert(prest(ts, i, d, td) is None);
            assert(prest_post(ts, i, d, td));
        }
    } else {
        assert(prest(ts, i, d, td) is None);
        assert(prest_post(ts, i, d, td));
    }
}

/// レコード式の健全性（閉じ括弧まで）。
pub proof fn prec_sound(ts: Seq<Tok>, i: nat, d: nat, td: nat)
    requires
        i <= ts.len(),
    ensures
        prec_post(ts, i, d, td),
    decreases d, 4nat, 0nat,
{
    reveal_with_fuel(prec, 1);
    reveal_with_fuel(tfe, 1);
    reveal_with_fuel(bfs, 1);
    reveal_with_fuel(bopt, 1);
    if sym(ts, i, '}') {
        pfx1(ts, i);
        assert(prec(ts, i, d, td) == Some((Seq::<(Seq<char>, Sx)>::empty(), None, (i + 1) as nat)));
        assert(suf(ts, i) =~= seq![Tok::Sym('}')] + suf(ts, i + 1));
        assert(prec_post(ts, i, d, td));
    } else {
        prest_sound(ts, i, d, td);
        assert(prec(ts, i, d, td) == prest(ts, i, d, td));
        assert(prec_post(ts, i, d, td));
    }
}

/// レコード式の健全性。`R {` の後ろの本体を読み、R を名前として受ける。
pub proof fn pp_sound_rec(ts: Seq<Tok>, i: nat, d: nat, td: nat)
    requires
        d > 0,
        i < ts.len(),
        ts[i as int] is Id,
        ident_ok(ts[i as int]->Id_0),
        sym(ts, i + 1, '{'),
        rec_head(ts, i + 2),
    ensures
        pp_post(ts, i, d, td),
    decreases d, 0nat, 0nat,
{
    let d1 = (d - 1) as nat;
    let r = ts[i as int]->Id_0;
    prec_sound(ts, i + 2, d1, td);
    assert(prec_post(ts, i + 2, d1, td));
    if let Some((fs, b, j)) = prec(ts, i + 2, d1, td) {
        pfx1(ts, i);
        pfx1(ts, i + 1);
        assert(ts[i as int] == Tok::Id(r));
        assert(word_tok(r) == Tok::Id(r));
        assert(pp(ts, i, d, td) == Some((Sx::Rec(r, fs, b), j)));
        assert(suf(ts, i) =~= seq![word_tok(r), Tok::Sym('{')] + suf(ts, i + 2));
        assert(te(Sx::Rec(r, fs, b), suf(ts, j)) == seq![word_tok(r), Tok::Sym('{')] + tfe(fs, 0, rtail(fs.len() > 0, b, suf(ts, j))));
        assert(bx(Sx::Rec(r, fs, b), d, td));
    }
}

/// 型の字段の並びの健全性（位置 i から、閉じ括弧まで）。
pub open spec fn pfds_post(ts: Seq<Tok>, i: nat, td: nat) -> bool {
    match pfds(ts, i, td) {
        Some((fs, tc, j)) => i < j <= ts.len() && fs.len() > 0 && suf(ts, i) == tfd(
            fs,
            0,
            tc,
            seq![Tok::Sym('}')] + suf(ts, j),
        ) && bfds(fs, 0, td),
        None => true,
    }
}

pub proof fn pfds_sound(ts: Seq<Tok>, i: nat, td: nat)
    requires
        i <= ts.len(),
    ensures
        pfds_post(ts, i, td),
    decreases ts.len() - i,
{
    reveal_with_fuel(pfds, 1);
    reveal_with_fuel(tfd, 1);
    reveal_with_fuel(bfds, 1);
    if idt(ts, i) is Some && sym(ts, i + 1, ':') {
        let f = idt(ts, i)->Some_0;
        assert(ident_ok(f));
        assert(word_tok(f) == Tok::Id(f));
        pfx1(ts, i);
        pfx1(ts, i + 1);
        pt_sound(ts, i + 2, td);
        if let Some((t, j)) = pt(ts, i + 2, td) {
            assert(pt_post(ts, i + 2, td));
            assert(suf(ts, i) =~= seq![word_tok(f), Tok::Sym(':')] + suf(ts, i + 2));
            if sym(ts, j, '}') {
                pfx1(ts, j);
                assert(pfds(ts, i, td) == Some((seq![(f, t)], false, (j + 1) as nat)));
                tfd_head(seq![(f, t)], 0, false, seq![Tok::Sym('}')] + suf(ts, j + 1));
                assert(suf(ts, i) =~= tfd(seq![(f, t)], 0, false, seq![Tok::Sym('}')] + suf(ts, j + 1)));
                bfds_one(f, t, td);
                assert(pfds_post(ts, i, td));
            } else if sym(ts, j, ',') && i < j {
                pfx1(ts, j);
                if sym(ts, j + 1, '}') {
                    pfx1(ts, j + 1);
                    assert(pfds(ts, i, td) == Some((seq![(f, t)], true, (j + 2) as nat)));
                    tfd_head(seq![(f, t)], 0, true, seq![Tok::Sym('}')] + suf(ts, j + 2));
                    assert(suf(ts, i) =~= tfd(seq![(f, t)], 0, true, seq![Tok::Sym('}')] + suf(ts, j + 2)));
                    assert(bt(t, td));
                    bfds_one(f, t, td);
                    assert(i < (j + 2) as nat);
                    assert((j + 2) as nat <= ts.len());
                    assert(pfds_post(ts, i, td));
                } else {
                    pfds_sound(ts, j + 1, td);
                    assert(pfds_post(ts, j + 1, td));
                    if let Some((fs2, tc2, m)) = pfds(ts, j + 1, td) {
                        assert(pfds(ts, i, td) == Some((seq![(f, t)] + fs2, tc2, m)));
                        let s = seq![(f, t)] + fs2;
                        tfd_head(s, 0, tc2, seq![Tok::Sym('}')] + suf(ts, m));
                        tfd_shift((f, t), fs2, 0, tc2, seq![Tok::Sym('}')] + suf(ts, m));
                        assert(tfd(s, 1, tc2, seq![Tok::Sym('}')] + suf(ts, m)) == tfd(fs2, 0, tc2, seq![Tok::Sym('}')] + suf(ts, m)));
                        assert(suf(ts, i) =~= tfd(s, 0, tc2, seq![Tok::Sym('}')] + suf(ts, m)));
                        bfds_shift((f, t), fs2, 0, td);
                        assert(bt(t, td));
                        assert(bfds(s, 0, td));
                        assert(i < m);
                        assert(m <= ts.len());
                        assert(pfds_post(ts, i, td));
                    } else {
                        assert(pfds(ts, i, td) is None);
                        assert(pfds_post(ts, i, td));
                    }
                }
            } else {
                assert(pfds(ts, i, td) is None);
                assert(pfds_post(ts, i, td));
            }
        } else {
            assert(pfds(ts, i, td) is None);
            assert(pfds_post(ts, i, td));
        }
    } else {
        assert(pfds(ts, i, td) is None);
        assert(pfds_post(ts, i, td));
    }
}

/// 基本の式の健全性（後置を含まない）。
pub proof fn pp_sound(ts: Seq<Tok>, i: nat, d: nat, td: nat)
    ensures
        pp_post(ts, i, d, td),
    decreases d, 1nat, 0nat,
{
    if d > 0 && i < ts.len() {
        pfx1(ts, i);
        match ts[i as int] {
            Tok::Id(x) => if ident_ok(x) && sym(ts, i + 1, '(') {
                pp_sound_call(ts, i, d, td);
            } else if ident_ok(x) && sym(ts, i + 1, '{') && rec_head(ts, i + 2) {
                pp_sound_rec(ts, i, d, td);
            },
            Tok::Kw(k) => {
                if soft(k) && !sym(ts, i + 1, '(') && !sym(ts, i + 1, '<') {
                    kw_word(k);
                    let e = Sx::Var(kwt(k));
                    assert(suf(ts, i) =~= te(e, suf(ts, i + 1)));
                } else if k == Kw::List {
                    pp_sound_list(ts, i, d, td);
                } else if k == Kw::Some {
                    pp_sound_some(ts, i, d, td);
                } else if k == Kw::None {
                    pp_sound_none(ts, i, d, td);
                } else if k == Kw::Pair {
                    pp_sound_pair(ts, i, d, td);
                } else if k == Kw::Let {
                    pp_sound_let(ts, i, d, td);
                } else if k == Kw::If {
                    pp_sound_if(ts, i, d, td);
                } else if k == Kw::Fold {
                    pp_sound_fold(ts, i, d, td);
                } else if k == Kw::MatchOption {
                    pp_sound_match(ts, i, d, td);
                } else if k == Kw::Ok || k == Kw::Err {
                    pp_sound_inj(ts, i, d, td);
                } else if k == Kw::MatchResult {
                    pp_sound_matchr(ts, i, d, td);
                } else if kw_b(k) is Some {
                    pp_sound_builtin(ts, i, d, td);
                }
            },
            _ => {},
        }
    }
}

proof fn pp_sound_call(ts: Seq<Tok>, i: nat, d: nat, td: nat)
    requires
        d > 0,
        i < ts.len(),
        ts[i as int] is Id,
        ident_ok(ts[i as int]->Id_0),
        sym(ts, i + 1, '('),
    ensures
        pp_post(ts, i, d, td),
    decreases d, 0nat, 0nat,
{
    let d1 = (d - 1) as nat;
    pargs_sound(ts, i + 2, d1, td);
    if let Some((es, j)) = pargs(ts, i + 2, d1, td) {
        pfx1(ts, i);
        pfx1(ts, i + 1);
        let e = pp(ts, i, d, td)->Some_0.0;
        assert(suf(ts, i) =~= te(e, suf(ts, j)));
    }
}

#[verifier::rlimit(100)]
proof fn pp_sound_builtin(ts: Seq<Tok>, i: nat, d: nat, td: nat)
    requires
        d > 0,
        i < ts.len(),
        ts[i as int] is Kw,
        kw_b(ts[i as int]->Kw_0) is Some,
        nv(ts, i),
    ensures
        pp_post(ts, i, d, td),
    decreases d, 0nat, 0nat,
{
    let d1 = (d - 1) as nat;
    let k = ts[i as int]->Kw_0;
    if sym(ts, i + 1, '(') {
        pargs_sound(ts, i + 2, d1, td);
        if let Some((es, j)) = pargs(ts, i + 2, d1, td) {
            pfx1(ts, i);
            pfx1(ts, i + 1);
            let b = kw_b(k)->Some_0;
            assert(bkw(b) == k);
            let e = pp(ts, i, d, td)->Some_0.0;
            assert(e == Sx::Builtin(b, es));
            assert(suf(ts, i) =~= te(e, suf(ts, j)));
        }
    }
}

proof fn pp_sound_list(ts: Seq<Tok>, i: nat, d: nat, td: nat)
    requires
        d > 0,
        i < ts.len(),
        ts[i as int] == Tok::Kw(Kw::List),
        nv(ts, i),
    ensures
        pp_post(ts, i, d, td),
    decreases d, 0nat, 0nat,
{
    let d1 = (d - 1) as nat;
    if sym(ts, i + 1, '<') {
        pt_sound(ts, i + 2, td);
        if let Some((t, j)) = pt(ts, i + 2, td) {
            if sym(ts, j, '>') && sym(ts, j + 1, '(') {
                pargs_sound(ts, j + 2, d1, td);
                if let Some((es, m)) = pargs(ts, j + 2, d1, td) {
                    pfx1(ts, i);
                    pfx1(ts, i + 1);
                    pfx1(ts, j);
                    pfx1(ts, j + 1);
                    let e = pp(ts, i, d, td)->Some_0.0;
                    assert(suf(ts, j) =~= seq![Tok::Sym('>'), Tok::Sym('(')] + targs(es, 0, suf(ts, m)));
                    assert(suf(ts, i) =~= te(e, suf(ts, m)));
                }
            }
        }
    }
}

proof fn pp_sound_some(ts: Seq<Tok>, i: nat, d: nat, td: nat)
    requires
        d > 0,
        i < ts.len(),
        ts[i as int] == Tok::Kw(Kw::Some),
        nv(ts, i),
    ensures
        pp_post(ts, i, d, td),
    decreases d, 0nat, 0nat,
{
    let d1 = (d - 1) as nat;
    if sym(ts, i + 1, '(') {
        pe_sound(ts, i + 2, d1, td);
        if let Some((a, j)) = pe(ts, i + 2, d1, td) {
            if sym(ts, j, ')') {
                pfx1(ts, i);
                pfx1(ts, i + 1);
                pfx1(ts, j);
                let e = pp(ts, i, d, td)->Some_0.0;
                assert(suf(ts, i) =~= te(e, suf(ts, j + 1)));
            }
        }
    }
}

proof fn pp_sound_none(ts: Seq<Tok>, i: nat, d: nat, td: nat)
    requires
        d > 0,
        i < ts.len(),
        ts[i as int] == Tok::Kw(Kw::None),
        nv(ts, i),
    ensures
        pp_post(ts, i, d, td),
    decreases d, 0nat, 0nat,
{
    if sym(ts, i + 1, '<') {
        pt_sound(ts, i + 2, td);
        if let Some((t, j)) = pt(ts, i + 2, td) {
            if sym(ts, j, '>') && sym(ts, j + 1, '(') && sym(ts, j + 2, ')') {
                pfx1(ts, i);
                pfx1(ts, i + 1);
                pfx1(ts, j);
                pfx1(ts, j + 1);
                pfx1(ts, j + 2);
                let e = pp(ts, i, d, td)->Some_0.0;
                assert(suf(ts, j) =~= seq![Tok::Sym('>'), Tok::Sym('('), Tok::Sym(')')] + suf(ts, j + 3));
                assert(suf(ts, i) =~= te(e, suf(ts, j + 3)));
            }
        }
    }
}

proof fn pp_sound_pair(ts: Seq<Tok>, i: nat, d: nat, td: nat)
    requires
        d > 0,
        i < ts.len(),
        ts[i as int] == Tok::Kw(Kw::Pair),
        nv(ts, i),
    ensures
        pp_post(ts, i, d, td),
    decreases d, 0nat, 0nat,
{
    let d1 = (d - 1) as nat;
    if sym(ts, i + 1, '(') {
        pe_sound(ts, i + 2, d1, td);
        if let Some((a, j)) = pe(ts, i + 2, d1, td) {
            if sym(ts, j, ',') {
                pe_sound(ts, j + 1, d1, td);
                if let Some((b, m)) = pe(ts, j + 1, d1, td) {
                    if sym(ts, m, ')') {
                        pfx1(ts, i);
                        pfx1(ts, i + 1);
                        pfx1(ts, j);
                        pfx1(ts, m);
                        let e = pp(ts, i, d, td)->Some_0.0;
                        assert(suf(ts, i) =~= te(e, suf(ts, m + 1)));
                    }
                }
            }
        }
    }
}

proof fn pp_sound_let(ts: Seq<Tok>, i: nat, d: nat, td: nat)
    requires
        d > 0,
        i < ts.len(),
        ts[i as int] == Tok::Kw(Kw::Let),
    ensures
        pp_post(ts, i, d, td),
    decreases d, 0nat, 0nat,
{
    let d1 = (d - 1) as nat;
    if let Some(x) = bdt(ts, i + 1) {
        bdt_sound(ts, i + 1);
        if sym(ts, i + 2, '=') {
            pe_sound(ts, i + 3, d1, td);
            if let Some((a, j)) = pe(ts, i + 3, d1, td) {
                if kwat(ts, j, Kw::In) {
                    pe_sound(ts, j + 1, d1, td);
                    if let Some((b, m)) = pe(ts, j + 1, d1, td) {
                        pfx1(ts, i);
                        pfx1(ts, i + 1);
                        pfx1(ts, i + 2);
                        pfx1(ts, j);
                        let e = pp(ts, i, d, td)->Some_0.0;
                        assert(suf(ts, i) =~= te(e, suf(ts, m)));
                    }
                }
            }
        }
    }
}

proof fn pp_sound_if(ts: Seq<Tok>, i: nat, d: nat, td: nat)
    requires
        d > 0,
        i < ts.len(),
        ts[i as int] == Tok::Kw(Kw::If),
    ensures
        pp_post(ts, i, d, td),
    decreases d, 0nat, 0nat,
{
    let d1 = (d - 1) as nat;
    if sym(ts, i + 1, '(') {
        pe_sound(ts, i + 2, d1, td);
        if let Some((c, j)) = pe(ts, i + 2, d1, td) {
            if sym(ts, j, ',') {
                pe_sound(ts, j + 1, d1, td);
                if let Some((a, m)) = pe(ts, j + 1, d1, td) {
                    if sym(ts, m, ',') {
                        pe_sound(ts, m + 1, d1, td);
                        if let Some((b, q)) = pe(ts, m + 1, d1, td) {
                            if sym(ts, q, ')') {
                                pfx1(ts, i);
                                pfx1(ts, i + 1);
                                pfx1(ts, j);
                                pfx1(ts, m);
                                pfx1(ts, q);
                                let e = pp(ts, i, d, td)->Some_0.0;
                                assert(suf(ts, i) =~= te(e, suf(ts, q + 1)));
                            }
                        }
                    }
                }
            }
        }
    }
}

proof fn pp_sound_fold(ts: Seq<Tok>, i: nat, d: nat, td: nat)
    requires
        d > 0,
        i < ts.len(),
        ts[i as int] == Tok::Kw(Kw::Fold),
    ensures
        pp_post(ts, i, d, td),
    decreases d, 0nat, 0nat,
{
    let d1 = (d - 1) as nat;
    if sym(ts, i + 1, '(') {
        pe_sound(ts, i + 2, d1, td);
        if let Some((l, j)) = pe(ts, i + 2, d1, td) {
            if sym(ts, j, ',') {
                pe_sound(ts, j + 1, d1, td);
                if let Some((n, m)) = pe(ts, j + 1, d1, td) {
                    if sym(ts, m, ',') && sym(ts, m + 1, '|') {
                        if let (Some(a), Some(x)) = (bdt(ts, m + 2), bdt(ts, m + 4)) {
                            bdt_sound(ts, m + 2);
                            bdt_sound(ts, m + 4);
                            if sym(ts, m + 3, ',') && sym(ts, m + 5, '|') {
                                pe_sound(ts, m + 6, d1, td);
                                if let Some((b, q)) = pe(ts, m + 6, d1, td) {
                                    if sym(ts, q, ')') {
                                        pfx1(ts, i);
                                        pfx1(ts, i + 1);
                                        pfx1(ts, j);
                                        pfx1(ts, m);
                                        pfx1(ts, m + 1);
                                        pfx1(ts, m + 2);
                                        pfx1(ts, m + 3);
                                        pfx1(ts, m + 4);
                                        pfx1(ts, m + 5);
                                        pfx1(ts, q);
                                        let e = pp(ts, i, d, td)->Some_0.0;
                                        let mid = seq![Tok::Sym(','), Tok::Sym('|'), word_tok(a), Tok::Sym(','), word_tok(x), Tok::Sym('|')];
                                        assert(suf(ts, m) =~= mid + te(b, seq![Tok::Sym(')')] + suf(ts, q + 1)));
                                        assert(suf(ts, i) =~= te(e, suf(ts, q + 1)));
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }
    }
}

proof fn pp_sound_match(ts: Seq<Tok>, i: nat, d: nat, td: nat)
    requires
        d > 0,
        i < ts.len(),
        ts[i as int] == Tok::Kw(Kw::MatchOption),
    ensures
        pp_post(ts, i, d, td),
    decreases d, 0nat, 0nat,
{
    let d1 = (d - 1) as nat;
    if sym(ts, i + 1, '(') {
        pe_sound(ts, i + 2, d1, td);
        if let Some((m, j)) = pe(ts, i + 2, d1, td) {
            if sym(ts, j, ',') {
                pe_sound(ts, j + 1, d1, td);
                if let Some((n, q)) = pe(ts, j + 1, d1, td) {
                    if sym(ts, q, ',') && sym(ts, q + 1, '|') {
                        if let Some(x) = bdt(ts, q + 2) {
                            bdt_sound(ts, q + 2);
                            if sym(ts, q + 3, '|') {
                                pe_sound(ts, q + 4, d1, td);
                                if let Some((b, u)) = pe(ts, q + 4, d1, td) {
                                    if sym(ts, u, ')') {
                                        pfx1(ts, i);
                                        pfx1(ts, i + 1);
                                        pfx1(ts, j);
                                        pfx1(ts, q);
                                        pfx1(ts, q + 1);
                                        pfx1(ts, q + 2);
                                        pfx1(ts, q + 3);
                                        pfx1(ts, u);
                                        let e = pp(ts, i, d, td)->Some_0.0;
                                        let mid = seq![Tok::Sym(','), Tok::Sym('|'), word_tok(x), Tok::Sym('|')];
                                        assert(suf(ts, q) =~= mid + te(b, seq![Tok::Sym(')')] + suf(ts, u + 1)));
                                        assert(suf(ts, i) =~= te(e, suf(ts, u + 1)));
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }
    }
}

proof fn pp_sound_inj(ts: Seq<Tok>, i: nat, d: nat, td: nat)
    requires
        d > 0,
        i < ts.len(),
        ts[i as int] == Tok::Kw(Kw::Ok) || ts[i as int] == Tok::Kw(Kw::Err),
        nv(ts, i),
    ensures
        pp_post(ts, i, d, td),
    decreases d, 0nat, 0nat,
{
    let d1 = (d - 1) as nat;
    if sym(ts, i + 1, '<') {
        pt_sound(ts, i + 2, td);
        if let Some((t, j)) = pt(ts, i + 2, td) {
            if sym(ts, j, ',') {
                pt_sound(ts, j + 1, td);
                if let Some((u, m)) = pt(ts, j + 1, td) {
                    if sym(ts, m, '>') && sym(ts, m + 1, '(') {
                        pe_sound(ts, m + 2, d1, td);
                        if let Some((a, q)) = pe(ts, m + 2, d1, td) {
                            if sym(ts, q, ')') {
                                pfx1(ts, i);
                                pfx1(ts, i + 1);
                                pfx1(ts, j);
                                pfx1(ts, m);
                                pfx1(ts, m + 1);
                                pfx1(ts, q);
                                let e = pp(ts, i, d, td)->Some_0.0;
                                assert(suf(ts, m) =~= seq![Tok::Sym('>'), Tok::Sym('(')] + te(a, seq![Tok::Sym(')')] + suf(ts, q + 1)));
                                assert(suf(ts, i) =~= te(e, suf(ts, q + 1)));
                            }
                        }
                    }
                }
            }
        }
    }
}

proof fn pp_sound_matchr(ts: Seq<Tok>, i: nat, d: nat, td: nat)
    requires
        d > 0,
        i < ts.len(),
        ts[i as int] == Tok::Kw(Kw::MatchResult),
    ensures
        pp_post(ts, i, d, td),
    decreases d, 0nat, 0nat,
{
    let d1 = (d - 1) as nat;
    if sym(ts, i + 1, '(') {
        pe_sound(ts, i + 2, d1, td);
        if let Some((m, j)) = pe(ts, i + 2, d1, td) {
            if sym(ts, j, ',') && sym(ts, j + 1, '|') && sym(ts, j + 3, '|') {
                if let Some(x) = bdt(ts, j + 2) {
                    bdt_sound(ts, j + 2);
                    pe_sound(ts, j + 4, d1, td);
                    if let Some((a, q)) = pe(ts, j + 4, d1, td) {
                        if sym(ts, q, ',') && sym(ts, q + 1, '|') && sym(ts, q + 3, '|') {
                            if let Some(y) = bdt(ts, q + 2) {
                                bdt_sound(ts, q + 2);
                                pe_sound(ts, q + 4, d1, td);
                                if let Some((b, u)) = pe(ts, q + 4, d1, td) {
                                    if sym(ts, u, ')') {
                                        pfx1(ts, i);
                                        pfx1(ts, i + 1);
                                        pfx1(ts, j);
                                        pfx1(ts, j + 1);
                                        pfx1(ts, j + 2);
                                        pfx1(ts, j + 3);
                                        pfx1(ts, q);
                                        pfx1(ts, q + 1);
                                        pfx1(ts, q + 2);
                                        pfx1(ts, q + 3);
                                        pfx1(ts, u);
                                        let e = pp(ts, i, d, td)->Some_0.0;
                                        let my = seq![Tok::Sym(','), Tok::Sym('|'), word_tok(y), Tok::Sym('|')];
                                        let mx = seq![Tok::Sym(','), Tok::Sym('|'), word_tok(x), Tok::Sym('|')];
                                        assert(suf(ts, q) =~= my + te(b, seq![Tok::Sym(')')] + suf(ts, u + 1)));
                                        assert(suf(ts, j) =~= mx + te(a, suf(ts, q)));
                                        assert(suf(ts, i) =~= te(e, suf(ts, u + 1)));
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }
    }
}

pub proof fn pargs_sound(ts: Seq<Tok>, i: nat, d: nat, td: nat)
    ensures
        pargs_post(ts, i, d, td),
    decreases d, 4nat, 0nat,
{
    if sym(ts, i, ')') {
        pfx1(ts, i);
        assert(suf(ts, i) =~= targs(Seq::<Sx>::empty(), 0, suf(ts, i + 1)));
    } else {
        pargs1_sound(ts, i, d, td);
    }
}

pub proof fn pargs1_sound(ts: Seq<Tok>, i: nat, d: nat, td: nat)
    ensures
        pargs1_post(ts, i, d, td),
    decreases d, 3nat, ts.len() - i,
{
    pe_sound(ts, i, d, td);
    if let Some((e, j)) = pe(ts, i, d, td) {
        if sym(ts, j, ')') {
            pfx1(ts, j);
            assert(targs(seq![e], 0, suf(ts, j + 1)) == te(e, seq![Tok::Sym(')')] + suf(ts, j + 1)));
            assert(bxs(seq![e], 1, d, td));
        } else if sym(ts, j, ',') && i < j {
            pargs1_sound(ts, j + 1, d, td);
            if let Some((es, m)) = pargs1(ts, j + 1, d, td) {
                pfx1(ts, j);
                targs_shift(e, es, 0, suf(ts, m));
                bxs_shift(e, es, 0, d, td);
                let s = seq![e] + es;
                assert(s[0] == e);
                assert(targs(s, 0, suf(ts, m)) == te(e, seq![Tok::Sym(',')] + targs(s, 1, suf(ts, m))));
            }
        }
    }
}

pub open spec fn pparams_post(ts: Seq<Tok>, i: nat, td: nat) -> bool {
    match pparams(ts, i, td) {
        Some((ps, j)) => i < j <= ts.len() && suf(ts, i) == tps(ps, 0, suf(ts, j)) && bps(ps, 0, td),
        None => true,
    }
}

pub open spec fn pparams1_post(ts: Seq<Tok>, i: nat, td: nat) -> bool {
    match pparams1(ts, i, td) {
        Some((ps, j)) => i < j <= ts.len() && ps.len() >= 1 && suf(ts, i) == tps(ps, 0, suf(ts, j))
            && bps(ps, 0, td),
        None => true,
    }
}

pub proof fn pparams1_sound(ts: Seq<Tok>, i: nat, td: nat)
    ensures
        pparams1_post(ts, i, td),
    decreases ts.len() - i,
{
    if let Some(x) = bdt(ts, i) {
        bdt_sound(ts, i);
        if sym(ts, i + 1, ':') {
            pt_sound(ts, i + 2, td);
            if let Some((t, j)) = pt(ts, i + 2, td) {
                pfx1(ts, i);
                pfx1(ts, i + 1);
                if sym(ts, j, ')') {
                    pfx1(ts, j);
                    let ps = seq![(x, t)];
                    assert(ps[0] == (x, t));
                    assert(suf(ts, i) =~= tps(ps, 0, suf(ts, j + 1)));
                    assert(bps(ps, 1, td));
                } else if sym(ts, j, ',') && i < j {
                    pparams1_sound(ts, j + 1, td);
                    if let Some((ps, m)) = pparams1(ts, j + 1, td) {
                        pfx1(ts, j);
                        tps_shift((x, t), ps, 0, suf(ts, m));
                        bps_shift((x, t), ps, 0, td);
                        let s = seq![(x, t)] + ps;
                        assert(s[0] == (x, t));
                        assert(suf(ts, i) =~= tps(s, 0, suf(ts, m)));
                    }
                }
            }
        }
    }
}

pub proof fn pparams_sound(ts: Seq<Tok>, i: nat, td: nat)
    ensures
        pparams_post(ts, i, td),
{
    if sym(ts, i, ')') {
        pfx1(ts, i);
        assert(suf(ts, i) =~= tps(Seq::<(Seq<char>, Ty)>::empty(), 0, suf(ts, i + 1)));
    } else {
        pparams1_sound(ts, i, td);
    }
}

pub open spec fn ptys_post(ts: Seq<Tok>, i: nat, td: nat) -> bool {
    match ptys(ts, i, td) {
        Some((ps, j)) => i < j <= ts.len() && ps.len() > 0 && suf(ts, i) == tts(ps, 0, suf(ts, j)) && bts(ps, 0, td),
        None => true,
    }
}

pub open spec fn pvar_post(ts: Seq<Tok>, i: nat, td: nat) -> bool {
    match pvar(ts, i, td) {
        Some((c, ps, j)) => i < j <= ts.len() && suf(ts, i) == seq![Tok::Id(c)] + tpay(ps, suf(ts, j)) && cname_ok(c)
            && bts(ps, 0, td),
        None => true,
    }
}

pub open spec fn pvars_post(ts: Seq<Tok>, i: nat, td: nat) -> bool {
    match pvars(ts, i, td) {
        Some((vs, j)) => i < j <= ts.len() && vs.len() > 0 && suf(ts, i) == tvars(vs, 0, suf(ts, j)) && bvars(vs, 0, td),
        None => true,
    }
}

/// 型の並びの健全性：読んだ型の並びの token 列は、位置 i からの型の並びの token 列に等しい。
pub proof fn ptys_sound(ts: Seq<Tok>, i: nat, td: nat)
    ensures
        ptys_post(ts, i, td),
    decreases ts.len() - i,
{
    pt_sound(ts, i, td);
    if let Some((t, j)) = pt(ts, i, td) {
        assert(pt_post(ts, i, td));
        if sym(ts, j, ',') && i < j {
            pfx1(ts, j);
            ptys_sound(ts, j + 1, td);
            if let Some((ps, m)) = ptys(ts, j + 1, td) {
                assert(ptys_post(ts, j + 1, td));
                let s = seq![t] + ps;
                tts_head(s, 0, suf(ts, m));
                tts_shift(t, ps, 0, suf(ts, m));
                bts_shift(t, ps, 0, td);
                assert(ptys(ts, i, td) == Some((s, m)));
                assert(i < m);
                assert(m <= ts.len());
                assert(s.len() > 0);
                assert(suf(ts, i) =~= tts(s, 0, suf(ts, m)));
                assert(bts(ps, 0, td));
                assert(bts(s, 1, td) == bts(ps, 0, td));
                assert(bt(t, td));
                assert(bts(s, 0, td));
                assert(ptys_post(ts, i, td));
            }
        } else {
            assert(ptys(ts, i, td) == Some((seq![t], j)));
            assert(suf(ts, i) =~= tts(seq![t], 0, suf(ts, j)));
            assert(bt(t, td));
            assert(bts(seq![t], 1, td));
            assert(bts(seq![t], 0, td));
            assert(ptys_post(ts, i, td));
        }
    }
}

/// 構築子の健全性：読んだ構築子の token 列は、位置 i からの token 列に等しい。
pub proof fn pvar_sound(ts: Seq<Tok>, i: nat, td: nat)
    ensures
        pvar_post(ts, i, td),
{
    if let Some(c) = cidt(ts, i) {
        assert(idt(ts, i) == Some(c));
        assert(cname_ok(c));
        pfx1(ts, i);
        assert(ts[i as int] == Tok::Id(c));
        if sym(ts, i + 1, '(') {
            pfx1(ts, i + 1);
            ptys_sound(ts, i + 2, td);
            if let Some((ps, j)) = ptys(ts, i + 2, td) {
                assert(ptys_post(ts, i + 2, td));
                if sym(ts, j, ')') {
                    pfx1(ts, j);
                    assert(pvar(ts, i, td) == Some((c, ps, j + 1)));
                    assert(suf(ts, i) =~= seq![Tok::Id(c)] + tpay(ps, suf(ts, j + 1)));
                    assert(pvar_post(ts, i, td));
                }
            }
        } else {
            assert(pvar(ts, i, td) == Some((c, Seq::<Ty>::empty(), i + 1)));
            assert(suf(ts, i) =~= seq![Tok::Id(c)] + tpay(Seq::<Ty>::empty(), suf(ts, i + 1)));
            assert(pvar_post(ts, i, td));
        }
    }
}

/// 直和型の構築子の並びの健全性。
pub proof fn pvars_sound(ts: Seq<Tok>, i: nat, td: nat)
    ensures
        pvars_post(ts, i, td),
    decreases ts.len() - i,
{
    pvar_sound(ts, i, td);
    if let Some((c, ps, j)) = pvar(ts, i, td) {
        assert(pvar_post(ts, i, td));
        if sym(ts, j, '|') && i < j {
            pfx1(ts, j);
            pvars_sound(ts, j + 1, td);
            if let Some((vs, m)) = pvars(ts, j + 1, td) {
                assert(pvars_post(ts, j + 1, td));
                let x = (c, ps);
                let s = seq![x] + vs;
                tvars_head(s, 0, suf(ts, m));
                tvars_shift(x, vs, 0, suf(ts, m));
                bvars_shift(x, vs, 0, td);
                assert(word_tok(c) == Tok::Id(c));
                assert(pvars(ts, i, td) == Some((s, m)));
                assert(i < m);
                assert(m <= ts.len());
                assert(s.len() > 0);
                assert(suf(ts, i) =~= tvars(s, 0, suf(ts, m)));
                assert(cname_ok(c));
                assert(bts(ps, 0, td));
                assert(bvars(vs, 0, td));
                assert(bvars(s, 1, td) == bvars(vs, 0, td));
                assert(bvars(s, 0, td));
                assert(pvars_post(ts, i, td));
            }
        } else {
            assert(pvars(ts, i, td) == Some((seq![(c, ps)], j)));
            assert(word_tok(c) == Tok::Id(c));
            assert(suf(ts, i) =~= tvars(seq![(c, ps)], 0, suf(ts, j)));
            assert(cname_ok(c));
            assert(bts(ps, 0, td));
            assert(bvars(seq![(c, ps)], 1, td));
            assert(bvars(seq![(c, ps)], 0, td));
            assert(pvars_post(ts, i, td));
        }
    }
}

pub open spec fn pd_post(ts: Seq<Tok>, i: nat, d: nat, td: nat) -> bool {
    match pd(ts, i, d, td) {
        Some((x, j)) => i < j <= ts.len() && suf(ts, i) == tdecl(x, suf(ts, j)) && bd(x, d, td),
        None => true,
    }
}

pub proof fn pd_sound(ts: Seq<Tok>, i: nat, d: nat, td: nat)
    ensures
        pd_post(ts, i, d, td),
{
    if kwat(ts, i, Kw::Fn) {
        if let Some(f) = idt(ts, i + 1) {
            if sym(ts, i + 2, '(') {
                pparams_sound(ts, i + 3, td);
                if let Some((ps, j)) = pparams(ts, i + 3, td) {
                    if j < ts.len() && ts[j as int] == Tok::Arrow {
                        pt_sound(ts, j + 1, td);
                        if let Some((r, m)) = pt(ts, j + 1, td) {
                            if sym(ts, m, '=') {
                                pe_sound(ts, m + 1, d, td);
                                if let Some((b, q)) = pe(ts, m + 1, d, td) {
                                    pfx1(ts, i);
                                    pfx1(ts, i + 1);
                                    pfx1(ts, i + 2);
                                    pfx1(ts, j);
                                    pfx1(ts, m);
                                    let x = pd(ts, i, d, td)->Some_0.0;
                                    assert(suf(ts, i) =~= tdecl(x, suf(ts, q)));
                                }
                            }
                        }
                    }
                }
            }
        }
    } else if kwat(ts, i, Kw::Entry) {
        if let Some(x) = idt(ts, i + 1) {
            pfx1(ts, i);
            pfx1(ts, i + 1);
            let y = pd(ts, i, d, td)->Some_0.0;
            assert(suf(ts, i) =~= tdecl(y, suf(ts, i + 2)));
        }
    } else if i < ts.len() && ts[i as int] == Tok::Id(tyw()) {
        if let Some(r) = idt(ts, i + 1) {
            if sym(ts, i + 2, '=') && sym(ts, i + 3, '{') {
                pfds_sound(ts, i + 4, td);
                assert(pfds_post(ts, i + 4, td));
                if let Some((fs, tc, j)) = pfds(ts, i + 4, td) {
                    pfx1(ts, i);
                    pfx1(ts, i + 1);
                    pfx1(ts, i + 2);
                    pfx1(ts, i + 3);
                    assert(word_tok(r) == Tok::Id(r));
                    let y = pd(ts, i, d, td)->Some_0.0;
                    assert(suf(ts, i) =~= tdecl(y, suf(ts, j)));
                }
            } else if sym(ts, i + 2, '=') {
                pvars_sound(ts, i + 3, td);
                if let Some((vs, j)) = pvars(ts, i + 3, td) {
                    pfx1(ts, i);
                    pfx1(ts, i + 1);
                    pfx1(ts, i + 2);
                    assert(word_tok(r) == Tok::Id(r));
                    let y = pd(ts, i, d, td)->Some_0.0;
                    assert(suf(ts, i) =~= tdecl(y, suf(ts, j)));
                }
            }
        }
    }
}

pub proof fn pds_sound(ts: Seq<Tok>, i: nat, d: nat, td: nat)
    requires
        i <= ts.len(),
    ensures
        pds(ts, i, d, td) matches Some(p) ==> suf(ts, i) == tds(p, 0) && bds(p, 0, d, td),
    decreases ts.len() - i,
{
    if i >= ts.len() {
        assert(suf(ts, i) =~= Seq::<Tok>::empty());
    } else {
        pd_sound(ts, i, d, td);
        if let Some((x, j)) = pd(ts, i, d, td) {
            if i < j <= ts.len() {
                pds_sound(ts, j, d, td);
                if let Some(xs) = pds(ts, j, d, td) {
                    tds_shift(x, xs, 0);
                    bds_shift(x, xs, 0, d, td);
                    let s = seq![x] + xs;
                    assert(s[0] == x);
                }
            }
        }
    }
}

// ------------------------------------------------------------------ 定理

/// parser 健全性：受理した AST の token 列は source の字句解析結果に等しく、
/// 深さ上限と名前規則（IDENT、予約語でない）を満たす。
pub proof fn parse_sound(s: Seq<char>, d: nat, td: nat)
    ensures
        parse(s, d, td) matches Some(p) ==> lex(s) == Some(tds(p, 0)) && bds(p, 0, d, td),
{
    if let Some(ts) = lex(s) {
        pds_sound(ts, 0, d, td);
        assert(suf(ts, 0) =~= ts);
    }
}

/// parser 完全性：source が深さ上限内で名前が IDENT の AST P の token 列に字句解析されるなら、
/// parser は P を返す。
pub proof fn parse_complete(s: Seq<char>, d: nat, td: nat, p: Seq<Sd>)
    requires
        lex(s) == Some(tds(p, 0)),
        bds(p, 0, d, td),
    ensures
        parse(s, d, td) == Some(p),
{
    let ts = tds(p, 0);
    assert(suf(ts, 0) =~= ts);
    pds_complete(ts, 0, d, td, p, 0);
    assert(p.subrange(0, p.len() as int) =~= p);
}

/// EBNF の非曖昧性：上限内の AST は token 列で一意に決まる。
pub proof fn toks_unique(p1: Seq<Sd>, p2: Seq<Sd>, d: nat, td: nat)
    requires
        bds(p1, 0, d, td),
        bds(p2, 0, d, td),
        tds(p1, 0) == tds(p2, 0),
    ensures
        p1 == p2,
{
    let ts = tds(p1, 0);
    assert(suf(ts, 0) =~= ts);
    pds_complete(ts, 0, d, td, p1, 0);
    pds_complete(ts, 0, d, td, p2, 0);
    assert(p1.subrange(0, p1.len() as int) =~= p1);
    assert(p2.subrange(0, p2.len() as int) =~= p2);
}

/// formatter の AST 保存性：正準ソースを parse すると元の AST に戻る。
pub proof fn format_preserves(p: Seq<Sd>, d: nat, td: nat)
    requires
        bds(p, 0, d, td),
    ensures
        parse(fds(p, 0), d, td) == Some(p),
        lex(fds(p, 0)) == Some(tds(p, 0)),
{
    fds_lex(p, 0, d, td);
    parse_complete(fds(p, 0), d, td, p);
}

/// formatter の冪等性：受理した source を整形して parse すると同じ AST が返り、
/// 再整形しても同じ文字列になる。整形は source の token 列を変えない。
pub proof fn format_idempotent(s: Seq<char>, d: nat, td: nat)
    requires
        parse(s, d, td) is Some,
    ensures
        ({
            let p = parse(s, d, td)->Some_0;
            &&& parse(fds(p, 0), d, td) == Some(p)
            &&& fds(parse(fds(p, 0), d, td)->Some_0, 0) == fds(p, 0)
            &&& lex(fds(p, 0)) == lex(s)
        }),
{
    let p = parse(s, d, td)->Some_0;
    parse_sound(s, d, td);
    format_preserves(p, d, td);
}

} // verus!
