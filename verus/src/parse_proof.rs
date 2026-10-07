//! parser の健全性・完全性（設計書 §11.2 の 1）と formatter の AST 保存性・冪等性（2）。

use crate::spec::*;
use crate::syntax::*;
use crate::syntax_proof::*;
use vstd::prelude::*;

verus! {

pub open spec fn suf(ts: Seq<Tok>, i: nat) -> Seq<Tok> {
    ts.subrange(i as int, ts.len() as int)
}

/// 式の直後に来てよい token 列（変数の直後の `(` は呼出しと読まれる）。
pub open spec fn nf(k: Seq<Tok>) -> bool {
    k.len() == 0 || k[0] != Tok::Sym('(')
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
        Ty::Pair(a, b) => {
            tt_app(*b, seq![Tok::Sym('>')] + k);
            tt_app(*b, seq![Tok::Sym('>')] + z);
            tt_app(*a, seq![Tok::Sym(',')] + tt(*b, seq![Tok::Sym('>')] + k));
            tt_app(*a, seq![Tok::Sym(',')] + tt(*b, seq![Tok::Sym('>')] + z));
        },
        _ => {},
    }
    assert(tt(t, k) =~= tt(t, z) + k);
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
            tt_app(t, seq![Tok::Sym(']'), Tok::Sym('(')] + targs(es, 0, k));
            tt_app(t, seq![Tok::Sym(']'), Tok::Sym('(')] + targs(es, 0, z));
        },
        Sx::Some(a) => {
            te_app(*a, seq![Tok::Sym(')')] + k);
            te_app(*a, seq![Tok::Sym(')')] + z);
        },
        Sx::None(t) => {
            tt_app(t, seq![Tok::Sym(']')] + k);
            tt_app(t, seq![Tok::Sym(']')] + z);
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
        Sx::Let(_, a, b) => {
            te_app(*b, k);
            te_app(*a, seq![Tok::Kw(Kw::In)] + te(*b, k));
            te_app(*a, seq![Tok::Kw(Kw::In)] + te(*b, z));
        },
        Sx::If(..) => te_app_if(e, k),
        Sx::Fold(..) => te_app_fold(e, k),
        Sx::Match(..) => te_app_match(e, k),
        _ => {},
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
        let mid = seq![Tok::Sym(','), Tok::Sym('|'), Tok::Id(a), Tok::Sym(','), Tok::Id(x), Tok::Sym('|')];
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
        let mid = seq![Tok::Sym(','), Tok::Sym('|'), Tok::Id(x), Tok::Sym('|')];
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

pub proof fn tdecl_app(x: Sd, k: Seq<Tok>)
    ensures
        tdecl(x, k) == tdecl(x, Seq::empty()) + k,
        tdecl(x, Seq::empty()).len() > 0,
        tdecl(x, k)[0] == Tok::Kw(Kw::Fn) || tdecl(x, k)[0] == Tok::Kw(Kw::Entry),
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
        Ty::List(a) => {
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
        Ty::Int => hd(ts, i, seq![Tok::Kw(Kw::TInt)], k),
        Ty::Bool => hd(ts, i, seq![Tok::Kw(Kw::TBool)], k),
        Ty::Unit => hd(ts, i, seq![Tok::Kw(Kw::TUnit)], k),
    }
}

pub open spec fn pe_pre(ts: Seq<Tok>, i: nat, d: nat, td: nat, e: Sx, k: Seq<Tok>) -> bool {
    &&& i <= ts.len()
    &&& suf(ts, i) == te(e, k)
    &&& bx(e, d, td)
    &&& nf(k)
}

pub proof fn pe_complete(ts: Seq<Tok>, i: nat, d: nat, td: nat, e: Sx, k: Seq<Tok>)
    requires
        pe_pre(ts, i, d, td, e, k),
    ensures
        pe(ts, i, d, td) == Some((e, (ts.len() - k.len()) as nat)),
    decreases e, 1nat,
{
    match e {
        Sx::Int(n) => hd(ts, i, seq![Tok::Int(n)], k),
        Sx::Bool(b) => hd(ts, i, seq![Tok::Kw(if b { Kw::True } else { Kw::False })], k),
        Sx::Unit => hd(ts, i, seq![Tok::Kw(Kw::Unit)], k),
        Sx::Var(x) => {
            hd(ts, i, seq![Tok::Id(x)], k);
            if k.len() > 0 {
                assert(k =~= seq![k[0]] + k.subrange(1, k.len() as int));
                hd(ts, i + 1, seq![k[0]], k.subrange(1, k.len() as int));
            }
        },
        Sx::List(..) => pe_complete_list(ts, i, d, td, e, k),
        Sx::Some(..) => pe_complete_some(ts, i, d, td, e, k),
        Sx::None(..) => pe_complete_none(ts, i, d, td, e, k),
        Sx::Pair(..) => pe_complete_pair(ts, i, d, td, e, k),
        Sx::Builtin(..) => pe_complete_builtin(ts, i, d, td, e, k),
        Sx::Call(..) => pe_complete_call(ts, i, d, td, e, k),
        Sx::Let(..) => pe_complete_let(ts, i, d, td, e, k),
        Sx::If(..) => pe_complete_if(ts, i, d, td, e, k),
        Sx::Fold(..) => pe_complete_fold(ts, i, d, td, e, k),
        Sx::Match(..) => pe_complete_match(ts, i, d, td, e, k),
    }
}

proof fn pe_complete_list(ts: Seq<Tok>, i: nat, d: nat, td: nat, e: Sx, k: Seq<Tok>)
    requires
        pe_pre(ts, i, d, td, e, k),
        e is List,
    ensures
        pe(ts, i, d, td) == Some((e, (ts.len() - k.len()) as nat)),
    decreases e, 0nat,
{
    if let Sx::List(t, es) = e {
        let z = Seq::<Tok>::empty();
        let ka = seq![Tok::Sym(']'), Tok::Sym('(')] + targs(es, 0, k);
        hd(ts, i, seq![Tok::Kw(Kw::List), Tok::Sym('[')], tt(t, ka));
        pt_complete(ts, i + 2, td, t, ka);
        tt_app(t, ka);
        at_end(ts, i + 2, tt(t, z), ka);
        let j = (ts.len() - ka.len()) as nat;
        hd(ts, j, seq![Tok::Sym(']'), Tok::Sym('(')], targs(es, 0, k));
        pargs_complete(ts, j + 2, (d - 1) as nat, td, es, k);
    }
}

proof fn pe_complete_some(ts: Seq<Tok>, i: nat, d: nat, td: nat, e: Sx, k: Seq<Tok>)
    requires
        pe_pre(ts, i, d, td, e, k),
        e is Some,
    ensures
        pe(ts, i, d, td) == Some((e, (ts.len() - k.len()) as nat)),
    decreases e, 0nat,
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

proof fn pe_complete_none(ts: Seq<Tok>, i: nat, d: nat, td: nat, e: Sx, k: Seq<Tok>)
    requires
        pe_pre(ts, i, d, td, e, k),
        e is None,
    ensures
        pe(ts, i, d, td) == Some((e, (ts.len() - k.len()) as nat)),
    decreases e, 0nat,
{
    if let Sx::None(t) = e {
        let z = Seq::<Tok>::empty();
        let ka = seq![Tok::Sym(']')] + k;
        hd(ts, i, seq![Tok::Kw(Kw::None), Tok::Sym('[')], tt(t, ka));
        pt_complete(ts, i + 2, td, t, ka);
        tt_app(t, ka);
        at_end(ts, i + 2, tt(t, z), ka);
        hd(ts, (ts.len() - ka.len()) as nat, seq![Tok::Sym(']')], k);
    }
}

proof fn pe_complete_pair(ts: Seq<Tok>, i: nat, d: nat, td: nat, e: Sx, k: Seq<Tok>)
    requires
        pe_pre(ts, i, d, td, e, k),
        e is Pair,
    ensures
        pe(ts, i, d, td) == Some((e, (ts.len() - k.len()) as nat)),
    decreases e, 0nat,
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

proof fn pe_complete_builtin(ts: Seq<Tok>, i: nat, d: nat, td: nat, e: Sx, k: Seq<Tok>)
    requires
        pe_pre(ts, i, d, td, e, k),
        e is Builtin,
    ensures
        pe(ts, i, d, td) == Some((e, (ts.len() - k.len()) as nat)),
    decreases e, 0nat,
{
    if let Sx::Builtin(b, es) = e {
        hd(ts, i, seq![Tok::Kw(bkw(b)), Tok::Sym('(')], targs(es, 0, k));
        pargs_complete(ts, i + 2, (d - 1) as nat, td, es, k);
        assert(kw_b(bkw(b)) == Some(b));
    }
}

proof fn pe_complete_call(ts: Seq<Tok>, i: nat, d: nat, td: nat, e: Sx, k: Seq<Tok>)
    requires
        pe_pre(ts, i, d, td, e, k),
        e is Call,
    ensures
        pe(ts, i, d, td) == Some((e, (ts.len() - k.len()) as nat)),
    decreases e, 0nat,
{
    if let Sx::Call(f, es) = e {
        hd(ts, i, seq![Tok::Id(f), Tok::Sym('(')], targs(es, 0, k));
        pargs_complete(ts, i + 2, (d - 1) as nat, td, es, k);
    }
}

proof fn pe_complete_let(ts: Seq<Tok>, i: nat, d: nat, td: nat, e: Sx, k: Seq<Tok>)
    requires
        pe_pre(ts, i, d, td, e, k),
        e is Let,
    ensures
        pe(ts, i, d, td) == Some((e, (ts.len() - k.len()) as nat)),
    decreases e, 0nat,
{
    if let Sx::Let(x, a, b) = e {
        let z = Seq::<Tok>::empty();
        let d1 = (d - 1) as nat;
        let ka = seq![Tok::Kw(Kw::In)] + te(*b, k);
        hd(ts, i, seq![Tok::Kw(Kw::Let), Tok::Id(x), Tok::Sym('=')], te(*a, ka));
        assert(idt(ts, i + 1) == Some(x));
        pe_complete(ts, i + 3, d1, td, *a, ka);
        te_app(*a, ka);
        at_end(ts, i + 3, te(*a, z), ka);
        let j = (ts.len() - ka.len()) as nat;
        hd(ts, j, seq![Tok::Kw(Kw::In)], te(*b, k));
        pe_complete(ts, j + 1, d1, td, *b, k);
    }
}

proof fn pe_complete_if(ts: Seq<Tok>, i: nat, d: nat, td: nat, e: Sx, k: Seq<Tok>)
    requires
        pe_pre(ts, i, d, td, e, k),
        e is If,
    ensures
        pe(ts, i, d, td) == Some((e, (ts.len() - k.len()) as nat)),
    decreases e, 0nat,
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

proof fn pe_complete_fold(ts: Seq<Tok>, i: nat, d: nat, td: nat, e: Sx, k: Seq<Tok>)
    requires
        pe_pre(ts, i, d, td, e, k),
        e is Fold,
    ensures
        pe(ts, i, d, td) == Some((e, (ts.len() - k.len()) as nat)),
    decreases e, 0nat,
{
    if let Sx::Fold(l, n, a, x, b) = e {
        let z = Seq::<Tok>::empty();
        let d1 = (d - 1) as nat;
        let kb = seq![Tok::Sym(')')] + k;
        let mid = seq![Tok::Sym(','), Tok::Sym('|'), Tok::Id(a), Tok::Sym(','), Tok::Id(x), Tok::Sym('|')];
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
        assert(idt(ts, m + 2) == Some(a));
        assert(idt(ts, m + 4) == Some(x));
        pe_complete(ts, m + 6, d1, td, *b, kb);
        te_app(*b, kb);
        at_end(ts, m + 6, te(*b, z), kb);
        hd(ts, (ts.len() - kb.len()) as nat, seq![Tok::Sym(')')], k);
    }
}

proof fn pe_complete_match(ts: Seq<Tok>, i: nat, d: nat, td: nat, e: Sx, k: Seq<Tok>)
    requires
        pe_pre(ts, i, d, td, e, k),
        e is Match,
    ensures
        pe(ts, i, d, td) == Some((e, (ts.len() - k.len()) as nat)),
    decreases e, 0nat,
{
    if let Sx::Match(m, n, x, b) = e {
        let z = Seq::<Tok>::empty();
        let d1 = (d - 1) as nat;
        let kb = seq![Tok::Sym(')')] + k;
        let mid = seq![Tok::Sym(','), Tok::Sym('|'), Tok::Id(x), Tok::Sym('|')];
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
        assert(idt(ts, q + 2) == Some(x));
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
    decreases es, es.len() + 1,
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
    decreases es, es.len() - j,
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
    hd(ts, i, seq![Tok::Id(x), Tok::Sym(':')], tt(t, kt));
    assert(idt(ts, i) == Some(x));
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
        hd(ts, i, seq![Tok::Id(ps[0].0), Tok::Sym(':')], tt(ps[0].1, kt));
        pparams1_complete(ts, i, td, ps, 0, k);
        assert(ps.subrange(0, ps.len() as int) =~= ps);
    }
}

pub proof fn pd_complete(ts: Seq<Tok>, i: nat, d: nat, td: nat, x: Sd, k: Seq<Tok>)
    requires
        i <= ts.len(),
        suf(ts, i) == tdecl(x, k),
        bd(x, d, td),
        nf(k),
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
        if j + 1 < p.len() {
            tdecl_app(p[(j + 1) as int], tds(p, j + 2));
        }
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
                        if sym(ts, j, '>') {
                            pfx1(ts, i + 1);
                            pfx1(ts, j);
                            let t = pt(ts, i, d)->Some_0.0;
                            assert(suf(ts, i) =~= tt(t, suf(ts, j + 1)));
                        }
                    }
                }
            },
            Tok::Kw(Kw::TPair) => {
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

pub open spec fn pe_post(ts: Seq<Tok>, i: nat, d: nat, td: nat) -> bool {
    match pe(ts, i, d, td) {
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

pub proof fn pe_sound(ts: Seq<Tok>, i: nat, d: nat, td: nat)
    ensures
        pe_post(ts, i, d, td),
    decreases d, 1nat, 0nat,
{
    if d > 0 && i < ts.len() {
        pfx1(ts, i);
        match ts[i as int] {
            Tok::Id(x) => if ident_ok(x) && sym(ts, i + 1, '(') {
                pe_sound_call(ts, i, d, td);
            },
            Tok::Kw(k) => {
                if k == Kw::List {
                    pe_sound_list(ts, i, d, td);
                } else if k == Kw::Some {
                    pe_sound_some(ts, i, d, td);
                } else if k == Kw::None {
                    pe_sound_none(ts, i, d, td);
                } else if k == Kw::Pair {
                    pe_sound_pair(ts, i, d, td);
                } else if k == Kw::Let {
                    pe_sound_let(ts, i, d, td);
                } else if k == Kw::If {
                    pe_sound_if(ts, i, d, td);
                } else if k == Kw::Fold {
                    pe_sound_fold(ts, i, d, td);
                } else if k == Kw::MatchOption {
                    pe_sound_match(ts, i, d, td);
                } else if kw_b(k) is Some {
                    pe_sound_builtin(ts, i, d, td);
                }
            },
            _ => {},
        }
    }
}

proof fn pe_sound_call(ts: Seq<Tok>, i: nat, d: nat, td: nat)
    requires
        d > 0,
        i < ts.len(),
        ts[i as int] is Id,
        ident_ok(ts[i as int]->Id_0),
        sym(ts, i + 1, '('),
    ensures
        pe_post(ts, i, d, td),
    decreases d, 0nat, 0nat,
{
    let d1 = (d - 1) as nat;
    pargs_sound(ts, i + 2, d1, td);
    if let Some((es, j)) = pargs(ts, i + 2, d1, td) {
        pfx1(ts, i);
        pfx1(ts, i + 1);
        let e = pe(ts, i, d, td)->Some_0.0;
        assert(suf(ts, i) =~= te(e, suf(ts, j)));
    }
}

proof fn pe_sound_builtin(ts: Seq<Tok>, i: nat, d: nat, td: nat)
    requires
        d > 0,
        i < ts.len(),
        ts[i as int] is Kw,
        kw_b(ts[i as int]->Kw_0) is Some,
    ensures
        pe_post(ts, i, d, td),
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
            let e = pe(ts, i, d, td)->Some_0.0;
            assert(e == Sx::Builtin(b, es));
            assert(suf(ts, i) =~= te(e, suf(ts, j)));
        }
    }
}

proof fn pe_sound_list(ts: Seq<Tok>, i: nat, d: nat, td: nat)
    requires
        d > 0,
        i < ts.len(),
        ts[i as int] == Tok::Kw(Kw::List),
    ensures
        pe_post(ts, i, d, td),
    decreases d, 0nat, 0nat,
{
    let d1 = (d - 1) as nat;
    if sym(ts, i + 1, '[') {
        pt_sound(ts, i + 2, td);
        if let Some((t, j)) = pt(ts, i + 2, td) {
            if sym(ts, j, ']') && sym(ts, j + 1, '(') {
                pargs_sound(ts, j + 2, d1, td);
                if let Some((es, m)) = pargs(ts, j + 2, d1, td) {
                    pfx1(ts, i);
                    pfx1(ts, i + 1);
                    pfx1(ts, j);
                    pfx1(ts, j + 1);
                    let e = pe(ts, i, d, td)->Some_0.0;
                    assert(suf(ts, j) =~= seq![Tok::Sym(']'), Tok::Sym('(')] + targs(es, 0, suf(ts, m)));
                    assert(suf(ts, i) =~= te(e, suf(ts, m)));
                }
            }
        }
    }
}

proof fn pe_sound_some(ts: Seq<Tok>, i: nat, d: nat, td: nat)
    requires
        d > 0,
        i < ts.len(),
        ts[i as int] == Tok::Kw(Kw::Some),
    ensures
        pe_post(ts, i, d, td),
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
                let e = pe(ts, i, d, td)->Some_0.0;
                assert(suf(ts, i) =~= te(e, suf(ts, j + 1)));
            }
        }
    }
}

proof fn pe_sound_none(ts: Seq<Tok>, i: nat, d: nat, td: nat)
    requires
        d > 0,
        i < ts.len(),
        ts[i as int] == Tok::Kw(Kw::None),
    ensures
        pe_post(ts, i, d, td),
    decreases d, 0nat, 0nat,
{
    if sym(ts, i + 1, '[') {
        pt_sound(ts, i + 2, td);
        if let Some((t, j)) = pt(ts, i + 2, td) {
            if sym(ts, j, ']') {
                pfx1(ts, i);
                pfx1(ts, i + 1);
                pfx1(ts, j);
                let e = pe(ts, i, d, td)->Some_0.0;
                assert(suf(ts, i) =~= te(e, suf(ts, j + 1)));
            }
        }
    }
}

proof fn pe_sound_pair(ts: Seq<Tok>, i: nat, d: nat, td: nat)
    requires
        d > 0,
        i < ts.len(),
        ts[i as int] == Tok::Kw(Kw::Pair),
    ensures
        pe_post(ts, i, d, td),
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
                        let e = pe(ts, i, d, td)->Some_0.0;
                        assert(suf(ts, i) =~= te(e, suf(ts, m + 1)));
                    }
                }
            }
        }
    }
}

proof fn pe_sound_let(ts: Seq<Tok>, i: nat, d: nat, td: nat)
    requires
        d > 0,
        i < ts.len(),
        ts[i as int] == Tok::Kw(Kw::Let),
    ensures
        pe_post(ts, i, d, td),
    decreases d, 0nat, 0nat,
{
    let d1 = (d - 1) as nat;
    if let Some(x) = idt(ts, i + 1) {
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
                        let e = pe(ts, i, d, td)->Some_0.0;
                        assert(suf(ts, i) =~= te(e, suf(ts, m)));
                    }
                }
            }
        }
    }
}

proof fn pe_sound_if(ts: Seq<Tok>, i: nat, d: nat, td: nat)
    requires
        d > 0,
        i < ts.len(),
        ts[i as int] == Tok::Kw(Kw::If),
    ensures
        pe_post(ts, i, d, td),
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
                                let e = pe(ts, i, d, td)->Some_0.0;
                                assert(suf(ts, i) =~= te(e, suf(ts, q + 1)));
                            }
                        }
                    }
                }
            }
        }
    }
}

proof fn pe_sound_fold(ts: Seq<Tok>, i: nat, d: nat, td: nat)
    requires
        d > 0,
        i < ts.len(),
        ts[i as int] == Tok::Kw(Kw::Fold),
    ensures
        pe_post(ts, i, d, td),
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
                        if let (Some(a), Some(x)) = (idt(ts, m + 2), idt(ts, m + 4)) {
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
                                        let e = pe(ts, i, d, td)->Some_0.0;
                                        let mid = seq![Tok::Sym(','), Tok::Sym('|'), Tok::Id(a), Tok::Sym(','), Tok::Id(x), Tok::Sym('|')];
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

proof fn pe_sound_match(ts: Seq<Tok>, i: nat, d: nat, td: nat)
    requires
        d > 0,
        i < ts.len(),
        ts[i as int] == Tok::Kw(Kw::MatchOption),
    ensures
        pe_post(ts, i, d, td),
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
                        if let Some(x) = idt(ts, q + 2) {
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
                                        let e = pe(ts, i, d, td)->Some_0.0;
                                        let mid = seq![Tok::Sym(','), Tok::Sym('|'), Tok::Id(x), Tok::Sym('|')];
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

pub proof fn pargs_sound(ts: Seq<Tok>, i: nat, d: nat, td: nat)
    ensures
        pargs_post(ts, i, d, td),
    decreases d, 3nat, 0nat,
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
    decreases d, 2nat, ts.len() - i,
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
    if let Some(x) = idt(ts, i) {
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
