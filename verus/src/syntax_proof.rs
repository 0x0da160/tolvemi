//! 表面構文の証明（設計書 §11.2 の 1、2）。
//!
//! - 字句：正準ソースを字句解析すると AST の token 列になる（`fds_lex`）。
//! - parser 健全性：`pds` が返した AST の token 列は入力 token 列に等しく、深さ上限と名前規則を満たす
//!   （`pds_sound`）。
//! - parser 完全性：深さ上限内で名前が IDENT の AST P について、P の token 列を `pds` に与えると
//!   P が返る（`pds_complete`）。従って token 列から AST は一意に決まる（`toks_unique`）。
//! - formatter：AST 保存性 `parse(fds(P)) == P`（`format_preserves`）と冪等性（`format_idempotent`）。

use crate::bigint::*;
use crate::json::*;
use crate::spec::*;
use crate::syntax::*;
use vstd::prelude::*;

verus! {

// ------------------------------------------------------------------ 字句の補題

/// 語の直後に来てよい列（語・整数を延長しない）。
pub open spec fn safe(k: Seq<char>) -> bool {
    k.len() == 0 || !(ident_char(k[0]) || k[0] == '-' || k[0] == '.')
}

/// 識別子の直後に来てよい列（識別子を延長しない。`.` や `-` は続けてよい）。
pub open spec fn wsafe(k: Seq<char>) -> bool {
    k.len() == 0 || !ident_char(k[0])
}

/// 式 e の直後に来てよい列。整数で終わる式は、続く `.`・`-`・識別子文字と字句が混ざるので `safe` を要る。
pub open spec fn fsafe(e: Sx, k: Seq<char>) -> bool {
    if ends_int(e) {
        safe(k)
    } else {
        wsafe(k)
    }
}

pub open spec fn is_word(w: Seq<char>) -> bool {
    &&& w.len() > 0
    &&& ident_start(w[0])
    &&& forall|i: int| 0 < i < w.len() ==> ident_char(#[trigger] w[i])
}

pub proof fn lw(c: char, s: Seq<char>, u: Seq<Tok>)
    requires
        is_ws(c),
        lex(s) == Some(u),
    ensures
        lex(seq![c] + s) == Some(u),
{
    let t = seq![c] + s;
    assert(t[0] == c);
    assert(t.subrange(1, t.len() as int) =~= s);
}

pub proof fn ls(c: char, s: Seq<char>, u: Seq<Tok>)
    requires
        is_sym(c),
        lex(s) == Some(u),
    ensures
        lex(seq![c] + s) == Some(seq![Tok::Sym(c)] + u),
{
    let t = seq![c] + s;
    assert(t[0] == c);
    assert(t.subrange(1, t.len() as int) =~= s);
}

pub proof fn larrow(s: Seq<char>, u: Seq<Tok>)
    requires
        lex(s) == Some(u),
    ensures
        lex(seq!['-', '>'] + s) == Some(seq![Tok::Arrow] + u),
{
    let t = seq!['-', '>'] + s;
    assert(t[0] == '-' && t[1] == '>');
    assert(t.subrange(2, t.len() as int) =~= s);
}

proof fn wend_at(w: Seq<char>, s: Seq<char>, i: nat)
    requires
        1 <= i <= w.len(),
        forall|j: int| 0 < j < w.len() ==> ident_char(#[trigger] w[j]),
        s.len() == 0 || !ident_char(s[0]),
    ensures
        wend(w + s, i) == w.len(),
    decreases w.len() - i,
{
    let t = w + s;
    if i < w.len() {
        assert(t[i as int] == w[i as int]);
        wend_at(w, s, i + 1);
    } else if s.len() > 0 {
        assert(t[i as int] == s[0]);
    }
}

pub proof fn lword(w: Seq<char>, s: Seq<char>, u: Seq<Tok>)
    requires
        is_word(w),
        s.len() == 0 || !ident_char(s[0]),
        lex(s) == Some(u),
    ensures
        lex(w + s) == Some(seq![word_tok(w)] + u),
{
    let t = w + s;
    assert(t[0] == w[0]);
    wend_at(w, s, 1);
    assert(t.subrange(0, w.len() as int) =~= w);
    assert(t.subrange(w.len() as int, t.len() as int) =~= s);
}

pub proof fn kw_word(k: Kw)
    ensures
        is_word(kwt(k)),
        kw_of(kwt(k)) == Some(k),
{
    let w = kwt(k);
    assert forall|i: int| 0 < i < w.len() implies ident_char(#[trigger] w[i]) by {
    }
}

pub proof fn lk(k: Kw, s: Seq<char>, u: Seq<Tok>)
    requires
        s.len() == 0 || !ident_char(s[0]),
        lex(s) == Some(u),
    ensures
        lex(kwt(k) + s) == Some(seq![Tok::Kw(k)] + u),
{
    kw_word(k);
    lword(kwt(k), s, u);
}

pub proof fn li(x: Seq<char>, s: Seq<char>, u: Seq<Tok>)
    requires
        ident_ok(x),
        s.len() == 0 || !ident_char(s[0]),
        lex(s) == Some(u),
    ensures
        lex(x + s) == Some(seq![Tok::Id(x)] + u),
{
    lword(x, s, u);
}

/// 予約語の綴りは予約語から一意に決まる。
pub proof fn kw_inv(x: Seq<char>)
    requires
        kw_of(x) is Some,
    ensures
        kwt(kw_of(x)->Some_0) == x,
{
    assert(kwt(kw_of(x)->Some_0) =~= x);
}

/// hof の語は、その hof に戻る。
pub proof fn hf_kw(h: Hf)
    ensures
        kw_hf(hkw(h)) == Some(h),
{
}

/// 語が hof の語なら、その hof の語はもとの語。
pub proof fn hf_kw_inv(k: Kw)
    requires
        kw_hf(k) is Some,
    ensures
        hkw(kw_hf(k)->Some_0) == k,
{
}

/// 変数・束縛の名前（IDENT か文脈キーワード）の字句。
pub proof fn ln(x: Seq<char>, s: Seq<char>, u: Seq<Tok>)
    requires
        name_ok(x),
        s.len() == 0 || !ident_char(s[0]),
        lex(s) == Some(u),
    ensures
        lex(x + s) == Some(seq![word_tok(x)] + u),
{
    if ident_ok(x) {
        lword(x, s, u);
    } else {
        kw_inv(x);
        kw_word(kw_of(x)->Some_0);
        lword(x, s, u);
    }
}

pub proof fn digit_char(c: char)
    ensures
        dval(c) >= 0 <==> is_digit(c),
{
}

proof fn nat_dec_lead(n: nat)
    ensures
        nat_dec(n).len() >= 1,
        nat_dec(n)[0] == '0' ==> n == 0,
    decreases n,
{
    if n >= 10 {
        nat_dec_lead(n / 10);
        assert(nat_dec(n)[0] == nat_dec(n / 10)[0]);
    }
}

proof fn dend_at(t: Seq<char>, a: nat, b: nat)
    requires
        a <= b <= t.len(),
        forall|j: int| a <= j < b ==> is_digit(#[trigger] t[j]),
        b == t.len() || !is_digit(t[b as int]),
    ensures
        dend(t, a) == b,
    decreases b - a,
{
    if a < b {
        dend_at(t, a + 1, b);
    }
}

pub proof fn lint(n: int, s: Seq<char>, u: Seq<Tok>)
    requires
        safe(s),
        lex(s) == Some(u),
    ensures
        lex(int_dec(n) + s) == Some(seq![Tok::Int(n)] + u),
{
    let d = int_dec(n);
    let t = d + s;
    int_dec_props(n);
    if n < 0 {
        let m = (-n) as nat;
        nat_dec_props(m);
        nat_dec_lead(m);
        let nd = nat_dec(m);
        assert(d =~= seq!['-'] + nd);
        assert(t[0] == '-');
        assert(t[1] == nd[0]);
        digit_char(nd[0]);
        assert forall|j: int| 1 <= j < d.len() implies is_digit(#[trigger] t[j]) by {
            assert(t[j] == nd[j - 1]);
            digit_char(nd[j - 1]);
        }
        if s.len() > 0 {
            assert(t[d.len() as int] == s[0]);
        }
        dend_at(t, 1, d.len());
    } else {
        nat_dec_props(n as nat);
        nat_dec_lead(n as nat);
        assert(t[0] == d[0]);
        digit_char(d[0]);
        assert forall|j: int| 0 <= j < d.len() implies is_digit(#[trigger] t[j]) by {
            assert(t[j] == d[j]);
            digit_char(d[j]);
        }
        if s.len() > 0 {
            assert(t[d.len() as int] == s[0]);
        }
        dend_at(t, 0, d.len());
        if d.len() > 1 {
            assert(n >= 10) by {
                if n < 10 {
                    assert(d.len() == 1);
                }
            }
        }
    }
    assert(t.subrange(0, d.len() as int) =~= d);
    assert(t.subrange(d.len() as int, t.len() as int) =~= s);
}

/// t の位置 p から x が並ぶ。
pub open spec fn at_(t: Seq<char>, p: int, x: Seq<char>) -> bool {
    0 <= p && p + x.len() <= t.len() && forall|j: int| 0 <= j < x.len() ==> t[p + j] == #[trigger] x[j]
}

proof fn esc_props(c: char, q: char)
    requires
        lit_ok(c),
        q == '"' || q == '\'',
    ensures
        esc(c, q).len() == 1 || esc(c, q).len() == 2,
        esc(c, q).len() == 1 ==> esc(c, q)[0] == c && c != q && c != '\\' && (c as u32) >= 0x20,
        esc(c, q).len() == 2 ==> esc(c, q)[0] == '\\' && unesc(esc(c, q)[1], q) == Some(c),
{
}

proof fn slit_escs(t: Seq<char>, p: int, w: Seq<char>)
    requires
        str_ok(w),
        at_(t, p, escs(w, '"') + seq!['"']),
    ensures
        slit(t, p as nat) == Some((w, (p + escs(w, '"').len() + 1) as nat)),
    decreases w.len(),
{
    let x = escs(w, '"') + seq!['"'];
    if w.len() == 0 {
        assert(x[0] == '"');
        assert(t[p + 0] == x[0]);
    } else {
        let c = w[0];
        let r = w.drop_first();
        let e = esc(c, '"');
        assert(lit_ok(w[0]));
        assert(str_ok(r)) by {
            assert forall|i: int| 0 <= i < r.len() implies lit_ok(#[trigger] r[i]) by {
                assert(r[i] == w[i + 1]);
            }
        }
        esc_props(c, '"');
        assert(x =~= e + (escs(r, '"') + seq!['"']));
        let y = escs(r, '"') + seq!['"'];
        assert(at_(t, p + e.len(), y)) by {
            assert forall|j: int| 0 <= j < y.len() implies t[p + e.len() + j] == #[trigger] y[j] by {
                assert(x[e.len() + j] == y[j]);
                assert(t[p + (e.len() + j)] == x[e.len() + j]);
            }
        }
        slit_escs(t, p + e.len(), r);
        assert(t[p + 0] == x[0]);
        assert(x[0] == e[0]);
        if e.len() == 2 {
            assert(t[p + 1] == x[1]);
            assert(x[1] == e[1]);
        }
        assert(seq![c] + r =~= w);
    }
}

pub proof fn lstr(w: Seq<char>, s: Seq<char>, u: Seq<Tok>)
    requires
        str_ok(w),
        lex(s) == Some(u),
    ensures
        lex(seq!['"'] + (escs(w, '"') + (seq!['"'] + s))) == Some(seq![Tok::Str(w)] + u),
{
    let t = seq!['"'] + (escs(w, '"') + (seq!['"'] + s));
    let x = escs(w, '"') + seq!['"'];
    assert(at_(t, 1, x)) by {
        assert forall|j: int| 0 <= j < x.len() implies t[1 + j] == #[trigger] x[j] by {}
    }
    slit_escs(t, 1, w);
    let j = 1 + escs(w, '"').len() + 1;
    assert(t[0] == '"');
    assert(t.subrange(j as int, t.len() as int) =~= s);
}

pub proof fn lchr(c: char, s: Seq<char>, u: Seq<Tok>)
    requires
        lit_ok(c),
        lex(s) == Some(u),
    ensures
        lex(seq!['\''] + (esc(c, '\'') + (seq!['\''] + s))) == Some(seq![Tok::Chr(c)] + u),
{
    let t = seq!['\''] + (esc(c, '\'') + (seq!['\''] + s));
    let e = esc(c, '\'');
    esc_props(c, '\'');
    assert(t[0] == '\'');
    if e.len() == 1 {
        assert(t[1] == c);
        assert(t[2] == '\'');
        assert(t.subrange(3, t.len() as int) =~= s);
    } else {
        assert(t[1] == '\\');
        assert(t[2] == e[1]);
        assert(t[3] == '\'');
        assert(t.subrange(4, t.len() as int) =~= s);
    }
}

/// ", " の後に s。
pub proof fn lcs(s: Seq<char>, u: Seq<Tok>)
    requires
        lex(s) == Some(u),
    ensures
        lex(seq![',', ' '] + s) == Some(seq![Tok::Sym(',')] + u),
{
    lw(' ', s, u);
    ls(',', seq![' '] + s, u);
    assert(seq![',', ' '] + s =~= seq![','] + (seq![' '] + s));
}

// ------------------------------------------------------------------ 正準ソースの字句解析

#[verifier::rlimit(200)]
pub proof fn ft_lex(t: Ty, k: Seq<char>, u: Seq<Tok>)
    requires
        lex(k) == Some(u),
        safe(k),
    ensures
        lex(ft(t, k)) == Some(tt(t, u)),
    decreases t,
{
    match t {
        Ty::Int => lk(Kw::TInt, k, u),
        Ty::Bool => lk(Kw::TBool, k, u),
        Ty::Unit => lk(Kw::TUnit, k, u),
        Ty::Char => lk(Kw::TChar, k, u),
        Ty::List(a) => if *a == Ty::Char {
            lk(Kw::TString, k, u);
        } else {
            let k1 = seq!['>'] + k;
            ls('>', k, u);
            ft_lex(*a, k1, seq![Tok::Sym('>')] + u);
            let k2 = seq!['<'] + ft(*a, k1);
            ls('<', ft(*a, k1), tt(*a, seq![Tok::Sym('>')] + u));
            lk(Kw::TList, k2, seq![Tok::Sym('<')] + tt(*a, seq![Tok::Sym('>')] + u));
            assert(seq![Tok::Kw(Kw::TList)] + (seq![Tok::Sym('<')] + tt(*a, seq![Tok::Sym('>')] + u))
                =~= tt(t, u));
        },
        Ty::Option(a) => {
            let k1 = seq!['>'] + k;
            ls('>', k, u);
            ft_lex(*a, k1, seq![Tok::Sym('>')] + u);
            let k2 = seq!['<'] + ft(*a, k1);
            ls('<', ft(*a, k1), tt(*a, seq![Tok::Sym('>')] + u));
            lk(Kw::TOption, k2, seq![Tok::Sym('<')] + tt(*a, seq![Tok::Sym('>')] + u));
            assert(seq![Tok::Kw(Kw::TOption)] + (seq![Tok::Sym('<')] + tt(*a, seq![Tok::Sym('>')] + u))
                =~= tt(t, u));
        },
        Ty::Pair(a, b) => {
            let kb = seq!['>'] + k;
            let ub = seq![Tok::Sym('>')] + u;
            ls('>', k, u);
            ft_lex(*b, kb, ub);
            let ka = seq![',', ' '] + ft(*b, kb);
            let ua = seq![Tok::Sym(',')] + tt(*b, ub);
            lcs(ft(*b, kb), tt(*b, ub));
            ft_lex(*a, ka, ua);
            let k2 = seq!['<'] + ft(*a, ka);
            ls('<', ft(*a, ka), tt(*a, ua));
            lk(Kw::TPair, k2, seq![Tok::Sym('<')] + tt(*a, ua));
            assert(seq![Tok::Kw(Kw::TPair)] + (seq![Tok::Sym('<')] + tt(*a, ua)) =~= tt(t, u));
        },
        Ty::Result(a, b) => {
            let kb = seq!['>'] + k;
            let ub = seq![Tok::Sym('>')] + u;
            ls('>', k, u);
            ft_lex(*b, kb, ub);
            let ka = seq![',', ' '] + ft(*b, kb);
            let ua = seq![Tok::Sym(',')] + tt(*b, ub);
            lcs(ft(*b, kb), tt(*b, ub));
            ft_lex(*a, ka, ua);
            let k2 = seq!['<'] + ft(*a, ka);
            ls('<', ft(*a, ka), tt(*a, ua));
            lk(Kw::TResult, k2, seq![Tok::Sym('<')] + tt(*a, ua));
            assert(seq![Tok::Kw(Kw::TResult)] + (seq![Tok::Sym('<')] + tt(*a, ua)) =~= tt(t, u));
        },
    }
}

/// 式の深さ上限は字句には関係しないが、名前の妥当性を bx から取り出すために使う。
pub proof fn fe_lex(e: Sx, d: nat, td: nat, k: Seq<char>, u: Seq<Tok>)
    requires
        bx(e, d, td),
        lex(k) == Some(u),
        fsafe(e, k),
    ensures
        lex(fe(e, k)) == Some(te(e, u)),
    decreases e, 1nat,
{
    match e {
        Sx::Int(n) => lint(n, k, u),
        Sx::Chr(c) => lchr(c, k, u),
        Sx::Str(w) => lstr(w, k, u),
        Sx::Bool(b) => lk(if b { Kw::True } else { Kw::False }, k, u),
        Sx::Unit => lk(Kw::Unit, k, u),
        Sx::Var(x) => ln(x, k, u),
        Sx::List(t, es) => fe_lex_list(e, d, td, k, u),
        Sx::Some(a) => fe_lex_some(e, d, td, k, u),
        Sx::None(t) => fe_lex_none(e, d, td, k, u),
        Sx::Pair(a, b) => fe_lex_pair(e, d, td, k, u),
        Sx::Builtin(b, es) => fe_lex_builtin(e, d, td, k, u),
        Sx::Call(f, es) => fe_lex_call(e, d, td, k, u),
        Sx::Let(x, a, b) => fe_lex_let(e, d, td, k, u),
        Sx::If(c, a, b) => fe_lex_if(e, d, td, k, u),
        Sx::Fold(l, i, a, x, b) => fe_lex_fold(e, d, td, k, u),
        Sx::Match(m, n, x, b) => fe_lex_match(e, d, td, k, u),
        Sx::Inj(..) => fe_lex_inj(e, d, td, k, u),
        Sx::MatchR(..) => fe_lex_matchr(e, d, td, k, u),
        Sx::Fld(..) => fe_lex_fld(e, d, td, k, u),
        Sx::Rec(..) => fe_lex_rec(e, d, td, k, u),
        Sx::SumMatch(..) => fe_lex_sumatch(e, d, td, k, u),
        Sx::Hof(..) => fe_lex_hof(e, d, td, k, u),
    }
}

proof fn fe_lex_list(e: Sx, d: nat, td: nat, k: Seq<char>, u: Seq<Tok>)
    requires
        e is List,
        bx(e, d, td),
        lex(k) == Some(u),
        fsafe(e, k),
    ensures
        lex(fe(e, k)) == Some(te(e, u)),
    decreases e, 0nat,
{
    let d1 = (d - 1) as nat;
    match e {
        Sx::List(t, es) => {
        fargs_lex(es, 0, d1, td, k, u);
        let ka = seq!['>', '('] + fargs(es, 0, k);
        let ua = seq![Tok::Sym('>'), Tok::Sym('(')] + targs(es, 0, u);
        ls('(', fargs(es, 0, k), targs(es, 0, u));
        ls('>', seq!['('] + fargs(es, 0, k), seq![Tok::Sym('(')] + targs(es, 0, u));
        assert(ka =~= seq!['>'] + (seq!['('] + fargs(es, 0, k)));
        assert(ua =~= seq![Tok::Sym('>')] + (seq![Tok::Sym('(')] + targs(es, 0, u)));
        ft_lex(t, ka, ua);
        ls('<', ft(t, ka), tt(t, ua));
        lk(Kw::List, seq!['<'] + ft(t, ka), seq![Tok::Sym('<')] + tt(t, ua));
        assert(seq![Tok::Kw(Kw::List)] + (seq![Tok::Sym('<')] + tt(t, ua)) =~= te(e, u));
        },
        _ => {},
    }
}

proof fn fe_lex_some(e: Sx, d: nat, td: nat, k: Seq<char>, u: Seq<Tok>)
    requires
        e is Some,
        bx(e, d, td),
        lex(k) == Some(u),
        fsafe(e, k),
    ensures
        lex(fe(e, k)) == Some(te(e, u)),
    decreases e, 0nat,
{
    let d1 = (d - 1) as nat;
    match e {
        Sx::Some(a) => {
        ls(')', k, u);
        fe_lex(*a, d1, td, seq![')'] + k, seq![Tok::Sym(')')] + u);
        let ua = te(*a, seq![Tok::Sym(')')] + u);
        ls('(', fe(*a, seq![')'] + k), ua);
        lk(Kw::Some, seq!['('] + fe(*a, seq![')'] + k), seq![Tok::Sym('(')] + ua);
        assert(seq![Tok::Kw(Kw::Some)] + (seq![Tok::Sym('(')] + ua) =~= te(e, u));
        },
        _ => {},
    }
}

proof fn fe_lex_none(e: Sx, d: nat, td: nat, k: Seq<char>, u: Seq<Tok>)
    requires
        e is None,
        bx(e, d, td),
        lex(k) == Some(u),
        fsafe(e, k),
    ensures
        lex(fe(e, k)) == Some(te(e, u)),
    decreases e, 0nat,
{
    let d1 = (d - 1) as nat;
    match e {
        Sx::None(t) => {
        let kc = seq!['>', '(', ')'] + k;
        let uc = seq![Tok::Sym('>'), Tok::Sym('('), Tok::Sym(')')] + u;
        ls(')', k, u);
        ls('(', seq![')'] + k, seq![Tok::Sym(')')] + u);
        ls('>', seq!['('] + (seq![')'] + k), seq![Tok::Sym('(')] + (seq![Tok::Sym(')')] + u));
        assert(kc =~= seq!['>'] + (seq!['('] + (seq![')'] + k)));
        assert(uc =~= seq![Tok::Sym('>')] + (seq![Tok::Sym('(')] + (seq![Tok::Sym(')')] + u)));
        ft_lex(t, kc, uc);
        let ua = tt(t, uc);
        ls('<', ft(t, kc), ua);
        lk(Kw::None, seq!['<'] + ft(t, kc), seq![Tok::Sym('<')] + ua);
        assert(seq![Tok::Kw(Kw::None)] + (seq![Tok::Sym('<')] + ua) =~= te(e, u));
        },
        _ => {},
    }
}

proof fn fe_lex_pair(e: Sx, d: nat, td: nat, k: Seq<char>, u: Seq<Tok>)
    requires
        e is Pair,
        bx(e, d, td),
        lex(k) == Some(u),
        fsafe(e, k),
    ensures
        lex(fe(e, k)) == Some(te(e, u)),
    decreases e, 0nat,
{
    let d1 = (d - 1) as nat;
    match e {
        Sx::Pair(a, b) => {
        ls(')', k, u);
        fe_lex(*b, d1, td, seq![')'] + k, seq![Tok::Sym(')')] + u);
        let kb = fe(*b, seq![')'] + k);
        let ub = te(*b, seq![Tok::Sym(')')] + u);
        lcs(kb, ub);
        fe_lex(*a, d1, td, seq![',', ' '] + kb, seq![Tok::Sym(',')] + ub);
        let ua = te(*a, seq![Tok::Sym(',')] + ub);
        ls('(', fe(*a, seq![',', ' '] + kb), ua);
        lk(Kw::Pair, seq!['('] + fe(*a, seq![',', ' '] + kb), seq![Tok::Sym('(')] + ua);
        assert(seq![Tok::Kw(Kw::Pair)] + (seq![Tok::Sym('(')] + ua) =~= te(e, u));
        },
        _ => {},
    }
}

proof fn fe_lex_builtin(e: Sx, d: nat, td: nat, k: Seq<char>, u: Seq<Tok>)
    requires
        e is Builtin,
        bx(e, d, td),
        lex(k) == Some(u),
        fsafe(e, k),
    ensures
        lex(fe(e, k)) == Some(te(e, u)),
    decreases e, 0nat,
{
    let d1 = (d - 1) as nat;
    match e {
        Sx::Builtin(b, es) => {
        fargs_lex(es, 0, d1, td, k, u);
        ls('(', fargs(es, 0, k), targs(es, 0, u));
        lk(bkw(b), seq!['('] + fargs(es, 0, k), seq![Tok::Sym('(')] + targs(es, 0, u));
        assert(seq![Tok::Kw(bkw(b))] + (seq![Tok::Sym('(')] + targs(es, 0, u)) =~= te(e, u));
        },
        _ => {},
    }
}

proof fn fe_lex_call(e: Sx, d: nat, td: nat, k: Seq<char>, u: Seq<Tok>)
    requires
        e is Call,
        bx(e, d, td),
        lex(k) == Some(u),
        fsafe(e, k),
    ensures
        lex(fe(e, k)) == Some(te(e, u)),
    decreases e, 0nat,
{
    let d1 = (d - 1) as nat;
    match e {
        Sx::Call(f, es) => {
        fargs_lex(es, 0, d1, td, k, u);
        ls('(', fargs(es, 0, k), targs(es, 0, u));
        li(f, seq!['('] + fargs(es, 0, k), seq![Tok::Sym('(')] + targs(es, 0, u));
        assert(seq![Tok::Id(f)] + (seq![Tok::Sym('(')] + targs(es, 0, u)) =~= te(e, u));
        },
        _ => {},
    }
}

#[verifier::rlimit(40)]
proof fn fe_lex_let(e: Sx, d: nat, td: nat, k: Seq<char>, u: Seq<Tok>)
    requires
        e is Let,
        bx(e, d, td),
        lex(k) == Some(u),
        fsafe(e, k),
    ensures
        lex(fe(e, k)) == Some(te(e, u)),
    decreases e, 0nat,
{
    let d1 = (d - 1) as nat;
    match e {
        Sx::Let(x, a, b) => {
        fe_lex(*b, d1, td, k, u);
        let l1 = fe(*b, k);
        let v1 = te(*b, u);
        lw(' ', l1, v1);
        lk(Kw::In, seq![' '] + l1, v1);
        let l3 = kwt(Kw::In) + (seq![' '] + l1);
        let v3 = seq![Tok::Kw(Kw::In)] + v1;
        lw(' ', l3, v3);
        fe_lex(*a, d1, td, seq![' '] + l3, v3);
        let l5 = fe(*a, seq![' '] + l3);
        let v5 = te(*a, v3);
        lw(' ', l5, v5);
        ls('=', seq![' '] + l5, v5);
        lw(' ', seq!['='] + (seq![' '] + l5), seq![Tok::Sym('=')] + v5);
        assert(seq![' ', '=', ' '] + l5 =~= seq![' '] + (seq!['='] + (seq![' '] + l5)));
        let l6 = seq![' ', '=', ' '] + l5;
        ln(x, l6, seq![Tok::Sym('=')] + v5);
        lw(' ', x + l6, seq![word_tok(x)] + (seq![Tok::Sym('=')] + v5));
        lk(Kw::Let, seq![' '] + (x + l6), seq![word_tok(x)] + (seq![Tok::Sym('=')] + v5));
        assert(seq![Tok::Kw(Kw::Let)] + (seq![word_tok(x)] + (seq![Tok::Sym('=')] + v5)) =~= te(e, u));
        },
        _ => {},
    }
}

proof fn fe_lex_if(e: Sx, d: nat, td: nat, k: Seq<char>, u: Seq<Tok>)
    requires
        e is If,
        bx(e, d, td),
        lex(k) == Some(u),
        fsafe(e, k),
    ensures
        lex(fe(e, k)) == Some(te(e, u)),
    decreases e, 0nat,
{
    let d1 = (d - 1) as nat;
    match e {
        Sx::If(c, a, b) => {
        ls(')', k, u);
        fe_lex(*b, d1, td, seq![')'] + k, seq![Tok::Sym(')')] + u);
        let kb = fe(*b, seq![')'] + k);
        let ub = te(*b, seq![Tok::Sym(')')] + u);
        lcs(kb, ub);
        fe_lex(*a, d1, td, seq![',', ' '] + kb, seq![Tok::Sym(',')] + ub);
        let ka = fe(*a, seq![',', ' '] + kb);
        let ua = te(*a, seq![Tok::Sym(',')] + ub);
        lcs(ka, ua);
        fe_lex(*c, d1, td, seq![',', ' '] + ka, seq![Tok::Sym(',')] + ua);
        let uc = te(*c, seq![Tok::Sym(',')] + ua);
        ls('(', fe(*c, seq![',', ' '] + ka), uc);
        lk(Kw::If, seq!['('] + fe(*c, seq![',', ' '] + ka), seq![Tok::Sym('(')] + uc);
        assert(seq![Tok::Kw(Kw::If)] + (seq![Tok::Sym('(')] + uc) =~= te(e, u));
        },
        _ => {},
    }
}

proof fn fe_lex_fold(e: Sx, d: nat, td: nat, k: Seq<char>, u: Seq<Tok>)
    requires
        e is Fold,
        bx(e, d, td),
        lex(k) == Some(u),
        fsafe(e, k),
    ensures
        lex(fe(e, k)) == Some(te(e, u)),
    decreases e, 0nat,
{
    let d1 = (d - 1) as nat;
    match e {
        Sx::Fold(l, i, a, x, b) => {
        ls(')', k, u);
        fe_lex(*b, d1, td, seq![')'] + k, seq![Tok::Sym(')')] + u);
        let kb = fe(*b, seq![')'] + k);
        let ub = te(*b, seq![Tok::Sym(')')] + u);
        // "|" " " body
        lw(' ', kb, ub);
        ls('|', seq![' '] + kb, ub);
        assert(seq!['|', ' '] + kb =~= seq!['|'] + (seq![' '] + kb));
        let k1 = seq!['|', ' '] + kb;
        let u1 = seq![Tok::Sym('|')] + ub;
        ln(x, k1, u1);
        let k2 = x + k1;
        let u2 = seq![word_tok(x)] + u1;
        lcs(k2, u2);
        let k3 = seq![',', ' '] + k2;
        let u3 = seq![Tok::Sym(',')] + u2;
        ln(a, k3, u3);
        let k4 = a + k3;
        let u4 = seq![word_tok(a)] + u3;
        ls('|', k4, u4);
        lcs(seq!['|'] + k4, seq![Tok::Sym('|')] + u4);
        assert(seq![',', ' ', '|'] + k4 =~= seq![',', ' '] + (seq!['|'] + k4));
        let k5 = seq![',', ' ', '|'] + k4;
        let u5 = seq![Tok::Sym(','), Tok::Sym('|')] + u4;
        assert(seq![Tok::Sym(',')] + (seq![Tok::Sym('|')] + u4) =~= u5);
        fe_lex(*i, d1, td, k5, u5);
        let ki = fe(*i, k5);
        let ui = te(*i, u5);
        lcs(ki, ui);
        fe_lex(*l, d1, td, seq![',', ' '] + ki, seq![Tok::Sym(',')] + ui);
        let ul = te(*l, seq![Tok::Sym(',')] + ui);
        ls('(', fe(*l, seq![',', ' '] + ki), ul);
        lk(Kw::Fold, seq!['('] + fe(*l, seq![',', ' '] + ki), seq![Tok::Sym('(')] + ul);
        assert(u5 =~= seq![Tok::Sym(','), Tok::Sym('|'), word_tok(a), Tok::Sym(','), word_tok(x), Tok::Sym('|')]
            + te(*b, seq![Tok::Sym(')')] + u));
        assert(seq![Tok::Kw(Kw::Fold)] + (seq![Tok::Sym('(')] + ul) =~= te(e, u));
        },
        _ => {},
    }
}

proof fn fe_lex_inj(e: Sx, d: nat, td: nat, k: Seq<char>, u: Seq<Tok>)
    requires
        e is Inj,
        bx(e, d, td),
        lex(k) == Some(u),
        fsafe(e, k),
    ensures
        lex(fe(e, k)) == Some(te(e, u)),
    decreases e, 0nat,
{
    let d1 = (d - 1) as nat;
    match e {
        Sx::Inj(ok, t, w, a) => {
        ls(')', k, u);
        fe_lex(*a, d1, td, seq![')'] + k, seq![Tok::Sym(')')] + u);
        let kx = fe(*a, seq![')'] + k);
        let ux = te(*a, seq![Tok::Sym(')')] + u);
        ls('(', kx, ux);
        ls('>', seq!['('] + kx, seq![Tok::Sym('(')] + ux);
        let kw = seq!['>', '('] + kx;
        let uw = seq![Tok::Sym('>'), Tok::Sym('(')] + ux;
        assert(kw =~= seq!['>'] + (seq!['('] + kx));
        assert(uw =~= seq![Tok::Sym('>')] + (seq![Tok::Sym('(')] + ux));
        ft_lex(w, kw, uw);
        lcs(ft(w, kw), tt(w, uw));
        let kt = seq![',', ' '] + ft(w, kw);
        let ut = seq![Tok::Sym(',')] + tt(w, uw);
        ft_lex(t, kt, ut);
        ls('<', ft(t, kt), tt(t, ut));
        let kk = if ok { Kw::Ok } else { Kw::Err };
        lk(kk, seq!['<'] + ft(t, kt), seq![Tok::Sym('<')] + tt(t, ut));
        assert(seq![Tok::Kw(kk)] + (seq![Tok::Sym('<')] + tt(t, ut)) =~= te(e, u));
        },
        _ => {},
    }
}

/// ", |x| " の後に kb。
proof fn lbar(x: Seq<char>, kb: Seq<char>, ub: Seq<Tok>)
    requires
        name_ok(x),
        lex(kb) == Some(ub),
    ensures
        lex(seq![',', ' ', '|'] + (x + (seq!['|', ' '] + kb))) == Some(
            seq![Tok::Sym(','), Tok::Sym('|'), word_tok(x), Tok::Sym('|')] + ub,
        ),
{
    lw(' ', kb, ub);
    ls('|', seq![' '] + kb, ub);
    assert(seq!['|', ' '] + kb =~= seq!['|'] + (seq![' '] + kb));
    let k1 = seq!['|', ' '] + kb;
    let u1 = seq![Tok::Sym('|')] + ub;
    ln(x, k1, u1);
    let k2 = x + k1;
    let u2 = seq![word_tok(x)] + u1;
    ls('|', k2, u2);
    lcs(seq!['|'] + k2, seq![Tok::Sym('|')] + u2);
    assert(seq![',', ' ', '|'] + k2 =~= seq![',', ' '] + (seq!['|'] + k2));
    assert(seq![Tok::Sym(',')] + (seq![Tok::Sym('|')] + u2) =~= seq![Tok::Sym(','), Tok::Sym('|'), word_tok(x), Tok::Sym('|')] + ub);
}

proof fn fe_lex_matchr(e: Sx, d: nat, td: nat, k: Seq<char>, u: Seq<Tok>)
    requires
        e is MatchR,
        bx(e, d, td),
        lex(k) == Some(u),
        fsafe(e, k),
    ensures
        lex(fe(e, k)) == Some(te(e, u)),
    decreases e, 0nat,
{
    let d1 = (d - 1) as nat;
    match e {
        Sx::MatchR(m, x, a, y, b) => {
        ls(')', k, u);
        fe_lex(*b, d1, td, seq![')'] + k, seq![Tok::Sym(')')] + u);
        let kb = fe(*b, seq![')'] + k);
        let ub = te(*b, seq![Tok::Sym(')')] + u);
        lbar(y, kb, ub);
        let k5 = seq![',', ' ', '|'] + (y + (seq!['|', ' '] + kb));
        let u5 = seq![Tok::Sym(','), Tok::Sym('|'), word_tok(y), Tok::Sym('|')] + ub;
        assert(k5[0] == ',');
        fe_lex(*a, d1, td, k5, u5);
        let ka = fe(*a, k5);
        let ua = te(*a, u5);
        lbar(x, ka, ua);
        let k6 = seq![',', ' ', '|'] + (x + (seq!['|', ' '] + ka));
        let u6 = seq![Tok::Sym(','), Tok::Sym('|'), word_tok(x), Tok::Sym('|')] + ua;
        assert(k6[0] == ',');
        fe_lex(*m, d1, td, k6, u6);
        let um = te(*m, u6);
        ls('(', fe(*m, k6), um);
        lk(Kw::MatchResult, seq!['('] + fe(*m, k6), seq![Tok::Sym('(')] + um);
        assert(seq![Tok::Kw(Kw::MatchResult)] + (seq![Tok::Sym('(')] + um) =~= te(e, u));
        },
        _ => {},
    }
}

proof fn fe_lex_match(e: Sx, d: nat, td: nat, k: Seq<char>, u: Seq<Tok>)
    requires
        e is Match,
        bx(e, d, td),
        lex(k) == Some(u),
        fsafe(e, k),
    ensures
        lex(fe(e, k)) == Some(te(e, u)),
    decreases e, 0nat,
{
    let d1 = (d - 1) as nat;
    match e {
        Sx::Match(m, n, x, b) => {
        ls(')', k, u);
        fe_lex(*b, d1, td, seq![')'] + k, seq![Tok::Sym(')')] + u);
        let kb = fe(*b, seq![')'] + k);
        let ub = te(*b, seq![Tok::Sym(')')] + u);
        // "|" " " body
        lw(' ', kb, ub);
        ls('|', seq![' '] + kb, ub);
        assert(seq!['|', ' '] + kb =~= seq!['|'] + (seq![' '] + kb));
        let k1 = seq!['|', ' '] + kb;
        let u1 = seq![Tok::Sym('|')] + ub;
        ln(x, k1, u1);
        let k2 = x + k1;
        let u2 = seq![word_tok(x)] + u1;
        ls('|', k2, u2);
        lcs(seq!['|'] + k2, seq![Tok::Sym('|')] + u2);
        assert(seq![',', ' ', '|'] + k2 =~= seq![',', ' '] + (seq!['|'] + k2));
        let k5 = seq![',', ' ', '|'] + k2;
        let u5 = seq![Tok::Sym(','), Tok::Sym('|')] + u2;
        assert(seq![Tok::Sym(',')] + (seq![Tok::Sym('|')] + u2) =~= u5);
        fe_lex(*n, d1, td, k5, u5);
        let kn = fe(*n, k5);
        let un = te(*n, u5);
        lcs(kn, un);
        fe_lex(*m, d1, td, seq![',', ' '] + kn, seq![Tok::Sym(',')] + un);
        let um = te(*m, seq![Tok::Sym(',')] + un);
        ls('(', fe(*m, seq![',', ' '] + kn), um);
        lk(Kw::MatchOption, seq!['('] + fe(*m, seq![',', ' '] + kn), seq![Tok::Sym('(')] + um);
        assert(u5 =~= seq![Tok::Sym(','), Tok::Sym('|'), word_tok(x), Tok::Sym('|')]
            + te(*b, seq![Tok::Sym(')')] + u));
        assert(seq![Tok::Kw(Kw::MatchOption)] + (seq![Tok::Sym('(')] + um) =~= te(e, u));
        },
        _ => {},
    }
}

/// 文脈語 `match` は予約語でなく、字句として Id になる。
pub proof fn mword_word()
    ensures
        is_word(mword()),
        word_tok(mword()) == Tok::Id(mword()),
        ident_ok(mword()),
{
    let w = mword();
    assert(w.len() == 5 && w[0] == 'm' && w[1] == 'a' && w[2] == 't' && w[3] == 'c' && w[4] == 'h');
    assert forall|i: int| 0 < i < w.len() implies ident_char(#[trigger] w[i]) by {}
    assert(kw_of(w) is None);
}

/// 枝の矢印 ` => ` の後に s（`=` と `>` は別々の記号）。
proof fn arrow_lex(s: Seq<char>, u: Seq<Tok>)
    requires
        lex(s) == Some(u),
    ensures
        lex(seq![' ', '=', '>', ' '] + s) == Some(seq![Tok::Sym('='), Tok::Sym('>')] + u),
{
    lw(' ', s, u);
    ls('>', seq![' '] + s, u);
    ls('=', seq!['>'] + (seq![' '] + s), seq![Tok::Sym('>')] + u);
    assert(seq![Tok::Sym('='), Tok::Sym('>')] + u =~= seq![Tok::Sym('=')] + (seq![Tok::Sym('>')] + u));
    lw(' ', seq!['='] + (seq!['>'] + (seq![' '] + s)), seq![Tok::Sym('='), Tok::Sym('>')] + u);
    assert(seq![' ', '=', '>', ' '] + s =~= seq![' '] + (seq!['='] + (seq!['>'] + (seq![' '] + s))));
}

/// 構築子のパターンの束縛の並びの字句（後ろは wsafe な k）。
proof fn fbinds_lex(bs: Seq<Seq<char>>, i: nat, k: Seq<char>, u: Seq<Tok>)
    requires
        bnames(bs),
        lex(k) == Some(u),
        wsafe(k),
    ensures
        lex(fbinds(bs, i, k)) == Some(tbinds(bs, i, u)),
    decreases bs.len() - i,
{
    if i >= bs.len() {
    } else if i + 1 == bs.len() {
        ln(bs[i as int], k, u);
    } else {
        fbinds_lex(bs, i + 1, k, u);
        let r = fbinds(bs, i + 1, k);
        let ur = tbinds(bs, i + 1, u);
        lcs(r, ur);
        ln(bs[i as int], seq![',', ' '] + r, seq![Tok::Sym(',')] + ur);
        assert(fbinds(bs, i, k) =~= bs[i as int] + (seq![',', ' '] + r));
        assert(tbinds(bs, i, u) =~= seq![word_tok(bs[i as int]), Tok::Sym(',')] + ur);
    }
}

/// 予約語の綴り kw（ok・err・some）と束縛 `kw "(" x ")"` の字句（後ろは wsafe な k）。
proof fn fpat_kwx(kw: Kw, x: Seq<char>, k: Seq<char>, u: Seq<Tok>)
    requires
        name_ok(x),
        lex(k) == Some(u),
        wsafe(k),
    ensures
        lex(kwt(kw) + (seq!['('] + (x + (seq![')'] + k)))) == Some(
            seq![Tok::Kw(kw), Tok::Sym('('), word_tok(x), Tok::Sym(')')] + u,
        ),
{
    ls(')', k, u);
    ln(x, seq![')'] + k, seq![Tok::Sym(')')] + u);
    assert(seq![word_tok(x), Tok::Sym(')')] + u =~= seq![word_tok(x)] + (seq![Tok::Sym(')')] + u));
    ls('(', x + (seq![')'] + k), seq![word_tok(x), Tok::Sym(')')] + u);
    lk(kw, seq!['('] + (x + (seq![')'] + k)), seq![Tok::Sym('(')] + (seq![word_tok(x), Tok::Sym(')')] + u));
    assert(seq![Tok::Kw(kw), Tok::Sym('('), word_tok(x), Tok::Sym(')')] + u =~= seq![Tok::Kw(kw)] + (seq![Tok::Sym('('), word_tok(x), Tok::Sym(')')] + u));
}

/// 枝の左辺（パターン）の字句（後ろは wsafe な k）。
proof fn fpat_lex(p: Spat, k: Seq<char>, u: Seq<Tok>)
    requires
        bpat(p),
        lex(k) == Some(u),
        wsafe(k),
    ensures
        lex(fpat(p, k)) == Some(tpat(p, u)),
{
    match p {
        Spat::Ctor(c, bs) => {
            if bs.len() == 0 {
                ln(c, k, u);
            } else {
                ls(')', k, u);
                fbinds_lex(bs, 0, seq![')'] + k, seq![Tok::Sym(')')] + u);
                ls('(', fbinds(bs, 0, seq![')'] + k), tbinds(bs, 0, seq![Tok::Sym(')')] + u));
                ln(c, seq!['('] + fbinds(bs, 0, seq![')'] + k), seq![Tok::Sym('(')] + tbinds(bs, 0, seq![Tok::Sym(')')] + u));
            }
        },
        Spat::Ok(x) => fpat_kwx(Kw::Ok, x, k, u),
        Spat::Err(x) => fpat_kwx(Kw::Err, x, k, u),
        Spat::Some(x) => fpat_kwx(Kw::Some, x, k, u),
        Spat::None => lk(Kw::None, k, u),
        Spat::Wild => {
            assert(is_word(seq!['_']));
            lword(seq!['_'], k, u);
        },
    }
}

/// 枝の並び（位置 i から）の字句。tail は後ろの続きで、安全な字句で始まる。
proof fn farms_lex(arms: Seq<(Spat, Sx)>, i: nat, d: nat, td: nat, tail: Seq<char>, tu: Seq<Tok>)
    requires
        barms(arms, i, d, td),
        lex(tail) == Some(tu),
        safe(tail),
    ensures
        lex(farms(arms, i, tail)) == Some(tarms(arms, i, tu)),
    decreases arms, arms.len() - i,
{
    reveal_with_fuel(barms, 1);
    if i < arms.len() {
        let p = arms[i as int].0;
        let body = arms[i as int].1;
        let last = i + 1 == arms.len();
        let kt = if last { tail } else { seq![',', ' '] + farms(arms, i + 1, tail) };
        let ut = if last { tu } else { seq![Tok::Sym(',')] + tarms(arms, i + 1, tu) };
        assert(lex(kt) == Some(ut)) by {
            if !last {
                farms_lex(arms, i + 1, d, td, tail, tu);
                lcs(farms(arms, i + 1, tail), tarms(arms, i + 1, tu));
            }
        }
        assert(safe(kt)) by {
            if !last {
                assert(kt[0] == ',');
            }
        }
        fe_lex(body, d, td, kt, ut);
        let kb = fe(body, kt);
        let ub = te(body, ut);
        arrow_lex(kb, ub);
        fpat_lex(p, seq![' ', '=', '>', ' '] + kb, seq![Tok::Sym('='), Tok::Sym('>')] + ub);
        assert(farms(arms, i, tail) =~= fpat(p, seq![' ', '=', '>', ' '] + kb));
        assert(tarms(arms, i, tu) =~= tpat(p, seq![Tok::Sym('='), Tok::Sym('>')] + ub));
    }
}

/// 字句の補題：`match e { 枝 }`（後ろの字句は k。閉じ括弧 `}` が後ろを区切る）。
proof fn fe_lex_sumatch(e: Sx, d: nat, td: nat, k: Seq<char>, u: Seq<Tok>)
    requires
        e is SumMatch,
        bx(e, d, td),
        lex(k) == Some(u),
        fsafe(e, k),
    ensures
        lex(fe(e, k)) == Some(te(e, u)),
    decreases e, 0nat,
{
    let d1 = (d - 1) as nat;
    match e {
        Sx::SumMatch(m, arms) => {
            ls('}', k, u);
            lw(' ', seq!['}'] + k, seq![Tok::Sym('}')] + u);
            assert(seq![' ', '}'] + k =~= seq![' '] + (seq!['}'] + k));
            let kc = seq![' ', '}'] + k;
            let uc = seq![Tok::Sym('}')] + u;
            assert(kc[0] == ' ');
            farms_lex(arms, 0, d1, td, kc, uc);
            let ka = farms(arms, 0, kc);
            let ua = tarms(arms, 0, uc);
            lw(' ', ka, ua);
            ls('{', seq![' '] + ka, ua);
            lw(' ', seq!['{'] + (seq![' '] + ka), seq![Tok::Sym('{')] + ua);
            let km = seq![' ', '{', ' '] + ka;
            let um = seq![Tok::Sym('{')] + ua;
            assert(km =~= seq![' '] + (seq!['{'] + (seq![' '] + ka)));
            assert(km[0] == ' ');
            assert(safe(km) && wsafe(km));
            fe_lex(*m, d1, td, km, um);
            let kmm = fe(*m, km);
            let umm = te(*m, um);
            lw(' ', kmm, umm);
            mword_word();
            lword(mword(), seq![' '] + kmm, umm);
            assert(fe(e, k) =~= mword() + (seq![' '] + kmm));
            assert(te(e, u) =~= seq![word_tok(mword())] + umm);
        },
        _ => {},
    }
}

/// 字句の補題：`hof(e, |x| b)`（後ろの字句は k。閉じ括弧 `)` が後ろを区切る）。
proof fn fe_lex_hof(e: Sx, d: nat, td: nat, k: Seq<char>, u: Seq<Tok>)
    requires
        e is Hof,
        bx(e, d, td),
        lex(k) == Some(u),
        fsafe(e, k),
    ensures
        lex(fe(e, k)) == Some(te(e, u)),
    decreases e, 0nat,
{
    let d1 = (d - 1) as nat;
    match e {
        Sx::Hof(h, l, x, b) => {
            ls(')', k, u);
            fe_lex(*b, d1, td, seq![')'] + k, seq![Tok::Sym(')')] + u);
            let kb = fe(*b, seq![')'] + k);
            let ub = te(*b, seq![Tok::Sym(')')] + u);
            // ", |x| " の後に本体
            lbar(x, kb, ub);
            let k5 = seq![',', ' ', '|'] + (x + (seq!['|', ' '] + kb));
            let u5 = seq![Tok::Sym(','), Tok::Sym('|'), word_tok(x), Tok::Sym('|')] + ub;
            assert(k5[0] == ',');
            fe_lex(*l, d1, td, k5, u5);
            let kl = fe(*l, k5);
            let ul = te(*l, u5);
            ls('(', kl, ul);
            lk(hkw(h), seq!['('] + kl, seq![Tok::Sym('(')] + ul);
            assert(fe(e, k) =~= kwt(hkw(h)) + (seq!['('] + kl));
            assert(seq![Tok::Kw(hkw(h))] + (seq![Tok::Sym('(')] + ul) =~= te(e, u));
        },
        _ => {},
    }
}

/// 名前の並びが空でないとき、名前は IDENT で、先頭は ident_ok。
proof fn nms_head(fs: Seq<Seq<char>>)
    requires
        fs.len() > 0,
        nms(fs),
    ensures
        ident_ok(fs[0]),
        nms(fs.subrange(1, fs.len() as int)),
{
    reveal_with_fuel(nms, 2);
}

/// IDENT の綴りは字句として Id になる（予約語でない）。
proof fn word_id(x: Seq<char>)
    requires
        ident_ok(x),
    ensures
        word_tok(x) == Tok::Id(x),
{
}

/// `.f` の並びが空でないなら、字句は `.` で始まる。
proof fn fdots_dot(fs: Seq<Seq<char>>, k: Seq<char>)
    requires
        fs.len() > 0,
    ensures
        fdots(fs, k).len() > 0,
        fdots(fs, k)[0] == '.',
{
    assert(fdots(fs, k) =~= seq!['.'] + (fs[0] + fdots(fs.subrange(1, fs.len() as int), k)));
}

/// 受けの後ろの `.` の並び。
pub proof fn fdots_lex(fs: Seq<Seq<char>>, k: Seq<char>, u: Seq<Tok>)
    requires
        nms(fs),
        lex(k) == Some(u),
        wsafe(k),
    ensures
        lex(fdots(fs, k)) == Some(tdots(fs, u)),
    decreases fs.len(),
{
    if fs.len() > 0 {
        nms_head(fs);
        let rest = fs.subrange(1, fs.len() as int);
        fdots_lex(rest, k, u);
        assert(wsafe(fdots(rest, k))) by {
            if rest.len() > 0 {
                fdots_dot(rest, k);
            }
        }
        word_id(fs[0]);
        li(fs[0], fdots(rest, k), tdots(rest, u));
        ls('.', fs[0] + fdots(rest, k), seq![Tok::Id(fs[0])] + tdots(rest, u));
        assert(fdots(fs, k) =~= seq!['.'] + (fs[0] + fdots(rest, k)));
        assert(tdots(fs, u) =~= seq![Tok::Sym('.')] + (seq![Tok::Id(fs[0])] + tdots(rest, u)));
    }
}

/// 閉じ部分 `..base` と ` }`（fields が空でないなら base の前に `, `）の字句。
pub proof fn frtail_lex(ne: bool, b: Option<Box<Sx>>, d: nat, td: nat, k: Seq<char>, u: Seq<Tok>)
    requires
        bopt(b, d, td),
        lex(k) == Some(u),
    ensures
        lex(frtail(ne, b, k)) == Some(rtail(ne, b, u)),
    decreases b, 0nat,
{
    ls('}', k, u);
    lw(' ', seq!['}'] + k, seq![Tok::Sym('}')] + u);
    assert(seq![' ', '}'] + k =~= seq![' '] + (seq!['}'] + k));
    match b {
        Some(x) => {
            fe_lex(*x, d, td, seq![' ', '}'] + k, seq![Tok::Sym('}')] + u);
            let kx = fe(*x, seq![' ', '}'] + k);
            let ux = te(*x, seq![Tok::Sym('}')] + u);
            ls('.', kx, ux);
            ls('.', seq!['.'] + kx, seq![Tok::Sym('.')] + ux);
            assert(seq!['.', '.'] + kx =~= seq!['.'] + (seq!['.'] + kx));
            assert(seq![Tok::Sym('.'), Tok::Sym('.')] + ux =~= seq![Tok::Sym('.')] + (seq![Tok::Sym('.')] + ux));
            assert(lex(frtail(ne, b, k)) == Some(rtail(ne, b, u))) by {
                assert(frtail(ne, b, k) =~= (if ne { seq![',', ' '] } else { seq![] }) + (seq!['.', '.'] + kx));
                assert(rtail(ne, b, u) =~= (if ne { seq![Tok::Sym(',')] } else { seq![] }) + (seq![Tok::Sym('.'), Tok::Sym('.')] + ux));
                if ne {
                    lcs(seq!['.', '.'] + kx, seq![Tok::Sym('.'), Tok::Sym('.')] + ux);
                }
            }
        },
        None => {
            assert(frtail(ne, b, k) =~= seq![' ', '}'] + k);
            assert(rtail(ne, b, u) =~= seq![Tok::Sym('}')] + u);
        },
    }
}

/// `ne` のとき閉じ部分は `, ` で始まり、字句として安全。
proof fn frtail_safe(ne: bool, b: Option<Box<Sx>>, k: Seq<char>)
    requires
        ne,
    ensures
        safe(frtail(ne, b, k)),
{
    match b {
        Some(x) => {},
        None => {},
    }
}

/// 整数で終わらない式（受けの条件）は、末尾が整数でない。
proof fn recv_not_int(a: Sx)
    requires
        recv_ok(a),
    ensures
        !ends_int(a),
{
}

/// レコード式の field の並び fs[i..] の字句。最後の field の後ろに tail が続く。
pub proof fn ffe_lex(fs: Seq<(Seq<char>, Sx)>, i: nat, d: nat, td: nat, tail: Seq<char>, u: Seq<Tok>)
    requires
        bfs(fs, i, d, td),
        lex(tail) == Some(u),
        i >= fs.len() || safe(tail),
    ensures
        lex(ffe(fs, i, tail)) == Some(tfe(fs, i, u)),
    decreases fs, fs.len() - i,
{
    if i < fs.len() {
        let x = fs[i as int].0;
        let v = fs[i as int].1;
        let last = i + 1 == fs.len();
        let kt = if last { tail } else { seq![',', ' '] + ffe(fs, i + 1, tail) };
        let ut = if last { u } else { seq![Tok::Sym(',')] + tfe(fs, i + 1, u) };
        assert(lex(kt) == Some(ut)) by {
            if !last {
                ffe_lex(fs, i + 1, d, td, tail, u);
                lcs(ffe(fs, i + 1, tail), tfe(fs, i + 1, u));
            }
        }
        assert(safe(kt)) by {
            if last {
            } else {
                assert(kt[0] == ',');
            }
        }
        fe_lex(v, d, td, kt, ut);
        let kv = fe(v, kt);
        let uv = te(v, ut);
        lw(' ', kv, uv);
        ls(':', seq![' '] + kv, uv);
        assert(seq![':', ' '] + kv =~= seq![':'] + (seq![' '] + kv));
        word_id(x);
        li(x, seq![':', ' '] + kv, seq![Tok::Sym(':')] + uv);
        assert(ffe(fs, i, tail) =~= x + (seq![':', ' '] + kv));
        assert(tfe(fs, i, u) =~= seq![word_tok(x), Tok::Sym(':')] + uv);
    }
}

/// 字句の補題：`e.f1.f2…`（受けは Let と整数でない式。後ろの字句は k）。
proof fn fe_lex_fld(e: Sx, d: nat, td: nat, k: Seq<char>, u: Seq<Tok>)
    requires
        e is Fld,
        bx(e, d, td),
        lex(k) == Some(u),
        fsafe(e, k),
    ensures
        lex(fe(e, k)) == Some(te(e, u)),
    decreases e, 0nat,
{
    match e {
        Sx::Fld(a, fs) => {
            recv_not_int(*a);
            assert(wsafe(k));
            fdots_lex(fs, k, u);
            fdots_dot(fs, k);
            fe_lex(*a, d, td, fdots(fs, k), tdots(fs, u));
        },
        _ => {},
    }
}

/// 字句の補題：`R { f: e, …, ..b }`（後ろの字句は k）。
proof fn fe_lex_rec(e: Sx, d: nat, td: nat, k: Seq<char>, u: Seq<Tok>)
    requires
        e is Rec,
        bx(e, d, td),
        lex(k) == Some(u),
        fsafe(e, k),
    ensures
        lex(fe(e, k)) == Some(te(e, u)),
    decreases e, 0nat,
{
    let d1 = (d - 1) as nat;
    match e {
        Sx::Rec(r, fs, b) => {
            word_id(r);
            if fs.len() == 0 && b is None {
                ls('}', k, u);
                ls('{', seq!['}'] + k, seq![Tok::Sym('}')] + u);
                lw(' ', seq!['{'] + (seq!['}'] + k), seq![Tok::Sym('{')] + (seq![Tok::Sym('}')] + u));
                li(r, seq![' '] + (seq!['{'] + (seq!['}'] + k)), seq![Tok::Sym('{')] + (seq![Tok::Sym('}')] + u));
                reveal_with_fuel(tfe, 1);
                reveal_with_fuel(rtail, 1);
                assert(fe(e, k) =~= r + (seq![' '] + (seq!['{'] + (seq!['}'] + k))));
                assert(tfe(fs, 0, rtail(fs.len() > 0, b, u)) =~= seq![Tok::Sym('}')] + u);
                assert(te(e, u) =~= seq![Tok::Id(r), Tok::Sym('{')] + (seq![Tok::Sym('}')] + u));
            } else {
                let ne = fs.len() > 0;
                let tc = frtail(ne, b, k);
                let tu = rtail(ne, b, u);
                frtail_lex(ne, b, d1, td, k, u);
                assert(fs.len() == 0 || safe(tc)) by {
                    if ne {
                        frtail_safe(ne, b, k);
                    }
                }
                ffe_lex(fs, 0, d1, td, tc, tu);
                lw(' ', ffe(fs, 0, tc), tfe(fs, 0, tu));
                ls('{', seq![' '] + ffe(fs, 0, tc), tfe(fs, 0, tu));
                lw(' ', seq!['{'] + (seq![' '] + ffe(fs, 0, tc)), seq![Tok::Sym('{')] + tfe(fs, 0, tu));
                li(r, seq![' '] + (seq!['{'] + (seq![' '] + ffe(fs, 0, tc))), seq![Tok::Sym('{')] + tfe(fs, 0, tu));
                assert(fe(e, k) =~= r + (seq![' '] + (seq!['{'] + (seq![' '] + ffe(fs, 0, tc)))));
                assert(te(e, u) =~= seq![Tok::Id(r), Tok::Sym('{')] + tfe(fs, 0, tu));
            }
        },
        _ => {},
    }
}

pub proof fn fargs_lex(es: Seq<Sx>, i: nat, d: nat, td: nat, k: Seq<char>, u: Seq<Tok>)
    requires
        bxs(es, i, d, td),
        lex(k) == Some(u),
    ensures
        lex(fargs(es, i, k)) == Some(targs(es, i, u)),
    decreases es, es.len() - i,
{
    if i >= es.len() {
        ls(')', k, u);
    } else if i + 1 == es.len() {
        ls(')', k, u);
        fe_lex(es[i as int], d, td, seq![')'] + k, seq![Tok::Sym(')')] + u);
    } else {
        fargs_lex(es, i + 1, d, td, k, u);
        lcs(fargs(es, i + 1, k), targs(es, i + 1, u));
        fe_lex(es[i as int], d, td, seq![',', ' '] + fargs(es, i + 1, k), seq![Tok::Sym(',')] + targs(es, i + 1, u));
    }
}

#[verifier::rlimit(60)]
pub proof fn fps_lex(ps: Seq<(Seq<char>, Ty)>, i: nat, td: nat, k: Seq<char>, u: Seq<Tok>)
    requires
        bps(ps, i, td),
        lex(k) == Some(u),
    ensures
        lex(fps(ps, i, k)) == Some(tps(ps, i, u)),
    decreases ps.len() - i,
{
    if i >= ps.len() {
        ls(')', k, u);
    } else {
        let (x, t) = ps[i as int];
        let (kt, ut) = if i + 1 == ps.len() {
            ls(')', k, u);
            (seq![')'] + k, seq![Tok::Sym(')')] + u)
        } else {
            fps_lex(ps, i + 1, td, k, u);
            lcs(fps(ps, i + 1, k), tps(ps, i + 1, u));
            (seq![',', ' '] + fps(ps, i + 1, k), seq![Tok::Sym(',')] + tps(ps, i + 1, u))
        };
        ft_lex(t, kt, ut);
        lw(' ', ft(t, kt), tt(t, ut));
        ls(':', seq![' '] + ft(t, kt), tt(t, ut));
        assert(seq![':', ' '] + ft(t, kt) =~= seq![':'] + (seq![' '] + ft(t, kt)));
        ln(x, seq![':', ' '] + ft(t, kt), seq![Tok::Sym(':')] + tt(t, ut));
        assert(seq![word_tok(x)] + (seq![Tok::Sym(':')] + tt(t, ut)) =~= tps(ps, i, u));
    }
}

/// レコード型の宣言の閉じ部分（末尾の `,` の有無に応じた ` }` と改行。続く字句は k）の字句。
proof fn dclose(tc: bool, k: Seq<char>, u: Seq<Tok>)
    requires
        lex(k) == Some(u),
    ensures
        lex((if tc { seq![',', ' ', '}'] } else { seq![' ', '}'] }) + seq!['\n'] + k) == Some(
            if tc { seq![Tok::Sym(',')] + (seq![Tok::Sym('}')] + u) } else { seq![Tok::Sym('}')] + u },
        ),
{
    lw('\n', k, u);
    ls('}', seq!['\n'] + k, u);
    lw(' ', seq!['}'] + (seq!['\n'] + k), seq![Tok::Sym('}')] + u);
    if tc {
        ls(',', seq![' '] + (seq!['}'] + (seq!['\n'] + k)), seq![Tok::Sym('}')] + u);
        assert(seq![',', ' ', '}'] + seq!['\n'] + k =~= seq![','] + (seq![' '] + (seq!['}'] + (seq!['\n'] + k))));
    } else {
        assert(seq![' ', '}'] + seq!['\n'] + k =~= seq![' '] + (seq!['}'] + (seq!['\n'] + k)));
    }
}

/// 閉じ部分の先頭は `,` か空白で、字句として安全。
proof fn dsafe(tc: bool, k: Seq<char>)
    ensures
        safe((if tc { seq![',', ' ', '}'] } else { seq![' ', '}'] }) + seq!['\n'] + k),
{
    if tc {
        assert((seq![',', ' ', '}'] + seq!['\n'] + k)[0] == ',');
    } else {
        assert((seq![' ', '}'] + seq!['\n'] + k)[0] == ' ');
    }
}

/// レコード型の field の並び fs[i..] の字句。最後の field の後ろは閉じ部分（dclose）。
pub proof fn ffd_lex(fs: Seq<(Seq<char>, Ty)>, i: nat, td: nat, tc: bool, k: Seq<char>, u: Seq<Tok>)
    requires
        bfds(fs, i, td),
        i < fs.len(),
        lex(k) == Some(u),
    ensures
        lex(ffd(fs, i, (if tc { seq![',', ' ', '}'] } else { seq![' ', '}'] }) + seq!['\n'] + k))
            == Some(tfd(fs, i, tc, seq![Tok::Sym('}')] + u)),
    decreases fs.len() - i,
{
    let tl = (if tc { seq![',', ' ', '}'] } else { seq![' ', '}'] }) + seq!['\n'];
    dclose(tc, k, u);
    dsafe(tc, k);
    let tu = if tc { seq![Tok::Sym(',')] + (seq![Tok::Sym('}')] + u) } else { seq![Tok::Sym('}')] + u };
    let x = fs[i as int].0;
    let t = fs[i as int].1;
    let last = i + 1 == fs.len();
    let kt = if last { tl + k } else { seq![',', ' '] + ffd(fs, i + 1, tl + k) };
    let ut = if last { tu } else { seq![Tok::Sym(',')] + tfd(fs, i + 1, tc, seq![Tok::Sym('}')] + u) };
    assert(lex(kt) == Some(ut)) by {
        if !last {
            ffd_lex(fs, i + 1, td, tc, k, u);
            lcs(ffd(fs, i + 1, tl + k), tfd(fs, i + 1, tc, seq![Tok::Sym('}')] + u));
        }
    }
    assert(safe(kt)) by {
        if !last {
            assert(kt[0] == ',');
        }
    }
    ft_lex(t, kt, ut);
    lw(' ', ft(t, kt), tt(t, ut));
    ls(':', seq![' '] + ft(t, kt), tt(t, ut));
    assert(seq![':', ' '] + ft(t, kt) =~= seq![':'] + (seq![' '] + ft(t, kt)));
    word_id(x);
    li(x, seq![':', ' '] + ft(t, kt), seq![Tok::Sym(':')] + tt(t, ut));
    assert(ffd(fs, i, tl + k) =~= x + (seq![':', ' '] + ft(t, kt)));
    assert(tfd(fs, i, tc, seq![Tok::Sym('}')] + u) =~= seq![Tok::Id(x), Tok::Sym(':')] + tt(t, ut));
}

/// 型の並びの先頭の型は深さ内（残りの並びも深さ内）。
pub proof fn bts_at(ps: Seq<Ty>, j: nat, td: nat)
    requires
        j < ps.len(),
        bts(ps, j, td),
    ensures
        bt(ps[j as int], td),
        bts(ps, j + 1, td),
{
}

/// 直和型の構築子の並びの先頭：名前は大文字で始まる IDENT、中身の型は深さ内。
pub proof fn bvars_at(vs: Seq<(Seq<char>, Seq<Ty>)>, j: nat, td: nat)
    requires
        j < vs.len(),
        bvars(vs, j, td),
    ensures
        cname_ok(vs[j as int].0),
        bts(vs[j as int].1, 0, td),
        bvars(vs, j + 1, td),
{
}

/// 型の並びの先頭の展開（token 側）。
pub proof fn tts_head(ps: Seq<Ty>, i: nat, k: Seq<Tok>)
    requires
        i < ps.len(),
    ensures
        tts(ps, i, k) == tt(ps[i as int], if i + 1 == ps.len() { k } else { seq![Tok::Sym(',')] + tts(ps, i + 1, k) }),
{
}

/// 直和型の構築子の並びの先頭の展開（token 側）。
pub proof fn tvars_head(vs: Seq<(Seq<char>, Seq<Ty>)>, i: nat, k: Seq<Tok>)
    requires
        i < vs.len(),
    ensures
        tvars(vs, i, k) == seq![word_tok(vs[i as int].0)] + tpay(
            vs[i as int].1,
            if i + 1 == vs.len() { k } else { seq![Tok::Sym('|')] + tvars(vs, i + 1, k) },
        ),
{
}

/// 型の並び `T, U, ...` の字句（後ろの続きは k。k は安全な字句で始まる）。
proof fn ftys_lex(ps: Seq<Ty>, i: nat, td: nat, k: Seq<char>, u: Seq<Tok>)
    requires
        i < ps.len(),
        bts(ps, i, td),
        lex(k) == Some(u),
        safe(k),
    ensures
        lex(ftys(ps, i, k)) == Some(tts(ps, i, u)),
    decreases ps.len() - i,
{
    bts_at(ps, i, td);
    if i + 1 == ps.len() {
        ft_lex(ps[i as int], k, u);
        assert(ftys(ps, i, k) == ft(ps[i as int], k));
        tts_head(ps, i, u);
    } else {
        ftys_lex(ps, i + 1, td, k, u);
        lcs(ftys(ps, i + 1, k), tts(ps, i + 1, u));
        ft_lex(ps[i as int], seq![',', ' '] + ftys(ps, i + 1, k), seq![Tok::Sym(',')] + tts(ps, i + 1, u));
        assert(ftys(ps, i, k) == ft(ps[i as int], seq![',', ' '] + ftys(ps, i + 1, k)));
        tts_head(ps, i, u);
    }
}

/// 構築子の中身の字句（空なら rest だけ、そうでなければ `(` 型の並び `)` と rest）。
proof fn fpay_lex(ps: Seq<Ty>, td: nat, k: Seq<char>, u: Seq<Tok>)
    requires
        bts(ps, 0, td),
        lex(k) == Some(u),
    ensures
        lex(fpay(ps, k)) == Some(tpay(ps, u)),
{
    if ps.len() > 0 {
        ls(')', k, u);
        ftys_lex(ps, 0, td, seq![')'] + k, seq![Tok::Sym(')')] + u);
        ls('(', ftys(ps, 0, seq![')'] + k), tts(ps, 0, seq![Tok::Sym(')')] + u));
        assert(fpay(ps, k) == seq!['('] + ftys(ps, 0, seq![')'] + k));
        assert(tpay(ps, u) == seq![Tok::Sym('(')] + tts(ps, 0, seq![Tok::Sym(')')] + u));
    }
}

/// 構築子の中身の字句は、字句の区切りとして安全（空白でも識別子文字でもない）。
proof fn fpay_wsafe(ps: Seq<Ty>, k: Seq<char>)
    requires
        wsafe(k),
    ensures
        wsafe(fpay(ps, k)),
{
    if ps.len() > 0 {
        assert(fpay(ps, k)[0] == '(');
    }
}

/// 直和型の構築子の並び vs[i..] の字句（最後の後ろは tail、字句は u）。
proof fn fvars_lex(vs: Seq<(Seq<char>, Seq<Ty>)>, i: nat, td: nat, tail: Seq<char>, u: Seq<Tok>)
    requires
        i < vs.len(),
        bvars(vs, i, td),
        lex(tail) == Some(u),
        wsafe(tail),
    ensures
        lex(fvars(vs, i, tail)) == Some(tvars(vs, i, u)),
    decreases vs.len() - i,
{
    bvars_at(vs, i, td);
    let x = vs[i as int];
    let last = i + 1 == vs.len();
    let kr = if last { tail } else { seq![' ', '|', ' '] + fvars(vs, i + 1, tail) };
    let ur = if last { u } else { seq![Tok::Sym('|')] + tvars(vs, i + 1, u) };
    assert(lex(kr) == Some(ur)) by {
        if !last {
            fvars_lex(vs, i + 1, td, tail, u);
            let kn = fvars(vs, i + 1, tail);
            let un = tvars(vs, i + 1, u);
            lw(' ', kn, un);
            ls('|', seq![' '] + kn, un);
            lw(' ', seq!['|'] + (seq![' '] + kn), seq![Tok::Sym('|')] + un);
            assert(seq![' ', '|', ' '] + kn =~= seq![' '] + (seq!['|'] + (seq![' '] + kn)));
        }
    }
    assert(wsafe(kr)) by {
        if !last {
            assert(kr[0] == ' ');
        }
    }
    fpay_lex(x.1, td, kr, ur);
    fpay_wsafe(x.1, kr);
    word_id(x.0);
    li(x.0, fpay(x.1, kr), tpay(x.1, ur));
    assert(fvars(vs, i, tail) == x.0 + fpay(x.1, kr));
    tvars_head(vs, i, u);
}

/// 文脈語 `type` は予約語でなく、字句として Id になる。
pub proof fn tyw_word()
    ensures
        is_word(tyw()),
        word_tok(tyw()) == Tok::Id(tyw()),
        ident_ok(tyw()),
{
    let w = tyw();
    assert(w.len() == 4 && w[0] == 't' && w[1] == 'y' && w[2] == 'p' && w[3] == 'e');
    assert forall|i: int| 0 < i < w.len() implies ident_char(#[trigger] w[i]) by {}
    assert(kw_of(w) is None);
}

/// レコード型の宣言一行 `type R = { f: T, …, }` の字句（後ろの字句は k）。
proof fn fd_lex_recty(r: Seq<char>, fs: Seq<(Seq<char>, Ty)>, td: nat, tc: bool, k: Seq<char>, u: Seq<Tok>)
    requires
        ident_ok(r),
        bfds(fs, 0, td),
        fs.len() > 0,
        lex(k) == Some(u),
    ensures
        lex(fd(Sd::RecTy(r, fs, tc), k)) == Some(tdecl(Sd::RecTy(r, fs, tc), u)),
{
    ffd_lex(fs, 0, td, tc, k, u);
    let kf = ffd(fs, 0, (if tc { seq![',', ' ', '}'] } else { seq![' ', '}'] }) + seq!['\n'] + k);
    let uf = tfd(fs, 0, tc, seq![Tok::Sym('}')] + u);
    word_id(r);
    tyw_word();
    lw(' ', kf, uf);
    ls('{', seq![' '] + kf, uf);
    lw(' ', seq!['{'] + (seq![' '] + kf), seq![Tok::Sym('{')] + uf);
    ls('=', seq![' '] + (seq!['{'] + (seq![' '] + kf)), seq![Tok::Sym('{')] + uf);
    let s3 = seq![' '] + (seq!['{'] + (seq![' '] + kf));
    let t4 = seq![Tok::Sym('=')] + (seq![Tok::Sym('{')] + uf);
    lw(' ', seq!['='] + s3, t4);
    let s5 = seq![' '] + (seq!['='] + s3);
    li(r, s5, t4);
    lw(' ', r + s5, seq![Tok::Id(r)] + t4);
    lword(tyw(), seq![' '] + (r + s5), seq![Tok::Id(r)] + t4);
    assert(fd(Sd::RecTy(r, fs, tc), k) =~= tyw() + (seq![' '] + (r + s5)));
    assert(tdecl(Sd::RecTy(r, fs, tc), u) =~= seq![Tok::Id(tyw())] + (seq![Tok::Id(r)] + t4));
}

/// 直和型の宣言一行 `type S = V1 | V2(T, U)` の字句（後ろの字句は k）。
proof fn fd_lex_sum(r: Seq<char>, vs: Seq<(Seq<char>, Seq<Ty>)>, td: nat, k: Seq<char>, u: Seq<Tok>)
    requires
        ident_ok(r),
        vs.len() > 0,
        bvars(vs, 0, td),
        lex(k) == Some(u),
    ensures
        lex(fd(Sd::Sum(r, vs), k)) == Some(tdecl(Sd::Sum(r, vs), u)),
{
    lw('\n', k, u);
    fvars_lex(vs, 0, td, seq!['\n'] + k, u);
    let kv = fvars(vs, 0, seq!['\n'] + k);
    let uv = tvars(vs, 0, u);
    lw(' ', kv, uv);
    ls('=', seq![' '] + kv, uv);
    lw(' ', seq!['='] + (seq![' '] + kv), seq![Tok::Sym('=')] + uv);
    let s = seq![' '] + (seq!['='] + (seq![' '] + kv));
    let t = seq![Tok::Sym('=')] + uv;
    word_id(r);
    li(r, s, t);
    lw(' ', r + s, seq![Tok::Id(r)] + t);
    tyw_word();
    lword(tyw(), seq![' '] + (r + s), seq![Tok::Id(r)] + t);
    assert(fd(Sd::Sum(r, vs), k) =~= tyw() + (seq![' '] + (r + s)));
    assert(tdecl(Sd::Sum(r, vs), u) =~= seq![Tok::Id(tyw())] + (seq![Tok::Id(r)] + t));
}

#[verifier::rlimit(60)]
pub proof fn fd_lex(x: Sd, d: nat, td: nat, k: Seq<char>, u: Seq<Tok>)
    requires
        bd(x, d, td),
        lex(k) == Some(u),
    ensures
        lex(fd(x, k)) == Some(tdecl(x, u)),
{
    match x {
        Sd::Fn(f, ps, r, b) => {
            lw('\n', k, u);
            fe_lex(b, d, td, seq!['\n'] + k, u);
            let kb = fe(b, seq!['\n'] + k);
            let ub = te(b, u);
            lw(' ', kb, ub);
            ls('=', seq![' '] + kb, ub);
            lw(' ', seq!['='] + (seq![' '] + kb), seq![Tok::Sym('=')] + ub);
            assert(seq![' ', '=', ' '] + kb =~= seq![' '] + (seq!['='] + (seq![' '] + kb)));
            ft_lex(r, seq![' ', '=', ' '] + kb, seq![Tok::Sym('=')] + ub);
            let kr = ft(r, seq![' ', '=', ' '] + kb);
            let ur = tt(r, seq![Tok::Sym('=')] + ub);
            lw(' ', kr, ur);
            larrow(seq![' '] + kr, ur);
            lw(' ', seq!['-', '>'] + (seq![' '] + kr), seq![Tok::Arrow] + ur);
            assert(seq![' ', '-', '>', ' '] + kr =~= seq![' '] + (seq!['-', '>'] + (seq![' '] + kr)));
            fps_lex(ps, 0, td, seq![' ', '-', '>', ' '] + kr, seq![Tok::Arrow] + ur);
            let kp = fps(ps, 0, seq![' ', '-', '>', ' '] + kr);
            let up = tps(ps, 0, seq![Tok::Arrow] + ur);
            ls('(', kp, up);
            li(f, seq!['('] + kp, seq![Tok::Sym('(')] + up);
            lw(' ', f + (seq!['('] + kp), seq![Tok::Id(f)] + (seq![Tok::Sym('(')] + up));
            lk(Kw::Fn, seq![' '] + (f + (seq!['('] + kp)), seq![Tok::Id(f)] + (seq![Tok::Sym('(')] + up));
            assert(seq![Tok::Kw(Kw::Fn)] + (seq![Tok::Id(f)] + (seq![Tok::Sym('(')] + up)) =~= tdecl(x, u));
        },
        Sd::Entry(n) => {
            lw('\n', k, u);
            li(n, seq!['\n'] + k, u);
            lw(' ', n + (seq!['\n'] + k), seq![Tok::Id(n)] + u);
            lk(Kw::Entry, seq![' '] + (n + (seq!['\n'] + k)), seq![Tok::Id(n)] + u);
            assert(seq![Tok::Kw(Kw::Entry)] + (seq![Tok::Id(n)] + u) =~= tdecl(x, u));
        },
        Sd::RecTy(r, fs, tc) => fd_lex_recty(r, fs, td, tc, k, u),
        Sd::Sum(r, vs) => fd_lex_sum(r, vs, td, k, u),
    }
}

/// 正準ソースの字句解析結果は AST の token 列。
pub proof fn fds_lex(p: Seq<Sd>, i: nat, d: nat, td: nat)
    requires
        bds(p, i, d, td),
    ensures
        lex(fds(p, i)) == Some(tds(p, i)),
    decreases p.len() - i,
{
    if i < p.len() {
        fds_lex(p, i + 1, d, td);
        fd_lex(p[i as int], d, td, fds(p, i + 1), tds(p, i + 1));
    }
}

// ------------------------------------------------------------------ 正準ソースの継続の分離

#[verifier::rlimit(50)]
pub proof fn ft_app(t: Ty, k: Seq<char>)
    ensures
        ft(t, k) == ft(t, Seq::empty()) + k,
    decreases t,
{
    let z = Seq::<char>::empty();
    match t {
        Ty::List(a) => {
            ft_app(*a, seq!['>'] + k);
            ft_app(*a, seq!['>'] + z);
        },
        Ty::Option(a) => {
            ft_app(*a, seq!['>'] + k);
            ft_app(*a, seq!['>'] + z);
        },
        Ty::Pair(a, b) | Ty::Result(a, b) => {
            ft_app(*b, seq!['>'] + k);
            ft_app(*b, seq!['>'] + z);
            ft_app(*a, seq![',', ' '] + ft(*b, seq!['>'] + k));
            ft_app(*a, seq![',', ' '] + ft(*b, seq!['>'] + z));
        },
        _ => {},
    }
    assert(ft(t, k) =~= ft(t, z) + k);
}

/// `.f` の並びは後ろの続きに対して結合する。
pub proof fn fdots_app(fs: Seq<Seq<char>>, k: Seq<char>)
    ensures
        fdots(fs, k) == fdots(fs, Seq::empty()) + k,
    decreases fs.len(),
{
    if fs.len() > 0 {
        fdots_app(fs.subrange(1, fs.len() as int), k);
    }
    assert(fdots(fs, k) =~= fdots(fs, Seq::empty()) + k);
}

/// 閉じ部分は後ろの続きに対して結合する。
pub proof fn frtail_app(ne: bool, b: Option<Box<Sx>>, k: Seq<char>)
    ensures
        frtail(ne, b, k) == frtail(ne, b, Seq::empty()) + k,
    decreases b, 0nat,
{
    match b {
        Some(x) => {
            fe_app(*x, seq![' ', '}'] + k);
            fe_app(*x, seq![' ', '}']);
            assert(frtail(ne, b, k) =~= frtail(ne, b, Seq::empty()) + k);
        },
        None => {
            assert(frtail(ne, b, k) =~= frtail(ne, b, Seq::empty()) + k);
        },
    }
}

/// レコード式の field の並びは後ろの続きに対して結合する。
pub proof fn ffe_app(fs: Seq<(Seq<char>, Sx)>, i: nat, k: Seq<char>)
    ensures
        ffe(fs, i, k) == ffe(fs, i, Seq::empty()) + k,
    decreases fs, fs.len() - i,
{
    if i < fs.len() {
        if i + 1 == fs.len() {
            fe_app(fs[i as int].1, k);
        } else {
            ffe_app(fs, i + 1, k);
            fe_app(fs[i as int].1, seq![',', ' '] + ffe(fs, i + 1, k));
            fe_app(fs[i as int].1, seq![',', ' '] + ffe(fs, i + 1, Seq::empty()));
        }
    }
    assert(ffe(fs, i, k) =~= ffe(fs, i, Seq::empty()) + k);
}

proof fn fe_app_rec(e: Sx, k: Seq<char>)
    requires
        e is Rec,
    ensures
        fe(e, k) == fe(e, Seq::empty()) + k,
    decreases e, 0nat,
{
    let z = Seq::<char>::empty();
    if let Sx::Rec(r, fs, b) = e {
        if fs.len() == 0 && b is None {
        } else {
            ffe_app(fs, 0, frtail(fs.len() > 0, b, k));
            ffe_app(fs, 0, frtail(fs.len() > 0, b, z));
            frtail_app(fs.len() > 0, b, k);
        }
    }
    assert(fe(e, k) =~= fe(e, z) + k);
}

/// レコード型の field の並びは後ろの続きに対して結合する。
pub proof fn ffd_app(fs: Seq<(Seq<char>, Ty)>, i: nat, k: Seq<char>)
    ensures
        ffd(fs, i, k) == ffd(fs, i, Seq::empty()) + k,
    decreases fs.len() - i,
{
    if i < fs.len() {
        if i + 1 == fs.len() {
            ft_app(fs[i as int].1, k);
        } else {
            ffd_app(fs, i + 1, k);
            ft_app(fs[i as int].1, seq![',', ' '] + ffd(fs, i + 1, k));
            ft_app(fs[i as int].1, seq![',', ' '] + ffd(fs, i + 1, Seq::empty()));
        }
    }
    assert(ffd(fs, i, k) =~= ffd(fs, i, Seq::empty()) + k);
}

/// 型の並びは後ろの続きに対して結合する。
pub proof fn ftys_app(ps: Seq<Ty>, i: nat, k: Seq<char>)
    ensures
        ftys(ps, i, k) == ftys(ps, i, Seq::empty()) + k,
    decreases ps.len() - i,
{
    let z = Seq::<char>::empty();
    if i < ps.len() {
        if i + 1 == ps.len() {
            ft_app(ps[i as int], k);
            ft_app(ps[i as int], z);
        } else {
            ftys_app(ps, i + 1, k);
            ft_app(ps[i as int], seq![',', ' '] + ftys(ps, i + 1, k));
            ft_app(ps[i as int], seq![',', ' '] + ftys(ps, i + 1, z));
        }
    }
    assert(ftys(ps, i, k) =~= ftys(ps, i, z) + k);
}

/// 構築子の中身は後ろの続きに対して結合する。
pub proof fn fpay_app(ps: Seq<Ty>, k: Seq<char>)
    ensures
        fpay(ps, k) == fpay(ps, Seq::empty()) + k,
{
    let z = Seq::<char>::empty();
    if ps.len() > 0 {
        ftys_app(ps, 0, seq![')'] + k);
        ftys_app(ps, 0, seq![')'] + z);
    }
    assert(fpay(ps, k) =~= fpay(ps, z) + k);
}

/// 直和型の構築子の並びは後ろの続きに対して結合する。
pub proof fn fvars_app(vs: Seq<(Seq<char>, Seq<Ty>)>, i: nat, k: Seq<char>)
    ensures
        fvars(vs, i, k) == fvars(vs, i, Seq::empty()) + k,
    decreases vs.len() - i,
{
    let z = Seq::<char>::empty();
    if i < vs.len() {
        if i + 1 == vs.len() {
            fpay_app(vs[i as int].1, k);
            fpay_app(vs[i as int].1, z);
        } else {
            fvars_app(vs, i + 1, k);
            fpay_app(vs[i as int].1, seq![' ', '|', ' '] + fvars(vs, i + 1, k));
            fpay_app(vs[i as int].1, seq![' ', '|', ' '] + fvars(vs, i + 1, z));
        }
    }
    assert(fvars(vs, i, k) =~= fvars(vs, i, z) + k);
}

#[verifier::rlimit(60)]
pub proof fn fe_app(e: Sx, k: Seq<char>)
    ensures
        fe(e, k) == fe(e, Seq::empty()) + k,
    decreases e, 1nat,
{
    let z = Seq::<char>::empty();
    match e {
        Sx::List(t, es) => {
            fargs_app(es, 0, k);
            fargs_app(es, 0, z);
            ft_app(t, seq!['>', '('] + fargs(es, 0, k));
            ft_app(t, seq!['>', '('] + fargs(es, 0, z));
        },
        Sx::Some(a) => {
            fe_app(*a, seq![')'] + k);
            fe_app(*a, seq![')'] + z);
        },
        Sx::None(t) => {
            ft_app(t, seq!['>', '(', ')'] + k);
            ft_app(t, seq!['>', '(', ')'] + z);
        },
        Sx::Pair(a, b) => {
            fe_app(*b, seq![')'] + k);
            fe_app(*b, seq![')'] + z);
            fe_app(*a, seq![',', ' '] + fe(*b, seq![')'] + k));
            fe_app(*a, seq![',', ' '] + fe(*b, seq![')'] + z));
        },
        Sx::Builtin(_, es) => {
            fargs_app(es, 0, k);
            fargs_app(es, 0, z);
        },
        Sx::Call(_, es) => {
            fargs_app(es, 0, k);
            fargs_app(es, 0, z);
        },
        Sx::Let(..) => fe_app_let(e, k),
        Sx::If(..) => fe_app_if(e, k),
        Sx::Fold(..) => fe_app_fold(e, k),
        Sx::Match(..) => fe_app_match(e, k),
        Sx::Inj(_, t, u, a) => {
            fe_app(*a, seq![')'] + k);
            fe_app(*a, seq![')'] + z);
            let ku = seq!['>', '('] + fe(*a, seq![')'] + k);
            let zu = seq!['>', '('] + fe(*a, seq![')'] + z);
            assert(ku =~= zu + k);
            ft_app(u, ku);
            ft_app(u, zu);
            let kt = seq![',', ' '] + ft(u, ku);
            let zt = seq![',', ' '] + ft(u, zu);
            assert(kt =~= zt + k);
            ft_app(t, kt);
            ft_app(t, zt);
        },
        Sx::MatchR(..) => fe_app_matchr(e, k),
        Sx::Fld(a, fs) => {
            fdots_app(fs, k);
            fe_app(*a, fdots(fs, k));
            fe_app(*a, fdots(fs, z));
        },
        Sx::Rec(..) => fe_app_rec(e, k),
        Sx::SumMatch(..) => fe_app_sumatch(e, k),
        Sx::Hof(..) => fe_app_hof(e, k),
        _ => {},
    }
    assert(fe(e, k) =~= fe(e, z) + k);
}

proof fn fe_app_matchr(e: Sx, k: Seq<char>)
    requires
        e is MatchR,
    ensures
        fe(e, k) == fe(e, Seq::empty()) + k,
    decreases e, 0nat,
{
    let z = Seq::<char>::empty();
    if let Sx::MatchR(m, x, a, y, b) = e {
        fe_app(*b, seq![')'] + k);
        fe_app(*b, seq![')'] + z);
        let ka = seq![',', ' ', '|'] + (y + (seq!['|', ' '] + fe(*b, seq![')'] + k)));
        let za = seq![',', ' ', '|'] + (y + (seq!['|', ' '] + fe(*b, seq![')'] + z)));
        assert(ka =~= za + k);
        fe_app(*a, ka);
        fe_app(*a, za);
        let km = seq![',', ' ', '|'] + (x + (seq!['|', ' '] + fe(*a, ka)));
        let zm = seq![',', ' ', '|'] + (x + (seq!['|', ' '] + fe(*a, za)));
        assert(km =~= zm + k);
        fe_app(*m, km);
        fe_app(*m, zm);
    }
    assert(fe(e, k) =~= fe(e, z) + k);
}

proof fn fe_app_let(e: Sx, k: Seq<char>)
    requires
        e is Let,
    ensures
        fe(e, k) == fe(e, Seq::empty()) + k,
    decreases e, 0nat,
{
    let z = Seq::<char>::empty();
    if let Sx::Let(x, a, b) = e {
        fe_app(*b, k);
        let ka = seq![' '] + (kwt(Kw::In) + (seq![' '] + fe(*b, k)));
        let za = seq![' '] + (kwt(Kw::In) + (seq![' '] + fe(*b, z)));
        fe_app(*a, ka);
        fe_app(*a, za);
        assert(ka =~= za + k);
    }
    assert(fe(e, k) =~= fe(e, z) + k);
}

proof fn fe_app_if(e: Sx, k: Seq<char>)
    requires
        e is If,
    ensures
        fe(e, k) == fe(e, Seq::empty()) + k,
    decreases e, 0nat,
{
    let z = Seq::<char>::empty();
    if let Sx::If(c, a, b) = e {
        fe_app(*b, seq![')'] + k);
        fe_app(*b, seq![')'] + z);
        let ka = seq![',', ' '] + fe(*b, seq![')'] + k);
        let za = seq![',', ' '] + fe(*b, seq![')'] + z);
        fe_app(*a, ka);
        fe_app(*a, za);
        assert(ka =~= za + k);
        let kc = seq![',', ' '] + fe(*a, ka);
        let zc = seq![',', ' '] + fe(*a, za);
        fe_app(*c, kc);
        fe_app(*c, zc);
        assert(kc =~= zc + k);
    }
    assert(fe(e, k) =~= fe(e, z) + k);
}

proof fn fe_app_fold(e: Sx, k: Seq<char>)
    requires
        e is Fold,
    ensures
        fe(e, k) == fe(e, Seq::empty()) + k,
    decreases e, 0nat,
{
    let z = Seq::<char>::empty();
    if let Sx::Fold(l, i, a, x, b) = e {
        fe_app(*b, seq![')'] + k);
        fe_app(*b, seq![')'] + z);
        let ki = seq![',', ' ', '|'] + (a + (seq![',', ' '] + (x + (seq!['|', ' '] + fe(*b, seq![')'] + k)))));
        let zi = seq![',', ' ', '|'] + (a + (seq![',', ' '] + (x + (seq!['|', ' '] + fe(*b, seq![')'] + z)))));
        assert(ki =~= zi + k);
        fe_app(*i, ki);
        fe_app(*i, zi);
        let kl = seq![',', ' '] + fe(*i, ki);
        let zl = seq![',', ' '] + fe(*i, zi);
        assert(kl =~= zl + k);
        fe_app(*l, kl);
        fe_app(*l, zl);
    }
    assert(fe(e, k) =~= fe(e, z) + k);
}

proof fn fe_app_match(e: Sx, k: Seq<char>)
    requires
        e is Match,
    ensures
        fe(e, k) == fe(e, Seq::empty()) + k,
    decreases e, 0nat,
{
    let z = Seq::<char>::empty();
    if let Sx::Match(m, n, x, b) = e {
        fe_app(*b, seq![')'] + k);
        fe_app(*b, seq![')'] + z);
        let kn = seq![',', ' ', '|'] + (x + (seq!['|', ' '] + fe(*b, seq![')'] + k)));
        let zn = seq![',', ' ', '|'] + (x + (seq!['|', ' '] + fe(*b, seq![')'] + z)));
        assert(kn =~= zn + k);
        fe_app(*n, kn);
        fe_app(*n, zn);
        let km = seq![',', ' '] + fe(*n, kn);
        let zm = seq![',', ' '] + fe(*n, zn);
        assert(km =~= zm + k);
        fe_app(*m, km);
        fe_app(*m, zm);
    }
    assert(fe(e, k) =~= fe(e, z) + k);
}

/// hof の印字は後ろの続き k に対して結合する。
proof fn fe_app_hof(e: Sx, k: Seq<char>)
    requires
        e is Hof,
    ensures
        fe(e, k) == fe(e, Seq::empty()) + k,
    decreases e, 0nat,
{
    let z = Seq::<char>::empty();
    if let Sx::Hof(h, l, x, b) = e {
        fe_app(*b, seq![')'] + k);
        fe_app(*b, seq![')'] + z);
        let kl = seq![',', ' ', '|'] + (x + (seq!['|', ' '] + fe(*b, seq![')'] + k)));
        let zl = seq![',', ' ', '|'] + (x + (seq!['|', ' '] + fe(*b, seq![')'] + z)));
        assert(kl =~= zl + k);
        fe_app(*l, kl);
        fe_app(*l, zl);
        assert(fe(*l, kl) =~= fe(*l, zl) + k);
        assert(fe(e, k) =~= fe(e, z) + k);
    }
    assert(fe(e, k) =~= fe(e, z) + k);
}

/// 束縛の並びは後ろの続き q に k を続けても、k は最後に付く。
pub proof fn fbinds_app(bs: Seq<Seq<char>>, i: nat, q: Seq<char>, k: Seq<char>)
    ensures
        fbinds(bs, i, q + k) == fbinds(bs, i, q) + k,
    decreases bs.len() - i,
{
    if i >= bs.len() {
    } else if i + 1 == bs.len() {
        assert(bs[i as int] + (q + k) =~= (bs[i as int] + q) + k);
    } else {
        fbinds_app(bs, i + 1, q, k);
        assert(bs[i as int] + (seq![',', ' '] + fbinds(bs, i + 1, q + k))
            =~= (bs[i as int] + (seq![',', ' '] + fbinds(bs, i + 1, q))) + k);
    }
    assert(fbinds(bs, i, q + k) =~= fbinds(bs, i, q) + k);
}

/// 枝の左辺の印字は後ろの続き q に k を続けても、k は最後に付く。
pub proof fn fpat_app(p: Spat, q: Seq<char>, k: Seq<char>)
    ensures
        fpat(p, q + k) == fpat(p, q) + k,
{
    match p {
        Spat::Ctor(c, bs) => {
            if bs.len() > 0 {
                fbinds_app(bs, 0, seq![')'] + q, k);
                assert(seq![')'] + (q + k) =~= (seq![')'] + q) + k);
            }
        },
        _ => {},
    }
    assert(fpat(p, q + k) =~= fpat(p, q) + k);
}

/// 枝の並びは後ろの続き k に対して結合する。
pub proof fn farms_app(arms: Seq<(Spat, Sx)>, i: nat, k: Seq<char>)
    ensures
        farms(arms, i, k) == farms(arms, i, Seq::empty()) + k,
    decreases arms, arms.len() - i,
{
    let z = Seq::<char>::empty();
    if i < arms.len() {
        let p = arms[i as int].0;
        let body = arms[i as int].1;
        if i + 1 == arms.len() {
            fe_app(body, k);
            let q = seq![' ', '=', '>', ' '] + fe(body, z);
            assert(seq![' ', '=', '>', ' '] + fe(body, k) =~= q + k);
            fpat_app(p, q, k);
        } else {
            farms_app(arms, i + 1, k);
            let q = seq![',', ' '] + farms(arms, i + 1, z);
            assert(seq![',', ' '] + farms(arms, i + 1, k) =~= q + k);
            fe_app(body, q + k);
            fe_app(body, q);
            assert(fe(body, q + k) =~= fe(body, q) + k);
            let r = seq![' ', '=', '>', ' '] + fe(body, q);
            assert(seq![' ', '=', '>', ' '] + fe(body, q + k) =~= r + k);
            fpat_app(p, r, k);
        }
    }
    assert(farms(arms, i, k) =~= farms(arms, i, z) + k);
}

/// `match e { 枝 }` の印字は後ろの続き k に対して結合する。
proof fn fe_app_sumatch(e: Sx, k: Seq<char>)
    requires
        e is SumMatch,
    ensures
        fe(e, k) == fe(e, Seq::empty()) + k,
    decreases e, 0nat,
{
    let z = Seq::<char>::empty();
    if let Sx::SumMatch(m, arms) = e {
        farms_app(arms, 0, seq![' ', '}']);
        farms_app(arms, 0, seq![' ', '}'] + k);
        assert(farms(arms, 0, seq![' ', '}'] + k) =~= farms(arms, 0, seq![' ', '}']) + k);
        let y = seq![' ', '{', ' '] + farms(arms, 0, seq![' ', '}']);
        assert(seq![' ', '{', ' '] + farms(arms, 0, seq![' ', '}'] + k) =~= y + k);
        fe_app(*m, y);
        fe_app(*m, y + k);
        assert(fe(*m, y + k) =~= fe(*m, y) + k);
        assert(seq![' ', '}'] + z =~= seq![' ', '}']);
    }
    assert(fe(e, k) =~= fe(e, z) + k);
}

pub proof fn fargs_app(es: Seq<Sx>, i: nat, k: Seq<char>)
    ensures
        fargs(es, i, k) == fargs(es, i, Seq::empty()) + k,
    decreases es, es.len() - i,
{
    let z = Seq::<char>::empty();
    if i >= es.len() {
    } else if i + 1 == es.len() {
        fe_app(es[i as int], seq![')'] + k);
        fe_app(es[i as int], seq![')'] + z);
    } else {
        fargs_app(es, i + 1, k);
        fe_app(es[i as int], seq![',', ' '] + fargs(es, i + 1, k));
        fe_app(es[i as int], seq![',', ' '] + fargs(es, i + 1, z));
    }
    assert(fargs(es, i, k) =~= fargs(es, i, z) + k);
}

pub proof fn fps_app(ps: Seq<(Seq<char>, Ty)>, i: nat, k: Seq<char>)
    ensures
        fps(ps, i, k) == fps(ps, i, Seq::empty()) + k,
    decreases ps.len() - i,
{
    let z = Seq::<char>::empty();
    if i < ps.len() {
        if i + 1 == ps.len() {
            ft_app(ps[i as int].1, seq![')'] + k);
            ft_app(ps[i as int].1, seq![')'] + z);
        } else {
            fps_app(ps, i + 1, k);
            ft_app(ps[i as int].1, seq![',', ' '] + fps(ps, i + 1, k));
            ft_app(ps[i as int].1, seq![',', ' '] + fps(ps, i + 1, z));
        }
    }
    assert(fps(ps, i, k) =~= fps(ps, i, z) + k);
}

/// レコード型の宣言一行は後ろの続きに対して結合する。
proof fn fd_app_recty(r: Seq<char>, fs: Seq<(Seq<char>, Ty)>, tc: bool, k: Seq<char>)
    ensures
        fd(Sd::RecTy(r, fs, tc), k) == fd(Sd::RecTy(r, fs, tc), Seq::empty()) + k,
{
    let z = Seq::<char>::empty();
    let tl = (if tc { seq![',', ' ', '}'] } else { seq![' ', '}'] }) + seq!['\n'];
    ffd_app(fs, 0, tl + k);
    ffd_app(fs, 0, tl + z);
    assert(fd(Sd::RecTy(r, fs, tc), k) =~= fd(Sd::RecTy(r, fs, tc), z) + k);
}

/// 直和型の宣言一行は後ろの続きに対して結合する。
proof fn fd_app_sum(r: Seq<char>, vs: Seq<(Seq<char>, Seq<Ty>)>, k: Seq<char>)
    ensures
        fd(Sd::Sum(r, vs), k) == fd(Sd::Sum(r, vs), Seq::empty()) + k,
{
    let z = Seq::<char>::empty();
    fvars_app(vs, 0, seq!['\n'] + k);
    fvars_app(vs, 0, seq!['\n'] + z);
    assert(fd(Sd::Sum(r, vs), k) =~= fd(Sd::Sum(r, vs), z) + k);
}

pub proof fn fd_app(x: Sd, k: Seq<char>)
    ensures
        fd(x, k) == fd(x, Seq::empty()) + k,
{
    let z = Seq::<char>::empty();
    if let Sd::Fn(f, ps, r, b) = x {
        fe_app(b, seq!['\n'] + k);
        fe_app(b, seq!['\n'] + z);
        let kr = seq![' ', '=', ' '] + fe(b, seq!['\n'] + k);
        let zr = seq![' ', '=', ' '] + fe(b, seq!['\n'] + z);
        assert(kr =~= zr + k);
        ft_app(r, kr);
        ft_app(r, zr);
        let kp = seq![' ', '-', '>', ' '] + ft(r, kr);
        let zp = seq![' ', '-', '>', ' '] + ft(r, zr);
        assert(kp =~= zp + k);
        fps_app(ps, 0, kp);
        fps_app(ps, 0, zp);
    }
    if let Sd::RecTy(r, fs, tc) = x {
        fd_app_recty(r, fs, tc, k);
    }
    if let Sd::Sum(r, vs) = x {
        fd_app_sum(r, vs, k);
    }
    assert(fd(x, k) =~= fd(x, z) + k);
}

} // verus!
