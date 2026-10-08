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

#[verifier::rlimit(40)]
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
        Ty::List(a) => {
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
    }
}

/// 式の深さ上限は字句には関係しないが、名前の妥当性を bx から取り出すために使う。
pub proof fn fe_lex(e: Sx, d: nat, td: nat, k: Seq<char>, u: Seq<Tok>)
    requires
        bx(e, d, td),
        lex(k) == Some(u),
        safe(k),
    ensures
        lex(fe(e, k)) == Some(te(e, u)),
    decreases e, 1nat,
{
    match e {
        Sx::Int(n) => lint(n, k, u),
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
    }
}

proof fn fe_lex_list(e: Sx, d: nat, td: nat, k: Seq<char>, u: Seq<Tok>)
    requires
        e is List,
        bx(e, d, td),
        lex(k) == Some(u),
        safe(k),
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
        safe(k),
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
        safe(k),
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
        safe(k),
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
        safe(k),
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
        safe(k),
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
        safe(k),
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
        safe(k),
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
        safe(k),
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

proof fn fe_lex_match(e: Sx, d: nat, td: nat, k: Seq<char>, u: Seq<Tok>)
    requires
        e is Match,
        bx(e, d, td),
        lex(k) == Some(u),
        safe(k),
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

pub proof fn fargs_lex(es: Seq<Sx>, i: nat, d: nat, td: nat, k: Seq<char>, u: Seq<Tok>)
    requires
        bxs(es, i, d, td),
        lex(k) == Some(u),
        safe(k),
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

pub proof fn fps_lex(ps: Seq<(Seq<char>, Ty)>, i: nat, td: nat, k: Seq<char>, u: Seq<Tok>)
    requires
        bps(ps, i, td),
        lex(k) == Some(u),
        safe(k),
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
        Ty::Pair(a, b) => {
            ft_app(*b, seq!['>'] + k);
            ft_app(*b, seq!['>'] + z);
            ft_app(*a, seq![',', ' '] + ft(*b, seq!['>'] + k));
            ft_app(*a, seq![',', ' '] + ft(*b, seq!['>'] + z));
        },
        _ => {},
    }
    assert(ft(t, k) =~= ft(t, z) + k);
}

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
        _ => {},
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
    assert(fd(x, k) =~= fd(x, z) + k);
}

} // verus!
