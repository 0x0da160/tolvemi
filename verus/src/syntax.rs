//! 表面構文の spec（設計書 §4）：予約語、字句、表面 AST、token 列への写像、正準ソース、
//! 字句解析器と構文解析器。
//!
//! - `te` などの token 写像は EBNF（§4.1）を「AST から token 列を作る関数」として書いたもの。
//!   AST P が source に対応するとは、`lex(source) == Some(tds(P, 0))` のことである。
//! - `fe` などは §4.3 の正準フォーマッタ。
//! - `lex` は §4.2 の字句規則、`pds` は再帰下降の構文解析器。
//! いずれも継続（後続の列 k）を引数に取る形で書き、連結の付け替えを証明で扱いやすくしている。
//! 証明は syntax_proof.rs、exec 実装は surface.rs。

use crate::bigint::*;
use crate::json::*;
use crate::spec::*;
use vstd::prelude::*;

verus! {

// ------------------------------------------------------------------ 予約語

#[derive(Clone, Copy, PartialEq, Eq)]
pub enum Kw {
    Fn,
    Entry,
    TInt,
    TBool,
    TUnit,
    TList,
    TOption,
    TPair,
    True,
    False,
    Unit,
    List,
    Some,
    None,
    Pair,
    Let,
    In,
    If,
    Fold,
    Add,
    Sub,
    Mul,
    Neg,
    Lt,
    Le,
    Eq,
    Mod,
    Fst,
    Snd,
    Cons,
    Concat,
    Reverse,
    Length,
    Uncons,
    MatchOption,
    Min,
    Max,
    Range,
    Contains,
    Sort,
}

pub open spec fn kwt(k: Kw) -> Seq<char> {
    match k {
        Kw::Fn => seq!['f', 'n'],
        Kw::Entry => seq!['e', 'n', 't', 'r', 'y'],
        Kw::TInt => seq!['I', 'n', 't'],
        Kw::TBool => seq!['B', 'o', 'o', 'l'],
        Kw::TUnit => seq!['U', 'n', 'i', 't'],
        Kw::TList => seq!['L', 'i', 's', 't'],
        Kw::TOption => seq!['O', 'p', 't', 'i', 'o', 'n'],
        Kw::TPair => seq!['P', 'a', 'i', 'r'],
        Kw::True => seq!['t', 'r', 'u', 'e'],
        Kw::False => seq!['f', 'a', 'l', 's', 'e'],
        Kw::Unit => seq!['u', 'n', 'i', 't'],
        Kw::List => seq!['l', 'i', 's', 't'],
        Kw::Some => seq!['s', 'o', 'm', 'e'],
        Kw::None => seq!['n', 'o', 'n', 'e'],
        Kw::Pair => seq!['p', 'a', 'i', 'r'],
        Kw::Let => seq!['l', 'e', 't'],
        Kw::In => seq!['i', 'n'],
        Kw::If => seq!['i', 'f'],
        Kw::Fold => seq!['f', 'o', 'l', 'd'],
        Kw::Add => seq!['a', 'd', 'd'],
        Kw::Sub => seq!['s', 'u', 'b'],
        Kw::Mul => seq!['m', 'u', 'l'],
        Kw::Neg => seq!['n', 'e', 'g'],
        Kw::Lt => seq!['l', 't'],
        Kw::Le => seq!['l', 'e'],
        Kw::Eq => seq!['e', 'q'],
        Kw::Mod => seq!['m', 'o', 'd'],
        Kw::Fst => seq!['f', 's', 't'],
        Kw::Snd => seq!['s', 'n', 'd'],
        Kw::Cons => seq!['c', 'o', 'n', 's'],
        Kw::Concat => seq!['c', 'o', 'n', 'c', 'a', 't'],
        Kw::Reverse => seq!['r', 'e', 'v', 'e', 'r', 's', 'e'],
        Kw::Length => seq!['l', 'e', 'n', 'g', 't', 'h'],
        Kw::Uncons => seq!['u', 'n', 'c', 'o', 'n', 's'],
        Kw::MatchOption => seq!['m', 'a', 't', 'c', 'h', '_', 'o', 'p', 't', 'i', 'o', 'n'],
        Kw::Min => seq!['m', 'i', 'n'],
        Kw::Max => seq!['m', 'a', 'x'],
        Kw::Range => seq!['r', 'a', 'n', 'g', 'e'],
        Kw::Contains => seq!['c', 'o', 'n', 't', 'a', 'i', 'n', 's'],
        Kw::Sort => seq!['s', 'o', 'r', 't'],
    }
}

pub open spec fn c2(s: Seq<char>, a: char, b: char) -> bool {
    s[0] == a && s[1] == b
}

pub open spec fn c3(s: Seq<char>, a: char, b: char, c: char) -> bool {
    s[0] == a && s[1] == b && s[2] == c
}

pub open spec fn c4(s: Seq<char>, a: char, b: char, c: char, d: char) -> bool {
    s[0] == a && s[1] == b && s[2] == c && s[3] == d
}

pub open spec fn c5(s: Seq<char>, a: char, b: char, c: char, d: char, e: char) -> bool {
    s[0] == a && s[1] == b && s[2] == c && s[3] == d && s[4] == e
}

pub open spec fn c6(s: Seq<char>, a: char, b: char, c: char, d: char, e: char, f: char) -> bool {
    s[0] == a && s[1] == b && s[2] == c && s[3] == d && s[4] == e && s[5] == f
}

/// 語が予約語ならその予約語。
pub open spec fn kw_of(s: Seq<char>) -> Option<Kw> {
    if s.len() == 2 {
        if c2(s, 'f', 'n') {
            Some(Kw::Fn)
        } else if c2(s, 'i', 'n') {
            Some(Kw::In)
        } else if c2(s, 'i', 'f') {
            Some(Kw::If)
        } else if c2(s, 'l', 't') {
            Some(Kw::Lt)
        } else if c2(s, 'l', 'e') {
            Some(Kw::Le)
        } else if c2(s, 'e', 'q') {
            Some(Kw::Eq)
        } else {
            None
        }
    } else if s.len() == 3 {
        if c3(s, 'I', 'n', 't') {
            Some(Kw::TInt)
        } else if c3(s, 'a', 'd', 'd') {
            Some(Kw::Add)
        } else if c3(s, 's', 'u', 'b') {
            Some(Kw::Sub)
        } else if c3(s, 'm', 'u', 'l') {
            Some(Kw::Mul)
        } else if c3(s, 'n', 'e', 'g') {
            Some(Kw::Neg)
        } else if c3(s, 'm', 'o', 'd') {
            Some(Kw::Mod)
        } else if c3(s, 'f', 's', 't') {
            Some(Kw::Fst)
        } else if c3(s, 's', 'n', 'd') {
            Some(Kw::Snd)
        } else if c3(s, 'l', 'e', 't') {
            Some(Kw::Let)
        } else if c3(s, 'm', 'i', 'n') {
            Some(Kw::Min)
        } else if c3(s, 'm', 'a', 'x') {
            Some(Kw::Max)
        } else {
            None
        }
    } else if s.len() == 4 {
        if c4(s, 'B', 'o', 'o', 'l') {
            Some(Kw::TBool)
        } else if c4(s, 'U', 'n', 'i', 't') {
            Some(Kw::TUnit)
        } else if c4(s, 'L', 'i', 's', 't') {
            Some(Kw::TList)
        } else if c4(s, 'P', 'a', 'i', 'r') {
            Some(Kw::TPair)
        } else if c4(s, 't', 'r', 'u', 'e') {
            Some(Kw::True)
        } else if c4(s, 'u', 'n', 'i', 't') {
            Some(Kw::Unit)
        } else if c4(s, 'l', 'i', 's', 't') {
            Some(Kw::List)
        } else if c4(s, 's', 'o', 'm', 'e') {
            Some(Kw::Some)
        } else if c4(s, 'n', 'o', 'n', 'e') {
            Some(Kw::None)
        } else if c4(s, 'p', 'a', 'i', 'r') {
            Some(Kw::Pair)
        } else if c4(s, 'f', 'o', 'l', 'd') {
            Some(Kw::Fold)
        } else if c4(s, 'c', 'o', 'n', 's') {
            Some(Kw::Cons)
        } else if c4(s, 's', 'o', 'r', 't') {
            Some(Kw::Sort)
        } else {
            None
        }
    } else if s.len() == 5 {
        if c5(s, 'e', 'n', 't', 'r', 'y') {
            Some(Kw::Entry)
        } else if c5(s, 'f', 'a', 'l', 's', 'e') {
            Some(Kw::False)
        } else if c5(s, 'r', 'a', 'n', 'g', 'e') {
            Some(Kw::Range)
        } else {
            None
        }
    } else if s.len() == 6 {
        if c6(s, 'O', 'p', 't', 'i', 'o', 'n') {
            Some(Kw::TOption)
        } else if c6(s, 'c', 'o', 'n', 'c', 'a', 't') {
            Some(Kw::Concat)
        } else if c6(s, 'l', 'e', 'n', 'g', 't', 'h') {
            Some(Kw::Length)
        } else if c6(s, 'u', 'n', 'c', 'o', 'n', 's') {
            Some(Kw::Uncons)
        } else {
            None
        }
    } else if s.len() == 7 {
        if c6(s, 'r', 'e', 'v', 'e', 'r', 's') && s[6] == 'e' {
            Some(Kw::Reverse)
        } else {
            None
        }
    } else if s.len() == 8 {
        if c6(s, 'c', 'o', 'n', 't', 'a', 'i') && s[6] == 'n' && s[7] == 's' {
            Some(Kw::Contains)
        } else {
            None
        }
    } else if s.len() == 12 {
        if c6(s, 'm', 'a', 't', 'c', 'h', '_') && s[6] == 'o' && s[7] == 'p' && s[8] == 't' && s[9] == 'i'
            && s[10] == 'o' && s[11] == 'n' {
            Some(Kw::MatchOption)
        } else {
            None
        }
    } else {
        None
    }
}

pub open spec fn bkw(b: Builtin) -> Kw {
    match b {
        Builtin::Add => Kw::Add,
        Builtin::Sub => Kw::Sub,
        Builtin::Mul => Kw::Mul,
        Builtin::Neg => Kw::Neg,
        Builtin::Lt => Kw::Lt,
        Builtin::Le => Kw::Le,
        Builtin::Eq => Kw::Eq,
        Builtin::Mod => Kw::Mod,
        Builtin::Fst => Kw::Fst,
        Builtin::Snd => Kw::Snd,
        Builtin::Cons => Kw::Cons,
        Builtin::Concat => Kw::Concat,
        Builtin::Reverse => Kw::Reverse,
        Builtin::Length => Kw::Length,
        Builtin::Uncons => Kw::Uncons,
        Builtin::Min => Kw::Min,
        Builtin::Max => Kw::Max,
        Builtin::Range => Kw::Range,
        Builtin::Contains => Kw::Contains,
        Builtin::Sort => Kw::Sort,
    }
}

pub open spec fn kw_b(k: Kw) -> Option<Builtin> {
    match k {
        Kw::Add => Some(Builtin::Add),
        Kw::Sub => Some(Builtin::Sub),
        Kw::Mul => Some(Builtin::Mul),
        Kw::Neg => Some(Builtin::Neg),
        Kw::Lt => Some(Builtin::Lt),
        Kw::Le => Some(Builtin::Le),
        Kw::Eq => Some(Builtin::Eq),
        Kw::Mod => Some(Builtin::Mod),
        Kw::Fst => Some(Builtin::Fst),
        Kw::Snd => Some(Builtin::Snd),
        Kw::Cons => Some(Builtin::Cons),
        Kw::Concat => Some(Builtin::Concat),
        Kw::Reverse => Some(Builtin::Reverse),
        Kw::Length => Some(Builtin::Length),
        Kw::Uncons => Some(Builtin::Uncons),
        Kw::Min => Some(Builtin::Min),
        Kw::Max => Some(Builtin::Max),
        Kw::Range => Some(Builtin::Range),
        Kw::Contains => Some(Builtin::Contains),
        Kw::Sort => Some(Builtin::Sort),
        _ => None,
    }
}

// ------------------------------------------------------------------ 文字の分類（§4.2）

pub open spec fn is_alpha(c: char) -> bool {
    (0x41 <= c as u32 && c as u32 <= 0x5a) || (0x61 <= c as u32 && c as u32 <= 0x7a)
}

pub open spec fn is_digit(c: char) -> bool {
    0x30 <= c as u32 && c as u32 <= 0x39
}

pub open spec fn ident_start(c: char) -> bool {
    is_alpha(c) || c == '_'
}

pub open spec fn ident_char(c: char) -> bool {
    ident_start(c) || is_digit(c)
}

pub open spec fn is_ws(c: char) -> bool {
    c == ' ' || c == '\t' || c == '\r' || c == '\n'
}

pub open spec fn is_sym(c: char) -> bool {
    c == '(' || c == ')' || c == '[' || c == ']' || c == '<' || c == '>' || c == ',' || c == ':'
        || c == '=' || c == '|'
}

/// IDENT（§4.2）で、予約語でないもの。
pub open spec fn ident_ok(x: Seq<char>) -> bool {
    &&& x.len() > 0
    &&& ident_start(x[0])
    &&& forall|i: int| 0 < i < x.len() ==> ident_char(#[trigger] x[i])
    &&& kw_of(x) is None
}

/// v1.1 の文脈キーワード（差分仕様 §2a）：組み込み関数と値の構築子の名前。変数・引数・束縛の名前に使える。
pub open spec fn soft(k: Kw) -> bool {
    kw_b(k) is Some || k == Kw::List || k == Kw::Some || k == Kw::None || k == Kw::Pair
}

/// 変数・引数・束縛の名前：IDENT か文脈キーワード。関数名と entry の名前は IDENT（`ident_ok`）に限る。
pub open spec fn name_ok(x: Seq<char>) -> bool {
    ident_ok(x) || (kw_of(x) is Some && soft(kw_of(x)->Some_0))
}

// ------------------------------------------------------------------ token と表面 AST

pub enum Tok {
    Int(int),
    Id(Seq<char>),
    Kw(Kw),
    Sym(char),
    Arrow,
}

pub enum Sx {
    Int(int),
    Bool(bool),
    Unit,
    Var(Seq<char>),
    List(Ty, Seq<Sx>),
    Some(Box<Sx>),
    None(Ty),
    Pair(Box<Sx>, Box<Sx>),
    Builtin(Builtin, Seq<Sx>),
    Call(Seq<char>, Seq<Sx>),
    Let(Seq<char>, Box<Sx>, Box<Sx>),
    If(Box<Sx>, Box<Sx>, Box<Sx>),
    Fold(Box<Sx>, Box<Sx>, Seq<char>, Seq<char>, Box<Sx>),
    /// match_option(m, n, |x| s)
    Match(Box<Sx>, Box<Sx>, Seq<char>, Box<Sx>),
}

pub enum Sd {
    Fn(Seq<char>, Seq<(Seq<char>, Ty)>, Ty, Sx),
    Entry(Seq<char>),
}

// ------------------------------------------------------------------ EBNF：AST の token 列（§4.1）

pub open spec fn tt(t: Ty, k: Seq<Tok>) -> Seq<Tok>
    decreases t,
{
    match t {
        Ty::Int => seq![Tok::Kw(Kw::TInt)] + k,
        Ty::Bool => seq![Tok::Kw(Kw::TBool)] + k,
        Ty::Unit => seq![Tok::Kw(Kw::TUnit)] + k,
        Ty::List(a) => seq![Tok::Kw(Kw::TList), Tok::Sym('<')] + tt(*a, seq![Tok::Sym('>')] + k),
        Ty::Option(a) => seq![Tok::Kw(Kw::TOption), Tok::Sym('<')] + tt(*a, seq![Tok::Sym('>')] + k),
        Ty::Pair(a, b) => seq![Tok::Kw(Kw::TPair), Tok::Sym('<')] + tt(
            *a,
            seq![Tok::Sym(',')] + tt(*b, seq![Tok::Sym('>')] + k),
        ),
    }
}

pub open spec fn te(e: Sx, k: Seq<Tok>) -> Seq<Tok>
    decreases e, 0nat,
{
    match e {
        Sx::Int(n) => seq![Tok::Int(n)] + k,
        Sx::Bool(b) => seq![Tok::Kw(if b { Kw::True } else { Kw::False })] + k,
        Sx::Unit => seq![Tok::Kw(Kw::Unit)] + k,
        Sx::Var(x) => seq![word_tok(x)] + k,
        Sx::List(t, es) => seq![Tok::Kw(Kw::List), Tok::Sym('<')] + tt(
            t,
            seq![Tok::Sym('>'), Tok::Sym('(')] + targs(es, 0, k),
        ),
        Sx::Some(a) => seq![Tok::Kw(Kw::Some), Tok::Sym('(')] + te(*a, seq![Tok::Sym(')')] + k),
        Sx::None(t) => seq![Tok::Kw(Kw::None), Tok::Sym('<')] + tt(t, seq![Tok::Sym('>'), Tok::Sym('('), Tok::Sym(')')] + k),
        Sx::Pair(a, b) => seq![Tok::Kw(Kw::Pair), Tok::Sym('(')] + te(
            *a,
            seq![Tok::Sym(',')] + te(*b, seq![Tok::Sym(')')] + k),
        ),
        Sx::Builtin(b, es) => seq![Tok::Kw(bkw(b)), Tok::Sym('(')] + targs(es, 0, k),
        Sx::Call(f, es) => seq![Tok::Id(f), Tok::Sym('(')] + targs(es, 0, k),
        Sx::Let(x, a, b) => seq![Tok::Kw(Kw::Let), word_tok(x), Tok::Sym('=')] + te(
            *a,
            seq![Tok::Kw(Kw::In)] + te(*b, k),
        ),
        Sx::If(c, a, b) => seq![Tok::Kw(Kw::If), Tok::Sym('(')] + te(
            *c,
            seq![Tok::Sym(',')] + te(*a, seq![Tok::Sym(',')] + te(*b, seq![Tok::Sym(')')] + k)),
        ),
        Sx::Fold(l, i, a, x, b) => seq![Tok::Kw(Kw::Fold), Tok::Sym('(')] + te(
            *l,
            seq![Tok::Sym(',')] + te(
                *i,
                seq![Tok::Sym(','), Tok::Sym('|'), word_tok(a), Tok::Sym(','), word_tok(x), Tok::Sym('|')]
                    + te(*b, seq![Tok::Sym(')')] + k),
            ),
        ),
        Sx::Match(m, n, x, b) => seq![Tok::Kw(Kw::MatchOption), Tok::Sym('(')] + te(
            *m,
            seq![Tok::Sym(',')] + te(
                *n,
                seq![Tok::Sym(','), Tok::Sym('|'), word_tok(x), Tok::Sym('|')] + te(*b, seq![Tok::Sym(')')] + k),
            ),
        ),
    }
}

/// `[ arguments ] ")"`：es[i..] をカンマ区切りで並べ、閉じ括弧を付ける。
pub open spec fn targs(es: Seq<Sx>, i: nat, k: Seq<Tok>) -> Seq<Tok>
    decreases es, es.len() - i,
{
    if i >= es.len() {
        seq![Tok::Sym(')')] + k
    } else if i + 1 == es.len() {
        te(es[i as int], seq![Tok::Sym(')')] + k)
    } else {
        te(es[i as int], seq![Tok::Sym(',')] + targs(es, i + 1, k))
    }
}

/// `[ params ] ")"`
pub open spec fn tps(ps: Seq<(Seq<char>, Ty)>, i: nat, k: Seq<Tok>) -> Seq<Tok>
    decreases ps.len() - i,
{
    if i >= ps.len() {
        seq![Tok::Sym(')')] + k
    } else {
        seq![word_tok(ps[i as int].0), Tok::Sym(':')] + tt(
            ps[i as int].1,
            if i + 1 == ps.len() {
                seq![Tok::Sym(')')] + k
            } else {
                seq![Tok::Sym(',')] + tps(ps, i + 1, k)
            },
        )
    }
}

pub open spec fn tdecl(d: Sd, k: Seq<Tok>) -> Seq<Tok> {
    match d {
        Sd::Fn(f, ps, r, b) => seq![Tok::Kw(Kw::Fn), Tok::Id(f), Tok::Sym('(')] + tps(
            ps,
            0,
            seq![Tok::Arrow] + tt(r, seq![Tok::Sym('=')] + te(b, k)),
        ),
        Sd::Entry(x) => seq![Tok::Kw(Kw::Entry), Tok::Id(x)] + k,
    }
}

/// プログラム P[i..] の token 列。
pub open spec fn tds(p: Seq<Sd>, i: nat) -> Seq<Tok>
    decreases p.len() - i,
{
    if i >= p.len() {
        Seq::empty()
    } else {
        tdecl(p[i as int], tds(p, i + 1))
    }
}

// ------------------------------------------------------------------ 正準フォーマッタ（§4.3）

pub open spec fn ft(t: Ty, k: Seq<char>) -> Seq<char>
    decreases t,
{
    match t {
        Ty::Int => kwt(Kw::TInt) + k,
        Ty::Bool => kwt(Kw::TBool) + k,
        Ty::Unit => kwt(Kw::TUnit) + k,
        Ty::List(a) => kwt(Kw::TList) + (seq!['<'] + ft(*a, seq!['>'] + k)),
        Ty::Option(a) => kwt(Kw::TOption) + (seq!['<'] + ft(*a, seq!['>'] + k)),
        Ty::Pair(a, b) => kwt(Kw::TPair) + (seq!['<'] + ft(*a, seq![',', ' '] + ft(*b, seq!['>'] + k))),
    }
}

pub open spec fn fe(e: Sx, k: Seq<char>) -> Seq<char>
    decreases e, 0nat,
{
    match e {
        Sx::Int(n) => int_dec(n) + k,
        Sx::Bool(b) => kwt(if b { Kw::True } else { Kw::False }) + k,
        Sx::Unit => kwt(Kw::Unit) + k,
        Sx::Var(x) => x + k,
        Sx::List(t, es) => kwt(Kw::List) + (seq!['<'] + ft(t, seq!['>', '('] + fargs(es, 0, k))),
        Sx::Some(a) => kwt(Kw::Some) + (seq!['('] + fe(*a, seq![')'] + k)),
        Sx::None(t) => kwt(Kw::None) + (seq!['<'] + ft(t, seq!['>', '(', ')'] + k)),
        Sx::Pair(a, b) => kwt(Kw::Pair) + (seq!['('] + fe(*a, seq![',', ' '] + fe(*b, seq![')'] + k))),
        Sx::Builtin(b, es) => kwt(bkw(b)) + (seq!['('] + fargs(es, 0, k)),
        Sx::Call(f, es) => f + (seq!['('] + fargs(es, 0, k)),
        Sx::Let(x, a, b) => kwt(Kw::Let) + (seq![' '] + (x + (seq![' ', '=', ' '] + fe(
            *a,
            seq![' '] + (kwt(Kw::In) + (seq![' '] + fe(*b, k))),
        )))),
        Sx::If(c, a, b) => kwt(Kw::If) + (seq!['('] + fe(
            *c,
            seq![',', ' '] + fe(*a, seq![',', ' '] + fe(*b, seq![')'] + k)),
        )),
        Sx::Fold(l, i, a, x, b) => kwt(Kw::Fold) + (seq!['('] + fe(
            *l,
            seq![',', ' '] + fe(
                *i,
                seq![',', ' ', '|'] + (a + (seq![',', ' '] + (x + (seq!['|', ' '] + fe(*b, seq![')'] + k))))),
            ),
        )),
        Sx::Match(m, n, x, b) => kwt(Kw::MatchOption) + (seq!['('] + fe(
            *m,
            seq![',', ' '] + fe(*n, seq![',', ' ', '|'] + (x + (seq!['|', ' '] + fe(*b, seq![')'] + k)))),
        )),
    }
}

pub open spec fn fargs(es: Seq<Sx>, i: nat, k: Seq<char>) -> Seq<char>
    decreases es, es.len() - i,
{
    if i >= es.len() {
        seq![')'] + k
    } else if i + 1 == es.len() {
        fe(es[i as int], seq![')'] + k)
    } else {
        fe(es[i as int], seq![',', ' '] + fargs(es, i + 1, k))
    }
}

pub open spec fn fps(ps: Seq<(Seq<char>, Ty)>, i: nat, k: Seq<char>) -> Seq<char>
    decreases ps.len() - i,
{
    if i >= ps.len() {
        seq![')'] + k
    } else {
        ps[i as int].0 + (seq![':', ' '] + ft(
            ps[i as int].1,
            if i + 1 == ps.len() {
                seq![')'] + k
            } else {
                seq![',', ' '] + fps(ps, i + 1, k)
            },
        ))
    }
}

pub open spec fn fd(d: Sd, k: Seq<char>) -> Seq<char> {
    match d {
        Sd::Fn(f, ps, r, b) => kwt(Kw::Fn) + (seq![' '] + (f + (seq!['('] + fps(
            ps,
            0,
            seq![' ', '-', '>', ' '] + ft(r, seq![' ', '=', ' '] + fe(b, seq!['\n'] + k)),
        )))),
        Sd::Entry(x) => kwt(Kw::Entry) + (seq![' '] + (x + (seq!['\n'] + k))),
    }
}

/// 正準ソース canonical_source(P[i..])。
pub open spec fn fds(p: Seq<Sd>, i: nat) -> Seq<char>
    decreases p.len() - i,
{
    if i >= p.len() {
        Seq::empty()
    } else {
        fd(p[i as int], fds(p, i + 1))
    }
}

// ------------------------------------------------------------------ 字句解析（§4.2）

pub open spec fn prepend(t: Tok, o: Option<Seq<Tok>>) -> Option<Seq<Tok>> {
    match o {
        Some(u) => Some(seq![t] + u),
        None => None,
    }
}

/// i 以降で最初の CR/LF の位置（行コメントの終わり）。
pub open spec fn cend(s: Seq<char>, i: nat) -> nat
    decreases s.len() - i,
{
    if i >= s.len() || s[i as int] == '\n' || s[i as int] == '\r' {
        i
    } else {
        cend(s, i + 1)
    }
}

/// i 以降で識別子文字が続く最後の次の位置。
pub open spec fn wend(s: Seq<char>, i: nat) -> nat
    decreases s.len() - i,
{
    if i >= s.len() || !ident_char(s[i as int]) {
        i
    } else {
        wend(s, i + 1)
    }
}

/// i 以降で数字が続く最後の次の位置。
pub open spec fn dend(s: Seq<char>, i: nat) -> nat
    decreases s.len() - i,
{
    if i >= s.len() || !is_digit(s[i as int]) {
        i
    } else {
        dend(s, i + 1)
    }
}

pub open spec fn word_tok(w: Seq<char>) -> Tok {
    match kw_of(w) {
        Some(k) => Tok::Kw(k),
        None => Tok::Id(w),
    }
}

/// 字句解析。最初の不正で None（診断の種類は区別しない）。
pub open spec fn lex(s: Seq<char>) -> Option<Seq<Tok>>
    decreases s.len(),
{
    if s.len() == 0 {
        Some(Seq::empty())
    } else {
        let c = s[0];
        if is_ws(c) {
            lex(s.subrange(1, s.len() as int))
        } else if c == '/' {
            if s.len() >= 2 && s[1] == '/' {
                let j = cend(s, 2);
                if 2 <= j <= s.len() {
                    lex(s.subrange(j as int, s.len() as int))
                } else {
                    None
                }
            } else {
                None
            }
        } else if ident_start(c) {
            let j = wend(s, 1);
            if 1 <= j <= s.len() {
                prepend(word_tok(s.subrange(0, j as int)), lex(s.subrange(j as int, s.len() as int)))
            } else {
                None
            }
        } else if c == '-' && s.len() >= 2 && s[1] == '>' {
            prepend(Tok::Arrow, lex(s.subrange(2, s.len() as int)))
        } else if is_digit(c) || (c == '-' && s.len() >= 2 && is_digit(s[1])) {
            let d0: nat = if c == '-' { 1 } else { 0 };
            let j = dend(s, d0);
            if !(d0 < j <= s.len()) {
                None
            } else if s[d0 as int] == '0' && (j - d0 > 1 || c == '-') {
                None
            } else if j < s.len() && (ident_start(s[j as int]) || s[j as int] == '-' || s[j as int] == '.') {
                None
            } else {
                match int_val(s.subrange(0, j as int)) {
                    Some(n) => prepend(Tok::Int(n), lex(s.subrange(j as int, s.len() as int))),
                    None => None,
                }
            }
        } else if is_sym(c) {
            prepend(Tok::Sym(c), lex(s.subrange(1, s.len() as int)))
        } else {
            None
        }
    }
}

// ------------------------------------------------------------------ 構文解析（§4.1）

pub open spec fn sym(ts: Seq<Tok>, i: nat, c: char) -> bool {
    i < ts.len() && ts[i as int] == Tok::Sym(c)
}

pub open spec fn kwat(ts: Seq<Tok>, i: nat, k: Kw) -> bool {
    i < ts.len() && ts[i as int] == Tok::Kw(k)
}

/// 位置 i の IDENT（予約語でない識別子）。
pub open spec fn idt(ts: Seq<Tok>, i: nat) -> Option<Seq<char>> {
    if i < ts.len() && ts[i as int] is Id && ident_ok(ts[i as int]->Id_0) {
        Some(ts[i as int]->Id_0)
    } else {
        None
    }
}

/// 位置 i の変数・引数・束縛の名前（IDENT か文脈キーワード）。
pub open spec fn bdt(ts: Seq<Tok>, i: nat) -> Option<Seq<char>> {
    if i < ts.len() {
        match ts[i as int] {
            Tok::Id(x) => if ident_ok(x) { Some(x) } else { None },
            Tok::Kw(k) => if soft(k) { Some(kwt(k)) } else { None },
            _ => None,
        }
    } else {
        None
    }
}

/// 型。深さ上限 d を超える入れ子は受理しない。
pub open spec fn pt(ts: Seq<Tok>, i: nat, d: nat) -> Option<(Ty, nat)>
    decreases d,
{
    if d == 0 || i >= ts.len() {
        None
    } else {
        match ts[i as int] {
            Tok::Kw(Kw::TInt) => Some((Ty::Int, i + 1)),
            Tok::Kw(Kw::TBool) => Some((Ty::Bool, i + 1)),
            Tok::Kw(Kw::TUnit) => Some((Ty::Unit, i + 1)),
            Tok::Kw(Kw::TList) => if sym(ts, i + 1, '<') {
                match pt(ts, i + 2, (d - 1) as nat) {
                    Some((a, j)) => if sym(ts, j, '>') {
                        Some((Ty::List(Box::new(a)), j + 1))
                    } else {
                        None
                    },
                    None => None,
                }
            } else {
                None
            },
            Tok::Kw(Kw::TOption) => if sym(ts, i + 1, '<') {
                match pt(ts, i + 2, (d - 1) as nat) {
                    Some((a, j)) => if sym(ts, j, '>') {
                        Some((Ty::Option(Box::new(a)), j + 1))
                    } else {
                        None
                    },
                    None => None,
                }
            } else {
                None
            },
            Tok::Kw(Kw::TPair) => if sym(ts, i + 1, '<') {
                match pt(ts, i + 2, (d - 1) as nat) {
                    Some((a, j)) => if sym(ts, j, ',') {
                        match pt(ts, j + 1, (d - 1) as nat) {
                            Some((b, m)) => if sym(ts, m, '>') {
                                Some((Ty::Pair(Box::new(a), Box::new(b)), m + 1))
                            } else {
                                None
                            },
                            None => None,
                        }
                    } else {
                        None
                    },
                    None => None,
                }
            } else {
                None
            },
            _ => None,
        }
    }
}

/// 式。d は式の入れ子の深さ上限、td は型の深さ上限。
pub open spec fn pe(ts: Seq<Tok>, i: nat, d: nat, td: nat) -> Option<(Sx, nat)>
    decreases d, 0nat, 0nat,
{
    if d == 0 || i >= ts.len() {
        None
    } else {
        let d1 = (d - 1) as nat;
        match ts[i as int] {
            Tok::Int(n) => Some((Sx::Int(n), i + 1)),
            Tok::Id(x) => if !ident_ok(x) {
                None
            } else if sym(ts, i + 1, '(') {
                match pargs(ts, i + 2, d1, td) {
                    Some((es, j)) => Some((Sx::Call(x, es), j)),
                    None => None,
                }
            } else {
                Some((Sx::Var(x), i + 1))
            },
            Tok::Kw(k) => {
                if soft(k) && !sym(ts, i + 1, '(') && !sym(ts, i + 1, '<') {
                    Some((Sx::Var(kwt(k)), i + 1))
                } else if k == Kw::True {
                    Some((Sx::Bool(true), i + 1))
                } else if k == Kw::False {
                    Some((Sx::Bool(false), i + 1))
                } else if k == Kw::Unit {
                    Some((Sx::Unit, i + 1))
                } else if k == Kw::List {
                    if sym(ts, i + 1, '<') {
                        match pt(ts, i + 2, td) {
                            Some((t, j)) => if sym(ts, j, '>') && sym(ts, j + 1, '(') {
                                match pargs(ts, j + 2, d1, td) {
                                    Some((es, m)) => Some((Sx::List(t, es), m)),
                                    None => None,
                                }
                            } else {
                                None
                            },
                            None => None,
                        }
                    } else {
                        None
                    }
                } else if k == Kw::Some {
                    if sym(ts, i + 1, '(') {
                        match pe(ts, i + 2, d1, td) {
                            Some((a, j)) => if sym(ts, j, ')') {
                                Some((Sx::Some(Box::new(a)), j + 1))
                            } else {
                                None
                            },
                            None => None,
                        }
                    } else {
                        None
                    }
                } else if k == Kw::None {
                    if sym(ts, i + 1, '<') {
                        match pt(ts, i + 2, td) {
                            Some((t, j)) => if sym(ts, j, '>') && sym(ts, j + 1, '(') && sym(ts, j + 2, ')') {
                                Some((Sx::None(t), j + 3))
                            } else {
                                None
                            },
                            None => None,
                        }
                    } else {
                        None
                    }
                } else if k == Kw::Pair {
                    if sym(ts, i + 1, '(') {
                        match pe(ts, i + 2, d1, td) {
                            Some((a, j)) => if sym(ts, j, ',') {
                                match pe(ts, j + 1, d1, td) {
                                    Some((b, m)) => if sym(ts, m, ')') {
                                        Some((Sx::Pair(Box::new(a), Box::new(b)), m + 1))
                                    } else {
                                        None
                                    },
                                    None => None,
                                }
                            } else {
                                None
                            },
                            None => None,
                        }
                    } else {
                        None
                    }
                } else if k == Kw::Let {
                    match bdt(ts, i + 1) {
                        Some(x) => if sym(ts, i + 2, '=') {
                            match pe(ts, i + 3, d1, td) {
                                Some((a, j)) => if kwat(ts, j, Kw::In) {
                                    match pe(ts, j + 1, d1, td) {
                                        Some((b, m)) => Some((Sx::Let(x, Box::new(a), Box::new(b)), m)),
                                        None => None,
                                    }
                                } else {
                                    None
                                },
                                None => None,
                            }
                        } else {
                            None
                        },
                        None => None,
                    }
                } else if k == Kw::If {
                    if sym(ts, i + 1, '(') {
                        match pe(ts, i + 2, d1, td) {
                            Some((c, j)) => if sym(ts, j, ',') {
                                match pe(ts, j + 1, d1, td) {
                                    Some((a, m)) => if sym(ts, m, ',') {
                                        match pe(ts, m + 1, d1, td) {
                                            Some((b, q)) => if sym(ts, q, ')') {
                                                Some((Sx::If(Box::new(c), Box::new(a), Box::new(b)), q + 1))
                                            } else {
                                                None
                                            },
                                            None => None,
                                        }
                                    } else {
                                        None
                                    },
                                    None => None,
                                }
                            } else {
                                None
                            },
                            None => None,
                        }
                    } else {
                        None
                    }
                } else if k == Kw::Fold {
                    if sym(ts, i + 1, '(') {
                        match pe(ts, i + 2, d1, td) {
                            Some((l, j)) => if sym(ts, j, ',') {
                                match pe(ts, j + 1, d1, td) {
                                    Some((n, m)) => if sym(ts, m, ',') && sym(ts, m + 1, '|') {
                                        match (bdt(ts, m + 2), bdt(ts, m + 4)) {
                                            (Some(a), Some(x)) => if sym(ts, m + 3, ',') && sym(ts, m + 5, '|') {
                                                match pe(ts, m + 6, d1, td) {
                                                    Some((b, q)) => if sym(ts, q, ')') {
                                                        Some((Sx::Fold(Box::new(l), Box::new(n), a, x, Box::new(b)), q + 1))
                                                    } else {
                                                        None
                                                    },
                                                    None => None,
                                                }
                                            } else {
                                                None
                                            },
                                            _ => None,
                                        }
                                    } else {
                                        None
                                    },
                                    None => None,
                                }
                            } else {
                                None
                            },
                            None => None,
                        }
                    } else {
                        None
                    }
                } else if k == Kw::MatchOption {
                    if sym(ts, i + 1, '(') {
                        match pe(ts, i + 2, d1, td) {
                            Some((m, j)) => if sym(ts, j, ',') {
                                match pe(ts, j + 1, d1, td) {
                                    Some((n, q)) => if sym(ts, q, ',') && sym(ts, q + 1, '|') {
                                        match bdt(ts, q + 2) {
                                            Some(x) => if sym(ts, q + 3, '|') {
                                                match pe(ts, q + 4, d1, td) {
                                                    Some((b, u)) => if sym(ts, u, ')') {
                                                        Some((Sx::Match(Box::new(m), Box::new(n), x, Box::new(b)), u + 1))
                                                    } else {
                                                        None
                                                    },
                                                    None => None,
                                                }
                                            } else {
                                                None
                                            },
                                            None => None,
                                        }
                                    } else {
                                        None
                                    },
                                    None => None,
                                }
                            } else {
                                None
                            },
                            None => None,
                        }
                    } else {
                        None
                    }
                } else {
                    match kw_b(k) {
                        Some(b) => if sym(ts, i + 1, '(') {
                            match pargs(ts, i + 2, d1, td) {
                                Some((es, j)) => Some((Sx::Builtin(b, es), j)),
                                None => None,
                            }
                        } else {
                            None
                        },
                        None => None,
                    }
                }
            },
            _ => None,
        }
    }
}

/// `[ arguments ] ")"`
pub open spec fn pargs(ts: Seq<Tok>, i: nat, d: nat, td: nat) -> Option<(Seq<Sx>, nat)>
    decreases d, 2nat, 0nat,
{
    if sym(ts, i, ')') {
        Some((Seq::empty(), i + 1))
    } else {
        pargs1(ts, i, d, td)
    }
}

/// `arguments ")"`
pub open spec fn pargs1(ts: Seq<Tok>, i: nat, d: nat, td: nat) -> Option<(Seq<Sx>, nat)>
    decreases d, 1nat, ts.len() - i,
{
    match pe(ts, i, d, td) {
        Some((e, j)) => if sym(ts, j, ')') {
            Some((seq![e], j + 1))
        } else if sym(ts, j, ',') && i < j {
            match pargs1(ts, j + 1, d, td) {
                Some((es, m)) => Some((seq![e] + es, m)),
                None => None,
            }
        } else {
            None
        },
        None => None,
    }
}

/// `[ params ] ")"`
pub open spec fn pparams(ts: Seq<Tok>, i: nat, td: nat) -> Option<(Seq<(Seq<char>, Ty)>, nat)> {
    if sym(ts, i, ')') {
        Some((Seq::empty(), i + 1))
    } else {
        pparams1(ts, i, td)
    }
}

pub open spec fn pparams1(ts: Seq<Tok>, i: nat, td: nat) -> Option<(Seq<(Seq<char>, Ty)>, nat)>
    decreases ts.len() - i,
{
    match bdt(ts, i) {
        Some(x) => if sym(ts, i + 1, ':') {
            match pt(ts, i + 2, td) {
                Some((t, j)) => if sym(ts, j, ')') {
                    Some((seq![(x, t)], j + 1))
                } else if sym(ts, j, ',') && i < j {
                    match pparams1(ts, j + 1, td) {
                        Some((ps, m)) => Some((seq![(x, t)] + ps, m)),
                        None => None,
                    }
                } else {
                    None
                },
                None => None,
            }
        } else {
            None
        },
        None => None,
    }
}

/// 宣言一つ。
pub open spec fn pd(ts: Seq<Tok>, i: nat, d: nat, td: nat) -> Option<(Sd, nat)> {
    if kwat(ts, i, Kw::Fn) {
        match idt(ts, i + 1) {
            Some(f) => if sym(ts, i + 2, '(') {
                match pparams(ts, i + 3, td) {
                    Some((ps, j)) => if j < ts.len() && ts[j as int] == Tok::Arrow {
                        match pt(ts, j + 1, td) {
                            Some((r, m)) => if sym(ts, m, '=') {
                                match pe(ts, m + 1, d, td) {
                                    Some((b, q)) => Some((Sd::Fn(f, ps, r, b), q)),
                                    None => None,
                                }
                            } else {
                                None
                            },
                            None => None,
                        }
                    } else {
                        None
                    },
                    None => None,
                }
            } else {
                None
            },
            None => None,
        }
    } else if kwat(ts, i, Kw::Entry) {
        match idt(ts, i + 1) {
            Some(x) => Some((Sd::Entry(x), i + 2)),
            None => None,
        }
    } else {
        None
    }
}

/// 宣言列（EOF まで）。
pub open spec fn pds(ts: Seq<Tok>, i: nat, d: nat, td: nat) -> Option<Seq<Sd>>
    decreases ts.len() - i,
{
    if i >= ts.len() {
        Some(Seq::empty())
    } else {
        match pd(ts, i, d, td) {
            Some((x, j)) => if i < j <= ts.len() {
                match pds(ts, j, d, td) {
                    Some(xs) => Some(seq![x] + xs),
                    None => None,
                }
            } else {
                None
            },
            None => None,
        }
    }
}

/// source を AST に。d、td は式と型の入れ子の深さ上限。
pub open spec fn parse(s: Seq<char>, d: nat, td: nat) -> Option<Seq<Sd>> {
    match lex(s) {
        Some(ts) => pds(ts, 0, d, td),
        None => None,
    }
}

// ------------------------------------------------------------------ 深さ上限と名前の妥当性

pub open spec fn bt(t: Ty, d: nat) -> bool
    decreases t,
{
    d > 0 && match t {
        Ty::List(a) => bt(*a, (d - 1) as nat),
        Ty::Option(a) => bt(*a, (d - 1) as nat),
        Ty::Pair(a, b) => bt(*a, (d - 1) as nat) && bt(*b, (d - 1) as nat),
        _ => true,
    }
}

/// 式 e は深さ d・型の深さ td の上限内にあり、名前は全て IDENT。
pub open spec fn bx(e: Sx, d: nat, td: nat) -> bool
    decreases e, 0nat,
{
    d > 0 && {
        let d1 = (d - 1) as nat;
        match e {
            Sx::Var(x) => name_ok(x),
            Sx::List(t, es) => bt(t, td) && bxs(es, 0, d1, td),
            Sx::Some(a) => bx(*a, d1, td),
            Sx::None(t) => bt(t, td),
            Sx::Pair(a, b) => bx(*a, d1, td) && bx(*b, d1, td),
            Sx::Builtin(_, es) => bxs(es, 0, d1, td),
            Sx::Call(f, es) => ident_ok(f) && bxs(es, 0, d1, td),
            Sx::Let(x, a, b) => name_ok(x) && bx(*a, d1, td) && bx(*b, d1, td),
            Sx::If(c, a, b) => bx(*c, d1, td) && bx(*a, d1, td) && bx(*b, d1, td),
            Sx::Fold(l, i, a, x, b) => name_ok(a) && name_ok(x) && bx(*l, d1, td) && bx(*i, d1, td) && bx(
                *b,
                d1,
                td,
            ),
            Sx::Match(m, n, x, b) => name_ok(x) && bx(*m, d1, td) && bx(*n, d1, td) && bx(*b, d1, td),
            _ => true,
        }
    }
}

pub open spec fn bxs(es: Seq<Sx>, i: nat, d: nat, td: nat) -> bool
    decreases es, es.len() - i,
{
    i >= es.len() || (bx(es[i as int], d, td) && bxs(es, i + 1, d, td))
}

pub open spec fn bps(ps: Seq<(Seq<char>, Ty)>, i: nat, td: nat) -> bool
    decreases ps.len() - i,
{
    i >= ps.len() || (name_ok(ps[i as int].0) && bt(ps[i as int].1, td) && bps(ps, i + 1, td))
}

pub open spec fn bd(x: Sd, d: nat, td: nat) -> bool {
    match x {
        Sd::Fn(f, ps, r, b) => ident_ok(f) && bps(ps, 0, td) && bt(r, td) && bx(b, d, td),
        Sd::Entry(x) => ident_ok(x),
    }
}

pub open spec fn bds(p: Seq<Sd>, i: nat, d: nat, td: nat) -> bool
    decreases p.len() - i,
{
    i >= p.len() || (bd(p[i as int], d, td) && bds(p, i + 1, d, td))
}

} // verus!
