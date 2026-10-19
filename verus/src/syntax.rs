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
    Div,
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
    TChar,
    TString,
    Code,
    CharOf,
    ToString,
    ParseInt,
    TResult,
    Ok,
    Err,
    MatchResult,
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
        Kw::Div => seq!['d', 'i', 'v'],
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
        Kw::TChar => seq!['C', 'h', 'a', 'r'],
        Kw::TString => seq!['S', 't', 'r', 'i', 'n', 'g'],
        Kw::Code => seq!['c', 'o', 'd', 'e'],
        Kw::CharOf => seq!['c', 'h', 'a', 'r'],
        Kw::ToString => seq!['t', 'o', '_', 's', 't', 'r', 'i', 'n', 'g'],
        Kw::ParseInt => seq!['p', 'a', 'r', 's', 'e', '_', 'i', 'n', 't'],
        Kw::TResult => seq!['R', 'e', 's', 'u', 'l', 't'],
        Kw::Ok => seq!['o', 'k'],
        Kw::Err => seq!['e', 'r', 'r'],
        Kw::MatchResult => seq!['m', 'a', 't', 'c', 'h', '_', 'r', 'e', 's', 'u', 'l', 't'],
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
        } else if c2(s, 'o', 'k') {
            Some(Kw::Ok)
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
        } else if c3(s, 'd', 'i', 'v') {
            Some(Kw::Div)
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
        } else if c3(s, 'e', 'r', 'r') {
            Some(Kw::Err)
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
        } else if c4(s, 'C', 'h', 'a', 'r') {
            Some(Kw::TChar)
        } else if c4(s, 'c', 'o', 'd', 'e') {
            Some(Kw::Code)
        } else if c4(s, 'c', 'h', 'a', 'r') {
            Some(Kw::CharOf)
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
        } else if c6(s, 'S', 't', 'r', 'i', 'n', 'g') {
            Some(Kw::TString)
        } else if c6(s, 'R', 'e', 's', 'u', 'l', 't') {
            Some(Kw::TResult)
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
    } else if s.len() == 9 {
        if c6(s, 't', 'o', '_', 's', 't', 'r') && s[6] == 'i' && s[7] == 'n' && s[8] == 'g' {
            Some(Kw::ToString)
        } else if c6(s, 'p', 'a', 'r', 's', 'e', '_') && s[6] == 'i' && s[7] == 'n' && s[8] == 't' {
            Some(Kw::ParseInt)
        } else {
            None
        }
    } else if s.len() == 12 {
        if c6(s, 'm', 'a', 't', 'c', 'h', '_') && s[6] == 'o' && s[7] == 'p' && s[8] == 't' && s[9] == 'i'
            && s[10] == 'o' && s[11] == 'n' {
            Some(Kw::MatchOption)
        } else if c6(s, 'm', 'a', 't', 'c', 'h', '_') && s[6] == 'r' && s[7] == 'e' && s[8] == 's' && s[9] == 'u'
            && s[10] == 'l' && s[11] == 't' {
            Some(Kw::MatchResult)
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
        Builtin::Div => Kw::Div,
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
        Builtin::Code => Kw::Code,
        Builtin::CharOf => Kw::CharOf,
        Builtin::ToString => Kw::ToString,
        Builtin::ParseInt => Kw::ParseInt,
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
        Kw::Div => Some(Builtin::Div),
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
        Kw::Code => Some(Builtin::Code),
        Kw::CharOf => Some(Builtin::CharOf),
        Kw::ToString => Some(Builtin::ToString),
        Kw::ParseInt => Some(Builtin::ParseInt),
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
        || c == '=' || c == '|' || c == '{' || c == '}' || c == '.'
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
    kw_b(k) is Some || k == Kw::List || k == Kw::Some || k == Kw::None || k == Kw::Pair || k == Kw::Entry || k == Kw::Ok || k == Kw::Err
}

/// 変数・引数・束縛の名前：IDENT か文脈キーワード。関数名と entry の名前は IDENT（`ident_ok`）に限る。
pub open spec fn name_ok(x: Seq<char>) -> bool {
    ident_ok(x) || (kw_of(x) is Some && soft(kw_of(x)->Some_0))
}

// ------------------------------------------------------------------ 文字・文字列リテラル（v1.2）

/// リテラルに書ける文字。制御文字は改行・タブ・復帰だけで、エスケープで書く。
pub open spec fn lit_ok(c: char) -> bool {
    (c as u32) >= 0x20 || c == '\n' || c == '\t' || c == '\r'
}

pub open spec fn str_ok(w: Seq<char>) -> bool {
    forall|i: int| 0 <= i < w.len() ==> lit_ok(#[trigger] w[i])
}

/// 正準形での 1 文字の綴り。q は区切りの引用符。
pub open spec fn esc(c: char, q: char) -> Seq<char> {
    if c == '\\' {
        seq!['\\', '\\']
    } else if c == q {
        seq!['\\', q]
    } else if c == '\n' {
        seq!['\\', 'n']
    } else if c == '\t' {
        seq!['\\', 't']
    } else if c == '\r' {
        seq!['\\', 'r']
    } else {
        seq![c]
    }
}

pub open spec fn escs(w: Seq<char>, q: char) -> Seq<char>
    decreases w.len(),
{
    if w.len() == 0 {
        Seq::empty()
    } else {
        esc(w[0], q) + escs(w.drop_first(), q)
    }
}

/// エスケープ `\x` が表す文字。
pub open spec fn unesc(x: char, q: char) -> Option<char> {
    if x == '\\' {
        Some('\\')
    } else if x == q {
        Some(q)
    } else if x == 'n' {
        Some('\n')
    } else if x == 't' {
        Some('\t')
    } else if x == 'r' {
        Some('\r')
    } else {
        None
    }
}

/// 文字列リテラルの中身を位置 i から閉じ引用符まで読む。結果は（中身, 閉じ引用符の次の位置）。
pub open spec fn slit(s: Seq<char>, i: nat) -> Option<(Seq<char>, nat)>
    decreases s.len() - i,
{
    if i >= s.len() {
        None
    } else if s[i as int] == '"' {
        Some((Seq::empty(), i + 1))
    } else if s[i as int] == '\\' {
        if i + 1 < s.len() {
            match unesc(s[(i + 1) as int], '"') {
                Some(c) => match slit(s, i + 2) {
                    Some((w, j)) => Some((seq![c] + w, j)),
                    None => None,
                },
                None => None,
            }
        } else {
            None
        }
    } else if (s[i as int] as u32) < 0x20 {
        None
    } else {
        match slit(s, i + 1) {
            Some((w, j)) => Some((seq![s[i as int]] + w, j)),
            None => None,
        }
    }
}

// ------------------------------------------------------------------ token と表面 AST

pub enum Tok {
    Int(int),
    /// v1.2：文字リテラル `'c'`。
    Chr(char),
    /// v1.2：文字列リテラル `"..."`（中身はエスケープを戻した文字の列）。
    Str(Seq<char>),
    Id(Seq<char>),
    Kw(Kw),
    Sym(char),
    Arrow,
}

pub enum Sx {
    Int(int),
    Chr(char),
    Str(Seq<char>),
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
    /// v1.4：ok<T, E>(x)（true）、err<T, E>(x)（false）
    Inj(bool, Ty, Ty, Box<Sx>),
    /// v1.4：match_result(m, |x| a, |y| b)
    MatchR(Box<Sx>, Seq<char>, Box<Sx>, Seq<char>, Box<Sx>),
    /// v1.1：e.f1.f2…（後置、左結合。受ける式は recv_ok、field 名は IDENT で、列は空でない）
    Fld(Box<Sx>, Seq<Seq<char>>),
    /// v1.1：R { f: e, ..b }（フィールドの並びと、省略できる base）
    Rec(Seq<char>, Seq<(Seq<char>, Sx)>, Option<Box<Sx>>),
}

pub enum Sd {
    Fn(Seq<char>, Seq<(Seq<char>, Ty)>, Ty, Sx),
    Entry(Seq<char>),
    /// v1.1：type R = { f: T, ... }（末尾の `,` の有無を持つ。整形がトークン列を変えないため）
    RecTy(Seq<char>, Seq<(Seq<char>, Ty)>, bool),
    /// v1.4：type S = V1 | V2(T, U)（構築子の名前と、中身の型の並び）
    Sum(Seq<char>, Seq<(Seq<char>, Seq<Ty>)>),
}

/// 宣言の先頭で読む文脈語 `type` の綴り（予約語ではない）。
pub open spec fn tyw() -> Seq<char> {
    seq!['t', 'y', 'p', 'e']
}

/// 後置（受ける式として許す形）：Let と整数は、続く `.f` と読み違えるか、字句に入らないので受けない。
pub open spec fn recv_ok(e: Sx) -> bool {
    !(e is Let) && !(e is Int) && !(e is Fld)
}

/// 末尾が整数の式（Let は本体で決まる）。後置の `.` は付かない。
pub open spec fn ends_int(e: Sx) -> bool
    decreases e,
{
    match e {
        Sx::Int(_) => true,
        Sx::Let(_, _, b) => ends_int(*b),
        _ => false,
    }
}

// ------------------------------------------------------------------ EBNF：AST の token 列（§4.1）

pub open spec fn tt(t: Ty, k: Seq<Tok>) -> Seq<Tok>
    decreases t,
{
    match t {
        Ty::Int => seq![Tok::Kw(Kw::TInt)] + k,
        Ty::Bool => seq![Tok::Kw(Kw::TBool)] + k,
        Ty::Unit => seq![Tok::Kw(Kw::TUnit)] + k,
        Ty::Char => seq![Tok::Kw(Kw::TChar)] + k,
        Ty::List(a) => if *a == Ty::Char {
            seq![Tok::Kw(Kw::TString)] + k
        } else {
            seq![Tok::Kw(Kw::TList), Tok::Sym('<')] + tt(*a, seq![Tok::Sym('>')] + k)
        },
        Ty::Option(a) => seq![Tok::Kw(Kw::TOption), Tok::Sym('<')] + tt(*a, seq![Tok::Sym('>')] + k),
        Ty::Pair(a, b) => seq![Tok::Kw(Kw::TPair), Tok::Sym('<')] + tt(
            *a,
            seq![Tok::Sym(',')] + tt(*b, seq![Tok::Sym('>')] + k),
        ),
        Ty::Result(a, b) => seq![Tok::Kw(Kw::TResult), Tok::Sym('<')] + tt(
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
        Sx::Chr(c) => seq![Tok::Chr(c)] + k,
        Sx::Str(w) => seq![Tok::Str(w)] + k,
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
        Sx::Inj(ok, t, u, x) => seq![Tok::Kw(if ok { Kw::Ok } else { Kw::Err }), Tok::Sym('<')] + tt(
            t,
            seq![Tok::Sym(',')] + tt(u, seq![Tok::Sym('>'), Tok::Sym('(')] + te(*x, seq![Tok::Sym(')')] + k)),
        ),
        Sx::MatchR(m, x, a, y, b) => seq![Tok::Kw(Kw::MatchResult), Tok::Sym('(')] + te(
            *m,
            seq![Tok::Sym(','), Tok::Sym('|'), word_tok(x), Tok::Sym('|')] + te(
                *a,
                seq![Tok::Sym(','), Tok::Sym('|'), word_tok(y), Tok::Sym('|')] + te(*b, seq![Tok::Sym(')')] + k),
            ),
        ),
        Sx::Fld(a, fs) => te(*a, tdots(fs, k)),
        Sx::Rec(r, fs, b) => seq![word_tok(r), Tok::Sym('{')] + tfe(fs, 0, rtail(fs.len() > 0, b, k)),
    }
}

/// `"." IDENT` の並び fs の後に k。
pub open spec fn tdots(fs: Seq<Seq<char>>, k: Seq<Tok>) -> Seq<Tok>
    decreases fs.len(),
{
    if fs.len() == 0 {
        k
    } else {
        seq![Tok::Sym('.'), word_tok(fs[0])] + tdots(fs.subrange(1, fs.len() as int), k)
    }
}

/// レコード式の `..base` と閉じ括弧。fields が空でないなら base の前にカンマ。
pub open spec fn rtail(ne: bool, b: Option<Box<Sx>>, k: Seq<Tok>) -> Seq<Tok>
    decreases b, 0nat,
{
    match b {
        Some(x) => (if ne { seq![Tok::Sym(',')] } else { seq![] }) + seq![Tok::Sym('.'), Tok::Sym('.')] + te(
            *x,
            seq![Tok::Sym('}')] + k,
        ),
        None => seq![Tok::Sym('}')] + k,
    }
}

/// レコード式の field の並び fs[i..]。最後の field の後ろに tail が続く。
pub open spec fn tfe(fs: Seq<(Seq<char>, Sx)>, i: nat, tail: Seq<Tok>) -> Seq<Tok>
    decreases fs, fs.len() - i,
{
    if i >= fs.len() {
        tail
    } else {
        seq![word_tok(fs[i as int].0), Tok::Sym(':')] + te(
            fs[i as int].1,
            if i + 1 == fs.len() {
                tail
            } else {
                seq![Tok::Sym(',')] + tfe(fs, i + 1, tail)
            },
        )
    }
}

/// レコード型の宣言の field の並び fs[i..]。最後の field の後ろに、末尾のカンマ tc があれば `,` を置き、tail（閉じ括弧を含む）が続く。
pub open spec fn tfd(fs: Seq<(Seq<char>, Ty)>, i: nat, tc: bool, tail: Seq<Tok>) -> Seq<Tok>
    decreases fs, fs.len() - i,
{
    if i >= fs.len() {
        tail
    } else {
        seq![word_tok(fs[i as int].0), Tok::Sym(':')] + tt(
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
        )
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

/// 大文字（構築子の名前の先頭）。
pub open spec fn is_upper(c: char) -> bool {
    0x41 <= c as u32 && c as u32 <= 0x5a
}

/// 構築子の名前：IDENT で、先頭が大文字。
pub open spec fn cname_ok(c: Seq<char>) -> bool {
    c.len() > 0 && ident_ok(c) && is_upper(c[0])
}

/// 位置 i の構築子の名前（大文字で始まる IDENT）。
pub open spec fn cidt(ts: Seq<Tok>, i: nat) -> Option<Seq<char>> {
    match idt(ts, i) {
        Some(c) => if c.len() > 0 && is_upper(c[0]) {
            Some(c)
        } else {
            None
        },
        None => None,
    }
}

/// 中身の型の並び `T, U, ...`（tail の前まで）。
pub open spec fn tts(ps: Seq<Ty>, i: nat, k: Seq<Tok>) -> Seq<Tok>
    decreases ps.len() - i,
{
    if i >= ps.len() {
        k
    } else if i + 1 == ps.len() {
        tt(ps[i as int], k)
    } else {
        tt(ps[i as int], seq![Tok::Sym(',')] + tts(ps, i + 1, k))
    }
}

/// 構築子の中身：空なら何もなく、そうでなければ `(` 型の並び `)`。
pub open spec fn tpay(ps: Seq<Ty>, k: Seq<Tok>) -> Seq<Tok> {
    if ps.len() == 0 {
        k
    } else {
        seq![Tok::Sym('(')] + tts(ps, 0, seq![Tok::Sym(')')] + k)
    }
}

/// 直和型の構築子の並び（`|` で区切り、最後の後ろに k）。
pub open spec fn tvars(vs: Seq<(Seq<char>, Seq<Ty>)>, i: nat, k: Seq<Tok>) -> Seq<Tok>
    decreases vs.len() - i,
{
    if i >= vs.len() {
        k
    } else {
        seq![word_tok(vs[i as int].0)] + tpay(
            vs[i as int].1,
            if i + 1 == vs.len() {
                k
            } else {
                seq![Tok::Sym('|')] + tvars(vs, i + 1, k)
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
        Sd::RecTy(r, fs, tc) => seq![Tok::Id(tyw()), word_tok(r), Tok::Sym('='), Tok::Sym('{')] + tfd(fs, 0, tc, seq![Tok::Sym('}')] + k),
        Sd::Sum(r, vs) => seq![Tok::Id(tyw()), word_tok(r), Tok::Sym('=')] + tvars(vs, 0, k),
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
        Ty::Char => kwt(Kw::TChar) + k,
        Ty::List(a) => if *a == Ty::Char {
            kwt(Kw::TString) + k
        } else {
            kwt(Kw::TList) + (seq!['<'] + ft(*a, seq!['>'] + k))
        },
        Ty::Option(a) => kwt(Kw::TOption) + (seq!['<'] + ft(*a, seq!['>'] + k)),
        Ty::Pair(a, b) => kwt(Kw::TPair) + (seq!['<'] + ft(*a, seq![',', ' '] + ft(*b, seq!['>'] + k))),
        Ty::Result(a, b) => kwt(Kw::TResult) + (seq!['<'] + ft(*a, seq![',', ' '] + ft(*b, seq!['>'] + k))),
    }
}

pub open spec fn fe(e: Sx, k: Seq<char>) -> Seq<char>
    decreases e, 0nat,
{
    match e {
        Sx::Int(n) => int_dec(n) + k,
        Sx::Chr(c) => seq!['\''] + (esc(c, '\'') + (seq!['\''] + k)),
        Sx::Str(w) => seq!['"'] + (escs(w, '"') + (seq!['"'] + k)),
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
        Sx::Inj(ok, t, u, x) => kwt(if ok { Kw::Ok } else { Kw::Err }) + (seq!['<'] + ft(
            t,
            seq![',', ' '] + ft(u, seq!['>', '('] + fe(*x, seq![')'] + k)),
        )),
        Sx::MatchR(m, x, a, y, b) => kwt(Kw::MatchResult) + (seq!['('] + fe(
            *m,
            seq![',', ' ', '|'] + (x + (seq!['|', ' '] + fe(
                *a,
                seq![',', ' ', '|'] + (y + (seq!['|', ' '] + fe(*b, seq![')'] + k))),
            ))),
        )),
        Sx::Fld(a, fs) => fe(*a, fdots(fs, k)),
        Sx::Rec(r, fs, b) => r + (seq![' ', '{'] + if fs.len() == 0 && b is None {
            seq!['}'] + k
        } else {
            seq![' '] + ffe(fs, 0, frtail(fs.len() > 0, b, k))
        }),
    }
}

/// `"." IDENT` の並び fs の後に k（字句）。
pub open spec fn fdots(fs: Seq<Seq<char>>, k: Seq<char>) -> Seq<char>
    decreases fs.len(),
{
    if fs.len() == 0 {
        k
    } else {
        seq!['.'] + fs[0] + fdots(fs.subrange(1, fs.len() as int), k)
    }
}

/// レコード式の閉じ部分（字句）：..base と ` }`。
pub open spec fn frtail(ne: bool, b: Option<Box<Sx>>, k: Seq<char>) -> Seq<char>
    decreases b, 0nat,
{
    match b {
        Some(x) => (if ne { seq![',', ' '] } else { seq![] }) + seq!['.', '.'] + fe(*x, seq![' ', '}'] + k),
        None => seq![' ', '}'] + k,
    }
}

/// レコード式の field の並び fs[i..]（字句）。最後の field の後ろに tail が続く。
pub open spec fn ffe(fs: Seq<(Seq<char>, Sx)>, i: nat, tail: Seq<char>) -> Seq<char>
    decreases fs, fs.len() - i,
{
    if i >= fs.len() {
        tail
    } else {
        fs[i as int].0 + (seq![':', ' '] + fe(
            fs[i as int].1,
            if i + 1 == fs.len() {
                tail
            } else {
                seq![',', ' '] + ffe(fs, i + 1, tail)
            },
        ))
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
        Sd::RecTy(r, fs, tc) => seq!['t', 'y', 'p', 'e', ' '] + (r + (seq![' ', '=', ' ', '{', ' '] + ffd(
            fs,
            0,
            (if tc { seq![',', ' ', '}'] } else { seq![' ', '}'] }) + seq!['\n'] + k,
        ))),
        Sd::Sum(r, vs) => seq!['t', 'y', 'p', 'e', ' '] + (r + (seq![' ', '=', ' '] + fvars(vs, 0, seq!['\n'] + k))),
    }
}

/// レコード型の宣言の field の並び fs[i..]（字句）。
pub open spec fn ffd(fs: Seq<(Seq<char>, Ty)>, i: nat, tail: Seq<char>) -> Seq<char>
    decreases fs, fs.len() - i,
{
    if i >= fs.len() {
        tail
    } else {
        fs[i as int].0 + (seq![':', ' '] + ft(
            fs[i as int].1,
            if i + 1 == fs.len() {
                tail
            } else {
                seq![',', ' '] + ffd(fs, i + 1, tail)
            },
        ))
    }
}

/// 型の並び `T, U, ...` の字句（tail の前まで）。
pub open spec fn ftys(ps: Seq<Ty>, i: nat, tail: Seq<char>) -> Seq<char>
    decreases ps.len() - i,
{
    if i >= ps.len() {
        tail
    } else if i + 1 == ps.len() {
        ft(ps[i as int], tail)
    } else {
        ft(ps[i as int], seq![',', ' '] + ftys(ps, i + 1, tail))
    }
}

/// 構築子の中身の字句：空なら rest だけ、そうでなければ `(` 型の並び `)` と rest。
pub open spec fn fpay(ps: Seq<Ty>, rest: Seq<char>) -> Seq<char> {
    if ps.len() == 0 {
        rest
    } else {
        seq!['('] + ftys(ps, 0, seq![')'] + rest)
    }
}

/// 直和型の構築子の並びの字句（` | ` で区切り、最後の後ろに tail）。
pub open spec fn fvars(vs: Seq<(Seq<char>, Seq<Ty>)>, i: nat, tail: Seq<char>) -> Seq<char>
    decreases vs.len() - i,
{
    if i >= vs.len() {
        tail
    } else {
        vs[i as int].0 + fpay(
            vs[i as int].1,
            if i + 1 == vs.len() {
                tail
            } else {
                seq![' ', '|', ' '] + fvars(vs, i + 1, tail)
            },
        )
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
        } else if c == '\'' {
            if s.len() >= 3 && s[1] != '\\' && s[1] != '\'' && (s[1] as u32) >= 0x20 && s[2] == '\'' {
                prepend(Tok::Chr(s[1]), lex(s.subrange(3, s.len() as int)))
            } else if s.len() >= 4 && s[1] == '\\' && unesc(s[2], '\'') is Some && s[3] == '\'' {
                prepend(Tok::Chr(unesc(s[2], '\'')->Some_0), lex(s.subrange(4, s.len() as int)))
            } else {
                None
            }
        } else if c == '"' {
            match slit(s, 1) {
                Some((w, j)) => if 1 <= j <= s.len() {
                    prepend(Tok::Str(w), lex(s.subrange(j as int, s.len() as int)))
                } else {
                    None
                },
                None => None,
            }
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
            Tok::Kw(Kw::TChar) => Some((Ty::Char, i + 1)),
            Tok::Kw(Kw::TString) => Some((Ty::List(Box::new(Ty::Char)), i + 1)),
            Tok::Kw(Kw::TList) => if sym(ts, i + 1, '<') {
                match pt(ts, i + 2, (d - 1) as nat) {
                    Some((a, j)) => if sym(ts, j, '>') && a != Ty::Char {
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
            Tok::Kw(Kw::TPair) | Tok::Kw(Kw::TResult) => if sym(ts, i + 1, '<') {
                match pt(ts, i + 2, (d - 1) as nat) {
                    Some((a, j)) => if sym(ts, j, ',') {
                        match pt(ts, j + 1, (d - 1) as nat) {
                            Some((b, m)) => if sym(ts, m, '>') {
                                Some((
                                    if ts[i as int] == Tok::Kw(Kw::TPair) {
                                        Ty::Pair(Box::new(a), Box::new(b))
                                    } else {
                                        Ty::Result(Box::new(a), Box::new(b))
                                    },
                                    m + 1,
                                ))
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

/// 後置（`.f`）を除く基本の式。d は式の入れ子の深さ上限、td は型の深さ上限。
pub open spec fn pp(ts: Seq<Tok>, i: nat, d: nat, td: nat) -> Option<(Sx, nat)>
    decreases d, 0nat, 0nat,
{
    if d == 0 || i >= ts.len() {
        None
    } else {
        let d1 = (d - 1) as nat;
        match ts[i as int] {
            Tok::Int(n) => Some((Sx::Int(n), i + 1)),
            Tok::Chr(c) => if lit_ok(c) {
                Some((Sx::Chr(c), i + 1))
            } else {
                None
            },
            Tok::Str(w) => if str_ok(w) {
                Some((Sx::Str(w), i + 1))
            } else {
                None
            },
            Tok::Id(x) => if !ident_ok(x) {
                None
            } else if sym(ts, i + 1, '(') {
                match pargs(ts, i + 2, d1, td) {
                    Some((es, j)) => Some((Sx::Call(x, es), j)),
                    None => None,
                }
            } else if sym(ts, i + 1, '{') && rec_head(ts, i + 2) {
                match prec(ts, i + 2, d1, td) {
                    Some((fs, b, j)) => Some((Sx::Rec(x, fs, b), j)),
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
                } else if k == Kw::Ok || k == Kw::Err {
                    if sym(ts, i + 1, '<') {
                        match pt(ts, i + 2, td) {
                            Some((t, j)) => if sym(ts, j, ',') {
                                match pt(ts, j + 1, td) {
                                    Some((u, m)) => if sym(ts, m, '>') && sym(ts, m + 1, '(') {
                                        match pe(ts, m + 2, d1, td) {
                                            Some((a, q)) => if sym(ts, q, ')') {
                                                Some((Sx::Inj(k == Kw::Ok, t, u, Box::new(a)), q + 1))
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
                } else if k == Kw::MatchResult {
                    if sym(ts, i + 1, '(') {
                        match pe(ts, i + 2, d1, td) {
                            Some((m, j)) => if sym(ts, j, ',') && sym(ts, j + 1, '|') && sym(ts, j + 3, '|') {
                                match bdt(ts, j + 2) {
                                    Some(x) => match pe(ts, j + 4, d1, td) {
                                        Some((a, q)) => if sym(ts, q, ',') && sym(ts, q + 1, '|') && sym(ts, q + 3, '|') {
                                            match bdt(ts, q + 2) {
                                                Some(y) => match pe(ts, q + 4, d1, td) {
                                                    Some((b, u)) => if sym(ts, u, ')') {
                                                        Some((Sx::MatchR(Box::new(m), x, Box::new(a), y, Box::new(b)), u + 1))
                                                    } else {
                                                        None
                                                    },
                                                    None => None,
                                                },
                                                None => None,
                                            }
                                        } else {
                                            None
                                        },
                                        None => None,
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

/// 式。基本の式の後に、`.IDENT` の並びが続けば受ける（左結合）。
pub open spec fn pe(ts: Seq<Tok>, i: nat, d: nat, td: nat) -> Option<(Sx, nat)>
    decreases d, 1nat, 0nat,
{
    match pp(ts, i, d, td) {
        Some((e, j)) => if recv_ok(e) && j + 1 < ts.len() && sym(ts, j, '.') && idt(ts, j + 1) is Some {
            let r = pfs(ts, j);
            Some((Sx::Fld(Box::new(e), r.0), r.1))
        } else {
            Some((e, j))
        },
        None => None,
    }
}

/// `"." IDENT` の並びを読む（位置 j から）。並びと、並びの後の位置。並びは最大に読む。
pub open spec fn pfs(ts: Seq<Tok>, j: nat) -> (Seq<Seq<char>>, nat)
    decreases ts.len() - j,
{
    if j + 1 < ts.len() && sym(ts, j, '.') && idt(ts, j + 1) is Some {
        let r = pfs(ts, j + 2);
        (seq![idt(ts, j + 1)->Some_0] + r.0, r.1)
    } else {
        (Seq::empty(), j)
    }
}

/// `R {` の後ろがレコード式の本体の形（`}`、`IDENT :`、`..`）なら、R は記録式の名前。
/// それ以外（`match x { ... }` の被験式など）は変数と読む。
pub open spec fn rec_head(ts: Seq<Tok>, i: nat) -> bool {
    sym(ts, i, '}') || (idt(ts, i) is Some && sym(ts, i + 1, ':')) || (sym(ts, i, '.') && sym(ts, i + 1, '.'))
}

/// レコード式の本体（`{` の後）。フィールドの並び、省略できる base、閉じ括弧の後の位置。
pub open spec fn prec(ts: Seq<Tok>, i: nat, d: nat, td: nat) -> Option<(Seq<(Seq<char>, Sx)>, Option<Box<Sx>>, nat)>
    decreases d, 3nat, ts.len() - i,
{
    if sym(ts, i, '}') {
        Some((Seq::empty(), None, i + 1))
    } else {
        prest(ts, i, d, td)
    }
}

/// レコード式の要素一つ（フィールド、または最後の `..base`）と、閉じ括弧までの残り。
pub open spec fn prest(ts: Seq<Tok>, i: nat, d: nat, td: nat) -> Option<(Seq<(Seq<char>, Sx)>, Option<Box<Sx>>, nat)>
    decreases d, 2nat, ts.len() - i,
{
    if sym(ts, i, '.') && sym(ts, i + 1, '.') {
        match pe(ts, i + 2, d, td) {
            Some((b, j)) => if sym(ts, j, '}') {
                Some((Seq::empty(), Some(Box::new(b)), j + 1))
            } else {
                None
            },
            None => None,
        }
    } else {
        match idt(ts, i) {
            Some(f) => if sym(ts, i + 1, ':') {
                match pe(ts, i + 2, d, td) {
                    Some((v, j)) => if sym(ts, j, '}') {
                        Some((seq![(f, v)], None, j + 1))
                    } else if sym(ts, j, ',') && i < j {
                        match prest(ts, j + 1, d, td) {
                            Some((fs, b, m)) => Some((seq![(f, v)] + fs, b, m)),
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
}

/// `[ arguments ] ")"`
pub open spec fn pargs(ts: Seq<Tok>, i: nat, d: nat, td: nat) -> Option<(Seq<Sx>, nat)>
    decreases d, 3nat, 0nat,
{
    if sym(ts, i, ')') {
        Some((Seq::empty(), i + 1))
    } else {
        pargs1(ts, i, d, td)
    }
}

/// `arguments ")"`
pub open spec fn pargs1(ts: Seq<Tok>, i: nat, d: nat, td: nat) -> Option<(Seq<Sx>, nat)>
    decreases d, 2nat, ts.len() - i,
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
    } else if i < ts.len() && ts[i as int] == Tok::Id(tyw()) {
        match idt(ts, i + 1) {
            Some(r) => if sym(ts, i + 2, '=') && sym(ts, i + 3, '{') {
                match pfds(ts, i + 4, td) {
                    Some((fs, tc, j)) => Some((Sd::RecTy(r, fs, tc), j)),
                    None => None,
                }
            } else if sym(ts, i + 2, '=') {
                match pvars(ts, i + 3, td) {
                    Some((vs, j)) => Some((Sd::Sum(r, vs), j)),
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
}

/// レコード型の宣言の field の並び（閉じ括弧まで）。一つ以上で、最後の後ろに `,` を一つ許す。
pub open spec fn pfds(ts: Seq<Tok>, i: nat, td: nat) -> Option<(Seq<(Seq<char>, Ty)>, bool, nat)>
    decreases ts.len() - i,
{
    match idt(ts, i) {
        Some(f) => if sym(ts, i + 1, ':') {
            match pt(ts, i + 2, td) {
                Some((t, j)) => if sym(ts, j, '}') {
                    Some((seq![(f, t)], false, j + 1))
                } else if sym(ts, j, ',') && i < j {
                    if sym(ts, j + 1, '}') {
                        Some((seq![(f, t)], true, j + 2))
                    } else {
                        match pfds(ts, j + 1, td) {
                            Some((fs, tc, m)) => Some((seq![(f, t)] + fs, tc, m)),
                            None => None,
                        }
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

/// 型の並び（一つ以上、カンマ区切り。閉じ括弧は読まない）。
pub open spec fn ptys(ts: Seq<Tok>, i: nat, td: nat) -> Option<(Seq<Ty>, nat)>
    decreases ts.len() - i,
{
    match pt(ts, i, td) {
        Some((t, j)) => if sym(ts, j, ',') && i < j {
            match ptys(ts, j + 1, td) {
                Some((ps, m)) => Some((seq![t] + ps, m)),
                None => None,
            }
        } else {
            Some((seq![t], j))
        },
        None => None,
    }
}

/// 構築子 `CTOR` か `CTOR "(" type ("," type)* ")"`（位置 i から）。名前、中身の型の並び、後ろの位置。
pub open spec fn pvar(ts: Seq<Tok>, i: nat, td: nat) -> Option<(Seq<char>, Seq<Ty>, nat)> {
    match cidt(ts, i) {
        Some(c) => if sym(ts, i + 1, '(') {
            match ptys(ts, i + 2, td) {
                Some((ps, j)) => if sym(ts, j, ')') {
                    Some((c, ps, j + 1))
                } else {
                    None
                },
                None => None,
            }
        } else {
            Some((c, Seq::empty(), i + 1))
        },
        None => None,
    }
}

/// 直和型の構築子の並び（`|` で区切る。位置 i から、一つ以上）。
pub open spec fn pvars(ts: Seq<Tok>, i: nat, td: nat) -> Option<(Seq<(Seq<char>, Seq<Ty>)>, nat)>
    decreases ts.len() - i,
{
    match pvar(ts, i, td) {
        Some((c, ps, j)) => if sym(ts, j, '|') && i < j {
            match pvars(ts, j + 1, td) {
                Some((vs, m)) => Some((seq![(c, ps)] + vs, m)),
                None => None,
            }
        } else {
            Some((seq![(c, ps)], j))
        },
        None => None,
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
        Ty::List(a) => *a == Ty::Char || bt(*a, (d - 1) as nat),
        Ty::Option(a) => bt(*a, (d - 1) as nat),
        Ty::Pair(a, b) | Ty::Result(a, b) => bt(*a, (d - 1) as nat) && bt(*b, (d - 1) as nat),
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
            Sx::Chr(c) => lit_ok(c),
            Sx::Str(w) => str_ok(w),
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
            Sx::Inj(_, t, u, x) => bt(t, td) && bt(u, td) && bx(*x, d1, td),
            Sx::MatchR(m, x, a, y, b) => name_ok(x) && name_ok(y) && bx(*m, d1, td) && bx(*a, d1, td) && bx(*b, d1, td),
            Sx::Fld(a, fs) => recv_ok(*a) && fs.len() > 0 && nms(fs) && bx(*a, d, td),
            Sx::Rec(r, fs, b) => ident_ok(r) && bfs(fs, 0, d1, td) && bopt(b, d1, td),
            _ => true,
        }
    }
}

/// レコード式の省略できる base は、あれば深さ内。
pub open spec fn bopt(b: Option<Box<Sx>>, d: nat, td: nat) -> bool
    decreases b, 0nat,
{
    match b {
        Some(x) => bx(*x, d, td),
        None => true,
    }
}

pub open spec fn bxs(es: Seq<Sx>, i: nat, d: nat, td: nat) -> bool
    decreases es, es.len() - i,
{
    i >= es.len() || (bx(es[i as int], d, td) && bxs(es, i + 1, d, td))
}

/// `.IDENT` の並びの名前は、すべて IDENT。
pub open spec fn nms(fs: Seq<Seq<char>>) -> bool
    decreases fs.len(),
{
    fs.len() == 0 || (ident_ok(fs[0]) && nms(fs.subrange(1, fs.len() as int)))
}

/// レコード式の field：名前は IDENT で、値は深さ内。
pub open spec fn bfs(fs: Seq<(Seq<char>, Sx)>, i: nat, d: nat, td: nat) -> bool
    decreases fs, fs.len() - i,
{
    i >= fs.len() || (ident_ok(fs[i as int].0) && bx(fs[i as int].1, d, td) && bfs(fs, i + 1, d, td))
}

/// レコード型の宣言の field：名前は IDENT で、型は深さ内。
pub open spec fn bfds(fs: Seq<(Seq<char>, Ty)>, i: nat, td: nat) -> bool
    decreases fs.len() - i,
{
    i >= fs.len() || (ident_ok(fs[i as int].0) && bt(fs[i as int].1, td) && bfds(fs, i + 1, td))
}

pub open spec fn bps(ps: Seq<(Seq<char>, Ty)>, i: nat, td: nat) -> bool
    decreases ps.len() - i,
{
    i >= ps.len() || (name_ok(ps[i as int].0) && bt(ps[i as int].1, td) && bps(ps, i + 1, td))
}

/// 型の並びの深さ（bt）。
pub open spec fn bts(ps: Seq<Ty>, i: nat, td: nat) -> bool
    decreases ps.len() - i,
{
    i >= ps.len() || (bt(ps[i as int], td) && bts(ps, i + 1, td))
}

/// 直和型の構築子：名前は大文字で始まる IDENT、中身の型は深さ内。
pub open spec fn bvars(vs: Seq<(Seq<char>, Seq<Ty>)>, i: nat, td: nat) -> bool
    decreases vs.len() - i,
{
    i >= vs.len() || (cname_ok(vs[i as int].0) && bts(vs[i as int].1, 0, td) && bvars(vs, i + 1, td))
}

pub open spec fn bd(x: Sd, d: nat, td: nat) -> bool {
    match x {
        Sd::Fn(f, ps, r, b) => ident_ok(f) && bps(ps, 0, td) && bt(r, td) && bx(b, d, td),
        Sd::Entry(x) => ident_ok(x),
        Sd::RecTy(r, fs, tc) => ident_ok(r) && fs.len() > 0 && bfds(fs, 0, td),
        Sd::Sum(r, vs) => ident_ok(r) && vs.len() > 0 && bvars(vs, 0, td),
    }
}

pub open spec fn bds(p: Seq<Sd>, i: nat, d: nat, td: nat) -> bool
    decreases p.len() - i,
{
    i >= p.len() || (bd(p[i as int], d, td) && bds(p, i + 1, d, td))
}

} // verus!
