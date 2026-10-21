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
    /// v1.5：hof の 6 語（文脈キーワード）
    Map,
    Filter,
    Any,
    All,
    Find,
    SortBy,
    /// v1.6：loop（文脈キーワード。式の位置で直後が `(` か `<` のとき語として読む。loop は型引数を持たないので `<` は読めず、それ以外は変数）
    Loop,
    /// v1.9：dict<K, V>()（文脈キーワード。式の位置で直後が `<` のとき語として読む。型引数を持つので `(` だけの形はない）
    Dict,
    /// v1.9：dict の九つの組込み（文脈キーワード。式の位置で直後が `(` のとき語として読む。型引数を持たないので `<` は読めず、それ以外は変数）
    DictGet,
    DictPut,
    DictRemove,
    DictHas,
    DictSize,
    DictKeys,
    DictValues,
    DictEntries,
    DictFrom,
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
        Kw::Map => seq!['m', 'a', 'p'],
        Kw::Filter => seq!['f', 'i', 'l', 't', 'e', 'r'],
        Kw::Any => seq!['a', 'n', 'y'],
        Kw::All => seq!['a', 'l', 'l'],
        Kw::Find => seq!['f', 'i', 'n', 'd'],
        Kw::SortBy => seq!['s', 'o', 'r', 't', '_', 'b', 'y'],
        Kw::Loop => seq!['l', 'o', 'o', 'p'],
        Kw::Dict => seq!['d', 'i', 'c', 't'],
        Kw::DictGet => seq!['d', 'i', 'c', 't', '_', 'g', 'e', 't'],
        Kw::DictPut => seq!['d', 'i', 'c', 't', '_', 'p', 'u', 't'],
        Kw::DictRemove => seq!['d', 'i', 'c', 't', '_', 'r', 'e', 'm', 'o', 'v', 'e'],
        Kw::DictHas => seq!['d', 'i', 'c', 't', '_', 'h', 'a', 's'],
        Kw::DictSize => seq!['d', 'i', 'c', 't', '_', 's', 'i', 'z', 'e'],
        Kw::DictKeys => seq!['d', 'i', 'c', 't', '_', 'k', 'e', 'y', 's'],
        Kw::DictValues => seq!['d', 'i', 'c', 't', '_', 'v', 'a', 'l', 'u', 'e', 's'],
        Kw::DictEntries => seq!['d', 'i', 'c', 't', '_', 'e', 'n', 't', 'r', 'i', 'e', 's'],
        Kw::DictFrom => seq!['d', 'i', 'c', 't', '_', 'f', 'r', 'o', 'm'],
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
        } else if c3(s, 'm', 'a', 'p') {
            Some(Kw::Map)
        } else if c3(s, 'a', 'n', 'y') {
            Some(Kw::Any)
        } else if c3(s, 'a', 'l', 'l') {
            Some(Kw::All)
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
        } else if c4(s, 'f', 'i', 'n', 'd') {
            Some(Kw::Find)
        } else if c4(s, 'l', 'o', 'o', 'p') {
            Some(Kw::Loop)
        } else if c4(s, 'd', 'i', 'c', 't') {
            Some(Kw::Dict)
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
        } else if c6(s, 'f', 'i', 'l', 't', 'e', 'r') {
            Some(Kw::Filter)
        } else {
            None
        }
    } else if s.len() == 7 {
        if c6(s, 'r', 'e', 'v', 'e', 'r', 's') && s[6] == 'e' {
            Some(Kw::Reverse)
        } else if c6(s, 's', 'o', 'r', 't', '_', 'b') && s[6] == 'y' {
            Some(Kw::SortBy)
        } else {
            None
        }
    } else if s.len() == 8 {
        if c6(s, 'c', 'o', 'n', 't', 'a', 'i') && s[6] == 'n' && s[7] == 's' {
            Some(Kw::Contains)
        } else if c6(s, 'd', 'i', 'c', 't', '_', 'g') && s[6] == 'e' && s[7] == 't' {
            Some(Kw::DictGet)
        } else if c6(s, 'd', 'i', 'c', 't', '_', 'p') && s[6] == 'u' && s[7] == 't' {
            Some(Kw::DictPut)
        } else if c6(s, 'd', 'i', 'c', 't', '_', 'h') && s[6] == 'a' && s[7] == 's' {
            Some(Kw::DictHas)
        } else {
            None
        }
    } else if s.len() == 9 {
        if c6(s, 't', 'o', '_', 's', 't', 'r') && s[6] == 'i' && s[7] == 'n' && s[8] == 'g' {
            Some(Kw::ToString)
        } else if c6(s, 'p', 'a', 'r', 's', 'e', '_') && s[6] == 'i' && s[7] == 'n' && s[8] == 't' {
            Some(Kw::ParseInt)
        } else if c6(s, 'd', 'i', 'c', 't', '_', 's') && s[6] == 'i' && s[7] == 'z' && s[8] == 'e' {
            Some(Kw::DictSize)
        } else if c6(s, 'd', 'i', 'c', 't', '_', 'k') && s[6] == 'e' && s[7] == 'y' && s[8] == 's' {
            Some(Kw::DictKeys)
        } else if c6(s, 'd', 'i', 'c', 't', '_', 'f') && s[6] == 'r' && s[7] == 'o' && s[8] == 'm' {
            Some(Kw::DictFrom)
        } else {
            None
        }
    } else if s.len() == 11 {
        if c6(s, 'd', 'i', 'c', 't', '_', 'r') && s[6] == 'e' && s[7] == 'm' && s[8] == 'o' && s[9] == 'v'
            && s[10] == 'e' {
            Some(Kw::DictRemove)
        } else if c6(s, 'd', 'i', 'c', 't', '_', 'v') && s[6] == 'a' && s[7] == 'l' && s[8] == 'u' && s[9] == 'e'
            && s[10] == 's' {
            Some(Kw::DictValues)
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
        } else if c6(s, 'd', 'i', 'c', 't', '_', 'e') && s[6] == 'n' && s[7] == 't' && s[8] == 'r' && s[9] == 'i'
            && s[10] == 'e' && s[11] == 's' {
            Some(Kw::DictEntries)
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

/// v1.5：関数を渡す組込み。`hof(xs, |x| e)` の形で、語の綴りは文脈キーワード（§4.2）。
#[derive(Clone, Copy, PartialEq, Eq)]
pub enum Hf {
    Map,
    Filter,
    Any,
    All,
    Find,
    SortBy,
}

/// hof の語（キーワードの token）。
pub open spec fn hkw(h: Hf) -> Kw {
    match h {
        Hf::Map => Kw::Map,
        Hf::Filter => Kw::Filter,
        Hf::Any => Kw::Any,
        Hf::All => Kw::All,
        Hf::Find => Kw::Find,
        Hf::SortBy => Kw::SortBy,
    }
}

/// 語が hof の語なら、その hof。
pub open spec fn kw_hf(k: Kw) -> Option<Hf> {
    match k {
        Kw::Map => Some(Hf::Map),
        Kw::Filter => Some(Hf::Filter),
        Kw::Any => Some(Hf::Any),
        Kw::All => Some(Hf::All),
        Kw::Find => Some(Hf::Find),
        Kw::SortBy => Some(Hf::SortBy),
        _ => None,
    }
}

/// v1.9：dict の九つの組込み（文脈キーワード）。語の直後が `(` のとき、型引数を持たない呼出しとして読む。
#[derive(Clone, Copy, PartialEq, Eq)]
pub enum Dop {
    Get,
    Put,
    Remove,
    Has,
    Size,
    Keys,
    Values,
    Entries,
    From,
}

/// dict の組込みの語（キーワードの token）。
pub open spec fn dkw(d: Dop) -> Kw {
    match d {
        Dop::Get => Kw::DictGet,
        Dop::Put => Kw::DictPut,
        Dop::Remove => Kw::DictRemove,
        Dop::Has => Kw::DictHas,
        Dop::Size => Kw::DictSize,
        Dop::Keys => Kw::DictKeys,
        Dop::Values => Kw::DictValues,
        Dop::Entries => Kw::DictEntries,
        Dop::From => Kw::DictFrom,
    }
}

/// 語が dict の組込みなら、その組込み。
pub open spec fn kw_dop(k: Kw) -> Option<Dop> {
    match k {
        Kw::DictGet => Some(Dop::Get),
        Kw::DictPut => Some(Dop::Put),
        Kw::DictRemove => Some(Dop::Remove),
        Kw::DictHas => Some(Dop::Has),
        Kw::DictSize => Some(Dop::Size),
        Kw::DictKeys => Some(Dop::Keys),
        Kw::DictValues => Some(Dop::Values),
        Kw::DictEntries => Some(Dop::Entries),
        Kw::DictFrom => Some(Dop::From),
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

/// 型の名前の判定（pt の IDENT 枝）。閉じた関数にして、pt の展開ごとに kw_of の表を展開しない。
pub closed spec fn tyname_ok(x: Seq<char>) -> bool {
    ident_ok(x)
}

/// tyname_ok は ident_ok と同じ（必要な所で開く）。
pub proof fn tyname_ok_eq(x: Seq<char>)
    ensures
        tyname_ok(x) == ident_ok(x),
{
    reveal(tyname_ok);
}

/// v1.1 の文脈キーワード（差分仕様 §2a）：組み込み関数と値の構築子の名前。変数・引数・束縛の名前に使える。
/// v1.5 の hof の語と v1.6 の loop、v1.9 の dict の語も、同じく変数・引数・束縛の名前に使える。
pub open spec fn soft(k: Kw) -> bool {
    kw_b(k) is Some || k == Kw::List || k == Kw::Some || k == Kw::None || k == Kw::Pair || k == Kw::Entry || k == Kw::Ok || k == Kw::Err
        || kw_hf(k) is Some || k == Kw::Loop || kw_dop(k) is Some || k == Kw::Dict
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

/// 表面の型（§4.1）。核の Ty の構成子に、宣言された型の名前 Named と v1.9 の Dict を加えたもの。
/// 名前は字句のまま持つ。名前を表に引くのは resolve.rs の仕事で、ここでは読むだけ。
pub enum SType {
    Int,
    Bool,
    Unit,
    Char,
    List(Box<SType>),
    Option(Box<SType>),
    Pair(Box<SType>, Box<SType>),
    Result(Box<SType>, Box<SType>),
    /// 宣言された型の名前（IDENT）。Dict も名前として読める（引数のない形だけ）。
    Named(Seq<char>),
    /// v1.9：Dict<K, V>（`Dict` の後ろの `<` で読む）
    Dict(Box<SType>, Box<SType>),
}

/// v1.9 の dict 型の綴り `Dict`。予約語ではない（式の語は小文字の `dict`）。
pub open spec fn dict_name() -> Seq<char> {
    seq!['D', 'i', 'c', 't']
}

pub enum Sx {
    Int(int),
    Chr(char),
    Str(Seq<char>),
    Bool(bool),
    Unit,
    Var(Seq<char>),
    List(SType, Seq<Sx>),
    Some(Box<Sx>),
    None(SType),
    Pair(Box<Sx>, Box<Sx>),
    Builtin(Builtin, Seq<Sx>),
    Call(Seq<char>, Seq<Sx>),
    Let(Seq<char>, Box<Sx>, Box<Sx>),
    If(Box<Sx>, Box<Sx>, Box<Sx>),
    Fold(Box<Sx>, Box<Sx>, Seq<char>, Seq<char>, Box<Sx>),
    /// match_option(m, n, |x| s)
    Match(Box<Sx>, Box<Sx>, Seq<char>, Box<Sx>),
    /// v1.4：ok<T, E>(x)（true）、err<T, E>(x)（false）
    Inj(bool, SType, SType, Box<Sx>),
    /// v1.4：match_result(m, |x| a, |y| b)
    MatchR(Box<Sx>, Seq<char>, Box<Sx>, Seq<char>, Box<Sx>),
    /// v1.1：e.f1.f2…（後置、左結合。受ける式は recv_ok、field 名は IDENT か文脈キーワードで、列は空でない）
    Fld(Box<Sx>, Seq<Seq<char>>),
    /// v1.1：R { f: e, ..b }（フィールドの並びと、省略できる base）
    Rec(Seq<char>, Seq<(Seq<char>, Sx)>, Option<Box<Sx>>),
    /// v1.4：match e { P => a, ... }（枝の並びは空でない）
    SumMatch(Box<Sx>, Seq<(Spat, Sx)>),
    /// v1.5：hof(xs, |x| e)（hof の語、被験の列、binder、本体）。binder は IDENT か文脈キーワード。
    Hof(Hf, Box<Sx>, Seq<char>, Box<Sx>),
    /// v1.6：loop(init, max, |s| e)（初期値、上限、binder、本体）。binder は IDENT か文脈キーワード。
    Loop(Box<Sx>, Box<Sx>, Seq<char>, Box<Sx>),
    /// v1.9：dict<K, V>()（空の辞書。型の引数は表面の型）
    DictNew(SType, SType),
    /// v1.9：dict の組込み呼出し（組込みの語と、引数の列）
    DictOp(Dop, Seq<Sx>),
}

/// v1.4：match の枝の左辺（パターン）。束縛の名前は bind（IDENT か文脈キーワード。`_` も名前として読む）。
pub enum Spat {
    /// CTOR か CTOR "(" bind ("," bind)* ")"
    Ctor(Seq<char>, Seq<Seq<char>>),
    /// ok "(" bind ")"
    Ok(Seq<char>),
    /// err "(" bind ")"
    Err(Seq<char>),
    /// some "(" bind ")"
    Some(Seq<char>),
    /// none
    None,
    /// _
    Wild,
}

pub enum Sd {
    Fn(Seq<char>, Seq<(Seq<char>, SType)>, SType, Sx),
    Entry(Seq<char>),
    /// v1.1：type R = { f: T, ... }（末尾の `,` の有無を持つ。整形がトークン列を変えないため）
    RecTy(Seq<char>, Seq<(Seq<char>, SType)>, bool),
    /// v1.4：type S = V1 | V2(T, U)（構築子の名前と、中身の型の並び）
    Sum(Seq<char>, Seq<(Seq<char>, Seq<SType>)>),
}

/// 宣言の先頭で読む文脈語 `type` の綴り（予約語ではない）。
pub open spec fn tyw() -> Seq<char> {
    seq!['t', 'y', 'p', 'e']
}

/// 式の先頭で読む文脈語 `match` の綴り（予約語ではない）。
pub open spec fn mword() -> Seq<char> {
    seq!['m', 'a', 't', 'c', 'h']
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

pub open spec fn tt(t: SType, k: Seq<Tok>) -> Seq<Tok>
    decreases t,
{
    match t {
        SType::Int => seq![Tok::Kw(Kw::TInt)] + k,
        SType::Bool => seq![Tok::Kw(Kw::TBool)] + k,
        SType::Unit => seq![Tok::Kw(Kw::TUnit)] + k,
        SType::Char => seq![Tok::Kw(Kw::TChar)] + k,
        SType::List(a) => if *a == SType::Char {
            seq![Tok::Kw(Kw::TString)] + k
        } else {
            seq![Tok::Kw(Kw::TList), Tok::Sym('<')] + tt(*a, seq![Tok::Sym('>')] + k)
        },
        SType::Option(a) => seq![Tok::Kw(Kw::TOption), Tok::Sym('<')] + tt(*a, seq![Tok::Sym('>')] + k),
        SType::Pair(a, b) => seq![Tok::Kw(Kw::TPair), Tok::Sym('<')] + tt(
            *a,
            seq![Tok::Sym(',')] + tt(*b, seq![Tok::Sym('>')] + k),
        ),
        SType::Result(a, b) => seq![Tok::Kw(Kw::TResult), Tok::Sym('<')] + tt(
            *a,
            seq![Tok::Sym(',')] + tt(*b, seq![Tok::Sym('>')] + k),
        ),
        SType::Named(x) => seq![Tok::Id(x)] + k,
        SType::Dict(a, b) => seq![Tok::Id(dict_name()), Tok::Sym('<')] + tt(
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
        Sx::SumMatch(m, arms) => seq![word_tok(mword())] + te(*m, seq![Tok::Sym('{')] + tarms(arms, 0, seq![Tok::Sym('}')] + k)),
        Sx::Hof(h, l, x, b) => seq![Tok::Kw(hkw(h)), Tok::Sym('(')] + te(
            *l,
            seq![Tok::Sym(','), Tok::Sym('|'), word_tok(x), Tok::Sym('|')] + te(*b, seq![Tok::Sym(')')] + k),
        ),
        Sx::Loop(i, m, x, b) => seq![Tok::Kw(Kw::Loop), Tok::Sym('(')] + te(
            *i,
            seq![Tok::Sym(',')] + te(
                *m,
                seq![Tok::Sym(','), Tok::Sym('|'), word_tok(x), Tok::Sym('|')] + te(*b, seq![Tok::Sym(')')] + k),
            ),
        ),
        Sx::DictNew(a, b) => seq![Tok::Kw(Kw::Dict), Tok::Sym('<')] + tt(
            a,
            seq![Tok::Sym(',')] + tt(b, seq![Tok::Sym('>'), Tok::Sym('('), Tok::Sym(')')] + k),
        ),
        Sx::DictOp(d, es) => seq![Tok::Kw(dkw(d)), Tok::Sym('(')] + targs(es, 0, k),
    }
}

/// 枝の左辺（パターン）の字句（後ろに k）。
pub open spec fn tpat(p: Spat, k: Seq<Tok>) -> Seq<Tok> {
    match p {
        Spat::Ctor(c, bs) => if bs.len() == 0 {
            seq![word_tok(c)] + k
        } else {
            seq![word_tok(c), Tok::Sym('(')] + tbinds(bs, 0, seq![Tok::Sym(')')] + k)
        },
        Spat::Ok(x) => seq![Tok::Kw(Kw::Ok), Tok::Sym('('), word_tok(x), Tok::Sym(')')] + k,
        Spat::Err(x) => seq![Tok::Kw(Kw::Err), Tok::Sym('('), word_tok(x), Tok::Sym(')')] + k,
        Spat::Some(x) => seq![Tok::Kw(Kw::Some), Tok::Sym('('), word_tok(x), Tok::Sym(')')] + k,
        Spat::None => seq![Tok::Kw(Kw::None)] + k,
        Spat::Wild => seq![word_tok(seq!['_'])] + k,
    }
}

/// 構築子のパターンの束縛の並び（字句。後ろに k）。
pub open spec fn tbinds(bs: Seq<Seq<char>>, i: nat, k: Seq<Tok>) -> Seq<Tok>
    decreases bs.len() - i,
{
    if i >= bs.len() {
        k
    } else if i + 1 == bs.len() {
        seq![word_tok(bs[i as int])] + k
    } else {
        seq![word_tok(bs[i as int]), Tok::Sym(',')] + tbinds(bs, i + 1, k)
    }
}

/// match の枝の並び（字句）：枝は「パターン `=` `>` 本体」、枝の間は `,`、最後の後ろに k。
pub open spec fn tarms(arms: Seq<(Spat, Sx)>, i: nat, k: Seq<Tok>) -> Seq<Tok>
    decreases arms, arms.len() - i,
{
    if i >= arms.len() {
        k
    } else {
        tpat(arms[i as int].0, seq![Tok::Sym('='), Tok::Sym('>')] + te(
            arms[i as int].1,
            if i + 1 == arms.len() {
                k
            } else {
                seq![Tok::Sym(',')] + tarms(arms, i + 1, k)
            },
        ))
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
pub open spec fn tfd(fs: Seq<(Seq<char>, SType)>, i: nat, tc: bool, tail: Seq<Tok>) -> Seq<Tok>
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
pub open spec fn tps(ps: Seq<(Seq<char>, SType)>, i: nat, k: Seq<Tok>) -> Seq<Tok>
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
pub open spec fn tts(ps: Seq<SType>, i: nat, k: Seq<Tok>) -> Seq<Tok>
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
pub open spec fn tpay(ps: Seq<SType>, k: Seq<Tok>) -> Seq<Tok> {
    if ps.len() == 0 {
        k
    } else {
        seq![Tok::Sym('(')] + tts(ps, 0, seq![Tok::Sym(')')] + k)
    }
}

/// 直和型の構築子の並び（`|` で区切り、最後の後ろに k）。
pub open spec fn tvars(vs: Seq<(Seq<char>, Seq<SType>)>, i: nat, k: Seq<Tok>) -> Seq<Tok>
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

pub open spec fn ft(t: SType, k: Seq<char>) -> Seq<char>
    decreases t,
{
    match t {
        SType::Int => kwt(Kw::TInt) + k,
        SType::Bool => kwt(Kw::TBool) + k,
        SType::Unit => kwt(Kw::TUnit) + k,
        SType::Char => kwt(Kw::TChar) + k,
        SType::List(a) => if *a == SType::Char {
            kwt(Kw::TString) + k
        } else {
            kwt(Kw::TList) + (seq!['<'] + ft(*a, seq!['>'] + k))
        },
        SType::Option(a) => kwt(Kw::TOption) + (seq!['<'] + ft(*a, seq!['>'] + k)),
        SType::Pair(a, b) => kwt(Kw::TPair) + (seq!['<'] + ft(*a, seq![',', ' '] + ft(*b, seq!['>'] + k))),
        SType::Result(a, b) => kwt(Kw::TResult) + (seq!['<'] + ft(*a, seq![',', ' '] + ft(*b, seq!['>'] + k))),
        SType::Named(x) => x + k,
        SType::Dict(a, b) => dict_name() + (seq!['<'] + ft(*a, seq![',', ' '] + ft(*b, seq!['>'] + k))),
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
        Sx::SumMatch(m, arms) => mword() + (seq![' '] + fe(*m, seq![' ', '{', ' '] + farms(arms, 0, seq![' ', '}'] + k))),
        Sx::Hof(h, l, x, b) => kwt(hkw(h)) + (seq!['('] + fe(
            *l,
            seq![',', ' ', '|'] + (x + (seq!['|', ' '] + fe(*b, seq![')'] + k))),
        )),
        Sx::Loop(i, m, x, b) => kwt(Kw::Loop) + (seq!['('] + fe(
            *i,
            seq![',', ' '] + fe(
                *m,
                seq![',', ' ', '|'] + (x + (seq!['|', ' '] + fe(*b, seq![')'] + k))),
            ),
        )),
        Sx::DictNew(a, b) => kwt(Kw::Dict) + (seq!['<'] + ft(
            a,
            seq![',', ' '] + ft(b, seq!['>', '(', ')'] + k),
        )),
        Sx::DictOp(d, es) => kwt(dkw(d)) + (seq!['('] + fargs(es, 0, k)),
    }
}

/// 枝の左辺（パターン）の字句（後ろに k）。
pub open spec fn fpat(p: Spat, k: Seq<char>) -> Seq<char> {
    match p {
        Spat::Ctor(c, bs) => if bs.len() == 0 {
            c + k
        } else {
            c + (seq!['('] + fbinds(bs, 0, seq![')'] + k))
        },
        Spat::Ok(x) => kwt(Kw::Ok) + (seq!['('] + (x + (seq![')'] + k))),
        Spat::Err(x) => kwt(Kw::Err) + (seq!['('] + (x + (seq![')'] + k))),
        Spat::Some(x) => kwt(Kw::Some) + (seq!['('] + (x + (seq![')'] + k))),
        Spat::None => kwt(Kw::None) + k,
        Spat::Wild => seq!['_'] + k,
    }
}

/// 構築子のパターンの束縛の並び（字句。後ろに k）。
pub open spec fn fbinds(bs: Seq<Seq<char>>, i: nat, k: Seq<char>) -> Seq<char>
    decreases bs.len() - i,
{
    if i >= bs.len() {
        k
    } else if i + 1 == bs.len() {
        bs[i as int] + k
    } else {
        bs[i as int] + (seq![',', ' '] + fbinds(bs, i + 1, k))
    }
}

/// match の枝の並び（字句）：枝は「パターン ` => ` 本体」、枝の間は `, `、最後の後ろに tail。
pub open spec fn farms(arms: Seq<(Spat, Sx)>, i: nat, tail: Seq<char>) -> Seq<char>
    decreases arms, arms.len() - i,
{
    if i >= arms.len() {
        tail
    } else {
        fpat(arms[i as int].0, seq![' ', '=', '>', ' '] + fe(
            arms[i as int].1,
            if i + 1 == arms.len() {
                tail
            } else {
                seq![',', ' '] + farms(arms, i + 1, tail)
            },
        ))
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

pub open spec fn fps(ps: Seq<(Seq<char>, SType)>, i: nat, k: Seq<char>) -> Seq<char>
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
pub open spec fn ffd(fs: Seq<(Seq<char>, SType)>, i: nat, tail: Seq<char>) -> Seq<char>
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
pub open spec fn ftys(ps: Seq<SType>, i: nat, tail: Seq<char>) -> Seq<char>
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
pub open spec fn fpay(ps: Seq<SType>, rest: Seq<char>) -> Seq<char> {
    if ps.len() == 0 {
        rest
    } else {
        seq!['('] + ftys(ps, 0, seq![')'] + rest)
    }
}

/// 直和型の構築子の並びの字句（` | ` で区切り、最後の後ろに tail）。
pub open spec fn fvars(vs: Seq<(Seq<char>, Seq<SType>)>, i: nat, tail: Seq<char>) -> Seq<char>
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
pub open spec fn pt(ts: Seq<Tok>, i: nat, d: nat) -> Option<(SType, nat)>
    decreases d,
{
    if d == 0 || i >= ts.len() {
        None
    } else {
        match ts[i as int] {
            Tok::Kw(Kw::TInt) => Some((SType::Int, i + 1)),
            Tok::Kw(Kw::TBool) => Some((SType::Bool, i + 1)),
            Tok::Kw(Kw::TUnit) => Some((SType::Unit, i + 1)),
            Tok::Kw(Kw::TChar) => Some((SType::Char, i + 1)),
            Tok::Kw(Kw::TString) => Some((SType::List(Box::new(SType::Char)), i + 1)),
            Tok::Kw(Kw::TList) => if sym(ts, i + 1, '<') {
                match pt(ts, i + 2, (d - 1) as nat) {
                    Some((a, j)) => if sym(ts, j, '>') && a != SType::Char {
                        Some((SType::List(Box::new(a)), j + 1))
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
                        Some((SType::Option(Box::new(a)), j + 1))
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
                                        SType::Pair(Box::new(a), Box::new(b))
                                    } else {
                                        SType::Result(Box::new(a), Box::new(b))
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
            Tok::Id(x) => if !tyname_ok(x) {
                None
            } else if x == dict_name() && sym(ts, i + 1, '<') {
                match pt(ts, i + 2, (d - 1) as nat) {
                    Some((a, j)) => if sym(ts, j, ',') {
                        match pt(ts, j + 1, (d - 1) as nat) {
                            Some((b, m)) => if sym(ts, m, '>') {
                                Some((SType::Dict(Box::new(a), Box::new(b)), m + 1))
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
                Some((SType::Named(x), i + 1))
            },
            _ => None,
        }
    }
}

/// 後置（`.f`）を除く基本の式。d は式の入れ子の深さ上限、td は型の深さ上限。
pub open spec fn pp(ts: Seq<Tok>, i: nat, d: nat, td: nat) -> Option<(Sx, nat)>
    decreases d, 0nat, 1nat,
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
            } else if x == mword() && pm(ts, i, d, td) is Some {
                pm(ts, i, d, td)
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
                } else if k == Kw::Loop {
                    // loop(init, max, |x| b)：語の直後が `(`（loop は `<` の形を持たない）。初期値、上限、binder、本体、閉じ括弧。
                    if sym(ts, i + 1, '(') {
                        match pe(ts, i + 2, d1, td) {
                            Some((a, j)) => if sym(ts, j, ',') {
                                match pe(ts, j + 1, d1, td) {
                                    Some((m, q)) => if sym(ts, q, ',') && sym(ts, q + 1, '|') && sym(ts, q + 3, '|') {
                                        match bdt(ts, q + 2) {
                                            Some(x) => match pe(ts, q + 4, d1, td) {
                                                Some((b, u)) => if sym(ts, u, ')') {
                                                    Some((Sx::Loop(Box::new(a), Box::new(m), x, Box::new(b)), u + 1))
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
                            },
                            None => None,
                        }
                    } else {
                        None
                    }
                } else if kw_hf(k) is Some {
                    // hof(e, |x| b)：語の直後が `(`（hof は `<` の形を持たない）。被験の列、binder、本体、閉じ括弧。
                    if sym(ts, i + 1, '(') {
                        match pe(ts, i + 2, d1, td) {
                            Some((l, j)) => if sym(ts, j, ',') && sym(ts, j + 1, '|') && sym(ts, j + 3, '|') {
                                match bdt(ts, j + 2) {
                                    Some(x) => match pe(ts, j + 4, d1, td) {
                                        Some((b, m)) => if sym(ts, m, ')') {
                                            Some((Sx::Hof(kw_hf(k)->Some_0, Box::new(l), x, Box::new(b)), m + 1))
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
                } else if k == Kw::Dict {
                    // dict<K, V>()：語の直後が `<`（`(` の形は持たない）。二つの型、`(`、`)`。
                    if sym(ts, i + 1, '<') {
                        match pt(ts, i + 2, td) {
                            Some((a, j)) => if sym(ts, j, ',') {
                                match pt(ts, j + 1, td) {
                                    Some((b, m)) => if sym(ts, m, '>') && sym(ts, m + 1, '(') && sym(ts, m + 2, ')') {
                                        Some((Sx::DictNew(a, b), m + 3))
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
                } else if kw_dop(k) is Some {
                    // dict の組込み：語の直後が `(`（型引数を持たないので `<` は読めない）。引数の列、閉じ括弧。
                    if sym(ts, i + 1, '(') {
                        match pargs(ts, i + 2, d1, td) {
                            Some((es, j)) => Some((Sx::DictOp(kw_dop(k)->Some_0, es), j)),
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
        Some((e, j)) => if recv_ok(e) && j + 1 < ts.len() && sym(ts, j, '.') && bdt(ts, j + 1) is Some {
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
    if j + 1 < ts.len() && sym(ts, j, '.') && bdt(ts, j + 1) is Some {
        let r = pfs(ts, j + 2);
        (seq![bdt(ts, j + 1)->Some_0] + r.0, r.1)
    } else {
        (Seq::empty(), j)
    }
}

/// `R {` の後ろがレコード式の本体の形（`}`、`名前 :`、`..`）なら、R は記録式の名前。
/// それ以外（`match x { ... }` の被験式など）は変数と読む。
pub open spec fn rec_head(ts: Seq<Tok>, i: nat) -> bool {
    sym(ts, i, '}') || (bdt(ts, i) is Some && sym(ts, i + 1, ':')) || (sym(ts, i, '.') && sym(ts, i + 1, '.'))
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
        match bdt(ts, i) {
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

/// `match e { 枝 }` の本体（位置 i は `match` の語）。被験式の後に `{`、枝の並び、閉じ括弧まで。
/// 後ろが被験式の形でなければ None（pp が変数などとして読み直す）。
pub open spec fn pm(ts: Seq<Tok>, i: nat, d: nat, td: nat) -> Option<(Sx, nat)>
    decreases d, 0nat, 0nat,
{
    if d == 0 {
        None
    } else {
        let d1 = (d - 1) as nat;
        match pe(ts, i + 1, d1, td) {
            Some((m, j)) => if sym(ts, j, '{') {
                match parm1(ts, j + 1, d1, td) {
                    Some((arms, k)) => Some((Sx::SumMatch(Box::new(m), arms), k)),
                    None => None,
                }
            } else {
                None
            },
            None => None,
        }
    }
}

/// 枝の並び（一つ以上）と、閉じ括弧 `}` の後の位置。枝の間は `,`、末尾に `,` は書かない（字句と枝の並びを一対一に対応させるため）。
pub open spec fn parm1(ts: Seq<Tok>, i: nat, d: nat, td: nat) -> Option<(Seq<(Spat, Sx)>, nat)>
    decreases d, 2nat, ts.len() - i,
{
    match ppat(ts, i) {
        Some((p, j)) => if sym(ts, j, '=') && sym(ts, j + 1, '>') {
            match pe(ts, j + 2, d, td) {
                Some((b, m)) => if sym(ts, m, '}') {
                    Some((seq![(p, b)], m + 1))
                } else if sym(ts, m, ',') && i < m {
                    match parm1(ts, m + 1, d, td) {
                        Some((arms, k)) => Some((seq![(p, b)] + arms, k)),
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

/// 枝の左辺（パターン）：位置 i から、パターンと後ろの位置。
pub open spec fn ppat(ts: Seq<Tok>, i: nat) -> Option<(Spat, nat)> {
    if cidt(ts, i) is Some {
        if sym(ts, i + 1, '(') {
            match pbinds(ts, i + 2) {
                Some((bs, j)) => Some((Spat::Ctor(cidt(ts, i)->Some_0, bs), j)),
                None => None,
            }
        } else {
            Some((Spat::Ctor(cidt(ts, i)->Some_0, Seq::empty()), i + 1))
        }
    } else if kwat(ts, i, Kw::Ok) && sym(ts, i + 1, '(') && bdt(ts, i + 2) is Some && sym(ts, i + 3, ')') {
        Some((Spat::Ok(bdt(ts, i + 2)->Some_0), i + 4))
    } else if kwat(ts, i, Kw::Err) && sym(ts, i + 1, '(') && bdt(ts, i + 2) is Some && sym(ts, i + 3, ')') {
        Some((Spat::Err(bdt(ts, i + 2)->Some_0), i + 4))
    } else if kwat(ts, i, Kw::Some) && sym(ts, i + 1, '(') && bdt(ts, i + 2) is Some && sym(ts, i + 3, ')') {
        Some((Spat::Some(bdt(ts, i + 2)->Some_0), i + 4))
    } else if kwat(ts, i, Kw::None) {
        Some((Spat::None, i + 1))
    } else if i < ts.len() && ts[i as int] == Tok::Id(seq!['_']) {
        Some((Spat::Wild, i + 1))
    } else {
        None
    }
}

/// 構築子の束縛の並び `bind ("," bind)* ")"`（位置 i から。閉じ括弧の後の位置）。
pub open spec fn pbinds(ts: Seq<Tok>, i: nat) -> Option<(Seq<Seq<char>>, nat)>
    decreases ts.len() - i,
{
    match bdt(ts, i) {
        Some(x) => if sym(ts, i + 1, ')') {
            Some((seq![x], i + 2))
        } else if sym(ts, i + 1, ',') {
            match pbinds(ts, i + 2) {
                Some((xs, j)) => Some((seq![x] + xs, j)),
                None => None,
            }
        } else {
            None
        },
        None => None,
    }
}

/// `[ params ] ")"`
pub open spec fn pparams(ts: Seq<Tok>, i: nat, td: nat) -> Option<(Seq<(Seq<char>, SType)>, nat)> {
    if sym(ts, i, ')') {
        Some((Seq::empty(), i + 1))
    } else {
        pparams1(ts, i, td)
    }
}

pub open spec fn pparams1(ts: Seq<Tok>, i: nat, td: nat) -> Option<(Seq<(Seq<char>, SType)>, nat)>
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
pub open spec fn pfds(ts: Seq<Tok>, i: nat, td: nat) -> Option<(Seq<(Seq<char>, SType)>, bool, nat)>
    decreases ts.len() - i,
{
    match bdt(ts, i) {
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
pub open spec fn ptys(ts: Seq<Tok>, i: nat, td: nat) -> Option<(Seq<SType>, nat)>
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
pub open spec fn pvar(ts: Seq<Tok>, i: nat, td: nat) -> Option<(Seq<char>, Seq<SType>, nat)> {
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
pub open spec fn pvars(ts: Seq<Tok>, i: nat, td: nat) -> Option<(Seq<(Seq<char>, Seq<SType>)>, nat)>
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

pub open spec fn bt(t: SType, d: nat) -> bool
    decreases t,
{
    d > 0 && match t {
        SType::List(a) => *a == SType::Char || bt(*a, (d - 1) as nat),
        SType::Option(a) => bt(*a, (d - 1) as nat),
        SType::Pair(a, b) | SType::Result(a, b) | SType::Dict(a, b) => bt(*a, (d - 1) as nat) && bt(*b, (d - 1) as nat),
        SType::Named(x) => ident_ok(x),
        SType::Int | SType::Bool | SType::Unit | SType::Char => true,
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
            Sx::SumMatch(m, arms) => arms.len() > 0 && bx(*m, d1, td) && barms(arms, 0, d1, td),
            Sx::Hof(_, l, x, b) => name_ok(x) && bx(*l, d1, td) && bx(*b, d1, td),
            Sx::Loop(i, m, x, b) => name_ok(x) && bx(*i, d1, td) && bx(*m, d1, td) && bx(*b, d1, td),
            Sx::DictNew(a, b) => bt(a, td) && bt(b, td),
            Sx::DictOp(_, es) => bxs(es, 0, d1, td),
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

/// 枝の左辺：構築子の名前は大文字で始まる IDENT、束縛の名前は名前（`_` も含む）。
pub open spec fn bpat(p: Spat) -> bool {
    match p {
        Spat::Ctor(c, bs) => cname_ok(c) && bnames(bs),
        Spat::Ok(x) | Spat::Err(x) | Spat::Some(x) => name_ok(x),
        Spat::None | Spat::Wild => true,
    }
}

/// 束縛の並びの名前は、すべて名前（`_` も含む）。
pub open spec fn bnames(bs: Seq<Seq<char>>) -> bool {
    forall|j: int| 0 <= j < bs.len() ==> name_ok(#[trigger] bs[j])
}

/// 枝の並び（位置 i から）：左辺は正しく、本体は深さ内。
pub open spec fn barms(arms: Seq<(Spat, Sx)>, i: nat, d: nat, td: nat) -> bool
    decreases arms, arms.len() - i,
{
    i >= arms.len() || (bpat(arms[i as int].0) && bx(arms[i as int].1, d, td) && barms(arms, i + 1, d, td))
}

pub open spec fn bxs(es: Seq<Sx>, i: nat, d: nat, td: nat) -> bool
    decreases es, es.len() - i,
{
    i >= es.len() || (bx(es[i as int], d, td) && bxs(es, i + 1, d, td))
}

/// `.名前` の並びの名前は、すべて field の名前（IDENT か文脈キーワード）。
pub open spec fn nms(fs: Seq<Seq<char>>) -> bool
    decreases fs.len(),
{
    fs.len() == 0 || (name_ok(fs[0]) && nms(fs.subrange(1, fs.len() as int)))
}

/// レコード式の field：名前は IDENT か文脈キーワードで、値は深さ内。
pub open spec fn bfs(fs: Seq<(Seq<char>, Sx)>, i: nat, d: nat, td: nat) -> bool
    decreases fs, fs.len() - i,
{
    i >= fs.len() || (name_ok(fs[i as int].0) && bx(fs[i as int].1, d, td) && bfs(fs, i + 1, d, td))
}

/// レコード型の宣言の field：名前は IDENT か文脈キーワードで、型は深さ内。
pub open spec fn bfds(fs: Seq<(Seq<char>, SType)>, i: nat, td: nat) -> bool
    decreases fs.len() - i,
{
    i >= fs.len() || (name_ok(fs[i as int].0) && bt(fs[i as int].1, td) && bfds(fs, i + 1, td))
}

pub open spec fn bps(ps: Seq<(Seq<char>, SType)>, i: nat, td: nat) -> bool
    decreases ps.len() - i,
{
    i >= ps.len() || (name_ok(ps[i as int].0) && bt(ps[i as int].1, td) && bps(ps, i + 1, td))
}

/// 型の並びの深さ（bt）。
pub open spec fn bts(ps: Seq<SType>, i: nat, td: nat) -> bool
    decreases ps.len() - i,
{
    i >= ps.len() || (bt(ps[i as int], td) && bts(ps, i + 1, td))
}

/// 直和型の構築子：名前は大文字で始まる IDENT、中身の型は深さ内。
pub open spec fn bvars(vs: Seq<(Seq<char>, Seq<SType>)>, i: nat, td: nat) -> bool
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
