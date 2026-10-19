//! 表面構文の exec 実装：字句解析器、構文解析器、正準フォーマッタ。
//!
//! それぞれ syntax.rs の spec 関数（`lex`、`pds`、`fds`）と同じ結果を返すことを証明する。
//! spec 側の性質（parser の健全性・完全性、formatter の AST 保存性・冪等性）は parse_proof.rs。

use crate::bigint::*;
use crate::ir::*;
use crate::json::*;
use crate::parse_proof::*;
use crate::spec::*;
use crate::syntax::*;
use crate::syntax_proof::*;
use vstd::prelude::*;

verus! {

// ------------------------------------------------------------------ exec の token と表面 AST

pub enum ETok {
    Int(Int),
    Chr(char),
    Str(Vec<char>),
    Id(Vec<char>),
    Kw(Kw),
    Sym(char),
    Arrow,
}

pub open spec fn vtok(t: ETok) -> Tok {
    match t {
        ETok::Int(n) => Tok::Int(n@),
        ETok::Chr(c) => Tok::Chr(c),
        ETok::Str(w) => Tok::Str(w@),
        ETok::Id(x) => Tok::Id(x@),
        ETok::Kw(k) => Tok::Kw(k),
        ETok::Sym(c) => Tok::Sym(c),
        ETok::Arrow => Tok::Arrow,
    }
}

pub open spec fn vtoks(ts: Seq<ETok>) -> Seq<Tok> {
    Seq::new(ts.len(), |i: int| vtok(ts[i]))
}

pub enum SExpr {
    Int(Int),
    Chr(char),
    Str(Vec<char>),
    Bool(bool),
    Unit,
    Var(Vec<char>),
    List(Ty, Vec<SExpr>),
    Some(Box<SExpr>),
    None(Ty),
    Pair(Box<SExpr>, Box<SExpr>),
    Builtin(Builtin, Vec<SExpr>),
    Call(Vec<char>, Vec<SExpr>),
    Let(Vec<char>, Box<SExpr>, Box<SExpr>),
    If(Box<SExpr>, Box<SExpr>, Box<SExpr>),
    Fold(Box<SExpr>, Box<SExpr>, Vec<char>, Vec<char>, Box<SExpr>),
    Match(Box<SExpr>, Box<SExpr>, Vec<char>, Box<SExpr>),
    Inj(bool, Ty, Ty, Box<SExpr>),
    MatchR(Box<SExpr>, Vec<char>, Box<SExpr>, Vec<char>, Box<SExpr>),
    /// v1.1：e.f1.f2…（名前の列は空でない）
    Fld(Box<SExpr>, Vec<Vec<char>>),
    /// v1.1：R { f: e, ..b }（名前と式は同じ長さの二つの列。省略できる base）
    Rec(Vec<char>, Vec<Vec<char>>, Vec<SExpr>, Option<Box<SExpr>>),
    /// v1.4：match e { P => a, ... }（被験式と、枝のパターンと本体の二つの列。同じ長さで空でない）
    SumMatch(Box<SExpr>, Vec<SPat>, Vec<SExpr>),
    /// v1.5：hof(e, |x| b)（hof の語、被験の列、binder、本体）
    Hof(Hf, Box<SExpr>, Vec<char>, Box<SExpr>),
    /// v1.6：loop(init, max, |s| e)（初期値、上限、binder、本体）
    Loop(Box<SExpr>, Box<SExpr>, Vec<char>, Box<SExpr>),
    /// v1.9：dict<A, B>()（空の辞書。型の引数は核の Ty）
    DictNew(Ty, Ty),
    /// v1.9：dict の組込み呼出し（組込みの語と、引数の列）
    DictOp(Dop, Vec<SExpr>),
}

/// v1.4：match の枝の左辺（パターン）。
pub enum SPat {
    /// CTOR か CTOR "(" bind ("," bind)* ")"（構築子の名前と束縛の並び）
    Ctor(Vec<char>, Vec<Vec<char>>),
    /// ok "(" bind ")"
    Ok(Vec<char>),
    /// err "(" bind ")"
    Err(Vec<char>),
    /// some "(" bind ")"
    Some(Vec<char>),
    /// none
    None,
    /// _
    Wild,
}

pub enum SDecl {
    Fn(Vec<char>, Vec<(Vec<char>, Ty)>, Ty, SExpr),
    Entry(Vec<char>),
    /// v1.1：type R = { f: T, ... }（末尾のカンマの有無を持つ）
    RecTy(Vec<char>, Vec<(Vec<char>, Ty)>, bool),
    /// v1.4：type S = V1 | V2(T, U)（構築子の名前と、中身の型の並び）
    Sum(Vec<char>, Vec<(Vec<char>, Vec<Ty>)>),
}

pub open spec fn vx(e: SExpr) -> Sx
    decreases e,
{
    match e {
        SExpr::Int(n) => Sx::Int(n@),
        SExpr::Chr(c) => Sx::Chr(c),
        SExpr::Str(w) => Sx::Str(w@),
        SExpr::Bool(b) => Sx::Bool(b),
        SExpr::Unit => Sx::Unit,
        SExpr::Var(x) => Sx::Var(x@),
        SExpr::List(t, es) => Sx::List(t, vxs(es)),
        SExpr::Some(a) => Sx::Some(Box::new(vx(*a))),
        SExpr::None(t) => Sx::None(t),
        SExpr::Pair(a, b) => Sx::Pair(Box::new(vx(*a)), Box::new(vx(*b))),
        SExpr::Builtin(b, es) => Sx::Builtin(b, vxs(es)),
        SExpr::Call(f, es) => Sx::Call(f@, vxs(es)),
        SExpr::Let(x, a, b) => Sx::Let(x@, Box::new(vx(*a)), Box::new(vx(*b))),
        SExpr::If(c, a, b) => Sx::If(Box::new(vx(*c)), Box::new(vx(*a)), Box::new(vx(*b))),
        SExpr::Fold(l, i, a, x, b) => Sx::Fold(Box::new(vx(*l)), Box::new(vx(*i)), a@, x@, Box::new(vx(*b))),
        SExpr::Match(m, n, x, b) => Sx::Match(Box::new(vx(*m)), Box::new(vx(*n)), x@, Box::new(vx(*b))),
        SExpr::Inj(ok, t, u, a) => Sx::Inj(ok, t, u, Box::new(vx(*a))),
        SExpr::MatchR(m, x, a, y, b) => Sx::MatchR(Box::new(vx(*m)), x@, Box::new(vx(*a)), y@, Box::new(vx(*b))),
        SExpr::Fld(a, ns) => Sx::Fld(Box::new(vx(*a)), vnames(ns@)),
        SExpr::Rec(r, ns, es, b) => Sx::Rec(r@, vfields(ns@, es@), vbase(b)),
        SExpr::SumMatch(m, ps, es) => Sx::SumMatch(Box::new(vx(*m)), varms(ps@, es@)),
        SExpr::Hof(h, l, x, b) => Sx::Hof(h, Box::new(vx(*l)), x@, Box::new(vx(*b))),
        SExpr::Loop(i, m, x, b) => Sx::Loop(Box::new(vx(*i)), Box::new(vx(*m)), x@, Box::new(vx(*b))),
        SExpr::DictNew(a, b) => Sx::DictNew(a, b),
        SExpr::DictOp(d, es) => Sx::DictOp(d, vxs(es)),
    }
}

pub open spec fn vnames(ns: Seq<Vec<char>>) -> Seq<Seq<char>> {
    Seq::new(ns.len(), |i: int| ns[i]@)
}

/// レコード式の字段（名前の列と式の列は同じ長さ。式の列を再帰の対象にする）。
pub open spec fn vfields(ns: Seq<Vec<char>>, es: Seq<SExpr>) -> Seq<(Seq<char>, Sx)>
    decreases es,
{
    Seq::new(ns.len(), |i: int| (ns[i]@, if 0 <= i < es.len() { vx(es[i]) } else { Sx::Unit }))
}

/// match の枝の左辺（パターン）の spec 値。
pub open spec fn vpat(p: SPat) -> Spat {
    match p {
        SPat::Ctor(c, bs) => Spat::Ctor(c@, vnames(bs@)),
        SPat::Ok(x) => Spat::Ok(x@),
        SPat::Err(x) => Spat::Err(x@),
        SPat::Some(x) => Spat::Some(x@),
        SPat::None => Spat::None,
        SPat::Wild => Spat::Wild,
    }
}

/// match の枝の並び（パターンの列と本体の列から。二つの列は同じ長さ）。
pub open spec fn varms(ps: Seq<SPat>, es: Seq<SExpr>) -> Seq<(Spat, Sx)>
    decreases es,
{
    Seq::new(ps.len(), |i: int| (vpat(ps[i]), if 0 <= i < es.len() { vx(es[i]) } else { Sx::Unit }))
}

/// レコード式の省略できる base。
pub open spec fn vbase(b: Option<Box<SExpr>>) -> Option<Box<Sx>>
    decreases b,
{
    match b {
        Some(x) => Some(Box::new(vx(*x))),
        None => None,
    }
}

pub open spec fn vxs(es: Vec<SExpr>) -> Seq<Sx>
    decreases es,
{
    Seq::new(es@.len(), |i: int| if 0 <= i < es@.len() { vx(es@[i]) } else { Sx::Unit })
}

pub open spec fn vps(ps: Seq<(Vec<char>, Ty)>) -> Seq<(Seq<char>, Ty)> {
    Seq::new(ps.len(), |i: int| (ps[i].0@, ps[i].1))
}

pub open spec fn vvars(vs: Seq<(Vec<char>, Vec<Ty>)>) -> Seq<(Seq<char>, Seq<Ty>)> {
    Seq::new(vs.len(), |i: int| (vs[i].0@, vs[i].1@))
}

pub open spec fn vd(x: SDecl) -> Sd {
    match x {
        SDecl::Fn(f, ps, r, b) => Sd::Fn(f@, vps(ps@), r, vx(b)),
        SDecl::Entry(n) => Sd::Entry(n@),
        SDecl::RecTy(r, fs, tc) => Sd::RecTy(r@, vps(fs@), tc),
        SDecl::Sum(r, vs) => Sd::Sum(r@, vvars(vs@)),
    }
}

pub open spec fn vds(p: Seq<SDecl>) -> Seq<Sd> {
    Seq::new(p.len(), |i: int| vd(p[i]))
}

// ------------------------------------------------------------------ 小さな exec 補助

pub fn clone_chars(v: &Vec<char>) -> (r: Vec<char>)
    ensures
        r@ == v@,
{
    let mut r: Vec<char> = Vec::new();
    let mut i: usize = 0;
    while i < v.len()
        invariant
            i <= v.len(),
            r@ == v@.subrange(0, i as int),
        decreases v.len() - i,
    {
        r.push(v[i]);
        i += 1;
        proof {
            assert(r@ =~= v@.subrange(0, i as int));
        }
    }
    proof {
        assert(r@ =~= v@);
    }
    r
}

pub fn eq_chars(a: &Vec<char>, b: &Vec<char>) -> (r: bool)
    ensures
        r == (a@ == b@),
{
    if a.len() != b.len() {
        return false;
    }
    let mut i: usize = 0;
    while i < a.len()
        invariant
            a.len() == b.len(),
            i <= a.len(),
            forall|j: int| 0 <= j < i ==> a@[j] == b@[j],
        decreases a.len() - i,
    {
        if a[i] != b[i] {
            return false;
        }
        i += 1;
    }
    proof {
        assert(a@ =~= b@);
    }
    true
}

fn append_chars(out: &mut Vec<char>, v: &Vec<char>)
    ensures
        final(out)@ == old(out)@ + v@,
{
    let mut i: usize = 0;
    while i < v.len()
        invariant
            i <= v.len(),
            out@ == old(out)@ + v@.subrange(0, i as int),
        decreases v.len() - i,
    {
        out.push(v[i]);
        i += 1;
        proof {
            assert(out@ =~= old(out)@ + v@.subrange(0, i as int));
        }
    }
    proof {
        assert(v@.subrange(0, v@.len() as int) =~= v@);
    }
}

pub fn is_alpha_e(c: char) -> (b: bool)
    ensures
        b == is_alpha(c),
{
    (0x41 <= c as u32 && c as u32 <= 0x5a) || (0x61 <= c as u32 && c as u32 <= 0x7a)
}

pub fn is_digit_e(c: char) -> (b: bool)
    ensures
        b == is_digit(c),
{
    0x30 <= c as u32 && c as u32 <= 0x39
}

pub fn ident_start_e(c: char) -> (b: bool)
    ensures
        b == ident_start(c),
{
    is_alpha_e(c) || c == '_'
}

pub fn ident_char_e(c: char) -> (b: bool)
    ensures
        b == ident_char(c),
{
    ident_start_e(c) || is_digit_e(c)
}

fn is_ws_e(c: char) -> (b: bool)
    ensures
        b == is_ws(c),
{
    c == ' ' || c == '\t' || c == '\r' || c == '\n'
}

fn is_sym_e(c: char) -> (b: bool)
    ensures
        b == is_sym(c),
{
    c == '(' || c == ')' || c == '[' || c == ']' || c == '<' || c == '>' || c == ',' || c == ':' || c == '='
        || c == '|' || c == '{' || c == '}' || c == '.'
}

fn dval_e(c: char) -> (r: u64)
    requires
        is_digit(c),
    ensures
        r as int == dval(c),
{
    (c as u32 - 0x30) as u64
}

// ------------------------------------------------------------------ 予約語

fn c2e(w: &Vec<char>, a: char, b: char) -> (r: bool)
    requires
        w@.len() == 2,
    ensures
        r == c2(w@, a, b),
{
    w[0] == a && w[1] == b
}

fn c3e(w: &Vec<char>, a: char, b: char, c: char) -> (r: bool)
    requires
        w@.len() == 3,
    ensures
        r == c3(w@, a, b, c),
{
    w[0] == a && w[1] == b && w[2] == c
}

fn c4e(w: &Vec<char>, a: char, b: char, c: char, d: char) -> (r: bool)
    requires
        w@.len() == 4,
    ensures
        r == c4(w@, a, b, c, d),
{
    w[0] == a && w[1] == b && w[2] == c && w[3] == d
}

fn c5e(w: &Vec<char>, a: char, b: char, c: char, d: char, e: char) -> (r: bool)
    requires
        w@.len() == 5,
    ensures
        r == c5(w@, a, b, c, d, e),
{
    w[0] == a && w[1] == b && w[2] == c && w[3] == d && w[4] == e
}

fn c6e(w: &Vec<char>, a: char, b: char, c: char, d: char, e: char, f: char) -> (r: bool)
    requires
        w@.len() >= 6,
    ensures
        r == c6(w@, a, b, c, d, e, f),
{
    w[0] == a && w[1] == b && w[2] == c && w[3] == d && w[4] == e && w[5] == f
}

pub fn kw_of_e(w: &Vec<char>) -> (r: Option<Kw>)
    ensures
        r == kw_of(w@),
{
    let n = w.len();
    if n == 2 {
        if c2e(w, 'f', 'n') {
            Some(Kw::Fn)
        } else if c2e(w, 'i', 'n') {
            Some(Kw::In)
        } else if c2e(w, 'i', 'f') {
            Some(Kw::If)
        } else if c2e(w, 'l', 't') {
            Some(Kw::Lt)
        } else if c2e(w, 'l', 'e') {
            Some(Kw::Le)
        } else if c2e(w, 'e', 'q') {
            Some(Kw::Eq)
        } else if c2e(w, 'o', 'k') {
            Some(Kw::Ok)
        } else {
            None
        }
    } else if n == 3 {
        if c3e(w, 'I', 'n', 't') {
            Some(Kw::TInt)
        } else if c3e(w, 'a', 'd', 'd') {
            Some(Kw::Add)
        } else if c3e(w, 's', 'u', 'b') {
            Some(Kw::Sub)
        } else if c3e(w, 'm', 'u', 'l') {
            Some(Kw::Mul)
        } else if c3e(w, 'n', 'e', 'g') {
            Some(Kw::Neg)
        } else if c3e(w, 'm', 'o', 'd') {
            Some(Kw::Mod)
        } else if c3e(w, 'd', 'i', 'v') {
            Some(Kw::Div)
        } else if c3e(w, 'f', 's', 't') {
            Some(Kw::Fst)
        } else if c3e(w, 's', 'n', 'd') {
            Some(Kw::Snd)
        } else if c3e(w, 'l', 'e', 't') {
            Some(Kw::Let)
        } else if c3e(w, 'm', 'i', 'n') {
            Some(Kw::Min)
        } else if c3e(w, 'm', 'a', 'x') {
            Some(Kw::Max)
        } else if c3e(w, 'e', 'r', 'r') {
            Some(Kw::Err)
        } else if c3e(w, 'm', 'a', 'p') {
            Some(Kw::Map)
        } else if c3e(w, 'a', 'n', 'y') {
            Some(Kw::Any)
        } else if c3e(w, 'a', 'l', 'l') {
            Some(Kw::All)
        } else {
            None
        }
    } else if n == 4 {
        if c4e(w, 'B', 'o', 'o', 'l') {
            Some(Kw::TBool)
        } else if c4e(w, 'U', 'n', 'i', 't') {
            Some(Kw::TUnit)
        } else if c4e(w, 'L', 'i', 's', 't') {
            Some(Kw::TList)
        } else if c4e(w, 'P', 'a', 'i', 'r') {
            Some(Kw::TPair)
        } else if c4e(w, 't', 'r', 'u', 'e') {
            Some(Kw::True)
        } else if c4e(w, 'u', 'n', 'i', 't') {
            Some(Kw::Unit)
        } else if c4e(w, 'l', 'i', 's', 't') {
            Some(Kw::List)
        } else if c4e(w, 's', 'o', 'm', 'e') {
            Some(Kw::Some)
        } else if c4e(w, 'n', 'o', 'n', 'e') {
            Some(Kw::None)
        } else if c4e(w, 'p', 'a', 'i', 'r') {
            Some(Kw::Pair)
        } else if c4e(w, 'f', 'o', 'l', 'd') {
            Some(Kw::Fold)
        } else if c4e(w, 'c', 'o', 'n', 's') {
            Some(Kw::Cons)
        } else if c4e(w, 's', 'o', 'r', 't') {
            Some(Kw::Sort)
        } else if c4e(w, 'C', 'h', 'a', 'r') {
            Some(Kw::TChar)
        } else if c4e(w, 'c', 'o', 'd', 'e') {
            Some(Kw::Code)
        } else if c4e(w, 'c', 'h', 'a', 'r') {
            Some(Kw::CharOf)
        } else if c4e(w, 'f', 'i', 'n', 'd') {
            Some(Kw::Find)
        } else if c4e(w, 'l', 'o', 'o', 'p') {
            Some(Kw::Loop)
        } else if c4e(w, 'd', 'i', 'c', 't') {
            Some(Kw::Dict)
        } else {
            None
        }
    } else if n == 5 {
        if c5e(w, 'e', 'n', 't', 'r', 'y') {
            Some(Kw::Entry)
        } else if c5e(w, 'f', 'a', 'l', 's', 'e') {
            Some(Kw::False)
        } else if c5e(w, 'r', 'a', 'n', 'g', 'e') {
            Some(Kw::Range)
        } else {
            None
        }
    } else if n == 6 {
        if c6e(w, 'O', 'p', 't', 'i', 'o', 'n') {
            Some(Kw::TOption)
        } else if c6e(w, 'c', 'o', 'n', 'c', 'a', 't') {
            Some(Kw::Concat)
        } else if c6e(w, 'l', 'e', 'n', 'g', 't', 'h') {
            Some(Kw::Length)
        } else if c6e(w, 'u', 'n', 'c', 'o', 'n', 's') {
            Some(Kw::Uncons)
        } else if c6e(w, 'S', 't', 'r', 'i', 'n', 'g') {
            Some(Kw::TString)
        } else if c6e(w, 'R', 'e', 's', 'u', 'l', 't') {
            Some(Kw::TResult)
        } else if c6e(w, 'f', 'i', 'l', 't', 'e', 'r') {
            Some(Kw::Filter)
        } else {
            None
        }
    } else if n == 7 {
        if c6e(w, 'r', 'e', 'v', 'e', 'r', 's') && w[6] == 'e' {
            Some(Kw::Reverse)
        } else if c6e(w, 's', 'o', 'r', 't', '_', 'b') && w[6] == 'y' {
            Some(Kw::SortBy)
        } else {
            None
        }
    } else if n == 8 {
        if c6e(w, 'c', 'o', 'n', 't', 'a', 'i') && w[6] == 'n' && w[7] == 's' {
            Some(Kw::Contains)
        } else if c6e(w, 'd', 'i', 'c', 't', '_', 'g') && w[6] == 'e' && w[7] == 't' {
            Some(Kw::DictGet)
        } else if c6e(w, 'd', 'i', 'c', 't', '_', 'p') && w[6] == 'u' && w[7] == 't' {
            Some(Kw::DictPut)
        } else if c6e(w, 'd', 'i', 'c', 't', '_', 'h') && w[6] == 'a' && w[7] == 's' {
            Some(Kw::DictHas)
        } else {
            None
        }
    } else if n == 9 {
        if c6e(w, 't', 'o', '_', 's', 't', 'r') && w[6] == 'i' && w[7] == 'n' && w[8] == 'g' {
            Some(Kw::ToString)
        } else if c6e(w, 'p', 'a', 'r', 's', 'e', '_') && w[6] == 'i' && w[7] == 'n' && w[8] == 't' {
            Some(Kw::ParseInt)
        } else if c6e(w, 'd', 'i', 'c', 't', '_', 's') && w[6] == 'i' && w[7] == 'z' && w[8] == 'e' {
            Some(Kw::DictSize)
        } else if c6e(w, 'd', 'i', 'c', 't', '_', 'k') && w[6] == 'e' && w[7] == 'y' && w[8] == 's' {
            Some(Kw::DictKeys)
        } else if c6e(w, 'd', 'i', 'c', 't', '_', 'f') && w[6] == 'r' && w[7] == 'o' && w[8] == 'm' {
            Some(Kw::DictFrom)
        } else {
            None
        }
    } else if n == 11 {
        if c6e(w, 'd', 'i', 'c', 't', '_', 'r') && w[6] == 'e' && w[7] == 'm' && w[8] == 'o' && w[9] == 'v'
            && w[10] == 'e' {
            Some(Kw::DictRemove)
        } else if c6e(w, 'd', 'i', 'c', 't', '_', 'v') && w[6] == 'a' && w[7] == 'l' && w[8] == 'u' && w[9] == 'e'
            && w[10] == 's' {
            Some(Kw::DictValues)
        } else {
            None
        }
    } else if n == 12 {
        if c6e(w, 'm', 'a', 't', 'c', 'h', '_') && w[6] == 'o' && w[7] == 'p' && w[8] == 't' && w[9] == 'i'
            && w[10] == 'o' && w[11] == 'n' {
            Some(Kw::MatchOption)
        } else if c6e(w, 'm', 'a', 't', 'c', 'h', '_') && w[6] == 'r' && w[7] == 'e' && w[8] == 's' && w[9] == 'u'
            && w[10] == 'l' && w[11] == 't' {
            Some(Kw::MatchResult)
        } else if c6e(w, 'd', 'i', 'c', 't', '_', 'e') && w[6] == 'n' && w[7] == 't' && w[8] == 'r' && w[9] == 'i'
            && w[10] == 'e' && w[11] == 's' {
            Some(Kw::DictEntries)
        } else {
            None
        }
    } else {
        None
    }
}

pub fn ident_ok_e(x: &Vec<char>) -> (r: bool)
    ensures
        r == ident_ok(x@),
{
    if x.len() == 0 || !ident_start_e(x[0]) {
        return false;
    }
    let mut i: usize = 1;
    while i < x.len()
        invariant
            1 <= i <= x.len(),
            forall|j: int| 0 < j < i ==> ident_char(#[trigger] x@[j]),
        decreases x.len() - i,
    {
        if !ident_char_e(x[i]) {
            return false;
        }
        i += 1;
    }
    kw_of_e(x).is_none()
}

// ------------------------------------------------------------------ 字句解析器

pub open spec fn app(u: Seq<Tok>, o: Option<Seq<Tok>>) -> Option<Seq<Tok>> {
    match o {
        Some(w) => Some(u + w),
        None => None,
    }
}

pub open spec fn sfx(s: Seq<char>, i: int) -> Seq<char> {
    s.subrange(i, s.len() as int)
}

proof fn sfx_sfx(s: Seq<char>, i: int, j: int)
    requires
        0 <= i <= i + j <= s.len(),
    ensures
        sfx(sfx(s, i), j) == sfx(s, i + j),
        sfx(s, i).len() == s.len() - i,
{
    assert(sfx(sfx(s, i), j) =~= sfx(s, i + j));
}

proof fn push_tok(out: Seq<ETok>, t: ETok)
    ensures
        vtoks(out.push(t)) == vtoks(out) + seq![vtok(t)],
{
    assert(vtoks(out.push(t)) =~= vtoks(out) + seq![vtok(t)]);
}

proof fn app_step(u: Seq<Tok>, t: Tok, o: Option<Seq<Tok>>)
    ensures
        app(u, prepend(t, o)) == app(u + seq![t], o),
{
    if let Some(w) = o {
        assert(u + (seq![t] + w) =~= (u + seq![t]) + w);
    }
}

/// 位置 i から識別子文字の続く終わり。
fn scan_word(s: &Vec<char>, i: usize) -> (j: usize)
    requires
        i < s.len(),
    ensures
        i < j <= s.len(),
        wend(sfx(s@, i as int), 1) == j - i,
{
    let n = s.len();
    let ghost t = sfx(s@, i as int);
    let mut j = i + 1;
    while j < n && ident_char_e(s[j])
        invariant
            i < j <= n,
            n == s.len(),
            t == sfx(s@, i as int),
            wend(t, 1) == wend(t, (j - i) as nat),
        decreases n - j,
    {
        proof {
            assert(t[(j - i) as int] == s@[j as int]);
        }
        j += 1;
    }
    proof {
        if j < n {
            assert(t[(j - i) as int] == s@[j as int]);
        }
    }
    j
}

fn scan_digits(s: &Vec<char>, i: usize, k: usize) -> (j: usize)
    requires
        i <= k <= s.len(),
    ensures
        k <= j <= s.len(),
        dend(sfx(s@, i as int), (k - i) as nat) == j - i,
        forall|m: int| k <= m < j ==> is_digit(#[trigger] s@[m]),
{
    let n = s.len();
    let ghost t = sfx(s@, i as int);
    let mut j = k;
    while j < n && is_digit_e(s[j])
        invariant
            k <= j <= n,
            n == s.len(),
            i <= k,
            t == sfx(s@, i as int),
            dend(t, (k - i) as nat) == dend(t, (j - i) as nat),
            forall|m: int| k <= m < j ==> is_digit(#[trigger] s@[m]),
        decreases n - j,
    {
        proof {
            assert(t[(j - i) as int] == s@[j as int]);
        }
        j += 1;
    }
    proof {
        if j < n {
            assert(t[(j - i) as int] == s@[j as int]);
        }
    }
    j
}

fn scan_comment(s: &Vec<char>, i: usize, k: usize) -> (j: usize)
    requires
        i <= k <= s.len(),
    ensures
        k <= j <= s.len(),
        cend(sfx(s@, i as int), (k - i) as nat) == j - i,
{
    let n = s.len();
    let ghost t = sfx(s@, i as int);
    let mut j = k;
    while j < n && s[j] != '\n' && s[j] != '\r'
        invariant
            k <= j <= n,
            n == s.len(),
            i <= k,
            t == sfx(s@, i as int),
            cend(t, (k - i) as nat) == cend(t, (j - i) as nat),
        decreases n - j,
    {
        proof {
            assert(t[(j - i) as int] == s@[j as int]);
        }
        j += 1;
    }
    proof {
        if j < n {
            assert(t[(j - i) as int] == s@[j as int]);
        }
    }
    j
}

proof fn nat_val_one(s: Seq<char>, a: int)
    requires
        0 <= a < s.len(),
        is_digit(s[a]),
    ensures
        nat_val(s.subrange(a, a + 1)) == Some(dval(s[a]) as nat),
{
    digit_char(s[a]);
    let t = s.subrange(a, a + 1);
    assert(t.last() == s[a]);
}

proof fn nat_val_step(s: Seq<char>, a: int, k: int, v: nat)
    requires
        0 <= a < k < s.len(),
        is_digit(s[k]),
        nat_val(s.subrange(a, k)) == Some(v),
    ensures
        nat_val(s.subrange(a, k + 1)) == Some(v * 10 + dval(s[k]) as nat),
{
    digit_char(s[k]);
    let t = s.subrange(a, k + 1);
    assert(t.last() == s[k]);
    assert(t.drop_last() =~= s.subrange(a, k));
}

/// s[a..b] の数字列の値。
fn digits_value(s: &Vec<char>, a: usize, b: usize) -> (r: Int)
    requires
        a < b <= s.len(),
        forall|m: int| a <= m < b ==> is_digit(#[trigger] s@[m]),
    ensures
        nat_val(s@.subrange(a as int, b as int)) == Some(r@ as nat),
        r@ >= 0,
{
    let ten = Int::from_u64(10);
    let mut acc = Int::from_u64(dval_e(s[a]));
    proof {
        nat_val_one(s@, a as int);
    }
    let mut k = a + 1;
    while k < b
        invariant
            a < k <= b,
            b <= s.len(),
            forall|m: int| a <= m < b ==> is_digit(#[trigger] s@[m]),
            acc@ >= 0,
            nat_val(s@.subrange(a as int, k as int)) == Some(acc@ as nat),
            ten@ == 10,
        decreases b - k,
    {
        let dk = Int::from_u64(dval_e(s[k]));
        proof {
            nat_val_step(s@, a as int, k as int, acc@ as nat);
            digit_char(s@[k as int]);
        }
        acc = acc.mul(&ten).add(&dk);
        k += 1;
    }
    acc
}

pub fn unesc_e(x: char, q: char) -> (r: Option<char>)
    ensures
        r == unesc(x, q),
{
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

pub fn lit_ok_e(c: char) -> (r: bool)
    ensures
        r == lit_ok(c),
{
    (c as u32) >= 0x20 || c == '\n' || c == '\t' || c == '\r'
}

pub fn str_ok_e(w: &Vec<char>) -> (r: bool)
    ensures
        r == str_ok(w@),
{
    let mut i: usize = 0;
    while i < w.len()
        invariant
            i <= w.len(),
            forall|j: int| 0 <= j < i ==> lit_ok(#[trigger] w@[j]),
        decreases w.len() - i,
    {
        if !lit_ok_e(w[i]) {
            return false;
        }
        i += 1;
    }
    true
}

/// 読み終えた中身 a の後に、残りを読んだ結果 o を続ける。
pub open spec fn sapp(a: Seq<char>, o: Option<(Seq<char>, nat)>) -> Option<(Seq<char>, nat)> {
    match o {
        Some((w, j)) => Some((a + w, j)),
        None => None,
    }
}

proof fn sapp_step(a: Seq<char>, c: char, o: Option<(Seq<char>, nat)>)
    ensures
        sapp(a, match o {
            Some((w, j)) => Some((seq![c] + w, j)),
            None => None,
        }) == sapp(a.push(c), o),
{
    if let Some((w, j)) = o {
        assert(a + (seq![c] + w) =~= a.push(c) + w);
    }
}

/// 文字列リテラルの中身を読む（spec の slit）。t = s[i..] の相対位置 k - i から。
fn scan_str(s: &Vec<char>, i: usize, k: usize) -> (r: Option<(Vec<char>, usize)>)
    requires
        i < k <= s.len(),
    ensures
        match r {
            Some((w, j)) => slit(sfx(s@, i as int), (k - i) as nat) == Some((w@, (j - i) as nat)) && k < j <= s.len(),
            None => slit(sfx(s@, i as int), (k - i) as nat) is None,
        },
{
    let n = s.len();
    let ghost t = sfx(s@, i as int);
    let mut acc: Vec<char> = Vec::new();
    let mut m = k;
    proof {
        if let Some((w, j)) = slit(t, (k - i) as nat) {
            assert(Seq::<char>::empty() + w =~= w);
        }
    }
    while m < n
        invariant
            i < k <= m <= n,
            n == s.len(),
            t == sfx(s@, i as int),
            t.len() == n - i,
            slit(t, (k - i) as nat) == sapp(acc@, slit(t, (m - i) as nat)),
        decreases n - m,
    {
        let c = s[m];
        proof {
            assert(t[(m - i) as int] == s@[m as int]);
        }
        if c == '"' {
            proof {
                assert(acc@ + Seq::<char>::empty() =~= acc@);
            }
            return Some((acc, m + 1));
        } else if c == '\\' {
            if m + 1 >= n {
                return None;
            }
            proof {
                assert(t[(m - i + 1) as int] == s@[m + 1]);
            }
            match unesc_e(s[m + 1], '"') {
                Some(x) => {
                    proof {
                        sapp_step(acc@, x, slit(t, (m - i + 2) as nat));
                    }
                    acc.push(x);
                    m = m + 2;
                },
                None => return None,
            }
        } else if (c as u32) < 0x20 {
            return None;
        } else {
            proof {
                sapp_step(acc@, c, slit(t, (m - i + 1) as nat));
            }
            acc.push(c);
            m = m + 1;
        }
    }
    None
}

#[verifier::rlimit(40)]
pub fn lex_e(s: &Vec<char>) -> (r: Option<Vec<ETok>>)
    ensures
        match r {
            Some(ts) => lex(s@) == Some(vtoks(ts@)) && ts@.len() <= s@.len(),
            None => lex(s@) is None,
        },
{
    let n = s.len();
    let mut out: Vec<ETok> = Vec::new();
    let mut i: usize = 0;
    proof {
        assert(sfx(s@, 0) =~= s@);
        assert(vtoks(out@) =~= Seq::<Tok>::empty());
        if let Some(w) = lex(s@) {
            assert(Seq::<Tok>::empty() + w =~= w);
        }
    }
    while i < n
        invariant
            i <= n,
            n == s.len(),
            lex(s@) == app(vtoks(out@), lex(sfx(s@, i as int))),
            out@.len() <= i,
        decreases n - i,
    {
        let ghost t = sfx(s@, i as int);
        proof {
            assert(t[0] == s@[i as int]);
            assert(t.len() == n - i);
        }
        let c = s[i];
        if is_ws_e(c) {
            proof {
                sfx_sfx(s@, i as int, 1);
            }
            i += 1;
        } else if c == '/' {
            if i + 1 < n && s[i + 1] == '/' {
                proof {
                    assert(t[1] == s@[i + 1]);
                }
                let j = scan_comment(s, i, i + 2);
                proof {
                    sfx_sfx(s@, i as int, (j - i) as int);
                }
                i = j;
            } else {
                return None;
            }
        } else if ident_start_e(c) {
            let j = scan_word(s, i);
            let mut w: Vec<char> = Vec::new();
            let mut m = i;
            while m < j
                invariant
                    i <= m <= j,
                    j <= n,
                    n == s.len(),
                    w@ == s@.subrange(i as int, m as int),
                decreases j - m,
            {
                w.push(s[m]);
                m += 1;
                proof {
                    assert(w@ =~= s@.subrange(i as int, m as int));
                }
            }
            proof {
                assert(t.subrange(0, (j - i) as int) =~= w@);
                sfx_sfx(s@, i as int, (j - i) as int);
            }
            let tok = match kw_of_e(&w) {
                Some(k) => ETok::Kw(k),
                None => ETok::Id(w),
            };
            proof {
                app_step(vtoks(out@), vtok(tok), lex(sfx(s@, j as int)));
                push_tok(out@, tok);
            }
            out.push(tok);
            i = j;
        } else if c == '-' && i + 1 < n && s[i + 1] == '>' {
            proof {
                assert(t[1] == s@[i + 1]);
                sfx_sfx(s@, i as int, 2);
                app_step(vtoks(out@), Tok::Arrow, lex(sfx(s@, i + 2)));
                push_tok(out@, ETok::Arrow);
            }
            out.push(ETok::Arrow);
            i = i + 2;
        } else if is_digit_e(c) || (c == '-' && i + 1 < n && is_digit_e(s[i + 1])) {
            proof {
                if c == '-' {
                    assert(t[1] == s@[i + 1]);
                }
            }
            let d0 = if c == '-' { i + 1 } else { i };
            let j = scan_digits(s, i, d0);
            if j == d0 {
                return None;
            }
            proof {
                assert(t[(d0 - i) as int] == s@[d0 as int]);
            }
            if s[d0] == '0' && (j - d0 > 1 || c == '-') {
                return None;
            }
            if j < n && (ident_start_e(s[j]) || s[j] == '-' || s[j] == '.') {
                proof {
                    assert(t[(j - i) as int] == s@[j as int]);
                }
                return None;
            }
            proof {
                if j < n {
                    assert(t[(j - i) as int] == s@[j as int]);
                }
            }
            let v = digits_value(s, d0, j);
            let val = if c == '-' { v.neg() } else { v };
            proof {
                let ds = t.subrange(0, (j - i) as int);
                if c == '-' {
                    assert(ds.drop_first() =~= s@.subrange(d0 as int, j as int));
                    assert(ds[0] == '-');
                } else {
                    assert(ds =~= s@.subrange(d0 as int, j as int));
                    assert(ds[0] == s@[i as int]);
                }
                assert(int_val(ds) == Some(val@));
                sfx_sfx(s@, i as int, (j - i) as int);
                app_step(vtoks(out@), Tok::Int(val@), lex(sfx(s@, j as int)));
                push_tok(out@, ETok::Int(val));
            }
            out.push(ETok::Int(val));
            i = j;
        } else if is_sym_e(c) {
            proof {
                sfx_sfx(s@, i as int, 1);
                app_step(vtoks(out@), Tok::Sym(c), lex(sfx(s@, i + 1)));
                push_tok(out@, ETok::Sym(c));
            }
            out.push(ETok::Sym(c));
            i += 1;
        } else if c == '\'' {
            if n - i > 2 && s[i + 1] != '\\' && s[i + 1] != '\'' && (s[i + 1] as u32) >= 0x20 && s[i + 2] == '\'' {
                let x = s[i + 1];
                proof {
                    assert(t[1] == s@[i + 1]);
                    assert(t[2] == s@[i + 2]);
                    sfx_sfx(s@, i as int, 3);
                    app_step(vtoks(out@), Tok::Chr(x), lex(sfx(s@, i + 3)));
                    push_tok(out@, ETok::Chr(x));
                }
                out.push(ETok::Chr(x));
                i = i + 3;
            } else if n - i > 3 && s[i + 1] == '\\' && s[i + 3] == '\'' {
                proof {
                    assert(t[1] == s@[i + 1]);
                    assert(t[2] == s@[i + 2]);
                    assert(t[3] == s@[i + 3]);
                }
                match unesc_e(s[i + 2], '\'') {
                    Some(x) => {
                        proof {
                            sfx_sfx(s@, i as int, 4);
                            app_step(vtoks(out@), Tok::Chr(x), lex(sfx(s@, i + 4)));
                            push_tok(out@, ETok::Chr(x));
                        }
                        out.push(ETok::Chr(x));
                        i = i + 4;
                    },
                    None => return None,
                }
            } else {
                proof {
                    if i + 1 < n {
                        assert(t[1] == s@[i + 1]);
                    }
                    if i + 2 < n {
                        assert(t[2] == s@[i + 2]);
                    }
                    if i + 3 < n {
                        assert(t[3] == s@[i + 3]);
                    }
                }
                return None;
            }
        } else if c == '"' {
            match scan_str(s, i, i + 1) {
                Some((w, j)) => {
                    proof {
                        sfx_sfx(s@, i as int, (j - i) as int);
                        app_step(vtoks(out@), Tok::Str(w@), lex(sfx(s@, j as int)));
                        push_tok(out@, ETok::Str(w));
                    }
                    out.push(ETok::Str(w));
                    i = j;
                },
                None => return None,
            }
        } else {
            return None;
        }
    }
    proof {
        assert(sfx(s@, n as int) =~= Seq::<char>::empty());
        assert(vtoks(out@) + Seq::<Tok>::empty() =~= vtoks(out@));
    }
    Some(out)
}

// ------------------------------------------------------------------ 構文解析器

/// 入力 token 数の上限（位置の加算が溢れないため）。
pub open spec fn small(ts: Seq<ETok>) -> bool {
    ts.len() < 0x1000_0000
}

fn sym_e(ts: &Vec<ETok>, i: usize, c: char) -> (r: bool)
    requires
        small(ts@),
    ensures
        r == sym(vtoks(ts@), i as nat, c),
{
    if i < ts.len() {
        proof {
            assert(vtoks(ts@)[i as int] == vtok(ts@[i as int]));
        }
        match &ts[i] {
            ETok::Sym(x) => *x == c,
            _ => false,
        }
    } else {
        false
    }
}

fn kwat_e(ts: &Vec<ETok>, i: usize, k: Kw) -> (r: bool)
    requires
        small(ts@),
        k == Kw::Fn || k == Kw::Entry || k == Kw::In || k == Kw::Ok || k == Kw::Err || k == Kw::Some
            || k == Kw::None,
    ensures
        r == kwat(vtoks(ts@), i as nat, k),
{
    if i < ts.len() {
        proof {
            assert(vtoks(ts@)[i as int] == vtok(ts@[i as int]));
        }
        match (&ts[i], k) {
            (ETok::Kw(Kw::Fn), Kw::Fn) => true,
            (ETok::Kw(Kw::Entry), Kw::Entry) => true,
            (ETok::Kw(Kw::In), Kw::In) => true,
            (ETok::Kw(Kw::Ok), Kw::Ok) => true,
            (ETok::Kw(Kw::Err), Kw::Err) => true,
            (ETok::Kw(Kw::Some), Kw::Some) => true,
            (ETok::Kw(Kw::None), Kw::None) => true,
            _ => false,
        }
    } else {
        false
    }
}

fn idt_e(ts: &Vec<ETok>, i: usize) -> (r: Option<Vec<char>>)
    requires
        small(ts@),
    ensures
        match r {
            Some(x) => idt(vtoks(ts@), i as nat) == Some(x@),
            None => idt(vtoks(ts@), i as nat) is None,
        },
{
    if i < ts.len() {
        proof {
            assert(vtoks(ts@)[i as int] == vtok(ts@[i as int]));
        }
        match &ts[i] {
            ETok::Id(x) => if ident_ok_e(x) {
                Some(clone_chars(x))
            } else {
                None
            },
            _ => None,
        }
    } else {
        None
    }
}

fn soft_e(k: Kw) -> (r: bool)
    ensures
        r == soft(k),
{
    match k {
        Kw::List | Kw::Some | Kw::None | Kw::Pair | Kw::Entry | Kw::Ok | Kw::Err => true,
        Kw::Map | Kw::Filter | Kw::Any | Kw::All | Kw::Find | Kw::SortBy | Kw::Loop => true,
        Kw::Dict | Kw::DictGet | Kw::DictPut | Kw::DictRemove | Kw::DictHas | Kw::DictSize | Kw::DictKeys
            | Kw::DictValues | Kw::DictEntries | Kw::DictFrom => true,
        _ => builtin_of(k).is_some(),
    }
}

fn kwt_e(k: Kw) -> (r: Vec<char>)
    ensures
        r@ == kwt(k),
{
    let mut v = Vec::new();
    push_kw(&mut v, k);
    proof {
        assert(v@ =~= kwt(k));
    }
    v
}

/// 位置 i の変数・引数・束縛の名前（IDENT か文脈キーワード）。
fn bdt_e(ts: &Vec<ETok>, i: usize) -> (r: Option<Vec<char>>)
    requires
        small(ts@),
    ensures
        match r {
            Some(x) => bdt(vtoks(ts@), i as nat) == Some(x@),
            None => bdt(vtoks(ts@), i as nat) is None,
        },
{
    if i < ts.len() {
        proof {
            assert(vtoks(ts@)[i as int] == vtok(ts@[i as int]));
        }
        match &ts[i] {
            ETok::Id(x) => if ident_ok_e(x) {
                Some(clone_chars(x))
            } else {
                None
            },
            ETok::Kw(k) => if soft_e(*k) {
                Some(kwt_e(*k))
            } else {
                None
            },
            _ => None,
        }
    } else {
        None
    }
}

pub fn pt_e(ts: &Vec<ETok>, i: usize, d: usize) -> (r: Option<(Ty, usize)>)
    requires
        small(ts@),
        i <= ts.len(),
    ensures
        match r {
            Some((t, j)) => pt(vtoks(ts@), i as nat, d as nat) == Some((t, j as nat)) && j <= ts.len(),
            None => pt(vtoks(ts@), i as nat, d as nat) is None,
        },
    decreases d,
{
    let ghost tv = vtoks(ts@);
    if d == 0 || i >= ts.len() {
        return None;
    }
    proof {
        assert(tv[i as int] == vtok(ts@[i as int]));
    }
    let k = match &ts[i] {
        ETok::Kw(k) => *k,
        _ => return None,
    };
    match k {
        Kw::TInt => Some((Ty::Int, i + 1)),
        Kw::TBool => Some((Ty::Bool, i + 1)),
        Kw::TUnit => Some((Ty::Unit, i + 1)),
        Kw::TChar => Some((Ty::Char, i + 1)),
        Kw::TString => Some((Ty::List(Box::new(Ty::Char)), i + 1)),
        Kw::TList | Kw::TOption => {
            if !sym_e(ts, i + 1, '<') {
                return None;
            }
            match pt_e(ts, i + 2, d - 1) {
                Some((a, j)) => if sym_e(ts, j, '>') {
                    let t = match k {
                        Kw::TList => match a {
                            Ty::Char => return None,
                            _ => Ty::List(Box::new(a)),
                        },
                        _ => Ty::Option(Box::new(a)),
                    };
                    Some((t, j + 1))
                } else {
                    None
                },
                None => None,
            }
        },
        Kw::TPair | Kw::TResult => {
            if !sym_e(ts, i + 1, '<') {
                return None;
            }
            match pt_e(ts, i + 2, d - 1) {
                Some((a, j)) => if sym_e(ts, j, ',') {
                    match pt_e(ts, j + 1, d - 1) {
                        Some((b, m)) => if sym_e(ts, m, '>') {
                            Some((
                                match k {
                                    Kw::TPair => Ty::Pair(Box::new(a), Box::new(b)),
                                    _ => Ty::Result(Box::new(a), Box::new(b)),
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
        },
        _ => None,
    }
}

pub open spec fn pe_ok(ts: Seq<ETok>, i: usize, d: usize, td: usize, r: Option<(SExpr, usize)>) -> bool {
    match r {
        Some((e, j)) => pe(vtoks(ts), i as nat, d as nat, td as nat) == Some((vx(e), j as nat)) && j <= ts.len(),
        None => pe(vtoks(ts), i as nat, d as nat, td as nat) is None,
    }
}

pub open spec fn pp_ok(ts: Seq<ETok>, i: usize, d: usize, td: usize, r: Option<(SExpr, usize)>) -> bool {
    match r {
        Some((e, j)) => pp(vtoks(ts), i as nat, d as nat, td as nat) == Some((vx(e), j as nat)) && j <= ts.len(),
        None => pp(vtoks(ts), i as nat, d as nat, td as nat) is None,
    }
}

/// 基本の式（後置の `.f` の並びを含まない）。
pub fn pp_e(ts: &Vec<ETok>, i: usize, d: usize, td: usize) -> (r: Option<(SExpr, usize)>)
    requires
        small(ts@),
        i <= ts.len(),
    ensures
        pp_ok(ts@, i, d, td, r),
    decreases d, 1nat,
{
    let ghost tv = vtoks(ts@);
    if d == 0 || i >= ts.len() {
        return None;
    }
    proof {
        assert(tv[i as int] == vtok(ts@[i as int]));
    }
    match &ts[i] {
        ETok::Int(n) => Some((SExpr::Int(n.copy()), i + 1)),
        ETok::Chr(c) => if lit_ok_e(*c) {
            Some((SExpr::Chr(*c), i + 1))
        } else {
            None
        },
        ETok::Str(w) => if str_ok_e(w) {
            Some((SExpr::Str(clone_chars(w)), i + 1))
        } else {
            None
        },
        ETok::Id(x) => if mword_e(x) {
            proof {
                mword_word();
                reveal_with_fuel(pp, 1);
            }
            match pm_e(ts, i, d, td) {
                Some(r) => Some(r),
                None => pid_e(ts, i, d, td),
            }
        } else {
            pid_e(ts, i, d, td)
        },
        ETok::Kw(k) => if soft_e(*k) && !sym_e(ts, i + 1, '(') && !sym_e(ts, i + 1, '<') {
            Some((SExpr::Var(kwt_e(*k)), i + 1))
        } else {
            match *k {
            Kw::True => Some((SExpr::Bool(true), i + 1)),
            Kw::False => Some((SExpr::Bool(false), i + 1)),
            Kw::Unit => Some((SExpr::Unit, i + 1)),
            Kw::List => pe_list_e(ts, i, d, td),
            Kw::Some => pe_some_e(ts, i, d, td),
            Kw::None => pe_none_e(ts, i, d, td),
            Kw::Pair => pe_pair_e(ts, i, d, td),
            Kw::Let => pe_let_e(ts, i, d, td),
            Kw::If => pe_if_e(ts, i, d, td),
            Kw::Fold => pe_fold_e(ts, i, d, td),
            Kw::MatchOption => pe_match_e(ts, i, d, td),
            Kw::Ok | Kw::Err => pe_inj_e(ts, i, d, td),
            Kw::MatchResult => pe_matchr_e(ts, i, d, td),
            Kw::Map => pe_hof_e(ts, i, d, td, Hf::Map),
            Kw::Filter => pe_hof_e(ts, i, d, td, Hf::Filter),
            Kw::Any => pe_hof_e(ts, i, d, td, Hf::Any),
            Kw::All => pe_hof_e(ts, i, d, td, Hf::All),
            Kw::Find => pe_hof_e(ts, i, d, td, Hf::Find),
            Kw::SortBy => pe_hof_e(ts, i, d, td, Hf::SortBy),
            Kw::Loop => pe_loop_e(ts, i, d, td),
            Kw::Dict => pe_dictnew_e(ts, i, d, td),
            Kw::DictGet => pe_dictop_e(ts, i, d, td, Dop::Get),
            Kw::DictPut => pe_dictop_e(ts, i, d, td, Dop::Put),
            Kw::DictRemove => pe_dictop_e(ts, i, d, td, Dop::Remove),
            Kw::DictHas => pe_dictop_e(ts, i, d, td, Dop::Has),
            Kw::DictSize => pe_dictop_e(ts, i, d, td, Dop::Size),
            Kw::DictKeys => pe_dictop_e(ts, i, d, td, Dop::Keys),
            Kw::DictValues => pe_dictop_e(ts, i, d, td, Dop::Values),
            Kw::DictEntries => pe_dictop_e(ts, i, d, td, Dop::Entries),
            Kw::DictFrom => pe_dictop_e(ts, i, d, td, Dop::From),
            _ => pe_builtin_e(ts, i, d, td),
            }
        },
        _ => None,
    }
}

/// 識別子で始まる式（呼び出し、レコード式、変数）。
fn pid_e(ts: &Vec<ETok>, i: usize, d: usize, td: usize) -> (r: Option<(SExpr, usize)>)
    requires
        small(ts@),
        i < ts.len(),
        d > 0,
        ts@[i as int] is Id,
        vtok(ts@[i as int]) == Tok::Id(mword()) ==> pm(vtoks(ts@), i as nat, d as nat, td as nat) is None,
    ensures
        pp_ok(ts@, i, d, td, r),
    decreases d, 0nat,
{
    let ghost tv = vtoks(ts@);
    proof {
        assert(tv[i as int] == vtok(ts@[i as int]));
    }
    let x = match &ts[i] {
        ETok::Id(x) => x,
        _ => return None,
    };
    if !ident_ok_e(x) {
        None
    } else if sym_e(ts, i + 1, '(') {
        match pargs_e(ts, i + 2, d - 1, td) {
            Some((es, j)) => Some((SExpr::Call(clone_chars(x), es), j)),
            None => None,
        }
    } else if sym_e(ts, i + 1, '{') && rec_head_e(ts, i + 2) {
        match prec_e(ts, i + 2, d - 1, td) {
            Some((ns, es, b, j)) => Some((SExpr::Rec(clone_chars(x), ns, es, b), j)),
            None => None,
        }
    } else {
        Some((SExpr::Var(clone_chars(x)), i + 1))
    }
}

/// 式（後置の `.f` の並びを含む）。
pub fn pe_e(ts: &Vec<ETok>, i: usize, d: usize, td: usize) -> (r: Option<(SExpr, usize)>)
    requires
        small(ts@),
        i <= ts.len(),
    ensures
        pe_ok(ts@, i, d, td, r),
    decreases d, 2nat,
{
    match pp_e(ts, i, d, td) {
        None => None,
        Some((e, j)) => {
            let named = match idt_e(ts, j + 1) {
                Some(_) => true,
                None => false,
            };
            if recv_ok_e(&e) && j + 1 < ts.len() && sym_e(ts, j, '.') && named {
                let (fs, m) = pfs_e(ts, j);
                Some((SExpr::Fld(Box::new(e), fs), m))
            } else {
                Some((e, j))
            }
        },
    }
}

/// 後置の `.f` の受け手になれる式か（整数・let・後置は受けない）。
fn recv_ok_e(e: &SExpr) -> (r: bool)
    ensures
        r == recv_ok(vx(*e)),
{
    proof {
        reveal_with_fuel(vx, 1);
    }
    match e {
        SExpr::Int(..) | SExpr::Let(..) | SExpr::Fld(..) => false,
        _ => true,
    }
}

/// `R {` の後ろがレコード式の本体の形か（`}`、`IDENT :`、`..`）。
fn rec_head_e(ts: &Vec<ETok>, i: usize) -> (r: bool)
    requires
        small(ts@),
    ensures
        r == rec_head(vtoks(ts@), i as nat),
{
    if sym_e(ts, i, '}') || (sym_e(ts, i, '.') && sym_e(ts, i + 1, '.')) {
        return true;
    }
    match idt_e(ts, i) {
        Some(_) => sym_e(ts, i + 1, ':'),
        None => false,
    }
}

/// `"." IDENT` の並び（位置 j から）。名前の列と、並びの後の位置。
fn pfs_e(ts: &Vec<ETok>, j: usize) -> (r: (Vec<Vec<char>>, usize))
    requires
        small(ts@),
        j <= ts.len(),
    ensures
        pfs(vtoks(ts@), j as nat) == (vnames(r.0@), r.1 as nat),
        r.1 <= ts.len(),
{
    let ghost tv = vtoks(ts@);
    let mut ns: Vec<Vec<char>> = Vec::new();
    let mut k = j;
    loop
        invariant
            small(ts@),
            tv == vtoks(ts@),
            j <= k <= ts.len(),
            pfs(tv, j as nat) == (vnames(ns@) + pfs(tv, k as nat).0, pfs(tv, k as nat).1),
        decreases ts.len() - k,
    {
        proof {
            reveal_with_fuel(pfs, 1);
        }
        if k + 1 < ts.len() && sym_e(ts, k, '.') {
            match idt_e(ts, k + 1) {
                Some(x) => {
                    let ghost old = ns@;
                    let ghost xv = x@;
                    ns.push(x);
                    proof {
                        assert(vnames(ns@) =~= vnames(old) + seq![xv]);
                        assert(pfs(tv, k as nat).0 =~= seq![xv] + pfs(tv, (k + 2) as nat).0);
                        assert(vnames(ns@) + pfs(tv, (k + 2) as nat).0 =~= vnames(old) + pfs(tv, k as nat).0);
                    }
                    k = k + 2;
                },
                None => {
                    proof {
                        assert(pfs(tv, k as nat) == (Seq::<Seq<char>>::empty(), k as nat));
                        assert(vnames(ns@) + Seq::<Seq<char>>::empty() =~= vnames(ns@));
                    }
                    return (ns, k);
                },
            }
        } else {
            proof {
                assert(pfs(tv, k as nat) == (Seq::<Seq<char>>::empty(), k as nat));
                assert(vnames(ns@) + Seq::<Seq<char>>::empty() =~= vnames(ns@));
            }
            return (ns, k);
        }
    }
}

/// レコード式の本体（`{` の後）。
fn prec_e(ts: &Vec<ETok>, i: usize, d: usize, td: usize) -> (r: Option<(Vec<Vec<char>>, Vec<SExpr>, Option<Box<SExpr>>, usize)>)
    requires
        small(ts@),
        i <= ts.len(),
    ensures
        match r {
            Some((ns, es, b, j)) => prec(vtoks(ts@), i as nat, d as nat, td as nat)
                == Some((vfields(ns@, es@), vbase(b), j as nat)) && j <= ts.len() && ns@.len() == es@.len(),
            None => prec(vtoks(ts@), i as nat, d as nat, td as nat) is None,
        },
    decreases d, 4nat,
{
    if sym_e(ts, i, '}') {
        let ns: Vec<Vec<char>> = Vec::new();
        let es: Vec<SExpr> = Vec::new();
        proof {
            assert(vfields(ns@, es@) =~= Seq::<(Seq<char>, Sx)>::empty());
        }
        return Some((ns, es, None, i + 1));
    }
    prest_e(ts, i, d, td)
}

/// レコード式の字段の並びと省略できる base（位置 i から、閉じ括弧まで）。
fn prest_e(ts: &Vec<ETok>, i: usize, d: usize, td: usize) -> (r: Option<(Vec<Vec<char>>, Vec<SExpr>, Option<Box<SExpr>>, usize)>)
    requires
        small(ts@),
        i <= ts.len(),
    ensures
        match r {
            Some((ns, es, b, j)) => prest(vtoks(ts@), i as nat, d as nat, td as nat)
                == Some((vfields(ns@, es@), vbase(b), j as nat)) && j <= ts.len() && ns@.len() == es@.len(),
            None => prest(vtoks(ts@), i as nat, d as nat, td as nat) is None,
        },
    decreases d, 3nat,
{
    let ghost tv = vtoks(ts@);
    let mut ns: Vec<Vec<char>> = Vec::new();
    let mut es: Vec<SExpr> = Vec::new();
    let mut k = i;
    proof {
        assert(vfields(ns@, es@) =~= Seq::<(Seq<char>, Sx)>::empty());
    }
    loop
        invariant
            small(ts@),
            tv == vtoks(ts@),
            k <= ts.len(),
            ns@.len() == es@.len(),
            prest(tv, i as nat, d as nat, td as nat) == catr(vfields(ns@, es@), prest(tv, k as nat, d as nat, td as nat)),
        decreases ts.len() - k,
    {
        proof {
            reveal_with_fuel(prest, 1);
        }
        if sym_e(ts, k, '.') && sym_e(ts, k + 1, '.') {
            match pe_e(ts, k + 2, d, td) {
                None => return None,
                Some((b, j)) => {
                    if sym_e(ts, j, '}') {
                        proof {
                            assert(vfields(ns@, es@) + Seq::<(Seq<char>, Sx)>::empty() =~= vfields(ns@, es@));
                        }
                        return Some((ns, es, Some(Box::new(b)), j + 1));
                    }
                    return None;
                },
            }
        }
        let f = match idt_e(ts, k) {
            Some(f) => f,
            None => return None,
        };
        if !sym_e(ts, k + 1, ':') {
            return None;
        }
        match pe_e(ts, k + 2, d, td) {
            None => return None,
            Some((v, j)) => {
                if sym_e(ts, j, '}') {
                    let ghost bn = ns@;
                    let ghost be = es@;
                    let ghost fv = f@;
                    let ghost vv = vx(v);
                    ns.push(f);
                    es.push(v);
                    proof {
                        assert(vfields(ns@, es@) =~= vfields(bn, be) + seq![(fv, vv)]);
                    }
                    return Some((ns, es, None, j + 1));
                } else if sym_e(ts, j, ',') && k < j {
                    let ghost bn = ns@;
                    let ghost be = es@;
                    let ghost fv = f@;
                    let ghost vv = vx(v);
                    ns.push(f);
                    es.push(v);
                    proof {
                        assert(vfields(ns@, es@) =~= vfields(bn, be) + seq![(fv, vv)]);
                        catr_app(vfields(bn, be), seq![(fv, vv)], prest(tv, (j + 1) as nat, d as nat, td as nat));
                    }
                    k = j + 1;
                } else {
                    return None;
                }
            },
        }
    }
}

/// レコード型の字段の並び（位置 i から、閉じ括弧まで）。
fn pfds_e(ts: &Vec<ETok>, i: usize, td: usize) -> (r: Option<(Vec<(Vec<char>, Ty)>, bool, usize)>)
    requires
        small(ts@),
        i <= ts.len(),
    ensures
        match r {
            Some((fs, tc, j)) => pfds(vtoks(ts@), i as nat, td as nat) == Some((vps(fs@), tc, j as nat)) && j <= ts.len(),
            None => pfds(vtoks(ts@), i as nat, td as nat) is None,
        },
{
    let ghost tv = vtoks(ts@);
    let mut fs: Vec<(Vec<char>, Ty)> = Vec::new();
    let mut k = i;
    proof {
        assert(vps(fs@) =~= Seq::<(Seq<char>, Ty)>::empty());
    }
    loop
        invariant
            small(ts@),
            tv == vtoks(ts@),
            k <= ts.len(),
            pfds(tv, i as nat, td as nat) == catf(vps(fs@), pfds(tv, k as nat, td as nat)),
        decreases ts.len() - k,
    {
        proof {
            reveal_with_fuel(pfds, 1);
        }
        let f = match idt_e(ts, k) {
            Some(f) => f,
            None => return None,
        };
        if !sym_e(ts, k + 1, ':') {
            return None;
        }
        match pt_e(ts, k + 2, td) {
            None => return None,
            Some((t, j)) => {
                if sym_e(ts, j, '}') {
                    let ghost bf = fs@;
                    let ghost fv = f@;
                    fs.push((f, t));
                    proof {
                        assert(vps(fs@) =~= vps(bf) + seq![(fv, fs@.last().1)]);
                    }
                    return Some((fs, false, j + 1));
                } else if sym_e(ts, j, ',') && k < j {
                    if sym_e(ts, j + 1, '}') {
                        let ghost bf = fs@;
                        let ghost fv = f@;
                        fs.push((f, t));
                        proof {
                            assert(vps(fs@) =~= vps(bf) + seq![(fv, fs@.last().1)]);
                        }
                        return Some((fs, true, j + 2));
                    }
                    let ghost bf = fs@;
                    let ghost fv = f@;
                    fs.push((f, t));
                    proof {
                        assert(vps(fs@) =~= vps(bf) + seq![(fv, fs@.last().1)]);
                        catf_app(vps(bf), seq![(fv, fs@.last().1)], pfds(tv, (j + 1) as nat, td as nat));
                    }
                    k = j + 1;
                } else {
                    return None;
                }
            },
        }
    }
}

/// 宣言の先頭の文脈語 `type`（予約語ではない識別子として読む）。
fn tyw_e(ts: &Vec<ETok>, i: usize) -> (r: bool)
    requires
        small(ts@),
    ensures
        r == (i < ts.len() && vtok(ts@[i as int]) == Tok::Id(tyw())),
{
    if i < ts.len() {
        match &ts[i] {
            ETok::Id(x) => {
                let mut w: Vec<char> = Vec::new();
                w.push('t');
                w.push('y');
                w.push('p');
                w.push('e');
                proof {
                    assert(w@ =~= tyw());
                }
                eq_chars(x, &w)
            },
            _ => false,
        }
    } else {
        false
    }
}

/// 字段の並びの連結（prest の結果の前に字段を付ける）。
pub open spec fn catr(u: Seq<(Seq<char>, Sx)>, o: Option<(Seq<(Seq<char>, Sx)>, Option<Box<Sx>>, nat)>) -> Option<
    (Seq<(Seq<char>, Sx)>, Option<Box<Sx>>, nat),
> {
    match o {
        Some((w, b, m)) => Some((u + w, b, m)),
        None => None,
    }
}

/// 型の字段の並びの連結（pfds の結果の前に字段を付ける）。
pub open spec fn catf(u: Seq<(Seq<char>, Ty)>, o: Option<(Seq<(Seq<char>, Ty)>, bool, nat)>) -> Option<
    (Seq<(Seq<char>, Ty)>, bool, nat),
> {
    match o {
        Some((w, tc, m)) => Some((u + w, tc, m)),
        None => None,
    }
}

proof fn catr_app(u: Seq<(Seq<char>, Sx)>, w: Seq<(Seq<char>, Sx)>, o: Option<(Seq<(Seq<char>, Sx)>, Option<Box<Sx>>, nat)>)
    ensures
        catr(u, catr(w, o)) == catr(u + w, o),
{
    match o {
        Some((x, b, m)) => {
            assert(u + (w + x) =~= (u + w) + x);
        },
        None => {},
    }
}

proof fn catf_app(u: Seq<(Seq<char>, Ty)>, w: Seq<(Seq<char>, Ty)>, o: Option<(Seq<(Seq<char>, Ty)>, bool, nat)>)
    ensures
        catf(u, catf(w, o)) == catf(u + w, o),
{
    match o {
        Some((x, tc, m)) => {
            assert(u + (w + x) =~= (u + w) + x);
        },
        None => {},
    }
}

/// 型の並びの連結（ptys の結果の前に型を付ける）。
pub open spec fn catt(u: Seq<Ty>, o: Option<(Seq<Ty>, nat)>) -> Option<(Seq<Ty>, nat)> {
    match o {
        Some((w, m)) => Some((u + w, m)),
        None => None,
    }
}

/// 直和型の構築子の並びの連結（pvars の結果の前に構築子を付ける）。
pub open spec fn catvs(u: Seq<(Seq<char>, Seq<Ty>)>, o: Option<(Seq<(Seq<char>, Seq<Ty>)>, nat)>) -> Option<
    (Seq<(Seq<char>, Seq<Ty>)>, nat),
> {
    match o {
        Some((w, m)) => Some((u + w, m)),
        None => None,
    }
}

proof fn catt_app(u: Seq<Ty>, w: Seq<Ty>, o: Option<(Seq<Ty>, nat)>)
    ensures
        catt(u, catt(w, o)) == catt(u + w, o),
{
    match o {
        Some((x, m)) => {
            assert(u + (w + x) =~= (u + w) + x);
        },
        None => {},
    }
}

proof fn catvs_app(u: Seq<(Seq<char>, Seq<Ty>)>, w: Seq<(Seq<char>, Seq<Ty>)>, o: Option<(Seq<(Seq<char>, Seq<Ty>)>, nat)>)
    ensures
        catvs(u, catvs(w, o)) == catvs(u + w, o),
{
    match o {
        Some((x, m)) => {
            assert(u + (w + x) =~= (u + w) + x);
        },
        None => {},
    }
}

fn builtin_of(k: Kw) -> (r: Option<Builtin>)
    ensures
        r == kw_b(k),
{
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

fn pe_builtin_e(ts: &Vec<ETok>, i: usize, d: usize, td: usize) -> (r: Option<(SExpr, usize)>)
    requires
        nv(vtoks(ts@), i as nat),
        small(ts@),
        i < ts.len(),
        d > 0,
        ts@[i as int] is Kw,
        ({
            let k = ts@[i as int]->Kw_0;
            k != Kw::True && k != Kw::False && k != Kw::Unit && k != Kw::List && k != Kw::Some && k != Kw::None
                && k != Kw::Pair && k != Kw::Let && k != Kw::If && k != Kw::Fold && k != Kw::MatchOption
                && k != Kw::Ok && k != Kw::Err && k != Kw::MatchResult
                && k != Kw::Map && k != Kw::Filter && k != Kw::Any && k != Kw::All && k != Kw::Find && k != Kw::SortBy
                && k != Kw::Loop
                && k != Kw::Dict && k != Kw::DictGet && k != Kw::DictPut && k != Kw::DictRemove && k != Kw::DictHas
                && k != Kw::DictSize && k != Kw::DictKeys && k != Kw::DictValues && k != Kw::DictEntries
                && k != Kw::DictFrom
        }),
    ensures
        pp_ok(ts@, i, d, td, r),
    decreases d, 0nat,
{
    let ghost tv = vtoks(ts@);
    proof {
        assert(tv[i as int] == vtok(ts@[i as int]));
    }
    let k = match &ts[i] {
        ETok::Kw(k) => *k,
        _ => return None,
    };
    match builtin_of(k) {
        Some(b) => if sym_e(ts, i + 1, '(') {
            match pargs_e(ts, i + 2, d - 1, td) {
                Some((es, j)) => Some((SExpr::Builtin(b, es), j)),
                None => None,
            }
        } else {
            None
        },
        None => None,
    }
}

fn pe_list_e(ts: &Vec<ETok>, i: usize, d: usize, td: usize) -> (r: Option<(SExpr, usize)>)
    requires
        nv(vtoks(ts@), i as nat),
        small(ts@),
        i < ts.len(),
        d > 0,
        vtok(ts@[i as int]) == Tok::Kw(Kw::List),
    ensures
        pp_ok(ts@, i, d, td, r),
    decreases d, 0nat,
{
    let ghost tv = vtoks(ts@);
    proof {
        assert(tv[i as int] == vtok(ts@[i as int]));
    }
    if !sym_e(ts, i + 1, '<') {
        return None;
    }
    match pt_e(ts, i + 2, td) {
        Some((t, j)) => if sym_e(ts, j, '>') && sym_e(ts, j + 1, '(') {
            match pargs_e(ts, j + 2, d - 1, td) {
                Some((es, m)) => Some((SExpr::List(t, es), m)),
                None => None,
            }
        } else {
            None
        },
        None => None,
    }
}

fn pe_some_e(ts: &Vec<ETok>, i: usize, d: usize, td: usize) -> (r: Option<(SExpr, usize)>)
    requires
        nv(vtoks(ts@), i as nat),
        small(ts@),
        i < ts.len(),
        d > 0,
        vtok(ts@[i as int]) == Tok::Kw(Kw::Some),
    ensures
        pp_ok(ts@, i, d, td, r),
    decreases d, 0nat,
{
    let ghost tv = vtoks(ts@);
    proof {
        assert(tv[i as int] == vtok(ts@[i as int]));
    }
    if !sym_e(ts, i + 1, '(') {
        return None;
    }
    match pe_e(ts, i + 2, d - 1, td) {
        Some((a, j)) => if sym_e(ts, j, ')') {
            Some((SExpr::Some(Box::new(a)), j + 1))
        } else {
            None
        },
        None => None,
    }
}

fn pe_none_e(ts: &Vec<ETok>, i: usize, d: usize, td: usize) -> (r: Option<(SExpr, usize)>)
    requires
        nv(vtoks(ts@), i as nat),
        small(ts@),
        i < ts.len(),
        d > 0,
        vtok(ts@[i as int]) == Tok::Kw(Kw::None),
    ensures
        pp_ok(ts@, i, d, td, r),
    decreases d, 0nat,
{
    let ghost tv = vtoks(ts@);
    proof {
        assert(tv[i as int] == vtok(ts@[i as int]));
    }
    if !sym_e(ts, i + 1, '<') {
        return None;
    }
    match pt_e(ts, i + 2, td) {
        Some((t, j)) => if sym_e(ts, j, '>') && sym_e(ts, j + 1, '(') && sym_e(ts, j + 2, ')') {
            Some((SExpr::None(t), j + 3))
        } else {
            None
        },
        None => None,
    }
}

fn pe_pair_e(ts: &Vec<ETok>, i: usize, d: usize, td: usize) -> (r: Option<(SExpr, usize)>)
    requires
        nv(vtoks(ts@), i as nat),
        small(ts@),
        i < ts.len(),
        d > 0,
        vtok(ts@[i as int]) == Tok::Kw(Kw::Pair),
    ensures
        pp_ok(ts@, i, d, td, r),
    decreases d, 0nat,
{
    let ghost tv = vtoks(ts@);
    proof {
        assert(tv[i as int] == vtok(ts@[i as int]));
    }
    if !sym_e(ts, i + 1, '(') {
        return None;
    }
    match pe_e(ts, i + 2, d - 1, td) {
        Some((a, j)) => if sym_e(ts, j, ',') {
            match pe_e(ts, j + 1, d - 1, td) {
                Some((b, m)) => if sym_e(ts, m, ')') {
                    Some((SExpr::Pair(Box::new(a), Box::new(b)), m + 1))
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

fn pe_let_e(ts: &Vec<ETok>, i: usize, d: usize, td: usize) -> (r: Option<(SExpr, usize)>)
    requires
        small(ts@),
        i < ts.len(),
        d > 0,
        vtok(ts@[i as int]) == Tok::Kw(Kw::Let),
    ensures
        pp_ok(ts@, i, d, td, r),
    decreases d, 0nat,
{
    let ghost tv = vtoks(ts@);
    proof {
        assert(tv[i as int] == vtok(ts@[i as int]));
    }
    let x = match bdt_e(ts, i + 1) {
        Some(x) => x,
        None => return None,
    };
    if !sym_e(ts, i + 2, '=') {
        return None;
    }
    match pe_e(ts, i + 3, d - 1, td) {
        Some((a, j)) => if kwat_e(ts, j, Kw::In) {
            match pe_e(ts, j + 1, d - 1, td) {
                Some((b, m)) => Some((SExpr::Let(x, Box::new(a), Box::new(b)), m)),
                None => None,
            }
        } else {
            None
        },
        None => None,
    }
}

fn pe_if_e(ts: &Vec<ETok>, i: usize, d: usize, td: usize) -> (r: Option<(SExpr, usize)>)
    requires
        small(ts@),
        i < ts.len(),
        d > 0,
        vtok(ts@[i as int]) == Tok::Kw(Kw::If),
    ensures
        pp_ok(ts@, i, d, td, r),
    decreases d, 0nat,
{
    let ghost tv = vtoks(ts@);
    proof {
        assert(tv[i as int] == vtok(ts@[i as int]));
    }
    if !sym_e(ts, i + 1, '(') {
        return None;
    }
    let (c, j) = match pe_e(ts, i + 2, d - 1, td) {
        Some(r) => r,
        None => return None,
    };
    if !sym_e(ts, j, ',') {
        return None;
    }
    let (a, m) = match pe_e(ts, j + 1, d - 1, td) {
        Some(r) => r,
        None => return None,
    };
    if !sym_e(ts, m, ',') {
        return None;
    }
    let (b, q) = match pe_e(ts, m + 1, d - 1, td) {
        Some(r) => r,
        None => return None,
    };
    if !sym_e(ts, q, ')') {
        return None;
    }
    Some((SExpr::If(Box::new(c), Box::new(a), Box::new(b)), q + 1))
}

fn pe_fold_e(ts: &Vec<ETok>, i: usize, d: usize, td: usize) -> (r: Option<(SExpr, usize)>)
    requires
        small(ts@),
        i < ts.len(),
        d > 0,
        vtok(ts@[i as int]) == Tok::Kw(Kw::Fold),
    ensures
        pp_ok(ts@, i, d, td, r),
    decreases d, 0nat,
{
    let ghost tv = vtoks(ts@);
    proof {
        assert(tv[i as int] == vtok(ts@[i as int]));
    }
    if !sym_e(ts, i + 1, '(') {
        return None;
    }
    let (l, j) = match pe_e(ts, i + 2, d - 1, td) {
        Some(r) => r,
        None => return None,
    };
    if !sym_e(ts, j, ',') {
        return None;
    }
    let (n, m) = match pe_e(ts, j + 1, d - 1, td) {
        Some(r) => r,
        None => return None,
    };
    if m >= ts.len() || !(sym_e(ts, m, ',') && sym_e(ts, m + 1, '|')) {
        return None;
    }
    let a = match bdt_e(ts, m + 2) {
        Some(a) => a,
        None => return None,
    };
    let x = match bdt_e(ts, m + 4) {
        Some(x) => x,
        None => return None,
    };
    if !(sym_e(ts, m + 3, ',') && sym_e(ts, m + 5, '|')) {
        return None;
    }
    if m + 6 > ts.len() {
        return None;
    }
    let (b, q) = match pe_e(ts, m + 6, d - 1, td) {
        Some(r) => r,
        None => return None,
    };
    if !sym_e(ts, q, ')') {
        return None;
    }
    Some((SExpr::Fold(Box::new(l), Box::new(n), a, x, Box::new(b)), q + 1))
}

fn pe_match_e(ts: &Vec<ETok>, i: usize, d: usize, td: usize) -> (r: Option<(SExpr, usize)>)
    requires
        small(ts@),
        i < ts.len(),
        d > 0,
        vtok(ts@[i as int]) == Tok::Kw(Kw::MatchOption),
    ensures
        pp_ok(ts@, i, d, td, r),
    decreases d, 0nat,
{
    let ghost tv = vtoks(ts@);
    proof {
        assert(tv[i as int] == vtok(ts@[i as int]));
    }
    if !sym_e(ts, i + 1, '(') {
        return None;
    }
    let (m, j) = match pe_e(ts, i + 2, d - 1, td) {
        Some(r) => r,
        None => return None,
    };
    if !sym_e(ts, j, ',') {
        return None;
    }
    let (n, q) = match pe_e(ts, j + 1, d - 1, td) {
        Some(r) => r,
        None => return None,
    };
    if q >= ts.len() || !(sym_e(ts, q, ',') && sym_e(ts, q + 1, '|')) {
        return None;
    }
    let x = match bdt_e(ts, q + 2) {
        Some(x) => x,
        None => return None,
    };
    if !sym_e(ts, q + 3, '|') {
        return None;
    }
    if q + 4 > ts.len() {
        return None;
    }
    let (b, u) = match pe_e(ts, q + 4, d - 1, td) {
        Some(r) => r,
        None => return None,
    };
    if !sym_e(ts, u, ')') {
        return None;
    }
    Some((SExpr::Match(Box::new(m), Box::new(n), x, Box::new(b)), u + 1))
}

/// hof の本体（位置 i は hof の語。語の後に `(`、被験の列、`,`、`|x|`、本体、閉じ括弧）。
fn pe_hof_e(ts: &Vec<ETok>, i: usize, d: usize, td: usize, h: Hf) -> (r: Option<(SExpr, usize)>)
    requires
        small(ts@),
        i < ts.len(),
        d > 0,
        vtok(ts@[i as int]) == Tok::Kw(hkw(h)),
        sym(vtoks(ts@), (i + 1) as nat, '(') || sym(vtoks(ts@), (i + 1) as nat, '<'),
    ensures
        pp_ok(ts@, i, d, td, r),
    decreases d, 0nat,
{
    let ghost tv = vtoks(ts@);
    proof {
        assert(tv[i as int] == vtok(ts@[i as int]));
        pp_hof_unfold(tv, i as nat, d as nat, td as nat, h);
    }
    if !sym_e(ts, i + 1, '(') {
        return None;
    }
    let (l, j) = match pe_e(ts, i + 2, d - 1, td) {
        Some(r) => r,
        None => return None,
    };
    if j + 4 > ts.len() || !(sym_e(ts, j, ',') && sym_e(ts, j + 1, '|') && sym_e(ts, j + 3, '|')) {
        return None;
    }
    let x = match bdt_e(ts, j + 2) {
        Some(x) => x,
        None => return None,
    };
    let (b, m) = match pe_e(ts, j + 4, d - 1, td) {
        Some(r) => r,
        None => return None,
    };
    if !sym_e(ts, m, ')') {
        return None;
    }
    Some((SExpr::Hof(h, Box::new(l), x, Box::new(b)), m + 1))
}

/// loop の本体（位置 i は loop の語。語の後に `(`、初期値、`,`、上限、`,`、`|x|`、本体、閉じ括弧）。
fn pe_loop_e(ts: &Vec<ETok>, i: usize, d: usize, td: usize) -> (r: Option<(SExpr, usize)>)
    requires
        small(ts@),
        i < ts.len(),
        d > 0,
        vtok(ts@[i as int]) == Tok::Kw(Kw::Loop),
        sym(vtoks(ts@), (i + 1) as nat, '(') || sym(vtoks(ts@), (i + 1) as nat, '<'),
    ensures
        pp_ok(ts@, i, d, td, r),
    decreases d, 0nat,
{
    if !sym_e(ts, i + 1, '(') {
        return None;
    }
    let (a, j) = match pe_e(ts, i + 2, d - 1, td) {
        Some(r) => r,
        None => return None,
    };
    if !sym_e(ts, j, ',') {
        return None;
    }
    let (m, q) = match pe_e(ts, j + 1, d - 1, td) {
        Some(r) => r,
        None => return None,
    };
    if !(sym_e(ts, q, ',') && sym_e(ts, q + 1, '|') && sym_e(ts, q + 3, '|')) {
        return None;
    }
    let x = match bdt_e(ts, q + 2) {
        Some(x) => x,
        None => return None,
    };
    if q + 4 > ts.len() {
        return None;
    }
    let (b, u) = match pe_e(ts, q + 4, d - 1, td) {
        Some(r) => r,
        None => return None,
    };
    if !sym_e(ts, u, ')') {
        return None;
    }
    Some((SExpr::Loop(Box::new(a), Box::new(m), x, Box::new(b)), u + 1))
}

/// dict<A, B>() の本体（位置 i は dict の語。語の後に `<`、二つの型、`(`、`)`）。
fn pe_dictnew_e(ts: &Vec<ETok>, i: usize, d: usize, td: usize) -> (r: Option<(SExpr, usize)>)
    requires
        nv(vtoks(ts@), i as nat),
        small(ts@),
        i < ts.len(),
        d > 0,
        vtok(ts@[i as int]) == Tok::Kw(Kw::Dict),
    ensures
        pp_ok(ts@, i, d, td, r),
    decreases d, 0nat,
{
    let ghost tv = vtoks(ts@);
    proof {
        assert(tv[i as int] == vtok(ts@[i as int]));
    }
    if !sym_e(ts, i + 1, '<') {
        return None;
    }
    let (a, j) = match pt_e(ts, i + 2, td) {
        Some(r) => r,
        None => return None,
    };
    if !sym_e(ts, j, ',') {
        return None;
    }
    let (b, m) = match pt_e(ts, j + 1, td) {
        Some(r) => r,
        None => return None,
    };
    if !(sym_e(ts, m, '>') && sym_e(ts, m + 1, '(') && sym_e(ts, m + 2, ')')) {
        return None;
    }
    Some((SExpr::DictNew(a, b), m + 3))
}

/// dict の組込み呼出しの本体（位置 i は組込みの語。語の後に `(`、引数の列、閉じ括弧）。
fn pe_dictop_e(ts: &Vec<ETok>, i: usize, d: usize, td: usize, h: Dop) -> (r: Option<(SExpr, usize)>)
    requires
        nv(vtoks(ts@), i as nat),
        small(ts@),
        i < ts.len(),
        d > 0,
        vtok(ts@[i as int]) == Tok::Kw(dkw(h)),
    ensures
        pp_ok(ts@, i, d, td, r),
    decreases d, 0nat,
{
    let ghost tv = vtoks(ts@);
    proof {
        assert(tv[i as int] == vtok(ts@[i as int]));
        dop_kw(h);
    }
    if !sym_e(ts, i + 1, '(') {
        return None;
    }
    match pargs_e(ts, i + 2, d - 1, td) {
        Some((es, j)) => Some((SExpr::DictOp(h, es), j)),
        None => None,
    }
}

/// 文脈語 `match` の綴り（予約語ではない識別子として読む）。
fn mword_e(x: &Vec<char>) -> (r: bool)
    ensures
        r == (x@ == mword()),
{
    let mut w: Vec<char> = Vec::new();
    w.push('m');
    w.push('a');
    w.push('t');
    w.push('c');
    w.push('h');
    proof {
        assert(w@ =~= mword());
    }
    eq_chars(x, &w)
}

/// 位置 i の `_`（ただの識別子として読む）。
fn wild_e(ts: &Vec<ETok>, i: usize) -> (r: bool)
    requires
        small(ts@),
    ensures
        r == (i < ts.len() && vtok(ts@[i as int]) == Tok::Id(seq!['_'])),
{
    if i < ts.len() {
        match &ts[i] {
            ETok::Id(x) => {
                let mut w: Vec<char> = Vec::new();
                w.push('_');
                proof {
                    assert(w@ =~= seq!['_']);
                }
                eq_chars(x, &w)
            },
            _ => false,
        }
    } else {
        false
    }
}

/// `kw "(" bind ")"` の bind（位置 i は kw。閉じ括弧の後ろの位置は i + 4）。
fn pwrap_e(ts: &Vec<ETok>, i: usize, k: Kw) -> (r: Option<Vec<char>>)
    requires
        small(ts@),
        i <= ts.len(),
        k == Kw::Ok || k == Kw::Err || k == Kw::Some,
    ensures
        match r {
            Some(x) => kwat(vtoks(ts@), i as nat, k) && sym(vtoks(ts@), (i + 1) as nat, '(') && bdt(
                vtoks(ts@),
                (i + 2) as nat,
            ) == Some(x@) && sym(vtoks(ts@), (i + 3) as nat, ')'),
            None => !(kwat(vtoks(ts@), i as nat, k) && sym(vtoks(ts@), (i + 1) as nat, '(') && bdt(
                vtoks(ts@),
                (i + 2) as nat,
            ) is Some && sym(vtoks(ts@), (i + 3) as nat, ')')),
        },
{
    if kwat_e(ts, i, k) && sym_e(ts, i + 1, '(') && sym_e(ts, i + 3, ')') {
        bdt_e(ts, i + 2)
    } else {
        None
    }
}

/// 構築子のパターンの束縛の並び `bind ("," bind)* ")"`（位置 i から。閉じ括弧の後ろの位置）。
fn pbinds_e(ts: &Vec<ETok>, i: usize) -> (r: Option<(Vec<Vec<char>>, usize)>)
    requires
        small(ts@),
        i <= ts.len(),
    ensures
        match r {
            Some((bs, j)) => pbinds(vtoks(ts@), i as nat) == Some((vnames(bs@), j as nat)) && j <= ts.len(),
            None => pbinds(vtoks(ts@), i as nat) is None,
        },
{
    let ghost tv = vtoks(ts@);
    let mut bs: Vec<Vec<char>> = Vec::new();
    let mut k = i;
    proof {
        assert(vnames(bs@) =~= Seq::<Seq<char>>::empty());
        if let Some((w, m)) = pbinds(tv, i as nat) {
            assert(Seq::<Seq<char>>::empty() + w =~= w);
        }
    }
    loop
        invariant
            small(ts@),
            tv == vtoks(ts@),
            k <= ts.len(),
            pbinds(tv, i as nat) == cat(vnames(bs@), pbinds(tv, k as nat)),
        decreases ts.len() - k,
    {
        proof {
            reveal_with_fuel(pbinds, 1);
        }
        let x = match bdt_e(ts, k) {
            Some(x) => x,
            None => return None,
        };
        if sym_e(ts, k + 1, ')') {
            let ghost before = vnames(bs@);
            let ghost xv = x@;
            bs.push(x);
            proof {
                assert(vnames(bs@) =~= before + seq![xv]);
                assert(pbinds(tv, k as nat) == Some((seq![xv], (k + 2) as nat)));
            }
            return Some((bs, k + 2));
        } else if sym_e(ts, k + 1, ',') {
            let ghost before = vnames(bs@);
            let ghost xv = x@;
            bs.push(x);
            proof {
                assert(vnames(bs@) =~= before + seq![xv]);
                assert(pbinds(tv, k as nat) == cat(seq![xv], pbinds(tv, (k + 2) as nat)));
                cat_app(before, seq![xv], pbinds(tv, (k + 2) as nat));
            }
            k = k + 2;
        } else {
            return None;
        }
    }
}

/// 枝の左辺（パターン）。位置 i はパターンの先頭で、戻り値はパターンと後ろの位置。
fn ppat_e(ts: &Vec<ETok>, i: usize) -> (r: Option<(SPat, usize)>)
    requires
        small(ts@),
        i <= ts.len(),
    ensures
        match r {
            Some((p, j)) => ppat(vtoks(ts@), i as nat) == Some((vpat(p), j as nat)) && j <= ts.len(),
            None => ppat(vtoks(ts@), i as nat) is None,
        },
{
    if let Some(c) = cidt_e(ts, i) {
        if sym_e(ts, i + 1, '(') {
            match pbinds_e(ts, i + 2) {
                Some((bs, j)) => Some((SPat::Ctor(c, bs), j)),
                None => None,
            }
        } else {
            proof {
                assert(vnames(Seq::<Vec<char>>::empty()) =~= Seq::<Seq<char>>::empty());
            }
            Some((SPat::Ctor(c, Vec::new()), i + 1))
        }
    } else if let Some(x) = pwrap_e(ts, i, Kw::Ok) {
        Some((SPat::Ok(x), i + 4))
    } else if let Some(x) = pwrap_e(ts, i, Kw::Err) {
        Some((SPat::Err(x), i + 4))
    } else if let Some(x) = pwrap_e(ts, i, Kw::Some) {
        Some((SPat::Some(x), i + 4))
    } else if kwat_e(ts, i, Kw::None) {
        Some((SPat::None, i + 1))
    } else if wild_e(ts, i) {
        Some((SPat::Wild, i + 1))
    } else {
        None
    }
}

/// 枝の並び（一つ以上）と、閉じ括弧 `}` の後ろの位置（位置 i は最初の枝のパターン）。
fn parm1_e(ts: &Vec<ETok>, i: usize, d: usize, td: usize) -> (r: Option<(Vec<SPat>, Vec<SExpr>, usize)>)
    requires
        small(ts@),
        i <= ts.len(),
    ensures
        match r {
            Some((ps, es, k)) => parm1(vtoks(ts@), i as nat, d as nat, td as nat) == Some((varms(ps@, es@), k as nat))
                && k <= ts.len(),
            None => parm1(vtoks(ts@), i as nat, d as nat, td as nat) is None,
        },
    decreases d, 3nat,
{
    let ghost tv = vtoks(ts@);
    let mut ps: Vec<SPat> = Vec::new();
    let mut es: Vec<SExpr> = Vec::new();
    let mut k = i;
    proof {
        assert(varms(ps@, es@) =~= Seq::<(Spat, Sx)>::empty());
        if let Some((w, m)) = parm1(tv, i as nat, d as nat, td as nat) {
            assert(Seq::<(Spat, Sx)>::empty() + w =~= w);
        }
    }
    loop
        invariant
            small(ts@),
            tv == vtoks(ts@),
            k <= ts.len(),
            ps@.len() == es@.len(),
            parm1(tv, i as nat, d as nat, td as nat) == cat(varms(ps@, es@), parm1(tv, k as nat, d as nat, td as nat)),
        decreases ts.len() - k,
    {
        proof {
            reveal_with_fuel(parm1, 1);
        }
        let (p, j) = match ppat_e(ts, k) {
            Some(r) => r,
            None => return None,
        };
        if !(sym_e(ts, j, '=') && sym_e(ts, j + 1, '>')) {
            return None;
        }
        let (b, m) = match pe_e(ts, j + 2, d, td) {
            Some(r) => r,
            None => return None,
        };
        if sym_e(ts, m, '}') {
            let ghost ps0 = ps@;
            let ghost es0 = es@;
            let ghost pv = vpat(p);
            let ghost bv = vx(b);
            ps.push(p);
            es.push(b);
            proof {
                assert(ps@.subrange(0, ps0.len() as int) =~= ps0);
                assert(es@.subrange(0, es0.len() as int) =~= es0);
                varms_push(ps0, es0, ps@, es@);
                assert(parm1(tv, k as nat, d as nat, td as nat) == Some((seq![(pv, bv)], (m + 1) as nat)));
                assert(varms(ps@, es@) =~= varms(ps0, es0) + seq![(pv, bv)]);
            }
            return Some((ps, es, m + 1));
        } else if sym_e(ts, m, ',') && k < m {
            let ghost ps0 = ps@;
            let ghost es0 = es@;
            let ghost pv = vpat(p);
            let ghost bv = vx(b);
            ps.push(p);
            es.push(b);
            proof {
                assert(ps@.subrange(0, ps0.len() as int) =~= ps0);
                assert(es@.subrange(0, es0.len() as int) =~= es0);
                varms_push(ps0, es0, ps@, es@);
                assert(parm1(tv, k as nat, d as nat, td as nat) == cat(
                    seq![(pv, bv)],
                    parm1(tv, (m + 1) as nat, d as nat, td as nat),
                ));
                assert(varms(ps@, es@) =~= varms(ps0, es0) + seq![(pv, bv)]);
                cat_app(varms(ps0, es0), seq![(pv, bv)], parm1(tv, (m + 1) as nat, d as nat, td as nat));
            }
            k = m + 1;
        } else {
            return None;
        }
    }
}

/// match 式の読み直し（位置 i は文脈語 `match`）。被験式の後ろは `{`、枝の並び、閉じ括弧。
fn pm_e(ts: &Vec<ETok>, i: usize, d: usize, td: usize) -> (r: Option<(SExpr, usize)>)
    requires
        small(ts@),
        i < ts.len(),
        d > 0,
    ensures
        match r {
            Some((e, j)) => pm(vtoks(ts@), i as nat, d as nat, td as nat) == Some((vx(e), j as nat)) && j <= ts.len(),
            None => pm(vtoks(ts@), i as nat, d as nat, td as nat) is None,
        },
    decreases d, 0nat,
{
    proof {
        reveal_with_fuel(pm, 1);
    }
    let (m, j) = match pe_e(ts, i + 1, d - 1, td) {
        Some(r) => r,
        None => return None,
    };
    if !sym_e(ts, j, '{') {
        return None;
    }
    let (ps, es, k) = match parm1_e(ts, j + 1, d - 1, td) {
        Some(r) => r,
        None => return None,
    };
    proof {
        reveal_with_fuel(vx, 1);
    }
    Some((SExpr::SumMatch(Box::new(m), ps, es), k))
}

fn pe_inj_e(ts: &Vec<ETok>, i: usize, d: usize, td: usize) -> (r: Option<(SExpr, usize)>)
    requires
        nv(vtoks(ts@), i as nat),
        small(ts@),
        i < ts.len(),
        d > 0,
        vtok(ts@[i as int]) == Tok::Kw(Kw::Ok) || vtok(ts@[i as int]) == Tok::Kw(Kw::Err),
    ensures
        pp_ok(ts@, i, d, td, r),
    decreases d, 0nat,
{
    let ghost tv = vtoks(ts@);
    proof {
        assert(tv[i as int] == vtok(ts@[i as int]));
    }
    let ok = match &ts[i] {
        ETok::Kw(Kw::Ok) => true,
        _ => false,
    };
    if !sym_e(ts, i + 1, '<') {
        return None;
    }
    let (t, j) = match pt_e(ts, i + 2, td) {
        Some(r) => r,
        None => return None,
    };
    if !sym_e(ts, j, ',') {
        return None;
    }
    let (u, m) = match pt_e(ts, j + 1, td) {
        Some(r) => r,
        None => return None,
    };
    if !(sym_e(ts, m, '>') && sym_e(ts, m + 1, '(')) {
        return None;
    }
    let (a, q) = match pe_e(ts, m + 2, d - 1, td) {
        Some(r) => r,
        None => return None,
    };
    if !sym_e(ts, q, ')') {
        return None;
    }
    Some((SExpr::Inj(ok, t, u, Box::new(a)), q + 1))
}

fn pe_matchr_e(ts: &Vec<ETok>, i: usize, d: usize, td: usize) -> (r: Option<(SExpr, usize)>)
    requires
        small(ts@),
        i < ts.len(),
        d > 0,
        vtok(ts@[i as int]) == Tok::Kw(Kw::MatchResult),
    ensures
        pp_ok(ts@, i, d, td, r),
    decreases d, 0nat,
{
    let ghost tv = vtoks(ts@);
    proof {
        assert(tv[i as int] == vtok(ts@[i as int]));
    }
    if !sym_e(ts, i + 1, '(') {
        return None;
    }
    let (m, j) = match pe_e(ts, i + 2, d - 1, td) {
        Some(r) => r,
        None => return None,
    };
    if j >= ts.len() || !(sym_e(ts, j, ',') && sym_e(ts, j + 1, '|') && sym_e(ts, j + 3, '|')) {
        return None;
    }
    let x = match bdt_e(ts, j + 2) {
        Some(x) => x,
        None => return None,
    };
    let (a, q) = match pe_e(ts, j + 4, d - 1, td) {
        Some(r) => r,
        None => return None,
    };
    if q >= ts.len() || !(sym_e(ts, q, ',') && sym_e(ts, q + 1, '|') && sym_e(ts, q + 3, '|')) {
        return None;
    }
    let y = match bdt_e(ts, q + 2) {
        Some(y) => y,
        None => return None,
    };
    let (b, u) = match pe_e(ts, q + 4, d - 1, td) {
        Some(r) => r,
        None => return None,
    };
    if !sym_e(ts, u, ')') {
        return None;
    }
    Some((SExpr::MatchR(Box::new(m), x, Box::new(a), y, Box::new(b)), u + 1))
}

/// 枝を一つ足した並び（先頭の並びは元のまま）の varms は、元の varms に一つ足したものと同じ。
proof fn varms_push(ps0: Seq<SPat>, es0: Seq<SExpr>, ps1: Seq<SPat>, es1: Seq<SExpr>)
    requires
        ps0.len() == es0.len(),
        ps1.len() == ps0.len() + 1,
        es1.len() == es0.len() + 1,
        ps1.subrange(0, ps0.len() as int) =~= ps0,
        es1.subrange(0, es0.len() as int) =~= es0,
    ensures
        varms(ps1, es1) == varms(ps0, es0) + seq![(vpat(ps1[ps0.len() as int]), vx(es1[es0.len() as int]))],
{
    let n = ps0.len() as int;
    let x = (vpat(ps1[n]), vx(es1[n]));
    assert forall|t: int| 0 <= t < n + 1 implies varms(ps1, es1)[t] == (varms(ps0, es0) + seq![x])[t] by {
        if t < n {
            assert(ps1[t] == ps0[t]);
            assert(es1[t] == es0[t]);
        }
    }
    assert(varms(ps1, es1) =~= varms(ps0, es0) + seq![x]);
}

proof fn vxs_push(a: Vec<SExpr>, b: Vec<SExpr>, e: SExpr)
    requires
        b@ == a@.push(e),
    ensures
        vxs(b) == vxs(a) + seq![vx(e)],
{
    assert(vxs(b) =~= vxs(a) + seq![vx(e)]);
}

pub open spec fn cat<T>(u: Seq<T>, o: Option<(Seq<T>, nat)>) -> Option<(Seq<T>, nat)> {
    match o {
        Some((w, m)) => Some((u + w, m)),
        None => None,
    }
}

/// 連結の結合：cat で先に w を付けてから u を付けるのは、u + w を付けるのと同じ。
proof fn cat_app<T>(u: Seq<T>, w: Seq<T>, o: Option<(Seq<T>, nat)>)
    ensures
        cat(u, cat(w, o)) == cat(u + w, o),
{
    if let Some((x, m)) = o {
        assert(u + (w + x) =~= (u + w) + x);
    }
}

/// `[ arguments ] ")"`。要素ごとの再帰をやめてループで読む（長い引数列で深い再帰にしない）。
pub fn pargs_e(ts: &Vec<ETok>, i: usize, d: usize, td: usize) -> (r: Option<(Vec<SExpr>, usize)>)
    requires
        small(ts@),
        i <= ts.len(),
    ensures
        match r {
            Some((es, j)) => pargs(vtoks(ts@), i as nat, d as nat, td as nat) == Some((vxs(es), j as nat))
                && j <= ts.len(),
            None => pargs(vtoks(ts@), i as nat, d as nat, td as nat) is None,
        },
    decreases d, 3nat,
{
    let ghost tv = vtoks(ts@);
    if sym_e(ts, i, ')') {
        let es: Vec<SExpr> = Vec::new();
        proof {
            assert(vxs(es) =~= Seq::<Sx>::empty());
        }
        return Some((es, i + 1));
    }
    let mut es: Vec<SExpr> = Vec::new();
    let mut k = i;
    proof {
        assert(vxs(es) =~= Seq::<Sx>::empty());
        if let Some((w, m)) = pargs1(tv, k as nat, d as nat, td as nat) {
            assert(Seq::<Sx>::empty() + w =~= w);
        }
    }
    loop
        invariant
            small(ts@),
            tv == vtoks(ts@),
            k <= ts.len(),
            !sym(tv, i as nat, ')'),
            pargs1(tv, i as nat, d as nat, td as nat) == cat(vxs(es), pargs1(tv, k as nat, d as nat, td as nat)),
        decreases ts.len() - k,
    {
        let ghost es0 = es;
        match pe_e(ts, k, d, td) {
            None => return None,
            Some((e, j)) => {
                if sym_e(ts, j, ')') {
                    es.push(e);
                    proof {
                        vxs_push(es0, es, e);
                    }
                    return Some((es, j + 1));
                } else if sym_e(ts, j, ',') && k < j {
                    es.push(e);
                    proof {
                        vxs_push(es0, es, e);
                        if let Some((w, m)) = pargs1(tv, (j + 1) as nat, d as nat, td as nat) {
                            assert(vxs(es0) + (seq![vx(e)] + w) =~= vxs(es) + w);
                        }
                    }
                    k = j + 1;
                } else {
                    return None;
                }
            },
        }
    }
}

pub fn pparams_e(ts: &Vec<ETok>, i: usize, td: usize) -> (r: Option<(Vec<(Vec<char>, Ty)>, usize)>)
    requires
        small(ts@),
        i <= ts.len(),
    ensures
        match r {
            Some((ps, j)) => pparams(vtoks(ts@), i as nat, td as nat) == Some((vps(ps@), j as nat))
                && j <= ts.len(),
            None => pparams(vtoks(ts@), i as nat, td as nat) is None,
        },
{
    let ghost tv = vtoks(ts@);
    let mut ps: Vec<(Vec<char>, Ty)> = Vec::new();
    proof {
        assert(vps(ps@) =~= Seq::<(Seq<char>, Ty)>::empty());
    }
    if sym_e(ts, i, ')') {
        return Some((ps, i + 1));
    }
    let mut k = i;
    proof {
        if let Some((w, m)) = pparams1(tv, k as nat, td as nat) {
            assert(Seq::<(Seq<char>, Ty)>::empty() + w =~= w);
        }
    }
    loop
        invariant
            small(ts@),
            tv == vtoks(ts@),
            k <= ts.len(),
            !sym(tv, i as nat, ')'),
            pparams1(tv, i as nat, td as nat) == cat(vps(ps@), pparams1(tv, k as nat, td as nat)),
        decreases ts.len() - k,
    {
        let ghost ps0 = ps@;
        let x = match bdt_e(ts, k) {
            Some(x) => x,
            None => return None,
        };
        if !sym_e(ts, k + 1, ':') {
            return None;
        }
        let (t, j) = match pt_e(ts, k + 2, td) {
            Some(r) => r,
            None => return None,
        };
        let ghost xv = x@;
        ps.push((x, t));
        proof {
            assert(vps(ps@) =~= vps(ps0) + seq![(xv, t)]);
        }
        if sym_e(ts, j, ')') {
            return Some((ps, j + 1));
        } else if sym_e(ts, j, ',') && k < j {
            proof {
                if let Some((w, m)) = pparams1(tv, (j + 1) as nat, td as nat) {
                    assert(vps(ps0) + (seq![(xv, t)] + w) =~= vps(ps@) + w);
                }
            }
            k = j + 1;
        } else {
            return None;
        }
    }
}

/// 大文字か（構築子の名前の先頭）。
fn is_upper_e(c: char) -> (r: bool)
    ensures
        r == is_upper(c),
{
    0x41 <= (c as u32) && (c as u32) <= 0x5a
}

/// 位置 i の構築子の名前（大文字で始まる IDENT）。
fn cidt_e(ts: &Vec<ETok>, i: usize) -> (r: Option<Vec<char>>)
    requires
        small(ts@),
    ensures
        match r {
            Some(c) => cidt(vtoks(ts@), i as nat) == Some(c@),
            None => cidt(vtoks(ts@), i as nat) is None,
        },
{
    match idt_e(ts, i) {
        Some(c) => if c.len() > 0 && is_upper_e(c[0]) {
            Some(c)
        } else {
            None
        },
        None => None,
    }
}

/// 型の並び（一つ以上、カンマ区切り。閉じ括弧は読まない）。
fn ptys_e(ts: &Vec<ETok>, i: usize, td: usize) -> (r: Option<(Vec<Ty>, usize)>)
    requires
        small(ts@),
        i <= ts.len(),
    ensures
        match r {
            Some((ps, j)) => ptys(vtoks(ts@), i as nat, td as nat) == Some((ps@, j as nat)) && j <= ts.len(),
            None => ptys(vtoks(ts@), i as nat, td as nat) is None,
        },
{
    let ghost tv = vtoks(ts@);
    let mut ps: Vec<Ty> = Vec::new();
    let mut k = i;
    proof {
        assert(ps@ =~= Seq::<Ty>::empty());
    }
    loop
        invariant
            small(ts@),
            tv == vtoks(ts@),
            k <= ts.len(),
            ptys(tv, i as nat, td as nat) == catt(ps@, ptys(tv, k as nat, td as nat)),
        decreases ts.len() - k,
    {
        proof {
            reveal_with_fuel(ptys, 1);
        }
        let (t, j) = match pt_e(ts, k, td) {
            None => return None,
            Some(r) => r,
        };
        if sym_e(ts, j, ',') && k < j {
            let ghost bf = ps@;
            ps.push(t);
            proof {
                assert(ps@ =~= bf + seq![ps@.last()]);
                catt_app(bf, seq![ps@.last()], ptys(tv, (j + 1) as nat, td as nat));
            }
            k = j + 1;
        } else {
            let ghost bf = ps@;
            ps.push(t);
            proof {
                assert(ps@ =~= bf + seq![ps@.last()]);
            }
            return Some((ps, j));
        }
    }
}

/// 構築子 `CTOR` か `CTOR "(" type ("," type)* ")"`（位置 i から）。名前、中身の型の並び、後ろの位置。
fn pvar_e(ts: &Vec<ETok>, i: usize, td: usize) -> (r: Option<(Vec<char>, Vec<Ty>, usize)>)
    requires
        small(ts@),
        i <= ts.len(),
    ensures
        match r {
            Some((c, ps, j)) => pvar(vtoks(ts@), i as nat, td as nat) == Some((c@, ps@, j as nat)) && j <= ts.len(),
            None => pvar(vtoks(ts@), i as nat, td as nat) is None,
        },
{
    let c = match cidt_e(ts, i) {
        Some(c) => c,
        None => return None,
    };
    if sym_e(ts, i + 1, '(') {
        let (ps, j) = match ptys_e(ts, i + 2, td) {
            Some(r) => r,
            None => return None,
        };
        if sym_e(ts, j, ')') {
            Some((c, ps, j + 1))
        } else {
            None
        }
    } else {
        Some((c, Vec::new(), i + 1))
    }
}

/// 直和型の構築子の並び（`|` で区切る。位置 i から、一つ以上）。
fn pvars_e(ts: &Vec<ETok>, i: usize, td: usize) -> (r: Option<(Vec<(Vec<char>, Vec<Ty>)>, usize)>)
    requires
        small(ts@),
        i <= ts.len(),
    ensures
        match r {
            Some((vs, j)) => pvars(vtoks(ts@), i as nat, td as nat) == Some((vvars(vs@), j as nat)) && j <= ts.len(),
            None => pvars(vtoks(ts@), i as nat, td as nat) is None,
        },
{
    let ghost tv = vtoks(ts@);
    let mut vs: Vec<(Vec<char>, Vec<Ty>)> = Vec::new();
    let mut k = i;
    proof {
        assert(vvars(vs@) =~= Seq::<(Seq<char>, Seq<Ty>)>::empty());
    }
    loop
        invariant
            small(ts@),
            tv == vtoks(ts@),
            k <= ts.len(),
            pvars(tv, i as nat, td as nat) == catvs(vvars(vs@), pvars(tv, k as nat, td as nat)),
        decreases ts.len() - k,
    {
        proof {
            reveal_with_fuel(pvars, 1);
        }
        let (c, ps, j) = match pvar_e(ts, k, td) {
            None => return None,
            Some(r) => r,
        };
        let ghost bf = vvars(vs@);
        if sym_e(ts, j, '|') && k < j {
            vs.push((c, ps));
            proof {
                assert(vvars(vs@) =~= bf + seq![(vs@.last().0@, vs@.last().1@)]);
                catvs_app(bf, seq![(vs@.last().0@, vs@.last().1@)], pvars(tv, (j + 1) as nat, td as nat));
            }
            k = j + 1;
        } else {
            vs.push((c, ps));
            proof {
                assert(vvars(vs@) =~= bf + seq![(vs@.last().0@, vs@.last().1@)]);
            }
            return Some((vs, j));
        }
    }
}

pub fn pd_e(ts: &Vec<ETok>, i: usize, d: usize, td: usize) -> (r: Option<(SDecl, usize)>)
    requires
        small(ts@),
        i <= ts.len(),
    ensures
        match r {
            Some((x, j)) => pd(vtoks(ts@), i as nat, d as nat, td as nat) == Some((vd(x), j as nat)) && j <= ts.len(),
            None => pd(vtoks(ts@), i as nat, d as nat, td as nat) is None,
        },
{
    let ghost tv = vtoks(ts@);
    if kwat_e(ts, i, Kw::Fn) {
        let f = match idt_e(ts, i + 1) {
            Some(f) => f,
            None => return None,
        };
        if !sym_e(ts, i + 2, '(') {
            return None;
        }
        let (ps, j) = match pparams_e(ts, i + 3, td) {
            Some(r) => r,
            None => return None,
        };
        if j >= ts.len() {
            return None;
        }
        proof {
            assert(tv[j as int] == vtok(ts@[j as int]));
        }
        match &ts[j] {
            ETok::Arrow => {},
            _ => return None,
        }
        let (r, m) = match pt_e(ts, j + 1, td) {
            Some(r) => r,
            None => return None,
        };
        if !sym_e(ts, m, '=') {
            return None;
        }
        let (b, q) = match pe_e(ts, m + 1, d, td) {
            Some(r) => r,
            None => return None,
        };
        Some((SDecl::Fn(f, ps, r, b), q))
    } else if kwat_e(ts, i, Kw::Entry) {
        match idt_e(ts, i + 1) {
            Some(x) => Some((SDecl::Entry(x), i + 2)),
            None => None,
        }
    } else if tyw_e(ts, i) {
        let r = match idt_e(ts, i + 1) {
            Some(r) => r,
            None => return None,
        };
        if !sym_e(ts, i + 2, '=') {
            return None;
        }
        if sym_e(ts, i + 3, '{') {
            match pfds_e(ts, i + 4, td) {
                Some((fs, tc, j)) => Some((SDecl::RecTy(r, fs, tc), j)),
                None => None,
            }
        } else {
            match pvars_e(ts, i + 3, td) {
                Some((vs, j)) => Some((SDecl::Sum(r, vs), j)),
                None => None,
            }
        }
    } else {
        None
    }
}

pub open spec fn catd(u: Seq<Sd>, o: Option<Seq<Sd>>) -> Option<Seq<Sd>> {
    match o {
        Some(w) => Some(u + w),
        None => None,
    }
}

pub fn pds_e(ts: &Vec<ETok>, d: usize, td: usize) -> (r: Option<Vec<SDecl>>)
    requires
        small(ts@),
    ensures
        match r {
            Some(p) => pds(vtoks(ts@), 0, d as nat, td as nat) == Some(vds(p@)),
            None => pds(vtoks(ts@), 0, d as nat, td as nat) is None,
        },
{
    let ghost tv = vtoks(ts@);
    let mut out: Vec<SDecl> = Vec::new();
    let mut i: usize = 0;
    proof {
        assert(vds(out@) =~= Seq::<Sd>::empty());
        if let Some(w) = pds(tv, 0, d as nat, td as nat) {
            assert(Seq::<Sd>::empty() + w =~= w);
        }
    }
    while i < ts.len()
        invariant
            small(ts@),
            tv == vtoks(ts@),
            i <= ts.len(),
            pds(tv, 0, d as nat, td as nat) == catd(vds(out@), pds(tv, i as nat, d as nat, td as nat)),
        decreases ts.len() - i,
    {
        let ghost o0 = out@;
        match pd_e(ts, i, d, td) {
            Some((x, j)) => {
                if i < j {
                    let ghost xv = vd(x);
                    out.push(x);
                    proof {
                        assert(vds(out@) =~= vds(o0) + seq![xv]);
                        if let Some(w) = pds(tv, j as nat, d as nat, td as nat) {
                            assert(vds(o0) + (seq![xv] + w) =~= vds(out@) + w);
                        }
                    }
                    i = j;
                } else {
                    return None;
                }
            },
            None => return None,
        }
    }
    proof {
        assert(vds(out@) + Seq::<Sd>::empty() =~= vds(out@));
    }
    Some(out)
}

/// source（文字列）を AST に。
pub fn parse_e(s: &Vec<char>, d: usize, td: usize) -> (r: Option<Vec<SDecl>>)
    requires
        s@.len() < 0x1000_0000,
    ensures
        match r {
            Some(p) => parse(s@, d as nat, td as nat) == Some(vds(p@)),
            None => parse(s@, d as nat, td as nat) is None,
        },
{
    match lex_e(s) {
        Some(ts) => pds_e(&ts, d, td),
        None => None,
    }
}

// ------------------------------------------------------------------ 正準フォーマッタ

fn push1(out: &mut Vec<char>, c: char)
    ensures
        final(out)@ == old(out)@ + seq![c],
{
    out.push(c);
    proof {
        assert(out@ =~= old(out)@ + seq![c]);
    }
}

fn push2(out: &mut Vec<char>, c0: char, c1: char)
    ensures
        final(out)@ == old(out)@ + seq![c0, c1],
{
    out.push(c0);
    out.push(c1);
    proof {
        assert(out@ =~= old(out)@ + seq![c0, c1]);
    }
}

fn push3(out: &mut Vec<char>, c0: char, c1: char, c2: char)
    ensures
        final(out)@ == old(out)@ + seq![c0, c1, c2],
{
    out.push(c0);
    out.push(c1);
    out.push(c2);
    proof {
        assert(out@ =~= old(out)@ + seq![c0, c1, c2]);
    }
}

fn push4(out: &mut Vec<char>, c0: char, c1: char, c2: char, c3: char)
    ensures
        final(out)@ == old(out)@ + seq![c0, c1, c2, c3],
{
    out.push(c0);
    out.push(c1);
    out.push(c2);
    out.push(c3);
    proof {
        assert(out@ =~= old(out)@ + seq![c0, c1, c2, c3]);
    }
}

fn push5(out: &mut Vec<char>, c0: char, c1: char, c2: char, c3: char, c4: char)
    ensures
        final(out)@ == old(out)@ + seq![c0, c1, c2, c3, c4],
{
    out.push(c0);
    out.push(c1);
    out.push(c2);
    out.push(c3);
    out.push(c4);
    proof {
        assert(out@ =~= old(out)@ + seq![c0, c1, c2, c3, c4]);
    }
}

fn push6(out: &mut Vec<char>, c0: char, c1: char, c2: char, c3: char, c4: char, c5: char)
    ensures
        final(out)@ == old(out)@ + seq![c0, c1, c2, c3, c4, c5],
{
    out.push(c0);
    out.push(c1);
    out.push(c2);
    out.push(c3);
    out.push(c4);
    out.push(c5);
    proof {
        assert(out@ =~= old(out)@ + seq![c0, c1, c2, c3, c4, c5]);
    }
}

fn push7(out: &mut Vec<char>, c0: char, c1: char, c2: char, c3: char, c4: char, c5: char, c6: char)
    ensures
        final(out)@ == old(out)@ + seq![c0, c1, c2, c3, c4, c5, c6],
{
    out.push(c0);
    out.push(c1);
    out.push(c2);
    out.push(c3);
    out.push(c4);
    out.push(c5);
    out.push(c6);
    proof {
        assert(out@ =~= old(out)@ + seq![c0, c1, c2, c3, c4, c5, c6]);
    }
}

fn push_kw(out: &mut Vec<char>, k: Kw)
    ensures
        final(out)@ == old(out)@ + kwt(k),
{
    match k {
        Kw::Fn => push2(out, 'f', 'n'),
        Kw::Entry => push5(out, 'e', 'n', 't', 'r', 'y'),
        Kw::TInt => push3(out, 'I', 'n', 't'),
        Kw::TBool => push4(out, 'B', 'o', 'o', 'l'),
        Kw::TUnit => push4(out, 'U', 'n', 'i', 't'),
        Kw::TList => push4(out, 'L', 'i', 's', 't'),
        Kw::TOption => push6(out, 'O', 'p', 't', 'i', 'o', 'n'),
        Kw::TPair => push4(out, 'P', 'a', 'i', 'r'),
        Kw::TChar => push4(out, 'C', 'h', 'a', 'r'),
        Kw::TString => push6(out, 'S', 't', 'r', 'i', 'n', 'g'),
        Kw::Code => push4(out, 'c', 'o', 'd', 'e'),
        Kw::CharOf => push4(out, 'c', 'h', 'a', 'r'),
        Kw::ToString => {
            push5(out, 't', 'o', '_', 's', 't');
            push4(out, 'r', 'i', 'n', 'g');
            proof {
                assert(out@ =~= old(out)@ + kwt(k));
            }
        },
        Kw::ParseInt => {
            push6(out, 'p', 'a', 'r', 's', 'e', '_');
            push3(out, 'i', 'n', 't');
            proof {
                assert(out@ =~= old(out)@ + kwt(k));
            }
        },
        Kw::True => push4(out, 't', 'r', 'u', 'e'),
        Kw::False => push5(out, 'f', 'a', 'l', 's', 'e'),
        Kw::Unit => push4(out, 'u', 'n', 'i', 't'),
        Kw::List => push4(out, 'l', 'i', 's', 't'),
        Kw::Some => push4(out, 's', 'o', 'm', 'e'),
        Kw::None => push4(out, 'n', 'o', 'n', 'e'),
        Kw::Pair => push4(out, 'p', 'a', 'i', 'r'),
        Kw::Let => push3(out, 'l', 'e', 't'),
        Kw::In => push2(out, 'i', 'n'),
        Kw::If => push2(out, 'i', 'f'),
        Kw::Fold => push4(out, 'f', 'o', 'l', 'd'),
        Kw::Add => push3(out, 'a', 'd', 'd'),
        Kw::Sub => push3(out, 's', 'u', 'b'),
        Kw::Mul => push3(out, 'm', 'u', 'l'),
        Kw::Neg => push3(out, 'n', 'e', 'g'),
        Kw::Lt => push2(out, 'l', 't'),
        Kw::Le => push2(out, 'l', 'e'),
        Kw::Eq => push2(out, 'e', 'q'),
        Kw::Mod => push3(out, 'm', 'o', 'd'),
        Kw::Div => push3(out, 'd', 'i', 'v'),
        Kw::Fst => push3(out, 'f', 's', 't'),
        Kw::Snd => push3(out, 's', 'n', 'd'),
        Kw::Cons => push4(out, 'c', 'o', 'n', 's'),
        Kw::Concat => push6(out, 'c', 'o', 'n', 'c', 'a', 't'),
        Kw::Reverse => push7(out, 'r', 'e', 'v', 'e', 'r', 's', 'e'),
        Kw::Length => push6(out, 'l', 'e', 'n', 'g', 't', 'h'),
        Kw::Uncons => push6(out, 'u', 'n', 'c', 'o', 'n', 's'),
        Kw::Min => push3(out, 'm', 'i', 'n'),
        Kw::Max => push3(out, 'm', 'a', 'x'),
        Kw::Range => push5(out, 'r', 'a', 'n', 'g', 'e'),
        Kw::Sort => push4(out, 's', 'o', 'r', 't'),
        Kw::Contains => {
            push4(out, 'c', 'o', 'n', 't');
            push4(out, 'a', 'i', 'n', 's');
            proof {
                assert(out@ =~= old(out)@ + kwt(k));
            }
        },
        Kw::MatchOption => {
            push6(out, 'm', 'a', 't', 'c', 'h', '_');
            push6(out, 'o', 'p', 't', 'i', 'o', 'n');
            proof {
                assert(out@ =~= old(out)@ + kwt(k));
            }
        },
        Kw::TResult => push6(out, 'R', 'e', 's', 'u', 'l', 't'),
        Kw::Ok => push2(out, 'o', 'k'),
        Kw::Err => push3(out, 'e', 'r', 'r'),
        Kw::MatchResult => {
            push6(out, 'm', 'a', 't', 'c', 'h', '_');
            push6(out, 'r', 'e', 's', 'u', 'l', 't');
            proof {
                assert(out@ =~= old(out)@ + kwt(k));
            }
        },
        Kw::Map => push3(out, 'm', 'a', 'p'),
        Kw::Filter => push6(out, 'f', 'i', 'l', 't', 'e', 'r'),
        Kw::Any => push3(out, 'a', 'n', 'y'),
        Kw::All => push3(out, 'a', 'l', 'l'),
        Kw::Find => push4(out, 'f', 'i', 'n', 'd'),
        Kw::Loop => push4(out, 'l', 'o', 'o', 'p'),
        Kw::SortBy => {
            push6(out, 's', 'o', 'r', 't', '_', 'b');
            push1(out, 'y');
            proof {
                assert(out@ =~= old(out)@ + kwt(k));
            }
        },
        Kw::Dict => push4(out, 'd', 'i', 'c', 't'),
        Kw::DictGet => {
            push5(out, 'd', 'i', 'c', 't', '_');
            push3(out, 'g', 'e', 't');
            proof {
                assert(out@ =~= old(out)@ + kwt(k));
            }
        },
        Kw::DictPut => {
            push5(out, 'd', 'i', 'c', 't', '_');
            push3(out, 'p', 'u', 't');
            proof {
                assert(out@ =~= old(out)@ + kwt(k));
            }
        },
        Kw::DictRemove => {
            push5(out, 'd', 'i', 'c', 't', '_');
            push6(out, 'r', 'e', 'm', 'o', 'v', 'e');
            proof {
                assert(out@ =~= old(out)@ + kwt(k));
            }
        },
        Kw::DictHas => {
            push5(out, 'd', 'i', 'c', 't', '_');
            push3(out, 'h', 'a', 's');
            proof {
                assert(out@ =~= old(out)@ + kwt(k));
            }
        },
        Kw::DictSize => {
            push5(out, 'd', 'i', 'c', 't', '_');
            push4(out, 's', 'i', 'z', 'e');
            proof {
                assert(out@ =~= old(out)@ + kwt(k));
            }
        },
        Kw::DictKeys => {
            push5(out, 'd', 'i', 'c', 't', '_');
            push4(out, 'k', 'e', 'y', 's');
            proof {
                assert(out@ =~= old(out)@ + kwt(k));
            }
        },
        Kw::DictValues => {
            push5(out, 'd', 'i', 'c', 't', '_');
            push6(out, 'v', 'a', 'l', 'u', 'e', 's');
            proof {
                assert(out@ =~= old(out)@ + kwt(k));
            }
        },
        Kw::DictEntries => {
            push5(out, 'd', 'i', 'c', 't', '_');
            push7(out, 'e', 'n', 't', 'r', 'i', 'e', 's');
            proof {
                assert(out@ =~= old(out)@ + kwt(k));
            }
        },
        Kw::DictFrom => {
            push5(out, 'd', 'i', 'c', 't', '_');
            push4(out, 'f', 'r', 'o', 'm');
            proof {
                assert(out@ =~= old(out)@ + kwt(k));
            }
        },
    }
}

/// hof の語（キーワードの token）の exec 版。
fn hkw_e(h: Hf) -> (r: Kw)
    ensures
        r == hkw(h),
{
    match h {
        Hf::Map => Kw::Map,
        Hf::Filter => Kw::Filter,
        Hf::Any => Kw::Any,
        Hf::All => Kw::All,
        Hf::Find => Kw::Find,
        Hf::SortBy => Kw::SortBy,
    }
}

/// dict の組込みの語（キーワードの token）の exec 版。
fn dkw_e(d: Dop) -> (r: Kw)
    ensures
        r == dkw(d),
{
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

fn push_ty(out: &mut Vec<char>, t: &Ty)
    ensures
        final(out)@ == old(out)@ + ft(*t, Seq::empty()),
    decreases t,
{
    let ghost o = out@;
    let ghost z = Seq::<char>::empty();
    match t {
        Ty::Int => push_kw(out, Kw::TInt),
        Ty::Bool => push_kw(out, Kw::TBool),
        Ty::Unit => push_kw(out, Kw::TUnit),
        Ty::Char => push_kw(out, Kw::TChar),
        Ty::List(a) => match &**a {
            Ty::Char => push_kw(out, Kw::TString),
            _ => {
                push_kw(out, Kw::TList);
                push1(out, '<');
                push_ty(out, a);
                push1(out, '>');
                proof {
                    ft_app(**a, seq!['>'] + z);
                    assert(out@ =~= o + ft(*t, z));
                }
            },
        },
        Ty::Option(a) => {
            push_kw(out, Kw::TOption);
            push1(out, '<');
            push_ty(out, a);
            push1(out, '>');
            proof {
                ft_app(**a, seq!['>'] + z);
                assert(out@ =~= o + ft(*t, z));
            }
        },
        Ty::Pair(a, b) | Ty::Result(a, b) => {
            push_kw(out, match t {
                Ty::Pair(..) => Kw::TPair,
                _ => Kw::TResult,
            });
            push1(out, '<');
            push_ty(out, a);
            push2(out, ',', ' ');
            push_ty(out, b);
            push1(out, '>');
            proof {
                ft_app(**b, seq!['>'] + z);
                ft_app(**a, seq![',', ' '] + ft(**b, seq!['>'] + z));
                assert(out@ =~= o + ft(*t, z));
            }
        },
    }
}

fn push_esc(out: &mut Vec<char>, c: char, q: char)
    ensures
        final(out)@ == old(out)@ + esc(c, q),
{
    if c == '\\' {
        push2(out, '\\', '\\');
    } else if c == q {
        push2(out, '\\', q);
    } else if c == '\n' {
        push2(out, '\\', 'n');
    } else if c == '\t' {
        push2(out, '\\', 't');
    } else if c == '\r' {
        push2(out, '\\', 'r');
    } else {
        push1(out, c);
    }
}

proof fn escs_app(a: Seq<char>, b: Seq<char>, q: char)
    ensures
        escs(a + b, q) == escs(a, q) + escs(b, q),
    decreases a.len(),
{
    if a.len() == 0 {
        assert(a + b =~= b);
        assert(Seq::<char>::empty() + escs(b, q) =~= escs(b, q));
    } else {
        escs_app(a.drop_first(), b, q);
        assert((a + b).drop_first() =~= a.drop_first() + b);
        assert((a + b)[0] == a[0]);
        assert(esc(a[0], q) + (escs(a.drop_first(), q) + escs(b, q)) =~= (esc(a[0], q) + escs(a.drop_first(), q))
            + escs(b, q));
    }
}

proof fn escs_one(c: char, q: char)
    ensures
        escs(seq![c], q) == esc(c, q),
{
    reveal_with_fuel(escs, 2);
    assert(seq![c].drop_first() =~= Seq::<char>::empty());
    assert(escs(Seq::<char>::empty(), q) == Seq::<char>::empty());
    assert(esc(c, q) + Seq::<char>::empty() =~= esc(c, q));
}

fn push_escs(out: &mut Vec<char>, w: &Vec<char>, q: char)
    ensures
        final(out)@ == old(out)@ + escs(w@, q),
{
    let ghost o = out@;
    let mut i: usize = 0;
    proof {
        assert(w@.subrange(0, 0) =~= Seq::<char>::empty());
        assert(o + Seq::<char>::empty() =~= o);
    }
    while i < w.len()
        invariant
            i <= w.len(),
            out@ == o + escs(w@.subrange(0, i as int), q),
        decreases w.len() - i,
    {
        proof {
            escs_app(w@.subrange(0, i as int), seq![w@[i as int]], q);
            escs_one(w@[i as int], q);
            assert(w@.subrange(0, i as int) + seq![w@[i as int]] =~= w@.subrange(0, i + 1));
        }
        push_esc(out, w[i], q);
        i += 1;
    }
    proof {
        assert(w@.subrange(0, w.len() as int) =~= w@);
    }
}

#[verifier::rlimit(60)]
fn push_e(out: &mut Vec<char>, e: &SExpr)
    ensures
        final(out)@ == old(out)@ + fe(vx(*e), Seq::empty()),
    decreases e, 1nat,
{
    let ghost o = out@;
    let ghost z = Seq::<char>::empty();
    match e {
        SExpr::Int(n) => {
            let ds = n.to_dec_chars();
            append_chars(out, &ds);
        },
        SExpr::Chr(c) => {
            push1(out, '\'');
            push_esc(out, *c, '\'');
            push1(out, '\'');
            proof {
                assert(out@ =~= o + fe(vx(*e), z));
            }
        },
        SExpr::Str(w) => {
            push1(out, '"');
            push_escs(out, w, '"');
            push1(out, '"');
            proof {
                assert(out@ =~= o + fe(vx(*e), z));
            }
        },
        SExpr::Bool(b) => push_kw(out, if *b { Kw::True } else { Kw::False }),
        SExpr::Unit => push_kw(out, Kw::Unit),
        SExpr::Var(x) => append_chars(out, x),
        SExpr::List(t, es) => {
            push_kw(out, Kw::List);
            push1(out, '<');
            push_ty(out, t);
            push2(out, '>', '(');
            push_args(out, es);
            proof {
                ft_app(*t, seq!['>', '('] + fargs(vxs(*es), 0, z));
            }
        },
        SExpr::Some(a) => {
            push_kw(out, Kw::Some);
            push1(out, '(');
            push_e(out, a);
            push1(out, ')');
            proof {
                fe_app(vx(**a), seq![')'] + z);
            }
        },
        SExpr::None(t) => {
            push_kw(out, Kw::None);
            push1(out, '<');
            push_ty(out, t);
            push1(out, '>');
            push2(out, '(', ')');
            proof {
                ft_app(*t, seq!['>', '(', ')'] + z);
            }
        },
        SExpr::Pair(a, b) => {
            push_kw(out, Kw::Pair);
            push1(out, '(');
            push_e(out, a);
            push2(out, ',', ' ');
            push_e(out, b);
            push1(out, ')');
            proof {
                fe_app(vx(**b), seq![')'] + z);
                fe_app(vx(**a), seq![',', ' '] + fe(vx(**b), seq![')'] + z));
            }
        },
        SExpr::Builtin(b, es) => {
            push_kw(out, builtin_kw(*b));
            push1(out, '(');
            push_args(out, es);
        },
        SExpr::Call(f, es) => {
            append_chars(out, f);
            push1(out, '(');
            push_args(out, es);
        },
        SExpr::Let(..) => push_let(out, e),
        SExpr::If(..) => push_if(out, e),
        SExpr::Fold(..) => push_fold(out, e),
        SExpr::Match(..) => push_match(out, e),
        SExpr::Inj(..) => push_inj(out, e),
        SExpr::MatchR(..) => push_matchr(out, e),
        SExpr::Fld(..) => push_fld(out, e),
        SExpr::Rec(..) => push_rec(out, e),
        SExpr::SumMatch(..) => push_summatch(out, e),
        SExpr::Hof(..) => push_hof(out, e),
        SExpr::Loop(..) => push_loop(out, e),
        SExpr::DictNew(..) => push_dictnew(out, e),
        SExpr::DictOp(d, es) => {
            push_kw(out, dkw_e(*d));
            push1(out, '(');
            push_args(out, es);
        },
    }
    proof {
        assert(out@ =~= o + fe(vx(*e), z));
    }
}

/// 後置の `.f`（受け手の式を出してから、名前を `.` で並べる）。
fn push_fld(out: &mut Vec<char>, e: &SExpr)
    requires
        e is Fld,
    ensures
        final(out)@ == old(out)@ + fe(vx(*e), Seq::empty()),
    decreases e, 0nat,
{
    let ghost o = out@;
    let ghost z = Seq::<char>::empty();
    if let SExpr::Fld(a, ns) = e {
        push_e(out, a);
        push_dots(out, ns);
        proof {
            reveal_with_fuel(fe, 1);
            fe_app(vx(**a), fdots(vnames(ns@), z));
        }
    }
    proof {
        assert(out@ =~= o + fe(vx(*e), z));
    }
}

/// `"." IDENT` の並びを出す（名前の列を先頭から）。
fn push_dots(out: &mut Vec<char>, ns: &Vec<Vec<char>>)
    ensures
        final(out)@ == old(out)@ + fdots(vnames(ns@), Seq::empty()),
{
    let ghost o = out@;
    let ghost v = vnames(ns@);
    let ghost z = Seq::<char>::empty();
    let mut i: usize = 0;
    proof {
        assert(v.subrange(0, v.len() as int) =~= v);
    }
    while i < ns.len()
        invariant
            v == vnames(ns@),
            i <= ns@.len(),
            out@ + fdots(v.subrange(i as int, v.len() as int), z) == o + fdots(v, z),
        decreases ns@.len() - i,
    {
        let ghost before = out@;
        proof {
            reveal_with_fuel(fdots, 1);
            assert(v.subrange(i as int, v.len() as int)[0] == v[i as int]);
            assert(v.subrange(i as int, v.len() as int).subrange(1, v.len() - i as int) =~= v.subrange(
                (i + 1) as int,
                v.len() as int,
            ));
        }
        push1(out, '.');
        append_chars(out, &ns[i]);
        proof {
            assert(out@ =~= before + seq!['.'] + v[i as int]);
        }
        i += 1;
    }
    proof {
        assert(v.subrange(ns@.len() as int, v.len() as int) =~= Seq::<Seq<char>>::empty());
    }
}

/// レコード式の本体（字段の並びと base の前まで）。字段の式の列が名前より短いときは unit を出す（対応する値のない字段）。
fn push_fields(out: &mut Vec<char>, ns: &Vec<Vec<char>>, es: &Vec<SExpr>)
    ensures
        final(out)@ == old(out)@ + ffe(vfields(ns@, es@), 0, Seq::empty()),
    decreases es, 0nat,
{
    let ghost o = out@;
    let ghost z = Seq::<char>::empty();
    let ghost v = vfields(ns@, es@);
    let mut i: usize = 0;
    while i < ns.len()
        invariant
            v == vfields(ns@, es@),
            i <= ns@.len(),
            o + ffe(v, 0, z) == out@ + (if i < ns@.len() { ffe(v, i as nat, z) } else { z }),
        decreases ns@.len() - i,
    {
        let ghost before = out@;
        let ghost tail = if i + 1 == ns@.len() { z } else { seq![',', ' '] + ffe(v, (i + 1) as nat, z) };
        proof {
            reveal_with_fuel(ffe, 1);
            assert(v[i as int].0 == ns@[i as int]@);
        }
        append_chars(out, &ns[i]);
        push2(out, ':', ' ');
        if i < es.len() {
            push_e(out, &es[i]);
            proof {
                assert(v[i as int].1 == vx(es@[i as int]));
                fe_app(vx(es@[i as int]), tail);
            }
        } else {
            push_kw(out, Kw::Unit);
            proof {
                assert(v[i as int].1 == Sx::Unit);
                fe_app(Sx::Unit, tail);
            }
        }
        if i + 1 < ns.len() {
            push2(out, ',', ' ');
        }
        i += 1;
    }
}

/// レコード型の字段の並び（名前と型）。
fn push_fds(out: &mut Vec<char>, fs: &Vec<(Vec<char>, Ty)>)
    ensures
        final(out)@ == old(out)@ + ffd(vps(fs@), 0, Seq::empty()),
{
    let ghost o = out@;
    let ghost z = Seq::<char>::empty();
    let ghost v = vps(fs@);
    let mut i: usize = 0;
    while i < fs.len()
        invariant
            v == vps(fs@),
            i <= fs@.len(),
            o + ffd(v, 0, z) == out@ + (if i < fs@.len() { ffd(v, i as nat, z) } else { z }),
        decreases fs@.len() - i,
    {
        let ghost tail = if i + 1 == fs@.len() { z } else { seq![',', ' '] + ffd(v, (i + 1) as nat, z) };
        proof {
            reveal_with_fuel(ffd, 1);
            assert(v[i as int].0 == fs@[i as int].0@);
        }
        append_chars(out, &fs[i].0);
        push2(out, ':', ' ');
        push_ty(out, &fs[i].1);
        proof {
            assert(v[i as int].1 == fs@[i as int].1);
            ft_app(fs@[i as int].1, tail);
        }
        if i + 1 < fs.len() {
            push2(out, ',', ' ');
        }
        i += 1;
    }
}

/// レコード式（`R { f: e, ..b }`、空は `R {}`）。
fn push_rec(out: &mut Vec<char>, e: &SExpr)
    requires
        e is Rec,
    ensures
        final(out)@ == old(out)@ + fe(vx(*e), Seq::empty()),
    decreases e, 0nat,
{
    let ghost o = out@;
    let ghost z = Seq::<char>::empty();
    if let SExpr::Rec(r, ns, es, b) = e {
        append_chars(out, r);
        push2(out, ' ', '{');
        let bare = match b {
            Some(_) => false,
            None => ns.len() == 0,
        };
        if bare {
            push1(out, '}');
            proof {
                reveal_with_fuel(vx, 1);
                reveal_with_fuel(fe, 1);
                assert(out@ =~= o + fe(vx(*e), z));
            }
        } else {
            push1(out, ' ');
            push_fields(out, ns, es);
            match b {
                Some(x) => {
                    if ns.len() > 0 {
                        push2(out, ',', ' ');
                    }
                    push2(out, '.', '.');
                    push_e(out, x);
                    push2(out, ' ', '}');
                    proof {
                        reveal_with_fuel(vx, 1);
                        reveal_with_fuel(fe, 1);
                        fe_app(vx(**x), seq![' ', '}'] + z);
                        ffe_app(vfields(ns@, es@), 0, frtail(ns@.len() > 0, vbase(*b), z));
                        assert(out@ =~= o + fe(vx(*e), z));
                    }
                },
                None => {
                    push2(out, ' ', '}');
                    proof {
                        reveal_with_fuel(vx, 1);
                        reveal_with_fuel(fe, 1);
                        ffe_app(vfields(ns@, es@), 0, frtail(ns@.len() > 0, vbase(*b), z));
                        assert(out@ =~= o + fe(vx(*e), z));
                    }
                },
            }
        }
    }
}

fn push_if(out: &mut Vec<char>, e: &SExpr)
    requires
        e is If,
    ensures
        final(out)@ == old(out)@ + fe(vx(*e), Seq::empty()),
    decreases e, 0nat,
{
    let ghost o = out@;
    let ghost z = Seq::<char>::empty();
    if let SExpr::If(c, a, b) = e {
        push_kw(out, Kw::If);
        push1(out, '(');
        push_e(out, c);
        push2(out, ',', ' ');
        push_e(out, a);
        push2(out, ',', ' ');
        push_e(out, b);
        push1(out, ')');
        proof {
            let kb = seq![')'] + z;
            fe_app(vx(**b), kb);
            let ka = seq![',', ' '] + fe(vx(**b), kb);
            fe_app(vx(**a), ka);
            fe_app(vx(**c), seq![',', ' '] + fe(vx(**a), ka));
        }
        proof {
            assert(out@ =~= o + fe(vx(*e), z));
        }
    }
}

fn push_let(out: &mut Vec<char>, e: &SExpr)
    requires
        e is Let,
    ensures
        final(out)@ == old(out)@ + fe(vx(*e), Seq::empty()),
    decreases e, 0nat,
{
    let ghost o = out@;
    let ghost z = Seq::<char>::empty();
    if let SExpr::Let(x, a, b) = e {
        push_kw(out, Kw::Let);
        push1(out, ' ');
        append_chars(out, x);
        push3(out, ' ', '=', ' ');
        push_e(out, a);
        push1(out, ' ');
        push_kw(out, Kw::In);
        push1(out, ' ');
        push_e(out, b);
        proof {
            fe_app(vx(**b), z);
            let ka = seq![' '] + (kwt(Kw::In) + (seq![' '] + fe(vx(**b), z)));
            fe_app(vx(**a), ka);
            assert(out@ =~= o + fe(vx(*e), z));
        }
    }
}

#[verifier::rlimit(65)]
fn push_fold(out: &mut Vec<char>, e: &SExpr)
    requires
        e is Fold,
    ensures
        final(out)@ == old(out)@ + fe(vx(*e), Seq::empty()),
    decreases e, 0nat,
{
    let ghost o = out@;
    let ghost z = Seq::<char>::empty();
    if let SExpr::Fold(l, i, a, x, b) = e {
        push_kw(out, Kw::Fold);
        push1(out, '(');
        push_e(out, l);
        push2(out, ',', ' ');
        push_e(out, i);
        push3(out, ',', ' ', '|');
        append_chars(out, a);
        push2(out, ',', ' ');
        append_chars(out, x);
        push2(out, '|', ' ');
        push_e(out, b);
        push1(out, ')');
        proof {
            fe_app(vx(**b), seq![')'] + z);
            let ki = seq![',', ' ', '|'] + (a@ + (seq![',', ' '] + (x@ + (seq!['|', ' '] + fe(vx(**b), seq![')'] + z)))));
            fe_app(vx(**i), ki);
            fe_app(vx(**l), seq![',', ' '] + fe(vx(**i), ki));
            assert(out@ =~= o + fe(vx(*e), z));
        }
    }
}

fn push_match(out: &mut Vec<char>, e: &SExpr)
    requires
        e is Match,
    ensures
        final(out)@ == old(out)@ + fe(vx(*e), Seq::empty()),
    decreases e, 0nat,
{
    let ghost o = out@;
    let ghost z = Seq::<char>::empty();
    if let SExpr::Match(m, n, x, b) = e {
        push_kw(out, Kw::MatchOption);
        push1(out, '(');
        push_e(out, m);
        push2(out, ',', ' ');
        push_e(out, n);
        push3(out, ',', ' ', '|');
        append_chars(out, x);
        push2(out, '|', ' ');
        push_e(out, b);
        push1(out, ')');
        proof {
            fe_app(vx(**b), seq![')'] + z);
            let kn = seq![',', ' ', '|'] + (x@ + (seq!['|', ' '] + fe(vx(**b), seq![')'] + z)));
            fe_app(vx(**n), kn);
            fe_app(vx(**m), seq![',', ' '] + fe(vx(**n), kn));
            assert(out@ =~= o + fe(vx(*e), z));
        }
    }
}

/// hof の印字（`hof(被験式, |x| 本体)`）。
fn push_hof(out: &mut Vec<char>, e: &SExpr)
    requires
        e is Hof,
    ensures
        final(out)@ == old(out)@ + fe(vx(*e), Seq::empty()),
    decreases e, 0nat,
{
    let ghost o = out@;
    let ghost z = Seq::<char>::empty();
    if let SExpr::Hof(h, m, x, b) = e {
        push_kw(out, hkw_e(*h));
        push1(out, '(');
        push_e(out, m);
        push3(out, ',', ' ', '|');
        append_chars(out, x);
        push2(out, '|', ' ');
        push_e(out, b);
        push1(out, ')');
        proof {
            fe_app(vx(**b), seq![')'] + z);
            let kn = seq![',', ' ', '|'] + (x@ + (seq!['|', ' '] + fe(vx(**b), seq![')'] + z)));
            fe_app(vx(**m), kn);
            assert(out@ =~= o + fe(vx(*e), z));
        }
    }
}

/// loop の印字（`loop(初期値, 上限, |s| 本体)`）。
fn push_loop(out: &mut Vec<char>, e: &SExpr)
    requires
        e is Loop,
    ensures
        final(out)@ == old(out)@ + fe(vx(*e), Seq::empty()),
    decreases e, 0nat,
{
    let ghost o = out@;
    let ghost z = Seq::<char>::empty();
    if let SExpr::Loop(i, m, x, b) = e {
        push_kw(out, Kw::Loop);
        push1(out, '(');
        push_e(out, i);
        push2(out, ',', ' ');
        push_e(out, m);
        push3(out, ',', ' ', '|');
        append_chars(out, x);
        push2(out, '|', ' ');
        push_e(out, b);
        push1(out, ')');
        proof {
            fe_app(vx(**b), seq![')'] + z);
            let km = seq![',', ' ', '|'] + (x@ + (seq!['|', ' '] + fe(vx(**b), seq![')'] + z)));
            fe_app(vx(**m), km);
            fe_app(vx(**i), seq![',', ' '] + fe(vx(**m), km));
            assert(out@ =~= o + fe(vx(*e), z));
        }
    }
}

/// dict<A, B>() の印字（`dict<A, B>()`）。
fn push_dictnew(out: &mut Vec<char>, e: &SExpr)
    requires
        e is DictNew,
    ensures
        final(out)@ == old(out)@ + fe(vx(*e), Seq::empty()),
    decreases e, 0nat,
{
    let ghost o = out@;
    let ghost z = Seq::<char>::empty();
    if let SExpr::DictNew(a, b) = e {
        push_kw(out, Kw::Dict);
        push1(out, '<');
        push_ty(out, a);
        push2(out, ',', ' ');
        push_ty(out, b);
        push3(out, '>', '(', ')');
        proof {
            ft_app(*b, seq!['>', '(', ')'] + z);
            ft_app(*a, seq![',', ' '] + ft(*b, seq!['>', '(', ')'] + z));
            assert(out@ =~= o + fe(vx(*e), z));
        }
    }
}

/// match 式の印字（`match 被験式 { 枝 }`）。
fn push_summatch(out: &mut Vec<char>, e: &SExpr)
    requires
        e is SumMatch,
    ensures
        final(out)@ == old(out)@ + fe(vx(*e), Seq::empty()),
    decreases e, 0nat,
{
    let ghost o = out@;
    let ghost z = Seq::<char>::empty();
    if let SExpr::SumMatch(m, ps, es) = e {
        push5(out, 'm', 'a', 't', 'c', 'h');
        push1(out, ' ');
        push_e(out, m);
        push3(out, ' ', '{', ' ');
        push_arms(out, ps, es);
        proof {
            reveal_with_fuel(vx, 1);
            reveal_with_fuel(fe, 1);
            fe_app(vx(**m), seq![' ', '{', ' '] + farms(varms(ps@, es@), 0, seq![' ', '}']));
            assert(seq![' ', '}'] + z =~= seq![' ', '}']);
            assert(out@ =~= o + fe(vx(*e), z));
        }
    }
}

/// 枝の一つの展開（枝 i は「パターン ` => ` 本体」で、後ろは次の枝、最後の枝なら閉じ括弧 tl）。
proof fn farms_step(v: Seq<(Spat, Sx)>, i: nat, tl: Seq<char>)
    requires
        i < v.len(),
    ensures
        farms(v, i, tl) == fpat(v[i as int].0, Seq::empty()) + (seq![' ', '=', '>', ' '] + fe(
            v[i as int].1,
            Seq::empty(),
        )) + (if i + 1 == v.len() {
            tl
        } else {
            seq![',', ' '] + farms(v, (i + 1) as nat, tl)
        }),
{
    reveal_with_fuel(farms, 1);
    let p = v[i as int].0;
    let body = v[i as int].1;
    let t = if i + 1 == v.len() { tl } else { seq![',', ' '] + farms(v, (i + 1) as nat, tl) };
    fe_app(body, t);
    fpat_app(p, Seq::empty(), seq![' ', '=', '>', ' '] + fe(body, t));
    assert(Seq::<char>::empty() + (seq![' ', '=', '>', ' '] + fe(body, t)) =~= seq![' ', '=', '>', ' '] + fe(body, t));
    assert(seq![' ', '=', '>', ' '] + fe(body, t) =~= (seq![' ', '=', '>', ' '] + fe(body, Seq::empty())) + t);
}

/// match の枝の並びと閉じ括弧 ` }`（枝は「パターン ` => ` 本体」、枝の間は `, `）。
/// 本体の列が枝より短いときは unit を出す（対応する本体のない枝。varms と同じ）。
#[verifier::rlimit(15)]
fn push_arms(out: &mut Vec<char>, ps: &Vec<SPat>, es: &Vec<SExpr>)
    ensures
        final(out)@ == old(out)@ + farms(varms(ps@, es@), 0, seq![' ', '}']),
    decreases es, 0nat,
{
    let ghost o = out@;
    let ghost v = varms(ps@, es@);
    let ghost tl = seq![' ', '}'];
    let mut i: usize = 0;
    proof {
        reveal_with_fuel(farms, 1);
    }
    while i < ps.len()
        invariant
            v == varms(ps@, es@),
            i <= ps@.len(),
            o + farms(v, 0, tl) == out@ + farms(v, i as nat, tl),
        decreases ps@.len() - i,
    {
        proof {
            vstd::std_specs::vec::axiom_vec_index_decreases(*ps, i as int);
            assert(v[i as int].0 == vpat(ps@[i as int]));
            if (i as int) < es@.len() {
                assert(v[i as int].1 == vx(es@[i as int]));
            } else {
                assert(v[i as int].1 == Sx::Unit);
            }
        }
        let ghost before = out@;
        push_pat(out, &ps[i]);
        push4(out, ' ', '=', '>', ' ');
        if i < es.len() {
            proof {
                vstd::std_specs::vec::axiom_vec_index_decreases(*es, i as int);
            }
            push_e(out, &es[i]);
        } else {
            push_kw(out, Kw::Unit);
        }
        if i + 1 < ps.len() {
            push2(out, ',', ' ');
        }
        proof {
            farms_step(v, i as nat, tl);
            if i + 1 == ps@.len() {
                reveal_with_fuel(farms, 1);
            }
        }
        i += 1;
    }
    push2(out, ' ', '}');
    proof {
        reveal_with_fuel(farms, 1);
        assert(out@ =~= o + farms(v, 0, tl));
    }
}

/// 枝の左辺（パターン）の印字（後ろに続きを付けない）。
fn push_pat(out: &mut Vec<char>, p: &SPat)
    ensures
        final(out)@ == old(out)@ + fpat(vpat(*p), Seq::empty()),
{
    let ghost o = out@;
    let ghost z = Seq::<char>::empty();
    match p {
        SPat::Ctor(c, bs) => {
            append_chars(out, c);
            if bs.len() > 0 {
                push1(out, '(');
                push_binds(out, bs);
                push1(out, ')');
                proof {
                    fbinds_app(vnames(bs@), 0, z, seq![')']);
                    assert(z + seq![')'] =~= seq![')'] + z);
                }
            }
        },
        SPat::Ok(x) => {
            push_kw(out, Kw::Ok);
            push1(out, '(');
            append_chars(out, x);
            push1(out, ')');
        },
        SPat::Err(x) => {
            push_kw(out, Kw::Err);
            push1(out, '(');
            append_chars(out, x);
            push1(out, ')');
        },
        SPat::Some(x) => {
            push_kw(out, Kw::Some);
            push1(out, '(');
            append_chars(out, x);
            push1(out, ')');
        },
        SPat::None => push_kw(out, Kw::None),
        SPat::Wild => push1(out, '_'),
    }
    proof {
        assert(out@ =~= o + fpat(vpat(*p), z));
    }
}

/// 構築子のパターンの束縛の並び（閉じ括弧の前まで）。
fn push_binds(out: &mut Vec<char>, bs: &Vec<Vec<char>>)
    ensures
        final(out)@ == old(out)@ + fbinds(vnames(bs@), 0, Seq::empty()),
{
    let ghost o = out@;
    let ghost z = Seq::<char>::empty();
    let ghost v = vnames(bs@);
    let mut i: usize = 0;
    while i < bs.len()
        invariant
            v == vnames(bs@),
            i <= bs@.len(),
            o + fbinds(v, 0, z) == out@ + (if i < bs@.len() { fbinds(v, i as nat, z) } else { z }),
        decreases bs@.len() - i,
    {
        proof {
            reveal_with_fuel(fbinds, 1);
            assert(v[i as int] == bs@[i as int]@);
        }
        append_chars(out, &bs[i]);
        if i + 1 < bs.len() {
            push2(out, ',', ' ');
        }
        i += 1;
    }
}

#[verifier::rlimit(100)]
fn push_inj(out: &mut Vec<char>, e: &SExpr)
    requires
        e is Inj,
    ensures
        final(out)@ == old(out)@ + fe(vx(*e), Seq::empty()),
    decreases e, 0nat,
{
    let ghost o = out@;
    let ghost z = Seq::<char>::empty();
    if let SExpr::Inj(ok, t, u, a) = e {
        push_kw(out, if *ok { Kw::Ok } else { Kw::Err });
        push1(out, '<');
        push_ty(out, t);
        push2(out, ',', ' ');
        push_ty(out, u);
        push2(out, '>', '(');
        push_e(out, a);
        push1(out, ')');
        proof {
            fe_app(vx(**a), seq![')'] + z);
            let ku = seq!['>', '('] + fe(vx(**a), seq![')'] + z);
            ft_app(*u, ku);
            ft_app(*t, seq![',', ' '] + ft(*u, ku));
            assert(out@ =~= o + fe(vx(*e), z));
        }
    }
}

fn push_matchr(out: &mut Vec<char>, e: &SExpr)
    requires
        e is MatchR,
    ensures
        final(out)@ == old(out)@ + fe(vx(*e), Seq::empty()),
    decreases e, 0nat,
{
    let ghost o = out@;
    let ghost z = Seq::<char>::empty();
    if let SExpr::MatchR(m, x, a, y, b) = e {
        push_kw(out, Kw::MatchResult);
        push1(out, '(');
        push_e(out, m);
        push3(out, ',', ' ', '|');
        append_chars(out, x);
        push2(out, '|', ' ');
        push_e(out, a);
        push3(out, ',', ' ', '|');
        append_chars(out, y);
        push2(out, '|', ' ');
        push_e(out, b);
        push1(out, ')');
        proof {
            fe_app(vx(**b), seq![')'] + z);
            let ka = seq![',', ' ', '|'] + (y@ + (seq!['|', ' '] + fe(vx(**b), seq![')'] + z)));
            fe_app(vx(**a), ka);
            fe_app(vx(**m), seq![',', ' ', '|'] + (x@ + (seq!['|', ' '] + fe(vx(**a), ka))));
            assert(out@ =~= o + fe(vx(*e), z));
        }
    }
}

fn builtin_kw(b: Builtin) -> (k: Kw)
    ensures
        k == bkw(b),
{
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

/// 引数列と閉じ括弧。
fn push_args(out: &mut Vec<char>, es: &Vec<SExpr>)
    ensures
        final(out)@ == old(out)@ + fargs(vxs(*es), 0, Seq::empty()),
    decreases es, 0nat,
{
    let ghost o = out@;
    let ghost z = Seq::<char>::empty();
    let ghost v = vxs(*es);
    if es.len() == 0 {
        push1(out, ')');
        return;
    }
    let mut i: usize = 0;
    while i < es.len()
        invariant
            v == vxs(*es),
            es@.len() > 0,
            i <= es@.len(),
            o + fargs(v, 0, z) == out@ + (if i < es@.len() { fargs(v, i as nat, z) } else { z }),
        decreases es@.len() - i,
    {
        proof {
            vstd::std_specs::vec::axiom_vec_index_decreases(*es, i as int);
            assert(v[i as int] == vx(es@[i as int]));
        }
        let ghost before = out@;
        push_e(out, &es[i]);
        if i + 1 == es.len() {
            push1(out, ')');
            proof {
                fe_app(v[i as int], seq![')'] + z);
                assert(before + fargs(v, i as nat, z) =~= out@ + z);
            }
        } else {
            push2(out, ',', ' ');
            proof {
                fe_app(v[i as int], seq![',', ' '] + fargs(v, (i + 1) as nat, z));
                assert(before + fargs(v, i as nat, z) =~= out@ + fargs(v, (i + 1) as nat, z));
            }
        }
        i += 1;
    }
    proof {
        assert(out@ + z =~= out@);
    }
}

fn push_params(out: &mut Vec<char>, ps: &Vec<(Vec<char>, Ty)>)
    ensures
        final(out)@ == old(out)@ + fps(vps(ps@), 0, Seq::empty()),
{
    let ghost o = out@;
    let ghost z = Seq::<char>::empty();
    let ghost v = vps(ps@);
    if ps.len() == 0 {
        push1(out, ')');
        return;
    }
    let mut i: usize = 0;
    while i < ps.len()
        invariant
            v == vps(ps@),
            ps@.len() > 0,
            i <= ps@.len(),
            o + fps(v, 0, z) == out@ + (if i < ps@.len() { fps(v, i as nat, z) } else { z }),
        decreases ps@.len() - i,
    {
        let ghost before = out@;
        let (x, t) = &ps[i];
        proof {
            assert(v[i as int] == (x@, *t));
        }
        append_chars(out, x);
        push2(out, ':', ' ');
        push_ty(out, t);
        if i + 1 == ps.len() {
            push1(out, ')');
            proof {
                ft_app(*t, seq![')'] + z);
                assert(before + fps(v, i as nat, z) =~= out@ + z);
            }
        } else {
            push2(out, ',', ' ');
            proof {
                ft_app(*t, seq![',', ' '] + fps(v, (i + 1) as nat, z));
                assert(before + fps(v, i as nat, z) =~= out@ + fps(v, (i + 1) as nat, z));
            }
        }
        i += 1;
    }
    proof {
        assert(out@ + z =~= out@);
    }
}

/// レコード型の宣言（`type R = { f: T, .. }`。末尾のカンマは tc）。
fn push_recty(out: &mut Vec<char>, r: &Vec<char>, fs: &Vec<(Vec<char>, Ty)>, tc: bool)
    ensures
        final(out)@ == old(out)@ + fd(Sd::RecTy(r@, vps(fs@), tc), Seq::empty()),
{
    let ghost o = out@;
    let ghost z = Seq::<char>::empty();
    push5(out, 't', 'y', 'p', 'e', ' ');
    append_chars(out, r);
    push5(out, ' ', '=', ' ', '{', ' ');
    push_fds(out, fs);
    if tc {
        push3(out, ',', ' ', '}');
        push1(out, '\n');
        proof {
            ffd_app(vps(fs@), 0, seq![',', ' ', '}'] + seq!['\n'] + z);
            assert(out@ =~= o + fd(Sd::RecTy(r@, vps(fs@), tc), z));
        }
    } else {
        push2(out, ' ', '}');
        push1(out, '\n');
        proof {
            ffd_app(vps(fs@), 0, seq![' ', '}'] + seq!['\n'] + z);
            assert(out@ =~= o + fd(Sd::RecTy(r@, vps(fs@), tc), z));
        }
    }
}

/// 型の並び（カンマ区切り。後ろに続きはない）。
fn push_stys(out: &mut Vec<char>, ps: &Vec<Ty>)
    ensures
        final(out)@ == old(out)@ + ftys(ps@, 0, Seq::empty()),
{
    let ghost o = out@;
    let ghost z = Seq::<char>::empty();
    let mut i: usize = 0;
    while i < ps.len()
        invariant
            i <= ps@.len(),
            o + ftys(ps@, 0, z) == out@ + (if i < ps@.len() { ftys(ps@, i as nat, z) } else { z }),
        decreases ps@.len() - i,
    {
        let ghost tail = if i + 1 == ps@.len() { z } else { seq![',', ' '] + ftys(ps@, (i + 1) as nat, z) };
        proof {
            reveal_with_fuel(ftys, 1);
        }
        push_ty(out, &ps[i]);
        proof {
            ft_app(ps@[i as int], tail);
        }
        if i + 1 < ps.len() {
            push2(out, ',', ' ');
        }
        i += 1;
    }
}

/// 直和型の構築子一つ：名前と、中身の型の並び（空なら括弧もない）。
fn push_svar(out: &mut Vec<char>, c: &Vec<char>, ps: &Vec<Ty>)
    ensures
        final(out)@ == old(out)@ + (c@ + fpay(ps@, Seq::empty())),
{
    let ghost o = out@;
    let ghost z = Seq::<char>::empty();
    append_chars(out, c);
    if ps.len() > 0 {
        push1(out, '(');
        push_stys(out, ps);
        push1(out, ')');
        proof {
            ftys_app(ps@, 0, seq![')'] + z);
            assert(out@ =~= o + (c@ + fpay(ps@, z)));
        }
    } else {
        proof {
            assert(out@ =~= o + c@);
        }
    }
}

/// 直和型の構築子の並び（` | ` で区切る。後ろに続きはない）。
fn push_svars(out: &mut Vec<char>, vs: &Vec<(Vec<char>, Vec<Ty>)>)
    ensures
        final(out)@ == old(out)@ + fvars(vvars(vs@), 0, Seq::empty()),
{
    let ghost o = out@;
    let ghost z = Seq::<char>::empty();
    let ghost v = vvars(vs@);
    let mut i: usize = 0;
    while i < vs.len()
        invariant
            v == vvars(vs@),
            i <= vs@.len(),
            o + fvars(v, 0, z) == out@ + (if i < vs@.len() { fvars(v, i as nat, z) } else { z }),
        decreases vs@.len() - i,
    {
        let ghost tail = if i + 1 == vs@.len() { z } else { seq![' ', '|', ' '] + fvars(v, (i + 1) as nat, z) };
        proof {
            reveal_with_fuel(fvars, 1);
            assert(v[i as int].0 == vs@[i as int].0@);
            assert(v[i as int].1 == vs@[i as int].1@);
            fpay_app(v[i as int].1, tail);
        }
        push_svar(out, &vs[i].0, &vs[i].1);
        if i + 1 < vs.len() {
            push3(out, ' ', '|', ' ');
        }
        i += 1;
    }
}

/// 直和型の宣言（`type S = V1 | V2(T, U)` と改行）。
fn push_sumty(out: &mut Vec<char>, r: &Vec<char>, vs: &Vec<(Vec<char>, Vec<Ty>)>)
    ensures
        final(out)@ == old(out)@ + fd(Sd::Sum(r@, vvars(vs@)), Seq::empty()),
{
    let ghost o = out@;
    let ghost z = Seq::<char>::empty();
    push5(out, 't', 'y', 'p', 'e', ' ');
    append_chars(out, r);
    push3(out, ' ', '=', ' ');
    push_svars(out, vs);
    push1(out, '\n');
    proof {
        fvars_app(vvars(vs@), 0, seq!['\n'] + z);
        assert(out@ =~= o + fd(Sd::Sum(r@, vvars(vs@)), z));
    }
}

fn push_decl(out: &mut Vec<char>, x: &SDecl)
    ensures
        final(out)@ == old(out)@ + fd(vd(*x), Seq::empty()),
{
    let ghost o = out@;
    let ghost z = Seq::<char>::empty();
    match x {
        SDecl::Fn(f, ps, r, b) => {
            push_kw(out, Kw::Fn);
            push1(out, ' ');
            append_chars(out, f);
            push1(out, '(');
            push_params(out, ps);
            push4(out, ' ', '-', '>', ' ');
            push_ty(out, r);
            push3(out, ' ', '=', ' ');
            push_e(out, b);
            push1(out, '\n');
            proof {
                fe_app(vx(*b), seq!['\n'] + z);
                let kr = seq![' ', '=', ' '] + fe(vx(*b), seq!['\n'] + z);
                ft_app(*r, kr);
                fps_app(vps(ps@), 0, seq![' ', '-', '>', ' '] + ft(*r, kr));
            }
        },
        SDecl::Entry(n) => {
            push_kw(out, Kw::Entry);
            push1(out, ' ');
            append_chars(out, n);
            push1(out, '\n');
        },
        SDecl::RecTy(r, fs, tc) => {
            push_recty(out, r, fs, *tc);
        },
        SDecl::Sum(r, vs) => {
            push_sumty(out, r, vs);
        },
    }
    proof {
        assert(out@ =~= o + fd(vd(*x), z));
    }
}

/// 正準ソース canonical_source(P)。
pub fn format_e(p: &Vec<SDecl>) -> (r: Vec<char>)
    ensures
        r@ == fds(vds(p@), 0),
{
    let ghost v = vds(p@);
    let mut out: Vec<char> = Vec::new();
    let mut i: usize = 0;
    proof {
        assert(Seq::<char>::empty() + fds(v, 0) =~= fds(v, 0));
    }
    while i < p.len()
        invariant
            v == vds(p@),
            i <= p@.len(),
            fds(v, 0) == out@ + fds(v, i as nat),
        decreases p@.len() - i,
    {
        let ghost before = out@;
        push_decl(&mut out, &p[i]);
        proof {
            assert(v[i as int] == vd(p@[i as int]));
            fd_app(v[i as int], fds(v, (i + 1) as nat));
            assert(before + fds(v, i as nat) =~= out@ + fds(v, (i + 1) as nat));
        }
        i += 1;
    }
    proof {
        assert(out@ + fds(v, i as nat) =~= out@);
    }
    out
}

} // verus!
