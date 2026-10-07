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
    Id(Vec<char>),
    Kw(Kw),
    Sym(char),
    Arrow,
}

pub open spec fn vtok(t: ETok) -> Tok {
    match t {
        ETok::Int(n) => Tok::Int(n@),
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
}

pub enum SDecl {
    Fn(Vec<char>, Vec<(Vec<char>, Ty)>, Ty, SExpr),
    Entry(Vec<char>),
}

pub open spec fn vx(e: SExpr) -> Sx
    decreases e,
{
    match e {
        SExpr::Int(n) => Sx::Int(n@),
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

pub open spec fn vd(x: SDecl) -> Sd {
    match x {
        SDecl::Fn(f, ps, r, b) => Sd::Fn(f@, vps(ps@), r, vx(b)),
        SDecl::Entry(n) => Sd::Entry(n@),
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
        || c == '|'
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
        } else if c3e(w, 'f', 's', 't') {
            Some(Kw::Fst)
        } else if c3e(w, 's', 'n', 'd') {
            Some(Kw::Snd)
        } else if c3e(w, 'l', 'e', 't') {
            Some(Kw::Let)
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
        } else {
            None
        }
    } else if n == 5 {
        if c5e(w, 'e', 'n', 't', 'r', 'y') {
            Some(Kw::Entry)
        } else if c5e(w, 'f', 'a', 'l', 's', 'e') {
            Some(Kw::False)
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
        } else {
            None
        }
    } else if n == 7 {
        if c6e(w, 'r', 'e', 'v', 'e', 'r', 's') && w[6] == 'e' {
            Some(Kw::Reverse)
        } else {
            None
        }
    } else if n == 12 {
        if c6e(w, 'm', 'a', 't', 'c', 'h', '_') && w[6] == 'o' && w[7] == 'p' && w[8] == 't' && w[9] == 'i'
            && w[10] == 'o' && w[11] == 'n' {
            Some(Kw::MatchOption)
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
        k == Kw::Fn || k == Kw::Entry || k == Kw::In,
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
        Kw::TList | Kw::TOption => {
            if !sym_e(ts, i + 1, '<') {
                return None;
            }
            match pt_e(ts, i + 2, d - 1) {
                Some((a, j)) => if sym_e(ts, j, '>') {
                    let t = match k {
                        Kw::TList => Ty::List(Box::new(a)),
                        _ => Ty::Option(Box::new(a)),
                    };
                    Some((t, j + 1))
                } else {
                    None
                },
                None => None,
            }
        },
        Kw::TPair => {
            if !sym_e(ts, i + 1, '<') {
                return None;
            }
            match pt_e(ts, i + 2, d - 1) {
                Some((a, j)) => if sym_e(ts, j, ',') {
                    match pt_e(ts, j + 1, d - 1) {
                        Some((b, m)) => if sym_e(ts, m, '>') {
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

pub fn pe_e(ts: &Vec<ETok>, i: usize, d: usize, td: usize) -> (r: Option<(SExpr, usize)>)
    requires
        small(ts@),
        i <= ts.len(),
    ensures
        pe_ok(ts@, i, d, td, r),
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
        ETok::Id(x) => {
            if !ident_ok_e(x) {
                None
            } else if sym_e(ts, i + 1, '(') {
                match pargs_e(ts, i + 2, d - 1, td) {
                    Some((es, j)) => Some((SExpr::Call(clone_chars(x), es), j)),
                    None => None,
                }
            } else {
                Some((SExpr::Var(clone_chars(x)), i + 1))
            }
        },
        ETok::Kw(k) => match *k {
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
            _ => pe_builtin_e(ts, i, d, td),
        },
        _ => None,
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
        Kw::Fst => Some(Builtin::Fst),
        Kw::Snd => Some(Builtin::Snd),
        Kw::Cons => Some(Builtin::Cons),
        Kw::Concat => Some(Builtin::Concat),
        Kw::Reverse => Some(Builtin::Reverse),
        Kw::Length => Some(Builtin::Length),
        Kw::Uncons => Some(Builtin::Uncons),
        _ => None,
    }
}

fn pe_builtin_e(ts: &Vec<ETok>, i: usize, d: usize, td: usize) -> (r: Option<(SExpr, usize)>)
    requires
        small(ts@),
        i < ts.len(),
        d > 0,
        ts@[i as int] is Kw,
        ({
            let k = ts@[i as int]->Kw_0;
            k != Kw::True && k != Kw::False && k != Kw::Unit && k != Kw::List && k != Kw::Some && k != Kw::None
                && k != Kw::Pair && k != Kw::Let && k != Kw::If && k != Kw::Fold && k != Kw::MatchOption
        }),
    ensures
        pe_ok(ts@, i, d, td, r),
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
        small(ts@),
        i < ts.len(),
        d > 0,
        vtok(ts@[i as int]) == Tok::Kw(Kw::List),
    ensures
        pe_ok(ts@, i, d, td, r),
    decreases d, 0nat,
{
    let ghost tv = vtoks(ts@);
    proof {
        assert(tv[i as int] == vtok(ts@[i as int]));
    }
    if !sym_e(ts, i + 1, '[') {
        return None;
    }
    match pt_e(ts, i + 2, td) {
        Some((t, j)) => if sym_e(ts, j, ']') && sym_e(ts, j + 1, '(') {
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
        small(ts@),
        i < ts.len(),
        d > 0,
        vtok(ts@[i as int]) == Tok::Kw(Kw::Some),
    ensures
        pe_ok(ts@, i, d, td, r),
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
        small(ts@),
        i < ts.len(),
        d > 0,
        vtok(ts@[i as int]) == Tok::Kw(Kw::None),
    ensures
        pe_ok(ts@, i, d, td, r),
    decreases d, 0nat,
{
    let ghost tv = vtoks(ts@);
    proof {
        assert(tv[i as int] == vtok(ts@[i as int]));
    }
    if !sym_e(ts, i + 1, '[') {
        return None;
    }
    match pt_e(ts, i + 2, td) {
        Some((t, j)) => if sym_e(ts, j, ']') {
            Some((SExpr::None(t), j + 1))
        } else {
            None
        },
        None => None,
    }
}

fn pe_pair_e(ts: &Vec<ETok>, i: usize, d: usize, td: usize) -> (r: Option<(SExpr, usize)>)
    requires
        small(ts@),
        i < ts.len(),
        d > 0,
        vtok(ts@[i as int]) == Tok::Kw(Kw::Pair),
    ensures
        pe_ok(ts@, i, d, td, r),
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
        pe_ok(ts@, i, d, td, r),
    decreases d, 0nat,
{
    let ghost tv = vtoks(ts@);
    proof {
        assert(tv[i as int] == vtok(ts@[i as int]));
    }
    let x = match idt_e(ts, i + 1) {
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
        pe_ok(ts@, i, d, td, r),
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
        pe_ok(ts@, i, d, td, r),
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
    let a = match idt_e(ts, m + 2) {
        Some(a) => a,
        None => return None,
    };
    let x = match idt_e(ts, m + 4) {
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
        pe_ok(ts@, i, d, td, r),
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
    let x = match idt_e(ts, q + 2) {
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
    decreases d, 2nat,
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
        let x = match idt_e(ts, k) {
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
        Kw::Fst => push3(out, 'f', 's', 't'),
        Kw::Snd => push3(out, 's', 'n', 'd'),
        Kw::Cons => push4(out, 'c', 'o', 'n', 's'),
        Kw::Concat => push6(out, 'c', 'o', 'n', 'c', 'a', 't'),
        Kw::Reverse => push7(out, 'r', 'e', 'v', 'e', 'r', 's', 'e'),
        Kw::Length => push6(out, 'l', 'e', 'n', 'g', 't', 'h'),
        Kw::Uncons => push6(out, 'u', 'n', 'c', 'o', 'n', 's'),
        Kw::MatchOption => {
            push6(out, 'm', 'a', 't', 'c', 'h', '_');
            push6(out, 'o', 'p', 't', 'i', 'o', 'n');
            proof {
                assert(out@ =~= old(out)@ + kwt(k));
            }
        },
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
        Ty::List(a) => {
            push_kw(out, Kw::TList);
            push1(out, '<');
            push_ty(out, a);
            push1(out, '>');
            proof {
                ft_app(**a, seq!['>'] + z);
                assert(out@ =~= o + ft(*t, z));
            }
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
        Ty::Pair(a, b) => {
            push_kw(out, Kw::TPair);
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
        SExpr::Bool(b) => push_kw(out, if *b { Kw::True } else { Kw::False }),
        SExpr::Unit => push_kw(out, Kw::Unit),
        SExpr::Var(x) => append_chars(out, x),
        SExpr::List(t, es) => {
            push_kw(out, Kw::List);
            push1(out, '[');
            push_ty(out, t);
            push2(out, ']', '(');
            push_args(out, es);
            proof {
                ft_app(*t, seq![']', '('] + fargs(vxs(*es), 0, z));
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
            push1(out, '[');
            push_ty(out, t);
            push1(out, ']');
            proof {
                ft_app(*t, seq![']'] + z);
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
    }
    proof {
        assert(out@ =~= o + fe(vx(*e), z));
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
        Builtin::Fst => Kw::Fst,
        Builtin::Snd => Kw::Snd,
        Builtin::Cons => Kw::Cons,
        Builtin::Concat => Kw::Concat,
        Builtin::Reverse => Kw::Reverse,
        Builtin::Length => Kw::Length,
        Builtin::Uncons => Kw::Uncons,
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
