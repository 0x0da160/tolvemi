//! 値の正準 JSON（設計書 §9）：encoder の検証と、正準形の往復性・型整合性（§11.2 の 9 の一部）。
//!
//! - `encode` は spec の `enc` どおりの文字列を出す（出力の encode に使う）。
//! - `dec` は正準形を型に沿って読む spec の復号器で、`roundtrip` により型付き値 v について
//!   `dec(enc(v)) == v`、`dec_typed` により復号結果が型を持つことを示す。
//! 入力に使う strict JSON parser（空白・escape・重複キー拒否を含む）は crates/tlvm にあり未検証。

use crate::bigint::*;
use crate::proof::*;
use crate::spec::*;
use crate::value::*;
use std::rc::Rc;
use vstd::prelude::*;

verus! {

// ------------------------------------------------------------------ 字句

#[verifier::opaque]
pub open spec fn l_int1() -> Seq<char> {
    seq!['{', '"', 't', 'a', 'g', '"', ':', '"', 'i', 'n', 't', '"', ',', '"', 'v', 'a', 'l', 'u', 'e', '"', ':', '"']
}

#[verifier::opaque]
pub open spec fn l_int2() -> Seq<char> {
    seq!['"', '}']
}

#[verifier::opaque]
pub open spec fn l_true() -> Seq<char> {
    seq!['{', '"', 't', 'a', 'g', '"', ':', '"', 'b', 'o', 'o', 'l', '"', ',', '"', 'v', 'a', 'l', 'u', 'e', '"', ':', 't', 'r', 'u', 'e', '}']
}

#[verifier::opaque]
pub open spec fn l_false() -> Seq<char> {
    seq!['{', '"', 't', 'a', 'g', '"', ':', '"', 'b', 'o', 'o', 'l', '"', ',', '"', 'v', 'a', 'l', 'u', 'e', '"', ':', 'f', 'a', 'l', 's', 'e', '}']
}

#[verifier::opaque]
pub open spec fn l_unit() -> Seq<char> {
    seq!['{', '"', 't', 'a', 'g', '"', ':', '"', 'u', 'n', 'i', 't', '"', '}']
}

#[verifier::opaque]
pub open spec fn l_none() -> Seq<char> {
    seq!['{', '"', 't', 'a', 'g', '"', ':', '"', 'n', 'o', 'n', 'e', '"', '}']
}

#[verifier::opaque]
pub open spec fn l_some() -> Seq<char> {
    seq!['{', '"', 't', 'a', 'g', '"', ':', '"', 's', 'o', 'm', 'e', '"', ',', '"', 'v', 'a', 'l', 'u', 'e', '"', ':']
}

#[verifier::opaque]
pub open spec fn l_close() -> Seq<char> {
    seq!['}']
}

#[verifier::opaque]
pub open spec fn l_pair1() -> Seq<char> {
    seq!['{', '"', 't', 'a', 'g', '"', ':', '"', 'p', 'a', 'i', 'r', '"', ',', '"', 'l', 'e', 'f', 't', '"', ':']
}

#[verifier::opaque]
pub open spec fn l_pair2() -> Seq<char> {
    seq![',', '"', 'r', 'i', 'g', 'h', 't', '"', ':']
}

#[verifier::opaque]
pub open spec fn l_list1() -> Seq<char> {
    seq!['{', '"', 't', 'a', 'g', '"', ':', '"', 'l', 'i', 's', 't', '"', ',', '"', 'i', 't', 'e', 'm', 's', '"', ':', '[']
}

#[verifier::opaque]
pub open spec fn l_comma() -> Seq<char> {
    seq![',']
}

#[verifier::opaque]
pub open spec fn l_list2() -> Seq<char> {
    seq![']', '}']
}


/// 字句の長さと、復号で区別に使う文字。
pub proof fn lits()
    ensures
        l_int1().len() == 22 && l_int1()[0] == '{',
        l_int2().len() == 2 && l_int2()[0] == '"',
        l_true().len() == 27 && l_true()[0] == '{' && l_true()[22] == 't',
        l_false().len() == 28 && l_false()[0] == '{' && l_false()[22] == 'f',
        l_unit().len() == 14 && l_unit()[0] == '{',
        l_none().len() == 14 && l_none()[0] == '{' && l_none()[8] == 'n',
        l_some().len() == 22 && l_some()[0] == '{' && l_some()[8] == 's',
        l_close().len() == 1,
        l_pair1().len() == 21 && l_pair1()[0] == '{',
        l_pair2().len() == 9,
        l_list1().len() == 23 && l_list1()[0] == '{',
        l_comma().len() == 1 && l_comma()[0] == ',',
        l_list2().len() == 2 && l_list2()[0] == ']',
{
    reveal(l_int1);
    reveal(l_int2);
    reveal(l_true);
    reveal(l_false);
    reveal(l_unit);
    reveal(l_none);
    reveal(l_some);
    reveal(l_close);
    reveal(l_pair1);
    reveal(l_pair2);
    reveal(l_list1);
    reveal(l_comma);
    reveal(l_list2);
}

// ------------------------------------------------------------------ encode の spec

pub open spec fn enc(v: Val) -> Seq<char>
    decreases v, 1nat,
{
    match v {
        Val::Int(n) => l_int1() + int_dec(n) + l_int2(),
        Val::Bool(b) => if b {
            l_true()
        } else {
            l_false()
        },
        Val::Unit => l_unit(),
        Val::None => l_none(),
        Val::Some(x) => l_some() + enc(*x) + l_close(),
        Val::Pair(a, b) => l_pair1() + enc(*a) + l_pair2() + enc(*b) + l_close(),
        Val::List(s) => l_list1() + enc_items(s, 0) + l_list2(),
    }
}

pub open spec fn enc_items(s: Seq<Val>, i: nat) -> Seq<char>
    decreases s, s.len() - i,
{
    if i >= s.len() {
        Seq::empty()
    } else {
        (if i > 0 {
            l_comma()
        } else {
            Seq::empty()
        }) + enc(s[i as int]) + enc_items(s, i + 1)
    }
}

// ------------------------------------------------------------------ 検証済み encoder

fn push_int1(out: &mut String)
    ensures
        final(out)@ == old(out)@ + l_int1(),
{
    out.push_str("{\"tag\":\"int\",\"value\":\"");
    proof {
        reveal(l_int1);
        reveal_strlit("{\"tag\":\"int\",\"value\":\"");
        assert("{\"tag\":\"int\",\"value\":\""@ =~= l_int1());
    }
}

fn push_int2(out: &mut String)
    ensures
        final(out)@ == old(out)@ + l_int2(),
{
    out.push_str("\"}");
    proof {
        reveal(l_int2);
        reveal_strlit("\"}");
        assert("\"}"@ =~= l_int2());
    }
}

fn push_true(out: &mut String)
    ensures
        final(out)@ == old(out)@ + l_true(),
{
    out.push_str("{\"tag\":\"bool\",\"value\":true}");
    proof {
        reveal(l_true);
        reveal_strlit("{\"tag\":\"bool\",\"value\":true}");
        assert("{\"tag\":\"bool\",\"value\":true}"@ =~= l_true());
    }
}

fn push_false(out: &mut String)
    ensures
        final(out)@ == old(out)@ + l_false(),
{
    out.push_str("{\"tag\":\"bool\",\"value\":false}");
    proof {
        reveal(l_false);
        reveal_strlit("{\"tag\":\"bool\",\"value\":false}");
        assert("{\"tag\":\"bool\",\"value\":false}"@ =~= l_false());
    }
}

fn push_unit(out: &mut String)
    ensures
        final(out)@ == old(out)@ + l_unit(),
{
    out.push_str("{\"tag\":\"unit\"}");
    proof {
        reveal(l_unit);
        reveal_strlit("{\"tag\":\"unit\"}");
        assert("{\"tag\":\"unit\"}"@ =~= l_unit());
    }
}

fn push_none(out: &mut String)
    ensures
        final(out)@ == old(out)@ + l_none(),
{
    out.push_str("{\"tag\":\"none\"}");
    proof {
        reveal(l_none);
        reveal_strlit("{\"tag\":\"none\"}");
        assert("{\"tag\":\"none\"}"@ =~= l_none());
    }
}

fn push_some(out: &mut String)
    ensures
        final(out)@ == old(out)@ + l_some(),
{
    out.push_str("{\"tag\":\"some\",\"value\":");
    proof {
        reveal(l_some);
        reveal_strlit("{\"tag\":\"some\",\"value\":");
        assert("{\"tag\":\"some\",\"value\":"@ =~= l_some());
    }
}

fn push_close(out: &mut String)
    ensures
        final(out)@ == old(out)@ + l_close(),
{
    out.push_str("}");
    proof {
        reveal(l_close);
        reveal_strlit("}");
        assert("}"@ =~= l_close());
    }
}

fn push_pair1(out: &mut String)
    ensures
        final(out)@ == old(out)@ + l_pair1(),
{
    out.push_str("{\"tag\":\"pair\",\"left\":");
    proof {
        reveal(l_pair1);
        reveal_strlit("{\"tag\":\"pair\",\"left\":");
        assert("{\"tag\":\"pair\",\"left\":"@ =~= l_pair1());
    }
}

fn push_pair2(out: &mut String)
    ensures
        final(out)@ == old(out)@ + l_pair2(),
{
    out.push_str(",\"right\":");
    proof {
        reveal(l_pair2);
        reveal_strlit(",\"right\":");
        assert(",\"right\":"@ =~= l_pair2());
    }
}

fn push_list1(out: &mut String)
    ensures
        final(out)@ == old(out)@ + l_list1(),
{
    out.push_str("{\"tag\":\"list\",\"items\":[");
    proof {
        reveal(l_list1);
        reveal_strlit("{\"tag\":\"list\",\"items\":[");
        assert("{\"tag\":\"list\",\"items\":["@ =~= l_list1());
    }
}

fn push_comma(out: &mut String)
    ensures
        final(out)@ == old(out)@ + l_comma(),
{
    out.push_str(",");
    proof {
        reveal(l_comma);
        reveal_strlit(",");
        assert(","@ =~= l_comma());
    }
}

fn push_list2(out: &mut String)
    ensures
        final(out)@ == old(out)@ + l_list2(),
{
    out.push_str("]}");
    proof {
        reveal(l_list2);
        reveal_strlit("]}");
        assert("]}"@ =~= l_list2());
    }
}

/// 値を正準 JSON で out に追記する。
pub fn encode(v: &Rc<Value>, out: &mut String)
    ensures
        final(out)@ == old(out)@ + enc(view_val(**v)),
    decreases **v, 1nat,
{
    let ghost o = out@;
    match &**v {
        Value::Int(n) => {
            push_int1(out);
            let d = n.to_dec();
            out.push_str(d.as_str());
            push_int2(out);
            proof {
                assert(out@ =~= o + enc(view_val(**v)));
            }
        },
        Value::Bool(b) => {
            if *b {
                push_true(out);
            } else {
                push_false(out);
            }
        },
        Value::Unit => push_unit(out),
        Value::None => push_none(out),
        Value::Some(x) => {
            push_some(out);
            encode(x, out);
            push_close(out);
            proof {
                assert(out@ =~= o + enc(view_val(**v)));
            }
        },
        Value::Pair(a, b) => {
            push_pair1(out);
            encode(a, out);
            push_pair2(out);
            encode(b, out);
            push_close(out);
            proof {
                assert(out@ =~= o + enc(view_val(**v)));
            }
        },
        Value::Nil | Value::Cons(_, _) => {
            push_list1(out);
            let ghost s = sp(dr(v));
            proof {
                assert(s.subrange(0, s.len() as int) =~= s);
            }
            encode_items(v, true, Ghost(s), Ghost(0), out);
            push_list2(out);
            proof {
                assert(out@ =~= o + enc(view_val(**v)));
            }
        },
    }
}

fn encode_items(cur: &Rc<Value>, first: bool, Ghost(s): Ghost<Seq<Val>>, Ghost(j): Ghost<nat>, out: &mut String)
    requires
        j <= s.len(),
        spine(**cur) == s.subrange(j as int, s.len() as int),
        first == (j == 0),
    ensures
        final(out)@ == old(out)@ + enc_items(s, j),
    decreases **cur, 0nat,
{
    let ghost o = out@;
    match &**cur {
        Value::Cons(h, t) => {
            proof {
                spine_step(s, j as int, dr(h), dr(t));
            }
            if !first {
                push_comma(out);
            }
            encode(h, out);
            encode_items(t, false, Ghost(s), Ghost((j + 1) as nat), out);
            proof {
                assert(out@ =~= o + enc_items(s, j));
            }
        },
        _ => {
            proof {
                assert(spine(**cur).len() == 0);
                assert(j == s.len());
                assert(enc_items(s, j) =~= Seq::<char>::empty());
                assert(out@ =~= o + enc_items(s, j));
            }
        },
    }
}

// ------------------------------------------------------------------ 正準形の復号（spec）

/// c の位置 pos から lit が続く。
pub open spec fn at(c: Seq<char>, pos: int, lit: Seq<char>) -> bool {
    0 <= pos && pos + lit.len() <= c.len() && c.subrange(pos, pos + lit.len()) == lit
}

pub open spec fn dval(ch: char) -> int {
    if ch == '0' {
        0
    } else if ch == '1' {
        1
    } else if ch == '2' {
        2
    } else if ch == '3' {
        3
    } else if ch == '4' {
        4
    } else if ch == '5' {
        5
    } else if ch == '6' {
        6
    } else if ch == '7' {
        7
    } else if ch == '8' {
        8
    } else if ch == '9' {
        9
    } else {
        -1
    }
}

/// 数字列の値。
pub open spec fn nat_val(s: Seq<char>) -> Option<nat>
    decreases s.len(),
{
    if s.len() == 0 || dval(s.last()) < 0 {
        None
    } else if s.len() == 1 {
        Some(dval(s.last()) as nat)
    } else {
        match nat_val(s.drop_last()) {
            Some(m) => Some(m * 10 + dval(s.last()) as nat),
            None => None,
        }
    }
}

pub open spec fn int_val(s: Seq<char>) -> Option<int> {
    if s.len() > 0 && s[0] == '-' {
        match nat_val(s.drop_first()) {
            Some(m) => Some(-(m as int)),
            None => None,
        }
    } else {
        match nat_val(s) {
            Some(m) => Some(m as int),
            None => None,
        }
    }
}

/// pos 以降で最初の '"' の位置（なければ c.len()）。
pub open spec fn scan_quote(c: Seq<char>, pos: int) -> int
    decreases c.len() - pos,
{
    if pos < 0 || pos >= c.len() {
        c.len() as int
    } else if c[pos] == '"' {
        pos
    } else {
        scan_quote(c, pos + 1)
    }
}

/// 正準形の値を型 t に沿って読む。成功すれば値と読み終えた位置。
pub open spec fn dec(c: Seq<char>, pos: int, t: Ty) -> Option<(Val, int)>
    decreases t, (c.len() - pos) as nat, 0nat,
{
    if pos < 0 || pos > c.len() {
        None
    } else {
        match t {
            Ty::Int => if at(c, pos, l_int1()) {
                let p1 = pos + l_int1().len();
                let q = scan_quote(c, p1);
                match int_val(c.subrange(p1, q)) {
                    Some(n) => if at(c, q, l_int2()) {
                        Some((Val::Int(n), q + l_int2().len()))
                    } else {
                        None
                    },
                    None => None,
                }
            } else {
                None
            },
            Ty::Bool => if at(c, pos, l_true()) {
                Some((Val::Bool(true), pos + l_true().len()))
            } else if at(c, pos, l_false()) {
                Some((Val::Bool(false), pos + l_false().len()))
            } else {
                None
            },
            Ty::Unit => if at(c, pos, l_unit()) {
                Some((Val::Unit, pos + l_unit().len()))
            } else {
                None
            },
            Ty::Option(el) => if at(c, pos, l_none()) {
                Some((Val::None, pos + l_none().len()))
            } else if at(c, pos, l_some()) {
                match dec(c, pos + l_some().len(), *el) {
                    Some((x, p2)) => if at(c, p2, l_close()) {
                        Some((Val::Some(Box::new(x)), p2 + 1))
                    } else {
                        None
                    },
                    None => None,
                }
            } else {
                None
            },
            Ty::Pair(ta, tb) => if at(c, pos, l_pair1()) {
                match dec(c, pos + l_pair1().len(), *ta) {
                    Some((a, p2)) => if at(c, p2, l_pair2()) {
                        match dec(c, p2 + l_pair2().len(), *tb) {
                            Some((b, p3)) => if at(c, p3, l_close()) {
                                Some((Val::Pair(Box::new(a), Box::new(b)), p3 + 1))
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
            Ty::List(el) => if at(c, pos, l_list1()) {
                match dec_items(c, pos + l_list1().len(), *el, true) {
                    Some((s, p2)) => if at(c, p2, l_list2()) {
                        Some((Val::List(s), p2 + l_list2().len()))
                    } else {
                        None
                    },
                    None => None,
                }
            } else {
                None
            },
        }
    }
}

/// リスト要素の並びを ']' の直前まで読む。
pub open spec fn dec_items(c: Seq<char>, pos: int, el: Ty, first: bool) -> Option<(Seq<Val>, int)>
    decreases el, (c.len() - pos) as nat, 1nat,
{
    if pos < 0 || pos >= c.len() {
        None
    } else if c[pos] == ']' {
        Some((Seq::empty(), pos))
    } else {
        let p = if first {
            pos
        } else {
            pos + 1
        };
        if !first && c[pos] != ',' {
            None
        } else {
            match dec(c, p, el) {
                Some((x, p2)) => if p2 <= pos || p2 > c.len() {
                    None
                } else {
                    match dec_items(c, p2, el, false) {
                        Some((xs, p3)) => Some((seq![x] + xs, p3)),
                        None => None,
                    }
                },
                None => None,
            }
        }
    }
}

// ------------------------------------------------------------------ 往復性と型整合性の証明

pub proof fn at_split(c: Seq<char>, pos: int, x: Seq<char>, y: Seq<char>)
    requires
        at(c, pos, x + y),
    ensures
        at(c, pos, x),
        at(c, pos + x.len(), y),
{
    let xy = x + y;
    assert(c.subrange(pos, pos + x.len()) =~= x) by {
        assert forall|k: int| 0 <= k < x.len() implies c.subrange(pos, pos + x.len())[k] == x[k] by {
            assert(c.subrange(pos, pos + xy.len())[k] == xy[k]);
        }
    }
    assert(c.subrange(pos + x.len(), pos + x.len() + y.len()) =~= y) by {
        assert forall|k: int| 0 <= k < y.len() implies c.subrange(pos + x.len(), pos + x.len() + y.len())[k] == y[k] by {
            assert(c.subrange(pos, pos + xy.len())[x.len() + k] == xy[x.len() + k]);
        }
    }
}

pub proof fn at_char(c: Seq<char>, pos: int, x: Seq<char>, k: int)
    requires
        at(c, pos, x),
        0 <= k < x.len(),
    ensures
        c[pos + k] == x[k],
{
    assert(c.subrange(pos, pos + x.len())[k] == x[k]);
}

pub proof fn digit_dval(d: int)
    requires
        0 <= d < 10,
    ensures
        dval(digit(d)) == d,
{
}

pub proof fn nat_dec_props(n: nat)
    ensures
        nat_dec(n).len() >= 1,
        forall|k: int| 0 <= k < nat_dec(n).len() ==> dval(#[trigger] nat_dec(n)[k]) >= 0,
        nat_val(nat_dec(n)) == Some(n),
    decreases n,
{
    if n < 10 {
        digit_dval(n as int);
    } else {
        nat_dec_props(n / 10);
        let m = nat_dec(n / 10);
        let s = nat_dec(n);
        digit_dval((n % 10) as int);
        assert(s == m.push(digit((n % 10) as int)));
        assert(s.drop_last() =~= m);
        assert forall|k: int| 0 <= k < s.len() implies dval(#[trigger] s[k]) >= 0 by {
            if k < m.len() {
                assert(s[k] == m[k]);
            }
        }
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod(n as int, 10);
        assert(nat_val(s) == Some((n / 10) * 10 + (n % 10) as nat));
    }
}

pub proof fn int_dec_props(n: int)
    ensures
        int_val(int_dec(n)) == Some(n),
        int_dec(n).len() >= 1,
        forall|k: int| 0 <= k < int_dec(n).len() ==> #[trigger] int_dec(n)[k] != '"',
{
    if n < 0 {
        let m = (-n) as nat;
        nat_dec_props(m);
        let s = int_dec(n);
        assert(s.drop_first() =~= nat_dec(m));
        assert forall|k: int| 0 <= k < s.len() implies #[trigger] s[k] != '"' by {
            if k > 0 {
                assert(s[k] == nat_dec(m)[k - 1]);
                assert(dval(nat_dec(m)[k - 1]) >= 0);
            }
        }
    } else {
        nat_dec_props(n as nat);
        let s = int_dec(n);
        assert(dval(s[0]) >= 0);
        assert forall|k: int| 0 <= k < s.len() implies #[trigger] s[k] != '"' by {
            assert(dval(s[k]) >= 0);
        }
    }
}

pub proof fn scan_to(c: Seq<char>, p: int, q: int)
    requires
        0 <= p <= q < c.len(),
        c[q] == '"',
        forall|k: int| p <= k < q ==> #[trigger] c[k] != '"',
    ensures
        scan_quote(c, p) == q,
    decreases q - p,
{
    if p < q {
        scan_to(c, p + 1, q);
    }
}

pub proof fn enc_first(v: Val)
    ensures
        enc(v).len() >= 1,
        enc(v)[0] == '{',
{
    lits();
    match v {
        Val::Int(n) => {
            assert(enc(v) == l_int1() + int_dec(n) + l_int2());
            assert((l_int1() + int_dec(n) + l_int2())[0] == l_int1()[0]);
        },
        Val::Bool(b) => {},
        Val::Unit => {},
        Val::None => {},
        Val::Some(x) => {
            assert((l_some() + enc(*x) + l_close())[0] == l_some()[0]);
        },
        Val::Pair(a, b) => {
            assert((l_pair1() + enc(*a) + l_pair2() + enc(*b) + l_close())[0] == l_pair1()[0]);
        },
        Val::List(s) => {
            assert((l_list1() + enc_items(s, 0) + l_list2())[0] == l_list1()[0]);
        },
    }
}

/// 往復性：型 t を持つ値 v の正準形を読むと v に戻る（後ろに何が続いてもよい）。
pub proof fn roundtrip(c: Seq<char>, pos: int, v: Val, t: Ty)
    requires
        val_type(v, t),
        at(c, pos, enc(v)),
    ensures
        dec(c, pos, t) == Some((v, pos + enc(v).len())),
    decreases v, 0nat,
{
    lits();
    match v {
        Val::Int(n) => roundtrip_int(c, pos, n),
        Val::Bool(b) => {
            if !b {
                at_char(c, pos, l_false(), 22);
                if at(c, pos, l_true()) {
                    at_char(c, pos, l_true(), 22);
                }
            }
        },
        Val::Unit => {},
        Val::None => {},
        Val::Some(x) => {
            let el = *t->Option_0;
            at_split(c, pos, l_some() + enc(*x), l_close());
            at_split(c, pos, l_some(), enc(*x));
            roundtrip(c, pos + l_some().len(), *x, el);
            roundtrip_some(c, pos, *x, el);
        },
        Val::Pair(a, b) => {
            let ta = *t->Pair_0;
            let tb = *t->Pair_1;
            at_split(c, pos, l_pair1() + enc(*a) + l_pair2() + enc(*b), l_close());
            at_split(c, pos, l_pair1() + enc(*a) + l_pair2(), enc(*b));
            at_split(c, pos, l_pair1() + enc(*a), l_pair2());
            at_split(c, pos, l_pair1(), enc(*a));
            roundtrip(c, pos + l_pair1().len(), *a, ta);
            roundtrip(c, pos + l_pair1().len() + enc(*a).len() + l_pair2().len(), *b, tb);
            roundtrip_pair(c, pos, *a, *b, ta, tb);
        },
        Val::List(s) => {
            let el = *t->List_0;
            assert(t == Ty::List(Box::new(el)));
            val_type_list(s, el);
            let items = enc_items(s, 0);
            assert(l_list1() + items + l_list2() == l_list1() + (items + l_list2()));
            at_split(c, pos, l_list1(), items + l_list2());
            at_split(c, pos + l_list1().len(), items, l_list2());
            roundtrip_items(c, pos + l_list1().len(), s, 0, el);
            assert(s.subrange(0, s.len() as int) =~= s);
            roundtrip_list(c, pos, s, el);
        },
    }
}

proof fn roundtrip_int(c: Seq<char>, pos: int, n: int)
    requires
        at(c, pos, enc(Val::Int(n))),
    ensures
        dec(c, pos, Ty::Int) == Some((Val::Int(n), pos + enc(Val::Int(n)).len())),
{
    lits();
    let d = int_dec(n);
    at_split(c, pos, l_int1() + d, l_int2());
    at_split(c, pos, l_int1(), d);
    let p1 = pos + l_int1().len();
    let q = p1 + d.len();
    int_dec_props(n);
    at_char(c, q, l_int2(), 0);
    assert forall|k: int| p1 <= k < q implies #[trigger] c[k] != '"' by {
        at_char(c, p1, d, k - p1);
    }
    scan_to(c, p1, q);
    assert(c.subrange(p1, q) =~= d);
}

proof fn roundtrip_some(c: Seq<char>, pos: int, x: Val, el: Ty)
    requires
        at(c, pos, l_some()),
        dec(c, pos + l_some().len(), el) == Some((x, pos + l_some().len() + enc(x).len())),
        at(c, pos + l_some().len() + enc(x).len(), l_close()),
    ensures
        dec(c, pos, Ty::Option(Box::new(el))) == Some((Val::Some(Box::new(x)), pos + enc(Val::Some(Box::new(x))).len())),
{
    lits();
    at_char(c, pos, l_some(), 8);
    if at(c, pos, l_none()) {
        at_char(c, pos, l_none(), 8);
    }
}

proof fn roundtrip_pair(c: Seq<char>, pos: int, a: Val, b: Val, ta: Ty, tb: Ty)
    requires
        at(c, pos, l_pair1()),
        dec(c, pos + l_pair1().len(), ta) == Some((a, pos + l_pair1().len() + enc(a).len())),
        at(c, pos + l_pair1().len() + enc(a).len(), l_pair2()),
        dec(c, pos + l_pair1().len() + enc(a).len() + l_pair2().len(), tb) == Some(
            (b, pos + l_pair1().len() + enc(a).len() + l_pair2().len() + enc(b).len()),
        ),
        at(c, pos + l_pair1().len() + enc(a).len() + l_pair2().len() + enc(b).len(), l_close()),
    ensures
        dec(c, pos, Ty::Pair(Box::new(ta), Box::new(tb))) == Some(
            (Val::Pair(Box::new(a), Box::new(b)), pos + enc(Val::Pair(Box::new(a), Box::new(b))).len()),
        ),
{
    lits();
}

proof fn roundtrip_list(c: Seq<char>, pos: int, s: Seq<Val>, el: Ty)
    requires
        at(c, pos, l_list1()),
        dec_items(c, pos + l_list1().len(), el, true) == Some((s, pos + l_list1().len() + enc_items(s, 0).len())),
        at(c, pos + l_list1().len() + enc_items(s, 0).len(), l_list2()),
    ensures
        dec(c, pos, Ty::List(Box::new(el))) == Some((Val::List(s), pos + enc(Val::List(s)).len())),
{
    lits();
}

pub proof fn roundtrip_items(c: Seq<char>, pos: int, s: Seq<Val>, i: nat, el: Ty)
    requires
        i <= s.len(),
        forall|k: int| 0 <= k < s.len() ==> val_type(#[trigger] s[k], el),
        at(c, pos, enc_items(s, i) + l_list2()),
    ensures
        dec_items(c, pos, el, i == 0) == Some((s.subrange(i as int, s.len() as int), pos + enc_items(s, i).len())),
    decreases s, s.len() - i,
{
    lits();
    let rest = enc_items(s, i);
    at_split(c, pos, rest, l_list2());
    if i == s.len() {
        at_char(c, pos, l_list2(), 0);
        assert(s.subrange(i as int, s.len() as int) =~= Seq::<Val>::empty());
    } else {
        let lead = if i > 0 {
            l_comma()
        } else {
            Seq::<char>::empty()
        };
        let x = s[i as int];
        let tail = enc_items(s, i + 1);
        assert(rest == lead + enc(x) + tail);
        assert(lead + enc(x) + tail + l_list2() == lead + enc(x) + (tail + l_list2()));
        at_split(c, pos, lead + enc(x) + tail, l_list2());
        at_split(c, pos, lead + enc(x), tail + l_list2());
        at_split(c, pos, lead, enc(x));
        enc_first(x);
        let p = pos + lead.len();
        at_char(c, p, enc(x), 0);
        if i > 0 {
            at_char(c, pos, l_comma(), 0);
        }
        roundtrip(c, p, x, el);
        let p2 = p + enc(x).len();
        roundtrip_items(c, p2, s, i + 1, el);
        assert(seq![x] + s.subrange((i + 1) as int, s.len() as int) =~= s.subrange(i as int, s.len() as int));
    }
}

/// 型整合性：正準形の復号が成功すれば、得た値は型を持つ。
pub proof fn dec_typed(c: Seq<char>, pos: int, t: Ty)
    requires
        dec(c, pos, t) is Some,
    ensures
        val_type(dec(c, pos, t)->Some_0.0, t),
    decreases t, (c.len() - pos) as nat, 0nat,
{
    lits();
    match t {
        Ty::Option(el) => {
            if !at(c, pos, l_none()) {
                dec_typed(c, pos + l_some().len(), *el);
            }
        },
        Ty::Pair(ta, tb) => {
            dec_typed(c, pos + l_pair1().len(), *ta);
            let p2 = dec(c, pos + l_pair1().len(), *ta)->Some_0.1;
            dec_typed(c, p2 + l_pair2().len(), *tb);
        },
        Ty::List(el) => {
            dec_items_typed(c, pos + l_list1().len(), *el, true);
            let s = dec_items(c, pos + l_list1().len(), *el, true)->Some_0.0;
            val_type_list(s, *el);
        },
        _ => {},
    }
}

pub proof fn dec_items_typed(c: Seq<char>, pos: int, el: Ty, first: bool)
    requires
        dec_items(c, pos, el, first) is Some,
    ensures
        forall|k: int|
            0 <= k < dec_items(c, pos, el, first)->Some_0.0.len() ==> val_type(
                #[trigger] dec_items(c, pos, el, first)->Some_0.0[k],
                el,
            ),
    decreases el, (c.len() - pos) as nat, 1nat,
{
    if c[pos] != ']' {
        let p = if first {
            pos
        } else {
            pos + 1
        };
        dec_typed(c, p, el);
        let (x, p2) = dec(c, p, el)->Some_0;
        dec_items_typed(c, p2, el, false);
        let xs = dec_items(c, p2, el, false)->Some_0.0;
        let all = seq![x] + xs;
        assert forall|k: int| 0 <= k < all.len() implies val_type(#[trigger] all[k], el) by {
            if k > 0 {
                assert(all[k] == xs[k - 1]);
            }
        }
    }
}

/// 出力の正準 JSON は、出力型に沿って読めば元の値に戻る。
pub proof fn output_roundtrip(v: Val, t: Ty)
    requires
        val_type(v, t),
    ensures
        dec(enc(v), 0, t) == Some((v, enc(v).len() as int)),
{
    assert(enc(v).subrange(0, enc(v).len() as int) =~= enc(v));
    roundtrip(enc(v), 0, v, t);
}

} // verus!
