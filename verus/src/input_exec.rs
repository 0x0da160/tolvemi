//! 入力値の strict JSON の実行コード：parser と値 JSON の復号。spec（input.rs）と一致することを証明する。
//!
//! 長い文字列・配列・メンバー列は要素ごとの再帰ではなくループで読む。再帰は構造の入れ子の深さ
//! （上限 d）までに限られる。

use crate::bigint::*;
use crate::input::*;
use crate::input_proof::*;
use crate::json::*;
use crate::spec::*;
use crate::surface::*;
use crate::value::*;
use std::rc::Rc;
use vstd::prelude::*;

verus! {

pub enum EJ {
    Null,
    Bool(bool),
    Num,
    Str(Vec<u32>),
    Arr(Vec<EJ>),
    Obj(Vec<Vec<u32>>, Vec<EJ>),
}

pub open spec fn vj(j: EJ) -> J
    decreases j,
{
    match j {
        EJ::Null => J::Null,
        EJ::Bool(b) => J::Bool(b),
        EJ::Num => J::Num,
        EJ::Str(x) => J::Str(x@),
        EJ::Arr(xs) => J::Arr(vjs(xs)),
        EJ::Obj(ks, vs) => J::Obj(vks(ks@), vjs(vs)),
    }
}

pub open spec fn vjs(xs: Vec<EJ>) -> Seq<J>
    decreases xs,
{
    Seq::new(xs@.len(), |i: int| if 0 <= i < xs@.len() { vj(xs@[i]) } else { J::Null })
}

pub open spec fn vks(ks: Seq<Vec<u32>>) -> Seq<Seq<u32>> {
    Seq::new(ks.len(), |i: int| ks[i]@)
}

pub open spec fn fits(s: Seq<char>) -> bool {
    s.len() < 0x1000_0000
}

proof fn vjs_push(a: Vec<EJ>, b: Vec<EJ>, x: EJ)
    requires
        b@ == a@.push(x),
    ensures
        vjs(b) == vjs(a) + seq![vj(x)],
{
    assert(vjs(b) =~= vjs(a) + seq![vj(x)]);
}

proof fn vks_push(a: Seq<Vec<u32>>, x: Vec<u32>)
    ensures
        vks(a.push(x)) == vks(a) + seq![x@],
{
    assert(vks(a.push(x)) =~= vks(a) + seq![x@]);
}

pub open spec fn cat2(
    u: Seq<Seq<u32>>,
    w: Seq<J>,
    o: Option<(Seq<Seq<u32>>, Seq<J>, nat)>,
) -> Option<(Seq<Seq<u32>>, Seq<J>, nat)> {
    match o {
        Some((a, b, m)) => Some((u + a, w + b, m)),
        None => None,
    }
}

// ------------------------------------------------------------------ 字句

fn ws_e(s: &Vec<char>, i: usize) -> (j: usize)
    requires
        i <= s.len(),
    ensures
        j == ws(s@, i as nat),
        i <= j <= s.len(),
{
    let mut j = i;
    while j < s.len() && (s[j] == ' ' || s[j] == '\t' || s[j] == '\n' || s[j] == '\r')
        invariant
            i <= j <= s.len(),
            ws(s@, i as nat) == ws(s@, j as nat),
        decreases s.len() - j,
    {
        j = j + 1;
    }
    j
}

fn isd_e(c: char) -> (r: bool)
    ensures
        r == isd(c),
{
    let u = c as u32;
    48 <= u && u <= 57
}

fn hexv_e(c: char) -> (r: i64)
    ensures
        r == hexv(c),
{
    let u = c as u32;
    if 48 <= u && u <= 57 {
        (u - 48) as i64
    } else if 97 <= u && u <= 102 {
        (u - 87) as i64
    } else if 65 <= u && u <= 70 {
        (u - 55) as i64
    } else {
        -1
    }
}

fn hex4_e(s: &Vec<char>, i: usize) -> (r: Option<u32>)
    requires
        i <= s.len(),
        fits(s@),
    ensures
        match hex4(s@, i as nat) {
            Some(v) => r == Some(v as u32) && 0 <= v < 0x10000,
            None => r is None,
        },
{
    if i + 4 > s.len() {
        return None;
    }
    let a = hexv_e(s[i]);
    let b = hexv_e(s[i + 1]);
    let c = hexv_e(s[i + 2]);
    let d = hexv_e(s[i + 3]);
    if a < 0 || b < 0 || c < 0 || d < 0 {
        return None;
    }
    Some((a * 4096 + b * 256 + c * 16 + d) as u32)
}

fn jesc_e(s: &Vec<char>, i: usize) -> (r: Option<(u32, usize)>)
    requires
        i < s.len(),
        fits(s@),
    ensures
        match jesc(s@, i as nat) {
            Some((u, k)) => r == Some((u, k as usize)) && k <= s.len(),
            None => r is None,
        },
{
    if i + 1 >= s.len() {
        return None;
    }
    let e = s[i + 1];
    if e == '"' {
        return Some((34, i + 2));
    } else if e == '\\' {
        return Some((92, i + 2));
    } else if e == '/' {
        return Some((47, i + 2));
    } else if e == 'b' {
        return Some((8, i + 2));
    } else if e == 'f' {
        return Some((12, i + 2));
    } else if e == 'n' {
        return Some((10, i + 2));
    } else if e == 'r' {
        return Some((13, i + 2));
    } else if e == 't' {
        return Some((9, i + 2));
    }
    if e != 'u' {
        return None;
    }
    let cu = match hex4_e(s, i + 2) {
        Some(v) => v,
        None => return None,
    };
    if 0xD800 <= cu && cu <= 0xDBFF {
        if i + 7 < s.len() && s[i + 6] == '\\' && s[i + 7] == 'u' {
            match hex4_e(s, i + 8) {
                Some(lo) => if 0xDC00 <= lo && lo <= 0xDFFF {
                    Some((0x10000 + (cu - 0xD800) * 1024 + (lo - 0xDC00), i + 12))
                } else {
                    None
                },
                None => None,
            }
        } else {
            None
        }
    } else if 0xDC00 <= cu && cu <= 0xDFFF {
        None
    } else {
        Some((cu, i + 6))
    }
}

fn jstr_e(s: &Vec<char>, i: usize) -> (r: Option<(Vec<u32>, usize)>)
    requires
        i <= s.len(),
        fits(s@),
    ensures
        match r {
            Some((v, f)) => jstr(s@, i as nat) == Some((v@, f as nat)) && f <= s.len(),
            None => jstr(s@, i as nat) is None,
        },
{
    let mut out: Vec<u32> = Vec::new();
    let mut k = i;
    proof {
        if let Some((w, m)) = jstr(s@, k as nat) {
            assert(Seq::<u32>::empty() + w =~= w);
        }
    }
    loop
        invariant
            i <= k <= s.len(),
            fits(s@),
            jstr(s@, i as nat) == cat(out@, jstr(s@, k as nat)),
        decreases s.len() - k,
    {
        if k >= s.len() {
            return None;
        }
        let c = s[k];
        if c == '"' {
            proof {
                assert(out@ + Seq::<u32>::empty() =~= out@);
            }
            return Some((out, k + 1));
        }
        if (c as u32) < 0x20 {
            return None;
        }
        if c == '\\' {
            match jesc_e(s, k) {
                None => return None,
                Some((u, k2)) => {
                    if !(k < k2 && k2 <= s.len()) {
                        return None;
                    }
                    let ghost o = out@;
                    out.push(u);
                    proof {
                        if let Some((w, m)) = jstr(s@, k2 as nat) {
                            assert(o + (seq![u] + w) =~= out@ + w);
                        }
                    }
                    k = k2;
                },
            }
        } else {
            let ghost o = out@;
            out.push(c as u32);
            proof {
                if let Some((w, m)) = jstr(s@, (k + 1) as nat) {
                    assert(o + (seq![c as u32] + w) =~= out@ + w);
                }
            }
            k = k + 1;
        }
    }
}

fn digs_e(s: &Vec<char>, i: usize) -> (j: usize)
    requires
        i <= s.len(),
    ensures
        j == digs(s@, i as nat),
        i <= j <= s.len(),
{
    let mut j = i;
    while j < s.len() && isd_e(s[j])
        invariant
            i <= j <= s.len(),
            digs(s@, i as nat) == digs(s@, j as nat),
        decreases s.len() - j,
    {
        j = j + 1;
    }
    j
}

fn jnum_e(s: &Vec<char>, i: usize) -> (r: Option<usize>)
    requires
        i <= s.len(),
        fits(s@),
    ensures
        match jnum(s@, i as nat) {
            Some(e) => r == Some(e as usize) && e <= s.len(),
            None => r is None,
        },
{
    let a = if i < s.len() && s[i] == '-' {
        i + 1
    } else {
        i
    };
    let b = if a < s.len() && s[a] == '0' {
        a + 1
    } else if a < s.len() && isd_e(s[a]) {
        digs_e(s, a)
    } else {
        return None;
    };
    let c = if b < s.len() && s[b] == '.' {
        if b + 1 < s.len() && isd_e(s[b + 1]) {
            digs_e(s, b + 1)
        } else {
            return None;
        }
    } else {
        b
    };
    if c < s.len() && (s[c] == 'e' || s[c] == 'E') {
        let d = if c + 1 < s.len() && (s[c + 1] == '+' || s[c + 1] == '-') {
            c + 2
        } else {
            c + 1
        };
        if d < s.len() && isd_e(s[d]) {
            Some(digs_e(s, d))
        } else {
            None
        }
    } else {
        Some(c)
    }
}

fn at_e(s: &Vec<char>, a: usize, w: &Vec<char>) -> (r: bool)
    requires
        a <= s.len(),
        fits(s@),
        w.len() < 16,
    ensures
        r == at(s@, a as int, w@),
{
    if a + w.len() > s.len() {
        return false;
    }
    let mut k = 0;
    while k < w.len()
        invariant
            k <= w.len(),
            a + w.len() <= s.len(),
            forall|m: int| 0 <= m < k ==> s@[a + m] == w@[m],
        decreases w.len() - k,
    {
        if s[a + k] != w[k] {
            proof {
                assert(s@.subrange(a as int, a + w.len())[k as int] == s@[a + k]);
            }
            return false;
        }
        k = k + 1;
    }
    proof {
        assert(s@.subrange(a as int, a + w.len()) =~= w@);
    }
    true
}

fn w_true_e() -> (r: Vec<char>)
    ensures
        r@ == w_true(),
{
    let mut r = Vec::new();
    r.push('t');
    r.push('r');
    r.push('u');
    r.push('e');
    proof {
        assert(r@ =~= w_true());
    }
    r
}

fn w_false_e() -> (r: Vec<char>)
    ensures
        r@ == w_false(),
{
    let mut r = Vec::new();
    r.push('f');
    r.push('a');
    r.push('l');
    r.push('s');
    r.push('e');
    proof {
        assert(r@ =~= w_false());
    }
    r
}

fn w_null_e() -> (r: Vec<char>)
    ensures
        r@ == w_null(),
{
    let mut r = Vec::new();
    r.push('n');
    r.push('u');
    r.push('l');
    r.push('l');
    proof {
        assert(r@ =~= w_null());
    }
    r
}

// ------------------------------------------------------------------ 構文

fn jv_e(s: &Vec<char>, i: usize, d: usize) -> (r: Option<(EJ, usize)>)
    requires
        i <= s.len(),
        fits(s@),
    ensures
        match r {
            Some((v, e)) => jv(s@, i as nat, d as nat) == Some((vj(v), e as nat)) && e <= s.len(),
            None => jv(s@, i as nat, d as nat) is None,
        },
    decreases d, 0nat,
{
    let a = ws_e(s, i);
    if a >= s.len() {
        return None;
    }
    let c = s[a];
    if c == '{' || c == '[' {
        if d == 0 {
            return None;
        }
        let b = ws_e(s, a + 1);
        if c == '{' {
            if b < s.len() && s[b] == '}' {
                let ks: Vec<Vec<u32>> = Vec::new();
                let vs: Vec<EJ> = Vec::new();
                proof {
                    assert(vks(ks@) =~= Seq::<Seq<u32>>::empty());
                    assert(vjs(vs) =~= Seq::<J>::empty());
                }
                return Some((EJ::Obj(ks, vs), b + 1));
            }
            match jmembers_e(s, b, d - 1) {
                Some((ks, vs, e)) => Some((EJ::Obj(ks, vs), e)),
                None => None,
            }
        } else {
            if b < s.len() && s[b] == ']' {
                let vs: Vec<EJ> = Vec::new();
                proof {
                    assert(vjs(vs) =~= Seq::<J>::empty());
                }
                return Some((EJ::Arr(vs), b + 1));
            }
            match jitems_e(s, b, d - 1) {
                Some((vs, e)) => Some((EJ::Arr(vs), e)),
                None => None,
            }
        }
    } else if c == '"' {
        match jstr_e(s, a + 1) {
            Some((x, e)) => Some((EJ::Str(x), e)),
            None => None,
        }
    } else if c == '-' || isd_e(c) {
        match jnum_e(s, a) {
            Some(e) => Some((EJ::Num, e)),
            None => None,
        }
    } else if at_e(s, a, &w_true_e()) {
        Some((EJ::Bool(true), a + 4))
    } else if at_e(s, a, &w_false_e()) {
        Some((EJ::Bool(false), a + 5))
    } else if at_e(s, a, &w_null_e()) {
        Some((EJ::Null, a + 4))
    } else {
        None
    }
}

fn jitems_e(s: &Vec<char>, i: usize, d: usize) -> (r: Option<(Vec<EJ>, usize)>)
    requires
        i <= s.len(),
        fits(s@),
    ensures
        match r {
            Some((vs, e)) => jitems(s@, i as nat, d as nat) == Some((vjs(vs), e as nat)) && e <= s.len(),
            None => jitems(s@, i as nat, d as nat) is None,
        },
    decreases d, 1nat,
{
    let mut out: Vec<EJ> = Vec::new();
    let mut k = i;
    proof {
        assert(vjs(out) =~= Seq::<J>::empty());
        if let Some((w, m)) = jitems(s@, k as nat, d as nat) {
            assert(Seq::<J>::empty() + w =~= w);
        }
    }
    loop
        invariant
            i <= k <= s.len(),
            fits(s@),
            jitems(s@, i as nat, d as nat) == cat(vjs(out), jitems(s@, k as nat, d as nat)),
        decreases s.len() - k,
    {
        let (v, e) = match jv_e(s, k, d) {
            Some(r) => r,
            None => return None,
        };
        let f = ws_e(s, e);
        if f < s.len() && s[f] == ',' {
            if !(k < f + 1 && f + 1 <= s.len()) {
                return None;
            }
            let ghost o = out;
            let ghost vv = vj(v);
            out.push(v);
            proof {
                vjs_push(o, out, v);
                if let Some((w, m)) = jitems(s@, (f + 1) as nat, d as nat) {
                    assert(vjs(o) + (seq![vv] + w) =~= vjs(out) + w);
                }
            }
            k = f + 1;
        } else if f < s.len() && s[f] == ']' {
            let ghost o = out;
            let ghost vv = vj(v);
            out.push(v);
            proof {
                vjs_push(o, out, v);
            }
            return Some((out, f + 1));
        } else {
            return None;
        }
    }
}

fn jmembers_e(s: &Vec<char>, i: usize, d: usize) -> (r: Option<(Vec<Vec<u32>>, Vec<EJ>, usize)>)
    requires
        i <= s.len(),
        fits(s@),
    ensures
        match r {
            Some((ks, vs, e)) => jmembers(s@, i as nat, d as nat) == Some((vks(ks@), vjs(vs), e as nat)) && e
                <= s.len(),
            None => jmembers(s@, i as nat, d as nat) is None,
        },
    decreases d, 1nat,
{
    let mut ks: Vec<Vec<u32>> = Vec::new();
    let mut vs: Vec<EJ> = Vec::new();
    let mut k = i;
    proof {
        assert(vks(ks@) =~= Seq::<Seq<u32>>::empty());
        assert(vjs(vs) =~= Seq::<J>::empty());
        if let Some((a, b, m)) = jmembers(s@, k as nat, d as nat) {
            assert(Seq::<Seq<u32>>::empty() + a =~= a);
            assert(Seq::<J>::empty() + b =~= b);
        }
    }
    loop
        invariant
            i <= k <= s.len(),
            fits(s@),
            jmembers(s@, i as nat, d as nat) == cat2(vks(ks@), vjs(vs), jmembers(s@, k as nat, d as nat)),
        decreases s.len() - k,
    {
        let a = ws_e(s, k);
        if !(a < s.len() && s[a] == '"') {
            return None;
        }
        let (key, b) = match jstr_e(s, a + 1) {
            Some(r) => r,
            None => return None,
        };
        let c = ws_e(s, b);
        if !(c < s.len() && s[c] == ':') || !(k < c + 1) {
            return None;
        }
        let (v, e) = match jv_e(s, c + 1, d) {
            Some(r) => r,
            None => return None,
        };
        let f = ws_e(s, e);
        let last = if f < s.len() && s[f] == ',' {
            if !(k < f + 1 && f + 1 <= s.len()) {
                return None;
            }
            false
        } else if f < s.len() && s[f] == '}' {
            true
        } else {
            return None;
        };
        let ghost ko = ks@;
        let ghost vo = vs;
        let ghost kk = key@;
        let ghost vv = vj(v);
        ks.push(key);
        vs.push(v);
        proof {
            vks_push(ko, ks@[ks@.len() - 1]);
            assert(ks@ == ko.push(ks@[ks@.len() - 1]));
            vjs_push(vo, vs, v);
            assert(vks(ks@) == vks(ko) + seq![kk]);
            assert(vjs(vs) == vjs(vo) + seq![vv]);
        }
        if last {
            return Some((ks, vs, f + 1));
        }
        proof {
            if let Some((x, y, m)) = jmembers(s@, (f + 1) as nat, d as nat) {
                assert(vks(ko) + (seq![kk] + x) =~= vks(ks@) + x);
                assert(vjs(vo) + (seq![vv] + y) =~= vjs(vs) + y);
            }
        }
        k = f + 1;
    }
}

/// strict JSON の文書全体を読む。
pub fn jparse_e(s: &Vec<char>, d: usize) -> (r: Option<EJ>)
    requires
        fits(s@),
    ensures
        match r {
            Some(j) => jparse(s@, d as nat) == Some(vj(j)),
            None => jparse(s@, d as nat) is None,
        },
{
    match jv_e(s, 0, d) {
        Some((j, e)) => {
            if ws_e(s, e) == s.len() {
                Some(j)
            } else {
                None
            }
        },
        None => None,
    }
}

// ------------------------------------------------------------------ 値 JSON の復号

fn codes(w: &Vec<char>) -> (r: Vec<u32>)
    ensures
        r@ == cs(w@),
{
    let mut r: Vec<u32> = Vec::new();
    let mut k = 0;
    while k < w.len()
        invariant
            k <= w.len(),
            r@ == cs(w@.subrange(0, k as int)),
        decreases w.len() - k,
    {
        let ghost o = r@;
        r.push(w[k] as u32);
        proof {
            assert(cs(w@.subrange(0, k + 1)) =~= o.push(w@[k as int] as u32));
        }
        k = k + 1;
    }
    proof {
        assert(w@.subrange(0, w.len() as int) =~= w@);
    }
    r
}

fn k_tag_e() -> (r: Vec<u32>)
    ensures
        r@ == k_tag(),
{
    let mut w: Vec<char> = Vec::new();
    w.push('t');
    w.push('a');
    w.push('g');
    proof {
        assert(w@ =~= c_tag());
    }
    codes(&w)
}

fn k_value_e() -> (r: Vec<u32>)
    ensures
        r@ == k_value(),
{
    let mut w: Vec<char> = Vec::new();
    w.push('v');
    w.push('a');
    w.push('l');
    w.push('u');
    w.push('e');
    proof {
        assert(w@ =~= c_value());
    }
    codes(&w)
}

fn k_left_e() -> (r: Vec<u32>)
    ensures
        r@ == k_left(),
{
    let mut w: Vec<char> = Vec::new();
    w.push('l');
    w.push('e');
    w.push('f');
    w.push('t');
    proof {
        assert(w@ =~= c_left());
    }
    codes(&w)
}

fn k_right_e() -> (r: Vec<u32>)
    ensures
        r@ == k_right(),
{
    let mut w: Vec<char> = Vec::new();
    w.push('r');
    w.push('i');
    w.push('g');
    w.push('h');
    w.push('t');
    proof {
        assert(w@ =~= c_right());
    }
    codes(&w)
}

fn k_items_e() -> (r: Vec<u32>)
    ensures
        r@ == k_items(),
{
    let mut w: Vec<char> = Vec::new();
    w.push('i');
    w.push('t');
    w.push('e');
    w.push('m');
    w.push('s');
    proof {
        assert(w@ =~= c_items());
    }
    codes(&w)
}

fn t_int_e() -> (r: Vec<u32>)
    ensures
        r@ == t_int(),
{
    let mut w: Vec<char> = Vec::new();
    w.push('i');
    w.push('n');
    w.push('t');
    proof {
        assert(w@ =~= c_int());
    }
    codes(&w)
}

fn t_bool_e() -> (r: Vec<u32>)
    ensures
        r@ == t_bool(),
{
    let mut w: Vec<char> = Vec::new();
    w.push('b');
    w.push('o');
    w.push('o');
    w.push('l');
    proof {
        assert(w@ =~= c_bool());
    }
    codes(&w)
}

fn t_unit_e() -> (r: Vec<u32>)
    ensures
        r@ == t_unit(),
{
    let mut w: Vec<char> = Vec::new();
    w.push('u');
    w.push('n');
    w.push('i');
    w.push('t');
    proof {
        assert(w@ =~= c_unit());
    }
    codes(&w)
}

fn t_none_e() -> (r: Vec<u32>)
    ensures
        r@ == t_none(),
{
    let mut w: Vec<char> = Vec::new();
    w.push('n');
    w.push('o');
    w.push('n');
    w.push('e');
    proof {
        assert(w@ =~= c_none());
    }
    codes(&w)
}

fn t_some_e() -> (r: Vec<u32>)
    ensures
        r@ == t_some(),
{
    let mut w: Vec<char> = Vec::new();
    w.push('s');
    w.push('o');
    w.push('m');
    w.push('e');
    proof {
        assert(w@ =~= c_some());
    }
    codes(&w)
}

fn t_pair_e() -> (r: Vec<u32>)
    ensures
        r@ == t_pair(),
{
    let mut w: Vec<char> = Vec::new();
    w.push('p');
    w.push('a');
    w.push('i');
    w.push('r');
    proof {
        assert(w@ =~= c_pair());
    }
    codes(&w)
}

fn t_list_e() -> (r: Vec<u32>)
    ensures
        r@ == t_list(),
{
    let mut w: Vec<char> = Vec::new();
    w.push('l');
    w.push('i');
    w.push('s');
    w.push('t');
    proof {
        assert(w@ =~= c_list());
    }
    codes(&w)
}



fn eq_u32s(a: &Vec<u32>, b: &Vec<u32>) -> (r: bool)
    ensures
        r == (a@ == b@),
{
    if a.len() != b.len() {
        return false;
    }
    let mut i = 0;
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
        i = i + 1;
    }
    proof {
        assert(a@ =~= b@);
    }
    true
}

fn kpos_e(ks: &Vec<Vec<u32>>, k: &Vec<u32>) -> (r: usize)
    ensures
        r == kpos(vks(ks@), k@, 0),
{
    let mut m = 0;
    while m < ks.len()
        invariant
            m <= ks.len(),
            kpos(vks(ks@), k@, 0) == kpos(vks(ks@), k@, m as nat),
        decreases ks.len() - m,
    {
        proof {
            assert(vks(ks@)[m as int] == ks@[m as int]@);
        }
        if eq_u32s(&ks[m], k) {
            return m;
        }
        m = m + 1;
    }
    m
}

fn distinct_e(ks: &Vec<Vec<u32>>) -> (r: bool)
    ensures
        r == distinct(vks(ks@)),
{
    let ghost kv = vks(ks@);
    let mut a = 0;
    while a < ks.len()
        invariant
            a <= ks.len(),
            kv == vks(ks@),
            forall|x: int, y: int| 0 <= x < y < ks.len() && x < a ==> kv[x] != kv[y],
        decreases ks.len() - a,
    {
        let mut b = a + 1;
        while b < ks.len()
            invariant
                a < ks.len(),
                a + 1 <= b <= ks.len(),
                kv == vks(ks@),
                forall|x: int, y: int| 0 <= x < y < ks.len() && x < a ==> kv[x] != kv[y],
                forall|y: int| a < y < b ==> kv[a as int] != kv[y],
            decreases ks.len() - b,
        {
            proof {
                assert(kv[a as int] == ks@[a as int]@);
                assert(kv[b as int] == ks@[b as int]@);
            }
            if eq_u32s(&ks[a], &ks[b]) {
                return false;
            }
            b = b + 1;
        }
        a = a + 1;
    }
    true
}

fn only_e(ks: &Vec<Vec<u32>>, req: &Vec<Vec<u32>>) -> (r: bool)
    ensures
        r == only(vks(ks@), vks(req@)),
{
    if ks.len() != req.len() {
        return false;
    }
    let mut m = 0;
    while m < req.len()
        invariant
            m <= req.len(),
            ks.len() == req.len(),
            forall|x: int| 0 <= x < m ==> #[trigger] kpos(vks(ks@), vks(req@)[x], 0) < ks.len(),
        decreases req.len() - m,
    {
        let p = kpos_e(ks, &req[m]);
        proof {
            assert(vks(req@)[m as int] == req@[m as int]@);
        }
        if p >= ks.len() {
            return false;
        }
        m = m + 1;
    }
    true
}

fn req1(a: Vec<u32>) -> (r: Vec<Vec<u32>>)
    ensures
        vks(r@) == seq![a@],
{
    let ghost av = a@;
    let mut r = Vec::new();
    r.push(a);
    proof {
        assert(vks(r@) =~= seq![av]);
    }
    r
}

fn req2(a: Vec<u32>, b: Vec<u32>) -> (r: Vec<Vec<u32>>)
    ensures
        vks(r@) == seq![a@, b@],
{
    let ghost av = a@;
    let ghost bv = b@;
    let mut r = Vec::new();
    r.push(a);
    r.push(b);
    proof {
        assert(vks(r@) =~= seq![av, bv]);
    }
    r
}

fn req3(a: Vec<u32>, b: Vec<u32>, c: Vec<u32>) -> (r: Vec<Vec<u32>>)
    ensures
        vks(r@) == seq![a@, b@, c@],
{
    let ghost av = a@;
    let ghost bv = b@;
    let ghost cv = c@;
    let mut r = Vec::new();
    r.push(a);
    r.push(b);
    r.push(c);
    proof {
        assert(vks(r@) =~= seq![av, bv, cv]);
    }
    r
}

/// 正準十進整数の値。
fn cint_e(x: &Vec<u32>) -> (r: Option<Int>)
    ensures
        match r {
            Some(n) => cint(x@) == Some(n@),
            None => cint(x@) is None,
        },
{
    let neg = x.len() > 0 && x[0] == 45;
    let a: usize = if neg {
        1
    } else {
        0
    };
    let ghost y = x@.subrange(a as int, x@.len() as int);
    proof {
        if neg {
            assert(x@.drop_first() =~= y);
        } else {
            assert(x@ =~= y);
        }
    }
    if x.len() <= a {
        return None;
    }
    let mut k = a;
    while k < x.len()
        invariant
            a <= k <= x.len(),
            y == x@.subrange(a as int, x@.len() as int),
            neg == (x@.len() > 0 && x@[0] == 45),
            a == (if neg { 1usize } else { 0usize }),
            neg ==> x@.drop_first() == y,
            !neg ==> x@ == y,
            forall|m: int| a <= m < k ==> dig(#[trigger] x@[m]),
        decreases x.len() - k,
    {
        if !(48 <= x[k] && x[k] <= 57) {
            proof {
                assert(y[k - a] == x@[k as int]);
            }
            return None;
        }
        k = k + 1;
    }
    proof {
        assert forall|m: int| 0 <= m < y.len() implies dig(#[trigger] y[m]) by {
            assert(y[m] == x@[a + m]);
        }
        assert(y[0] == x@[a as int]);
    }
    if x[a] == 48 && x.len() != a + 1 {
        return None;
    }
    let ten = Int::from_u64(10);
    let mut acc = Int::from_u64(0);
    let mut k = a;
    proof {
        assert(x@.subrange(a as int, a as int) =~= Seq::<u32>::empty());
    }
    while k < x.len()
        invariant
            a <= k <= x.len(),
            ten@ == 10,
            y == x@.subrange(a as int, x@.len() as int),
            neg == (x@.len() > 0 && x@[0] == 45),
            a == (if neg { 1usize } else { 0usize }),
            neg ==> x@.drop_first() == y,
            !neg ==> x@ == y,
            acc@ == nv(x@.subrange(a as int, k as int)),
            forall|m: int| a <= m < x.len() ==> dig(#[trigger] x@[m]),
        decreases x.len() - k,
    {
        let dk = Int::from_u64((x[k] - 48) as u64);
        proof {
            let t = x@.subrange(a as int, k + 1);
            assert(t.drop_last() =~= x@.subrange(a as int, k as int));
            assert(t.last() == x@[k as int]);
            assert(dig(x@[k as int]));
        }
        acc = acc.mul(&ten).add(&dk);
        k = k + 1;
    }
    proof {
        assert(x@.subrange(a as int, x@.len() as int) == y);
    }
    if neg {
        if !acc.is_positive() {
            return None;
        }
        Some(acc.neg())
    } else {
        Some(acc)
    }
}

pub open spec fn catv(u: Seq<Val>, o: Option<Seq<Val>>) -> Option<Seq<Val>> {
    match o {
        Some(w) => Some(u + w),
        None => None,
    }
}

/// 値 JSON の木を型 t の値として読む。
pub fn jd_e(j: &EJ, t: &Ty) -> (r: Option<Rc<Value>>)
    ensures
        match r {
            Some(v) => jd(vj(*j), *t) == Some(view_val(*v)),
            None => jd(vj(*j), *t) is None,
        },
    decreases j,
{
    match j {
        EJ::Obj(ks, vs) => {
            let ghost jv0 = vj(*j);
            let ghost kv = vks(ks@);
            let ghost vsv = vjs(*vs);
            proof {
                assert(jv0 == J::Obj(kv, vsv));
                keys();
            }
            if ks.len() != vs.len() || ks.len() > 3 || !distinct_e(ks) {
                return None;
            }
            let it = kpos_e(ks, &k_tag_e());
            if it >= vs.len() {
                return None;
            }
            proof {
                assert(vsv[it as int] == vj(vs@[it as int]));
            }
            let g = match &vs[it] {
                EJ::Str(g) => g,
                _ => return None,
            };
            let iv = kpos_e(ks, &k_value_e());
            let il = kpos_e(ks, &k_left_e());
            let ir = kpos_e(ks, &k_right_e());
            let ii = kpos_e(ks, &k_items_e());
            match t {
                Ty::Int => {
                    if !(eq_u32s(g, &t_int_e()) && only_e(ks, &req2(k_tag_e(), k_value_e()))) || iv >= vs.len() {
                        return None;
                    }
                    proof {
                        assert(vsv[iv as int] == vj(vs@[iv as int]));
                    }
                    match &vs[iv] {
                        EJ::Str(x) => match cint_e(x) {
                            Some(n) => Some(Rc::new(Value::Int(n))),
                            None => None,
                        },
                        _ => None,
                    }
                },
                Ty::Bool => {
                    if !(eq_u32s(g, &t_bool_e()) && only_e(ks, &req2(k_tag_e(), k_value_e()))) || iv >= vs.len() {
                        return None;
                    }
                    proof {
                        assert(vsv[iv as int] == vj(vs@[iv as int]));
                    }
                    match &vs[iv] {
                        EJ::Bool(b) => Some(Rc::new(Value::Bool(*b))),
                        _ => None,
                    }
                },
                Ty::Unit => {
                    if eq_u32s(g, &t_unit_e()) && only_e(ks, &req1(k_tag_e())) {
                        Some(Rc::new(Value::Unit))
                    } else {
                        None
                    }
                },
                Ty::Option(el) => {
                    if eq_u32s(g, &t_none_e()) && only_e(ks, &req1(k_tag_e())) {
                        return Some(Rc::new(Value::None));
                    }
                    if !(eq_u32s(g, &t_some_e()) && only_e(ks, &req2(k_tag_e(), k_value_e()))) || iv >= vs.len() {
                        return None;
                    }
                    proof {
                        assert(vsv[iv as int] == vj(vs@[iv as int]));
                        vstd::std_specs::vec::axiom_vec_index_decreases(*vs, iv as int);
                    }
                    match jd_e(&vs[iv], el) {
                        Some(x) => Some(Rc::new(Value::Some(x))),
                        None => None,
                    }
                },
                Ty::Pair(ta, tb) => {
                    if !(eq_u32s(g, &t_pair_e()) && only_e(ks, &req3(k_tag_e(), k_left_e(), k_right_e())))
                        || il >= vs.len() || ir >= vs.len() {
                        return None;
                    }
                    proof {
                        assert(vsv[il as int] == vj(vs@[il as int]));
                        assert(vsv[ir as int] == vj(vs@[ir as int]));
                        vstd::std_specs::vec::axiom_vec_index_decreases(*vs, il as int);
                        vstd::std_specs::vec::axiom_vec_index_decreases(*vs, ir as int);
                    }
                    let a = match jd_e(&vs[il], ta) {
                        Some(a) => a,
                        None => return None,
                    };
                    let b = match jd_e(&vs[ir], tb) {
                        Some(b) => b,
                        None => return None,
                    };
                    Some(Rc::new(Value::Pair(a, b)))
                },
                Ty::List(el) => {
                    if !(eq_u32s(g, &t_list_e()) && only_e(ks, &req2(k_tag_e(), k_items_e()))) || ii >= vs.len() {
                        return None;
                    }
                    proof {
                        assert(vsv[ii as int] == vj(vs@[ii as int]));
                        vstd::std_specs::vec::axiom_vec_index_decreases(*vs, ii as int);
                    }
                    match &vs[ii] {
                        EJ::Arr(xs) => match jds_e(xs, el) {
                            Some(out) => Some(list_of(out)),
                            None => None,
                        },
                        _ => None,
                    }
                },
            }
        },
        _ => None,
    }
}

/// 配列の各要素を型 t の値として読む。
fn jds_e(xs: &Vec<EJ>, t: &Ty) -> (r: Option<Vec<Rc<Value>>>)
    ensures
        match r {
            Some(out) => jds(vjs(*xs), *t, 0) == Some(view_vals(out@)),
            None => jds(vjs(*xs), *t, 0) is None,
        },
    decreases xs,
{
    let ghost xv = vjs(*xs);
    let mut out: Vec<Rc<Value>> = Vec::new();
    let mut k = 0;
    proof {
        assert(view_vals(out@) =~= Seq::<Val>::empty());
        if let Some(w) = jds(xv, *t, 0) {
            assert(Seq::<Val>::empty() + w =~= w);
        }
    }
    while k < xs.len()
        invariant
            k <= xs.len(),
            xv == vjs(*xs),
            jds(xv, *t, 0) == catv(view_vals(out@), jds(xv, *t, k as nat)),
        decreases xs.len() - k,
    {
        proof {
            vstd::std_specs::vec::axiom_vec_index_decreases(*xs, k as int);
            assert(xv[k as int] == vj(xs@[k as int]));
        }
        let x = match jd_e(&xs[k], t) {
            Some(x) => x,
            None => return None,
        };
        let ghost o = out@;
        out.push(x);
        proof {
            assert(view_vals(out@) =~= view_vals(o) + seq![vv(x)]);
            if let Some(w) = jds(xv, *t, (k + 1) as nat) {
                assert(view_vals(o) + (seq![vv(x)] + w) =~= view_vals(out@) + w);
            }
        }
        k = k + 1;
    }
    proof {
        assert(view_vals(out@) + Seq::<Val>::empty() =~= view_vals(out@));
    }
    Some(out)
}

/// 値の列からリスト値を作る（後ろから cons する）。
fn list_of(vs: Vec<Rc<Value>>) -> (r: Rc<Value>)
    ensures
        view_val(*r) == Val::List(view_vals(vs@)),
{
    let ghost all = vs@;
    let ghost sv = view_vals(all);
    let mut vs = vs;
    let mut out = Rc::new(Value::Nil);
    loop
        invariant
            vs@.len() <= all.len(),
            vs@ == all.subrange(0, vs@.len() as int),
            sv == view_vals(all),
            is_list(*out),
            spine(*out) == sv.subrange(vs@.len() as int, all.len() as int),
        ensures
            vs@.len() == 0,
        decreases vs@.len(),
    {
        match vs.pop() {
            Some(v) => {
                let ghost k = vs@.len();
                proof {
                    assert(vv(v) == sv[k as int]);
                    spine_cons(v, out);
                    assert(seq![sv[k as int]] + sv.subrange(k as int + 1, all.len() as int) =~= sv.subrange(
                        k as int,
                        all.len() as int,
                    ));
                }
                out = Rc::new(Value::Cons(v, out));
            },
            None => break,
        }
    }
    proof {
        assert(sv.subrange(0, all.len() as int) =~= sv);
    }
    out
}

/// 入力 JSON 文書を型 t の値として読む。返した値は spec の `input_val` が定める唯一の値で、型 t を持つ。
pub fn decode_input_e(s: &Vec<char>, d: usize, t: &Ty) -> (r: Option<Rc<Value>>)
    requires
        s@.len() < 0x1000_0000,
    ensures
        match r {
            Some(v) => input_val(s@, d as nat, *t) == Some(view_val(*v)) && val_type(view_val(*v), *t),
            None => input_val(s@, d as nat, *t) is None,
        },
{
    proof {
        input_typed(s@, d as nat, *t);
    }
    match jparse_e(s, d) {
        Some(j) => jd_e(&j, t),
        None => None,
    }
}

} // verus!
