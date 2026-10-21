//! 入力値の strict JSON（設計書 §9、§9.3a と §11.2 の 9 の入力側）。
//!
//! - `jparse` は strict JSON の文法（空白、escape、surrogate pair、構造の深さ上限）を表す spec の parser。
//!   文字列は Unicode scalar 値の列として読み、対にならない surrogate は拒否する。
//! - `jd` は値 JSON の復号（§9）。tag と型の対応、必須キーと余分なキーの拒否、重複キーの拒否、
//!   正準整数を確かめる。資源上限（InputAdmission の値の深さ・node 数・桁数）は含まない。
//! - 辞書 `Dict<K, V>` は (鍵, 値) の対のリストとして読む。受理の条件は、鍵の正準 JSON（`enc`）が
//!   どの二つも異なること（`keys_distinct`）。最初の誤りが辞書の重複鍵かどうかは `dupfirst` が
//!   values.rs の順（DFS）で定める。
//! - 証明：復号した値は消去後の型 `derase(t)` を持つ（`input_typed`）、受理した JSON に重複キーは無い（`input_nodup`）、
//!   型付き値の正準 JSON を読むと元の値に戻る（`input_roundtrip`。辞書を含む型には及ばない）、
//!   辞書の重複鍵の拒否（`input_dupfirst_rejects`）、受理した辞書の値は項の順の対のリスト（`dict_items_order`）。

use crate::bigint::*;
use crate::json::*;
use crate::proof::*;
use crate::spec::*;
use vstd::prelude::*;

verus! {

/// JSON の木。数値の中身は値 JSON で使わないので持たない。
pub enum J {
    Null,
    Bool(bool),
    Num,
    Str(Seq<u32>),
    Arr(Seq<J>),
    Obj(Seq<Seq<u32>>, Seq<J>),
}

// ------------------------------------------------------------------ 字句

pub open spec fn jws(c: char) -> bool {
    c == ' ' || c == '\t' || c == '\n' || c == '\r'
}

pub open spec fn ws(s: Seq<char>, i: nat) -> nat
    decreases s.len() - i,
{
    if i < s.len() && jws(s[i as int]) {
        ws(s, i + 1)
    } else {
        i
    }
}

pub open spec fn isd(c: char) -> bool {
    48 <= (c as u32) && (c as u32) <= 57
}

pub open spec fn hexv(c: char) -> int {
    let u = c as u32 as int;
    if 48 <= u && u <= 57 {
        u - 48
    } else if 97 <= u && u <= 102 {
        u - 87
    } else if 65 <= u && u <= 70 {
        u - 55
    } else {
        -1
    }
}

pub open spec fn hex4(s: Seq<char>, i: nat) -> Option<int> {
    if i + 4 <= s.len() && hexv(s[i as int]) >= 0 && hexv(s[(i + 1) as int]) >= 0 && hexv(s[(i + 2) as int]) >= 0 && hexv(s[(i + 3) as int])
        >= 0 {
        Some(hexv(s[i as int]) * 4096 + hexv(s[(i + 1) as int]) * 256 + hexv(s[(i + 2) as int]) * 16 + hexv(s[(i + 3) as int]))
    } else {
        None
    }
}

/// 一文字の escape。
pub open spec fn esc1(c: char) -> Option<u32> {
    if c == '"' {
        Some(34u32)
    } else if c == '\\' {
        Some(92u32)
    } else if c == '/' {
        Some(47u32)
    } else if c == 'b' {
        Some(8u32)
    } else if c == 'f' {
        Some(12u32)
    } else if c == 'n' {
        Some(10u32)
    } else if c == 'r' {
        Some(13u32)
    } else if c == 't' {
        Some(9u32)
    } else {
        None
    }
}

/// s[i] == '\\' から始まる escape の scalar 値と次の位置。対にならない surrogate は None。
pub open spec fn jesc(s: Seq<char>, i: nat) -> Option<(u32, nat)> {
    if i + 1 >= s.len() {
        None
    } else {
        match esc1(s[(i + 1) as int]) {
            Some(u) => Some((u, i + 2)),
            None => if s[(i + 1) as int] != 'u' {
                None
            } else {
                match hex4(s, i + 2) {
                    None => None,
                    Some(cu) => if 0xD800 <= cu && cu <= 0xDBFF {
                        if i + 7 < s.len() && s[(i + 6) as int] == '\\' && s[(i + 7) as int] == 'u' {
                            match hex4(s, i + 8) {
                                Some(lo) => if 0xDC00 <= lo && lo <= 0xDFFF {
                                    Some(((0x10000 + (cu - 0xD800) * 1024 + (lo - 0xDC00)) as u32, i + 12))
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
                        Some((cu as u32, i + 6))
                    },
                }
            },
        }
    }
}

/// 開き引用符の直後 i から閉じ引用符まで。中身の scalar 列と閉じ引用符の次の位置。
pub open spec fn jstr(s: Seq<char>, i: nat) -> Option<(Seq<u32>, nat)>
    decreases s.len() - i,
{
    if i >= s.len() {
        None
    } else if s[i as int] == '"' {
        Some((Seq::empty(), i + 1))
    } else if (s[i as int] as u32) < 0x20 {
        None
    } else if s[i as int] == '\\' {
        match jesc(s, i) {
            Some((u, k)) => if i < k && k <= s.len() {
                match jstr(s, k) {
                    Some((r, e)) => Some((seq![u] + r, e)),
                    None => None,
                }
            } else {
                None
            },
            None => None,
        }
    } else {
        match jstr(s, i + 1) {
            Some((r, e)) => Some((seq![s[i as int] as u32] + r, e)),
            None => None,
        }
    }
}

/// i 以降の数字の並びの終わり。
pub open spec fn digs(s: Seq<char>, i: nat) -> nat
    decreases s.len() - i,
{
    if i < s.len() && isd(s[i as int]) {
        digs(s, i + 1)
    } else {
        i
    }
}

pub open spec fn jfrac(s: Seq<char>, b: nat) -> Option<nat> {
    if b < s.len() && s[b as int] == '.' {
        if b + 1 < s.len() && isd(s[(b + 1) as int]) {
            Some(digs(s, b + 1))
        } else {
            None
        }
    } else {
        Some(b)
    }
}

pub open spec fn jexp(s: Seq<char>, c: nat) -> Option<nat> {
    if c < s.len() && (s[c as int] == 'e' || s[c as int] == 'E') {
        let d: nat = if c + 1 < s.len() && (s[(c + 1) as int] == '+' || s[(c + 1) as int] == '-') {
            c + 2
        } else {
            c + 1
        };
        if d < s.len() && isd(s[d as int]) {
            Some(digs(s, d))
        } else {
            None
        }
    } else {
        Some(c)
    }
}

/// 数値の終わりの位置。
pub open spec fn jnum(s: Seq<char>, i: nat) -> Option<nat> {
    let a: nat = if i < s.len() && s[i as int] == '-' {
        i + 1
    } else {
        i
    };
    let b: Option<nat> = if a < s.len() && s[a as int] == '0' {
        Some(a + 1)
    } else if a < s.len() && isd(s[a as int]) {
        Some(digs(s, a))
    } else {
        None
    };
    match b {
        Some(b) => match jfrac(s, b) {
            Some(c) => jexp(s, c),
            None => None,
        },
        None => None,
    }
}

pub open spec fn w_true() -> Seq<char> {
    seq!['t', 'r', 'u', 'e']
}

pub open spec fn w_false() -> Seq<char> {
    seq!['f', 'a', 'l', 's', 'e']
}

pub open spec fn w_null() -> Seq<char> {
    seq!['n', 'u', 'l', 'l']
}

// ------------------------------------------------------------------ 構文（d は残りの入れ子の深さ）

/// 位置 i から値を一つ読む（前の空白を含む）。
pub open spec fn jv(s: Seq<char>, i: nat, d: nat) -> Option<(J, nat)>
    decreases d, s.len() - i, 0nat,
{
    let a = ws(s, i);
    if a >= s.len() || i > s.len() {
        None
    } else {
        let c = s[a as int];
        if c == '{' || c == '[' {
            if d == 0 {
                None
            } else {
                let b = ws(s, a + 1);
                if b < s.len() && s[b as int] == (if c == '{' {
                    '}'
                } else {
                    ']'
                }) {
                    Some((if c == '{' { J::Obj(Seq::empty(), Seq::empty()) } else { J::Arr(Seq::empty()) }, b + 1))
                } else if b > s.len() {
                    None
                } else if c == '{' {
                    match jmembers(s, b, (d - 1) as nat) {
                        Some((ks, vs, e)) => Some((J::Obj(ks, vs), e)),
                        None => None,
                    }
                } else {
                    match jitems(s, b, (d - 1) as nat) {
                        Some((vs, e)) => Some((J::Arr(vs), e)),
                        None => None,
                    }
                }
            }
        } else if c == '"' {
            match jstr(s, a + 1) {
                Some((x, e)) => Some((J::Str(x), e)),
                None => None,
            }
        } else if c == '-' || isd(c) {
            match jnum(s, a) {
                Some(e) => Some((J::Num, e)),
                None => None,
            }
        } else if at(s, a as int, w_true()) {
            Some((J::Bool(true), a + 4))
        } else if at(s, a as int, w_false()) {
            Some((J::Bool(false), a + 5))
        } else if at(s, a as int, w_null()) {
            Some((J::Null, a + 4))
        } else {
            None
        }
    }
}

/// 配列の要素列（'[' と空白の後から ']' の次まで）。
pub open spec fn jitems(s: Seq<char>, i: nat, d: nat) -> Option<(Seq<J>, nat)>
    decreases d, s.len() - i, 1nat,
{
    if i > s.len() {
        None
    } else {
        match jv(s, i, d) {
            None => None,
            Some((v, e)) => {
                let f = ws(s, e);
                if f < s.len() && s[f as int] == ',' {
                    if i < f + 1 && f + 1 <= s.len() {
                        match jitems(s, f + 1, d) {
                            Some((vs, g)) => Some((seq![v] + vs, g)),
                            None => None,
                        }
                    } else {
                        None
                    }
                } else if f < s.len() && s[f as int] == ']' {
                    Some((seq![v], f + 1))
                } else {
                    None
                }
            },
        }
    }
}

/// object のメンバー列（'{' と空白の後から '}' の次まで）。キー列と値列に分けて返す。
pub open spec fn jmembers(s: Seq<char>, i: nat, d: nat) -> Option<(Seq<Seq<u32>>, Seq<J>, nat)>
    decreases d, s.len() - i, 1nat,
{
    let a = ws(s, i);
    if i > s.len() || !(a < s.len() && s[a as int] == '"') {
        None
    } else {
        match jstr(s, a + 1) {
            None => None,
            Some((k, b)) => {
                let c = ws(s, b);
                if !(c < s.len() && s[c as int] == ':') || !(i < c + 1) {
                    None
                } else {
                    match jv(s, c + 1, d) {
                        None => None,
                        Some((v, e)) => {
                            let f = ws(s, e);
                            if f < s.len() && s[f as int] == ',' {
                                if i < f + 1 && f + 1 <= s.len() {
                                    match jmembers(s, f + 1, d) {
                                        Some((ks, vs, g)) => Some((seq![k] + ks, seq![v] + vs, g)),
                                        None => None,
                                    }
                                } else {
                                    None
                                }
                            } else if f < s.len() && s[f as int] == '}' {
                                Some((seq![k], seq![v], f + 1))
                            } else {
                                None
                            }
                        },
                    }
                }
            },
        }
    }
}

/// strict JSON の文書全体（前後の空白を許す）。d は構造の入れ子の深さ上限。
pub open spec fn jparse(s: Seq<char>, d: nat) -> Option<J> {
    match jv(s, 0, d) {
        Some((j, e)) => if ws(s, e) == s.len() {
            Some(j)
        } else {
            None
        },
        None => None,
    }
}

// ------------------------------------------------------------------ 値 JSON の復号（§9）

pub open spec fn cs(w: Seq<char>) -> Seq<u32> {
    Seq::new(w.len(), |k: int| w[k] as u32)
}

pub open spec fn c_tag() -> Seq<char> {
    seq!['t', 'a', 'g']
}

pub open spec fn k_tag() -> Seq<u32> {
    cs(c_tag())
}

pub open spec fn c_value() -> Seq<char> {
    seq!['v', 'a', 'l', 'u', 'e']
}

pub open spec fn k_value() -> Seq<u32> {
    cs(c_value())
}

pub open spec fn c_left() -> Seq<char> {
    seq!['l', 'e', 'f', 't']
}

pub open spec fn k_left() -> Seq<u32> {
    cs(c_left())
}

pub open spec fn c_right() -> Seq<char> {
    seq!['r', 'i', 'g', 'h', 't']
}

pub open spec fn k_right() -> Seq<u32> {
    cs(c_right())
}

pub open spec fn c_items() -> Seq<char> {
    seq!['i', 't', 'e', 'm', 's']
}

pub open spec fn k_items() -> Seq<u32> {
    cs(c_items())
}

pub open spec fn c_int() -> Seq<char> {
    seq!['i', 'n', 't']
}

pub open spec fn t_int() -> Seq<u32> {
    cs(c_int())
}

pub open spec fn c_char() -> Seq<char> {
    seq!['c', 'h', 'a', 'r']
}

pub open spec fn t_char() -> Seq<u32> {
    cs(c_char())
}

pub open spec fn c_bool() -> Seq<char> {
    seq!['b', 'o', 'o', 'l']
}

pub open spec fn t_bool() -> Seq<u32> {
    cs(c_bool())
}

pub open spec fn c_unit() -> Seq<char> {
    seq!['u', 'n', 'i', 't']
}

pub open spec fn t_unit() -> Seq<u32> {
    cs(c_unit())
}

pub open spec fn c_none() -> Seq<char> {
    seq!['n', 'o', 'n', 'e']
}

pub open spec fn t_none() -> Seq<u32> {
    cs(c_none())
}

pub open spec fn c_some() -> Seq<char> {
    seq!['s', 'o', 'm', 'e']
}

pub open spec fn t_some() -> Seq<u32> {
    cs(c_some())
}

pub open spec fn c_ok() -> Seq<char> {
    seq!['o', 'k']
}

pub open spec fn t_ok() -> Seq<u32> {
    cs(c_ok())
}

pub open spec fn c_err() -> Seq<char> {
    seq!['e', 'r', 'r']
}

pub open spec fn t_err() -> Seq<u32> {
    cs(c_err())
}

pub open spec fn c_pair() -> Seq<char> {
    seq!['p', 'a', 'i', 'r']
}

pub open spec fn t_pair() -> Seq<u32> {
    cs(c_pair())
}

pub open spec fn c_list() -> Seq<char> {
    seq!['l', 'i', 's', 't']
}

pub open spec fn t_list() -> Seq<u32> {
    cs(c_list())
}

/// キー k の最初の位置（無ければ ks.len()）。
pub open spec fn kpos(ks: Seq<Seq<u32>>, k: Seq<u32>, i: nat) -> nat
    decreases ks.len() - i,
{
    if i >= ks.len() {
        ks.len()
    } else if ks[i as int] == k {
        i
    } else {
        kpos(ks, k, i + 1)
    }
}

pub open spec fn distinct(ks: Seq<Seq<u32>>) -> bool {
    forall|a: int, b: int| 0 <= a < b < ks.len() ==> ks[a] != ks[b]
}

/// キーの集合がちょうど req（重複は別に distinct で拒否する）。
pub open spec fn only(ks: Seq<Seq<u32>>, req: Seq<Seq<u32>>) -> bool {
    &&& ks.len() == req.len()
    &&& forall|r: int| 0 <= r < req.len() ==> #[trigger] kpos(ks, req[r], 0) < ks.len()
}

pub open spec fn dig(u: u32) -> bool {
    48 <= u && u <= 57
}

/// 数字列の値。
pub open spec fn nv(x: Seq<u32>) -> nat
    decreases x.len(),
{
    if x.len() == 0 {
        0
    } else {
        nv(x.drop_last()) * 10 + (x.last() - 48) as nat
    }
}

/// 先頭ゼロの無い数字列。
pub open spec fn cnat(x: Seq<u32>) -> bool {
    &&& x.len() >= 1
    &&& forall|k: int| 0 <= k < x.len() ==> dig(#[trigger] x[k])
    &&& (x[0] != 48 || x.len() == 1)
}

/// 正準十進整数（'-0'、'+1'、先頭ゼロを拒否）。
pub open spec fn cint(x: Seq<u32>) -> Option<int> {
    if x.len() > 0 && x[0] == 45 {
        let y = x.drop_first();
        if cnat(y) && nv(y) != 0 {
            Some(-(nv(y) as int))
        } else {
            None
        }
    } else if cnat(x) {
        Some(nv(x) as int)
    } else {
        None
    }
}

/// 値 JSON の復号。
pub open spec fn jd(j: J, t: Ty) -> Option<Val>
    decreases j, 0nat,
{
    match j {
        J::Obj(ks, vs) => {
            let it = kpos(ks, k_tag(), 0);
            if ks.len() != vs.len() || !distinct(ks) || it >= vs.len() {
                None
            } else {
                match vs[it as int] {
                    J::Str(g) => {
                        let iv = kpos(ks, k_value(), 0);
                        let il = kpos(ks, k_left(), 0);
                        let ir = kpos(ks, k_right(), 0);
                        let ii = kpos(ks, k_items(), 0);
                        match t {
                            Ty::Int => if g == t_int() && only(ks, seq![k_tag(), k_value()]) && iv < vs.len() {
                                match vs[iv as int] {
                                    J::Str(x) => match cint(x) {
                                        Some(n) => Some(Val::Int(n)),
                                        None => None,
                                    },
                                    _ => None,
                                }
                            } else {
                                None
                            },
                            Ty::Char => if g == t_char() && only(ks, seq![k_tag(), k_value()]) && iv < vs.len() {
                                match vs[iv as int] {
                                    J::Str(x) => match cint(x) {
                                        Some(n) => if scalar(n) { Some(Val::Char(n)) } else { None },
                                        None => None,
                                    },
                                    _ => None,
                                }
                            } else {
                                None
                            },
                            Ty::Bool => if g == t_bool() && only(ks, seq![k_tag(), k_value()]) && iv < vs.len() {
                                match vs[iv as int] {
                                    J::Bool(b) => Some(Val::Bool(b)),
                                    _ => None,
                                }
                            } else {
                                None
                            },
                            Ty::Unit => if g == t_unit() && only(ks, seq![k_tag()]) {
                                Some(Val::Unit)
                            } else {
                                None
                            },
                            Ty::Option(el) => if g == t_none() && only(ks, seq![k_tag()]) {
                                Some(Val::None)
                            } else if g == t_some() && only(ks, seq![k_tag(), k_value()]) && iv < vs.len() {
                                match jd(vs[iv as int], *el) {
                                    Some(x) => Some(Val::Some(Box::new(x))),
                                    None => None,
                                }
                            } else {
                                None
                            },
                            Ty::Result(ta, tb) => if g == t_ok() && only(ks, seq![k_tag(), k_value()]) && iv < vs.len() {
                                match jd(vs[iv as int], *ta) {
                                    Some(x) => Some(Val::Ok(Box::new(x))),
                                    None => None,
                                }
                            } else if g == t_err() && only(ks, seq![k_tag(), k_value()]) && iv < vs.len() {
                                match jd(vs[iv as int], *tb) {
                                    Some(x) => Some(Val::Err(Box::new(x))),
                                    None => None,
                                }
                            } else {
                                None
                            },
                            Ty::Pair(ta, tb) => if g == t_pair() && only(ks, seq![k_tag(), k_left(), k_right()]) && il
                                < vs.len() && ir < vs.len() {
                                match (jd(vs[il as int], *ta), jd(vs[ir as int], *tb)) {
                                    (Some(x), Some(y)) => Some(Val::Pair(Box::new(x), Box::new(y))),
                                    _ => None,
                                }
                            } else {
                                None
                            },
                            Ty::List(el) => if g == t_list() && only(ks, seq![k_tag(), k_items()]) && ii < vs.len() {
                                match vs[ii as int] {
                                    J::Arr(xs) => match jds(xs, *el, 0) {
                                        Some(w) => Some(Val::List(w)),
                                        None => None,
                                    },
                                    _ => None,
                                }
                            } else {
                                None
                            },
                            Ty::Named(_) => None,
                            Ty::Dict(kb, vb) => if g == t_list() && only(ks, seq![k_tag(), k_items()]) && ii < vs.len() {
                                match vs[ii as int] {
                                    J::Arr(xs) => match jds(xs, Ty::Pair(kb, vb), 0) {
                                        Some(ps) => if keys_distinct(ps) { Some(Val::List(ps)) } else { None },
                                        None => None,
                                    },
                                    _ => None,
                                }
                            } else {
                                None
                            },
                        }
                    },
                    _ => None,
                }
            }
        },
        _ => None,
    }
}

pub open spec fn jds(xs: Seq<J>, t: Ty, i: nat) -> Option<Seq<Val>>
    decreases xs, xs.len() - i,
{
    if i >= xs.len() {
        Some(Seq::empty())
    } else {
        match (jd(xs[i as int], t), jds(xs, t, i + 1)) {
            (Some(v), Some(w)) => Some(seq![v] + w),
            _ => None,
        }
    }
}

/// どの object のキーも重複しない。
pub open spec fn nodup(j: J) -> bool
    decreases j, 0nat,
{
    match j {
        J::Obj(ks, vs) => distinct(ks) && nodups(vs, 0),
        J::Arr(xs) => nodups(xs, 0),
        _ => true,
    }
}

pub open spec fn nodups(xs: Seq<J>, i: nat) -> bool
    decreases xs, xs.len() - i,
{
    if i >= xs.len() {
        true
    } else {
        nodup(xs[i as int]) && nodups(xs, i + 1)
    }
}

/// 型の消去：Dict<K, V> は値として List<Pair<K, V>> である。型付けの性質は消去後の型で述べる。
pub open spec fn derase(t: Ty) -> Ty
    decreases t,
{
    match t {
        Ty::List(el) => Ty::List(Box::new(derase(*el))),
        Ty::Option(el) => Ty::Option(Box::new(derase(*el))),
        Ty::Pair(ta, tb) => Ty::Pair(Box::new(derase(*ta)), Box::new(derase(*tb))),
        Ty::Result(ta, tb) => Ty::Result(Box::new(derase(*ta)), Box::new(derase(*tb))),
        Ty::Dict(kb, vb) => Ty::List(Box::new(Ty::Pair(Box::new(derase(*kb)), Box::new(derase(*vb))))),
        _ => t,
    }
}

/// 対の値の鍵の正準 JSON（検証済みの符号化 enc）。対でなければ空。
pub open spec fn pkey_enc(v: Val) -> Seq<char> {
    match v {
        Val::Pair(k, _) => enc(*k),
        _ => Seq::empty(),
    }
}

/// 対の列の鍵は、どの二つも正準 JSON が異なる（辞書の鍵の相異）。
pub open spec fn keys_distinct(ps: Seq<Val>) -> bool {
    forall|a: int, b: int| 0 <= a < b < ps.len() ==> pkey_enc(ps[a]) != pkey_enc(ps[b])
}

/// 木 j を型 t で読んだ値（読めないときは Unit。使うのは読めたときだけ）。
pub open spec fn jval(j: J, t: Ty) -> Val {
    match jd(j, t) {
        Some(v) => v,
        None => Val::Unit,
    }
}

/// 先頭 i 項の鍵の符号化（項の順）。
pub open spec fn pkeys(xs: Seq<J>, t: Ty, i: nat) -> Seq<Seq<char>>
    decreases i,
{
    if i == 0 || i > xs.len() {
        Seq::empty()
    } else {
        pkeys(xs, t, (i - 1) as nat).push(pkey_enc(jval(xs[(i - 1) as int], t)))
    }
}

/// 木 j を型 t で読むとき、trusted の復号器（values.rs）の最初の誤りが辞書の重複鍵である。
/// values.rs の DFS の順（形の検査、対の子の順、項の順）を写す。鍵の重複の検査の位置だけを表し、
/// 資源上限の誤りは含まない（上限は性質の外）。
pub open spec fn dupfirst(j: J, t: Ty) -> bool
    decreases j, 0nat,
{
    match j {
        J::Obj(ks, vs) => {
            let it = kpos(ks, k_tag(), 0);
            if ks.len() != vs.len() || !distinct(ks) || it >= vs.len() {
                false
            } else {
                match vs[it as int] {
                    J::Str(g) => {
                        let iv = kpos(ks, k_value(), 0);
                        let il = kpos(ks, k_left(), 0);
                        let ir = kpos(ks, k_right(), 0);
                        let ii = kpos(ks, k_items(), 0);
                        match t {
                            Ty::Option(el) => if g == t_some() && only(ks, seq![k_tag(), k_value()]) && iv < vs.len() {
                                dupfirst(vs[iv as int], *el)
                            } else {
                                false
                            },
                            Ty::Result(ta, tb) => if g == t_ok() && only(ks, seq![k_tag(), k_value()]) && iv < vs.len() {
                                dupfirst(vs[iv as int], *ta)
                            } else if g == t_err() && only(ks, seq![k_tag(), k_value()]) && iv < vs.len() {
                                dupfirst(vs[iv as int], *tb)
                            } else {
                                false
                            },
                            Ty::Pair(ta, tb) => if g == t_pair() && only(ks, seq![k_tag(), k_left(), k_right()]) && il
                                < vs.len() && ir < vs.len() {
                                match (vs[il as int], vs[ir as int]) {
                                    (J::Obj(_, _), J::Obj(_, _)) => if jd(vs[il as int], *ta) is None {
                                        dupfirst(vs[il as int], *ta)
                                    } else {
                                        dupfirst(vs[ir as int], *tb)
                                    },
                                    _ => false,
                                }
                            } else {
                                false
                            },
                            Ty::List(el) => if g == t_list() && only(ks, seq![k_tag(), k_items()]) && ii < vs.len() {
                                match vs[ii as int] {
                                    J::Arr(xs) => dupfirst_items(xs, *el, 0),
                                    _ => false,
                                }
                            } else {
                                false
                            },
                            Ty::Dict(kb, vb) => if g == t_list() && only(ks, seq![k_tag(), k_items()]) && ii < vs.len() {
                                match vs[ii as int] {
                                    J::Arr(xs) => dupfirst_dict(xs, Ty::Pair(kb, vb), 0),
                                    _ => false,
                                }
                            } else {
                                false
                            },
                            _ => false,
                        }
                    },
                    _ => false,
                }
            }
        },
        _ => false,
    }
}

/// 項 xs[i..] を型 el で読む。最初に読めない項の誤りが重複鍵であるとき真。
pub open spec fn dupfirst_items(xs: Seq<J>, el: Ty, i: nat) -> bool
    decreases xs, xs.len() - i,
{
    if i >= xs.len() {
        false
    } else if jd(xs[i as int], el) is None {
        dupfirst(xs[i as int], el)
    } else {
        dupfirst_items(xs, el, i + 1)
    }
}

/// 辞書の項 xs[i..]（各項は対）。最初の誤りが項の誤りの重複鍵であるとき真。
/// 項 i の鍵が、先頭 i 項の鍵のどれかと等しければ重複（values.rs は読んだ後に鍵を検査する）。
pub open spec fn dupfirst_dict(xs: Seq<J>, pt: Ty, i: nat) -> bool
    decreases xs, xs.len() - i,
{
    if i >= xs.len() {
        false
    } else if jd(xs[i as int], pt) is None {
        dupfirst(xs[i as int], pt)
    } else if !(jval(xs[i as int], pt) is Pair) {
        false
    } else if pkeys(xs, pt, i).contains(pkey_enc(jval(xs[i as int], pt))) {
        true
    } else {
        dupfirst_dict(xs, pt, i + 1)
    }
}

/// 入力 JSON 文書の復号で、trusted の復号器の最初の誤りが辞書の重複鍵である。
/// 文書の object のキーの重複は trusted の構文解析が先に拒否する（nodup）。
pub open spec fn input_dupfirst(s: Seq<char>, d: nat, t: Ty) -> bool {
    match jparse(s, d) {
        Some(j) => nodup(j) && dupfirst(j, t),
        None => false,
    }
}

/// 入力 JSON 文書を型 t の値として読む。
pub open spec fn input_val(s: Seq<char>, d: nat, t: Ty) -> Option<Val> {
    match jparse(s, d) {
        Some(j) => jd(j, t),
        None => None,
    }
}

} // verus!
