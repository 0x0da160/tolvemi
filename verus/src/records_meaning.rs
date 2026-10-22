//! 源のレコードの意味（段階 2 の S4a）。展開（pair の入れ子への書き換え）を経由しない、印なしの源の意味。
//!
//! 値 `RVal` のレコードは field の値の列（宣言の順）で、pair とは別の値である。式 `RExpr` は記録の断片：
//! 整数・真偽・単位・変数・pair・構築 `R { f: e, ..base }`・参照 `e.f`・if・let。field は名前（番号）で書き、構築と参照は
//! 持ち主の宣言の名前の列（宣言の順）を添える。位置は宣言の列の中の位置で、名前の解決（resolve.rs）の仕事である。
//!
//! 意味 `rmean` は部分関数。名前の規則に違反する形（未知の field、同じ field の重複、書いていない field があるのに
//! base が無い）と、値を持たない形は None になる。base は書いていない field があるときだけ評価する。全部書いた
//! 構築は base を見ない（静的には E-RECORD-BASE-REDUNDANT で拒否される形で、ここでは値だけを決める）。
//!
//! 証明したこと（`assume`・`admit`・`external_body` なし）：
//! - 名前の位置（`pos_some`）と、書いた field の値の対応（`wmap_get`、`wmap_dom`、`wmap_dup`）。
//! - 全部書いた構築の参照（`get_build`）、書いた field の更新の参照（`get_written`）、書いていない field の更新は
//!   base の参照（`get_base`）、全部書いた更新は base を捨てる（`drop_base`）。
//! - 欠けた field、未知の field、重複は None（`missing`、`unknown`、`dup`）。
//!
//! 証明していないこと：展開（resolve.rs の rx）がこの意味と一致すること（S4b）、印つきの写し、型付け。

use vstd::prelude::*;

verus! {

/// 源の値。レコードは field の値の列（宣言の順）。pair とは別の値。
pub enum RVal {
    Int(int),
    Bool(bool),
    /// 文字（Unicode のスカラー値の整数）。
    Char(int),
    /// Option の none。
    None,
    /// Option の some（中の値）。
    Some(Box<RVal>),
    Unit,
    Pair(Box<RVal>, Box<RVal>),
    Rec(Seq<RVal>),
}

/// 源の式（レコードの断片）。field は名前（番号）で書く。構築と参照は持ち主の宣言の名前の列 decl を添える。
pub enum RExpr {
    Int(int),
    Bool(bool),
    Char(int),
    /// Option の none（型は値に現れないので持たない）。
    None,
    /// Option の some。
    Some(Box<RExpr>),
    Unit,
    Var(nat),
    Pair(Box<RExpr>, Box<RExpr>),
    /// R { f: e, ..base }：宣言の名前の列、書いた field（名前と式の列）、省略できる base。
    Rec(Seq<nat>, Seq<(nat, RExpr)>, Option<Box<RExpr>>),
    /// e.f：持ち主の宣言の名前の列 decl と、参照する field の名前 f。
    Fld(Box<RExpr>, Seq<nat>, nat),
    /// if c then a else b。c は真偽値でなければならない。
    If(Box<RExpr>, Box<RExpr>, Box<RExpr>),
    /// let x = a in b：束縛する名前 x（核の番号、rx の sc.len()）、束縛する式 a、本体 b。
    Let(nat, Box<RExpr>, Box<RExpr>),
}

/// 名前 f の位置（宣言の名前の列 decl の中で最初に現れる位置）。
pub open spec fn pos(decl: Seq<nat>, f: nat) -> Option<nat>
    decreases decl.len(),
{
    if decl.len() == 0 {
        None
    } else if decl[0] == f {
        Some(0)
    } else {
        match pos(decl.drop_first(), f) {
            Some(k) => Some(k + 1),
            None => None,
        }
    }
}

/// 書いた field の名前は、どれも宣言の名前（未知の field は拒否する）。
pub open spec fn known(decl: Seq<nat>, ws: Seq<(nat, RExpr)>) -> bool {
    forall|k: int| 0 <= k < ws.len() ==> pos(decl, #[trigger] ws[k].0) is Some
}

/// 名前 n は書いた field のどれかに現れる。
pub open spec fn written(ws: Seq<(nat, RExpr)>, n: nat) -> bool {
    exists|k: int| 0 <= k < ws.len() && #[trigger] ws[k].0 == n
}

/// 宣言の名前は、どれも書いた field に現れる（書いていない field が無い）。
pub open spec fn covered(decl: Seq<nat>, ws: Seq<(nat, RExpr)>) -> bool {
    forall|j: int| 0 <= j < decl.len() ==> written(ws, #[trigger] decl[j])
}

/// 書いた field の値を名前から値へ写す（i から順に評価する）。同じ名前が二度あれば None。
pub open spec fn wmap(env: Map<nat, RVal>, ws: Seq<(nat, RExpr)>, i: nat) -> Option<Map<nat, RVal>>
    decreases ws, ws.len() - i,
{
    if i >= ws.len() {
        Some(Map::empty())
    } else {
        match (rmean(env, ws[i as int].1), wmap(env, ws, i + 1)) {
            (Some(v), Some(m)) => if m.contains_key(ws[i as int].0) {
                None
            } else {
                Some(m.insert(ws[i as int].0, v))
            },
            _ => None,
        }
    }
}

/// 字段の値の列：宣言の位置 j に、書いた値（名前が m にあれば）、無ければ bs の j 番目（bs の長さの内側）。
pub open spec fn place(decl: Seq<nat>, m: Map<nat, RVal>, bs: Seq<RVal>) -> Seq<RVal> {
    Seq::new(
        decl.len(),
        |j: int| if m.contains_key(decl[j]) {
            m[decl[j]]
        } else if j < bs.len() {
            bs[j]
        } else {
            RVal::Unit
        },
    )
}

/// 源の意味（部分関数）。
pub open spec fn rmean(env: Map<nat, RVal>, e: RExpr) -> Option<RVal>
    decreases e, 0nat,
{
    match e {
        RExpr::Int(i) => Some(RVal::Int(i)),
        RExpr::Bool(b) => Some(RVal::Bool(b)),
        RExpr::Char(c) => Some(RVal::Char(c)),
        RExpr::None => Some(RVal::None),
        RExpr::Some(a) => match rmean(env, *a) {
            Some(v) => Some(RVal::Some(Box::new(v))),
            None => None,
        },
        RExpr::Unit => Some(RVal::Unit),
        RExpr::Var(x) => if env.contains_key(x) {
            Some(env[x])
        } else {
            None
        },
        RExpr::Pair(a, b) => match (rmean(env, *a), rmean(env, *b)) {
            (Some(u), Some(v)) => Some(RVal::Pair(Box::new(u), Box::new(v))),
            _ => None,
        },
        RExpr::Rec(decl, ws, base) => if !known(decl, ws) {
            None
        } else {
            match wmap(env, ws, 0) {
                None => None,
                Some(m) => if forall|j: int| 0 <= j < decl.len() ==> m.contains_key(#[trigger] decl[j]) {
                    Some(RVal::Rec(place(decl, m, Seq::empty())))
                } else {
                    match base {
                        None => None,
                        Some(b) => match rmean(env, *b) {
                            Some(RVal::Rec(bs)) => if bs.len() == decl.len() {
                                Some(RVal::Rec(place(decl, m, bs)))
                            } else {
                                None
                            },
                            _ => None,
                        },
                    }
                },
            }
        },
        RExpr::Fld(r, decl, f) => match (rmean(env, *r), pos(decl, f)) {
            (Some(RVal::Rec(vs)), Some(p)) => if vs.len() == decl.len() && p < vs.len() {
                Some(vs[p as int])
            } else {
                None
            },
            _ => None,
        },
        RExpr::If(c, a, b) => match rmean(env, *c) {
            Some(RVal::Bool(true)) => rmean(env, *a),
            Some(RVal::Bool(false)) => rmean(env, *b),
            _ => None,
        },
        RExpr::Let(x, a, b) => match rmean(env, *a) {
            Some(va) => rmean(env.insert(x, va), *b),
            None => None,
        },
    }
}

// ------------------------------------------------------------------ 名前の位置

/// 名前の位置は宣言の内側で、そこに名前 f がある。
pub proof fn pos_some(decl: Seq<nat>, f: nat)
    requires
        pos(decl, f) is Some,
    ensures
        pos(decl, f)->Some_0 < decl.len(),
        decl[pos(decl, f)->Some_0 as int] == f,
    decreases decl.len(),
{
    reveal_with_fuel(pos, 2);
    if decl[0] == f {
    } else {
        pos_some(decl.drop_first(), f);
    }
}

// ------------------------------------------------------------------ 書いた field の値

/// 評価が通れば、番号 k の書いた field の名前は地図に入り、その値は式の値である。
pub proof fn wmap_get(env: Map<nat, RVal>, ws: Seq<(nat, RExpr)>, i: nat, m: Map<nat, RVal>, k: int)
    requires
        wmap(env, ws, i) == Some(m),
        i <= k < ws.len(),
    ensures
        m.contains_key(ws[k].0),
        rmean(env, ws[k].1) is Some,
        m[ws[k].0] == rmean(env, ws[k].1)->Some_0,
    decreases ws.len() - i,
{
    reveal_with_fuel(wmap, 2);
    if k == i as int {
    } else {
        let m1 = wmap(env, ws, i + 1)->Some_0;
        wmap_get(env, ws, i + 1, m1, k);
    }
}

/// 地図に入る名前は、どれかの書いた field の名前である。
pub proof fn wmap_dom(env: Map<nat, RVal>, ws: Seq<(nat, RExpr)>, i: nat, m: Map<nat, RVal>, n: nat)
    requires
        wmap(env, ws, i) == Some(m),
        m.contains_key(n),
    ensures
        exists|k: int| i <= k < ws.len() && #[trigger] ws[k].0 == n,
    decreases ws.len() - i,
{
    reveal_with_fuel(wmap, 2);
    if i >= ws.len() {
    } else {
        let m1 = wmap(env, ws, i + 1)->Some_0;
        if ws[i as int].0 == n {
        } else {
            wmap_dom(env, ws, i + 1, m1, n);
        }
    }
}

/// 同じ名前が二度あれば、評価は None になる（重複は拒否する）。
pub proof fn wmap_dup(env: Map<nat, RVal>, ws: Seq<(nat, RExpr)>, i: nat, a: int, b: int)
    requires
        i <= a < b < ws.len(),
        ws[a].0 == ws[b].0,
    ensures
        wmap(env, ws, i) is None,
    decreases ws.len() - i,
{
    reveal_with_fuel(wmap, 2);
    if a == i as int {
        if wmap(env, ws, i + 1) is Some {
            let m1 = wmap(env, ws, i + 1)->Some_0;
            wmap_get(env, ws, i + 1, m1, b);
        }
    } else {
        wmap_dup(env, ws, i + 1, a, b);
    }
}

// ------------------------------------------------------------------ 参照と更新

/// 全部書いた構築（base が無い）の参照：字段 f の値は、f を書いた式の値。
pub proof fn get_build(env: Map<nat, RVal>, decl: Seq<nat>, ws: Seq<(nat, RExpr)>, f: nat, p: nat, k: int)
    requires
        known(decl, ws),
        covered(decl, ws),
        pos(decl, f) == Some(p),
        0 <= k < ws.len(),
        ws[k].0 == f,
        wmap(env, ws, 0) is Some,
    ensures
        rmean(env, RExpr::Fld(Box::new(RExpr::Rec(decl, ws, None)), decl, f)) == rmean(env, ws[k].1),
{
    let m = wmap(env, ws, 0)->Some_0;
    wmap_get(env, ws, 0, m, k);
    assert forall|j: int| 0 <= j < decl.len() implies m.contains_key(#[trigger] decl[j]) by {
        assert(written(ws, decl[j]));
        let k2 = choose|k2: int| 0 <= k2 < ws.len() && ws[k2].0 == decl[j];
        wmap_get(env, ws, 0, m, k2);
    }
    pos_some(decl, f);
    reveal_with_fuel(rmean, 2);
}

/// 書いた field の参照（base があっても、構築の値が決まれば）：字段 f の値は、f を書いた式の値。
pub proof fn get_written(env: Map<nat, RVal>, decl: Seq<nat>, ws: Seq<(nat, RExpr)>, base: Option<Box<RExpr>>, f: nat, p: nat, k: int)
    requires
        pos(decl, f) == Some(p),
        0 <= k < ws.len(),
        ws[k].0 == f,
        rmean(env, RExpr::Rec(decl, ws, base)) is Some,
    ensures
        rmean(env, RExpr::Fld(Box::new(RExpr::Rec(decl, ws, base)), decl, f)) == rmean(env, ws[k].1),
{
    reveal_with_fuel(rmean, 2);
    assert(wmap(env, ws, 0) is Some);
    let m = wmap(env, ws, 0)->Some_0;
    wmap_get(env, ws, 0, m, k);
    pos_some(decl, f);
}

/// 書いていない field の参照：更新の値の字段 f は、base の字段 f と同じ。
/// 構築そのものが評価できる（wmap が通る）ときに限る。評価できない構築は、base が評価できても None。
pub proof fn get_base(env: Map<nat, RVal>, decl: Seq<nat>, ws: Seq<(nat, RExpr)>, b: Box<RExpr>, f: nat, p: nat)
    requires
        known(decl, ws),
        pos(decl, f) == Some(p),
        wmap(env, ws, 0) is Some,
        forall|k: int| 0 <= k < ws.len() ==> ws[k].0 != f,
    ensures
        rmean(env, RExpr::Fld(Box::new(RExpr::Rec(decl, ws, Some(b))), decl, f))
            == rmean(env, RExpr::Fld(b, decl, f)),
{
    reveal_with_fuel(rmean, 2);
    pos_some(decl, f);
    let m = wmap(env, ws, 0)->Some_0;
    assert(!m.contains_key(f)) by {
        if m.contains_key(f) {
            wmap_dom(env, ws, 0, m, f);
        }
    }
    assert(!(forall|j: int| 0 <= j < decl.len() ==> m.contains_key(#[trigger] decl[j]))) by {
        if forall|j: int| 0 <= j < decl.len() ==> m.contains_key(#[trigger] decl[j]) {
            assert(m.contains_key(decl[p as int]));
        }
    }
}

/// 全部書いた更新は base を見ない：base の値（評価できるか）に依らず、構築と同じ値。
pub proof fn drop_base(env: Map<nat, RVal>, decl: Seq<nat>, ws: Seq<(nat, RExpr)>, b: Box<RExpr>)
    requires
        covered(decl, ws),
    ensures
        rmean(env, RExpr::Rec(decl, ws, Some(b))) == rmean(env, RExpr::Rec(decl, ws, None)),
{
    reveal_with_fuel(rmean, 2);
    if wmap(env, ws, 0) is Some {
        let m = wmap(env, ws, 0)->Some_0;
        assert forall|j: int| 0 <= j < decl.len() implies m.contains_key(#[trigger] decl[j]) by {
            assert(written(ws, decl[j]));
            let k2 = choose|k2: int| 0 <= k2 < ws.len() && ws[k2].0 == decl[j];
            wmap_get(env, ws, 0, m, k2);
        }
    }
}

// ------------------------------------------------------------------ 拒否

/// 欠けた field があり、base が無いなら None。
pub proof fn missing(env: Map<nat, RVal>, decl: Seq<nat>, ws: Seq<(nat, RExpr)>)
    requires
        known(decl, ws),
        !covered(decl, ws),
    ensures
        rmean(env, RExpr::Rec(decl, ws, None)) is None,
{
    reveal_with_fuel(rmean, 2);
    if wmap(env, ws, 0) is Some {
        let m = wmap(env, ws, 0)->Some_0;
        assert(!(forall|j: int| 0 <= j < decl.len() ==> m.contains_key(#[trigger] decl[j]))) by {
            if forall|j: int| 0 <= j < decl.len() ==> m.contains_key(#[trigger] decl[j]) {
                assert forall|j: int| 0 <= j < decl.len() implies written(ws, #[trigger] decl[j]) by {
                    assert(m.contains_key(decl[j]));
                    wmap_dom(env, ws, 0, m, decl[j]);
                }
                assert(covered(decl, ws));
            }
        }
    }
}

/// 未知の field は None。
pub proof fn unknown(env: Map<nat, RVal>, decl: Seq<nat>, ws: Seq<(nat, RExpr)>, base: Option<Box<RExpr>>)
    requires
        !known(decl, ws),
    ensures
        rmean(env, RExpr::Rec(decl, ws, base)) is None,
{
    reveal_with_fuel(rmean, 2);
}

/// 同じ field を二度書けば None。
pub proof fn dup(env: Map<nat, RVal>, decl: Seq<nat>, ws: Seq<(nat, RExpr)>, base: Option<Box<RExpr>>, a: int, b: int)
    requires
        0 <= a < b < ws.len(),
        ws[a].0 == ws[b].0,
    ensures
        rmean(env, RExpr::Rec(decl, ws, base)) is None,
{
    reveal_with_fuel(rmean, 2);
    wmap_dup(env, ws, 0, a, b);
}

} // verus!
