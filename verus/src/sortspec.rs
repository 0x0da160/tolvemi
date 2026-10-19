//! sort_by の仕様（段階 1b・SH1 の第三部）。
//!
//! OD-3 の決定（挿入の手順）に従い、源の意味は挿入の手順そのものとする。
//! 鍵つきの要素 (値, 鍵) を、先頭から一つずつ整列済みの列へ挿入する。新しい要素は、鍵が自分より大きい
//! 最初の要素の前に入る。鍵が等しい要素は元の順のまま（安定）。
//! 核の書換え（sortmeaning.rs）は、この挿入を畳み込みで行い、同じ値の列になることを示す。

use crate::spec::*;
use vstd::prelude::*;

verus! {

// ------------------------------------------------------------------ 挿入の手順

/// 整列済みの列 s に要素 e を挿入する（鍵が e の鍵より大きい最初の要素の前）。
pub open spec fn ins_sorted(s: Seq<(Val, int)>, e: (Val, int)) -> Seq<(Val, int)>
    decreases s.len(),
{
    if s.len() == 0 {
        seq![e]
    } else if e.1 < s[0].1 {
        seq![e] + s
    } else {
        seq![s[0]] + ins_sorted(s.drop_first(), e)
    }
}

/// 先頭 n 個の要素を、順に挿入して並べた列。
pub open spec fn sort_prefix(zp: Seq<(Val, int)>, n: nat) -> Seq<(Val, int)>
    decreases n,
{
    if n == 0 || n > zp.len() {
        Seq::empty()
    } else {
        ins_sorted(sort_prefix(zp, (n - 1) as nat), zp[(n - 1) as int])
    }
}

/// 値の列（鍵を外す）。
pub open spec fn pvals(s: Seq<(Val, int)>) -> Seq<Val> {
    Seq::new(s.len(), |i: int| s[i].0)
}

/// 値と鍵を組にする（keys は items と同じ長さ）。
pub open spec fn zip_keys(items: Seq<Val>, keys: Seq<int>) -> Seq<(Val, int)> {
    Seq::new(items.len(), |i: int| (items[i], keys[i]))
}

/// sort_by の意味：値を鍵の昇順に、同じ鍵は元の順のまま並べた列。
pub open spec fn sort_vals(items: Seq<Val>, keys: Seq<int>) -> Seq<Val> {
    pvals(sort_prefix(zip_keys(items, keys), items.len()))
}

/// 整数の値を整数にする（整数でなければ None）。
pub open spec fn int_of_val(v: Val) -> Option<int> {
    match v {
        Val::Int(n) => Some(n),
        _ => None,
    }
}

/// 鍵の値の列を整数の列にする（整数でない値があれば None）。
pub open spec fn int_seq(vs: Seq<Val>) -> Option<Seq<int>> {
    if forall|i: int| 0 <= i < vs.len() ==> int_of_val(#[trigger] vs[i]) is Some {
        Some(Seq::new(vs.len(), |i: int| int_of_val(vs[i])->Some_0))
    } else {
        None
    }
}

// ------------------------------------------------------------------ 内側の畳み込みの状態

/// 先頭 q 個の要素を処理した後の出力（逆順に積んだ列）と、e を置いたかどうか。
/// 要素 t の鍵が e の鍵より大きければ、t の前に e を置く。
pub open spec fn out_ins(ep: (Val, int), s: Seq<(Val, int)>, q: nat) -> (Seq<Val>, bool)
    decreases q,
{
    if q == 0 {
        (Seq::empty(), false)
    } else {
        let t = s[(q - 1) as int];
        let prev = out_ins(ep, s, (q - 1) as nat);
        if prev.1 {
            (seq![t.0] + prev.0, true)
        } else if ep.1 < t.1 {
            (seq![t.0, ep.0] + prev.0, true)
        } else {
            (seq![t.0] + prev.0, false)
        }
    }
}

/// 内側の畳み込みの状態。j = 0 は初期状態（鍵の枠は None）。j ≥ 1 では、最初の要素 e の鍵 ep.1 を枠に残し、
/// 出力は先頭 j - 1 個の要素 s[0..j-1] を処理した結果。
pub open spec fn inner_val(ep: (Val, int), s: Seq<(Val, int)>, j: nat) -> Val {
    if j == 0 {
        Val::Pair(
            Box::new(Val::None),
            Box::new(Val::Pair(Box::new(Val::List(Seq::empty())), Box::new(Val::Bool(false)))),
        )
    } else {
        Val::Pair(
            Box::new(Val::Some(Box::new(Val::Int(ep.1)))),
            Box::new(
                Val::Pair(
                    Box::new(Val::List(out_ins(ep, s, (j - 1) as nat).0)),
                    Box::new(Val::Bool(out_ins(ep, s, (j - 1) as nat).1)),
                ),
            ),
        )
    }
}

// ------------------------------------------------------------------ 補題

/// 先頭への追加の reverse は、末尾への追加に一致する。
pub proof fn rev_cons(x: Val, s: Seq<Val>)
    ensures
        rev(seq![x] + s) =~= rev(s) + seq![x],
{
    let t = seq![x] + s;
    assert(rev(t).len() == t.len());
    assert((rev(s) + seq![x]).len() == t.len());
    assert forall|i: int| 0 <= i < t.len() implies rev(t)[i] == (rev(s) + seq![x])[i] by {
        if i == s.len() {
            assert(t[0] == x);
        } else {
            assert(t[t.len() - 1 - i] == s[s.len() - 1 - i]);
            assert(rev(s)[i] == s[s.len() - 1 - i]);
        }
    }
    assert(rev(t) =~= rev(s) + seq![x]);
}

/// 対の値の列を取り出すと、末尾への追加は値の末尾への追加になる。
pub proof fn pvals_snoc(s: Seq<(Val, int)>, t: (Val, int))
    ensures
        pvals(s + seq![t]) =~= pvals(s) + seq![t.0],
{
    let u = s + seq![t];
    assert(pvals(u).len() == pvals(s).len() + 1);
    assert forall|i: int| 0 <= i < pvals(u).len() implies pvals(u)[i] == (pvals(s) + seq![t.0])[i] by {
        if i < s.len() {
            assert(u[i] == s[i]);
        } else {
            assert(u[i] == t);
        }
    }
    assert(pvals(u) =~= pvals(s) + seq![t.0]);
}

/// 挿入の基本：鍵がすべて e 以下の列への挿入は、末尾への追加になる。
pub proof fn ins_all_le(s: Seq<(Val, int)>, e: (Val, int))
    requires
        forall|r: int| 0 <= r < s.len() ==> s[r].1 <= e.1,
    ensures
        ins_sorted(s, e) =~= s + seq![e],
    decreases s.len(),
{
    reveal_with_fuel(ins_sorted, 2);
    if s.len() > 0 {
        let d = s.drop_first();
        assert(s =~= seq![s[0]] + d);
        assert(s[0].1 <= e.1);
        assert forall|r: int| 0 <= r < d.len() implies d[r].1 <= e.1 by {
            assert(d[r] == s[r + 1]);
        }
        ins_all_le(d, e);
        assert(!(e.1 < s[0].1));
        assert(ins_sorted(s, e) =~= seq![s[0]] + ins_sorted(d, e));
        assert(seq![s[0]] + (d + seq![e]) =~= (seq![s[0]] + d) + seq![e]);
    }
}

/// 鍵が e より大きい要素が先頭側にあれば、末尾に要素を足しても挿入の位置は変わらない。
pub proof fn ins_snoc_gt(s: Seq<(Val, int)>, e: (Val, int), t: (Val, int))
    requires
        exists|r: int| 0 <= r < s.len() && s[r].1 > e.1,
    ensures
        ins_sorted(s + seq![t], e) =~= ins_sorted(s, e) + seq![t],
    decreases s.len(),
{
    reveal_with_fuel(ins_sorted, 2);
    let u = s + seq![t];
    if s.len() == 0 {
        let r = choose|r: int| 0 <= r < s.len() && s[r].1 > e.1;
        assert(false);
    } else if e.1 < s[0].1 {
        assert(u[0] == s[0]);
        assert(ins_sorted(u, e) =~= seq![e] + u);
        assert(ins_sorted(s, e) =~= seq![e] + s);
        assert(seq![e] + u =~= (seq![e] + s) + seq![t]);
    } else {
        let r = choose|r: int| 0 <= r < s.len() && s[r].1 > e.1;
        let d = s.drop_first();
        assert(s[0].1 <= e.1);
        assert(r != 0);
        assert(s =~= seq![s[0]] + d);
        assert(d[r - 1] == s[r]);
        assert(u[0] == s[0]);
        assert(u.drop_first() =~= d + seq![t]);
        assert(0 <= r - 1 < d.len() && d[r - 1].1 > e.1);
        assert(exists|r2: int| 0 <= r2 < d.len() && d[r2].1 > e.1) by {
            assert(0 <= r - 1 < d.len() && d[r - 1].1 > e.1);
        }
        ins_snoc_gt(d, e, t);
        assert(ins_sorted(u, e) =~= seq![s[0]] + ins_sorted(u.drop_first(), e));
        assert(ins_sorted(s, e) =~= seq![s[0]] + ins_sorted(d, e));
        assert(seq![s[0]] + (ins_sorted(d, e) + seq![t]) =~= (seq![s[0]] + ins_sorted(d, e)) + seq![t]);
    }
}

/// 鍵がすべて e 以下の列に、e より大きい鍵の要素を足すと、挿入は「列、e、要素」になる。
pub proof fn ins_snoc_tail(s: Seq<(Val, int)>, e: (Val, int), t: (Val, int))
    requires
        forall|r: int| 0 <= r < s.len() ==> s[r].1 <= e.1,
        e.1 < t.1,
    ensures
        ins_sorted(s + seq![t], e) =~= s + seq![e] + seq![t],
    decreases s.len(),
{
    reveal_with_fuel(ins_sorted, 2);
    let u = s + seq![t];
    if s.len() == 0 {
        assert(u =~= seq![t]);
        assert(ins_sorted(u, e) =~= seq![e] + seq![t]);
    } else {
        let d = s.drop_first();
        assert(s =~= seq![s[0]] + d);
        assert(u =~= seq![s[0]] + (d + seq![t]));
        assert(u[0] == s[0]);
        assert(u.drop_first() =~= d + seq![t]);
        assert(s[0].1 <= e.1);
        assert forall|r: int| 0 <= r < d.len() implies d[r].1 <= e.1 by {
            assert(d[r] == s[r + 1]);
        }
        ins_snoc_tail(d, e, t);
        assert(!(e.1 < s[0].1));
        assert(ins_sorted(u, e) =~= seq![s[0]] + ins_sorted(u.drop_first(), e));
        assert(ins_sorted(u.drop_first(), e) =~= d + seq![e] + seq![t]);
        assert(seq![s[0]] + (d + seq![e] + seq![t]) =~= (seq![s[0]] + d) + seq![e] + seq![t]);
    }
}

/// 内側の出力の不変条件（先頭 q 個について）。
/// 置いたのは、先頭 q 個に鍵が e より大きい要素があるとき、かつそのときだけ。
/// 置いたときの出力の逆順は、先頭 q 個へ挿入した列の値に一致する。置いていないときは、
/// 先頭 q 個の鍵がすべて e 以下で、出力の逆順は先頭 q 個の値の列に一致する。
pub proof fn out_ins_inv(ep: (Val, int), s: Seq<(Val, int)>, q: nat)
    requires
        q <= s.len(),
    ensures
        out_ins(ep, s, q).1 <==> (exists|r: int| 0 <= r < q && s[r].1 > ep.1),
        out_ins(ep, s, q).1 ==> rev(out_ins(ep, s, q).0) =~= pvals(ins_sorted(s.subrange(0, q as int), ep)),
        !out_ins(ep, s, q).1 ==> (forall|r: int| 0 <= r < q ==> s[r].1 <= ep.1) && rev(out_ins(ep, s, q).0)
            =~= pvals(s.subrange(0, q as int)),
    decreases q,
{
    reveal_with_fuel(out_ins, 1);
    if q > 0 {
        let qq = (q - 1) as nat;
        out_ins_inv(ep, s, qq);
        let t = s[qq as int];
        let prev = out_ins(ep, s, qq);
        let sub = s.subrange(0, qq as int);
        assert(sub.len() == qq);
        assert(forall|r: int| 0 <= r < qq ==> sub[r] == s[r]);
        assert(sub + seq![t] =~= s.subrange(0, q as int));
        if prev.1 {
            assert(exists|r: int| 0 <= r < sub.len() && sub[r].1 > ep.1) by {
                let r0 = choose|r: int| 0 <= r < qq && s[r].1 > ep.1;
                assert(sub[r0] == s[r0]);
            }
            ins_snoc_gt(sub, ep, t);
            rev_cons(t.0, prev.0);
            pvals_snoc(ins_sorted(sub, ep), t);
            assert(ins_sorted(sub + seq![t], ep) =~= ins_sorted(s.subrange(0, q as int), ep));
        } else if ep.1 < t.1 {
            assert(exists|r: int| 0 <= r < q && s[r].1 > ep.1) by {
                assert(0 <= qq < q && s[qq as int].1 > ep.1);
            }
            assert(forall|r: int| 0 <= r < sub.len() ==> sub[r].1 <= ep.1);
            ins_snoc_tail(sub, ep, t);
            pvals_snoc(sub, ep);
            pvals_snoc(sub + seq![ep], t);
            rev_cons(ep.0, prev.0);
            rev_cons(t.0, seq![ep.0] + prev.0);
            assert(seq![t.0, ep.0] + prev.0 =~= seq![t.0] + (seq![ep.0] + prev.0));
            assert(ins_sorted(s.subrange(0, q as int), ep) =~= sub + seq![ep] + seq![t]);
        } else {
            assert(forall|r: int| 0 <= r < q ==> s[r].1 <= ep.1) by {
                assert forall|r: int| 0 <= r < q implies s[r].1 <= ep.1 by {
                    if r < qq {
                        assert(s[r].1 <= ep.1);
                    } else {
                        assert(r == qq);
                    }
                }
            }
            rev_cons(t.0, prev.0);
            pvals_snoc(sub, t);
            assert(pvals(sub + seq![t]) =~= pvals(s.subrange(0, q as int)));
        }
    }
}

/// 整数の列を値の列にして戻すと、もとの整数の列になる。
pub proof fn int_seq_of(keys: Seq<int>)
    ensures
        int_seq(Seq::new(keys.len(), |i: int| Val::Int(keys[i]))) == Some(keys),
{
    let vs = Seq::new(keys.len(), |i: int| Val::Int(keys[i]));
    assert(forall|i: int| 0 <= i < vs.len() ==> int_of_val(#[trigger] vs[i]) is Some);
    assert(int_seq(vs) == Some(Seq::new(vs.len(), |i: int| int_of_val(vs[i])->Some_0)));
    assert(Seq::new(vs.len(), |i: int| int_of_val(vs[i])->Some_0) =~= keys);
}

} // verus!
