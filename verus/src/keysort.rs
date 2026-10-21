//! 鍵の符号の列の整列（入力の復号の重複キーの検査に使う）。
//!
//! - `lex_le` は u32 の列の辞書式順序。反対称・推移・全域を示す（`lex_antisym`、`lex_trans`、`lex_total`）。
//! - `sort_keys_e` は鍵の列を併合整列し、鍵への参照の列を返す。返す列は入力の並べ替え（多重集合が等しい）で、
//!   辞書式順序に整列している。鍵の比較は O(n log n) 回。
//! - `sorted_perm_distinct`：整列した並べ替えでは、隣り合う二つが異なることと、元の列のどの二つも異なること
//!   （`distinct`）は同じ。

use crate::input::*;
use crate::input_exec::*;
use vstd::prelude::*;
use vstd::seq_lib::*;

verus! {

// ------------------------------------------------------------------ 辞書式順序

/// u32 の列の辞書式順序（a が b 以下）。先頭から比べて最初に異なる値の小さい方が前。片方が他方の先頭部分なら短い方が前。
pub open spec fn lex_le(a: Seq<u32>, b: Seq<u32>) -> bool
    decreases a.len(),
{
    if a.len() == 0 {
        true
    } else if b.len() == 0 {
        false
    } else if a[0] != b[0] {
        a[0] < b[0]
    } else {
        lex_le(a.drop_first(), b.drop_first())
    }
}

/// どの二つも辞書式順序に並ぶ（前が後以下）。
pub open spec fn lex_sorted(s: Seq<Seq<u32>>) -> bool {
    forall|a: int, b: int| 0 <= a < b < s.len() ==> #[trigger] lex_le(s[a], s[b])
}

/// 隣り合う二つが異なる。
pub open spec fn adj_distinct(s: Seq<Seq<u32>>) -> bool {
    forall|k: int| 1 <= k < s.len() ==> #[trigger] s[k] != s[k - 1]
}

/// 鍵への参照の列が指す鍵の列。
pub open spec fn rkeys(s: Seq<&Vec<u32>>) -> Seq<Seq<u32>> {
    Seq::new(s.len(), |i: int| s[i]@)
}

pub proof fn lex_antisym(a: Seq<u32>, b: Seq<u32>)
    requires
        lex_le(a, b),
        lex_le(b, a),
    ensures
        a == b,
    decreases a.len(),
{
    if a.len() > 0 && b.len() > 0 {
        lex_antisym(a.drop_first(), b.drop_first());
        assert(a =~= seq![a[0]] + a.drop_first());
        assert(b =~= seq![b[0]] + b.drop_first());
    } else {
        assert(a =~= b);
    }
}

pub proof fn lex_trans(a: Seq<u32>, b: Seq<u32>, c: Seq<u32>)
    requires
        lex_le(a, b),
        lex_le(b, c),
    ensures
        lex_le(a, c),
    decreases a.len(),
{
    if a.len() > 0 && b.len() > 0 && c.len() > 0 && a[0] == b[0] && b[0] == c[0] {
        lex_trans(a.drop_first(), b.drop_first(), c.drop_first());
    }
}

pub proof fn lex_total(a: Seq<u32>, b: Seq<u32>)
    ensures
        lex_le(a, b) || lex_le(b, a),
    decreases a.len(),
{
    if a.len() > 0 && b.len() > 0 && a[0] == b[0] {
        lex_total(a.drop_first(), b.drop_first());
    }
}

// ------------------------------------------------------------------ 整列と相異

/// 並べ替え（多重集合が等しい）は、どの二つも異なることを保つ。
pub proof fn perm_distinct(s: Seq<Seq<u32>>, t: Seq<Seq<u32>>)
    requires
        t.to_multiset() == s.to_multiset(),
        distinct(s),
    ensures
        distinct(t),
{
    assert(s.no_duplicates());
    s.lemma_multiset_has_no_duplicates();
    t.lemma_multiset_has_no_duplicates_conv();
}

/// 整列した列 t が s の並べ替えなら、s のどの二つも異なることと、t の隣り合う二つが異なることは同じ。
pub proof fn sorted_perm_distinct(s: Seq<Seq<u32>>, t: Seq<Seq<u32>>)
    requires
        t.to_multiset() == s.to_multiset(),
        lex_sorted(t),
    ensures
        distinct(s) <==> adj_distinct(t),
{
    if distinct(s) {
        perm_distinct(s, t);
    }
    if adj_distinct(t) {
        // t[a] == t[b]（a < b）なら t[a] <= t[a + 1] <= t[b] == t[a] で、反対称より t[a] == t[a + 1]
        assert forall|a: int, b: int| 0 <= a < b < t.len() implies t[a] != t[b] by {
            if t[a] == t[b] {
                assert(t[a + 1] != t[a]);
                assert(lex_le(t[a], t[a + 1]));
                if a + 1 < b {
                    assert(lex_le(t[a + 1], t[b]));
                    lex_antisym(t[a], t[a + 1]);
                }
            }
        }
        perm_distinct(t, s);
    }
}

/// 整列した列 s のどれも x 以下なら、末尾に x を足しても整列している。
proof fn sorted_push(s: Seq<Seq<u32>>, x: Seq<u32>)
    requires
        lex_sorted(s),
        forall|p: int| 0 <= p < s.len() ==> #[trigger] lex_le(s[p], x),
    ensures
        lex_sorted(s.push(x)),
{
    assert forall|p: int, q: int| 0 <= p < q < s.push(x).len() implies #[trigger] lex_le(s.push(x)[p], s.push(x)[q]) by {
        if q < s.len() {
            assert(lex_le(s[p], s[q]));
        } else {
            assert(lex_le(s[p], x));
        }
    }
}

/// 列 s のどれも x 以下で、x が y 以下なら、s のどれも y 以下。
proof fn bound_trans(s: Seq<Seq<u32>>, x: Seq<u32>, y: Seq<u32>)
    requires
        forall|p: int| 0 <= p < s.len() ==> #[trigger] lex_le(s[p], x),
        lex_le(x, y),
    ensures
        forall|p: int| 0 <= p < s.len() ==> #[trigger] lex_le(s[p], y),
{
    assert forall|p: int| 0 <= p < s.len() implies #[trigger] lex_le(s[p], y) by {
        lex_trans(s[p], x, y);
    }
}

/// 列 s のどれも y 以下で、x も y 以下なら、末尾に x を足した列のどれも y 以下。
proof fn bound_push(s: Seq<Seq<u32>>, x: Seq<u32>, y: Seq<u32>)
    requires
        forall|p: int| 0 <= p < s.len() ==> #[trigger] lex_le(s[p], y),
        lex_le(x, y),
    ensures
        forall|p: int| 0 <= p < s.push(x).len() ==> #[trigger] lex_le(s.push(x)[p], y),
{
    assert forall|p: int| 0 <= p < s.push(x).len() implies #[trigger] lex_le(s.push(x)[p], y) by {
        if p < s.len() {
            assert(lex_le(s[p], y));
        }
    }
}

proof fn rkeys_push(s: Seq<&Vec<u32>>, x: &Vec<u32>)
    ensures
        rkeys(s.push(x)) == rkeys(s).push(x@),
{
    assert(rkeys(s.push(x)) =~= rkeys(s).push(x@));
}

// ------------------------------------------------------------------ 実行コード

/// a が b 以下（辞書式順序）か。
pub fn lex_le_e(a: &Vec<u32>, b: &Vec<u32>) -> (r: bool)
    ensures
        r == lex_le(a@, b@),
{
    let mut i: usize = 0;
    proof {
        assert(a@.subrange(0, a@.len() as int) =~= a@);
        assert(b@.subrange(0, b@.len() as int) =~= b@);
    }
    while i < a.len() && i < b.len() && a[i] == b[i]
        invariant
            i <= a.len(),
            i <= b.len(),
            lex_le(a@, b@) == lex_le(a@.subrange(i as int, a@.len() as int), b@.subrange(i as int, b@.len() as int)),
        decreases a.len() - i,
    {
        proof {
            let x = a@.subrange(i as int, a@.len() as int);
            let y = b@.subrange(i as int, b@.len() as int);
            assert(x.drop_first() =~= a@.subrange(i + 1, a@.len() as int));
            assert(y.drop_first() =~= b@.subrange(i + 1, b@.len() as int));
            assert(x[0] == y[0]);
        }
        i = i + 1;
    }
    proof {
        let x = a@.subrange(i as int, a@.len() as int);
        let y = b@.subrange(i as int, b@.len() as int);
        if i < a.len() && i < b.len() {
            assert(x[0] == a@[i as int]);
            assert(y[0] == b@[i as int]);
        }
    }
    if i == a.len() {
        true
    } else if i == b.len() {
        false
    } else {
        a[i] < b[i]
    }
}

/// 整列した二つの列を併合する。
fn merge_e<'a>(a: &Vec<&'a Vec<u32>>, b: &Vec<&'a Vec<u32>>) -> (r: Vec<&'a Vec<u32>>)
    requires
        lex_sorted(rkeys(a@)),
        lex_sorted(rkeys(b@)),
        a@.len() + b@.len() <= usize::MAX,
    ensures
        r@.len() == a@.len() + b@.len(),
        rkeys(r@).to_multiset() == rkeys(a@).to_multiset().add(rkeys(b@).to_multiset()),
        lex_sorted(rkeys(r@)),
{
    broadcast use vstd::multiset::group_multiset_axioms, vstd::multiset::group_multiset_properties;
    broadcast use group_to_multiset_ensures;

    let ghost ra = rkeys(a@);
    let ghost rb = rkeys(b@);
    let mut r: Vec<&'a Vec<u32>> = Vec::with_capacity(a.len() + b.len());
    let mut i: usize = 0;
    let mut j: usize = 0;
    proof {
        assert(rkeys(r@).len() == 0);
        assert(rkeys(r@).to_multiset() =~= ra.subrange(0, 0).to_multiset().add(rb.subrange(0, 0).to_multiset()));
    }
    while i < a.len() || j < b.len()
        invariant
            ra == rkeys(a@),
            rb == rkeys(b@),
            i <= a@.len(),
            j <= b@.len(),
            r@.len() == i + j,
            lex_sorted(ra),
            lex_sorted(rb),
            rkeys(r@).to_multiset() == ra.subrange(0, i as int).to_multiset().add(rb.subrange(0, j as int).to_multiset()),
            lex_sorted(rkeys(r@)),
            i < ra.len() ==> forall|p: int| 0 <= p < rkeys(r@).len() ==> #[trigger] lex_le(rkeys(r@)[p], ra[i as int]),
            j < rb.len() ==> forall|p: int| 0 <= p < rkeys(r@).len() ==> #[trigger] lex_le(rkeys(r@)[p], rb[j as int]),
        decreases a@.len() + b@.len() - i - j,
    {
        let ghost r0 = r@;
        let ghost s = rkeys(r0);
        if j >= b.len() || (i < a.len() && lex_le_e(a[i], b[j])) {
            let x = a[i];
            r.push(x);
            proof {
                let xk = ra[i as int];
                rkeys_push(r0, x);
                assert(rkeys(r@) == s.push(xk));
                assert(ra.subrange(0, i + 1) =~= ra.subrange(0, i as int).push(xk));
                to_multiset_build(s, xk);
                to_multiset_build(ra.subrange(0, i as int), xk);
                assert(rkeys(r@).to_multiset() =~= ra.subrange(0, i + 1).to_multiset().add(
                    rb.subrange(0, j as int).to_multiset(),
                ));
                sorted_push(s, xk);
                if i + 1 < ra.len() {
                    assert(lex_le(ra[i as int], ra[i + 1]));
                    bound_trans(s, xk, ra[i + 1]);
                    bound_push(s, xk, ra[i + 1]);
                }
                if j < rb.len() {
                    bound_push(s, xk, rb[j as int]);
                }
            }
            i = i + 1;
        } else {
            let y = b[j];
            r.push(y);
            proof {
                let yk = rb[j as int];
                if i < ra.len() {
                    lex_total(ra[i as int], yk);
                }
                rkeys_push(r0, y);
                assert(rkeys(r@) == s.push(yk));
                assert(rb.subrange(0, j + 1) =~= rb.subrange(0, j as int).push(yk));
                to_multiset_build(s, yk);
                to_multiset_build(rb.subrange(0, j as int), yk);
                assert(rkeys(r@).to_multiset() =~= ra.subrange(0, i as int).to_multiset().add(
                    rb.subrange(0, j + 1).to_multiset(),
                ));
                sorted_push(s, yk);
                if j + 1 < rb.len() {
                    assert(lex_le(rb[j as int], rb[j + 1]));
                    bound_trans(s, yk, rb[j + 1]);
                    bound_push(s, yk, rb[j + 1]);
                }
                if i < ra.len() {
                    bound_push(s, yk, ra[i as int]);
                }
            }
            j = j + 1;
        }
    }
    proof {
        assert(ra.subrange(0, ra.len() as int) =~= ra);
        assert(rb.subrange(0, rb.len() as int) =~= rb);
    }
    r
}

/// ks[lo..hi) の鍵を辞書式順序に整列した参照の列（併合整列）。
fn msort_e<'a>(ks: &'a Vec<Vec<u32>>, lo: usize, hi: usize) -> (r: Vec<&'a Vec<u32>>)
    requires
        lo <= hi <= ks@.len(),
    ensures
        r@.len() == hi - lo,
        rkeys(r@).to_multiset() == vks(ks@).subrange(lo as int, hi as int).to_multiset(),
        lex_sorted(rkeys(r@)),
    decreases hi - lo,
{
    if hi - lo <= 1 {
        let mut r: Vec<&'a Vec<u32>> = Vec::new();
        if hi - lo == 1 {
            r.push(&ks[lo]);
        }
        proof {
            assert(rkeys(r@) =~= vks(ks@).subrange(lo as int, hi as int));
        }
        return r;
    }
    let mid = lo + (hi - lo) / 2;
    let a = msort_e(ks, lo, mid);
    let b = msort_e(ks, mid, hi);
    proof {
        let s = vks(ks@);
        assert(s.subrange(lo as int, hi as int) =~= s.subrange(lo as int, mid as int) + s.subrange(mid as int, hi as int));
        lemma_multiset_commutative(s.subrange(lo as int, mid as int), s.subrange(mid as int, hi as int));
    }
    merge_e(&a, &b)
}

/// 鍵の列を辞書式順序に整列した、鍵への参照の列。入力の並べ替え（多重集合が等しい）で、整列している。
pub fn sort_keys_e<'a>(ks: &'a Vec<Vec<u32>>) -> (r: Vec<&'a Vec<u32>>)
    ensures
        rkeys(r@).to_multiset() == vks(ks@).to_multiset(),
        lex_sorted(rkeys(r@)),
{
    let r = msort_e(ks, 0, ks.len());
    proof {
        assert(vks(ks@).subrange(0, ks@.len() as int) =~= vks(ks@));
    }
    r
}

} // verus!
