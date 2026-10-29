//! v1.14 の再帰する直和型の書換えの計画（DECISION-43）。recursive.rs が、型の循環（自分に戻る型）を辺の表から決める部分を、
//! 検証済みの exec に替える。
//!
//! 辺の表（頂点は型の名前の番号、辺は宣言が書いた型の名前どうし）は recursive.rs の接着で作る（検証していない）。
//! ここで決めるのは `reach_e`：頂点 `src` から一本以上の辺をたどって届く頂点の印。spec は `reaches`（長さが二以上の道の端）。
//! 型 t が循環に入るかは `reach_e(adj, t)[t]` で決まり、spec では `reaches(adj, t, t)` になる。
//! 符号化（`List<Int>`）、match の書換え、型の展開は、この計画の外（接着のまま、検証していない）。

use vstd::prelude::*;

verus! {

/// 辺の表（行のベクタの並び）を、spec の列の列にする。
pub open spec fn rows(adj: Seq<Vec<bool>>) -> Seq<Seq<bool>> {
    Seq::new(adj.len(), |i: int| adj[i]@)
}

/// 辺の表は正方形（どの行も、行の数と同じ長さ）。
pub open spec fn square(adj: Seq<Seq<bool>>) -> bool {
    forall|i: int| 0 <= i < adj.len() ==> adj[i].len() == adj.len()
}

/// 道：頂点の並びで、頂点はすべて表の中、隣り合う組はすべて辺。
pub open spec fn walk_ok(adj: Seq<Seq<bool>>, v: Seq<nat>) -> bool {
    &&& v.len() >= 1
    &&& forall|t: int| 0 <= t < v.len() ==> v[t] < adj.len()
    &&& forall|t: int| 0 <= t < v.len() - 1 ==> adj[v[t] as int][v[t + 1] as int]
}

/// `src` から `k` へ、一本以上の辺をたどる道がある（長さ二以上の道で、始点が `src`、終点が `k`）。
pub open spec fn reaches(adj: Seq<Seq<bool>>, src: nat, k: nat) -> bool {
    exists|v: Seq<nat>| walk_ok(adj, v) && v.len() >= 2 && v[0] == src && v[v.len() - 1] == k
}

/// 印が `vis` の頂点の集まりは、辺で閉じている（`vis[j]` で `adj[j][k]` なら `vis[k]`）。
pub open spec fn closed(adj: Seq<Seq<bool>>, vis: Seq<bool>) -> bool {
    forall|j: int, k: int|
        0 <= j < adj.len() && 0 <= k < adj.len() && vis[j] && adj[j][k] ==> vis[k]
}

/// 印の数（true の個数）。
pub open spec fn count_true(s: Seq<bool>) -> nat
    decreases s.len(),
{
    if s.len() == 0 {
        0
    } else {
        count_true(s.drop_last()) + if s.last() { 1nat } else { 0nat }
    }
}

proof fn lemma_count_le(s: Seq<bool>)
    ensures
        count_true(s) <= s.len(),
    decreases s.len(),
{
    if s.len() > 0 {
        lemma_count_le(s.drop_last());
    }
}

/// 偽の一つを真にすると、真の数は一つ増える。
proof fn lemma_count_update(s: Seq<bool>, k: int)
    requires
        0 <= k < s.len(),
        !s[k],
    ensures
        count_true(s.update(k, true)) == count_true(s) + 1,
    decreases s.len(),
{
    let t = s.update(k, true);
    if k == s.len() - 1 {
        assert(t.drop_last() =~= s.drop_last());
        assert(t.last() == true);
        assert(!s.last());
    } else {
        lemma_count_update(s.drop_last(), k);
        assert(t.drop_last() =~= s.drop_last().update(k, true));
        assert(t.last() == s.last());
    }
}

/// 道の末尾に辺をたどって頂点を足すと、また道になる。
proof fn lemma_extend(adj: Seq<Seq<bool>>, src: nat, v: Seq<nat>, k: nat)
    requires
        walk_ok(adj, v),
        v.len() >= 2,
        v[0] == src,
        k < adj.len(),
        adj[v[v.len() - 1] as int][k as int],
    ensures
        reaches(adj, src, k),
{
    let w = v.push(k);
    assert forall|t: int| 0 <= t < w.len() implies w[t] < adj.len() by {
        if t < v.len() {
            assert(w[t] == v[t]);
        } else {
            assert(w[t] == k);
        }
    }
    assert forall|t: int| 0 <= t < w.len() - 1 implies adj[w[t] as int][w[t + 1] as int] by {
        assert(w[t] == v[t]);
        if t + 1 < v.len() {
            assert(w[t + 1] == v[t + 1]);
        } else {
            assert(w[t + 1] == k);
            assert(w[t] == v[v.len() - 1]);
        }
    }
    assert(w.len() >= 2 && w[0] == src && w[w.len() - 1] == k);
    assert(walk_ok(adj, w));
}

/// 辺で閉じていて、`src` の辺の先をすべて含む印は、`src` から長さ二以上の道で届く頂点をすべて含む（道の長さの帰納法）。
proof fn lemma_complete(adj: Seq<Seq<bool>>, src: nat, vis: Seq<bool>, v: Seq<nat>)
    requires
        square(adj),
        vis.len() == adj.len(),
        src < adj.len(),
        closed(adj, vis),
        forall|k: int| 0 <= k < adj.len() && adj[src as int][k] ==> vis[k],
        walk_ok(adj, v),
        v.len() >= 2,
        v[0] == src,
    ensures
        vis[v[v.len() - 1] as int],
    decreases v.len(),
{
    if v.len() == 2 {
        assert(adj[src as int][v[1] as int]);
        assert(vis[v[1] as int]);
    } else {
        let w = v.drop_last();
        assert(w.len() == v.len() - 1);
        assert(walk_ok(adj, w)) by {
            assert forall|t: int| 0 <= t < w.len() implies w[t] < adj.len() by {
                assert(w[t] == v[t]);
            }
            assert forall|t: int| 0 <= t < w.len() - 1 implies adj[w[t] as int][w[t + 1] as int] by {
                assert(w[t] == v[t]);
                assert(w[t + 1] == v[t + 1]);
            }
        }
        assert(w[0] == src);
        lemma_complete(adj, src, vis, w);
        assert(w[w.len() - 1] == v[v.len() - 2]);
        assert(adj[v[v.len() - 2] as int][v[v.len() - 1] as int]);
    }
}

/// 辺の表の行は、表の要素の列（`rows` の添字）と同じ。
proof fn lemma_rows_eq(adj: Seq<Vec<bool>>, i: int)
    requires
        0 <= i < adj.len(),
    ensures
        rows(adj)[i] == adj[i]@,
{}

/// 辺の表が正方形なら、添字で取った行は表の行の数と同じ長さ。
proof fn lemma_row_len(adj: Seq<Vec<bool>>, i: int)
    requires
        square(rows(adj)),
        0 <= i < adj.len(),
    ensures
        adj[i]@.len() == adj.len(),
{
    lemma_rows_eq(adj, i);
    assert(rows(adj)[i].len() == rows(adj).len());
}

/// `src` から一本以上の辺をたどって届く頂点の印（`reaches` と同じ）。
pub fn reach_e(adj: &Vec<Vec<bool>>, src: usize) -> (r: Vec<bool>)
    requires
        src < adj.len(),
        square(rows(adj@)),
    ensures
        r@.len() == adj@.len(),
        forall|k: nat| k < adj@.len() ==> r@[k as int] == reaches(rows(adj@), src as nat, k),
{
    let n = adj.len();
    proof {
        lemma_row_len(adj@, src as int);
        lemma_rows_eq(adj@, src as int);
    }
    // 初めの印は、`src` の辺の先
    let mut vis: Vec<bool> = Vec::new();
    let mut k: usize = 0;
    while k < n
        invariant
            k <= n,
            n == adj@.len(),
            src < n,
            square(rows(adj@)),
            adj@[src as int]@.len() == n,
            vis@.len() == k,
            forall|j: int| 0 <= j < k ==> vis@[j] == rows(adj@)[src as int][j],
        decreases n - k,
    {
        vis.push(adj[src][k]);
        k += 1;
    }
    proof {
        lemma_count_le(vis@);
        assert forall|j: int| 0 <= j < n && vis@[j] implies reaches(rows(adj@), src as nat, j as nat) by {
            let w = seq![src as nat, j as nat];
            assert(walk_ok(rows(adj@), w));
        }
    }
    // 一回の掃き出しで印が増えたら、もう一回。増えなければ、印は辺で閉じている。
    let mut changed = true;
    while changed
        invariant
            n == adj@.len(),
            vis@.len() == n,
            square(rows(adj@)),
            src < n,
            adj@[src as int]@.len() == n,
            forall|j: int| 0 <= j < n && vis@[j] ==> reaches(rows(adj@), src as nat, j as nat),
            forall|j: int| 0 <= j < n && rows(adj@)[src as int][j] ==> vis@[j],
            count_true(vis@) <= n,
            !changed ==> closed(rows(adj@), vis@),
        decreases 2 * ((n as int) - (count_true(vis@) as int)) + if changed { 1int } else { 0int },
    {
        let ghost before = count_true(vis@);
        changed = false;
        let mut j: usize = 0;
        while j < n
            invariant
                n == adj@.len(),
                vis@.len() == n,
                square(rows(adj@)),
                src < n,
                adj@[src as int]@.len() == n,
                j <= n,
                forall|a: int| 0 <= a < n && vis@[a] ==> reaches(rows(adj@), src as nat, a as nat),
                forall|a: int| 0 <= a < n && rows(adj@)[src as int][a] ==> vis@[a],
                count_true(vis@) <= n,
                changed ==> count_true(vis@) > before,
                !changed ==> count_true(vis@) == before,
                !changed ==> forall|a: int, b: int|
                    0 <= a < j && 0 <= b < n && vis@[a] && rows(adj@)[a][b] ==> vis@[b],
            decreases n - j,
        {
            proof {
                lemma_row_len(adj@, j as int);
                lemma_rows_eq(adj@, j as int);
            }
            if vis[j] {
                let mut k: usize = 0;
                while k < n
                    invariant
                        n == adj@.len(),
                        vis@.len() == n,
                        square(rows(adj@)),
                        src < n,
                        adj@[src as int]@.len() == n,
                        adj@[j as int]@.len() == n,
                        j < n,
                        k <= n,
                        vis@[j as int],
                        forall|a: int| 0 <= a < n && vis@[a] ==> reaches(rows(adj@), src as nat, a as nat),
                        forall|a: int| 0 <= a < n && rows(adj@)[src as int][a] ==> vis@[a],
                        count_true(vis@) <= n,
                        changed ==> count_true(vis@) > before,
                        !changed ==> count_true(vis@) == before,
                        !changed ==> forall|a: int, b: int|
                            0 <= a < j && 0 <= b < n && vis@[a] && rows(adj@)[a][b] ==> vis@[b],
                        !changed ==> forall|b: int|
                            0 <= b < k && rows(adj@)[j as int][b] ==> vis@[b],
                    decreases n - k,
                {
                    if adj[j][k] && !vis[k] {
                        proof {
                            // 印の先の頂点は、`src` から届く道に、辺を一本足したもの
                            assert(reaches(rows(adj@), src as nat, j as nat));
                            let w = choose|w: Seq<nat>| walk_ok(rows(adj@), w) && w.len() >= 2 && w[0] == src as nat && w[w.len() - 1] == j as nat;
                            lemma_extend(rows(adj@), src as nat, w, k as nat);
                            lemma_count_update(vis@, k as int);
                            lemma_count_le(vis@.update(k as int, true));
                        }
                        vis[k] = true;
                        changed = true;
                    }
                    k += 1;
                }
            }
            j += 1;
        }
        proof {
            assert(!changed ==> closed(rows(adj@), vis@));
        }
    }
    proof {
        lemma_count_le(vis@);
        assert forall|k: nat| k < n implies (vis@[k as int] == reaches(rows(adj@), src as nat, k)) by {
            if reaches(rows(adj@), src as nat, k) {
                let v = choose|v: Seq<nat>| walk_ok(rows(adj@), v) && v.len() >= 2 && v[0] == src as nat && v[v.len() - 1] == k;
                lemma_complete(rows(adj@), src as nat, vis@, v);
            }
        }
    }
    vis
}

} // verus!
