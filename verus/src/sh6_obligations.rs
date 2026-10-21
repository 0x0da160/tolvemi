//! SH6：hof の形ごとの仮定の証明（段階 1b）。
//!
//! simulation.rs の模擬（SH4）は、hof の形ごとの意味（`ob_map` から `ob_sort_by`）を名前つきの仮定として受け取る。
//! ここでは書換えの形を構文の仮定 `hof_shapes` に書き、そこから各仮定を示す。
//!
//! `hof_shapes(rw)`：hof の形の写しは、子の写しから作った畳み込みの形になる（crates/tlvm/src/hof.rs の lower と同じ形。
//! fold_meaning.rs の map_collect・filter_collect・any_fold・all_fold・find_fold と、sortmeaning.rs の sort_collect）。
//! 導入する名前（acc など）は要素の名前 x と違い、本体の写しに現れない（absent。SH5 の新しさ。hof.rs の fresh は
//! プログラムの名前とそれまでに割り当てた名前を避ける）。空の列と None の型の注釈は評価が読まないので、存在で書く。
//! 意味の証明は fold_meaning.rs・sortmeaning.rs の定理（collect_map・filter_meaning・any_meaning・all_meaning・
//! find_meaning・sort_core_meaning）を使う。

use crate::bigstep::*;
use crate::fold_meaning::*;
use crate::proof::*;
use crate::records_proof::*;
use crate::simulation::*;
use crate::sortmeaning::*;
use crate::sortspec::*;
use crate::spec::*;
use crate::xmeaning::*;
use crate::xsem::*;
use vstd::prelude::*;

verus! {

// ------------------------------------------------------------------ 書換えの形（構文の仮定）

/// map の写し：`reverse(fold(rw(xs), [], |acc, x| cons(rw(c), acc)))`。
pub open spec fn map_form(rw: spec_fn(XExpr) -> Expr, xs: XExpr, x: nat, c: XExpr) -> bool {
    exists|t: Ty, acc: nat|
        #![trigger map_collect(rw(xs), t, acc, x, rw(c))]
        acc != x && absent(acc, rw(c)) && rw(XExpr::Map(Box::new(xs), x, Box::new(c))) == map_collect(
            rw(xs),
            t,
            acc,
            x,
            rw(c),
        )
}

/// filter の写し：`reverse(fold(rw(xs), [], |acc, x| if rw(c) then cons(x, acc) else acc))`。
pub open spec fn filter_form(rw: spec_fn(XExpr) -> Expr, xs: XExpr, x: nat, c: XExpr) -> bool {
    exists|t: Ty, acc: nat|
        #![trigger filter_collect(rw(xs), t, acc, x, rw(c))]
        acc != x && absent(acc, rw(c)) && rw(XExpr::Filter(Box::new(xs), x, Box::new(c))) == filter_collect(
            rw(xs),
            t,
            acc,
            x,
            rw(c),
        )
}

/// any の写し：`fold(rw(xs), false, |acc, x| if acc then true else rw(c))`。
pub open spec fn any_form(rw: spec_fn(XExpr) -> Expr, xs: XExpr, x: nat, c: XExpr) -> bool {
    exists|acc: nat|
        #![trigger any_fold(rw(xs), acc, x, rw(c))]
        acc != x && absent(acc, rw(c)) && rw(XExpr::Any(Box::new(xs), x, Box::new(c))) == any_fold(rw(xs), acc, x, rw(c))
}

/// all の写し：`fold(rw(xs), true, |acc, x| if acc then rw(c) else false)`。
pub open spec fn all_form(rw: spec_fn(XExpr) -> Expr, xs: XExpr, x: nat, c: XExpr) -> bool {
    exists|acc: nat|
        #![trigger all_fold(rw(xs), acc, x, rw(c))]
        acc != x && absent(acc, rw(c)) && rw(XExpr::All(Box::new(xs), x, Box::new(c))) == all_fold(rw(xs), acc, x, rw(c))
}

/// find の写し：`fold(rw(xs), None, |acc, x| match acc { None => if rw(c) then Some(x) else None, Some(y) => Some(y) })`。
pub open spec fn find_form(rw: spec_fn(XExpr) -> Expr, xs: XExpr, x: nat, c: XExpr) -> bool {
    exists|t: Ty, acc: nat, y: nat|
        #![trigger find_fold(rw(xs), t, acc, x, rw(c), y)]
        acc != x && absent(acc, rw(c)) && rw(XExpr::Find(Box::new(xs), x, Box::new(c))) == find_fold(
            rw(xs),
            t,
            acc,
            x,
            rw(c),
            y,
        )
}

/// sort_by の写し：sort_collect（外側の fold で要素 e を取り、内側の fold で整列済みの列へ挿入する）。
/// 導入する名前 acc・e・st・y・ky・ke・rb は互いに違い（names_ok）、acc・e・st・y は鍵の写しに現れない。
pub open spec fn sort_form(rw: spec_fn(XExpr) -> Expr, xs: XExpr, x: nat, k: XExpr) -> bool {
    exists|t: Ty, acc: nat, e: nat, st: nat, y: nat, ky: nat, ke: nat, rb: nat|
        #![trigger sort_collect(rw(xs), t, acc, e, st, y, ky, ke, rb, x, rw(k))]
        names_ok(acc, e, st, y, ky, ke, rb, x) && absent(acc, rw(k)) && absent(e, rw(k)) && absent(st, rw(k))
            && absent(y, rw(k)) && rw(XExpr::SortBy(Box::new(xs), x, Box::new(k))) == sort_collect(
            rw(xs),
            t,
            acc,
            e,
            st,
            y,
            ky,
            ke,
            rb,
            x,
            rw(k),
        )
}

/// 書換えの形の仮定（hof.rs の lower の形と、導入する名前の新しさ）。SH6 の ob はすべてこれから示す。
pub open spec fn hof_shapes(rw: spec_fn(XExpr) -> Expr) -> bool {
    &&& forall|xs: XExpr, x: nat, c: XExpr| #[trigger] map_form(rw, xs, x, c)
    &&& forall|xs: XExpr, x: nat, c: XExpr| #[trigger] filter_form(rw, xs, x, c)
    &&& forall|xs: XExpr, x: nat, c: XExpr| #[trigger] any_form(rw, xs, x, c)
    &&& forall|xs: XExpr, x: nat, c: XExpr| #[trigger] all_form(rw, xs, x, c)
    &&& forall|xs: XExpr, x: nat, c: XExpr| #[trigger] find_form(rw, xs, x, c)
    &&& forall|xs: XExpr, x: nat, k: XExpr| #[trigger] sort_form(rw, xs, x, k)
}

// ------------------------------------------------------------------ 形の名前の取り出し

pub proof fn map_names(rw: spec_fn(XExpr) -> Expr, xs: XExpr, x: nat, c: XExpr) -> (r: (Ty, nat))
    requires
        hof_shapes(rw),
    ensures
        r.1 != x,
        absent(r.1, rw(c)),
        rw(XExpr::Map(Box::new(xs), x, Box::new(c))) == map_collect(rw(xs), r.0, r.1, x, rw(c)),
{
    assert(map_form(rw, xs, x, c));
    let (t, acc) = choose|t: Ty, acc: nat|
        #![trigger map_collect(rw(xs), t, acc, x, rw(c))]
        acc != x && absent(acc, rw(c)) && rw(XExpr::Map(Box::new(xs), x, Box::new(c))) == map_collect(
            rw(xs),
            t,
            acc,
            x,
            rw(c),
        );
    (t, acc)
}

pub proof fn filter_names(rw: spec_fn(XExpr) -> Expr, xs: XExpr, x: nat, c: XExpr) -> (r: (Ty, nat))
    requires
        hof_shapes(rw),
    ensures
        r.1 != x,
        absent(r.1, rw(c)),
        rw(XExpr::Filter(Box::new(xs), x, Box::new(c))) == filter_collect(rw(xs), r.0, r.1, x, rw(c)),
{
    assert(filter_form(rw, xs, x, c));
    let (t, acc) = choose|t: Ty, acc: nat|
        #![trigger filter_collect(rw(xs), t, acc, x, rw(c))]
        acc != x && absent(acc, rw(c)) && rw(XExpr::Filter(Box::new(xs), x, Box::new(c))) == filter_collect(
            rw(xs),
            t,
            acc,
            x,
            rw(c),
        );
    (t, acc)
}

pub proof fn any_names(rw: spec_fn(XExpr) -> Expr, xs: XExpr, x: nat, c: XExpr) -> (acc: nat)
    requires
        hof_shapes(rw),
    ensures
        acc != x,
        absent(acc, rw(c)),
        rw(XExpr::Any(Box::new(xs), x, Box::new(c))) == any_fold(rw(xs), acc, x, rw(c)),
{
    assert(any_form(rw, xs, x, c));
    choose|acc: nat|
        #![trigger any_fold(rw(xs), acc, x, rw(c))]
        acc != x && absent(acc, rw(c)) && rw(XExpr::Any(Box::new(xs), x, Box::new(c))) == any_fold(rw(xs), acc, x, rw(c))
}

pub proof fn all_names(rw: spec_fn(XExpr) -> Expr, xs: XExpr, x: nat, c: XExpr) -> (acc: nat)
    requires
        hof_shapes(rw),
    ensures
        acc != x,
        absent(acc, rw(c)),
        rw(XExpr::All(Box::new(xs), x, Box::new(c))) == all_fold(rw(xs), acc, x, rw(c)),
{
    assert(all_form(rw, xs, x, c));
    choose|acc: nat|
        #![trigger all_fold(rw(xs), acc, x, rw(c))]
        acc != x && absent(acc, rw(c)) && rw(XExpr::All(Box::new(xs), x, Box::new(c))) == all_fold(rw(xs), acc, x, rw(c))
}

pub proof fn find_names(rw: spec_fn(XExpr) -> Expr, xs: XExpr, x: nat, c: XExpr) -> (r: (Ty, nat, nat))
    requires
        hof_shapes(rw),
    ensures
        r.1 != x,
        absent(r.1, rw(c)),
        rw(XExpr::Find(Box::new(xs), x, Box::new(c))) == find_fold(rw(xs), r.0, r.1, x, rw(c), r.2),
{
    assert(find_form(rw, xs, x, c));
    let (t, acc, y) = choose|t: Ty, acc: nat, y: nat|
        #![trigger find_fold(rw(xs), t, acc, x, rw(c), y)]
        acc != x && absent(acc, rw(c)) && rw(XExpr::Find(Box::new(xs), x, Box::new(c))) == find_fold(
            rw(xs),
            t,
            acc,
            x,
            rw(c),
            y,
        );
    (t, acc, y)
}

/// sort_by の形の名前：(t, acc, e, st, y, ky, ke, rb)。
pub proof fn sort_names(rw: spec_fn(XExpr) -> Expr, xs: XExpr, x: nat, k: XExpr) -> (r: (
    Ty,
    nat,
    nat,
    nat,
    nat,
    nat,
    nat,
    nat,
))
    requires
        hof_shapes(rw),
    ensures
        names_ok(r.1, r.2, r.3, r.4, r.5, r.6, r.7, x),
        absent(r.1, rw(k)),
        absent(r.2, rw(k)),
        absent(r.3, rw(k)),
        absent(r.4, rw(k)),
        rw(XExpr::SortBy(Box::new(xs), x, Box::new(k))) == sort_collect(
            rw(xs),
            r.0,
            r.1,
            r.2,
            r.3,
            r.4,
            r.5,
            r.6,
            r.7,
            x,
            rw(k),
        ),
{
    assert(sort_form(rw, xs, x, k));
    let (t, acc, e, st, y, ky, ke, rb) = choose|t: Ty, acc: nat, e: nat, st: nat, y: nat, ky: nat, ke: nat, rb: nat|
        #![trigger sort_collect(rw(xs), t, acc, e, st, y, ky, ke, rb, x, rw(k))]
        names_ok(acc, e, st, y, ky, ke, rb, x) && absent(acc, rw(k)) && absent(e, rw(k)) && absent(st, rw(k))
            && absent(y, rw(k)) && rw(XExpr::SortBy(Box::new(xs), x, Box::new(k))) == sort_collect(
            rw(xs),
            t,
            acc,
            e,
            st,
            y,
            ky,
            ke,
            rb,
            x,
            rw(k),
        );
    (t, acc, e, st, y, ky, ke, rb)
}

// ------------------------------------------------------------------ 列の補題

/// 要素 stop だけ真の列（stop が長さ以上なら、どこも真でない）。
pub open spec fn mark(n: nat, stop: nat) -> Seq<bool> {
    Seq::new(n, |k: int| k == stop as int)
}

/// 要素 stop だけ偽の列。
pub open spec fn unmark(n: nat, stop: nat) -> Seq<bool> {
    Seq::new(n, |k: int| k != stop as int)
}

/// 先頭 k 個に真があるのは、stop < k のとき。
pub proof fn any_k_mark(n: nat, stop: nat, k: nat)
    requires
        k <= n,
    ensures
        any_k(mark(n, stop), k) == (stop < k),
    decreases k,
{
    reveal_with_fuel(any_k, 1);
    if k > 0 {
        any_k_mark(n, stop, (k - 1) as nat);
        assert(mark(n, stop)[k - 1] == ((k - 1) as int == stop as int));
    }
}

/// 先頭 k 個がすべて真なのは、k <= stop のとき。
pub proof fn all_k_unmark(n: nat, stop: nat, k: nat)
    requires
        k <= n,
    ensures
        all_k(unmark(n, stop), k) == (k <= stop),
    decreases k,
{
    reveal_with_fuel(all_k, 1);
    if k > 0 {
        all_k_unmark(n, stop, (k - 1) as nat);
        assert(unmark(n, stop)[k - 1] == ((k - 1) as int != stop as int));
    }
}

/// 先頭 k 個で最初に選ばれるのは、stop < k なら要素 stop、そうでなければ無い。
pub proof fn first_k_mark(items: Seq<Val>, stop: nat, k: nat)
    requires
        k <= items.len(),
    ensures
        first_k(items, mark(items.len() as nat, stop), k) == (if stop < k {
            Val::Some(Box::new(items[stop as int]))
        } else {
            Val::None
        }),
    decreases k,
{
    reveal_with_fuel(first_k, 1);
    if k > 0 {
        first_k_mark(items, stop, (k - 1) as nat);
        assert(mark(items.len() as nat, stop)[k - 1] == ((k - 1) as int == stop as int));
    }
}

/// 先頭 kept(j) と残り kept_from(j) を合わせると、全体の kept(n) になる（xmeaning.rs の kept_split と同じ）。
pub proof fn kept_from_split(items: Seq<Val>, keep: Seq<bool>, j: nat)
    requires
        keep.len() == items.len(),
        j <= items.len(),
    ensures
        kept(items, keep, j) + kept_from(items, keep, j) == kept(items, keep, items.len() as nat),
    decreases items.len() - j,
{
    reveal_with_fuel(kept, 1);
    reveal_with_fuel(kept_from, 1);
    if j < items.len() {
        kept_from_split(items, keep, j + 1);
        if keep[j as int] {
            assert(kept(items, keep, j + 1) =~= kept(items, keep, j) + seq![items[j as int]]);
            assert(kept_from(items, keep, j) =~= seq![items[j as int]] + kept_from(items, keep, j + 1));
        } else {
            assert(kept(items, keep, j + 1) =~= kept(items, keep, j));
            assert(kept_from(items, keep, j) =~= kept_from(items, keep, j + 1));
        }
        assert(kept(items, keep, j) + kept_from(items, keep, j) =~= kept(items, keep, j + 1) + kept_from(
            items,
            keep,
            j + 1,
        ));
    } else {
        assert(kept_from(items, keep, j) =~= Seq::<Val>::empty());
        assert(kept(items, keep, j) + Seq::<Val>::empty() =~= kept(items, keep, j));
    }
}

/// kept_from(0) は全体の kept(n) に等しい。
pub proof fn kept_from_all(items: Seq<Val>, keep: Seq<bool>)
    requires
        keep.len() == items.len(),
    ensures
        kept_from(items, keep, 0) == kept(items, keep, items.len() as nat),
{
    reveal_with_fuel(kept, 1);
    kept_from_split(items, keep, 0);
    assert(kept(items, keep, 0) =~= Seq::<Val>::empty());
    assert(Seq::<Val>::empty() + kept_from(items, keep, 0) =~= kept_from(items, keep, 0));
}

/// int_seq の結果は、各値の整数を並べた列。
pub proof fn int_seq_vals(kv: Seq<Val>, keys: Seq<int>)
    requires
        int_seq(kv) == Some(keys),
    ensures
        keys.len() == kv.len(),
        forall|i: int| 0 <= i < kv.len() ==> kv[i] == Val::Int(#[trigger] keys[i]),
{
    assert(forall|i: int| 0 <= i < kv.len() ==> int_of_val(#[trigger] kv[i]) is Some);
    assert(keys == Seq::new(kv.len(), |i: int| int_of_val(kv[i])->Some_0));
    assert forall|i: int| 0 <= i < kv.len() implies kv[i] == Val::Int(#[trigger] keys[i]) by {
        assert(int_of_val(kv[i]) is Some);
    }
}

// ------------------------------------------------------------------ 形ごとの意味（Done）

/// map：列が items に、各要素の本体の写しが vs[k] に評価されれば、写しの map は List(vs) に評価される。
pub proof fn map_done(
    p: Prog,
    rw: spec_fn(XExpr) -> Expr,
    env: Map<nat, Val>,
    xs: XExpr,
    x: nat,
    c: XExpr,
    items: Seq<Val>,
    vs: Seq<Val>,
)
    requires
        hof_shapes(rw),
        evals_to(p, env, rw(xs), Val::List(items)),
        map_ok(p, rw, env, x, c, items, vs, 0),
    ensures
        evals_to(p, env, rw(XExpr::Map(Box::new(xs), x, Box::new(c))), Val::List(vs)),
{
    let (t, acc) = map_names(rw, xs, x, c);
    assert forall|k: int| 0 <= k < items.len() implies evals_to(p, #[trigger] env.insert(x, items[k]), rw(c), vs[k]) by {
        assert(evals_to(p, env.insert(x, items[k]), rw(c), vs[k - (0nat as int)]));
    }
    collect_map(p, env, rw(xs), t, acc, x, rw(c), items, vs);
}

/// filter：各要素の述語の写しが Bool(keep[k]) に評価されれば、写しの filter は kept_from(0) に評価される。
pub proof fn filter_done(
    p: Prog,
    rw: spec_fn(XExpr) -> Expr,
    env: Map<nat, Val>,
    xs: XExpr,
    x: nat,
    c: XExpr,
    items: Seq<Val>,
    keep: Seq<bool>,
    out: Seq<Val>,
)
    requires
        hof_shapes(rw),
        evals_to(p, env, rw(xs), Val::List(items)),
        filter_keep(p, rw, env, x, c, items, keep, out, 0),
    ensures
        evals_to(p, env, rw(XExpr::Filter(Box::new(xs), x, Box::new(c))), Val::List(out)),
{
    let (t, acc) = filter_names(rw, xs, x, c);
    assert forall|k: int| 0 <= k < items.len() implies evals_to(
        p,
        #[trigger] env.insert(x, items[k]),
        rw(c),
        Val::Bool(keep[k]),
    ) by {}
    filter_meaning(p, env, rw(xs), t, acc, x, rw(c), items, keep);
    kept_from_all(items, keep);
}

/// any：stop より前の述語が偽、stop の述語が真（stop が長さなら無い）なら、写しの any は Bool(stop < 長さ)。
pub proof fn any_done(
    p: Prog,
    rw: spec_fn(XExpr) -> Expr,
    env: Map<nat, Val>,
    xs: XExpr,
    x: nat,
    c: XExpr,
    items: Seq<Val>,
    stop: nat,
    out: Val,
)
    requires
        hof_shapes(rw),
        evals_to(p, env, rw(xs), Val::List(items)),
        any_stop(p, rw, env, x, c, items, 0, stop, out),
    ensures
        evals_to(p, env, rw(XExpr::Any(Box::new(xs), x, Box::new(c))), out),
{
    let acc = any_names(rw, xs, x, c);
    let n = items.len() as nat;
    let keep = mark(n, stop);
    assert forall|k: int| 0 <= k < items.len() && !any_k(keep, k as nat) implies evals_to(
        p,
        #[trigger] env.insert(x, items[k]),
        rw(c),
        Val::Bool(keep[k]),
    ) by {
        any_k_mark(n, stop, k as nat);
        if k < stop as int {
            assert(keep[k] == false);
        } else {
            assert(k == stop as int);
            assert(keep[k] == true);
        }
    }
    any_meaning(p, env, rw(xs), acc, x, rw(c), items, keep);
    any_k_mark(n, stop, n);
}

/// all：stop より前の述語が真、stop の述語が偽（stop が長さなら無い）なら、写しの all は Bool(stop == 長さ)。
pub proof fn all_done(
    p: Prog,
    rw: spec_fn(XExpr) -> Expr,
    env: Map<nat, Val>,
    xs: XExpr,
    x: nat,
    c: XExpr,
    items: Seq<Val>,
    stop: nat,
    out: Val,
)
    requires
        hof_shapes(rw),
        evals_to(p, env, rw(xs), Val::List(items)),
        all_stop(p, rw, env, x, c, items, 0, stop, out),
    ensures
        evals_to(p, env, rw(XExpr::All(Box::new(xs), x, Box::new(c))), out),
{
    let acc = all_names(rw, xs, x, c);
    let n = items.len() as nat;
    let keep = unmark(n, stop);
    assert forall|k: int| 0 <= k < items.len() && all_k(keep, k as nat) implies evals_to(
        p,
        #[trigger] env.insert(x, items[k]),
        rw(c),
        Val::Bool(keep[k]),
    ) by {
        all_k_unmark(n, stop, k as nat);
        if k < stop as int {
            assert(keep[k] == true);
        } else {
            assert(k == stop as int);
            assert(keep[k] == false);
        }
    }
    all_meaning(p, env, rw(xs), acc, x, rw(c), items, keep);
    all_k_unmark(n, stop, n);
}

/// find：stop より前の述語が偽、stop の述語が真なら、写しの find は Some(items[stop])（stop が長さなら None）。
pub proof fn find_done(
    p: Prog,
    rw: spec_fn(XExpr) -> Expr,
    env: Map<nat, Val>,
    xs: XExpr,
    x: nat,
    c: XExpr,
    items: Seq<Val>,
    stop: nat,
    out: Val,
)
    requires
        hof_shapes(rw),
        evals_to(p, env, rw(xs), Val::List(items)),
        find_stop(p, rw, env, x, c, items, 0, stop, out),
    ensures
        evals_to(p, env, rw(XExpr::Find(Box::new(xs), x, Box::new(c))), out),
{
    let (t, acc, y) = find_names(rw, xs, x, c);
    let n = items.len() as nat;
    let keep = mark(n, stop);
    assert forall|k: int| 0 <= k < items.len() && first_k(items, keep, k as nat) is None implies evals_to(
        p,
        #[trigger] env.insert(x, items[k]),
        rw(c),
        Val::Bool(keep[k]),
    ) by {
        first_k_mark(items, stop, k as nat);
        if k < stop as int {
            assert(keep[k] == false);
        } else {
            assert(k == stop as int);
            assert(keep[k] == true);
        }
    }
    find_meaning(p, env, rw(xs), t, acc, x, y, rw(c), items, keep);
    first_k_mark(items, stop, n);
}

/// sort_by：各要素の鍵の写しが kv[k] に評価され、kv が整数の列 keys なら、写しの sort_by は sort_vals(items, keys)。
pub proof fn sort_done(
    p: Prog,
    rw: spec_fn(XExpr) -> Expr,
    env: Map<nat, Val>,
    xs: XExpr,
    x: nat,
    k: XExpr,
    items: Seq<Val>,
    kv: Seq<Val>,
    keys: Seq<int>,
)
    requires
        hof_shapes(rw),
        evals_to(p, env, rw(xs), Val::List(items)),
        map_ok(p, rw, env, x, k, items, kv, 0),
        int_seq(kv) == Some(keys),
    ensures
        evals_to(p, env, rw(XExpr::SortBy(Box::new(xs), x, Box::new(k))), Val::List(sort_vals(items, keys))),
{
    let (t, acc, e, st, y, ky, ke, rb) = sort_names(rw, xs, x, k);
    int_seq_vals(kv, keys);
    let zp = zip_keys(items, keys);
    assert forall|m: int| 0 <= m < zp.len() implies evals_to(
        p,
        #[trigger] env.insert(x, zp[m].0),
        rw(k),
        Val::Int(zp[m].1),
    ) by {
        assert(zp[m].0 == items[m]);
        assert(zp[m].1 == keys[m]);
        assert(evals_to(p, env.insert(x, items[m]), rw(k), kv[m - (0nat as int)]));
        assert(kv[m] == Val::Int(keys[m]));
    }
    assert(keyed(p, env, x, rw(k), zp));
    sort_core_meaning(p, env, rw(xs), t, acc, e, st, y, ky, ke, rb, x, rw(k), items, keys);
}

// ------------------------------------------------------------------ 意味の仮定（ob_map から ob_sort_by）の証明

pub proof fn ob_map_holds(p: Prog, rw: spec_fn(XExpr) -> Expr)
    requires
        hof_shapes(rw),
    ensures
        ob_map(p, rw),
{
    assert forall|env: Map<nat, Val>, xs: XExpr, x: nat, c: XExpr, items: Seq<Val>, vs: Seq<Val>|
        #![trigger evals_to(p, env, rw(XExpr::Map(Box::new(xs), x, Box::new(c))), Val::List(vs)), map_ok(p, rw, env, x, c, items, vs, 0)]
        evals_to(p, env, rw(xs), Val::List(items)) && map_ok(p, rw, env, x, c, items, vs, 0) implies evals_to(
            p,
            env,
            rw(XExpr::Map(Box::new(xs), x, Box::new(c))),
            Val::List(vs),
        ) by {
        map_done(p, rw, env, xs, x, c, items, vs);
    }
}

pub proof fn ob_filter_holds(p: Prog, rw: spec_fn(XExpr) -> Expr)
    requires
        hof_shapes(rw),
    ensures
        ob_filter(p, rw),
{
    assert forall|env: Map<nat, Val>, xs: XExpr, x: nat, c: XExpr, items: Seq<Val>, keep: Seq<bool>, out: Seq<Val>|
        #![trigger evals_to(p, env, rw(XExpr::Filter(Box::new(xs), x, Box::new(c))), Val::List(out)), filter_keep(p, rw, env, x, c, items, keep, out, 0)]
        evals_to(p, env, rw(xs), Val::List(items)) && filter_keep(p, rw, env, x, c, items, keep, out, 0) implies evals_to(
            p,
            env,
            rw(XExpr::Filter(Box::new(xs), x, Box::new(c))),
            Val::List(out),
        ) by {
        filter_done(p, rw, env, xs, x, c, items, keep, out);
    }
}

pub proof fn ob_any_holds(p: Prog, rw: spec_fn(XExpr) -> Expr)
    requires
        hof_shapes(rw),
    ensures
        ob_any(p, rw),
{
    assert forall|env: Map<nat, Val>, xs: XExpr, x: nat, c: XExpr, items: Seq<Val>, stop: nat, out: Val|
        #![trigger evals_to(p, env, rw(XExpr::Any(Box::new(xs), x, Box::new(c))), out), any_stop(p, rw, env, x, c, items, 0, stop, out)]
        evals_to(p, env, rw(xs), Val::List(items)) && any_stop(p, rw, env, x, c, items, 0, stop, out) implies evals_to(
            p,
            env,
            rw(XExpr::Any(Box::new(xs), x, Box::new(c))),
            out,
        ) by {
        any_done(p, rw, env, xs, x, c, items, stop, out);
    }
}

pub proof fn ob_all_holds(p: Prog, rw: spec_fn(XExpr) -> Expr)
    requires
        hof_shapes(rw),
    ensures
        ob_all(p, rw),
{
    assert forall|env: Map<nat, Val>, xs: XExpr, x: nat, c: XExpr, items: Seq<Val>, stop: nat, out: Val|
        #![trigger evals_to(p, env, rw(XExpr::All(Box::new(xs), x, Box::new(c))), out), all_stop(p, rw, env, x, c, items, 0, stop, out)]
        evals_to(p, env, rw(xs), Val::List(items)) && all_stop(p, rw, env, x, c, items, 0, stop, out) implies evals_to(
            p,
            env,
            rw(XExpr::All(Box::new(xs), x, Box::new(c))),
            out,
        ) by {
        all_done(p, rw, env, xs, x, c, items, stop, out);
    }
}

pub proof fn ob_find_holds(p: Prog, rw: spec_fn(XExpr) -> Expr)
    requires
        hof_shapes(rw),
    ensures
        ob_find(p, rw),
{
    assert forall|env: Map<nat, Val>, xs: XExpr, x: nat, c: XExpr, items: Seq<Val>, stop: nat, out: Val|
        #![trigger evals_to(p, env, rw(XExpr::Find(Box::new(xs), x, Box::new(c))), out), find_stop(p, rw, env, x, c, items, 0, stop, out)]
        evals_to(p, env, rw(xs), Val::List(items)) && find_stop(p, rw, env, x, c, items, 0, stop, out) implies evals_to(
            p,
            env,
            rw(XExpr::Find(Box::new(xs), x, Box::new(c))),
            out,
        ) by {
        find_done(p, rw, env, xs, x, c, items, stop, out);
    }
}

pub proof fn ob_sort_by_holds(p: Prog, rw: spec_fn(XExpr) -> Expr)
    requires
        hof_shapes(rw),
    ensures
        ob_sort_by(p, rw),
{
    assert forall|env: Map<nat, Val>, xs: XExpr, x: nat, k: XExpr, items: Seq<Val>, kv: Seq<Val>, keys: Seq<int>|
        #![trigger evals_to(p, env, rw(XExpr::SortBy(Box::new(xs), x, Box::new(k))), Val::List(sort_vals(items, keys))), int_seq(kv)]
        evals_to(p, env, rw(xs), Val::List(items)) && map_ok(p, rw, env, x, k, items, kv, 0) && int_seq(kv) == Some(keys)
            implies evals_to(
            p,
            env,
            rw(XExpr::SortBy(Box::new(xs), x, Box::new(k))),
            Val::List(sort_vals(items, keys)),
        ) by {
        sort_done(p, rw, env, xs, x, k, items, kv, keys);
    }
}

/// SH6 の意味の側：書換えが hof の形を持てば（hof_shapes）、六つの意味の仮定が成り立つ。
pub proof fn sh6_ob_done(p: Prog, rw: spec_fn(XExpr) -> Expr)
    requires
        hof_shapes(rw),
    ensures
        ob_map(p, rw),
        ob_filter(p, rw),
        ob_any(p, rw),
        ob_all(p, rw),
        ob_find(p, rw),
        ob_sort_by(p, rw),
{
    ob_map_holds(p, rw);
    ob_filter_holds(p, rw);
    ob_any_holds(p, rw);
    ob_all_holds(p, rw);
    ob_find_holds(p, rw);
    ob_sort_by_holds(p, rw);
}

} // verus!
