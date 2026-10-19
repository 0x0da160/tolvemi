//! 源の短絡の意味（段階 1b・SH1 の第二部）。
//!
//! any・all・find は、結果が決まった要素で止まり、それより後の要素の述語を評価しない。
//! 核の書換え（any_fold・all_fold・find_fold、fold_meaning.rs）も、畳み込みの中で同じ要素だけ述語を評価する。
//! ここでは、源の評価が同じ要素だけを評価し、同じ結果になることを示す。

use crate::bigstep::*;
use crate::fold_meaning::*;
use crate::proof::*;
use crate::records_proof::*;
use crate::spec::*;
use crate::xmeaning::*;
use crate::xsem::*;
use vstd::prelude::*;

verus! {

// ------------------------------------------------------------------ 先頭の性質の伸長

/// 先頭 k 個に真があれば、それより長い先頭にも真がある。
proof fn any_k_stays(keep: Seq<bool>, k: nat, m: nat)
    requires
        k <= m,
        any_k(keep, k),
    ensures
        any_k(keep, m),
    decreases m - k,
{
    reveal_with_fuel(any_k, 1);
    if k < m {
        any_k_stays(keep, k, (m - 1) as nat);
    }
}

/// 先頭 k 個に偽があれば、それより長い先頭にも偽がある。
proof fn all_k_stays(keep: Seq<bool>, k: nat, m: nat)
    requires
        k <= m,
        !all_k(keep, k),
    ensures
        !all_k(keep, m),
    decreases m - k,
{
    reveal_with_fuel(all_k, 1);
    if k < m {
        all_k_stays(keep, k, (m - 1) as nat);
    }
}

/// 先頭 k 個で値が選ばれていれば、それより長い先頭でも同じ値が選ばれる。
proof fn first_k_stays(items: Seq<Val>, keep: Seq<bool>, k: nat, m: nat)
    requires
        k <= m,
        first_k(items, keep, k) is Some,
    ensures
        first_k(items, keep, m) == first_k(items, keep, k),
    decreases m - k,
{
    reveal_with_fuel(first_k, 1);
    if k < m {
        first_k_stays(items, keep, k, (m - 1) as nat);
    }
}

// ------------------------------------------------------------------ 燃料の単調性

/// any の源の評価は、燃料を増やしても成功した評価と同じ結果になる。
proof fn xany_mono(p: Prog, n: nat, m: nat, env: Map<nat, Val>, x: nat, c: Expr, items: Seq<Val>, j: nat)
    requires
        n <= m,
        xany(embed_prog(p), n, env, x, embed(c), items, j) is Done,
    ensures
        xany(embed_prog(p), m, env, x, embed(c), items, j) == xany(embed_prog(p), n, env, x, embed(c), items, j),
    decreases items.len() - j,
{
    if j < items.len() {
        let env2 = env.insert(x, items[j as int]);
        let f = (n - 1) as nat;
        let fm = (m - 1) as nat;
        assert(n > 0);
        assert(xeval(embed_prog(p), f, env2, embed(c)) is Done);
        xlift(p, f, fm, env2, c);
        if xeval(embed_prog(p), f, env2, embed(c)) == Res::Done(Val::Bool(false)) {
            assert(xany(embed_prog(p), f, env, x, embed(c), items, j + 1) is Done);
            xany_mono(p, f, fm, env, x, c, items, j + 1);
        }
    }
}

/// all の源の評価の単調性。
proof fn xall_mono(p: Prog, n: nat, m: nat, env: Map<nat, Val>, x: nat, c: Expr, items: Seq<Val>, j: nat)
    requires
        n <= m,
        xall(embed_prog(p), n, env, x, embed(c), items, j) is Done,
    ensures
        xall(embed_prog(p), m, env, x, embed(c), items, j) == xall(embed_prog(p), n, env, x, embed(c), items, j),
    decreases items.len() - j,
{
    if j < items.len() {
        let env2 = env.insert(x, items[j as int]);
        let f = (n - 1) as nat;
        let fm = (m - 1) as nat;
        assert(n > 0);
        assert(xeval(embed_prog(p), f, env2, embed(c)) is Done);
        xlift(p, f, fm, env2, c);
        if xeval(embed_prog(p), f, env2, embed(c)) == Res::Done(Val::Bool(true)) {
            assert(xall(embed_prog(p), f, env, x, embed(c), items, j + 1) is Done);
            xall_mono(p, f, fm, env, x, c, items, j + 1);
        }
    }
}

/// find の源の評価の単調性。
proof fn xfind_mono(p: Prog, n: nat, m: nat, env: Map<nat, Val>, x: nat, c: Expr, items: Seq<Val>, j: nat)
    requires
        n <= m,
        xfind(embed_prog(p), n, env, x, embed(c), items, j) is Done,
    ensures
        xfind(embed_prog(p), m, env, x, embed(c), items, j) == xfind(embed_prog(p), n, env, x, embed(c), items, j),
    decreases items.len() - j,
{
    if j < items.len() {
        let env2 = env.insert(x, items[j as int]);
        let f = (n - 1) as nat;
        let fm = (m - 1) as nat;
        assert(n > 0);
        assert(xeval(embed_prog(p), f, env2, embed(c)) is Done);
        xlift(p, f, fm, env2, c);
        if xeval(embed_prog(p), f, env2, embed(c)) == Res::Done(Val::Bool(false)) {
            assert(xfind(embed_prog(p), f, env, x, embed(c), items, j + 1) is Done);
            xfind_mono(p, f, fm, env, x, c, items, j + 1);
        }
    }
}

// ------------------------------------------------------------------ 要素ごとの燃料の存在

/// any：先頭に真が無ければ（!any_k(j)）、要素ごとの述語の値から、源の any は真偽の結果を返す（燃料の存在）。
/// 述語は、真がまだ無い要素でだけ評価する。
proof fn xany_from_each(p: Prog, env: Map<nat, Val>, x: nat, c: Expr, items: Seq<Val>, keep: Seq<bool>, j: nat)
    requires
        keep.len() == items.len(),
        j <= items.len(),
        !any_k(keep, j),
        forall|k: int|
            0 <= k < items.len() && !any_k(keep, k as nat) ==> evals_to(
                p,
                #[trigger] env.insert(x, items[k]),
                c,
                Val::Bool(keep[k]),
            ),
    ensures
        exists|n: nat|
            #[trigger] xany(embed_prog(p), n, env, x, embed(c), items, j) == Res::Done(
                Val::Bool(any_k(keep, items.len() as nat)),
            ),
    decreases items.len() - j,
{
    reveal_with_fuel(any_k, 1);
    if j == items.len() {
        assert(xany(embed_prog(p), 1, env, x, embed(c), items, j) == Res::Done(Val::Bool(false)));
    } else {
        let env2 = env.insert(x, items[j as int]);
        assert(evals_to(p, env2, c, Val::Bool(keep[j as int])));
        let n1 = choose|n: nat| #[trigger] eval(p, n, env2, c) == Res::Done(Val::Bool(keep[j as int]));
        embed_eval(p, n1, env2, c);
        if keep[j as int] {
            assert(any_k(keep, (j + 1) as nat));
            any_k_stays(keep, (j + 1) as nat, items.len() as nat);
            assert(xany(embed_prog(p), n1 + 1, env, x, embed(c), items, j) == Res::Done(
                Val::Bool(any_k(keep, items.len() as nat)),
            ));
        } else {
            assert(!any_k(keep, (j + 1) as nat));
            xany_from_each(p, env, x, c, items, keep, j + 1);
            let n2 = choose|n: nat|
                #[trigger] xany(embed_prog(p), n, env, x, embed(c), items, j + 1) == Res::Done(
                    Val::Bool(any_k(keep, items.len() as nat)),
                );
            let n = max(n1, n2);
            lift(p, n1, n, env2, c);
            embed_eval(p, n, env2, c);
            xany_mono(p, n2, n, env, x, c, items, j + 1);
            assert(xany(embed_prog(p), n + 1, env, x, embed(c), items, j) == Res::Done(
                Val::Bool(any_k(keep, items.len() as nat)),
            ));
        }
    }
}

/// all：先頭がすべて真なら（all_k(j)）、要素ごとの述語の値から、源の all は真偽の結果を返す（燃料の存在）。
proof fn xall_from_each(p: Prog, env: Map<nat, Val>, x: nat, c: Expr, items: Seq<Val>, keep: Seq<bool>, j: nat)
    requires
        keep.len() == items.len(),
        j <= items.len(),
        all_k(keep, j),
        forall|k: int|
            0 <= k < items.len() && all_k(keep, k as nat) ==> evals_to(
                p,
                #[trigger] env.insert(x, items[k]),
                c,
                Val::Bool(keep[k]),
            ),
    ensures
        exists|n: nat|
            #[trigger] xall(embed_prog(p), n, env, x, embed(c), items, j) == Res::Done(
                Val::Bool(all_k(keep, items.len() as nat)),
            ),
    decreases items.len() - j,
{
    reveal_with_fuel(all_k, 1);
    if j == items.len() {
        assert(xall(embed_prog(p), 1, env, x, embed(c), items, j) == Res::Done(Val::Bool(true)));
    } else {
        let env2 = env.insert(x, items[j as int]);
        assert(evals_to(p, env2, c, Val::Bool(keep[j as int])));
        let n1 = choose|n: nat| #[trigger] eval(p, n, env2, c) == Res::Done(Val::Bool(keep[j as int]));
        embed_eval(p, n1, env2, c);
        if keep[j as int] {
            assert(all_k(keep, (j + 1) as nat));
            xall_from_each(p, env, x, c, items, keep, j + 1);
            let n2 = choose|n: nat|
                #[trigger] xall(embed_prog(p), n, env, x, embed(c), items, j + 1) == Res::Done(
                    Val::Bool(all_k(keep, items.len() as nat)),
                );
            let n = max(n1, n2);
            lift(p, n1, n, env2, c);
            embed_eval(p, n, env2, c);
            xall_mono(p, n2, n, env, x, c, items, j + 1);
            assert(xall(embed_prog(p), n + 1, env, x, embed(c), items, j) == Res::Done(
                Val::Bool(all_k(keep, items.len() as nat)),
            ));
        } else {
            assert(!all_k(keep, (j + 1) as nat));
            all_k_stays(keep, (j + 1) as nat, items.len() as nat);
            assert(xall(embed_prog(p), n1 + 1, env, x, embed(c), items, j) == Res::Done(
                Val::Bool(all_k(keep, items.len() as nat)),
            ));
        }
    }
}

/// find：先頭に選ばれた値が無ければ（first_k(j) is None）、要素ごとの述語の値から、源の find は選ばれた値を返す（燃料の存在）。
proof fn xfind_from_each(p: Prog, env: Map<nat, Val>, x: nat, c: Expr, items: Seq<Val>, keep: Seq<bool>, j: nat)
    requires
        keep.len() == items.len(),
        j <= items.len(),
        first_k(items, keep, j) is None,
        forall|k: int|
            0 <= k < items.len() && first_k(items, keep, k as nat) is None ==> evals_to(
                p,
                #[trigger] env.insert(x, items[k]),
                c,
                Val::Bool(keep[k]),
            ),
    ensures
        exists|n: nat|
            #[trigger] xfind(embed_prog(p), n, env, x, embed(c), items, j) == Res::Done(
                first_k(items, keep, items.len() as nat),
            ),
    decreases items.len() - j,
{
    reveal_with_fuel(first_k, 1);
    if j == items.len() {
        assert(xfind(embed_prog(p), 1, env, x, embed(c), items, j) == Res::Done(Val::None));
    } else {
        let env2 = env.insert(x, items[j as int]);
        assert(evals_to(p, env2, c, Val::Bool(keep[j as int])));
        let n1 = choose|n: nat| #[trigger] eval(p, n, env2, c) == Res::Done(Val::Bool(keep[j as int]));
        embed_eval(p, n1, env2, c);
        if keep[j as int] {
            assert(first_k(items, keep, (j + 1) as nat) is Some);
            first_k_stays(items, keep, (j + 1) as nat, items.len() as nat);
            assert(xfind(embed_prog(p), n1 + 1, env, x, embed(c), items, j) == Res::Done(
                Val::Some(Box::new(items[j as int])),
            ));
        } else {
            assert(first_k(items, keep, (j + 1) as nat) is None);
            xfind_from_each(p, env, x, c, items, keep, j + 1);
            let n2 = choose|n: nat|
                #[trigger] xfind(embed_prog(p), n, env, x, embed(c), items, j + 1) == Res::Done(
                    first_k(items, keep, items.len() as nat),
                );
            let n = max(n1, n2);
            lift(p, n1, n, env2, c);
            embed_eval(p, n, env2, c);
            xfind_mono(p, n2, n, env, x, c, items, j + 1);
            assert(xfind(embed_prog(p), n + 1, env, x, embed(c), items, j) == Res::Done(
                first_k(items, keep, items.len() as nat),
            ));
        }
    }
}

// ------------------------------------------------------------------ 源の意味（核の書換えと同じ前提）

/// 源の any：要素の述語の値が核と同じなら、源の any は any_k(keep, n) に評価される。
proof fn any_source(
    p: Prog,
    env: Map<nat, Val>,
    xs: Expr,
    x: nat,
    c: Expr,
    items: Seq<Val>,
    keep: Seq<bool>,
    out: bool,
)
    requires
        keep.len() == items.len(),
        out == any_k(keep, items.len() as nat),
        evals_to(p, env, xs, Val::List(items)),
        forall|k: int|
            0 <= k < items.len() && !any_k(keep, k as nat) ==> evals_to(
                p,
                #[trigger] env.insert(x, items[k]),
                c,
                Val::Bool(keep[k]),
            ),
    ensures
        xevals_to(
            embed_prog(p),
            env,
            XExpr::Any(Box::new(embed(xs)), x, Box::new(embed(c))),
            Val::Bool(out),
        ),
{
    reveal_with_fuel(any_k, 1);
    xany_from_each(p, env, x, c, items, keep, 0);
    let n1 = choose|n: nat| #[trigger] eval(p, n, env, xs) == Res::Done(Val::List(items));
    let n2 = choose|n: nat|
        #[trigger] xany(embed_prog(p), n, env, x, embed(c), items, 0) == Res::Done(
            Val::Bool(any_k(keep, items.len() as nat)),
        );
    let n = max(n1, n2);
    lift(p, n1, n, env, xs);
    embed_eval(p, n, env, xs);
    xany_mono(p, n2, n, env, x, c, items, 0);
    assert(xeval(embed_prog(p), n + 1, env, XExpr::Any(Box::new(embed(xs)), x, Box::new(embed(c)))) == Res::Done(
        Val::Bool(out),
    ));
}

/// 源の all：要素の述語の値が核と同じなら、源の all は all_k(keep, n) に評価される。
proof fn all_source(
    p: Prog,
    env: Map<nat, Val>,
    xs: Expr,
    x: nat,
    c: Expr,
    items: Seq<Val>,
    keep: Seq<bool>,
    out: bool,
)
    requires
        keep.len() == items.len(),
        out == all_k(keep, items.len() as nat),
        evals_to(p, env, xs, Val::List(items)),
        forall|k: int|
            0 <= k < items.len() && all_k(keep, k as nat) ==> evals_to(
                p,
                #[trigger] env.insert(x, items[k]),
                c,
                Val::Bool(keep[k]),
            ),
    ensures
        xevals_to(
            embed_prog(p),
            env,
            XExpr::All(Box::new(embed(xs)), x, Box::new(embed(c))),
            Val::Bool(out),
        ),
{
    reveal_with_fuel(all_k, 1);
    xall_from_each(p, env, x, c, items, keep, 0);
    let n1 = choose|n: nat| #[trigger] eval(p, n, env, xs) == Res::Done(Val::List(items));
    let n2 = choose|n: nat|
        #[trigger] xall(embed_prog(p), n, env, x, embed(c), items, 0) == Res::Done(
            Val::Bool(all_k(keep, items.len() as nat)),
        );
    let n = max(n1, n2);
    lift(p, n1, n, env, xs);
    embed_eval(p, n, env, xs);
    xall_mono(p, n2, n, env, x, c, items, 0);
    assert(xeval(embed_prog(p), n + 1, env, XExpr::All(Box::new(embed(xs)), x, Box::new(embed(c)))) == Res::Done(
        Val::Bool(out),
    ));
}

/// 源の find：要素の述語の値が核と同じなら、源の find は first_k(keep, n) に評価される。
proof fn find_source(
    p: Prog,
    env: Map<nat, Val>,
    xs: Expr,
    x: nat,
    c: Expr,
    items: Seq<Val>,
    keep: Seq<bool>,
    out: Val,
)
    requires
        keep.len() == items.len(),
        out == first_k(items, keep, items.len() as nat),
        evals_to(p, env, xs, Val::List(items)),
        forall|k: int|
            0 <= k < items.len() && first_k(items, keep, k as nat) is None ==> evals_to(
                p,
                #[trigger] env.insert(x, items[k]),
                c,
                Val::Bool(keep[k]),
            ),
    ensures
        xevals_to(
            embed_prog(p),
            env,
            XExpr::Find(Box::new(embed(xs)), x, Box::new(embed(c))),
            out,
        ),
{
    reveal_with_fuel(first_k, 1);
    xfind_from_each(p, env, x, c, items, keep, 0);
    let n1 = choose|n: nat| #[trigger] eval(p, n, env, xs) == Res::Done(Val::List(items));
    let n2 = choose|n: nat|
        #[trigger] xfind(embed_prog(p), n, env, x, embed(c), items, 0) == Res::Done(
            first_k(items, keep, items.len() as nat),
        );
    let n = max(n1, n2);
    lift(p, n1, n, env, xs);
    embed_eval(p, n, env, xs);
    xfind_mono(p, n2, n, env, x, c, items, 0);
    assert(xeval(embed_prog(p), n + 1, env, XExpr::Find(Box::new(embed(xs)), x, Box::new(embed(c)))) == Res::Done(
        out,
    ));
}

/// any の意味（核の書換えとの一致）：源の any と any_fold は、同じ前提から同じ真偽値に評価される。
pub proof fn any_meaning_x(
    p: Prog,
    env: Map<nat, Val>,
    xs: Expr,
    acc: nat,
    x: nat,
    c: Expr,
    items: Seq<Val>,
    keep: Seq<bool>,
)
    requires
        acc != x,
        absent(acc, c),
        keep.len() == items.len(),
        evals_to(p, env, xs, Val::List(items)),
        forall|k: int|
            0 <= k < items.len() && !any_k(keep, k as nat) ==> evals_to(
                p,
                #[trigger] env.insert(x, items[k]),
                c,
                Val::Bool(keep[k]),
            ),
    ensures
        xevals_to(
            embed_prog(p),
            env,
            XExpr::Any(Box::new(embed(xs)), x, Box::new(embed(c))),
            Val::Bool(any_k(keep, items.len() as nat)),
        ),
        evals_to(p, env, any_fold(xs, acc, x, c), Val::Bool(any_k(keep, items.len() as nat))),
{
    any_source(p, env, xs, x, c, items, keep, any_k(keep, items.len() as nat));
    any_meaning(p, env, xs, acc, x, c, items, keep);
}

/// all の意味（核の書換えとの一致）：源の all と all_fold は、同じ前提から同じ真偽値に評価される。
pub proof fn all_meaning_x(
    p: Prog,
    env: Map<nat, Val>,
    xs: Expr,
    acc: nat,
    x: nat,
    c: Expr,
    items: Seq<Val>,
    keep: Seq<bool>,
)
    requires
        acc != x,
        absent(acc, c),
        keep.len() == items.len(),
        evals_to(p, env, xs, Val::List(items)),
        forall|k: int|
            0 <= k < items.len() && all_k(keep, k as nat) ==> evals_to(
                p,
                #[trigger] env.insert(x, items[k]),
                c,
                Val::Bool(keep[k]),
            ),
    ensures
        xevals_to(
            embed_prog(p),
            env,
            XExpr::All(Box::new(embed(xs)), x, Box::new(embed(c))),
            Val::Bool(all_k(keep, items.len() as nat)),
        ),
        evals_to(p, env, all_fold(xs, acc, x, c), Val::Bool(all_k(keep, items.len() as nat))),
{
    all_source(p, env, xs, x, c, items, keep, all_k(keep, items.len() as nat));
    all_meaning(p, env, xs, acc, x, c, items, keep);
}

/// find の意味（核の書換えとの一致）：源の find と find_fold は、同じ前提から同じ値に評価される。
/// 源の束縛名 item は、核の反復変数 item に対応する。x は選ばれた値を束縛する核の名前。
pub proof fn find_meaning_x(
    p: Prog,
    env: Map<nat, Val>,
    xs: Expr,
    t: Ty,
    acc: nat,
    item: nat,
    x: nat,
    c: Expr,
    items: Seq<Val>,
    keep: Seq<bool>,
)
    requires
        acc != item,
        absent(acc, c),
        keep.len() == items.len(),
        evals_to(p, env, xs, Val::List(items)),
        forall|k: int|
            0 <= k < items.len() && first_k(items, keep, k as nat) is None ==> evals_to(
                p,
                #[trigger] env.insert(item, items[k]),
                c,
                Val::Bool(keep[k]),
            ),
    ensures
        xevals_to(
            embed_prog(p),
            env,
            XExpr::Find(Box::new(embed(xs)), item, Box::new(embed(c))),
            first_k(items, keep, items.len() as nat),
        ),
        evals_to(p, env, find_fold(xs, t, acc, item, c, x), first_k(items, keep, items.len() as nat)),
{
    find_source(p, env, xs, item, c, items, keep, first_k(items, keep, items.len() as nat));
    find_meaning(p, env, xs, t, acc, item, x, c, items, keep);
}

} // verus!
