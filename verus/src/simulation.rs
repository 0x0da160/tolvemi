//! SH4：書換え全体の模擬（段階 0）。
//!
//! 源のプログラム `XProg`（xsem.rs。hof の形を含む）と、関数ごとに書き換えた後の核のプログラム `Prog`（spec.rs）の
//! 関係 `sim_prog` を定める。源の評価が値 w を返すなら、書換え後の評価も w を返す（燃料の存在）。書換え後の
//! 非 OutOfFuel の結果はすべて w に等しい（決定性）。
//!
//! 名前つきの仮定（sim_ok にまとめる。どれも証明せず、引数として渡す）：
//! - `homomorphic(rw)`（ob-core）：核の形（定数・変数・組・呼出し・束縛・fold・match など）の書換えは形を保ち、
//!   子を `rw` で写す。呼出しは同じ番号と、引数の写し。
//! - `ob_map` から `ob_sort_by`：hof の形ごとの意味の定理。源の子の値に対応する写しの子の値が揃えば、
//!   写しも同じ値に評価される。段階 1b（SH6）で示す。書換えの新しい名前の新鮮さ（SH5）もここに含める。
//!
//! 証明は燃料についての帰納。呼出しは燃料を一つ減らすので、ランクは使わない。ランクは書換え後の呼出し条件
//! （`call_typing_erased`）と、整形式の書換え後のプログラムの停止（`sh4_total_target`）にだけ使う。
//! 署名は `erase_sig` で消去する（Dict<K, V> は List<Pair<K, V>>）。List・None・Inj の型注釈も `erase_ty` で消去する。
//! 評価は型注釈を読まないので、値の模擬は注釈に依らない。整形式（wf）の検査は検査器（検証済みの部品）が見る。

use crate::bigstep::*;
use crate::proof::*;
use crate::sortspec::*;
use crate::spec::*;
use crate::xmeaning::kept_from;
use crate::xsem::*;
use vstd::prelude::*;

verus! {

// ------------------------------------------------------------------ 署名の消去

/// 源の型を核の型に消去する。Dict<K, V> は List<Pair<K, V>>、ほかは構造どおり。
pub open spec fn erase_ty(t: Ty) -> Ty
    decreases t,
{
    match t {
        Ty::List(a) => Ty::List(Box::new(erase_ty(*a))),
        Ty::Option(a) => Ty::Option(Box::new(erase_ty(*a))),
        Ty::Pair(a, b) => Ty::Pair(Box::new(erase_ty(*a)), Box::new(erase_ty(*b))),
        Ty::Result(a, b) => Ty::Result(Box::new(erase_ty(*a)), Box::new(erase_ty(*b))),
        Ty::Dict(k, v) => Ty::List(Box::new(Ty::Pair(Box::new(erase_ty(*k)), Box::new(erase_ty(*v))))),
        _ => t,
    }
}

/// 核の関数の署名は、源の署名を消去したものに等しい（引数の名前は変えない）。
pub open spec fn erase_sig(xf: XFunc, f: Func) -> bool {
    &&& f.params.len() == xf.params.len()
    &&& forall|k: int| 0 <= k < xf.params.len() ==> #[trigger] f.params[k].0 == xf.params[k].0
    &&& forall|k: int| 0 <= k < xf.params.len() ==> #[trigger] f.params[k].1 == erase_ty(xf.params[k].1)
    &&& f.ret == erase_ty(xf.ret)
}

// ------------------------------------------------------------------ 写しと構造

pub open spec fn rw_args(rw: spec_fn(XExpr) -> Expr, es: Seq<XExpr>) -> Seq<Expr> {
    Seq::new(es.len(), |i: int| rw(es[i]))
}

/// 書換えの写しの構造：宣言の数・ランク・rec の印・entry は源と同じ。関数ごとに署名は消去したもので、本体は rw の写し。
pub open spec fn sim_prog(xp: XProg, p: Prog, rw: spec_fn(XExpr) -> Expr) -> bool {
    &&& p.funcs.len() == xp.funcs.len()
    &&& p.rank == xp.rank
    &&& p.rec == xp.rec
    &&& p.entry == xp.entry
    &&& forall|g: int| 0 <= g < xp.funcs.len() ==> erase_sig(xp.funcs[g], #[trigger] p.funcs[g])
    &&& forall|g: int| 0 <= g < xp.funcs.len() ==> #[trigger] p.funcs[g].body == rw(xp.funcs[g].body)
}

/// ob-core：核の形の書換えは形を保ち、子を rw で写す（呼出しは番号と引数の写し）。
/// List・None・Inj の型注釈は erase_ty で消去する。値の意味は注釈を読まない（eval は注釈を見ない）。
pub open spec fn homomorphic(rw: spec_fn(XExpr) -> Expr) -> bool {
    &&& forall|n: int| #[trigger] rw(XExpr::Int(n)) == Expr::Int(n)
    &&& forall|b: bool| #[trigger] rw(XExpr::Bool(b)) == Expr::Bool(b)
    &&& rw(XExpr::Unit) == Expr::Unit
    &&& forall|c: int| #[trigger] rw(XExpr::Char(c)) == Expr::Char(c)
    &&& forall|x: nat| #[trigger] rw(XExpr::Var(x)) == Expr::Var(x)
    &&& forall|t: Ty, es: Seq<XExpr>| #[trigger] rw(XExpr::List(t, es)) == Expr::List(erase_ty(t), rw_args(rw, es))
    &&& forall|a: XExpr| #[trigger] rw(XExpr::Some(Box::new(a))) == Expr::Some(Box::new(rw(a)))
    &&& forall|t: Ty| #[trigger] rw(XExpr::None(t)) == Expr::None(erase_ty(t))
    &&& forall|a: XExpr, b: XExpr|
        #[trigger] rw(XExpr::Pair(Box::new(a), Box::new(b))) == Expr::Pair(Box::new(rw(a)), Box::new(rw(b)))
    &&& forall|bi: Builtin, es: Seq<XExpr>| #[trigger] rw(XExpr::Builtin(bi, es)) == Expr::Builtin(bi, rw_args(rw, es))
    &&& forall|g: nat, es: Seq<XExpr>| #[trigger] rw(XExpr::Call(g, es)) == Expr::Call(g, rw_args(rw, es))
    &&& forall|x: nat, a: XExpr, b: XExpr|
        #[trigger] rw(XExpr::Let(x, Box::new(a), Box::new(b))) == Expr::Let(x, Box::new(rw(a)), Box::new(rw(b)))
    &&& forall|c: XExpr, a: XExpr, b: XExpr|
        #[trigger] rw(XExpr::If(Box::new(c), Box::new(a), Box::new(b))) == Expr::If(
            Box::new(rw(c)),
            Box::new(rw(a)),
            Box::new(rw(b)),
        )
    &&& forall|xs: XExpr, init: XExpr, acc: nat, item: nat, body: XExpr|
        #[trigger] rw(XExpr::Fold(Box::new(xs), Box::new(init), acc, item, Box::new(body))) == Expr::Fold(
            Box::new(rw(xs)),
            Box::new(rw(init)),
            acc,
            item,
            Box::new(rw(body)),
        )
    &&& forall|m: XExpr, nb: XExpr, x: nat, sm: XExpr|
        #[trigger] rw(XExpr::Match(Box::new(m), Box::new(nb), x, Box::new(sm))) == Expr::Match(
            Box::new(rw(m)),
            Box::new(rw(nb)),
            x,
            Box::new(rw(sm)),
        )
    &&& forall|ok: bool, t: Ty, u: Ty, a: XExpr|
        #[trigger] rw(XExpr::Inj(ok, t, u, Box::new(a))) == Expr::Inj(ok, erase_ty(t), erase_ty(u), Box::new(rw(a)))
    &&& forall|m: XExpr, x: nat, a: XExpr, y: nat, b: XExpr|
        #[trigger] rw(XExpr::MatchR(Box::new(m), x, Box::new(a), y, Box::new(b))) == Expr::MatchR(
            Box::new(rw(m)),
            x,
            Box::new(rw(a)),
            y,
            Box::new(rw(b)),
        )
}

// ------------------------------------------------------------------ hof の形ごとの意味の仮定（ob-*）
//
// 各 ob は「写しの子が、源の子の値の並びに対応する値に評価されれば、写しの形も源の結果に評価される」。
// 源の側の並びは、xsem.rs の評価器が通る要素（any・all・find は止まるまで）と同じ。

/// 写しの map が、要素ごとの本体の値 vs（items の各要素に対応する）を返す。
pub open spec fn map_ok(
    p: Prog,
    rw: spec_fn(XExpr) -> Expr,
    env: Map<nat, Val>,
    x: nat,
    c: XExpr,
    items: Seq<Val>,
    vs: Seq<Val>,
    j: nat,
) -> bool {
    &&& vs.len() + j == items.len()
    &&& forall|k: int|
        j <= k < items.len() ==> evals_to(p, #[trigger] env.insert(x, items[k]), rw(c), vs[k - (j as int)])
}

pub open spec fn filter_keep(
    p: Prog,
    rw: spec_fn(XExpr) -> Expr,
    env: Map<nat, Val>,
    x: nat,
    c: XExpr,
    items: Seq<Val>,
    keep: Seq<bool>,
    out: Seq<Val>,
    j: nat,
) -> bool {
    &&& keep.len() == items.len()
    &&& forall|k: int|
        j <= k < items.len() ==> evals_to(p, #[trigger] env.insert(x, items[k]), rw(c), Val::Bool(keep[k]))
    &&& out == kept_from(items, keep, j)
}

/// any：述語が偽の要素を j から stop まで飛ばし、stop で真になる（stop = 長さなら無い）。
pub open spec fn any_stop(
    p: Prog,
    rw: spec_fn(XExpr) -> Expr,
    env: Map<nat, Val>,
    x: nat,
    c: XExpr,
    items: Seq<Val>,
    j: nat,
    stop: nat,
    out: Val,
) -> bool {
    &&& j <= stop
    &&& stop <= items.len()
    &&& forall|k: int|
        j <= k < stop ==> evals_to(p, #[trigger] env.insert(x, items[k]), rw(c), Val::Bool(false))
    &&& stop < items.len() ==> evals_to(p, env.insert(x, items[stop as int]), rw(c), Val::Bool(true))
    &&& out == Val::Bool(stop < items.len())
}

/// all：述語が真の要素を j から stop まで飛ばし、stop で偽になる（stop = 長さなら無い）。
pub open spec fn all_stop(
    p: Prog,
    rw: spec_fn(XExpr) -> Expr,
    env: Map<nat, Val>,
    x: nat,
    c: XExpr,
    items: Seq<Val>,
    j: nat,
    stop: nat,
    out: Val,
) -> bool {
    &&& j <= stop
    &&& stop <= items.len()
    &&& forall|k: int|
        j <= k < stop ==> evals_to(p, #[trigger] env.insert(x, items[k]), rw(c), Val::Bool(true))
    &&& stop < items.len() ==> evals_to(p, env.insert(x, items[stop as int]), rw(c), Val::Bool(false))
    &&& out == Val::Bool(stop == items.len())
}

/// find：述語が偽の要素を飛ばし、stop で真になる（stop = 長さなら無い）。
pub open spec fn find_stop(
    p: Prog,
    rw: spec_fn(XExpr) -> Expr,
    env: Map<nat, Val>,
    x: nat,
    c: XExpr,
    items: Seq<Val>,
    j: nat,
    stop: nat,
    out: Val,
) -> bool {
    &&& j <= stop
    &&& stop <= items.len()
    &&& forall|k: int|
        j <= k < stop ==> evals_to(p, #[trigger] env.insert(x, items[k]), rw(c), Val::Bool(false))
    &&& stop < items.len() ==> evals_to(p, env.insert(x, items[stop as int]), rw(c), Val::Bool(true))
    &&& out == (if stop < items.len() { Val::Some(Box::new(items[stop as int])) } else { Val::None })
}

pub open spec fn ob_map(p: Prog, rw: spec_fn(XExpr) -> Expr) -> bool {
    forall|env: Map<nat, Val>, xs: XExpr, x: nat, c: XExpr, items: Seq<Val>, vs: Seq<Val>|
        #![trigger evals_to(p, env, rw(XExpr::Map(Box::new(xs), x, Box::new(c))), Val::List(vs)), map_ok(p, rw, env, x, c, items, vs, 0)]
        evals_to(p, env, rw(xs), Val::List(items)) && map_ok(p, rw, env, x, c, items, vs, 0)
            ==> evals_to(p, env, rw(XExpr::Map(Box::new(xs), x, Box::new(c))), Val::List(vs))
}

pub open spec fn ob_filter(p: Prog, rw: spec_fn(XExpr) -> Expr) -> bool {
    forall|env: Map<nat, Val>, xs: XExpr, x: nat, c: XExpr, items: Seq<Val>, keep: Seq<bool>, out: Seq<Val>|
        #![trigger evals_to(p, env, rw(XExpr::Filter(Box::new(xs), x, Box::new(c))), Val::List(out)), filter_keep(p, rw, env, x, c, items, keep, out, 0)]
        evals_to(p, env, rw(xs), Val::List(items)) && filter_keep(p, rw, env, x, c, items, keep, out, 0)
            ==> evals_to(p, env, rw(XExpr::Filter(Box::new(xs), x, Box::new(c))), Val::List(out))
}

pub open spec fn ob_any(p: Prog, rw: spec_fn(XExpr) -> Expr) -> bool {
    forall|env: Map<nat, Val>, xs: XExpr, x: nat, c: XExpr, items: Seq<Val>, stop: nat, out: Val|
        #![trigger evals_to(p, env, rw(XExpr::Any(Box::new(xs), x, Box::new(c))), out), any_stop(p, rw, env, x, c, items, 0, stop, out)]
        evals_to(p, env, rw(xs), Val::List(items)) && any_stop(p, rw, env, x, c, items, 0, stop, out)
            ==> evals_to(p, env, rw(XExpr::Any(Box::new(xs), x, Box::new(c))), out)
}

pub open spec fn ob_all(p: Prog, rw: spec_fn(XExpr) -> Expr) -> bool {
    forall|env: Map<nat, Val>, xs: XExpr, x: nat, c: XExpr, items: Seq<Val>, stop: nat, out: Val|
        #![trigger evals_to(p, env, rw(XExpr::All(Box::new(xs), x, Box::new(c))), out), all_stop(p, rw, env, x, c, items, 0, stop, out)]
        evals_to(p, env, rw(xs), Val::List(items)) && all_stop(p, rw, env, x, c, items, 0, stop, out)
            ==> evals_to(p, env, rw(XExpr::All(Box::new(xs), x, Box::new(c))), out)
}

pub open spec fn ob_find(p: Prog, rw: spec_fn(XExpr) -> Expr) -> bool {
    forall|env: Map<nat, Val>, xs: XExpr, x: nat, c: XExpr, items: Seq<Val>, stop: nat, out: Val|
        #![trigger evals_to(p, env, rw(XExpr::Find(Box::new(xs), x, Box::new(c))), out), find_stop(p, rw, env, x, c, items, 0, stop, out)]
        evals_to(p, env, rw(xs), Val::List(items)) && find_stop(p, rw, env, x, c, items, 0, stop, out)
            ==> evals_to(p, env, rw(XExpr::Find(Box::new(xs), x, Box::new(c))), out)
}

pub open spec fn ob_sort_by(p: Prog, rw: spec_fn(XExpr) -> Expr) -> bool {
    forall|env: Map<nat, Val>, xs: XExpr, x: nat, k: XExpr, items: Seq<Val>, kv: Seq<Val>, keys: Seq<int>|
        #![trigger evals_to(p, env, rw(XExpr::SortBy(Box::new(xs), x, Box::new(k))), Val::List(sort_vals(items, keys))), int_seq(kv)]
        evals_to(p, env, rw(xs), Val::List(items)) && map_ok(p, rw, env, x, k, items, kv, 0) && int_seq(kv) == Some(keys)
            ==> evals_to(p, env, rw(XExpr::SortBy(Box::new(xs), x, Box::new(k))), Val::List(sort_vals(items, keys)))
}

/// 模擬の仮定の全体。
pub open spec fn sim_ok(xp: XProg, p: Prog, rw: spec_fn(XExpr) -> Expr) -> bool {
    &&& sim_prog(xp, p, rw)
    &&& homomorphic(rw)
    &&& ob_map(p, rw)
    &&& ob_filter(p, rw)
    &&& ob_any(p, rw)
    &&& ob_all(p, rw)
    &&& ob_find(p, rw)
    &&& ob_sort_by(p, rw)
}

/// 源の entry の実行（核の eval_entry と同じ形）。
pub open spec fn xeval_entry(xp: XProg, fuel: nat, v: Val) -> Res {
    let f = xp.funcs[xp.entry as int];
    xeval(xp, fuel, bind(f.params, seq![v], 1), f.body)
}

// ------------------------------------------------------------------ 補助の補題

/// 引数の名前が同じなら、束縛の環境は同じ。
proof fn bind_names_eq(p1: Seq<(nat, Ty)>, p2: Seq<(nat, Ty)>, vs: Seq<Val>, n: nat)
    requires
        p1.len() == p2.len(),
        forall|k: int| 0 <= k < p1.len() ==> #[trigger] p1[k].0 == p2[k].0,
    ensures
        bind(p1, vs, n) == bind(p2, vs, n),
    decreases n, 0nat,
{
    if n > 0 {
        bind_names_eq(p1, p2, vs, (n - 1) as nat);
    }
}

/// 両方の list で kept_from は、添字 j 以降の keep だけで決まる。
proof fn kept_from_congr(items: Seq<Val>, k1: Seq<bool>, k2: Seq<bool>, j: nat)
    requires
        k1.len() == items.len(),
        k2.len() == items.len(),
        j <= items.len(),
        forall|k: int| j <= k < items.len() ==> #[trigger] k1[k] == k2[k],
    ensures
        kept_from(items, k1, j) == kept_from(items, k2, j),
    decreases items.len() - j,
{
    reveal_with_fuel(kept_from, 1);
    if j < items.len() {
        kept_from_congr(items, k1, k2, j + 1);
        assert(k1[j as int] == k2[j as int]);
    }
}

// 各 ob を使う補題（ob の仮定を一度だけ展開する）。
proof fn use_ob_map(p: Prog, rw: spec_fn(XExpr) -> Expr, env: Map<nat, Val>, xs: XExpr, x: nat, c: XExpr, items: Seq<Val>, vs: Seq<Val>)
    requires
        ob_map(p, rw),
        evals_to(p, env, rw(xs), Val::List(items)),
        map_ok(p, rw, env, x, c, items, vs, 0),
    ensures
        evals_to(p, env, rw(XExpr::Map(Box::new(xs), x, Box::new(c))), Val::List(vs)),
{
}

proof fn use_ob_filter(p: Prog, rw: spec_fn(XExpr) -> Expr, env: Map<nat, Val>, xs: XExpr, x: nat, c: XExpr, items: Seq<Val>, keep: Seq<bool>, out: Seq<Val>)
    requires
        ob_filter(p, rw),
        evals_to(p, env, rw(xs), Val::List(items)),
        filter_keep(p, rw, env, x, c, items, keep, out, 0),
    ensures
        evals_to(p, env, rw(XExpr::Filter(Box::new(xs), x, Box::new(c))), Val::List(out)),
{
}

proof fn use_ob_any(p: Prog, rw: spec_fn(XExpr) -> Expr, env: Map<nat, Val>, xs: XExpr, x: nat, c: XExpr, items: Seq<Val>, stop: nat, out: Val)
    requires
        ob_any(p, rw),
        evals_to(p, env, rw(xs), Val::List(items)),
        any_stop(p, rw, env, x, c, items, 0, stop, out),
    ensures
        evals_to(p, env, rw(XExpr::Any(Box::new(xs), x, Box::new(c))), out),
{
}

proof fn use_ob_all(p: Prog, rw: spec_fn(XExpr) -> Expr, env: Map<nat, Val>, xs: XExpr, x: nat, c: XExpr, items: Seq<Val>, stop: nat, out: Val)
    requires
        ob_all(p, rw),
        evals_to(p, env, rw(xs), Val::List(items)),
        all_stop(p, rw, env, x, c, items, 0, stop, out),
    ensures
        evals_to(p, env, rw(XExpr::All(Box::new(xs), x, Box::new(c))), out),
{
}

proof fn use_ob_find(p: Prog, rw: spec_fn(XExpr) -> Expr, env: Map<nat, Val>, xs: XExpr, x: nat, c: XExpr, items: Seq<Val>, stop: nat, out: Val)
    requires
        ob_find(p, rw),
        evals_to(p, env, rw(xs), Val::List(items)),
        find_stop(p, rw, env, x, c, items, 0, stop, out),
    ensures
        evals_to(p, env, rw(XExpr::Find(Box::new(xs), x, Box::new(c))), out),
{
}

proof fn use_ob_sort_by(p: Prog, rw: spec_fn(XExpr) -> Expr, env: Map<nat, Val>, xs: XExpr, x: nat, k: XExpr, items: Seq<Val>, kv: Seq<Val>, keys: Seq<int>)
    requires
        ob_sort_by(p, rw),
        evals_to(p, env, rw(xs), Val::List(items)),
        map_ok(p, rw, env, x, k, items, kv, 0),
        int_seq(kv) == Some(keys),
    ensures
        evals_to(p, env, rw(XExpr::SortBy(Box::new(xs), x, Box::new(k))), Val::List(sort_vals(items, keys))),
{
}

// ------------------------------------------------------------------ 列の模擬（燃料で帰納）

/// 引数列：源の評価が vs を返すなら、写しの引数列は vs に評価される。
proof fn sim_args(xp: XProg, p: Prog, rw: spec_fn(XExpr) -> Expr, n: nat, env: Map<nat, Val>, es: Seq<XExpr>, i: nat, vs: Seq<Val>)
    requires
        sim_ok(xp, p, rw),
        xeval_args(xp, n, env, es, i) == ResSeq::Done(vs),
    ensures
        args_to(p, env, rw_args(rw, es), i, vs),
    decreases n, 0nat,
{
    if n > 0 && i < es.len() {
        let f = (n - 1) as nat;
        match xeval(xp, f, env, es[i as int]) {
            Res::Done(v) => match xeval_args(xp, f, env, es, i + 1) {
                ResSeq::Done(vs2) => {
                    sim_expr(xp, p, rw, f, env, es[i as int], v);
                    sim_args(xp, p, rw, f, env, es, i + 1, vs2);
                    let m1 = choose|m: nat| #[trigger] eval(p, m, env, rw(es[i as int])) == Res::Done(v);
                    let m2 = choose|m: nat| #[trigger] eval_args(p, m, env, rw_args(rw, es), i + 1) == ResSeq::Done(vs2);
                    let mm = (max(m1, m2) + 1) as nat;
                    mono(p, m1, (mm - 1) as nat, env, rw(es[i as int]));
                    mono_args(p, m2, (mm - 1) as nat, env, rw_args(rw, es), i + 1);
                    assert(rw_args(rw, es)[i as int] == rw(es[i as int]));
                    assert(eval_args(p, mm, env, rw_args(rw, es), i) == ResSeq::Done(vs));
                },
                _ => {},
            },
            _ => {},
        }
    } else if n > 0 {
        assert(eval_args(p, 1, env, rw_args(rw, es), i) == ResSeq::Done(Seq::<Val>::empty()));
    }
}

/// fold の本体：源の畳み込みが v を返すなら、写しの畳み込みも v に評価される。
proof fn sim_fold(xp: XProg, p: Prog, rw: spec_fn(XExpr) -> Expr, n: nat, env: Map<nat, Val>, acc: nat, item: nat, body: XExpr, items: Seq<Val>, j: nat, a: Val, v: Val)
    requires
        sim_ok(xp, p, rw),
        xeval_fold(xp, n, env, acc, item, body, items, j, a) == Res::Done(v),
    ensures
        fold_to(p, env, acc, item, rw(body), items, j, a, v),
    decreases n, 0nat,
{
    if n > 0 && j < items.len() {
        let f = (n - 1) as nat;
        let env2 = env.insert(acc, a).insert(item, items[j as int]);
        match xeval(xp, f, env2, body) {
            Res::Done(v1) => {
                sim_expr(xp, p, rw, f, env2, body, v1);
                sim_fold(xp, p, rw, f, env, acc, item, body, items, j + 1, v1, v);
                let m1 = choose|m: nat| #[trigger] eval(p, m, env2, rw(body)) == Res::Done(v1);
                let m2 = choose|m: nat| #[trigger] eval_fold(p, m, env, acc, item, rw(body), items, j + 1, v1) == Res::Done(v);
                let mm = (max(m1, m2) + 1) as nat;
                mono(p, m1, (mm - 1) as nat, env2, rw(body));
                mono_fold(p, m2, (mm - 1) as nat, env, acc, item, rw(body), items, j + 1, v1);
                assert(eval_fold(p, mm, env, acc, item, rw(body), items, j, a) == Res::Done(v));
            },
            _ => {},
        }
    } else if n > 0 {
        assert(eval_fold(p, 1, env, acc, item, rw(body), items, j, a) == Res::Done(a));
    }
}

/// map の列：源の xmap が vs を返すなら、各要素の本体の写しは対応する値に評価される。
proof fn sim_xmap(xp: XProg, p: Prog, rw: spec_fn(XExpr) -> Expr, n: nat, env: Map<nat, Val>, x: nat, c: XExpr, items: Seq<Val>, j: nat, vs: Seq<Val>)
    requires
        sim_ok(xp, p, rw),
        j <= items.len(),
        xmap(xp, n, env, x, c, items, j) == ResSeq::Done(vs),
    ensures
        map_ok(p, rw, env, x, c, items, vs, j),
    decreases n, 0nat,
{
    if n > 0 && j < items.len() {
        let f = (n - 1) as nat;
        let env2 = env.insert(x, items[j as int]);
        match xeval(xp, f, env2, c) {
            Res::Done(v) => match xmap(xp, f, env, x, c, items, j + 1) {
                ResSeq::Done(vs2) => {
                    sim_expr(xp, p, rw, f, env2, c, v);
                    sim_xmap(xp, p, rw, f, env, x, c, items, j + 1, vs2);
                    assert(vs == seq![v] + vs2);
                    assert forall|k: int| j <= k < items.len() implies evals_to(
                        p,
                        #[trigger] env.insert(x, items[k]),
                        rw(c),
                        vs[k - (j as int)],
                    ) by {
                        if k == j as int {
                            assert(vs[k - (j as int)] == v);
                        } else {
                            assert(vs[k - (j as int)] == vs2[k - ((j + 1) as int)]);
                        }
                    }
                    assert(map_ok(p, rw, env, x, c, items, vs, j));
                },
                _ => {},
            },
            _ => {},
        }
    } else if n > 0 {
        assert(map_ok(p, rw, env, x, c, items, vs, j));
    }
}

/// filter の列：源の xfilter が out を返すなら、述語の値の列 keep があり、out は kept_from に等しい。
proof fn sim_filter(xp: XProg, p: Prog, rw: spec_fn(XExpr) -> Expr, n: nat, env: Map<nat, Val>, x: nat, c: XExpr, items: Seq<Val>, j: nat, out: Seq<Val>)
    requires
        sim_ok(xp, p, rw),
        j <= items.len(),
        xfilter(xp, n, env, x, c, items, j) == ResSeq::Done(out),
    ensures
        exists|keep: Seq<bool>| #[trigger] filter_keep(p, rw, env, x, c, items, keep, out, j),
    decreases n, 0nat,
{
    reveal_with_fuel(kept_from, 1);
    if n > 0 && j < items.len() {
        let f = (n - 1) as nat;
        let env2 = env.insert(x, items[j as int]);
        match xeval(xp, f, env2, c) {
            Res::Done(Val::Bool(b)) => match xfilter(xp, f, env, x, c, items, j + 1) {
                ResSeq::Done(vs2) => {
                    sim_expr(xp, p, rw, f, env2, c, Val::Bool(b));
                    sim_filter(xp, p, rw, f, env, x, c, items, j + 1, vs2);
                    let keep2 = choose|keep: Seq<bool>| #[trigger] filter_keep(p, rw, env, x, c, items, keep, vs2, j + 1);
                    let keep = keep2.update(j as int, b);
                    kept_from_congr(items, keep2, keep, j + 1);
                    assert forall|k: int| j <= k < items.len() implies evals_to(p, #[trigger] env.insert(x, items[k]), rw(c), Val::Bool(keep[k])) by {
                        if k != j as int {
                            assert(j + 1 <= k);
                            assert(keep[k] == keep2[k]);
                        }
                    }
                    assert(filter_keep(p, rw, env, x, c, items, keep, out, j));
                },
                _ => {},
            },
            _ => {},
        }
    } else if n > 0 {
        let keep = Seq::new(items.len(), |k: int| false);
        assert(filter_keep(p, rw, env, x, c, items, keep, out, j));
    }
}

/// any の列：源の xany が out を返すなら、止まる位置 stop がある。
proof fn sim_any(xp: XProg, p: Prog, rw: spec_fn(XExpr) -> Expr, n: nat, env: Map<nat, Val>, x: nat, c: XExpr, items: Seq<Val>, j: nat, out: Val)
    requires
        sim_ok(xp, p, rw),
        j <= items.len(),
        xany(xp, n, env, x, c, items, j) == Res::Done(out),
    ensures
        exists|stop: nat| #[trigger] any_stop(p, rw, env, x, c, items, j, stop, out),
    decreases n, 0nat,
{
    if n > 0 && j < items.len() {
        let f = (n - 1) as nat;
        let env2 = env.insert(x, items[j as int]);
        match xeval(xp, f, env2, c) {
            Res::Done(Val::Bool(true)) => {
                sim_expr(xp, p, rw, f, env2, c, Val::Bool(true));
                assert(any_stop(p, rw, env, x, c, items, j, j, out));
            },
            Res::Done(Val::Bool(false)) => {
                sim_expr(xp, p, rw, f, env2, c, Val::Bool(false));
                sim_any(xp, p, rw, f, env, x, c, items, j + 1, out);
                let stop = choose|s: nat| #[trigger] any_stop(p, rw, env, x, c, items, j + 1, s, out);
                assert forall|k: int| j <= k < stop implies evals_to(p, #[trigger] env.insert(x, items[k]), rw(c), Val::Bool(false)) by {
                    if k != j as int {
                        assert(j + 1 <= k);
                    }
                }
                assert(any_stop(p, rw, env, x, c, items, j, stop, out));
            },
            _ => {},
        }
    } else if n > 0 {
        assert(any_stop(p, rw, env, x, c, items, j, j, out));
    }
}

/// all の列。
proof fn sim_all(xp: XProg, p: Prog, rw: spec_fn(XExpr) -> Expr, n: nat, env: Map<nat, Val>, x: nat, c: XExpr, items: Seq<Val>, j: nat, out: Val)
    requires
        sim_ok(xp, p, rw),
        j <= items.len(),
        xall(xp, n, env, x, c, items, j) == Res::Done(out),
    ensures
        exists|stop: nat| #[trigger] all_stop(p, rw, env, x, c, items, j, stop, out),
    decreases n, 0nat,
{
    if n > 0 && j < items.len() {
        let f = (n - 1) as nat;
        let env2 = env.insert(x, items[j as int]);
        match xeval(xp, f, env2, c) {
            Res::Done(Val::Bool(false)) => {
                sim_expr(xp, p, rw, f, env2, c, Val::Bool(false));
                assert(all_stop(p, rw, env, x, c, items, j, j, out));
            },
            Res::Done(Val::Bool(true)) => {
                sim_expr(xp, p, rw, f, env2, c, Val::Bool(true));
                sim_all(xp, p, rw, f, env, x, c, items, j + 1, out);
                let stop = choose|s: nat| #[trigger] all_stop(p, rw, env, x, c, items, j + 1, s, out);
                assert forall|k: int| j <= k < stop implies evals_to(p, #[trigger] env.insert(x, items[k]), rw(c), Val::Bool(true)) by {
                    if k != j as int {
                        assert(j + 1 <= k);
                    }
                }
                assert(all_stop(p, rw, env, x, c, items, j, stop, out));
            },
            _ => {},
        }
    } else if n > 0 {
        assert(all_stop(p, rw, env, x, c, items, j, j, out));
    }
}

/// find の列。
proof fn sim_find(xp: XProg, p: Prog, rw: spec_fn(XExpr) -> Expr, n: nat, env: Map<nat, Val>, x: nat, c: XExpr, items: Seq<Val>, j: nat, out: Val)
    requires
        sim_ok(xp, p, rw),
        j <= items.len(),
        xfind(xp, n, env, x, c, items, j) == Res::Done(out),
    ensures
        exists|stop: nat| #[trigger] find_stop(p, rw, env, x, c, items, j, stop, out),
    decreases n, 0nat,
{
    if n > 0 && j < items.len() {
        let f = (n - 1) as nat;
        let env2 = env.insert(x, items[j as int]);
        match xeval(xp, f, env2, c) {
            Res::Done(Val::Bool(true)) => {
                sim_expr(xp, p, rw, f, env2, c, Val::Bool(true));
                assert(find_stop(p, rw, env, x, c, items, j, j, out));
            },
            Res::Done(Val::Bool(false)) => {
                sim_expr(xp, p, rw, f, env2, c, Val::Bool(false));
                sim_find(xp, p, rw, f, env, x, c, items, j + 1, out);
                let stop = choose|s: nat| #[trigger] find_stop(p, rw, env, x, c, items, j + 1, s, out);
                assert forall|k: int| j <= k < stop implies evals_to(p, #[trigger] env.insert(x, items[k]), rw(c), Val::Bool(false)) by {
                    if k != j as int {
                        assert(j + 1 <= k);
                    }
                }
                assert(find_stop(p, rw, env, x, c, items, j, stop, out));
            },
            _ => {},
        }
    } else if n > 0 {
        assert(find_stop(p, rw, env, x, c, items, j, j, out));
    }
}

// ------------------------------------------------------------------ 式の模擬（燃料で帰納）

/// 式の模擬：源の式が燃料 n で値 v に評価されるなら、写しは v に評価される。
pub proof fn sim_expr(xp: XProg, p: Prog, rw: spec_fn(XExpr) -> Expr, n: nat, env: Map<nat, Val>, e: XExpr, v: Val)
    requires
        sim_ok(xp, p, rw),
        xeval(xp, n, env, e) == Res::Done(v),
    ensures
        evals_to(p, env, rw(e), v),
    decreases n, 1nat,
{
    if n == 0 {
        assert(xeval(xp, 0, env, e) == Res::OutOfFuel);
    } else {
        let f = (n - 1) as nat;
        match e {
            XExpr::Int(c) => {
                assert(rw(e) == Expr::Int(c));
                bs_leaf(p, env, Expr::Int(c));
            },
            XExpr::Bool(b) => {
                assert(rw(e) == Expr::Bool(b));
                bs_leaf(p, env, Expr::Bool(b));
            },
            XExpr::Unit => {
                assert(rw(e) == Expr::Unit);
                bs_leaf(p, env, Expr::Unit);
            },
            XExpr::Char(c) => {
                assert(rw(e) == Expr::Char(c));
                bs_leaf(p, env, Expr::Char(c));
            },
            XExpr::Var(x) => {
                assert(env.contains_key(x));
                assert(rw(e) == Expr::Var(x));
                bs_var(p, env, x);
                assert(v == env[x]);
            },
            XExpr::None(t) => {
                assert(rw(e) == Expr::None(erase_ty(t)));
                bs_leaf(p, env, Expr::None(erase_ty(t)));
            },
            XExpr::List(t, es) => match xeval_args(xp, f, env, es, 0) {
                ResSeq::Done(vs) => {
                    sim_args(xp, p, rw, f, env, es, 0, vs);
                    assert(rw(e) == Expr::List(erase_ty(t), rw_args(rw, es)));
                    bs_list(p, env, erase_ty(t), rw_args(rw, es), vs);
                },
                _ => {},
            },
            XExpr::Some(a) => match xeval(xp, f, env, *a) {
                Res::Done(va) => {
                    sim_expr(xp, p, rw, f, env, *a, va);
                    assert(rw(e) == Expr::Some(Box::new(rw(*a))));
                    bs_some(p, env, rw(*a), va);
                },
                _ => {},
            },
            XExpr::Pair(a, b) => match xeval(xp, f, env, *a) {
                Res::Done(va) => match xeval(xp, f, env, *b) {
                    Res::Done(vb) => {
                        sim_expr(xp, p, rw, f, env, *a, va);
                        sim_expr(xp, p, rw, f, env, *b, vb);
                        assert(rw(e) == Expr::Pair(Box::new(rw(*a)), Box::new(rw(*b))));
                        bs_pair(p, env, rw(*a), rw(*b), va, vb);
                    },
                    _ => {},
                },
                _ => {},
            },
            XExpr::Builtin(bi, es) => match xeval_args(xp, f, env, es, 0) {
                ResSeq::Done(vs) => {
                    sim_args(xp, p, rw, f, env, es, 0, vs);
                    assert(rw(e) == Expr::Builtin(bi, rw_args(rw, es)));
                    bs_builtin(p, env, bi, rw_args(rw, es), vs, v);
                },
                _ => {},
            },
            XExpr::Call(g, es) => match xeval_args(xp, f, env, es, 0) {
                ResSeq::Done(vs) => {
                    if g < xp.funcs.len() && vs.len() == xp.funcs[g as int].params.len() {
                        let env2 = bind(xp.funcs[g as int].params, vs, vs.len());
                        sim_expr(xp, p, rw, f, env2, xp.funcs[g as int].body, v);
                        sim_args(xp, p, rw, f, env, es, 0, vs);
                        assert(erase_sig(xp.funcs[g as int], p.funcs[g as int]));
                        bind_names_eq(p.funcs[g as int].params, xp.funcs[g as int].params, vs, vs.len());
                        assert(p.funcs[g as int].body == rw(xp.funcs[g as int].body));
                        assert(rw(e) == Expr::Call(g, rw_args(rw, es)));
                        bs_call(p, env, g, rw_args(rw, es), vs, v);
                    }
                },
                _ => {},
            },
            XExpr::Let(x, a, b) => match xeval(xp, f, env, *a) {
                Res::Done(va) => {
                    sim_expr(xp, p, rw, f, env, *a, va);
                    sim_expr(xp, p, rw, f, env.insert(x, va), *b, v);
                    assert(rw(e) == Expr::Let(x, Box::new(rw(*a)), Box::new(rw(*b))));
                    bs_let(p, env, x, rw(*a), rw(*b), va, v);
                },
                _ => {},
            },
            XExpr::If(c, a, b) => match xeval(xp, f, env, *c) {
                Res::Done(Val::Bool(cv)) => {
                    sim_expr(xp, p, rw, f, env, *c, Val::Bool(cv));
                    if cv {
                        sim_expr(xp, p, rw, f, env, *a, v);
                    } else {
                        sim_expr(xp, p, rw, f, env, *b, v);
                    }
                    assert(rw(e) == Expr::If(Box::new(rw(*c)), Box::new(rw(*a)), Box::new(rw(*b))));
                    bs_if(p, env, rw(*c), rw(*a), rw(*b), cv, v);
                },
                _ => {},
            },
            XExpr::Fold(xs, init, acc, item, body) => match xeval(xp, f, env, *xs) {
                Res::Done(Val::List(s)) => match xeval(xp, f, env, *init) {
                    Res::Done(v0) => {
                        sim_expr(xp, p, rw, f, env, *xs, Val::List(s));
                        sim_expr(xp, p, rw, f, env, *init, v0);
                        sim_fold(xp, p, rw, f, env, acc, item, *body, s, 0, v0, v);
                        assert(rw(e) == Expr::Fold(Box::new(rw(*xs)), Box::new(rw(*init)), acc, item, Box::new(rw(*body))));
                        bs_fold(p, env, rw(*xs), rw(*init), acc, item, rw(*body), s, v0, v);
                    },
                    _ => {},
                },
                _ => {},
            },
            XExpr::Match(m, nb, x, sm) => match xeval(xp, f, env, *m) {
                Res::Done(Val::None) => {
                    sim_expr(xp, p, rw, f, env, *m, Val::None);
                    sim_expr(xp, p, rw, f, env, *nb, v);
                    assert(rw(e) == Expr::Match(Box::new(rw(*m)), Box::new(rw(*nb)), x, Box::new(rw(*sm))));
                    bs_match(p, env, rw(*m), rw(*nb), x, rw(*sm), Val::None, v);
                },
                Res::Done(Val::Some(w)) => {
                    sim_expr(xp, p, rw, f, env, *m, Val::Some(w));
                    sim_expr(xp, p, rw, f, env.insert(x, *w), *sm, v);
                    assert(rw(e) == Expr::Match(Box::new(rw(*m)), Box::new(rw(*nb)), x, Box::new(rw(*sm))));
                    bs_match(p, env, rw(*m), rw(*nb), x, rw(*sm), Val::Some(w), v);
                },
                _ => {},
            },
            XExpr::Inj(ok, t, u, a) => match xeval(xp, f, env, *a) {
                Res::Done(va) => {
                    sim_expr(xp, p, rw, f, env, *a, va);
                    assert(rw(e) == Expr::Inj(ok, erase_ty(t), erase_ty(u), Box::new(rw(*a))));
                    bs_inj(p, env, ok, erase_ty(t), erase_ty(u), rw(*a), va);
                    assert(v == inj_val(ok, va));
                },
                _ => {},
            },
            XExpr::MatchR(m, x, a, y, b) => match xeval(xp, f, env, *m) {
                Res::Done(Val::Ok(w)) => {
                    sim_expr(xp, p, rw, f, env, *m, Val::Ok(w));
                    sim_expr(xp, p, rw, f, env.insert(x, *w), *a, v);
                    assert(rw(e) == Expr::MatchR(Box::new(rw(*m)), x, Box::new(rw(*a)), y, Box::new(rw(*b))));
                    bs_matchr(p, env, rw(*m), x, rw(*a), y, rw(*b), Val::Ok(w), v);
                },
                Res::Done(Val::Err(w)) => {
                    sim_expr(xp, p, rw, f, env, *m, Val::Err(w));
                    sim_expr(xp, p, rw, f, env.insert(y, *w), *b, v);
                    assert(rw(e) == Expr::MatchR(Box::new(rw(*m)), x, Box::new(rw(*a)), y, Box::new(rw(*b))));
                    bs_matchr(p, env, rw(*m), x, rw(*a), y, rw(*b), Val::Err(w), v);
                },
                _ => {},
            },
            XExpr::Map(_, _, _) => sim_map_node(xp, p, rw, n, env, e, v),
            XExpr::Filter(_, _, _) => sim_filter_node(xp, p, rw, n, env, e, v),
            XExpr::Any(_, _, _) => sim_any_node(xp, p, rw, n, env, e, v),
            XExpr::All(_, _, _) => sim_all_node(xp, p, rw, n, env, e, v),
            XExpr::Find(_, _, _) => sim_find_node(xp, p, rw, n, env, e, v),
            XExpr::SortBy(_, _, _) => sim_sort_node(xp, p, rw, n, env, e, v),
        }
    }
}

// hof の形：子を模擬し、列の補題と仮定 ob で結ぶ。帰納の順は (n, 0)（式の模擬は (n, 1)）。

proof fn sim_map_node(xp: XProg, p: Prog, rw: spec_fn(XExpr) -> Expr, n: nat, env: Map<nat, Val>, e: XExpr, v: Val)
    requires
        sim_ok(xp, p, rw),
        e is Map,
        xeval(xp, n, env, e) == Res::Done(v),
    ensures
        evals_to(p, env, rw(e), v),
    decreases n, 0nat,
{
    if n > 0 {
        let f = (n - 1) as nat;
        match e {
            XExpr::Map(xs, x, c) => match xeval(xp, f, env, *xs) {
                Res::Done(Val::List(items)) => match xmap(xp, f, env, x, *c, items, 0) {
                    ResSeq::Done(vs) => {
                        sim_expr(xp, p, rw, f, env, *xs, Val::List(items));
                        sim_xmap(xp, p, rw, f, env, x, *c, items, 0, vs);
                        use_ob_map(p, rw, env, *xs, x, *c, items, vs);
                        assert(v == Val::List(vs));
                    },
                    _ => {},
                },
                _ => {},
            },
            _ => {},
        }
    }
}

proof fn sim_filter_node(xp: XProg, p: Prog, rw: spec_fn(XExpr) -> Expr, n: nat, env: Map<nat, Val>, e: XExpr, v: Val)
    requires
        sim_ok(xp, p, rw),
        e is Filter,
        xeval(xp, n, env, e) == Res::Done(v),
    ensures
        evals_to(p, env, rw(e), v),
    decreases n, 0nat,
{
    if n > 0 {
        let f = (n - 1) as nat;
        match e {
            XExpr::Filter(xs, x, c) => match xeval(xp, f, env, *xs) {
                Res::Done(Val::List(items)) => match xfilter(xp, f, env, x, *c, items, 0) {
                    ResSeq::Done(out) => {
                        sim_expr(xp, p, rw, f, env, *xs, Val::List(items));
                        sim_filter(xp, p, rw, f, env, x, *c, items, 0, out);
                        let keep = choose|keep: Seq<bool>| #[trigger] filter_keep(p, rw, env, x, *c, items, keep, out, 0);
                        use_ob_filter(p, rw, env, *xs, x, *c, items, keep, out);
                        assert(v == Val::List(out));
                    },
                    _ => {},
                },
                _ => {},
            },
            _ => {},
        }
    }
}

proof fn sim_any_node(xp: XProg, p: Prog, rw: spec_fn(XExpr) -> Expr, n: nat, env: Map<nat, Val>, e: XExpr, v: Val)
    requires
        sim_ok(xp, p, rw),
        e is Any,
        xeval(xp, n, env, e) == Res::Done(v),
    ensures
        evals_to(p, env, rw(e), v),
    decreases n, 0nat,
{
    if n > 0 {
        let f = (n - 1) as nat;
        match e {
            XExpr::Any(xs, x, c) => match xeval(xp, f, env, *xs) {
                Res::Done(Val::List(items)) => {
                    sim_expr(xp, p, rw, f, env, *xs, Val::List(items));
                    sim_any(xp, p, rw, f, env, x, *c, items, 0, v);
                    let stop = choose|s: nat| #[trigger] any_stop(p, rw, env, x, *c, items, 0, s, v);
                    use_ob_any(p, rw, env, *xs, x, *c, items, stop, v);
                },
                _ => {},
            },
            _ => {},
        }
    }
}

proof fn sim_all_node(xp: XProg, p: Prog, rw: spec_fn(XExpr) -> Expr, n: nat, env: Map<nat, Val>, e: XExpr, v: Val)
    requires
        sim_ok(xp, p, rw),
        e is All,
        xeval(xp, n, env, e) == Res::Done(v),
    ensures
        evals_to(p, env, rw(e), v),
    decreases n, 0nat,
{
    if n > 0 {
        let f = (n - 1) as nat;
        match e {
            XExpr::All(xs, x, c) => match xeval(xp, f, env, *xs) {
                Res::Done(Val::List(items)) => {
                    sim_expr(xp, p, rw, f, env, *xs, Val::List(items));
                    sim_all(xp, p, rw, f, env, x, *c, items, 0, v);
                    let stop = choose|s: nat| #[trigger] all_stop(p, rw, env, x, *c, items, 0, s, v);
                    use_ob_all(p, rw, env, *xs, x, *c, items, stop, v);
                },
                _ => {},
            },
            _ => {},
        }
    }
}

proof fn sim_find_node(xp: XProg, p: Prog, rw: spec_fn(XExpr) -> Expr, n: nat, env: Map<nat, Val>, e: XExpr, v: Val)
    requires
        sim_ok(xp, p, rw),
        e is Find,
        xeval(xp, n, env, e) == Res::Done(v),
    ensures
        evals_to(p, env, rw(e), v),
    decreases n, 0nat,
{
    if n > 0 {
        let f = (n - 1) as nat;
        match e {
            XExpr::Find(xs, x, c) => match xeval(xp, f, env, *xs) {
                Res::Done(Val::List(items)) => {
                    sim_expr(xp, p, rw, f, env, *xs, Val::List(items));
                    sim_find(xp, p, rw, f, env, x, *c, items, 0, v);
                    let stop = choose|s: nat| #[trigger] find_stop(p, rw, env, x, *c, items, 0, s, v);
                    use_ob_find(p, rw, env, *xs, x, *c, items, stop, v);
                },
                _ => {},
            },
            _ => {},
        }
    }
}

proof fn sim_sort_node(xp: XProg, p: Prog, rw: spec_fn(XExpr) -> Expr, n: nat, env: Map<nat, Val>, e: XExpr, v: Val)
    requires
        sim_ok(xp, p, rw),
        e is SortBy,
        xeval(xp, n, env, e) == Res::Done(v),
    ensures
        evals_to(p, env, rw(e), v),
    decreases n, 0nat,
{
    if n > 0 {
        let f = (n - 1) as nat;
        match e {
            XExpr::SortBy(xs, x, k) => match xeval(xp, f, env, *xs) {
                Res::Done(Val::List(items)) => match xmap(xp, f, env, x, *k, items, 0) {
                    ResSeq::Done(kv) => match int_seq(kv) {
                        Some(keys) => {
                            sim_expr(xp, p, rw, f, env, *xs, Val::List(items));
                            sim_xmap(xp, p, rw, f, env, x, *k, items, 0, kv);
                            use_ob_sort_by(p, rw, env, *xs, x, *k, items, kv, keys);
                            assert(v == Val::List(sort_vals(items, keys)));
                        },
                        None => {},
                    },
                    _ => {},
                },
                _ => {},
            },
            _ => {},
        }
    }
}

// ------------------------------------------------------------------ 主の定理

/// SH4 の主張：源の entry が燃料 n で w を返すなら、書換え後の entry は w を返す（燃料の存在）。
/// 書換え後の非 OutOfFuel の結果はすべて w に等しい（決定性）。
pub proof fn sh4_same_value(xp: XProg, p: Prog, rw: spec_fn(XExpr) -> Expr, n: nat, v: Val, w: Val)
    requires
        sim_ok(xp, p, rw),
        xp.entry < xp.funcs.len(),
        xeval_entry(xp, n, v) == Res::Done(w),
    ensures
        exists|m: nat| #[trigger] eval_entry(p, m, v) == Res::Done(w),
        forall|m: nat| !(#[trigger] eval_entry(p, m, v) is OutOfFuel) ==> eval_entry(p, m, v) == Res::Done(w),
{
    let fx = xp.funcs[xp.entry as int];
    let fp = p.funcs[p.entry as int];
    assert(erase_sig(xp.funcs[xp.entry as int], p.funcs[p.entry as int]));
    bind_names_eq(fp.params, fx.params, seq![v], 1);
    assert(fp.body == rw(fx.body));
    assert(xeval(xp, n, bind(fx.params, seq![v], 1), fx.body) == Res::Done(w));
    sim_expr(xp, p, rw, n, bind(fx.params, seq![v], 1), fx.body, w);
    let m0 = choose|m: nat| #[trigger] eval(p, m, bind(fp.params, seq![v], 1), fp.body) == Res::Done(w);
    assert(eval_entry(p, m0, v) == Res::Done(w));
    assert forall|m: nat| !(#[trigger] eval_entry(p, m, v) is OutOfFuel) implies eval_entry(p, m, v) == Res::Done(w) by {
        entry_deterministic(p, m, m0, v);
    }
}

/// 呼出しの型付けは署名の消去と一致する（ランクの条件は源と同じ証明書による）。
pub proof fn call_typing_erased(
    xp: XProg,
    p: Prog,
    rw: spec_fn(XExpr) -> Expr,
    r: nat,
    ctx: Map<nat, Ty>,
    g: nat,
    es: Seq<Expr>,
    ts: Seq<Ty>,
)
    requires
        sim_prog(xp, p, rw),
        wf(p),
        g < xp.funcs.len(),
        p.rank[g as int] < r || p.rec[g as int],
        ty_args(p, r, ctx, es, 0) == Some(ts),
        ts.len() == xp.funcs[g as int].params.len(),
        forall|k: int| 0 <= k < ts.len() ==> ts[k] == erase_ty(xp.funcs[g as int].params[k].1),
    ensures
        ty_expr(p, r, ctx, Expr::Call(g, es)) == Some(erase_ty(xp.funcs[g as int].ret)),
{
    assert(erase_sig(xp.funcs[g as int], p.funcs[g as int]));
}

/// 入力の型は署名の消去で変わらない（entry の一引数）。
pub proof fn entry_input_erased(xp: XProg, p: Prog, rw: spec_fn(XExpr) -> Expr, v: Val)
    requires
        sim_prog(xp, p, rw),
        xp.entry < xp.funcs.len(),
        xp.funcs[xp.entry as int].params.len() == 1,
        val_type(v, erase_ty(xp.funcs[xp.entry as int].params[0].1)),
    ensures
        p.entry < p.funcs.len(),
        val_type(v, p.funcs[p.entry as int].params[0].1),
{
    assert(erase_sig(xp.funcs[xp.entry as int], p.funcs[p.entry as int]));
}

/// 整形式の書換え後のプログラムは、その入力で停止する（ランクの証明書を使う。entry_total）。
pub proof fn sh4_total_target(p: Prog, v: Val)
    requires
        wf(p),
        no_rec(p),
        val_type(v, p.funcs[p.entry as int].params[0].1),
    ensures
        exists|m: nat, w: Val|
            #![trigger eval_entry(p, m, v), val_type(w, p.funcs[p.entry as int].ret)]
            eval_entry(p, m, v) == Res::Done(w) && val_type(w, p.funcs[p.entry as int].ret),
{
    entry_total(p, v);
}

} // verus!
