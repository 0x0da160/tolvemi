//! SH4 の逆向き（段階 0）：型の付いたプログラムでは、書換え後の値は源の値に等しい。
//! 主張（`sh4_back_typed`）：書換え後の入口が燃料 m で w を返すなら、源の入口は十分大きい燃料で w を返す。
//! 証明は書換え後の評価の燃料についての帰納（`back_expr`）。各形で、書換え後の評価の分解から源の評価を組み立てる。
//! 源の評価は閾値（`xat`：燃料 n0 以上で同じ値を返す）の形で表す。閾値は和と一つ足すことで合成する。
//! 畳み込みの形（fold・map・filter・any・all・find・sort_by）は、要素ごとの帰納（`fold_back` など）で閾値を集める。
//! sort_by は、外側の畳み込みの段ごとに鍵の値と閾値を集め、整列の意味（`sort_core_meaning`）で結果を定める。
//! 整列の鍵だけは、評価が存在する（evals_to）の形で整列の意味の補題に渡す。結果の一致は評価の決定性で示す（`evals_to_done_eq`）。
//! 型は、書換え後の式の型付け（ty_expr）と型保存（sound）から、要素・述語・鍵の型を取り出す。

use crate::bigstep::*;
use crate::fold_meaning::*;
use crate::proof::*;
use crate::records_proof::*;
use crate::sh6_obligations::*;
use crate::sh6_safe::*;
use crate::simulation::*;
use crate::sortmeaning::*;
use crate::sortspec::*;
use crate::spec::*;
use crate::xmeaning::*;
use crate::xsem::*;
use crate::xtyping::*;
use vstd::prelude::*;

verus! {

// ------------------------------------------------------------------ 源の閾値（ある燃料以上で先ず値になる）

/// 源の式 e は、燃料 n0 以上でずっと値 v に評価される。
pub open spec fn xat(xp: XProg, env: Map<nat, Val>, e: XExpr, v: Val, n0: nat) -> bool {
    forall|n: nat| n >= n0 ==> #[trigger] xeval(xp, n, env, e) == Res::Done(v)
}

/// 源の引数列 es[i..] は、燃料 n0 以上でずっと vs に評価される。
pub open spec fn xat_args(xp: XProg, env: Map<nat, Val>, es: Seq<XExpr>, i: nat, vs: Seq<Val>, n0: nat) -> bool {
    forall|n: nat| n >= n0 ==> #[trigger] xeval_args(xp, n, env, es, i) == ResSeq::Done(vs)
}

/// 束縛の除去：acc が e に現れなければ、acc を外した環境で同じ評価になる（item は残す）。
proof fn eval_drop(p: Prog, n: nat, env: Map<nat, Val>, acc: nat, a: Val, item: nat, u: Val, e: Expr)
    requires
        absent(acc, e),
        acc != item,
    ensures
        eval(p, n, env.insert(acc, a).insert(item, u), e) == eval(p, n, env.insert(item, u), e),
{
    eval_absent(p, n, env.insert(item, u), e, acc, a);
    assert(env.insert(item, u).insert(acc, a) =~= env.insert(acc, a).insert(item, u));
}

// ------------------------------------------------------------------ 源の一段の補題（xeval を具体的な形で一段開く）

proof fn xs_int(xp: XProg, n: nat, env: Map<nat, Val>, c: int)
    requires
        n >= 1,
    ensures
        xeval(xp, n, env, XExpr::Int(c)) == Res::Done(Val::Int(c)),
{
    reveal_with_fuel(xeval, 1);
}

proof fn xs_bool(xp: XProg, n: nat, env: Map<nat, Val>, b: bool)
    requires
        n >= 1,
    ensures
        xeval(xp, n, env, XExpr::Bool(b)) == Res::Done(Val::Bool(b)),
{
    reveal_with_fuel(xeval, 1);
}

proof fn xs_unit(xp: XProg, n: nat, env: Map<nat, Val>)
    requires
        n >= 1,
    ensures
        xeval(xp, n, env, XExpr::Unit) == Res::Done(Val::Unit),
{
    reveal_with_fuel(xeval, 1);
}

proof fn xs_char(xp: XProg, n: nat, env: Map<nat, Val>, c: int)
    requires
        n >= 1,
    ensures
        xeval(xp, n, env, XExpr::Char(c)) == Res::Done(Val::Char(c)),
{
    reveal_with_fuel(xeval, 1);
}

proof fn xs_none(xp: XProg, n: nat, env: Map<nat, Val>, t: Ty)
    requires
        n >= 1,
    ensures
        xeval(xp, n, env, XExpr::None(t)) == Res::Done(Val::None),
{
    reveal_with_fuel(xeval, 1);
}

proof fn xs_var(xp: XProg, n: nat, env: Map<nat, Val>, x: nat)
    requires
        n >= 1,
        env.contains_key(x),
    ensures
        xeval(xp, n, env, XExpr::Var(x)) == Res::Done(env[x]),
{
    reveal_with_fuel(xeval, 1);
}

proof fn xs_pair(xp: XProg, n: nat, env: Map<nat, Val>, a: XExpr, b: XExpr, va: Val, vb: Val)
    requires
        n >= 1,
        xeval(xp, (n - 1) as nat, env, a) == Res::Done(va),
        xeval(xp, (n - 1) as nat, env, b) == Res::Done(vb),
    ensures
        xeval(xp, n, env, XExpr::Pair(Box::new(a), Box::new(b))) == Res::Done(Val::Pair(Box::new(va), Box::new(vb))),
{
    reveal_with_fuel(xeval, 1);
}

proof fn xs_some(xp: XProg, n: nat, env: Map<nat, Val>, a: XExpr, va: Val)
    requires
        n >= 1,
        xeval(xp, (n - 1) as nat, env, a) == Res::Done(va),
    ensures
        xeval(xp, n, env, XExpr::Some(Box::new(a))) == Res::Done(Val::Some(Box::new(va))),
{
    reveal_with_fuel(xeval, 1);
}

proof fn xs_inj(xp: XProg, n: nat, env: Map<nat, Val>, ok: bool, t: Ty, u: Ty, a: XExpr, va: Val)
    requires
        n >= 1,
        xeval(xp, (n - 1) as nat, env, a) == Res::Done(va),
    ensures
        xeval(xp, n, env, XExpr::Inj(ok, t, u, Box::new(a))) == Res::Done(inj_val(ok, va)),
{
    reveal_with_fuel(xeval, 1);
}

proof fn xs_let(xp: XProg, n: nat, env: Map<nat, Val>, x: nat, a: XExpr, b: XExpr, va: Val, v: Val)
    requires
        n >= 1,
        xeval(xp, (n - 1) as nat, env, a) == Res::Done(va),
        xeval(xp, (n - 1) as nat, env.insert(x, va), b) == Res::Done(v),
    ensures
        xeval(xp, n, env, XExpr::Let(x, Box::new(a), Box::new(b))) == Res::Done(v),
{
    reveal_with_fuel(xeval, 1);
}

proof fn xs_if_true(xp: XProg, n: nat, env: Map<nat, Val>, c: XExpr, a: XExpr, b: XExpr, v: Val)
    requires
        n >= 1,
        xeval(xp, (n - 1) as nat, env, c) == Res::Done(Val::Bool(true)),
        xeval(xp, (n - 1) as nat, env, a) == Res::Done(v),
    ensures
        xeval(xp, n, env, XExpr::If(Box::new(c), Box::new(a), Box::new(b))) == Res::Done(v),
{
    reveal_with_fuel(xeval, 1);
}

proof fn xs_if_false(xp: XProg, n: nat, env: Map<nat, Val>, c: XExpr, a: XExpr, b: XExpr, v: Val)
    requires
        n >= 1,
        xeval(xp, (n - 1) as nat, env, c) == Res::Done(Val::Bool(false)),
        xeval(xp, (n - 1) as nat, env, b) == Res::Done(v),
    ensures
        xeval(xp, n, env, XExpr::If(Box::new(c), Box::new(a), Box::new(b))) == Res::Done(v),
{
    reveal_with_fuel(xeval, 1);
}

proof fn xs_match_none(xp: XProg, n: nat, env: Map<nat, Val>, mm: XExpr, nb: XExpr, x: nat, sm: XExpr, v: Val)
    requires
        n >= 1,
        xeval(xp, (n - 1) as nat, env, mm) == Res::Done(Val::None),
        xeval(xp, (n - 1) as nat, env, nb) == Res::Done(v),
    ensures
        xeval(xp, n, env, XExpr::Match(Box::new(mm), Box::new(nb), x, Box::new(sm))) == Res::Done(v),
{
    reveal_with_fuel(xeval, 1);
}

proof fn xs_match_some(xp: XProg, n: nat, env: Map<nat, Val>, mm: XExpr, nb: XExpr, x: nat, sm: XExpr, w: Val, v: Val)
    requires
        n >= 1,
        xeval(xp, (n - 1) as nat, env, mm) == Res::Done(Val::Some(Box::new(w))),
        xeval(xp, (n - 1) as nat, env.insert(x, w), sm) == Res::Done(v),
    ensures
        xeval(xp, n, env, XExpr::Match(Box::new(mm), Box::new(nb), x, Box::new(sm))) == Res::Done(v),
{
    reveal_with_fuel(xeval, 1);
}

proof fn xs_matchr_ok(xp: XProg, n: nat, env: Map<nat, Val>, mm: XExpr, x: nat, a: XExpr, y: nat, b: XExpr, w: Val, v: Val)
    requires
        n >= 1,
        xeval(xp, (n - 1) as nat, env, mm) == Res::Done(Val::Ok(Box::new(w))),
        xeval(xp, (n - 1) as nat, env.insert(x, w), a) == Res::Done(v),
    ensures
        xeval(xp, n, env, XExpr::MatchR(Box::new(mm), x, Box::new(a), y, Box::new(b))) == Res::Done(v),
{
    reveal_with_fuel(xeval, 1);
}

proof fn xs_matchr_err(xp: XProg, n: nat, env: Map<nat, Val>, mm: XExpr, x: nat, a: XExpr, y: nat, b: XExpr, w: Val, v: Val)
    requires
        n >= 1,
        xeval(xp, (n - 1) as nat, env, mm) == Res::Done(Val::Err(Box::new(w))),
        xeval(xp, (n - 1) as nat, env.insert(y, w), b) == Res::Done(v),
    ensures
        xeval(xp, n, env, XExpr::MatchR(Box::new(mm), x, Box::new(a), y, Box::new(b))) == Res::Done(v),
{
    reveal_with_fuel(xeval, 1);
}

proof fn xs_builtin(xp: XProg, n: nat, env: Map<nat, Val>, bi: Builtin, es: Seq<XExpr>, vs: Seq<Val>, v: Val)
    requires
        n >= 1,
        xeval_args(xp, (n - 1) as nat, env, es, 0) == ResSeq::Done(vs),
        apply(bi, vs) == Res::Done(v),
    ensures
        xeval(xp, n, env, XExpr::Builtin(bi, es)) == Res::Done(v),
{
    reveal_with_fuel(xeval, 1);
}

proof fn xs_list(xp: XProg, n: nat, env: Map<nat, Val>, t: Ty, es: Seq<XExpr>, vs: Seq<Val>)
    requires
        n >= 1,
        xeval_args(xp, (n - 1) as nat, env, es, 0) == ResSeq::Done(vs),
    ensures
        xeval(xp, n, env, XExpr::List(t, es)) == Res::Done(Val::List(vs)),
{
    reveal_with_fuel(xeval, 1);
}

proof fn xs_call(xp: XProg, n: nat, env: Map<nat, Val>, g: nat, es: Seq<XExpr>, vs: Seq<Val>)
    requires
        n >= 1,
        xeval_args(xp, (n - 1) as nat, env, es, 0) == ResSeq::Done(vs),
        g < xp.funcs.len(),
        vs.len() == xp.funcs[g as int].params.len(),
    ensures
        xeval(xp, n, env, XExpr::Call(g, es)) == xeval(
            xp,
            (n - 1) as nat,
            bind(xp.funcs[g as int].params, vs, vs.len()),
            xp.funcs[g as int].body,
        ),
{
    reveal_with_fuel(xeval, 1);
}

proof fn xs_args_nil(xp: XProg, n: nat, env: Map<nat, Val>, es: Seq<XExpr>, i: nat)
    requires
        n >= 1,
        i >= es.len(),
    ensures
        xeval_args(xp, n, env, es, i) == ResSeq::Done(Seq::<Val>::empty()),
{
    reveal_with_fuel(xeval_args, 1);
}

proof fn xs_args_cons(xp: XProg, n: nat, env: Map<nat, Val>, es: Seq<XExpr>, i: nat, v: Val, vs: Seq<Val>)
    requires
        n >= 1,
        i < es.len(),
        xeval(xp, (n - 1) as nat, env, es[i as int]) == Res::Done(v),
        xeval_args(xp, (n - 1) as nat, env, es, (i + 1) as nat) == ResSeq::Done(vs),
    ensures
        xeval_args(xp, n, env, es, i) == ResSeq::Done(seq![v] + vs),
{
    reveal_with_fuel(xeval_args, 1);
}

proof fn xs_fold(
    xp: XProg,
    n: nat,
    env: Map<nat, Val>,
    xs: XExpr,
    init: XExpr,
    acc: nat,
    item: nat,
    body: XExpr,
    items: Seq<Val>,
    a0: Val,
    r: Res,
)
    requires
        n >= 1,
        xeval(xp, (n - 1) as nat, env, xs) == Res::Done(Val::List(items)),
        xeval(xp, (n - 1) as nat, env, init) == Res::Done(a0),
        xeval_fold(xp, (n - 1) as nat, env, acc, item, body, items, 0, a0) == r,
    ensures
        xeval(xp, n, env, XExpr::Fold(Box::new(xs), Box::new(init), acc, item, Box::new(body))) == r,
{
    reveal_with_fuel(xeval, 1);
}

proof fn xs_fold_nil(xp: XProg, n: nat, env: Map<nat, Val>, acc: nat, item: nat, body: XExpr, items: Seq<Val>, j: nat, a: Val)
    requires
        n >= 1,
        j >= items.len(),
    ensures
        xeval_fold(xp, n, env, acc, item, body, items, j, a) == Res::Done(a),
{
    reveal_with_fuel(xeval_fold, 1);
}

proof fn xs_fold_step(
    xp: XProg,
    n: nat,
    env: Map<nat, Val>,
    acc: nat,
    item: nat,
    body: XExpr,
    items: Seq<Val>,
    j: nat,
    a: Val,
    v: Val,
    r: Res,
)
    requires
        n >= 1,
        j < items.len(),
        xeval(xp, (n - 1) as nat, env.insert(acc, a).insert(item, items[j as int]), body) == Res::Done(v),
        xeval_fold(xp, (n - 1) as nat, env, acc, item, body, items, (j + 1) as nat, v) == r,
    ensures
        xeval_fold(xp, n, env, acc, item, body, items, j, a) == r,
{
    reveal_with_fuel(xeval_fold, 1);
}

proof fn xs_sort(xp: XProg, n: nat, env: Map<nat, Val>, xs: XExpr, x: nat, k: XExpr, items: Seq<Val>, kv: Seq<Val>, keys: Seq<int>)
    requires
        n >= 1,
        xeval(xp, (n - 1) as nat, env, xs) == Res::Done(Val::List(items)),
        xmap(xp, (n - 1) as nat, env, x, k, items, 0) == ResSeq::Done(kv),
        int_seq(kv) == Some(keys),
    ensures
        xeval(xp, n, env, XExpr::SortBy(Box::new(xs), x, Box::new(k))) == Res::Done(Val::List(sort_vals(items, keys))),
{
    reveal_with_fuel(xeval, 1);
}

proof fn xs_map(xp: XProg, n: nat, env: Map<nat, Val>, xs: XExpr, x: nat, c: XExpr, items: Seq<Val>, gv: Seq<Val>)
    requires
        n >= 1,
        xeval(xp, (n - 1) as nat, env, xs) == Res::Done(Val::List(items)),
        xmap(xp, (n - 1) as nat, env, x, c, items, 0) == ResSeq::Done(gv),
    ensures
        xeval(xp, n, env, XExpr::Map(Box::new(xs), x, Box::new(c))) == Res::Done(Val::List(gv)),
{
    reveal_with_fuel(xeval, 1);
}

proof fn xs_filter(xp: XProg, n: nat, env: Map<nat, Val>, xs: XExpr, x: nat, c: XExpr, items: Seq<Val>, out: Seq<Val>)
    requires
        n >= 1,
        xeval(xp, (n - 1) as nat, env, xs) == Res::Done(Val::List(items)),
        xfilter(xp, (n - 1) as nat, env, x, c, items, 0) == ResSeq::Done(out),
    ensures
        xeval(xp, n, env, XExpr::Filter(Box::new(xs), x, Box::new(c))) == Res::Done(Val::List(out)),
{
    reveal_with_fuel(xeval, 1);
}

proof fn xs_any(xp: XProg, n: nat, env: Map<nat, Val>, xs: XExpr, x: nat, c: XExpr, items: Seq<Val>, r: Res)
    requires
        n >= 1,
        xeval(xp, (n - 1) as nat, env, xs) == Res::Done(Val::List(items)),
        xany(xp, (n - 1) as nat, env, x, c, items, 0) == r,
    ensures
        xeval(xp, n, env, XExpr::Any(Box::new(xs), x, Box::new(c))) == r,
{
    reveal_with_fuel(xeval, 1);
}

proof fn xs_all(xp: XProg, n: nat, env: Map<nat, Val>, xs: XExpr, x: nat, c: XExpr, items: Seq<Val>, r: Res)
    requires
        n >= 1,
        xeval(xp, (n - 1) as nat, env, xs) == Res::Done(Val::List(items)),
        xall(xp, (n - 1) as nat, env, x, c, items, 0) == r,
    ensures
        xeval(xp, n, env, XExpr::All(Box::new(xs), x, Box::new(c))) == r,
{
    reveal_with_fuel(xeval, 1);
}

proof fn xs_find(xp: XProg, n: nat, env: Map<nat, Val>, xs: XExpr, x: nat, c: XExpr, items: Seq<Val>, r: Res)
    requires
        n >= 1,
        xeval(xp, (n - 1) as nat, env, xs) == Res::Done(Val::List(items)),
        xfind(xp, (n - 1) as nat, env, x, c, items, 0) == r,
    ensures
        xeval(xp, n, env, XExpr::Find(Box::new(xs), x, Box::new(c))) == r,
{
    reveal_with_fuel(xeval, 1);
}

// 系列（xmap・xfilter・xany・xall・xfind）の一段。

proof fn xs_xmap_nil(xp: XProg, n: nat, env: Map<nat, Val>, x: nat, c: XExpr, items: Seq<Val>, j: nat)
    requires
        n >= 1,
        j >= items.len(),
    ensures
        xmap(xp, n, env, x, c, items, j) == ResSeq::Done(Seq::<Val>::empty()),
{
    reveal_with_fuel(xmap, 1);
}

proof fn xs_xmap_cons(xp: XProg, n: nat, env: Map<nat, Val>, x: nat, c: XExpr, items: Seq<Val>, j: nat, v: Val, gs: Seq<Val>)
    requires
        n >= 1,
        j < items.len(),
        xeval(xp, (n - 1) as nat, env.insert(x, items[j as int]), c) == Res::Done(v),
        xmap(xp, (n - 1) as nat, env, x, c, items, (j + 1) as nat) == ResSeq::Done(gs),
    ensures
        xmap(xp, n, env, x, c, items, j) == ResSeq::Done(seq![v] + gs),
{
    reveal_with_fuel(xmap, 1);
}

proof fn xs_xfilter_nil(xp: XProg, n: nat, env: Map<nat, Val>, x: nat, c: XExpr, items: Seq<Val>, j: nat)
    requires
        n >= 1,
        j >= items.len(),
    ensures
        xfilter(xp, n, env, x, c, items, j) == ResSeq::Done(Seq::<Val>::empty()),
{
    reveal_with_fuel(xfilter, 1);
}

proof fn xs_xfilter_keep(xp: XProg, n: nat, env: Map<nat, Val>, x: nat, c: XExpr, items: Seq<Val>, j: nat, gs: Seq<Val>)
    requires
        n >= 1,
        j < items.len(),
        xeval(xp, (n - 1) as nat, env.insert(x, items[j as int]), c) == Res::Done(Val::Bool(true)),
        xfilter(xp, (n - 1) as nat, env, x, c, items, (j + 1) as nat) == ResSeq::Done(gs),
    ensures
        xfilter(xp, n, env, x, c, items, j) == ResSeq::Done(seq![items[j as int]] + gs),
{
    reveal_with_fuel(xfilter, 1);
}

proof fn xs_xfilter_drop(xp: XProg, n: nat, env: Map<nat, Val>, x: nat, c: XExpr, items: Seq<Val>, j: nat, gs: Seq<Val>)
    requires
        n >= 1,
        j < items.len(),
        xeval(xp, (n - 1) as nat, env.insert(x, items[j as int]), c) == Res::Done(Val::Bool(false)),
        xfilter(xp, (n - 1) as nat, env, x, c, items, (j + 1) as nat) == ResSeq::Done(gs),
    ensures
        xfilter(xp, n, env, x, c, items, j) == ResSeq::Done(gs),
{
    reveal_with_fuel(xfilter, 1);
}

proof fn xs_xany_nil(xp: XProg, n: nat, env: Map<nat, Val>, x: nat, c: XExpr, items: Seq<Val>, j: nat)
    requires
        n >= 1,
        j >= items.len(),
    ensures
        xany(xp, n, env, x, c, items, j) == Res::Done(Val::Bool(false)),
{
    reveal_with_fuel(xany, 1);
}

proof fn xs_xany_true(xp: XProg, n: nat, env: Map<nat, Val>, x: nat, c: XExpr, items: Seq<Val>, j: nat)
    requires
        n >= 1,
        j < items.len(),
        xeval(xp, (n - 1) as nat, env.insert(x, items[j as int]), c) == Res::Done(Val::Bool(true)),
    ensures
        xany(xp, n, env, x, c, items, j) == Res::Done(Val::Bool(true)),
{
    reveal_with_fuel(xany, 1);
}

proof fn xs_xany_false(xp: XProg, n: nat, env: Map<nat, Val>, x: nat, c: XExpr, items: Seq<Val>, j: nat, r: Res)
    requires
        n >= 1,
        j < items.len(),
        xeval(xp, (n - 1) as nat, env.insert(x, items[j as int]), c) == Res::Done(Val::Bool(false)),
        xany(xp, (n - 1) as nat, env, x, c, items, (j + 1) as nat) == r,
    ensures
        xany(xp, n, env, x, c, items, j) == r,
{
    reveal_with_fuel(xany, 1);
}

proof fn xs_xall_nil(xp: XProg, n: nat, env: Map<nat, Val>, x: nat, c: XExpr, items: Seq<Val>, j: nat)
    requires
        n >= 1,
        j >= items.len(),
    ensures
        xall(xp, n, env, x, c, items, j) == Res::Done(Val::Bool(true)),
{
    reveal_with_fuel(xall, 1);
}

proof fn xs_xall_true(xp: XProg, n: nat, env: Map<nat, Val>, x: nat, c: XExpr, items: Seq<Val>, j: nat, r: Res)
    requires
        n >= 1,
        j < items.len(),
        xeval(xp, (n - 1) as nat, env.insert(x, items[j as int]), c) == Res::Done(Val::Bool(true)),
        xall(xp, (n - 1) as nat, env, x, c, items, (j + 1) as nat) == r,
    ensures
        xall(xp, n, env, x, c, items, j) == r,
{
    reveal_with_fuel(xall, 1);
}

proof fn xs_xall_false(xp: XProg, n: nat, env: Map<nat, Val>, x: nat, c: XExpr, items: Seq<Val>, j: nat)
    requires
        n >= 1,
        j < items.len(),
        xeval(xp, (n - 1) as nat, env.insert(x, items[j as int]), c) == Res::Done(Val::Bool(false)),
    ensures
        xall(xp, n, env, x, c, items, j) == Res::Done(Val::Bool(false)),
{
    reveal_with_fuel(xall, 1);
}

proof fn xs_xfind_nil(xp: XProg, n: nat, env: Map<nat, Val>, x: nat, c: XExpr, items: Seq<Val>, j: nat)
    requires
        n >= 1,
        j >= items.len(),
    ensures
        xfind(xp, n, env, x, c, items, j) == Res::Done(Val::None),
{
    reveal_with_fuel(xfind, 1);
}

proof fn xs_xfind_hit(xp: XProg, n: nat, env: Map<nat, Val>, x: nat, c: XExpr, items: Seq<Val>, j: nat)
    requires
        n >= 1,
        j < items.len(),
        xeval(xp, (n - 1) as nat, env.insert(x, items[j as int]), c) == Res::Done(Val::Bool(true)),
    ensures
        xfind(xp, n, env, x, c, items, j) == Res::Done(Val::Some(Box::new(items[j as int]))),
{
    reveal_with_fuel(xfind, 1);
}

proof fn xs_xfind_miss(xp: XProg, n: nat, env: Map<nat, Val>, x: nat, c: XExpr, items: Seq<Val>, j: nat, r: Res)
    requires
        n >= 1,
        j < items.len(),
        xeval(xp, (n - 1) as nat, env.insert(x, items[j as int]), c) == Res::Done(Val::Bool(false)),
        xfind(xp, (n - 1) as nat, env, x, c, items, (j + 1) as nat) == r,
    ensures
        xfind(xp, n, env, x, c, items, j) == r,
{
    reveal_with_fuel(xfind, 1);
}

// ------------------------------------------------------------------ 書換え後の評価の分解（燃料の数え方を固定する）

/// 畳み込みの一段：要素 j を処理して w になるなら、本体は先ず値 v1 になり、残りの畳み込みは v1 から w になる。
proof fn fold_step_val(p: Prog, m: nat, env: Map<nat, Val>, acc: nat, item: nat, body: Expr, items: Seq<Val>, j: nat, a: Val, w: Val) -> (v1: Val)
    requires
        j < items.len(),
        eval_fold(p, m, env, acc, item, body, items, j, a) == Res::Done(w),
    ensures
        m >= 1,
        eval(p, (m - 1) as nat, env.insert(acc, a).insert(item, items[j as int]), body) == Res::Done(v1),
        eval_fold(p, (m - 1) as nat, env, acc, item, body, items, j + 1, v1) == Res::Done(w),
{
    reveal_with_fuel(eval_fold, 2);
    match eval(p, (m - 1) as nat, env.insert(acc, a).insert(item, items[j as int]), body) {
        Res::Done(v) => v,
        _ => {
            assert(false);
            Val::Unit
        },
    }
}

/// 一引数の組込みの評価の逆：結果 w は、引数の値 v1 に組込みを当てたものである（引数は燃料 f - 2 で値になる）。
proof fn inv_builtin1(p: Prog, f: nat, env: Map<nat, Val>, b: Builtin, e1: Expr, w: Val) -> (v1: Val)
    requires
        eval(p, f, env, Expr::Builtin(b, seq![e1])) == Res::Done(w),
    ensures
        eval(p, (f - 2) as nat, env, e1) == Res::Done(v1),
        apply(b, seq![v1]) == Res::Done(w),
        f >= 3,
{
    reveal_with_fuel(eval, 3);
    reveal_with_fuel(eval_args, 3);
    match eval(p, (f - 2) as nat, env, e1) {
        Res::Done(v) => v,
        _ => {
            assert(false);
            Val::Unit
        },
    }
}

/// 二引数の組込みの評価の逆：第一引数は燃料 f - 2 で、第二引数は燃料 f - 3 で値になる。
proof fn inv_builtin2(p: Prog, f: nat, env: Map<nat, Val>, b: Builtin, e1: Expr, e2: Expr, w: Val) -> (v12: (Val, Val))
    requires
        eval(p, f, env, Expr::Builtin(b, seq![e1, e2])) == Res::Done(w),
    ensures
        f >= 4,
        eval(p, (f - 2) as nat, env, e1) == Res::Done(v12.0),
        eval(p, (f - 3) as nat, env, e2) == Res::Done(v12.1),
        apply(b, seq![v12.0, v12.1]) == Res::Done(w),
{
    reveal_with_fuel(eval, 3);
    reveal_with_fuel(eval_args, 3);
    match eval(p, (f - 2) as nat, env, e1) {
        Res::Done(v1) => match eval(p, (f - 3) as nat, env, e2) {
            Res::Done(v2) => (v1, v2),
            _ => {
                assert(false);
                (Val::Unit, Val::Unit)
            },
        },
        _ => {
            assert(false);
            (Val::Unit, Val::Unit)
        },
    }
}

/// if の評価の逆：条件は燃料 f - 1 で真偽に評価され、選ばれた枝は燃料 f - 1 で w になる。
proof fn inv_if(p: Prog, f: nat, env: Map<nat, Val>, c: Expr, a: Expr, b: Expr, w: Val) -> (cv: bool)
    requires
        eval(p, f, env, Expr::If(Box::new(c), Box::new(a), Box::new(b))) == Res::Done(w),
    ensures
        eval(p, (f - 1) as nat, env, c) == Res::Done(Val::Bool(cv)),
        cv ==> eval(p, (f - 1) as nat, env, a) == Res::Done(w),
        !cv ==> eval(p, (f - 1) as nat, env, b) == Res::Done(w),
{
    reveal_with_fuel(eval, 2);
    match eval(p, (f - 1) as nat, env, c) {
        Res::Done(Val::Bool(true)) => true,
        Res::Done(Val::Bool(false)) => false,
        _ => {
            assert(false);
            false
        },
    }
}

/// let の評価の逆：束縛は燃料 f - 1 で値 va になり、本体は燃料 f - 1 で w になる。
proof fn inv_let(p: Prog, f: nat, env: Map<nat, Val>, x: nat, a: Expr, b: Expr, w: Val) -> (va: Val)
    requires
        eval(p, f, env, Expr::Let(x, Box::new(a), Box::new(b))) == Res::Done(w),
    ensures
        eval(p, (f - 1) as nat, env, a) == Res::Done(va),
        eval(p, (f - 1) as nat, env.insert(x, va), b) == Res::Done(w),
{
    reveal_with_fuel(eval, 2);
    match eval(p, (f - 1) as nat, env, a) {
        Res::Done(v) => v,
        _ => {
            assert(false);
            Val::Unit
        },
    }
}

/// 変数の評価：燃料が一つでもあれば、束縛された値を返す。
proof fn eval_var_val(p: Prog, f: nat, env: Map<nat, Val>, x: nat)
    requires
        f >= 1,
        env.contains_key(x),
    ensures
        eval(p, f, env, Expr::Var(x)) == Res::Done(env[x]),
{
    reveal_with_fuel(eval, 1);
}

/// Cons(h, acc) の評価の逆：acc が List(as) なら、結果は h の値を先頭に足した列である。
proof fn inv_cons_head(p: Prog, f: nat, env: Map<nat, Val>, h: Expr, acc: nat, as_: Seq<Val>, v1: Val) -> (hv: Val)
    requires
        env.contains_key(acc),
        env[acc] == Val::List(as_),
        eval(p, f, env, Expr::Builtin(Builtin::Cons, seq![h, Expr::Var(acc)])) == Res::Done(v1),
    ensures
        f >= 4,
        eval(p, (f - 2) as nat, env, h) == Res::Done(hv),
        v1 == Val::List(seq![hv] + as_),
{
    let v12 = inv_builtin2(p, f, env, Builtin::Cons, h, Expr::Var(acc), v1);
    eval_var_val(p, (f - 3) as nat, env, acc);
    assert(apply(Builtin::Cons, seq![v12.0, v12.1]) == Res::Done(v1));
    assert(v12.1 == env[acc]);
    v12.0
}

// ------------------------------------------------------------------ 列の値の補題

/// reverse の連結：rev(a + b) = rev(b) + rev(a)。
proof fn rev_app(a: Seq<Val>, b: Seq<Val>)
    ensures
        rev(a + b) =~= rev(b) + rev(a),
{
    let n = a.len() + b.len();
    assert forall|i: int| 0 <= i < n implies rev(a + b)[i] == (rev(b) + rev(a))[i] by {
        if i < b.len() {
            assert(rev(b).len() == b.len());
            assert((a + b)[n - 1 - i] == b[b.len() - 1 - i]);
        } else {
            assert((a + b)[n - 1 - i] == a[a.len() - 1 - (i - b.len())]);
        }
    }
    assert(rev(a + b) =~= rev(b) + rev(a));
}

// ------------------------------------------------------------------ 燃料と定数の補助

/// 評価が値を返すなら、燃料は一つ以上ある。
proof fn done_fuel_pos(p: Prog, n: nat, env: Map<nat, Val>, e: Expr, v: Val)
    requires
        eval(p, n, env, e) == Res::Done(v),
    ensures
        n >= 1,
{
    reveal_with_fuel(eval, 1);
}

/// 真偽の定数の評価。
proof fn bool_done(p: Prog, n: nat, env: Map<nat, Val>, b: bool, v: Val)
    requires
        eval(p, n, env, Expr::Bool(b)) == Res::Done(v),
    ensures
        v == Val::Bool(b),
{
    reveal_with_fuel(eval, 1);
}

/// None の評価。
proof fn none_done(p: Prog, n: nat, env: Map<nat, Val>, t: Ty, v: Val)
    requires
        eval(p, n, env, Expr::None(t)) == Res::Done(v),
    ensures
        v == Val::None,
{
    reveal_with_fuel(eval, 1);
}

/// Some(x) の評価：x が束縛されていれば、Some の値。
proof fn some_var_done(p: Prog, n: nat, env: Map<nat, Val>, x: nat, v: Val)
    requires
        env.contains_key(x),
        eval(p, n, env, Expr::Some(Box::new(Expr::Var(x)))) == Res::Done(v),
    ensures
        v == Val::Some(Box::new(env[x])),
{
    reveal_with_fuel(eval, 2);
}

/// 畳み込みの評価の分解（rw の畳み込みの形）：結果 w なら、列は items、初期値は v0 で、畳み込みは w。
proof fn fold_unfold(p: Prog, f: nat, env: Map<nat, Val>, xs: Expr, init: Expr, acc: nat, item: nat, body: Expr, w: Val) -> (r: (
    Seq<Val>,
    Val,
))
    requires
        eval(p, f, env, Expr::Fold(Box::new(xs), Box::new(init), acc, item, Box::new(body))) == Res::Done(w),
    ensures
        f >= 1,
        eval(p, (f - 1) as nat, env, xs) == Res::Done(Val::List(r.0)),
        eval(p, (f - 1) as nat, env, init) == Res::Done(r.1),
        eval_fold(p, (f - 1) as nat, env, acc, item, body, r.0, 0, r.1) == Res::Done(w),
{
    reveal_with_fuel(eval, 1);
    match eval(p, (f - 1) as nat, env, xs) {
        Res::Done(Val::List(items)) => match eval(p, (f - 1) as nat, env, init) {
            Res::Done(v0) => (items, v0),
            _ => {
                assert(false);
                (Seq::empty(), Val::Unit)
            },
        },
        _ => {
            assert(false);
            (Seq::empty(), Val::Unit)
        },
    }
}

/// 逆向きの反転の評価：reverse の結果 w は、引数 v1 が List(s) のとき List(rev(s))。
proof fn reverse_inv(v1: Val, w: Val) -> (s: Seq<Val>)
    requires
        apply(Builtin::Reverse, seq![v1]) == Res::Done(w),
    ensures
        v1 == Val::List(s),
        w == Val::List(rev(s)),
{
    match v1 {
        Val::List(s) => s,
        _ => {
            assert(false);
            Seq::empty()
        },
    }
}

/// match の評価の分解：調べる式と枝は燃料 f - 1 で評価される。調べる式の値は sv（None なら nb、Some なら束縛して sm が w）。
proof fn inv_match(p: Prog, f: nat, env: Map<nat, Val>, mm: Expr, nb: Expr, yb: nat, sm: Expr, w: Val) -> (sv: Val)
    requires
        eval(p, f, env, Expr::Match(Box::new(mm), Box::new(nb), yb, Box::new(sm))) == Res::Done(w),
    ensures
        f >= 2,
        eval(p, (f - 1) as nat, env, mm) == Res::Done(sv),
        sv == Val::None ==> eval(p, (f - 1) as nat, env, nb) == Res::Done(w),
        sv is Some ==> eval(p, (f - 1) as nat, env.insert(yb, *sv->Some_0), sm) == Res::Done(w),
{
    reveal_with_fuel(eval, 2);
    match eval(p, (f - 1) as nat, env, mm) {
        Res::Done(Val::None) => Val::None,
        Res::Done(Val::Some(v)) => Val::Some(v),
        _ => {
            assert(false);
            Val::Unit
        },
    }
}

/// 偽の累積値で if acc then t1 else false の畳み込みは、偽のまま（真偽の結果は偽）。
proof fn if_false_acc(p: Prog, f: nat, env: Map<nat, Val>, acc: nat, c: Expr, v: Val)
    requires
        env.contains_key(acc),
        env[acc] == Val::Bool(false),
        eval(p, f, env, Expr::If(Box::new(Expr::Var(acc)), Box::new(c), Box::new(Expr::Bool(false)))) == Res::Done(v),
    ensures
        v == Val::Bool(false),
{
    reveal_with_fuel(eval, 2);
}

/// 真の累積値で if acc then true else c の本体は真に評価される。
proof fn any_body_true(p: Prog, f: nat, env: Map<nat, Val>, acc: nat, c: Expr, v: Val)
    requires
        env.contains_key(acc),
        env[acc] == Val::Bool(true),
        eval(p, f, env, Expr::If(Box::new(Expr::Var(acc)), Box::new(Expr::Bool(true)), Box::new(c))) == Res::Done(v),
    ensures
        v == Val::Bool(true),
{
    reveal_with_fuel(eval, 2);
}

/// 真の累積値で any の畳み込みは真のまま（結果は真）。
proof fn any_fold_true(p: Prog, m: nat, env: Map<nat, Val>, acc: nat, x: nat, c: Expr, items: Seq<Val>, j: nat, res: bool)
    requires
        acc != x,
        j <= items.len(),
        eval_fold(p, m, env, acc, x, Expr::If(Box::new(Expr::Var(acc)), Box::new(Expr::Bool(true)), Box::new(c)), items, j, Val::Bool(true))
            == Res::Done(Val::Bool(res)),
    ensures
        res,
    decreases items.len() - j,
{
    reveal_with_fuel(eval_fold, 1);
    if j < items.len() {
        let body = Expr::If(Box::new(Expr::Var(acc)), Box::new(Expr::Bool(true)), Box::new(c));
        let v1 = fold_step_val(p, m, env, acc, x, body, items, j, Val::Bool(true), Val::Bool(res));
        let env1 = env.insert(acc, Val::Bool(true)).insert(x, items[j as int]);
        assert(env1.contains_key(acc));
        assert(env1[acc] == Val::Bool(true));
        any_body_true(p, (m - 1) as nat, env1, acc, c, v1);
        any_fold_true(p, (m - 1) as nat, env, acc, x, c, items, j + 1, res);
    }
}

/// all の畳み込み（累積値が真から始まる）：結果が偽なら、偽になる要素 stop があり、それより前は真。
/// 結果が真なら、どの要素の述語も真（燃料 m 未満で）。
proof fn all_false_acc(p: Prog, f: nat, env: Map<nat, Val>, acc: nat, x: nat, c: Expr, items: Seq<Val>, j: nat, res: bool)
    requires
        acc != x,
        j <= items.len(),
        eval_fold(p, f, env, acc, x, Expr::If(Box::new(Expr::Var(acc)), Box::new(c), Box::new(Expr::Bool(false))), items, j, Val::Bool(false))
            == Res::Done(Val::Bool(res)),
    ensures
        !res,
    decreases items.len() - j,
{
    reveal_with_fuel(eval_fold, 1);
    if j < items.len() {
        let body = Expr::If(Box::new(Expr::Var(acc)), Box::new(c), Box::new(Expr::Bool(false)));
        let v1 = fold_step_val(p, f, env, acc, x, body, items, j, Val::Bool(false), Val::Bool(res));
        let env1 = env.insert(acc, Val::Bool(false)).insert(x, items[j as int]);
        assert(env1.contains_key(acc));
        assert(env1[acc] == Val::Bool(false));
        if_false_acc(p, (f - 1) as nat, env1, acc, c, v1);
        all_false_acc(p, (f - 1) as nat, env, acc, x, c, items, j + 1, res);
    }
}

// ------------------------------------------------------------------ 源の核の形の閾値（段の補題の組）

proof fn xat_leaf_int(xp: XProg, env: Map<nat, Val>, c: int) -> (n0: nat)
    ensures
        xat(xp, env, XExpr::Int(c), Val::Int(c), n0),
{
    assert forall|n: nat| n >= 1 implies #[trigger] xeval(xp, n, env, XExpr::Int(c)) == Res::Done(Val::Int(c)) by {
        xs_int(xp, n, env, c);
    }
    1
}

proof fn xat_leaf_bool(xp: XProg, env: Map<nat, Val>, b: bool) -> (n0: nat)
    ensures
        xat(xp, env, XExpr::Bool(b), Val::Bool(b), n0),
{
    assert forall|n: nat| n >= 1 implies #[trigger] xeval(xp, n, env, XExpr::Bool(b)) == Res::Done(Val::Bool(b)) by {
        xs_bool(xp, n, env, b);
    }
    1
}

proof fn xat_leaf_unit(xp: XProg, env: Map<nat, Val>) -> (n0: nat)
    ensures
        xat(xp, env, XExpr::Unit, Val::Unit, n0),
{
    assert forall|n: nat| n >= 1 implies #[trigger] xeval(xp, n, env, XExpr::Unit) == Res::Done(Val::Unit) by {
        xs_unit(xp, n, env);
    }
    1
}

proof fn xat_leaf_char(xp: XProg, env: Map<nat, Val>, c: int) -> (n0: nat)
    ensures
        xat(xp, env, XExpr::Char(c), Val::Char(c), n0),
{
    assert forall|n: nat| n >= 1 implies #[trigger] xeval(xp, n, env, XExpr::Char(c)) == Res::Done(Val::Char(c)) by {
        xs_char(xp, n, env, c);
    }
    1
}

proof fn xat_leaf_none(xp: XProg, env: Map<nat, Val>, t: Ty) -> (n0: nat)
    ensures
        xat(xp, env, XExpr::None(t), Val::None, n0),
{
    assert forall|n: nat| n >= 1 implies #[trigger] xeval(xp, n, env, XExpr::None(t)) == Res::Done(Val::None) by {
        xs_none(xp, n, env, t);
    }
    1
}

proof fn xat_var(xp: XProg, env: Map<nat, Val>, x: nat) -> (n0: nat)
    requires
        env.contains_key(x),
    ensures
        xat(xp, env, XExpr::Var(x), env[x], n0),
{
    assert forall|n: nat| n >= 1 implies #[trigger] xeval(xp, n, env, XExpr::Var(x)) == Res::Done(env[x]) by {
        xs_var(xp, n, env, x);
    }
    1
}

proof fn xat_pair(xp: XProg, env: Map<nat, Val>, a: XExpr, b: XExpr, va: Val, vb: Val, n1: nat, n2: nat) -> (n0: nat)
    requires
        xat(xp, env, a, va, n1),
        xat(xp, env, b, vb, n2),
    ensures
        xat(xp, env, XExpr::Pair(Box::new(a), Box::new(b)), Val::Pair(Box::new(va), Box::new(vb)), n0),
{
    assert forall|n: nat| n >= n1 + n2 + 1 implies #[trigger] xeval(xp, n, env, XExpr::Pair(Box::new(a), Box::new(b)))
        == Res::Done(Val::Pair(Box::new(va), Box::new(vb))) by {
        assert(xeval(xp, (n - 1) as nat, env, a) == Res::Done(va));
        assert(xeval(xp, (n - 1) as nat, env, b) == Res::Done(vb));
        xs_pair(xp, n, env, a, b, va, vb);
    }
    n1 + n2 + 1
}

proof fn xat_some(xp: XProg, env: Map<nat, Val>, a: XExpr, va: Val, n1: nat) -> (n0: nat)
    requires
        xat(xp, env, a, va, n1),
    ensures
        xat(xp, env, XExpr::Some(Box::new(a)), Val::Some(Box::new(va)), n0),
{
    assert forall|n: nat| n >= n1 + 1 implies #[trigger] xeval(xp, n, env, XExpr::Some(Box::new(a))) == Res::Done(
        Val::Some(Box::new(va)),
    ) by {
        assert(xeval(xp, (n - 1) as nat, env, a) == Res::Done(va));
        xs_some(xp, n, env, a, va);
    }
    n1 + 1
}

proof fn xat_inj(xp: XProg, env: Map<nat, Val>, ok: bool, t: Ty, u: Ty, a: XExpr, va: Val, n1: nat) -> (n0: nat)
    requires
        xat(xp, env, a, va, n1),
    ensures
        xat(xp, env, XExpr::Inj(ok, t, u, Box::new(a)), inj_val(ok, va), n0),
{
    assert forall|n: nat| n >= n1 + 1 implies #[trigger] xeval(xp, n, env, XExpr::Inj(ok, t, u, Box::new(a))) == Res::Done(
        inj_val(ok, va),
    ) by {
        assert(xeval(xp, (n - 1) as nat, env, a) == Res::Done(va));
        xs_inj(xp, n, env, ok, t, u, a, va);
    }
    n1 + 1
}

proof fn xat_let(xp: XProg, env: Map<nat, Val>, x: nat, a: XExpr, b: XExpr, va: Val, v: Val, n1: nat, n2: nat) -> (n0: nat)
    requires
        xat(xp, env, a, va, n1),
        xat(xp, env.insert(x, va), b, v, n2),
    ensures
        xat(xp, env, XExpr::Let(x, Box::new(a), Box::new(b)), v, n0),
{
    assert forall|n: nat| n >= n1 + n2 + 1 implies #[trigger] xeval(xp, n, env, XExpr::Let(x, Box::new(a), Box::new(b)))
        == Res::Done(v) by {
        assert(xeval(xp, (n - 1) as nat, env, a) == Res::Done(va));
        assert(xeval(xp, (n - 1) as nat, env.insert(x, va), b) == Res::Done(v));
        xs_let(xp, n, env, x, a, b, va, v);
    }
    n1 + n2 + 1
}

proof fn xat_if_true(xp: XProg, env: Map<nat, Val>, c: XExpr, a: XExpr, b: XExpr, v: Val, n1: nat, n2: nat) -> (n0: nat)
    requires
        xat(xp, env, c, Val::Bool(true), n1),
        xat(xp, env, a, v, n2),
    ensures
        xat(xp, env, XExpr::If(Box::new(c), Box::new(a), Box::new(b)), v, n0),
{
    assert forall|n: nat| n >= n1 + n2 + 1 implies #[trigger] xeval(xp, n, env, XExpr::If(Box::new(c), Box::new(a), Box::new(b)))
        == Res::Done(v) by {
        assert(xeval(xp, (n - 1) as nat, env, c) == Res::Done(Val::Bool(true)));
        assert(xeval(xp, (n - 1) as nat, env, a) == Res::Done(v));
        xs_if_true(xp, n, env, c, a, b, v);
    }
    n1 + n2 + 1
}

proof fn xat_if_false(xp: XProg, env: Map<nat, Val>, c: XExpr, a: XExpr, b: XExpr, v: Val, n1: nat, n2: nat) -> (n0: nat)
    requires
        xat(xp, env, c, Val::Bool(false), n1),
        xat(xp, env, b, v, n2),
    ensures
        xat(xp, env, XExpr::If(Box::new(c), Box::new(a), Box::new(b)), v, n0),
{
    assert forall|n: nat| n >= n1 + n2 + 1 implies #[trigger] xeval(xp, n, env, XExpr::If(Box::new(c), Box::new(a), Box::new(b)))
        == Res::Done(v) by {
        assert(xeval(xp, (n - 1) as nat, env, c) == Res::Done(Val::Bool(false)));
        assert(xeval(xp, (n - 1) as nat, env, b) == Res::Done(v));
        xs_if_false(xp, n, env, c, a, b, v);
    }
    n1 + n2 + 1
}

proof fn xat_match_none(xp: XProg, env: Map<nat, Val>, mm: XExpr, nb: XExpr, x: nat, sm: XExpr, v: Val, n1: nat, n2: nat) -> (n0: nat)
    requires
        xat(xp, env, mm, Val::None, n1),
        xat(xp, env, nb, v, n2),
    ensures
        xat(xp, env, XExpr::Match(Box::new(mm), Box::new(nb), x, Box::new(sm)), v, n0),
{
    assert forall|n: nat| n >= n1 + n2 + 1 implies #[trigger] xeval(xp, n, env, XExpr::Match(Box::new(mm), Box::new(nb), x, Box::new(sm)))
        == Res::Done(v) by {
        assert(xeval(xp, (n - 1) as nat, env, mm) == Res::Done(Val::None));
        assert(xeval(xp, (n - 1) as nat, env, nb) == Res::Done(v));
        xs_match_none(xp, n, env, mm, nb, x, sm, v);
    }
    n1 + n2 + 1
}

proof fn xat_match_some(xp: XProg, env: Map<nat, Val>, mm: XExpr, nb: XExpr, x: nat, sm: XExpr, w: Val, v: Val, n1: nat, n2: nat) -> (n0: nat)
    requires
        xat(xp, env, mm, Val::Some(Box::new(w)), n1),
        xat(xp, env.insert(x, w), sm, v, n2),
    ensures
        xat(xp, env, XExpr::Match(Box::new(mm), Box::new(nb), x, Box::new(sm)), v, n0),
{
    assert forall|n: nat| n >= n1 + n2 + 1 implies #[trigger] xeval(xp, n, env, XExpr::Match(Box::new(mm), Box::new(nb), x, Box::new(sm)))
        == Res::Done(v) by {
        assert(xeval(xp, (n - 1) as nat, env, mm) == Res::Done(Val::Some(Box::new(w))));
        assert(xeval(xp, (n - 1) as nat, env.insert(x, w), sm) == Res::Done(v));
        xs_match_some(xp, n, env, mm, nb, x, sm, w, v);
    }
    n1 + n2 + 1
}

proof fn xat_matchr_ok(xp: XProg, env: Map<nat, Val>, mm: XExpr, x: nat, a: XExpr, y: nat, b: XExpr, w: Val, v: Val, n1: nat, n2: nat) -> (n0: nat)
    requires
        xat(xp, env, mm, Val::Ok(Box::new(w)), n1),
        xat(xp, env.insert(x, w), a, v, n2),
    ensures
        xat(xp, env, XExpr::MatchR(Box::new(mm), x, Box::new(a), y, Box::new(b)), v, n0),
{
    assert forall|n: nat| n >= n1 + n2 + 1 implies #[trigger] xeval(xp, n, env, XExpr::MatchR(Box::new(mm), x, Box::new(a), y, Box::new(b)))
        == Res::Done(v) by {
        assert(xeval(xp, (n - 1) as nat, env, mm) == Res::Done(Val::Ok(Box::new(w))));
        assert(xeval(xp, (n - 1) as nat, env.insert(x, w), a) == Res::Done(v));
        xs_matchr_ok(xp, n, env, mm, x, a, y, b, w, v);
    }
    n1 + n2 + 1
}

proof fn xat_matchr_err(xp: XProg, env: Map<nat, Val>, mm: XExpr, x: nat, a: XExpr, y: nat, b: XExpr, w: Val, v: Val, n1: nat, n2: nat) -> (n0: nat)
    requires
        xat(xp, env, mm, Val::Err(Box::new(w)), n1),
        xat(xp, env.insert(y, w), b, v, n2),
    ensures
        xat(xp, env, XExpr::MatchR(Box::new(mm), x, Box::new(a), y, Box::new(b)), v, n0),
{
    assert forall|n: nat| n >= n1 + n2 + 1 implies #[trigger] xeval(xp, n, env, XExpr::MatchR(Box::new(mm), x, Box::new(a), y, Box::new(b)))
        == Res::Done(v) by {
        assert(xeval(xp, (n - 1) as nat, env, mm) == Res::Done(Val::Err(Box::new(w))));
        assert(xeval(xp, (n - 1) as nat, env.insert(y, w), b) == Res::Done(v));
        xs_matchr_err(xp, n, env, mm, x, a, y, b, w, v);
    }
    n1 + n2 + 1
}

// ------------------------------------------------------------------ 源の引数列・組込み・呼出しの閾値

proof fn xat_args_nil(xp: XProg, env: Map<nat, Val>, es: Seq<XExpr>, i: nat) -> (n0: nat)
    requires
        i >= es.len(),
    ensures
        xat_args(xp, env, es, i, Seq::<Val>::empty(), n0),
{
    assert forall|n: nat| n >= 1 implies #[trigger] xeval_args(xp, n, env, es, i) == ResSeq::Done(Seq::<Val>::empty()) by {
        xs_args_nil(xp, n, env, es, i);
    }
    1
}

proof fn xat_args_cons(xp: XProg, env: Map<nat, Val>, es: Seq<XExpr>, i: nat, v: Val, vs: Seq<Val>, n1: nat, n2: nat) -> (n0: nat)
    requires
        i < es.len(),
        xat(xp, env, es[i as int], v, n1),
        xat_args(xp, env, es, (i + 1) as nat, vs, n2),
    ensures
        xat_args(xp, env, es, i, seq![v] + vs, n0),
{
    assert forall|n: nat| n >= n1 + n2 + 1 implies #[trigger] xeval_args(xp, n, env, es, i) == ResSeq::Done(seq![v] + vs) by {
        assert(xeval(xp, (n - 1) as nat, env, es[i as int]) == Res::Done(v));
        assert(xeval_args(xp, (n - 1) as nat, env, es, (i + 1) as nat) == ResSeq::Done(vs));
        xs_args_cons(xp, n, env, es, i, v, vs);
    }
    n1 + n2 + 1
}

proof fn xat_list(xp: XProg, env: Map<nat, Val>, t: Ty, es: Seq<XExpr>, vs: Seq<Val>, n1: nat) -> (n0: nat)
    requires
        xat_args(xp, env, es, 0, vs, n1),
    ensures
        xat(xp, env, XExpr::List(t, es), Val::List(vs), n0),
{
    assert forall|n: nat| n >= n1 + 1 implies #[trigger] xeval(xp, n, env, XExpr::List(t, es)) == Res::Done(Val::List(vs)) by {
        assert(xeval_args(xp, (n - 1) as nat, env, es, 0) == ResSeq::Done(vs));
        xs_list(xp, n, env, t, es, vs);
    }
    n1 + 1
}

proof fn xat_builtin(xp: XProg, env: Map<nat, Val>, bi: Builtin, es: Seq<XExpr>, vs: Seq<Val>, v: Val, n1: nat) -> (n0: nat)
    requires
        xat_args(xp, env, es, 0, vs, n1),
        apply(bi, vs) == Res::Done(v),
    ensures
        xat(xp, env, XExpr::Builtin(bi, es), v, n0),
{
    assert forall|n: nat| n >= n1 + 1 implies #[trigger] xeval(xp, n, env, XExpr::Builtin(bi, es)) == Res::Done(v) by {
        assert(xeval_args(xp, (n - 1) as nat, env, es, 0) == ResSeq::Done(vs));
        xs_builtin(xp, n, env, bi, es, vs, v);
    }
    n1 + 1
}

proof fn xat_call(xp: XProg, env: Map<nat, Val>, g: nat, es: Seq<XExpr>, vs: Seq<Val>, v: Val, n1: nat, n2: nat) -> (n0: nat)
    requires
        xat_args(xp, env, es, 0, vs, n1),
        g < xp.funcs.len(),
        vs.len() == xp.funcs[g as int].params.len(),
        xat(xp, bind(xp.funcs[g as int].params, vs, vs.len()), xp.funcs[g as int].body, v, n2),
    ensures
        xat(xp, env, XExpr::Call(g, es), v, n0),
{
    let env2 = bind(xp.funcs[g as int].params, vs, vs.len());
    assert forall|n: nat| n >= n1 + n2 + 1 implies #[trigger] xeval(xp, n, env, XExpr::Call(g, es)) == Res::Done(v) by {
        assert(xeval_args(xp, (n - 1) as nat, env, es, 0) == ResSeq::Done(vs));
        assert(xeval(xp, (n - 1) as nat, env2, xp.funcs[g as int].body) == Res::Done(v));
        xs_call(xp, n, env, g, es, vs);
    }
    n1 + n2 + 1
}




// ------------------------------------------------------------------ 書換え後の形の評価の分解（燃料は一つ下）

/// 空のリストの評価（畳み込みの初期値 List(t, [])）：値は空の列。
proof fn nil_done(p: Prog, n: nat, env: Map<nat, Val>, t: Ty, v: Val)
    requires
        eval(p, n, env, Expr::List(t, Seq::empty())) == Res::Done(v),
    ensures
        v == Val::List(Seq::<Val>::empty()),
{
    reveal_with_fuel(eval, 2);
    reveal_with_fuel(eval_args, 2);
}

/// 対の評価の分解：要素はどちらも燃料 f - 1 で値になる。
proof fn inv_pair(p: Prog, f: nat, env: Map<nat, Val>, a: Expr, b: Expr, w: Val) -> (vab: (Val, Val))
    requires
        eval(p, f, env, Expr::Pair(Box::new(a), Box::new(b))) == Res::Done(w),
    ensures
        f >= 1,
        eval(p, (f - 1) as nat, env, a) == Res::Done(vab.0),
        eval(p, (f - 1) as nat, env, b) == Res::Done(vab.1),
        w == Val::Pair(Box::new(vab.0), Box::new(vab.1)),
{
    reveal_with_fuel(eval, 1);
    match eval(p, (f - 1) as nat, env, a) {
        Res::Done(va) => match eval(p, (f - 1) as nat, env, b) {
            Res::Done(vb) => (va, vb),
            _ => {
                assert(false);
                (Val::Unit, Val::Unit)
            },
        },
        _ => {
            assert(false);
            (Val::Unit, Val::Unit)
        },
    }
}

/// some の評価の分解：中身は燃料 f - 1 で値になる。
proof fn inv_some(p: Prog, f: nat, env: Map<nat, Val>, a: Expr, w: Val) -> (va: Val)
    requires
        eval(p, f, env, Expr::Some(Box::new(a))) == Res::Done(w),
    ensures
        f >= 1,
        eval(p, (f - 1) as nat, env, a) == Res::Done(va),
        w == Val::Some(Box::new(va)),
{
    reveal_with_fuel(eval, 1);
    match eval(p, (f - 1) as nat, env, a) {
        Res::Done(v) => v,
        _ => {
            assert(false);
            Val::Unit
        },
    }
}

/// 注入の評価の分解：中身は燃料 f - 1 で値になる。
proof fn inv_inj(p: Prog, f: nat, env: Map<nat, Val>, ok: bool, t: Ty, u: Ty, a: Expr, w: Val) -> (va: Val)
    requires
        eval(p, f, env, Expr::Inj(ok, t, u, Box::new(a))) == Res::Done(w),
    ensures
        f >= 1,
        eval(p, (f - 1) as nat, env, a) == Res::Done(va),
        w == inj_val(ok, va),
{
    reveal_with_fuel(eval, 1);
    match eval(p, (f - 1) as nat, env, a) {
        Res::Done(v) => v,
        _ => {
            assert(false);
            Val::Unit
        },
    }
}

/// match_result の評価の分解：調べる式は燃料 f - 1 で値 sv になり、選ばれた枝が燃料 f - 1 で w になる。
proof fn inv_matchr(p: Prog, f: nat, env: Map<nat, Val>, mm: Expr, x: nat, a: Expr, y: nat, b: Expr, w: Val) -> (sv: Val)
    requires
        eval(p, f, env, Expr::MatchR(Box::new(mm), x, Box::new(a), y, Box::new(b))) == Res::Done(w),
    ensures
        f >= 2,
        eval(p, (f - 1) as nat, env, mm) == Res::Done(sv),
        sv is Ok ==> eval(p, (f - 1) as nat, env.insert(x, *sv->Ok_0), a) == Res::Done(w),
        sv is Err ==> eval(p, (f - 1) as nat, env.insert(y, *sv->Err_0), b) == Res::Done(w),
        sv is Ok || sv is Err,
{
    reveal_with_fuel(eval, 2);
    match eval(p, (f - 1) as nat, env, mm) {
        Res::Done(Val::Ok(v)) => Val::Ok(v),
        Res::Done(Val::Err(v)) => Val::Err(v),
        _ => {
            assert(false);
            Val::Unit
        },
    }
}

/// 組込みの評価の分解：引数は燃料 f - 1 で値 vs になり、組込みを当てると w になる。
proof fn inv_bi(p: Prog, f: nat, env: Map<nat, Val>, b: Builtin, es: Seq<Expr>, w: Val) -> (vs: Seq<Val>)
    requires
        eval(p, f, env, Expr::Builtin(b, es)) == Res::Done(w),
    ensures
        f >= 1,
        eval_args(p, (f - 1) as nat, env, es, 0) == ResSeq::Done(vs),
        apply(b, vs) == Res::Done(w),
{
    reveal_with_fuel(eval, 1);
    match eval_args(p, (f - 1) as nat, env, es, 0) {
        ResSeq::Done(vs) => vs,
        _ => {
            assert(false);
            Seq::empty()
        },
    }
}

/// リストの評価の分解：要素は燃料 f - 1 で vs になり、結果は List(vs)。
proof fn inv_list(p: Prog, f: nat, env: Map<nat, Val>, t: Ty, es: Seq<Expr>, w: Val) -> (vs: Seq<Val>)
    requires
        eval(p, f, env, Expr::List(t, es)) == Res::Done(w),
    ensures
        f >= 1,
        eval_args(p, (f - 1) as nat, env, es, 0) == ResSeq::Done(vs),
        w == Val::List(vs),
{
    reveal_with_fuel(eval, 1);
    match eval_args(p, (f - 1) as nat, env, es, 0) {
        ResSeq::Done(vs) => vs,
        _ => {
            assert(false);
            Seq::empty()
        },
    }
}

/// 呼出しの評価の分解：引数は燃料 f - 1 で vs になり、呼出し先の本体が燃料 f - 1 で w を返す（形が合うとき）。
proof fn inv_call(p: Prog, f: nat, env: Map<nat, Val>, g: nat, es: Seq<Expr>, w: Val) -> (vs: Seq<Val>)
    requires
        eval(p, f, env, Expr::Call(g, es)) == Res::Done(w),
    ensures
        f >= 1,
        eval_args(p, (f - 1) as nat, env, es, 0) == ResSeq::Done(vs),
        g < p.funcs.len(),
        vs.len() == p.funcs[g as int].params.len(),
        eval(p, (f - 1) as nat, bind(p.funcs[g as int].params, vs, vs.len()), p.funcs[g as int].body) == Res::Done(w),
{
    reveal_with_fuel(eval, 1);
    match eval_args(p, (f - 1) as nat, env, es, 0) {
        ResSeq::Done(vs) => {
            if g < p.funcs.len() && vs.len() == p.funcs[g as int].params.len() {
                vs
            } else {
                assert(false);
                vs
            }
        },
        _ => {
            assert(false);
            Seq::empty()
        },
    }
}

/// 引数列の一段の分解：先頭の要素は燃料 f - 1 で値 vt.0 になり、残りは燃料 f - 1 で vt.1 になる。
proof fn inv_args_cons(p: Prog, f: nat, env: Map<nat, Val>, es: Seq<Expr>, i: nat, vs: Seq<Val>) -> (vt: (Val, Seq<Val>))
    requires
        i < es.len(),
        eval_args(p, f, env, es, i) == ResSeq::Done(vs),
    ensures
        f >= 1,
        eval(p, (f - 1) as nat, env, es[i as int]) == Res::Done(vt.0),
        eval_args(p, (f - 1) as nat, env, es, (i + 1) as nat) == ResSeq::Done(vt.1),
        vs == seq![vt.0] + vt.1,
{
    reveal_with_fuel(eval_args, 1);
    match eval(p, (f - 1) as nat, env, es[i as int]) {
        Res::Done(v) => match eval_args(p, (f - 1) as nat, env, es, (i + 1) as nat) {
            ResSeq::Done(vs2) => (v, vs2),
            _ => {
                assert(false);
                (Val::Unit, Seq::empty())
            },
        },
        _ => {
            assert(false);
            (Val::Unit, Seq::empty())
        },
    }
}

/// 引数が空の列の評価：燃料が一つでもあれば、空の列の値。
proof fn args_done_empty(p: Prog, f: nat, env: Map<nat, Val>, es: Seq<Expr>, i: nat, vs: Seq<Val>)
    requires
        i >= es.len(),
        eval_args(p, f, env, es, i) == ResSeq::Done(vs),
    ensures
        vs == Seq::<Val>::empty(),
{
    reveal_with_fuel(eval_args, 1);
}

/// 呼出しの型の分解：型が付けば、引数の型の列 ts があり、呼出し先は存在し、ts は仮引数の型に等しい。
proof fn call_ty_inv(p: Prog, r: nat, ctx: Map<nat, Ty>, es: Seq<Expr>, g: nat) -> (ts: Seq<Ty>)
    requires
        ty_expr(p, r, ctx, Expr::Call(g, es)) is Some,
    ensures
        ty_args(p, r, ctx, es, 0) == Some(ts),
        g < p.funcs.len(),
        ts.len() == p.funcs[g as int].params.len(),
        forall|k: int| 0 <= k < ts.len() ==> #[trigger] ts[k] == p.funcs[g as int].params[k].1,
{
    reveal_with_fuel(ty_expr, 1);
    match ty_args(p, r, ctx, es, 0) {
        Some(ts) => ts,
        None => {
            assert(false);
            Seq::empty()
        },
    }
}

/// 畳み込みの累積値が Some(v) なら、残りの要素でも Some(v) のまま。結果は Some(v)。
proof fn find_some_fixed(
    p: Prog,
    f: nat,
    env: Map<nat, Val>,
    acc: nat,
    x: nat,
    c: Expr,
    t: Ty,
    y: nat,
    items: Seq<Val>,
    j: nat,
    v: Val,
    w: Val,
)
    requires
        acc != x,
        eval_fold(p, f, env, acc, x, select_body(c, t, acc, x, y), items, j, Val::Some(Box::new(v))) == Res::Done(w),
    ensures
        w == Val::Some(Box::new(v)),
    decreases items.len() - j,
{
    reveal_with_fuel(eval_fold, 1);
    if j < items.len() {
        let a = Val::Some(Box::new(v));
        let body = select_body(c, t, acc, x, y);
        let nb = Expr::If(Box::new(c), Box::new(Expr::Some(Box::new(Expr::Var(x)))), Box::new(Expr::None(t)));
        let sm = Expr::Some(Box::new(Expr::Var(y)));
        assert(body == Expr::Match(Box::new(Expr::Var(acc)), Box::new(nb), y, Box::new(sm)));
        let v1 = fold_step_val(p, f, env, acc, x, body, items, j, a, w);
        let envb = env.insert(acc, a).insert(x, items[j as int]);
        assert(envb.contains_key(acc) && envb[acc] == a);
        let sv = inv_match(p, (f - 1) as nat, envb, Expr::Var(acc), nb, y, sm, v1);
        eval_var_val(p, (f - 2) as nat, envb, acc);
        assert(sv == a);
        assert(sv is Some);
        let pv = *sv->Some_0;
        assert(pv == v);
        let envy = envb.insert(y, pv);
        assert(envy.contains_key(y));
        some_var_done(p, (f - 2) as nat, envy, y, v1);
        assert(v1 == Val::Some(Box::new(v)));
        find_some_fixed(p, (f - 1) as nat, env, acc, x, c, t, y, items, j + 1, v, w);
    } else {
        assert(w == Val::Some(Box::new(v)));
    }
}

// ------------------------------------------------------------------ 補助（真偽・一要素の列）

/// 真偽の型の値は真偽の値。
proof fn bool_val(v: Val) -> (b: bool)
    requires
        val_type(v, Ty::Bool),
    ensures
        v == Val::Bool(b),
{
    bool_of_ty(v);
    match v {
        Val::Bool(c) => c,
        _ => {
            assert(false);
            false
        },
    }
}

/// 一要素の列の reverse は、その列。
proof fn rev_single(v: Val)
    ensures
        rev(seq![v]) =~= seq![v],
{
    assert(rev(seq![v]).len() == 1);
    assert(rev(seq![v])[0] == v);
    assert(rev(seq![v]) =~= seq![v]);
}

// ------------------------------------------------------------------ 畳み込みの一般の形（閾値つき）

/// 源の畳み込み（一般の本体）の逆：書換え後の畳み込みが w なら、源の畳み込みは十分大きい燃料で w を返す。
/// 要素の本体は、累積値を含む環境で評価される（源の本体は acc を使ってよい）。
proof fn fold_back(
    xp: XProg,
    p: Prog,
    rw: spec_fn(XExpr) -> Expr,
    m: nat,
    r: nat,
    ctx: Map<nat, Ty>,
    env: Map<nat, Val>,
    acc: nat,
    item: nat,
    body: XExpr,
    ta: Ty,
    s: Ty,
    items: Seq<Val>,
    j: nat,
    a: Val,
    w: Val,
) -> (n0: nat)
    requires
        sim_prog(xp, p, rw),
        homomorphic(rw),
        hof_shapes(rw),
        wf(p),
        env_ok(env, ctx),
        ty_expr(p, r, ctx.insert(acc, ta).insert(item, s), rw(body)) == Some(ta),
        val_type(a, ta),
        forall|k: int| #![trigger items[k]] j <= k < items.len() ==> val_type(items[k], s),
        eval_fold(p, m, env, acc, item, rw(body), items, j, a) == Res::Done(w),
    ensures
        forall|n: nat| n >= n0 ==> #[trigger] xeval_fold(xp, n, env, acc, item, body, items, j, a) == Res::Done(w),
    decreases m, 0nat,
{
    reveal_with_fuel(eval_fold, 1);
    if j >= items.len() {
        assert(w == a);
        assert forall|n: nat| n >= 1 implies #[trigger] xeval_fold(xp, n, env, acc, item, body, items, j, a) == Res::Done(w) by {
            xs_fold_nil(xp, n, env, acc, item, body, items, j, a);
        }
        1
    } else {
        let v1 = fold_step_val(p, m, env, acc, item, rw(body), items, j, a, w);
        let env_a = env.insert(acc, a);
        let envb = env_a.insert(item, items[j as int]);
        let ctx_a = ctx.insert(acc, ta);
        env_ok_insert(env, ctx, acc, a, ta);
        assert(val_type(items[j as int], s));
        env_ok_insert(env_a, ctx_a, item, items[j as int], s);
        let ctx2 = ctx_a.insert(item, s);
        assert(ctx2 == ctx.insert(acc, ta).insert(item, s));
        sound(p, (m - 1) as nat, r, ctx2, envb, rw(body), v1);
        assert(val_type(v1, ta));
        let tb = back_expr(xp, p, rw, (m - 1) as nat, r, ctx2, envb, body, v1);
        let rest = fold_back(xp, p, rw, (m - 1) as nat, r, ctx, env, acc, item, body, ta, s, items, j + 1, v1, w);
        assert forall|n: nat| n >= tb + rest + 1 implies #[trigger] xeval_fold(xp, n, env, acc, item, body, items, j, a) == Res::Done(w) by {
            assert(xeval(xp, (n - 1) as nat, envb, body) == Res::Done(v1));
            assert(xeval_fold(xp, (n - 1) as nat, env, acc, item, body, items, (j + 1) as nat, v1) == Res::Done(w));
            xs_fold_step(xp, n, env, acc, item, body, items, j, a, v1, Res::Done(w));
        }
        tb + rest + 1
    }
}

// ------------------------------------------------------------------ map・filter（累積値は列）

/// map の畳み込みの逆：累積値 as_ から要素 j 以降を処理して sv になるなら、写像の源は閾値以上で gv を返す。
/// sv は rev(gv) に as_ を足した列（先頭に積んだ順）。
proof fn map_back(
    xp: XProg,
    p: Prog,
    rw: spec_fn(XExpr) -> Expr,
    m: nat,
    r: nat,
    ctx: Map<nat, Ty>,
    env: Map<nat, Val>,
    acc: nat,
    x: nat,
    c: XExpr,
    s: Ty,
    items: Seq<Val>,
    j: nat,
    as_: Seq<Val>,
    sv: Seq<Val>,
) -> (res: (nat, Seq<Val>))
    requires
        sim_prog(xp, p, rw),
        homomorphic(rw),
        hof_shapes(rw),
        wf(p),
        env_ok(env, ctx),
        acc != x,
        absent(acc, rw(c)),
        ty_expr(p, r, ctx.insert(x, s), rw(c)) is Some,
        forall|k: int| #![trigger items[k]] j <= k < items.len() ==> val_type(items[k], s),
        eval_fold(p, m, env, acc, x, cons_body(rw(c), acc), items, j, Val::List(as_)) == Res::Done(Val::List(sv)),
    ensures
        forall|n: nat| n >= res.0 ==> #[trigger] xmap(xp, n, env, x, c, items, j) == ResSeq::Done(res.1),
        sv == rev(res.1) + as_,
        j <= items.len() ==> res.1.len() + j == items.len(),
    decreases m, 0nat,
{
    reveal_with_fuel(eval_fold, 1);
    if j >= items.len() {
        assert(sv == as_);
        assert forall|n: nat| n >= 1 implies #[trigger] xmap(xp, n, env, x, c, items, j) == ResSeq::Done(Seq::<Val>::empty()) by {
            xs_xmap_nil(xp, n, env, x, c, items, j);
        }
        (1, Seq::empty())
    } else {
        let g = rw(c);
        let a = Val::List(as_);
        let body = cons_body(g, acc);
        let v1 = fold_step_val(p, m, env, acc, x, body, items, j, a, Val::List(sv));
        let envb = env.insert(acc, a).insert(x, items[j as int]);
        assert(envb.contains_key(acc) && envb[acc] == a);
        assert(body == Expr::Builtin(Builtin::Cons, seq![g, Expr::Var(acc)]));
        let hv = inv_cons_head(p, (m - 1) as nat, envb, g, acc, as_, v1);
        assert(v1 == Val::List(seq![hv] + as_));
        eval_drop(p, (m - 3) as nat, env, acc, a, x, items[j as int], g);
        env_ok_insert(env, ctx, x, items[j as int], s);
        let tb = back_expr(xp, p, rw, (m - 3) as nat, r, ctx.insert(x, s), env.insert(x, items[j as int]), c, hv);
        let (nr, gr) = map_back(xp, p, rw, (m - 1) as nat, r, ctx, env, acc, x, c, s, items, j + 1, seq![hv] + as_, sv);
        let gv = seq![hv] + gr;
        assert forall|n: nat| n >= tb + nr + 1 implies #[trigger] xmap(xp, n, env, x, c, items, j) == ResSeq::Done(gv) by {
            assert(xeval(xp, (n - 1) as nat, env.insert(x, items[j as int]), c) == Res::Done(hv));
            assert(xmap(xp, (n - 1) as nat, env, x, c, items, (j + 1) as nat) == ResSeq::Done(gr));
            xs_xmap_cons(xp, n, env, x, c, items, j, hv, gr);
        }
        rev_app(seq![hv], gr);
        rev_single(hv);
        assert((rev(gr) + seq![hv]) + as_ =~= rev(gr) + (seq![hv] + as_));
        assert(rev(gv) =~= rev(gr) + seq![hv]);
        (tb + nr + 1, gv)
    }
}

/// filter の畳み込みの逆：述語の値は真偽で、累積値 as_ から要素 j 以降を処理して sv になるなら、
/// 絞り込みの源は閾値以上で out を返す。sv は rev(out) に as_ を足した列。
proof fn filter_back(
    xp: XProg,
    p: Prog,
    rw: spec_fn(XExpr) -> Expr,
    m: nat,
    r: nat,
    ctx: Map<nat, Ty>,
    env: Map<nat, Val>,
    acc: nat,
    x: nat,
    c: XExpr,
    s: Ty,
    items: Seq<Val>,
    j: nat,
    as_: Seq<Val>,
    sv: Seq<Val>,
) -> (res: (nat, Seq<Val>))
    requires
        sim_prog(xp, p, rw),
        homomorphic(rw),
        hof_shapes(rw),
        wf(p),
        env_ok(env, ctx),
        acc != x,
        absent(acc, rw(c)),
        ty_expr(p, r, ctx.insert(x, s), rw(c)) == Some(Ty::Bool),
        forall|k: int| #![trigger items[k]] j <= k < items.len() ==> val_type(items[k], s),
        eval_fold(
            p,
            m,
            env,
            acc,
            x,
            filter_body(rw(c), acc, x),
            items,
            j,
            Val::List(as_),
        ) == Res::Done(Val::List(sv)),
    ensures
        forall|n: nat| n >= res.0 ==> #[trigger] xfilter(xp, n, env, x, c, items, j) == ResSeq::Done(res.1),
        sv == rev(res.1) + as_,
    decreases m, 0nat,
{
    reveal_with_fuel(eval_fold, 1);
    if j >= items.len() {
        assert(sv == as_);
        assert forall|n: nat| n >= 1 implies #[trigger] xfilter(xp, n, env, x, c, items, j) == ResSeq::Done(Seq::<Val>::empty()) by {
            xs_xfilter_nil(xp, n, env, x, c, items, j);
        }
        (1, Seq::empty())
    } else {
        let g = rw(c);
        let a = Val::List(as_);
        let cons_e = Expr::Builtin(Builtin::Cons, seq![Expr::Var(x), Expr::Var(acc)]);
        let body = filter_body(g, acc, x);
        assert(body == Expr::If(Box::new(g), Box::new(cons_e), Box::new(Expr::Var(acc))));
        let v1 = fold_step_val(p, m, env, acc, x, body, items, j, a, Val::List(sv));
        let envb = env.insert(acc, a).insert(x, items[j as int]);
        assert(envb.contains_key(acc) && envb[acc] == a);
        let cv = inv_if(p, (m - 1) as nat, envb, g, cons_e, Expr::Var(acc), v1);
        eval_drop(p, (m - 2) as nat, env, acc, a, x, items[j as int], g);
        env_ok_insert(env, ctx, x, items[j as int], s);
        let tc = back_expr(xp, p, rw, (m - 2) as nat, r, ctx.insert(x, s), env.insert(x, items[j as int]), c, Val::Bool(cv));
        if cv {
            inv_cons_head_var(p, (m - 2) as nat, envb, x, acc, as_, v1);
            assert(v1 == Val::List(seq![items[j as int]] + as_));
            let (nr, gr) = filter_back(xp, p, rw, (m - 1) as nat, r, ctx, env, acc, x, c, s, items, j + 1, seq![items[j as int]] + as_, sv);
            let out = seq![items[j as int]] + gr;
            assert forall|n: nat| n >= tc + nr + 1 implies #[trigger] xfilter(xp, n, env, x, c, items, j) == ResSeq::Done(out) by {
                assert(xeval(xp, (n - 1) as nat, env.insert(x, items[j as int]), c) == Res::Done(Val::Bool(true)));
                assert(xfilter(xp, (n - 1) as nat, env, x, c, items, (j + 1) as nat) == ResSeq::Done(gr));
                xs_xfilter_keep(xp, n, env, x, c, items, j, gr);
            }
            rev_app(seq![items[j as int]], gr);
            rev_single(items[j as int]);
            assert((rev(gr) + seq![items[j as int]]) + as_ =~= rev(gr) + (seq![items[j as int]] + as_));
            assert(rev(out) =~= rev(gr) + seq![items[j as int]]);
            (tc + nr + 1, out)
        } else {
            done_fuel_pos(p, (m - 2) as nat, envb, Expr::Var(acc), v1);
            eval_var_val(p, (m - 2) as nat, envb, acc);
            assert(v1 == a);
            let (nr, gr) = filter_back(xp, p, rw, (m - 1) as nat, r, ctx, env, acc, x, c, s, items, j + 1, as_, sv);
            assert forall|n: nat| n >= tc + nr + 1 implies #[trigger] xfilter(xp, n, env, x, c, items, j) == ResSeq::Done(gr) by {
                assert(xeval(xp, (n - 1) as nat, env.insert(x, items[j as int]), c) == Res::Done(Val::Bool(false)));
                assert(xfilter(xp, (n - 1) as nat, env, x, c, items, (j + 1) as nat) == ResSeq::Done(gr));
                xs_xfilter_drop(xp, n, env, x, c, items, j, gr);
            }
            (tc + nr + 1, gr)
        }
    }
}

/// Cons(x, acc) の評価の逆（h が変数 x のとき）：先頭は束縛された要素の値。
proof fn inv_cons_head_var(p: Prog, f: nat, env: Map<nat, Val>, x: nat, acc: nat, as_: Seq<Val>, v1: Val)
    requires
        env.contains_key(x),
        env.contains_key(acc),
        env[acc] == Val::List(as_),
        eval(p, f, env, Expr::Builtin(Builtin::Cons, seq![Expr::Var(x), Expr::Var(acc)])) == Res::Done(v1),
    ensures
        v1 == Val::List(seq![env[x]] + as_),
{
    let hv = inv_cons_head(p, f, env, Expr::Var(x), acc, as_, v1);
    eval_var_val(p, (f - 2) as nat, env, x);
    assert(hv == env[x]);
}

// ------------------------------------------------------------------ any・all・find（累積値は真偽・選択）

/// any の畳み込みの逆：累積値が偽から始まり、結果が b なら、源の any は閾値以上で b を返す。
proof fn any_back(
    xp: XProg,
    p: Prog,
    rw: spec_fn(XExpr) -> Expr,
    m: nat,
    r: nat,
    ctx: Map<nat, Ty>,
    env: Map<nat, Val>,
    acc: nat,
    x: nat,
    c: XExpr,
    s: Ty,
    items: Seq<Val>,
    j: nat,
    b: bool,
) -> (n0: nat)
    requires
        sim_prog(xp, p, rw),
        homomorphic(rw),
        hof_shapes(rw),
        wf(p),
        env_ok(env, ctx),
        acc != x,
        absent(acc, rw(c)),
        ty_expr(p, r, ctx.insert(x, s), rw(c)) == Some(Ty::Bool),
        forall|k: int| #![trigger items[k]] j <= k < items.len() ==> val_type(items[k], s),
        eval_fold(
            p,
            m,
            env,
            acc,
            x,
            Expr::If(Box::new(Expr::Var(acc)), Box::new(Expr::Bool(true)), Box::new(rw(c))),
            items,
            j,
            Val::Bool(false),
        ) == Res::Done(Val::Bool(b)),
    ensures
        forall|n: nat| n >= n0 ==> #[trigger] xany(xp, n, env, x, c, items, j) == Res::Done(Val::Bool(b)),
    decreases m, 0nat,
{
    reveal_with_fuel(eval_fold, 1);
    if j >= items.len() {
        assert(b == false);
        assert forall|n: nat| n >= 1 implies #[trigger] xany(xp, n, env, x, c, items, j) == Res::Done(Val::Bool(false)) by {
            xs_xany_nil(xp, n, env, x, c, items, j);
        }
        1
    } else {
        let g = rw(c);
        let body = Expr::If(Box::new(Expr::Var(acc)), Box::new(Expr::Bool(true)), Box::new(g));
        let a = Val::Bool(false);
        let v1 = fold_step_val(p, m, env, acc, x, body, items, j, a, Val::Bool(b));
        let envb = env.insert(acc, a).insert(x, items[j as int]);
        assert(envb.contains_key(acc) && envb[acc] == a);
        let cv = inv_if(p, (m - 1) as nat, envb, Expr::Var(acc), Expr::Bool(true), g, v1);
        done_fuel_pos(p, (m - 2) as nat, envb, Expr::Var(acc), Val::Bool(cv));
        eval_var_val(p, (m - 2) as nat, envb, acc);
        assert(!cv);
        eval_drop(p, (m - 2) as nat, env, acc, a, x, items[j as int], g);
        env_ok_insert(env, ctx, x, items[j as int], s);
        sound(p, (m - 2) as nat, r, ctx.insert(x, s), env.insert(x, items[j as int]), g, v1);
        let b1 = bool_val(v1);
        let tc = back_expr(xp, p, rw, (m - 2) as nat, r, ctx.insert(x, s), env.insert(x, items[j as int]), c, Val::Bool(b1));
        if b1 {
            any_fold_true(p, (m - 1) as nat, env, acc, x, g, items, j + 1, b);
            assert(b == true);
            assert forall|n: nat| n >= tc + 1 implies #[trigger] xany(xp, n, env, x, c, items, j) == Res::Done(Val::Bool(b)) by {
                assert(xeval(xp, (n - 1) as nat, env.insert(x, items[j as int]), c) == Res::Done(Val::Bool(true)));
                xs_xany_true(xp, n, env, x, c, items, j);
            }
            tc + 1
        } else {
            let nr = any_back(xp, p, rw, (m - 1) as nat, r, ctx, env, acc, x, c, s, items, j + 1, b);
            assert forall|n: nat| n >= tc + nr + 1 implies #[trigger] xany(xp, n, env, x, c, items, j) == Res::Done(Val::Bool(b)) by {
                assert(xeval(xp, (n - 1) as nat, env.insert(x, items[j as int]), c) == Res::Done(Val::Bool(false)));
                assert(xany(xp, (n - 1) as nat, env, x, c, items, (j + 1) as nat) == Res::Done(Val::Bool(b)));
                xs_xany_false(xp, n, env, x, c, items, j, Res::Done(Val::Bool(b)));
            }
            tc + nr + 1
        }
    }
}

/// all の畳み込みの逆：累積値が真から始まり、結果が b なら、源の all は閾値以上で b を返す。
proof fn all_back(
    xp: XProg,
    p: Prog,
    rw: spec_fn(XExpr) -> Expr,
    m: nat,
    r: nat,
    ctx: Map<nat, Ty>,
    env: Map<nat, Val>,
    acc: nat,
    x: nat,
    c: XExpr,
    s: Ty,
    items: Seq<Val>,
    j: nat,
    b: bool,
) -> (n0: nat)
    requires
        sim_prog(xp, p, rw),
        homomorphic(rw),
        hof_shapes(rw),
        wf(p),
        env_ok(env, ctx),
        acc != x,
        absent(acc, rw(c)),
        ty_expr(p, r, ctx.insert(x, s), rw(c)) == Some(Ty::Bool),
        forall|k: int| #![trigger items[k]] j <= k < items.len() ==> val_type(items[k], s),
        eval_fold(
            p,
            m,
            env,
            acc,
            x,
            Expr::If(Box::new(Expr::Var(acc)), Box::new(rw(c)), Box::new(Expr::Bool(false))),
            items,
            j,
            Val::Bool(true),
        ) == Res::Done(Val::Bool(b)),
    ensures
        forall|n: nat| n >= n0 ==> #[trigger] xall(xp, n, env, x, c, items, j) == Res::Done(Val::Bool(b)),
    decreases m, 0nat,
{
    reveal_with_fuel(eval_fold, 1);
    if j >= items.len() {
        assert(b == true);
        assert forall|n: nat| n >= 1 implies #[trigger] xall(xp, n, env, x, c, items, j) == Res::Done(Val::Bool(true)) by {
            xs_xall_nil(xp, n, env, x, c, items, j);
        }
        1
    } else {
        let g = rw(c);
        let body = Expr::If(Box::new(Expr::Var(acc)), Box::new(g), Box::new(Expr::Bool(false)));
        let a = Val::Bool(true);
        let v1 = fold_step_val(p, m, env, acc, x, body, items, j, a, Val::Bool(b));
        let envb = env.insert(acc, a).insert(x, items[j as int]);
        assert(envb.contains_key(acc) && envb[acc] == a);
        let cv = inv_if(p, (m - 1) as nat, envb, Expr::Var(acc), g, Expr::Bool(false), v1);
        done_fuel_pos(p, (m - 2) as nat, envb, Expr::Var(acc), Val::Bool(cv));
        eval_var_val(p, (m - 2) as nat, envb, acc);
        assert(cv);
        eval_drop(p, (m - 2) as nat, env, acc, a, x, items[j as int], g);
        env_ok_insert(env, ctx, x, items[j as int], s);
        sound(p, (m - 2) as nat, r, ctx.insert(x, s), env.insert(x, items[j as int]), g, v1);
        let b1 = bool_val(v1);
        let tc = back_expr(xp, p, rw, (m - 2) as nat, r, ctx.insert(x, s), env.insert(x, items[j as int]), c, Val::Bool(b1));
        if b1 {
            let nr = all_back(xp, p, rw, (m - 1) as nat, r, ctx, env, acc, x, c, s, items, j + 1, b);
            assert forall|n: nat| n >= tc + nr + 1 implies #[trigger] xall(xp, n, env, x, c, items, j) == Res::Done(Val::Bool(b)) by {
                assert(xeval(xp, (n - 1) as nat, env.insert(x, items[j as int]), c) == Res::Done(Val::Bool(true)));
                assert(xall(xp, (n - 1) as nat, env, x, c, items, (j + 1) as nat) == Res::Done(Val::Bool(b)));
                xs_xall_true(xp, n, env, x, c, items, j, Res::Done(Val::Bool(b)));
            }
            tc + nr + 1
        } else {
            all_false_acc(p, (m - 1) as nat, env, acc, x, g, items, j + 1, b);
            assert(b == false);
            assert forall|n: nat| n >= tc + 1 implies #[trigger] xall(xp, n, env, x, c, items, j) == Res::Done(Val::Bool(b)) by {
                assert(xeval(xp, (n - 1) as nat, env.insert(x, items[j as int]), c) == Res::Done(Val::Bool(false)));
                xs_xall_false(xp, n, env, x, c, items, j);
            }
            tc + 1
        }
    }
}

/// find の畳み込みの逆：累積値が None から始まり、結果が w なら、源の find は閾値以上で w を返す。
proof fn find_back(
    xp: XProg,
    p: Prog,
    rw: spec_fn(XExpr) -> Expr,
    m: nat,
    r: nat,
    ctx: Map<nat, Ty>,
    env: Map<nat, Val>,
    acc: nat,
    x: nat,
    c: XExpr,
    y: nat,
    t: Ty,
    s: Ty,
    items: Seq<Val>,
    j: nat,
    w: Val,
) -> (n0: nat)
    requires
        sim_prog(xp, p, rw),
        homomorphic(rw),
        hof_shapes(rw),
        wf(p),
        env_ok(env, ctx),
        acc != x,
        absent(acc, rw(c)),
        ty_expr(p, r, ctx.insert(x, s), rw(c)) == Some(Ty::Bool),
        forall|k: int| #![trigger items[k]] j <= k < items.len() ==> val_type(items[k], s),
        eval_fold(p, m, env, acc, x, select_body(rw(c), t, acc, x, y), items, j, Val::None) == Res::Done(w),
    ensures
        forall|n: nat| n >= n0 ==> #[trigger] xfind(xp, n, env, x, c, items, j) == Res::Done(w),
    decreases m, 0nat,
{
    reveal_with_fuel(eval_fold, 1);
    if j >= items.len() {
        assert(w == Val::None);
        assert forall|n: nat| n >= 1 implies #[trigger] xfind(xp, n, env, x, c, items, j) == Res::Done(Val::None) by {
            xs_xfind_nil(xp, n, env, x, c, items, j);
        }
        1
    } else {
        let g = rw(c);
        let body = select_body(g, t, acc, x, y);
        let nb = Expr::If(Box::new(g), Box::new(Expr::Some(Box::new(Expr::Var(x)))), Box::new(Expr::None(t)));
        let sm = Expr::Some(Box::new(Expr::Var(y)));
        assert(body == Expr::Match(Box::new(Expr::Var(acc)), Box::new(nb), y, Box::new(sm)));
        let v1 = fold_step_val(p, m, env, acc, x, body, items, j, Val::None, w);
        let envb = env.insert(acc, Val::None).insert(x, items[j as int]);
        assert(envb.contains_key(acc) && envb[acc] == Val::None);
        let sc = inv_match(p, (m - 1) as nat, envb, Expr::Var(acc), nb, y, sm, v1);
        done_fuel_pos(p, (m - 2) as nat, envb, Expr::Var(acc), sc);
        eval_var_val(p, (m - 2) as nat, envb, acc);
        assert(sc == Val::None);
        let cv = inv_if(p, (m - 2) as nat, envb, g, Expr::Some(Box::new(Expr::Var(x))), Expr::None(t), v1);
        eval_drop(p, (m - 3) as nat, env, acc, Val::None, x, items[j as int], g);
        env_ok_insert(env, ctx, x, items[j as int], s);
        let tc = back_expr(xp, p, rw, (m - 3) as nat, r, ctx.insert(x, s), env.insert(x, items[j as int]), c, Val::Bool(cv));
        if cv {
            some_var_done(p, (m - 3) as nat, envb, x, v1);
            assert(v1 == Val::Some(Box::new(items[j as int])));
            find_some_fixed(p, (m - 1) as nat, env, acc, x, g, t, y, items, j + 1, items[j as int], w);
            assert(w == Val::Some(Box::new(items[j as int])));
            assert forall|n: nat| n >= tc + 1 implies #[trigger] xfind(xp, n, env, x, c, items, j) == Res::Done(w) by {
                assert(xeval(xp, (n - 1) as nat, env.insert(x, items[j as int]), c) == Res::Done(Val::Bool(true)));
                xs_xfind_hit(xp, n, env, x, c, items, j);
            }
            tc + 1
        } else {
            none_done(p, (m - 3) as nat, envb, t, v1);
            assert(v1 == Val::None);
            let nr = find_back(xp, p, rw, (m - 1) as nat, r, ctx, env, acc, x, c, y, t, s, items, j + 1, w);
            assert forall|n: nat| n >= tc + nr + 1 implies #[trigger] xfind(xp, n, env, x, c, items, j) == Res::Done(w) by {
                assert(xeval(xp, (n - 1) as nat, env.insert(x, items[j as int]), c) == Res::Done(Val::Bool(false)));
                assert(xfind(xp, (n - 1) as nat, env, x, c, items, (j + 1) as nat) == Res::Done(w));
                xs_xfind_miss(xp, n, env, x, c, items, j, Res::Done(w));
            }
            tc + nr + 1
        }
    }
}

// ------------------------------------------------------------------ 束縛の環境の同値（simulation.rs の bind_names_eq の写し）

proof fn bind_names_eq_b(p1: Seq<(nat, Ty)>, p2: Seq<(nat, Ty)>, vs: Seq<Val>, n: nat)
    requires
        p1.len() == p2.len(),
        forall|k: int| 0 <= k < p1.len() ==> #[trigger] p1[k].0 == p2[k].0,
    ensures
        bind(p1, vs, n) == bind(p2, vs, n),
    decreases n,
{
    if n > 0 {
        bind_names_eq_b(p1, p2, vs, (n - 1) as nat);
    }
}

// ------------------------------------------------------------------ 形ごとの逆（閾値を返す）

/// 整数の定数：書換えは同じ定数。
proof fn back_int(xp: XProg, p: Prog, rw: spec_fn(XExpr) -> Expr, m: nat, env: Map<nat, Val>, c: int, w: Val) -> (n0: nat)
    requires
        homomorphic(rw),
        eval(p, m, env, rw(XExpr::Int(c))) == Res::Done(w),
    ensures
        xat(xp, env, XExpr::Int(c), w, n0),
{
    assert(rw(XExpr::Int(c)) == Expr::Int(c));
    reveal_with_fuel(eval, 1);
    assert(w == Val::Int(c));
    xat_leaf_int(xp, env, c)
}

proof fn back_bool(xp: XProg, p: Prog, rw: spec_fn(XExpr) -> Expr, m: nat, env: Map<nat, Val>, b: bool, w: Val) -> (n0: nat)
    requires
        homomorphic(rw),
        eval(p, m, env, rw(XExpr::Bool(b))) == Res::Done(w),
    ensures
        xat(xp, env, XExpr::Bool(b), w, n0),
{
    assert(rw(XExpr::Bool(b)) == Expr::Bool(b));
    bool_done(p, m, env, b, w);
    xat_leaf_bool(xp, env, b)
}

proof fn back_unit(xp: XProg, p: Prog, rw: spec_fn(XExpr) -> Expr, m: nat, env: Map<nat, Val>, w: Val) -> (n0: nat)
    requires
        homomorphic(rw),
        eval(p, m, env, rw(XExpr::Unit)) == Res::Done(w),
    ensures
        xat(xp, env, XExpr::Unit, w, n0),
{
    assert(rw(XExpr::Unit) == Expr::Unit);
    reveal_with_fuel(eval, 1);
    assert(w == Val::Unit);
    xat_leaf_unit(xp, env)
}

proof fn back_char(xp: XProg, p: Prog, rw: spec_fn(XExpr) -> Expr, m: nat, env: Map<nat, Val>, c: int, w: Val) -> (n0: nat)
    requires
        homomorphic(rw),
        eval(p, m, env, rw(XExpr::Char(c))) == Res::Done(w),
    ensures
        xat(xp, env, XExpr::Char(c), w, n0),
{
    assert(rw(XExpr::Char(c)) == Expr::Char(c));
    reveal_with_fuel(eval, 1);
    assert(w == Val::Char(c));
    xat_leaf_char(xp, env, c)
}

proof fn back_none(xp: XProg, p: Prog, rw: spec_fn(XExpr) -> Expr, m: nat, env: Map<nat, Val>, t: Ty, w: Val) -> (n0: nat)
    requires
        homomorphic(rw),
        eval(p, m, env, rw(XExpr::None(t))) == Res::Done(w),
    ensures
        xat(xp, env, XExpr::None(t), w, n0),
{
    assert(rw(XExpr::None(t)) == Expr::None(erase_ty(t)));
    none_done(p, m, env, erase_ty(t), w);
    xat_leaf_none(xp, env, t)
}

proof fn back_var(xp: XProg, p: Prog, rw: spec_fn(XExpr) -> Expr, m: nat, env: Map<nat, Val>, x: nat, w: Val) -> (n0: nat)
    requires
        homomorphic(rw),
        eval(p, m, env, rw(XExpr::Var(x))) == Res::Done(w),
    ensures
        xat(xp, env, XExpr::Var(x), w, n0),
{
    assert(rw(XExpr::Var(x)) == Expr::Var(x));
    reveal_with_fuel(eval, 1);
    assert(env.contains_key(x));
    assert(w == env[x]);
    xat_var(xp, env, x)
}

/// 引数列の逆：各要素は燃料 m - 1 で値になり、残りの列も同じ。閾値は要素ごとの閾値の和。
proof fn back_args(
    xp: XProg,
    p: Prog,
    rw: spec_fn(XExpr) -> Expr,
    m: nat,
    r: nat,
    ctx: Map<nat, Ty>,
    env: Map<nat, Val>,
    es: Seq<XExpr>,
    i: nat,
    vs: Seq<Val>,
) -> (n0: nat)
    requires
        sim_prog(xp, p, rw),
        homomorphic(rw),
        hof_shapes(rw),
        wf(p),
        env_ok(env, ctx),
        ty_args(p, r, ctx, rw_args(rw, es), i) is Some,
        eval_args(p, m, env, rw_args(rw, es), i) == ResSeq::Done(vs),
    ensures
        xat_args(xp, env, es, i, vs, n0),
    decreases m, 1nat,
{
    assert(rw_args(rw, es).len() == es.len());
    if i >= es.len() {
        args_done_empty(p, m, env, rw_args(rw, es), i, vs);
        xat_args_nil(xp, env, es, i)
    } else {
        let vt = inv_args_cons(p, m, env, rw_args(rw, es), i, vs);
        assert(rw_args(rw, es)[i as int] == rw(es[i as int]));
        reveal_with_fuel(ty_args, 1);
        assert(ty_expr(p, r, ctx, rw(es[i as int])) is Some);
        assert(ty_args(p, r, ctx, rw_args(rw, es), (i + 1) as nat) is Some);
        let n1 = back_expr(xp, p, rw, (m - 1) as nat, r, ctx, env, es[i as int], vt.0);
        let n2 = back_args(xp, p, rw, (m - 1) as nat, r, ctx, env, es, (i + 1) as nat, vt.1);
        xat_args_cons(xp, env, es, i, vt.0, vt.1, n1, n2)
    }
}

/// リストの逆：要素の列の閾値。
proof fn back_list(xp: XProg, p: Prog, rw: spec_fn(XExpr) -> Expr, m: nat, r: nat, ctx: Map<nat, Ty>, env: Map<nat, Val>, t: Ty, es: Seq<XExpr>, w: Val) -> (n0: nat)
    requires
        sim_prog(xp, p, rw),
        homomorphic(rw),
        hof_shapes(rw),
        wf(p),
        env_ok(env, ctx),
        ty_expr(p, r, ctx, rw(XExpr::List(t, es))) is Some,
        eval(p, m, env, rw(XExpr::List(t, es))) == Res::Done(w),
    ensures
        xat(xp, env, XExpr::List(t, es), w, n0),
    decreases m, 1nat,
{
    assert(rw(XExpr::List(t, es)) == Expr::List(erase_ty(t), rw_args(rw, es)));
    let vs = inv_list(p, m, env, erase_ty(t), rw_args(rw, es), w);
    reveal_with_fuel(ty_expr, 1);
    assert(ty_args(p, r, ctx, rw_args(rw, es), 0) is Some);
    let n1 = back_args(xp, p, rw, (m - 1) as nat, r, ctx, env, es, 0, vs);
    xat_list(xp, env, t, es, vs, n1)
}

proof fn back_some(xp: XProg, p: Prog, rw: spec_fn(XExpr) -> Expr, m: nat, r: nat, ctx: Map<nat, Ty>, env: Map<nat, Val>, a: XExpr, w: Val) -> (n0: nat)
    requires
        sim_prog(xp, p, rw),
        homomorphic(rw),
        hof_shapes(rw),
        wf(p),
        env_ok(env, ctx),
        ty_expr(p, r, ctx, rw(XExpr::Some(Box::new(a)))) is Some,
        eval(p, m, env, rw(XExpr::Some(Box::new(a)))) == Res::Done(w),
    ensures
        xat(xp, env, XExpr::Some(Box::new(a)), w, n0),
    decreases m, 1nat,
{
    assert(rw(XExpr::Some(Box::new(a))) == Expr::Some(Box::new(rw(a))));
    reveal_with_fuel(ty_expr, 1);
    let va = inv_some(p, m, env, rw(a), w);
    let n1 = back_expr(xp, p, rw, (m - 1) as nat, r, ctx, env, a, va);
    xat_some(xp, env, a, va, n1)
}

proof fn back_pair(xp: XProg, p: Prog, rw: spec_fn(XExpr) -> Expr, m: nat, r: nat, ctx: Map<nat, Ty>, env: Map<nat, Val>, a: XExpr, b: XExpr, w: Val) -> (n0: nat)
    requires
        sim_prog(xp, p, rw),
        homomorphic(rw),
        hof_shapes(rw),
        wf(p),
        env_ok(env, ctx),
        ty_expr(p, r, ctx, rw(XExpr::Pair(Box::new(a), Box::new(b)))) is Some,
        eval(p, m, env, rw(XExpr::Pair(Box::new(a), Box::new(b)))) == Res::Done(w),
    ensures
        xat(xp, env, XExpr::Pair(Box::new(a), Box::new(b)), w, n0),
    decreases m, 1nat,
{
    assert(rw(XExpr::Pair(Box::new(a), Box::new(b))) == Expr::Pair(Box::new(rw(a)), Box::new(rw(b))));
    reveal_with_fuel(ty_expr, 1);
    let vab = inv_pair(p, m, env, rw(a), rw(b), w);
    let n1 = back_expr(xp, p, rw, (m - 1) as nat, r, ctx, env, a, vab.0);
    let n2 = back_expr(xp, p, rw, (m - 1) as nat, r, ctx, env, b, vab.1);
    xat_pair(xp, env, a, b, vab.0, vab.1, n1, n2)
}

proof fn back_builtin(xp: XProg, p: Prog, rw: spec_fn(XExpr) -> Expr, m: nat, r: nat, ctx: Map<nat, Ty>, env: Map<nat, Val>, bi: Builtin, es: Seq<XExpr>, w: Val) -> (n0: nat)
    requires
        sim_prog(xp, p, rw),
        homomorphic(rw),
        hof_shapes(rw),
        wf(p),
        env_ok(env, ctx),
        ty_expr(p, r, ctx, rw(XExpr::Builtin(bi, es))) is Some,
        eval(p, m, env, rw(XExpr::Builtin(bi, es))) == Res::Done(w),
    ensures
        xat(xp, env, XExpr::Builtin(bi, es), w, n0),
    decreases m, 1nat,
{
    assert(rw(XExpr::Builtin(bi, es)) == Expr::Builtin(bi, rw_args(rw, es)));
    reveal_with_fuel(ty_expr, 1);
    let vs = inv_bi(p, m, env, bi, rw_args(rw, es), w);
    assert(ty_args(p, r, ctx, rw_args(rw, es), 0) is Some);
    let n1 = back_args(xp, p, rw, (m - 1) as nat, r, ctx, env, es, 0, vs);
    xat_builtin(xp, env, bi, es, vs, w, n1)
}

/// 呼出しの逆：引数は燃料 m - 1 で vs になり、呼出し先の本体は束縛した環境で燃料 m - 1 で w になる。
proof fn back_call(xp: XProg, p: Prog, rw: spec_fn(XExpr) -> Expr, m: nat, r: nat, ctx: Map<nat, Ty>, env: Map<nat, Val>, g: nat, es: Seq<XExpr>, w: Val) -> (n0: nat)
    requires
        sim_prog(xp, p, rw),
        homomorphic(rw),
        hof_shapes(rw),
        wf(p),
        env_ok(env, ctx),
        ty_expr(p, r, ctx, rw(XExpr::Call(g, es))) is Some,
        eval(p, m, env, rw(XExpr::Call(g, es))) == Res::Done(w),
    ensures
        xat(xp, env, XExpr::Call(g, es), w, n0),
    decreases m, 1nat,
{
    assert(rw(XExpr::Call(g, es)) == Expr::Call(g, rw_args(rw, es)));
    let ts = call_ty_inv(p, r, ctx, rw_args(rw, es), g);
    let vs = inv_call(p, m, env, g, rw_args(rw, es), w);
    let fp = p.funcs[g as int];
    let fx = xp.funcs[g as int];
    assert(erase_sig(fx, fp));
    assert(vs.len() == ts.len());
    sound_args(p, (m - 1) as nat, r, ctx, env, rw_args(rw, es), 0, vs);
    assert forall|k: int| 0 <= k < vs.len() implies val_type(vs[k], fp.params[k].1) by {
        assert(ts[k] == fp.params[k].1);
    }
    bind_ok(fp.params, vs, vs.len());
    bind_names_eq_b(fp.params, fx.params, vs, vs.len());
    assert(fp.body == rw(fx.body));
    assert(ty_expr(p, p.rank[g as int], param_ctx(fp.params, fp.params.len()), fp.body) == Some(fp.ret));
    let env2 = bind(fx.params, vs, vs.len());
    let n2 = back_expr(xp, p, rw, (m - 1) as nat, p.rank[g as int], param_ctx(fp.params, fp.params.len()), env2, fx.body, w);
    let n1 = back_args(xp, p, rw, (m - 1) as nat, r, ctx, env, es, 0, vs);
    xat_call(xp, env, g, es, vs, w, n1, n2)
}

/// let の逆：束縛は燃料 m - 1 で va になり、本体は束縛した環境で燃料 m - 1 で w になる。
proof fn back_let(xp: XProg, p: Prog, rw: spec_fn(XExpr) -> Expr, m: nat, r: nat, ctx: Map<nat, Ty>, env: Map<nat, Val>, x: nat, a: XExpr, b: XExpr, w: Val) -> (n0: nat)
    requires
        sim_prog(xp, p, rw),
        homomorphic(rw),
        hof_shapes(rw),
        wf(p),
        env_ok(env, ctx),
        ty_expr(p, r, ctx, rw(XExpr::Let(x, Box::new(a), Box::new(b)))) is Some,
        eval(p, m, env, rw(XExpr::Let(x, Box::new(a), Box::new(b)))) == Res::Done(w),
    ensures
        xat(xp, env, XExpr::Let(x, Box::new(a), Box::new(b)), w, n0),
    decreases m, 1nat,
{
    assert(rw(XExpr::Let(x, Box::new(a), Box::new(b))) == Expr::Let(x, Box::new(rw(a)), Box::new(rw(b))));
    ty_let_inv(p, r, ctx, x, rw(a), rw(b));
    let va = inv_let(p, m, env, x, rw(a), rw(b), w);
    let na = back_expr(xp, p, rw, (m - 1) as nat, r, ctx, env, a, va);
    sound(p, (m - 1) as nat, r, ctx, env, rw(a), va);
    let ta = ty_expr(p, r, ctx, rw(a))->Some_0;
    env_ok_insert(env, ctx, x, va, ta);
    let nb = back_expr(xp, p, rw, (m - 1) as nat, r, ctx.insert(x, ta), env.insert(x, va), b, w);
    xat_let(xp, env, x, a, b, va, w, na, nb)
}

/// if の逆：条件は燃料 m - 1 で真偽に評価され、選ばれた枝は燃料 m - 1 で w になる。
proof fn back_if(xp: XProg, p: Prog, rw: spec_fn(XExpr) -> Expr, m: nat, r: nat, ctx: Map<nat, Ty>, env: Map<nat, Val>, c: XExpr, a: XExpr, b: XExpr, w: Val) -> (n0: nat)
    requires
        sim_prog(xp, p, rw),
        homomorphic(rw),
        hof_shapes(rw),
        wf(p),
        env_ok(env, ctx),
        ty_expr(p, r, ctx, rw(XExpr::If(Box::new(c), Box::new(a), Box::new(b)))) is Some,
        eval(p, m, env, rw(XExpr::If(Box::new(c), Box::new(a), Box::new(b)))) == Res::Done(w),
    ensures
        xat(xp, env, XExpr::If(Box::new(c), Box::new(a), Box::new(b)), w, n0),
    decreases m, 1nat,
{
    assert(rw(XExpr::If(Box::new(c), Box::new(a), Box::new(b))) == Expr::If(Box::new(rw(c)), Box::new(rw(a)), Box::new(rw(b))));
    ty_if_inv(p, r, ctx, rw(c), rw(a), rw(b));
    let cv = inv_if(p, m, env, rw(c), rw(a), rw(b), w);
    let nc = back_expr(xp, p, rw, (m - 1) as nat, r, ctx, env, c, Val::Bool(cv));
    if cv {
        let na = back_expr(xp, p, rw, (m - 1) as nat, r, ctx, env, a, w);
        xat_if_true(xp, env, c, a, b, w, nc, na)
    } else {
        let nb = back_expr(xp, p, rw, (m - 1) as nat, r, ctx, env, b, w);
        xat_if_false(xp, env, c, a, b, w, nc, nb)
    }
}

/// match_option の逆：調べる式の値 sv で枝が決まる。
proof fn back_match(xp: XProg, p: Prog, rw: spec_fn(XExpr) -> Expr, m: nat, r: nat, ctx: Map<nat, Ty>, env: Map<nat, Val>, mm: XExpr, nb: XExpr, x: nat, sm: XExpr, w: Val) -> (n0: nat)
    requires
        sim_prog(xp, p, rw),
        homomorphic(rw),
        hof_shapes(rw),
        wf(p),
        env_ok(env, ctx),
        ty_expr(p, r, ctx, rw(XExpr::Match(Box::new(mm), Box::new(nb), x, Box::new(sm)))) is Some,
        eval(p, m, env, rw(XExpr::Match(Box::new(mm), Box::new(nb), x, Box::new(sm)))) == Res::Done(w),
    ensures
        xat(xp, env, XExpr::Match(Box::new(mm), Box::new(nb), x, Box::new(sm)), w, n0),
    decreases m, 1nat,
{
    assert(rw(XExpr::Match(Box::new(mm), Box::new(nb), x, Box::new(sm))) == Expr::Match(
        Box::new(rw(mm)),
        Box::new(rw(nb)),
        x,
        Box::new(rw(sm)),
    ));
    let te = ty_match_inv(p, r, ctx, rw(mm), rw(nb), x, rw(sm));
    let sv = inv_match(p, m, env, rw(mm), rw(nb), x, rw(sm), w);
    sound(p, (m - 1) as nat, r, ctx, env, rw(mm), sv);
    let nm = back_expr(xp, p, rw, (m - 1) as nat, r, ctx, env, mm, sv);
    if sv == Val::None {
        let nn = back_expr(xp, p, rw, (m - 1) as nat, r, ctx, env, nb, w);
        xat_match_none(xp, env, mm, nb, x, sm, w, nm, nn)
    } else {
        assert(sv is Some);
        let pl = *sv->Some_0;
        assert(val_type(pl, te));
        env_ok_insert(env, ctx, x, pl, te);
        let ns = back_expr(xp, p, rw, (m - 1) as nat, r, ctx.insert(x, te), env.insert(x, pl), sm, w);
        xat_match_some(xp, env, mm, nb, x, sm, pl, w, nm, ns)
    }
}

/// match_result の逆：調べる式の値で枝が決まる。
proof fn back_matchr(xp: XProg, p: Prog, rw: spec_fn(XExpr) -> Expr, m: nat, r: nat, ctx: Map<nat, Ty>, env: Map<nat, Val>, mm: XExpr, x: nat, a: XExpr, y: nat, b: XExpr, w: Val) -> (n0: nat)
    requires
        sim_prog(xp, p, rw),
        homomorphic(rw),
        hof_shapes(rw),
        wf(p),
        env_ok(env, ctx),
        ty_expr(p, r, ctx, rw(XExpr::MatchR(Box::new(mm), x, Box::new(a), y, Box::new(b)))) is Some,
        eval(p, m, env, rw(XExpr::MatchR(Box::new(mm), x, Box::new(a), y, Box::new(b)))) == Res::Done(w),
    ensures
        xat(xp, env, XExpr::MatchR(Box::new(mm), x, Box::new(a), y, Box::new(b)), w, n0),
    decreases m, 1nat,
{
    assert(rw(XExpr::MatchR(Box::new(mm), x, Box::new(a), y, Box::new(b))) == Expr::MatchR(
        Box::new(rw(mm)),
        x,
        Box::new(rw(a)),
        y,
        Box::new(rw(b)),
    ));
    let tt = ty_matchr_inv(p, r, ctx, rw(mm), x, rw(a), y, rw(b));
    let sv = inv_matchr(p, m, env, rw(mm), x, rw(a), y, rw(b), w);
    sound(p, (m - 1) as nat, r, ctx, env, rw(mm), sv);
    let nm = back_expr(xp, p, rw, (m - 1) as nat, r, ctx, env, mm, sv);
    if sv is Ok {
        let pl = *sv->Ok_0;
        assert(val_type(pl, tt.0));
        env_ok_insert(env, ctx, x, pl, tt.0);
        let na = back_expr(xp, p, rw, (m - 1) as nat, r, ctx.insert(x, tt.0), env.insert(x, pl), a, w);
        xat_matchr_ok(xp, env, mm, x, a, y, b, pl, w, nm, na)
    } else {
        assert(sv is Err);
        let pl = *sv->Err_0;
        assert(val_type(pl, tt.1));
        env_ok_insert(env, ctx, y, pl, tt.1);
        let nb = back_expr(xp, p, rw, (m - 1) as nat, r, ctx.insert(y, tt.1), env.insert(y, pl), b, w);
        xat_matchr_err(xp, env, mm, x, a, y, b, pl, w, nm, nb)
    }
}

/// 注入の逆：中身は燃料 m - 1 で値になる。
proof fn back_inj(xp: XProg, p: Prog, rw: spec_fn(XExpr) -> Expr, m: nat, r: nat, ctx: Map<nat, Ty>, env: Map<nat, Val>, ok: bool, t: Ty, u: Ty, a: XExpr, w: Val) -> (n0: nat)
    requires
        sim_prog(xp, p, rw),
        homomorphic(rw),
        hof_shapes(rw),
        wf(p),
        env_ok(env, ctx),
        ty_expr(p, r, ctx, rw(XExpr::Inj(ok, t, u, Box::new(a)))) is Some,
        eval(p, m, env, rw(XExpr::Inj(ok, t, u, Box::new(a)))) == Res::Done(w),
    ensures
        xat(xp, env, XExpr::Inj(ok, t, u, Box::new(a)), w, n0),
    decreases m, 1nat,
{
    assert(rw(XExpr::Inj(ok, t, u, Box::new(a))) == Expr::Inj(ok, erase_ty(t), erase_ty(u), Box::new(rw(a))));
    reveal_with_fuel(ty_expr, 1);
    let va = inv_inj(p, m, env, ok, erase_ty(t), erase_ty(u), rw(a), w);
    let n1 = back_expr(xp, p, rw, (m - 1) as nat, r, ctx, env, a, va);
    xat_inj(xp, env, ok, t, u, a, va, n1)
}

// ------------------------------------------------------------------ hof の形（写しの名前を取り出して、畳み込みの逆へ）

/// map の逆：写しは reverse(畳み込み)。畳み込みの結果の列 sv から、写像の閾値と値 gv を得る。
proof fn back_map(xp: XProg, p: Prog, rw: spec_fn(XExpr) -> Expr, m: nat, r: nat, ctx: Map<nat, Ty>, env: Map<nat, Val>, xs: XExpr, x: nat, c: XExpr, w: Val) -> (n0: nat)
    requires
        sim_prog(xp, p, rw),
        homomorphic(rw),
        hof_shapes(rw),
        wf(p),
        env_ok(env, ctx),
        ty_expr(p, r, ctx, rw(XExpr::Map(Box::new(xs), x, Box::new(c)))) is Some,
        eval(p, m, env, rw(XExpr::Map(Box::new(xs), x, Box::new(c)))) == Res::Done(w),
    ensures
        xat(xp, env, XExpr::Map(Box::new(xs), x, Box::new(c)), w, n0),
    decreases m, 1nat,
{
    let (t, acc) = map_names(rw, xs, x, c);
    assert(rw(XExpr::Map(Box::new(xs), x, Box::new(c))) == map_collect(rw(xs), t, acc, x, rw(c)));
    let s = map_inv(p, r, ctx, rw(xs), t, acc, x, rw(c));
    let fe = Expr::Fold(Box::new(rw(xs)), Box::new(Expr::List(t, Seq::empty())), acc, x, Box::new(cons_body(rw(c), acc)));
    assert(map_collect(rw(xs), t, acc, x, rw(c)) == Expr::Builtin(Builtin::Reverse, seq![fe]));
    let v1 = inv_builtin1(p, m, env, Builtin::Reverse, fe, w);
    let sl = reverse_inv(v1, w);
    let rr = fold_unfold(p, (m - 2) as nat, env, rw(xs), Expr::List(t, Seq::empty()), acc, x, cons_body(rw(c), acc), v1);
    nil_done(p, (m - 3) as nat, env, t, rr.1);
    let items = rr.0;
    let nx = back_expr(xp, p, rw, (m - 3) as nat, r, ctx, env, xs, Val::List(items));
    sound(p, (m - 3) as nat, r, ctx, env, rw(xs), Val::List(items));
    val_type_list(items, s);
    assert(rr.1 == Val::List(Seq::<Val>::empty()));
    let (nm, gv) = map_back(xp, p, rw, (m - 3) as nat, r, ctx, env, acc, x, c, s, items, 0, Seq::empty(), sl);
    rev_rev(gv);
    assert(sl =~= rev(gv));
    assert(w == Val::List(gv));
    assert forall|n: nat| n >= nx + nm + 1 implies #[trigger] xeval(xp, n, env, XExpr::Map(Box::new(xs), x, Box::new(c))) == Res::Done(Val::List(gv)) by {
        assert(xeval(xp, (n - 1) as nat, env, xs) == Res::Done(Val::List(items)));
        assert(xmap(xp, (n - 1) as nat, env, x, c, items, 0) == ResSeq::Done(gv));
        xs_map(xp, n, env, xs, x, c, items, gv);
    }
    nx + nm + 1
}

/// filter の逆：写しは reverse(畳み込み)。
proof fn back_filter(xp: XProg, p: Prog, rw: spec_fn(XExpr) -> Expr, m: nat, r: nat, ctx: Map<nat, Ty>, env: Map<nat, Val>, xs: XExpr, x: nat, c: XExpr, w: Val) -> (n0: nat)
    requires
        sim_prog(xp, p, rw),
        homomorphic(rw),
        hof_shapes(rw),
        wf(p),
        env_ok(env, ctx),
        ty_expr(p, r, ctx, rw(XExpr::Filter(Box::new(xs), x, Box::new(c)))) is Some,
        eval(p, m, env, rw(XExpr::Filter(Box::new(xs), x, Box::new(c)))) == Res::Done(w),
    ensures
        xat(xp, env, XExpr::Filter(Box::new(xs), x, Box::new(c)), w, n0),
    decreases m, 1nat,
{
    let (t, acc) = filter_names(rw, xs, x, c);
    assert(rw(XExpr::Filter(Box::new(xs), x, Box::new(c))) == filter_collect(rw(xs), t, acc, x, rw(c)));
    let s = filter_inv(p, r, ctx, rw(xs), t, acc, x, rw(c));
    let fe = Expr::Fold(Box::new(rw(xs)), Box::new(Expr::List(t, Seq::empty())), acc, x, Box::new(filter_body(rw(c), acc, x)));
    assert(filter_collect(rw(xs), t, acc, x, rw(c)) == Expr::Builtin(Builtin::Reverse, seq![fe]));
    let v1 = inv_builtin1(p, m, env, Builtin::Reverse, fe, w);
    let sl = reverse_inv(v1, w);
    let rr = fold_unfold(p, (m - 2) as nat, env, rw(xs), Expr::List(t, Seq::empty()), acc, x, filter_body(rw(c), acc, x), v1);
    nil_done(p, (m - 3) as nat, env, t, rr.1);
    let items = rr.0;
    let nx = back_expr(xp, p, rw, (m - 3) as nat, r, ctx, env, xs, Val::List(items));
    sound(p, (m - 3) as nat, r, ctx, env, rw(xs), Val::List(items));
    val_type_list(items, s);
    assert(rr.1 == Val::List(Seq::<Val>::empty()));
    let (nf, out) = filter_back(xp, p, rw, (m - 3) as nat, r, ctx, env, acc, x, c, s, items, 0, Seq::empty(), sl);
    rev_rev(out);
    assert(sl =~= rev(out));
    assert(w == Val::List(out));
    assert forall|n: nat| n >= nx + nf + 1 implies #[trigger] xeval(xp, n, env, XExpr::Filter(Box::new(xs), x, Box::new(c))) == Res::Done(Val::List(out)) by {
        assert(xeval(xp, (n - 1) as nat, env, xs) == Res::Done(Val::List(items)));
        assert(xfilter(xp, (n - 1) as nat, env, x, c, items, 0) == ResSeq::Done(out));
        xs_filter(xp, n, env, xs, x, c, items, out);
    }
    nx + nf + 1
}

/// any の逆：写しは fold(xs, false, |acc, x| if acc then true else c)。
proof fn back_any(xp: XProg, p: Prog, rw: spec_fn(XExpr) -> Expr, m: nat, r: nat, ctx: Map<nat, Ty>, env: Map<nat, Val>, xs: XExpr, x: nat, c: XExpr, w: Val) -> (n0: nat)
    requires
        sim_prog(xp, p, rw),
        homomorphic(rw),
        hof_shapes(rw),
        wf(p),
        env_ok(env, ctx),
        ty_expr(p, r, ctx, rw(XExpr::Any(Box::new(xs), x, Box::new(c)))) is Some,
        eval(p, m, env, rw(XExpr::Any(Box::new(xs), x, Box::new(c)))) == Res::Done(w),
    ensures
        xat(xp, env, XExpr::Any(Box::new(xs), x, Box::new(c)), w, n0),
    decreases m, 1nat,
{
    let acc = any_names(rw, xs, x, c);
    assert(rw(XExpr::Any(Box::new(xs), x, Box::new(c))) == any_fold(rw(xs), acc, x, rw(c)));
    let s = any_inv(p, r, ctx, rw(xs), acc, x, rw(c));
    let body = Expr::If(Box::new(Expr::Var(acc)), Box::new(Expr::Bool(true)), Box::new(rw(c)));
    assert(any_fold(rw(xs), acc, x, rw(c)) == Expr::Fold(Box::new(rw(xs)), Box::new(Expr::Bool(false)), acc, x, Box::new(body)));
    let rr = fold_unfold(p, m, env, rw(xs), Expr::Bool(false), acc, x, body, w);
    bool_done(p, (m - 1) as nat, env, false, rr.1);
    let items = rr.0;
    let tt = ty_fold_inv(p, r, ctx, rw(xs), Expr::Bool(false), acc, x, body);
    assert(ty_expr(p, r, ctx, Expr::Bool(false)) == Some(Ty::Bool));
    assert(tt.1 == Ty::Bool);
    sound(p, m, r, ctx, env, any_fold(rw(xs), acc, x, rw(c)), w);
    let b = bool_val(w);
    assert(rr.1 == Val::Bool(false));
    let nx = back_expr(xp, p, rw, (m - 1) as nat, r, ctx, env, xs, Val::List(items));
    sound(p, (m - 1) as nat, r, ctx, env, rw(xs), Val::List(items));
    val_type_list(items, s);
    let na = any_back(xp, p, rw, (m - 1) as nat, r, ctx, env, acc, x, c, s, items, 0, b);
    assert(w == Val::Bool(b));
    assert forall|n: nat| n >= nx + na + 1 implies #[trigger] xeval(xp, n, env, XExpr::Any(Box::new(xs), x, Box::new(c))) == Res::Done(Val::Bool(b)) by {
        assert(xeval(xp, (n - 1) as nat, env, xs) == Res::Done(Val::List(items)));
        assert(xany(xp, (n - 1) as nat, env, x, c, items, 0) == Res::Done(Val::Bool(b)));
        xs_any(xp, n, env, xs, x, c, items, Res::Done(Val::Bool(b)));
    }
    nx + na + 1
}

/// all の逆：写しは fold(xs, true, |acc, x| if acc then c else false)。
proof fn back_all(xp: XProg, p: Prog, rw: spec_fn(XExpr) -> Expr, m: nat, r: nat, ctx: Map<nat, Ty>, env: Map<nat, Val>, xs: XExpr, x: nat, c: XExpr, w: Val) -> (n0: nat)
    requires
        sim_prog(xp, p, rw),
        homomorphic(rw),
        hof_shapes(rw),
        wf(p),
        env_ok(env, ctx),
        ty_expr(p, r, ctx, rw(XExpr::All(Box::new(xs), x, Box::new(c)))) is Some,
        eval(p, m, env, rw(XExpr::All(Box::new(xs), x, Box::new(c)))) == Res::Done(w),
    ensures
        xat(xp, env, XExpr::All(Box::new(xs), x, Box::new(c)), w, n0),
    decreases m, 1nat,
{
    let acc = all_names(rw, xs, x, c);
    assert(rw(XExpr::All(Box::new(xs), x, Box::new(c))) == all_fold(rw(xs), acc, x, rw(c)));
    let s = all_inv(p, r, ctx, rw(xs), acc, x, rw(c));
    let body = Expr::If(Box::new(Expr::Var(acc)), Box::new(rw(c)), Box::new(Expr::Bool(false)));
    assert(all_fold(rw(xs), acc, x, rw(c)) == Expr::Fold(Box::new(rw(xs)), Box::new(Expr::Bool(true)), acc, x, Box::new(body)));
    let rr = fold_unfold(p, m, env, rw(xs), Expr::Bool(true), acc, x, body, w);
    bool_done(p, (m - 1) as nat, env, true, rr.1);
    let items = rr.0;
    let tt = ty_fold_inv(p, r, ctx, rw(xs), Expr::Bool(true), acc, x, body);
    assert(ty_expr(p, r, ctx, Expr::Bool(true)) == Some(Ty::Bool));
    assert(tt.1 == Ty::Bool);
    sound(p, m, r, ctx, env, all_fold(rw(xs), acc, x, rw(c)), w);
    let b = bool_val(w);
    assert(rr.1 == Val::Bool(true));
    let nx = back_expr(xp, p, rw, (m - 1) as nat, r, ctx, env, xs, Val::List(items));
    sound(p, (m - 1) as nat, r, ctx, env, rw(xs), Val::List(items));
    val_type_list(items, s);
    let na = all_back(xp, p, rw, (m - 1) as nat, r, ctx, env, acc, x, c, s, items, 0, b);
    assert(w == Val::Bool(b));
    assert forall|n: nat| n >= nx + na + 1 implies #[trigger] xeval(xp, n, env, XExpr::All(Box::new(xs), x, Box::new(c))) == Res::Done(Val::Bool(b)) by {
        assert(xeval(xp, (n - 1) as nat, env, xs) == Res::Done(Val::List(items)));
        assert(xall(xp, (n - 1) as nat, env, x, c, items, 0) == Res::Done(Val::Bool(b)));
        xs_all(xp, n, env, xs, x, c, items, Res::Done(Val::Bool(b)));
    }
    nx + na + 1
}

/// find の逆：写しは fold(xs, None, |acc, x| select)。
proof fn back_find(xp: XProg, p: Prog, rw: spec_fn(XExpr) -> Expr, m: nat, r: nat, ctx: Map<nat, Ty>, env: Map<nat, Val>, xs: XExpr, x: nat, c: XExpr, w: Val) -> (n0: nat)
    requires
        sim_prog(xp, p, rw),
        homomorphic(rw),
        hof_shapes(rw),
        wf(p),
        env_ok(env, ctx),
        ty_expr(p, r, ctx, rw(XExpr::Find(Box::new(xs), x, Box::new(c)))) is Some,
        eval(p, m, env, rw(XExpr::Find(Box::new(xs), x, Box::new(c)))) == Res::Done(w),
    ensures
        xat(xp, env, XExpr::Find(Box::new(xs), x, Box::new(c)), w, n0),
    decreases m, 1nat,
{
    let nms = find_names(rw, xs, x, c);
    let t = nms.0;
    let acc = nms.1;
    let y = nms.2;
    assert(rw(XExpr::Find(Box::new(xs), x, Box::new(c))) == find_fold(rw(xs), t, acc, x, rw(c), y));
    let s = find_inv(p, r, ctx, rw(xs), t, acc, x, rw(c), y);
    let body = select_body(rw(c), t, acc, x, y);
    let rr = fold_unfold(p, m, env, rw(xs), Expr::None(t), acc, x, body, w);
    none_done(p, (m - 1) as nat, env, t, rr.1);
    let items = rr.0;
    let nx = back_expr(xp, p, rw, (m - 1) as nat, r, ctx, env, xs, Val::List(items));
    sound(p, (m - 1) as nat, r, ctx, env, rw(xs), Val::List(items));
    val_type_list(items, s);
    assert(rr.1 == Val::None);
    let nf = find_back(xp, p, rw, (m - 1) as nat, r, ctx, env, acc, x, c, y, t, s, items, 0, w);
    assert forall|n: nat| n >= nx + nf + 1 implies #[trigger] xeval(xp, n, env, XExpr::Find(Box::new(xs), x, Box::new(c))) == Res::Done(w) by {
        assert(xeval(xp, (n - 1) as nat, env, xs) == Res::Done(Val::List(items)));
        assert(xfind(xp, (n - 1) as nat, env, x, c, items, 0) == Res::Done(w));
        xs_find(xp, n, env, xs, x, c, items, Res::Done(w));
    }
    nx + nf + 1
}

/// 畳み込みの逆（源の畳み込みそのもの）：列の値 items と初期値 v0 の閾値、および畳み込みの閾値を集める。
proof fn back_fold(xp: XProg, p: Prog, rw: spec_fn(XExpr) -> Expr, m: nat, r: nat, ctx: Map<nat, Ty>, env: Map<nat, Val>, xs: XExpr, init: XExpr, acc: nat, item: nat, body: XExpr, w: Val) -> (n0: nat)
    requires
        sim_prog(xp, p, rw),
        homomorphic(rw),
        hof_shapes(rw),
        wf(p),
        env_ok(env, ctx),
        ty_expr(p, r, ctx, rw(XExpr::Fold(Box::new(xs), Box::new(init), acc, item, Box::new(body)))) is Some,
        eval(p, m, env, rw(XExpr::Fold(Box::new(xs), Box::new(init), acc, item, Box::new(body)))) == Res::Done(w),
    ensures
        xat(xp, env, XExpr::Fold(Box::new(xs), Box::new(init), acc, item, Box::new(body)), w, n0),
    decreases m, 1nat,
{
    assert(rw(XExpr::Fold(Box::new(xs), Box::new(init), acc, item, Box::new(body))) == Expr::Fold(Box::new(rw(xs)), Box::new(rw(init)), acc, item, Box::new(rw(body))));
    let tt = ty_fold_inv(p, r, ctx, rw(xs), rw(init), acc, item, rw(body));
    let rr = fold_unfold(p, m, env, rw(xs), rw(init), acc, item, rw(body), w);
    let items = rr.0;
    let v0 = rr.1;
    assert(m >= 1);
    sound(p, (m - 1) as nat, r, ctx, env, rw(init), v0);
    assert(ty_expr(p, r, ctx, rw(init)) == Some(tt.1));
    assert(val_type(v0, tt.1));
    sound(p, (m - 1) as nat, r, ctx, env, rw(xs), Val::List(items));
    assert(ty_expr(p, r, ctx, rw(xs)) == Some(Ty::List(Box::new(tt.0))));
    val_type_list(items, tt.0);
    let nx = back_expr(xp, p, rw, (m - 1) as nat, r, ctx, env, xs, Val::List(items));
    let ni = back_expr(xp, p, rw, (m - 1) as nat, r, ctx, env, init, v0);
    let nf = fold_back(xp, p, rw, (m - 1) as nat, r, ctx, env, acc, item, body, tt.1, tt.0, items, 0, v0, w);
    assert forall|n: nat| n >= nx + ni + nf + 1 implies #[trigger] xeval(xp, n, env, XExpr::Fold(Box::new(xs), Box::new(init), acc, item, Box::new(body))) == Res::Done(w) by {
        assert(xeval(xp, (n - 1) as nat, env, xs) == Res::Done(Val::List(items)));
        assert(xeval(xp, (n - 1) as nat, env, init) == Res::Done(v0));
        assert(xeval_fold(xp, (n - 1) as nat, env, acc, item, body, items, 0, v0) == Res::Done(w));
        xs_fold(xp, n, env, xs, init, acc, item, body, items, v0, Res::Done(w));
    }
    nx + ni + nf + 1
}

// ------------------------------------------------------------------ sort_by：鍵の取り出しと整列の逆

/// 整数の型の値は整数の値。
proof fn int_val(v: Val) -> (c: int)
    requires
        val_type(v, Ty::Int),
    ensures
        v == Val::Int(c),
{
    int_of_ty(v);
    match v {
        Val::Int(c) => c,
        _ => {
            assert(false);
            0
        },
    }
}

/// 内側の畳み込みの初期状態の値：(None, ([], false))。
proof fn init_state_val(p: Prog, f: nat, env: Map<nat, Val>, t: Ty, v0: Val)
    requires
        eval(p, f, env, init_state(t)) == Res::Done(v0),
    ensures
        v0 == Val::Pair(Box::new(Val::None), Box::new(Val::Pair(Box::new(Val::List(Seq::<Val>::empty())), Box::new(Val::Bool(false))))),
{
    let vab = inv_pair(p, f, env, Expr::None(Ty::Int), pair_e(Expr::List(t, Seq::empty()), Expr::Bool(false)), v0);
    none_done(p, (f - 1) as nat, env, Ty::Int, vab.0);
    let vb = inv_pair(p, (f - 1) as nat, env, Expr::List(t, Seq::empty()), Expr::Bool(false), vab.1);
    nil_done(p, (f - 2) as nat, env, t, vb.0);
    bool_done(p, (f - 2) as nat, env, false, vb.1);
}

/// 内側の畳み込みの初期状態では、置いた印（状態の第二の第二成分）は偽。
proof fn cond_init_false(p: Prog, f: nat, env: Map<nat, Val>, st: nat, v0: Val, cv: bool)
    requires
        env.contains_key(st),
        env[st] == v0,
        v0 == Val::Pair(Box::new(Val::None), Box::new(Val::Pair(Box::new(Val::List(Seq::<Val>::empty())), Box::new(Val::Bool(false))))),
        eval(p, f, env, sort_cond(st)) == Res::Done(Val::Bool(cv)),
    ensures
        !cv,
{
    let v1 = inv_builtin1(p, f, env, Builtin::Snd, psnd(Expr::Var(st)), Val::Bool(cv));
    let v2 = inv_builtin1(p, (f - 2) as nat, env, Builtin::Snd, Expr::Var(st), v1);
    eval_var_val(p, (f - 4) as nat, env, st);
    assert(v2 == v0);
    assert(v1 == Val::Pair(Box::new(Val::List(Seq::<Val>::empty())), Box::new(Val::Bool(false))));
    assert(!cv);
}

/// 鍵の式の値は、束縛 acc・e・st・y を外しても同じ（eval 版）。
proof fn key_drop(p: Prog, n: nat, env: Map<nat, Val>, acc: nat, a: Val, e: nat, ev: Val, st: nat, sv: Val, y: nat, yv: Val, x: nat, k: Expr)
    requires
        acc != x,
        e != x,
        st != x,
        y != x,
        absent(acc, k),
        absent(e, k),
        absent(st, k),
        absent(y, k),
    ensures
        eval(p, n, env.insert(acc, a).insert(e, ev).insert(st, sv).insert(y, yv).insert(x, yv), k) == eval(p, n, env.insert(x, yv), k),
{
    eval_drop(p, n, env.insert(acc, a).insert(e, ev).insert(st, sv), y, yv, x, yv, k);
    eval_drop(p, n, env.insert(acc, a).insert(e, ev), st, sv, x, yv, k);
    eval_drop(p, n, env.insert(acc, a), e, ev, x, yv, k);
    eval_drop(p, n, env, acc, a, x, yv, k);
}

/// 整列の結果の決め方：評価が列 v に行くなら、ある燃料で w に行く評価は w = v に等しい。
proof fn evals_to_done_eq(p: Prog, env: Map<nat, Val>, e: Expr, v: Val, m: nat, w: Val)
    requires
        evals_to(p, env, e, v),
        eval(p, m, env, e) == Res::Done(w),
    ensures
        w == v,
{
    let n2 = choose|n: nat| #[trigger] eval(p, n, env, e) == Res::Done(v);
    eval_deterministic(p, m, n2, env, e);
}

/// 並べ替えの畳み込みの逆：外側の畳み込みの段ごとに、要素の鍵の閾値と鍵の値（整数）を集める。
/// lst は段の始めの整列済みの列。結果の列は要素 j 以降の鍵の値で、写しの鍵の閾値と一致する。
proof fn sort_walk(
    xp: XProg,
    p: Prog,
    rw: spec_fn(XExpr) -> Expr,
    m: nat,
    r: nat,
    ctx: Map<nat, Ty>,
    env: Map<nat, Val>,
    acc: nat,
    e: nat,
    st: nat,
    y: nat,
    ky: nat,
    ke: nat,
    rb: nat,
    x: nat,
    k: XExpr,
    t: Ty,
    s: Ty,
    items: Seq<Val>,
    j: nat,
    lst: Seq<Val>,
    w: Val,
) -> (res: (nat, Seq<Val>))
    requires
        sim_prog(xp, p, rw),
        homomorphic(rw),
        hof_shapes(rw),
        wf(p),
        env_ok(env, ctx),
        names_ok(acc, e, st, y, ky, ke, rb, x),
        absent(acc, rw(k)),
        absent(e, rw(k)),
        absent(st, rw(k)),
        absent(y, rw(k)),
        ty_expr(p, r, ctx.insert(x, s), rw(k)) == Some(Ty::Int),
        forall|i: int| #![trigger items[i]] j <= i < items.len() ==> val_type(items[i], s),
        eval_fold(p, m, env, acc, e, sort_body(t, acc, e, st, y, ky, ke, rb, x, rw(k)), items, j, Val::List(lst)) == Res::Done(w),
    ensures
        forall|n: nat| n >= res.0 ==> #[trigger] xmap(xp, n, env, x, k, items, j) == ResSeq::Done(res.1),
        forall|i: int| #![trigger res.1[i]] 0 <= i < res.1.len() ==> res.1[i] is Int,
        forall|i: int| #![trigger res.1[i]] 0 <= i < res.1.len() ==> evals_to(p, env.insert(x, items[j as int + i]), rw(k), res.1[i]),
        j <= items.len() ==> res.1.len() + j == items.len(),
    decreases m, 0nat,
{
    reveal_with_fuel(eval_fold, 1);
    if j >= items.len() {
        assert forall|n: nat| n >= 1 implies #[trigger] xmap(xp, n, env, x, k, items, j) == ResSeq::Done(Seq::<Val>::empty()) by {
            xs_xmap_nil(xp, n, env, x, k, items, j);
        }
        (1, Seq::empty())
    } else {
        let g = rw(k);
        let body = sort_body(t, acc, e, st, y, ky, ke, rb, x, g);
        let a = Val::List(lst);
        let u = items[j as int];
        let v1 = fold_step_val(p, m, env, acc, e, body, items, j, a, w);
        let inner = Expr::Fold(Box::new(cons_e(Expr::Var(e), Expr::Var(acc))), Box::new(init_state(t)), st, y, Box::new(sort_inner(e, st, y, ky, ke, x, g)));
        let revb = Expr::Builtin(Builtin::Reverse, seq![sort_rev(e, rb)]);
        assert(body == Expr::Let(rb, Box::new(inner), Box::new(revb)));
        let env_s = env.insert(acc, a).insert(e, u);
        assert(env_s.contains_key(acc) && env_s[acc] == a);
        assert(env_s.contains_key(e) && env_s[e] == u);
        let va = inv_let(p, (m - 1) as nat, env_s, rb, inner, revb, v1);
        let vr = inv_builtin1(p, (m - 2) as nat, env_s.insert(rb, va), Builtin::Reverse, sort_rev(e, rb), v1);
        let srev = reverse_inv(vr, v1);
        assert(v1 == Val::List(rev(srev)));
        let fu = fold_unfold(p, (m - 2) as nat, env_s, cons_e(Expr::Var(e), Expr::Var(acc)), init_state(t), st, y, sort_inner(e, st, y, ky, ke, x, g), va);
        let itsin = fu.0;
        let v0in = fu.1;
        assert(cons_e(Expr::Var(e), Expr::Var(acc)) == Expr::Builtin(Builtin::Cons, seq![Expr::Var(e), Expr::Var(acc)]));
        inv_cons_head_var(p, (m - 3) as nat, env_s, e, acc, lst, Val::List(itsin));
        assert(itsin == seq![u] + lst);
        assert(itsin[0] == u);
        init_state_val(p, (m - 3) as nat, env_s, t, v0in);
        let v1in = fold_step_val(p, (m - 3) as nat, env_s, st, y, sort_inner(e, st, y, ky, ke, x, g), itsin, 0, v0in, va);
        let envb = env_s.insert(st, v0in).insert(y, u);
        assert(envb.contains_key(st) && envb[st] == v0in);
        let cv = inv_if(p, (m - 4) as nat, envb, sort_cond(st), sort_placed(st, y), sort_fresh(e, st, y, ky, ke, x, g), v1in);
        cond_init_false(p, (m - 5) as nat, envb, st, v0in, cv);
        assert(!cv);
        let kv = inv_let(p, (m - 5) as nat, envb, ky, Expr::Let(x, Box::new(Expr::Var(y)), Box::new(g)), sort_match(e, st, y, ky, ke), v1in);
        let yv = inv_let(p, (m - 6) as nat, envb, x, Expr::Var(y), g, kv);
        done_fuel_pos(p, (m - 7) as nat, envb, Expr::Var(y), yv);
        eval_var_val(p, (m - 7) as nat, envb, y);
        assert(yv == u);
        key_drop(p, (m - 7) as nat, env, acc, a, e, u, st, v0in, y, u, x, g);
        assert(eval(p, (m - 7) as nat, env.insert(x, u), g) == Res::Done(kv));
        assert(val_type(u, s));
        env_ok_insert(env, ctx, x, u, s);
        sound(p, (m - 7) as nat, r, ctx.insert(x, s), env.insert(x, u), g, kv);
        assert(val_type(kv, Ty::Int));
        let c = int_val(kv);
        assert(kv == Val::Int(c));
        let tk = back_expr(xp, p, rw, (m - 7) as nat, r, ctx.insert(x, s), env.insert(x, u), k, Val::Int(c));
        let rest = sort_walk(xp, p, rw, (m - 1) as nat, r, ctx, env, acc, e, st, y, ky, ke, rb, x, k, t, s, items, j + 1, rev(srev), w);
        let res_seq = seq![Val::Int(c)] + rest.1;
        assert forall|n: nat| n >= tk + rest.0 + 1 implies #[trigger] xmap(xp, n, env, x, k, items, j) == ResSeq::Done(res_seq) by {
            assert(xeval(xp, (n - 1) as nat, env.insert(x, items[j as int]), k) == Res::Done(Val::Int(c)));
            assert(xmap(xp, (n - 1) as nat, env, x, k, items, (j + 1) as nat) == ResSeq::Done(rest.1));
            xs_xmap_cons(xp, n, env, x, k, items, j, Val::Int(c), rest.1);
        }
        assert forall|i: int| 0 <= i < res_seq.len() implies #[trigger] res_seq[i] is Int by {
            if i > 0 {
                assert(res_seq[i] == rest.1[i - 1]);
            }
        }
        assert forall|i: int| 0 <= i < res_seq.len() implies evals_to(p, env.insert(x, items[j as int + i]), g, #[trigger] res_seq[i]) by {
            if i == 0 {
                assert(items[j as int + i] == u);
                assert(eval(p, (m - 7) as nat, env.insert(x, u), g) == Res::Done(Val::Int(c)));
                assert(evals_to(p, env.insert(x, u), g, Val::Int(c)));
            } else {
                assert(res_seq[i] == rest.1[i - 1]);
                assert(items[j as int + i] == items[(j + 1) as int + (i - 1)]);
            }
        }
        (tk + rest.0 + 1, res_seq)
    }
}

/// sort_by の逆：書換えの整列の列と鍵を、閾値つきの写しの鍵から集め、整列の意味（sort_core_meaning）で結果を定める。
proof fn back_sort(xp: XProg, p: Prog, rw: spec_fn(XExpr) -> Expr, m: nat, r: nat, ctx: Map<nat, Ty>, env: Map<nat, Val>, xs: XExpr, x: nat, k: XExpr, w: Val) -> (n0: nat)
    requires
        sim_prog(xp, p, rw),
        homomorphic(rw),
        hof_shapes(rw),
        wf(p),
        env_ok(env, ctx),
        ty_expr(p, r, ctx, rw(XExpr::SortBy(Box::new(xs), x, Box::new(k)))) is Some,
        eval(p, m, env, rw(XExpr::SortBy(Box::new(xs), x, Box::new(k)))) == Res::Done(w),
    ensures
        xat(xp, env, XExpr::SortBy(Box::new(xs), x, Box::new(k)), w, n0),
    decreases m, 1nat,
{
    let nm = sort_names(rw, xs, x, k);
    let t = nm.0;
    let acc = nm.1;
    let e = nm.2;
    let st = nm.3;
    let y = nm.4;
    let ky = nm.5;
    let ke = nm.6;
    let rb = nm.7;
    assert(rw(XExpr::SortBy(Box::new(xs), x, Box::new(k))) == sort_collect(rw(xs), t, acc, e, st, y, ky, ke, rb, x, rw(k)));
    let s = sort_inv(p, r, ctx, rw(xs), t, acc, e, st, y, ky, ke, rb, x, rw(k));
    let body = sort_body(t, acc, e, st, y, ky, ke, rb, x, rw(k));
    assert(sort_collect(rw(xs), t, acc, e, st, y, ky, ke, rb, x, rw(k)) == Expr::Fold(Box::new(rw(xs)), Box::new(Expr::List(t, Seq::empty())), acc, e, Box::new(body)));
    let rr = fold_unfold(p, m, env, rw(xs), Expr::List(t, Seq::empty()), acc, e, body, w);
    assert(m >= 1);
    nil_done(p, (m - 1) as nat, env, t, rr.1);
    assert(rr.1 == Val::List(Seq::<Val>::empty()));
    let items = rr.0;
    sound(p, (m - 1) as nat, r, ctx, env, rw(xs), Val::List(items));
    val_type_list(items, s);
    let nx = back_expr(xp, p, rw, (m - 1) as nat, r, ctx, env, xs, Val::List(items));
    let wl = sort_walk(xp, p, rw, (m - 1) as nat, r, ctx, env, acc, e, st, y, ky, ke, rb, x, k, t, s, items, 0, Seq::empty(), w);
    let nk = wl.0;
    let gs = wl.1;
    assert(gs.len() == items.len());
    let keys = Seq::new(items.len(), |i: int| gs[i]->Int_0);
    assert(keys.len() == items.len());
    assert forall|i: int| 0 <= i < gs.len() implies gs[i] == Val::Int(#[trigger] keys[i]) by {
        assert(gs[i] is Int);
    }
    assert(gs =~= Seq::new(keys.len(), |i: int| Val::Int(keys[i])));
    int_seq_of(keys);
    assert(int_seq(gs) == Some(keys));
    assert forall|mm: int| 0 <= mm < items.len() implies evals_to(p, env.insert(x, items[mm]), rw(k), #[trigger] gs[mm]) by {
        assert(items[0 as int + mm] == items[mm]);
    }
    assert(evals_to(p, env, rw(xs), Val::List(items))) by {
        assert(eval(p, (m - 1) as nat, env, rw(xs)) == Res::Done(Val::List(items)));
    }
    let zp = zip_keys(items, keys);
    assert forall|mm: int| 0 <= mm < zp.len() implies evals_to(p, env.insert(x, #[trigger] zp[mm].0), rw(k), Val::Int(zp[mm].1)) by {
        assert(zp[mm].0 == items[mm]);
        assert(zp[mm].1 == keys[mm]);
        assert(gs[mm] == Val::Int(keys[mm]));
    }
    assert(keyed(p, env, x, rw(k), zp));
    sort_core_meaning(p, env, rw(xs), t, acc, e, st, y, ky, ke, rb, x, rw(k), items, keys);
    assert(eval(p, m, env, sort_collect(rw(xs), t, acc, e, st, y, ky, ke, rb, x, rw(k))) == Res::Done(w));
    evals_to_done_eq(p, env, sort_collect(rw(xs), t, acc, e, st, y, ky, ke, rb, x, rw(k)), Val::List(sort_vals(items, keys)), m, w);
    assert forall|n: nat| n >= nx + nk + 1 implies #[trigger] xeval(xp, n, env, XExpr::SortBy(Box::new(xs), x, Box::new(k))) == Res::Done(w) by {
        assert(xeval(xp, (n - 1) as nat, env, xs) == Res::Done(Val::List(items)));
        assert(xmap(xp, (n - 1) as nat, env, x, k, items, 0) == ResSeq::Done(gs));
        xs_sort(xp, n, env, xs, x, k, items, gs, keys);
    }
    nx + nk + 1
}

// ------------------------------------------------------------------ 形の振り分けと入口

/// 書換え後の式が燃料 m で w を返すなら、源の式は閾値以上で w を返す（形で分ける）。
proof fn back_expr(xp: XProg, p: Prog, rw: spec_fn(XExpr) -> Expr, m: nat, r: nat, ctx: Map<nat, Ty>, env: Map<nat, Val>, e: XExpr, w: Val) -> (n0: nat)
    requires
        sim_prog(xp, p, rw),
        homomorphic(rw),
        hof_shapes(rw),
        wf(p),
        env_ok(env, ctx),
        ty_expr(p, r, ctx, rw(e)) is Some,
        eval(p, m, env, rw(e)) == Res::Done(w),
    ensures
        xat(xp, env, e, w, n0),
    decreases m, 2nat,
{
    match e {
        XExpr::Int(c) => back_int(xp, p, rw, m, env, c, w),
        XExpr::Bool(b) => back_bool(xp, p, rw, m, env, b, w),
        XExpr::Unit => back_unit(xp, p, rw, m, env, w),
        XExpr::Char(c) => back_char(xp, p, rw, m, env, c, w),
        XExpr::Var(x) => back_var(xp, p, rw, m, env, x, w),
        XExpr::List(t, es) => back_list(xp, p, rw, m, r, ctx, env, t, es, w),
        XExpr::Some(a) => back_some(xp, p, rw, m, r, ctx, env, *a, w),
        XExpr::None(t) => back_none(xp, p, rw, m, env, t, w),
        XExpr::Pair(a, b) => back_pair(xp, p, rw, m, r, ctx, env, *a, *b, w),
        XExpr::Builtin(bi, es) => back_builtin(xp, p, rw, m, r, ctx, env, bi, es, w),
        XExpr::Call(g, es) => back_call(xp, p, rw, m, r, ctx, env, g, es, w),
        XExpr::Let(x, a, b) => back_let(xp, p, rw, m, r, ctx, env, x, *a, *b, w),
        XExpr::If(c, a, b) => back_if(xp, p, rw, m, r, ctx, env, *c, *a, *b, w),
        XExpr::Fold(xs, init, acc, item, body) => back_fold(xp, p, rw, m, r, ctx, env, *xs, *init, acc, item, *body, w),
        XExpr::Match(mm, nb, x, sm) => back_match(xp, p, rw, m, r, ctx, env, *mm, *nb, x, *sm, w),
        XExpr::Inj(ok, t, u, a) => back_inj(xp, p, rw, m, r, ctx, env, ok, t, u, *a, w),
        XExpr::MatchR(mm, x, a, y, b) => back_matchr(xp, p, rw, m, r, ctx, env, *mm, x, *a, y, *b, w),
        XExpr::Map(xs, x, c) => back_map(xp, p, rw, m, r, ctx, env, *xs, x, *c, w),
        XExpr::Filter(xs, x, c) => back_filter(xp, p, rw, m, r, ctx, env, *xs, x, *c, w),
        XExpr::Any(xs, x, c) => back_any(xp, p, rw, m, r, ctx, env, *xs, x, *c, w),
        XExpr::All(xs, x, c) => back_all(xp, p, rw, m, r, ctx, env, *xs, x, *c, w),
        XExpr::Find(xs, x, c) => back_find(xp, p, rw, m, r, ctx, env, *xs, x, *c, w),
        XExpr::SortBy(xs, x, k) => back_sort(xp, p, rw, m, r, ctx, env, *xs, x, *k, w),
    }
}

/// SH4 の逆（型の付いたプログラム）：書換え後の入口が燃料 m で w を返すなら、源の入口は十分大きい燃料で w を返す。
pub proof fn sh4_back_typed(xp: XProg, p: Prog, rw: spec_fn(XExpr) -> Expr, v: Val)
    requires
        xp.entry < xp.funcs.len(),
        sim_prog(xp, p, rw),
        homomorphic(rw),
        hof_shapes(rw),
        wf(p),
        val_type(v, p.funcs[p.entry as int].params[0].1),
    ensures
        forall|m: nat, w: Val| eval_entry(p, m, v) == Res::Done(w) ==> exists|n: nat| xeval_entry(xp, n, v) == Res::Done(w),
{
    assert forall|m: nat, w: Val| eval_entry(p, m, v) == Res::Done(w) implies exists|n: nat| xeval_entry(xp, n, v) == Res::Done(w) by {
        let fx = xp.funcs[xp.entry as int];
        let fp = p.funcs[p.entry as int];
        assert(fp.params.len() == 1);
        assert(erase_sig(fx, fp));
        bind_names_eq_b(fp.params, fx.params, seq![v], 1);
        assert(seq![v][0] == v);
        assert(val_type(seq![v][0], fp.params[0].1));
        let vs = seq![v];
        assert forall|k: int| 0 <= k < 1 implies val_type(#[trigger] vs[k], fp.params[k].1) by {
            assert(k == 0);
        }
        bind_ok(fp.params, vs, 1);
        assert(fp.body == rw(fx.body));
        assert(ty_expr(p, p.rank[p.entry as int], param_ctx(fp.params, fp.params.len()), fp.body) == Some(fp.ret));
        let n0 = back_expr(xp, p, rw, m, p.rank[p.entry as int], param_ctx(fp.params, fp.params.len()), bind(fx.params, vs, 1), fx.body, w);
        assert(xeval(xp, n0, bind(fx.params, vs, 1), fx.body) == Res::Done(w));
        assert(xeval_entry(xp, n0, v) == Res::Done(w));
    }
}
} // verus!
