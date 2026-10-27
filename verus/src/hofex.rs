//! 書換えの exec 実装（段階 1b、DECISION-43）：hofrw.rs の写し rw_tb を、検証済みの exec の木の上で計算する。
//!
//! 源の exec の式 `EX` は `XExpr` の写しで、hof の形（map・filter・any・all・find・sort_by）を含む。
//! 書換え `rw_ex` は、表 `tb`（束縛名、要素の型、本体の型の三つ組の列。先頭から最初に一致する項を読む）を引いて、核の exec の式
//! `EExpr`（ir.rs）を作る。結果の写し（view_expr）は、spec の `rw_tb(view_tb(tb), view_ex(e))` に等しい。
//!
//! 導入する名前は hof_base（hofrw.rs）で、加算は検査つき。桁あふれは None を返す（書換えの拒否）。
//! 呼出し側（Rust の接着）は None を、資源の上限による拒否として扱う。
//!
//! 扱わないこと：Rust の AST（crates/tlvm の Expr）との変換、表（checker の HofTypes）の出どころ。

use crate::bigint::*;
use crate::fold_meaning::*;
use crate::fresh::*;
use crate::hofrw::*;
use crate::ir::*;
use crate::proof::*;
use crate::simulation::*;
use crate::sortmeaning::*;
use crate::spec::*;
use crate::xsem::*;
use vstd::prelude::*;

verus! {

// ------------------------------------------------------------------ 源の exec の式と写像

/// 源の exec の式（`XExpr` の写し）。
pub enum EX {
    Int(Int),
    Bool(bool),
    Unit,
    Char(u32),
    Var(usize),
    List(Ty, Vec<EX>),
    Some(Box<EX>),
    None(Ty),
    Pair(Box<EX>, Box<EX>),
    Builtin(Builtin, Vec<EX>),
    Call(usize, Vec<EX>),
    Let(usize, Box<EX>, Box<EX>),
    If(Box<EX>, Box<EX>, Box<EX>),
    Fold(Box<EX>, Box<EX>, usize, usize, Box<EX>),
    Match(Box<EX>, Box<EX>, usize, Box<EX>),
    Inj(bool, Ty, Ty, Box<EX>),
    MatchR(Box<EX>, usize, Box<EX>, usize, Box<EX>),
    Map(Box<EX>, usize, Box<EX>),
    Filter(Box<EX>, usize, Box<EX>),
    Any(Box<EX>, usize, Box<EX>),
    All(Box<EX>, usize, Box<EX>),
    Find(Box<EX>, usize, Box<EX>),
    SortBy(Box<EX>, usize, Box<EX>),
}

pub open spec fn view_ex(e: EX) -> XExpr
    decreases e,
{
    match e {
        EX::Int(n) => XExpr::Int(n@),
        EX::Bool(b) => XExpr::Bool(b),
        EX::Unit => XExpr::Unit,
        EX::Char(c) => XExpr::Char(c as int),
        EX::Var(x) => XExpr::Var(x as nat),
        EX::List(t, es) => XExpr::List(t, view_exs(es)),
        EX::Some(x) => XExpr::Some(Box::new(view_ex(*x))),
        EX::None(t) => XExpr::None(t),
        EX::Pair(a, b) => XExpr::Pair(Box::new(view_ex(*a)), Box::new(view_ex(*b))),
        EX::Builtin(b, es) => XExpr::Builtin(b, view_exs(es)),
        EX::Call(g, es) => XExpr::Call(g as nat, view_exs(es)),
        EX::Let(x, a, b) => XExpr::Let(x as nat, Box::new(view_ex(*a)), Box::new(view_ex(*b))),
        EX::If(c, a, b) => XExpr::If(Box::new(view_ex(*c)), Box::new(view_ex(*a)), Box::new(view_ex(*b))),
        EX::Fold(xs, init, acc, item, body) => XExpr::Fold(
            Box::new(view_ex(*xs)),
            Box::new(view_ex(*init)),
            acc as nat,
            item as nat,
            Box::new(view_ex(*body)),
        ),
        EX::Match(m, nb, x, sm) => XExpr::Match(
            Box::new(view_ex(*m)),
            Box::new(view_ex(*nb)),
            x as nat,
            Box::new(view_ex(*sm)),
        ),
        EX::Inj(ok, t, u, a) => XExpr::Inj(ok, t, u, Box::new(view_ex(*a))),
        EX::MatchR(m, x, a, y, b) => XExpr::MatchR(
            Box::new(view_ex(*m)),
            x as nat,
            Box::new(view_ex(*a)),
            y as nat,
            Box::new(view_ex(*b)),
        ),
        EX::Map(xs, x, c) => XExpr::Map(Box::new(view_ex(*xs)), x as nat, Box::new(view_ex(*c))),
        EX::Filter(xs, x, c) => XExpr::Filter(Box::new(view_ex(*xs)), x as nat, Box::new(view_ex(*c))),
        EX::Any(xs, x, c) => XExpr::Any(Box::new(view_ex(*xs)), x as nat, Box::new(view_ex(*c))),
        EX::All(xs, x, c) => XExpr::All(Box::new(view_ex(*xs)), x as nat, Box::new(view_ex(*c))),
        EX::Find(xs, x, c) => XExpr::Find(Box::new(view_ex(*xs)), x as nat, Box::new(view_ex(*c))),
        EX::SortBy(xs, x, k) => XExpr::SortBy(Box::new(view_ex(*xs)), x as nat, Box::new(view_ex(*k))),
    }
}

pub open spec fn view_exs(es: Vec<EX>) -> Seq<XExpr>
    decreases es,
{
    Seq::new(es@.len(), |i: int| if 0 <= i < es@.len() { view_ex(es@[i]) } else { XExpr::Unit })
}

/// 表の写し（束縛名を nat に、順序はそのまま）。
pub open spec fn view_tb(tb: Vec<(usize, Ty, Ty)>) -> Seq<(nat, Ty, Ty)> {
    Seq::new(tb@.len(), |i: int| (tb@[i].0 as nat, tb@[i].1, tb@[i].2))
}

// ------------------------------------------------------------------ 表の引き

/// hof の束縛名 x の（要素の型、本体の型）を表から読む（先頭から最初に一致する項。無ければ（Int、Int））。
/// hof_ann と hof_body の exec 版。
pub fn ent_e(tb: &Vec<(usize, Ty, Ty)>, x: usize) -> (r: (Ty, Ty))
    ensures
        r.0 == hof_ann(view_tb(*tb), x as nat),
        r.1 == hof_body(view_tb(*tb), x as nat),
{
    let mut i: usize = 0;
    while i < tb.len()
        invariant
            i <= tb.len(),
            forall|j: int| 0 <= j < i ==> tb@[j].0 != x,
            hof_ent_at(view_tb(*tb), i as nat, x as nat) == hof_ent_at(view_tb(*tb), 0, x as nat),
        decreases tb.len() - i,
    {
        if tb[i].0 == x {
            proof {
                assert(view_tb(*tb)[i as int] == (tb@[i as int].0 as nat, tb@[i as int].1, tb@[i as int].2));
            }
            return (ty_clone(&tb[i].1), ty_clone(&tb[i].2));
        }
        i = i + 1;
    }
    (Ty::Int, Ty::Int)
}

// ------------------------------------------------------------------ 名前の上限（top の検査つき版）

/// y + 1（あふれれば None）。
fn succ_e(y: usize) -> (r: Option<usize>)
    ensures
        match r {
            Some(v) => v as nat == y as nat + 1,
            None => y == usize::MAX,
        },
{
    if y < usize::MAX {
        Some(y + 1)
    } else {
        None
    }
}

/// 二つの上限の大きい方（どちらかが None なら None）。
pub fn max_o(a: Option<usize>, b: Option<usize>) -> (r: Option<usize>)
    ensures
        match r {
            Some(v) => match (a, b) {
                (Some(x), Some(y)) => v as nat == max(x as nat, y as nat),
                _ => false,
            },
            None => true,
        },
{
    match (a, b) {
        (Some(x), Some(y)) => {
            if x >= y {
                Some(x)
            } else {
                Some(y)
            }
        },
        _ => None,
    }
}

/// 列 es の i 番目以降の名前の上限（top_args の exec 版）。
fn top_es(es: &Vec<EExpr>, i: usize) -> (r: Option<usize>)
    ensures
        match r {
            Some(v) => v as nat == top_args(view_exprs(*es), i as nat),
            None => true,
        },
    decreases es, es.len() - i,
{
    if i >= es.len() {
        Some(0)
    } else {
        max_o(top_e(&es[i]), top_es(es, i + 1))
    }
}

/// 式の名前の上限（top の exec 版）。桁あふれは None。
pub fn top_e(e: &EExpr) -> (r: Option<usize>)
    ensures
        match r {
            Some(v) => v as nat == top(view_expr(*e)),
            None => true,
        },
    decreases e,
{
    match e {
        EExpr::Var(y) => succ_e(*y),
        EExpr::List(_, es) => top_es(es, 0),
        EExpr::Some(a) => top_e(a),
        EExpr::Pair(a, b) => max_o(top_e(a), top_e(b)),
        EExpr::Builtin(_, es) => top_es(es, 0),
        EExpr::Call(_, es) => top_es(es, 0),
        EExpr::Let(y, a, b) => max_o(succ_e(*y), max_o(top_e(a), top_e(b))),
        EExpr::If(c, a, b) => max_o(top_e(c), max_o(top_e(a), top_e(b))),
        EExpr::Fold(xs, init, acc, item, body) => max_o(
            max_o(succ_e(*acc), succ_e(*item)),
            max_o(top_e(xs), max_o(top_e(init), top_e(body))),
        ),
        EExpr::Match(s, nb, y, sm) => max_o(succ_e(*y), max_o(top_e(s), max_o(top_e(nb), top_e(sm)))),
        EExpr::Inj(_, _, _, a) => top_e(a),
        EExpr::MatchR(s, y, a, z, b) => max_o(
            max_o(succ_e(*y), succ_e(*z)),
            max_o(top_e(s), max_o(top_e(a), top_e(b))),
        ),
        _ => Some(0),
    }
}

// ------------------------------------------------------------------ 型の消去と加算

/// 型の消去（erase_ty の exec 版）。
pub fn erase_x(t: Ty) -> (r: Ty)
    ensures
        r == erase_ty(t),
    decreases t,
{
    match t {
        Ty::List(a) => Ty::List(Box::new(erase_x(*a))),
        Ty::Option(a) => Ty::Option(Box::new(erase_x(*a))),
        Ty::Pair(a, b) => Ty::Pair(Box::new(erase_x(*a)), Box::new(erase_x(*b))),
        Ty::Result(a, b) => Ty::Result(Box::new(erase_x(*a)), Box::new(erase_x(*b))),
        Ty::Dict(k, v) => Ty::List(Box::new(Ty::Pair(Box::new(erase_x(*k)), Box::new(erase_x(*v))))),
        _ => t,
    }
}

/// b + k（あふれれば None）。k は小さい定数。
fn add_e(b: usize, k: usize) -> (r: Option<usize>)
    ensures
        match r {
            Some(v) => v as nat == b as nat + k as nat,
            None => b as nat + k as nat > usize::MAX as nat,
        },
{
    if b <= usize::MAX - k {
        Some(b + k)
    } else {
        None
    }
}

// ------------------------------------------------------------------ 核の式の組立て（spec の形と一致）

pub fn var_x(n: usize) -> (r: EExpr)
    ensures
        view_expr(r) == Expr::Var(n as nat),
{
    EExpr::Var(n)
}

pub fn bool_x(b: bool) -> (r: EExpr)
    ensures
        view_expr(r) == Expr::Bool(b),
{
    EExpr::Bool(b)
}

pub fn none_x(t: Ty) -> (r: EExpr)
    ensures
        view_expr(r) == Expr::None(t),
{
    EExpr::None(t)
}

pub fn nil_x(t: Ty) -> (r: EExpr)
    ensures
        view_expr(r) == Expr::List(t, Seq::empty()),
{
    let es: Vec<EExpr> = Vec::new();
    proof {
        assert(view_exprs(es) =~= Seq::<Expr>::empty());
    }
    EExpr::List(t, es)
}

pub fn some_x(a: EExpr) -> (r: EExpr)
    ensures
        view_expr(r) == Expr::Some(Box::new(view_expr(a))),
{
    EExpr::Some(Box::new(a))
}

pub fn pair_x(a: EExpr, b: EExpr) -> (r: EExpr)
    ensures
        view_expr(r) == pair_e(view_expr(a), view_expr(b)),
{
    EExpr::Pair(Box::new(a), Box::new(b))
}

pub fn let_x(x: usize, a: EExpr, b: EExpr) -> (r: EExpr)
    ensures
        view_expr(r) == Expr::Let(x as nat, Box::new(view_expr(a)), Box::new(view_expr(b))),
{
    EExpr::Let(x, Box::new(a), Box::new(b))
}

pub fn if_x(c: EExpr, a: EExpr, b: EExpr) -> (r: EExpr)
    ensures
        view_expr(r) == Expr::If(Box::new(view_expr(c)), Box::new(view_expr(a)), Box::new(view_expr(b))),
{
    EExpr::If(Box::new(c), Box::new(a), Box::new(b))
}

pub fn match_x(s: EExpr, nb: EExpr, y: usize, sm: EExpr) -> (r: EExpr)
    ensures
        view_expr(r) == Expr::Match(
            Box::new(view_expr(s)),
            Box::new(view_expr(nb)),
            y as nat,
            Box::new(view_expr(sm)),
        ),
{
    EExpr::Match(Box::new(s), Box::new(nb), y, Box::new(sm))
}

pub fn fold_x(xs: EExpr, init: EExpr, acc: usize, item: usize, body: EExpr) -> (r: EExpr)
    ensures
        view_expr(r) == Expr::Fold(
            Box::new(view_expr(xs)),
            Box::new(view_expr(init)),
            acc as nat,
            item as nat,
            Box::new(view_expr(body)),
        ),
{
    EExpr::Fold(Box::new(xs), Box::new(init), acc, item, Box::new(body))
}

/// 組込みの一引数の呼出し。
pub fn bi1_x(b: Builtin, a: EExpr) -> (r: EExpr)
    ensures
        view_expr(r) == Expr::Builtin(b, seq![view_expr(a)]),
{
    let ghost av = view_expr(a);
    let mut args: Vec<EExpr> = Vec::new();
    args.push(a);
    proof {
        assert(view_exprs(args) =~= seq![av]);
    }
    EExpr::Builtin(b, args)
}

/// 組込みの二引数の呼出し。
pub fn bi2_x(b: Builtin, a: EExpr, c: EExpr) -> (r: EExpr)
    ensures
        view_expr(r) == Expr::Builtin(b, seq![view_expr(a), view_expr(c)]),
{
    let ghost av = view_expr(a);
    let ghost cv = view_expr(c);
    let mut args: Vec<EExpr> = Vec::new();
    args.push(a);
    args.push(c);
    proof {
        assert(view_exprs(args) =~= seq![av, cv]);
    }
    EExpr::Builtin(b, args)
}

// ------------------------------------------------------------------ 整列の本体（sortmeaning.rs の形）

pub fn fst_x(a: EExpr) -> (r: EExpr)
    ensures
        view_expr(r) == pfst(view_expr(a)),
{
    bi1_x(Builtin::Fst, a)
}

pub fn snd_x(a: EExpr) -> (r: EExpr)
    ensures
        view_expr(r) == psnd(view_expr(a)),
{
    bi1_x(Builtin::Snd, a)
}

pub fn cons_x(a: EExpr, c: EExpr) -> (r: EExpr)
    ensures
        view_expr(r) == cons_e(view_expr(a), view_expr(c)),
{
    bi2_x(Builtin::Cons, a, c)
}

pub fn reverse_x(a: EExpr) -> (r: EExpr)
    ensures
        view_expr(r) == Expr::Builtin(Builtin::Reverse, seq![view_expr(a)]),
{
    bi1_x(Builtin::Reverse, a)
}

pub fn lt_x(a: EExpr, c: EExpr) -> (r: EExpr)
    ensures
        view_expr(r) == Expr::Builtin(Builtin::Lt, seq![view_expr(a), view_expr(c)]),
{
    bi2_x(Builtin::Lt, a, c)
}

/// init_state(t) の exec 版。
pub fn init_state_x(t: Ty) -> (r: EExpr)
    ensures
        view_expr(r) == init_state(t),
{
    let l = nil_x(t);
    let p = pair_x(l, bool_x(false));
    pair_x(none_x(Ty::Int), p)
}

pub fn sort_cond_x(st: usize) -> (r: EExpr)
    ensures
        view_expr(r) == sort_cond(st as nat),
{
    snd_x(snd_x(var_x(st)))
}

pub fn sort_placed_x(st: usize, y: usize) -> (r: EExpr)
    ensures
        view_expr(r) == sort_placed(st as nat, y as nat),
{
    let a = fst_x(var_x(st));
    let b = cons_x(var_x(y), fst_x(snd_x(var_x(st))));
    pair_x(a, pair_x(b, bool_x(true)))
}

pub fn sort_before_x(e: usize, st: usize, y: usize) -> (r: EExpr)
    ensures
        view_expr(r) == sort_before(e as nat, st as nat, y as nat),
{
    let a = fst_x(var_x(st));
    let b = cons_x(var_x(y), cons_x(var_x(e), fst_x(snd_x(var_x(st)))));
    pair_x(a, pair_x(b, bool_x(true)))
}

pub fn sort_after_x(st: usize, y: usize) -> (r: EExpr)
    ensures
        view_expr(r) == sort_after(st as nat, y as nat),
{
    let a = fst_x(var_x(st));
    let b = cons_x(var_x(y), fst_x(snd_x(var_x(st))));
    pair_x(a, pair_x(b, bool_x(false)))
}

pub fn sort_lt_x(e: usize, st: usize, y: usize, ky: usize, ke: usize) -> (r: EExpr)
    ensures
        view_expr(r) == sort_lt(e as nat, st as nat, y as nat, ky as nat, ke as nat),
{
    let c = lt_x(var_x(ke), var_x(ky));
    let a = sort_before_x(e, st, y);
    let b = sort_after_x(st, y);
    if_x(c, a, b)
}

pub fn sort_match_x(e: usize, st: usize, y: usize, ky: usize, ke: usize) -> (r: EExpr)
    ensures
        view_expr(r) == sort_match(e as nat, st as nat, y as nat, ky as nat, ke as nat),
{
    let s = fst_x(var_x(st));
    let nb = pair_x(some_x(var_x(ky)), snd_x(var_x(st)));
    let sm = sort_lt_x(e, st, y, ky, ke);
    match_x(s, nb, ke, sm)
}

pub fn sort_fresh_x(e: usize, st: usize, y: usize, ky: usize, ke: usize, x: usize, k: EExpr) -> (r: EExpr)
    ensures
        view_expr(r) == sort_fresh(e as nat, st as nat, y as nat, ky as nat, ke as nat, x as nat, view_expr(k)),
{
    let inner = let_x(x, var_x(y), k);
    let m = sort_match_x(e, st, y, ky, ke);
    let_x(ky, inner, m)
}

pub fn sort_inner_x(e: usize, st: usize, y: usize, ky: usize, ke: usize, x: usize, k: EExpr) -> (r: EExpr)
    ensures
        view_expr(r) == sort_inner(e as nat, st as nat, y as nat, ky as nat, ke as nat, x as nat, view_expr(k)),
{
    let c = sort_cond_x(st);
    let a = sort_placed_x(st, y);
    let b = sort_fresh_x(e, st, y, ky, ke, x, k);
    if_x(c, a, b)
}

pub fn sort_rev_x(e: usize, rb: usize) -> (r: EExpr)
    ensures
        view_expr(r) == sort_rev(e as nat, rb as nat),
{
    let c = snd_x(snd_x(var_x(rb)));
    let a = fst_x(snd_x(var_x(rb)));
    let b = cons_x(var_x(e), fst_x(snd_x(var_x(rb))));
    if_x(c, a, b)
}

pub fn sort_body_x(t: Ty, acc: usize, e: usize, st: usize, y: usize, ky: usize, ke: usize, rb: usize, x: usize, k: EExpr) -> (r: EExpr)
    ensures
        view_expr(r) == sort_body(t, acc as nat, e as nat, st as nat, y as nat, ky as nat, ke as nat, rb as nat, x as nat, view_expr(k)),
{
    let cs = cons_x(var_x(e), var_x(acc));
    let init = init_state_x(t);
    let inner = sort_inner_x(e, st, y, ky, ke, x, k);
    let fold = fold_x(cs, init, st, y, inner);
    let rev = reverse_x(sort_rev_x(e, rb));
    let_x(rb, fold, rev)
}

// ------------------------------------------------------------------ hof の形の組立て（fold_meaning.rs の形）

pub fn cons_body_x(g: EExpr, acc: usize) -> (r: EExpr)
    ensures
        view_expr(r) == cons_body(view_expr(g), acc as nat),
{
    let v = var_x(acc);
    cons_x(g, v)
}

pub fn filter_body_x(c: EExpr, acc: usize, item: usize) -> (r: EExpr)
    ensures
        view_expr(r) == filter_body(view_expr(c), acc as nat, item as nat),
{
    let a = cons_x(var_x(item), var_x(acc));
    if_x(c, a, var_x(acc))
}

pub fn select_body_x(c: EExpr, t: Ty, acc: usize, item: usize, x: usize) -> (r: EExpr)
    ensures
        view_expr(r) == select_body(view_expr(c), t, acc as nat, item as nat, x as nat),
{
    let s = var_x(acc);
    let nb = if_x(c, some_x(var_x(item)), none_x(t));
    let sm = some_x(var_x(x));
    match_x(s, nb, x, sm)
}

pub fn map_x(xs: EExpr, t: Ty, acc: usize, x: usize, g: EExpr) -> (r: EExpr)
    ensures
        view_expr(r) == map_collect(view_expr(xs), t, acc as nat, x as nat, view_expr(g)),
{
    let cb = cons_body_x(g, acc);
    let f = fold_x(xs, nil_x(t), acc, x, cb);
    reverse_x(f)
}

pub fn filter_x(xs: EExpr, t: Ty, acc: usize, x: usize, c: EExpr) -> (r: EExpr)
    ensures
        view_expr(r) == filter_collect(view_expr(xs), t, acc as nat, x as nat, view_expr(c)),
{
    let fb = filter_body_x(c, acc, x);
    let f = fold_x(xs, nil_x(t), acc, x, fb);
    reverse_x(f)
}

pub fn any_x(xs: EExpr, acc: usize, x: usize, c: EExpr) -> (r: EExpr)
    ensures
        view_expr(r) == any_fold(view_expr(xs), acc as nat, x as nat, view_expr(c)),
{
    let v = var_x(acc);
    let body = if_x(v, bool_x(true), c);
    fold_x(xs, bool_x(false), acc, x, body)
}

pub fn all_x(xs: EExpr, acc: usize, x: usize, c: EExpr) -> (r: EExpr)
    ensures
        view_expr(r) == all_fold(view_expr(xs), acc as nat, x as nat, view_expr(c)),
{
    let v = var_x(acc);
    let body = if_x(v, c, bool_x(false));
    fold_x(xs, bool_x(true), acc, x, body)
}

pub fn find_x(xs: EExpr, t: Ty, acc: usize, x: usize, c: EExpr, y: usize) -> (r: EExpr)
    ensures
        view_expr(r) == find_fold(view_expr(xs), t, acc as nat, x as nat, view_expr(c), y as nat),
{
    let t2 = ty_clone(&t);
    let init = none_x(t);
    let body = select_body_x(c, t2, acc, x, y);
    fold_x(xs, init, acc, x, body)
}

pub fn sort_collect_x(xs: EExpr, t: Ty, acc: usize, e: usize, st: usize, y: usize, ky: usize, ke: usize, rb: usize, x: usize, k: EExpr) -> (r: EExpr)
    ensures
        view_expr(r) == sort_collect(
            view_expr(xs),
            t,
            acc as nat,
            e as nat,
            st as nat,
            y as nat,
            ky as nat,
            ke as nat,
            rb as nat,
            x as nat,
            view_expr(k),
        ),
{
    let t2 = ty_clone(&t);
    let init = nil_x(t);
    let body = sort_body_x(t2, acc, e, st, y, ky, ke, rb, x, k);
    fold_x(xs, init, acc, e, body)
}

// ------------------------------------------------------------------ 書換え（rw_tb の exec 版）

/// 列の写しの閉じた形：要素ごとに一致する並びは、rw_tb_args に等しい。
proof fn args_close(tb: Seq<(nat, Ty, Ty)>, es: Seq<XExpr>, outv: Seq<Expr>)
    requires
        outv.len() == es.len(),
        forall|j: int| 0 <= j < es.len() ==> outv[j] == rw_tb(tb, es[j]),
    ensures
        outv =~= rw_tb_args(tb, es, 0),
{
    tb_args_eq(tb, es, 0);
    assert(outv =~= Seq::new(es.len(), |k: int| rw_tb(tb, es[k])));
}

/// hof_base(x, g) の exec 版：max(x + 1, top(g))。
fn hof_base_x(x: usize, g: &EExpr) -> (r: Option<usize>)
    ensures
        match r {
            Some(v) => v as nat == hof_base(x as nat, view_expr(*g)),
            None => true,
        },
{
    let a = succ_e(x);
    let b = top_e(g);
    max_o(a, b)
}

/// 列の写し（rw_tb_args の exec 版）。
fn rw_args_e(tb: &Vec<(usize, Ty, Ty)>, es: &Vec<EX>) -> (r: Option<Vec<EExpr>>)
    ensures
        match r {
            Some(v) => view_exprs(v) =~= rw_tb_args(view_tb(*tb), view_exs(*es), 0),
            None => true,
        },
    decreases es,
{
    let mut out: Vec<EExpr> = Vec::new();
    let mut i: usize = 0;
    while i < es.len()
        invariant
            i <= es.len(),
            out@.len() == i,
            forall|j: int| 0 <= j < i ==> view_expr(#[trigger] out@[j]) == rw_tb(view_tb(*tb), view_ex(es@[j])),
        decreases es.len() - i,
    {
        let v = match rw_ex(tb, &es[i]) {
            Some(v) => v,
            None => return None,
        };
        out.push(v);
        i = i + 1;
    }
    proof {
        let outv = view_exprs(out);
        assert forall|j: int| 0 <= j < view_exs(*es).len() implies outv[j] == rw_tb(view_tb(*tb), view_exs(*es)[j]) by {
            assert(outv[j] == view_expr(out@[j]));
            assert(view_exs(*es)[j] == view_ex(es@[j]));
        }
        args_close(view_tb(*tb), view_exs(*es), outv);
    }
    Some(out)
}

/// 源の exec の式の写し（rw_tb の exec 版）。桁あふれのときだけ None。
pub fn rw_ex(tb: &Vec<(usize, Ty, Ty)>, e: &EX) -> (r: Option<EExpr>)
    ensures
        match r {
            Some(v) => view_expr(v) == rw_tb(view_tb(*tb), view_ex(*e)),
            None => true,
        },
    decreases e,
{
    proof {
        reveal_with_fuel(rw_tb, 1);
        reveal_with_fuel(view_ex, 1);
    }
    match e {
        EX::Int(n) => Some(EExpr::Int(n.copy())),
        EX::Bool(b) => Some(bool_x(*b)),
        EX::Unit => Some(EExpr::Unit),
        EX::Char(c) => Some(EExpr::Char(*c)),
        EX::Var(x) => Some(var_x(*x)),
        EX::List(t, es) => {
            let v = match rw_args_e(tb, es) {
                Some(v) => v,
                None => return None,
            };
            Some(EExpr::List(erase_x(ty_clone(t)), v))
        },
        EX::Some(a) => {
            let va = match rw_ex(tb, a) {
                Some(v) => v,
                None => return None,
            };
            Some(some_x(va))
        },
        EX::None(t) => Some(none_x(erase_x(ty_clone(t)))),
        EX::Pair(a, b) => {
            let va = match rw_ex(tb, a) {
                Some(v) => v,
                None => return None,
            };
            let vb = match rw_ex(tb, b) {
                Some(v) => v,
                None => return None,
            };
            Some(pair_x(va, vb))
        },
        EX::Builtin(b, es) => {
            let v = match rw_args_e(tb, es) {
                Some(v) => v,
                None => return None,
            };
            Some(EExpr::Builtin(*b, v))
        },
        EX::Call(g, es) => {
            let v = match rw_args_e(tb, es) {
                Some(v) => v,
                None => return None,
            };
            Some(EExpr::Call(*g, v))
        },
        EX::Let(x, a, b) => {
            let va = match rw_ex(tb, a) {
                Some(v) => v,
                None => return None,
            };
            let vb = match rw_ex(tb, b) {
                Some(v) => v,
                None => return None,
            };
            Some(let_x(*x, va, vb))
        },
        EX::If(c, a, b) => {
            let vc = match rw_ex(tb, c) {
                Some(v) => v,
                None => return None,
            };
            let va = match rw_ex(tb, a) {
                Some(v) => v,
                None => return None,
            };
            let vb = match rw_ex(tb, b) {
                Some(v) => v,
                None => return None,
            };
            Some(if_x(vc, va, vb))
        },
        EX::Fold(xs, init, acc, item, body) => {
            let vxs = match rw_ex(tb, xs) {
                Some(v) => v,
                None => return None,
            };
            let vinit = match rw_ex(tb, init) {
                Some(v) => v,
                None => return None,
            };
            let vbody = match rw_ex(tb, body) {
                Some(v) => v,
                None => return None,
            };
            Some(fold_x(vxs, vinit, *acc, *item, vbody))
        },
        EX::Match(m, nb, x, sm) => {
            let vm = match rw_ex(tb, m) {
                Some(v) => v,
                None => return None,
            };
            let vnb = match rw_ex(tb, nb) {
                Some(v) => v,
                None => return None,
            };
            let vsm = match rw_ex(tb, sm) {
                Some(v) => v,
                None => return None,
            };
            Some(match_x(vm, vnb, *x, vsm))
        },
        EX::Inj(ok, t, u, a) => {
            let va = match rw_ex(tb, a) {
                Some(v) => v,
                None => return None,
            };
            Some(EExpr::Inj(*ok, erase_x(ty_clone(t)), erase_x(ty_clone(u)), Box::new(va)))
        },
        EX::MatchR(m, x, a, y, b) => {
            let vm = match rw_ex(tb, m) {
                Some(v) => v,
                None => return None,
            };
            let va = match rw_ex(tb, a) {
                Some(v) => v,
                None => return None,
            };
            let vb = match rw_ex(tb, b) {
                Some(v) => v,
                None => return None,
            };
            Some(EExpr::MatchR(Box::new(vm), *x, Box::new(va), *y, Box::new(vb)))
        },
        EX::Map(xs, x, c) => {
            let vxs = match rw_ex(tb, xs) {
                Some(v) => v,
                None => return None,
            };
            let g = match rw_ex(tb, c) {
                Some(v) => v,
                None => return None,
            };
            let b = match hof_base_x(*x, &g) {
                Some(v) => v,
                None => return None,
            };
            let t = erase_x(ent_e(tb, *x).1);
            Some(map_x(vxs, t, b, *x, g))
        },
        EX::Filter(xs, x, c) => {
            let vxs = match rw_ex(tb, xs) {
                Some(v) => v,
                None => return None,
            };
            let g = match rw_ex(tb, c) {
                Some(v) => v,
                None => return None,
            };
            let b = match hof_base_x(*x, &g) {
                Some(v) => v,
                None => return None,
            };
            let t = erase_x(ent_e(tb, *x).0);
            Some(filter_x(vxs, t, b, *x, g))
        },
        EX::Any(xs, x, c) => {
            let vxs = match rw_ex(tb, xs) {
                Some(v) => v,
                None => return None,
            };
            let g = match rw_ex(tb, c) {
                Some(v) => v,
                None => return None,
            };
            let b = match hof_base_x(*x, &g) {
                Some(v) => v,
                None => return None,
            };
            Some(any_x(vxs, b, *x, g))
        },
        EX::All(xs, x, c) => {
            let vxs = match rw_ex(tb, xs) {
                Some(v) => v,
                None => return None,
            };
            let g = match rw_ex(tb, c) {
                Some(v) => v,
                None => return None,
            };
            let b = match hof_base_x(*x, &g) {
                Some(v) => v,
                None => return None,
            };
            Some(all_x(vxs, b, *x, g))
        },
        EX::Find(xs, x, c) => {
            let vxs = match rw_ex(tb, xs) {
                Some(v) => v,
                None => return None,
            };
            let g = match rw_ex(tb, c) {
                Some(v) => v,
                None => return None,
            };
            let b = match hof_base_x(*x, &g) {
                Some(v) => v,
                None => return None,
            };
            let b1 = match add_e(b, 1) {
                Some(v) => v,
                None => return None,
            };
            let t = erase_x(ent_e(tb, *x).0);
            Some(find_x(vxs, t, b, *x, g, b1))
        },
        EX::SortBy(xs, x, c) => {
            let vxs = match rw_ex(tb, xs) {
                Some(v) => v,
                None => return None,
            };
            let g = match rw_ex(tb, c) {
                Some(v) => v,
                None => return None,
            };
            let b = match hof_base_x(*x, &g) {
                Some(v) => v,
                None => return None,
            };
            let b1 = match add_e(b, 1) {
                Some(v) => v,
                None => return None,
            };
            let b2 = match add_e(b, 2) {
                Some(v) => v,
                None => return None,
            };
            let b3 = match add_e(b, 3) {
                Some(v) => v,
                None => return None,
            };
            let b4 = match add_e(b, 4) {
                Some(v) => v,
                None => return None,
            };
            let b5 = match add_e(b, 5) {
                Some(v) => v,
                None => return None,
            };
            let b6 = match add_e(b, 6) {
                Some(v) => v,
                None => return None,
            };
            let t = erase_x(ent_e(tb, *x).0);
            Some(sort_collect_x(vxs, t, b, b1, b2, b3, b4, b5, b6, *x, g))
        },
    }
}

} // verus!
