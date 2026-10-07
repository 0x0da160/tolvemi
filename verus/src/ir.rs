//! 検証済み exec 部品が扱う中間表現（名前解決済み AST）と、その spec 層への写像。
//!
//! 型 `Ty` と組込み `Builtin` は spec 層の定義をそのまま exec でも使う。式は整数リテラルに
//! 多倍長整数を持つので exec 用の `EExpr` を別に定義し、`view` で spec の `Expr` に写す。

use crate::bigint::Int;
use crate::spec::*;
use vstd::prelude::*;

verus! {

pub enum EExpr {
    Int(Int),
    Bool(bool),
    Unit,
    Var(usize),
    List(Ty, Vec<EExpr>),
    Some(Box<EExpr>),
    None(Ty),
    Pair(Box<EExpr>, Box<EExpr>),
    Builtin(Builtin, Vec<EExpr>),
    Call(usize, Vec<EExpr>),
    Let(usize, Box<EExpr>, Box<EExpr>),
    If(Box<EExpr>, Box<EExpr>, Box<EExpr>),
    Fold(Box<EExpr>, Box<EExpr>, usize, usize, Box<EExpr>),
    Match(Box<EExpr>, Box<EExpr>, usize, Box<EExpr>),
}

pub open spec fn view_expr(e: EExpr) -> Expr
    decreases e,
{
    match e {
        EExpr::Int(n) => Expr::Int(n@),
        EExpr::Bool(b) => Expr::Bool(b),
        EExpr::Unit => Expr::Unit,
        EExpr::Var(x) => Expr::Var(x as nat),
        EExpr::List(t, es) => Expr::List(t, view_exprs(es)),
        EExpr::Some(x) => Expr::Some(Box::new(view_expr(*x))),
        EExpr::None(t) => Expr::None(t),
        EExpr::Pair(a, b) => Expr::Pair(Box::new(view_expr(*a)), Box::new(view_expr(*b))),
        EExpr::Builtin(b, es) => Expr::Builtin(b, view_exprs(es)),
        EExpr::Call(g, es) => Expr::Call(g as nat, view_exprs(es)),
        EExpr::Let(x, a, b) => Expr::Let(x as nat, Box::new(view_expr(*a)), Box::new(view_expr(*b))),
        EExpr::If(c, a, b) => Expr::If(
            Box::new(view_expr(*c)),
            Box::new(view_expr(*a)),
            Box::new(view_expr(*b)),
        ),
        EExpr::Fold(xs, init, acc, item, body) => Expr::Fold(
            Box::new(view_expr(*xs)),
            Box::new(view_expr(*init)),
            acc as nat,
            item as nat,
            Box::new(view_expr(*body)),
        ),
        EExpr::Match(m, n, x, sm) => Expr::Match(
            Box::new(view_expr(*m)),
            Box::new(view_expr(*n)),
            x as nat,
            Box::new(view_expr(*sm)),
        ),
    }
}

pub open spec fn view_exprs(es: Vec<EExpr>) -> Seq<Expr>
    decreases es,
{
    Seq::new(es@.len(), |i: int| if 0 <= i < es@.len() { view_expr(es@[i]) } else { Expr::Unit })
}

pub struct EFunc {
    pub params: Vec<(usize, Ty)>,
    pub ret: Ty,
    pub body: EExpr,
}

pub struct EProg {
    pub funcs: Vec<EFunc>,
    pub rank: Vec<usize>,
    pub entry: usize,
}

pub open spec fn view_params(ps: Seq<(usize, Ty)>) -> Seq<(nat, Ty)> {
    Seq::new(ps.len(), |i: int| (ps[i].0 as nat, ps[i].1))
}

pub open spec fn view_func(f: EFunc) -> Func {
    Func { params: view_params(f.params@), ret: f.ret, body: view_expr(f.body) }
}

pub open spec fn view_prog(p: EProg) -> Prog {
    Prog {
        funcs: Seq::new(p.funcs@.len(), |i: int| view_func(p.funcs@[i])),
        rank: Seq::new(p.rank@.len(), |i: int| p.rank@[i] as nat),
        entry: p.entry as nat,
    }
}

// ------------------------------------------------------------------ Ty の exec 操作

pub fn ty_clone(t: &Ty) -> (r: Ty)
    ensures
        r == *t,
    decreases t,
{
    match t {
        Ty::Int => Ty::Int,
        Ty::Bool => Ty::Bool,
        Ty::Unit => Ty::Unit,
        Ty::List(a) => Ty::List(Box::new(ty_clone(a))),
        Ty::Option(a) => Ty::Option(Box::new(ty_clone(a))),
        Ty::Pair(a, b) => Ty::Pair(Box::new(ty_clone(a)), Box::new(ty_clone(b))),
    }
}

pub fn ty_eq(s: &Ty, t: &Ty) -> (r: bool)
    ensures
        r == (*s == *t),
    decreases s,
{
    match (s, t) {
        (Ty::Int, Ty::Int) | (Ty::Bool, Ty::Bool) | (Ty::Unit, Ty::Unit) => true,
        (Ty::List(a), Ty::List(b)) | (Ty::Option(a), Ty::Option(b)) => ty_eq(a, b),
        (Ty::Pair(a, b), Ty::Pair(c, d)) => ty_eq(a, c) && ty_eq(b, d),
        _ => false,
    }
}

} // verus!
