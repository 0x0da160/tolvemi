//! spec 層（設計書 §11.1）：型、値、名前解決済み AST、型付け、呼出しランク、
//! 燃料付きの数学的評価 `eval_fuel`。
//!
//! 名前は exec 層の name phase で解決済みとし、変数・binder は `nat`、関数は
//! `Prog::funcs` の添字で表す。呼出しグラフが DAG であることは、各関数に付けた
//! ランク証明書 `Prog::rank` と「呼出し先のランクは真に小さい」という型付け条件で表す。

use vstd::prelude::*;

verus! {

// ------------------------------------------------------------------ 型と値（§3）

pub enum Ty {
    Int,
    Bool,
    Unit,
    List(Box<Ty>),
    Option(Box<Ty>),
    Pair(Box<Ty>, Box<Ty>),
}

/// 有限木としての値。リストは要素の有限列。
pub enum Val {
    Int(int),
    Bool(bool),
    Unit,
    None,
    Some(Box<Val>),
    Pair(Box<Val>, Box<Val>),
    List(Seq<Val>),
}

/// 値 v が型 t を持つ。
pub open spec fn val_type(v: Val, t: Ty) -> bool
    decreases v, 0nat,
{
    match v {
        Val::Int(_) => t == Ty::Int,
        Val::Bool(_) => t == Ty::Bool,
        Val::Unit => t == Ty::Unit,
        Val::None => t is Option,
        Val::Some(x) => t is Option && val_type(*x, *t->Option_0),
        Val::Pair(a, b) => t is Pair && val_type(*a, *t->Pair_0) && val_type(*b, *t->Pair_1),
        Val::List(s) => t is List && list_type(s, *t->List_0, 0),
    }
}

/// s[i..] の全要素が型 t を持つ（量化子の中で再帰しないよう列に沿って再帰する）。
pub open spec fn list_type(s: Seq<Val>, t: Ty, i: nat) -> bool
    decreases s, s.len() - i,
{
    if i >= s.len() {
        true
    } else {
        val_type(s[i as int], t) && list_type(s, t, i + 1)
    }
}

// ------------------------------------------------------------------ AST（§4.1）

#[derive(Clone, Copy, PartialEq, Eq)]
pub enum Builtin {
    Add,
    Sub,
    Mul,
    Neg,
    Lt,
    Le,
    Eq,
    Mod,
    Fst,
    Snd,
    Cons,
    Concat,
    Reverse,
    Length,
}

pub enum Expr {
    Int(int),
    Bool(bool),
    Unit,
    Var(nat),
    List(Ty, Seq<Expr>),
    Some(Box<Expr>),
    None(Ty),
    Pair(Box<Expr>, Box<Expr>),
    Builtin(Builtin, Seq<Expr>),
    /// ユーザー関数呼出し（関数は `Prog::funcs` の添字）
    Call(nat, Seq<Expr>),
    Let(nat, Box<Expr>, Box<Expr>),
    If(Box<Expr>, Box<Expr>, Box<Expr>),
    /// fold(list, init, |acc, item| body)
    Fold(Box<Expr>, Box<Expr>, nat, nat, Box<Expr>),
}

pub struct Func {
    pub params: Seq<(nat, Ty)>,
    pub ret: Ty,
    pub body: Expr,
}

pub struct Prog {
    pub funcs: Seq<Func>,
    /// DAG のランク証明書（§5.4）。呼出し先は真に小さいランクを持つ。
    pub rank: Seq<nat>,
    pub entry: nat,
}

// ------------------------------------------------------------------ 型付け（§6）

pub open spec fn builtin_type(b: Builtin, ts: Seq<Ty>) -> Option<Ty> {
    match b {
        Builtin::Add | Builtin::Sub | Builtin::Mul => {
            if ts.len() == 2 && ts[0] == Ty::Int && ts[1] == Ty::Int { Some(Ty::Int) } else { None }
        },
        Builtin::Neg => if ts.len() == 1 && ts[0] == Ty::Int { Some(Ty::Int) } else { None },
        Builtin::Lt | Builtin::Le => {
            if ts.len() == 2 && ts[0] == Ty::Int && ts[1] == Ty::Int { Some(Ty::Bool) } else { None }
        },
        Builtin::Eq => if ts.len() == 2 && ts[0] == ts[1] { Some(Ty::Bool) } else { None },
        Builtin::Mod => {
            if ts.len() == 2 && ts[0] == Ty::Int && ts[1] == Ty::Int {
                Some(Ty::Option(Box::new(Ty::Int)))
            } else {
                None
            }
        },
        Builtin::Fst => if ts.len() == 1 && ts[0] is Pair { Some(*ts[0]->Pair_0) } else { None },
        Builtin::Snd => if ts.len() == 1 && ts[0] is Pair { Some(*ts[0]->Pair_1) } else { None },
        Builtin::Cons => {
            if ts.len() == 2 && ts[1] == Ty::List(Box::new(ts[0])) { Some(ts[1]) } else { None }
        },
        Builtin::Concat => {
            if ts.len() == 2 && ts[0] is List && ts[1] == ts[0] { Some(ts[0]) } else { None }
        },
        Builtin::Reverse => if ts.len() == 1 && ts[0] is List { Some(ts[0]) } else { None },
        Builtin::Length => if ts.len() == 1 && ts[0] is List { Some(Ty::Int) } else { None },
    }
}

/// 引数リストから作る環境（後の同名引数が前を上書きする）。
pub open spec fn param_ctx(params: Seq<(nat, Ty)>, n: nat) -> Map<nat, Ty>
    decreases n,
{
    if n == 0 || n > params.len() {
        Map::empty()
    } else {
        param_ctx(params, (n - 1) as nat).insert(params[n - 1].0, params[n - 1].1)
    }
}

pub open spec fn bind(params: Seq<(nat, Ty)>, vs: Seq<Val>, n: nat) -> Map<nat, Val>
    decreases n,
{
    if n == 0 || n > params.len() || n > vs.len() {
        Map::empty()
    } else {
        bind(params, vs, (n - 1) as nat).insert(params[n - 1].0, vs[n - 1])
    }
}

/// ランク上限 r の関数本体内での式の型。注釈により型は一意に決まる（Option の None は型エラー）。
pub open spec fn ty_expr(p: Prog, r: nat, ctx: Map<nat, Ty>, e: Expr) -> Option<Ty>
    decreases e, 0nat,
{
    match e {
        Expr::Int(_) => Some(Ty::Int),
        Expr::Bool(_) => Some(Ty::Bool),
        Expr::Unit => Some(Ty::Unit),
        Expr::Var(x) => if ctx.contains_key(x) { Some(ctx[x]) } else { None },
        Expr::List(t, es) => match ty_args(p, r, ctx, es, 0) {
            Some(ts) => if forall|k: int| 0 <= k < ts.len() ==> #[trigger] ts[k] == t {
                Some(Ty::List(Box::new(t)))
            } else {
                None
            },
            None => None,
        },
        Expr::Some(x) => match ty_expr(p, r, ctx, *x) {
            Some(t) => Some(Ty::Option(Box::new(t))),
            None => None,
        },
        Expr::None(t) => Some(Ty::Option(Box::new(t))),
        Expr::Pair(a, b) => match (ty_expr(p, r, ctx, *a), ty_expr(p, r, ctx, *b)) {
            (Some(ta), Some(tb)) => Some(Ty::Pair(Box::new(ta), Box::new(tb))),
            _ => None,
        },
        Expr::Builtin(b, es) => match ty_args(p, r, ctx, es, 0) {
            Some(ts) => builtin_type(b, ts),
            None => None,
        },
        Expr::Call(g, es) => match ty_args(p, r, ctx, es, 0) {
            Some(ts) => if g < p.funcs.len() && g < p.rank.len() && p.rank[g as int] < r
                && ts.len() == p.funcs[g as int].params.len()
                && forall|k: int| 0 <= k < ts.len() ==> #[trigger] ts[k] == p.funcs[g as int].params[k].1 {
                Some(p.funcs[g as int].ret)
            } else {
                None
            },
            None => None,
        },
        Expr::Let(x, a, b) => match ty_expr(p, r, ctx, *a) {
            Some(ta) => ty_expr(p, r, ctx.insert(x, ta), *b),
            None => None,
        },
        Expr::If(c, a, b) => match (ty_expr(p, r, ctx, *c), ty_expr(p, r, ctx, *a), ty_expr(p, r, ctx, *b)) {
            (Some(tc), Some(ta), Some(tb)) => if tc == Ty::Bool && ta == tb { Some(ta) } else { None },
            _ => None,
        },
        Expr::Fold(xs, init, acc, item, body) => match (ty_expr(p, r, ctx, *xs), ty_expr(p, r, ctx, *init)) {
            (Some(tx), Some(ta)) => if tx is List
                && ty_expr(p, r, ctx.insert(acc, ta).insert(item, *tx->List_0), *body) == Some(ta) {
                Some(ta)
            } else {
                None
            },
            _ => None,
        },
    }
}

/// es[i..] の型列。
pub open spec fn ty_args(p: Prog, r: nat, ctx: Map<nat, Ty>, es: Seq<Expr>, i: nat) -> Option<Seq<Ty>>
    decreases es, es.len() - i,
{
    if i >= es.len() {
        Some(Seq::empty())
    } else {
        match (ty_expr(p, r, ctx, es[i as int]), ty_args(p, r, ctx, es, i + 1)) {
            (Some(t), Some(ts)) => Some(seq![t] + ts),
            _ => None,
        }
    }
}

/// 整形式プログラム：全関数が型付き、呼出しはランクを下げ、entry は一引数。
pub open spec fn wf(p: Prog) -> bool {
    &&& p.rank.len() == p.funcs.len()
    &&& p.entry < p.funcs.len()
    &&& p.funcs[p.entry as int].params.len() == 1
    &&& forall|g: int| 0 <= g < p.funcs.len() ==> #[trigger] ty_expr(
        p,
        p.rank[g],
        param_ctx(p.funcs[g].params, p.funcs[g].params.len()),
        p.funcs[g].body,
    ) == Some(p.funcs[g].ret)
}

// ------------------------------------------------------------------ 評価（§7、§8.2）

pub enum Res {
    Done(Val),
    Stuck,
    OutOfFuel,
}

pub enum ResSeq {
    Done(Seq<Val>),
    Stuck,
    OutOfFuel,
}

/// 組込みの意味（§7.4）。mod は正の除数に対する非負剰余。
pub open spec fn apply(b: Builtin, vs: Seq<Val>) -> Res {
    if vs.len() == 2 {
        match (b, vs[0], vs[1]) {
            (Builtin::Add, Val::Int(x), Val::Int(y)) => Res::Done(Val::Int(x + y)),
            (Builtin::Sub, Val::Int(x), Val::Int(y)) => Res::Done(Val::Int(x - y)),
            (Builtin::Mul, Val::Int(x), Val::Int(y)) => Res::Done(Val::Int(x * y)),
            (Builtin::Lt, Val::Int(x), Val::Int(y)) => Res::Done(Val::Bool(x < y)),
            (Builtin::Le, Val::Int(x), Val::Int(y)) => Res::Done(Val::Bool(x <= y)),
            (Builtin::Eq, x, y) => Res::Done(Val::Bool(x == y)),
            (Builtin::Mod, Val::Int(x), Val::Int(y)) => if y > 0 {
                Res::Done(Val::Some(Box::new(Val::Int(x % y))))
            } else {
                Res::Done(Val::None)
            },
            (Builtin::Cons, x, Val::List(s)) => Res::Done(Val::List(seq![x] + s)),
            (Builtin::Concat, Val::List(s), Val::List(u)) => Res::Done(Val::List(s + u)),
            _ => Res::Stuck,
        }
    } else if vs.len() == 1 {
        match (b, vs[0]) {
            (Builtin::Neg, Val::Int(x)) => Res::Done(Val::Int(-x)),
            (Builtin::Fst, Val::Pair(a, _)) => Res::Done(*a),
            (Builtin::Snd, Val::Pair(_, c)) => Res::Done(*c),
            (Builtin::Reverse, Val::List(s)) => Res::Done(Val::List(rev(s))),
            (Builtin::Length, Val::List(s)) => Res::Done(Val::Int(s.len() as int)),
            _ => Res::Stuck,
        }
    } else {
        Res::Stuck
    }
}

pub open spec fn rev(s: Seq<Val>) -> Seq<Val> {
    Seq::new(s.len(), |i: int| s[s.len() - 1 - i])
}

/// 燃料付き評価 eval_fuel。左から右の call-by-value。各再帰で燃料を一つ消費する。
pub open spec fn eval(p: Prog, fuel: nat, env: Map<nat, Val>, e: Expr) -> Res
    decreases fuel,
{
    if fuel == 0 {
        Res::OutOfFuel
    } else {
        let f = (fuel - 1) as nat;
        match e {
            Expr::Int(n) => Res::Done(Val::Int(n)),
            Expr::Bool(b) => Res::Done(Val::Bool(b)),
            Expr::Unit => Res::Done(Val::Unit),
            Expr::None(_) => Res::Done(Val::None),
            Expr::Var(x) => if env.contains_key(x) { Res::Done(env[x]) } else { Res::Stuck },
            Expr::List(_, es) => match eval_args(p, f, env, es, 0) {
                ResSeq::Done(vs) => Res::Done(Val::List(vs)),
                ResSeq::Stuck => Res::Stuck,
                ResSeq::OutOfFuel => Res::OutOfFuel,
            },
            Expr::Some(x) => match eval(p, f, env, *x) {
                Res::Done(v) => Res::Done(Val::Some(Box::new(v))),
                r => r,
            },
            Expr::Pair(a, b) => match eval(p, f, env, *a) {
                Res::Done(va) => match eval(p, f, env, *b) {
                    Res::Done(vb) => Res::Done(Val::Pair(Box::new(va), Box::new(vb))),
                    r => r,
                },
                r => r,
            },
            Expr::Builtin(b, es) => match eval_args(p, f, env, es, 0) {
                ResSeq::Done(vs) => apply(b, vs),
                ResSeq::Stuck => Res::Stuck,
                ResSeq::OutOfFuel => Res::OutOfFuel,
            },
            Expr::Call(g, es) => match eval_args(p, f, env, es, 0) {
                ResSeq::Done(vs) => if g < p.funcs.len() && vs.len() == p.funcs[g as int].params.len() {
                    eval(p, f, bind(p.funcs[g as int].params, vs, vs.len()), p.funcs[g as int].body)
                } else {
                    Res::Stuck
                },
                ResSeq::Stuck => Res::Stuck,
                ResSeq::OutOfFuel => Res::OutOfFuel,
            },
            Expr::Let(x, a, b) => match eval(p, f, env, *a) {
                Res::Done(v) => eval(p, f, env.insert(x, v), *b),
                r => r,
            },
            Expr::If(c, a, b) => match eval(p, f, env, *c) {
                Res::Done(Val::Bool(true)) => eval(p, f, env, *a),
                Res::Done(Val::Bool(false)) => eval(p, f, env, *b),
                Res::Done(_) => Res::Stuck,
                r => r,
            },
            Expr::Fold(xs, init, acc, item, body) => match eval(p, f, env, *xs) {
                Res::Done(Val::List(s)) => match eval(p, f, env, *init) {
                    Res::Done(v0) => eval_fold(p, f, env, acc, item, *body, s, 0, v0),
                    r => r,
                },
                Res::Done(_) => Res::Stuck,
                r => r,
            },
        }
    }
}

/// es[i..] を左から右へ評価する。
pub open spec fn eval_args(p: Prog, fuel: nat, env: Map<nat, Val>, es: Seq<Expr>, i: nat) -> ResSeq
    decreases fuel,
{
    if fuel == 0 {
        ResSeq::OutOfFuel
    } else if i >= es.len() {
        ResSeq::Done(Seq::empty())
    } else {
        let f = (fuel - 1) as nat;
        match eval(p, f, env, es[i as int]) {
            Res::Done(v) => match eval_args(p, f, env, es, i + 1) {
                ResSeq::Done(vs) => ResSeq::Done(seq![v] + vs),
                r => r,
            },
            Res::Stuck => ResSeq::Stuck,
            Res::OutOfFuel => ResSeq::OutOfFuel,
        }
    }
}

/// 左畳み込み：items[j..] を累積値 acc から順に処理する。
pub open spec fn eval_fold(
    p: Prog,
    fuel: nat,
    env: Map<nat, Val>,
    acc: nat,
    item: nat,
    body: Expr,
    items: Seq<Val>,
    j: nat,
    a: Val,
) -> Res
    decreases fuel,
{
    if fuel == 0 {
        Res::OutOfFuel
    } else if j >= items.len() {
        Res::Done(a)
    } else {
        let f = (fuel - 1) as nat;
        match eval(p, f, env.insert(acc, a).insert(item, items[j as int]), body) {
            Res::Done(v) => eval_fold(p, f, env, acc, item, body, items, j + 1, v),
            r => r,
        }
    }
}

/// entry 関数を入力値 v に適用する。
pub open spec fn eval_entry(p: Prog, fuel: nat, v: Val) -> Res {
    let f = p.funcs[p.entry as int];
    eval(p, fuel, bind(f.params, seq![v], 1), f.body)
}

} // verus!
