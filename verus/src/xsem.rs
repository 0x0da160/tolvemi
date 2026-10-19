//! 源の意味（段階 1b・SH1 の第一部）。
//!
//! 源の式 `XExpr` は核の式（`Expr`、spec.rs）に hof の形（map・filter・any・all・find）を加えたもの。
//! 評価器 `xeval` は核の `eval` と同じ燃料の数え方を使う。hof の形は要素を左から順に評価し、
//! any・all・find は結果が決まった要素で止まる（後の要素の述語は評価しない）。
//! 核だけの式は `embed` で写し、同じ燃料で同じ結果になることを示す（保存性）。
//! sort_by・loop・dict は、それぞれの決定（OD-3・OD-4・OD-6）の後に加える。

use crate::bigstep::*;
use crate::spec::*;
use vstd::prelude::*;

verus! {

/// 源の式：核の式に、hof の形を加えたもの。
pub enum XExpr {
    Int(int),
    Bool(bool),
    Unit,
    Char(int),
    Var(nat),
    List(Ty, Seq<XExpr>),
    Some(Box<XExpr>),
    None(Ty),
    Pair(Box<XExpr>, Box<XExpr>),
    Builtin(Builtin, Seq<XExpr>),
    Call(nat, Seq<XExpr>),
    Let(nat, Box<XExpr>, Box<XExpr>),
    If(Box<XExpr>, Box<XExpr>, Box<XExpr>),
    Fold(Box<XExpr>, Box<XExpr>, nat, nat, Box<XExpr>),
    Match(Box<XExpr>, Box<XExpr>, nat, Box<XExpr>),
    Inj(bool, Ty, Ty, Box<XExpr>),
    MatchR(Box<XExpr>, nat, Box<XExpr>, nat, Box<XExpr>),
    /// hof：map(xs, |x| body)。x は要素を束縛する名前。
    Map(Box<XExpr>, nat, Box<XExpr>),
    /// hof：filter(xs, |x| c)。
    Filter(Box<XExpr>, nat, Box<XExpr>),
    /// hof：any(xs, |x| c)。真になった要素で止まる。
    Any(Box<XExpr>, nat, Box<XExpr>),
    /// hof：all(xs, |x| c)。偽になった要素で止まる。
    All(Box<XExpr>, nat, Box<XExpr>),
    /// hof：find(xs, |x| c)。最初に真になった要素の Some、無ければ None。
    Find(Box<XExpr>, nat, Box<XExpr>),
}

pub struct XFunc {
    pub params: Seq<(nat, Ty)>,
    pub ret: Ty,
    pub body: XExpr,
}

pub struct XProg {
    pub funcs: Seq<XFunc>,
    pub entry: nat,
}

/// 源の評価器。核の eval と同じ燃料の数え方で、各再帰で燃料を一つ消費する。
pub open spec fn xeval(xp: XProg, fuel: nat, env: Map<nat, Val>, e: XExpr) -> Res
    decreases fuel,
{
    if fuel == 0 {
        Res::OutOfFuel
    } else {
        let f = (fuel - 1) as nat;
        match e {
            XExpr::Int(n) => Res::Done(Val::Int(n)),
            XExpr::Bool(b) => Res::Done(Val::Bool(b)),
            XExpr::Unit => Res::Done(Val::Unit),
            XExpr::Char(c) => Res::Done(Val::Char(c)),
            XExpr::Var(x) => if env.contains_key(x) { Res::Done(env[x]) } else { Res::Stuck },
            XExpr::List(_, es) => match xeval_args(xp, f, env, es, 0) {
                ResSeq::Done(vs) => Res::Done(Val::List(vs)),
                ResSeq::Stuck => Res::Stuck,
                ResSeq::OutOfFuel => Res::OutOfFuel,
            },
            XExpr::Some(x) => match xeval(xp, f, env, *x) {
                Res::Done(v) => Res::Done(Val::Some(Box::new(v))),
                r => r,
            },
            XExpr::None(_) => Res::Done(Val::None),
            XExpr::Pair(a, b) => match xeval(xp, f, env, *a) {
                Res::Done(va) => match xeval(xp, f, env, *b) {
                    Res::Done(vb) => Res::Done(Val::Pair(Box::new(va), Box::new(vb))),
                    r => r,
                },
                r => r,
            },
            XExpr::Builtin(b, es) => match xeval_args(xp, f, env, es, 0) {
                ResSeq::Done(vs) => apply(b, vs),
                ResSeq::Stuck => Res::Stuck,
                ResSeq::OutOfFuel => Res::OutOfFuel,
            },
            XExpr::Call(g, es) => match xeval_args(xp, f, env, es, 0) {
                ResSeq::Done(vs) => if g < xp.funcs.len() && vs.len() == xp.funcs[g as int].params.len() {
                    xeval(xp, f, bind(xp.funcs[g as int].params, vs, vs.len()), xp.funcs[g as int].body)
                } else {
                    Res::Stuck
                },
                ResSeq::Stuck => Res::Stuck,
                ResSeq::OutOfFuel => Res::OutOfFuel,
            },
            XExpr::Let(x, a, b) => match xeval(xp, f, env, *a) {
                Res::Done(v) => xeval(xp, f, env.insert(x, v), *b),
                r => r,
            },
            XExpr::If(c, a, b) => match xeval(xp, f, env, *c) {
                Res::Done(Val::Bool(true)) => xeval(xp, f, env, *a),
                Res::Done(Val::Bool(false)) => xeval(xp, f, env, *b),
                Res::Done(_) => Res::Stuck,
                r => r,
            },
            XExpr::Fold(xs, init, acc, item, body) => match xeval(xp, f, env, *xs) {
                Res::Done(Val::List(s)) => match xeval(xp, f, env, *init) {
                    Res::Done(v0) => xeval_fold(xp, f, env, acc, item, *body, s, 0, v0),
                    r => r,
                },
                Res::Done(_) => Res::Stuck,
                r => r,
            },
            XExpr::Match(m, nb, x, sm) => match xeval(xp, f, env, *m) {
                Res::Done(Val::None) => xeval(xp, f, env, *nb),
                Res::Done(Val::Some(v)) => xeval(xp, f, env.insert(x, *v), *sm),
                Res::Done(_) => Res::Stuck,
                r => r,
            },
            XExpr::Inj(ok, _, _, x) => match xeval(xp, f, env, *x) {
                Res::Done(v) => Res::Done(inj_val(ok, v)),
                r => r,
            },
            XExpr::MatchR(m, x, a, y, b) => match xeval(xp, f, env, *m) {
                Res::Done(Val::Ok(v)) => xeval(xp, f, env.insert(x, *v), *a),
                Res::Done(Val::Err(v)) => xeval(xp, f, env.insert(y, *v), *b),
                Res::Done(_) => Res::Stuck,
                r => r,
            },
            XExpr::Map(xs, x, c) => match xeval(xp, f, env, *xs) {
                Res::Done(Val::List(s)) => match xmap(xp, f, env, x, *c, s, 0) {
                    ResSeq::Done(vs) => Res::Done(Val::List(vs)),
                    ResSeq::Stuck => Res::Stuck,
                    ResSeq::OutOfFuel => Res::OutOfFuel,
                },
                Res::Done(_) => Res::Stuck,
                r => r,
            },
            XExpr::Filter(xs, x, c) => match xeval(xp, f, env, *xs) {
                Res::Done(Val::List(s)) => match xfilter(xp, f, env, x, *c, s, 0) {
                    ResSeq::Done(vs) => Res::Done(Val::List(vs)),
                    ResSeq::Stuck => Res::Stuck,
                    ResSeq::OutOfFuel => Res::OutOfFuel,
                },
                Res::Done(_) => Res::Stuck,
                r => r,
            },
            XExpr::Any(xs, x, c) => match xeval(xp, f, env, *xs) {
                Res::Done(Val::List(s)) => xany(xp, f, env, x, *c, s, 0),
                Res::Done(_) => Res::Stuck,
                r => r,
            },
            XExpr::All(xs, x, c) => match xeval(xp, f, env, *xs) {
                Res::Done(Val::List(s)) => xall(xp, f, env, x, *c, s, 0),
                Res::Done(_) => Res::Stuck,
                r => r,
            },
            XExpr::Find(xs, x, c) => match xeval(xp, f, env, *xs) {
                Res::Done(Val::List(s)) => xfind(xp, f, env, x, *c, s, 0),
                Res::Done(_) => Res::Stuck,
                r => r,
            },
        }
    }
}

/// es[i..] を左から右へ評価する（核の eval_args と同じ）。
pub open spec fn xeval_args(xp: XProg, fuel: nat, env: Map<nat, Val>, es: Seq<XExpr>, i: nat) -> ResSeq
    decreases fuel,
{
    if fuel == 0 {
        ResSeq::OutOfFuel
    } else if i >= es.len() {
        ResSeq::Done(Seq::empty())
    } else {
        let f = (fuel - 1) as nat;
        match xeval(xp, f, env, es[i as int]) {
            Res::Done(v) => match xeval_args(xp, f, env, es, i + 1) {
                ResSeq::Done(vs) => ResSeq::Done(seq![v] + vs),
                r => r,
            },
            Res::Stuck => ResSeq::Stuck,
            Res::OutOfFuel => ResSeq::OutOfFuel,
        }
    }
}

/// 左畳み込み（核の eval_fold と同じ）。
pub open spec fn xeval_fold(
    xp: XProg,
    fuel: nat,
    env: Map<nat, Val>,
    acc: nat,
    item: nat,
    body: XExpr,
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
        match xeval(xp, f, env.insert(acc, a).insert(item, items[j as int]), body) {
            Res::Done(v) => xeval_fold(xp, f, env, acc, item, body, items, j + 1, v),
            r => r,
        }
    }
}

/// map：要素ごとに本体を評価し、値を順に集める。
pub open spec fn xmap(xp: XProg, fuel: nat, env: Map<nat, Val>, x: nat, c: XExpr, items: Seq<Val>, j: nat) -> ResSeq
    decreases fuel,
{
    if fuel == 0 {
        ResSeq::OutOfFuel
    } else if j >= items.len() {
        ResSeq::Done(Seq::empty())
    } else {
        let f = (fuel - 1) as nat;
        match xeval(xp, f, env.insert(x, items[j as int]), c) {
            Res::Done(v) => match xmap(xp, f, env, x, c, items, j + 1) {
                ResSeq::Done(vs) => ResSeq::Done(seq![v] + vs),
                r => r,
            },
            Res::Stuck => ResSeq::Stuck,
            Res::OutOfFuel => ResSeq::OutOfFuel,
        }
    }
}

/// filter：述語が真の要素を、順に集める。述語の値が真偽でなければ止まる。
pub open spec fn xfilter(
    xp: XProg,
    fuel: nat,
    env: Map<nat, Val>,
    x: nat,
    c: XExpr,
    items: Seq<Val>,
    j: nat,
) -> ResSeq
    decreases fuel,
{
    if fuel == 0 {
        ResSeq::OutOfFuel
    } else if j >= items.len() {
        ResSeq::Done(Seq::empty())
    } else {
        let f = (fuel - 1) as nat;
        match xeval(xp, f, env.insert(x, items[j as int]), c) {
            Res::Done(Val::Bool(true)) => match xfilter(xp, f, env, x, c, items, j + 1) {
                ResSeq::Done(vs) => ResSeq::Done(seq![items[j as int]] + vs),
                r => r,
            },
            Res::Done(Val::Bool(false)) => xfilter(xp, f, env, x, c, items, j + 1),
            Res::Done(_) => ResSeq::Stuck,
            Res::Stuck => ResSeq::Stuck,
            Res::OutOfFuel => ResSeq::OutOfFuel,
        }
    }
}

/// any：真になった要素で止まる（後の要素の述語は評価しない）。
pub open spec fn xany(xp: XProg, fuel: nat, env: Map<nat, Val>, x: nat, c: XExpr, items: Seq<Val>, j: nat) -> Res
    decreases fuel,
{
    if fuel == 0 {
        Res::OutOfFuel
    } else if j >= items.len() {
        Res::Done(Val::Bool(false))
    } else {
        let f = (fuel - 1) as nat;
        match xeval(xp, f, env.insert(x, items[j as int]), c) {
            Res::Done(Val::Bool(true)) => Res::Done(Val::Bool(true)),
            Res::Done(Val::Bool(false)) => xany(xp, f, env, x, c, items, j + 1),
            Res::Done(_) => Res::Stuck,
            Res::Stuck => Res::Stuck,
            Res::OutOfFuel => Res::OutOfFuel,
        }
    }
}

/// all：偽になった要素で止まる（後の要素の述語は評価しない）。
pub open spec fn xall(xp: XProg, fuel: nat, env: Map<nat, Val>, x: nat, c: XExpr, items: Seq<Val>, j: nat) -> Res
    decreases fuel,
{
    if fuel == 0 {
        Res::OutOfFuel
    } else if j >= items.len() {
        Res::Done(Val::Bool(true))
    } else {
        let f = (fuel - 1) as nat;
        match xeval(xp, f, env.insert(x, items[j as int]), c) {
            Res::Done(Val::Bool(true)) => xall(xp, f, env, x, c, items, j + 1),
            Res::Done(Val::Bool(false)) => Res::Done(Val::Bool(false)),
            Res::Done(_) => Res::Stuck,
            Res::Stuck => Res::Stuck,
            Res::OutOfFuel => Res::OutOfFuel,
        }
    }
}

/// find：最初に真になった要素を Some で返す（真の要素が無ければ None）。
pub open spec fn xfind(xp: XProg, fuel: nat, env: Map<nat, Val>, x: nat, c: XExpr, items: Seq<Val>, j: nat) -> Res
    decreases fuel,
{
    if fuel == 0 {
        Res::OutOfFuel
    } else if j >= items.len() {
        Res::Done(Val::None)
    } else {
        let f = (fuel - 1) as nat;
        match xeval(xp, f, env.insert(x, items[j as int]), c) {
            Res::Done(Val::Bool(true)) => Res::Done(Val::Some(Box::new(items[j as int]))),
            Res::Done(Val::Bool(false)) => xfind(xp, f, env, x, c, items, j + 1),
            Res::Done(_) => Res::Stuck,
            Res::Stuck => Res::Stuck,
            Res::OutOfFuel => Res::OutOfFuel,
        }
    }
}

// ------------------------------------------------------------------ 核の式の写し

/// 核の式を源の式に写す（hof の形を含まない）。
pub open spec fn embed(e: Expr) -> XExpr
    decreases e, 0nat,
{
    match e {
        Expr::Int(n) => XExpr::Int(n),
        Expr::Bool(b) => XExpr::Bool(b),
        Expr::Unit => XExpr::Unit,
        Expr::Char(c) => XExpr::Char(c),
        Expr::Var(x) => XExpr::Var(x),
        Expr::List(t, es) => XExpr::List(t, embed_args(es, 0)),
        Expr::Some(a) => XExpr::Some(Box::new(embed(*a))),
        Expr::None(t) => XExpr::None(t),
        Expr::Pair(a, b) => XExpr::Pair(Box::new(embed(*a)), Box::new(embed(*b))),
        Expr::Builtin(b, es) => XExpr::Builtin(b, embed_args(es, 0)),
        Expr::Call(g, es) => XExpr::Call(g, embed_args(es, 0)),
        Expr::Let(x, a, b) => XExpr::Let(x, Box::new(embed(*a)), Box::new(embed(*b))),
        Expr::If(c, a, b) => XExpr::If(Box::new(embed(*c)), Box::new(embed(*a)), Box::new(embed(*b))),
        Expr::Fold(xs, init, acc, item, body) => XExpr::Fold(
            Box::new(embed(*xs)),
            Box::new(embed(*init)),
            acc,
            item,
            Box::new(embed(*body)),
        ),
        Expr::Match(m, nb, x, sm) => XExpr::Match(
            Box::new(embed(*m)),
            Box::new(embed(*nb)),
            x,
            Box::new(embed(*sm)),
        ),
        Expr::Inj(ok, t, u, a) => XExpr::Inj(ok, t, u, Box::new(embed(*a))),
        Expr::MatchR(m, x, a, y, b) => XExpr::MatchR(
            Box::new(embed(*m)),
            x,
            Box::new(embed(*a)),
            y,
            Box::new(embed(*b)),
        ),
    }
}

pub open spec fn embed_args(es: Seq<Expr>, i: nat) -> Seq<XExpr>
    decreases es, es.len() - i,
{
    if i >= es.len() {
        Seq::empty()
    } else {
        seq![embed(es[i as int])] + embed_args(es, i + 1)
    }
}

/// 核のプログラムを源のプログラムに写す（関数の本体を写し、宣言の順を保つ）。
pub open spec fn embed_prog(p: Prog) -> XProg {
    XProg {
        funcs: Seq::new(
            p.funcs.len(),
            |i: int| XFunc { params: p.funcs[i].params, ret: p.funcs[i].ret, body: embed(p.funcs[i].body) },
        ),
        entry: p.entry,
    }
}

proof fn embed_args_len(es: Seq<Expr>, i: nat)
    ensures
        embed_args(es, i).len() == (if i >= es.len() { 0 } else { (es.len() - i) as nat }),
    decreases es.len() - i,
{
    if i < es.len() {
        embed_args_len(es, i + 1);
    }
}

proof fn embed_args_at(es: Seq<Expr>, i: nat, k: nat)
    requires
        i <= k < es.len(),
    ensures
        embed_args(es, i)[(k - i) as int] == embed(es[k as int]),
    decreases k - i,
{
    embed_args_len(es, i + 1);
    if i < k {
        embed_args_at(es, i + 1, k);
    }
}

/// 核の式の評価と、その写しの評価は、同じ燃料で同じ結果になる（保存性）。
pub proof fn embed_eval(p: Prog, n: nat, env: Map<nat, Val>, e: Expr)
    ensures
        xeval(embed_prog(p), n, env, embed(e)) == eval(p, n, env, e),
    decreases n,
{
    if n > 0 {
        let f = (n - 1) as nat;
        match e {
            Expr::Int(_) => {},
            Expr::Bool(_) => {},
            Expr::Unit => {},
            Expr::Char(_) => {},
            Expr::Var(_) => {},
            Expr::None(_) => {},
            Expr::List(_, es) => embed_args_eval(p, f, env, es, 0),
            Expr::Some(a) => embed_eval(p, f, env, *a),
            Expr::Pair(a, b) => {
                embed_eval(p, f, env, *a);
                match eval(p, f, env, *a) {
                    Res::Done(_) => embed_eval(p, f, env, *b),
                    _ => {},
                }
            },
            Expr::Builtin(_, es) => embed_args_eval(p, f, env, es, 0),
            Expr::Call(g, es) => {
                embed_args_eval(p, f, env, es, 0);
                match eval_args(p, f, env, es, 0) {
                    ResSeq::Done(vs) => {
                        if g < p.funcs.len() && vs.len() == p.funcs[g as int].params.len() {
                            embed_eval(p, f, bind(p.funcs[g as int].params, vs, vs.len()), p.funcs[g as int].body);
                        }
                    },
                    _ => {},
                }
            },
            Expr::Let(x, a, b) => {
                embed_eval(p, f, env, *a);
                match eval(p, f, env, *a) {
                    Res::Done(v) => embed_eval(p, f, env.insert(x, v), *b),
                    _ => {},
                }
            },
            Expr::If(c, a, b) => {
                embed_eval(p, f, env, *c);
                match eval(p, f, env, *c) {
                    Res::Done(Val::Bool(true)) => embed_eval(p, f, env, *a),
                    Res::Done(Val::Bool(false)) => embed_eval(p, f, env, *b),
                    _ => {},
                }
            },
            Expr::Fold(xs, init, acc, item, body) => {
                embed_eval(p, f, env, *xs);
                match eval(p, f, env, *xs) {
                    Res::Done(Val::List(s)) => {
                        embed_eval(p, f, env, *init);
                        match eval(p, f, env, *init) {
                            Res::Done(v0) => embed_fold_eval(p, f, env, acc, item, *body, s, 0, v0),
                            _ => {},
                        }
                    },
                    _ => {},
                }
            },
            Expr::Match(m, nb, x, sm) => {
                embed_eval(p, f, env, *m);
                match eval(p, f, env, *m) {
                    Res::Done(Val::None) => embed_eval(p, f, env, *nb),
                    Res::Done(Val::Some(v)) => embed_eval(p, f, env.insert(x, *v), *sm),
                    _ => {},
                }
            },
            Expr::Inj(_, _, _, a) => embed_eval(p, f, env, *a),
            Expr::MatchR(m, x, a, y, b) => {
                embed_eval(p, f, env, *m);
                match eval(p, f, env, *m) {
                    Res::Done(Val::Ok(v)) => embed_eval(p, f, env.insert(x, *v), *a),
                    Res::Done(Val::Err(v)) => embed_eval(p, f, env.insert(y, *v), *b),
                    _ => {},
                }
            },
        }
    }
}

/// 引数列の評価の保存性（写しの添字は元の式の添字と同じ）。
proof fn embed_args_eval(p: Prog, n: nat, env: Map<nat, Val>, es: Seq<Expr>, i: nat)
    ensures
        xeval_args(embed_prog(p), n, env, embed_args(es, 0), i) == eval_args(p, n, env, es, i),
    decreases n,
{
    embed_args_len(es, 0);
    if n > 0 && i < es.len() {
        let f = (n - 1) as nat;
        embed_args_at(es, 0, i);
        embed_eval(p, f, env, es[i as int]);
        match eval(p, f, env, es[i as int]) {
            Res::Done(_) => embed_args_eval(p, f, env, es, i + 1),
            _ => {},
        }
    }
}

/// 畳み込みの保存性。
proof fn embed_fold_eval(
    p: Prog,
    n: nat,
    env: Map<nat, Val>,
    acc: nat,
    item: nat,
    body: Expr,
    items: Seq<Val>,
    j: nat,
    a: Val,
)
    ensures
        xeval_fold(embed_prog(p), n, env, acc, item, embed(body), items, j, a) == eval_fold(
            p,
            n,
            env,
            acc,
            item,
            body,
            items,
            j,
            a,
        ),
    decreases n,
{
    if n > 0 && j < items.len() {
        let f = (n - 1) as nat;
        let env2 = env.insert(acc, a).insert(item, items[j as int]);
        embed_eval(p, f, env2, body);
        match eval(p, f, env2, body) {
            Res::Done(v) => embed_fold_eval(p, f, env, acc, item, body, items, j + 1, v),
            _ => {},
        }
    }
}

} // verus!
