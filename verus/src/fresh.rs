//! 新しい名前の確保（段階 0・SH5）。
//!
//! rewrite は、式の名前（参照にも束縛にも現れるもの）のどれとも違う名前を新しく割り当てる。
//! 割り当ては `top(e)`（e の名前の最大 + 1）から順に行う。`below(n, e)` は e の名前がすべて n より小さいことを表し、
//! n 以上の名前は e に現れない（`below_absent`）。だから割り当てた名前は、束縛の新しさ（absent）を満たす。

use crate::proof::*;
use crate::records_proof::*;
use crate::spec::*;
use vstd::prelude::*;

verus! {

/// 式の名前（参照にも束縛にも）がすべて n より小さい。
pub open spec fn below(n: nat, e: Expr) -> bool
    decreases e, 0nat,
{
    match e {
        Expr::Var(y) => y < n,
        Expr::List(_, es) => below_args(n, es, 0),
        Expr::Some(a) => below(n, *a),
        Expr::Pair(a, b) => below(n, *a) && below(n, *b),
        Expr::Builtin(_, es) => below_args(n, es, 0),
        Expr::Call(_, es) => below_args(n, es, 0),
        Expr::Let(y, a, b) => y < n && below(n, *a) && below(n, *b),
        Expr::If(c, a, b) => below(n, *c) && below(n, *a) && below(n, *b),
        Expr::Fold(xs, init, acc, item, body) => acc < n && item < n && below(n, *xs) && below(n, *init)
            && below(n, *body),
        Expr::Match(m, nb, y, sm) => y < n && below(n, *m) && below(n, *nb) && below(n, *sm),
        Expr::Inj(_, _, _, a) => below(n, *a),
        Expr::MatchR(m, y, a, z, b) => y < n && z < n && below(n, *m) && below(n, *a) && below(n, *b),
        _ => true,
    }
}

pub open spec fn below_args(n: nat, es: Seq<Expr>, i: nat) -> bool
    decreases es, es.len() - i,
{
    if i >= es.len() {
        true
    } else {
        below(n, es[i as int]) && below_args(n, es, i + 1)
    }
}

/// 名前の上限を広げても、式の名前はすべて上限より小さい。
pub proof fn below_mono(n: nat, m: nat, e: Expr)
    requires
        below(n, e),
        n <= m,
    ensures
        below(m, e),
    decreases e, 0nat,
{
    match e {
        Expr::Var(_) => {},
        Expr::List(_, es) => below_mono_args(n, m, es, 0),
        Expr::Some(a) => below_mono(n, m, *a),
        Expr::Pair(a, b) => {
            below_mono(n, m, *a);
            below_mono(n, m, *b);
        },
        Expr::Builtin(_, es) => below_mono_args(n, m, es, 0),
        Expr::Call(_, es) => below_mono_args(n, m, es, 0),
        Expr::Let(_, a, b) => {
            below_mono(n, m, *a);
            below_mono(n, m, *b);
        },
        Expr::If(c, a, b) => {
            below_mono(n, m, *c);
            below_mono(n, m, *a);
            below_mono(n, m, *b);
        },
        Expr::Fold(xs, init, _, _, body) => {
            below_mono(n, m, *xs);
            below_mono(n, m, *init);
            below_mono(n, m, *body);
        },
        Expr::Match(s, nb, _, sm) => {
            below_mono(n, m, *s);
            below_mono(n, m, *nb);
            below_mono(n, m, *sm);
        },
        Expr::Inj(_, _, _, a) => below_mono(n, m, *a),
        Expr::MatchR(s, _, a, _, b) => {
            below_mono(n, m, *s);
            below_mono(n, m, *a);
            below_mono(n, m, *b);
        },
        _ => {},
    }
}

pub proof fn below_mono_args(n: nat, m: nat, es: Seq<Expr>, i: nat)
    requires
        below_args(n, es, i),
        n <= m,
    ensures
        below_args(m, es, i),
    decreases es, es.len() - i,
{
    if i < es.len() {
        below_mono(n, m, es[i as int]);
        below_mono_args(n, m, es, i + 1);
    }
}

/// n 以上の名前 x は、n より小さい名前だけの式には現れない。
pub proof fn below_absent(n: nat, x: nat, e: Expr)
    requires
        below(n, e),
        n <= x,
    ensures
        absent(x, e),
    decreases e, 0nat,
{
    match e {
        Expr::Var(_) => {},
        Expr::List(_, es) => below_absent_args(n, x, es, 0),
        Expr::Some(a) => below_absent(n, x, *a),
        Expr::Pair(a, b) => {
            below_absent(n, x, *a);
            below_absent(n, x, *b);
        },
        Expr::Builtin(_, es) => below_absent_args(n, x, es, 0),
        Expr::Call(_, es) => below_absent_args(n, x, es, 0),
        Expr::Let(_, a, b) => {
            below_absent(n, x, *a);
            below_absent(n, x, *b);
        },
        Expr::If(c, a, b) => {
            below_absent(n, x, *c);
            below_absent(n, x, *a);
            below_absent(n, x, *b);
        },
        Expr::Fold(xs, init, _, _, body) => {
            below_absent(n, x, *xs);
            below_absent(n, x, *init);
            below_absent(n, x, *body);
        },
        Expr::Match(s, nb, _, sm) => {
            below_absent(n, x, *s);
            below_absent(n, x, *nb);
            below_absent(n, x, *sm);
        },
        Expr::Inj(_, _, _, a) => below_absent(n, x, *a),
        Expr::MatchR(s, _, a, _, b) => {
            below_absent(n, x, *s);
            below_absent(n, x, *a);
            below_absent(n, x, *b);
        },
        _ => {},
    }
}

pub proof fn below_absent_args(n: nat, x: nat, es: Seq<Expr>, i: nat)
    requires
        below_args(n, es, i),
        n <= x,
    ensures
        absent_args(x, es, i),
    decreases es, es.len() - i,
{
    if i < es.len() {
        below_absent(n, x, es[i as int]);
        below_absent_args(n, x, es, i + 1);
    }
}

/// 式の名前の最大 + 1（名前が無ければ 0）。rewrite はこれ以上の名前から割り当てる。
pub open spec fn top(e: Expr) -> nat
    decreases e, 0nat,
{
    match e {
        Expr::Var(y) => y + 1,
        Expr::List(_, es) => top_args(es, 0),
        Expr::Some(a) => top(*a),
        Expr::Pair(a, b) => max(top(*a), top(*b)),
        Expr::Builtin(_, es) => top_args(es, 0),
        Expr::Call(_, es) => top_args(es, 0),
        Expr::Let(y, a, b) => max(y + 1, max(top(*a), top(*b))),
        Expr::If(c, a, b) => max(top(*c), max(top(*a), top(*b))),
        Expr::Fold(xs, init, acc, item, body) => max(
            max(acc + 1, item + 1),
            max(top(*xs), max(top(*init), top(*body))),
        ),
        Expr::Match(s, nb, y, sm) => max(y + 1, max(top(*s), max(top(*nb), top(*sm)))),
        Expr::Inj(_, _, _, a) => top(*a),
        Expr::MatchR(s, y, a, z, b) => max(max(y + 1, z + 1), max(top(*s), max(top(*a), top(*b)))),
        _ => 0,
    }
}

pub open spec fn top_args(es: Seq<Expr>, i: nat) -> nat
    decreases es, es.len() - i,
{
    if i >= es.len() {
        0
    } else {
        max(top(es[i as int]), top_args(es, i + 1))
    }
}

/// top(e) は e の名前の上限になる。
pub proof fn top_below(e: Expr)
    ensures
        below(top(e), e),
    decreases e, 0nat,
{
    match e {
        Expr::Var(_) => {},
        Expr::List(_, es) => top_below_args(es, 0),
        Expr::Some(a) => {
            top_below(*a);
            below_mono(top(*a), top(e), *a);
        },
        Expr::Pair(a, b) => {
            top_below(*a);
            below_mono(top(*a), top(e), *a);
            top_below(*b);
            below_mono(top(*b), top(e), *b);
        },
        Expr::Builtin(_, es) => top_below_args(es, 0),
        Expr::Call(_, es) => top_below_args(es, 0),
        Expr::Let(_, a, b) => {
            top_below(*a);
            below_mono(top(*a), top(e), *a);
            top_below(*b);
            below_mono(top(*b), top(e), *b);
        },
        Expr::If(c, a, b) => {
            top_below(*c);
            below_mono(top(*c), top(e), *c);
            top_below(*a);
            below_mono(top(*a), top(e), *a);
            top_below(*b);
            below_mono(top(*b), top(e), *b);
        },
        Expr::Fold(xs, init, _, _, body) => {
            top_below(*xs);
            below_mono(top(*xs), top(e), *xs);
            top_below(*init);
            below_mono(top(*init), top(e), *init);
            top_below(*body);
            below_mono(top(*body), top(e), *body);
        },
        Expr::Match(s, nb, _, sm) => {
            top_below(*s);
            below_mono(top(*s), top(e), *s);
            top_below(*nb);
            below_mono(top(*nb), top(e), *nb);
            top_below(*sm);
            below_mono(top(*sm), top(e), *sm);
        },
        Expr::Inj(_, _, _, a) => {
            top_below(*a);
            below_mono(top(*a), top(e), *a);
        },
        Expr::MatchR(s, _, a, _, b) => {
            top_below(*s);
            below_mono(top(*s), top(e), *s);
            top_below(*a);
            below_mono(top(*a), top(e), *a);
            top_below(*b);
            below_mono(top(*b), top(e), *b);
        },
        _ => {},
    }
}

pub proof fn top_below_args(es: Seq<Expr>, i: nat)
    ensures
        below_args(top_args(es, i), es, i),
    decreases es, es.len() - i,
{
    if i < es.len() {
        top_below(es[i as int]);
        below_mono(top(es[i as int]), top_args(es, i), es[i as int]);
        top_below_args(es, i + 1);
        below_mono_args(top_args(es, i + 1), top_args(es, i), es, i + 1);
    }
}

/// rewrite の割り当て：e の名前の上限 top(e) から i 番目の名前は、e のどこにも現れない。
/// 同じ e から割り当てた名前どうしは、番号が違えば違う。
pub proof fn fresh_name_ok(e: Expr, i: nat, j: nat)
    ensures
        absent(top(e) + i, e),
        i != j ==> top(e) + i != top(e) + j,
{
    top_below(e);
    below_absent(top(e), top(e) + i, e);
}

} // verus!
