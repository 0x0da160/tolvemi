//! 名前解決（設計書 §5.1、§5.2、§11.2 の 3）。
//!
//! spec の `resolve` は表面 AST（名前付き）から名前解決済み AST（spec::Prog の関数列と entry）を作る。
//! - トップレベル関数名は相異なる（`distinct(fs)`）。全関数は全体で可視で、前方参照できる。
//! - 引数名は関数ごとに相異なる。
//! - `let x = a in b` の x は b でだけ見え、外側の可視変数をシャドーできない。
//! - fold の二 binder は相異なり、本体でだけ見え、外側をシャドーできない。
//! - 変数は可視変数の列（scope）での位置に、呼出しは関数の位置に置き換える。
//! - entry 宣言はちょうど一つで、既知の関数を指し、その関数の引数は一つ。
//! exec の `resolve_e` が spec の `resolve` と同じ結果を返すことを証明する。

use crate::ir::*;
use crate::spec::*;
use crate::surface::*;
use crate::syntax::*;
use vstd::prelude::*;

verus! {

// ------------------------------------------------------------------ spec

pub open spec fn idx(s: Seq<Seq<char>>, x: Seq<char>, i: nat) -> Option<nat>
    decreases s.len() - i,
{
    if i >= s.len() {
        None
    } else if s[i as int] == x {
        Some(i)
    } else {
        idx(s, x, i + 1)
    }
}

pub open spec fn distinct(s: Seq<Seq<char>>) -> bool {
    forall|i: int, j: int| 0 <= i < j < s.len() ==> s[i] != s[j]
}

/// 式の名前解決。fs は関数名の列、sc は可視変数の列（外側から順）。
pub open spec fn rx(fs: Seq<Seq<char>>, sc: Seq<Seq<char>>, e: Sx) -> Option<Expr>
    decreases e, 0nat,
{
    match e {
        Sx::Int(n) => Some(Expr::Int(n)),
        Sx::Bool(b) => Some(Expr::Bool(b)),
        Sx::Unit => Some(Expr::Unit),
        Sx::Var(x) => match idx(sc, x, 0) {
            Some(k) => Some(Expr::Var(k)),
            None => None,
        },
        Sx::List(t, es) => match rxs(fs, sc, es, 0) {
            Some(xs) => Some(Expr::List(t, xs)),
            None => None,
        },
        Sx::Some(a) => match rx(fs, sc, *a) {
            Some(x) => Some(Expr::Some(Box::new(x))),
            None => None,
        },
        Sx::None(t) => Some(Expr::None(t)),
        Sx::Pair(a, b) => match (rx(fs, sc, *a), rx(fs, sc, *b)) {
            (Some(x), Some(y)) => Some(Expr::Pair(Box::new(x), Box::new(y))),
            _ => None,
        },
        Sx::Builtin(b, es) => match rxs(fs, sc, es, 0) {
            Some(xs) => Some(Expr::Builtin(b, xs)),
            None => None,
        },
        Sx::Call(f, es) => match (idx(fs, f, 0), rxs(fs, sc, es, 0)) {
            (Some(g), Some(xs)) => Some(Expr::Call(g, xs)),
            _ => None,
        },
        Sx::Let(x, a, b) => if idx(sc, x, 0) is Some {
            None
        } else {
            match (rx(fs, sc, *a), rx(fs, sc.push(x), *b)) {
                (Some(ra), Some(rb)) => Some(Expr::Let(sc.len(), Box::new(ra), Box::new(rb))),
                _ => None,
            }
        },
        Sx::If(c, a, b) => match (rx(fs, sc, *c), rx(fs, sc, *a), rx(fs, sc, *b)) {
            (Some(x), Some(y), Some(z)) => Some(Expr::If(Box::new(x), Box::new(y), Box::new(z))),
            _ => None,
        },
        Sx::Fold(l, i, a, x, b) => if a == x || idx(sc, a, 0) is Some || idx(sc, x, 0) is Some {
            None
        } else {
            match (rx(fs, sc, *l), rx(fs, sc, *i), rx(fs, sc.push(a).push(x), *b)) {
                (Some(rl), Some(ri), Some(rb)) => Some(
                    Expr::Fold(Box::new(rl), Box::new(ri), sc.len(), sc.len() + 1, Box::new(rb)),
                ),
                _ => None,
            }
        },
    }
}

pub open spec fn rxs(fs: Seq<Seq<char>>, sc: Seq<Seq<char>>, es: Seq<Sx>, i: nat) -> Option<Seq<Expr>>
    decreases es, es.len() - i,
{
    if i >= es.len() {
        Some(Seq::empty())
    } else {
        match (rx(fs, sc, es[i as int]), rxs(fs, sc, es, i + 1)) {
            (Some(x), Some(xs)) => Some(seq![x] + xs),
            _ => None,
        }
    }
}

/// p[0..n] の関数宣言。
pub open spec fn fns_upto(p: Seq<Sd>, n: nat) -> Seq<Sd>
    decreases n,
{
    if n == 0 || n > p.len() {
        Seq::empty()
    } else if p[n - 1] is Fn {
        fns_upto(p, (n - 1) as nat).push(p[n - 1])
    } else {
        fns_upto(p, (n - 1) as nat)
    }
}

/// p[0..n] の entry 宣言の名前。
pub open spec fn ents_upto(p: Seq<Sd>, n: nat) -> Seq<Seq<char>>
    decreases n,
{
    if n == 0 || n > p.len() {
        Seq::empty()
    } else if p[n - 1] is Entry {
        ents_upto(p, (n - 1) as nat).push(p[n - 1]->Entry_0)
    } else {
        ents_upto(p, (n - 1) as nat)
    }
}

pub open spec fn fname(d: Sd) -> Seq<char> {
    match d {
        Sd::Fn(f, _, _, _) => f,
        Sd::Entry(x) => x,
    }
}

pub open spec fn names_of(ds: Seq<Sd>) -> Seq<Seq<char>> {
    Seq::new(ds.len(), |i: int| fname(ds[i]))
}

pub open spec fn pnames(ps: Seq<(Seq<char>, Ty)>) -> Seq<Seq<char>> {
    Seq::new(ps.len(), |i: int| ps[i].0)
}

pub open spec fn rparams(ps: Seq<(Seq<char>, Ty)>) -> Seq<(nat, Ty)> {
    Seq::new(ps.len(), |k: int| (k as nat, ps[k].1))
}

pub open spec fn rfunc(fs: Seq<Seq<char>>, d: Sd) -> Option<Func> {
    match d {
        Sd::Fn(_, ps, r, b) => if !distinct(pnames(ps)) {
            None
        } else {
            match rx(fs, pnames(ps), b) {
                Some(body) => Some(Func { params: rparams(ps), ret: r, body }),
                None => None,
            }
        },
        Sd::Entry(_) => None,
    }
}

/// ds[0..n] の各関数の名前解決。
pub open spec fn rfuncs(fs: Seq<Seq<char>>, ds: Seq<Sd>, n: nat) -> Option<Seq<Func>>
    decreases n,
{
    if n == 0 {
        Some(Seq::empty())
    } else if n > ds.len() {
        None
    } else {
        match (rfuncs(fs, ds, (n - 1) as nat), rfunc(fs, ds[n - 1])) {
            (Some(a), Some(f)) => Some(a.push(f)),
            _ => None,
        }
    }
}

/// プログラムの名前解決と entry 検査。関数列と entry の添字を返す。
pub open spec fn resolve(p: Seq<Sd>) -> Option<(Seq<Func>, nat)> {
    let ds = fns_upto(p, p.len());
    let fs = names_of(ds);
    let es = ents_upto(p, p.len());
    if !distinct(fs) || es.len() != 1 {
        None
    } else {
        match (rfuncs(fs, ds, ds.len()), idx(fs, es[0], 0)) {
            (Some(funcs), Some(g)) => if g < funcs.len() && funcs[g as int].params.len() == 1 {
                Some((funcs, g))
            } else {
                None
            },
            _ => None,
        }
    }
}

// ------------------------------------------------------------------ 性質

/// 見つかった位置には x があり、それより前には x はない。
pub proof fn idx_props(s: Seq<Seq<char>>, x: Seq<char>, i: nat)
    ensures
        idx(s, x, i) matches Some(k) ==> i <= k < s.len() && s[k as int] == x && forall|j: int|
            i <= j < k ==> s[j] != x,
        idx(s, x, i) is None ==> forall|j: int| i <= j < s.len() ==> s[j] != x,
    decreases s.len() - i,
{
    if i < s.len() {
        idx_props(s, x, i + 1);
    }
}

/// 名前が相異なる列では、位置 k の名前の位置は k（解決は一意）。
pub proof fn idx_unique(s: Seq<Seq<char>>, k: int)
    requires
        distinct(s),
        0 <= k < s.len(),
    ensures
        idx(s, s[k], 0) == Some(k as nat),
{
    idx_props(s, s[k], 0);
    if let Some(m) = idx(s, s[k], 0) {
        if (m as int) < k {
            assert(s[m as int] != s[k]);
        }
    }
}

/// 解決した変数は可視変数の範囲内を指す（scope 整合性）。
pub open spec fn scoped(e: Expr, n: nat) -> bool
    decreases e, 0nat,
{
    match e {
        Expr::Var(k) => k < n,
        Expr::List(_, es) => scoped_all(es, n, 0),
        Expr::Some(a) => scoped(*a, n),
        Expr::Pair(a, b) => scoped(*a, n) && scoped(*b, n),
        Expr::Builtin(_, es) => scoped_all(es, n, 0),
        Expr::Call(_, es) => scoped_all(es, n, 0),
        Expr::Let(x, a, b) => x == n && scoped(*a, n) && scoped(*b, n + 1),
        Expr::If(c, a, b) => scoped(*c, n) && scoped(*a, n) && scoped(*b, n),
        Expr::Fold(l, i, a, x, b) => a == n && x == n + 1 && scoped(*l, n) && scoped(*i, n) && scoped(*b, n + 2),
        _ => true,
    }
}

pub open spec fn scoped_all(es: Seq<Expr>, n: nat, i: nat) -> bool
    decreases es, es.len() - i,
{
    i >= es.len() || (scoped(es[i as int], n) && scoped_all(es, n, i + 1))
}

/// 名前解決の結果は scope 整合で、scope 内の名前は常に相異なる（シャドーがない）。
pub proof fn rx_scoped(fs: Seq<Seq<char>>, sc: Seq<Seq<char>>, e: Sx)
    requires
        distinct(sc),
    ensures
        rx(fs, sc, e) matches Some(x) ==> scoped(x, sc.len()),
    decreases e, 0nat,
{
    match e {
        Sx::Var(x) => idx_props(sc, x, 0),
        Sx::List(_, es) => rxs_scoped(fs, sc, es, 0),
        Sx::Some(a) => rx_scoped(fs, sc, *a),
        Sx::Pair(a, b) => {
            rx_scoped(fs, sc, *a);
            rx_scoped(fs, sc, *b);
        },
        Sx::Builtin(_, es) => rxs_scoped(fs, sc, es, 0),
        Sx::Call(_, es) => rxs_scoped(fs, sc, es, 0),
        Sx::Let(x, a, b) => {
            idx_props(sc, x, 0);
            rx_scoped(fs, sc, *a);
            if idx(sc, x, 0) is None {
                let s2 = sc.push(x);
                assert forall|i: int, j: int| 0 <= i < j < s2.len() implies s2[i] != s2[j] by {
                    if j == sc.len() {
                        assert(sc[i] != x);
                    }
                }
                rx_scoped(fs, s2, *b);
            }
        },
        Sx::If(c, a, b) => {
            rx_scoped(fs, sc, *c);
            rx_scoped(fs, sc, *a);
            rx_scoped(fs, sc, *b);
        },
        Sx::Fold(l, i, a, x, b) => {
            idx_props(sc, a, 0);
            idx_props(sc, x, 0);
            rx_scoped(fs, sc, *l);
            rx_scoped(fs, sc, *i);
            if !(a == x || idx(sc, a, 0) is Some || idx(sc, x, 0) is Some) {
                let s2 = sc.push(a).push(x);
                assert forall|p: int, q: int| 0 <= p < q < s2.len() implies s2[p] != s2[q] by {
                    if q == sc.len() + 1 {
                        if p < sc.len() {
                            assert(sc[p] != x);
                        }
                    } else if q == sc.len() {
                        assert(sc[p] != a);
                    }
                }
                rx_scoped(fs, s2, *b);
            }
        },
        _ => {},
    }
}

pub proof fn rxs_scoped(fs: Seq<Seq<char>>, sc: Seq<Seq<char>>, es: Seq<Sx>, i: nat)
    requires
        distinct(sc),
    ensures
        rxs(fs, sc, es, i) matches Some(xs) ==> scoped_all(xs, sc.len(), 0),
    decreases es, es.len() - i,
{
    if i < es.len() {
        rx_scoped(fs, sc, es[i as int]);
        rxs_scoped(fs, sc, es, i + 1);
        if let Some(xs) = rxs(fs, sc, es, i) {
            let x = rx(fs, sc, es[i as int])->Some_0;
            let ys = rxs(fs, sc, es, i + 1)->Some_0;
            scoped_all_cons(x, ys, sc.len(), 0);
        }
    }
}

proof fn scoped_all_cons(x: Expr, ys: Seq<Expr>, n: nat, i: nat)
    requires
        scoped(x, n),
        scoped_all(ys, n, i),
    ensures
        scoped_all(seq![x] + ys, n, i + 1) && (i == 0 ==> scoped_all(seq![x] + ys, n, 0)),
    decreases ys.len() - i,
{
    let s = seq![x] + ys;
    if i < ys.len() {
        assert(s[(i + 1) as int] == ys[i as int]);
        scoped_all_cons(x, ys, n, i + 1);
    }
    if i == 0 {
        assert(s[0] == x);
    }
}

// ------------------------------------------------------------------ exec

pub open spec fn vnames(v: Seq<Vec<char>>) -> Seq<Seq<char>> {
    Seq::new(v.len(), |i: int| v[i]@)
}

fn idx_e(s: &Vec<Vec<char>>, x: &Vec<char>) -> (r: Option<usize>)
    ensures
        match r {
            Some(k) => idx(vnames(s@), x@, 0) == Some(k as nat) && k < s@.len(),
            None => idx(vnames(s@), x@, 0) is None,
        },
{
    let ghost v = vnames(s@);
    let mut i: usize = 0;
    while i < s.len()
        invariant
            v == vnames(s@),
            i <= s@.len(),
            idx(v, x@, 0) == idx(v, x@, i as nat),
        decreases s@.len() - i,
    {
        proof {
            assert(v[i as int] == s@[i as int]@);
        }
        if eq_chars(&s[i], x) {
            return Some(i);
        }
        i += 1;
    }
    None
}

fn distinct_e(s: &Vec<Vec<char>>) -> (r: bool)
    ensures
        r == distinct(vnames(s@)),
{
    let ghost v = vnames(s@);
    let mut j: usize = 0;
    while j < s.len()
        invariant
            v == vnames(s@),
            j <= s@.len(),
            forall|a: int, b: int| 0 <= a < b < j ==> v[a] != v[b],
        decreases s@.len() - j,
    {
        let mut i: usize = 0;
        while i < j
            invariant
                v == vnames(s@),
                i <= j < s@.len(),
                forall|a: int| 0 <= a < i ==> v[a] != v[j as int],
            decreases j - i,
        {
            proof {
                assert(v[i as int] == s@[i as int]@);
                assert(v[j as int] == s@[j as int]@);
            }
            if eq_chars(&s[i], &s[j]) {
                return false;
            }
            i += 1;
        }
        j += 1;
    }
    true
}

proof fn vnames_push(a: Seq<Vec<char>>, x: Vec<char>)
    ensures
        vnames(a.push(x)) == vnames(a).push(x@),
{
    assert(vnames(a.push(x)) =~= vnames(a).push(x@));
}

proof fn view_exprs_push(a: Vec<EExpr>, b: Vec<EExpr>, e: EExpr)
    requires
        b@ == a@.push(e),
    ensures
        view_exprs(b) == view_exprs(a) + seq![view_expr(e)],
{
    assert(view_exprs(b) =~= view_exprs(a) + seq![view_expr(e)]);
}

pub open spec fn cato(u: Seq<Expr>, o: Option<Seq<Expr>>) -> Option<Seq<Expr>> {
    match o {
        Some(w) => Some(u + w),
        None => None,
    }
}

pub fn rx_e(fs: &Vec<Vec<char>>, sc: &mut Vec<Vec<char>>, e: &SExpr) -> (r: Option<EExpr>)
    ensures
        final(sc)@ == old(sc)@,
        match r {
            Some(x) => rx(vnames(fs@), vnames(old(sc)@), vx(*e)) == Some(view_expr(x)),
            None => rx(vnames(fs@), vnames(old(sc)@), vx(*e)) is None,
        },
    decreases e, 1nat,
{
    let ghost f = vnames(fs@);
    let ghost s = vnames(sc@);
    match e {
        SExpr::Int(n) => Some(EExpr::Int(n.copy())),
        SExpr::Bool(b) => Some(EExpr::Bool(*b)),
        SExpr::Unit => Some(EExpr::Unit),
        SExpr::Var(x) => match idx_e(sc, x) {
            Some(k) => Some(EExpr::Var(k)),
            None => None,
        },
        SExpr::List(t, es) => match rxs_e(fs, sc, es) {
            Some(xs) => Some(EExpr::List(ty_clone(t), xs)),
            None => None,
        },
        SExpr::Some(a) => match rx_e(fs, sc, a) {
            Some(x) => Some(EExpr::Some(Box::new(x))),
            None => None,
        },
        SExpr::None(t) => Some(EExpr::None(ty_clone(t))),
        SExpr::Pair(a, b) => {
            let x = rx_e(fs, sc, a);
            let y = rx_e(fs, sc, b);
            match (x, y) {
                (Some(x), Some(y)) => Some(EExpr::Pair(Box::new(x), Box::new(y))),
                _ => None,
            }
        },
        SExpr::Builtin(b, es) => match rxs_e(fs, sc, es) {
            Some(xs) => Some(EExpr::Builtin(*b, xs)),
            None => None,
        },
        SExpr::Call(g, es) => {
            let gi = idx_e(fs, g);
            let xs = rxs_e(fs, sc, es);
            match (gi, xs) {
                (Some(gi), Some(xs)) => Some(EExpr::Call(gi, xs)),
                _ => None,
            }
        },
        SExpr::Let(..) => rx_let_e(fs, sc, e),
        SExpr::If(c, a, b) => {
            let x = rx_e(fs, sc, c);
            let y = rx_e(fs, sc, a);
            let z = rx_e(fs, sc, b);
            match (x, y, z) {
                (Some(x), Some(y), Some(z)) => Some(EExpr::If(Box::new(x), Box::new(y), Box::new(z))),
                _ => None,
            }
        },
        SExpr::Fold(..) => rx_fold_e(fs, sc, e),
    }
}

fn rx_let_e(fs: &Vec<Vec<char>>, sc: &mut Vec<Vec<char>>, e: &SExpr) -> (r: Option<EExpr>)
    requires
        e is Let,
    ensures
        final(sc)@ == old(sc)@,
        match r {
            Some(x) => rx(vnames(fs@), vnames(old(sc)@), vx(*e)) == Some(view_expr(x)),
            None => rx(vnames(fs@), vnames(old(sc)@), vx(*e)) is None,
        },
    decreases e, 0nat,
{
    let ghost s0 = sc@;
    if let SExpr::Let(x, a, b) = e {
        if idx_e(sc, x).is_some() {
            return None;
        }
        let ra = rx_e(fs, sc, a);
        if ra.is_none() {
            return None;
        }
        sc.push(clone_chars(x));
        let k = sc.len() - 1;
        proof {
            vnames_push(s0, sc@[k as int]);
        }
        let rb = rx_e(fs, sc, b);
        sc.pop();
        proof {
            assert(sc@ =~= s0);
        }
        match (ra, rb) {
            (Some(ra), Some(rb)) => Some(EExpr::Let(k, Box::new(ra), Box::new(rb))),
            _ => None,
        }
    } else {
        None
    }
}

fn rx_fold_e(fs: &Vec<Vec<char>>, sc: &mut Vec<Vec<char>>, e: &SExpr) -> (r: Option<EExpr>)
    requires
        e is Fold,
    ensures
        final(sc)@ == old(sc)@,
        match r {
            Some(x) => rx(vnames(fs@), vnames(old(sc)@), vx(*e)) == Some(view_expr(x)),
            None => rx(vnames(fs@), vnames(old(sc)@), vx(*e)) is None,
        },
    decreases e, 0nat,
{
    let ghost s0 = sc@;
    if let SExpr::Fold(l, i, a, x, b) = e {
        if eq_chars(a, x) || idx_e(sc, a).is_some() || idx_e(sc, x).is_some() {
            return None;
        }
        let rl = rx_e(fs, sc, l);
        let ri = rx_e(fs, sc, i);
        if rl.is_none() || ri.is_none() {
            return None;
        }
        sc.push(clone_chars(a));
        let ghost s1 = sc@;
        sc.push(clone_chars(x));
        let k1 = sc.len() - 1;
        let k = k1 - 1;
        proof {
            vnames_push(s0, s1[k as int]);
            vnames_push(s1, sc@[k1 as int]);
        }
        let rb = rx_e(fs, sc, b);
        sc.pop();
        sc.pop();
        proof {
            assert(sc@ =~= s0);
        }
        match (rl, ri, rb) {
            (Some(rl), Some(ri), Some(rb)) => Some(EExpr::Fold(Box::new(rl), Box::new(ri), k, k1, Box::new(rb))),
            _ => None,
        }
    } else {
        None
    }
}

pub fn rxs_e(fs: &Vec<Vec<char>>, sc: &mut Vec<Vec<char>>, es: &Vec<SExpr>) -> (r: Option<Vec<EExpr>>)
    ensures
        final(sc)@ == old(sc)@,
        match r {
            Some(xs) => rxs(vnames(fs@), vnames(old(sc)@), vxs(*es), 0) == Some(view_exprs(xs)),
            None => rxs(vnames(fs@), vnames(old(sc)@), vxs(*es), 0) is None,
        },
    decreases es, 0nat,
{
    let ghost f = vnames(fs@);
    let ghost s = vnames(sc@);
    let ghost s0 = sc@;
    let ghost v = vxs(*es);
    let mut out: Vec<EExpr> = Vec::new();
    let mut i: usize = 0;
    proof {
        assert(view_exprs(out) =~= Seq::<Expr>::empty());
        if let Some(w) = rxs(f, s, v, 0) {
            assert(Seq::<Expr>::empty() + w =~= w);
        }
    }
    while i < es.len()
        invariant
            f == vnames(fs@),
            s == vnames(sc@),
            sc@ == s0,
            s0 == old(sc)@,
            v == vxs(*es),
            i <= es@.len(),
            rxs(f, s, v, 0) == cato(view_exprs(out), rxs(f, s, v, i as nat)),
        decreases es@.len() - i,
    {
        proof {
            vstd::std_specs::vec::axiom_vec_index_decreases(*es, i as int);
            assert(v[i as int] == vx(es@[i as int]));
        }
        let ghost o0 = out;
        match rx_e(fs, sc, &es[i]) {
            Some(x) => {
                let ghost xv = view_expr(x);
                out.push(x);
                proof {
                    view_exprs_push(o0, out, x);
                    if let Some(w) = rxs(f, s, v, (i + 1) as nat) {
                        assert(view_exprs(o0) + (seq![xv] + w) =~= view_exprs(out) + w);
                    }
                }
                i += 1;
            },
            None => return None,
        }
    }
    proof {
        assert(view_exprs(out) + Seq::<Expr>::empty() =~= view_exprs(out));
    }
    Some(out)
}

pub open spec fn vfuncs(fs: Seq<EFunc>) -> Seq<Func> {
    Seq::new(fs.len(), |i: int| view_func(fs[i]))
}

fn rfunc_e(fs: &Vec<Vec<char>>, d: &SDecl) -> (r: Option<EFunc>)
    ensures
        match r {
            Some(f) => rfunc(vnames(fs@), vd(*d)) == Some(view_func(f)),
            None => rfunc(vnames(fs@), vd(*d)) is None,
        },
{
    match d {
        SDecl::Fn(_, ps, ret, body) => {
            let ghost pv = vps(ps@);
            let mut sc: Vec<Vec<char>> = Vec::new();
            let mut params: Vec<(usize, Ty)> = Vec::new();
            let mut i: usize = 0;
            while i < ps.len()
                invariant
                    pv == vps(ps@),
                    i <= ps@.len(),
                    vnames(sc@) == pnames(pv).subrange(0, i as int),
                    view_params(params@) == rparams(pv).subrange(0, i as int),
                decreases ps@.len() - i,
            {
                let ghost s0 = sc@;
                let ghost q0 = params@;
                let (x, t) = &ps[i];
                sc.push(clone_chars(x));
                params.push((i, ty_clone(t)));
                proof {
                    vnames_push(s0, sc@[i as int]);
                    assert(pv[i as int] == (x@, *t));
                    assert(vnames(sc@) == vnames(s0).push(x@));
                    assert(pnames(pv).subrange(0, i + 1) =~= pnames(pv).subrange(0, i as int).push(x@));
                    assert(view_params(params@) =~= view_params(q0).push((i as nat, *t)));
                    assert(rparams(pv).subrange(0, i + 1) =~= rparams(pv).subrange(0, i as int).push((i as nat, *t)));
                }
                i += 1;
            }
            proof {
                assert(pnames(pv).subrange(0, i as int) =~= pnames(pv));
                assert(rparams(pv).subrange(0, i as int) =~= rparams(pv));
            }
            if !distinct_e(&sc) {
                return None;
            }
            match rx_e(fs, &mut sc, body) {
                Some(b) => Some(EFunc { params, ret: ty_clone(ret), body: b }),
                None => None,
            }
        },
        SDecl::Entry(_) => None,
    }
}

/// 名前解決と entry 検査。関数列と entry の添字を返す。
pub fn resolve_e(p: &Vec<SDecl>) -> (r: Option<(Vec<EFunc>, usize)>)
    ensures
        match r {
            Some((fs, g)) => resolve(vds(p@)) == Some((vfuncs(fs@), g as nat)) && g < fs@.len(),
            None => resolve(vds(p@)) is None,
        },
{
    let ghost v = vds(p@);
    let mut names: Vec<Vec<char>> = Vec::new();
    let mut fidx: Vec<usize> = Vec::new();
    let mut ents: Vec<usize> = Vec::new();
    let mut i: usize = 0;
    proof {
        assert(vnames(names@) =~= names_of(fns_upto(v, 0)));
    }
    while i < p.len()
        invariant
            v == vds(p@),
            i <= p@.len(),
            vnames(names@) == names_of(fns_upto(v, i as nat)),
            fns_upto(v, i as nat) == Seq::new(fidx@.len(), |m: int| v[fidx@[m] as int]),
            forall|k: int| 0 <= k < fidx@.len() ==> #[trigger] fidx@[k] < p@.len(),
            ents_upto(v, i as nat) == Seq::new(ents@.len(), |m: int| v[ents@[m] as int]->Entry_0),
            forall|k: int| 0 <= k < ents@.len() ==> #[trigger] ents@[k] < p@.len() && v[ents@[k] as int] is Entry,
        decreases p@.len() - i,
    {
        proof {
            assert(v[i as int] == vd(p@[i as int]));
        }
        let ghost n0 = names@;
        let ghost f0 = fns_upto(v, i as nat);
        let ghost e0 = ents_upto(v, i as nat);
        match &p[i] {
            SDecl::Fn(f, _, _, _) => {
                names.push(clone_chars(f));
                fidx.push(i);
                proof {
                    assert(fns_upto(v, (i + 1) as nat) == f0.push(v[i as int]));
                    assert(ents_upto(v, (i + 1) as nat) == e0);
                    vnames_push(n0, names@[n0.len() as int]);
                    assert(names_of(f0.push(v[i as int])) =~= names_of(f0).push(fname(v[i as int])));
                    assert(f0.push(v[i as int]) =~= Seq::new(fidx@.len(), |m: int| v[fidx@[m] as int]));
                }
            },
            SDecl::Entry(_) => {
                ents.push(i);
                proof {
                    assert(fns_upto(v, (i + 1) as nat) == f0);
                    assert(ents_upto(v, (i + 1) as nat) == e0.push(v[i as int]->Entry_0));
                    assert(e0.push(v[i as int]->Entry_0) =~= Seq::new(ents@.len(), |m: int| v[ents@[m] as int]->Entry_0));
                }
            },
        }
        i += 1;
    }
    let ghost ds = fns_upto(v, v.len());
    let ghost fsv = names_of(ds);
    if !distinct_e(&names) || ents.len() != 1 {
        return None;
    }
    let mut out: Vec<EFunc> = Vec::new();
    let mut k: usize = 0;
    proof {
        assert(vfuncs(out@) =~= Seq::<Func>::empty());
    }
    while k < fidx.len()
        invariant
            v == vds(p@),
            ds == fns_upto(v, v.len()),
            fsv == names_of(ds),
            vnames(names@) == fsv,
            ds == Seq::new(fidx@.len(), |m: int| v[fidx@[m] as int]),
            forall|m: int| 0 <= m < fidx@.len() ==> #[trigger] fidx@[m] < p@.len(),
            k <= fidx@.len(),
            out@.len() == k,
            rfuncs(fsv, ds, k as nat) == Some(vfuncs(out@)),
        decreases fidx@.len() - k,
    {
        let j = fidx[k];
        proof {
            assert(ds[k as int] == v[j as int]);
            assert(v[j as int] == vd(p@[j as int]));
        }
        match rfunc_e(&names, &p[j]) {
            Some(f) => {
                let ghost o0 = out@;
                out.push(f);
                proof {
                    assert(vfuncs(out@) =~= vfuncs(o0).push(view_func(f)));
                }
                k += 1;
            },
            None => {
                proof {
                    rfuncs_none(fsv, ds, (k + 1) as nat, ds.len());
                }
                return None;
            },
        }
    }
    let e = ents[0];
    proof {
        assert(ents_upto(v, v.len())[0] == v[e as int]->Entry_0);
        assert(v[e as int] == vd(p@[e as int]));
    }
    let g = match &p[e] {
        SDecl::Entry(x) => match idx_e(&names, x) {
            Some(g) => g,
            None => return None,
        },
        _ => return None,
    };
    proof {
        idx_props(fsv, ents_upto(v, v.len())[0], 0);
    }
    if out[g].params.len() != 1 {
        return None;
    }
    Some((out, g))
}

/// 途中の関数が解決できなければ全体も解決できない。
proof fn rfuncs_none(fs: Seq<Seq<char>>, ds: Seq<Sd>, n: nat, m: nat)
    requires
        rfuncs(fs, ds, n) is None,
        n <= m,
    ensures
        rfuncs(fs, ds, m) is None,
    decreases m - n,
{
    if n < m {
        rfuncs_none(fs, ds, n + 1, m);
    }
}

} // verus!
