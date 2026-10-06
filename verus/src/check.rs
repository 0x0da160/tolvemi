//! 検証済みの型検査器とランク（DAG 証明書）検査（§11.2 の 4、5）。
//!
//! `check_prog` が真を返したなら spec の整形式条件 `wf` が成り立つ。`wf` は呼出し先の
//! ランクが真に小さいことを含むので、ランク列は呼出しグラフが DAG であることの証明書になる。
//! ランク列そのものは crates/tlvm の未検証の Tarjan 実装が作るが、ここで検査するので
//! その正しさを信頼する必要はない。

use crate::bigint::Int;
use crate::ir::*;
use crate::proof::*;
use crate::spec::*;
use crate::value::*;
use std::rc::Rc;
use vstd::prelude::*;

verus! {

/// 型環境（後に積んだ束縛が前を隠す）。
pub open spec fn ctx_view(s: Seq<(usize, Ty)>) -> Map<nat, Ty>
    decreases s.len(),
{
    if s.len() == 0 {
        Map::empty()
    } else {
        ctx_view(s.drop_last()).insert(s.last().0 as nat, s.last().1)
    }
}

pub proof fn ctx_view_push(s: Seq<(usize, Ty)>, x: usize, t: Ty)
    ensures
        ctx_view(s.push((x, t))) == ctx_view(s).insert(x as nat, t),
{
    assert(s.push((x, t)).drop_last() =~= s);
}

pub proof fn ctx_view_lookup(s: Seq<(usize, Ty)>, i: int, x: usize)
    requires
        0 <= i < s.len(),
        s[i].0 == x,
        forall|j: int| i < j < s.len() ==> (#[trigger] s[j]).0 != x,
    ensures
        ctx_view(s).contains_key(x as nat),
        ctx_view(s)[x as nat] == s[i].1,
    decreases s.len(),
{
    if i < s.len() - 1 {
        let d = s.drop_last();
        assert forall|j: int| i < j < d.len() implies (#[trigger] d[j]).0 != x by {
            assert(d[j] == s[j]);
        }
        ctx_view_lookup(d, i, x);
    }
}

fn ctx_lookup(ctx: &Vec<(usize, Ty)>, x: usize) -> (r: Option<Ty>)
    ensures
        r is Some ==> ctx_view(ctx@).contains_key(x as nat) && ctx_view(ctx@)[x as nat] == r->Some_0,
{
    let mut i = ctx.len();
    while i > 0
        invariant
            i <= ctx@.len(),
            forall|j: int| i <= j < ctx@.len() ==> (#[trigger] ctx@[j]).0 != x,
        decreases i,
    {
        i = i - 1;
        if ctx[i].0 == x {
            proof {
                ctx_view_lookup(ctx@, i as int, x);
            }
            return Some(ty_clone(&ctx[i].1));
        }
    }
    None
}

/// 各要素の型が分かれば、要素列の型列が分かる（後ろから組み立てる）。
pub proof fn ty_args_from_each(p: Prog, r: nat, ctx: Map<nat, Ty>, es: Seq<Expr>, ts: Seq<Ty>, i: nat)
    requires
        ts.len() == es.len(),
        i <= es.len(),
        forall|k: int| 0 <= k < es.len() ==> ty_expr(p, r, ctx, #[trigger] es[k]) == Some(ts[k]),
    ensures
        ty_args(p, r, ctx, es, i) == Some(ts.subrange(i as int, ts.len() as int)),
    decreases es.len() - i,
{
    if i < es.len() {
        ty_args_from_each(p, r, ctx, es, ts, i + 1);
        assert(ty_expr(p, r, ctx, es[i as int]) == Some(ts[i as int]));
        assert(seq![ts[i as int]] + ts.subrange((i + 1) as int, ts.len() as int) =~= ts.subrange(i as int, ts.len() as int));
    } else {
        assert(ts.subrange(i as int, ts.len() as int) =~= Seq::<Ty>::empty());
    }
}

pub fn builtin_ty(b: Builtin, ts: &Vec<Ty>) -> (r: Option<Ty>)
    ensures
        r is Some ==> builtin_type(b, ts@) == r,
{
    let n = ts.len();
    match b {
        Builtin::Add | Builtin::Sub | Builtin::Mul => {
            if n == 2 && ty_eq(&ts[0], &Ty::Int) && ty_eq(&ts[1], &Ty::Int) {
                Some(Ty::Int)
            } else {
                None
            }
        },
        Builtin::Neg => if n == 1 && ty_eq(&ts[0], &Ty::Int) {
            Some(Ty::Int)
        } else {
            None
        },
        Builtin::Lt | Builtin::Le => {
            if n == 2 && ty_eq(&ts[0], &Ty::Int) && ty_eq(&ts[1], &Ty::Int) {
                Some(Ty::Bool)
            } else {
                None
            }
        },
        Builtin::Eq => if n == 2 && ty_eq(&ts[0], &ts[1]) {
            Some(Ty::Bool)
        } else {
            None
        },
        Builtin::Mod => {
            if n == 2 && ty_eq(&ts[0], &Ty::Int) && ty_eq(&ts[1], &Ty::Int) {
                Some(Ty::Option(Box::new(Ty::Int)))
            } else {
                None
            }
        },
        Builtin::Fst => if n == 1 {
            match &ts[0] {
                Ty::Pair(a, _) => Some(ty_clone(a)),
                _ => None,
            }
        } else {
            None
        },
        Builtin::Snd => if n == 1 {
            match &ts[0] {
                Ty::Pair(_, c) => Some(ty_clone(c)),
                _ => None,
            }
        } else {
            None
        },
        Builtin::Cons => {
            if n == 2 && ty_eq(&ts[1], &Ty::List(Box::new(ty_clone(&ts[0])))) {
                Some(ty_clone(&ts[1]))
            } else {
                None
            }
        },
        Builtin::Concat => {
            if n == 2 && (match &ts[0] {
                Ty::List(_) => true,
                _ => false,
            }) && ty_eq(&ts[1], &ts[0]) {
                Some(ty_clone(&ts[0]))
            } else {
                None
            }
        },
        Builtin::Reverse => if n == 1 && (match &ts[0] {
            Ty::List(_) => true,
            _ => false,
        }) {
            Some(ty_clone(&ts[0]))
        } else {
            None
        },
        Builtin::Length => if n == 1 && (match &ts[0] {
            Ty::List(_) => true,
            _ => false,
        }) {
            Some(Ty::Int)
        } else {
            None
        },
    }
}

/// ランク上限 r の関数本体内での式の型（spec の `ty_expr` と一致する）。
pub fn ty_of(p: &EProg, r: usize, ctx: &mut Vec<(usize, Ty)>, e: &EExpr) -> (res: Option<Ty>)
    ensures
        final(ctx)@ == old(ctx)@,
        res is Some ==> ty_expr(view_prog(*p), r as nat, ctx_view(old(ctx)@), view_expr(*e)) == res,
    decreases e, 1nat,
{
    let ghost pp = view_prog(*p);
    let ghost c = ctx_view(ctx@);
    match e {
        EExpr::Int(_) => Some(Ty::Int),
        EExpr::Bool(_) => Some(Ty::Bool),
        EExpr::Unit => Some(Ty::Unit),
        EExpr::Var(x) => ctx_lookup(ctx, *x),
        EExpr::List(t, es) => {
            let ts = ty_list_of(p, r, ctx, es)?;
            let mut k = 0;
            while k < ts.len()
                invariant
                    ctx@ == old(ctx)@,
                    forall|j: int| 0 <= j < k ==> #[trigger] ts@[j] == *t,
                decreases ts@.len() - k,
            {
                if !ty_eq(&ts[k], t) {
                    return None;
                }
                k = k + 1;
            }
            Some(Ty::List(Box::new(ty_clone(t))))
        },
        EExpr::Some(x) => {
            let t = ty_of(p, r, ctx, x)?;
            Some(Ty::Option(Box::new(t)))
        },
        EExpr::None(t) => Some(Ty::Option(Box::new(ty_clone(t)))),
        EExpr::Pair(a, b) => {
            let ta = ty_of(p, r, ctx, a)?;
            let tb = ty_of(p, r, ctx, b)?;
            Some(Ty::Pair(Box::new(ta), Box::new(tb)))
        },
        EExpr::Builtin(b, es) => {
            let ts = ty_list_of(p, r, ctx, es)?;
            builtin_ty(*b, &ts)
        },
        EExpr::Call(g, es) => {
            let ts = ty_list_of(p, r, ctx, es)?;
            if *g >= p.funcs.len() || *g >= p.rank.len() || p.rank[*g] >= r {
                return None;
            }
            let f = &p.funcs[*g];
            if ts.len() != f.params.len() {
                return None;
            }
            let mut k = 0;
            while k < ts.len()
                invariant
                    ctx@ == old(ctx)@,
                    ts@.len() == f.params@.len(),
                    forall|j: int| 0 <= j < k ==> #[trigger] ts@[j] == f.params@[j].1,
                decreases ts@.len() - k,
            {
                if !ty_eq(&ts[k], &f.params[k].1) {
                    return None;
                }
                k = k + 1;
            }
            proof {
                assert(pp.funcs[*g as int] == view_func(p.funcs@[*g as int]));
                assert forall|j: int| 0 <= j < ts@.len() implies #[trigger] ts@[j] == pp.funcs[*g as int].params[j].1 by {
                    assert(ts@[j] == f.params@[j].1);
                }
            }
            Some(ty_clone(&f.ret))
        },
        EExpr::Let(x, a, b) => {
            let ta = ty_of(p, r, ctx, a)?;
            let ghost before = ctx@;
            ctx.push((*x, ty_clone(&ta)));
            proof {
                ctx_view_push(before, *x, ta);
            }
            let tb = ty_of(p, r, ctx, b);
            ctx.pop();
            proof {
                assert(ctx@ =~= before);
            }
            tb
        },
        EExpr::If(c, a, b) => {
            let tc = ty_of(p, r, ctx, c)?;
            let ta = ty_of(p, r, ctx, a)?;
            let tb = ty_of(p, r, ctx, b)?;
            if ty_eq(&tc, &Ty::Bool) && ty_eq(&ta, &tb) {
                Some(ta)
            } else {
                None
            }
        },
        EExpr::Fold(xs, init, acc, item, body) => {
            let tx = ty_of(p, r, ctx, xs)?;
            let ta = ty_of(p, r, ctx, init)?;
            let el = match &tx {
                Ty::List(el) => ty_clone(el),
                _ => return None,
            };
            let ghost before = ctx@;
            ctx.push((*acc, ty_clone(&ta)));
            ctx.push((*item, el));
            proof {
                ctx_view_push(before, *acc, ta);
                ctx_view_push(before.push((*acc, ta)), *item, el);
            }
            let tb = ty_of(p, r, ctx, body);
            ctx.pop();
            ctx.pop();
            proof {
                assert(ctx@ =~= before);
            }
            match tb {
                Some(tb) => if ty_eq(&tb, &ta) {
                    Some(ta)
                } else {
                    None
                },
                None => None,
            }
        },
    }
}

/// 式列の型列（spec の `ty_args(.., 0)` と一致する）。
pub fn ty_list_of(p: &EProg, r: usize, ctx: &mut Vec<(usize, Ty)>, es: &Vec<EExpr>) -> (res: Option<Vec<Ty>>)
    ensures
        final(ctx)@ == old(ctx)@,
        res is Some ==> ty_args(view_prog(*p), r as nat, ctx_view(old(ctx)@), view_exprs(*es), 0) == Some(
            res->Some_0@,
        ),
    decreases es, 0nat,
{
    let ghost pp = view_prog(*p);
    let ghost c = ctx_view(ctx@);
    let ghost esv = view_exprs(*es);
    let ghost c0 = ctx@;
    let mut ts: Vec<Ty> = Vec::new();
    let mut i = 0;
    while i < es.len()
        invariant
            ctx@ == c0,
            c0 == old(ctx)@,
            c == ctx_view(c0),
            pp == view_prog(*p),
            esv == view_exprs(*es),
            i <= es@.len(),
            ts@.len() == i,
            forall|k: int| 0 <= k < i ==> ty_expr(pp, r as nat, c, #[trigger] esv[k]) == Some(ts@[k]),
        decreases es@.len() - i,
    {
        proof {
            vstd::std_specs::vec::axiom_vec_index_decreases(*es, i as int);
        }
        let t = ty_of(p, r, ctx, &es[i])?;
        proof {
            assert(esv[i as int] == view_expr(es@[i as int]));
        }
        let ghost old_ts = ts@;
        ts.push(t);
        proof {
            assert forall|k: int| 0 <= k < i + 1 implies ty_expr(pp, r as nat, c, #[trigger] esv[k]) == Some(ts@[k]) by {
                if k < i {
                    assert(ts@[k] == old_ts[k]);
                }
            }
        }
        i = i + 1;
    }
    proof {
        ty_args_from_each(pp, r as nat, c, esv, ts@, 0);
        assert(ts@.subrange(0, ts@.len() as int) =~= ts@);
    }
    Some(ts)
}

/// 引数列から作る型環境（spec の `param_ctx` と一致する）。
fn params_ctx(params: &Vec<(usize, Ty)>) -> (ctx: Vec<(usize, Ty)>)
    ensures
        ctx_view(ctx@) == param_ctx(view_params(params@), params@.len()),
{
    let mut ctx: Vec<(usize, Ty)> = Vec::new();
    let mut k = 0;
    while k < params.len()
        invariant
            k <= params@.len(),
            ctx_view(ctx@) == param_ctx(view_params(params@), k as nat),
        decreases params@.len() - k,
    {
        let ghost before = ctx@;
        ctx.push((params[k].0, ty_clone(&params[k].1)));
        proof {
            ctx_view_push(before, params@[k as int].0, params@[k as int].1);
        }
        k = k + 1;
    }
    ctx
}

/// 整形式検査。真なら spec の `wf` が成り立つ。
pub fn check_prog(p: &EProg) -> (ok: bool)
    ensures
        ok ==> wf(view_prog(*p)),
{
    let ghost pp = view_prog(*p);
    if p.rank.len() != p.funcs.len() || p.entry >= p.funcs.len() || p.funcs[p.entry].params.len() != 1 {
        return false;
    }
    let mut g = 0;
    while g < p.funcs.len()
        invariant
            pp == view_prog(*p),
            p.rank@.len() == p.funcs@.len(),
            g <= p.funcs@.len(),
            forall|h: int|
                0 <= h < g ==> #[trigger] ty_expr(
                    pp,
                    pp.rank[h],
                    param_ctx(pp.funcs[h].params, pp.funcs[h].params.len()),
                    pp.funcs[h].body,
                ) == Some(pp.funcs[h].ret),
        decreases p.funcs@.len() - g,
    {
        let f = &p.funcs[g];
        let mut ctx = params_ctx(&f.params);
        let t = ty_of(p, p.rank[g], &mut ctx, &f.body);
        match t {
            Some(t) => if !ty_eq(&t, &f.ret) {
                return false;
            },
            None => return false,
        }
        proof {
            assert(pp.funcs[g as int] == view_func(p.funcs@[g as int]));
            assert(pp.rank[g as int] == p.rank@[g as int] as nat);
        }
        g = g + 1;
    }
    proof {
        assert(pp.funcs[p.entry as int] == view_func(p.funcs@[p.entry as int]));
    }
    true
}

// ------------------------------------------------------------------ 値の型検査

/// 値が型を持つかを調べる（復号済み入力の検査に使う）。
pub fn has_type(v: &Rc<Value>, t: &Ty) -> (r: bool)
    ensures
        r ==> val_type(view_val(**v), *t),
    decreases **v, 1nat,
{
    match (&**v, t) {
        (Value::Int(_), Ty::Int) => true,
        (Value::Bool(_), Ty::Bool) => true,
        (Value::Unit, Ty::Unit) => true,
        (Value::None, Ty::Option(_)) => true,
        (Value::Some(x), Ty::Option(a)) => has_type(x, a),
        (Value::Pair(a, b), Ty::Pair(ta, tb)) => has_type(a, ta) && has_type(b, tb),
        (Value::Nil, Ty::List(el)) | (Value::Cons(_, _), Ty::List(el)) => {
            let ok = list_has_type(v, el);
            proof {
                if ok {
                    val_type_list(sp(*v), dr(el));
                    assert(*t == Ty::List(Box::new(dr(el))));
                }
            }
            ok
        },
        _ => false,
    }
}

fn list_has_type(v: &Rc<Value>, el: &Ty) -> (r: bool)
    ensures
        r ==> forall|k: int| 0 <= k < spine(**v).len() ==> val_type(#[trigger] spine(**v)[k], *el),
    decreases **v, 0nat,
{
    match &**v {
        Value::Cons(h, t) => {
            if !has_type(h, el) {
                return false;
            }
            let ok = list_has_type(t, el);
            proof {
                if ok {
                    spine_cons(dr(h), dr(t));
                    assert forall|k: int| 0 <= k < spine(**v).len() implies val_type(#[trigger] spine(**v)[k], *el) by {
                        if k > 0 {
                            assert(spine(**v)[k] == spine(**t)[k - 1]);
                        }
                    }
                }
            }
            ok
        },
        _ => true,
    }
}

} // verus!
