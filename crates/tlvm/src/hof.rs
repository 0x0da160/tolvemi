//! v1.5 の関数を渡す組み込み `map`・`filter`・`any`・`all`・`find`・`sort_by`（差分仕様 §1、§2）と、
//! v1.6 の上限つき反復 `loop`（v1.6 差分仕様 §1、§2）。
//!
//! 型検査器は `ExprKind::Hof` を直接検査し、要素の型と本体の型を node index ごとに `HofTypes` に残す。
//! `lower` はその型を使い、検証済み部品へ渡すソース用に `fold`・`reverse`・`cons`・`if`・`match_option`・`let`
//! の組み合わせへ書き換える。
//!
//! ```text
//! map(xs, |x| e)     => reverse(fold(xs, list<B>(), |acc, x| cons(e, acc)))
//! filter(xs, |x| p)  => reverse(fold(xs, list<A>(), |acc, x| if(p, cons(x, acc), acc)))
//! any(xs, |x| p)     => fold(xs, false, |acc, x| if(acc, true, p))
//! all(xs, |x| p)     => fold(xs, true, |acc, x| if(acc, p, false))
//! find(xs, |x| p)    => fold(xs, none<A>(), |acc, x| match_option(acc, if(p, some(x), none<A>()), |y| some(y)))
//! sort_by(xs, |x| k) => fold(xs, list<A>(), |acc, e|
//!                         let r = fold(cons(e, acc), pair(none<Int>(), pair(list<A>(), false)), |st, y|
//!                           if(snd(snd(st)), pair(fst(st), pair(cons(y, fst(snd(st))), true)),
//!                             let ky = (let x = y in k) in
//!                             match_option(fst(st), pair(some(ky), snd(st)), |ke|
//!                               if(lt(ke, ky), pair(fst(st), pair(cons(y, cons(e, fst(snd(st)))), true)),
//!                                 pair(fst(st), pair(cons(y, fst(snd(st))), false)))))) in
//!                         reverse(if(snd(snd(r)), fst(snd(r)), cons(e, fst(snd(r))))))
//! loop(init, max, |s| e)
//!   => match_result(
//!        fold(range(0, max), ok<S, S>(init), |acc, i|
//!          match_result(acc, |s| match_option(e, err<S, S>(s), |s2| ok<S, S>(s2)), |d| err<S, S>(d))),
//!        |r| none<S>(), |d| some(d))
//! ```
//!
//! `loop` の状態は `Result<S, S>`（ok = 続行中、err = 止まった）。止まった後の歩では本体を評価せず、
//! `max` 回の歩を終えても ok のままなら `none<S>()`。`max <= 0` なら `range(0, max)` が空なので本体を評価しない。
//! s はユーザーの binder（外側の名前をシャドーしないことは名前の検査で確かめてある）。
//!
//! `sort_by` は安定な挿入整列：整列済みの acc を小さい方から見て、鍵が e の鍵より大きい最初の要素の前に e を
//! 入れる（等しい鍵の要素の後ろに入るので、元の順が保たれる）。内側の fold は `cons(e, acc)` を走査し、最初の反復で
//! e の鍵を、以降は比較のたびに要素の鍵を `let x = 要素 in k` で計算し直す（e を入れた後は計算しない）。鍵の本体 k は
//! 書き換え後のソースに一度だけ現れるので、sort_by の鍵の中に sort_by を入れ子にしてもソースは指数的に大きくならない。
//! x はユーザーの binder で、外側に x を束縛するものはないのでシャドーされることはない。
//! acc・e・st・y・r・ke などの導入する名前（`hof1` など）は、プログラム中のどの名前とも重ならない。
//!
//! 書き換えは検証されていない接着部分（`trust-boundary.toml` の `glue`）。検証済み部品は書き換え後の
//! プログラムを検査・実行するので、停止性・型安全性・決定性は書き換え後のプログラムについて成り立つ。

use crate::checker::HofTypes;
use crate::syntax::*;
use std::collections::HashSet;

/// `map` など（v1.6 の `loop` も）を一つでも含むか。
pub fn has_hof(p: &Program) -> bool {
    fn ex(e: &Expr) -> bool {
        matches!(e.kind, ExprKind::Hof { .. } | ExprKind::Loop { .. }) || e.children().into_iter().any(ex)
    }
    p.functions().any(|f| ex(&f.body))
}

/// プログラム中の名前（関数名、引数、変数、束縛、呼び出し先）。
fn collect(e: &Expr, out: &mut HashSet<String>) {
    match &e.kind {
        ExprKind::Var(n) | ExprKind::Let { name: n, .. } | ExprKind::Call { callee: n, .. } => {
            out.insert(n.clone());
        }
        ExprKind::Fold { acc, item, .. } => {
            out.insert(acc.clone());
            out.insert(item.clone());
        }
        ExprKind::Match { binder, .. } | ExprKind::Hof { binder, .. } | ExprKind::Loop { binder, .. } => {
            out.insert(binder.clone());
        }
        ExprKind::MatchResult { ok_binder, err_binder, .. } => {
            out.insert(ok_binder.clone());
            out.insert(err_binder.clone());
        }
        ExprKind::SumMatch { arms, .. } => {
            for a in arms {
                out.extend(a.pat.binds.iter().map(|(b, _)| b.clone()));
            }
        }
        _ => {}
    }
    for c in e.children() {
        collect(c, out);
    }
}

/// 意味論上の型を構文上の型にする（書き換えで書く `list<A>()`、`none<A>()` 用）。
fn type_node(t: &Ty, meta: Meta) -> TypeNode {
    TypeNode::new(t.tag(), t.args().iter().map(|a| type_node(a, meta)).collect(), meta)
}

struct Lower<'a> {
    types: &'a HofTypes,
    taken: HashSet<String>,
    fresh: usize,
}

/// 書き換えで作る式（span と node index は元の `map` などのもの）。
struct B {
    m: Meta,
}

impl B {
    fn ex(&self, kind: ExprKind) -> Expr {
        Expr { kind, meta: self.m }
    }
    fn var(&self, n: &str) -> Expr {
        self.ex(ExprKind::Var(n.to_string()))
    }
    fn call(&self, f: &str, args: Vec<Expr>) -> Expr {
        self.ex(ExprKind::Call { callee: f.into(), args, builtin: true, callee_span: self.m.span })
    }
    fn if_(&self, c: Expr, t: Expr, f: Expr) -> Expr {
        self.ex(ExprKind::If(Box::new(c), Box::new(t), Box::new(f)))
    }
    fn pair(&self, a: Expr, b: Expr) -> Expr {
        self.ex(ExprKind::Pair(Box::new(a), Box::new(b)))
    }
    fn bool(&self, b: bool) -> Expr {
        self.ex(ExprKind::Bool(b))
    }
    fn empty(&self, t: &Ty) -> Expr {
        self.ex(ExprKind::List { element_type: type_node(t, self.m), items: vec![] })
    }
    fn none(&self, t: &Ty) -> Expr {
        self.ex(ExprKind::None(type_node(t, self.m)))
    }
    fn let_(&self, name: &str, value: Expr, body: Expr) -> Expr {
        self.ex(ExprKind::Let { name: name.into(), name_span: self.m.span, value: Box::new(value), body: Box::new(body) })
    }
    fn fold(&self, list: Expr, init: Expr, acc: &str, item: &str, body: Expr) -> Expr {
        self.ex(ExprKind::Fold {
            list: Box::new(list),
            init: Box::new(init),
            acc: acc.into(),
            acc_span: self.m.span,
            item: item.into(),
            item_span: self.m.span,
            body: Box::new(body),
        })
    }
}

impl Lower<'_> {
    fn fresh(&mut self) -> String {
        loop {
            self.fresh += 1;
            let n = format!("hof{}", self.fresh);
            if !self.taken.contains(&n) {
                self.taken.insert(n.clone());
                return n;
            }
        }
    }

    fn expr(&mut self, e: &Expr) -> Expr {
        let mut out = e.clone();
        for c in out.children_mut() {
            *c = self.expr(c);
        }
        // 型が無いのは検査で拒否したプログラムだけ（そのまま残す。検証済み parser は受理しない）
        let Some((a, b)) = self.types.get(&e.meta.index).cloned() else {
            return out;
        };
        let (op, list, binder, body) = match out.kind {
            ExprKind::Hof { op, list, binder, body, .. } => (op, list, binder, body),
            ExprKind::Loop { init, max, binder, body, .. } => return self.loop_(e.meta, *init, *max, binder, *body, &a),
            _ => return out,
        };
        let k = B { m: e.meta };
        let x = binder;
        let (xs, p) = (*list, *body);
        let acc = self.fresh();
        match op {
            HofOp::Map => {
                let step = k.call("cons", vec![p, k.var(&acc)]);
                k.call("reverse", vec![k.fold(xs, k.empty(&b), &acc, &x, step)])
            }
            HofOp::Filter => {
                let step = k.if_(p, k.call("cons", vec![k.var(&x), k.var(&acc)]), k.var(&acc));
                k.call("reverse", vec![k.fold(xs, k.empty(&a), &acc, &x, step)])
            }
            HofOp::Any => {
                let step = k.if_(k.var(&acc), k.bool(true), p);
                k.fold(xs, k.bool(false), &acc, &x, step)
            }
            HofOp::All => {
                let step = k.if_(k.var(&acc), p, k.bool(false));
                k.fold(xs, k.bool(true), &acc, &x, step)
            }
            HofOp::Find => {
                let y = self.fresh();
                let found = k.if_(p, k.ex(ExprKind::Some(Box::new(k.var(&x)))), k.none(&a));
                let keep = k.ex(ExprKind::Some(Box::new(k.var(&y))));
                let step = k.ex(ExprKind::Match {
                    scrutinee: Box::new(k.var(&acc)),
                    on_none: Box::new(found),
                    binder: y,
                    binder_span: e.meta.span,
                    on_some: Box::new(keep),
                });
                k.fold(xs, k.none(&a), &acc, &x, step)
            }
            HofOp::SortBy => {
                let (el, st, y, kv, ke, r) = (self.fresh(), self.fresh(), self.fresh(), self.fresh(), self.fresh(), self.fresh());
                let fst = |e: Expr| k.call("fst", vec![e]);
                let snd = |e: Expr| k.call("snd", vec![e]);
                let cons = |h: Expr, t: Expr| k.call("cons", vec![h, t]);
                // st = pair(e の鍵（最初の反復で決まる）, pair(書き出した列（逆順）, e を入れたか))
                let out = || fst(snd(k.var(&st)));
                let state = |rest: Expr, done: bool| k.pair(fst(k.var(&st)), k.pair(rest, k.bool(done)));
                let copy = state(cons(k.var(&y), out()), true);
                let insert = state(cons(k.var(&y), cons(k.var(&el), out())), true);
                let skip = state(cons(k.var(&y), out()), false);
                let compare = k.if_(k.call("lt", vec![k.var(&ke), k.var(&kv)]), insert, skip);
                let first = k.pair(k.ex(ExprKind::Some(Box::new(k.var(&kv)))), snd(k.var(&st)));
                let on_key = k.ex(ExprKind::Match {
                    scrutinee: Box::new(fst(k.var(&st))),
                    on_none: Box::new(first),
                    binder: ke,
                    binder_span: e.meta.span,
                    on_some: Box::new(compare),
                });
                // 要素 y の鍵：let x = y in k（x はユーザーの binder。鍵の本体はソース上に一度だけ現れる）
                let key = k.let_(&x, k.var(&y), p);
                let inner = k.if_(snd(snd(k.var(&st))), copy, k.let_(&kv, key, on_key));
                let init = k.pair(k.none(&Ty::int()), k.pair(k.empty(&a), k.bool(false)));
                let scan = k.fold(cons(k.var(&el), k.var(&acc)), init, &st, &y, inner);
                let rest = snd(k.var(&r));
                let done = k.call("reverse", vec![k.if_(snd(rest.clone()), fst(rest.clone()), cons(k.var(&el), fst(rest)))]);
                k.fold(xs, k.empty(&a), &acc, &el, k.let_(&r, scan, done))
            }
        }
    }
}

impl Lower<'_> {
    /// v1.6：`loop(init, max, |s| e)`（`st` は状態の型 S）。
    fn loop_(&mut self, m: Meta, init: Expr, max: Expr, s: String, body: Expr, st: &Ty) -> Expr {
        let k = B { m };
        let (acc, i, s2, d, r) = (self.fresh(), self.fresh(), self.fresh(), self.fresh(), self.fresh());
        let rt = type_node(&Ty::result(st.clone(), st.clone()), m);
        let inj = |ok: bool, v: Expr| k.ex(ExprKind::Inj { ok, ty: rt.clone(), value: Box::new(v) });
        let match_result = |scrutinee: Expr, okb: &str, on_ok: Expr, errb: &str, on_err: Expr| {
            k.ex(ExprKind::MatchResult {
                scrutinee: Box::new(scrutinee),
                ok_binder: okb.into(),
                ok_span: m.span,
                on_ok: Box::new(on_ok),
                err_binder: errb.into(),
                err_span: m.span,
                on_err: Box::new(on_err),
            })
        };
        // 1 歩：本体が some(s2) なら続け、none なら今の状態で止まる
        let step = k.ex(ExprKind::Match {
            scrutinee: Box::new(body),
            on_none: Box::new(inj(false, k.var(&s))),
            binder: s2.clone(),
            binder_span: m.span,
            on_some: Box::new(inj(true, k.var(&s2))),
        });
        let fold_body = match_result(k.var(&acc), &s, step, &d, inj(false, k.var(&d)));
        let steps = k.call("range", vec![k.ex(ExprKind::Int(0.into())), max]);
        let run = k.fold(steps, inj(true, init), &acc, &i, fold_body);
        match_result(run, &r, k.none(st), &d, k.ex(ExprKind::Some(Box::new(k.var(&d)))))
    }
}

/// `map` などを fold などに書き換える（検証済み部品へ渡すソース用）。`types` は型検査の結果
/// （`CheckOutcome::hof`）。型の無い node（拒否したプログラム）はそのまま残す。
pub fn lower(p: &Program, types: &HofTypes) -> Program {
    let mut taken = HashSet::new();
    for f in p.functions() {
        taken.insert(f.name.clone());
        taken.extend(f.params.iter().map(|q| q.name.clone()));
        collect(&f.body, &mut taken);
    }
    let mut l = Lower { types, taken, fresh: 0 };
    let declarations = p
        .declarations
        .iter()
        .map(|d| match d {
            Decl::Fn(f) => Decl::Fn(FnDecl { body: l.expr(&f.body), ..f.clone() }),
            d => d.clone(),
        })
        .collect();
    Program { declarations, meta: p.meta }
}
