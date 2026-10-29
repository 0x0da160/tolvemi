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
//!   => let s0 = pair(0, ok<S, S>(init)) in let m = max in
//!      let rg = range(0, 16) in let one = range(0, 1) in let nil = list<Int>() in
//!      let r = fold(if(lt(16^15, m), rg, one), s0, |a1, i1|                   -- 段 1（1 要素 = 16^15 歩）
//!          fold(if(lt(fst(a1), m), if(lt(16^14, sub(m, fst(a1))), rg, one), nil), a1, |a2, i2|
//!            ...                                                            -- 段 2〜15（1 要素 = 16^(16-j) 歩）
//!              let n = min(16, sub(m, fst(a15))) in                         -- 段 16：n 歩
//!              let res = fold(range(0, n), snd(a15), |acc, i|
//!                match_result(acc, |s| match_option(e, err<S, S>(s), |s2| ok<S, S>(s2)), |d| err<S, S>(d))) in
//!              pair(match_result(res, |x| add(fst(a15), n), |x| m), res)
//!            ...) in
//!      match_result(snd(r), |v| none<S>(), |d| some(d))
//! ```
//!
//! 評価の順は左から右：init（`s0` の初期状態の中）を max（`m`）より先に評価する。両方が資源の上限で失敗するなら、
//! 報告されるのは init のエラー。
//!
//! 書換え後の式の深さ：段 1 の fold の上には束縛が 6 個（s0・m・rg・one・nil・r）あり、評価の順を変える前の形
//! （`let m = max` を一番外側に置いた m・rg・one・nil の束縛 4 個と match_result・snd）と同じく深さ 6 に段 1 が来る。
//! そのため loop の本体の深さは前と同じ（loop 1 段あたり 26）。max は s0 の束縛の内側に入るので前より 1 段深い
//! （init を先に評価するには、init を含む束縛を max の束縛の外に置くので、この 1 段は避けられない）。init は段 1 の
//! 初期状態の中（深さ 9）から一番外側の束縛の中（深さ 3）に移って 6 段浅い。
//!
//! `loop` の状態は `pair(c, Result<S, S>)`。c は本体を評価した回数（止まったときは m にする）、ok = 続行中、
//! err = 止まった。一番内側の段は v1.6 当初の書き換えと同じ fold を高々 16 歩ずつ進める（止まった後の歩では本体を
//! 評価しない）。外側の 15 段は、残りの歩 `m - c` がその段の 1 要素の受け持ち（16^(16-j)）より多ければ 16 要素の
//! `rg`、そうでなければ 1 要素の `one` を辿り、`c >= m`（止まったか m 回評価した）になった後は空のリスト `nil` を辿る。
//! 本体の評価はちょうど `min(m, 止まるまでの回数)` 回で、手間はそれに比例する歩と、止まった後に各段で残る高々 15 要素
//! （m が 16^k 以下なら高々 k 段）の比較で済む（以前の `fold(range(0, max), ...)` は max に比例した）。
//! 受け持てる歩は 16^16 = 2^64 回までで、それより大きい max でも 2^64 回で打ち切るが、どの実行上限（step 数）も
//! 2^64 より小さいので観測できない。`max <= 0` なら段 2 から空のリストを辿るので本体を評価しない。
//! s はユーザーの binder（外側の名前をシャドーしないことは名前の検査で確かめてある）。本体はソースに一度だけ現れる。
//!
//! `sort_by` は安定な挿入整列：整列済みの acc を小さい方から見て、鍵が e の鍵より大きい最初の要素の前に e を
//! 入れる（等しい鍵の要素の後ろに入るので、元の順が保たれる）。内側の fold は `cons(e, acc)` を走査し、最初の反復で
//! e の鍵を、以降は比較のたびに要素の鍵を `let x = 要素 in k` で計算し直す（e を入れた後は計算しない）。鍵の本体 k は
//! 書き換え後のソースに一度だけ現れるので、sort_by の鍵の中に sort_by を入れ子にしてもソースは指数的に大きくならない。
//! x はユーザーの binder で、外側に x を束縛するものはないのでシャドーされることはない。
//! acc・e・st・y・r・ke などの導入する名前（`hof1` など）は、プログラム中のどの名前とも重ならない。
//!
//! v1.9 の辞書の操作（`dict_get` など）と空の辞書 `dict<K, V>()` も同じ走査で書き換える（形は `dict` モジュール）。
//!
//! 書き換えは検証されていない接着部分（`trust-boundary.toml` の `glue`）。検証済み部品は書き換え後の
//! プログラムを検査・実行するので、停止性・型安全性・決定性は書き換え後のプログラムについて成り立つ。

use crate::checker::HofTypes;
use crate::syntax::*;
use std::collections::HashSet;

/// `map` など（v1.6 の `loop` も）を一つでも含むか。
pub fn has_hof(p: &Program) -> bool {
    fn ex(e: &Expr) -> bool {
        matches!(e.kind, ExprKind::Hof { .. } | ExprKind::Loop { .. })
            || e.children().into_iter().any(ex)
    }
    p.functions().any(|f| ex(&f.body))
}

/// `loop` を一つでも含むか（検証済みの hof の経路は loop を含まない。`has_hof` は loop も数える）。
pub fn has_loop(p: &Program) -> bool {
    fn ex(e: &Expr) -> bool {
        matches!(e.kind, ExprKind::Loop { .. }) || e.children().into_iter().any(ex)
    }
    p.functions().any(|f| ex(&f.body))
}

/// 入れ子の loop の最も深い連鎖の段数と、その連鎖で一番外側の loop の span（loop を含まないプログラムは None）。
/// 書き換えの前の構文木で数える（式の深さの上限を超えた診断の位置に使う）。
pub fn deepest_loop_nest(p: &Program) -> Option<(usize, crate::diagnostics::Span)> {
    fn walk(e: &Expr) -> (usize, Option<crate::diagnostics::Span>) {
        let (mut d, mut s) = (0, None);
        for c in e.children() {
            let (cd, cs) = walk(c);
            if cd > d {
                d = cd;
                s = cs;
            }
        }
        if matches!(e.kind, ExprKind::Loop { .. }) {
            (d + 1, Some(e.meta.span()))
        } else {
            (d, s)
        }
    }
    p.functions()
        .map(|f| walk(&f.body))
        .filter_map(|(d, s)| s.map(|s| (d, s)))
        .max_by_key(|(d, _)| *d)
}

/// プログラム中の名前（関数名、引数、変数、束縛、呼び出し先）。
pub(crate) fn collect(e: &Expr, out: &mut HashSet<String>) {
    match &e.kind {
        ExprKind::Var(n) | ExprKind::Let { name: n, .. } | ExprKind::Call { callee: n, .. } => {
            out.insert(n.clone());
        }
        ExprKind::Fold { acc, item, .. } => {
            out.insert(acc.clone());
            out.insert(item.clone());
        }
        ExprKind::Match { binder, .. }
        | ExprKind::Hof { binder, .. }
        | ExprKind::Loop { binder, .. } => {
            out.insert(binder.clone());
        }
        ExprKind::MatchResult {
            ok_binder,
            err_binder,
            ..
        } => {
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
pub(crate) fn type_node(t: &Ty, meta: Meta) -> TypeNode {
    TypeNode::new(
        t.tag(),
        t.args().iter().map(|a| type_node(a, meta)).collect(),
        meta,
    )
}

pub(crate) struct Lower<'a> {
    types: &'a HofTypes,
    taken: HashSet<String>,
    fresh: usize,
}

/// 書き換えで作る式（span と node index は元の `map` などのもの）。
pub(crate) struct B {
    pub(crate) m: Meta,
}

impl B {
    pub(crate) fn ex(&self, kind: ExprKind) -> Expr {
        Expr { kind, meta: self.m }
    }
    pub(crate) fn var(&self, n: &str) -> Expr {
        self.ex(ExprKind::Var(n.to_string()))
    }
    pub(crate) fn call(&self, f: &str, args: Vec<Expr>) -> Expr {
        self.ex(ExprKind::Call {
            callee: f.into(),
            args,
            builtin: true,
            callee_span: self.m.span,
            type_args: vec![],
        })
    }
    pub(crate) fn if_(&self, c: Expr, t: Expr, f: Expr) -> Expr {
        self.ex(ExprKind::If(Box::new(c), Box::new(t), Box::new(f)))
    }
    pub(crate) fn pair(&self, a: Expr, b: Expr) -> Expr {
        self.ex(ExprKind::Pair(Box::new(a), Box::new(b)))
    }
    pub(crate) fn bool(&self, b: bool) -> Expr {
        self.ex(ExprKind::Bool(b))
    }
    pub(crate) fn empty(&self, t: &Ty) -> Expr {
        self.ex(ExprKind::List {
            element_type: type_node(t, self.m),
            items: vec![],
        })
    }
    pub(crate) fn none(&self, t: &Ty) -> Expr {
        self.ex(ExprKind::None(type_node(t, self.m)))
    }
    pub(crate) fn let_(&self, name: &str, value: Expr, body: Expr) -> Expr {
        self.ex(ExprKind::Let {
            name: name.into(),
            name_span: self.m.span,
            value: Box::new(value),
            body: Box::new(body),
        })
    }
    pub(crate) fn fold(&self, list: Expr, init: Expr, acc: &str, item: &str, body: Expr) -> Expr {
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

impl<'a> Lower<'a> {
    pub(crate) fn new(types: &'a HofTypes, taken: HashSet<String>) -> Lower<'a> {
        Lower {
            types,
            taken,
            fresh: 0,
        }
    }

    pub(crate) fn fresh(&mut self) -> String {
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
        // v1.9：空の辞書（型は node に書いてある）
        if let ExprKind::DictNew(t) = &out.kind {
            return crate::dict::lower_new(t, e.meta);
        }
        // 型が無いのは検査で拒否したプログラムだけ（そのまま残す。検証済み parser は受理しない）
        let Some((a, b)) = self.types.get(&e.meta.index).cloned() else {
            return out;
        };
        let (op, list, binder, body) = match out.kind {
            // v1.9：辞書の操作（a、b は鍵と値の型）
            ExprKind::Call {
                callee,
                args,
                builtin: true,
                ..
            } if DICT_OPS.contains(&callee.as_str()) => {
                return self.dict_op(e.meta, &callee, args, &a, &b);
            }
            ExprKind::Hof {
                op,
                list,
                binder,
                body,
                ..
            } => (op, list, binder, body),
            ExprKind::Loop {
                init,
                max,
                binder,
                body,
                ..
            } => return self.loop_(e.meta, *init, *max, binder, *body, &a),
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
                let (el, st, y, kv, ke, r) = (
                    self.fresh(),
                    self.fresh(),
                    self.fresh(),
                    self.fresh(),
                    self.fresh(),
                    self.fresh(),
                );
                let fst = |e: Expr| k.call("fst", vec![e]);
                let snd = |e: Expr| k.call("snd", vec![e]);
                let cons = |h: Expr, t: Expr| k.call("cons", vec![h, t]);
                // st = pair(e の鍵（最初の反復で決まる）, pair(書き出した列（逆順）, e を入れたか))
                let out = || fst(snd(k.var(&st)));
                let state =
                    |rest: Expr, done: bool| k.pair(fst(k.var(&st)), k.pair(rest, k.bool(done)));
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
                let done = k.call(
                    "reverse",
                    vec![k.if_(
                        snd(rest.clone()),
                        fst(rest.clone()),
                        cons(k.var(&el), fst(rest)),
                    )],
                );
                k.fold(xs, k.empty(&a), &acc, &el, k.let_(&r, scan, done))
            }
        }
    }
}

/// v1.6：`loop` の書き換えで入れ子にする fold の段数と、各段の 1 要素が受け持つ歩の数の比。
/// 本体を評価できる回数の上限は LOOP_BASE^LOOP_LEVELS = 16^16 = 2^64 で、どの実行上限（step 数）よりも大きい。
pub const LOOP_BASE: u64 = 16;
pub const LOOP_LEVELS: u32 = 16;

impl Lower<'_> {
    /// v1.6：`loop(init, max, |s| e)`（`st` は状態の型 S）。検証済みの exec 版（dictloop_verified）で写せるならそれを
    /// 使い、写せなければ `loop_rust`。段の構成はモジュールの説明を参照。
    fn loop_(&mut self, m: Meta, init: Expr, max: Expr, s: String, body: Expr, st: &Ty) -> Expr {
        if let Some(e) = crate::dictloop_verified::loop_(self, m, &init, &max, &s, &body, st) {
            return e;
        }
        self.loop_rust(m, init, max, s, body, st)
    }

    /// 従来の書換え（`loop_` が検証済みの版で写せないとき）。同じ段の構成を作る。
    pub(crate) fn loop_rust(
        &mut self,
        m: Meta,
        init: Expr,
        max: Expr,
        s: String,
        body: Expr,
        st: &Ty,
    ) -> Expr {
        let k = B { m };
        let int = |n: u64| k.ex(ExprKind::Int(n.into()));
        let (mx, rg, one) = (self.fresh(), self.fresh(), self.fresh());
        let rt = type_node(&Ty::result(st.clone(), st.clone()), m);
        let inj = |ok: bool, v: Expr| {
            k.ex(ExprKind::Inj {
                ok,
                ty: rt.clone(),
                value: Box::new(v),
            })
        };
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
        let fst = |e: Expr| k.call("fst", vec![e]);
        let snd = |e: Expr| k.call("snd", vec![e]);
        // 外側の段（LOOP_LEVELS - 1 段）の acc と item（外側から順）
        let outer: Vec<(String, String)> = (1..LOOP_LEVELS)
            .map(|_| (self.fresh(), self.fresh()))
            .collect();
        let (a, _) = &outer[outer.len() - 1];
        // 一番内側の段：n = min(LOOP_BASE, max - c) 歩を v1.6 当初の形の fold で進める（c >= max なら n <= 0 で何もしない）
        let (n, acc, i, s2, d, res, x, s0) = (
            self.fresh(),
            self.fresh(),
            self.fresh(),
            self.fresh(),
            self.fresh(),
            self.fresh(),
            self.fresh(),
            self.fresh(),
        );
        // 空のリスト list<Int>()（c >= max になった後に段 2〜15 が辿る）を束縛する名前
        let nil = self.fresh();
        let step = k.ex(ExprKind::Match {
            scrutinee: Box::new(body),
            on_none: Box::new(inj(false, k.var(&s))),
            binder: s2.clone(),
            binder_span: m.span,
            on_some: Box::new(inj(true, k.var(&s2))),
        });
        let chunk = k.fold(
            k.call("range", vec![int(0), k.var(&n)]),
            snd(k.var(a)),
            &acc,
            &i,
            match_result(k.var(&acc), &s, step, &d, inj(false, k.var(&d))),
        );
        // 止まったら c = max（それ以降、外側の段は残りの歩ごとに比較 1 回と空の fold で終わる）
        let counted = k.pair(
            match_result(
                k.var(&res),
                &x,
                k.call("add", vec![fst(k.var(a)), k.var(&n)]),
                &x,
                k.var(&mx),
            ),
            k.var(&res),
        );
        let remaining = |a: &str| k.call("sub", vec![k.var(&mx), fst(k.var(a))]);
        let mut inner = k.let_(
            &n,
            k.call("min", vec![int(LOOP_BASE), remaining(a)]),
            k.let_(&res, chunk, counted),
        );
        for j in (0..outer.len()).rev() {
            let (a, i) = &outer[j];
            // この段の 1 要素は LOOP_BASE^(LOOP_LEVELS - 1 - j) 歩を受け持つ。残りがそれより多ければ LOOP_BASE 要素、
            // そうでなければ 1 要素を辿る。外側の段の状態で c >= max なら（止まったか max 回評価した）空のリストを辿る
            let width = int(LOOP_BASE.pow(LOOP_LEVELS - 1 - j as u32));
            inner = if j == 0 {
                let list = k.if_(
                    k.call("lt", vec![width, k.var(&mx)]),
                    k.var(&rg),
                    k.var(&one),
                );
                k.fold(list, k.var(&s0), a, i, inner)
            } else {
                let prev = &outer[j - 1].0;
                let list = k.if_(
                    k.call("lt", vec![width, remaining(prev)]),
                    k.var(&rg),
                    k.var(&one),
                );
                let guarded = k.if_(
                    k.call("lt", vec![fst(k.var(prev)), k.var(&mx)]),
                    list,
                    k.var(&nil),
                );
                k.fold(guarded, k.var(prev), a, i, inner)
            };
        }
        let (fr, r) = (self.fresh(), self.fresh());
        let result = k.let_(
            &fr,
            inner,
            match_result(
                snd(k.var(&fr)),
                &r,
                k.none(st),
                &d,
                k.ex(ExprKind::Some(Box::new(k.var(&d)))),
            ),
        );
        let full = k.call("range", vec![int(0), int(LOOP_BASE)]);
        let single = k.call("range", vec![int(0), int(1)]);
        let empty = k.empty(&Ty::int());
        // 段 1 の初期状態 pair(0, ok(init)) を一番外側で束縛するので、init は max より先に評価する。段 1 の fold の上は
        // 束縛 6 個（s0、m、rg、one、nil、段の結果 fr）で、評価の順を変える前（束縛 4 個と match_result、snd）と同じ
        // 深さ 6 になり、loop の本体の書換え後の深さは変わらない。
        k.let_(
            &s0,
            k.pair(int(0), inj(true, init)),
            k.let_(
                &mx,
                max,
                k.let_(&rg, full, k.let_(&one, single, k.let_(&nil, empty, result))),
            ),
        )
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
    let mut l = Lower::new(types, taken);
    let declarations = p
        .declarations
        .iter()
        .map(|d| match d {
            Decl::Fn(f) => Decl::Fn(FnDecl {
                body: l.expr(&f.body),
                ..f.clone()
            }),
            d => d.clone(),
        })
        .collect();
    Program {
        declarations,
        meta: p.meta,
        imports: p.imports.clone(),
    }
}
