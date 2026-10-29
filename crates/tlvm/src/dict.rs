//! v1.9 の辞書 `Dict<K, V>`（差分仕様 §1、§2）。
//!
//! 型検査器は `Dict<K, V>` を `List<Pair<K, V>>` とは別の型として検査し、操作（`dict_get` などの呼び出し）ごとに
//! 鍵と値の型を node index ごとに `HofTypes` に残す。`hof::lower` がその型を使って操作を `fold` などへ書き換え
//! （`lower_op`）、最後に `erase` が型の `Dict<K, V>` を `List<Pair<K, V>>` にする。書き換え後の辞書は、挿入順に並び
//! 鍵が相異なる `(鍵, 値)` の列である（Python の dict と同じ順序）。鍵は `eq` と同じ構造的等価性で比べる。
//!
//! ```text
//! dict<K, V>()          => list<Pair<K, V>>()
//! dict_size(d)          => length(d)
//! dict_entries(d)       => d
//! dict_keys(d)          => reverse(fold(d, list<K>(), |acc, e| cons(fst(e), acc)))
//! dict_values(d)        => reverse(fold(d, list<V>(), |acc, e| cons(snd(e), acc)))
//! dict_get(d, k)        => let dd = d in let kk = k in
//!                          fold(dd, none<V>(), |acc, e| if(eq(fst(e), kk), some(snd(e)), acc))
//! dict_has(d, k)        => let dd = d in let kk = k in fold(dd, false, |acc, e| if(acc, true, eq(fst(e), kk)))
//! dict_remove(d, k)     => let dd = d in let kk = k in
//!                          reverse(fold(dd, list<Pair<K, V>>(), |acc, e| if(eq(fst(e), kk), acc, cons(e, acc))))
//! dict_put(d, k, v)     => let dd = d in let kk = k in let vv = v in PUT(dd, kk, vv)
//! dict_from(xs)         => fold(xs, list<Pair<K, V>>(), |acc, p| let kk = fst(p) in let vv = snd(p) in PUT(acc, kk, vv))
//!
//! PUT(d, kk, vv)        => let r = fold(d, pair(list<Pair<K, V>>(), false), |acc, e|
//!                            if(eq(fst(e), kk), pair(cons(pair(kk, vv), fst(acc)), true), pair(cons(e, fst(acc)), snd(acc)))) in
//!                          reverse(if(snd(r), fst(r), cons(pair(kk, vv), fst(r))))
//! ```
//!
//! 鍵が既にあれば値をその位置で置き換え、なければ末尾に足す。引数は左から順に一度だけ評価する（`let`）。
//! どの操作も辞書の大きさ n に対して O(n) の歩（`dict_from` は O(n²)）。dd・kk・acc・e などの導入する名前は
//! `hof1` などの、プログラム中のどの名前とも重ならないもの（`hof::lower` と同じ列）。
//!
//! 書き換えは検証されていない接着部分（`trust-boundary.toml` の `glue`）。検証済み部品は書き換え後の
//! プログラムを検査・実行するので、停止性・型安全性・決定性は書き換え後のプログラムについて成り立つ。
//! 鍵が相異なることは書き換えの性質（各操作が保つ）と、入力の復号での検査（`values`・`plain`）で保つ。

use crate::hof::{Lower, B};
use crate::syntax::*;

/// 辞書（型、空の辞書、操作）を一つでも含むか。
pub fn has_dict(p: &Program) -> bool {
    fn ty(t: &TypeNode) -> bool {
        t.tag == TyTag::Dict || t.args.iter().any(ty)
    }
    fn ex(e: &Expr) -> bool {
        match &e.kind {
            ExprKind::DictNew(_) => true,
            ExprKind::Call {
                callee,
                builtin: true,
                ..
            } if DICT_OPS.contains(&callee.as_str()) => true,
            ExprKind::List {
                element_type: t, ..
            }
            | ExprKind::None(t)
            | ExprKind::Inj { ty: t, .. }
                if ty(t) =>
            {
                true
            }
            _ => e.children().into_iter().any(ex),
        }
    }
    p.declarations.iter().any(|d| match d {
        Decl::Fn(f) => f.params.iter().any(|q| ty(&q.ty)) || ty(&f.return_type) || ex(&f.body),
        Decl::Type(t) => t.fields.iter().any(|f| ty(&f.ty)),
        Decl::Sum(s) => s.variants.iter().any(|v| v.fields.iter().any(ty)),
        Decl::Entry(_) => false,
    })
}

/// 空の辞書 `dict<K, V>()`（`t` は `Dict<K, V>` の型 node）を空のリストにする。
pub(crate) fn lower_new(t: &TypeNode, m: Meta) -> Expr {
    let entry = TypeNode::new(TyTag::Pair, t.args.clone(), t.meta);
    Expr {
        kind: ExprKind::List {
            element_type: entry,
            items: vec![],
        },
        meta: m,
    }
}

impl Lower<'_> {
    /// 辞書の操作 `op(args)`（引数は書き換え済み。k、v は鍵と値の型）。検証済みの exec 版（dictloop_verified）で
    /// 写せるならそれを使い、写せなければ `dict_op_rust`。形はモジュールの説明を参照。
    pub(crate) fn dict_op(&mut self, m: Meta, op: &str, args: Vec<Expr>, k: &Ty, v: &Ty) -> Expr {
        if let Some(e) = crate::dictloop_verified::dict_op(self, m, op, &args, k, v) {
            return e;
        }
        self.dict_op_rust(m, op, args, k, v)
    }

    /// 従来の書換え（`dict_op` が検証済みの版で写せないとき）。同じ形を作る。
    pub(crate) fn dict_op_rust(
        &mut self,
        m: Meta,
        op: &str,
        args: Vec<Expr>,
        k: &Ty,
        v: &Ty,
    ) -> Expr {
        let b = B { m };
        let entry = Ty::pair(k.clone(), v.clone());
        let mut args = args.into_iter();
        let mut arg = || args.next().expect("arity checked");
        match op {
            "dict_size" => b.call("length", vec![arg()]),
            "dict_entries" => arg(),
            "dict_keys" | "dict_values" => {
                let (acc, e) = (self.fresh(), self.fresh());
                let (proj, t) = if op == "dict_keys" {
                    ("fst", k)
                } else {
                    ("snd", v)
                };
                let step = b.call("cons", vec![b.call(proj, vec![b.var(&e)]), b.var(&acc)]);
                b.call("reverse", vec![b.fold(arg(), b.empty(t), &acc, &e, step)])
            }
            "dict_from" => {
                let (acc, p, kk, vv) = (self.fresh(), self.fresh(), self.fresh(), self.fresh());
                let put = self.put(&b, b.var(&acc), &kk, &vv, &entry);
                let step = b.let_(
                    &kk,
                    b.call("fst", vec![b.var(&p)]),
                    b.let_(&vv, b.call("snd", vec![b.var(&p)]), put),
                );
                b.fold(arg(), b.empty(&entry), &acc, &p, step)
            }
            _ => {
                // dict_get・dict_has・dict_remove・dict_put：辞書と鍵（dict_put は値も）を順に一度だけ評価する
                let (dd, kk) = (self.fresh(), self.fresh());
                let (d, key) = (arg(), arg());
                let same = |e: &str| b.call("eq", vec![b.call("fst", vec![b.var(e)]), b.var(&kk)]);
                let body = match op {
                    "dict_get" => {
                        let (acc, e) = (self.fresh(), self.fresh());
                        let found = b.ex(ExprKind::Some(Box::new(b.call("snd", vec![b.var(&e)]))));
                        let step = b.if_(same(&e), found, b.var(&acc));
                        b.fold(b.var(&dd), b.none(v), &acc, &e, step)
                    }
                    "dict_has" => {
                        let (acc, e) = (self.fresh(), self.fresh());
                        let step = b.if_(b.var(&acc), b.bool(true), same(&e));
                        b.fold(b.var(&dd), b.bool(false), &acc, &e, step)
                    }
                    "dict_remove" => {
                        let (acc, e) = (self.fresh(), self.fresh());
                        let step = b.if_(
                            same(&e),
                            b.var(&acc),
                            b.call("cons", vec![b.var(&e), b.var(&acc)]),
                        );
                        b.call(
                            "reverse",
                            vec![b.fold(b.var(&dd), b.empty(&entry), &acc, &e, step)],
                        )
                    }
                    _ => {
                        let vv = self.fresh();
                        let value = arg();
                        let put = self.put(&b, b.var(&dd), &kk, &vv, &entry);
                        return b.let_(&dd, d, b.let_(&kk, key, b.let_(&vv, value, put)));
                    }
                };
                b.let_(&dd, d, b.let_(&kk, key, body))
            }
        }
    }

    /// PUT(d, kk, vv)：鍵 kk があればその位置の値を vv にし、なければ末尾に (kk, vv) を足す。
    fn put(&mut self, b: &B, d: Expr, kk: &str, vv: &str, entry: &Ty) -> Expr {
        let (r, acc, e) = (self.fresh(), self.fresh(), self.fresh());
        let fst = |x: Expr| b.call("fst", vec![x]);
        let snd = |x: Expr| b.call("snd", vec![x]);
        let cons = |h: Expr, t: Expr| b.call("cons", vec![h, t]);
        let new = || b.pair(b.var(kk), b.var(vv));
        let same = b.call("eq", vec![fst(b.var(&e)), b.var(kk)]);
        let replaced = b.pair(cons(new(), fst(b.var(&acc))), b.bool(true));
        let kept = b.pair(cons(b.var(&e), fst(b.var(&acc))), snd(b.var(&acc)));
        let scan = b.fold(
            d,
            b.pair(b.empty(entry), b.bool(false)),
            &acc,
            &e,
            b.if_(same, replaced, kept),
        );
        let done = b.call(
            "reverse",
            vec![b.if_(snd(b.var(&r)), fst(b.var(&r)), cons(new(), fst(b.var(&r))))],
        );
        b.let_(&r, scan, done)
    }
}

/// 型の `Dict<K, V>` を `List<Pair<K, V>>` にする（その場で。`Dict` を含まない型は変えない）。
fn erase_ty(t: &mut TypeNode) {
    for a in &mut t.args {
        erase_ty(a);
    }
    if t.tag == TyTag::Dict {
        let entry = TypeNode::new(TyTag::Pair, std::mem::take(&mut t.args), t.meta);
        *t = TypeNode::new(TyTag::List, vec![entry], t.meta);
    }
}

fn erase_expr(e: &mut Expr) {
    for c in e.children_mut() {
        erase_expr(c);
    }
    let m = e.meta;
    match &mut e.kind {
        ExprKind::List {
            element_type: t, ..
        }
        | ExprKind::None(t)
        | ExprKind::Inj { ty: t, .. } => erase_ty(t),
        // 型検査で拒否したプログラムにだけ残る（書き換えは型の付いた node だけ）
        ExprKind::DictNew(t) => {
            let mut t = t.clone();
            erase_ty(&mut t);
            *e = lower_new(&t, m);
        }
        ExprKind::Field {
            target: Some((t, _, _)),
            ..
        } => erase_ty(t),
        ExprKind::SumMatch {
            kind: Some(MatchKind::Sum { ty, fields }),
            ..
        } => {
            erase_ty(ty);
            fields.iter_mut().flatten().for_each(erase_ty);
        }
        _ => {}
    }
}

/// v1.9：プログラム中の型の `Dict<K, V>` をすべて `List<Pair<K, V>>` にする（`hof::lower` の後、検証済み部品へ渡す
/// ソース用）。残っている `dict<K, V>()` も空のリストにする。その場で書き換える（`erase` の複製なしの版）。
pub fn erase_in_place(p: &mut Program) {
    for d in &mut p.declarations {
        match d {
            Decl::Fn(f) => {
                f.params.iter_mut().for_each(|q| erase_ty(&mut q.ty));
                erase_ty(&mut f.return_type);
                erase_expr(&mut f.body);
            }
            Decl::Type(t) => t.fields.iter_mut().for_each(|f| erase_ty(&mut f.ty)),
            Decl::Sum(s) => s
                .variants
                .iter_mut()
                .for_each(|v| v.fields.iter_mut().for_each(erase_ty)),
            Decl::Entry(_) => {}
        }
    }
}

/// v1.9：`erase_in_place` と同じ（複製したプログラムを返す）。
pub fn erase(p: &Program) -> Program {
    let mut out = p.clone();
    erase_in_place(&mut out);
    out
}
