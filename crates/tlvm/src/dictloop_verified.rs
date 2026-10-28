//! v1.6 の `loop` と v1.9 の辞書の操作の書換えを、検証済みの exec 版で行う（DECISION-43、段階 1b）。
//!
//! 検証済みの版（`tlvm_verified::loopex::loop_rw_x`、`tlvm_verified::dictex::dict_rw_x`）は被演算子を式として受け取る。
//! ここでは被演算子を仮の変数で渡す（init・mx・body は 0・1・2、loop の束縛 s は 3。辞書の操作の被演算子は 0・1・2）。
//! 書換えの結果の仮の変数は、書換え済みの被演算子の式（Rust の式のまま。節点の位置とメタも保つ）で置き換える。
//! 導入する名前は、検証済みの版が取る番号 b+1+k を、`Lower::fresh` の k 番目の名前にする。`fresh` の呼出しの順は
//! 従来の書換え（`Lower::loop_rust`、`Lower::dict_op_rust`）と同じなので、出力も従来の書換えと同じになる（テストで確かめる）。
//!
//! 被演算子は書き換えず、型は `verified_ty` で写して `erase_x` で消去する。写せないもの（型が検証済みの型に無い、
//! 被演算子の数が合わない、名前の桁あふれ）は None を返し、呼出し側は従来の書換えを使う。
//!
//! 信頼の境界：この接着（仮の変数、名前の対応、置き換え、型の写し）は検証していない（trust-boundary.toml の
//! `rewrite-shape` の (3)）。検証しているのは dict_rw・loop_rw と exec 版の一致（dictex.rs・loopex.rs）だけ。

use crate::hof::Lower;
use crate::hof_verified::{builtin_name, node_of};
use crate::syntax::*;
use crate::values::verified_ty;
use tlvm_verified::dictex::dict_rw_x;
use tlvm_verified::hof_types::DictOp;
use tlvm_verified::hofex::{erase_x, top_e};
use tlvm_verified::ir::EExpr;
use tlvm_verified::loopex::loop_rw_x;
use tlvm_verified::spec::Ty as VTy;

/// 被演算子の仮の変数の数（loop の init・mx・body、辞書の操作の被演算子）。
const OPERANDS: usize = 3;

/// loop の束縛 s の仮の番号（被演算子の次）。
const BINDER: usize = OPERANDS;

/// loop の書換えが導入する名前の数（loopex.rs の 44 個）。
const LOOP_NAMES: usize = 44;

/// 辞書の操作の名前（syntax.rs の `DICT_OPS`）を検証済みの操作にする。
fn dict_op_of(name: &str) -> Option<DictOp> {
    Some(match name {
        "dict_get" => DictOp::Get,
        "dict_put" => DictOp::Put,
        "dict_remove" => DictOp::Remove,
        "dict_has" => DictOp::Has,
        "dict_size" => DictOp::Size,
        "dict_keys" => DictOp::Keys,
        "dict_values" => DictOp::Values,
        "dict_entries" => DictOp::Entries,
        "dict_from" => DictOp::From,
        _ => return None,
    })
}

/// 被演算子の数（dictex.rs の `dict_args` の長さ）。
fn dict_arity(op: &DictOp) -> usize {
    match op {
        DictOp::Size | DictOp::Entries | DictOp::Keys | DictOp::Values | DictOp::From => 1,
        DictOp::Get | DictOp::Has | DictOp::Remove => 2,
        DictOp::Put => 3,
    }
}

/// 導入する名前の数（dict_types.rs の `dict_names`）。
fn dict_names(op: &DictOp) -> usize {
    match op {
        DictOp::Size | DictOp::Entries => 0,
        DictOp::Keys | DictOp::Values => 2,
        DictOp::Get | DictOp::Has | DictOp::Remove => 4,
        DictOp::Put => 6,
        DictOp::From => 7,
    }
}

/// 型を検証済みの型に写し、消去する（書換えの注釈は消去した型を使う）。
fn erased(t: &Ty) -> Option<VTy> {
    Some(erase_x(verified_ty(t)?))
}

/// 式の名前の上限の最大（dict_top と loop_top の部品）。
fn max_top(es: &[&EExpr]) -> Option<usize> {
    es.iter().try_fold(0usize, |m, e| Some(m.max(top_e(e)?)))
}

/// `Lower::fresh` の名前を k 個、順に取る。
fn fresh_names(lower: &mut Lower<'_>, k: usize) -> Vec<String> {
    (0..k).map(|_| lower.fresh()).collect()
}

/// 検証済みの版が返した式を Rust の式にする。仮の変数は被演算子の式に（一度だけ）置き換え、loop の束縛は元の名前、
/// 導入する名前は `names` の順（番号 start+k が names[k]）にする。
struct Splice {
    meta: Meta,
    /// 導入する名前の先頭の番号（b+1）
    start: usize,
    names: Vec<String>,
    /// loop の束縛の元の名前（辞書の操作には無い）
    binder: Option<String>,
    /// 被演算子の式（番号は仮の変数の番号）。置き換えると空になる
    operands: Vec<Option<Expr>>,
}

impl Splice {
    fn new(
        meta: Meta,
        start: usize,
        names: Vec<String>,
        binder: Option<String>,
        operands: &[Expr],
    ) -> Splice {
        Splice {
            meta,
            start,
            names,
            binder,
            operands: operands.iter().cloned().map(Some).collect(),
        }
    }

    /// 束縛や変数の名前。loop の束縛は元の名前、それ以外は導入する名前。
    fn name(&self, n: usize) -> Option<String> {
        match &self.binder {
            Some(s) if n == BINDER => Some(s.clone()),
            _ => self.names.get(n.checked_sub(self.start)?).cloned(),
        }
    }

    fn exs(&mut self, es: &[EExpr]) -> Option<Vec<Expr>> {
        es.iter().map(|e| self.ex(e)).collect()
    }

    fn ex(&mut self, e: &EExpr) -> Option<Expr> {
        let m = self.meta;
        let kind = match e {
            EExpr::Var(n) if *n < OPERANDS => return self.operands.get_mut(*n)?.take(),
            EExpr::Var(n) => ExprKind::Var(self.name(*n)?),
            EExpr::Int(n) => ExprKind::Int(n.n.clone()),
            EExpr::Bool(b) => ExprKind::Bool(*b),
            EExpr::List(t, es) => ExprKind::List {
                element_type: node_of(t, m)?,
                items: self.exs(es)?,
            },
            EExpr::Some(a) => ExprKind::Some(Box::new(self.ex(a)?)),
            EExpr::None(t) => ExprKind::None(node_of(t, m)?),
            EExpr::Pair(a, b) => ExprKind::Pair(Box::new(self.ex(a)?), Box::new(self.ex(b)?)),
            EExpr::Builtin(b, es) => ExprKind::Call {
                callee: builtin_name(b).to_string(),
                args: self.exs(es)?,
                builtin: true,
                callee_span: m.span,
                type_args: vec![],
            },
            EExpr::Let(x, a, b) => {
                let value = self.ex(a)?;
                ExprKind::Let {
                    name: self.name(*x)?,
                    name_span: m.span,
                    value: Box::new(value),
                    body: Box::new(self.ex(b)?),
                }
            }
            EExpr::If(c, a, b) => ExprKind::If(
                Box::new(self.ex(c)?),
                Box::new(self.ex(a)?),
                Box::new(self.ex(b)?),
            ),
            EExpr::Fold(xs, init, acc, item, body) => {
                let list = self.ex(xs)?;
                let init = self.ex(init)?;
                ExprKind::Fold {
                    list: Box::new(list),
                    init: Box::new(init),
                    acc: self.name(*acc)?,
                    acc_span: m.span,
                    item: self.name(*item)?,
                    item_span: m.span,
                    body: Box::new(self.ex(body)?),
                }
            }
            EExpr::Match(s, nb, y, sm) => {
                let scrutinee = self.ex(s)?;
                let on_none = self.ex(nb)?;
                let binder = self.name(*y)?;
                ExprKind::Match {
                    scrutinee: Box::new(scrutinee),
                    on_none: Box::new(on_none),
                    binder,
                    binder_span: m.span,
                    on_some: Box::new(self.ex(sm)?),
                }
            }
            EExpr::Inj(ok, t, u, a) => ExprKind::Inj {
                ok: *ok,
                ty: TypeNode::new(TyTag::Result, vec![node_of(t, m)?, node_of(u, m)?], m),
                value: Box::new(self.ex(a)?),
            },
            EExpr::MatchR(s, x, a, y, b) => {
                let scrutinee = self.ex(s)?;
                let ok_binder = self.name(*x)?;
                let on_ok = self.ex(a)?;
                let err_binder = self.name(*y)?;
                ExprKind::MatchResult {
                    scrutinee: Box::new(scrutinee),
                    ok_binder,
                    ok_span: m.span,
                    on_ok: Box::new(on_ok),
                    err_binder,
                    err_span: m.span,
                    on_err: Box::new(self.ex(b)?),
                }
            }
            _ => return None,
        };
        Some(Expr { kind, meta: m })
    }

    /// 書換えの結果を Rust の式にする。被演算子は全部一度ずつ使われていなければならない。
    fn finish(mut self, e: &EExpr) -> Option<Expr> {
        let out = self.ex(e)?;
        self.operands.iter().all(Option::is_none).then_some(out)
    }
}

/// 辞書の操作 `name(args)` の書換え（`Lower::dict_op_rust` と同じ形）。写せないとき None。
pub(crate) fn dict_op(
    lower: &mut Lower<'_>,
    m: Meta,
    name: &str,
    args: &[Expr],
    k: &Ty,
    v: &Ty,
) -> Option<Expr> {
    let op = dict_op_of(name)?;
    if args.len() != dict_arity(&op) {
        return None;
    }
    let names = dict_names(&op);
    let (a0, a1, a2) = (EExpr::Var(0), EExpr::Var(1), EExpr::Var(2));
    // 導入する名前は b+1 から（dict_rw_x と同じ。b は三つの仮の変数の名前の上限の最大）
    let start = max_top(&[&a0, &a1, &a2])? + 1;
    let out = dict_rw_x(op, a0, a1, a2, erased(k)?, erased(v)?)?;
    let names = fresh_names(lower, names);
    Splice::new(m, start, names, None, args).finish(&out)
}

/// loop の書換え（`Lower::loop_rust` と同じ形）。`st` は状態の型 S。写せないとき None。
pub(crate) fn loop_(
    lower: &mut Lower<'_>,
    m: Meta,
    init: &Expr,
    max: &Expr,
    s: &str,
    body: &Expr,
    st: &Ty,
) -> Option<Expr> {
    let (i0, mx, bd) = (EExpr::Var(0), EExpr::Var(1), EExpr::Var(2));
    // 導入する名前は loop_top の次から（b は s + 1 と、max と body の名前の上限の大きい方）
    let start = (BINDER + 1).max(max_top(&[&mx, &bd])?) + 1;
    let out = loop_rw_x(i0, mx, BINDER, bd, erased(st)?)?;
    let names = fresh_names(lower, LOOP_NAMES);
    let operands = [init.clone(), max.clone(), body.clone()];
    Splice::new(m, start, names, Some(s.to_string()), &operands).finish(&out)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::checker::HofTypes;
    use std::collections::{HashMap, HashSet};

    fn meta() -> Meta {
        Meta::new((0, 0), 0)
    }

    fn ex(kind: ExprKind) -> Expr {
        Expr { kind, meta: meta() }
    }

    fn var(n: &str) -> Expr {
        ex(ExprKind::Var(n.into()))
    }

    fn int(n: i64) -> Expr {
        ex(ExprKind::Int(n.into()))
    }

    fn call(f: &str, args: Vec<Expr>) -> Expr {
        ex(ExprKind::Call {
            callee: f.into(),
            args,
            builtin: true,
            callee_span: meta().span,
            type_args: vec![],
        })
    }

    /// 検証済みの書換えと従来の書換えは、同じ式を作る（名前と節点のメタまで）。
    fn same(verified: Option<Expr>, rust: Expr) {
        let verified = verified.expect("the verified rewrite applies");
        assert_eq!(format!("{verified:?}"), format!("{rust:?}"));
    }

    #[test]
    fn dict_operations_match_the_rust_rewrites() {
        let (k, v) = (Ty::int(), Ty::int());
        let cases = [
            ("dict_size", vec![var("d")]),
            ("dict_entries", vec![var("d")]),
            ("dict_keys", vec![var("d")]),
            ("dict_values", vec![var("d")]),
            ("dict_from", vec![var("xs")]),
            ("dict_get", vec![var("d"), var("key")]),
            ("dict_has", vec![var("d"), var("key")]),
            ("dict_remove", vec![var("d"), var("key")]),
            ("dict_put", vec![var("d"), var("key"), var("value")]),
            (
                "dict_get",
                vec![call("concat", vec![var("a"), var("b")]), int(1)],
            ),
        ];
        for (op, args) in cases {
            let types: HofTypes = HashMap::new();
            let mut lower = Lower::new(&types, HashSet::new());
            let verified = dict_op(&mut lower, meta(), op, &args, &k, &v);
            let mut lower = Lower::new(&types, HashSet::new());
            let rust = lower.dict_op_rust(meta(), op, args, &k, &v);
            same(verified, rust);
        }
    }

    #[test]
    fn loop_matches_the_rust_rewrite() {
        let body = ex(ExprKind::If(
            Box::new(call("lt", vec![var("x"), int(10)])),
            Box::new(ex(ExprKind::Some(Box::new(call(
                "add",
                vec![var("x"), int(1)],
            ))))),
            Box::new(ex(ExprKind::None(TypeNode::new(
                TyTag::Int,
                vec![],
                meta(),
            )))),
        ));
        let (init, max) = (int(0), call("add", vec![var("n"), int(1)]));
        let types: HofTypes = HashMap::new();
        let mut lower = Lower::new(&types, HashSet::new());
        let verified = loop_(&mut lower, meta(), &init, &max, "x", &body, &Ty::int());
        let mut lower = Lower::new(&types, HashSet::new());
        let rust = lower.loop_rust(meta(), init, max, "x".into(), body, &Ty::int());
        same(verified, rust);
    }

    #[test]
    fn unknown_or_wrong_arity_is_left_to_the_rust_rewrite() {
        let types: HofTypes = HashMap::new();
        let mut lower = Lower::new(&types, HashSet::new());
        let (k, v) = (Ty::int(), Ty::int());
        assert!(dict_op(&mut lower, meta(), "dict_get", &[var("d")], &k, &v).is_none());
        assert!(dict_op(&mut lower, meta(), "dict_frob", &[var("d")], &k, &v).is_none());
    }
}
