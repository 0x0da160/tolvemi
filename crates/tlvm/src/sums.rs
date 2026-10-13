//! v1.4 のユーザー定義の直和型と `match`（差分仕様 §3）。
//!
//! `type Name = A(T1, ...) | B | ...` は、variant が n 個（n ≥ 2）なら `Result<P1, Result<P2, ... Result<Pn-1, Pn>>>`
//! の別名である（Pk は k 番目の variant の中身の型。中身がなければ `Unit`、一つならその型、複数なら右に入れ子にした
//! `Pair`）。n = 1 なら P1 そのもの。構築 `A(x, ...)` は `ok`／`err` の入れ子に、`match` は `match_result`
//! （`Option` なら `match_option`）の入れ子と、中身を取り出す `fst`／`snd` の `let` に書き換える。
//! 型の等価性は展開後の構造で決まり、直和型の名前は表示と plain JSON にだけ使う。
//!
//! 処理は二段に分かれる。`expand` は型名を展開し、構築を書き換え、`match` の pattern を解決して網羅性を
//! 検査する（診断の phase は name）。型検査器は `match` を（対象と束縛の型が分かる形で）直接検査し、
//! `lower` が検証済み部品へ渡すソース用に `match_result` などへ書き換える。
//!
//! 書き換えは検証されていない接着部分（`trust-boundary.toml` の `glue`）。検証済み部品は書き換え後の
//! プログラム（`lower` の結果を整形したソース）を検査・実行する。

use crate::diagnostics::{closest, Diagnostic};
use crate::formatter::format_type;
use crate::syntax::*;
use std::collections::{HashMap, HashSet};
use std::sync::Arc;

/// 直和型の宣言か `match` を一つでも含むか。
pub fn has_sums(p: &Program) -> bool {
    fn ex(e: &Expr) -> bool {
        matches!(e.kind, ExprKind::SumMatch { .. }) || e.children().into_iter().any(ex)
    }
    p.declarations.iter().any(|d| match d {
        Decl::Sum(_) => true,
        Decl::Fn(f) => ex(&f.body),
        _ => false,
    })
}

struct SumTy {
    info: Arc<SumInfo>,
    /// 宣言の位置（型名は使う前に宣言する）
    pos: usize,
    /// `chain[k]` は k 番目以降の variant を表す型（`chain[0]` が名前付きの型全体。n = 1 なら P1）
    chain: Vec<TypeNode>,
    /// variant ごとの中身の型（展開後）
    fields: Vec<Vec<TypeNode>>,
    /// variant ごとの宣言の形（`Rect(Int, Int)`。修復ヒント用）
    sigs: Vec<String>,
    /// v1.10：型引数（総称の直和型のとき。`chain` と `fields` はこの名前の `TyTag::Param` を含む）
    tparams: Vec<TypeParam>,
    /// v1.10：宣言の meta と variant の名前の span（構築子の関数を作るとき用）
    meta: Meta,
    spans: Vec<Sp>,
}

impl SumTy {
    fn params(&self) -> Vec<String> {
        self.tparams.iter().map(|p| p.name.clone()).collect()
    }
    /// v1.10：型引数を `args` に置き換えた `chain`。
    fn chain_with(&self, args: &[TypeNode]) -> Vec<TypeNode> {
        let params = self.params();
        self.chain
            .iter()
            .map(|t| t.subst(&|p| params.iter().position(|q| q == p).map(|i| args[i].clone())))
            .collect()
    }
}

struct Env {
    sums: HashMap<String, SumTy>,
    /// 構築子 → （型名、variant の位置）
    ctors: HashMap<String, (String, usize)>,
    /// レコード型の名前 → 宣言の位置
    records: HashMap<String, usize>,
    /// プログラム中の直和型の名前（宣言の前後を問わない）
    sum_names: HashSet<String>,
    fns: HashSet<String>,
    diags: Vec<Diagnostic>,
    scope: Vec<String>,
    /// v1.10：型引数を推論する構築（`Node(x, 1)`）のために作った総称の関数（構築子 → 関数名）と、その宣言
    synth: HashMap<String, String>,
    synth_decls: Vec<FnDecl>,
    /// 新しく作る名前が重ならないための、プログラム中の全ての名前
    taken: HashSet<String>,
}

fn upper(s: &str) -> bool {
    s.starts_with(|c: char| c.is_ascii_uppercase())
}

fn ex(kind: ExprKind, meta: Meta) -> Expr {
    Expr { kind, meta }
}

/// 中身の型：なし → `Unit`、一つ → その型、複数 → 右に入れ子にした `Pair`。
fn payload_type(fields: &[TypeNode], meta: Meta) -> TypeNode {
    match fields.len() {
        0 => TypeNode::new(TyTag::Unit, vec![], meta),
        _ => {
            let mut t = fields[fields.len() - 1].clone();
            for f in fields[..fields.len() - 1].iter().rev() {
                t = TypeNode::new(TyTag::Pair, vec![f.clone(), t], meta);
            }
            t
        }
    }
}

/// `Ctor(...)` の形の説明（中身の数だけ `_`）。
fn pattern_text(name: &str, m: usize) -> String {
    if m == 0 {
        name.to_string()
    } else {
        format!("{name}({})", vec!["_"; m].join(", "))
    }
}

#[derive(Clone, PartialEq)]
enum Fam {
    Sum(String),
    Result,
    Option,
}

impl Fam {
    fn describe(&self) -> String {
        match self {
            Fam::Sum(s) => format!("constructor of {s}"),
            Fam::Result => "ok(..) / err(..) (Result)".into(),
            Fam::Option => "some(..) / none (Option)".into(),
        }
    }
}

impl Env {
    fn err(&mut self, code: &'static str, span: (usize, usize), index: usize) -> &mut Diagnostic {
        self.diags.push(Diagnostic::error("name", code, span).at(index));
        self.diags.last_mut().unwrap()
    }

    /// 型の中の直和型の名前を展開する。`at` はこの型を書いた宣言の位置（それより前に宣言した型だけ使える）。
    fn ty(&mut self, t: &TypeNode, at: usize) -> TypeNode {
        if t.tag == TyTag::Param {
            return t.clone();
        }
        if let Some(n) = &t.name {
            let later = match self.sums.get(n) {
                Some(s) if s.pos < at => {
                    // v1.10：総称の直和型は型引数を置き換える（`Tree<Int>`）
                    let params = s.params();
                    let args: Vec<TypeNode> = t.args.iter().map(|a| self.ty(a, at)).collect();
                    if args.len() != params.len() {
                        crate::generics::arity_error(&mut self.diags, n, &params, args.len(), t.meta);
                        return TypeNode::new(TyTag::Unit, vec![], t.meta);
                    }
                    let mut x = if params.is_empty() { self.sums[n].chain[0].clone() } else { self.sums[n].chain_with(&args)[0].clone() };
                    x.meta = t.meta;
                    return x;
                }
                Some(_) => true,
                None => self.sum_names.contains(n) || self.records.get(n).is_some_and(|p| *p >= at),
            };
            if !later && !self.records.contains_key(n) {
                let near = closest(n, self.sum_names.iter().chain(self.records.keys()).map(|k| k.as_str()), 3);
                let fix = if near.is_empty() {
                    "a type declared above with `type Name = { field: Type, ... }` or `type Name = A | B(T)`".to_string()
                } else {
                    format!("type declared above, e.g. {}", near.join(", "))
                };
                let fix = crate::generics::param_note(n, fix);
                let d = self.err("E-RECORD-UNKNOWN-TYPE", t.meta.span(), t.meta.index);
                *d = d.clone().act(n).fix("replace_type", t.meta.span(), fix);
                return TypeNode::new(TyTag::Unit, vec![], t.meta);
            }
            if later {
                let d = self.err("E-RECORD-UNKNOWN-TYPE", t.meta.span(), t.meta.index);
                *d = d.clone().act(n).fix(
                    "replace_type",
                    t.meta.span(),
                    format!("a type declared above this declaration ({n} is declared here or later; types cannot be recursive)"),
                );
                return TypeNode::new(TyTag::Unit, vec![], t.meta);
            }
            // レコード型の名前（または未知の名前）は records::expand が扱う（v1.10：型引数の中の直和型はここで展開する）
            return TypeNode { args: t.args.iter().map(|a| self.ty(a, at)).collect(), ..t.clone() };
        }
        TypeNode { args: t.args.iter().map(|a| self.ty(a, at)).collect(), ..t.clone() }
    }

    fn conflict(&mut self, name: &str, span: Sp, index: usize) {
        if self.ctors.contains_key(name) {
            let d = self.err("E-SUM-NAME-CONFLICT", span.t(), index);
            *d = d.clone().act(name).fix(
                "replace_identifier",
                span.t(),
                format!("name different from the constructor {name} (constructors, functions, variables and types share one namespace)"),
            );
        }
    }

    fn unknown_ctor(&mut self, name: &str, span: Sp, index: usize, in_pattern: bool) {
        let mut cands: Vec<&str> = self.ctors.keys().map(|k| k.as_str()).collect();
        if in_pattern {
            cands.extend(["ok", "err", "some", "none"]);
        }
        let near = closest(name, cands.iter().copied(), 3);
        let fix = if !near.is_empty() {
            format!("declared constructor, e.g. {}", near.join(", "))
        } else {
            let mut all: Vec<&str> = self.ctors.keys().map(|k| k.as_str()).collect();
            all.sort();
            let extra = if in_pattern { ", or ok(x), err(e), some(x), none, _" } else { "" };
            format!("constructor declared with `type Name = A | B(T)`: {}{extra}", all.join(", "))
        };
        let d = self.err("E-SUM-UNKNOWN-CTOR", span.t(), index);
        *d = d.clone().act(name).fix("replace_identifier", span.t(), fix);
    }

    fn arity(&mut self, ctor: &str, given: usize, parens: bool, span: Sp, index: usize, pattern: bool) {
        let (sum, k) = self.ctors[ctor].clone();
        let sig = self.sums[&sum].sigs[k].clone();
        let m = self.sums[&sum].fields[k].len();
        let fix = if m == 0 {
            format!("{ctor} has no fields: write it without parentheses")
        } else if pattern {
            format!("{} (one name or _ per field of {sig})", pattern_text(ctor, m))
        } else {
            format!("{ctor}(...) with {m} argument(s), as declared: {sig}")
        };
        let act = if m == 0 && parens { "parentheses".to_string() } else { format!("{given} fields") };
        let d = self.err("E-SUM-CTOR-ARITY", span.t(), index);
        *d = d.clone().exp(format!("{m} fields")).act(act).fix("replace_expression", span.t(), fix);
    }

    /// 構築子 `ctor` を中身 `args` で構築する式（ok／err の入れ子）。
    fn construct(&self, ctor: &str, args: Vec<Expr>, meta: Meta) -> Expr {
        let (sum, _) = &self.ctors[ctor];
        self.construct_in(ctor, args, meta, &self.sums[sum].chain)
    }

    /// v1.10：`chain`（型引数を置き換えた型の列）を使って構築する。
    fn construct_in(&self, ctor: &str, mut args: Vec<Expr>, meta: Meta, chain: &[TypeNode]) -> Expr {
        let (_, k) = &self.ctors[ctor];
        let n = chain.len();
        let mut payload = match args.len() {
            0 => ex(ExprKind::Unit, meta),
            _ => {
                let mut e = args.pop().unwrap();
                while let Some(a) = args.pop() {
                    e = ex(ExprKind::Pair(Box::new(a), Box::new(e)), meta);
                }
                e
            }
        };
        if n == 1 {
            return payload;
        }
        if k + 1 < n {
            payload = ex(ExprKind::Inj { ok: true, ty: chain[*k].clone(), value: Box::new(payload) }, meta);
        }
        for j in (0..*k).rev() {
            payload = ex(ExprKind::Inj { ok: false, ty: chain[j].clone(), value: Box::new(payload) }, meta);
        }
        payload
    }

    /// v1.10：総称の直和型の構築子 `ctor` を、型引数を推論して構築する総称の関数（なければ作る）の名前。
    /// `fn node_new<T>(a1: T, a2: Int) -> Tree<T> = err<Unit, Pair<T, Int>>(pair(a1, a2))` のような関数で、
    /// 型引数は普通の総称の関数の呼び出しと同じく引数の型から推論する。
    fn synth(&mut self, ctor: &str) -> String {
        if let Some(n) = self.synth.get(ctor) {
            return n.clone();
        }
        let (sum, k) = self.ctors[ctor].clone();
        let base = format!("{}_new", ctor.to_ascii_lowercase());
        let name = crate::generics::fresh(&mut self.taken, &base);
        let st = &self.sums[&sum];
        let (meta, span, tparams, ret) = (st.meta, st.spans[k], st.tparams.clone(), st.chain[0].clone());
        let fields = st.fields[k].clone();
        let mut params = vec![];
        let mut vars = vec![];
        for (i, f) in fields.into_iter().enumerate() {
            let pn = crate::generics::fresh(&mut self.taken, &format!("{name}_arg{}", i + 1));
            vars.push(ex(ExprKind::Var(pn.clone()), meta));
            params.push(Param { name: pn, name_span: span, ty: f, meta });
        }
        let body = self.construct(ctor, vars, meta);
        self.synth_decls.push(FnDecl {
            name: name.clone(),
            name_span: span,
            params,
            return_type: ret,
            body,
            meta,
            rec: false,
            rec_span: Sp::default(),
            type_params: tparams,
            ctor: Some(ctor.to_string()),
        });
        self.synth.insert(ctor.to_string(), name.clone());
        name
    }

    fn bind<R>(&mut self, names: &[(&str, Sp)], index: usize, f: impl FnOnce(&mut Self) -> R) -> R {
        let n = self.scope.len();
        for (b, sp) in names {
            self.conflict(b, *sp, index);
            self.scope.push(b.to_string());
        }
        let r = f(self);
        self.scope.truncate(n);
        r
    }

    fn expr(&mut self, e: &Expr) -> Expr {
        let m = e.meta;
        let i = m.index;
        let kind = match &e.kind {
            ExprKind::Var(n) if self.ctors.contains_key(n) && !self.scope.contains(n) => {
                let (sum, k) = self.ctors[n].clone();
                let fm = self.sums[&sum].fields[k].len();
                if fm != 0 {
                    self.arity(n, 0, false, m.span, i, false);
                } else if !self.sums[&sum].tparams.is_empty() {
                    // v1.10：総称の直和型の中身のない構築子は、型引数を推論する手がかりがない（`none<T>()` と同じく書く）
                    let params = self.sums[&sum].params();
                    let d = Diagnostic::error("name", "E-TYPE-GENERIC-INFER", m.span()).at(i).exp(format!("type arguments for {}", params.join(", "))).act(n).fix(
                        "replace_expression",
                        m.span(),
                        format!(
                            "{n}<{}>() with each type parameter replaced by a concrete type, e.g. {n}<{}>() (like none<T>())",
                            params.join(", "),
                            vec!["Int"; params.len()].join(", ")
                        ),
                    );
                    self.diags.push(d);
                    return ex(ExprKind::Unit, m);
                }
                return self.construct(n, vec![], m);
            }
            ExprKind::Var(n) if upper(n) && !self.scope.contains(n) && !self.ctors.is_empty() => {
                self.unknown_ctor(n, m.span, i, false);
                ExprKind::Unit
            }
            ExprKind::Call { callee, args, builtin: false, callee_span, type_args } if self.ctors.contains_key(callee) => {
                let args: Vec<Expr> = args.iter().map(|a| self.expr(a)).collect();
                let (sum, k) = self.ctors[callee].clone();
                let fm = self.sums[&sum].fields[k].len();
                let params = self.sums[&sum].params();
                if !type_args.is_empty() {
                    // v1.10：型引数を書いた構築 `Node<Int>(x, 1)`、`Leaf<Int>()`
                    let targs: Vec<TypeNode> = type_args.iter().map(|t| self.ty(t, usize::MAX)).collect();
                    if targs.len() != params.len() {
                        let at = Meta::new((callee_span.0, m.span.1), i);
                        crate::generics::arity_error(&mut self.diags, &sum, &params, targs.len(), at);
                        return ex(ExprKind::Unit, m);
                    }
                    if args.len() != fm {
                        self.arity(callee, args.len(), true, Sp(callee_span.0, m.span.1), i, false);
                        return ex(ExprKind::Unit, m);
                    }
                    let chain = self.sums[&sum].chain_with(&targs);
                    return self.construct_in(callee, args, m, &chain);
                }
                if fm == 0 || args.len() != fm {
                    self.arity(callee, args.len(), true, Sp(callee_span.0, m.span.1), i, false);
                    return ex(ExprKind::Unit, m);
                }
                if !params.is_empty() {
                    // v1.10：型引数は総称の関数の呼び出しとして型検査で推論する
                    let f = self.synth(callee);
                    return ex(ExprKind::Call { callee: f, args, builtin: false, callee_span: *callee_span, type_args: vec![] }, m);
                }
                return self.construct(callee, args, m);
            }
            ExprKind::Call { callee, builtin: false, callee_span, .. }
                if upper(callee) && !self.fns.contains(callee) && !self.ctors.is_empty() =>
            {
                self.unknown_ctor(callee, *callee_span, i, false);
                ExprKind::Unit
            }
            ExprKind::Call { callee, args, builtin, callee_span, type_args } => ExprKind::Call {
                callee: callee.clone(),
                args: args.iter().map(|a| self.expr(a)).collect(),
                builtin: *builtin,
                callee_span: *callee_span,
                type_args: type_args.iter().map(|t| self.ty(t, usize::MAX)).collect(),
            },
            ExprKind::List { element_type, items } => ExprKind::List {
                element_type: self.ty(element_type, usize::MAX),
                items: items.iter().map(|x| self.expr(x)).collect(),
            },
            ExprKind::None(t) => ExprKind::None(self.ty(t, usize::MAX)),
            ExprKind::DictNew(t) => ExprKind::DictNew(self.ty(t, usize::MAX)),
            ExprKind::Inj { ok, ty, value } => {
                ExprKind::Inj { ok: *ok, ty: self.ty(ty, usize::MAX), value: Box::new(self.expr(value)) }
            }
            ExprKind::Let { name, name_span, value, body } => {
                let value = Box::new(self.expr(value));
                let body = Box::new(self.bind(&[(name, *name_span)], i, |s| s.expr(body)));
                ExprKind::Let { name: name.clone(), name_span: *name_span, value, body }
            }
            ExprKind::Fold { list, init, acc, acc_span, item, item_span, body } => {
                let list = Box::new(self.expr(list));
                let init = Box::new(self.expr(init));
                let body = Box::new(self.bind(&[(acc, *acc_span), (item, *item_span)], i, |s| s.expr(body)));
                ExprKind::Fold { list, init, acc: acc.clone(), acc_span: *acc_span, item: item.clone(), item_span: *item_span, body }
            }
            ExprKind::Hof { op, list, binder, binder_span, body } => {
                let list = Box::new(self.expr(list));
                let body = Box::new(self.bind(&[(binder, *binder_span)], i, |s| s.expr(body)));
                ExprKind::Hof { op: *op, list, binder: binder.clone(), binder_span: *binder_span, body }
            }
            ExprKind::Loop { init, max, binder, binder_span, body } => {
                let init = Box::new(self.expr(init));
                let max = Box::new(self.expr(max));
                let body = Box::new(self.bind(&[(binder, *binder_span)], i, |s| s.expr(body)));
                ExprKind::Loop { init, max, binder: binder.clone(), binder_span: *binder_span, body }
            }
            ExprKind::Match { scrutinee, on_none, binder, binder_span, on_some } => {
                let scrutinee = Box::new(self.expr(scrutinee));
                let on_none = Box::new(self.expr(on_none));
                let on_some = Box::new(self.bind(&[(binder, *binder_span)], i, |s| s.expr(on_some)));
                ExprKind::Match { scrutinee, on_none, binder: binder.clone(), binder_span: *binder_span, on_some }
            }
            ExprKind::MatchResult { scrutinee, ok_binder, ok_span, on_ok, err_binder, err_span, on_err } => {
                let scrutinee = Box::new(self.expr(scrutinee));
                let on_ok = Box::new(self.bind(&[(ok_binder, *ok_span)], i, |s| s.expr(on_ok)));
                let on_err = Box::new(self.bind(&[(err_binder, *err_span)], i, |s| s.expr(on_err)));
                ExprKind::MatchResult {
                    scrutinee,
                    ok_binder: ok_binder.clone(),
                    ok_span: *ok_span,
                    on_ok,
                    err_binder: err_binder.clone(),
                    err_span: *err_span,
                    on_err,
                }
            }
            ExprKind::SumMatch { scrutinee, arms, kw_span, close_span, .. } => {
                return self.sum_match(e, scrutinee, arms, *kw_span, *close_span);
            }
            _ => {
                let mut out = e.clone();
                for c in out.children_mut() {
                    *c = self.expr(c);
                }
                return out;
            }
        };
        ex(kind, m)
    }

    fn sum_match(&mut self, e: &Expr, scrutinee: &Expr, arms: &[Arm], kw_span: Sp, close_span: Sp) -> Expr {
        let m = e.meta;
        let i = m.index;
        let scrutinee = self.expr(scrutinee);
        let before = self.diags.len();
        // pattern を解決し、どの型の場合か（直和型、Result、Option）を決める
        let mut fam: Option<Fam> = None;
        let mut variants: Vec<Option<usize>> = vec![];
        for a in arms {
            let p = &a.pat;
            let r = match &p.kind {
                PatKind::Ctor(c) => match self.ctors.get(c).cloned() {
                    Some((sum, k)) => {
                        let fm = self.sums[&sum].fields[k].len();
                        if (fm == 0 && p.parens) || (fm > 0 && p.binds.len() != fm) {
                            self.arity(c, p.binds.len(), p.parens, p.span, i, true);
                        }
                        Some((Fam::Sum(sum), k))
                    }
                    None => {
                        self.unknown_ctor(c, p.span, i, true);
                        None
                    }
                },
                PatKind::Ok => Some((Fam::Result, 0)),
                PatKind::Err => Some((Fam::Result, 1)),
                PatKind::Some => Some((Fam::Option, 0)),
                PatKind::None => Some((Fam::Option, 1)),
                PatKind::Wild => None,
            };
            variants.push(r.as_ref().map(|(_, k)| *k));
            if let Some((f, _)) = r {
                match &fam {
                    None => fam = Some(f),
                    Some(g) if *g != f => {
                        let g = g.clone();
                        let d = self.err("E-MATCH-MIXED", p.span.t(), i);
                        *d = d.clone().exp(g.describe()).act(f.describe()).fix(
                            "replace_expression",
                            p.span.t(),
                            format!("pattern for the same type as the first arm: {}", g.describe()),
                        );
                    }
                    _ => {}
                }
            }
        }
        // 網羅性：全部の場合を一度ずつか、最後の `_` で残りをまとめる
        if self.diags.len() == before {
            let names: Vec<String> = match &fam {
                Some(Fam::Sum(s)) => {
                    let st = &self.sums[s];
                    st.info.variants.iter().map(|(v, fm)| pattern_text(v, *fm)).collect()
                }
                Some(Fam::Result) => vec!["ok(v)".into(), "err(e)".into()],
                Some(Fam::Option) => vec!["some(v)".into(), "none".into()],
                None => vec![],
            };
            let mut seen = vec![false; names.len()];
            let mut wild = false;
            for (a, v) in arms.iter().zip(&variants) {
                let unreachable = wild || (v.is_none() && !seen.is_empty() && seen.iter().all(|x| *x));
                if unreachable {
                    let d = self.err("E-MATCH-UNREACHABLE", a.span.t(), i);
                    *d = d.clone().fix(
                        "delete_span",
                        a.span.t(),
                        "delete this arm: the arms before it already cover every case it could match".to_string(),
                    );
                    continue;
                }
                match v {
                    Some(k) if seen[*k] => {
                        let d = self.err("E-MATCH-DUPLICATE", a.span.t(), i);
                        *d = d.clone().act(names[*k].clone()).fix(
                            "delete_span",
                            a.span.t(),
                            format!("delete this arm: an earlier arm already handles {}", names[*k]),
                        );
                    }
                    Some(k) => seen[*k] = true,
                    None => wild = true,
                }
            }
            let missing: Vec<&str> = names.iter().zip(&seen).filter(|(_, s)| !**s).map(|(n, _)| n.as_str()).collect();
            if !wild && !missing.is_empty() {
                let list = missing.join(", ");
                let arms_text: Vec<String> = missing.iter().map(|p| format!("{p} => ...")).collect();
                let d = self.err("E-MATCH-MISSING", kw_span.t(), i);
                *d = d.clone().exp(list).fix(
                    "insert_text",
                    (close_span.0, close_span.0),
                    format!("arms for the missing cases, inserted before '}}': `, {}` (or one final `_ => ...`)", arms_text.join(", ")),
                );
            }
        }
        // 枝の本体（束縛は枝の中だけで見える）
        let mut out_arms = vec![];
        for (a, v) in arms.iter().zip(&variants) {
            let names: Vec<(&str, Sp)> = a.pat.binds.iter().filter(|(b, _)| b != "_").map(|(b, s)| (b.as_str(), *s)).collect();
            let body = self.bind(&names, i, |s| s.expr(&a.body));
            out_arms.push(Arm { body, variant: *v, ..a.clone() });
        }
        let kind = match fam {
            Some(Fam::Sum(s)) => {
                let st = &self.sums[&s];
                let mut ty = st.chain[0].clone();
                ty.meta = scrutinee.meta;
                MatchKind::Sum { ty, fields: st.fields.clone() }
            }
            Some(Fam::Result) => MatchKind::Result,
            Some(Fam::Option) => MatchKind::Option,
            None => MatchKind::Any,
        };
        ex(ExprKind::SumMatch { scrutinee: Box::new(scrutinee), arms: out_arms, kw_span, close_span, kind: Some(kind) }, m)
    }

    fn declare(&mut self, pos: usize, sd: &SumDecl, type_names: &HashSet<&str>) {
        let idx = sd.meta.index;
        if self.sums.contains_key(&sd.name) || self.records.contains_key(&sd.name) {
            let d = self.err("E-RECORD-DUPLICATE-TYPE", sd.name_span.t(), idx);
            *d = d.clone().act(&sd.name);
            return;
        }
        let mut variants = vec![];
        let mut fields = vec![];
        let mut sigs = vec![];
        for v in &sd.variants {
            if variants.iter().any(|(n, _)| *n == v.name) || self.ctors.contains_key(&v.name) {
                let d = self.err("E-SUM-DUPLICATE-CTOR", v.name_span.t(), idx);
                *d = d.clone().act(&v.name).fix(
                    "replace_identifier",
                    v.name_span.t(),
                    "constructor name not used by any other variant in the program".to_string(),
                );
            } else if self.fns.contains(&v.name) || type_names.contains(v.name.as_str()) {
                let what = if self.fns.contains(&v.name) { "function" } else { "type" };
                let d = self.err("E-SUM-NAME-CONFLICT", v.name_span.t(), idx);
                *d = d.clone().act(&v.name).fix(
                    "replace_identifier",
                    v.name_span.t(),
                    format!("constructor name different from the {what} {}", v.name),
                );
            }
            fields.push(v.fields.iter().map(|f| self.ty(f, pos)).collect::<Vec<_>>());
            sigs.push(if v.fields.is_empty() {
                v.name.clone()
            } else {
                format!("{}({})", v.name, v.fields.iter().map(format_type).collect::<Vec<_>>().join(", "))
            });
            variants.push((v.name.clone(), v.fields.len()));
        }
        let meta = sd.meta;
        let payloads: Vec<TypeNode> = fields.iter().map(|fs| payload_type(fs, meta)).collect();
        let n = payloads.len();
        let mut chain = vec![payloads[n - 1].clone()];
        for p in payloads[..n - 1].iter().rev() {
            let next = chain[0].clone();
            chain.insert(0, TypeNode::new(TyTag::Result, vec![p.clone(), next], meta));
        }
        let inner = if n == 1 { chain[0].label.clone() } else { Label::default() };
        let params: Vec<String> = sd.type_params.iter().map(|p| p.name.clone()).collect();
        let generic = (!params.is_empty()).then(|| {
            let mut t = chain[0].clone();
            t.label = Label::default();
            Generic { params, template: t }
        });
        let info = Arc::new(SumInfo { name: sd.name.clone(), variants, inner, generic });
        chain[0].label = Label(Some(Named::Sum(info.clone())));
        for (k, (v, _)) in info.variants.iter().enumerate() {
            self.ctors.entry(v.clone()).or_insert_with(|| (sd.name.clone(), k));
        }
        let spans = sd.variants.iter().map(|v| v.name_span).collect();
        let st = SumTy { info, pos, chain, fields, sigs, tparams: sd.type_params.clone(), meta, spans };
        self.sums.insert(sd.name.clone(), st);
    }
}

/// 直和型を展開する。型宣言を除き、型名を展開後の型に、構築を ok／err の入れ子に置き換え、`match` の pattern を
/// 解決する（`ExprKind::SumMatch` は型検査器が検査し、`lower` が match_result などにする）。
/// レコードの構文（レコード型の名前、構築、field の参照）はそのまま残す（この後で `records::expand` が扱う）。
pub fn expand(p: &Program) -> Result<Program, Vec<Diagnostic>> {
    let mut env = Env {
        sums: HashMap::new(),
        ctors: HashMap::new(),
        records: HashMap::new(),
        sum_names: p
            .declarations
            .iter()
            .filter_map(|d| match d {
                Decl::Sum(s) => Some(s.name.clone()),
                _ => None,
            })
            .collect(),
        fns: p.functions().map(|f| f.name.clone()).collect(),
        diags: vec![],
        scope: vec![],
        synth: HashMap::new(),
        synth_decls: vec![],
        taken: crate::generics::idents(p),
    };
    let mut type_names: HashSet<&str> = HashSet::new();
    for (pos, d) in p.declarations.iter().enumerate() {
        match d {
            Decl::Type(t) => {
                env.records.entry(t.name.clone()).or_insert(pos);
                type_names.insert(&t.name);
            }
            Decl::Sum(s) => {
                type_names.insert(&s.name);
            }
            _ => {}
        }
    }
    for (pos, d) in p.declarations.iter().enumerate() {
        if let Decl::Sum(s) = d {
            env.declare(pos, s, &type_names);
        }
    }
    let mut decls = vec![];
    for (pos, d) in p.declarations.iter().enumerate() {
        match d {
            Decl::Sum(_) => {}
            Decl::Entry(e) => decls.push(Decl::Entry(e.clone())),
            Decl::Type(t) => {
                let fields = t.fields.iter().map(|f| FieldDecl { ty: env.ty(&f.ty, pos), ..f.clone() }).collect();
                decls.push(Decl::Type(TypeDecl { fields, ..t.clone() }));
            }
            Decl::Fn(f) => {
                let params: Vec<Param> = f.params.iter().map(|q| Param { ty: env.ty(&q.ty, usize::MAX), ..q.clone() }).collect();
                for q in &params {
                    env.conflict(&q.name, q.name_span, q.meta.index);
                }
                let return_type = env.ty(&f.return_type, usize::MAX);
                env.scope = params.iter().map(|q| q.name.clone()).collect();
                let body = env.expr(&f.body);
                env.scope.clear();
                decls.push(Decl::Fn(FnDecl { params, return_type, body, ..f.clone() }));
            }
        }
    }
    // v1.10：型引数を推論する構築のために作った総称の関数（宣言の末尾に置く）
    decls.extend(env.synth_decls.drain(..).map(Decl::Fn));
    if env.diags.is_empty() {
        Ok(Program { declarations: decls, meta: p.meta })
    } else {
        Err(env.diags)
    }
}

// ---------------------------------------------------------------- lower

struct Lower {
    taken: HashSet<String>,
    fresh: usize,
}

fn collect(e: &Expr, out: &mut HashSet<String>) {
    match &e.kind {
        ExprKind::Var(n) => {
            out.insert(n.clone());
        }
        ExprKind::Let { name, .. } => {
            out.insert(name.clone());
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
        ExprKind::Call { callee, .. } => {
            out.insert(callee.clone());
        }
        _ => {}
    }
    for c in e.children() {
        collect(c, out);
    }
}

impl Lower {
    fn fresh(&mut self) -> String {
        loop {
            self.fresh += 1;
            let n = format!("sum{}", self.fresh);
            if !self.taken.contains(&n) {
                self.taken.insert(n.clone());
                return n;
            }
        }
    }

    fn expr(&mut self, e: &Expr) -> Expr {
        if let ExprKind::SumMatch { scrutinee, arms, kind: Some(kind), .. } = &e.kind {
            let scrutinee = self.expr(scrutinee);
            let arms: Vec<Arm> = arms.iter().map(|a| Arm { body: self.expr(&a.body), ..a.clone() }).collect();
            return self.lower_match(e.meta, scrutinee, &arms, kind);
        }
        let mut out = e.clone();
        for c in out.children_mut() {
            *c = self.expr(c);
        }
        out
    }

    fn lower_match(&mut self, m: Meta, scrutinee: Expr, arms: &[Arm], kind: &MatchKind) -> Expr {
        let wild = arms.iter().find(|a| a.variant.is_none()).map(|a| a.body.clone());
        let arm = |k: usize| arms.iter().find(|a| a.variant == Some(k));
        let body = |k: usize| arm(k).map(|a| a.body.clone()).or_else(|| wild.clone()).expect("exhaustive match");
        // 一つの束縛の名前（`_` なら新しい名前）
        let binder = |l: &mut Lower, k: usize| -> String {
            match arm(k).and_then(|a| a.pat.binds.first()) {
                Some((b, _)) if b != "_" => b.clone(),
                _ => l.fresh(),
            }
        };
        match kind {
            MatchKind::Any => {
                let v = self.fresh();
                let sp = Sp(m.span.0, m.span.0);
                ex(ExprKind::Let { name: v, name_span: sp, value: Box::new(scrutinee), body: Box::new(wild.expect("wildcard arm")) }, m)
            }
            MatchKind::Option => {
                let b = binder(self, 0);
                ex(
                    ExprKind::Match {
                        scrutinee: Box::new(scrutinee),
                        on_none: Box::new(body(1)),
                        binder: b,
                        binder_span: m.span,
                        on_some: Box::new(body(0)),
                    },
                    m,
                )
            }
            MatchKind::Result => {
                let x = binder(self, 0);
                let y = binder(self, 1);
                ex(
                    ExprKind::MatchResult {
                        scrutinee: Box::new(scrutinee),
                        ok_binder: x,
                        ok_span: m.span,
                        on_ok: Box::new(body(0)),
                        err_binder: y,
                        err_span: m.span,
                        on_err: Box::new(body(1)),
                    },
                    m,
                )
            }
            MatchKind::Sum { fields, .. } => {
                let counts: Vec<usize> = fields.iter().map(|f| f.len()).collect();
                self.level(m, 0, scrutinee, arms, &counts, &wild)
            }
        }
    }

    /// k 番目以降の variant を表す値 `src` の分解。
    fn level(&mut self, m: Meta, k: usize, src: Expr, arms: &[Arm], counts: &[usize], wild: &Option<Expr>) -> Expr {
        let n = counts.len();
        if n == 1 || k + 1 == n {
            return self.payload(m, k, src, arms, counts, wild);
        }
        let explicit = |j: usize| arms.iter().any(|a| a.variant == Some(j));
        let arm = arms.iter().find(|a| a.variant == Some(k));
        // ok の枝：中身が一つで名前があれば、その名前を binder にする
        let (x, on_ok) = match arm {
            Some(a) if counts[k] == 1 && a.pat.binds[0].0 != "_" => (a.pat.binds[0].0.clone(), a.body.clone()),
            _ => {
                let x = self.fresh();
                let var = ex(ExprKind::Var(x.clone()), m);
                let b = self.payload(m, k, var, arms, counts, wild);
                (x, b)
            }
        };
        let y = self.fresh();
        let on_err = if (k + 1..n).any(explicit) {
            let var = ex(ExprKind::Var(y.clone()), m);
            self.level(m, k + 1, var, arms, counts, wild)
        } else {
            wild.clone().expect("exhaustive match")
        };
        ex(
            ExprKind::MatchResult {
                scrutinee: Box::new(src),
                ok_binder: x,
                ok_span: m.span,
                on_ok: Box::new(on_ok),
                err_binder: y,
                err_span: m.span,
                on_err: Box::new(on_err),
            },
            m,
        )
    }

    /// k 番目の variant の中身 `src` を枝の束縛に取り出して本体を評価する式。
    fn payload(&mut self, m: Meta, k: usize, src: Expr, arms: &[Arm], counts: &[usize], wild: &Option<Expr>) -> Expr {
        let Some(a) = arms.iter().find(|a| a.variant == Some(k)) else {
            return wild.clone().expect("exhaustive match");
        };
        let fm = counts[k];
        let sp = Sp(m.span.0, m.span.0);
        let let_ = |name: String, value: Expr, body: Expr| {
            ex(ExprKind::Let { name, name_span: sp, value: Box::new(value), body: Box::new(body) }, m)
        };
        let names: Vec<&str> = a.pat.binds.iter().map(|(b, _)| b.as_str()).collect();
        if fm == 0 || names.iter().all(|b| *b == "_") {
            return a.body.clone();
        }
        if fm == 1 {
            return let_(names[0].to_string(), src, a.body.clone());
        }
        let (v, wrap) = match &src.kind {
            ExprKind::Var(v) => (v.clone(), None),
            _ => (self.fresh(), Some(src)),
        };
        let call = |name: &str, arg: Expr| {
            ex(ExprKind::Call { callee: name.into(), args: vec![arg], builtin: true, callee_span: m.span, type_args: vec![] }, m)
        };
        let mut out = a.body.clone();
        for (i, b) in names.iter().enumerate().rev() {
            if *b == "_" {
                continue;
            }
            let mut x = ex(ExprKind::Var(v.clone()), m);
            for _ in 0..i {
                x = call("snd", x);
            }
            if i + 1 < fm {
                x = call("fst", x);
            }
            out = let_(b.to_string(), x, out);
        }
        match wrap {
            Some(value) => let_(v, value, out),
            None => out,
        }
    }
}

/// `match` を `match_result`／`match_option`／`let` と `fst`／`snd` に書き換える（検証済み部品へ渡すソース用）。
/// 書き換えで導入する名前（`sum1` など）はプログラム中のどの名前とも重ならない。
pub fn lower(p: &Program) -> Program {
    let mut taken = HashSet::new();
    for d in &p.declarations {
        if let Decl::Fn(f) = d {
            taken.insert(f.name.clone());
            taken.extend(f.params.iter().map(|q| q.name.clone()));
            collect(&f.body, &mut taken);
        }
    }
    let mut l = Lower { taken, fresh: 0 };
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
