//! v1.14 の再帰する直和型（差分仕様 `spec/lptl-v1.14`）。
//!
//! 項に自分自身（または循環に入る別の直和型）を含む直和型 `type Tree = Leaf | Node(Tree, Int, Tree)` は、
//! 型としては `List<Int>` に置き換える。値は整数の列で、先頭が構築子の番号（宣言の順、0 から）、そのあとに
//! 項ごとに `[長さ] ++ 中身` が続く。Int の項の中身は一つの整数、Bool の項の中身は 0 か 1、再帰する型の項の
//! 中身はその値そのもの。項の長さを前に置くので、次の項の位置を求めるのに子の中身を再帰で読まずに済む。
//!
//! 検査の前に書き換える（検証されていない接着部分）。
//! - 構築 `Node(l, v, r)` は、値の列を作る関数 `node_new(l, v, r)` の呼び出しに。引数のない構築子は列の定数に。
//! - `match` は、先頭の番号と比べる `if` の連鎖に。束縛は補助関数 `rec_at`・`rec_take`・`rec_drop` で項を
//!   取り出す（どれも LPTL の関数として書き、型検査と検証済み部品が検査する）。
//! - 型の名前は `List<Int>` に。型エラーの文面にも `List<Int>` と出る（既知の制限）。
//!
//! 直和型の展開（sums）より前に行う。再帰しない直和型はこれまでどおり sums が扱う。

use crate::diagnostics::Diagnostic;
use crate::formatter::format_type;
use crate::generics::{arity_error, fresh, idents};
use crate::sums::pattern_text;
use crate::syntax::*;
use num_bigint::BigInt;
use std::collections::{HashMap, HashSet};

/// 循環に入る直和型の名前（宣言の型の名前をたどって自分に戻るもの）。
fn recursive_names(p: &Program) -> HashSet<String> {
    let mut edges: HashMap<String, Vec<String>> = HashMap::new();
    for d in &p.declarations {
        match d {
            Decl::Sum(s) => {
                let out = edges.entry(s.name.clone()).or_default();
                for v in &s.variants {
                    for f in &v.fields {
                        mentions(f, out);
                    }
                }
            }
            Decl::Type(t) => {
                let out = edges.entry(t.name.clone()).or_default();
                for f in &t.fields {
                    mentions(&f.ty, out);
                }
            }
            _ => {}
        }
    }
    p.declarations
        .iter()
        .filter_map(|d| match d {
            Decl::Sum(s) if reaches(&edges, &s.name, &s.name) => Some(s.name.clone()),
            _ => None,
        })
        .collect()
}

/// 型の node が書いた名前（型引数の中も）。
fn mentions(t: &TypeNode, out: &mut Vec<String>) {
    if t.tag != TyTag::Param {
        if let Some(n) = &t.name {
            out.push(n.clone());
        }
    }
    for a in &t.args {
        mentions(a, out);
    }
}

/// `from` の辺をたどって `target` に戻るか。
fn reaches(edges: &HashMap<String, Vec<String>>, from: &str, target: &str) -> bool {
    let mut seen: HashSet<&str> = HashSet::new();
    let mut todo: Vec<&str> = edges.get(from).into_iter().flatten().map(String::as_str).collect();
    while let Some(n) = todo.pop() {
        if n == target {
            return true;
        }
        if seen.insert(n) {
            todo.extend(edges.get(n).into_iter().flatten().map(String::as_str));
        }
    }
    false
}

/// 再帰する直和型を含むか（あれば `expand` で書き換える）。
pub fn has_recursive(p: &Program) -> bool {
    !recursive_names(p).is_empty()
}

/// 項の中身の符号化。
#[derive(Clone, Copy, PartialEq)]
enum Kind {
    Int,
    Bool,
    Rec,
}

/// 中身の型を符号化できるか（Int、Bool、再帰する型そのもの）。
fn kind_of(t: &TypeNode, rec: &HashSet<String>) -> Option<Kind> {
    if t.tag == TyTag::Param || !t.args.is_empty() {
        return None;
    }
    match &t.name {
        Some(n) => rec.contains(n).then_some(Kind::Rec),
        None => match t.tag {
            TyTag::Int => Some(Kind::Int),
            TyTag::Bool => Some(Kind::Bool),
            _ => None,
        },
    }
}

#[derive(Clone)]
struct Variant {
    name: String,
    kinds: Vec<Kind>,
    /// 宣言の形（`Node(Tree, Int, Tree)`。診断用）
    sig: String,
    /// 構築の関数の名前
    func: String,
    meta: Meta,
    span: Sp,
}

struct Env {
    rec: HashSet<String>,
    /// 全ての直和型の構築子の名前（再帰しない型のものも。混ざった pattern の診断に使う）
    all_ctors: HashSet<String>,
    /// 再帰する型の名前 → 項（宣言の順）
    tys: HashMap<String, Vec<Variant>>,
    /// 構築子の名前 → （型の名前、項の番号）
    ctors: HashMap<String, (String, usize)>,
    /// 補助関数の名前
    at: String,
    take: String,
    drop: String,
    taken: HashSet<String>,
    diags: Vec<Diagnostic>,
    fns: Vec<FnDecl>,
}

pub fn expand(p: &Program) -> Result<Program, Vec<Diagnostic>> {
    let all_ctors = p
        .declarations
        .iter()
        .filter_map(|d| match d {
            Decl::Sum(s) => Some(s.variants.iter().map(|v| v.name.clone())),
            _ => None,
        })
        .flatten()
        .collect();
    let mut env = Env {
        rec: recursive_names(p),
        all_ctors,
        tys: HashMap::new(),
        ctors: HashMap::new(),
        at: String::new(),
        take: String::new(),
        drop: String::new(),
        taken: idents(p),
        diags: vec![],
        fns: vec![],
    };
    env.at = env.name("rec_at");
    env.take = env.name("rec_take");
    env.drop = env.name("rec_drop");
    env.declare(p);
    env.binder_conflicts(p);
    env.helpers();
    let mut decls = vec![];
    for d in &p.declarations {
        match d {
            Decl::Sum(s) if env.rec.contains(&s.name) => {}
            Decl::Sum(s) => {
                let mut variants = vec![];
                for v in &s.variants {
                    let fields = v.fields.iter().map(|f| env.rty(f)).collect();
                    variants.push(VariantDecl { fields, ..v.clone() });
                }
                decls.push(Decl::Sum(SumDecl { variants, ..s.clone() }));
            }
            Decl::Type(t) => {
                let fields = t.fields.iter().map(|f| FieldDecl { ty: env.rty(&f.ty), ..f.clone() }).collect();
                decls.push(Decl::Type(TypeDecl { fields, ..t.clone() }));
            }
            Decl::Entry(e) => decls.push(Decl::Entry(e.clone())),
            Decl::Fn(f) => {
                let params = f.params.iter().map(|q| Param { ty: env.rty(&q.ty), ..q.clone() }).collect();
                let return_type = env.rty(&f.return_type);
                let body = env.expr(&f.body);
                decls.push(Decl::Fn(FnDecl { params, return_type, body, ..f.clone() }));
            }
        }
    }
    // 構築の関数と補助関数は宣言の末尾に置く（sums と同じ）
    decls.extend(std::mem::take(&mut env.fns).into_iter().map(Decl::Fn));
    if env.diags.is_empty() {
        Ok(Program { declarations: decls, meta: p.meta, imports: p.imports.clone() })
    } else {
        Err(env.diags)
    }
}

fn ex(kind: ExprKind, m: Meta) -> Expr {
    Expr { kind, meta: m }
}

fn int_node(m: Meta) -> TypeNode {
    TypeNode::new(TyTag::Int, vec![], m)
}

fn list_int_node(m: Meta) -> TypeNode {
    TypeNode::new(TyTag::List, vec![int_node(m)], m)
}

fn int(n: usize, m: Meta) -> Expr {
    ex(ExprKind::Int(BigInt::from(n as u64)), m)
}

fn var(n: &str, m: Meta) -> Expr {
    ex(ExprKind::Var(n.to_string()), m)
}

/// 組み込みの関数の呼び出し。
fn builtin(f: &str, args: Vec<Expr>, m: Meta) -> Expr {
    ex(ExprKind::Call { callee: f.to_string(), args, builtin: true, callee_span: m.span, type_args: vec![] }, m)
}

/// 補助関数の呼び出し（利用者の関数と同じ扱い）。
fn call(f: &str, args: Vec<Expr>, m: Meta) -> Expr {
    ex(ExprKind::Call { callee: f.to_string(), args, builtin: false, callee_span: m.span, type_args: vec![] }, m)
}

/// `Int` の列 `list<Int>(items)`。
fn list(items: Vec<Expr>, m: Meta) -> Expr {
    ex(ExprKind::List { element_type: int_node(m), items }, m)
}

fn pair(a: Expr, b: Expr, m: Meta) -> Expr {
    ex(ExprKind::Pair(Box::new(a), Box::new(b)), m)
}

fn if_(c: Expr, t: Expr, f: Expr, m: Meta) -> Expr {
    ex(ExprKind::If(Box::new(c), Box::new(t), Box::new(f)), m)
}

fn let_(name: &str, span: Sp, value: Expr, body: Expr, m: Meta) -> Expr {
    ex(ExprKind::Let { name: name.to_string(), name_span: span, value: Box::new(value), body: Box::new(body) }, m)
}

fn fold(list: Expr, init: Expr, acc: &str, item: &str, body: Expr, m: Meta) -> Expr {
    ex(
        ExprKind::Fold {
            list: Box::new(list),
            init: Box::new(init),
            acc: acc.to_string(),
            acc_span: m.span,
            item: item.to_string(),
            item_span: m.span,
            body: Box::new(body),
        },
        m,
    )
}

/// 補助関数の宣言（診断の未使用の警告は出さない）。
fn func(name: &str, params: Vec<(String, TypeNode)>, ret: TypeNode, body: Expr, m: Meta) -> FnDecl {
    FnDecl {
        name: name.to_string(),
        name_span: Sp::default(),
        params: params.into_iter().map(|(n, ty)| Param { name: n, name_span: Sp::default(), ty, meta: m }).collect(),
        return_type: ret,
        body,
        meta: m,
        rec: false,
        rec_span: Sp::default(),
        type_params: vec![],
        ctor: Some(name.to_string()),
    }
}

impl Env {
    /// `base`、`base2`、... のうち、まだ使っていない名前（以後は使ったものとする）。
    fn name(&mut self, base: &str) -> String {
        fresh(&mut self.taken, base)
    }

    fn push(&mut self, d: Diagnostic) {
        self.diags.push(d);
    }

    /// 再帰する型の宣言を読み、構築子の番号と項の符号化を決める。名前の誤り・項の型の誤りを報告する。
    fn declare(&mut self, p: &Program) {
        let mut type_count: HashMap<&str, usize> = HashMap::new();
        let mut ctor_count: HashMap<&str, usize> = HashMap::new();
        for d in &p.declarations {
            match d {
                Decl::Sum(s) => {
                    *type_count.entry(&s.name).or_default() += 1;
                    for v in &s.variants {
                        *ctor_count.entry(&v.name).or_default() += 1;
                    }
                }
                Decl::Type(t) => *type_count.entry(&t.name).or_default() += 1,
                _ => {}
            }
        }
        let fn_names: HashSet<&str> = p.functions().map(|f| f.name.as_str()).collect();
        for d in &p.declarations {
            let Decl::Sum(s) = d else { continue };
            if !self.rec.contains(&s.name) {
                continue;
            }
            let idx = s.meta.index;
            if type_count[s.name.as_str()] > 1 {
                let d = Diagnostic::error("name", "E-RECORD-DUPLICATE-TYPE", s.name_span.t()).at(idx).act(&s.name);
                self.push(d);
            }
            if !s.type_params.is_empty() {
                let d = Diagnostic::error("name", "E-REC-TYPE-PARAM", s.name_span.t()).at(idx).exp("a recursive type without type parameters").act(&s.name).fix(
                    "replace_type",
                    s.name_span.t(),
                    format!("{} without type parameters: generic recursive types are not supported yet", s.name),
                );
                self.push(d);
            }
            let mut variants = vec![];
            for (k, v) in s.variants.iter().enumerate() {
                let generic = !s.type_params.is_empty();
                if ctor_count[v.name.as_str()] > 1 {
                    let d = Diagnostic::error("name", "E-SUM-DUPLICATE-CTOR", v.name_span.t()).at(idx).act(&v.name).fix(
                        "replace_identifier",
                        v.name_span.t(),
                        "constructor name not used by any other variant in the program".to_string(),
                    );
                    self.push(d);
                } else if fn_names.contains(v.name.as_str()) || type_count.contains_key(v.name.as_str()) {
                    let what = if fn_names.contains(v.name.as_str()) { "function" } else { "type" };
                    let d = Diagnostic::error("name", "E-SUM-NAME-CONFLICT", v.name_span.t()).at(idx).act(&v.name).fix(
                        "replace_identifier",
                        v.name_span.t(),
                        format!("constructor name different from the {what} {}", v.name),
                    );
                    self.push(d);
                }
                let mut kinds = vec![];
                for f in &v.fields {
                    match kind_of(f, &self.rec) {
                        Some(kd) => kinds.push(kd),
                        None if generic => kinds.push(Kind::Int),
                        None => {
                            let d = Diagnostic::error("name", "E-REC-FIELD-TYPE", f.meta.span())
                                .at(f.meta.index)
                                .exp("Int, Bool, or a recursive type")
                                .act(format_type(f))
                                .fix(
                                    "replace_type",
                                    f.meta.span(),
                                    "Int, Bool, or the recursive type itself (String, List, records and other sum types are not supported in a constructor of a recursive type yet)"
                                        .to_string(),
                                );
                            self.push(d);
                            kinds.push(Kind::Int);
                        }
                    }
                }
                let sig = if v.fields.is_empty() {
                    v.name.clone()
                } else {
                    format!("{}({})", v.name, v.fields.iter().map(format_type).collect::<Vec<_>>().join(", "))
                };
                let func = self.name(&format!("{}_new", v.name.to_ascii_lowercase()));
                self.ctors.entry(v.name.clone()).or_insert_with(|| (s.name.clone(), k));
                variants.push(Variant { name: v.name.clone(), kinds, sig, func, meta: s.meta, span: v.name_span });
            }
            self.tys.insert(s.name.clone(), variants.clone());
            for (k, v) in variants.iter().enumerate() {
                let f = self.ctor_fn(v, k);
                self.fns.push(f);
            }
        }
    }

    /// 式と宣言の名前（束縛と引数）が、再帰する型の構築子の名前と重ならないこと（sums と同じ診断）。
    fn binder_conflicts(&mut self, p: &Program) {
        fn walk(e: &Expr, out: &mut Vec<(String, Sp, usize)>) {
            let i = e.meta.index;
            match &e.kind {
                ExprKind::Let { name, name_span, .. } | ExprKind::Hof { binder: name, binder_span: name_span, .. } => {
                    out.push((name.clone(), *name_span, i));
                }
                ExprKind::Loop { binder, binder_span, .. } | ExprKind::Match { binder, binder_span, .. } => {
                    out.push((binder.clone(), *binder_span, i));
                }
                ExprKind::Fold { acc, acc_span, item, item_span, .. } => {
                    out.push((acc.clone(), *acc_span, i));
                    out.push((item.clone(), *item_span, i));
                }
                ExprKind::MatchResult { ok_binder, ok_span, err_binder, err_span, .. } => {
                    out.push((ok_binder.clone(), *ok_span, i));
                    out.push((err_binder.clone(), *err_span, i));
                }
                ExprKind::SumMatch { arms, .. } => {
                    for a in arms {
                        for (b, sp) in a.pat.binds.iter().filter(|(b, _)| b != "_") {
                            out.push((b.clone(), *sp, i));
                        }
                    }
                }
                _ => {}
            }
            for c in e.children() {
                walk(c, out);
            }
        }
        let mut found: Vec<(String, Sp, usize)> = vec![];
        for f in p.functions() {
            for q in &f.params {
                found.push((q.name.clone(), q.name_span, q.meta.index));
            }
            walk(&f.body, &mut found);
        }
        for (name, sp, i) in found {
            if self.ctors.contains_key(&name) {
                let d = Diagnostic::error("name", "E-SUM-NAME-CONFLICT", sp.t()).at(i).act(&name).fix(
                    "replace_identifier",
                    sp.t(),
                    format!("name different from the constructor {name} (constructors, functions, variables and types share one namespace)"),
                );
                self.push(d);
            }
        }
    }

    /// 構築子 `v`（項の番号 `k`）の関数：`[k] ++ [1, x]`（Int）、`[1, b]`（Bool）、`[長さ] ++ 値`（再帰する型）を連結する。
    fn ctor_fn(&mut self, v: &Variant, k: usize) -> FnDecl {
        let m = v.meta;
        let base = v.name.to_ascii_lowercase();
        let mut params = vec![];
        let mut args = vec![];
        for (i, kd) in v.kinds.iter().enumerate() {
            let pn = self.name(&format!("{base}_arg{}", i + 1));
            let ty = match kd {
                Kind::Int => int_node(m),
                Kind::Bool => TypeNode::new(TyTag::Bool, vec![], m),
                Kind::Rec => list_int_node(m),
            };
            args.push(var(&pn, m));
            params.push((pn, ty));
        }
        let blocks: Vec<Expr> = v
            .kinds
            .iter()
            .zip(&args)
            .map(|(kd, a)| match kd {
                Kind::Int => list(vec![int(1, m), a.clone()], m),
                Kind::Bool => list(vec![int(1, m), if_(a.clone(), int(1, m), int(0, m), m)], m),
                Kind::Rec => builtin("concat", vec![list(vec![builtin("length", vec![a.clone()], m)], m), a.clone()], m),
            })
            .collect();
        let mut rest: Option<Expr> = None;
        for b in blocks.into_iter().rev() {
            rest = Some(match rest {
                None => b,
                Some(r) => builtin("concat", vec![b, r], m),
            });
        }
        let tag = list(vec![int(k, m)], m);
        let body = match rest {
            None => tag,
            Some(r) => builtin("concat", vec![tag, r], m),
        };
        let mut f = func(&v.func, params, list_int_node(m), body, m);
        f.name_span = v.span;
        f.ctor = Some(v.name.clone());
        f
    }

    /// 補助関数：`rec_drop(xs, n)` は先頭の n 個を除いた残り、`rec_take(xs, n)` は先頭の n 個、
    /// `rec_at(xs, i)` は i 番目（0 から。範囲外は 0）。どれも `fold` と組み込みの関数だけで書く。
    fn helpers(&mut self) {
        let m = Meta::default();
        let (drop, take, at) = (self.drop.clone(), self.take.clone(), self.at.clone());
        // rec_drop
        let (xs, n, acc, item) = (self.name("xs"), self.name("n"), self.name("acc"), self.name("item"));
        let step = if_(
            builtin("lt", vec![builtin("fst", vec![var(&acc, m)], m), var(&n, m)], m),
            pair(builtin("add", vec![builtin("fst", vec![var(&acc, m)], m), int(1, m)], m), builtin("snd", vec![var(&acc, m)], m), m),
            pair(
                builtin("fst", vec![var(&acc, m)], m),
                builtin("cons", vec![var(&item, m), builtin("snd", vec![var(&acc, m)], m)], m),
                m,
            ),
            m,
        );
        let folded = fold(var(&xs, m), pair(int(0, m), list(vec![], m), m), &acc, &item, step, m);
        let body = builtin("reverse", vec![builtin("snd", vec![folded], m)], m);
        let f = func(&drop, vec![(xs, list_int_node(m)), (n, int_node(m))], list_int_node(m), body, m);
        self.fns.push(f);
        // rec_take
        let (xs, n, acc, item) = (self.name("xs"), self.name("n"), self.name("acc"), self.name("item"));
        let step = if_(
            builtin("lt", vec![builtin("fst", vec![var(&acc, m)], m), var(&n, m)], m),
            pair(
                builtin("add", vec![builtin("fst", vec![var(&acc, m)], m), int(1, m)], m),
                builtin("cons", vec![var(&item, m), builtin("snd", vec![var(&acc, m)], m)], m),
                m,
            ),
            var(&acc, m),
            m,
        );
        let folded = fold(var(&xs, m), pair(int(0, m), list(vec![], m), m), &acc, &item, step, m);
        let body = builtin("reverse", vec![builtin("snd", vec![folded], m)], m);
        let f = func(&take, vec![(xs, list_int_node(m)), (n, int_node(m))], list_int_node(m), body, m);
        self.fns.push(f);
        // rec_at
        let (xs, i, acc, item) = (self.name("xs"), self.name("i"), self.name("acc"), self.name("item"));
        let one = call(&take, vec![call(&drop, vec![var(&xs, m), var(&i, m)], m), int(1, m)], m);
        let body = fold(one, int(0, m), &acc, &item, var(&item, m), m);
        let f = func(&at, vec![(xs, list_int_node(m)), (i, int_node(m))], int_node(m), body, m);
        self.fns.push(f);
    }

    /// 再帰する型の node を `List<Int>` に置き換える（型引数は書けない）。
    fn rty(&mut self, t: &TypeNode) -> TypeNode {
        if t.tag != TyTag::Param {
            if let Some(n) = &t.name {
                if self.rec.contains(n) {
                    if !t.args.is_empty() {
                        arity_error(&mut self.diags, n, &[], t.args.len(), t.meta);
                    }
                    return list_int_node(t.meta);
                }
            }
        }
        let args = t.args.iter().map(|a| self.rty(a)).collect();
        TypeNode { args, ..t.clone() }
    }

    fn rec_arm(&self, a: &Arm) -> bool {
        matches!(&a.pat.kind, PatKind::Ctor(c) if self.ctors.contains_key(c))
    }

    fn expr(&mut self, e: &Expr) -> Expr {
        let m = e.meta;
        match &e.kind {
            ExprKind::Var(n) if self.ctors.contains_key(n) => {
                let (ty, k) = self.ctors[n].clone();
                if !self.tys[&ty][k].kinds.is_empty() {
                    self.arity(n, 0, false, m.span.t(), m.index, false);
                    return ex(ExprKind::Unit, m);
                }
                list(vec![int(k, m)], m)
            }
            ExprKind::Call { callee, args, builtin: false, callee_span, type_args } if self.ctors.contains_key(callee) => {
                let args: Vec<Expr> = args.iter().map(|a| self.expr(a)).collect();
                let (ty, k) = self.ctors[callee].clone();
                let fm = self.tys[&ty][k].kinds.len();
                if !type_args.is_empty() {
                    arity_error(&mut self.diags, &ty, &[], type_args.len(), m);
                    return ex(ExprKind::Unit, m);
                }
                if fm == 0 || args.len() != fm {
                    self.arity(callee, args.len(), true, (callee_span.0, m.span.1), m.index, false);
                    return ex(ExprKind::Unit, m);
                }
                let func = self.tys[&ty][k].func.clone();
                ex(ExprKind::Call { callee: func, args, builtin: false, callee_span: *callee_span, type_args: vec![] }, m)
            }
            ExprKind::SumMatch { scrutinee, arms, kw_span, close_span, .. } if arms.iter().any(|a| self.rec_arm(a)) => {
                self.sum_match(e, scrutinee, arms, *kw_span, *close_span)
            }
            _ => {
                let mut out = e.clone();
                match &mut out.kind {
                    ExprKind::List { element_type: t, .. }
                    | ExprKind::None(t)
                    | ExprKind::DictNew(t)
                    | ExprKind::Inj { ty: t, .. } => {
                        let new = self.rty(t);
                        *t = new;
                    }
                    ExprKind::Call { type_args, .. } => {
                        for t in type_args.iter_mut() {
                            let new = self.rty(t);
                            *t = new;
                        }
                    }
                    _ => {}
                }
                for c in out.children_mut() {
                    let new = self.expr(c);
                    *c = new;
                }
                out
            }
        }
    }

    /// 構築子の引数の個数の誤り（sums と同じ診断）。
    fn arity(&mut self, ctor: &str, given: usize, parens: bool, span: (usize, usize), index: usize, pattern: bool) {
        let (ty, k) = self.ctors[ctor].clone();
        let v = &self.tys[&ty][k];
        let (fm, sig) = (v.kinds.len(), v.sig.clone());
        let fix = if fm == 0 {
            format!("{ctor} has no fields: write it without parentheses")
        } else if pattern {
            format!("{} (one name or _ per field of {sig})", pattern_text(ctor, fm))
        } else {
            format!("{ctor}(...) with {fm} argument(s), as declared: {sig}")
        };
        let act = if fm == 0 && parens { "parentheses".to_string() } else { format!("{given} fields") };
        let d = Diagnostic::error("name", "E-SUM-CTOR-ARITY", span).at(index).exp(format!("{fm} fields")).act(act).fix("replace_expression", span, fix);
        self.push(d);
    }

    fn unreachable(&mut self, span: (usize, usize), index: usize) {
        let d = Diagnostic::error("name", "E-MATCH-UNREACHABLE", span).at(index).fix(
            "delete_span",
            span,
            "delete this arm: the arms before it already cover every case it could match",
        );
        self.push(d);
    }

    /// 再帰する型の `match` を、番号による `if` の連鎖に書き換える。
    fn sum_match(&mut self, e: &Expr, scrut: &Expr, arms: &[Arm], kw: Sp, close: Sp) -> Expr {
        let m = e.meta;
        let before = self.diags.len();
        let scrut = self.expr(scrut);
        let Some(ty) = arms.iter().find_map(|a| match &a.pat.kind {
            PatKind::Ctor(c) => self.ctors.get(c).map(|(t, _)| t.clone()),
            _ => None,
        }) else {
            return ex(ExprKind::Unit, m);
        };
        let variants: Vec<(String, usize)> = self.tys[&ty].iter().map(|v| (v.name.clone(), v.kinds.len())).collect();
        let names: Vec<String> = variants.iter().map(|(n, fm)| pattern_text(n, *fm)).collect();
        let mut done = vec![false; variants.len()];
        let mut wild: Option<usize> = None;
        let mut plan: Vec<(usize, usize)> = vec![];
        for (i, a) in arms.iter().enumerate() {
            let p = &a.pat;
            if wild.is_some() {
                self.unreachable(a.span.t(), m.index);
                continue;
            }
            match &p.kind {
                PatKind::Wild => {
                    if !done.is_empty() && done.iter().all(|d| *d) {
                        self.unreachable(a.span.t(), m.index);
                    } else {
                        wild = Some(i);
                    }
                }
                PatKind::Ctor(c) if self.ctors.get(c).is_some_and(|(t, _)| *t == ty) => {
                    let k = self.ctors[c].1;
                    if done[k] {
                        let d = Diagnostic::error("name", "E-MATCH-DUPLICATE", a.span.t()).at(m.index).act(names[k].clone()).fix(
                            "delete_span",
                            a.span.t(),
                            format!("delete this arm: an earlier arm already handles {}", names[k]),
                        );
                        self.push(d);
                    } else {
                        let fm = variants[k].1;
                        if (fm == 0 && p.parens) || (fm > 0 && p.binds.len() != fm) {
                            self.arity(c, p.binds.len(), p.parens, p.span.t(), m.index, true);
                        }
                        done[k] = true;
                        plan.push((k, i));
                    }
                }
                _ => {
                    let (act, fix) = match &p.kind {
                        PatKind::Ctor(c) if self.ctors.contains_key(c) => {
                            (c.clone(), format!("pattern for the same type as the first arm: constructor of {ty}"))
                        }
                        PatKind::Ctor(c) => (c.clone(), format!("declared constructor of {ty}: {}", names.join(", "))),
                        PatKind::Ok => ("ok(..)".into(), format!("pattern for the same type as the first arm: constructor of {ty}")),
                        PatKind::Err => ("err(..)".into(), format!("pattern for the same type as the first arm: constructor of {ty}")),
                        PatKind::Some => ("some(..)".into(), format!("pattern for the same type as the first arm: constructor of {ty}")),
                        PatKind::None => ("none".into(), format!("pattern for the same type as the first arm: constructor of {ty}")),
                        PatKind::Wild => unreachable!("wildcard arms are handled above"),
                    };
                    let d = if matches!(&p.kind, PatKind::Ctor(c) if !self.all_ctors.contains(c)) {
                        Diagnostic::error("name", "E-SUM-UNKNOWN-CTOR", p.span.t()).at(m.index).act(act).fix("replace_identifier", p.span.t(), fix)
                    } else {
                        Diagnostic::error("name", "E-MATCH-MIXED", p.span.t()).at(m.index).exp(format!("constructor of {ty}")).act(act).fix(
                            "replace_expression",
                            p.span.t(),
                            fix,
                        )
                    };
                    self.push(d);
                }
            }
        }
        if self.diags.len() == before && wild.is_none() {
            let missing: Vec<String> = names.iter().zip(&done).filter(|(_, d)| !**d).map(|(n, _)| n.clone()).collect();
            if !missing.is_empty() {
                let arms_text: Vec<String> = missing.iter().map(|p| format!("{p} => ...")).collect();
                let d = Diagnostic::error("name", "E-MATCH-MISSING", kw.t()).at(m.index).exp(missing.join(", ")).fix(
                    "insert_text",
                    (close.0, close.0),
                    format!("arms for the missing cases, inserted before '}}': `, {}` (or one final `_ => ...`)", arms_text.join(", ")),
                );
                self.push(d);
            }
        }
        // 枝の本体（束縛は枝の中だけで見える）
        let sv = self.name("scrut");
        let tv = self.name("tag");
        let mut tests: Vec<(usize, Expr)> = vec![];
        for (k, i) in plan {
            let body = self.arm(&ty, k, &arms[i], &sv, m);
            tests.push((k, body));
        }
        let default = match wild {
            Some(i) => self.expr(&arms[i].body),
            None => tests.pop().map(|(_, b)| b).unwrap_or_else(|| ex(ExprKind::Unit, m)),
        };
        if self.diags.len() > before {
            return ex(ExprKind::Unit, m);
        }
        let mut out = default;
        for (k, body) in tests.into_iter().rev() {
            let c = builtin("eq", vec![var(&tv, m), int(k, m)], m);
            out = if_(c, body, out, m);
        }
        let head = call(&self.at.clone(), vec![var(&sv, m), int(0, m)], m);
        let out = let_(&tv, m.span, head, out, m);
        let_(&sv, m.span, scrut, out, m)
    }

    /// 項 `k` の枝の本体。項の中身を、長さの前置きに従って順に取り出して束縛し、その中で `body` を書く。
    fn arm(&mut self, ty: &str, k: usize, a: &Arm, sv: &str, m: Meta) -> Expr {
        let kinds = self.tys[ty][k].kinds.clone();
        let body = self.expr(&a.body);
        let n = kinds.len();
        let mut lets: Vec<(String, Sp, Expr)> = vec![];
        if n > 0 {
            let (drop, take, at) = (self.drop.clone(), self.take.clone(), self.at.clone());
            let mut rest = self.name("rest");
            lets.push((rest.clone(), m.span, call(&drop, vec![var(sv, m), int(1, m)], m)));
            for j in 0..n {
                let (bind, bind_span) = a.pat.binds.get(j).cloned().unwrap_or_else(|| ("_".to_string(), Sp::default()));
                let want = bind != "_";
                if !want && j + 1 == n {
                    break;
                }
                let len = self.name("len");
                lets.push((len.clone(), m.span, call(&at, vec![var(&rest, m), int(0, m)], m)));
                if want {
                    let data = self.name("data");
                    let inner = call(&drop, vec![var(&rest, m), int(1, m)], m);
                    lets.push((data.clone(), m.span, call(&take, vec![inner, var(&len, m)], m)));
                    let value = match kinds[j] {
                        Kind::Int => call(&at, vec![var(&data, m), int(0, m)], m),
                        Kind::Bool => builtin("eq", vec![call(&at, vec![var(&data, m), int(0, m)], m), int(1, m)], m),
                        Kind::Rec => var(&data, m),
                    };
                    lets.push((bind, bind_span, value));
                }
                if j + 1 < n {
                    let next = self.name("rest");
                    let skip = builtin("add", vec![int(1, m), var(&len, m)], m);
                    lets.push((next.clone(), m.span, call(&drop, vec![var(&rest, m), skip], m)));
                    rest = next;
                }
            }
        }
        let mut out = body;
        for (name, span, value) in lets.into_iter().rev() {
            out = let_(&name, span, value, out, m);
        }
        out
    }
}
