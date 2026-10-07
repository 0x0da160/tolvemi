//! v1.1 のレコード型（差分仕様 §1b）。
//!
//! `type Name = { f1: T1, ..., fn: Tn }` は field の型を右に入れ子にした pair の型の別名である
//! （n = 1 なら T1 そのもの）。構築 `Name { ... }` は pair の入れ子に、参照 `e.f` は `fst`／`snd` の
//! 並びに書き換える。型の等価性は展開後の構造で決まり、レコード名は表示と plain JSON にだけ使う。
//!
//! 書き換えは検証されていない接着部分（`trust-boundary.toml` の `glue`）。検証済み部品は
//! 書き換え後のプログラム（`lower` の結果を整形したソース）を検査・実行する。

use crate::diagnostics::{closest, Diagnostic};
use crate::syntax::*;
use std::collections::{HashMap, HashSet};
use std::sync::Arc;

/// レコードの構文（型宣言、型名、構築、field の参照）を一つでも含むか。
pub fn has_records(p: &Program) -> bool {
    fn ty(t: &TypeNode) -> bool {
        t.name.is_some() || t.args.iter().any(ty)
    }
    fn ex(e: &Expr) -> bool {
        match &e.kind {
            ExprKind::Record { .. } | ExprKind::Field { .. } => true,
            ExprKind::List { element_type, .. } if ty(element_type) => true,
            ExprKind::None(t) if ty(t) => true,
            _ => e.children().into_iter().any(ex),
        }
    }
    p.declarations.iter().any(|d| match d {
        Decl::Type(_) => true,
        Decl::Fn(f) => f.params.iter().any(|p| ty(&p.ty)) || ty(&f.return_type) || ex(&f.body),
        Decl::Entry(_) => false,
    })
}

struct Rec {
    info: Arc<RecordInfo>,
    /// 展開後の型（レコード名付き）
    ty: TypeNode,
}

struct Env {
    types: HashMap<String, Rec>,
    /// field 名 → レコード名（field 名はプログラム全体で一意）
    owner: HashMap<String, String>,
    diags: Vec<Diagnostic>,
    /// 書き換えで導入する変数名の候補を避けるための、プログラム中の全識別子
    idents: HashSet<String>,
    fresh: usize,
}

/// 展開後のレコード型：field の型を右に入れ子にした pair（n = 1 ならその型）にレコード名を付ける。
fn record_type(fields: &[TypeNode], label: Label, meta: Meta) -> TypeNode {
    let mut t = fields[fields.len() - 1].clone();
    for f in fields[..fields.len() - 1].iter().rev() {
        t = TypeNode::new(TyTag::Pair, vec![f.clone(), t], meta);
    }
    t.label = label;
    t
}

impl Env {
    fn err(&mut self, code: &'static str, span: (usize, usize), index: usize) -> &mut Diagnostic {
        self.diags.push(Diagnostic::error("name", code, span).at(index));
        self.diags.last_mut().unwrap()
    }

    /// 型の中のレコード名を展開する。
    fn ty(&mut self, t: &TypeNode) -> TypeNode {
        if let Some(n) = &t.name {
            return match self.types.get(n) {
                Some(r) => {
                    let mut x = r.ty.clone();
                    x.meta = t.meta;
                    x
                }
                None => {
                    let near = closest(n, self.types.keys().map(|k| k.as_str()), 3);
                    let fix = if near.is_empty() {
                        "a type declared above with `type Name = { field: Type, ... }`".to_string()
                    } else {
                        format!("record type declared above, e.g. {}", near.join(", "))
                    };
                    let d = self.err("E-RECORD-UNKNOWN-TYPE", t.meta.span(), t.meta.index);
                    *d = d.clone().act(n).fix("replace_type", t.meta.span(), fix);
                    TypeNode::new(TyTag::Unit, vec![], t.meta)
                }
            };
        }
        TypeNode { args: t.args.iter().map(|a| self.ty(a)).collect(), ..t.clone() }
    }

    fn fresh_name(&mut self) -> String {
        loop {
            self.fresh += 1;
            let n = format!("rec{}", self.fresh);
            if !self.idents.contains(&n) {
                self.idents.insert(n.clone());
                return n;
            }
        }
    }

    fn field_access(&mut self, base: Expr, rec: &str, i: usize, meta: Meta, span: Sp) -> Expr {
        let r = &self.types[rec];
        let n = r.info.fields.len();
        Expr {
            kind: ExprKind::Field {
                expr: Box::new(base),
                field: r.info.fields[i].clone(),
                field_span: span,
                target: Some((r.ty.clone(), i, n)),
            },
            meta,
        }
    }

    fn expr(&mut self, e: &Expr) -> Expr {
        let m = e.meta;
        let kind = match &e.kind {
            ExprKind::List { element_type, items } => {
                ExprKind::List { element_type: self.ty(element_type), items: items.iter().map(|x| self.expr(x)).collect() }
            }
            ExprKind::None(t) => ExprKind::None(self.ty(t)),
            ExprKind::Some(v) => ExprKind::Some(Box::new(self.expr(v))),
            ExprKind::Pair(a, b) => ExprKind::Pair(Box::new(self.expr(a)), Box::new(self.expr(b))),
            ExprKind::Call { callee, args, builtin, callee_span } => ExprKind::Call {
                callee: callee.clone(),
                args: args.iter().map(|x| self.expr(x)).collect(),
                builtin: *builtin,
                callee_span: *callee_span,
            },
            ExprKind::Let { name, name_span, value, body } => ExprKind::Let {
                name: name.clone(),
                name_span: *name_span,
                value: Box::new(self.expr(value)),
                body: Box::new(self.expr(body)),
            },
            ExprKind::If(c, t, f) => ExprKind::If(Box::new(self.expr(c)), Box::new(self.expr(t)), Box::new(self.expr(f))),
            ExprKind::Fold { list, init, acc, acc_span, item, item_span, body } => ExprKind::Fold {
                list: Box::new(self.expr(list)),
                init: Box::new(self.expr(init)),
                acc: acc.clone(),
                acc_span: *acc_span,
                item: item.clone(),
                item_span: *item_span,
                body: Box::new(self.expr(body)),
            },
            ExprKind::Match { scrutinee, on_none, binder, binder_span, on_some } => ExprKind::Match {
                scrutinee: Box::new(self.expr(scrutinee)),
                on_none: Box::new(self.expr(on_none)),
                binder: binder.clone(),
                binder_span: *binder_span,
                on_some: Box::new(self.expr(on_some)),
            },
            ExprKind::Field { expr, field, field_span, .. } => {
                let inner = self.expr(expr);
                match self.owner.get(field).cloned() {
                    Some(rec) => {
                        let i = self.types[&rec].info.fields.iter().position(|f| f == field).unwrap();
                        return self.field_access(inner, &rec, i, m, *field_span);
                    }
                    None => {
                        let near = closest(field, self.owner.keys().map(|k| k.as_str()), 3);
                        let fix = if near.is_empty() {
                            "a field of a declared record type".to_string()
                        } else {
                            format!("declared field, e.g. {}", near.join(", "))
                        };
                        let d = self.err("E-RECORD-UNKNOWN-FIELD", field_span.t(), m.index);
                        *d = d.clone().act(field).fix("replace_identifier", field_span.t(), fix);
                        return inner;
                    }
                }
            }
            ExprKind::Record { name, name_span, fields, base } => return self.record(e, name, *name_span, fields, base),
            k => k.clone(),
        };
        Expr { kind, meta: m }
    }

    fn record(&mut self, e: &Expr, name: &str, name_span: Sp, fields: &[RecordField], base: &Option<Box<Expr>>) -> Expr {
        let m = e.meta;
        let unit = Expr { kind: ExprKind::Unit, meta: m };
        let Some(r) = self.types.get(name) else {
            let near = closest(name, self.types.keys().map(|k| k.as_str()), 3);
            let fix = if near.is_empty() {
                "a type declared above with `type Name = { field: Type, ... }`".to_string()
            } else {
                format!("record type declared above, e.g. {}", near.join(", "))
            };
            let d = self.err("E-RECORD-UNKNOWN-TYPE", name_span.t(), m.index);
            *d = d.clone().act(name).fix("replace_identifier", name_span.t(), fix);
            return unit;
        };
        let names = r.info.fields.clone();
        let mut given: Vec<Option<Expr>> = vec![None; names.len()];
        for f in fields {
            let v = self.expr(&f.value);
            match names.iter().position(|n| *n == f.name) {
                Some(i) if given[i].is_some() => {
                    let d = self.err("E-RECORD-DUPLICATE-FIELD", f.name_span.t(), m.index);
                    *d = d.clone().act(&f.name);
                }
                Some(i) => given[i] = Some(v),
                None => {
                    let fix = format!("field of {name}: {}", names.join(", "));
                    let d = self.err("E-RECORD-UNKNOWN-FIELD", f.name_span.t(), m.index);
                    *d = d.clone().act(&f.name).fix("replace_identifier", f.name_span.t(), fix);
                }
            }
        }
        // `..base` は書かれていない field を base から取る。base が変数でなければ let で一度だけ評価する
        let mut wrap: Option<(String, Sp, Expr)> = None;
        let base_expr = base.as_ref().map(|b| {
            let bx = self.expr(b);
            if matches!(bx.kind, ExprKind::Var(_)) || given.iter().filter(|g| g.is_none()).count() <= 1 {
                bx
            } else {
                let v = self.fresh_name();
                let var = Expr { kind: ExprKind::Var(v.clone()), meta: bx.meta };
                wrap = Some((v, Sp(bx.meta.span().0, bx.meta.span().0), bx));
                var
            }
        });
        let missing: Vec<&str> = names.iter().zip(&given).filter(|(_, g)| g.is_none()).map(|(n, _)| n.as_str()).collect();
        if base_expr.is_none() && !missing.is_empty() {
            let list = missing.join(", ");
            let d = self.err("E-RECORD-MISSING-FIELD", name_span.t(), m.index);
            *d = d.clone().exp(&list).fix(
                "replace_expression",
                m.span(),
                format!("{name} {{ ... }} with every field ({}), or `..base` to copy the rest", names.join(", ")),
            );
            return unit;
        }
        let mut vals: Vec<Expr> = vec![];
        for (i, g) in given.into_iter().enumerate() {
            vals.push(match g {
                Some(v) => v,
                None => {
                    let b = base_expr.clone().unwrap();
                    let bm = b.meta;
                    self.field_access(b, name, i, bm, Sp(bm.span().0, bm.span().1))
                }
            });
        }
        let mut out = vals.pop().unwrap();
        while let Some(v) = vals.pop() {
            out = Expr { kind: ExprKind::Pair(Box::new(v), Box::new(out)), meta: m };
        }
        if let Some((v, sp, value)) = wrap {
            out = Expr { kind: ExprKind::Let { name: v, name_span: sp, value: Box::new(value), body: Box::new(out) }, meta: m };
        }
        out
    }
}

fn collect_idents(p: &Program, out: &mut HashSet<String>) {
    fn ex(e: &Expr, out: &mut HashSet<String>) {
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
            ExprKind::Match { binder, .. } => {
                out.insert(binder.clone());
            }
            ExprKind::Call { callee, .. } => {
                out.insert(callee.clone());
            }
            _ => {}
        }
        for c in e.children() {
            ex(c, out);
        }
    }
    for d in &p.declarations {
        if let Decl::Fn(f) = d {
            out.insert(f.name.clone());
            for p in &f.params {
                out.insert(p.name.clone());
            }
            ex(&f.body, out);
        }
    }
}

/// レコードの構文を展開する。型宣言を除き、型名を展開後の型に、構築を pair の入れ子に置き換え、
/// field の参照に位置を付ける（`ExprKind::Field` は型検査器が検査し、`lower` が fst／snd にする）。
pub fn expand(p: &Program) -> Result<Program, Vec<Diagnostic>> {
    let mut env = Env { types: HashMap::new(), owner: HashMap::new(), diags: vec![], idents: HashSet::new(), fresh: 0 };
    collect_idents(p, &mut env.idents);
    for d in &p.declarations {
        let Decl::Type(t) = d else { continue };
        let idx = t.meta.index;
        if env.types.contains_key(&t.name) {
            let d = env.err("E-RECORD-DUPLICATE-TYPE", t.name_span.t(), idx);
            *d = d.clone().act(&t.name);
            continue;
        }
        let mut names: Vec<String> = vec![];
        let mut tys = vec![];
        for f in &t.fields {
            // field の型には、この宣言より前に宣言したレコード型だけを書ける（再帰型を作らない）
            tys.push(env.ty(&f.ty));
            if names.contains(&f.name) {
                let d = env.err("E-RECORD-DUPLICATE-FIELD", f.name_span.t(), idx);
                *d = d.clone().act(&f.name);
            } else if let Some(other) = env.owner.get(&f.name).cloned() {
                let d = env.err("E-RECORD-FIELD-CONFLICT", f.name_span.t(), idx);
                *d = d.clone().act(&f.name).fix(
                    "replace_identifier",
                    f.name_span.t(),
                    format!("field name not used by another record type ('{}' is a field of {other})", f.name),
                );
            }
            names.push(f.name.clone());
        }
        for n in &names {
            env.owner.entry(n.clone()).or_insert_with(|| t.name.clone());
        }
        let info = Arc::new(RecordInfo { name: t.name.clone(), fields: names });
        let ty = record_type(&tys, Label(Some(info.clone())), t.meta);
        env.types.insert(t.name.clone(), Rec { info, ty });
    }
    let mut decls = vec![];
    for d in &p.declarations {
        match d {
            Decl::Type(_) => {}
            Decl::Entry(e) => decls.push(Decl::Entry(e.clone())),
            Decl::Fn(f) => {
                let params = f.params.iter().map(|p| Param { ty: env.ty(&p.ty), ..p.clone() }).collect();
                let return_type = env.ty(&f.return_type);
                let body = env.expr(&f.body);
                decls.push(Decl::Fn(FnDecl { params, return_type, body, ..f.clone() }));
            }
        }
    }
    if env.diags.is_empty() {
        Ok(Program { declarations: decls, meta: p.meta })
    } else {
        Err(env.diags)
    }
}

/// field の参照を `fst`／`snd` の並びに、レコード名付きの型を素の型にする（検証済み部品へ渡すソース用）。
pub fn lower(p: &Program) -> Program {
    fn ex(e: &Expr) -> Expr {
        let m = e.meta;
        if let ExprKind::Field { expr, field_span, target: Some((_, i, n)), .. } = &e.kind {
            let call = |name: &str, arg: Expr| Expr {
                kind: ExprKind::Call { callee: name.into(), args: vec![arg], builtin: true, callee_span: *field_span },
                meta: m,
            };
            let mut x = ex(expr);
            for _ in 0..*i {
                x = call("snd", x);
            }
            if i + 1 < *n {
                x = call("fst", x);
            }
            return x;
        }
        let mut out = e.clone();
        match &mut out.kind {
            ExprKind::List { items, .. } => items.iter_mut().for_each(|x| *x = ex(x)),
            ExprKind::Some(v) => **v = ex(v),
            ExprKind::Pair(a, b) => {
                **a = ex(a);
                **b = ex(b);
            }
            ExprKind::Call { args, .. } => args.iter_mut().for_each(|x| *x = ex(x)),
            ExprKind::Let { value, body, .. } => {
                **value = ex(value);
                **body = ex(body);
            }
            ExprKind::If(c, t, f) => {
                **c = ex(c);
                **t = ex(t);
                **f = ex(f);
            }
            ExprKind::Fold { list, init, body, .. } => {
                **list = ex(list);
                **init = ex(init);
                **body = ex(body);
            }
            ExprKind::Match { scrutinee, on_none, on_some, .. } => {
                **scrutinee = ex(scrutinee);
                **on_none = ex(on_none);
                **on_some = ex(on_some);
            }
            _ => {}
        }
        out
    }
    let declarations = p
        .declarations
        .iter()
        .map(|d| match d {
            Decl::Fn(f) => Decl::Fn(FnDecl { body: ex(&f.body), ..f.clone() }),
            d => d.clone(),
        })
        .collect();
    Program { declarations, meta: p.meta }
}
