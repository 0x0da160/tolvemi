//! v1.1 のレコード型（差分仕様 §1b）。
//!
//! `type Name = { f1: T1, ..., fn: Tn }` は field の型を右に入れ子にした pair の型の別名である
//! （n = 1 なら T1 そのもの）。構築 `Name { ... }` は pair の入れ子に、参照 `e.f` は `fst`／`snd` の
//! 並びに書き換える。型の等価性は宣言で決まる（v1.15 の名義の型。宣言ごとの印は `nominal.rs`）。展開後の構造が
//! 同じでも宣言が違えば別の型で、レコード名は診断の文面と表示と plain JSON に使う。
//!
//! 書換えの判断は検証済み（`tlvm_verified::records_plan`）：字段の位置（`place_e`）、字段の参照の fst／snd の
//! 並び（`field_steps_e`）、構築の拒否と base の束縛（`record_mode_e`）。木の走査、型の展開、字段の名前の番号づけは
//! 検証されていない接着部分（`trust-boundary.toml` の `glue`）。検証済み部品は書き換え後のプログラム（`lower` の
//! 結果を整形したソース）を検査・実行する。

use crate::diagnostics::{closest, Diagnostic};
use crate::nominal::{self, Tags};
use crate::syntax::*;
use std::collections::{HashMap, HashSet};
use std::sync::Arc;
use tlvm_verified::records_plan::{field_steps_e, place_e, record_mode_e, RecMode};

/// レコードの構文（型宣言、型名、構築、field の参照）を一つでも含むか。
pub fn has_records(p: &Program) -> bool {
    fn ty(t: &TypeNode) -> bool {
        t.is_named() || t.args.iter().any(ty)
    }
    // 式の木は明示的な stack で見る（書換え後の深い木で再帰しない）
    fn ex(e: &Expr) -> bool {
        let mut stack = vec![e];
        while let Some(e) = stack.pop() {
            match &e.kind {
                ExprKind::Record { .. } | ExprKind::Field { .. } => return true,
                ExprKind::Call { type_args, .. } if type_args.iter().any(ty) => return true,
                ExprKind::List { element_type, .. } if ty(element_type) => return true,
                ExprKind::None(t) | ExprKind::Inj { ty: t, .. } | ExprKind::DictNew(t) if ty(t) => {
                    return true
                }
                _ => stack.extend(e.children()),
            }
        }
        false
    }
    p.declarations.iter().any(|d| match d {
        Decl::Type(_) => true,
        Decl::Fn(f) => f.params.iter().any(|p| ty(&p.ty)) || ty(&f.return_type) || ex(&f.body),
        Decl::Entry(_) | Decl::Sum(_) => false,
    })
}

struct Rec {
    info: Arc<RecordInfo>,
    /// 展開後の型（レコード名付き）。v1.10：総称のレコード型なら型引数（`TyTag::Param`）を含む
    ty: TypeNode,
    /// v1.10：型引数の名前（宣言順）
    params: Vec<String>,
    /// v1.15：印を付ける補助関数の名前（印つきの写しだけ）
    wrap: Option<String>,
    /// 字段の名前の番号（宣言の順）。`place_e` が位置を決める
    ids: Vec<usize>,
}

struct Env {
    types: HashMap<String, Rec>,
    /// field 名 → レコード名（field 名はプログラム全体で一意）
    owner: HashMap<String, String>,
    diags: Vec<Diagnostic>,
    /// 書き換えで導入する変数名の候補を避けるための、プログラム中の全識別子
    idents: HashSet<String>,
    fresh: usize,
    /// v1.15：名義の型の番号（印つきの写しだけ）と、印を付ける・外す補助関数の宣言
    tags: Option<Tags>,
    helpers: Vec<FnDecl>,
    /// 字段の名前の番号（同じ名前は同じ番号）
    names_id: HashMap<String, usize>,
}

/// レコード型・直和型の名前（展開前）を含むか。
fn has_named(t: &TypeNode) -> bool {
    t.is_named() || t.args.iter().any(has_named)
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
        self.diags
            .push(Diagnostic::error("name", code, span).at(index));
        self.diags.last_mut().unwrap()
    }

    /// 型の中のレコード名を展開する。
    fn ty(&mut self, t: &TypeNode) -> TypeNode {
        if t.tag == TyTag::Param {
            return t.clone();
        }
        if let Some(n) = &t.name {
            return match self.types.get(n) {
                Some(r) => {
                    // v1.10：総称のレコード型は型引数を置き換える（`Box<Int>`）
                    let (params, template) = (r.params.clone(), r.ty.clone());
                    let args: Vec<TypeNode> = t.args.iter().map(|a| self.ty(a)).collect();
                    if args.len() != params.len() {
                        crate::generics::arity_error(
                            &mut self.diags,
                            n,
                            &params,
                            args.len(),
                            t.meta,
                        );
                        return TypeNode::new(TyTag::Unit, vec![], t.meta);
                    }
                    let mut x = if params.is_empty() {
                        template
                    } else {
                        template
                            .subst(&|p| params.iter().position(|q| q == p).map(|i| args[i].clone()))
                    };
                    x.meta = t.meta;
                    // v1.4：中身が一つのレコードだけの直和型（`type W = W(P)`）は直和型の名前を保つ
                    // （レコード名は plain JSON 用に直和型の情報の側へ移す）
                    if let Some(Named::Sum(s)) = &t.label.0 {
                        let info = SumInfo {
                            name: s.name.clone(),
                            variants: s.variants.clone(),
                            inner: x.label.clone(),
                            generic: s.generic.as_ref().map(|g| self.generic(g)),
                            tagged: s.tagged,
                        };
                        x.label = Label(Some(Named::Sum(Arc::new(info))));
                    } else if t.label.0.is_some() {
                        x.label = t.label.clone();
                    }
                    x
                }
                None => {
                    let near = closest(n, self.types.keys().map(|k| k.as_str()), 3);
                    let fix = if near.is_empty() {
                        "a type declared above with `type Name = { field: Type, ... }`".to_string()
                    } else {
                        format!("record type declared above, e.g. {}", near.join(", "))
                    };
                    let fix = crate::generics::param_note(n, fix);
                    let d = self.err("E-RECORD-UNKNOWN-TYPE", t.meta.span(), t.meta.index);
                    *d = d.clone().act(n).fix("replace_type", t.meta.span(), fix);
                    TypeNode::new(TyTag::Unit, vec![], t.meta)
                }
            };
        }
        let mut out = TypeNode {
            args: t.args.iter().map(|a| self.ty(a)).collect(),
            ..t.clone()
        };
        // v1.10：総称の直和型の名前が持つ展開後の型（表示で型引数を復元する）の中のレコード型の名前も展開する
        if let Some(Named::Sum(s)) = &t.label.0 {
            if let Some(g) = s.generic.as_ref().filter(|g| has_named(&g.template)) {
                let generic = Some(self.generic(g));
                let info = SumInfo {
                    name: s.name.clone(),
                    variants: s.variants.clone(),
                    inner: s.inner.clone(),
                    generic,
                    tagged: s.tagged,
                };
                out.label = Label(Some(Named::Sum(Arc::new(info))));
            }
        }
        out
    }

    fn generic(&mut self, g: &Generic) -> Generic {
        Generic {
            params: g.params.clone(),
            template: self.ty(&g.template),
        }
    }

    /// v1.15：補助関数の名前（プログラム中の名前と重ならないもの）。
    fn name_of(&mut self, base: &str) -> String {
        crate::generics::fresh(&mut self.idents, base)
    }

    /// 字段の名前の番号。同じ名前は同じ番号を返す。
    fn intern(&mut self, name: &str) -> usize {
        let n = self.names_id.len();
        *self.names_id.entry(name.to_string()).or_insert(n)
    }

    /// レコード `rec` の字段 `field` の位置（宣言の順）。`place_e` が決める。
    fn position(&self, rec: &str, field: &str) -> Option<usize> {
        let f = *self.names_id.get(field)?;
        place_e(&self.types[rec].ids, f)
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
            ExprKind::List {
                element_type,
                items,
            } => ExprKind::List {
                element_type: self.ty(element_type),
                items: items.iter().map(|x| self.expr(x)).collect(),
            },
            ExprKind::None(t) => ExprKind::None(self.ty(t)),
            ExprKind::DictNew(t) => ExprKind::DictNew(self.ty(t)),
            ExprKind::Some(v) => ExprKind::Some(Box::new(self.expr(v))),
            ExprKind::Pair(a, b) => ExprKind::Pair(Box::new(self.expr(a)), Box::new(self.expr(b))),
            ExprKind::Call {
                callee,
                args,
                builtin,
                callee_span,
                type_args,
            } => ExprKind::Call {
                callee: callee.clone(),
                args: args.iter().map(|x| self.expr(x)).collect(),
                builtin: *builtin,
                callee_span: *callee_span,
                type_args: type_args.iter().map(|t| self.ty(t)).collect(),
            },
            ExprKind::Let {
                name,
                name_span,
                value,
                body,
            } => ExprKind::Let {
                name: name.clone(),
                name_span: *name_span,
                value: Box::new(self.expr(value)),
                body: Box::new(self.expr(body)),
            },
            ExprKind::If(c, t, f) => ExprKind::If(
                Box::new(self.expr(c)),
                Box::new(self.expr(t)),
                Box::new(self.expr(f)),
            ),
            ExprKind::Fold {
                list,
                init,
                acc,
                acc_span,
                item,
                item_span,
                body,
            } => ExprKind::Fold {
                list: Box::new(self.expr(list)),
                init: Box::new(self.expr(init)),
                acc: acc.clone(),
                acc_span: *acc_span,
                item: item.clone(),
                item_span: *item_span,
                body: Box::new(self.expr(body)),
            },
            ExprKind::Hof {
                op,
                list,
                binder,
                binder_span,
                body,
            } => ExprKind::Hof {
                op: *op,
                list: Box::new(self.expr(list)),
                binder: binder.clone(),
                binder_span: *binder_span,
                body: Box::new(self.expr(body)),
            },
            ExprKind::Loop {
                init,
                max,
                binder,
                binder_span,
                body,
            } => ExprKind::Loop {
                init: Box::new(self.expr(init)),
                max: Box::new(self.expr(max)),
                binder: binder.clone(),
                binder_span: *binder_span,
                body: Box::new(self.expr(body)),
            },
            ExprKind::Match {
                scrutinee,
                on_none,
                binder,
                binder_span,
                on_some,
            } => ExprKind::Match {
                scrutinee: Box::new(self.expr(scrutinee)),
                on_none: Box::new(self.expr(on_none)),
                binder: binder.clone(),
                binder_span: *binder_span,
                on_some: Box::new(self.expr(on_some)),
            },
            ExprKind::Field {
                expr,
                field,
                field_span,
                ..
            } => {
                let inner = self.expr(expr);
                match self.owner.get(field).cloned() {
                    Some(rec) => {
                        let i = self.position(&rec, field).unwrap();
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
                        *d = d
                            .clone()
                            .act(field)
                            .fix("replace_identifier", field_span.t(), fix);
                        return inner;
                    }
                }
            }
            ExprKind::Record {
                name,
                name_span,
                fields,
                base,
            } => return self.record(e, name, *name_span, fields, base),
            ExprKind::Inj { ok, ty, value } => ExprKind::Inj {
                ok: *ok,
                ty: self.ty(ty),
                value: Box::new(self.expr(value)),
            },
            ExprKind::MatchResult {
                scrutinee,
                ok_binder,
                ok_span,
                on_ok,
                err_binder,
                err_span,
                on_err,
            } => ExprKind::MatchResult {
                scrutinee: Box::new(self.expr(scrutinee)),
                ok_binder: ok_binder.clone(),
                ok_span: *ok_span,
                on_ok: Box::new(self.expr(on_ok)),
                err_binder: err_binder.clone(),
                err_span: *err_span,
                on_err: Box::new(self.expr(on_err)),
            },
            ExprKind::SumMatch {
                scrutinee,
                arms,
                kw_span,
                close_span,
                kind,
            } => ExprKind::SumMatch {
                scrutinee: Box::new(self.expr(scrutinee)),
                arms: arms
                    .iter()
                    .map(|a| Arm {
                        body: self.expr(&a.body),
                        ..a.clone()
                    })
                    .collect(),
                kw_span: *kw_span,
                close_span: *close_span,
                kind: kind.as_ref().map(|k| match k {
                    MatchKind::Sum { ty, fields } => MatchKind::Sum {
                        ty: self.ty(ty),
                        fields: fields
                            .iter()
                            .map(|fs| fs.iter().map(|f| self.ty(f)).collect())
                            .collect(),
                    },
                    k => k.clone(),
                }),
            },
            k => k.clone(),
        };
        Expr { kind, meta: m }
    }

    fn record(
        &mut self,
        e: &Expr,
        name: &str,
        name_span: Sp,
        fields: &[RecordField],
        base: &Option<Box<Expr>>,
    ) -> Expr {
        let m = e.meta;
        let unit = Expr {
            kind: ExprKind::Unit,
            meta: m,
        };
        let Some(r) = self.types.get(name) else {
            let near = closest(name, self.types.keys().map(|k| k.as_str()), 3);
            let fix = if near.is_empty() {
                "a type declared above with `type Name = { field: Type, ... }`".to_string()
            } else {
                format!("record type declared above, e.g. {}", near.join(", "))
            };
            let d = self.err("E-RECORD-UNKNOWN-TYPE", name_span.t(), m.index);
            *d = d
                .clone()
                .act(name)
                .fix("replace_identifier", name_span.t(), fix);
            return unit;
        };
        let names = r.info.fields.clone();
        let seal = r.wrap.clone();
        let mut given: Vec<Option<Expr>> = vec![None; names.len()];
        for f in fields {
            let v = self.expr(&f.value);
            match self.position(name, &f.name) {
                Some(i) if given[i].is_some() => {
                    let d = self.err("E-RECORD-DUPLICATE-FIELD", f.name_span.t(), m.index);
                    *d = d.clone().act(&f.name);
                }
                Some(i) => given[i] = Some(v),
                None => {
                    let fix = format!("field of {name}: {}", names.join(", "));
                    let d = self.err("E-RECORD-UNKNOWN-FIELD", f.name_span.t(), m.index);
                    *d = d
                        .clone()
                        .act(&f.name)
                        .fix("replace_identifier", f.name_span.t(), fix);
                }
            }
        }
        // `..base` は書かれていない field を base から取る。base が変数でなく書かれていない field が二つ以上なら、
        // let で一度だけ評価する。拒否と、let の有無は検証済みの `record_mode_e` が決める
        let flags: Vec<bool> = given.iter().map(Option::is_some).collect();
        let base_var = base
            .as_ref()
            .is_some_and(|b| matches!(b.kind, ExprKind::Var(_)));
        let mode = record_mode_e(&flags, base.is_some(), base_var);
        let mut wrap: Option<(String, Sp, Expr)> = None;
        let base_expr = base.as_ref().map(|b| {
            let bx = self.expr(b);
            if mode != RecMode::Bind {
                bx
            } else {
                let v = self.fresh_name();
                let var = Expr {
                    kind: ExprKind::Var(v.clone()),
                    meta: bx.meta,
                };
                wrap = Some((v, Sp(bx.meta.span().0, bx.meta.span().0), bx));
                var
            }
        });
        let missing: Vec<&str> = names
            .iter()
            .zip(&given)
            .filter(|(_, g)| g.is_none())
            .map(|(n, _)| n.as_str())
            .collect();
        if mode == RecMode::Missing {
            let list = missing.join(", ");
            let d = self.err("E-RECORD-MISSING-FIELD", name_span.t(), m.index);
            *d = d.clone().exp(&list).fix(
                "replace_expression",
                m.span(),
                format!(
                    "{name} {{ ... }} with every field ({}), or `..base` to copy the rest",
                    names.join(", ")
                ),
            );
            return unit;
        }
        // 書かれていない field がなければ、`..base` が写す先はない。base は検査せずに捨てていたので、この形は拒否する
        if let Some(b) = base.as_ref().filter(|_| mode == RecMode::BaseRedundant) {
            let d = self.err("E-RECORD-BASE-REDUNDANT", b.meta.span(), m.index);
            *d = d.clone().fix(
                "replace_expression",
                m.span(),
                format!(
                    "{name} {{ ... }} with every field ({}), without `..base`",
                    names.join(", ")
                ),
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
            out = Expr {
                kind: ExprKind::Pair(Box::new(v), Box::new(out)),
                meta: m,
            };
        }
        if let Some((v, sp, value)) = wrap {
            out = Expr {
                kind: ExprKind::Let {
                    name: v,
                    name_span: sp,
                    value: Box::new(value),
                    body: Box::new(out),
                },
                meta: m,
            };
        }
        // v1.15：印つきの写しでは、構築の結果に名義の型の印を付ける（補助関数の結果の型は印つきの型）
        if let Some(f) = seal {
            out = nominal::call(&f, out, m);
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
pub fn expand(p: &Program, tags: Option<&Tags>) -> Result<Program, Vec<Diagnostic>> {
    let mut env = Env {
        types: HashMap::new(),
        owner: HashMap::new(),
        diags: vec![],
        idents: HashSet::new(),
        fresh: 0,
        tags: tags.cloned(),
        helpers: vec![],
        names_id: HashMap::new(),
    };
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
                    format!(
                        "field name not used by another record type ('{}' is a field of {other})",
                        f.name
                    ),
                );
            }
            names.push(f.name.clone());
        }
        let ids: Vec<usize> = names.iter().map(|n| env.intern(n)).collect();
        for n in &names {
            env.owner.entry(n.clone()).or_insert_with(|| t.name.clone());
        }
        let params: Vec<String> = t.type_params.iter().map(|p| p.name.clone()).collect();
        let generic = (!params.is_empty()).then(|| Generic {
            params: params.clone(),
            template: record_type(&tys, Label::default(), t.meta),
        });
        let info = Arc::new(RecordInfo {
            name: t.name.clone(),
            fields: names.clone(),
            generic: generic.clone(),
            tagged: false,
        });
        let plain = record_type(&tys, Label(Some(Named::Record(info.clone()))), t.meta);
        // v1.15：印つきの写し：型の名前は印 r を付けた型（表示の名前は印つきの型の情報）。印を付ける・外す補助関数を作る
        let (ty, wrap) = match env.tags.as_ref().and_then(|g| g.get(&t.name)) {
            Some(r) => {
                let tgeneric = generic.as_ref().map(|g| Generic {
                    params: g.params.clone(),
                    template: nominal::named_ty(r, g.template.clone(), Label::default(), t.meta),
                });
                let tinfo = Arc::new(RecordInfo {
                    name: t.name.clone(),
                    fields: names,
                    generic: tgeneric,
                    tagged: true,
                });
                let named =
                    nominal::named_ty(r, plain.clone(), Label(Some(Named::Record(tinfo))), t.meta);
                let base = t.name.to_ascii_lowercase();
                let wrap = env.name_of(&format!("{base}_wrap"));
                env.helpers.push(nominal::wrap_fn(
                    &wrap,
                    r,
                    plain.clone(),
                    named.clone(),
                    &t.type_params,
                    t.meta,
                    &t.name,
                ));
                (named, Some(wrap))
            }
            None => (plain, None),
        };
        env.types.insert(
            t.name.clone(),
            Rec {
                info,
                ty,
                params,
                wrap,
                ids,
            },
        );
    }
    let mut decls = vec![];
    for d in &p.declarations {
        match d {
            Decl::Type(_) => {}
            Decl::Sum(s) => decls.push(Decl::Sum(s.clone())),
            Decl::Entry(e) => decls.push(Decl::Entry(e.clone())),
            Decl::Fn(f) => {
                let params = f
                    .params
                    .iter()
                    .map(|p| Param {
                        ty: env.ty(&p.ty),
                        ..p.clone()
                    })
                    .collect();
                let return_type = env.ty(&f.return_type);
                let body = env.expr(&f.body);
                decls.push(Decl::Fn(FnDecl {
                    params,
                    return_type,
                    body,
                    ..f.clone()
                }));
            }
        }
    }
    // v1.15：印を付ける・外す補助関数（印つきの写しだけ）
    decls.extend(env.helpers.drain(..).map(Decl::Fn));
    if env.diags.is_empty() {
        Ok(Program {
            declarations: decls,
            meta: p.meta,
            imports: p.imports.clone(),
        })
    } else {
        Err(env.diags)
    }
}

/// field の参照を `fst`／`snd` の並びに、レコード名付きの型を素の型にする（検証済み部品へ渡すソース用）。
pub fn lower(p: &Program) -> Program {
    let mut out = p.clone();
    lower_in_place(&mut out);
    out
}

/// `lower` と同じ。field の参照を含まないプログラムには何もしない（複製もしない）。
pub fn lower_in_place(p: &mut Program) {
    if !has_records(p) {
        return;
    }
    for d in &mut p.declarations {
        if let Decl::Fn(f) = d {
            lower_expr(&mut f.body);
        }
    }
}

/// `e` の中の field の参照を、その場で書き換える。書き換えるのは下の形の子だけ（それ以外の node の子には入らない）。
fn lower_expr(e: &mut Expr) {
    let m = e.meta;
    if let ExprKind::Field {
        expr,
        field_span,
        target: Some((rt, i, n)),
        ..
    } = &e.kind
    {
        let (fs, tagged, i, n) = (*field_span, nominal::is_tagged(rt), *i, *n);
        let call = |name: &str, arg: Expr| Expr {
            kind: ExprKind::Call {
                callee: name.into(),
                args: vec![arg],
                builtin: true,
                callee_span: fs,
                type_args: vec![],
            },
            meta: m,
        };
        let mut x = (**expr).clone();
        lower_expr(&mut x);
        // v1.15：印つきの型の値は、印の後ろの構造から中身を取り出す（印は型検査器が検査済み）。
        // fst／snd の並びは検証済みの `field_steps_e` が決める（先頭の snd は印つきのときだけ）
        for s in field_steps_e(tagged, i, n) {
            x = call(if s { "snd" } else { "fst" }, x);
        }
        *e = x;
        return;
    }
    match &mut e.kind {
        ExprKind::List { items, .. } => items.iter_mut().for_each(lower_expr),
        ExprKind::Some(v) => lower_expr(v),
        ExprKind::Pair(a, b) => {
            lower_expr(a);
            lower_expr(b);
        }
        ExprKind::Call { args, .. } => args.iter_mut().for_each(lower_expr),
        ExprKind::Let { value, body, .. } => {
            lower_expr(value);
            lower_expr(body);
        }
        ExprKind::If(c, t, f) => {
            lower_expr(c);
            lower_expr(t);
            lower_expr(f);
        }
        ExprKind::Fold {
            list, init, body, ..
        } => {
            lower_expr(list);
            lower_expr(init);
            lower_expr(body);
        }
        ExprKind::Hof { list, body, .. } => {
            lower_expr(list);
            lower_expr(body);
        }
        ExprKind::Loop {
            init, max, body, ..
        } => {
            lower_expr(init);
            lower_expr(max);
            lower_expr(body);
        }
        ExprKind::Match {
            scrutinee,
            on_none,
            on_some,
            ..
        } => {
            lower_expr(scrutinee);
            lower_expr(on_none);
            lower_expr(on_some);
        }
        ExprKind::Inj { value, .. } => lower_expr(value),
        ExprKind::MatchResult {
            scrutinee,
            on_ok,
            on_err,
            ..
        } => {
            lower_expr(scrutinee);
            lower_expr(on_ok);
            lower_expr(on_err);
        }
        ExprKind::SumMatch {
            scrutinee, arms, ..
        } => {
            lower_expr(scrutinee);
            arms.iter_mut().for_each(|a| lower_expr(&mut a.body));
        }
        _ => {}
    }
}
