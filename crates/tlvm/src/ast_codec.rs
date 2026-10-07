//! ast_codec_v1 の decoder（設計書 §19.2–19.3、§18.1b の AST API Admission）。

use crate::diagnostics::Diagnostic;
use crate::parser::{expr_depths, Admission, Depths};
use crate::profiles::{AstTransportProfile, StaticProfile};
use crate::strict_json::{parse, smallest_key, JKind, JNode, JsonFailKind};
use crate::syntax::*;
use crate::values::is_canonical_int;

use JKind::{Array as A, Boolean as B, Object as O, String as S};

const PROGRAM_FIELDS: &[(&str, JKind)] = &[("codec", S), ("declarations", A)];
const PARAM_FIELDS: &[(&str, JKind)] = &[("name", S), ("type", O)];
const DECL_TAGS: &[&str] = &["fn", "entry"];
const TYPE_TAGS: &[&str] = &["int", "bool", "unit", "list", "option", "pair"];
const EXPR_TAGS: &[&str] =
    &["int", "bool", "unit", "var", "list", "some", "none", "pair", "call", "let", "if", "fold", "match_option"];

fn decl_fields(tag: &str) -> &'static [(&'static str, JKind)] {
    match tag {
        "fn" => &[("name", S), ("params", A), ("return_type", O), ("body", O)],
        _ => &[("name", S)],
    }
}

fn type_fields(tag: &str) -> &'static [(&'static str, JKind)] {
    match tag {
        "list" | "option" => &[("element", O)],
        "pair" => &[("left", O), ("right", O)],
        _ => &[],
    }
}

fn expr_fields(tag: &str) -> &'static [(&'static str, JKind)] {
    match tag {
        "int" => &[("value", S)],
        "bool" => &[("value", B)],
        "var" => &[("name", S)],
        "list" => &[("element_type", O), ("items", A)],
        "some" => &[("value", O)],
        "none" => &[("element_type", O)],
        "pair" => &[("left", O), ("right", O)],
        "call" => &[("callee", S), ("args", A)],
        "let" => &[("name", S), ("value", O), ("body", O)],
        "if" => &[("condition", O), ("then", O), ("else", O)],
        "fold" => &[("list", O), ("init", O), ("acc", S), ("item", S), ("body", O)],
        "match_option" => &[("scrutinee", O), ("on_none", O), ("binder", S), ("on_some", O)],
        _ => &[],
    }
}

fn type_tag(tag: &str) -> TyTag {
    match tag {
        "int" => TyTag::Int,
        "bool" => TyTag::Bool,
        "unit" => TyTag::Unit,
        "list" => TyTag::List,
        "option" => TyTag::Option,
        _ => TyTag::Pair,
    }
}

pub fn is_identifier(s: &str) -> bool {
    let b = s.as_bytes();
    !b.is_empty()
        && (b[0].is_ascii_alphabetic() || b[0] == b'_')
        && b.iter().all(|c| c.is_ascii_alphanumeric() || *c == b'_')
        && !is_keyword(s)
}

#[derive(Debug)]
pub enum Transport {
    Ok(JNode),
    BoundaryFailure,
    Invalid(Vec<Diagnostic>),
}

/// transport 検査（bytes 上限 → UTF-8 → strict JSON → schema）。
pub fn transport(data: &[u8], tp: &AstTransportProfile, sp: &StaticProfile) -> Transport {
    if data.len() > tp.json_bytes {
        return Transport::Invalid(vec![Diagnostic::error("ast-boundary", "E-AST-LIMIT-BYTES", (0, 0))
            .exp(tp.json_bytes.to_string())
            .act(data.len().to_string())]);
    }
    if std::str::from_utf8(data).is_err() {
        return Transport::BoundaryFailure;
    }
    let root = match parse(data, tp.json_depth) {
        Ok(r) => r,
        Err(f) => {
            let code = match f.kind {
                JsonFailKind::Syntax => "E-AST-JSON-SYNTAX",
                JsonFailKind::Depth => "E-AST-LIMIT-JSON-DEPTH",
                JsonFailKind::Scalar => "E-AST-STRING-SCALAR",
                JsonFailKind::Duplicate => "E-AST-DUPLICATE-KEY",
            };
            return Transport::Invalid(vec![Diagnostic::error("ast-parse", code, f.span)]);
        }
    };
    match (Schema { sp }).program(&root) {
        Ok(()) => Transport::Ok(root),
        Err(d) => Transport::Invalid(vec![d]),
    }
}

type R = Result<(), Diagnostic>;

struct Schema<'a> {
    sp: &'a StaticProfile,
}

fn fail(code: &'static str, span: (usize, usize)) -> Diagnostic {
    Diagnostic::error("ast-schema", code, span)
}

impl Schema<'_> {
    fn header<'n>(&self, n: &'n JNode, allowed: &[&str]) -> Result<&'n str, Diagnostic> {
        if n.kind != O {
            return Err(fail("E-AST-FIELD-TYPE", n.span()).exp("object").act(n.kind.name()));
        }
        let tag = n.get("tag").ok_or_else(|| fail("E-AST-MISSING-FIELD", n.close_span()).exp("tag"))?;
        if tag.kind != S {
            return Err(fail("E-AST-TAG", tag.span()).exp("string").act(tag.kind.name()));
        }
        if !allowed.contains(&tag.text.as_str()) {
            return Err(fail("E-AST-TAG", tag.span()).exp(allowed.join(" | ")).act(tag.text.clone()));
        }
        Ok(&tag.text)
    }

    fn keys(&self, n: &JNode, fs: &[(&str, JKind)], tagged: bool) -> R {
        for (k, _) in fs {
            if n.get(k).is_none() {
                return Err(fail("E-AST-MISSING-FIELD", n.close_span()).exp(*k));
            }
        }
        let extra = smallest_key(
            n.members.iter().map(|m| m.key.as_str()).filter(|k| !(tagged && *k == "tag") && !fs.iter().any(|(f, _)| f == k)),
        );
        if let Some(k) = extra {
            return Err(fail("E-AST-UNKNOWN-FIELD", n.key_span(k)).act(k));
        }
        for (k, kind) in fs {
            let c = n.get(k).unwrap();
            if c.kind != *kind {
                return Err(fail("E-AST-FIELD-TYPE", c.span()).exp(kind.name()).act(c.kind.name()));
            }
        }
        Ok(())
    }

    fn ident(&self, s: &JNode) -> R {
        if is_identifier(&s.text) {
            Ok(())
        } else {
            Err(fail("E-AST-IDENTIFIER", s.span()).exp("identifier"))
        }
    }

    fn program(&self, n: &JNode) -> R {
        if n.kind != O {
            return Err(fail("E-AST-FIELD-TYPE", n.span()).exp("object").act(n.kind.name()));
        }
        let codec = n.get("codec").ok_or_else(|| fail("E-AST-CODEC", n.close_span()).exp("ast_codec_v1"))?;
        if codec.kind != S || codec.text != "ast_codec_v1" {
            return Err(fail("E-AST-CODEC", codec.span()).exp("ast_codec_v1"));
        }
        self.keys(n, PROGRAM_FIELDS, false)?;
        for d in &n.get("declarations").unwrap().items {
            self.decl(d)?;
        }
        Ok(())
    }

    fn decl(&self, n: &JNode) -> R {
        let tag = self.header(n, DECL_TAGS)?;
        self.keys(n, decl_fields(tag), true)?;
        self.ident(n.get("name").unwrap())?;
        if tag == "fn" {
            for p in &n.get("params").unwrap().items {
                self.param(p)?;
            }
            self.ty(n.get("return_type").unwrap())?;
            self.expr(n.get("body").unwrap())?;
        }
        Ok(())
    }

    fn param(&self, n: &JNode) -> R {
        if n.kind != O {
            return Err(fail("E-AST-FIELD-TYPE", n.span()).exp("object").act(n.kind.name()));
        }
        self.keys(n, PARAM_FIELDS, false)?;
        self.ident(n.get("name").unwrap())?;
        self.ty(n.get("type").unwrap())
    }

    fn ty(&self, n: &JNode) -> R {
        let tag = self.header(n, TYPE_TAGS)?;
        let fs = type_fields(tag);
        self.keys(n, fs, true)?;
        for (k, _) in fs {
            self.ty(n.get(k).unwrap())?;
        }
        Ok(())
    }

    fn expr(&self, n: &JNode) -> R {
        let tag = self.header(n, EXPR_TAGS)?;
        let fs = expr_fields(tag);
        self.keys(n, fs, true)?;
        for (k, _) in fs {
            let c = n.get(k).unwrap();
            match (tag, *k) {
                ("int", "value") => {
                    if !is_canonical_int(&c.text) {
                        return Err(fail("E-AST-INTEGER", c.span()));
                    }
                    let digits = c.text.trim_start_matches('-').len();
                    if digits > self.sp.integer_digits {
                        return Err(fail("E-AST-LIMIT-INTEGER-DIGITS", c.span())
                            .exp(self.sp.integer_digits.to_string())
                            .act(digits.to_string()));
                    }
                }
                ("bool", _) => {}
                ("call", "callee") => {
                    if !is_builtin(&c.text) {
                        self.ident(c)?;
                    }
                }
                (_, "name" | "acc" | "item" | "binder") => self.ident(c)?,
                (_, "element_type") => self.ty(c)?,
                (_, "items" | "args") => {
                    for x in &c.items {
                        self.expr(x)?;
                    }
                }
                _ => self.expr(c)?,
            }
        }
        Ok(())
    }
}

/// transport 通過後、共通 Admission を発行しながら表面 AST を構築する。
/// guard 超過時は structural-limits の cutoff 診断を返す。
pub fn build(root: &JNode, sp: &StaticProfile) -> Result<Program, Diagnostic> {
    let mut b = Builder { adm: Admission::new(sp) };
    b.program(root)
}

struct Builder {
    adm: Admission,
}

fn sp_of(n: &JNode) -> Sp {
    Sp(n.start, n.end)
}

impl Builder {
    fn program(&mut self, n: &JNode) -> Result<Program, Diagnostic> {
        let idx = self.adm.admit(n.span(), Depths::default())?;
        let mut decls = vec![];
        for d in &n.get("declarations").unwrap().items {
            let name = d.get("name").unwrap();
            if d.get("tag").unwrap().text == "entry" {
                let i = self.adm.admit(d.span(), Depths::default())?;
                decls.push(Decl::Entry(EntryDecl { name: name.text.clone(), name_span: sp_of(name), meta: Meta::new(d.span(), i) }));
                continue;
            }
            let i = self.adm.admit(d.span(), Depths { fn_: true, ..Default::default() })?;
            let mut params = vec![];
            for p in &d.get("params").unwrap().items {
                let pi = self.adm.admit(p.span(), Depths::default())?;
                let pn = p.get("name").unwrap();
                let ty = self.ty(p.get("type").unwrap(), 1)?;
                params.push(Param { name: pn.text.clone(), name_span: sp_of(pn), ty, meta: Meta::new(p.span(), pi) });
            }
            let ret = self.ty(d.get("return_type").unwrap(), 1)?;
            let body = self.expr(d.get("body").unwrap(), 1, 0, 0)?;
            decls.push(Decl::Fn(FnDecl {
                name: name.text.clone(),
                name_span: sp_of(name),
                params,
                return_type: ret,
                body,
                meta: Meta::new(d.span(), i),
            }));
        }
        Ok(Program { declarations: decls, meta: Meta::new(n.span(), idx) })
    }

    fn ty(&mut self, n: &JNode, depth: usize) -> Result<TypeNode, Diagnostic> {
        let tag = &n.get("tag").unwrap().text;
        let i = self.adm.admit(n.span(), Depths { ty: Some(depth), ..Default::default() })?;
        let mut args = vec![];
        for (k, _) in type_fields(tag) {
            args.push(self.ty(n.get(k).unwrap(), depth + 1)?);
        }
        Ok(TypeNode { tag: type_tag(tag), args, meta: Meta::new(n.span(), i) })
    }

    fn expr(&mut self, n: &JNode, d: usize, ld: usize, fd: usize) -> Result<Expr, Diagnostic> {
        let tag = n.get("tag").unwrap().text.as_str();
        let (i, ld, fd) = match tag {
            "let" => (self.adm.admit(n.span(), Depths { expr: Some(d), let_: Some(ld + 1), ..Default::default() })?, ld + 1, fd),
            "fold" => (self.adm.admit(n.span(), Depths { expr: Some(d), fold: Some(fd + 1), ..Default::default() })?, ld, fd + 1),
            "match_option" => {
                (self.adm.admit(n.span(), Depths { expr: Some(d), let_: Some(ld + 1), ..Default::default() })?, ld + 1, fd)
            }
            _ => (self.adm.admit(n.span(), expr_depths(d))?, ld, fd),
        };
        let g = |k: &str| n.get(k).unwrap();
        let kind = match tag {
            "int" => ExprKind::Int(g("value").text.parse().unwrap()),
            "bool" => ExprKind::Bool(g("value").boolean),
            "unit" => ExprKind::Unit,
            "var" => ExprKind::Var(g("name").text.clone()),
            "list" => {
                let ty = self.ty(g("element_type"), 1)?;
                let mut items = vec![];
                for c in &g("items").items {
                    items.push(self.expr(c, d + 1, ld, fd)?);
                }
                ExprKind::List { element_type: ty, items }
            }
            "some" => ExprKind::Some(Box::new(self.expr(g("value"), d + 1, ld, fd)?)),
            "none" => ExprKind::None(self.ty(g("element_type"), 1)?),
            "pair" => {
                let a = self.expr(g("left"), d + 1, ld, fd)?;
                let b = self.expr(g("right"), d + 1, ld, fd)?;
                ExprKind::Pair(Box::new(a), Box::new(b))
            }
            "call" => {
                let callee = g("callee");
                let mut args = vec![];
                for c in &g("args").items {
                    args.push(self.expr(c, d + 1, ld, fd)?);
                }
                ExprKind::Call { callee: callee.text.clone(), args, builtin: is_builtin(&callee.text), callee_span: sp_of(callee) }
            }
            "let" => {
                let v = self.expr(g("value"), d + 1, ld, fd)?;
                let b = self.expr(g("body"), d + 1, ld, fd)?;
                ExprKind::Let { name: g("name").text.clone(), name_span: sp_of(g("name")), value: Box::new(v), body: Box::new(b) }
            }
            "if" => {
                let c = self.expr(g("condition"), d + 1, ld, fd)?;
                let t = self.expr(g("then"), d + 1, ld, fd)?;
                let e = self.expr(g("else"), d + 1, ld, fd)?;
                ExprKind::If(Box::new(c), Box::new(t), Box::new(e))
            }
            "match_option" => {
                let s = self.expr(g("scrutinee"), d + 1, ld, fd)?;
                let none = self.expr(g("on_none"), d + 1, ld, fd)?;
                let some = self.expr(g("on_some"), d + 1, ld, fd)?;
                ExprKind::Match {
                    scrutinee: Box::new(s),
                    on_none: Box::new(none),
                    binder: g("binder").text.clone(),
                    binder_span: sp_of(g("binder")),
                    on_some: Box::new(some),
                }
            }
            _ => {
                let xs = self.expr(g("list"), d + 1, ld, fd)?;
                let init = self.expr(g("init"), d + 1, ld, fd)?;
                let body = self.expr(g("body"), d + 1, ld, fd)?;
                ExprKind::Fold {
                    list: Box::new(xs),
                    init: Box::new(init),
                    acc: g("acc").text.clone(),
                    acc_span: sp_of(g("acc")),
                    item: g("item").text.clone(),
                    item_span: sp_of(g("item")),
                    body: Box::new(body),
                }
            }
        };
        Ok(Expr { kind, meta: Meta::new(n.span(), i) })
    }
}
