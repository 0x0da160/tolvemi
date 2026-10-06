//! 表面 AST と意味論上の型（設計書 §3、§4.1、§19.2）。
//!
//! AST node は span（UTF-8 bytes の半開区間）と論理 node index（前順 Admission index）を
//! 持つが、構造的等価性の比較対象には含めない（`Meta` と `Sp` の `PartialEq` は常に真）。

use num_bigint::BigInt;
use std::fmt;
use std::sync::Arc;

pub const KEYWORDS: [&str; 33] = [
    "fn", "entry", "Int", "Bool", "Unit", "List", "Option", "Pair", "true", "false", "unit", "list", "some", "none",
    "pair", "let", "in", "if", "fold", "add", "sub", "mul", "neg", "lt", "le", "eq", "mod", "fst", "snd", "cons",
    "concat", "reverse", "length",
];

pub fn is_keyword(s: &str) -> bool {
    KEYWORDS.contains(&s)
}

pub fn builtin_arity(name: &str) -> Option<usize> {
    Some(match name {
        "add" | "sub" | "mul" | "lt" | "le" | "eq" | "mod" | "cons" | "concat" => 2,
        "neg" | "fst" | "snd" | "reverse" | "length" => 1,
        _ => return None,
    })
}

pub fn is_builtin(name: &str) -> bool {
    builtin_arity(name).is_some()
}

/// 比較対象外の span。
#[derive(Clone, Copy, Debug, Default)]
pub struct Sp(pub usize, pub usize);

impl PartialEq for Sp {
    fn eq(&self, _: &Self) -> bool {
        true
    }
}

impl Sp {
    pub fn t(self) -> (usize, usize) {
        (self.0, self.1)
    }
}

#[derive(Clone, Copy, Debug, Default)]
pub struct Meta {
    pub span: Sp,
    pub index: usize,
}

impl PartialEq for Meta {
    fn eq(&self, _: &Self) -> bool {
        true
    }
}

impl Meta {
    pub fn new(span: (usize, usize), index: usize) -> Meta {
        Meta { span: Sp(span.0, span.1), index }
    }
    pub fn span(&self) -> (usize, usize) {
        self.span.t()
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum TyTag {
    Int,
    Bool,
    Unit,
    List,
    Option,
    Pair,
    Error,
}

impl TyTag {
    pub fn name(self) -> &'static str {
        match self {
            TyTag::Int => "Int",
            TyTag::Bool => "Bool",
            TyTag::Unit => "Unit",
            TyTag::List => "List",
            TyTag::Option => "Option",
            TyTag::Pair => "Pair",
            TyTag::Error => "Error",
        }
    }
    pub fn from_keyword(s: &str) -> Option<TyTag> {
        Some(match s {
            "Int" => TyTag::Int,
            "Bool" => TyTag::Bool,
            "Unit" => TyTag::Unit,
            "List" => TyTag::List,
            "Option" => TyTag::Option,
            "Pair" => TyTag::Pair,
            _ => return None,
        })
    }
    pub fn arity(self) -> usize {
        match self {
            TyTag::List | TyTag::Option => 1,
            TyTag::Pair => 2,
            _ => 0,
        }
    }
}

// ------------------------------------------------------------------ 構文

#[derive(Clone, Debug, PartialEq)]
pub struct TypeNode {
    pub tag: TyTag,
    pub args: Vec<TypeNode>,
    pub meta: Meta,
}

#[derive(Clone, Debug, PartialEq)]
pub enum ExprKind {
    Int(BigInt),
    Bool(bool),
    Unit,
    Var(String),
    List { element_type: TypeNode, items: Vec<Expr> },
    Some(Box<Expr>),
    None(TypeNode),
    Pair(Box<Expr>, Box<Expr>),
    Call { callee: String, args: Vec<Expr>, builtin: bool, callee_span: Sp },
    Let { name: String, name_span: Sp, value: Box<Expr>, body: Box<Expr> },
    If(Box<Expr>, Box<Expr>, Box<Expr>),
    Fold { list: Box<Expr>, init: Box<Expr>, acc: String, acc_span: Sp, item: String, item_span: Sp, body: Box<Expr> },
}

#[derive(Clone, Debug, PartialEq)]
pub struct Expr {
    pub kind: ExprKind,
    pub meta: Meta,
}

impl Expr {
    /// 子式を左から右の順で返す。
    pub fn children(&self) -> Vec<&Expr> {
        match &self.kind {
            ExprKind::List { items, .. } => items.iter().collect(),
            ExprKind::Some(v) => vec![v],
            ExprKind::Pair(a, b) => vec![a, b],
            ExprKind::Call { args, .. } => args.iter().collect(),
            ExprKind::Let { value, body, .. } => vec![value, body],
            ExprKind::If(c, t, e) => vec![c, t, e],
            ExprKind::Fold { list, init, body, .. } => vec![list, init, body],
            _ => vec![],
        }
    }
}

#[derive(Clone, Debug, PartialEq)]
pub struct Param {
    pub name: String,
    pub name_span: Sp,
    pub ty: TypeNode,
    pub meta: Meta,
}

#[derive(Clone, Debug, PartialEq)]
pub struct FnDecl {
    pub name: String,
    pub name_span: Sp,
    pub params: Vec<Param>,
    pub return_type: TypeNode,
    pub body: Expr,
    pub meta: Meta,
}

#[derive(Clone, Debug, PartialEq)]
pub struct EntryDecl {
    pub name: String,
    pub name_span: Sp,
    pub meta: Meta,
}

#[derive(Clone, Debug, PartialEq)]
pub enum Decl {
    Fn(FnDecl),
    Entry(EntryDecl),
}

#[derive(Clone, Debug, PartialEq)]
pub struct Program {
    pub declarations: Vec<Decl>,
    pub meta: Meta,
}

impl Program {
    pub fn functions(&self) -> impl Iterator<Item = &FnDecl> {
        self.declarations.iter().filter_map(|d| match d {
            Decl::Fn(f) => Some(f),
            _ => None,
        })
    }
    pub fn entries(&self) -> impl Iterator<Item = &EntryDecl> {
        self.declarations.iter().filter_map(|d| match d {
            Decl::Entry(e) => Some(e),
            _ => None,
        })
    }
}

// ------------------------------------------------------------------ 意味論上の型

struct TyNode {
    tag: TyTag,
    args: Vec<Ty>,
    depth: usize,
}

/// 単相型。共有 DAG で表し、深さはキャッシュする。ErrorType は深さ0。
#[derive(Clone)]
pub struct Ty(Arc<TyNode>);

impl Ty {
    pub fn new(tag: TyTag, args: Vec<Ty>) -> Ty {
        let depth = if tag == TyTag::Error { 0 } else { 1 + args.iter().map(|a| a.depth()).max().unwrap_or(0) };
        Ty(Arc::new(TyNode { tag, args, depth }))
    }
    pub fn int() -> Ty {
        Ty::new(TyTag::Int, vec![])
    }
    pub fn bool() -> Ty {
        Ty::new(TyTag::Bool, vec![])
    }
    pub fn unit() -> Ty {
        Ty::new(TyTag::Unit, vec![])
    }
    pub fn error() -> Ty {
        Ty::new(TyTag::Error, vec![])
    }
    pub fn list(t: Ty) -> Ty {
        Ty::new(TyTag::List, vec![t])
    }
    pub fn option(t: Ty) -> Ty {
        Ty::new(TyTag::Option, vec![t])
    }
    pub fn pair(a: Ty, b: Ty) -> Ty {
        Ty::new(TyTag::Pair, vec![a, b])
    }
    pub fn tag(&self) -> TyTag {
        self.0.tag
    }
    pub fn args(&self) -> &[Ty] {
        &self.0.args
    }
    pub fn arg(&self, i: usize) -> Ty {
        self.0.args[i].clone()
    }
    pub fn depth(&self) -> usize {
        self.0.depth
    }
    pub fn is_error(&self) -> bool {
        self.0.tag == TyTag::Error
    }
    pub fn of(node: &TypeNode) -> Ty {
        Ty::new(node.tag, node.args.iter().map(Ty::of).collect())
    }

    fn write_limited(&self, out: &mut String, budget: &mut usize) {
        if *budget == 0 {
            return;
        }
        let name = self.0.tag.name();
        if name.len() > *budget {
            out.push('…');
            *budget = 0;
            return;
        }
        out.push_str(name);
        *budget -= name.len();
        if !self.0.args.is_empty() {
            out.push('<');
            for (i, a) in self.0.args.iter().enumerate() {
                if i > 0 {
                    out.push_str(", ");
                }
                a.write_limited(out, budget);
                if *budget == 0 {
                    return;
                }
            }
            out.push('>');
        }
    }
}

impl PartialEq for Ty {
    fn eq(&self, other: &Ty) -> bool {
        Arc::ptr_eq(&self.0, &other.0) || (self.0.tag == other.0.tag && self.0.args == other.0.args)
    }
}

/// 型表示。共有により指数的に大きくなりうるため 4096 文字で打ち切る。
impl fmt::Display for Ty {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut s = String::new();
        let mut budget = 4096;
        self.write_limited(&mut s, &mut budget);
        f.write_str(&s)
    }
}

impl fmt::Debug for Ty {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Display::fmt(self, f)
    }
}
