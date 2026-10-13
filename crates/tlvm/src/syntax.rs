//! 表面 AST と意味論上の型（設計書 §3、§4.1、§19.2）。
//!
//! AST node は span（UTF-8 bytes の半開区間）と論理 node index（前順 Admission index）を
//! 持つが、構造的等価性の比較対象には含めない（`Meta` と `Sp` の `PartialEq` は常に真）。

use num_bigint::BigInt;
use std::fmt;
use std::sync::Arc;

pub const KEYWORDS: [&str; 57] = [
    "fn", "entry", "Int", "Bool", "Unit", "List", "Option", "Pair", "true", "false", "unit", "list", "some", "none",
    "pair", "let", "in", "if", "fold", "add", "sub", "mul", "neg", "lt", "le", "eq", "mod", "fst", "snd", "cons",
    "concat", "reverse", "length", "uncons", "match_option", "min", "max", "range", "contains", "sort", "Char", "String",
    "code", "char", "to_string", "parse_int", "Result", "ok", "err", "match_result", "map", "filter", "any", "all", "find",
    "sort_by", "loop",
];

pub fn is_keyword(s: &str) -> bool {
    KEYWORDS.contains(&s)
}

pub fn builtin_arity(name: &str) -> Option<usize> {
    Some(match name {
        "add" | "sub" | "mul" | "lt" | "le" | "eq" | "mod" | "cons" | "concat" | "min" | "max" | "range" | "contains" => 2,
        "neg" | "fst" | "snd" | "reverse" | "length" | "uncons" | "sort" | "code" | "char" | "to_string" | "parse_int" => 1,
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
    /// v1.2：Unicode scalar value。`String` は `List<Char>` の別名
    Char,
    List,
    Option,
    Pair,
    /// v1.4：`Result<T, E>`
    Result,
    Error,
}

impl TyTag {
    pub fn name(self) -> &'static str {
        match self {
            TyTag::Int => "Int",
            TyTag::Bool => "Bool",
            TyTag::Unit => "Unit",
            TyTag::Char => "Char",
            TyTag::List => "List",
            TyTag::Option => "Option",
            TyTag::Pair => "Pair",
            TyTag::Result => "Result",
            TyTag::Error => "Error",
        }
    }
    pub fn from_keyword(s: &str) -> Option<TyTag> {
        Some(match s {
            "Int" => TyTag::Int,
            "Bool" => TyTag::Bool,
            "Unit" => TyTag::Unit,
            "Char" => TyTag::Char,
            "List" => TyTag::List,
            "Option" => TyTag::Option,
            "Pair" => TyTag::Pair,
            "Result" => TyTag::Result,
            _ => return None,
        })
    }
    pub fn arity(self) -> usize {
        match self {
            TyTag::List | TyTag::Option => 1,
            TyTag::Pair | TyTag::Result => 2,
            _ => 0,
        }
    }
}

/// v1.5：リストと一引数のラムダ `|x| e` を取る特殊形式（`hof::lower` が fold などに書き換える）。
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum HofOp {
    Map,
    Filter,
    Any,
    All,
    Find,
    SortBy,
}

impl HofOp {
    pub const ALL: [HofOp; 6] = [HofOp::Map, HofOp::Filter, HofOp::Any, HofOp::All, HofOp::Find, HofOp::SortBy];

    pub fn name(self) -> &'static str {
        match self {
            HofOp::Map => "map",
            HofOp::Filter => "filter",
            HofOp::Any => "any",
            HofOp::All => "all",
            HofOp::Find => "find",
            HofOp::SortBy => "sort_by",
        }
    }
    pub fn from_name(s: &str) -> Option<HofOp> {
        HofOp::ALL.into_iter().find(|o| o.name() == s)
    }
}

/// v1.6：上限つき反復 `loop(init, max, |s| e)` の名前。
pub const LOOP: &str = "loop";

/// ラムダを取る特殊形式の名前（v1.5 の 6 語と v1.6 の `loop`）。直後が `(` のときだけ特殊形式。
pub fn is_lambda_form(s: &str) -> bool {
    HofOp::from_name(s).is_some() || s == LOOP
}

// ------------------------------------------------------------------ 構文

#[derive(Clone, Debug, PartialEq)]
pub struct TypeNode {
    pub tag: TyTag,
    pub args: Vec<TypeNode>,
    pub meta: Meta,
    /// v1.1：レコード型の名前（`records::expand` が展開する前だけ。tag は Error）
    pub name: Option<String>,
    /// 展開後のレコード型に付く名前と field 名（表示と plain JSON 用。比較対象外）
    pub label: Label,
}

impl TypeNode {
    pub fn new(tag: TyTag, args: Vec<TypeNode>, meta: Meta) -> TypeNode {
        TypeNode { tag, args, meta, name: None, label: Label::default() }
    }
    /// v1.2：`String`（= `List<Char>`）か。
    pub fn is_string(&self) -> bool {
        self.tag == TyTag::List && self.args[0].tag == TyTag::Char && self.args[0].name.is_none()
    }
}

/// レコード型の名前と field 名（宣言順）。
#[derive(Debug, PartialEq, Eq)]
pub struct RecordInfo {
    pub name: String,
    pub fields: Vec<String>,
}

/// v1.4：ユーザー定義の直和型の名前と variant（宣言順。名前と中身の数）。
#[derive(Debug)]
pub struct SumInfo {
    pub name: String,
    pub variants: Vec<(String, usize)>,
    /// variant が一つで中身が一つのとき、その中身の型に付いていた名前（型全体の名前で上書きされるので別に持つ）
    pub inner: Label,
}

/// 型に付く名前（レコード型か直和型）。
#[derive(Clone, Debug)]
pub enum Named {
    Record(Arc<RecordInfo>),
    Sum(Arc<SumInfo>),
}

impl Named {
    pub fn name(&self) -> &str {
        match self {
            Named::Record(r) => &r.name,
            Named::Sum(s) => &s.name,
        }
    }
}

/// 型に付くレコード・直和型の名前。型の等価性には含めない（展開後の構造で決まる構造的な型）。
#[derive(Clone, Debug, Default)]
pub struct Label(pub Option<Named>);

impl PartialEq for Label {
    fn eq(&self, _: &Self) -> bool {
        true
    }
}

#[derive(Clone, Debug, PartialEq)]
pub enum ExprKind {
    Int(BigInt),
    /// v1.2：文字リテラル `'c'`
    Char(char),
    /// v1.2：文字列リテラル `"..."`（型は `String` = `List<Char>`）
    Str(String),
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
    /// v1.1：match_option(scrutinee, on_none, |binder| on_some)
    Match { scrutinee: Box<Expr>, on_none: Box<Expr>, binder: String, binder_span: Sp, on_some: Box<Expr> },
    /// v1.1：レコードの構築 `Name { f: e, ..., ..base }`（`records::expand` が pair の入れ子にする）
    Record { name: String, name_span: Sp, fields: Vec<RecordField>, base: Option<Box<Expr>> },
    /// v1.1：field の参照 `e.f`。`target` は展開後に付く（レコード型、field の位置、field の数）
    Field { expr: Box<Expr>, field: String, field_span: Sp, target: Option<(TypeNode, usize, usize)> },
    /// v1.4：`ok<T, E>(x)`（ok = true）、`err<T, E>(x)`。`ty` は `Result<T, E>`（直和型の構築なら名前付き）
    Inj { ok: bool, ty: TypeNode, value: Box<Expr> },
    /// v1.4：match_result(scrutinee, |ok_binder| on_ok, |err_binder| on_err)
    MatchResult {
        scrutinee: Box<Expr>,
        ok_binder: String,
        ok_span: Sp,
        on_ok: Box<Expr>,
        err_binder: String,
        err_span: Sp,
        on_err: Box<Expr>,
    },
    /// v1.4：`match e { P => e, ... }`（`sums::expand` が `kind` と各 arm の `variant` を付け、`sums::lower` が書き換える）
    SumMatch { scrutinee: Box<Expr>, arms: Vec<Arm>, kw_span: Sp, close_span: Sp, kind: Option<MatchKind> },
    /// v1.5：`map(xs, |x| e)` など（`op` が形の名前。`binder` は body の中でだけ見える）
    Hof { op: HofOp, list: Box<Expr>, binder: String, binder_span: Sp, body: Box<Expr> },
    /// v1.6：`loop(init, max, |binder| body)`（`binder` は body の中でだけ見える）
    Loop { init: Box<Expr>, max: Box<Expr>, binder: String, binder_span: Sp, body: Box<Expr> },
}

/// v1.4：`match` の一つの枝。
#[derive(Clone, Debug, PartialEq)]
pub struct Arm {
    pub pat: Pattern,
    pub body: Expr,
    /// pattern の先頭から body の末尾まで
    pub span: Sp,
    /// 展開後：この枝が受け持つ場合の番号（直和型は variant の位置、Result は ok = 0・err = 1、
    /// Option は some = 0・none = 1）。`_` は None
    pub variant: Option<usize>,
}

#[derive(Clone, Debug, PartialEq)]
pub enum PatKind {
    Ctor(String),
    Ok,
    Err,
    Some,
    None,
    Wild,
}

#[derive(Clone, Debug, PartialEq)]
pub struct Pattern {
    pub kind: PatKind,
    pub span: Sp,
    /// `CTOR(...)` のように括弧を書いたか
    pub parens: bool,
    /// 束縛する名前（`_` は束縛しない）
    pub binds: Vec<(String, Sp)>,
}

/// v1.4：`match` の対象の種類（展開後）。
#[derive(Clone, Debug, PartialEq)]
pub enum MatchKind {
    /// 直和型（展開後の名前付きの型と、variant ごとの中身の型）
    Sum { ty: TypeNode, fields: Vec<Vec<TypeNode>> },
    Result,
    Option,
    /// `_` だけ
    Any,
}

#[derive(Clone, Debug, PartialEq)]
pub struct RecordField {
    pub name: String,
    pub name_span: Sp,
    pub value: Expr,
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
            ExprKind::Hof { list, body, .. } => vec![list, body],
            ExprKind::Loop { init, max, body, .. } => vec![init, max, body],
            ExprKind::Match { scrutinee, on_none, on_some, .. } => vec![scrutinee, on_none, on_some],
            ExprKind::Record { fields, base, .. } => fields.iter().map(|f| &f.value).chain(base.as_deref()).collect(),
            ExprKind::Field { expr, .. } => vec![expr],
            ExprKind::Inj { value, .. } => vec![value],
            ExprKind::MatchResult { scrutinee, on_ok, on_err, .. } => vec![scrutinee, on_ok, on_err],
            ExprKind::SumMatch { scrutinee, arms, .. } => {
                std::iter::once(&**scrutinee).chain(arms.iter().map(|a| &a.body)).collect()
            }
            _ => vec![],
        }
    }
}

impl Expr {
    /// 子式（`children` と同じ順）への可変参照。
    pub fn children_mut(&mut self) -> Vec<&mut Expr> {
        match &mut self.kind {
            ExprKind::List { items, .. } => items.iter_mut().collect(),
            ExprKind::Some(v) | ExprKind::Inj { value: v, .. } => vec![&mut **v],
            ExprKind::Pair(a, b) => vec![&mut **a, &mut **b],
            ExprKind::Call { args, .. } => args.iter_mut().collect(),
            ExprKind::Let { value, body, .. } => vec![&mut **value, &mut **body],
            ExprKind::If(c, t, e) => vec![&mut **c, &mut **t, &mut **e],
            ExprKind::Fold { list, init, body, .. } => vec![&mut **list, &mut **init, &mut **body],
            ExprKind::Hof { list, body, .. } => vec![&mut **list, &mut **body],
            ExprKind::Loop { init, max, body, .. } => vec![&mut **init, &mut **max, &mut **body],
            ExprKind::Match { scrutinee, on_none, on_some, .. } => vec![&mut **scrutinee, &mut **on_none, &mut **on_some],
            ExprKind::Record { fields, base, .. } => {
                fields.iter_mut().map(|f| &mut f.value).chain(base.as_deref_mut()).collect()
            }
            ExprKind::Field { expr, .. } => vec![&mut **expr],
            ExprKind::MatchResult { scrutinee, on_ok, on_err, .. } => vec![&mut **scrutinee, &mut **on_ok, &mut **on_err],
            ExprKind::SumMatch { scrutinee, arms, .. } => {
                std::iter::once(&mut **scrutinee).chain(arms.iter_mut().map(|a| &mut a.body)).collect()
            }
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
    /// v1.1：`type Name = { f: T, ... }`
    Type(TypeDecl),
    /// v1.4：`type Name = A | B(T, ...) | ...`
    Sum(SumDecl),
}

#[derive(Clone, Debug, PartialEq)]
pub struct SumDecl {
    pub name: String,
    pub name_span: Sp,
    pub variants: Vec<VariantDecl>,
    pub meta: Meta,
}

#[derive(Clone, Debug, PartialEq)]
pub struct VariantDecl {
    pub name: String,
    pub name_span: Sp,
    pub fields: Vec<TypeNode>,
}

#[derive(Clone, Debug, PartialEq)]
pub struct TypeDecl {
    pub name: String,
    pub name_span: Sp,
    pub fields: Vec<FieldDecl>,
    pub meta: Meta,
}

#[derive(Clone, Debug, PartialEq)]
pub struct FieldDecl {
    pub name: String,
    pub name_span: Sp,
    pub ty: TypeNode,
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
    label: Label,
}

/// 単相型。共有 DAG で表し、深さはキャッシュする。ErrorType は深さ0。
#[derive(Clone)]
pub struct Ty(Arc<TyNode>);

impl Ty {
    pub fn new(tag: TyTag, args: Vec<Ty>) -> Ty {
        let depth = if tag == TyTag::Error { 0 } else { 1 + args.iter().map(|a| a.depth()).max().unwrap_or(0) };
        Ty(Arc::new(TyNode { tag, args, depth, label: Label::default() }))
    }
    /// レコード名を付けた型（等価性は変わらない）。
    pub fn labeled(&self, label: Label) -> Ty {
        Ty(Arc::new(TyNode { tag: self.0.tag, args: self.0.args.clone(), depth: self.0.depth, label }))
    }
    /// レコード名を外した型。
    pub fn unlabeled(&self) -> Ty {
        self.labeled(Label::default())
    }
    pub fn record(&self) -> Option<&Arc<RecordInfo>> {
        match &self.0.label.0 {
            Some(Named::Record(r)) => Some(r),
            _ => None,
        }
    }
    /// v1.4：直和型の名前と variant。
    pub fn sum(&self) -> Option<&Arc<SumInfo>> {
        match &self.0.label.0 {
            Some(Named::Sum(s)) => Some(s),
            _ => None,
        }
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
    pub fn char() -> Ty {
        Ty::new(TyTag::Char, vec![])
    }
    /// `String`（= `List<Char>`）
    pub fn string() -> Ty {
        Ty::list(Ty::char())
    }
    /// `List<Char>`（表示は `String`）か。
    pub fn is_string(&self) -> bool {
        self.0.tag == TyTag::List && self.0.args[0].tag() == TyTag::Char
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
    pub fn result(a: Ty, b: Ty) -> Ty {
        Ty::new(TyTag::Result, vec![a, b])
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
        let t = Ty::new(node.tag, node.args.iter().map(Ty::of).collect());
        if node.label.0.is_some() {
            t.labeled(node.label.clone())
        } else {
            t
        }
    }

    fn write_limited(&self, out: &mut String, budget: &mut usize) {
        if *budget == 0 {
            return;
        }
        if let Some(r) = &self.0.label.0 {
            let name = r.name();
            if name.len() <= *budget {
                out.push_str(name);
                *budget -= name.len();
            } else {
                out.push('…');
                *budget = 0;
            }
            return;
        }
        let name = if self.is_string() { "String" } else { self.0.tag.name() };
        if name.len() > *budget {
            out.push('…');
            *budget = 0;
            return;
        }
        out.push_str(name);
        *budget -= name.len();
        if !self.0.args.is_empty() && !self.is_string() {
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
