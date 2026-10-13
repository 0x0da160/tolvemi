//! 表面 AST と意味論上の型（設計書 §3、§4.1、§19.2）。
//!
//! AST node は span（UTF-8 bytes の半開区間）と論理 node index（前順 Admission index）を
//! 持つが、構造的等価性の比較対象には含めない（`Meta` と `Sp` の `PartialEq` は常に真）。

use num_bigint::BigInt;
use std::fmt;
use std::sync::Arc;

pub const KEYWORDS: [&str; 68] = [
    "fn", "entry", "Int", "Bool", "Unit", "List", "Option", "Pair", "true", "false", "unit", "list", "some", "none",
    "pair", "let", "in", "if", "fold", "add", "sub", "mul", "neg", "lt", "le", "eq", "mod", "fst", "snd", "cons",
    "concat", "reverse", "length", "uncons", "match_option", "min", "max", "range", "contains", "sort", "Char", "String",
    "code", "char", "to_string", "parse_int", "Result", "ok", "err", "match_result", "map", "filter", "any", "all", "find",
    "sort_by", "loop", "div", "dict", "dict_get", "dict_put", "dict_remove", "dict_has", "dict_size", "dict_keys",
    "dict_values", "dict_entries", "dict_from",
];

pub fn is_keyword(s: &str) -> bool {
    KEYWORDS.contains(&s)
}

pub fn builtin_arity(name: &str) -> Option<usize> {
    Some(match name {
        "add" | "sub" | "mul" | "lt" | "le" | "eq" | "mod" | "div" | "cons" | "concat" | "min" | "max" | "range" | "contains" => 2,
        "neg" | "fst" | "snd" | "reverse" | "length" | "uncons" | "sort" | "code" | "char" | "to_string" | "parse_int" => 1,
        // v1.9：辞書の操作（`dict::lower_op` が fold などに書き換える）
        "dict_put" => 3,
        "dict_get" | "dict_remove" | "dict_has" => 2,
        "dict_size" | "dict_keys" | "dict_values" | "dict_entries" | "dict_from" => 1,
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
    /// v1.9：`Dict<K, V>`（型検査の後で `List<Pair<K, V>>` に書き換える。`dict` モジュール）
    Dict,
    /// v1.10：型引数 `T`（総称の関数・型の宣言の中だけ。単相化の後には残らない。`generics` モジュール）。
    /// 名前は `TypeNode::name`（意味論上の型では `Ty::param_name`）
    Param,
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
            TyTag::Dict => "Dict",
            TyTag::Param => "Param",
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
            TyTag::Pair | TyTag::Result | TyTag::Dict => 2,
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

/// v1.7：関数の印 `rec`（文脈キーワード。最上位で直後が `fn` のときだけ印。予約語ではない）。
pub const REC: &str = "rec";

/// v1.6：上限つき反復 `loop(init, max, |s| e)` の名前。
pub const LOOP: &str = "loop";

/// v1.9：辞書の型の名前（予約語ではない。型の位置で直後が `<` のときだけ `Dict<K, V>`）。
pub const DICT_TYPE: &str = "Dict";

/// v1.9：空の辞書 `dict<K, V>()` の名前。
pub const DICT_NEW: &str = "dict";

/// v1.9：辞書の操作（組み込み関数の形。`dict::lower_op` が fold などに書き換える）。
pub const DICT_OPS: [&str; 9] =
    ["dict_get", "dict_put", "dict_remove", "dict_has", "dict_size", "dict_keys", "dict_values", "dict_entries", "dict_from"];

/// v1.9：辞書の名前（`dict` と操作）か。
pub fn is_dict_word(s: &str) -> bool {
    s == DICT_NEW || DICT_OPS.contains(&s)
}

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
    /// v1.10：型引数 `name` の node。
    pub fn param(name: &str, meta: Meta) -> TypeNode {
        TypeNode { name: Some(name.to_string()), ..TypeNode::new(TyTag::Param, vec![], meta) }
    }
    /// v1.10：レコード型・直和型の名前（展開前。型引数 `T` は含まない）か。
    pub fn is_named(&self) -> bool {
        self.name.is_some() && self.tag != TyTag::Param
    }
    /// v1.10：型引数を含むか。
    pub fn has_params(&self) -> bool {
        self.tag == TyTag::Param || self.args.iter().any(TypeNode::has_params)
    }
    /// v1.10：型引数を置き換える（`f` が None を返す型引数は残す）。置き換えた node に名前（レコード型・直和型の
    /// label）が付いていれば、置き換え後の node に移す（一つの field のレコード `type Box<T> = { v: T }` の展開は
    /// 型引数そのものに名前が付く）。
    pub fn subst(&self, f: &dyn Fn(&str) -> Option<TypeNode>) -> TypeNode {
        if self.tag == TyTag::Param {
            return match self.name.as_deref().and_then(f) {
                Some(mut r) => {
                    if self.label.0.is_some() {
                        r.label = self.label.clone();
                    }
                    r
                }
                None => self.clone(),
            };
        }
        if !self.has_params() {
            return self.clone();
        }
        TypeNode { args: self.args.iter().map(|a| a.subst(f)).collect(), ..self.clone() }
    }
}

/// v1.10：宣言の型引数 `<T, U>` の一つ（名前は大文字で始まる）。
#[derive(Clone, Debug, PartialEq)]
pub struct TypeParam {
    pub name: String,
    pub span: Sp,
}

/// レコード型の名前と field 名（宣言順）。
#[derive(Debug)]
pub struct RecordInfo {
    pub name: String,
    pub fields: Vec<String>,
    /// v1.10：型引数（総称のレコード型のとき）と、型引数を含む展開後の型（表示で `Box<Int>` の型引数を復元する）
    pub generic: Option<Generic>,
}

/// v1.10：総称のレコード型・直和型の型引数の名前と、型引数を含む展開後の型（型引数はすべてこの型に現れる）。
#[derive(Debug, Clone)]
pub struct Generic {
    pub params: Vec<String>,
    pub template: TypeNode,
}

/// v1.4：ユーザー定義の直和型の名前と variant（宣言順。名前と中身の数）。
#[derive(Debug)]
pub struct SumInfo {
    pub name: String,
    pub variants: Vec<(String, usize)>,
    /// variant が一つで中身が一つのとき、その中身の型に付いていた名前（型全体の名前で上書きされるので別に持つ）
    pub inner: Label,
    /// v1.10：総称の直和型の型引数と展開後の型
    pub generic: Option<Generic>,
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
    /// v1.10：総称の型なら型引数と展開後の型。
    pub fn generic(&self) -> Option<&Generic> {
        match self {
            Named::Record(r) => r.generic.as_ref(),
            Named::Sum(s) => s.generic.as_ref(),
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
    /// v1.10：`type_args` は明示した型引数 `f<Int>(x)`（書かなければ空。総称の関数なら型検査で推論する）
    Call { callee: String, args: Vec<Expr>, builtin: bool, callee_span: Sp, type_args: Vec<TypeNode> },
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
    /// v1.9：空の辞書 `dict<K, V>()`（型は `Dict<K, V>` の型 node）
    DictNew(TypeNode),
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
    /// v1.7：`rec fn` の印（上限なしの再帰を許す。停止は保証しない）
    pub rec: bool,
    /// v1.7：印 `rec` の span（source から読んだときだけ。比較対象外）
    pub rec_span: Sp,
    /// v1.10：型引数 `fn f<T, U>(...)`（なければ空）
    pub type_params: Vec<TypeParam>,
    /// v1.10：総称の直和型の構築子のために展開で作った関数なら、その構築子の名前（診断の表示用。未使用の警告を出さない）
    pub ctor: Option<String>,
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
    /// v1.10：型引数 `type Tree<T> = ...`
    pub type_params: Vec<TypeParam>,
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
    /// v1.10：型引数 `type Box<T> = { ... }`
    pub type_params: Vec<TypeParam>,
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
    /// v1.11：先頭の `import "path.tlvm"`（宣言より前）。ファイルからの検査（`api::compile_files`）が解決して
    /// 一つのプログラムにまとめる。source の文字列だけを受け取る API では E-IMPORT-UNSUPPORTED
    pub imports: Vec<ImportDecl>,
}

/// v1.11：`import "path.tlvm"`。`path` は復号した文字列、`span` は `import` から文字列リテラルの終わりまで。
#[derive(Clone, Debug, PartialEq)]
pub struct ImportDecl {
    pub path: String,
    pub path_span: Sp,
    pub span: Sp,
}

impl Program {
    pub fn functions(&self) -> impl Iterator<Item = &FnDecl> {
        self.declarations.iter().filter_map(|d| match d {
            Decl::Fn(f) => Some(f),
            _ => None,
        })
    }
    /// v1.7：`rec` の印のある関数があるか（あれば停止は保証されない）。
    pub fn has_rec(&self) -> bool {
        self.functions().any(|f| f.rec)
    }
    /// v1.7：印 `rec` を外したプログラム（検証済み部品に渡す整形ソース用。印は別に渡す）。
    pub fn unmarked(&self) -> Program {
        let mut p = self.clone();
        for d in &mut p.declarations {
            if let Decl::Fn(f) = d {
                f.rec = false;
            }
        }
        p
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
    /// v1.10：型引数（tag が Param のとき）の名前
    pname: Option<Arc<str>>,
    /// v1.10：型引数を含むか
    params: bool,
}

/// 単相型。共有 DAG で表し、深さはキャッシュする。ErrorType は深さ0。
#[derive(Clone)]
pub struct Ty(Arc<TyNode>);

impl Ty {
    pub fn new(tag: TyTag, args: Vec<Ty>) -> Ty {
        let depth = if tag == TyTag::Error { 0 } else { 1 + args.iter().map(|a| a.depth()).max().unwrap_or(0) };
        let params = args.iter().any(|a| a.has_params());
        Ty(Arc::new(TyNode { tag, args, depth, label: Label::default(), pname: None, params }))
    }
    /// v1.10：型引数 `name`（総称の関数の本体では、どの型にも使える操作だけが通る不透明な型）。
    pub fn param(name: &str) -> Ty {
        Ty(Arc::new(TyNode { tag: TyTag::Param, args: vec![], depth: 1, label: Label::default(), pname: Some(name.into()), params: true }))
    }
    /// v1.10：型引数の名前（型引数でなければ None）。
    pub fn param_name(&self) -> Option<&str> {
        self.0.pname.as_deref()
    }
    /// v1.10：型引数を含むか。
    pub fn has_params(&self) -> bool {
        self.0.params
    }
    /// v1.10：型に付いた名前（レコード型・直和型。単相化で型を構文に戻すとき用）
    pub fn label(&self) -> Label {
        self.0.label.clone()
    }
    /// v1.10：型引数を置き換える（`f` が None を返す型引数は残す）。名前（label）は保つ。置き換えた型引数に
    /// 名前が付いていれば置き換え後の型に移す（`TypeNode::subst` と同じ）。
    pub fn subst(&self, f: &dyn Fn(&str) -> Option<Ty>) -> Ty {
        if !self.0.params {
            return self.clone();
        }
        if let Some(n) = &self.0.pname {
            return match f(n) {
                Some(r) if self.0.label.0.is_some() => r.labeled(self.0.label.clone()),
                Some(r) => r,
                None => self.clone(),
            };
        }
        let t = Ty::new(self.0.tag, self.0.args.iter().map(|a| a.subst(f)).collect());
        if self.0.label.0.is_some() {
            t.labeled(self.0.label.clone())
        } else {
            t
        }
    }
    /// v1.10：`pattern` の型引数を `self` の対応する部分に束縛する（一方向の照合。`self` の型引数は定数として扱う）。
    /// 形が違うか、同じ型引数に違う型が当たれば None。束縛は `out` に足す（既にある束縛とも照合する）。
    pub fn bind(pattern: &Ty, target: &Ty, out: &mut Vec<(Arc<str>, Ty)>) -> Option<()> {
        // 展開前の名前が残った部分（表示用の展開後の型の一部）は何にでも合う
        if pattern.0.tag == TyTag::Error {
            return Some(());
        }
        if let Some(n) = &pattern.0.pname {
            return match out.iter().find(|(m, _)| m == n) {
                Some((_, t)) => (t == target).then_some(()),
                None => {
                    out.push((n.clone(), target.clone()));
                    Some(())
                }
            };
        }
        if !pattern.0.params {
            return (pattern == target).then_some(());
        }
        if pattern.0.tag != target.0.tag || pattern.0.args.len() != target.0.args.len() {
            return None;
        }
        for (p, t) in pattern.0.args.iter().zip(&target.0.args) {
            Ty::bind(p, t, out)?;
        }
        Some(())
    }
    /// レコード名を付けた型（等価性は変わらない）。
    pub fn labeled(&self, label: Label) -> Ty {
        Ty(Arc::new(TyNode {
            tag: self.0.tag,
            args: self.0.args.clone(),
            depth: self.0.depth,
            label,
            pname: self.0.pname.clone(),
            params: self.0.params,
        }))
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
    /// v1.9：`Dict<K, V>`
    pub fn dict(k: Ty, v: Ty) -> Ty {
        Ty::new(TyTag::Dict, vec![k, v])
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
        let t = if node.tag == TyTag::Param {
            Ty::param(node.name.as_deref().unwrap_or("?"))
        } else {
            Ty::new(node.tag, node.args.iter().map(Ty::of).collect())
        };
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
                return;
            }
            // v1.10：総称の型は、展開後の型と照合して型引数を復元する（`Box<Int>`）
            if let Some(g) = r.generic() {
                let mut b = vec![];
                let found = Ty::bind(&Ty::of(&g.template), &self.unlabeled(), &mut b).is_some();
                out.push('<');
                for (i, p) in g.params.iter().enumerate() {
                    if i > 0 {
                        out.push_str(", ");
                    }
                    match b.iter().find(|(n, _)| &**n == p.as_str()) {
                        Some((_, t)) if found => t.write_limited(out, budget),
                        _ => out.push('?'),
                    }
                    if *budget == 0 {
                        return;
                    }
                }
                out.push('>');
            }
            return;
        }
        if let Some(n) = &self.0.pname {
            if n.len() > *budget {
                out.push('…');
                *budget = 0;
            } else {
                out.push_str(n);
                *budget -= n.len();
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
        Arc::ptr_eq(&self.0, &other.0)
            || (self.0.tag == other.0.tag && self.0.pname == other.0.pname && self.0.args == other.0.args)
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
