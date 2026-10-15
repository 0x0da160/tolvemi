//! v1.15：名義の型（型の名前による区別）。
//!
//! 宣言した型（レコード型・直和型・再帰する直和型。総称の型は宣言ごとに一つ）は、展開後の構造が同じでも
//! 型の名前で区別する。展開で名前を消すと区別できないので、検査用の写し（印つきの写し）では、宣言の番号 `r` の
//! 型 `T` を `Pair<印 r, S>` とする（`S` は展開後の構造。印 `r` は `Pair<Unit, Unit>` を r 段入れ子にした型で、
//! 宣言ごとに違う）。構築は `<名前>_wrap` を通して印を付ける（結果の型は印つきの型）。取り出し（field の参照と
//! `match`）は印つきの型のまま検査し（型検査器が印を検査する）、検証済みの部品へ渡す前に印を外す（`is_tagged`）。
//! 実行する写し（印なし）は今までどおり構造だだけで書き、印を付けない。
//!
//! 印の番号は、展開の前のプログラムの宣言の順で一度だけ決める（`Tags::of`）。総称の型は宣言ごとの一つの印で、
//! 型引数の違いは構造の違いとして現れる（型引数は型の中に残る）。
//!
//! 書き換えは検証されていない接着部分（`trust-boundary.toml` の `glue`）。

use crate::syntax::*;
use std::collections::HashMap;

/// 宣言の番号：レコード型と直和型の宣言の順（同じ名前の二つ目以降は数えない）。
#[derive(Clone, Default)]
pub struct Tags {
    idx: HashMap<String, usize>,
}

impl Tags {
    pub fn of(p: &Program) -> Tags {
        let mut idx: HashMap<String, usize> = HashMap::new();
        for d in &p.declarations {
            let name = match d {
                Decl::Type(t) => &t.name,
                Decl::Sum(s) => &s.name,
                Decl::Fn(_) | Decl::Entry(_) => continue,
            };
            let n = idx.len();
            idx.entry(name.clone()).or_insert(n);
        }
        Tags { idx }
    }

    /// 型の名前の番号（宣言していなければ None）。
    pub fn get(&self, name: &str) -> Option<usize> {
        self.idx.get(name).copied()
    }
}

/// 番号 `r` の印の型：`Pair<Unit, Unit>` を r 段入れ子にしたもの（段数が違えば別の型になる）。
pub fn tag_ty(r: usize, m: Meta) -> TypeNode {
    let unit = || TypeNode::new(TyTag::Unit, vec![], m);
    let mut t = TypeNode::new(TyTag::Pair, vec![unit(), unit()], m);
    for _ in 0..r {
        t = TypeNode::new(TyTag::Pair, vec![unit(), t], m);
    }
    t
}

/// 番号 `r` の印の値（`tag_ty(r)` の型）。
pub fn tag_val(r: usize, m: Meta) -> Expr {
    let unit = || ex(ExprKind::Unit, m);
    let mut v = pair(unit(), unit(), m);
    for _ in 0..r {
        v = pair(unit(), v, m);
    }
    v
}

/// 番号 `r` の名前付きの型：`Pair<印 r, inner>`。`label` は表示用の名前と型引数（型の等価性には含めない）。
pub fn named_ty(r: usize, inner: TypeNode, label: Label, m: Meta) -> TypeNode {
    let mut t = TypeNode::new(TyTag::Pair, vec![tag_ty(r, m), inner], m);
    t.label = label;
    t
}

pub fn ex(kind: ExprKind, m: Meta) -> Expr {
    Expr { kind, meta: m }
}

fn var(n: &str, m: Meta) -> Expr {
    ex(ExprKind::Var(n.to_string()), m)
}

fn pair(a: Expr, b: Expr, m: Meta) -> Expr {
    ex(ExprKind::Pair(Box::new(a), Box::new(b)), m)
}

/// 組み込みの関数の呼び出し（`snd` など）。
pub fn builtin(f: &str, args: Vec<Expr>, m: Meta) -> Expr {
    ex(
        ExprKind::Call {
            callee: f.to_string(),
            args,
            builtin: true,
            callee_span: m.span,
            type_args: vec![],
        },
        m,
    )
}

/// 補助関数の呼び出し（利用者の関数と同じ扱い。型引数は引数の型から推論する）。
pub fn call(f: &str, arg: Expr, m: Meta) -> Expr {
    ex(
        ExprKind::Call {
            callee: f.to_string(),
            args: vec![arg],
            builtin: false,
            callee_span: m.span,
            type_args: vec![],
        },
        m,
    )
}

/// 補助関数の宣言（診断の未使用の警告は出さない）。`ctor` は診断に出す名前（型の名前）。
fn helper(
    name: &str,
    params: Vec<(&str, TypeNode)>,
    ret: TypeNode,
    body: Expr,
    tparams: &[TypeParam],
    m: Meta,
    ctor: &str,
) -> FnDecl {
    FnDecl {
        name: name.to_string(),
        name_span: Sp::default(),
        params: params
            .into_iter()
            .map(|(n, ty)| Param {
                name: n.to_string(),
                name_span: Sp::default(),
                ty,
                meta: m,
            })
            .collect(),
        return_type: ret,
        body,
        meta: m,
        rec: false,
        rec_span: Sp::default(),
        type_params: tparams.to_vec(),
        ctor: Some(ctor.to_string()),
    }
}

/// 印を付ける補助関数 `name(x: inner) -> named = pair(印, x)`。`named` は `named_ty(r, inner, ..)`。
pub fn wrap_fn(
    name: &str,
    r: usize,
    inner: TypeNode,
    named: TypeNode,
    tparams: &[TypeParam],
    m: Meta,
    ctor: &str,
) -> FnDecl {
    let body = pair(tag_val(r, m), var("x", m), m);
    helper(name, vec![("x", inner)], named, body, tparams, m, ctor)
}

/// 印つきの型（名義の型の印を付けた型）か。`match` と field の参照は、この型の値から印を外してから中身を取り出す。
pub fn is_tagged(t: &TypeNode) -> bool {
    match &t.label.0 {
        Some(Named::Record(r)) => r.tagged,
        Some(Named::Sum(s)) => s.tagged,
        None => false,
    }
}
