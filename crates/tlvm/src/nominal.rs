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
//! 印の型と印の値（`tag_ty`・`tag_val`）は、検証済みの exec 版（`tlvm_verified::resolve::tag_ty_e`・`tag_expr_e`）を写す。
//! 印の番号（`Tags::of`）は、検証済みの exec 版（`tlvm_verified::tagged_names::seen_names_e`）が決める。
//! 名前つきの型・補助関数（`named_ty`・`wrap_fn`）は、検証されていない接着部分（`trust-boundary.toml` の `glue`）のまま。

use crate::syntax::*;
use std::collections::HashMap;
use tlvm_verified::ir::EExpr;
use tlvm_verified::resolve::{tag_expr_e, tag_ty_e};
use tlvm_verified::spec::Ty as VTy;

/// 宣言の番号：レコード型と直和型の宣言の順（同じ名前の二つ目以降は数えない）。
#[derive(Clone, Default)]
pub struct Tags {
    idx: HashMap<String, usize>,
}

impl Tags {
    /// 型の宣言（レコード型・直和型）の名前を宣言の順に並べ、番号を決める（関数と entry は数えない）。
    pub fn of(p: &Program) -> Tags {
        let names: Vec<&str> = p
            .declarations
            .iter()
            .filter_map(|d| match d {
                Decl::Type(t) => Some(t.name.as_str()),
                Decl::Sum(s) => Some(s.name.as_str()),
                Decl::Fn(_) | Decl::Entry(_) => None,
            })
            .collect();
        Tags::from_names(&names)
    }

    /// 名前の列から番号を作る。番号は、最初に現れた順の相異なる名前の位置（同じ名前の後の方は数えない）。
    /// 位置は検証済みの `seen_names_e` が作る。
    pub fn from_names(names: &[&str]) -> Tags {
        let chars: Vec<Vec<char>> = names.iter().map(|n| n.chars().collect()).collect();
        let seen = tlvm_verified::tagged_names::seen_names_e(&chars);
        let idx = seen
            .iter()
            .enumerate()
            .map(|(i, n)| (n.iter().collect::<String>(), i))
            .collect();
        Tags { idx }
    }

    /// 型の名前の番号（宣言していなければ None）。
    pub fn get(&self, name: &str) -> Option<usize> {
        self.idx.get(name).copied()
    }
}

/// 番号 `r` の印の型：`Pair<Unit, Unit>` を r 段入れ子にしたもの（段数が違えば別の型になる）。検証済みの `tag_ty_e` を写す。
pub fn tag_ty(r: usize, m: Meta) -> TypeNode {
    verified_tag_ty(&tag_ty_e(r), m)
}

/// 番号 `r` の印の値（`tag_ty(r)` の型）。検証済みの `tag_expr_e` を写す。
pub fn tag_val(r: usize, m: Meta) -> Expr {
    verified_tag_val(&tag_expr_e(r), m)
}

/// 検証済みの印の型を写す（Unit と Pair だけ。`tag_ty_e` はこれ以外の型を作らない）。
fn verified_tag_ty(t: &VTy, m: Meta) -> TypeNode {
    match t {
        VTy::Unit => TypeNode::new(TyTag::Unit, vec![], m),
        VTy::Pair(a, b) => TypeNode::new(
            TyTag::Pair,
            vec![verified_tag_ty(a, m), verified_tag_ty(b, m)],
            m,
        ),
        _ => unreachable!("the tag types are built from Unit and Pair"),
    }
}

/// 検証済みの印の式を写す（Unit と Pair だけ。`tag_expr_e` はこれ以外の式を作らない）。
fn verified_tag_val(e: &EExpr, m: Meta) -> Expr {
    match e {
        EExpr::Unit => ex(ExprKind::Unit, m),
        EExpr::Pair(a, b) => pair(verified_tag_val(a, m), verified_tag_val(b, m), m),
        _ => unreachable!("the tag values are built from Unit and Pair"),
    }
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

#[cfg(test)]
mod tests {
    use super::*;

    /// 検証済みの版を使う前の印の型（比べる基準）。
    fn old_tag_ty(r: usize, m: Meta) -> TypeNode {
        let unit = || TypeNode::new(TyTag::Unit, vec![], m);
        let mut t = TypeNode::new(TyTag::Pair, vec![unit(), unit()], m);
        for _ in 0..r {
            t = TypeNode::new(TyTag::Pair, vec![unit(), t], m);
        }
        t
    }

    /// 検証済みの版を使う前の印の値（比べる基準）。
    fn old_tag_val(r: usize, m: Meta) -> Expr {
        let unit = || ex(ExprKind::Unit, m);
        let mut v = pair(unit(), unit(), m);
        for _ in 0..r {
            v = pair(unit(), v, m);
        }
        v
    }

    /// 番号は、最初に現れた順の相異なる名前の位置。検証済みの版を使う前の、名前を表に入れる書き方と同じ結果になる。
    #[test]
    fn numbers_follow_the_first_occurrence_of_each_name() {
        let cases: [&[&str]; 4] = [
            &[],
            &["A", "B", "C"],
            &["A", "B", "A", "C", "B"],
            &["A", "A"],
        ];
        for names in cases {
            let mut old: HashMap<String, usize> = HashMap::new();
            for n in names {
                let k = old.len();
                old.entry(n.to_string()).or_insert(k);
            }
            let tags = Tags::from_names(names);
            for n in ["A", "B", "C", "D"] {
                assert_eq!(tags.get(n), old.get(n).copied(), "name {n} in {names:?}");
            }
        }
    }

    #[test]
    fn verified_tags_match_the_rust_construction() {
        let m = Meta::new((0, 0), 0);
        for r in 0..12 {
            assert_eq!(
                format!("{:?}", tag_ty(r, m)),
                format!("{:?}", old_tag_ty(r, m)),
                "tag type {r}"
            );
            assert_eq!(
                format!("{:?}", tag_val(r, m)),
                format!("{:?}", old_tag_val(r, m)),
                "tag value {r}"
            );
        }
    }
}
