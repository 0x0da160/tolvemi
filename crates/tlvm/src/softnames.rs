//! v1.1 の文脈キーワード（差分仕様 §2a）。
//!
//! 組み込み関数と値の構築子の名前（`length`、`pair` など）は、呼び出しの位置（直後が `(` か `<`）
//! でだけキーワードとして働き、変数・引数・束縛・field の名前には使える。検証済み部品の構文規則は
//! これを直接受け付ける。AST transport（ast_codec_v1）の名前は字句表の 68 語をすべて除くので、
//! `tlvm ast` と `encode_ast` は、そうした語を変数などの名前に使ったプログラムを付け替えずに拒否する
//! （`E-AST-IDENTIFIER`、§4.2）。
//!
//! この拒否は検証されていない接着部分（`trust-boundary.toml` の `glue`）。誤って通しても、AST transport の
//! decoder が同じ名前を `E-AST-IDENTIFIER` で拒否するので、受理の判定は変わらない。

use crate::diagnostics::{Diagnostic, Span};
use crate::syntax::*;

/// 変数名として使える予約語（組み込み関数と値の構築子の名前）。
/// v1.5：`map filter any all find sort_by` も（直後が `(` のときだけ特殊形式）。v1.6：`loop` も。v1.8：`div` も。
/// v1.9：`dict` と `dict_get` などの辞書の操作も（`Dict` は予約語でなく、型の位置で直後が `<` のときだけ辞書の型）。
pub const SOFT_KEYWORDS: [&str; 49] = [
    "entry",
    "list",
    "some",
    "none",
    "pair",
    "ok",
    "err",
    "add",
    "sub",
    "mul",
    "neg",
    "lt",
    "le",
    "eq",
    "mod",
    "fst",
    "snd",
    "cons",
    "concat",
    "reverse",
    "length",
    "uncons",
    "min",
    "max",
    "range",
    "contains",
    "sort",
    "code",
    "char",
    "to_string",
    "parse_int",
    "map",
    "filter",
    "any",
    "all",
    "find",
    "sort_by",
    "loop",
    "div",
    "dict",
    "dict_get",
    "dict_put",
    "dict_remove",
    "dict_has",
    "dict_size",
    "dict_keys",
    "dict_values",
    "dict_entries",
    "dict_from",
];

pub fn is_soft_keyword(s: &str) -> bool {
    SOFT_KEYWORDS.contains(&s)
}

/// 式の中の名前（変数・束縛・利用者関数の呼出し）を、その位置つきで集める（ソース順とは限らない）。
fn names_in<'a>(e: &'a Expr, out: &mut Vec<(&'a str, Span)>) {
    let m = e.meta.span();
    match &e.kind {
        ExprKind::Var(x) => out.push((x.as_str(), m)),
        ExprKind::Let {
            name, name_span, ..
        } => out.push((name.as_str(), name_span.t())),
        ExprKind::Fold {
            acc,
            acc_span,
            item,
            item_span,
            ..
        } => {
            out.push((acc.as_str(), acc_span.t()));
            out.push((item.as_str(), item_span.t()));
        }
        ExprKind::Match {
            binder,
            binder_span,
            ..
        }
        | ExprKind::Hof {
            binder,
            binder_span,
            ..
        }
        | ExprKind::Loop {
            binder,
            binder_span,
            ..
        } => out.push((binder.as_str(), binder_span.t())),
        ExprKind::MatchResult {
            ok_binder,
            ok_span,
            err_binder,
            err_span,
            ..
        } => {
            out.push((ok_binder.as_str(), ok_span.t()));
            out.push((err_binder.as_str(), err_span.t()));
        }
        ExprKind::SumMatch { arms, .. } => {
            for a in arms {
                out.extend(a.pat.binds.iter().map(|(b, s)| (b.as_str(), s.t())));
            }
        }
        ExprKind::Call {
            callee,
            builtin: false,
            callee_span,
            ..
        } => out.push((callee.as_str(), callee_span.t())),
        _ => {}
    }
    for c in e.children() {
        names_in(c, out);
    }
}

/// 字句表の 68 語（予約語と文脈キーワード）を AST の名前に使った箇所のうち、ソース順で最初のものを
/// `E-AST-IDENTIFIER` の診断にする。AST transport の decoder と同じ規則（§4.2、§19.2）。
pub fn keyword_name_error(p: &Program) -> Option<Diagnostic> {
    let mut uses: Vec<(&str, Span)> = vec![];
    for d in &p.declarations {
        match d {
            Decl::Fn(fd) => {
                uses.push((fd.name.as_str(), fd.name_span.t()));
                uses.extend(fd.type_params.iter().map(|t| (t.name.as_str(), t.span.t())));
                uses.extend(fd.params.iter().map(|q| (q.name.as_str(), q.name_span.t())));
                names_in(&fd.body, &mut uses);
            }
            Decl::Entry(e) => uses.push((e.name.as_str(), e.name_span.t())),
            Decl::Type(_) | Decl::Sum(_) => {}
        }
    }
    let (name, span) = uses
        .into_iter()
        .filter(|(n, _)| is_keyword(n))
        .min_by_key(|(_, s)| s.0)?;
    Some(
        Diagnostic::error("ast-schema", "E-AST-IDENTIFIER", span).exp("identifier").act(name).fix(
            "replace_identifier",
            span,
            format!("'{name}' is a keyword, which an AST name cannot be: use another name such as {name}_ here and at every use"),
        ),
    )
}
