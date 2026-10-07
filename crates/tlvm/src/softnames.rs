//! v1.1 の文脈キーワード（差分仕様 §2a）。
//!
//! 組み込み関数と値の構築子の名前（`length`、`pair` など）は、呼び出しの位置（直後が `(` か `<`）
//! でだけキーワードとして働き、変数・引数・束縛・field の名前には使える。検証済み部品の字句規則は
//! これらを常に予約語として扱うので、検証済み部品に渡す前に、そうした変数名をプログラム中の
//! どの識別子とも重ならない名前に一斉に付け替える（α 変換なので、名前の解決と評価の結果は変わらない）。
//!
//! 付け替えは検証されていない接着部分（`trust-boundary.toml` の `glue`）。

use crate::syntax::*;
use std::collections::{HashMap, HashSet};

/// 変数名として使える予約語（組み込み関数と値の構築子の名前）。
pub const SOFT_KEYWORDS: [&str; 19] = [
    "list", "some", "none", "pair", "add", "sub", "mul", "neg", "lt", "le", "eq", "mod", "fst", "snd", "cons",
    "concat", "reverse", "length", "uncons",
];

pub fn is_soft_keyword(s: &str) -> bool {
    SOFT_KEYWORDS.contains(&s)
}

fn walk<'a>(e: &'a Expr, f: &mut impl FnMut(&'a str)) {
    match &e.kind {
        ExprKind::Var(x) => f(x),
        ExprKind::Let { name, .. } => f(name),
        ExprKind::Fold { acc, item, .. } => {
            f(acc);
            f(item);
        }
        ExprKind::Match { binder, .. } => f(binder),
        ExprKind::Call { callee, builtin: false, .. } => f(callee),
        _ => {}
    }
    for c in e.children() {
        walk(c, f);
    }
}

/// プログラム中の変数・引数・束縛の名前（関数名を含む）。
fn names(p: &Program) -> Vec<&str> {
    let mut out = vec![];
    for d in &p.declarations {
        match d {
            Decl::Fn(fd) => {
                out.push(fd.name.as_str());
                out.extend(fd.params.iter().map(|q| q.name.as_str()));
                walk(&fd.body, &mut |x| out.push(x));
            }
            Decl::Entry(e) => out.push(e.name.as_str()),
            Decl::Type(_) => {}
        }
    }
    out
}

/// 予約語を名前に使った変数・引数・束縛を含むか。
pub fn has_soft_names(p: &Program) -> bool {
    names(p).into_iter().any(is_soft_keyword)
}

/// 予約語の名前をプログラム中に現れない名前（`length_kw` など）に付け替える。
pub fn rename(p: &Program) -> Program {
    let taken: HashSet<String> = names(p).into_iter().map(String::from).collect();
    let mut map: HashMap<String, String> = HashMap::new();
    for w in SOFT_KEYWORDS {
        let mut n = format!("{w}_kw");
        while taken.contains(&n) {
            n.push('_');
        }
        map.insert(w.to_string(), n);
    }
    let r = |s: &mut String| {
        if let Some(n) = map.get(s.as_str()) {
            *s = n.clone();
        }
    };
    fn ex(e: &mut Expr, r: &dyn Fn(&mut String)) {
        match &mut e.kind {
            ExprKind::Var(x) => r(x),
            ExprKind::List { items, .. } => items.iter_mut().for_each(|x| ex(x, r)),
            ExprKind::Some(v) => ex(v, r),
            ExprKind::Pair(a, b) => {
                ex(a, r);
                ex(b, r);
            }
            ExprKind::Call { args, .. } => args.iter_mut().for_each(|x| ex(x, r)),
            ExprKind::Let { name, value, body, .. } => {
                r(name);
                ex(value, r);
                ex(body, r);
            }
            ExprKind::If(c, t, f) => {
                ex(c, r);
                ex(t, r);
                ex(f, r);
            }
            ExprKind::Fold { list, init, acc, item, body, .. } => {
                ex(list, r);
                ex(init, r);
                r(acc);
                r(item);
                ex(body, r);
            }
            ExprKind::Match { scrutinee, on_none, binder, on_some, .. } => {
                ex(scrutinee, r);
                ex(on_none, r);
                r(binder);
                ex(on_some, r);
            }
            ExprKind::Record { fields, base, .. } => {
                fields.iter_mut().for_each(|f| ex(&mut f.value, r));
                if let Some(b) = base {
                    ex(b, r);
                }
            }
            ExprKind::Field { expr, .. } => ex(expr, r),
            ExprKind::Int(_) | ExprKind::Bool(_) | ExprKind::Unit | ExprKind::None(_) => {}
        }
    }
    let mut out = p.clone();
    for d in &mut out.declarations {
        if let Decl::Fn(fd) = d {
            fd.params.iter_mut().for_each(|q| r(&mut q.name));
            ex(&mut fd.body, &r);
        }
    }
    out
}
