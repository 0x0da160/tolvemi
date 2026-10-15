//! v1.10 のユーザー定義の型引数（総称の関数・レコード型・直和型。差分仕様 §1、§2）。
//!
//! 処理は四段に分かれる。
//!
//! 1. `resolve`（診断の phase は name）：宣言の型引数 `<T, U>` を検査し、型の位置に書いた `T` を `TyTag::Param` の
//!    node にする（宣言されていない型引数、重複、型の名前との衝突、型の宣言で使わない型引数を拒否する）。
//!    総称のレコード型・直和型の展開（`Box<Int>` の型引数の置き換え）は `records::expand`・`sums::expand` が行う。
//! 2. 型検査（`checker`）：総称の関数の本体は一度だけ、型引数を不透明な型として検査する（どの型にも使える操作
//!    だけが通る。`eq` は全ての値が構造的等価性を持つので使える）。呼び出しの型引数は明示したものか、引数の型との
//!    一階の照合で推論したもので、呼び出しの node ごとに `Instances` に残る。
//! 3. `infinite`：多相再帰（呼び出しのたびに型引数が大きくなる再帰）を拒否する（E-TYPE-GENERIC-INFINITE）。
//! 4. `monomorphize`：使われた型引数の組ごとに、総称の関数を具体的な型の関数に複製する（名前は `first_g1` などの、
//!    プログラム中のどの名前とも重ならないもの）。使われない総称の関数はコードにならない。複製の数と型の大きさには
//!    上限がある（E-LIMIT-STATIC-GENERIC-INSTANCES）。単相化したプログラムをもう一度型検査し、以降（`hof::lower`
//!    など）はそれを使う。
//!
//! 総称のレコード型・直和型そのものは、展開後の構造的な型に型引数を入れたもので、単相化は要らない。展開後の型
//! （型引数を含むもの）は field の参照（`ExprKind::Field` の target）と `match` の種類（`MatchKind::Sum`）に残り、
//! 型検査器が値の型と照合して型引数を決める（単相化はこれを置き換えない）。
//!
//! 書き換えは検証されていない接着部分（`trust-boundary.toml` の `glue`）。検証済み部品は単相化・書き換え後の
//! プログラムを検査・実行するので、停止性・型安全性・決定性は書き換え後のプログラムについて成り立つ。

use crate::checker::{
    check_program_second, check_program_with, collect_params, user_calls, CheckOptions,
    CheckOutcome, Instances, SecondPass,
};
use crate::diagnostics::Diagnostic;
use crate::profiles::StaticProfile;
use crate::syntax::*;
use std::collections::{HashMap, HashSet, VecDeque};

/// 単相化で作る関数の数の上限。
pub const MAX_INSTANCES: usize = 256;
/// 単相化の型引数一つの大きさ（型の node 数）の上限。
pub const MAX_INSTANCE_TYPE_NODES: usize = 256;

// ---------------------------------------------------------------- 共通

/// プログラム中の名前（関数名、引数、変数、束縛、呼び出し先、型名、構築子）。新しい名前を重ねないため。
pub fn idents(p: &Program) -> HashSet<String> {
    fn ex(e: &Expr, out: &mut HashSet<String>) {
        match &e.kind {
            ExprKind::Var(n) | ExprKind::Let { name: n, .. } | ExprKind::Call { callee: n, .. } => {
                out.insert(n.clone());
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
            _ => {}
        }
        for c in e.children() {
            ex(c, out);
        }
    }
    let mut out = HashSet::new();
    for d in &p.declarations {
        match d {
            Decl::Fn(f) => {
                out.insert(f.name.clone());
                out.extend(f.params.iter().map(|q| q.name.clone()));
                ex(&f.body, &mut out);
            }
            Decl::Entry(e) => {
                out.insert(e.name.clone());
            }
            Decl::Type(t) => {
                out.insert(t.name.clone());
            }
            Decl::Sum(s) => {
                out.insert(s.name.clone());
                out.extend(s.variants.iter().map(|v| v.name.clone()));
            }
        }
    }
    out
}

/// `base` か、`base2`、`base3`、... のうち、`taken` にない最初の名前（予約語は避ける）。`taken` に足す。
pub fn fresh(taken: &mut HashSet<String>, base: &str) -> String {
    let mut n = 1;
    loop {
        let name = if n == 1 {
            base.to_string()
        } else {
            format!("{base}{n}")
        };
        if !taken.contains(&name) && !is_keyword(&name) {
            taken.insert(name.clone());
            return name;
        }
        n += 1;
    }
}

/// v1.10：宣言されていない型の名前が型引数らしければ（`T`、`K2` など）、型引数の宣言を修復ヒントに添える。
pub fn param_note(n: &str, fix: String) -> String {
    if looks_like_param(n) {
        format!("{fix}; or, if {n} is meant as a type parameter, declare it after the function or type name: fn f<{n}>(...) / type Name<{n}> = ...")
    } else {
        fix
    }
}

/// 型の名前 `name`（型引数 `params`）に `given` 個の型引数を書いた誤り（E-TYPE-GENERIC-ARITY、phase name）。
pub fn arity_error(
    diags: &mut Vec<Diagnostic>,
    name: &str,
    params: &[String],
    given: usize,
    meta: Meta,
) {
    let fix = if params.is_empty() {
        format!("{name} without type arguments: {name} is not generic")
    } else {
        format!(
            "{name}<{}> with {} type argument(s), one per type parameter of {name}",
            params.join(", "),
            params.len()
        )
    };
    diags.push(
        Diagnostic::error("name", "E-TYPE-GENERIC-ARITY", meta.span())
            .exp(format!("{} type arguments", params.len()))
            .act(format!("{given} type arguments"))
            .at(meta.index)
            .fix("replace_type", meta.span(), fix),
    );
}

/// 式の中の型の node（`list<T>`、`none<T>`、`dict<K, V>`、`ok<T, E>`、呼び出しの型引数）を書き換える。
/// field の参照の target と `match` の種類（展開後の型）は書き換えない。
fn map_expr_types(e: &mut Expr, f: &mut dyn FnMut(&TypeNode) -> TypeNode) {
    match &mut e.kind {
        ExprKind::List {
            element_type: t, ..
        }
        | ExprKind::None(t)
        | ExprKind::DictNew(t)
        | ExprKind::Inj { ty: t, .. } => *t = f(t),
        ExprKind::Call { type_args, .. } => type_args.iter_mut().for_each(|t| *t = f(t)),
        _ => {}
    }
    for c in e.children_mut() {
        map_expr_types(c, f);
    }
}

fn walk_expr_types<'a>(e: &'a Expr, f: &mut dyn FnMut(&'a TypeNode)) {
    match &e.kind {
        ExprKind::List {
            element_type: t, ..
        }
        | ExprKind::None(t)
        | ExprKind::DictNew(t)
        | ExprKind::Inj { ty: t, .. } => f(t),
        ExprKind::Call { type_args, .. } => type_args.iter().for_each(&mut *f),
        _ => {}
    }
    for c in e.children() {
        walk_expr_types(c, f);
    }
}

/// 型引数の構文（宣言の型引数、呼び出しの型引数、型引数つきの型の名前、型引数の node）か、宣言されていない
/// 型の名前を含むか（含めば `resolve` を通す）。
pub fn has_generics(p: &Program) -> bool {
    let declared: HashSet<&str> = type_names(p);
    let mut found = false;
    let mut look = |t: &TypeNode| {
        fn go(t: &TypeNode, declared: &HashSet<&str>) -> bool {
            t.tag == TyTag::Param
                || (t.is_named()
                    && (!t.args.is_empty() || !declared.contains(t.name.as_deref().unwrap_or(""))))
                || t.args.iter().any(|a| go(a, declared))
        }
        found |= go(t, &declared);
    };
    for d in &p.declarations {
        match d {
            Decl::Fn(f) => {
                if !f.type_params.is_empty() {
                    return true;
                }
                f.params.iter().for_each(|q| look(&q.ty));
                look(&f.return_type);
                walk_expr_types(&f.body, &mut |t| look(t));
                fn calls(e: &Expr) -> bool {
                    matches!(&e.kind, ExprKind::Call { type_args, .. } if !type_args.is_empty())
                        || e.children().into_iter().any(calls)
                }
                if calls(&f.body) {
                    return true;
                }
            }
            Decl::Type(t) => {
                if !t.type_params.is_empty() {
                    return true;
                }
                t.fields.iter().for_each(|f| look(&f.ty));
            }
            Decl::Sum(s) => {
                if !s.type_params.is_empty() {
                    return true;
                }
                s.variants
                    .iter()
                    .flat_map(|v| &v.fields)
                    .for_each(&mut look);
            }
            Decl::Entry(_) => {}
        }
    }
    found
}

/// 総称の関数を含むか（展開の後。含めば単相化する）。
pub fn is_generic(p: &Program) -> bool {
    p.functions().any(|f| !f.type_params.is_empty())
}

fn type_names(p: &Program) -> HashSet<&str> {
    p.declarations
        .iter()
        .filter_map(|d| match d {
            Decl::Type(t) => Some(t.name.as_str()),
            Decl::Sum(s) => Some(s.name.as_str()),
            _ => None,
        })
        .collect()
}

// ---------------------------------------------------------------- resolve

struct Resolve<'a> {
    declared: HashSet<&'a str>,
    diags: Vec<Diagnostic>,
}

/// 型引数らしい名前（宣言されていない型の名前で、大文字一文字か、大文字一文字と数字）。
fn looks_like_param(n: &str) -> bool {
    let b = n.as_bytes();
    !b.is_empty() && b[0].is_ascii_uppercase() && b[1..].iter().all(|c| c.is_ascii_digit())
}

impl Resolve<'_> {
    /// 一つの宣言の型引数 `params` の下で型の node を解決する。`owner` は宣言の種類と名前（修復ヒント用）、
    /// `insert_at` は型引数を足す位置（宣言の名前の直後か、既にある型引数の最後の直後）。
    fn ty(
        &mut self,
        t: &TypeNode,
        params: &[TypeParam],
        owner: &str,
        insert_at: usize,
    ) -> TypeNode {
        let names: Vec<&str> = params.iter().map(|p| p.name.as_str()).collect();
        if t.tag == TyTag::Param {
            let n = t.name.as_deref().unwrap_or("");
            if !names.contains(&n) {
                self.unknown(n, t.meta, &names, owner, insert_at);
            }
            return t.clone();
        }
        if let Some(n) = t.name.as_deref() {
            if names.contains(&n) {
                if !t.args.is_empty() {
                    self.diags.push(
                        Diagnostic::error("name", "E-TYPE-GENERIC-ARITY", t.meta.span())
                            .exp("0 type arguments")
                            .act(format!("{} type arguments", t.args.len()))
                            .at(t.meta.index)
                            .fix("replace_type", t.meta.span(), format!("{n} without type arguments: {n} is a type parameter, which stands for a whole type")),
                    );
                }
                return TypeNode::param(n, t.meta);
            }
            // 総称でない宣言では、型引数らしい名前で、近い名前の型も宣言されていないときだけ（それ以外は
            // レコード型・直和型の名前の誤りとして records・sums が E-RECORD-UNKNOWN-TYPE を出す）
            let near_type =
                || !crate::diagnostics::closest(n, self.declared.iter().copied(), 1).is_empty();
            if !self.declared.contains(n)
                && (!names.is_empty() || (looks_like_param(n) && !near_type()))
            {
                self.unknown(n, t.meta, &names, owner, insert_at);
                return TypeNode::new(TyTag::Unit, vec![], t.meta);
            }
        }
        TypeNode {
            args: t
                .args
                .iter()
                .map(|a| self.ty(a, params, owner, insert_at))
                .collect(),
            ..t.clone()
        }
    }

    fn unknown(&mut self, n: &str, meta: Meta, names: &[&str], owner: &str, insert_at: usize) {
        let fix = if names.is_empty() {
            format!(
                "'<{n}>' after the name of {owner} to declare the type parameter {n} (fn first<{n}>(xs: List<{n}>) -> Option<{n}> = ...), or use a concrete or declared type instead of {n}"
            )
        } else {
            format!(
                "', {n}' at the end of the type parameters of {owner} (<{}, {n}>) to declare {n}, or use one of the declared type parameters ({}) or a concrete type",
                names.join(", "),
                names.join(", ")
            )
        };
        self.diags.push(
            Diagnostic::error("name", "E-TYPE-GENERIC-UNKNOWN-PARAM", meta.span())
                .exp(if names.is_empty() {
                    "declared type".to_string()
                } else {
                    format!("type parameter {}", names.join(", "))
                })
                .act(n)
                .at(meta.index)
                .fix("insert_text", (insert_at, insert_at), fix),
        );
    }

    /// 宣言の型引数の重複と、宣言された型の名前との衝突。
    fn params(&mut self, params: &[TypeParam], index: usize) {
        for (i, p) in params.iter().enumerate() {
            if params[..i].iter().any(|q| q.name == p.name) {
                self.diags.push(
                    Diagnostic::error("name", "E-TYPE-GENERIC-DUPLICATE-PARAM", p.span.t())
                        .act(&p.name)
                        .at(index)
                        .fix("replace_identifier", p.span.t(), "type parameter name not used by another type parameter of the same declaration"),
                );
            } else if self.declared.contains(p.name.as_str()) {
                self.diags.push(
                    Diagnostic::error("name", "E-TYPE-GENERIC-PARAM-CONFLICT", p.span.t())
                        .act(&p.name)
                        .at(index)
                        .fix(
                            "replace_identifier",
                            p.span.t(),
                            format!("type parameter name different from the declared type {} (for example a single letter such as T)", p.name),
                        ),
                );
            }
        }
    }
}

fn insert_point(name_span: Sp, params: &[TypeParam]) -> usize {
    params.last().map_or(name_span.1, |p| p.span.1)
}

/// 宣言の型引数を検査し、型の位置の型引数の名前を `TyTag::Param` の node にする（phase name）。
pub fn resolve(p: &Program) -> Result<Program, Vec<Diagnostic>> {
    let mut r = Resolve {
        declared: type_names(p),
        diags: vec![],
    };
    let mut out = p.clone();
    for d in &mut out.declarations {
        match d {
            Decl::Fn(f) => {
                r.params(&f.type_params, f.meta.index);
                let tp = f.type_params.clone();
                let owner = format!("fn {}", f.name);
                let at = insert_point(f.name_span, &tp);
                for q in &mut f.params {
                    q.ty = r.ty(&q.ty, &tp, &owner, at);
                }
                f.return_type = r.ty(&f.return_type, &tp, &owner, at);
                map_expr_types(&mut f.body, &mut |t| r.ty(t, &tp, &owner, at));
            }
            Decl::Type(t) => {
                r.params(&t.type_params, t.meta.index);
                let tp = t.type_params.clone();
                let owner = format!("type {}", t.name);
                let at = insert_point(t.name_span, &tp);
                for f in &mut t.fields {
                    f.ty = r.ty(&f.ty, &tp, &owner, at);
                }
                let used: Vec<&TypeNode> = t.fields.iter().map(|f| &f.ty).collect();
                unused(&mut r.diags, &tp, &used, &t.name, t.meta.index);
            }
            Decl::Sum(s) => {
                r.params(&s.type_params, s.meta.index);
                let tp = s.type_params.clone();
                let owner = format!("type {}", s.name);
                let at = insert_point(s.name_span, &tp);
                for v in &mut s.variants {
                    for f in &mut v.fields {
                        *f = r.ty(f, &tp, &owner, at);
                    }
                }
                let used: Vec<&TypeNode> = s.variants.iter().flat_map(|v| &v.fields).collect();
                unused(&mut r.diags, &tp, &used, &s.name, s.meta.index);
            }
            Decl::Entry(_) => {}
        }
    }
    if r.diags.is_empty() {
        Ok(out)
    } else {
        Err(r.diags)
    }
}

/// 型の宣言の型引数は field（variant の中身）のどこかに現れなければならない（型は宣言の印と展開後の構造で決まるので、
/// 現れない型引数は型の区別にも構造にも効かない）。
fn unused(
    diags: &mut Vec<Diagnostic>,
    params: &[TypeParam],
    used: &[&TypeNode],
    name: &str,
    index: usize,
) {
    fn mentions(t: &TypeNode, n: &str) -> bool {
        (t.tag == TyTag::Param && t.name.as_deref() == Some(n))
            || t.args.iter().any(|a| mentions(a, n))
    }
    for p in params {
        if !used.iter().any(|t| mentions(t, &p.name)) {
            diags.push(
                Diagnostic::error("name", "E-TYPE-GENERIC-UNUSED-PARAM", p.span.t())
                    .act(&p.name)
                    .at(index)
                    .fix(
                        "delete_span",
                        p.span.t(),
                        format!(
                            "delete the type parameter {} of {name} (with its comma), or use it in a field: a type parameter of a type must appear in a field or variant, since types are compared by their structure",
                            p.name
                        ),
                    ),
            );
        }
    }
}

// ---------------------------------------------------------------- 多相再帰

/// 呼び出しのたびに型引数が大きくなる再帰（`f<T>` から `f<List<T>>` を呼ぶなど）を拒否する。
/// 総称の関数 f の型引数 P から、f の本体の呼び出し `g<..., A_j, ...>` の g の j 番目の型引数へ、A_j が P を含めば
/// 辺を引く（A_j が P そのものなら重み 0、P を真に含めば重み 1）。重み 1 の辺が閉路に乗れば、単相化は止まらない。
pub fn infinite(p: &Program, inst: &Instances) -> Vec<Diagnostic> {
    let generic: HashMap<&str, &FnDecl> = p
        .functions()
        .filter(|f| !f.type_params.is_empty())
        .map(|f| (f.name.as_str(), f))
        .collect();
    // 辺：（f、P の位置）→（g、j）、重み、呼び出しの span と node、表示
    type Node<'a> = (&'a str, usize);
    let mut edges: Vec<(Node, Node, bool, (usize, usize), usize, String)> = vec![];
    for f in generic.values() {
        let names: Vec<&str> = f.type_params.iter().map(|q| q.name.as_str()).collect();
        for c in user_calls(&f.body) {
            let (Some(g), Some(tys)) = (generic.get(c.callee), inst.get(&c.index)) else {
                continue;
            };
            let shown = format!(
                "{}<{}>",
                g.ctor.as_deref().unwrap_or(&g.name),
                tys.iter()
                    .map(|t| t.to_string())
                    .collect::<Vec<_>>()
                    .join(", ")
            );
            for (j, t) in tys.iter().enumerate() {
                for q in collect_params(t) {
                    let Some(i) = names.iter().position(|n| *n == q) else {
                        continue;
                    };
                    let grows = t.param_name() != Some(q.as_str());
                    edges.push((
                        (f.name.as_str(), i),
                        (g.name.as_str(), j),
                        grows,
                        c.span,
                        c.index,
                        shown.clone(),
                    ));
                }
            }
        }
    }
    let reaches = |from: Node, to: Node| {
        let mut seen: HashSet<Node> = HashSet::from([from]);
        let mut todo = vec![from];
        while let Some(x) = todo.pop() {
            if x == to {
                return true;
            }
            for (a, b, ..) in &edges {
                if *a == x && seen.insert(*b) {
                    todo.push(*b);
                }
            }
        }
        false
    };
    let mut diags: Vec<Diagnostic> = vec![];
    let mut reported = HashSet::new();
    for (a, b, grows, span, index, shown) in &edges {
        if !*grows || !reaches(*b, *a) || !reported.insert(*index) {
            continue;
        }
        let f = generic[a.0];
        let params: Vec<&str> = f.type_params.iter().map(|q| q.name.as_str()).collect();
        diags.push(
            Diagnostic::error("typecheck", "E-TYPE-GENERIC-INFINITE", *span).exp(format!("type arguments that do not grow around the recursion through {}", f.name)).act(shown.clone()).at(*index).fix(
                "replace_expression",
                *span,
                format!(
                    "a recursive call whose type arguments do not grow: calling {shown} from {}<{}> builds a larger type from {} on every round of the recursion, which would need infinitely many instances; pass the type parameters unchanged, or keep the growing data in a value (for example a List) instead of in the type",
                    f.name,
                    params.join(", "),
                    params[a.1]
                ),
            ),
        );
    }
    diags
}

// ---------------------------------------------------------------- 単相化

/// 意味論上の型を構文上の型にする（名前は保つ）。
fn node_of(t: &Ty, meta: Meta) -> TypeNode {
    let mut n = TypeNode::new(
        t.tag(),
        t.args().iter().map(|a| node_of(a, meta)).collect(),
        meta,
    );
    if let Some(p) = t.param_name() {
        n.name = Some(p.to_string());
    }
    n.label = t.label();
    n
}

/// 型の木としての node 数（`cap` で打ち切る）。
fn size(t: &Ty, cap: usize) -> usize {
    let mut n = 1;
    for a in t.args() {
        if n > cap {
            break;
        }
        n += size(a, cap - n.min(cap));
    }
    n
}

/// 構造の鍵（名前は含めない。型の等価性と同じ）。
fn key(t: &Ty, out: &mut String) {
    out.push_str(t.tag().name());
    if let Some(p) = t.param_name() {
        out.push(':');
        out.push_str(p);
    }
    if !t.args().is_empty() {
        out.push('<');
        for (i, a) in t.args().iter().enumerate() {
            if i > 0 {
                out.push(',');
            }
            key(a, out);
        }
        out.push('>');
    }
}

struct Mono<'a> {
    generic: HashMap<&'a str, &'a FnDecl>,
    inst: &'a Instances,
    taken: HashSet<String>,
    /// （関数名、型引数）→ 複製の名前
    names: HashMap<String, String>,
    queue: VecDeque<(String, Vec<Ty>, String)>,
    count: usize,
    next_index: usize,
    diags: Vec<Diagnostic>,
}

impl Mono<'_> {
    /// 総称の関数 `f` の型引数 `tys`（具体的な型）の複製の名前（なければ作って待ち行列に入れる）。
    fn instance(&mut self, f: &str, tys: Vec<Ty>, call: &Expr) -> Option<String> {
        for t in &tys {
            if size(t, MAX_INSTANCE_TYPE_NODES + 1) > MAX_INSTANCE_TYPE_NODES {
                self.limit(
                    call,
                    format!("a type argument with more than {MAX_INSTANCE_TYPE_NODES} type nodes"),
                );
                return None;
            }
        }
        let mut k = format!("{f}<");
        for t in &tys {
            key(t, &mut k);
            k.push(';');
        }
        if let Some(n) = self.names.get(&k) {
            return Some(n.clone());
        }
        self.count += 1;
        if self.count > MAX_INSTANCES {
            self.limit(call, format!("more than {MAX_INSTANCES} instances"));
            return None;
        }
        let name = fresh(&mut self.taken, &format!("{f}_g{}", self.count));
        self.names.insert(k, name.clone());
        self.queue.push_back((f.to_string(), tys, name.clone()));
        Some(name)
    }

    fn limit(&mut self, call: &Expr, act: String) {
        if !self.diags.is_empty() {
            return;
        }
        self.diags.push(
            Diagnostic::error("semantic-limits", "E-LIMIT-STATIC-GENERIC-INSTANCES", call.meta.span())
                .exp(format!("at most {MAX_INSTANCES} instances of generic functions, each type argument at most {MAX_INSTANCE_TYPE_NODES} type nodes"))
                .act(act)
                .at(call.meta.index),
        );
    }

    /// 本体を複製する：型引数を `cur` で置き換え、総称の関数の呼び出しを複製の呼び出しにする。
    fn body(&mut self, e: &Expr, cur: &[(String, Ty)]) -> Expr {
        let sub = |t: &TypeNode| -> TypeNode {
            if cur.is_empty() {
                return t.clone();
            }
            t.subst(&|n| {
                cur.iter()
                    .find(|(m, _)| m == n)
                    .map(|(_, ty)| node_of(ty, t.meta))
            })
        };
        let mut out = e.clone();
        match &mut out.kind {
            ExprKind::List {
                element_type: t, ..
            }
            | ExprKind::None(t)
            | ExprKind::DictNew(t)
            | ExprKind::Inj { ty: t, .. } => *t = sub(t),
            ExprKind::Call {
                callee,
                builtin: false,
                type_args,
                ..
            } => {
                type_args.clear();
                if self.generic.contains_key(callee.as_str()) {
                    let tys: Vec<Ty> = self.inst.get(&e.meta.index).cloned().unwrap_or_default();
                    let tys: Vec<Ty> = tys
                        .iter()
                        .map(|t| {
                            t.subst(&|n| cur.iter().find(|(m, _)| m == n).map(|(_, ty)| ty.clone()))
                        })
                        .collect();
                    if let Some(n) = self.instance(callee, tys, e) {
                        *callee = n;
                    }
                }
            }
            _ => {}
        }
        for c in out.children_mut() {
            *c = self.body(c, cur);
        }
        out
    }

    fn renumber(&mut self, e: &mut Expr) {
        e.meta.index = self.next_index;
        self.next_index += 1;
        for c in e.children_mut() {
            self.renumber(c);
        }
    }
}

fn max_index(p: &Program) -> usize {
    fn ex(e: &Expr) -> usize {
        e.children()
            .into_iter()
            .map(ex)
            .max()
            .unwrap_or(0)
            .max(e.meta.index)
    }
    p.declarations
        .iter()
        .map(|d| match d {
            Decl::Fn(f) => ex(&f.body).max(f.meta.index),
            Decl::Entry(e) => e.meta.index,
            Decl::Type(t) => t.meta.index,
            Decl::Sum(s) => s.meta.index,
        })
        .max()
        .unwrap_or(0)
        .max(p.meta.index)
}

/// 総称の関数を、使われた型引数の組ごとの具体的な関数に複製する。総称でない関数はそのまま（総称の関数の呼び出しは
/// 複製の名前にする）、総称の関数の宣言は除き、複製を宣言の末尾に足す。`inst` は総称のプログラムの型検査の結果。
pub fn monomorphize(p: &Program, inst: &Instances) -> Result<Program, Vec<Diagnostic>> {
    let generic: HashMap<&str, &FnDecl> = p
        .functions()
        .filter(|f| !f.type_params.is_empty())
        .map(|f| (f.name.as_str(), f))
        .collect();
    let mut m = Mono {
        generic,
        inst,
        taken: idents(p),
        names: HashMap::new(),
        queue: VecDeque::new(),
        count: 0,
        next_index: max_index(p) + 1,
        diags: vec![],
    };
    let mut decls = vec![];
    for d in &p.declarations {
        match d {
            Decl::Fn(f) if !f.type_params.is_empty() => {}
            Decl::Fn(f) => {
                let body = m.body(&f.body, &[]);
                decls.push(Decl::Fn(FnDecl { body, ..f.clone() }));
            }
            d => decls.push(d.clone()),
        }
    }
    while let Some((name, tys, mangled)) = m.queue.pop_front() {
        if !m.diags.is_empty() {
            break;
        }
        let f = m.generic[name.as_str()];
        let cur: Vec<(String, Ty)> = f
            .type_params
            .iter()
            .map(|q| q.name.clone())
            .zip(tys)
            .collect();
        let sub = |t: &TypeNode| {
            t.subst(&|n| {
                cur.iter()
                    .find(|(q, _)| q == n)
                    .map(|(_, ty)| node_of(ty, t.meta))
            })
        };
        let params = f
            .params
            .iter()
            .map(|q| Param {
                ty: sub(&q.ty),
                ..q.clone()
            })
            .collect();
        let return_type = sub(&f.return_type);
        let mut body = m.body(&f.body, &cur);
        m.renumber(&mut body);
        decls.push(Decl::Fn(FnDecl {
            name: mangled,
            params,
            return_type,
            body,
            type_params: vec![],
            ctor: None,
            ..f.clone()
        }));
    }
    if m.diags.is_empty() {
        Ok(Program {
            declarations: decls,
            meta: p.meta,
            imports: p.imports.clone(),
        })
    } else {
        Err(m.diags)
    }
}

/// 展開後のプログラムを型検査し、総称の関数があれば多相再帰を検査して単相化し、単相化したものをもう一度
/// 型検査する。返すのは（検査の結果、以降の書き換えに使うプログラム）。診断は総称のプログラムの検査のもの
/// （警告を含む）に、単相化の拒否と単相化後の検査の error を足したもの。受理したプログラムは単相化後のもの。
pub fn check(px: &Program, eof: usize, profile: &StaticProfile) -> (CheckOutcome, Program) {
    check_with(px, eof, profile, &CheckOptions::default())
}

/// `check` と同じ検査を、比較 cache の切替と論理 trace の有無を選んで行う（試験用）。仕事量は二つのパスの和で、
/// 論理 trace は第一パスに第二パス（複製の本体だけ）を続けたもの（規則 G、§18.1c）。
pub fn check_with(
    px: &Program,
    eof: usize,
    profile: &StaticProfile,
    opts: &CheckOptions,
) -> (CheckOutcome, Program) {
    // 二つのパスで同じ正準化の表を使う（Interned のとき。表は外側のこの範囲で開き、内側の検査は開いたまま使う）
    let _interning =
        crate::intern::Scope::enter(opts.sharing == crate::checker::TypeSharing::Interned);
    let mut o = check_program_with(px, eof, profile, opts);
    if !is_generic(px) || o.typed.is_none() {
        return (o, px.clone());
    }
    let inf = infinite(px, &o.inst);
    if !inf.is_empty() {
        o.diagnostics.extend(inf);
        o.typed = None;
        return (o, px.clone());
    }
    match monomorphize(px, &o.inst) {
        Err(d) => {
            o.diagnostics.extend(d);
            o.typed = None;
            (o, px.clone())
        }
        Ok(pm) => {
            // 規則 G：第二パスは単相化で作った複製だけを数え、第一パスの総計から続けて数える
            let orig: HashSet<&str> = px.functions().map(|f| f.name.as_str()).collect();
            let counted: HashSet<String> = pm
                .functions()
                .filter(|f| !orig.contains(f.name.as_str()))
                .map(|f| f.name.clone())
                .collect();
            let pass = SecondPass {
                counted,
                start: o.work.unwrap_or_default(),
            };
            let o2 = check_program_second(&pm, eof, profile, opts, &pass);
            let mut diagnostics = o.diagnostics;
            diagnostics.extend(o2.diagnostics.into_iter().filter(|d| d.severity == "error"));
            let typed = if diagnostics.iter().any(|d| d.severity == "error") {
                None
            } else {
                o2.typed
            };
            let trace = match (o.trace, o2.trace) {
                (Some(mut a), Some(b)) => {
                    a.extend(b);
                    Some(a)
                }
                (a, b) => a.or(b),
            };
            let sharing_hits = o.sharing_hits + o2.sharing_hits;
            let out = CheckOutcome {
                diagnostics,
                typed,
                work: o2.work,
                hof: o2.hof,
                inst: o2.inst,
                trace,
                sharing_hits,
            };
            (out, pm)
        }
    }
}
