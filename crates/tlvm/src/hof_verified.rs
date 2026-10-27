//! v1.5 の hof（map・filter・any・all・find・sort_by）の書換えの、検証済みの経路（DECISION-43）。
//!
//! `hof::lower` と同じ書換えを、検証済みの `tlvm_verified::hofex::rw_ex` で行う。Rust の AST を検証済みの源の式
//! `EX` に写す（束縛ごとに別の番号をつけ、hof の束縛には要素の型と本体の型の組を表に入れる。文字列は引数のない
//! 呼出しで写し、戻すとき元の文字列にする）。`rw_ex` の結果の核の式 `EExpr` を Rust の AST に戻すとき、すべての
//! 束縛を新しい名前（`hof` の番号。どの元の名前とも重ならない）で付け直し、参照は有効範囲に従って対応させる。
//! こうすると、束縛の名前の重なりは、番号の対応に影響しない。
//!
//! 写せないもの（ループ、辞書の操作、空の辞書、表の無い hof）を含むプログラムは `None` を返し、`lower_hof` は
//! 従来の `hof::lower` を使う。
//!
//! 信頼の境界：この接着（写し、番号の付け方、表の作り方、戻し）は検証していない（trust-boundary.toml の
//! `rewrite-shape` の (1)・(2)）。検証しているのは `rw_ex` の事後条件（hofex.rs の `rewrite-exec-hof`）だけ。
//!
//! 検証済みの経路（`route_table`、`verified_hofs`）は、束縛の番号と形の並びを、検証済みの解決（hofprog.rs）の並びと
//! 実行時に比べる。一致しなければ経路は拒否する（api.rs の `verified_from_source_hof`）。この比べが、表の番号の
//! 信頼を実行時の検査に替える。

use crate::checker::HofTypes;
use crate::hof::{collect, has_hof};
use crate::syntax::*;
use crate::values::verified_ty;
use std::collections::{HashMap, HashSet};
use tlvm_verified::bigint::Int;
use tlvm_verified::hofex::{rw_ex, EX};
use tlvm_verified::hofprog::EXFunc;
use tlvm_verified::ir::EExpr;
use tlvm_verified::spec::{Builtin, Ty as VTy};

/// hof を含むプログラムは検証済みの書換えを試し、写せないものは従来の書換えを使う。hof を含まないプログラムは
/// 従来の書換えに任せる（ループや辞書の書換えは従来の経路のまま）。
pub fn lower_hof(p: &Program, types: &HofTypes) -> Program {
    if has_hof(p) {
        if let Some(q) = lower(p, types) {
            return q;
        }
    }
    crate::hof::lower(p, types)
}

/// 検証済みの経路で書き換える。写せない式、または `rw_ex` が None（名前の桁あふれ）を返すとき None。
pub fn lower(p: &Program, types: &HofTypes) -> Option<Program> {
    // 名前の衝突を避ける集合は hof::lower と同じ（関数の名、引数の名、本体の名前）
    let mut taken: HashSet<String> = HashSet::new();
    for f in p.functions() {
        taken.insert(f.name.clone());
        taken.extend(f.params.iter().map(|q| q.name.clone()));
        collect(&f.body, &mut taken);
    }
    let names: Vec<String> = p.functions().map(|f| f.name.clone()).collect();
    let funcs: HashMap<String, usize> = names
        .iter()
        .cloned()
        .enumerate()
        .map(|(i, n)| (n, i))
        .collect();

    // 写す：関数ごとに引数と本体を EX にする。表は全体で一つ（束縛ごとに番号が違う）
    let mut conv = Conv {
        types,
        funcs: &funcs,
        fns: names.len(),
        scope: Vec::new(),
        next: 0,
        table: Vec::new(),
        hofs: Vec::new(),
        strs: Vec::new(),
    };
    let mut bodies: Vec<(Vec<usize>, EX)> = Vec::new();
    for f in p.functions() {
        conv.scope.clear();
        let params: Vec<usize> = f.params.iter().map(|q| conv.bind(&q.name)).collect();
        let body = conv.ex(&f.body)?;
        bodies.push((params, body));
    }

    // 書換え：表は全体の表を使う（束縛ごとに番号が違うので、どの関数の本体にも同じ表でよい）
    let mut rewritten: Vec<(Vec<usize>, EExpr)> = Vec::new();
    for (params, body) in &bodies {
        rewritten.push((params.clone(), rw_ex(&conv.table, body)?));
    }

    // 戻す：束縛をすべて新しい名前で付け直す
    let mut back = Back {
        names: &names,
        strs: conv.strs,
        taken,
        fresh: 0,
        scope: Vec::new(),
        meta: p.meta,
    };
    let mut rest = rewritten.into_iter();
    let mut declarations = Vec::new();
    for d in &p.declarations {
        match d {
            Decl::Fn(f) => {
                let (params, body) = rest.next()?;
                back.scope.clear();
                back.meta = f.meta;
                let new_params: Vec<Param> = f
                    .params
                    .iter()
                    .zip(params)
                    .map(|(q, n)| Param {
                        name: back.bind(n),
                        ..q.clone()
                    })
                    .collect();
                let new_body = back.ex(&body)?;
                declarations.push(Decl::Fn(FnDecl {
                    params: new_params,
                    body: new_body,
                    ..f.clone()
                }));
            }
            d => declarations.push(d.clone()),
        }
    }
    Some(Program {
        declarations,
        meta: p.meta,
        imports: p.imports.clone(),
    })
}

/// 源の式への写し。束縛ごとに番号をつけ、hof の束縛には（要素の型、本体の型）を表に入れる。
struct Conv<'a> {
    types: &'a HofTypes,
    funcs: &'a HashMap<String, usize>,
    /// 関数の数。文字列の値を呼ぶ番号は、これより後ろから始まる
    fns: usize,
    /// 有効な束縛（内側が後ろ）：名前と番号
    scope: Vec<(String, usize)>,
    next: usize,
    table: Vec<(usize, VTy, VTy)>,
    /// hof の束縛の並び（束縛の番号と形、allocation の順）。検証済みの解決の並びと比べる（`route_table`）
    hofs: Vec<(usize, u8)>,
    /// 文字列の値。引数のない呼出し（番号は `fns` の後ろ）で写し、戻すとき元の文字列にする。文字のリストに写すと
    /// 文面が変わり、変数や束縛の番号で写すと、書換えが作る束縛の番号と衝突しうる（呼出しは束縛しない）。
    strs: Vec<String>,
}

impl Conv<'_> {
    fn number(&mut self) -> usize {
        let n = self.next;
        self.next += 1;
        n
    }

    fn bind(&mut self, name: &str) -> usize {
        let n = self.number();
        self.scope.push((name.to_string(), n));
        n
    }

    fn lookup(&self, name: &str) -> Option<usize> {
        self.scope
            .iter()
            .rev()
            .find(|(s, _)| s == name)
            .map(|(_, n)| *n)
    }

    fn exs(&mut self, es: &[Expr]) -> Option<Vec<EX>> {
        es.iter().map(|e| self.ex(e)).collect()
    }

    fn ex(&mut self, e: &Expr) -> Option<EX> {
        Some(match &e.kind {
            ExprKind::Int(n) => EX::Int(Int { n: n.clone() }),
            ExprKind::Char(c) => EX::Char(*c as u32),
            // 文字列は引数のない呼出し（`strs` の番号）で写す。戻すとき、元の文字列にする（型は List<Char>）
            ExprKind::Str(s) => {
                self.strs.push(s.clone());
                EX::Call(self.fns + self.strs.len() - 1, vec![])
            }
            ExprKind::Bool(b) => EX::Bool(*b),
            ExprKind::Unit => EX::Unit,
            ExprKind::Var(x) => EX::Var(self.lookup(x)?),
            ExprKind::List {
                element_type,
                items,
            } => EX::List(vty_node(element_type)?, self.exs(items)?),
            ExprKind::Some(a) => EX::Some(Box::new(self.ex(a)?)),
            ExprKind::None(t) => EX::None(vty_node(t)?),
            ExprKind::Pair(a, b) => EX::Pair(Box::new(self.ex(a)?), Box::new(self.ex(b)?)),
            ExprKind::Call {
                callee,
                args,
                builtin,
                ..
            } => {
                let args = self.exs(args)?;
                if *builtin {
                    EX::Builtin(builtin_of(callee)?, args)
                } else {
                    EX::Call(*self.funcs.get(callee)?, args)
                }
            }
            ExprKind::Let {
                name, value, body, ..
            } => {
                let v = self.ex(value)?;
                let mark = self.scope.len();
                let n = self.bind(name);
                let b = self.ex(body)?;
                self.scope.truncate(mark);
                EX::Let(n, Box::new(v), Box::new(b))
            }
            ExprKind::If(c, a, b) => EX::If(
                Box::new(self.ex(c)?),
                Box::new(self.ex(a)?),
                Box::new(self.ex(b)?),
            ),
            ExprKind::Fold {
                list,
                init,
                acc,
                item,
                body,
                ..
            } => {
                let xs = self.ex(list)?;
                let i0 = self.ex(init)?;
                let mark = self.scope.len();
                let a = self.bind(acc);
                let it = self.bind(item);
                let b = self.ex(body)?;
                self.scope.truncate(mark);
                EX::Fold(Box::new(xs), Box::new(i0), a, it, Box::new(b))
            }
            ExprKind::Match {
                scrutinee,
                on_none,
                binder,
                on_some,
                ..
            } => {
                let s = self.ex(scrutinee)?;
                let nb = self.ex(on_none)?;
                let mark = self.scope.len();
                let n = self.bind(binder);
                let sm = self.ex(on_some)?;
                self.scope.truncate(mark);
                EX::Match(Box::new(s), Box::new(nb), n, Box::new(sm))
            }
            ExprKind::Inj { ok, ty, value } => EX::Inj(
                *ok,
                vty_node(ty.args.first()?)?,
                vty_node(ty.args.get(1)?)?,
                Box::new(self.ex(value)?),
            ),
            ExprKind::MatchResult {
                scrutinee,
                ok_binder,
                on_ok,
                err_binder,
                on_err,
                ..
            } => {
                let s = self.ex(scrutinee)?;
                let mark = self.scope.len();
                let x = self.bind(ok_binder);
                let a = self.ex(on_ok)?;
                self.scope.truncate(mark);
                let mark = self.scope.len();
                let y = self.bind(err_binder);
                let b = self.ex(on_err)?;
                self.scope.truncate(mark);
                EX::MatchR(Box::new(s), x, Box::new(a), y, Box::new(b))
            }
            ExprKind::Hof {
                op,
                list,
                binder,
                body,
                ..
            } => {
                let (a, b) = self.types.get(&e.meta.index)?;
                let (ta, tb) = (verified_ty(a)?, verified_ty(b)?);
                let xs = self.ex(list)?;
                let mark = self.scope.len();
                let x = self.bind(binder);
                self.hofs.push((x, op_tag(op)));
                let c = self.ex(body)?;
                self.scope.truncate(mark);
                self.table.push((x, ta, tb));
                let (xs, c) = (Box::new(xs), Box::new(c));
                match op {
                    HofOp::Map => EX::Map(xs, x, c),
                    HofOp::Filter => EX::Filter(xs, x, c),
                    HofOp::Any => EX::Any(xs, x, c),
                    HofOp::All => EX::All(xs, x, c),
                    HofOp::Find => EX::Find(xs, x, c),
                    HofOp::SortBy => EX::SortBy(xs, x, c),
                }
            }
            // ループ、辞書の操作と空の辞書は、この経路の外（従来の書換え）
            _ => return None,
        })
    }
}

/// 戻す：核の式を Rust の AST にする。束縛は、すべて新しい名前（hof の番号。元の名前と重ならない）で付ける。
struct Back<'a> {
    /// 関数の名（EExpr::Call の添字の順）
    names: &'a [String],
    /// 文字列の値（`Conv::strs`。呼出しの番号は関数の数の後ろ）
    strs: Vec<String>,
    taken: HashSet<String>,
    fresh: usize,
    /// 有効な束縛（内側が後ろ）：番号と新しい名前
    scope: Vec<(usize, String)>,
    /// 生成する節点の位置（関数の位置）
    meta: Meta,
}

impl Back<'_> {
    /// hof::lower の `fresh` と同じ名前の作り方（hof1、hof2、…。どの元の名前とも重ならない）。
    fn new_name(&mut self) -> String {
        loop {
            self.fresh += 1;
            let n = format!("hof{}", self.fresh);
            if !self.taken.contains(&n) {
                self.taken.insert(n.clone());
                return n;
            }
        }
    }

    fn bind(&mut self, n: usize) -> String {
        let name = self.new_name();
        self.scope.push((n, name.clone()));
        name
    }

    fn name_of(&self, n: usize) -> Option<String> {
        self.scope
            .iter()
            .rev()
            .find(|(m, _)| *m == n)
            .map(|(_, s)| s.clone())
    }

    fn exs(&mut self, es: &[EExpr]) -> Option<Vec<Expr>> {
        es.iter().map(|e| self.ex(e)).collect()
    }

    fn ex(&mut self, e: &EExpr) -> Option<Expr> {
        let m = self.meta;
        let kind = match e {
            EExpr::Int(n) => ExprKind::Int(n.n.clone()),
            EExpr::Bool(b) => ExprKind::Bool(*b),
            EExpr::Unit => ExprKind::Unit,
            EExpr::Char(c) => ExprKind::Char(char::from_u32(*c)?),
            EExpr::Var(x) => ExprKind::Var(self.name_of(*x)?),
            EExpr::List(t, es) => ExprKind::List {
                element_type: node_of(t, m)?,
                items: self.exs(es)?,
            },
            EExpr::Some(a) => ExprKind::Some(Box::new(self.ex(a)?)),
            EExpr::None(t) => ExprKind::None(node_of(t, m)?),
            EExpr::Pair(a, b) => ExprKind::Pair(Box::new(self.ex(a)?), Box::new(self.ex(b)?)),
            EExpr::Builtin(b, es) => ExprKind::Call {
                callee: builtin_name(b).to_string(),
                args: self.exs(es)?,
                builtin: true,
                callee_span: m.span,
                type_args: vec![],
            },
            // 文字列の値（`Conv::ex`）。引数はない
            EExpr::Call(g, es) if *g >= self.names.len() => {
                if !es.is_empty() {
                    return None;
                }
                ExprKind::Str(self.strs.get(*g - self.names.len())?.clone())
            }
            EExpr::Call(g, es) => ExprKind::Call {
                callee: self.names.get(*g)?.clone(),
                args: self.exs(es)?,
                builtin: false,
                callee_span: m.span,
                type_args: vec![],
            },
            EExpr::Let(x, a, b) => {
                let value = self.ex(a)?;
                let mark = self.scope.len();
                let name = self.bind(*x);
                let body = self.ex(b)?;
                self.scope.truncate(mark);
                ExprKind::Let {
                    name,
                    name_span: m.span,
                    value: Box::new(value),
                    body: Box::new(body),
                }
            }
            EExpr::If(c, a, b) => ExprKind::If(
                Box::new(self.ex(c)?),
                Box::new(self.ex(a)?),
                Box::new(self.ex(b)?),
            ),
            EExpr::Fold(xs, init, acc, item, body) => {
                let list = self.ex(xs)?;
                let init = self.ex(init)?;
                let mark = self.scope.len();
                let acc_name = self.bind(*acc);
                let item_name = self.bind(*item);
                let body = self.ex(body)?;
                self.scope.truncate(mark);
                ExprKind::Fold {
                    list: Box::new(list),
                    init: Box::new(init),
                    acc: acc_name,
                    acc_span: m.span,
                    item: item_name,
                    item_span: m.span,
                    body: Box::new(body),
                }
            }
            EExpr::Match(s, nb, y, sm) => {
                let scrutinee = self.ex(s)?;
                let on_none = self.ex(nb)?;
                let mark = self.scope.len();
                let binder = self.bind(*y);
                let on_some = self.ex(sm)?;
                self.scope.truncate(mark);
                ExprKind::Match {
                    scrutinee: Box::new(scrutinee),
                    on_none: Box::new(on_none),
                    binder,
                    binder_span: m.span,
                    on_some: Box::new(on_some),
                }
            }
            EExpr::Inj(ok, t, u, a) => ExprKind::Inj {
                ok: *ok,
                ty: TypeNode::new(TyTag::Result, vec![node_of(t, m)?, node_of(u, m)?], m),
                value: Box::new(self.ex(a)?),
            },
            EExpr::MatchR(s, x, a, y, b) => {
                let scrutinee = self.ex(s)?;
                let mark = self.scope.len();
                let ok_binder = self.bind(*x);
                let on_ok = self.ex(a)?;
                self.scope.truncate(mark);
                let mark = self.scope.len();
                let err_binder = self.bind(*y);
                let on_err = self.ex(b)?;
                self.scope.truncate(mark);
                ExprKind::MatchResult {
                    scrutinee: Box::new(scrutinee),
                    ok_binder,
                    ok_span: m.span,
                    on_ok: Box::new(on_ok),
                    err_binder,
                    err_span: m.span,
                    on_err: Box::new(on_err),
                }
            }
        };
        Some(Expr { kind, meta: m })
    }
}

/// 検証済みの経路の表（Rust の接着）。`table` は束縛ごとの（要素の型、本体の型）、`hofs` は hof の束縛の（番号、形）を
/// 番号の順（allocation の順）に並べたもの。`hofs` は検証済みの解決の並び（`verified_hofs`）と一致するかを呼出し側が
/// 検査する。一致すれば、表の番号は検証済みの解決の番号と同じで、表の型は源の hof の型である（DECISION-38 の信頼）。
pub struct RouteTable {
    pub table: Vec<(usize, VTy, VTy)>,
    pub hofs: Vec<(usize, u8)>,
}

/// 検証済みの経路の表を作る。束縛の番号は `conv` と同じ（引数が先、本体が続く。関数の順に計数器を受け継ぐ）。
/// 写せない式（ループ、辞書など）や、表に無い hof があれば None。
pub fn route_table(p: &Program, types: &HofTypes) -> Option<RouteTable> {
    let names: Vec<String> = p.functions().map(|f| f.name.clone()).collect();
    let funcs: HashMap<String, usize> = names
        .iter()
        .cloned()
        .enumerate()
        .map(|(i, n)| (n, i))
        .collect();
    let mut conv = Conv {
        types,
        funcs: &funcs,
        fns: names.len(),
        scope: Vec::new(),
        next: 0,
        table: Vec::new(),
        hofs: Vec::new(),
        strs: Vec::new(),
    };
    for f in p.functions() {
        conv.scope.clear();
        for q in &f.params {
            conv.bind(&q.name);
        }
        conv.ex(&f.body)?;
    }
    Some(RouteTable {
        table: conv.table,
        hofs: conv.hofs,
    })
}

/// 検証済みの解決の hof の並び（束縛の番号と形、allocation の順）。関数の順に、引数の番号の後の本体から。
pub fn verified_hofs(fs: &[EXFunc]) -> Vec<(usize, u8)> {
    let mut out = Vec::new();
    for f in fs {
        hof_seq(&f.body, &mut out);
    }
    out
}

/// hof の形の番号（`verified_hofs` と `Conv` の並びで同じ番号を使う）。
fn op_tag(op: &HofOp) -> u8 {
    match op {
        HofOp::Map => 0,
        HofOp::Filter => 1,
        HofOp::Any => 2,
        HofOp::All => 3,
        HofOp::Find => 4,
        HofOp::SortBy => 5,
    }
}

/// 検証済みの式の hof の並び。`Conv::ex` と同じ順（hof は、リストを先に、束縛を次に、本体を最後に訪ねる）。
fn hof_seq(e: &EX, out: &mut Vec<(usize, u8)>) {
    match e {
        EX::Int(_) | EX::Bool(_) | EX::Unit | EX::Char(_) | EX::Var(_) | EX::None(_) => {}
        EX::List(_, es) | EX::Builtin(_, es) | EX::Call(_, es) => {
            for a in es {
                hof_seq(a, out);
            }
        }
        EX::Some(a) | EX::Inj(_, _, _, a) => hof_seq(a, out),
        EX::Pair(a, b) | EX::Let(_, a, b) => {
            hof_seq(a, out);
            hof_seq(b, out);
        }
        EX::If(c, a, b) => {
            hof_seq(c, out);
            hof_seq(a, out);
            hof_seq(b, out);
        }
        EX::Fold(xs, init, _, _, body) => {
            hof_seq(xs, out);
            hof_seq(init, out);
            hof_seq(body, out);
        }
        EX::Match(s, nb, _, sm) => {
            hof_seq(s, out);
            hof_seq(nb, out);
            hof_seq(sm, out);
        }
        EX::MatchR(s, _, a, _, b) => {
            hof_seq(s, out);
            hof_seq(a, out);
            hof_seq(b, out);
        }
        EX::Map(xs, x, c)
        | EX::Filter(xs, x, c)
        | EX::Any(xs, x, c)
        | EX::All(xs, x, c)
        | EX::Find(xs, x, c)
        | EX::SortBy(xs, x, c) => {
            hof_seq(xs, out);
            out.push((*x, hof_tag_ex(e)));
            hof_seq(c, out);
        }
    }
}

/// 検証済みの hof の形の番号（`op_tag` と同じ）。
fn hof_tag_ex(e: &EX) -> u8 {
    match e {
        EX::Map(..) => 0,
        EX::Filter(..) => 1,
        EX::Any(..) => 2,
        EX::All(..) => 3,
        EX::Find(..) => 4,
        _ => 5,
    }
}

/// 型の節点から検証済みの型へ（値の型の写しと同じ対応。Dict は核の型の Dict に写す）。
fn vty_node(t: &TypeNode) -> Option<VTy> {
    let arg = |i: usize| t.args.get(i).and_then(vty_node);
    Some(match t.tag {
        TyTag::Int => VTy::Int,
        TyTag::Bool => VTy::Bool,
        TyTag::Unit => VTy::Unit,
        TyTag::Char => VTy::Char,
        TyTag::List => VTy::List(Box::new(arg(0)?)),
        TyTag::Option => VTy::Option(Box::new(arg(0)?)),
        TyTag::Pair => VTy::Pair(Box::new(arg(0)?), Box::new(arg(1)?)),
        TyTag::Result => VTy::Result(Box::new(arg(0)?), Box::new(arg(1)?)),
        TyTag::Dict => VTy::Dict(Box::new(arg(0)?), Box::new(arg(1)?)),
        _ => return None,
    })
}

/// 検証済みの型から型の節点へ（書換えの後の注釈。消去した型だけが来る）。
fn node_of(t: &VTy, m: Meta) -> Option<TypeNode> {
    let (tag, args) = match t {
        VTy::Int => (TyTag::Int, vec![]),
        VTy::Bool => (TyTag::Bool, vec![]),
        VTy::Unit => (TyTag::Unit, vec![]),
        VTy::Char => (TyTag::Char, vec![]),
        VTy::List(a) => (TyTag::List, vec![node_of(a, m)?]),
        VTy::Option(a) => (TyTag::Option, vec![node_of(a, m)?]),
        VTy::Pair(a, b) => (TyTag::Pair, vec![node_of(a, m)?, node_of(b, m)?]),
        VTy::Result(a, b) => (TyTag::Result, vec![node_of(a, m)?, node_of(b, m)?]),
        VTy::Dict(a, b) => (TyTag::Dict, vec![node_of(a, m)?, node_of(b, m)?]),
        _ => return None,
    };
    Some(TypeNode::new(tag, args, m))
}

/// 組込みの名前から検証済みの組込み（呼出しの名前と同じ）。hof の書換えが使うもの以外も含む。
fn builtin_of(name: &str) -> Option<Builtin> {
    Some(match name {
        "add" => Builtin::Add,
        "sub" => Builtin::Sub,
        "mul" => Builtin::Mul,
        "neg" => Builtin::Neg,
        "lt" => Builtin::Lt,
        "le" => Builtin::Le,
        "eq" => Builtin::Eq,
        "mod" => Builtin::Mod,
        "div" => Builtin::Div,
        "fst" => Builtin::Fst,
        "snd" => Builtin::Snd,
        "cons" => Builtin::Cons,
        "concat" => Builtin::Concat,
        "reverse" => Builtin::Reverse,
        "length" => Builtin::Length,
        "uncons" => Builtin::Uncons,
        "min" => Builtin::Min,
        "max" => Builtin::Max,
        "range" => Builtin::Range,
        "contains" => Builtin::Contains,
        "sort" => Builtin::Sort,
        "code" => Builtin::Code,
        "char" => Builtin::CharOf,
        "to_string" => Builtin::ToString,
        "parse_int" => Builtin::ParseInt,
        _ => return None,
    })
}

fn builtin_name(b: &Builtin) -> &'static str {
    match b {
        Builtin::Add => "add",
        Builtin::Sub => "sub",
        Builtin::Mul => "mul",
        Builtin::Neg => "neg",
        Builtin::Lt => "lt",
        Builtin::Le => "le",
        Builtin::Eq => "eq",
        Builtin::Mod => "mod",
        Builtin::Div => "div",
        Builtin::Fst => "fst",
        Builtin::Snd => "snd",
        Builtin::Cons => "cons",
        Builtin::Concat => "concat",
        Builtin::Reverse => "reverse",
        Builtin::Length => "length",
        Builtin::Uncons => "uncons",
        Builtin::Min => "min",
        Builtin::Max => "max",
        Builtin::Range => "range",
        Builtin::Contains => "contains",
        Builtin::Sort => "sort",
        Builtin::Code => "code",
        Builtin::CharOf => "char",
        Builtin::ToString => "to_string",
        Builtin::ParseInt => "parse_int",
    }
}
