//! 共通静的検査：name → call-graph → typecheck(+semantic-limits) → entry → warnings。
//!
//! Surface（compile）と AST（compile_ast）の双方がこのモジュールを通る
//! （設計書 §5、§6、§10.2、§18.1a）。

use crate::diagnostics::{closest, Diagnostic};
use crate::profiles::StaticProfile;
use crate::syntax::*;
use std::collections::{HashMap, HashSet};

// ======================================================================= name

const BUILTINS: [&str; 20] = [
    "add", "sub", "mul", "neg", "lt", "le", "eq", "mod", "fst", "snd", "cons", "concat", "reverse", "length", "uncons",
    "min", "max", "range", "contains", "sort",
];

pub fn check_names(prog: &Program) -> Vec<Diagnostic> {
    let mut diags = vec![];
    let mut known: HashSet<&str> = HashSet::new();
    for f in prog.functions() {
        if !known.insert(&f.name) {
            diags.push(Diagnostic::error("name", "E-NAME-DUPLICATE-FUNCTION", f.name_span.t()).act(&f.name).at(f.meta.index));
        }
    }

    fn walk<'a>(e: &'a Expr, env: &mut Vec<&'a str>, known: &HashSet<&str>, diags: &mut Vec<Diagnostic>) {
        let idx = e.meta.index;
        match &e.kind {
            ExprKind::Var(n) => {
                if !env.contains(&n.as_str()) {
                    let mut d = Diagnostic::error("name", "E-NAME-UNBOUND-VARIABLE", e.meta.span()).act(n).at(idx);
                    if !env.is_empty() {
                        // scope 内の変数を、近い名前を先に、最大 8 件
                        let near = closest(n, env.iter().copied(), 8);
                        let mut rest: Vec<&str> = env.iter().copied().filter(|v| !near.contains(v)).collect();
                        rest.sort();
                        rest.dedup();
                        let names: Vec<&str> = near.into_iter().chain(rest).take(8).collect();
                        d = d.fix("replace_identifier", e.meta.span(), format!("variable in scope: {}", names.join(", ")));
                    }
                    diags.push(d);
                }
            }
            ExprKind::Call { callee, args, builtin, callee_span } => {
                if !builtin && !known.contains(callee.as_str()) {
                    let near = closest(callee, known.iter().copied().chain(BUILTINS), 3);
                    let constraint = if near.is_empty() {
                        "name of a defined function or builtin".to_string()
                    } else {
                        format!("defined function or builtin, e.g. {}", near.join(", "))
                    };
                    diags.push(
                        Diagnostic::error("name", "E-NAME-UNKNOWN-FUNCTION", callee_span.t())
                            .act(callee)
                            .at(idx)
                            .fix("replace_identifier", callee_span.t(), constraint),
                    );
                }
                for a in args {
                    walk(a, env, known, diags);
                }
            }
            ExprKind::Let { name, name_span, value, body } => {
                walk(value, env, known, diags);
                if env.contains(&name.as_str()) {
                    diags.push(Diagnostic::error("name", "E-NAME-SHADOW", name_span.t()).act(name).at(idx));
                }
                env.push(name);
                walk(body, env, known, diags);
                env.pop();
            }
            ExprKind::Fold { list, init, acc, acc_span, item, item_span, body } => {
                walk(list, env, known, diags);
                walk(init, env, known, diags);
                if env.contains(&acc.as_str()) {
                    diags.push(Diagnostic::error("name", "E-NAME-SHADOW", acc_span.t()).act(acc).at(idx));
                }
                if item == acc {
                    diags.push(Diagnostic::error("name", "E-NAME-DUPLICATE-BINDER", item_span.t()).act(item).at(idx));
                } else if env.contains(&item.as_str()) {
                    diags.push(Diagnostic::error("name", "E-NAME-SHADOW", item_span.t()).act(item).at(idx));
                }
                env.push(acc);
                env.push(item);
                walk(body, env, known, diags);
                env.pop();
                env.pop();
            }
            ExprKind::Match { scrutinee, on_none, binder, binder_span, on_some } => {
                walk(scrutinee, env, known, diags);
                walk(on_none, env, known, diags);
                if env.contains(&binder.as_str()) {
                    diags.push(Diagnostic::error("name", "E-NAME-SHADOW", binder_span.t()).act(binder).at(idx));
                }
                env.push(binder);
                walk(on_some, env, known, diags);
                env.pop();
            }
            _ => {
                for c in e.children() {
                    walk(c, env, known, diags);
                }
            }
        }
    }

    for d in &prog.declarations {
        match d {
            Decl::Fn(f) => {
                let mut env: Vec<&str> = vec![];
                for p in &f.params {
                    if env.contains(&p.name.as_str()) {
                        diags.push(Diagnostic::error("name", "E-NAME-DUPLICATE-PARAM", p.name_span.t()).act(&p.name).at(p.meta.index));
                    } else {
                        env.push(&p.name);
                    }
                }
                walk(&f.body, &mut env, &known, &mut diags);
            }
            Decl::Type(_) => {}
            Decl::Entry(e) => {
                if !known.contains(e.name.as_str()) {
                    let near = closest(&e.name, known.iter().copied(), 3);
                    let constraint = if near.is_empty() {
                        "name of a defined one-parameter function".to_string()
                    } else {
                        format!("defined function, e.g. {}", near.join(", "))
                    };
                    diags.push(
                        Diagnostic::error("name", "E-ENTRY-UNKNOWN", e.name_span.t())
                            .act(&e.name)
                            .at(e.meta.index)
                            .fix("replace_identifier", e.name_span.t(), constraint),
                    );
                }
            }
        }
    }
    diags
}

// ================================================================= call graph

pub struct CallSite<'a> {
    pub callee: &'a str,
    pub span: (usize, usize),
    pub index: usize,
}

/// 本体中の全ての構文上のユーザー call（非選択枝・fold 本体を含む）を前順で返す。
pub fn user_calls(e: &Expr) -> Vec<CallSite<'_>> {
    let mut out = vec![];
    let mut stack = vec![e];
    while let Some(x) = stack.pop() {
        if let ExprKind::Call { callee, builtin: false, callee_span, .. } = &x.kind {
            out.push(CallSite { callee, span: callee_span.t(), index: x.meta.index });
        }
        let ch = x.children();
        stack.extend(ch.into_iter().rev());
    }
    out
}

pub struct CallGraph<'a> {
    pub edges: HashMap<&'a str, Vec<CallSite<'a>>>,
    pub rank: Option<HashMap<String, usize>>,
    pub diags: Vec<Diagnostic>,
}

pub fn check_call_graph<'a>(fns: &[&'a FnDecl]) -> CallGraph<'a> {
    let edges: HashMap<&str, Vec<CallSite>> = fns.iter().map(|f| (f.name.as_str(), user_calls(&f.body))).collect();
    // Tarjan の強連結成分分解（反復版）。成分は逆トポロジカル順に得られる。
    let mut index: HashMap<&str, usize> = HashMap::new();
    let mut low: HashMap<&str, usize> = HashMap::new();
    let mut on_stack: HashSet<&str> = HashSet::new();
    let mut stack: Vec<&str> = vec![];
    let mut sccs: Vec<Vec<&str>> = vec![];
    let mut counter = 0;
    for f in fns {
        let root = f.name.as_str();
        if index.contains_key(root) {
            continue;
        }
        let mut work: Vec<(&str, usize)> = vec![(root, 0)];
        while let Some((v, i)) = work.pop() {
            if i == 0 {
                index.insert(v, counter);
                low.insert(v, counter);
                counter += 1;
                stack.push(v);
                on_stack.insert(v);
            }
            let succ = &edges[v];
            if i < succ.len() {
                work.push((v, i + 1));
                let w = succ[i].callee;
                if !index.contains_key(w) {
                    work.push((w, 0));
                } else if on_stack.contains(w) {
                    let m = low[v].min(index[w]);
                    low.insert(v, m);
                }
                continue;
            }
            if low[v] == index[v] {
                let mut comp = vec![];
                loop {
                    let w = stack.pop().unwrap();
                    on_stack.remove(w);
                    comp.push(w);
                    if w == v {
                        break;
                    }
                }
                sccs.push(comp);
            }
            if let Some(&(parent, _)) = work.last() {
                let m = low[parent].min(low[v]);
                low.insert(parent, m);
            }
        }
    }
    let mut diags = vec![];
    for comp in &sccs {
        let members: HashSet<&str> = comp.iter().copied().collect();
        let inner: Vec<&CallSite> = comp.iter().flat_map(|f| edges[f].iter()).filter(|c| members.contains(c.callee)).collect();
        if let Some(primary) = inner.iter().min_by_key(|c| c.span) {
            let mut names: Vec<&str> = members.into_iter().collect();
            names.sort();
            let list = names.join(", ");
            let mut d = Diagnostic::error("call-graph", "E-CYCLE-CALL", primary.span).act(list.clone()).at(primary.index);
            d.message = format!("関数呼出しが循環しています: {list}");
            diags.push(d);
        }
    }
    let rank = if diags.is_empty() {
        let mut rank: HashMap<String, usize> = HashMap::new();
        for comp in &sccs {
            let f = comp[0];
            let r = edges[f].iter().map(|c| rank[c.callee] + 1).max().unwrap_or(0);
            rank.insert(f.to_string(), r);
        }
        Some(rank)
    } else {
        None
    };
    CallGraph { edges, rank, diags }
}

// ================================================================= typecheck

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct WorkCounter {
    pub visit: u64,
    pub build: u64,
    pub compare: u64,
}

impl WorkCounter {
    pub fn total(&self) -> u64 {
        self.visit + self.build + self.compare
    }
}

#[derive(Clone, Copy)]
enum Ev {
    Visit,
    Build,
    Compare,
}

type TcR<T> = Result<T, Diagnostic>;

pub struct TypeChecker<'a> {
    fns: &'a HashMap<&'a str, &'a FnDecl>,
    profile: &'a StaticProfile,
    pub work: WorkCounter,
    pub diags: Vec<Diagnostic>,
    env: Vec<(&'a str, Ty)>,
}

impl<'a> TypeChecker<'a> {
    pub fn new(fns: &'a HashMap<&'a str, &'a FnDecl>, profile: &'a StaticProfile) -> Self {
        TypeChecker { fns, profile, work: WorkCounter::default(), diags: vec![], env: vec![] }
    }

    fn event(&mut self, ev: Ev, node: &Meta) -> TcR<()> {
        if self.work.total() + 1 > self.profile.semantic_work {
            return Err(Diagnostic::error("semantic-limits", "E-LIMIT-STATIC-SEMANTIC-WORK", node.span())
                .exp(self.profile.semantic_work.to_string())
                .act((self.work.total() + 1).to_string())
                .at(node.index));
        }
        match ev {
            Ev::Visit => self.work.visit += 1,
            Ev::Build => self.work.build += 1,
            Ev::Compare => self.work.compare += 1,
        }
        Ok(())
    }

    fn build(&mut self, ty: Ty, node: &Meta) -> TcR<Ty> {
        if ty.depth() > self.profile.semantic_type_depth {
            return Err(Diagnostic::error("semantic-limits", "E-LIMIT-STATIC-SEMANTIC-TYPE-DEPTH", node.span())
                .exp(self.profile.semantic_type_depth.to_string())
                .act(ty.depth().to_string())
                .at(node.index));
        }
        self.event(Ev::Build, node)?;
        Ok(ty)
    }

    /// Equal(A,B)。ErrorType を含むなら 0 イベントで None。
    fn equal(&mut self, a: &Ty, b: &Ty, node: &Meta) -> TcR<Option<bool>> {
        if a.is_error() || b.is_error() {
            return Ok(None);
        }
        let mut todo = vec![(a.clone(), b.clone())];
        while let Some((x, y)) = todo.pop() {
            self.event(Ev::Compare, node)?;
            if x.tag() != y.tag() {
                return Ok(Some(false));
            }
            for (p, q) in x.args().iter().zip(y.args()).rev() {
                todo.push((p.clone(), q.clone()));
            }
        }
        Ok(Some(true))
    }

    fn head(&mut self, t: &Ty, tag: TyTag, node: &Meta) -> TcR<Option<bool>> {
        if t.is_error() {
            return Ok(None);
        }
        self.event(Ev::Compare, node)?;
        Ok(Some(t.tag() == tag))
    }

    fn report(&mut self, code: &'static str, node: &Meta, expected: impl ToString, actual: impl ToString) {
        self.diags.push(Diagnostic::error("typecheck", code, node.span()).exp(expected.to_string()).act(actual.to_string()).at(node.index));
    }

    pub fn check_function(&mut self, f: &'a FnDecl) -> TcR<()> {
        self.env = f.params.iter().map(|p| (p.name.as_str(), Ty::of(&p.ty))).collect();
        let body_t = self.expr(&f.body)?;
        let ret = Ty::of(&f.return_type);
        if self.equal(&body_t, &ret, &f.body.meta)? == Some(false) {
            self.report("E-TYPE-RETURN", &f.body.meta, &ret, &body_t);
        }
        Ok(())
    }

    fn lookup(&self, name: &str) -> Ty {
        self.env.iter().rev().find(|(n, _)| *n == name).map(|(_, t)| t.clone()).expect("name phase guarantees binding")
    }

    fn expr(&mut self, e: &'a Expr) -> TcR<Ty> {
        let m = &e.meta;
        self.event(Ev::Visit, m)?;
        match &e.kind {
            ExprKind::Int(_) => self.build(Ty::int(), m),
            ExprKind::Bool(_) => self.build(Ty::bool(), m),
            ExprKind::Unit => self.build(Ty::unit(), m),
            ExprKind::Var(n) => Ok(self.lookup(n)),
            ExprKind::List { element_type, items } => {
                let elem = Ty::of(element_type);
                let mut ts = vec![];
                for i in items {
                    ts.push(self.expr(i)?);
                }
                let mut ok = true;
                for (item, t) in items.iter().zip(&ts) {
                    let r = self.equal(t, &elem, &item.meta)?;
                    if r == Some(false) {
                        self.report("E-TYPE-LIST-ITEM", &item.meta, &elem, t);
                    }
                    ok &= r == Some(true);
                }
                if ok {
                    self.build(Ty::list(elem), m)
                } else {
                    Ok(Ty::error())
                }
            }
            ExprKind::None(t) => self.build(Ty::option(Ty::of(t)), m),
            ExprKind::Some(v) => {
                let t = self.expr(v)?;
                if t.is_error() {
                    Ok(t)
                } else {
                    self.build(Ty::option(t), m)
                }
            }
            ExprKind::Pair(a, b) => {
                let ta = self.expr(a)?;
                let tb = self.expr(b)?;
                if ta.is_error() || tb.is_error() {
                    Ok(Ty::error())
                } else {
                    self.build(Ty::pair(ta, tb), m)
                }
            }
            ExprKind::Let { name, value, body, .. } => {
                let vt = self.expr(value)?;
                self.env.push((name, vt.clone()));
                let bt = self.expr(body);
                self.env.pop();
                let bt = bt?;
                Ok(if vt.is_error() || bt.is_error() { Ty::error() } else { bt })
            }
            ExprKind::If(c, t, f) => {
                let ct = self.expr(c)?;
                let tt = self.expr(t)?;
                let ft = self.expr(f)?;
                let mut ok = !(ct.is_error() || tt.is_error() || ft.is_error());
                if self.equal(&ct, &Ty::bool(), &c.meta)? == Some(false) {
                    self.report("E-TYPE-IF-CONDITION", &c.meta, "Bool", &ct);
                    ok = false;
                }
                if self.equal(&tt, &ft, &f.meta)? == Some(false) {
                    self.report("E-TYPE-IF-BRANCH", &f.meta, &tt, &ft);
                    ok = false;
                }
                Ok(if ok { tt } else { Ty::error() })
            }
            ExprKind::Fold { list, init, acc, item, body, .. } => {
                let xt = self.expr(list)?;
                let it = self.expr(init)?;
                let mut ok = !(xt.is_error() || it.is_error());
                let item_t = match self.head(&xt, TyTag::List, &list.meta)? {
                    Some(true) => xt.arg(0),
                    Some(false) => {
                        self.report("E-TYPE-FOLD-LIST", &list.meta, "List", &xt);
                        ok = false;
                        Ty::error()
                    }
                    None => Ty::error(),
                };
                self.env.push((acc, it.clone()));
                self.env.push((item, item_t));
                let bt = self.expr(body);
                self.env.pop();
                self.env.pop();
                let bt = bt?;
                ok &= !bt.is_error();
                if self.equal(&bt, &it, &body.meta)? == Some(false) {
                    self.report("E-TYPE-FOLD-BODY", &body.meta, &it, &bt);
                    ok = false;
                }
                Ok(if ok { it } else { Ty::error() })
            }
            ExprKind::Field { expr, target: Some((rt, i, n)), .. } => {
                // v1.1：e.f。e の型は field を持つレコード型（展開後の pair の入れ子）と等しい
                let t = self.expr(expr)?;
                let want = Ty::of(rt);
                // 型注釈から来た型はレコード名を持つ。名前が違えば、形が同じでも別のレコードの field とみなす
                let other = matches!((t.record(), want.record()), (Some(a), Some(b)) if a.name != b.name);
                let same = if other { Some(false) } else { self.equal(&t, &want, &expr.meta)? };
                match same {
                    Some(true) => {
                        let mut ft = want;
                        for _ in 0..*i {
                            ft = ft.arg(1);
                        }
                        if i + 1 < *n {
                            ft = ft.arg(0);
                        }
                        Ok(ft)
                    }
                    Some(false) => {
                        self.report("E-TYPE-FIELD-ACCESS", &expr.meta, &want, &t);
                        Ok(Ty::error())
                    }
                    None => Ok(Ty::error()),
                }
            }
            // records::expand の後には現れない
            ExprKind::Record { .. } | ExprKind::Field { .. } => Ok(Ty::error()),
            ExprKind::Match { scrutinee, on_none, binder, on_some, .. } => {
                let st = self.expr(scrutinee)?;
                let nt = self.expr(on_none)?;
                let mut ok = !(st.is_error() || nt.is_error());
                let payload = match self.head(&st, TyTag::Option, &scrutinee.meta)? {
                    Some(true) => st.arg(0),
                    Some(false) => {
                        self.report("E-TYPE-MATCH-SCRUTINEE", &scrutinee.meta, "Option", &st);
                        ok = false;
                        Ty::error()
                    }
                    None => Ty::error(),
                };
                self.env.push((binder, payload));
                let bt = self.expr(on_some);
                self.env.pop();
                let bt = bt?;
                ok &= !bt.is_error();
                if self.equal(&bt, &nt, &on_some.meta)? == Some(false) {
                    self.report("E-TYPE-MATCH-BRANCH", &on_some.meta, &nt, &bt);
                    ok = false;
                }
                Ok(if ok { nt } else { Ty::error() })
            }
            ExprKind::Call { callee, args, builtin, .. } => self.call(e, callee, args, *builtin),
        }
    }

    fn call(&mut self, e: &'a Expr, name: &str, args: &'a [Expr], builtin: bool) -> TcR<Ty> {
        let m = &e.meta;
        let arity = if builtin { builtin_arity(name).unwrap() } else { self.fns[name].params.len() };
        if args.len() != arity {
            let code = if builtin { "E-ARITY-BUILTIN" } else { "E-ARITY-USER" };
            self.report(code, m, format!("{arity} arguments"), format!("{} arguments", args.len()));
            for a in args {
                self.expr(a)?;
            }
            return Ok(Ty::error());
        }
        let mut ts = vec![];
        for a in args {
            ts.push(self.expr(a)?);
        }
        let mut ok = !ts.iter().any(|t| t.is_error());
        macro_rules! need {
            ($r:expr, $code:expr, $node:expr, $exp:expr, $act:expr) => {{
                let r = $r;
                if r == Some(false) {
                    self.report($code, $node, $exp, $act);
                    ok = false;
                }
                r
            }};
        }
        if !builtin {
            let f = self.fns[name];
            for ((a, t), p) in args.iter().zip(&ts).zip(&f.params) {
                let pt = Ty::of(&p.ty);
                need!(self.equal(t, &pt, &a.meta)?, "E-TYPE-ARG", &a.meta, &pt, t);
            }
            return Ok(if ok { Ty::of(&f.return_type) } else { Ty::error() });
        }
        let int = Ty::int();
        match name {
            "add" | "sub" | "mul" | "lt" | "le" | "mod" | "min" | "max" | "range" => {
                need!(self.equal(&ts[0], &int, &args[0].meta)?, "E-TYPE-ARG", &args[0].meta, &int, &ts[0]);
                need!(self.equal(&ts[1], &int, &args[1].meta)?, "E-TYPE-ARG", &args[1].meta, &int, &ts[1]);
                if !ok {
                    return Ok(Ty::error());
                }
                match name {
                    "lt" | "le" => self.build(Ty::bool(), m),
                    "range" => {
                        let inner = self.build(Ty::int(), m)?;
                        self.build(Ty::list(inner), m)
                    }
                    "mod" => {
                        let inner = self.build(Ty::int(), m)?;
                        self.build(Ty::option(inner), m)
                    }
                    _ => self.build(Ty::int(), m),
                }
            }
            "neg" => {
                need!(self.equal(&ts[0], &int, &args[0].meta)?, "E-TYPE-ARG", &args[0].meta, &int, &ts[0]);
                if ok { self.build(Ty::int(), m) } else { Ok(Ty::error()) }
            }
            "eq" => {
                need!(self.equal(&ts[0], &ts[1], &args[1].meta)?, "E-TYPE-EQ-OPERANDS", &args[1].meta, &ts[0], &ts[1]);
                if ok { self.build(Ty::bool(), m) } else { Ok(Ty::error()) }
            }
            "fst" | "snd" => {
                let code = if name == "fst" { "E-TYPE-FST-ARG" } else { "E-TYPE-SND-ARG" };
                need!(self.head(&ts[0], TyTag::Pair, &args[0].meta)?, code, &args[0].meta, "Pair", &ts[0]);
                Ok(if ok { ts[0].arg(if name == "fst" { 0 } else { 1 }) } else { Ty::error() })
            }
            "cons" => {
                let h = need!(self.head(&ts[1], TyTag::List, &args[1].meta)?, "E-TYPE-EXPECTED-LIST", &args[1].meta, "List", &ts[1]);
                if h == Some(true) {
                    let el = ts[1].arg(0);
                    need!(self.equal(&ts[0], &el, &args[0].meta)?, "E-TYPE-ARG", &args[0].meta, &el, &ts[0]);
                }
                Ok(if ok { ts[1].clone() } else { Ty::error() })
            }
            "concat" => {
                let h1 = need!(self.head(&ts[0], TyTag::List, &args[0].meta)?, "E-TYPE-EXPECTED-LIST", &args[0].meta, "List", &ts[0]);
                let h2 = need!(self.head(&ts[1], TyTag::List, &args[1].meta)?, "E-TYPE-EXPECTED-LIST", &args[1].meta, "List", &ts[1]);
                if h1 == Some(true) && h2 == Some(true) {
                    let (a, b) = (ts[0].arg(0), ts[1].arg(0));
                    need!(self.equal(&a, &b, &args[1].meta)?, "E-TYPE-ARG", &args[1].meta, &ts[0], &ts[1]);
                }
                Ok(if ok { ts[0].clone() } else { Ty::error() })
            }
            "contains" => {
                let h = need!(self.head(&ts[0], TyTag::List, &args[0].meta)?, "E-TYPE-EXPECTED-LIST", &args[0].meta, "List", &ts[0]);
                if h == Some(true) {
                    let el = ts[0].arg(0);
                    need!(self.equal(&ts[1], &el, &args[1].meta)?, "E-TYPE-ARG", &args[1].meta, &el, &ts[1]);
                }
                if ok { self.build(Ty::bool(), m) } else { Ok(Ty::error()) }
            }
            "sort" => {
                let li = Ty::list(Ty::int());
                need!(self.equal(&ts[0], &li, &args[0].meta)?, "E-TYPE-ARG", &args[0].meta, &li, &ts[0]);
                Ok(if ok { ts[0].clone() } else { Ty::error() })
            }
            "uncons" => {
                need!(self.head(&ts[0], TyTag::List, &args[0].meta)?, "E-TYPE-EXPECTED-LIST", &args[0].meta, "List", &ts[0]);
                if !ok {
                    return Ok(Ty::error());
                }
                let p = self.build(Ty::pair(ts[0].arg(0), ts[0].clone()), m)?;
                self.build(Ty::option(p), m)
            }
            "reverse" | "length" => {
                need!(self.head(&ts[0], TyTag::List, &args[0].meta)?, "E-TYPE-EXPECTED-LIST", &args[0].meta, "List", &ts[0]);
                if !ok {
                    Ok(Ty::error())
                } else if name == "reverse" {
                    Ok(ts[0].clone())
                } else {
                    self.build(Ty::int(), m)
                }
            }
            _ => unreachable!("unknown builtin {name}"),
        }
    }
}

// ======================================================================= driver

/// 受理済みプログラム（不透明値）。
#[derive(Clone, Debug)]
pub struct TypedProgram {
    pub program: Program,
    pub entry: String,
    pub input_type: Ty,
    pub output_type: Ty,
    pub rank: HashMap<String, usize>,
    pub spec_version: Option<String>,
    /// 検証済み部品（lexer・parser・名前解決・型検査）が作った実行可能プログラム。
    /// api::compile / compile_ast が設定する。
    pub verified: Option<std::sync::Arc<VerifiedProgram>>,
}

/// 検証済み部品の中間表現（`tlvm_verified::ir::EProg`）。
pub struct VerifiedProgram(pub tlvm_verified::ir::EProg);

impl std::fmt::Debug for VerifiedProgram {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "VerifiedProgram({} functions)", self.0.funcs.len())
    }
}

impl TypedProgram {
    pub fn function(&self, name: &str) -> &FnDecl {
        self.program.functions().find(|f| f.name == name).expect("accepted program resolves calls")
    }
}

#[derive(Default)]
pub struct CheckOutcome {
    pub diagnostics: Vec<Diagnostic>,
    pub typed: Option<TypedProgram>,
    pub work: Option<WorkCounter>,
}

pub fn check_program(prog: &Program, eof: usize, profile: &StaticProfile) -> CheckOutcome {
    let mut out = CheckOutcome::default();
    // name
    let name_diags = check_names(prog);
    if !name_diags.is_empty() {
        out.diagnostics = name_diags;
        return out;
    }
    let fns: Vec<&FnDecl> = prog.functions().collect();
    let entries: Vec<&EntryDecl> = prog.entries().collect();
    let fn_map: HashMap<&str, &FnDecl> = fns.iter().map(|f| (f.name.as_str(), *f)).collect();

    // call-graph（循環があっても typecheck と entry は実行する）
    let cg = check_call_graph(&fns);
    out.diagnostics.extend(cg.diags.iter().cloned());

    // typecheck + semantic-limits
    let mut tc = TypeChecker::new(&fn_map, profile);
    for f in &fns {
        if let Err(cutoff) = tc.check_function(f) {
            out.work = Some(tc.work);
            out.diagnostics.append(&mut tc.diags);
            out.diagnostics.push(cutoff);
            return out;
        }
    }
    out.work = Some(tc.work);
    out.diagnostics.append(&mut tc.diags);

    // entry
    let mut entry_ok = false;
    if entries.is_empty() {
        out.diagnostics.push(Diagnostic::error("entry", "E-ENTRY-MISSING", (eof, eof)));
    } else if entries.len() >= 2 {
        let d = entries[1];
        out.diagnostics.push(Diagnostic::error("entry", "E-ENTRY-DUPLICATE", d.meta.span()).at(d.meta.index));
    } else {
        let d = entries[0];
        let n = fn_map[d.name.as_str()].params.len();
        if n != 1 {
            out.diagnostics.push(
                Diagnostic::error("entry", "E-ENTRY-ARITY", d.name_span.t()).exp("1 parameter").act(format!("{n} parameters")).at(d.meta.index),
            );
        } else {
            entry_ok = true;
        }
    }

    // warnings
    if entry_ok {
        let root = entries[0].name.as_str();
        let mut live: HashSet<&str> = HashSet::from([root]);
        let mut todo = vec![root];
        while let Some(f) = todo.pop() {
            for c in &cg.edges[f] {
                if live.insert(c.callee) {
                    todo.push(c.callee);
                }
            }
        }
        for f in &fns {
            if !live.contains(f.name.as_str()) {
                out.diagnostics.push(Diagnostic::warning("warnings", "W-UNUSED-FUNCTION", f.name_span.t()).at(f.meta.index));
            }
        }
    }

    if !out.diagnostics.iter().any(|d| d.severity == "error") {
        let ef = fn_map[entries[0].name.as_str()];
        out.typed = Some(TypedProgram {
            program: prog.clone(),
            entry: ef.name.clone(),
            input_type: Ty::of(&ef.params[0].ty),
            output_type: Ty::of(&ef.return_type),
            rank: cg.rank.unwrap_or_default(),
            spec_version: None,
            verified: None,
        });
    }
    out
}
