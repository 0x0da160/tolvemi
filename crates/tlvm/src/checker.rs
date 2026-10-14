//! 共通静的検査：name → call-graph → typecheck(+semantic-limits) → entry → warnings。
//!
//! Surface（compile）と AST（compile_ast）の双方がこのモジュールを通る
//! （設計書 §5、§6、§10.2、§18.1a）。

use crate::diagnostics::{closest, Diagnostic};
use crate::profiles::StaticProfile;
use crate::syntax::*;
use std::collections::{HashMap, HashSet};

// ======================================================================= name

const BUILTINS: [&str; 25] = [
    "add", "sub", "mul", "neg", "lt", "le", "eq", "mod", "fst", "snd", "cons", "concat", "reverse", "length", "uncons",
    "min", "max", "range", "contains", "sort", "code", "char", "to_string", "parse_int", "div",
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
            ExprKind::Call { callee, args, builtin, callee_span, .. } => {
                if !builtin && !known.contains(callee.as_str()) {
                    let hof = HofOp::ALL.map(HofOp::name);
                    let near = closest(callee, known.iter().copied().chain(BUILTINS).chain(hof).chain([LOOP]).chain(DICT_OPS), 3);
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
            // v1.5：map などの binder は本体の中でだけ見える（match_option の binder と同じ規則）
            ExprKind::Hof { list, binder, binder_span, body, .. } => {
                walk(list, env, known, diags);
                if env.contains(&binder.as_str()) {
                    diags.push(Diagnostic::error("name", "E-NAME-SHADOW", binder_span.t()).act(binder).at(idx));
                }
                env.push(binder);
                walk(body, env, known, diags);
                env.pop();
            }
            // v1.6：loop の binder も本体の中でだけ見える
            ExprKind::Loop { init, max, binder, binder_span, body } => {
                walk(init, env, known, diags);
                walk(max, env, known, diags);
                if env.contains(&binder.as_str()) {
                    diags.push(Diagnostic::error("name", "E-NAME-SHADOW", binder_span.t()).act(binder).at(idx));
                }
                env.push(binder);
                walk(body, env, known, diags);
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
            // v1.4：二つの binder はそれぞれの枝でだけ見える（同じ名前でもよい）
            ExprKind::MatchResult { scrutinee, ok_binder, ok_span, on_ok, err_binder, err_span, on_err } => {
                walk(scrutinee, env, known, diags);
                for (b, sp, body) in [(ok_binder, ok_span, on_ok), (err_binder, err_span, on_err)] {
                    if env.contains(&b.as_str()) {
                        diags.push(Diagnostic::error("name", "E-NAME-SHADOW", sp.t()).act(b).at(idx));
                    }
                    env.push(b);
                    walk(body, env, known, diags);
                    env.pop();
                }
            }
            // v1.4：`match` の枝の束縛（`_` は束縛しない）。一つの枝の中では相異なる名前
            ExprKind::SumMatch { scrutinee, arms, .. } => {
                walk(scrutinee, env, known, diags);
                for a in arms {
                    let n = env.len();
                    for (b, sp) in &a.pat.binds {
                        if b == "_" {
                            continue;
                        }
                        if env[n..].contains(&b.as_str()) {
                            diags.push(Diagnostic::error("name", "E-NAME-DUPLICATE-BINDER", sp.t()).act(b).at(idx));
                        } else if env.contains(&b.as_str()) {
                            diags.push(Diagnostic::error("name", "E-NAME-SHADOW", sp.t()).act(b).at(idx));
                        }
                        env.push(b);
                    }
                    walk(&a.body, env, known, diags);
                    env.truncate(n);
                }
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
            Decl::Type(_) | Decl::Sum(_) => {}
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

/// v1.7：`rec` の印のある関数へ入る辺を除いた呼出しグラフが DAG であることを検査し、ランクを作る。
/// ランクは印のない呼出し先について rank[callee] < rank[caller] を満たす（印のある呼出し先は免除。
/// 検証済みの型付け条件「rank[g] < r または rec[g]」に合わせる）。`edges` は除く前の全ての辺（未使用の警告用）。
pub fn check_call_graph<'a>(fns: &[&'a FnDecl]) -> CallGraph<'a> {
    let edges: HashMap<&str, Vec<CallSite>> = fns.iter().map(|f| (f.name.as_str(), user_calls(&f.body))).collect();
    let marked: HashSet<&str> = fns.iter().filter(|f| f.rec).map(|f| f.name.as_str()).collect();
    let dag: HashMap<&str, Vec<&CallSite>> =
        edges.iter().map(|(f, cs)| (*f, cs.iter().filter(|c| !marked.contains(c.callee)).collect())).collect();
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
            let succ = &dag[v];
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
        let inner: Vec<&CallSite> = comp.iter().flat_map(|f| dag[f].iter().copied()).filter(|c| members.contains(c.callee)).collect();
        if let Some(primary) = inner.iter().min_by_key(|c| c.span) {
            let mut names: Vec<&str> = members.iter().copied().collect();
            names.sort();
            let list = names.join(", ");
            let mut d = Diagnostic::error("call-graph", "E-CYCLE-CALL", primary.span).act(list.clone()).at(primary.index);
            d.message = format!("関数呼出しが循環しています: {list}");
            // v1.7：循環にある関数（の先頭）に `rec` を付ける修復ヒント
            if let Some(first) = fns.iter().filter(|f| members.contains(f.name.as_str())).min_by_key(|f| f.meta.span().0) {
                let at = first.meta.span().0;
                d = d.fix(
                    "insert_text",
                    (at, at),
                    format!(
                        "'rec ' before 'fn' of every function on the cycle ({list}) to allow unbounded recursion (termination is then not guaranteed); prefer fold or loop when the number of steps is bounded"
                    ),
                );
            }
            diags.push(d);
        }
    }
    let rank = if diags.is_empty() {
        let mut rank: HashMap<String, usize> = HashMap::new();
        for comp in &sccs {
            let f = comp[0];
            let r = dag[f].iter().map(|c| rank[c.callee] + 1).max().unwrap_or(0);
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

impl Ev {
    fn name(self) -> &'static str {
        match self {
            Ev::Visit => "visit",
            Ev::Build => "build",
            Ev::Compare => "compare",
        }
    }
}

/// v1.12：型比較の共有（比較 cache）の切替。On は比較の結果と論理イベント列を覚え、同じ対の再照合では列を再生して計数する。
/// 論理 trace・仕事量・cutoff は Off と同じになる（§18.1a）。interning は行わない。
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub enum TypeSharing {
    #[default]
    Off,
    On,
}

/// v1.12：`check_program_with` の選択。trace は試験用の論理 trace（イベント名と論理 node index）を取る。
#[derive(Clone, Copy, Debug, Default)]
pub struct CheckOptions {
    pub sharing: TypeSharing,
    pub trace: bool,
}

/// `equal` の一回分の結果。鍵の型は保持し、Arc の address が再利用されないようにする。
struct CachedEq {
    _a: Ty,
    _b: Ty,
    result: Option<bool>,
    events: Vec<Ev>,
}

type TcR<T> = Result<T, Diagnostic>;

/// v1.5：`map` などの node（論理 node index）ごとの（要素の型 A、本体の型）。`hof::lower` が使う。
/// v1.6：`loop` の node は（状態の型 S、本体の型 Option<S>）。
/// v1.9：辞書の操作（`dict_get` などの呼び出し）の node は（鍵の型 K、値の型 V）。
pub type HofTypes = HashMap<usize, (Ty, Ty)>;

/// v1.10：総称の関数の呼び出し（論理 node index）ごとの型引数（明示したものか推論したもの。呼び出し側の型引数を
/// 含みうる）。`generics::monomorphize` が使う。
pub type Instances = HashMap<usize, Vec<Ty>>;

/// v1.10：型の照合（`TypeChecker::bind`）の失敗。
enum Bad {
    /// 形が違う
    Shape,
    /// i 番目の型引数に、前の束縛（第 2 要素）と違う型（第 3 要素）が当たった
    Conflict(usize, Ty, Ty),
}

pub struct TypeChecker<'a> {
    fns: &'a HashMap<&'a str, &'a FnDecl>,
    profile: &'a StaticProfile,
    pub work: WorkCounter,
    pub diags: Vec<Diagnostic>,
    env: Vec<(&'a str, Ty)>,
    pub hof: HofTypes,
    /// v1.10：総称の関数の呼び出しの型引数
    pub inst: Instances,
    /// v1.12：比較 cache の切替、cache（鍵は両型の address）、`equal` の中で出した論理イベント（On のときだけ記録）
    sharing: TypeSharing,
    cache: HashMap<(usize, usize), CachedEq>,
    rec: Option<Vec<Ev>>,
    /// v1.12：cache から再生した回数（試験用。論理計数には入らない）
    pub sharing_hits: u64,
    /// v1.12：試験用の論理 trace（None なら記録しない）
    pub trace: Option<Vec<(&'static str, usize)>>,
    /// 規則 G（§18.1c）：いまの関数の論理イベントを数えるか。第二パスで複製でない関数は検査するが数えない。
    counting: bool,
}

impl<'a> TypeChecker<'a> {
    pub fn new(fns: &'a HashMap<&'a str, &'a FnDecl>, profile: &'a StaticProfile) -> Self {
        TypeChecker {
            fns,
            profile,
            work: WorkCounter::default(),
            diags: vec![],
            env: vec![],
            hof: HashMap::new(),
            inst: HashMap::new(),
            sharing: TypeSharing::Off,
            cache: HashMap::new(),
            rec: None,
            sharing_hits: 0,
            trace: None,
            counting: true,
        }
    }

    /// v1.12：比較 cache の切替と論理 trace の有無を決める（`new` の直後に一度だけ呼ぶ）。
    pub fn configure(&mut self, o: CheckOptions) {
        self.sharing = o.sharing;
        self.trace = o.trace.then(Vec::new);
    }

    /// v1.10：`pat` の型引数（名前が `vars` にあるもの）を `t` の対応する部分に束縛する一方向の照合。
    /// `t` の型引数（呼び出し側の総称の関数の型引数）は定数として扱う。ErrorType を含む部分は照合しない。
    fn bind(&mut self, pat: &Ty, t: &Ty, vars: &[String], sub: &mut [Option<Ty>], node: &Meta) -> TcR<Result<(), Bad>> {
        if t.is_error() || pat.is_error() {
            return Ok(Ok(()));
        }
        if let Some(i) = pat.param_name().and_then(|n| vars.iter().position(|v| v == n)) {
            self.event(Ev::Compare, node)?;
            return Ok(match sub[i].clone() {
                None => {
                    sub[i] = Some(t.clone());
                    Ok(())
                }
                Some(prev) => match self.equal(&prev, t, node)? {
                    Some(false) => Err(Bad::Conflict(i, prev, t.clone())),
                    _ => Ok(()),
                },
            });
        }
        if !pat.has_params() {
            return Ok(match self.equal(pat, t, node)? {
                Some(false) => Err(Bad::Shape),
                _ => Ok(()),
            });
        }
        self.event(Ev::Compare, node)?;
        if pat.tag() != t.tag() || pat.args().len() != t.args().len() {
            return Ok(Err(Bad::Shape));
        }
        for (p, q) in pat.args().iter().zip(t.args()) {
            if let Err(b) = self.bind(p, q, vars, sub, node)? {
                return Ok(Err(b));
            }
        }
        Ok(Ok(()))
    }

    /// v1.10：総称のレコード型・直和型の展開後の型 `want`（型引数を含む）と値の型 `t` を照合し、型引数の束縛を返す。
    fn bind_template(&mut self, want: &Ty, t: &Ty, node: &Meta) -> TcR<Option<Vec<(String, Ty)>>> {
        let vars: Vec<String> = match want.record().map(|r| r.generic.clone()).or_else(|| want.sum().map(|s| s.generic.clone())) {
            Some(Some(g)) => g.params,
            _ => collect_params(want),
        };
        let mut sub = vec![None; vars.len()];
        Ok(match self.bind(want, t, &vars, &mut sub, node)? {
            Ok(()) => Some(vars.into_iter().zip(sub).filter_map(|(v, s)| s.map(|s| (v, s))).collect()),
            Err(_) => None,
        })
    }

    fn event(&mut self, ev: Ev, node: &Meta) -> TcR<()> {
        if !self.counting {
            // 規則 G：数えない関数の比較も、外側の比較 cache の記録には入れる（数える場合に同じ列を再生できるように）
            if let Some(r) = self.rec.as_mut() {
                r.push(ev);
            }
            return Ok(());
        }
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
        if let Some(r) = self.rec.as_mut() {
            r.push(ev);
        }
        if let Some(t) = self.trace.as_mut() {
            t.push((ev.name(), node.index));
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

    /// Equal(A,B)。ErrorType を含むなら 0 イベントで None。On のときは同じ対の既知の結果を、覚えた論理イベント列の再生で返す。
    fn equal(&mut self, a: &Ty, b: &Ty, node: &Meta) -> TcR<Option<bool>> {
        if a.is_error() || b.is_error() {
            return Ok(None);
        }
        if self.sharing == TypeSharing::Off {
            return self.equal_plain(a, b, node);
        }
        let key = (a.addr(), b.addr());
        if let Some((res, evs)) = self.cache.get(&key).map(|c| (c.result, c.events.clone())) {
            self.sharing_hits += 1;
            for ev in evs {
                self.event(ev, node)?;
            }
            return Ok(res);
        }
        let outer = self.rec.replace(vec![]);
        let r = self.equal_plain(a, b, node);
        let mine = std::mem::replace(&mut self.rec, outer).unwrap_or_default();
        if let Some(o) = self.rec.as_mut() {
            o.extend(mine.iter().copied());
        }
        let res = r?;
        self.cache.insert(key, CachedEq { _a: a.clone(), _b: b.clone(), result: res, events: mine });
        Ok(res)
    }

    fn equal_plain(&mut self, a: &Ty, b: &Ty, node: &Meta) -> TcR<Option<bool>> {
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
        let before = self.diags.len();
        let body_t = self.expr(&f.body)?;
        let ret = Ty::of(&f.return_type);
        if self.equal(&body_t, &ret, &f.body.meta)? == Some(false) {
            self.report("E-TYPE-RETURN", &f.body.meta, &ret, &body_t);
        }
        // v1.10：総称の関数の本体で、型引数の値に特定の型の操作（add など）を使った
        for d in &mut self.diags[before..] {
            let Some(t) = f.type_params.iter().find(|p| d.actual.as_deref() == Some(p.name.as_str())) else { continue };
            if d.repair.is_some() || !d.code.starts_with("E-TYPE-") {
                continue;
            }
            let (t, name) = (&t.name, f.ctor.as_deref().unwrap_or(&f.name));
            let need = d.expected.clone().unwrap_or_else(|| "a concrete type".into());
            *d = d.clone().fix(
                "replace_expression",
                d.span,
                format!(
                    "{t} is a type parameter of {name}: in the body a value of type {t} supports only what works for every type (eq, pair, some, cons, list<{t}>(...), passing it on); to use it as {need}, give {name} a parameter of type {need} instead of {t}, or do this part in the caller where the type is known"
                ),
            );
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
            ExprKind::Char(_) => self.build(Ty::char(), m),
            ExprKind::Str(_) => {
                let c = self.build(Ty::char(), m)?;
                self.build(Ty::list(c), m)
            }
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
            // v1.9：`dict<K, V>()` は Dict<K, V>
            ExprKind::DictNew(t) => self.build(Ty::of(t), m),
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
            ExprKind::Hof { op, list, binder, body, .. } => self.hof(e, *op, list, binder, body),
            ExprKind::Loop { init, max, binder, body, .. } => self.loop_(e, init, max, binder, body),
            ExprKind::Field { expr, target: Some((rt, i, n)), .. } => {
                // v1.1：e.f。e の型は field を持つレコード型（展開後の pair の入れ子）と等しい
                let t = self.expr(expr)?;
                let want = Ty::of(rt);
                // 型注釈から来た型はレコード名を持つ。名前が違えば、形が同じでも別のレコードの field とみなす
                let other = matches!((t.record(), want.record()), (Some(a), Some(b)) if a.name != b.name);
                // v1.10：総称のレコード型は型引数を照合で決める
                let mut binds = vec![];
                let same = if other {
                    Some(false)
                } else if want.has_params() && !t.is_error() {
                    match self.bind_template(&want, &t, &expr.meta)? {
                        Some(b) => {
                            binds = b;
                            Some(true)
                        }
                        None => Some(false),
                    }
                } else {
                    self.equal(&t, &want, &expr.meta)?
                };
                match same {
                    Some(true) => {
                        // v1.15：印つきの型（名義の型）は印の後ろの展開後の構造で field を数える
                        let mut ft = if want.record().is_some_and(|r| r.tagged) { want.arg(1) } else { want.clone() };
                        for _ in 0..*i {
                            ft = ft.arg(1);
                        }
                        if i + 1 < *n {
                            ft = ft.arg(0);
                        }
                        if !binds.is_empty() {
                            ft = ft.subst(&|p| binds.iter().find(|(q, _)| q == p).map(|(_, t)| t.clone()));
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
            ExprKind::Call { callee, args, builtin, type_args, callee_span } => self.call(e, callee, args, *builtin, type_args, *callee_span),
            // v1.4：ok<T, E>(x) は x : T、err<T, E>(x) は x : E のとき Result<T, E>
            ExprKind::Inj { ok, ty, value } => {
                let vt = self.expr(value)?;
                let want = Ty::of(ty);
                let payload = want.arg(if *ok { 0 } else { 1 });
                match self.equal(&vt, &payload, &value.meta)? {
                    Some(true) => self.build(want, m),
                    Some(false) => {
                        self.report("E-TYPE-ARG", &value.meta, &payload, &vt);
                        Ok(Ty::error())
                    }
                    None => Ok(Ty::error()),
                }
            }
            ExprKind::MatchResult { scrutinee, ok_binder, on_ok, err_binder, on_err, .. } => {
                let st = self.expr(scrutinee)?;
                let mut ok = !st.is_error();
                let (a, b) = match self.head(&st, TyTag::Result, &scrutinee.meta)? {
                    Some(true) => (st.arg(0), st.arg(1)),
                    Some(false) => {
                        self.report("E-TYPE-MATCH-SCRUTINEE", &scrutinee.meta, "Result", &st);
                        ok = false;
                        (Ty::error(), Ty::error())
                    }
                    None => (Ty::error(), Ty::error()),
                };
                self.env.push((ok_binder, a));
                let at = self.expr(on_ok);
                self.env.pop();
                let at = at?;
                self.env.push((err_binder, b));
                let bt = self.expr(on_err);
                self.env.pop();
                let bt = bt?;
                ok &= !(at.is_error() || bt.is_error());
                if self.equal(&bt, &at, &on_err.meta)? == Some(false) {
                    self.report("E-TYPE-MATCH-BRANCH", &on_err.meta, &at, &bt);
                    ok = false;
                }
                Ok(if ok { at } else { Ty::error() })
            }
            ExprKind::SumMatch { scrutinee, arms, kind: Some(kind), .. } => self.sum_match(scrutinee, arms, kind),
            // sums::expand の後には現れない
            ExprKind::SumMatch { .. } => Ok(Ty::error()),
        }
    }

    /// v1.5：`map(xs, |x| e)` など。xs : List<A>（String も）、x : A。filter・any・all・find の本体は Bool、
    /// sort_by の本体は Int。結果は map が List<B>、filter・sort_by が List<A>、any・all が Bool、find が Option<A>。
    fn hof(&mut self, e: &'a Expr, op: HofOp, list: &'a Expr, binder: &'a str, body: &'a Expr) -> TcR<Ty> {
        let m = &e.meta;
        let xt = self.expr(list)?;
        let mut ok = !xt.is_error();
        let elem = match self.head(&xt, TyTag::List, &list.meta)? {
            Some(true) => xt.arg(0),
            Some(false) => {
                self.report("E-TYPE-HOF-LIST", &list.meta, "List", &xt);
                ok = false;
                Ty::error()
            }
            None => Ty::error(),
        };
        self.env.push((binder, elem.clone()));
        let bt = self.expr(body);
        self.env.pop();
        let bt = bt?;
        ok &= !bt.is_error();
        let want = match op {
            HofOp::Map => None,
            HofOp::SortBy => Some(Ty::int()),
            _ => Some(Ty::bool()),
        };
        if let Some(w) = want {
            if self.equal(&bt, &w, &body.meta)? == Some(false) {
                self.report("E-TYPE-HOF-BODY", &body.meta, &w, &bt);
                ok = false;
            }
        }
        if !ok {
            return Ok(Ty::error());
        }
        self.hof.insert(m.index, (elem.clone(), bt.clone()));
        match op {
            HofOp::Map => self.build(Ty::list(bt), m),
            HofOp::Filter | HofOp::SortBy => Ok(xt),
            HofOp::Any | HofOp::All => self.build(Ty::bool(), m),
            HofOp::Find => self.build(Ty::option(elem), m),
        }
    }

    /// v1.6：`loop(init, max, |s| e)`。init : S、max : Int、s : S の下で e : Option<S>。結果は Option<S>。
    /// 規則 L（§18.1c）：結果型 Option<S> の BuildType は、init・max・e がすべて正常なときだけ、最後に一つ数える。
    fn loop_(&mut self, e: &'a Expr, init: &'a Expr, max: &'a Expr, binder: &'a str, body: &'a Expr) -> TcR<Ty> {
        let m = &e.meta;
        let st = self.expr(init)?;
        let mt = self.expr(max)?;
        let mut ok = !(st.is_error() || mt.is_error());
        if self.equal(&mt, &Ty::int(), &max.meta)? == Some(false) {
            self.report("E-TYPE-LOOP-MAX", &max.meta, "Int", &mt);
            ok = false;
        }
        self.env.push((binder, st.clone()));
        let bt = self.expr(body);
        self.env.pop();
        let bt = bt?;
        ok &= !bt.is_error();
        if !st.is_error() {
            let want = Ty::option(st.clone());
            if self.equal(&bt, &want, &body.meta)? == Some(false) {
                self.report("E-TYPE-LOOP-BODY", &body.meta, &want, &bt);
                ok = false;
            }
        }
        if !ok {
            return Ok(Ty::error());
        }
        self.build(Ty::option(st.clone()), m)?;
        self.hof.insert(m.index, (st, bt.clone()));
        Ok(bt)
    }

    /// v1.4：`match`。対象の型を確かめ、枝ごとに束縛の型を決めて本体を検査する（枝の型はすべて等しい）。
    fn sum_match(&mut self, scrutinee: &'a Expr, arms: &'a [Arm], kind: &'a MatchKind) -> TcR<Ty> {
        let st = self.expr(scrutinee)?;
        let sm = &scrutinee.meta;
        let mut ok = !st.is_error();
        // 場合ごとの束縛の型（対象の型が合わなければ ErrorType）
        let fields: Vec<Vec<Ty>> = match kind {
            MatchKind::Sum { ty, fields } => {
                let want = Ty::of(ty);
                // v1.10：総称の直和型は対象の型と照合して型引数を決め、中身の型に入れる
                let mut binds = vec![];
                if want.has_params() && !st.is_error() {
                    match self.bind_template(&want, &st, sm)? {
                        Some(b) => binds = b,
                        None => {
                            self.report("E-TYPE-MATCH-SCRUTINEE", sm, &want, &st);
                            ok = false;
                        }
                    }
                } else if self.equal(&st, &want, sm)? == Some(false) {
                    self.report("E-TYPE-MATCH-SCRUTINEE", sm, &want, &st);
                    ok = false;
                }
                let inst = |f: &TypeNode| Ty::of(f).subst(&|p| binds.iter().find(|(q, _)| q == p).map(|(_, t)| t.clone()));
                fields.iter().map(|fs| fs.iter().map(|f| if ok { inst(f) } else { Ty::error() }).collect()).collect()
            }
            MatchKind::Result | MatchKind::Option => {
                let (tag, name) = if *kind == MatchKind::Result { (TyTag::Result, "Result") } else { (TyTag::Option, "Option") };
                match self.head(&st, tag, sm)? {
                    Some(true) if tag == TyTag::Result => vec![vec![st.arg(0)], vec![st.arg(1)]],
                    Some(true) => vec![vec![st.arg(0)], vec![]],
                    r => {
                        if r == Some(false) {
                            self.report("E-TYPE-MATCH-SCRUTINEE", sm, name, &st);
                        }
                        ok = false;
                        vec![vec![Ty::error()], vec![Ty::error()]]
                    }
                }
            }
            MatchKind::Any => {
                if !st.is_error() {
                    self.event(Ev::Compare, sm)?;
                    if !(st.sum().is_some() || matches!(st.tag(), TyTag::Result | TyTag::Option)) {
                        self.report("E-TYPE-MATCH-SCRUTINEE", sm, "sum type, Result or Option", &st);
                        ok = false;
                    }
                }
                vec![]
            }
        };
        let mut first: Option<Ty> = None;
        for a in arms {
            let n = self.env.len();
            if let Some(v) = a.variant {
                for (i, (b, _)) in a.pat.binds.iter().enumerate() {
                    if b != "_" {
                        let t = fields.get(v).and_then(|fs| fs.get(i)).cloned().unwrap_or_else(Ty::error);
                        self.env.push((b, t));
                    }
                }
            }
            let t = self.expr(&a.body);
            self.env.truncate(n);
            let t = t?;
            if t.is_error() {
                ok = false;
                continue;
            }
            match &first {
                None => first = Some(t),
                Some(f) => {
                    if self.equal(&t, f, &a.body.meta)? == Some(false) {
                        let f = f.clone();
                        self.report("E-TYPE-MATCH-BRANCH", &a.body.meta, &f, &t);
                        ok = false;
                    }
                }
            }
        }
        Ok(match first {
            Some(t) if ok => t,
            _ => Ty::error(),
        })
    }

    /// v1.10：総称の関数の呼び出し（型引数を書いたものも）。型引数は明示したものを使い、なければ引数の型との照合で
    /// 推論する（一階の照合。戻り型だけに現れる型引数は推論できないので明示を求める）。
    fn generic_call(&mut self, e: &'a Expr, name: &str, args: &'a [Expr], type_args: &'a [TypeNode], callee_span: Sp) -> TcR<Ty> {
        let m = &e.meta;
        let f = self.fns[name];
        let shown = f.ctor.as_deref().unwrap_or(name).to_string();
        let vars: Vec<String> = f.type_params.iter().map(|p| p.name.clone()).collect();
        let mut ts = vec![];
        for a in args {
            ts.push(self.expr(a)?);
        }
        if !type_args.is_empty() && type_args.len() != vars.len() {
            let span = (callee_span.0, m.span().1);
            let fix = if vars.is_empty() {
                format!("{shown}(...) without type arguments: {shown} is not generic")
            } else {
                format!("{shown}<{}>(...) with {} type argument(s), one per type parameter", vars.join(", "), vars.len())
            };
            self.diags.push(
                Diagnostic::error("typecheck", "E-TYPE-GENERIC-ARITY", span)
                    .exp(format!("{} type arguments", vars.len()))
                    .act(format!("{} type arguments", type_args.len()))
                    .at(m.index)
                    .fix("replace_expression", span, fix),
            );
            return Ok(Ty::error());
        }
        if args.len() != f.params.len() {
            let n = f.params.len();
            self.report("E-ARITY-USER", m, format!("{n} arguments"), format!("{} arguments", args.len()));
            return Ok(Ty::error());
        }
        let explicit = !type_args.is_empty();
        let mut sub: Vec<Option<Ty>> = type_args.iter().map(|t| Some(Ty::of(t))).collect();
        sub.resize(vars.len(), None);
        let mut ok = !ts.iter().any(|t| t.is_error());
        for ((a, t), p) in args.iter().zip(&ts).zip(&f.params) {
            let pt = Ty::of(&p.ty);
            match self.bind(&pt, t, &vars, &mut sub, &a.meta)? {
                Ok(()) => {}
                Err(Bad::Conflict(i, prev, new)) if !explicit => {
                    let v = &vars[i];
                    self.diags.push(
                        Diagnostic::error("typecheck", "E-TYPE-GENERIC-MISMATCH", a.meta.span())
                            .exp(prev.to_string())
                            .act(new.to_string())
                            .at(a.meta.index)
                            .fix(
                                "replace_expression",
                                a.meta.span(),
                                format!(
                                    "expression whose type gives {v} = {prev}: the type parameter {v} of {shown} was inferred as {prev} from an earlier argument, so every argument written with {v} must use {prev}; if a different type is meant, convert the arguments first or write {shown}<...>(...) explicitly"
                                ),
                            ),
                    );
                    ok = false;
                }
                Err(_) => {
                    let shown_t = pt.subst(&|n| vars.iter().position(|v| v == n).and_then(|i| sub[i].clone()));
                    self.report("E-TYPE-ARG", &a.meta, &shown_t, t);
                    ok = false;
                }
            }
        }
        if !ok {
            return Ok(Ty::error());
        }
        if sub.iter().any(|s| s.is_none()) {
            let missing: Vec<&str> = vars.iter().zip(&sub).filter(|(_, s)| s.is_none()).map(|(v, _)| v.as_str()).collect();
            let shape: Vec<String> = vars.iter().zip(&sub).map(|(v, s)| s.as_ref().map_or(v.clone(), |t| t.to_string())).collect();
            let at = callee_span.1;
            let parens = if f.params.is_empty() { "()" } else { "(...)" };
            self.diags.push(
                Diagnostic::error("typecheck", "E-TYPE-GENERIC-INFER", callee_span.t())
                    .exp(format!("type arguments for {}", missing.join(", ")))
                    .act(format!("{shown}{parens}"))
                    .at(m.index)
                    .fix(
                        "insert_text",
                        (at, at),
                        format!(
                            "'<{}>' after {shown}, replacing {} with concrete types: {} cannot be inferred from the argument types (it appears only in the return type or nowhere in the parameters), so write {shown}<{}>{parens}",
                            shape.join(", "),
                            missing.join(", "),
                            missing.join(", "),
                            shape.join(", ")
                        ),
                    ),
            );
            return Ok(Ty::error());
        }
        let tys: Vec<Ty> = sub.into_iter().map(|s| s.expect("all bound")).collect();
        for t in &tys {
            self.build(t.clone(), m)?;
        }
        let ret = Ty::of(&f.return_type).subst(&|n| vars.iter().position(|v| v == n).map(|i| tys[i].clone()));
        self.inst.insert(m.index, tys);
        self.build(ret, m)
    }

    fn call(&mut self, e: &'a Expr, name: &str, args: &'a [Expr], builtin: bool, type_args: &'a [TypeNode], callee_span: Sp) -> TcR<Ty> {
        let m = &e.meta;
        if !builtin && (!type_args.is_empty() || !self.fns[name].type_params.is_empty()) {
            return self.generic_call(e, name, args, type_args, callee_span);
        }
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
            "add" | "sub" | "mul" | "lt" | "le" | "mod" | "div" | "min" | "max" | "range" => {
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
                    "mod" | "div" => {
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
                // v1.15：名義の型は Pair の別名ではない（印の後ろの構造を fst・snd で取り出させない）
                let named = ts[0].record().is_some_and(|r| r.tagged) || ts[0].sum().is_some_and(|s| s.tagged);
                let pair = if named { Some(false) } else { self.head(&ts[0], TyTag::Pair, &args[0].meta)? };
                need!(pair, code, &args[0].meta, "Pair", &ts[0]);
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
            // v1.2：文字と文字列
            "code" => {
                let c = Ty::char();
                need!(self.equal(&ts[0], &c, &args[0].meta)?, "E-TYPE-ARG", &args[0].meta, &c, &ts[0]);
                if ok { self.build(Ty::int(), m) } else { Ok(Ty::error()) }
            }
            "char" | "to_string" => {
                need!(self.equal(&ts[0], &int, &args[0].meta)?, "E-TYPE-ARG", &args[0].meta, &int, &ts[0]);
                if !ok {
                    return Ok(Ty::error());
                }
                let c = self.build(Ty::char(), m)?;
                if name == "char" { self.build(Ty::option(c), m) } else { self.build(Ty::list(c), m) }
            }
            "parse_int" => {
                let st = Ty::string();
                need!(self.equal(&ts[0], &st, &args[0].meta)?, "E-TYPE-ARG", &args[0].meta, &st, &ts[0]);
                if !ok {
                    return Ok(Ty::error());
                }
                let i = self.build(Ty::int(), m)?;
                self.build(Ty::option(i), m)
            }
            // v1.9：辞書の操作
            "dict_from" => {
                // 引数は List<Pair<K, V>>
                let shape = match (self.head(&ts[0], TyTag::List, &args[0].meta)?, ok) {
                    (Some(true), true) => self.head(&ts[0].arg(0), TyTag::Pair, &args[0].meta)?,
                    (r, _) => r,
                };
                need!(shape, "E-TYPE-DICT-FROM", &args[0].meta, "List<Pair<K, V>>", &ts[0]);
                if !ok {
                    return Ok(Ty::error());
                }
                let (k, v) = (ts[0].arg(0).arg(0), ts[0].arg(0).arg(1));
                self.hof.insert(m.index, (k.clone(), v.clone()));
                self.build(Ty::dict(k, v), m)
            }
            _ if DICT_OPS.contains(&name) => {
                let h = need!(self.head(&ts[0], TyTag::Dict, &args[0].meta)?, "E-TYPE-DICT-ARG", &args[0].meta, "Dict<K, V>", &ts[0]);
                if h != Some(true) {
                    return Ok(Ty::error());
                }
                let (k, v) = (ts[0].arg(0), ts[0].arg(1));
                // 鍵（dict_get・dict_put・dict_remove・dict_has の第 2 引数）と値（dict_put の第 3 引数）
                if args.len() >= 2 {
                    need!(self.equal(&ts[1], &k, &args[1].meta)?, "E-TYPE-ARG", &args[1].meta, &k, &ts[1]);
                }
                if args.len() == 3 {
                    need!(self.equal(&ts[2], &v, &args[2].meta)?, "E-TYPE-ARG", &args[2].meta, &v, &ts[2]);
                }
                if !ok {
                    return Ok(Ty::error());
                }
                self.hof.insert(m.index, (k.clone(), v.clone()));
                match name {
                    "dict_get" => self.build(Ty::option(v), m),
                    "dict_put" | "dict_remove" => Ok(ts[0].clone()),
                    "dict_has" => self.build(Ty::bool(), m),
                    "dict_size" => self.build(Ty::int(), m),
                    "dict_keys" => self.build(Ty::list(k), m),
                    "dict_values" => self.build(Ty::list(v), m),
                    _ => {
                        let p = self.build(Ty::pair(k, v), m)?;
                        self.build(Ty::list(p), m)
                    }
                }
            }
            _ => unreachable!("unknown builtin {name}"),
        }
    }
}

/// v1.10：型に現れる型引数の名前（現れる順、重複なし）。
pub fn collect_params(t: &Ty) -> Vec<String> {
    fn go(t: &Ty, out: &mut Vec<String>) {
        if !t.has_params() {
            return;
        }
        if let Some(n) = t.param_name() {
            if !out.iter().any(|m| m == n) {
                out.push(n.to_string());
            }
            return;
        }
        for a in t.args() {
            go(a, out);
        }
    }
    let mut out = vec![];
    go(t, &mut out);
    out
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
    /// v1.5：`map` などの型（型検査まで進んだときだけ）
    pub hof: HofTypes,
    /// v1.10：総称の関数の呼び出しの型引数（型検査まで進んだときだけ）
    pub inst: Instances,
    /// v1.12：試験用の論理 trace（`CheckOptions::trace` のときだけ）と、比較 cache の再生回数
    pub trace: Option<Vec<(&'static str, usize)>>,
    pub sharing_hits: u64,
}

pub fn check_program(prog: &Program, eof: usize, profile: &StaticProfile) -> CheckOutcome {
    check_program_with(prog, eof, profile, &CheckOptions::default())
}

/// v1.12：`check_program` と同じ検査を、比較 cache の切替と論理 trace の有無を選んで行う。
pub fn check_program_with(prog: &Program, eof: usize, profile: &StaticProfile, opts: &CheckOptions) -> CheckOutcome {
    check_scoped(prog, eof, profile, opts, None)
}

/// 規則 G（§18.1c）の第二パスの設定。
pub struct SecondPass {
    /// 数える関数の名前（単相化で作った複製）
    pub counted: HashSet<String>,
    /// 第一パスの仕事量の総計。第二パスはここから数え、上限は第一パスと第二パスの和に対して検査する。
    pub start: WorkCounter,
}

/// 規則 G（§18.1c）：単相化の後の第二パス。全関数を検査するが（`hof`・`inst` の表を作るため）、数えるのは
/// `pass.counted` の関数だけである。非総称の関数は第一パスで数えたので、ここでは数え直さない。
pub fn check_program_second(prog: &Program, eof: usize, profile: &StaticProfile, opts: &CheckOptions, pass: &SecondPass) -> CheckOutcome {
    check_scoped(prog, eof, profile, opts, Some(pass))
}

fn check_scoped(prog: &Program, eof: usize, profile: &StaticProfile, opts: &CheckOptions, pass: Option<&SecondPass>) -> CheckOutcome {
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
    tc.configure(*opts);
    if let Some(p) = pass {
        tc.work = p.start;
    }
    for f in &fns {
        tc.counting = pass.is_none_or(|p| p.counted.contains(&f.name));
        if let Err(cutoff) = tc.check_function(f) {
            out.work = Some(tc.work);
            out.trace = tc.trace.take();
            out.sharing_hits = tc.sharing_hits;
            out.diagnostics.append(&mut tc.diags);
            out.diagnostics.push(cutoff);
            return out;
        }
    }
    out.work = Some(tc.work);
    out.trace = tc.trace.take();
    out.sharing_hits = tc.sharing_hits;
    out.diagnostics.append(&mut tc.diags);
    out.hof = std::mem::take(&mut tc.hof);
    out.inst = std::mem::take(&mut tc.inst);

    // entry
    let mut entry_ok = false;
    if entries.is_empty() {
        out.diagnostics.push(Diagnostic::error("entry", "E-ENTRY-MISSING", (eof, eof)));
    } else if entries.len() >= 2 {
        let d = entries[1];
        out.diagnostics.push(Diagnostic::error("entry", "E-ENTRY-DUPLICATE", d.meta.span()).at(d.meta.index));
    } else {
        let d = entries[0];
        let ef = fn_map[d.name.as_str()];
        let n = ef.params.len();
        if !ef.type_params.is_empty() {
            // v1.10：entry の関数は総称にできない（入出力の型が一つに決まらない）
            let names: Vec<&str> = ef.type_params.iter().map(|p| p.name.as_str()).collect();
            let at = ef.meta.span().0;
            out.diagnostics.push(
                Diagnostic::error("entry", "E-ENTRY-GENERIC", d.name_span.t())
                    .exp("function without type parameters")
                    .act(format!("{}<{}>", ef.name, names.join(", ")))
                    .at(d.meta.index)
                    .fix(
                        "insert_text",
                        (at, at),
                        format!(
                            "a non-generic wrapper with concrete types, e.g. fn main(x: List<Int>) -> Int = {}(x), and name it in entry instead (entry main)",
                            ef.name
                        ),
                    ),
            );
        } else if n != 1 {
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
            // v1.10：構築子のために作った関数は使われなくても警告しない（生成したもの）
            if !live.contains(f.name.as_str()) && f.ctor.is_none() {
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

impl TypedProgram {
    /// v1.7：停止が保証されるか（`rec` の印のある関数がないとき。あれば止まらない再帰は資源上限で打ち切る）。
    pub fn terminates(&self) -> bool {
        !self.program.has_rec()
    }
    /// v1.7：`rec` の印のある関数の名前（宣言順）。
    pub fn rec_functions(&self) -> Vec<&str> {
        self.program.functions().filter(|f| f.rec).map(|f| f.name.as_str()).collect()
    }
}
