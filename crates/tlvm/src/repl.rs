//! v1.12：対話的な評価環境 `tlvm repl`（検証されていない front-end。判定と実行は今までの経路が行う）。
//!
//! セッションは宣言（`fn`・`rec fn`・`type`）と `import` の列を持つ。入力が宣言なら、セッションに加えたプログラムを検査し、
//! 受理されたときだけ加える（拒否なら元のセッションを残す）。同じ名前の宣言は置き換える。入力が式なら、
//! `fn __repl_main(__repl_unit: Unit) -> T = <式>` と `entry __repl_main` をセッションの宣言の後に付けたプログラムを作り、
//! 今までの `compile` と `run`（`tlvm run` と同じ静的・実行プロファイル）で検査・実行して `値 : 型` を出す（値は plain JSON）。
//!
//! 式の型 `T` は、まず `-> Unit` で検査し、`E-TYPE-RETURN` の actual（本体の型）を戻り型にして検査し直して決める。
//! 本体がレコードの構築 `P { ... }` なら、先に `-> P` を試す（レコードの構築の型は構造の型 `Pair<...>` と表示されるため）。
//!
//! 出力はすべて標準出力に書く（診断は `--human` と同じ形）。標準入力が端末のときだけ prompt（`> `、続きの行は `. `）を出す。

use crate::api::{compile, parse_source, run, CompileResult, Parsed, SourceCompile};
use crate::checker::TypedProgram;
use crate::diagnostics::{render_human, Diagnostic};
use crate::evaluator::RunResult;
use crate::imports;
use crate::plain::encode_plain;
use crate::profiles::{ExecutionProfile, HostPolicy, InputProfile, StaticProfile};
use crate::syntax::{Decl, ExprKind, Program, Ty};
use crate::values::{decode_input, DecodeResult, TypedValue};
use std::io::{BufRead, Write};

const MAIN: &str = "__repl_main";
const ARG: &str = "__repl_unit";
const ROOT: &str = "<repl>";

/// セッションの一つの要素（import の行か、一つの宣言の source）。
#[derive(Clone, Debug)]
struct Chunk {
    import: bool,
    /// 宣言する名前（関数・型・構築子）。import は空
    names: Vec<String>,
    text: String,
}

/// 検査に渡す source の一部が、どの表示用の source のどこから来たか。
struct Region {
    start: usize,
    len: usize,
    label: String,
    /// 診断を表示する source
    text: String,
    /// `text` の中での開始位置
    origin: usize,
}

struct Built {
    source: String,
    regions: Vec<Region>,
    /// 式の本体の位置（つないだ source 上）
    body: Option<(usize, usize)>,
}

/// 追加する chunk と、その表示用の位置（ラベル、source、source の中の位置）。
struct New {
    chunk: Chunk,
    label: String,
    text: String,
    origin: usize,
}

#[derive(Default)]
pub struct Session {
    chunks: Vec<Chunk>,
}

/// 式を検査した結果。
enum Typed {
    Ok(Box<TypedProgram>),
    Err(Vec<String>),
}

fn declared(p: &Program) -> Vec<String> {
    let mut v = vec![];
    for d in &p.declarations {
        match d {
            Decl::Fn(f) => v.push(f.name.clone()),
            Decl::Type(t) => v.push(t.name.clone()),
            Decl::Sum(t) => {
                v.push(t.name.clone());
                v.extend(t.variants.iter().map(|c| c.name.clone()));
            }
            Decl::Entry(_) => {}
        }
    }
    v
}

/// 宣言の source 上の範囲（`rec fn` は `rec` から）。
fn decl_span(d: &Decl) -> (usize, usize) {
    match d {
        Decl::Fn(f) if f.rec => (f.rec_span.0, f.meta.span().1),
        Decl::Fn(f) => f.meta.span(),
        Decl::Type(t) => t.meta.span(),
        Decl::Sum(t) => t.meta.span(),
        Decl::Entry(e) => e.meta.span(),
    }
}

impl Session {
    pub fn new() -> Session {
        Session::default()
    }

    /// 宣言と import の source（`:list`）。
    pub fn listing(&self) -> Vec<String> {
        let imports = self.chunks.iter().filter(|c| c.import);
        imports.chain(self.chunks.iter().filter(|c| !c.import)).map(|c| c.text.clone()).collect()
    }

    fn build(&self, chunks: &[Chunk], news: &[New], tail: Option<(&str, &str, &str)>) -> Built {
        let mut source = String::new();
        let mut regions = vec![];
        // import はファイルの先頭に置く
        let mut items: Vec<(&Chunk, Option<&New>)> = chunks.iter().map(|c| (c, None)).collect();
        items.extend(news.iter().map(|n| (&n.chunk, Some(n))));
        items.sort_by_key(|(c, _)| !c.import);
        for (c, n) in items {
            let (label, text, origin) = match n {
                Some(n) => (n.label.clone(), n.text.clone(), n.origin),
                None => ("<session>".to_string(), c.text.clone(), 0),
            };
            regions.push(Region { start: source.len(), len: c.text.len(), label, text, origin });
            source.push_str(&c.text);
            source.push('\n');
        }
        let mut body = None;
        match tail {
            // 式は source の最後に置く（EOF の位置の診断も式の終わりとして示せる）
            Some((ty, label, expr)) => {
                source.push_str(&format!("entry {MAIN}\nfn {MAIN}({ARG}: Unit) -> {ty} =\n"));
                let start = source.len();
                regions.push(Region { start, len: expr.len(), label: label.to_string(), text: expr.to_string(), origin: 0 });
                source.push_str(expr);
                body = Some((start, source.len()));
            }
            None => source.push_str(&format!("fn {MAIN}({ARG}: Unit) -> Unit = unit\nentry {MAIN}\n")),
        }
        Built { source, regions, body }
    }

    /// 診断を表示用の形にする（source の一部から来たものはその source の位置で示す）。
    fn render(b: &Built, files: &[(String, Vec<u8>)], d: &Diagnostic) -> String {
        if let Some(f) = d.file.as_deref().filter(|f| *f != ROOT) {
            if let Some((_, src)) = files.iter().find(|(n, _)| n == f) {
                return render_human(d, f, src);
            }
        }
        let s = d.span.0;
        for r in &b.regions {
            if s >= r.start && s <= r.start + r.len {
                let shift = |x: usize| x.saturating_sub(r.start).min(r.len) + r.origin;
                let mut d = d.clone();
                d.span = (shift(d.span.0), shift(d.span.1.max(d.span.0)));
                if let Some(rep) = d.repair.as_mut() {
                    rep.target_span = (shift(rep.target_span.0), shift(rep.target_span.1.max(rep.target_span.0)));
                }
                return render_human(&d, &r.label, r.text.as_bytes());
            }
        }
        render_human(d, ROOT, b.source.as_bytes())
    }

    fn compile(b: &Built) -> (SourceCompile, Vec<(String, Vec<u8>)>) {
        let sp = StaticProfile::default();
        // import はカレントディレクトリから解決する
        let mut loader = imports::FsLoader::new("./__repl__.tlvm");
        imports::compile_root(ROOT, "__repl__.tlvm", b.source.as_bytes(), &mut loader, &sp)
    }

    fn errors(b: &Built, r: &SourceCompile, files: &[(String, Vec<u8>)]) -> Vec<String> {
        match r {
            SourceCompile::SourceBoundaryFailure => vec!["error: an imported file is not valid UTF-8 (SourceBoundaryFailure)".into()],
            SourceCompile::Result(r) => r.errors().iter().map(|d| Self::render(b, files, d)).collect(),
        }
    }

    /// 宣言を加えたプログラムを検査し、受理なら加える。返すのは表示する行。
    fn commit(&mut self, news: Vec<New>) -> Result<Vec<String>, Vec<String>> {
        let new_names: Vec<&String> = news.iter().flat_map(|n| n.chunk.names.iter()).collect();
        let new_imports: Vec<&str> = news.iter().filter(|n| n.chunk.import).map(|n| n.chunk.text.as_str()).collect();
        let mut replaced = vec![];
        let kept: Vec<Chunk> = self
            .chunks
            .iter()
            .filter(|c| {
                let clash = c.names.iter().any(|n| new_names.contains(&n)) || (c.import && new_imports.contains(&c.text.as_str()));
                if clash && !c.import {
                    replaced.push(c.names.first().cloned().unwrap_or_default());
                }
                !clash
            })
            .cloned()
            .collect();
        let b = self.build(&kept, &news, None);
        let (r, files) = Self::compile(&b);
        match &r {
            SourceCompile::Result(CompileResult::Accepted { .. }) => {}
            _ => return Err(Self::errors(&b, &r, &files)),
        }
        let mut out = vec![];
        for n in &news {
            if n.chunk.import {
                out.push(format!("imported {}", n.chunk.text.trim_start_matches("import").trim()));
            } else if let Some(name) = n.chunk.names.first() {
                if replaced.contains(name) {
                    out.push(format!("redefined {name}"));
                } else {
                    out.push(format!("defined {name}"));
                }
            }
        }
        self.chunks = kept;
        self.chunks.extend(news.into_iter().map(|n| n.chunk));
        Ok(out)
    }

    /// source（宣言と import の列）を chunk に分ける。entry は `ignore_entry` なら無視し、そうでなければ誤りにする。
    /// `rebase` があれば import のパスをそのディレクトリからのパスに直す（`:load`）。
    fn split(text: &str, label: &str, rebase: Option<&str>, ignore_entry: bool) -> Result<Vec<New>, Vec<String>> {
        let sp = StaticProfile::default();
        let p = match parse_source(text.as_bytes(), &sp) {
            Parsed::Program(p) => p,
            Parsed::Failed(_) => {
                // 修復ヒントと照合を含む今までの診断で示す
                return Err(match compile(text.as_bytes(), &sp) {
                    SourceCompile::Result(r) => r.errors().iter().map(|d| render_human(d, label, text.as_bytes())).collect(),
                    SourceCompile::SourceBoundaryFailure => vec!["error: input is not valid UTF-8".into()],
                });
            }
        };
        let mut news = vec![];
        for i in &p.imports {
            let path = match rebase {
                Some(dir) => match imports::join(dir, &i.path) {
                    Ok(p) => p,
                    Err(why) => return Err(vec![format!("{label}: import \"{}\": {why}", i.path)]),
                },
                None => i.path.clone(),
            };
            let (s, e) = i.span.t();
            let line = if rebase.is_some() { format!("import {}", crate::diagnostics::json_string(&path)) } else { text[s..e].trim_end().to_string() };
            news.push(New { chunk: Chunk { import: true, names: vec![], text: line }, label: label.into(), text: text.into(), origin: s });
        }
        for d in &p.declarations {
            if let Decl::Entry(e) = d {
                if ignore_entry {
                    continue;
                }
                let (line, col) = crate::diagnostics::line_col(text.as_bytes(), e.meta.span().0);
                return Err(vec![format!("{label}:{line}:{col}: error: the REPL has no entry; type an expression to evaluate it")]);
            }
            let (s, e) = decl_span(d);
            let one = Program { declarations: vec![d.clone()], meta: p.meta, imports: vec![] };
            news.push(New {
                chunk: Chunk { import: false, names: declared(&one), text: text[s..e].to_string() },
                label: label.into(),
                text: text.into(),
                origin: s,
            });
        }
        Ok(news)
    }

    /// 宣言の入力を加える。
    pub fn declare(&mut self, input: &str) -> Result<Vec<String>, Vec<String>> {
        let news = Self::split(input, "<input>", None, false)?;
        if news.is_empty() {
            return Ok(vec![]);
        }
        self.commit(news)
    }

    /// ファイルの宣言と import を加える（entry は無視する。import のパスはカレントディレクトリからのパスに直す）。
    pub fn load(&mut self, path: &str) -> Result<Vec<String>, Vec<String>> {
        let text = match std::fs::read(path) {
            Ok(b) => match String::from_utf8(b) {
                Ok(t) => t,
                Err(_) => return Err(vec![format!("error: {path}: not valid UTF-8 (SourceBoundaryFailure)")]),
            },
            Err(e) => return Err(vec![format!("error: {path}: {e}")]),
        };
        let dir = std::path::Path::new(path).parent().map(|d| d.to_string_lossy().replace('\\', "/")).unwrap_or_default();
        let dir = dir.trim_start_matches("./").to_string();
        let news = Self::split(&text, path, Some(&dir), true)?;
        let n = news.iter().filter(|n| !n.chunk.import).count();
        let mut out = self.commit(news)?;
        out.push(format!("loaded {n} declaration(s) from {path}"));
        Ok(out)
    }

    fn probe(&self, expr: &str, ty: &str) -> (Built, SourceCompile, Vec<(String, Vec<u8>)>) {
        let b = self.build(&self.chunks, &[], Some((ty, "<input>", expr)));
        let (r, files) = Self::compile(&b);
        (b, r, files)
    }

    /// 式を検査する（戻り型を推論する）。
    fn typed(&self, expr: &str) -> Typed {
        let (b, r, files) = self.probe(expr, "Unit");
        let errors = match r {
            SourceCompile::Result(CompileResult::Accepted { program, .. }) => return Typed::Ok(Box::new(program)),
            SourceCompile::Result(CompileResult::Rejected { errors, .. }) => errors,
            f => return Typed::Err(Self::errors(&b, &f, &files)),
        };
        let (body_s, body_e) = b.body.unwrap_or_default();
        let is_ret = |d: &Diagnostic| d.code == "E-TYPE-RETURN" && d.span.0 >= body_s && d.span.0 <= body_e && d.file.as_deref().is_none_or(|f| f == ROOT);
        let others: Vec<String> = errors.iter().filter(|d| !is_ret(d)).map(|d| Self::render(&b, &files, d)).collect();
        if !others.is_empty() {
            return Typed::Err(others);
        }
        let Some(actual) = errors.iter().find(|d| is_ret(d)).and_then(|d| d.actual.clone()) else {
            return Typed::Err(errors.iter().map(|d| Self::render(&b, &files, d)).collect());
        };
        let mut candidates = vec![];
        // レコードの構築なら、その型の名前で（値を field 名つきで表示するため）
        if let Parsed::Program(p) = parse_source(b.source.as_bytes(), &StaticProfile::default()) {
            if let Some(f) = p.functions().find(|f| f.name == MAIN) {
                if let ExprKind::Record { name, .. } = &f.body.kind {
                    candidates.push(name.clone());
                }
            }
        }
        candidates.push(actual);
        let mut last = vec![];
        for ty in candidates {
            let (b, r, files) = self.probe(expr, &ty);
            match r {
                SourceCompile::Result(CompileResult::Accepted { program, .. }) => return Typed::Ok(Box::new(program)),
                r => last = Self::errors(&b, &r, &files),
            }
        }
        Typed::Err(last)
    }

    /// `:type`：式の型。
    pub fn type_of(&self, expr: &str) -> Result<String, Vec<String>> {
        match self.typed(expr) {
            Typed::Ok(p) => Ok(p.output_type.to_string()),
            Typed::Err(e) => Err(e),
        }
    }

    /// 式を評価して `値 : 型` を返す。
    pub fn eval(&self, expr: &str) -> Result<String, Vec<String>> {
        let p = match self.typed(expr) {
            Typed::Ok(p) => p,
            Typed::Err(e) => return Err(e),
        };
        let tv: TypedValue = match decode_input(&Ty::unit(), br#"{"tag":"unit"}"#, &InputProfile::default()) {
            DecodeResult::Decoded(tv) => tv,
            _ => return Err(vec!["error: InternalFault unit-input".into()]),
        };
        match run(&p, &tv, &ExecutionProfile::default(), &HostPolicy::default()) {
            Ok(RunResult::Completed { output, .. }) => match encode_plain(&p.output_type, &output) {
                Ok(v) => Ok(format!("{v} : {}", p.output_type)),
                Err(e) => Err(vec![format!("error: InternalFault {e}")]),
            },
            Ok(RunResult::ResourceExhausted { kind, observed, limit }) => {
                Err(vec![format!("error: ResourceExhausted {kind} (observed {observed}, limit {limit})")])
            }
            Ok(RunResult::HostAborted(r)) => Err(vec![format!("error: HostAborted {r}")]),
            Ok(RunResult::InternalFault(r)) => Err(vec![format!("error: InternalFault {r}")]),
            Err(e) => Err(vec![format!("error: InternalFault {e}")]),
        }
    }

    pub fn reset(&mut self) {
        self.chunks.clear();
    }
}

/// 入力が宣言（`fn`、`rec fn`、`type`、`import "..."`、`entry`）で始まるか。
pub fn is_declaration(input: &str) -> bool {
    let t = strip_comments_ws(input);
    let word = |s: &str| -> (String, String) {
        let w: String = s.chars().take_while(|c| c.is_ascii_alphanumeric() || *c == '_').collect();
        let rest = s[w.len()..].to_string();
        (w, rest)
    };
    let (w, rest) = word(&t);
    let rest_t = rest.trim_start();
    match w.as_str() {
        "fn" | "entry" => rest.starts_with(char::is_whitespace),
        "rec" => word(rest_t).0 == "fn",
        "type" => rest.starts_with(char::is_whitespace) && rest_t.starts_with(|c: char| c.is_ascii_alphabetic()),
        "import" => rest_t.starts_with('"'),
        _ => false,
    }
}

/// 先頭の空白と行コメントを除く。
fn strip_comments_ws(s: &str) -> String {
    let mut t = s.trim_start();
    while let Some(r) = t.strip_prefix("//") {
        t = r.split_once('\n').map_or("", |(_, r)| r).trim_start();
    }
    t.to_string()
}

/// 入力が続くか（括弧が閉じていない、行末が `=`・`->`・`,`・`in` など）。
pub fn needs_more(input: &str) -> bool {
    let mut depth: i64 = 0;
    let mut chars = input.chars().peekable();
    let mut last_code_line = String::new();
    let mut line = String::new();
    while let Some(c) = chars.next() {
        match c {
            '"' | '\'' => {
                line.push(c);
                while let Some(d) = chars.next() {
                    line.push(d);
                    if d == '\\' {
                        if let Some(e) = chars.next() {
                            line.push(e);
                        }
                    } else if d == c || d == '\n' {
                        break;
                    }
                }
            }
            '/' if chars.peek() == Some(&'/') => {
                while chars.peek().is_some_and(|d| *d != '\n') {
                    chars.next();
                }
            }
            '(' | '[' | '{' => {
                depth += 1;
                line.push(c);
            }
            ')' | ']' | '}' => {
                depth -= 1;
                line.push(c);
            }
            '\n' => {
                if !line.trim().is_empty() {
                    last_code_line = std::mem::take(&mut line);
                }
                line.clear();
            }
            c => line.push(c),
        }
    }
    if !line.trim().is_empty() {
        last_code_line = line;
    }
    let l = last_code_line.trim_end();
    depth > 0
        || l.ends_with('=')
        || l.ends_with("->")
        || l.ends_with(',')
        || l.ends_with('|')
        || l.ends_with(" in")
        || l.ends_with(" =>")
}

pub const HELP: &str = "\
Enter a declaration (fn, rec fn, type, import \"path.tlvm\") to add it to the session,
or an expression to evaluate it (prints `value : Type`, the value in plain JSON).
Input continues on the next line while brackets are open or the line ends with = -> , | in.
Commands:
  :type EXPR   show the type of EXPR
  :list        show the declarations of the session
  :reset       remove all declarations
  :load FILE   add the declarations and imports of FILE (its entry is ignored)
  :help        show this help
  :quit        leave the REPL (end of input also leaves)";

/// 一つの入力を処理する。`None` なら終わる。
pub fn handle(session: &mut Session, input: &str) -> Option<Vec<String>> {
    let t = input.trim();
    let lines = |r: Result<Vec<String>, Vec<String>>| match r {
        Ok(v) | Err(v) => v,
    };
    if let Some(cmd) = t.strip_prefix(':') {
        let (name, arg) = cmd.split_once(char::is_whitespace).map_or((cmd, ""), |(n, a)| (n, a.trim()));
        return Some(match name {
            "q" | "quit" => return None,
            "h" | "help" | "?" => vec![HELP.to_string()],
            "t" | "type" if !arg.is_empty() => lines(session.type_of(arg).map(|t| vec![t])),
            "l" | "list" => {
                let l = session.listing();
                if l.is_empty() {
                    vec!["(no declarations)".into()]
                } else {
                    l
                }
            }
            "r" | "reset" => {
                session.reset();
                vec!["session cleared".into()]
            }
            "load" if !arg.is_empty() => lines(session.load(arg)),
            "t" | "type" | "load" => vec![format!("usage: :{name} {}", if name == "load" { "FILE" } else { "EXPR" })],
            _ => vec![format!("unknown command :{name} (see :help)")],
        });
    }
    if t.is_empty() {
        return Some(vec![]);
    }
    Some(if is_declaration(t) { lines(session.declare(t)) } else { lines(session.eval(t).map(|v| vec![v])) })
}

/// REPL の本体。`file` があれば最初に読む（読めなければ診断を出して終了コード 1）。
pub fn repl(file: Option<&str>, input: &mut dyn BufRead, out: &mut dyn Write, prompt: bool) -> std::io::Result<i32> {
    let mut session = Session::new();
    if let Some(f) = file {
        match session.load(f) {
            Ok(v) => {
                for l in v {
                    writeln!(out, "{l}")?;
                }
            }
            Err(v) => {
                for l in v {
                    writeln!(out, "{l}")?;
                }
                return Ok(1);
            }
        }
    }
    let mut buf = String::new();
    loop {
        if prompt {
            write!(out, "{}", if buf.is_empty() { "> " } else { ". " })?;
            out.flush()?;
        }
        let mut line = String::new();
        let eof = input.read_line(&mut line)? == 0;
        if !eof {
            buf.push_str(&line);
            if !buf.trim_start().starts_with(':') && needs_more(&buf) {
                continue;
            }
        }
        if !buf.trim().is_empty() {
            match handle(&mut session, &buf) {
                Some(v) => {
                    for l in v {
                        writeln!(out, "{l}")?;
                    }
                }
                None => return Ok(0),
            }
        }
        buf.clear();
        out.flush()?;
        if eof {
            if prompt {
                writeln!(out)?;
            }
            return Ok(0);
        }
    }
}
