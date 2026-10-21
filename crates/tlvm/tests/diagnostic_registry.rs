//! 診断の版付き registry（`knowledge/diagnostics/registry-v1.json`）と処理系の照合（G0）。
//!
//! 検査する内容：
//! - registry の形：版、code の一意性と整列、各 code の severity・phase・message_template・repair・発生箇所
//! - 発生箇所（`emitted_by` と repair の `source`）が実在する行を指すこと。その行に code の文字列か、その code を
//!   値に持つ const の名前がある
//! - ソースに書かれた `"E-…"`・`"W-…"` の文字列がすべて registry に載っていること
//! - message_template と repair の constraint の固定の文字列が、処理系のソースに書かれていること
//! - 下の fixture 表の診断：code が registry にあり、severity と phase が一致し、message が message_template と
//!   一致し（E-CYCLE-CALL だけは前方一致で、implementation_note に理由がある）、repair の kind が registry の規則の
//!   どれかと一致すること（constraint は placeholder のない規則では完全一致。param_note の続きだけは許す）
//! - 各 code は fixture のどれかで発生するか、発生しない理由 `unreached` を持つこと
//!
//! registry は外部の crate を使わず、この file の中の小さな JSON 読み取りで読む。

use std::collections::{BTreeMap, BTreeSet};
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicUsize, Ordering};

use tlvm::api::{
    compile, compile_ast, compile_files, compile_path, AstCompile, CompileResult, SourceCompile,
};
use tlvm::diagnostics::Diagnostic;
use tlvm::embed::{Limits, Program, RunError};
use tlvm::profiles::{AstTransportProfile, InputProfile, StaticProfile};
use tlvm::syntax::Ty;

// ---------------------------------------------------------------- JSON の読み取り（外部 crate なし）

#[derive(Debug)]
enum J {
    Null,
    Bool,
    Int(i64),
    Str(String),
    Arr(Vec<J>),
    Obj(Vec<(String, J)>),
}

struct Reader {
    c: Vec<char>,
    i: usize,
}

impl Reader {
    fn ws(&mut self) {
        while self.i < self.c.len() && matches!(self.c[self.i], ' ' | '\t' | '\n' | '\r') {
            self.i += 1;
        }
    }

    fn peek(&mut self) -> Option<char> {
        self.ws();
        self.c.get(self.i).copied()
    }

    fn eat(&mut self, want: char) {
        assert_eq!(
            self.peek(),
            Some(want),
            "expected {want:?} at char {}",
            self.i
        );
        self.i += 1;
    }

    fn word(&mut self, w: &str) {
        let got: String = self.c[self.i..].iter().take(w.chars().count()).collect();
        assert_eq!(got, w, "at char {}", self.i);
        self.i += w.chars().count();
    }

    fn hex4(&mut self) -> u32 {
        let h: String = self.c[self.i..self.i + 4].iter().collect();
        self.i += 4;
        u32::from_str_radix(&h, 16).expect("hex escape")
    }

    fn string(&mut self) -> String {
        self.eat('"');
        let mut out = String::new();
        loop {
            let ch = self.c[self.i];
            self.i += 1;
            match ch {
                '"' => return out,
                '\\' => {
                    let e = self.c[self.i];
                    self.i += 1;
                    match e {
                        '"' | '\\' | '/' => out.push(e),
                        'n' => out.push('\n'),
                        't' => out.push('\t'),
                        'r' => out.push('\r'),
                        'b' => out.push('\u{8}'),
                        'f' => out.push('\u{c}'),
                        'u' => {
                            let hi = self.hex4();
                            if (0xD800..0xDC00).contains(&hi) {
                                self.word("\\u");
                                let lo = self.hex4();
                                let cp = 0x10000 + ((hi - 0xD800) << 10) + (lo - 0xDC00);
                                out.push(char::from_u32(cp).expect("surrogate pair"));
                            } else {
                                out.push(char::from_u32(hi).expect("scalar"));
                            }
                        }
                        other => panic!("bad escape \\{other}"),
                    }
                }
                c => out.push(c),
            }
        }
    }

    fn value(&mut self) -> J {
        match self.peek() {
            Some('{') => {
                self.eat('{');
                let mut m: Vec<(String, J)> = Vec::new();
                if self.peek() == Some('}') {
                    self.eat('}');
                    return J::Obj(m);
                }
                loop {
                    self.ws();
                    let k = self.string();
                    assert!(!m.iter().any(|(x, _)| *x == k), "duplicate key {k}");
                    self.eat(':');
                    let v = self.value();
                    m.push((k, v));
                    match self.peek() {
                        Some(',') => self.eat(','),
                        _ => {
                            self.eat('}');
                            return J::Obj(m);
                        }
                    }
                }
            }
            Some('[') => {
                self.eat('[');
                let mut v = Vec::new();
                if self.peek() == Some(']') {
                    self.eat(']');
                    return J::Arr(v);
                }
                loop {
                    v.push(self.value());
                    match self.peek() {
                        Some(',') => self.eat(','),
                        _ => {
                            self.eat(']');
                            return J::Arr(v);
                        }
                    }
                }
            }
            Some('"') => J::Str(self.string()),
            Some('t') => {
                self.word("true");
                J::Bool
            }
            Some('f') => {
                self.word("false");
                J::Bool
            }
            Some('n') => {
                self.word("null");
                J::Null
            }
            Some(c) if c == '-' || c.is_ascii_digit() => {
                let start = self.i;
                self.i += 1;
                while self.i < self.c.len() && self.c[self.i].is_ascii_digit() {
                    self.i += 1;
                }
                let t: String = self.c[start..self.i].iter().collect();
                J::Int(t.parse().expect("integer"))
            }
            other => panic!("unexpected {other:?} at char {}", self.i),
        }
    }
}

fn parse_json(text: &str) -> J {
    let mut r = Reader {
        c: text.chars().collect(),
        i: 0,
    };
    let v = r.value();
    assert!(r.peek().is_none(), "trailing text after the JSON value");
    v
}

fn field<'a>(o: &'a J, k: &str) -> Option<&'a J> {
    match o {
        J::Obj(m) => m.iter().find(|(x, _)| x == k).map(|(_, v)| v),
        _ => panic!("expected an object"),
    }
}

fn text(j: &J) -> &str {
    match j {
        J::Str(s) => s,
        other => panic!("expected a string, got {other:?}"),
    }
}

// ---------------------------------------------------------------- registry の読み込み

struct Rule {
    kind: String,
    constraint: String,
    source: String,
}

struct Entry {
    code: String,
    severity: String,
    phases: Vec<String>,
    template: String,
    /// 空なら repair は null
    rules: Vec<Rule>,
    emitted_by: Vec<String>,
    implementation_note: Option<String>,
    unreached: Option<String>,
}

const REPAIR_KINDS: [&str; 5] = [
    "replace_expression",
    "replace_identifier",
    "replace_type",
    "insert_text",
    "delete_span",
];

/// message の前方一致だけを求める code（implementation_note に理由がある）。
const PREFIX_MATCH: &[&str] = &["E-CYCLE-CALL"];

fn repo_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../..")
}

fn load_registry() -> (String, Vec<Entry>) {
    let path = repo_root().join("knowledge/diagnostics/registry-v1.json");
    let raw = std::fs::read_to_string(&path).unwrap_or_else(|e| panic!("{}: {e}", path.display()));
    let root = parse_json(&raw);
    assert!(
        matches!(field(&root, "registry_version"), Some(J::Int(1))),
        "registry_version must be 1"
    );
    let description = text(field(&root, "description").expect("description")).to_string();
    let codes = match field(&root, "codes") {
        Some(J::Arr(v)) => v,
        _ => panic!("codes must be an array"),
    };
    let mut out = Vec::new();
    for c in codes {
        let phases = match field(c, "phase").expect("phase") {
            J::Str(s) => vec![s.clone()],
            J::Arr(v) => v.iter().map(|x| text(x).to_string()).collect(),
            other => panic!("phase: {other:?}"),
        };
        let rules = match field(c, "repair").expect("repair") {
            J::Null => Vec::new(),
            J::Obj(_) => vec![rule(field(c, "repair").expect("repair"))],
            J::Arr(v) => v.iter().map(rule).collect(),
            other => panic!("repair: {other:?}"),
        };
        let emitted_by = match field(c, "emitted_by").expect("emitted_by") {
            J::Arr(v) => v.iter().map(|x| text(x).to_string()).collect(),
            other => panic!("emitted_by: {other:?}"),
        };
        let opt = |k: &str| match field(c, k) {
            Some(J::Str(s)) => Some(s.clone()),
            Some(J::Null) | None => None,
            Some(other) => panic!("{k}: {other:?}"),
        };
        out.push(Entry {
            code: text(field(c, "code").expect("code")).to_string(),
            severity: text(field(c, "severity").expect("severity")).to_string(),
            phases,
            template: text(field(c, "message_template").expect("message_template")).to_string(),
            rules,
            emitted_by,
            implementation_note: opt("implementation_note"),
            unreached: opt("unreached"),
        });
    }
    (description, out)
}

fn rule(j: &J) -> Rule {
    Rule {
        kind: text(field(j, "kind").expect("kind")).to_string(),
        constraint: text(field(j, "constraint").expect("constraint")).to_string(),
        source: text(field(j, "source").expect("source")).to_string(),
    }
}

// ---------------------------------------------------------------- ソースの走査

fn src_files(dir: &Path, out: &mut Vec<PathBuf>) {
    for e in std::fs::read_dir(dir).expect("read src dir") {
        let p = e.expect("entry").path();
        if p.is_dir() {
            src_files(&p, out);
        } else if p.extension().is_some_and(|x| x == "rs") {
            out.push(p);
        }
    }
}

fn all_sources() -> Vec<(PathBuf, String)> {
    let mut files = Vec::new();
    src_files(
        &Path::new(env!("CARGO_MANIFEST_DIR")).join("src"),
        &mut files,
    );
    files.sort();
    files
        .into_iter()
        .map(|p| {
            let t = std::fs::read_to_string(&p).expect("read source");
            (p, t)
        })
        .collect()
}

/// `"E-…"` や `"W-…"` の文字列リテラル（code の形）を全部集める。
fn code_literals(text: &str) -> BTreeSet<String> {
    let mut out = BTreeSet::new();
    for pat in ["\"E-", "\"W-"] {
        for (idx, _) in text.match_indices(pat) {
            let body = &text[idx + 1..];
            let len = body
                .bytes()
                .take_while(|c| c.is_ascii_uppercase() || c.is_ascii_digit() || *c == b'-')
                .count();
            // `"E-TYPE-"` のような接頭辞の比較は code ではない
            if body.as_bytes().get(len) == Some(&b'"') && !body[..len].ends_with('-') {
                out.insert(body[..len].to_string());
            }
        }
    }
    out
}

/// `const NAME: &str = "CODE";` の名前と値。
fn const_codes(text: &str) -> BTreeMap<String, String> {
    let mut m = BTreeMap::new();
    for line in text.lines() {
        let Some(rest) = line
            .trim_start()
            .strip_prefix("pub const ")
            .or_else(|| line.trim_start().strip_prefix("const "))
        else {
            continue;
        };
        let Some((name, after)) = rest.split_once(':') else {
            continue;
        };
        if let Some(v) = after.split('"').nth(1) {
            if v.starts_with("E-") || v.starts_with("W-") {
                m.insert(name.trim().to_string(), v.to_string());
            }
        }
    }
    m
}

/// `path:line` が実在する行を指し、その行に code か、その code を値に持つ const の名前があること。
/// `need_code` が偽のときは行の内容を問わない（repair の source は規則を書いた行で、文字列は様々なため）。
fn check_site(
    site: &str,
    code: &str,
    consts: &BTreeMap<String, String>,
    need_code: bool,
) -> Result<(), String> {
    let (path, line) = site
        .rsplit_once(':')
        .ok_or_else(|| format!("{site}: not file:line"))?;
    let n: usize = line.parse().map_err(|_| format!("{site}: bad line"))?;
    let file = repo_root().join(path);
    let body = std::fs::read_to_string(&file).map_err(|e| format!("{site}: {e}"))?;
    let lines: Vec<&str> = body.lines().collect();
    if n == 0 || n > lines.len() {
        return Err(format!("{site}: line out of range ({} lines)", lines.len()));
    }
    if !need_code {
        return Ok(());
    }
    let l = lines[n - 1];
    let quoted = format!("\"{code}\"");
    let via_const = consts
        .iter()
        .any(|(name, v)| v.as_str() == code && l.contains(name.as_str()));
    if l.contains(&quoted) || via_const {
        Ok(())
    } else {
        Err(format!("{site}: line does not name {code}: {}", l.trim()))
    }
}

// ---------------------------------------------------------------- fixture の診断

struct Case {
    code: &'static str,
    diags: Vec<Diagnostic>,
}

fn case(code: &'static str, diags: Vec<Diagnostic>) -> Case {
    Case { code, diags }
}

fn sp() -> StaticProfile {
    StaticProfile::default()
}

fn all(r: CompileResult) -> Vec<Diagnostic> {
    let mut v = r.errors().to_vec();
    v.extend(r.warnings().iter().cloned());
    v
}

fn src(text: &str) -> Vec<Diagnostic> {
    src_with(text, &sp())
}

fn src_with(text: &str, p: &StaticProfile) -> Vec<Diagnostic> {
    match compile(text.as_bytes(), p) {
        SourceCompile::Result(r) => all(r),
        SourceCompile::SourceBoundaryFailure => panic!("boundary failure"),
    }
}

fn files_with(fs: &[(&str, &str)], p: &StaticProfile) -> Vec<Diagnostic> {
    let map: BTreeMap<String, String> = fs
        .iter()
        .map(|(k, v)| (k.to_string(), v.to_string()))
        .collect();
    match compile_files(fs[0].0, &map, p) {
        SourceCompile::Result(r) => all(r),
        SourceCompile::SourceBoundaryFailure => panic!("boundary failure"),
    }
}

/// 一時ディレクトリに作ったプロジェクト（根は main.tlvm）を、パスから検査する。
fn project(fs: &[(&str, &str)]) -> Vec<Diagnostic> {
    static N: AtomicUsize = AtomicUsize::new(0);
    let n = N.fetch_add(1, Ordering::Relaxed);
    let dir = PathBuf::from(env!("CARGO_TARGET_TMPDIR"))
        .join(format!("registry-{}-{n}", std::process::id()));
    for (rel, body) in fs {
        let path = dir.join(rel);
        std::fs::create_dir_all(path.parent().expect("parent")).expect("mkdir");
        std::fs::write(&path, body).expect("write");
    }
    let root = dir.join("main.tlvm");
    let r = compile_path(root.to_str().expect("utf-8 path"), &sp());
    let _ = std::fs::remove_dir_all(&dir);
    match r.expect("compile_path").0 {
        SourceCompile::Result(r) => all(r),
        SourceCompile::SourceBoundaryFailure => panic!("boundary failure"),
    }
}

fn input(program: &str, json: &str, ip: InputProfile) -> Vec<Diagnostic> {
    let p = Program::compile(program).unwrap_or_else(|e| panic!("fixture rejected: {e:?}"));
    let limits = Limits {
        input: ip,
        ..Limits::default()
    };
    match p.run_json_with(json, &limits) {
        Err(RunError::Input(ds)) => ds,
        other => panic!("expected an input error, got {other:?}"),
    }
}

fn ast(json: &str, p: &StaticProfile, tp: &AstTransportProfile) -> Vec<Diagnostic> {
    match compile_ast(json.as_bytes(), p, tp) {
        AstCompile::AstInvalid(ds) => ds,
        AstCompile::Result(r) => all(r),
        AstCompile::AstBoundaryFailure => panic!("boundary failure"),
    }
}

const AST_BASE: &str = r#"{"codec":"ast_codec_v1","declarations":[{"tag":"fn","name":"f","params":[{"name":"x","type":{"tag":"int"}}],"return_type":{"tag":"int"},"body":{"tag":"var","name":"x"}},{"tag":"entry","name":"f"}]}"#;

const PKG_APP: &str = r#"{"dependencies":{"stats":{"path":"deps/stats","version":"0.2.0"}}}"#;
const PKG_STATS: &str = r#"{"name":"stats","version":"0.2.0"}"#;
const PKG_MAIN: &str =
    "import \"@stats/lib.tlvm\"\nfn solve(xs: List<Int>) -> Int = total(xs)\nentry solve\n";
const PKG_LIB: &str = "fn total(xs: List<Int>) -> Int = fold(xs, 0, |acc, x| add(acc, x))\n";

fn many_functions(body: &str, n: usize) -> String {
    let mut s = String::new();
    for i in 0..n {
        s += &format!("fn g{i}(x: Int) -> Int = {body}\n");
    }
    s += "fn f(x: Int) -> Int = x\nentry f\n";
    s
}

fn generic_instances() -> String {
    // 型引数の具体化が 256 を超えるように、Int と Bool を List・Option で包んだ 257 個の型で id を呼ぶ
    // （record 型を 256 個以上宣言すると別の上限 E-LIMIT-STATIC-SEMANTIC-TYPE-DEPTH に当たるので使わない）。
    // 各 id の呼出しは g_i に置き、g_i は二分木の子を呼ぶので、すべての複製が使われる。
    let mut types: Vec<(String, String)> = Vec::new();
    for m in 0..9u32 {
        for bits in 0..(1u32 << m) {
            for (base, lit) in [("Int", "1"), ("Bool", "true")] {
                let wraps: Vec<&str> = (0..m)
                    .map(|j| {
                        if (bits >> j) & 1 == 0 {
                            "List"
                        } else {
                            "Option"
                        }
                    })
                    .collect();
                let mut t = base.to_string();
                for w in wraps.iter().rev() {
                    t = format!("{w}<{t}>");
                }
                let e = match wraps.first() {
                    None => lit.to_string(),
                    Some(&outer) => {
                        let inner = &t[outer.len() + 1..t.len() - 1];
                        if outer == "List" {
                            format!("list<{inner}>()")
                        } else {
                            format!("none<{inner}>()")
                        }
                    }
                };
                types.push((t, e));
            }
        }
    }
    types.truncate(257);
    let n = types.len();
    let mut s = String::from("fn id<T>(x: T) -> T = x\n");
    for (i, (_, e)) in types.iter().enumerate() {
        let kids: Vec<usize> = [2 * i + 1, 2 * i + 2]
            .into_iter()
            .filter(|&c| c < n)
            .collect();
        let call = format!("let r = id({e}) in ");
        let body = match kids.as_slice() {
            [] => format!("{call}0"),
            [only] => format!("{call}g{only}(x)"),
            [a, b] => format!("{call}add(g{a}(x), g{b}(x))"),
            _ => unreachable!(),
        };
        s += &format!("fn g{i}(x: Int) -> Int = {body}\n");
    }
    s += "fn f(x: Int) -> Int = g0(x)\nentry f\n";
    s
}

fn cases() -> Vec<Case> {
    let limit = |f: fn(&mut StaticProfile)| {
        let mut p = sp();
        f(&mut p);
        p
    };
    let mut v = vec![
        // ---- lex
        case("E-LEX-INVALID-NUMERIC-BOUNDARY", src("fn f(x: Int) -> Int = 12x entry f\n")),
        case("E-LEX-NON-ASCII", src("fn f(x: Int) -> Int = é entry f\n")),
        case("E-LEX-UNEXPECTED-CHARACTER", src("fn f(x: Int) -> Int = x + 1 entry f\n")),
        case("E-LEX-INVALID-INTEGER", src("fn f(x: Int) -> Int = 01 entry f\n")),
        case("E-LEX-INVALID-ESCAPE", src("fn f(x: Int) -> String = \"a\\q\" entry f\n")),
        case("E-LEX-UNTERMINATED-STRING", src("fn f(x: Int) -> String = \"abc entry f\n")),
        case("E-LEX-INVALID-CHAR-LITERAL", src("fn f(x: Int) -> Char = '' entry f\n")),
        case("E-LEX-CONTROL-CHAR-IN-LITERAL", src("fn f(x: Int) -> String = \"a\tb\" entry f\n")),
        // ---- parse
        case("E-PARSE-UNEXPECTED-TOKEN", src("fn f(x: Int) -> Int = x 1 entry f\n")),
        case("E-PARSE-EXPECTED-TOKEN", src("fn f(x: Int) -> Option<Int> = none[Foo] entry f\n")),
        case("E-PARSE-EXPECTED-TYPE", src("fn f(x: 3) -> Int = 0 entry f\n")),
        case("E-PARSE-EXPECTED-IDENT", src("fn let(x: Int) -> Int = x entry let\n")),
        case("E-PARSE-EXPECTED-EXPR", src("fn f(x: Int) -> Int = ) entry f\n")),
        case("E-PARSE-EXPECTED-PATTERN", src("type S = A | B\nfn f(x: S) -> Int = match x { 1 => 0, _ => 1 } entry f\n")),
        case("E-PARSE-EXPECTED-LAMBDA", src("fn f(x: List<Int>) -> List<Int> = map(x, add) entry f\n")),
        case("E-PARSE-STRING-TYPE", src("fn f(x: List<Char>) -> Int = 0 entry f\n")),
        case("E-PARSE-REC-ENTRY", src("fn f(x: Int) -> Int = x\nrec entry f\n")),
        case("E-PARSE-RECOVERY-LIMIT", src(&format!("{}entry g0\n", (0..12).map(|i| format!("fn g{i}(x: Int) -> Int = x 1\n")).collect::<String>()))),
        case("E-IMPORT-AFTER-DECL", src("fn f(x: Int) -> Int = x\nimport \"a.tlvm\"\nentry f\n")),
        // ---- name, arity, entry, call-graph
        case("E-NAME-UNBOUND-VARIABLE", src("fn f(x: Int) -> Int = y entry f\n")),
        case("E-NAME-UNKNOWN-FUNCTION", src("fn f(x: Int) -> Int = gg(x) entry f\n")),
        case("E-NAME-DUPLICATE-FUNCTION", src("fn f(x: Int) -> Int = x\nfn f(x: Int) -> Int = x\nentry f\n")),
        case("E-NAME-DUPLICATE-PARAM", src("fn f(x: Int, x: Int) -> Int = x entry f\n")),
        case("E-NAME-DUPLICATE-BINDER", src("fn f(xs: List<Int>) -> Int = fold(xs, 0, |x, x| x) entry f\n")),
        case("E-NAME-SHADOW", src("fn f(x: Int) -> Int = let x = 1 in x entry f\n")),
        case("E-ENTRY-UNKNOWN", src("fn f(x: Int) -> Int = x entry g\n")),
        case("E-ENTRY-MISSING", src("fn f(x: Int) -> Int = x\n")),
        case("E-ENTRY-DUPLICATE", src("fn f(x: Int) -> Int = x entry f entry f\n")),
        case("E-ENTRY-ARITY", src("fn f() -> Int = 0 entry f\n")),
        case("E-ENTRY-GENERIC", src("fn f<T>(x: T) -> T = x entry f\n")),
        case("E-CYCLE-CALL", src("fn f(x: Int) -> Int = f(x) entry f\n")),
        case("E-ARITY-USER", src("fn g(y: Int) -> Int = y\nfn f(x: Int) -> Int = g(1, true) entry f\n")),
        case("E-ARITY-BUILTIN", src("fn f(x: Int) -> Int = add(1, true, 0) entry f\n")),
        // ---- typecheck
        case("E-TYPE-RETURN", src("fn f(x: Int) -> Bool = x entry f\n")),
        case("E-TYPE-ARG", src("fn g(y: Int) -> Int = y\nfn f(x: Int) -> Int = g(true) entry f\n")),
        case("E-TYPE-IF-CONDITION", src("fn f(x: Int) -> Int = if(x, 1, 2) entry f\n")),
        case("E-TYPE-IF-BRANCH", src("fn f(x: Int) -> Int = if(true, 1, none<Int>()) entry f\n")),
        case("E-TYPE-FST-ARG", src("fn f(x: Int) -> Int = fst(1) entry f\n")),
        case("E-TYPE-SND-ARG", src("fn f(x: Int) -> Int = snd(1) entry f\n")),
        case("E-TYPE-EQ-OPERANDS", src("fn f(x: Int) -> Bool = eq(1, true) entry f\n")),
        case("E-TYPE-EXPECTED-LIST", src("fn f(x: Int) -> List<Int> = concat(1, list<Int>()) entry f\n")),
        case("E-TYPE-LIST-ITEM", src("fn f(x: Int) -> List<Int> = list<Int>(1, true) entry f\n")),
        case("E-TYPE-FOLD-LIST", src("fn f(n: Int) -> Int = fold(1, 0, |acc, x| acc) entry f\n")),
        case("E-TYPE-FOLD-BODY", src("fn f(n: Int) -> Int = fold(list<Int>(1), 0, |acc, x| true) entry f\n")),
        case("E-TYPE-HOF-LIST", src("fn f(n: Int) -> List<Int> = map(1, |x| x) entry f\n")),
        case("E-TYPE-HOF-BODY", src("fn f(n: Int) -> List<Int> = filter(list<Int>(1), |x| 1) entry f\n")),
        case("E-TYPE-LOOP-MAX", src("fn f(x: Int) -> Option<Int> = loop(0, true, |s| none<Int>()) entry f\n")),
        case("E-TYPE-LOOP-BODY", src("fn f(x: Int) -> Option<Int> = loop(0, 3, |s| some(true)) entry f\n")),
        case("E-TYPE-MATCH-SCRUTINEE", src("fn f(n: Int) -> Int = match_option(1, 0, |x| x) entry f\n")),
        case("E-TYPE-MATCH-BRANCH", src("fn f(n: Int) -> Int = match_option(some(1), 0, |x| true) entry f\n")),
        case("E-TYPE-DICT-ARG", src("fn f(x: Int) -> Int = dict_get(1, 2) entry f\n")),
        case("E-TYPE-DICT-FROM", src("fn f(x: Int) -> Int = dict_from(1) entry f\n")),
        case("E-TYPE-FIELD-ACCESS", src("type P = { a: Int }\nfn f(x: Int) -> Int = x.a entry f\n")),
        case("E-TYPE-GENERIC-ARITY", src("fn id<T>(x: T) -> T = x\nfn f(x: Int) -> Int = id<Int, Int>(x) entry f\n")),
        case("E-TYPE-GENERIC-UNKNOWN-PARAM", src("fn g(x: U) -> Int = 0\nfn f(x: Int) -> Int = g(x) entry f\n")),
        case("E-TYPE-GENERIC-DUPLICATE-PARAM", src("fn g<T, T>(x: T) -> T = x\nfn f(x: Int) -> Int = g(x) entry f\n")),
        case("E-TYPE-GENERIC-PARAM-CONFLICT", src("type T = { a: Int }\nfn g<T>(x: T) -> T = x\nfn f(x: Int) -> Int = x entry f\n")),
        case("E-TYPE-GENERIC-UNUSED-PARAM", src("type Box<T> = { value: Int }\nfn f(x: Int) -> Int = x entry f\n")),
        case("E-TYPE-GENERIC-MISMATCH", src("fn same<T>(a: T, b: T) -> T = a\nfn f(x: Int) -> Int = same(1, true) entry f\n")),
        case("E-TYPE-GENERIC-INFER", src("fn mk<T>() -> List<T> = list<T>()\nfn f(x: Int) -> List<Int> = mk() entry f\n")),
        case("E-TYPE-GENERIC-INFER", src("type Maybe<T> = Nothing | Just(T)\nfn f(x: Int) -> Maybe<Int> = Nothing entry f\n")),
        case("E-TYPE-GENERIC-ARITY", src("type Box<T> = { value: T }\nfn f(x: Box<Int, Int>) -> Int = 0 entry f\n")),
        case("E-TYPE-GENERIC-ARITY", src("fn f<T>(x: T<Int>) -> Int = 0 entry f\n")),
        case("E-TYPE-GENERIC-INFINITE", src("rec fn g<T>(x: T, n: Int) -> Int = if(le(n, 0), 0, g(pair(x, x), sub(n, 1)))\nfn f(x: Int) -> Int = g(x, 3) entry f\n")),
        // ---- records, sums, match, recursive types
        case("E-RECORD-UNKNOWN-TYPE", src("fn f(x: Nope) -> Int = 0 entry f\n")),
        case("E-RECORD-UNKNOWN-FIELD", src("type P = { a: Int }\nfn f(x: Int) -> P = P { b: x } entry f\n")),
        case("E-RECORD-DUPLICATE-FIELD", src("type P = { a: Int }\nfn f(x: Int) -> P = P { a: x, a: x } entry f\n")),
        case("E-RECORD-DUPLICATE-TYPE", src("type P = { a: Int }\ntype P = { b: Int }\nfn f(x: Int) -> Int = x entry f\n")),
        case("E-RECORD-FIELD-CONFLICT", src("type P = { a: Int }\ntype Q = { a: Int }\nfn f(x: Int) -> Int = x entry f\n")),
        case("E-RECORD-MISSING-FIELD", src("type P = { a: Int, b: Int }\nfn f(x: Int) -> P = P { a: x } entry f\n")),
        case("E-RECORD-BASE-REDUNDANT", src("type P = { a: Int, b: Int }\nfn f(x: P) -> P = P { a: 1, b: 2, ..x } entry f\n")),
        case("E-SUM-DUPLICATE-CTOR", src("type S = A | A\nfn f(x: Int) -> Int = x entry f\n")),
        case("E-SUM-NAME-CONFLICT", src("type S = Add | B\nfn Add(x: Int) -> Int = x\nfn f(x: Int) -> Int = x entry f\n")),
        case("E-SUM-UNKNOWN-CTOR", src("type S = A | B\nfn f(x: S) -> Int = match x { A => 0, C => 1 } entry f\n")),
        case("E-SUM-CTOR-ARITY", src("type S = A | B(Int)\nfn f(x: Int) -> S = B(1, 2) entry f\n")),
        case("E-MATCH-MISSING", src("type S = A | B\nfn f(x: S) -> Int = match x { A => 0 } entry f\n")),
        case("E-MATCH-DUPLICATE", src("type S = A | B\nfn f(x: S) -> Int = match x { A => 0, A => 1, B => 2 } entry f\n")),
        case("E-MATCH-UNREACHABLE", src("type S = A | B\nfn f(x: S) -> Int = match x { A => 0, B => 1, _ => 2 } entry f\n")),
        case("E-MATCH-MIXED", src("type S = A | B\nfn f(x: S) -> Int = match x { A => 0, some(y) => 1 } entry f\n")),
        case("E-REC-FIELD-TYPE", src("type T = Leaf | Node(String, T)\nfn f(x: Int) -> Int = x entry f\n")),
        case("E-REC-TYPE-PARAM", src("type T<A> = Leaf | Node(Int, T<A>)\nfn f(x: Int) -> Int = x entry f\n")),
        // ---- warnings
        case("W-UNUSED-FUNCTION", src("fn f(x: Int) -> Int = x\nfn g(y: Int) -> Int = y entry f\n")),
        case("W-DIAG-LIMIT", src(&many_functions("x", 40))),
        case("E-DIAG-LIMIT", src(&many_functions("y", 40))),
        // ---- static limits (source)
        case("E-LIMIT-STATIC-SOURCE-BYTES", src_with("fn f(x: Int) -> Int = x entry f\n", &limit(|p| p.source_bytes = 10))),
        case("E-LIMIT-STATIC-TOKENS", src_with("fn f(x: Int) -> Int = x entry f\n", &limit(|p| p.tokens = 5))),
        case("E-LIMIT-STATIC-INTEGER-DIGITS", src_with("fn f(x: Int) -> Int = 123 entry f\n", &limit(|p| p.integer_digits = 2))),
        case("E-LIMIT-STATIC-FUNCTIONS", src_with("fn g(x: Int) -> Int = x\nfn f(x: Int) -> Int = g(x) entry f\n", &limit(|p| p.functions = 1))),
        case("E-LIMIT-STATIC-AST-NODES", src_with("fn f(x: Int) -> Int = add(x, 1) entry f\n", &limit(|p| p.ast_nodes = 3))),
        case("E-LIMIT-STATIC-TYPE-DEPTH", src_with("fn f(x: List<List<Int>>) -> Int = 0 entry f\n", &limit(|p| p.type_depth = 1))),
        case("E-LIMIT-STATIC-LET-DEPTH", src_with("fn f(x: Int) -> Int = let a = x in let b = a in b entry f\n", &limit(|p| p.let_depth = 1))),
        case("E-LIMIT-STATIC-FOLD-DEPTH", src_with("fn f(n: Int) -> Int = fold(list<Int>(1), 0, |acc, x| fold(list<Int>(2), acc, |a, y| a)) entry f\n", &limit(|p| p.fold_depth = 1))),
        case("E-LIMIT-STATIC-EXPR-DEPTH", src_with("fn f(x: Int) -> Int = add(add(add(x, 1), 1), 1) entry f\n", &limit(|p| p.expr_depth = 2))),
        case("E-LIMIT-STATIC-EXPR-DEPTH", src_with("fn f(n: Int) -> Option<Int> = loop(0, 3, |s| some(add(s, 1))) entry f\n", &limit(|p| p.expr_depth = 5))),
        case("E-LIMIT-STATIC-SEMANTIC-TYPE-DEPTH", src_with("fn f(x: Int) -> Int = fst(pair(1, 2)) entry f\n", &limit(|p| p.semantic_type_depth = 1))),
        case("E-LIMIT-STATIC-SEMANTIC-WORK", src_with("fn f(x: Int) -> Int = add(x, 1) entry f\n", &limit(|p| p.semantic_work = 1))),
        case("E-LIMIT-STATIC-REWRITTEN-BYTES", src_with("fn f(xs: List<Int>) -> List<Int> = map(xs, |x| add(x, 1)) entry f\n", &limit(|p| p.rewritten_bytes = 10))),
        case("E-LIMIT-STATIC-GENERIC-INSTANCES", src(&generic_instances())),
        // ---- imports and packages
        case("E-IMPORT-UNSUPPORTED", src("import \"a.tlvm\"\nfn f(x: Int) -> Int = x entry f\n")),
        case("E-IMPORT-PATH", files_with(&[("main.tlvm", "import \"/abs.tlvm\"\nfn f(x: Int) -> Int = x entry f\n")], &sp())),
        case("E-IMPORT-NOT-FOUND", files_with(&[("main.tlvm", "import \"lib/missing.tlvm\"\nfn f(x: Int) -> Int = x entry f\n")], &sp())),
        case("E-IMPORT-CYCLE", files_with(&[("main.tlvm", "import \"a.tlvm\"\nfn f(x: Int) -> Int = x entry f\n"), ("a.tlvm", "import \"main.tlvm\"\nfn g(x: Int) -> Int = x\n")], &sp())),
        case("E-IMPORT-CONFLICT", files_with(&[("main.tlvm", "import \"a.tlvm\"\nimport \"b.tlvm\"\nfn f(x: Int) -> Int = x entry f\n"), ("a.tlvm", "fn g(x: Int) -> Int = x\n"), ("b.tlvm", "fn g(x: Int) -> Int = x\n")], &sp())),
        case("E-LIMIT-STATIC-IMPORT-FILES", files_with(&[("main.tlvm", "import \"a.tlvm\"\nfn f(x: Int) -> Int = g(x) entry f\n"), ("a.tlvm", "fn g(x: Int) -> Int = x\n")], &limit(|p| p.import_files = 1))),
        case("E-LIMIT-STATIC-SOURCE-BYTES", files_with(&[("main.tlvm", "import \"a.tlvm\"\nfn f(x: Int) -> Int = g(x) entry f\n"), ("a.tlvm", "fn g(x: Int) -> Int = add(x, 1)\nfn h(x: Int) -> Int = add(x, 2)\nfn k(x: Int) -> Int = add(x, 3)\n")], &limit(|p| p.source_bytes = 120))),
        case("E-PKG-MANIFEST", project(&[("tlvm.json", "{broken"), ("main.tlvm", PKG_MAIN), ("deps/stats/tlvm.json", PKG_STATS), ("deps/stats/lib.tlvm", PKG_LIB)])),
        case("E-PKG-PATH", project(&[("tlvm.json", r#"{"dependencies":{"stats":{"path":"/abs/stats","version":"0.2.0"}}}"#), ("main.tlvm", PKG_MAIN), ("deps/stats/tlvm.json", PKG_STATS), ("deps/stats/lib.tlvm", PKG_LIB)])),
        case("E-PKG-NOT-FOUND", project(&[("tlvm.json", PKG_APP), ("main.tlvm", PKG_MAIN), ("deps/stats/lib.tlvm", PKG_LIB)])),
        case("E-PKG-NAME", project(&[("tlvm.json", PKG_APP), ("main.tlvm", PKG_MAIN), ("deps/stats/tlvm.json", r#"{"name":"other","version":"0.2.0"}"#), ("deps/stats/lib.tlvm", PKG_LIB)])),
        case("E-PKG-VERSION", project(&[("tlvm.json", r#"{"dependencies":{"stats":{"path":"deps/stats","version":"0.3.0"}}}"#), ("main.tlvm", PKG_MAIN), ("deps/stats/tlvm.json", PKG_STATS), ("deps/stats/lib.tlvm", PKG_LIB)])),
        case("E-PKG-UNKNOWN", project(&[("main.tlvm", PKG_MAIN), ("deps/stats/tlvm.json", PKG_STATS), ("deps/stats/lib.tlvm", PKG_LIB)])),
    ];
    v.extend(input_and_ast_cases());
    v
}

fn input_and_ast_cases() -> Vec<Case> {
    let int_prog = "fn f(x: Int) -> Int = x entry f\n";
    let rec_prog = "type P = { a: Int }\nfn f(x: P) -> Int = 0 entry f\n";
    let list_prog = "fn f(xs: List<Int>) -> Int = 0 entry f\n";
    let ip = |f: fn(&mut InputProfile)| {
        let mut p = InputProfile::default();
        f(&mut p);
        p
    };
    let tp = |f: fn(&mut AstTransportProfile)| {
        let mut p = AstTransportProfile::default();
        f(&mut p);
        p
    };
    let sp_ = |f: fn(&mut StaticProfile)| {
        let mut p = sp();
        f(&mut p);
        p
    };
    let dflt = InputProfile::default();
    vec![
        // ---- input (plain JSON)
        case("E-INPUT-JSON-SYNTAX", input(int_prog, "[1,", dflt.clone())),
        case("E-INPUT-STRING-SCALAR", input("fn f(x: String) -> Int = 0 entry f\n", r#""\ud800""#, dflt.clone())),
        case("E-INPUT-DUPLICATE-KEY", input(rec_prog, r#"{"a":1,"a":2}"#, dflt.clone())),
        case("E-INPUT-FIELD-TYPE", input(rec_prog, "1", dflt.clone())),
        case("E-INPUT-MISSING-FIELD", input(rec_prog, "{}", dflt.clone())),
        case("E-INPUT-UNKNOWN-FIELD", input(rec_prog, r#"{"a":1,"b":2}"#, dflt.clone())),
        case("E-INPUT-TAG", input("type S = A | B(Int)\nfn f(x: S) -> Int = 0 entry f\n", r#"{"C":1}"#, dflt.clone())),
        case("E-INPUT-INTEGER", input(int_prog, "-0", dflt.clone())),
        case("E-INPUT-DICT-DUPLICATE-KEY", input("fn f(d: Dict<String, Int>) -> Int = fold(dict_values(d), 0, |a, v| add(a, v))\nentry f\n", r#"[["a",1],["a",2]]"#, dflt.clone())),
        case("E-LIMIT-INPUT-JSON-BYTES", input(int_prog, "[1,2]", ip(|p| p.json_bytes = 2))),
        case("E-LIMIT-INPUT-JSON-DEPTH", input(list_prog, "[[1]]", ip(|p| p.json_depth = 1))),
        case("E-LIMIT-INPUT-VALUE-DEPTH", input("fn f(xs: List<List<Int>>) -> Int = 0 entry f\n", "[[1]]", ip(|p| p.value_depth = 1))),
        case("E-LIMIT-INPUT-VALUE-NODES", input(list_prog, "[1,2]", ip(|p| p.value_nodes = 1))),
        case("E-LIMIT-INPUT-INTEGER-DIGITS", input(int_prog, "123", ip(|p| p.integer_digits = 2))),
        // ---- input (value JSON)
        case("E-INPUT-CHAR", match tlvm::api::decode_input(&Ty::char(), br#"{"tag":"char","value":"55296"}"#, &dflt) {
            tlvm::DecodeResult::Invalid(d) => d,
            _ => panic!("expected E-INPUT-CHAR"),
        }),
        // ---- AST transport
        case("E-AST-JSON-SYNTAX", ast("{\"codec\":", &sp(), &AstTransportProfile::default())),
        case("E-AST-LIMIT-JSON-DEPTH", ast(AST_BASE, &sp(), &tp(|p| p.json_depth = 2))),
        case("E-AST-STRING-SCALAR", ast(&AST_BASE.replace("\"name\":\"f\"", "\"name\":\"\\ud800\""), &sp(), &AstTransportProfile::default())),
        case("E-AST-DUPLICATE-KEY", ast(r#"{"codec":"ast_codec_v1","codec":"ast_codec_v1","declarations":[]}"#, &sp(), &AstTransportProfile::default())),
        case("E-AST-LIMIT-BYTES", ast(AST_BASE, &sp(), &tp(|p| p.json_bytes = 10))),
        case("E-AST-CODEC", ast(&AST_BASE.replace("ast_codec_v1", "other"), &sp(), &AstTransportProfile::default())),
        case("E-AST-MISSING-FIELD", ast(r#"{"codec":"ast_codec_v1","declarations":[{"tag":"fn","name":"f","params":[],"return_type":{"tag":"int"}},{"tag":"entry","name":"f"}]}"#, &sp(), &AstTransportProfile::default())),
        case("E-AST-UNKNOWN-FIELD", ast(r#"{"codec":"ast_codec_v1","declarations":[{"tag":"entry","name":"f","extra":1}]}"#, &sp(), &AstTransportProfile::default())),
        case("E-AST-FIELD-TYPE", ast(r#"{"codec":"ast_codec_v1","declarations":[{"tag":"entry","name":1}]}"#, &sp(), &AstTransportProfile::default())),
        case("E-AST-TAG", ast(r#"{"codec":"ast_codec_v1","declarations":[{"tag":"bogus","name":"f"}]}"#, &sp(), &AstTransportProfile::default())),
        case("E-AST-IDENTIFIER", ast(&AST_BASE.replace("\"name\":\"f\",\"params\"", "\"name\":\"let\",\"params\""), &sp(), &AstTransportProfile::default())),
        case("E-AST-INTEGER", ast(&AST_BASE.replace("{\"tag\":\"var\",\"name\":\"x\"}", "{\"tag\":\"int\",\"value\":\"01\"}"), &sp(), &AstTransportProfile::default())),
        case("E-AST-LIMIT-INTEGER-DIGITS", ast(&AST_BASE.replace("{\"tag\":\"var\",\"name\":\"x\"}", "{\"tag\":\"int\",\"value\":\"123\"}"), &sp_(|p| p.integer_digits = 2), &AstTransportProfile::default())),
        case("E-AST-LITERAL", ast(&AST_BASE.replace("{\"tag\":\"var\",\"name\":\"x\"}", "{\"tag\":\"char\",\"value\":\"ab\"}"), &sp(), &AstTransportProfile::default())),
        case("E-AST-STRING-TYPE", ast(&AST_BASE.replace("{\"tag\":\"int\"}}]", "{\"tag\":\"list\",\"element\":{\"tag\":\"char\"}}}]"), &sp(), &AstTransportProfile::default())),
    ]
}

// ---------------------------------------------------------------- 検査

#[test]
fn registry_has_a_version_and_sorted_unique_codes() {
    let (_, entries) = load_registry();
    let codes: Vec<&str> = entries.iter().map(|e| e.code.as_str()).collect();
    let mut sorted = codes.clone();
    sorted.sort();
    sorted.dedup();
    assert_eq!(codes, sorted, "codes must be unique and sorted by code");
    assert!(!codes.is_empty());
}

#[test]
fn registry_entries_have_complete_fields() {
    let (description, entries) = load_registry();
    assert!(!description.is_empty());
    for e in &entries {
        assert!(
            e.code.starts_with("E-") || e.code.starts_with("W-"),
            "{}: code prefix",
            e.code
        );
        assert!(
            matches!(e.severity.as_str(), "error" | "warning"),
            "{}: severity {}",
            e.code,
            e.severity
        );
        assert_eq!(
            e.severity == "warning",
            e.code.starts_with("W-"),
            "{}: severity must follow the code prefix",
            e.code
        );
        assert!(!e.phases.is_empty(), "{}: phase", e.code);
        assert!(!e.emitted_by.is_empty(), "{}: emitted_by", e.code);
        for r in &e.rules {
            assert!(
                REPAIR_KINDS.contains(&r.kind.as_str()),
                "{}: repair kind {}",
                e.code,
                r.kind
            );
            assert!(!r.constraint.is_empty(), "{}: empty constraint", e.code);
        }
        if let Some(r) = &e.unreached {
            assert!(!r.is_empty(), "{}: empty unreached reason", e.code);
        }
    }
}

#[test]
fn emitted_by_and_repair_sources_point_at_source_lines() {
    let (_, entries) = load_registry();
    let sources = all_sources();
    let consts: BTreeMap<String, String> =
        sources.iter().flat_map(|(_, t)| const_codes(t)).collect();
    for e in &entries {
        for site in &e.emitted_by {
            if let Err(msg) = check_site(site, &e.code, &consts, true) {
                panic!("{msg}");
            }
        }
        for r in &e.rules {
            if let Err(msg) = check_site(&r.source, &e.code, &consts, false) {
                panic!("{msg}");
            }
        }
    }
}

#[test]
fn every_code_literal_in_the_source_is_registered() {
    let (_, entries) = load_registry();
    let registered: BTreeSet<&str> = entries.iter().map(|e| e.code.as_str()).collect();
    let mut seen = BTreeSet::new();
    for (_, t) in all_sources() {
        seen.extend(code_literals(&t));
    }
    let missing: Vec<&String> = seen
        .iter()
        .filter(|c| !registered.contains(c.as_str()))
        .collect();
    assert!(
        missing.is_empty(),
        "source codes missing from the registry: {missing:?}"
    );
    let unused: Vec<&&str> = registered.iter().filter(|c| !seen.contains(**c)).collect();
    assert!(
        unused.is_empty(),
        "registry codes not in the source: {unused:?}"
    );
}

#[test]
fn templates_and_constraints_are_source_text() {
    let (_, entries) = load_registry();
    let diag_src =
        std::fs::read_to_string(Path::new(env!("CARGO_MANIFEST_DIR")).join("src/diagnostics.rs"))
            .expect("diagnostics.rs");
    let all_src: String = all_sources()
        .into_iter()
        .map(|(_, t)| t)
        .collect::<Vec<_>>()
        .join("\n");
    for e in &entries {
        if e.template.is_empty() {
            assert!(
                e.implementation_note.is_some(),
                "{}: empty template needs an implementation_note",
                e.code
            );
            continue;
        }
        let escaped = rust_escape(&e.template);
        assert!(
            diag_src.contains(&escaped),
            "{}: message_template is not the text in diagnostics.rs: {}",
            e.code,
            e.template
        );
    }
    for e in &entries {
        for r in &e.rules {
            for frag in fragments(&r.constraint) {
                let esc = rust_escape(&frag);
                let esc_braces = esc.replace('{', "{{").replace('}', "}}");
                assert!(
                    all_src.contains(&esc) || all_src.contains(&esc_braces),
                    "{}: constraint fragment is not in the source: {frag:?}",
                    e.code
                );
            }
        }
    }
}

/// Rust の文字列リテラルの中の書き方（`\` と `"` と改行）。
fn rust_escape(s: &str) -> String {
    let mut out = String::new();
    for c in s.chars() {
        match c {
            '\\' => out.push_str("\\\\"),
            '"' => out.push_str("\\\""),
            '\n' => out.push_str("\\n"),
            c => out.push(c),
        }
    }
    out
}

/// 規則の文字列を `{}` と `{名前}` の placeholder で区切った、固定の部分。
fn fragments(s: &str) -> Vec<String> {
    let mut out = Vec::new();
    let mut cur = String::new();
    let mut chars = s.chars().peekable();
    while let Some(c) = chars.next() {
        if c == '{' {
            let mut name = String::new();
            let mut closed = false;
            let mut look = chars.clone();
            while let Some(d) = look.next() {
                if d == '}' {
                    closed = true;
                    break;
                }
                if !(d.is_ascii_alphanumeric() || d == '_') {
                    break;
                }
                name.push(d);
            }
            if closed {
                for _ in 0..=name.chars().count() {
                    chars.next();
                }
                if !cur.is_empty() {
                    out.push(std::mem::take(&mut cur));
                }
                continue;
            }
        }
        cur.push(c);
    }
    if !cur.is_empty() {
        out.push(cur);
    }
    out.into_iter().filter(|f| f.chars().count() >= 3).collect()
}

fn has_placeholder(s: &str) -> bool {
    s.contains("{}")
        || fragments(s).len() != 1
        || fragments(s).first().map(|f| f.as_str()) != Some(s)
}

/// 処理系の constraint が registry の規則と合うか。placeholder のある規則は kind だけで合う。
/// placeholder のない規則は完全に一致し、ただし型引数らしい名前では generics.rs の `param_note` が
/// 後ろに「; or, if …」の文を付けるので、その形の続きは許す。
fn constraint_matches(rule: &str, actual: &str) -> bool {
    if has_placeholder(rule) {
        return true;
    }
    match actual.strip_prefix(rule) {
        Some(rest) => rest.is_empty() || rest.starts_with("; or, if "),
        None => false,
    }
}

/// fixture の診断を registry と照合する。
#[test]
fn fixture_diagnostics_match_the_registry() {
    let (_, entries) = load_registry();
    let by_code: BTreeMap<&str, &Entry> = entries.iter().map(|e| (e.code.as_str(), e)).collect();
    let mut exercised: BTreeSet<&'static str> = BTreeSet::new();
    for c in cases() {
        assert!(
            c.diags.iter().any(|d| d.code == c.code),
            "{}: the fixture does not produce its code; produced {:?}",
            c.code,
            c.diags
                .iter()
                .map(|d| (d.code, d.phase))
                .collect::<Vec<_>>()
        );
        for d in &c.diags {
            let e = by_code
                .get(d.code)
                .unwrap_or_else(|| panic!("{}: not in the registry", d.code));
            exercised.insert(d.code);
            assert_eq!(d.severity, e.severity, "{}: severity", d.code);
            assert!(
                e.phases.iter().any(|p| p == d.phase),
                "{}: phase {} is not in the registry {:?}",
                d.code,
                d.phase,
                e.phases
            );
            if PREFIX_MATCH.contains(&d.code) {
                assert!(
                    d.message.starts_with(&e.template),
                    "{}: message {:?} does not start with {:?}",
                    d.code,
                    d.message,
                    e.template
                );
            } else {
                assert_eq!(d.message, e.template, "{}: message", d.code);
            }
            match &d.repair {
                None => {}
                Some(r) => {
                    assert!(
                        !e.rules.is_empty(),
                        "{}: the implementation sets a repair but the registry says null",
                        d.code
                    );
                    let ok = e.rules.iter().any(|rule| {
                        rule.kind == r.kind && constraint_matches(&rule.constraint, &r.constraint)
                    });
                    assert!(
                        ok,
                        "{}: repair {:?} matches no registry rule {:?}",
                        d.code,
                        (r.kind, &r.constraint),
                        e.rules
                            .iter()
                            .map(|x| (&x.kind, &x.constraint))
                            .collect::<Vec<_>>()
                    );
                }
            }
        }
    }
    for e in &entries {
        let hit = exercised.contains(e.code.as_str());
        match &e.unreached {
            Some(_) => assert!(
                !hit,
                "{}: marked unreached but a fixture produces it",
                e.code
            ),
            None => assert!(
                hit,
                "{}: no fixture produces it and it has no unreached reason",
                e.code
            ),
        }
    }
}

#[test]
fn implementation_notes_are_present_for_the_known_differences() {
    let (_, entries) = load_registry();
    for code in [
        "E-CYCLE-CALL",
        "E-INTERNAL-SOURCE-BOUNDARY",
        "E-DIAG-LIMIT",
        "W-DIAG-LIMIT",
    ] {
        let e = entries.iter().find(|e| e.code == code).expect(code);
        assert!(
            e.implementation_note.is_some(),
            "{code}: implementation_note"
        );
    }
}
