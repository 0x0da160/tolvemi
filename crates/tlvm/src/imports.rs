//! v1.11：`import "path.tlvm"` の解決（検証されていない接着部分）。
//!
//! 根のファイルから import をたどって各ファイルを一度ずつ読み（菱形の import でも一度）、依存されるものが先に来る順
//! （深さ優先の帰りがけ順。根は最後）に、一つの source へつなぐ。つなぐときは、各ファイルの import の行と、根以外の
//! ファイルの `entry` 宣言を同じ長さの空白に置き換える（位置を保つ）。つないだ source を今までの `api::compile` に渡すので、
//! 型引数・直和型・レコード・map など・辞書の書き換えはすべてまとめたプログラムに対して行われ、検証済み部品が確かめるのも
//! まとめたプログラムである。診断の span は、つないだ source 上の位置からファイルの中の位置に戻し、`file` を付ける。
//!
//! ファイルを読むのは [`Loader`] で、CLI はファイルシステム（[`FsLoader`]）、`api::compile_files` は名前と source の
//! 対応表（[`MapLoader`]）を使う。どちらもパスは根のファイルのディレクトリからの相対パス（`/` 区切り、`.`・`..` を
//! 含まない正規形）で受け取る。

use crate::api::{compile, parse_source, result, Parsed, SourceCompile};
use crate::diagnostics::{finalize, Diagnostic};
use crate::packages::{self, Dep};
use crate::profiles::StaticProfile;
use crate::syntax::{Decl, Program};
use std::collections::{BTreeMap, HashMap};
use std::io::Read;
use std::path::{Path, PathBuf};
use std::rc::Rc;

/// ファイルを読む口。`rel` は根のファイルのディレクトリからの正規形の相対パス。
pub trait Loader {
    /// 中身を読む。`max_bytes` より長いファイルは `max_bytes + 1` bytes まで読めばよい（長さの上限の診断に使う）。
    /// 無ければ Err（理由）。
    fn load(&mut self, rel: &str, max_bytes: usize) -> Result<Vec<u8>, String>;
    /// 診断の `file` に出す名前。
    fn display(&self, rel: &str) -> String;
}

/// ファイルシステムから読む（CLI 用）。根のファイルのディレクトリの外（symlink で外を指すものを含む）は読まない。
pub struct FsLoader {
    root_dir: PathBuf,
}

impl FsLoader {
    /// `root_path` は根のファイルのパス（CLI に渡されたもの）。
    pub fn new(root_path: &str) -> FsLoader {
        FsLoader { root_dir: Path::new(root_path).parent().map(Path::to_path_buf).unwrap_or_default() }
    }
}

impl Loader for FsLoader {
    fn load(&mut self, rel: &str, max_bytes: usize) -> Result<Vec<u8>, String> {
        let dir = if self.root_dir.as_os_str().is_empty() { Path::new(".") } else { self.root_dir.as_path() };
        let path = dir.join(rel);
        let (Ok(real), Ok(base)) = (path.canonicalize(), dir.canonicalize()) else { return Err("no such file".into()) };
        if !real.starts_with(&base) {
            return Err("resolves outside the root file's directory".into());
        }
        if !real.is_file() {
            return Err("not a regular file".into());
        }
        let f = std::fs::File::open(&real).map_err(|e| e.to_string())?;
        let mut v = vec![];
        f.take(max_bytes as u64 + 1).read_to_end(&mut v).map_err(|e| e.to_string())?;
        Ok(v)
    }
    fn display(&self, rel: &str) -> String {
        if self.root_dir.as_os_str().is_empty() {
            rel.to_string()
        } else {
            self.root_dir.join(rel).to_string_lossy().into_owned()
        }
    }
}

/// 名前と source の対応表から読む（`api::compile_files` 用。ファイルシステムには触れない）。
/// 対応表の key は `/` 区切りのパス（`.`・`..` を含まない）で、根の key のディレクトリからの相対パスで引く。
pub struct MapLoader<'a> {
    pub root_dir: String,
    pub files: &'a BTreeMap<String, String>,
}

impl MapLoader<'_> {
    fn key(&self, rel: &str) -> String {
        if self.root_dir.is_empty() {
            rel.to_string()
        } else {
            format!("{}/{rel}", self.root_dir)
        }
    }
}

impl Loader for MapLoader<'_> {
    fn load(&mut self, rel: &str, _max_bytes: usize) -> Result<Vec<u8>, String> {
        self.files.get(&self.key(rel)).map(|s| s.as_bytes().to_vec()).ok_or_else(|| "not in the map of sources".into())
    }
    fn display(&self, rel: &str) -> String {
        self.key(rel)
    }
}

/// import のパスの字句の規則（v1.11）：空でなく、`/` で始まらず、`\`・`:`・制御文字を含まず、`.tlvm` で終わる。
fn check_path(path: &str) -> Result<(), &'static str> {
    if path.is_empty() {
        return Err("empty path");
    }
    if path.starts_with('/') {
        return Err("absolute paths are not allowed");
    }
    if path.chars().any(|c| c == '\\' || c == ':' || c.is_control()) {
        return Err("use '/' as the separator; '\\', ':' and control characters are not allowed");
    }
    if !path.ends_with(".tlvm") {
        return Err("the path must end in .tlvm");
    }
    Ok(())
}

/// import のパスを、それを書いたファイルのディレクトリ `dir`（正規形の相対パス。根なら空）に対して解決し、正規形にする。
pub fn join(dir: &str, path: &str) -> Result<String, &'static str> {
    check_path(path)?;
    let mut parts: Vec<&str> = dir.split('/').filter(|s| !s.is_empty()).collect();
    for c in path.split('/') {
        match c {
            "" => return Err("empty path component ('//' or a trailing '/')"),
            "." => {}
            ".." => {
                if parts.pop().is_none() {
                    return Err("'..' must not go above the root file's directory");
                }
            }
            c => parts.push(c),
        }
    }
    match parts.last() {
        Some(last) if last.len() > ".tlvm".len() => Ok(parts.join("/")),
        _ => Err("the file name must not be empty"),
    }
}

fn dir_of(rel: &str) -> &str {
    rel.rsplit_once('/').map_or("", |(d, _)| d)
}

/// 一つのファイル（つないだ source の一部）。
#[derive(Clone, Debug)]
pub struct Segment {
    /// 診断の `file` に出す名前
    pub file: String,
    /// つないだ source の中の開始位置
    pub start: usize,
    pub len: usize,
}

/// import をまとめた一つのプログラムの source。
#[derive(Clone, Debug)]
pub struct Merged {
    pub source: Vec<u8>,
    /// 依存されるものが先（根は最後）
    pub segments: Vec<Segment>,
    /// 読んだファイル（名前と元の中身。根が先頭）。`--human` の表示に使う
    pub files: Vec<(String, Vec<u8>)>,
}

impl Merged {
    fn root(&self) -> &Segment {
        self.segments.last().expect("root segment")
    }

    /// つないだ source 上の位置を (ファイル, ファイルの中の位置) に戻す。どのファイルにも当たらない位置（先頭の区切り）は根の 0。
    fn locate(&self, at: usize) -> (&Segment, usize) {
        for s in &self.segments {
            if at >= s.start && at <= s.start + s.len {
                return (s, at - s.start);
            }
        }
        // 末尾の区切りの改行より後（EOF）は根の終わり
        let root = self.root();
        if at > root.start {
            return (root, root.len);
        }
        (root, 0)
    }

    fn map_span(&self, (a, b): (usize, usize)) -> (&Segment, (usize, usize)) {
        let (seg, s) = self.locate(a);
        let e = b.saturating_sub(seg.start).clamp(s, seg.len.max(s));
        (seg, (s, e))
    }

    /// 診断の span をファイルの中の位置に直し、`file` を付ける。
    pub fn attribute(&self, ds: Vec<Diagnostic>) -> Vec<Diagnostic> {
        let root = self.root().file.clone();
        ds.into_iter()
            .filter_map(|mut d| {
                let (seg, span) = self.map_span(d.span);
                let file = seg.file.clone();
                // ライブラリの関数が根の entry から使われないのは普通のことなので、その warning は出さない
                if d.code == "W-UNUSED-FUNCTION" && file != root {
                    return None;
                }
                d.span = span;
                if let Some(r) = d.repair.as_mut() {
                    let (_, t) = self.map_span(r.target_span);
                    r.target_span = t;
                }
                d.file = Some(file);
                Some(d)
            })
            .collect()
    }

    pub fn source_of(&self, file: &str) -> Option<&[u8]> {
        self.files.iter().find(|(f, _)| f == file).map(|(_, b)| b.as_slice())
    }
}

pub enum Resolved {
    /// 根に import がない（か根自体が構文として読めない）：根だけを今までどおり検査する（`file` は付けない）
    Single,
    Merged(Merged),
    /// 解決の誤り・読んだファイルの構文の誤り・名前の衝突（`file` 付き）。読めたファイルの名前と中身も返す
    Rejected { errors: Vec<Diagnostic>, files: Vec<(String, Vec<u8>)> },
    /// 読んだファイルが UTF-8 でない
    SourceBoundaryFailure { file: String },
}

struct File {
    rel: String,
    display: String,
    bytes: Vec<u8>,
    /// 構文として読めなかったファイルは None（診断は既に出してある）
    program: Option<Program>,
}

/// ディレクトリの `tlvm.json` の読み方（v1.16）。
#[derive(Clone)]
enum Slot {
    /// そのディレクトリに `tlvm.json` がない
    Absent,
    /// `tlvm.json` があるが誤っている（診断は出してある）
    Bad,
    Pkg(Rc<Pkg>),
}

/// 読んだパッケージ。
struct Pkg {
    /// 根からの正規形のディレクトリ（根は空）
    dir: String,
    /// 診断に出す、マニフェストの名前
    display: String,
    name: Option<String>,
    version: Option<String>,
    deps: BTreeMap<String, Dep>,
}

struct Walk<'a> {
    loader: &'a mut dyn Loader,
    profile: &'a StaticProfile,
    files: Vec<File>,
    index: HashMap<String, usize>,
    stack: Vec<usize>,
    order: Vec<usize>,
    total: usize,
    diags: Vec<Diagnostic>,
    boundary: Option<String>,
    stop: bool,
    /// 読んだ `tlvm.json`（ディレクトリごとに一度）
    pkgs: HashMap<String, Slot>,
    /// 読んだ `tlvm.json` の名前と中身（`files` に足す。診断の表示に使う）
    manifests: Vec<(String, Vec<u8>)>,
}

fn err(code: &'static str, file: &str, span: (usize, usize)) -> Diagnostic {
    let mut d = Diagnostic::error("import", code, span);
    d.file = Some(file.to_string());
    d
}

impl Walk<'_> {
    /// ディレクトリ `dir` の `tlvm.json` を読む（ディレクトリごとに一度。誤りは診断に出し、以後は Bad として扱う）。
    fn slot(&mut self, dir: &str) -> Slot {
        if let Some(s) = self.pkgs.get(dir) {
            return s.clone();
        }
        let key = if dir.is_empty() { packages::MANIFEST.to_string() } else { format!("{dir}/{}", packages::MANIFEST) };
        let display = self.loader.display(&key);
        let s = match self.loader.load(&key, packages::MANIFEST_MAX_BYTES) {
            Err(_) => Slot::Absent,
            Ok(bytes) => {
                self.manifests.push((display.clone(), bytes.clone()));
                match packages::parse(&bytes) {
                    Ok(m) => Slot::Pkg(Rc::new(Pkg { dir: dir.to_string(), display, name: m.name, version: m.version, deps: m.deps })),
                    Err((why, span)) => {
                        self.diags.push(err("E-PKG-MANIFEST", &display, span).act(why).fix(
                            "replace_expression",
                            span,
                            "a tlvm.json whose keys are only name, version and dependencies (see the LPTL v1.16 delta)",
                        ));
                        Slot::Bad
                    }
                }
            }
        };
        self.pkgs.insert(dir.to_string(), s.clone());
        s
    }

    /// ディレクトリ `dir` から上へたどって最初の `tlvm.json` のパッケージ（無ければ None）。誤りのものに当たれば Err（診断は出してある）。
    fn nearest(&mut self, dir: &str) -> Result<Option<Rc<Pkg>>, ()> {
        let mut d = dir.to_string();
        loop {
            match self.slot(&d) {
                Slot::Pkg(p) => return Ok(Some(p)),
                Slot::Bad => return Err(()),
                Slot::Absent => {}
            }
            if d.is_empty() {
                return Ok(None);
            }
            d = dir_of(&d).to_string();
        }
    }

    /// パッケージ `from` が宣言した依存 `name` のパッケージを読む（使われたときに読む）。誤りは診断に出して Err を返す。
    fn dependency(&mut self, from: &Pkg, name: &str) -> Result<Rc<Pkg>, ()> {
        let dep: Dep = from.deps[name].clone();
        let dir = match packages::join_dir(&from.dir, &dep.path) {
            Ok(d) if !d.is_empty() && d != from.dir => d,
            Ok(_) => {
                self.diags.push(err("E-PKG-PATH", &from.display, dep.path_span).act(format!(
                    "\"{}\": resolves to the project root or to the declaring package itself",
                    dep.path
                )).fix("replace_expression", dep.path_span, "a path to a subdirectory that holds the dependency's tlvm.json"));
                return Err(());
            }
            Err(why) => {
                self.diags.push(err("E-PKG-PATH", &from.display, dep.path_span).act(format!("\"{}\": {why}", dep.path)).fix(
                    "replace_expression",
                    dep.path_span,
                    "a relative path with '/' separators that stays inside the project, such as \"deps/stats\"",
                ));
                return Err(());
            }
        };
        let p = match self.slot(&dir) {
            Slot::Pkg(p) => p,
            Slot::Absent => {
                self.diags.push(err("E-PKG-NOT-FOUND", &from.display, dep.path_span).act(format!("{dir}/{}: no such file", packages::MANIFEST)).fix(
                    "replace_expression",
                    dep.path_span,
                    "the path of a directory that holds a tlvm.json declaring the package",
                ));
                return Err(());
            }
            Slot::Bad => return Err(()),
        };
        if p.name.as_deref() != Some(name) {
            let said = p.name.as_deref().map_or("no name".to_string(), |n| format!("\"{n}\""));
            self.diags.push(err("E-PKG-NAME", &from.display, dep.name_span).act(format!("{name}: {} says {said}", p.display)).fix(
                "replace_identifier",
                dep.name_span,
                "the dependency's name, the same as the \"name\" in its tlvm.json",
            ));
            return Err(());
        }
        if let Some(pin) = &dep.pin {
            if p.version.as_deref() != Some(pin.as_str()) {
                let has = p.version.as_deref().unwrap_or("no version");
                self.diags.push(err("E-PKG-VERSION", &from.display, dep.pin_span).act(format!("{name}: pinned {pin}, but {} has {has}", p.display)).fix(
                    "replace_expression",
                    dep.pin_span,
                    "the version of the dependency's tlvm.json, or the version it declares",
                ));
                return Err(());
            }
        }
        Ok(p)
    }

    /// `@名前/パス` の import（v1.16）を、依存のディレクトリからの正規形の相対パスにする。`body` は `@` の後ろ。
    fn package_target(&mut self, i: usize, body: &str, span: (usize, usize), from: &str) -> Result<String, ()> {
        let dir = dir_of(&self.files[i].rel).to_string();
        let Some(pkg) = self.nearest(&dir)? else {
            self.diags.push(err("E-PKG-UNKNOWN", from, span).act(format!("@{body}: this file is in no package (no tlvm.json at or above its directory)")).fix(
                "replace_expression",
                span,
                "a relative path to the file, or a tlvm.json that declares the dependency",
            ));
            return Err(());
        };
        let Some((name, path)) = body.split_once('/') else {
            self.diags.push(err("E-IMPORT-PATH", from, span).act(format!("\"@{body}\": expected @name/path.tlvm")).fix(
                "replace_expression",
                span,
                "\"@name/path.tlvm\", such as \"@stats/summary.tlvm\"",
            ));
            return Err(());
        };
        if !packages::valid_name(name) {
            self.diags.push(err("E-IMPORT-PATH", from, span).act(format!("\"@{body}\": the name must match [a-z][a-z0-9_]*")).fix(
                "replace_expression",
                span,
                "\"@name/path.tlvm\", such as \"@stats/summary.tlvm\"",
            ));
            return Err(());
        }
        if !pkg.deps.contains_key(name) {
            let declared: Vec<&str> = pkg.deps.keys().map(String::as_str).collect();
            let list = if declared.is_empty() { "none".to_string() } else { declared.join(", ") };
            self.diags.push(err("E-PKG-UNKNOWN", from, span).act(format!("@{name}: not a dependency of this package (declared: {list})")).fix(
                "replace_expression",
                span,
                "the name of a dependency declared in tlvm.json, or a relative path",
            ));
            return Err(());
        }
        let dep = self.dependency(&pkg, name)?;
        if let Err(why) = check_path(path) {
            self.diags.push(err("E-IMPORT-PATH", from, span).act(format!("\"@{name}/{path}\": {why}")).fix(
                "replace_expression",
                span,
                "\"@name/path.tlvm\", such as \"@stats/summary.tlvm\"",
            ));
            return Err(());
        }
        match packages::join_dir(&dep.dir, path) {
            Ok(key) if key.starts_with(&format!("{}/", dep.dir)) => Ok(key),
            _ => {
                self.diags.push(err("E-IMPORT-PATH", from, span).act(format!("\"@{name}/{path}\": must stay inside the dependency's directory")).fix(
                    "replace_expression",
                    span,
                    "a path inside the dependency's directory",
                ));
                Err(())
            }
        }
    }

    fn visit(&mut self, i: usize) {
        self.stack.push(i);
        let imports = self.files[i].program.as_ref().map(|p| p.imports.clone()).unwrap_or_default();
        let from = self.files[i].display.clone();
        for imp in imports {
            if self.stop {
                break;
            }
            let target = if let Some(body) = imp.path.strip_prefix('@') {
                match self.package_target(i, body, imp.path_span.t(), &from) {
                    Ok(t) => t,
                    Err(()) => continue,
                }
            } else {
                match join(dir_of(&self.files[i].rel), &imp.path) {
                    Ok(t) => t,
                    Err(why) => {
                        self.diags.push(err("E-IMPORT-PATH", &from, imp.path_span.t()).act(format!("\"{}\": {why}", imp.path)).fix(
                            "replace_expression",
                            imp.path_span.t(),
                            "relative path ending in .tlvm, such as \"lib/util.tlvm\", resolved from the importing file's directory (no leading '/', no '\\', no '..' above the root file's directory)",
                        ));
                        continue;
                    }
                }
            };
            if let Some(pos) = self.stack.iter().position(|&j| self.files[j].rel == target) {
                let mut cycle: Vec<String> = self.stack[pos..].iter().map(|&j| self.files[j].display.clone()).collect();
                cycle.push(self.files[self.stack[pos]].display.clone());
                self.diags.push(err("E-IMPORT-CYCLE", &from, imp.span.t()).act(cycle.join(" -> ")).fix(
                    "delete_span",
                    imp.span.t(),
                    "remove this import: files must not import each other in a cycle; move the definitions both files need into a third file that both import",
                ));
                continue;
            }
            if self.index.contains_key(&target) {
                continue;
            }
            let display = self.loader.display(&target);
            if self.files.len() >= self.profile.import_files {
                self.diags.push(
                    err("E-LIMIT-STATIC-IMPORT-FILES", &from, imp.span.t())
                        .exp(self.profile.import_files.to_string())
                        .act((self.files.len() + 1).to_string()),
                );
                self.stop = true;
                break;
            }
            let bytes = match self.loader.load(&target, self.profile.source_bytes) {
                Ok(b) => b,
                Err(why) => {
                    self.diags.push(err("E-IMPORT-NOT-FOUND", &from, imp.path_span.t()).act(format!("{display}: {why}")).fix(
                        "replace_expression",
                        imp.path_span.t(),
                        "path of an existing .tlvm file, relative to the directory of the importing file",
                    ));
                    continue;
                }
            };
            self.total += bytes.len();
            if self.total > self.profile.source_bytes {
                self.diags.push(
                    err("E-LIMIT-STATIC-SOURCE-BYTES", &from, imp.span.t())
                        .exp(self.profile.source_bytes.to_string())
                        .act(self.total.to_string()),
                );
                self.stop = true;
                break;
            }
            if std::str::from_utf8(&bytes).is_err() {
                self.boundary = Some(display);
                self.stop = true;
                break;
            }
            let program = match parse_source(&bytes, self.profile) {
                Parsed::Program(p) => Some(p),
                _ => {
                    // 構文の誤り：単一ファイルと同じ診断（修復ヒント・検証済み parser との照合を含む）を、このファイルに付けて出す
                    if let SourceCompile::Result(r) = compile(&bytes, self.profile) {
                        for mut d in r.errors().iter().cloned() {
                            d.file = Some(display.clone());
                            self.diags.push(d);
                        }
                    }
                    None
                }
            };
            let j = self.files.len();
            self.index.insert(target.clone(), j);
            self.files.push(File { rel: target, display, bytes, program });
            if self.files[j].program.is_some() {
                self.visit(j);
            }
        }
        self.stack.pop();
        self.order.push(i);
    }
}

/// 宣言する名前（関数・型・構築子）と、その名前の span。
fn declared(p: &Program) -> Vec<(String, (usize, usize))> {
    let mut v = vec![];
    for d in &p.declarations {
        match d {
            Decl::Fn(f) => v.push((f.name.clone(), f.name_span.t())),
            Decl::Type(t) => v.push((t.name.clone(), t.name_span.t())),
            Decl::Sum(t) => {
                v.push((t.name.clone(), t.name_span.t()));
                for c in &t.variants {
                    v.push((c.name.clone(), c.name_span.t()));
                }
            }
            Decl::Entry(_) => {}
        }
    }
    v
}

/// 根のファイルから import をたどり、一つの source にまとめる。`root_rel` は根のファイル名（ディレクトリを除いた名前）、
/// `root_display` は診断に出す根の名前。
pub fn resolve(root_display: &str, root_rel: &str, root: &[u8], loader: &mut dyn Loader, profile: &StaticProfile) -> Resolved {
    let Parsed::Program(rp) = parse_source(root, profile) else { return Resolved::Single };
    if rp.imports.is_empty() {
        return Resolved::Single;
    }
    let mut w = Walk {
        loader,
        profile,
        files: vec![File { rel: root_rel.to_string(), display: root_display.to_string(), bytes: root.to_vec(), program: Some(rp) }],
        index: HashMap::new(),
        stack: vec![],
        order: vec![],
        total: root.len(),
        diags: vec![],
        boundary: None,
        stop: false,
        pkgs: HashMap::new(),
        manifests: vec![],
    };
    w.index.insert(root_rel.to_string(), 0);
    w.visit(0);
    let mut files: Vec<(String, Vec<u8>)> = w.files.iter().map(|f| (f.display.clone(), f.bytes.clone())).collect();
    files.extend(w.manifests.iter().cloned());
    if let Some(file) = w.boundary {
        return Resolved::SourceBoundaryFailure { file };
    }
    if !w.diags.is_empty() || w.stop {
        return Resolved::Rejected { errors: finalize(w.diags).0, files };
    }
    // 名前の衝突：同じ名前を二つのファイルが定義する（一つのファイルの中の重複は今までの診断に任せる）
    let mut seen: HashMap<String, usize> = HashMap::new();
    let mut diags = vec![];
    for &i in &w.order {
        let f = &w.files[i];
        let Some(p) = &f.program else { continue };
        let mut here = std::collections::HashSet::new();
        for (name, span) in declared(p) {
            match seen.get(&name) {
                Some(&j) if j != i => {
                    diags.push(
                        err("E-IMPORT-CONFLICT", &f.display, span)
                            .act(format!("{name}: defined in {} and in {}", w.files[j].display, f.display))
                            .fix(
                                "replace_identifier",
                                span,
                                format!("a name not defined in any other file of the program ({name} is already defined in {}); imported files share one namespace", w.files[j].display),
                            ),
                    );
                }
                _ => {
                    if here.insert(name.clone()) {
                        seen.entry(name).or_insert(i);
                    }
                }
            }
        }
    }
    if !diags.is_empty() {
        return Resolved::Rejected { errors: finalize(diags).0, files };
    }
    // つなぐ：import の行と、根以外の entry を空白にする（改行は残して位置を保つ）
    let mut source = vec![b'\n'];
    let mut segments = vec![];
    for &i in &w.order {
        let f = &w.files[i];
        let p = f.program.as_ref().expect("parsed");
        let mut b = f.bytes.clone();
        let mut blank = |(s, e): (usize, usize)| {
            for c in &mut b[s.min(e)..e.min(f.bytes.len())] {
                if *c != b'\n' {
                    *c = b' ';
                }
            }
        };
        for imp in &p.imports {
            blank(imp.span.t());
        }
        if i != 0 {
            for e in p.entries() {
                blank(e.meta.span());
            }
        }
        segments.push(Segment { file: f.display.clone(), start: source.len(), len: b.len() });
        source.extend_from_slice(&b);
        source.push(b'\n');
    }
    Resolved::Merged(Merged { source, segments, files })
}

/// まとめた source を検査し、診断をファイルに戻す。
pub fn compile_merged(m: &Merged, profile: &StaticProfile) -> SourceCompile {
    // 区切りの改行の分だけ source bytes の上限を広げる（ファイルの合計は resolve が上限と比べてある）
    let mut mp = profile.clone();
    mp.source_bytes = mp.source_bytes.max(m.source.len());
    match compile(&m.source, &mp) {
        SourceCompile::SourceBoundaryFailure => SourceCompile::SourceBoundaryFailure,
        SourceCompile::Result(r) => SourceCompile::Result(match r {
            crate::api::CompileResult::Accepted { program, warnings, work } => {
                crate::api::CompileResult::Accepted { program, warnings: m.attribute(warnings), work }
            }
            crate::api::CompileResult::Rejected { errors, warnings, work } => {
                crate::api::CompileResult::Rejected { errors: m.attribute(errors), warnings: m.attribute(warnings), work }
            }
        }),
    }
}

/// 根のファイルを import ごと検査する。`files` は読んだファイル（名前と中身。根が先頭。import がなければ根だけ）。
pub fn compile_root(
    root_display: &str,
    root_rel: &str,
    root: &[u8],
    loader: &mut dyn Loader,
    profile: &StaticProfile,
) -> (SourceCompile, Vec<(String, Vec<u8>)>) {
    match resolve(root_display, root_rel, root, loader, profile) {
        Resolved::Single => (compile(root, profile), vec![(root_display.to_string(), root.to_vec())]),
        Resolved::Merged(m) => (compile_merged(&m, profile), m.files),
        Resolved::Rejected { errors, files } => (SourceCompile::Result(result(errors, None)), files),
        Resolved::SourceBoundaryFailure { .. } => (SourceCompile::SourceBoundaryFailure, vec![]),
    }
}

/// まとめた source を構文解析する（`tlvm ast` 用）。誤りの診断はファイルに戻す。
pub fn parse_merged(m: &Merged, profile: &StaticProfile) -> Result<Program, Vec<Diagnostic>> {
    let mut mp = profile.clone();
    mp.source_bytes = mp.source_bytes.max(m.source.len());
    match parse_source(&m.source, &mp) {
        Parsed::Program(p) => Ok(p),
        Parsed::Failed(SourceCompile::Result(r)) => Err(m.attribute(r.errors().to_vec())),
        Parsed::Failed(SourceCompile::SourceBoundaryFailure) => Err(vec![]),
    }
}
