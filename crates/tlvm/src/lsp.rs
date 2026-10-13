//! v1.12：最小の Language Server `tlvm lsp`（検証されていない front-end。判定は今までの検査の経路が行う）。
//!
//! 標準入出力の JSON-RPC 2.0（`Content-Length` の header で区切る）で、次だけを扱う：
//!
//! - `initialize`・`initialized`・`shutdown`・`exit`
//! - `textDocument/didOpen`・`didChange`（全文の同期）・`didClose` → `textDocument/publishDiagnostics`
//! - `textDocument/formatting`（正準の整形。全文を置き換える一つの edit。構文の誤りがあれば null）
//!
//! 診断の span（UTF-8 の bytes）は LSP の位置（行と UTF-16 の code unit の列）に直す。`file://` の文書の import は
//! その文書のファイルのディレクトリから解決し、開いている文書があればその中身を、なければディスクのファイルを読む。
//! import したファイルの診断は、根の文書の最初の import の行に `file:行:列:` を付けて出す。
//! JSON の読み取りは `strict_json`、書き出しは手で組み立てる（依存を増やさない）。

use crate::api::{canonical, compile, needs_glue, parse_source, without_rec_markers, Parsed, SourceCompile};
use crate::diagnostics::{json_string, line_col, Diagnostic};
use crate::formatter::format_program;
use crate::imports::{self, FsLoader, Loader};
use crate::profiles::StaticProfile;
use crate::strict_json::{self, JKind, JNode};
use std::collections::BTreeMap;
use std::io::{BufRead, Write};
use std::path::{Path, PathBuf};

/// 一つの message の本体の上限（bytes）。
const MAX_MESSAGE: usize = 64 << 20;

/// 開いている文書。
struct Doc {
    text: String,
    version: Option<String>,
}

pub struct Server {
    docs: BTreeMap<String, Doc>,
    initialized: bool,
    shutdown: bool,
}

/// `Content-Length` で区切った message を一つ読む。EOF なら None。
pub fn read_message(input: &mut dyn BufRead) -> std::io::Result<Option<Vec<u8>>> {
    let mut len: Option<usize> = None;
    let mut any = false;
    loop {
        let mut line = String::new();
        if input.read_line(&mut line)? == 0 {
            return if any {
                Err(std::io::Error::new(std::io::ErrorKind::UnexpectedEof, "EOF in header"))
            } else {
                Ok(None)
            };
        }
        any = true;
        let l = line.trim_end_matches(['\r', '\n']);
        if l.is_empty() {
            if len.is_none() {
                // 空行だけなら読み飛ばす
                any = false;
                continue;
            }
            break;
        }
        if let Some((k, v)) = l.split_once(':') {
            if k.trim().eq_ignore_ascii_case("content-length") {
                len = v.trim().parse().ok();
            }
        }
    }
    let n = len.unwrap_or(0);
    if n > MAX_MESSAGE {
        return Err(std::io::Error::new(std::io::ErrorKind::InvalidData, "message too large"));
    }
    let mut body = vec![0; n];
    input.read_exact(&mut body)?;
    Ok(Some(body))
}

pub fn write_message(out: &mut dyn Write, body: &str) -> std::io::Result<()> {
    write!(out, "Content-Length: {}\r\n\r\n{body}", body.len())?;
    out.flush()
}

/// byte 位置を LSP の位置（行、UTF-16 の列）にする。
pub fn position(text: &str, offset: usize) -> (usize, usize) {
    let mut off = offset.min(text.len());
    while !text.is_char_boundary(off) {
        off -= 1;
    }
    let before = &text[..off];
    let line = before.matches('\n').count();
    let start = before.rfind('\n').map_or(0, |i| i + 1);
    let col = text[start..off].chars().map(char::len_utf16).sum();
    (line, col)
}

fn range_json(text: &str, (s, e): (usize, usize)) -> String {
    let (l1, c1) = position(text, s);
    let (l2, c2) = position(text, e.max(s));
    format!("{{\"start\":{{\"line\":{l1},\"character\":{c1}}},\"end\":{{\"line\":{l2},\"character\":{c2}}}}}")
}

/// 診断の message（期待・実際の値と修復ヒントを添える）。
fn message(d: &Diagnostic) -> String {
    let mut m = if d.message.is_empty() { d.code.to_string() } else { d.message.clone() };
    match (&d.expected, &d.actual) {
        (Some(e), Some(a)) => m.push_str(&format!(" (expected {e}, found {a})")),
        (Some(e), None) => m.push_str(&format!(" (expected {e})")),
        (None, Some(a)) => m.push_str(&format!(" (found {a})")),
        (None, None) => {}
    }
    if let Some(r) = &d.repair {
        m.push_str(&format!("\nrepair ({}): {}", r.kind, r.constraint));
    }
    m
}

fn diag_json(text: &str, span: (usize, usize), severity: u8, code: &str, msg: &str) -> String {
    format!(
        "{{\"range\":{},\"severity\":{severity},\"code\":{},\"source\":\"tlvm\",\"message\":{}}}",
        range_json(text, span),
        json_string(code),
        json_string(msg)
    )
}

/// `file://` の URI をパスにする（`%XX` を戻す）。それ以外は None。
pub fn uri_path(uri: &str) -> Option<PathBuf> {
    let rest = uri.strip_prefix("file://")?;
    // file://host/path の host は localhost か空だけ
    let path = if rest.starts_with('/') { rest } else { rest.strip_prefix("localhost")? };
    let b = path.as_bytes();
    let mut out = vec![];
    let mut i = 0;
    while i < b.len() {
        if b[i] == b'%' && i + 2 < b.len() {
            let h = std::str::from_utf8(&b[i + 1..i + 3]).ok().and_then(|h| u8::from_str_radix(h, 16).ok())?;
            out.push(h);
            i += 3;
        } else {
            out.push(b[i]);
            i += 1;
        }
    }
    Some(PathBuf::from(String::from_utf8(out).ok()?))
}

/// 開いている文書を先に、なければディスクを読む loader。
struct Overlay<'a> {
    fs: FsLoader,
    dir: PathBuf,
    open: BTreeMap<PathBuf, &'a str>,
}

impl Loader for Overlay<'_> {
    fn load(&mut self, rel: &str, max_bytes: usize) -> Result<Vec<u8>, String> {
        if let Some(t) = self.open.get(&self.dir.join(rel)) {
            return Ok(t.as_bytes().to_vec());
        }
        self.fs.load(rel, max_bytes)
    }
    fn display(&self, rel: &str) -> String {
        self.fs.display(rel)
    }
}

/// 文書を検査して診断（LSP の Diagnostic の JSON）の列を返す。
pub fn diagnose(uri: &str, text: &str, others: &BTreeMap<String, String>) -> Vec<String> {
    let sp = StaticProfile::default();
    let (r, files, root) = match uri_path(uri) {
        Some(path) => {
            let display = path.to_string_lossy().into_owned();
            let rel = path.file_name().map(|n| n.to_string_lossy().into_owned()).unwrap_or_default();
            let dir = path.parent().map(Path::to_path_buf).unwrap_or_default();
            let open = others.iter().filter_map(|(u, t)| uri_path(u).map(|p| (p, t.as_str()))).collect();
            let mut loader = Overlay { fs: FsLoader::new(&display), dir, open };
            let (r, files) = imports::compile_root(&display, &rel, text.as_bytes(), &mut loader, &sp);
            (r, files, Some(display))
        }
        None => (compile(text.as_bytes(), &sp), vec![], None),
    };
    let r = match r {
        SourceCompile::Result(r) => r,
        SourceCompile::SourceBoundaryFailure => {
            return vec![diag_json(text, (0, 0), 1, "SourceBoundaryFailure", "an imported file is not valid UTF-8")];
        }
    };
    // import したファイルの診断を置く場所：根の最初の import の行
    let import_span = match parse_source(text.as_bytes(), &sp) {
        Parsed::Program(p) => p.imports.first().map(|i| i.span.t()),
        _ => None,
    }
    .unwrap_or((0, 0));
    let mut out = vec![];
    for (d, sev) in r.errors().iter().map(|d| (d, 1)).chain(r.warnings().iter().map(|d| (d, 2))) {
        match d.file.as_deref() {
            Some(f) if Some(f) != root.as_deref() => {
                let (line, col) = files.iter().find(|(n, _)| n == f).map_or((1, 1), |(_, src)| line_col(src, d.span.0));
                out.push(diag_json(text, import_span, sev, d.code, &format!("{f}:{line}:{col}: {}", message(d))));
            }
            _ => out.push(diag_json(text, d.span, sev, d.code, &message(d))),
        }
    }
    out
}

/// 正準の整形（`tlvm fmt` と同じ）。構文の誤りがあれば（または検証済み formatter と食い違えば）None。
pub fn format_text(text: &str) -> Option<String> {
    let sp = StaticProfile::default();
    let Parsed::Program(p) = parse_source(text.as_bytes(), &sp) else { return None };
    if needs_glue(&p) || !p.imports.is_empty() {
        return Some(format_program(&p));
    }
    let out = format_program(&p);
    let bare = format_program(&p.unmarked());
    match canonical(&without_rec_markers(text, &p), &sp) {
        Some(o) if o == bare => Some(out),
        _ => None,
    }
}

fn response(id: &str, result: &str) -> String {
    format!("{{\"jsonrpc\":\"2.0\",\"id\":{id},\"result\":{result}}}")
}

fn error(id: &str, code: i64, msg: &str) -> String {
    format!("{{\"jsonrpc\":\"2.0\",\"id\":{id},\"error\":{{\"code\":{code},\"message\":{}}}}}", json_string(msg))
}

fn str_at<'a>(n: &'a JNode, path: &[&str]) -> Option<&'a str> {
    let mut cur = n;
    for k in path {
        cur = cur.get(k)?;
    }
    (cur.kind == JKind::String).then_some(cur.text.as_str())
}

impl Default for Server {
    fn default() -> Self {
        Self::new()
    }
}

impl Server {
    pub fn new() -> Server {
        Server { docs: BTreeMap::new(), initialized: false, shutdown: false }
    }

    fn publish(&self, uri: &str) -> String {
        let (diags, version) = match self.docs.get(uri) {
            Some(d) => {
                let others: BTreeMap<String, String> =
                    self.docs.iter().filter(|(u, _)| u.as_str() != uri).map(|(u, d)| (u.clone(), d.text.clone())).collect();
                (diagnose(uri, &d.text, &others), d.version.clone())
            }
            None => (vec![], None),
        };
        let v = version.map(|v| format!(",\"version\":{v}")).unwrap_or_default();
        format!(
            "{{\"jsonrpc\":\"2.0\",\"method\":\"textDocument/publishDiagnostics\",\"params\":{{\"uri\":{}{v},\"diagnostics\":[{}]}}}}",
            json_string(uri),
            diags.join(",")
        )
    }

    /// 文書が変わったとき：その文書と、ほかの開いている文書（import で依存しうる）の診断を出す。
    fn republish(&self, uri: &str) -> Vec<String> {
        let mut v = vec![self.publish(uri)];
        v.extend(self.docs.keys().filter(|u| u.as_str() != uri).map(|u| self.publish(u)));
        v
    }

    /// 一つの message を処理し、送る message の列を返す。`Some(code)` なら終了する。
    pub fn handle(&mut self, body: &[u8]) -> (Vec<String>, Option<i32>) {
        let msg = match strict_json::parse(body, 512) {
            Ok(m) if m.kind == JKind::Object => m,
            _ => return (vec![error("null", -32700, "parse error")], None),
        };
        let method = str_at(&msg, &["method"]).unwrap_or("").to_string();
        let id = msg.get("id").map(|n| String::from_utf8_lossy(&body[n.start..n.end]).into_owned());
        let empty = JNode { kind: JKind::Null, start: 0, end: 0, text: String::new(), boolean: false, members: vec![], items: vec![] };
        let params = msg.get("params").unwrap_or(&empty);
        let uri = str_at(params, &["textDocument", "uri"]).map(str::to_string);
        if let Some(id) = &id {
            if method.is_empty() {
                // client からの response（server は request を送らないので無視）
                return (vec![], None);
            }
            if !self.initialized && method != "initialize" {
                return (vec![error(id, -32002, "server not initialized")], None);
            }
            if self.shutdown {
                return (vec![error(id, -32600, "server is shut down")], None);
            }
            let out = match method.as_str() {
                "initialize" => {
                    self.initialized = true;
                    response(
                        id,
                        &format!(
                            "{{\"capabilities\":{{\"textDocumentSync\":{{\"openClose\":true,\"change\":1}},\"documentFormattingProvider\":true}},\"serverInfo\":{{\"name\":\"tlvm\",\"version\":{}}}}}",
                            json_string(env!("CARGO_PKG_VERSION"))
                        ),
                    )
                }
                "shutdown" => {
                    self.shutdown = true;
                    response(id, "null")
                }
                "textDocument/formatting" => {
                    let edit = uri.as_ref().and_then(|u| self.docs.get(u)).and_then(|d| {
                        let f = format_text(&d.text)?;
                        Some(if f == d.text {
                            "[]".to_string()
                        } else {
                            format!("[{{\"range\":{},\"newText\":{}}}]", range_json(&d.text, (0, d.text.len())), json_string(&f))
                        })
                    });
                    response(id, edit.as_deref().unwrap_or("null"))
                }
                _ => error(id, -32601, &format!("method not found: {method}")),
            };
            return (vec![out], None);
        }
        // notification
        match method.as_str() {
            "exit" => return (vec![], Some(if self.shutdown { 0 } else { 1 })),
            _ if !self.initialized || self.shutdown => {}
            "textDocument/didOpen" => {
                if let (Some(u), Some(t)) = (uri, str_at(params, &["textDocument", "text"])) {
                    let version = params.get("textDocument").and_then(|d| d.get("version")).map(|n| String::from_utf8_lossy(&body[n.start..n.end]).into_owned());
                    self.docs.insert(u.clone(), Doc { text: t.to_string(), version });
                    return (self.republish(&u), None);
                }
            }
            "textDocument/didChange" => {
                // 全文の同期：最後の変更の text が新しい全文
                let text = params.get("contentChanges").and_then(|c| c.items.last()).and_then(|c| str_at(c, &["text"]));
                if let (Some(u), Some(t)) = (uri, text) {
                    let version = params.get("textDocument").and_then(|d| d.get("version")).map(|n| String::from_utf8_lossy(&body[n.start..n.end]).into_owned());
                    self.docs.insert(u.clone(), Doc { text: t.to_string(), version });
                    return (self.republish(&u), None);
                }
            }
            "textDocument/didClose" => {
                if let Some(u) = uri {
                    self.docs.remove(&u);
                    let mut v = vec![format!(
                        "{{\"jsonrpc\":\"2.0\",\"method\":\"textDocument/publishDiagnostics\",\"params\":{{\"uri\":{},\"diagnostics\":[]}}}}",
                        json_string(&u)
                    )];
                    v.extend(self.docs.keys().map(|o| self.publish(o)));
                    return (v, None);
                }
            }
            _ => {}
        }
        (vec![], None)
    }
}

/// server の本体。`exit` の通知で終わる（`shutdown` の後なら 0、前なら 1）。入力の EOF も同じ。
pub fn serve(input: &mut dyn BufRead, out: &mut dyn Write) -> std::io::Result<i32> {
    let mut s = Server::new();
    loop {
        let body = match read_message(input) {
            Ok(Some(b)) => b,
            Ok(None) => return Ok(if s.shutdown { 0 } else { 1 }),
            // 壊れた header・大きすぎる message の後は区切りが分からないので終わる
            Err(e) => return Err(e),
        };
        let (msgs, exit) = s.handle(&body);
        for m in msgs {
            write_message(out, &m)?;
        }
        if let Some(c) = exit {
            return Ok(c);
        }
    }
}
