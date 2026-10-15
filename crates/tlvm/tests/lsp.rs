//! v1.12 の `tlvm lsp`（差分仕様 §2）。build した binary に JSON-RPC の message を流し、返った message を確かめる。

use std::io::Write;
use std::path::PathBuf;
use std::process::{Command, Stdio};
use tlvm::diagnostics::json_string;
use tlvm::strict_json::{parse, JKind, JNode};

fn frame(body: &str) -> String {
    format!("Content-Length: {}\r\n\r\n{body}", body.len())
}

fn request(id: u32, method: &str, params: &str) -> String {
    frame(&format!(
        "{{\"jsonrpc\":\"2.0\",\"id\":{id},\"method\":\"{method}\",\"params\":{params}}}"
    ))
}

fn notify(method: &str, params: &str) -> String {
    frame(&format!(
        "{{\"jsonrpc\":\"2.0\",\"method\":\"{method}\",\"params\":{params}}}"
    ))
}

fn init() -> String {
    request(1, "initialize", "{\"capabilities\":{}}") + &notify("initialized", "{}")
}

fn bye() -> String {
    request(99, "shutdown", "null") + &notify("exit", "null")
}

fn open(uri: &str, text: &str) -> String {
    notify(
        "textDocument/didOpen",
        &format!(
            "{{\"textDocument\":{{\"uri\":{},\"languageId\":\"tlvm\",\"version\":1,\"text\":{}}}}}",
            json_string(uri),
            json_string(text)
        ),
    )
}

fn change(uri: &str, version: u32, text: &str) -> String {
    notify(
        "textDocument/didChange",
        &format!(
            "{{\"textDocument\":{{\"uri\":{},\"version\":{version}}},\"contentChanges\":[{{\"text\":{}}}]}}",
            json_string(uri),
            json_string(text)
        ),
    )
}

fn format_req(id: u32, uri: &str) -> String {
    request(id, "textDocument/formatting", &format!("{{\"textDocument\":{{\"uri\":{}}},\"options\":{{\"tabSize\":2,\"insertSpaces\":true}}}}", json_string(uri)))
}

/// server を動かし、（終了コード、返った message）を返す。
fn serve(input: &str) -> (i32, Vec<JNode>) {
    let mut child = Command::new(env!("CARGO_BIN_EXE_tlvm"))
        .arg("lsp")
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .unwrap();
    child
        .stdin
        .take()
        .unwrap()
        .write_all(input.as_bytes())
        .unwrap();
    let o = child.wait_with_output().unwrap();
    let mut out = o.stdout.as_slice();
    let mut msgs = vec![];
    while !out.is_empty() {
        let end = out
            .windows(4)
            .position(|w| w == b"\r\n\r\n")
            .expect("header");
        let header = std::str::from_utf8(&out[..end]).unwrap();
        let n: usize = header
            .strip_prefix("Content-Length: ")
            .expect("content-length")
            .parse()
            .unwrap();
        let body = &out[end + 4..end + 4 + n];
        msgs.push(parse(body, 512).expect("json"));
        out = &out[end + 4 + n..];
    }
    (o.status.code().unwrap(), msgs)
}

fn s<'a>(n: &'a JNode, path: &[&str]) -> &'a str {
    let mut c = n;
    for k in path {
        c = c.get(k).unwrap_or_else(|| panic!("no {k}"));
    }
    &c.text
}

fn response(msgs: &[JNode], id: &str) -> JNode {
    msgs.iter()
        .find(|m| {
            m.get("id")
                .is_some_and(|i| i.text == id || (i.kind == JKind::Null && id == "null"))
        })
        .unwrap_or_else(|| panic!("no response {id}"))
        .clone()
}

/// 指定した URI の publishDiagnostics（順に）。
fn published(msgs: &[JNode], uri: &str) -> Vec<Vec<JNode>> {
    msgs.iter()
        .filter(|m| {
            m.get("method")
                .is_some_and(|x| x.text == "textDocument/publishDiagnostics")
        })
        .filter(|m| s(m, &["params", "uri"]) == uri)
        .map(|m| {
            m.get("params")
                .unwrap()
                .get("diagnostics")
                .unwrap()
                .items
                .clone()
        })
        .collect()
}

/// range の (開始行, 開始列, 終了行, 終了列)。
fn range(d: &JNode) -> (usize, usize, usize, usize) {
    let n = |a: &str, b: &str| s(d, &["range", a, b]).parse::<usize>().unwrap();
    (
        n("start", "line"),
        n("start", "character"),
        n("end", "line"),
        n("end", "character"),
    )
}

const URI: &str = "untitled:doc";

#[test]
fn handshake_and_exit_codes() {
    let (code, msgs) = serve(&(init() + &bye()));
    assert_eq!(code, 0);
    let r = response(&msgs, "1");
    assert_eq!(
        s(
            &r,
            &["result", "capabilities", "textDocumentSync", "change"]
        ),
        "1"
    );
    assert!(
        r.get("result")
            .unwrap()
            .get("capabilities")
            .unwrap()
            .get("documentFormattingProvider")
            .unwrap()
            .boolean
    );
    assert_eq!(s(&r, &["result", "serverInfo", "name"]), "tlvm");
    assert_eq!(
        response(&msgs, "99").get("result").unwrap().kind,
        JKind::Null
    );
    // shutdown の前の exit は終了コード 1、EOF も同じ
    assert_eq!(serve(&(init() + &notify("exit", "null"))).0, 1);
    assert_eq!(serve(&init()).0, 1);
    assert_eq!(serve(&(init() + &request(99, "shutdown", "null"))).0, 0);
}

#[test]
fn requests_before_initialize_and_unknown_methods() {
    let (_, msgs) = serve(
        &(request(5, "textDocument/formatting", "{}")
            + &init()
            + &request(6, "textDocument/hover", "{}")
            + &bye()),
    );
    assert_eq!(s(&response(&msgs, "5"), &["error", "code"]), "-32002");
    assert_eq!(s(&response(&msgs, "6"), &["error", "code"]), "-32601");
    // 文字列の id もそのまま返す
    let (_, msgs) = serve(
        &(init()
            + &frame("{\"jsonrpc\":\"2.0\",\"id\":\"abc\",\"method\":\"shutdown\"}")
            + &notify("exit", "null")),
    );
    assert_eq!(
        response(&msgs, "abc").get("result").unwrap().kind,
        JKind::Null
    );
    // JSON として読めなければ parse error
    let (_, msgs) = serve(&(init() + &frame("{oops") + &bye()));
    assert_eq!(s(&response(&msgs, "null"), &["error", "code"]), "-32700");
}

#[test]
fn diagnostics_on_open_and_change() {
    let bad = "fn f(x: Int) -> Int = add(x, true)\nentry f\n";
    let good = "fn f(x: Int) -> Int = add(x, 1)\nentry f\n";
    let (_, msgs) = serve(
        &(init()
            + &open(URI, bad)
            + &change(URI, 2, good)
            + &change(URI, 3, "fn f(x: Int) -> Int = \n")
            + &bye()),
    );
    let p = published(&msgs, URI);
    assert_eq!(p.len(), 3);
    assert_eq!(p[0].len(), 1);
    let d = &p[0][0];
    assert_eq!(s(d, &["code"]), "E-TYPE-ARG");
    assert_eq!(s(d, &["severity"]), "1");
    assert_eq!(s(d, &["source"]), "tlvm");
    assert_eq!(range(d), (0, 29, 0, 33));
    let m = s(d, &["message"]);
    assert!(
        m.contains("(expected Int, found Bool)")
            && m.contains("\nrepair (replace_expression): expression of type Int"),
        "{m}"
    );
    // 誤りのない文書は空の診断
    assert!(p[1].is_empty());
    assert_eq!(s(&p[2][0], &["code"]), "E-PARSE-EXPECTED-EXPR");
    assert_eq!(range(&p[2][0]).0, 1);
    // version を返す
    let versions: Vec<&str> = msgs
        .iter()
        .filter_map(|m| m.get("params")?.get("version"))
        .map(|v| v.text.as_str())
        .collect();
    assert_eq!(versions, ["1", "2", "3"]);
}

#[test]
fn warnings_have_severity_2() {
    let (_, msgs) = serve(
        &(init()
            + &open(
                URI,
                "fn unused(x: Int) -> Int = x\nfn f(x: Int) -> Int = x\nentry f\n",
            )
            + &bye()),
    );
    let p = published(&msgs, URI);
    assert_eq!(s(&p[0][0], &["code"]), "W-UNUSED-FUNCTION");
    assert_eq!(s(&p[0][0], &["severity"]), "2");
    assert_eq!(range(&p[0][0]), (0, 3, 0, 9));
}

#[test]
fn utf16_positions() {
    // 誤りの前に非 ASCII の文字列がある：列は UTF-16 の code unit で数える（日本語は 1 文字 1 単位、😀 は 2 単位）
    let text = "fn f(x: Int) -> String =\n  concat(\"日本語😀\", x)\nentry f\n";
    let (_, msgs) = serve(&(init() + &open(URI, text) + &bye()));
    let d = &published(&msgs, URI)[0][0];
    assert_eq!(s(d, &["code"]), "E-TYPE-EXPECTED-LIST");
    // `  concat("日本語😀", ` は 2 + 7 + 1 + 3 + 2 + 1 + 2 = 18 単位（bytes では 25）
    assert_eq!(range(d), (1, 18, 1, 19));
}

#[test]
fn formatting_edit() {
    let messy = "fn  f(x:Int)->Int=add( x,1 )\nentry   f";
    let canon = "fn f(x: Int) -> Int = add(x, 1)\nentry f\n";
    let (_, msgs) = serve(
        &(init()
            + &open(URI, messy)
            + &format_req(2, URI)
            + &change(URI, 2, canon)
            + &format_req(3, URI)
            + &change(URI, 3, "fn f(x: Int) -> Int = add(x,\n")
            + &format_req(4, URI)
            + &format_req(5, "untitled:nope")
            + &bye()),
    );
    let r = response(&msgs, "2");
    let edits = &r.get("result").unwrap().items;
    assert_eq!(edits.len(), 1);
    assert_eq!(range(&edits[0]), (0, 0, 1, 9));
    assert_eq!(s(&edits[0], &["newText"]), canon);
    // 既に正準なら edit はない
    assert!(response(&msgs, "3").get("result").unwrap().items.is_empty());
    assert_eq!(
        response(&msgs, "3").get("result").unwrap().kind,
        JKind::Array
    );
    // 構文の誤りがあれば null
    assert_eq!(
        response(&msgs, "4").get("result").unwrap().kind,
        JKind::Null
    );
    assert_eq!(
        response(&msgs, "5").get("result").unwrap().kind,
        JKind::Null
    );
}

#[test]
fn formatting_programs_with_records() {
    let (_, msgs) = serve(
        &(init()
            + &open(URI, "type P = {x: Int}\nfn f(p: P) -> Int = p.x\nentry f\n")
            + &format_req(2, URI)
            + &bye()),
    );
    let r = response(&msgs, "2");
    assert_eq!(
        s(&r.get("result").unwrap().items[0], &["newText"]),
        "type P = { x: Int }\nfn f(p: P) -> Int = p.x\nentry f\n"
    );
}

#[test]
fn close_clears_diagnostics() {
    let (_, msgs) = serve(
        &(init()
            + &open(URI, "fn f(x: Int) -> Int = y\nentry f\n")
            + &notify(
                "textDocument/didClose",
                &format!("{{\"textDocument\":{{\"uri\":{}}}}}", json_string(URI)),
            )
            + &bye()),
    );
    let p = published(&msgs, URI);
    assert_eq!(p.len(), 2);
    assert_eq!(s(&p[0][0], &["code"]), "E-NAME-UNBOUND-VARIABLE");
    assert!(p[1].is_empty());
}

struct Dir(PathBuf);

impl Drop for Dir {
    fn drop(&mut self) {
        let _ = std::fs::remove_dir_all(&self.0);
    }
}

#[test]
fn imports_use_open_documents_then_disk() {
    let d = Dir(std::env::temp_dir().join(format!("tlvm-lsp-{}", std::process::id())));
    let _ = std::fs::remove_dir_all(&d.0);
    std::fs::create_dir_all(d.0.join("lib")).unwrap();
    std::fs::write(
        d.0.join("lib/sq.tlvm"),
        "fn sq(x: Int) -> Int = mul(x, x)\n",
    )
    .unwrap();
    std::fs::write(
        d.0.join("lib/broken.tlvm"),
        "fn broken(x: Int) -> Int = true\n",
    )
    .unwrap();
    let base = format!("file://{}", d.0.to_string_lossy().replace(' ', "%20"));
    let main = format!("{base}/main.tlvm");
    let lib = format!("{base}/lib/cube.tlvm");
    let (_, msgs) = serve(
        &(init()
            // lib/cube.tlvm はディスクにない：開いている文書の中身を使う
            + &open(&main, "import \"lib/sq.tlvm\"\nimport \"lib/cube.tlvm\"\nfn f(x: Int) -> Int = add(sq(x), cube(x))\nentry f\n")
            + &open(&lib, "fn cube(x: Int) -> Int = mul(x, mul(x, x))\n")
            + &change(&main, 2, "import \"lib/broken.tlvm\"\nimport \"lib/none.tlvm\"\nfn f(x: Int) -> Int = x\nentry f\n")
            + &change(&main, 3, "import \"lib/broken.tlvm\"\nfn f(x: Int) -> Int = x\nentry f\n")
            + &bye()),
    );
    let p = published(&msgs, &main);
    // 開いた時点では cube.tlvm を開いていないので見つからない。開くと main の診断も出し直す
    assert_eq!(s(&p[0][0], &["code"]), "E-IMPORT-NOT-FOUND");
    assert_eq!(range(&p[0][0]), (1, 7, 1, 22));
    assert!(p[1].is_empty(), "{:?}", p[1]);
    assert_eq!(s(&p[2][0], &["code"]), "E-IMPORT-NOT-FOUND");
    // import したファイルの誤りは根の最初の import の行に、そのファイルの位置を添えて出す
    let d3 = &p[3][0];
    assert_eq!(s(d3, &["code"]), "E-TYPE-RETURN");
    assert_eq!(range(d3), (0, 0, 0, 24));
    assert!(
        s(d3, &["message"]).contains("broken.tlvm:1:28: "),
        "{}",
        s(d3, &["message"])
    );
    // ライブラリ単独では entry がない
    assert_eq!(
        s(&published(&msgs, &lib)[0][0], &["code"]),
        "E-ENTRY-MISSING"
    );
}

#[test]
fn import_in_untitled_document_is_unsupported() {
    let (_, msgs) = serve(
        &(init() + &open(URI, "import \"a.tlvm\"\nfn f(x: Int) -> Int = x\nentry f\n") + &bye()),
    );
    assert_eq!(
        s(&published(&msgs, URI)[0][0], &["code"]),
        "E-IMPORT-UNSUPPORTED"
    );
}
