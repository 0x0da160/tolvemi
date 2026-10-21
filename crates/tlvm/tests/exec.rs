//! v1.3 の入出力ランタイム（`tlvm exec`）。

use std::io::Write;
use std::process::{Command, Stdio};

fn with_file<T>(src: &str, f: impl FnOnce(&str) -> T) -> T {
    static N: std::sync::atomic::AtomicUsize = std::sync::atomic::AtomicUsize::new(0);
    let n = N.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
    let path = std::env::temp_dir().join(format!("tlvm-exec-{}-{n}.tlvm", std::process::id()));
    std::fs::write(&path, src).unwrap();
    let r = f(path.to_str().unwrap());
    std::fs::remove_file(&path).unwrap();
    r
}

/// （終了コード、標準出力、標準エラー）
fn exec(src: &str, args: &[&str], stdin: &[u8]) -> (i32, String, String) {
    with_file(src, |p| {
        let mut c = Command::new(env!("CARGO_BIN_EXE_tlvm"))
            .arg("exec")
            .arg(p)
            .args(args)
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::piped())
            .spawn()
            .unwrap();
        c.stdin.take().unwrap().write_all(stdin).unwrap();
        let o = c.wait_with_output().unwrap();
        (
            o.status.code().unwrap(),
            String::from_utf8(o.stdout).unwrap(),
            String::from_utf8(o.stderr).unwrap(),
        )
    })
}

const UPPER: &str = "fn up(c: Char) -> Char =
  let n = code(c) in
  if(if(le(97, n), le(n, 122), false), match_option(char(sub(n, 32)), c, |u| u), c)
fn solve(s: String) -> String = reverse(fold(s, \"\", |acc, c| cons(up(c), acc)))
entry solve
";

#[test]
fn stdin_to_stdout() {
    assert_eq!(
        exec(UPPER, &[], "héllo\nworld\n".as_bytes()),
        (0, "HéLLO\nWORLD\n".into(), String::new())
    );
    assert_eq!(exec(UPPER, &[], b""), (0, String::new(), String::new()));
}

#[test]
fn args_and_stdin() {
    let src = "fn solve(p: Pair<List<String>, String>) -> String =
  concat(fold(fst(p), \"\", |acc, a| concat(acc, concat(a, \";\"))), concat(\"|\", snd(p)))
entry solve
";
    // FILE より後ろは --plain のような語もプログラムへの引数
    assert_eq!(
        exec(src, &["a", "--plain", "b c"], b"xyz").1,
        "a;--plain;b c;|xyz"
    );
    let count = "fn solve(a: List<String>) -> Int = length(a)\nentry solve\n";
    assert_eq!(exec(count, &["1", "2", "3"], b"").1, "3\n");
}

#[test]
fn non_string_output_is_plain_json() {
    let src = "fn solve(s: String) -> Pair<Int, List<String>> = pair(length(s), list<String>(s, \"\\\"\"))\nentry solve\n";
    assert_eq!(exec(src, &[], b"ab").1, "[2,[\"ab\",\"\\\"\"]]\n");
}

#[test]
fn errors() {
    let (code, _, err) = exec(UPPER, &[], b"\xff");
    assert_eq!(code, 1);
    assert!(err.contains("InvalidUtf8"));
    let (code, _, err) = exec("fn solve(x: Int) -> Int = x\nentry solve\n", &[], b"");
    assert_eq!(code, 64);
    assert!(err.contains("UnsupportedEntry"));
    let (code, _, err) = exec(
        "fn solve(s: String) -> String = s entry solve oops",
        &[],
        b"",
    );
    assert_eq!(code, 1);
    assert!(err.contains("E-PARSE"));
}

#[test]
fn large_input() {
    let text = "ab cd\n".repeat(100_000);
    let (code, out, _) = exec(UPPER, &[], text.as_bytes());
    assert_eq!(code, 0);
    assert_eq!(out, text.to_uppercase());
}
