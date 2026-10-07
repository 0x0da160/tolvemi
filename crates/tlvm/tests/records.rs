//! v1.1 のレコード型（`type Name = { ... }`、構築、`e.f`、`..base`）。

use std::process::Command;
use tlvm::api::*;
use tlvm::profiles::*;

fn tlvm(args: &[&str]) -> (i32, String, String) {
    let o = Command::new(env!("CARGO_BIN_EXE_tlvm")).args(args).output().unwrap();
    (o.status.code().unwrap(), String::from_utf8(o.stdout).unwrap(), String::from_utf8(o.stderr).unwrap())
}

fn with_file<T>(src: &str, f: impl FnOnce(&str) -> T) -> T {
    static N: std::sync::atomic::AtomicUsize = std::sync::atomic::AtomicUsize::new(0);
    let n = N.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
    let path = std::env::temp_dir().join(format!("tlvm-rec-{}-{n}.tlvm", std::process::id()));
    std::fs::write(&path, src).unwrap();
    let r = f(path.to_str().unwrap());
    std::fs::remove_file(&path).unwrap();
    r
}

fn run(src: &str, input: &str) -> String {
    with_file(src, |p| {
        let (code, out, err) = tlvm(&["run", p, input, "--plain"]);
        assert_eq!(code, 0, "{err}");
        out.trim_end().to_string()
    })
}

fn codes(src: &str) -> Vec<&'static str> {
    match compile(src.as_bytes(), &StaticProfile::default()) {
        SourceCompile::Result(r) => r.errors().iter().map(|d| d.code).collect(),
        _ => vec!["boundary"],
    }
}

const STATS: &str = "type Stats = { count: Int, total: Int, best: Option<Int> }
fn step(s: Stats, x: Int) -> Stats =
  Stats { count: add(s.count, 1), total: add(s.total, x), best: match_option(s.best, some(x), |b| if(lt(b, x), some(x), some(b))) }
fn solve(xs: List<Int>) -> Stats = fold(xs, Stats { count: 0, total: 0, best: none<Int>() }, |acc, x| step(acc, x))
entry solve
";

#[test]
fn construct_access_and_plain_objects() {
    assert_eq!(run(STATS, "[3, 9, 2]"), r#"{"count":3,"total":14,"best":9}"#);
    assert_eq!(run(STATS, "[]"), r#"{"count":0,"total":0,"best":null}"#);
    // 値 JSON（正準出力）は pair の入れ子
    with_file(STATS, |p| {
        let (code, out, _) = tlvm(&["run", p, r#"{"tag":"list","items":[]}"#]);
        assert_eq!(code, 0);
        assert!(out.starts_with(r#"{"tag":"pair","left":{"tag":"int","value":"0"}"#), "{out}");
    });
}

#[test]
fn update_nested_and_single_field() {
    let src = "type P = { a: Int, b: Bool }
type Q = { p: P, n: Int }
type One = { v: Int }
fn solve(q: Q) -> Pair<Q, One> = pair(Q { p: P { b: true, ..q.p }, ..q }, One { v: add(q.p.a, q.n) })
entry solve
";
    assert_eq!(run(src, r#"{"p": {"a": 5, "b": false}, "n": 2}"#), r#"[{"p":{"a":5,"b":true},"n":2},{"v":7}]"#);
    // plain 入力の key の過不足は入力エラー
    with_file(src, |p| {
        let (code, _, err) = tlvm(&["run", p, r#"{"p": {"a": 5}, "n": 2}"#, "--plain"]);
        assert_eq!(code, 1);
        assert!(err.contains("E-INPUT-MISSING-FIELD"), "{err}");
        let (code, _, err) = tlvm(&["run", p, r#"{"p": {"a": 5, "b": true, "c": 1}, "n": 2}"#, "--plain"]);
        assert_eq!(code, 1);
        assert!(err.contains("E-INPUT-UNKNOWN-FIELD"), "{err}");
    });
}

#[test]
fn record_diagnostics() {
    let h = "type P = { a: Int, b: Bool }\n";
    assert_eq!(codes(&format!("{h}fn f(p: P) -> Int = p.c entry f")), ["E-RECORD-UNKNOWN-FIELD"]);
    assert_eq!(codes(&format!("{h}fn f(p: R) -> Int = 1 entry f")), ["E-RECORD-UNKNOWN-TYPE"]);
    assert_eq!(codes(&format!("{h}fn f(x: Int) -> P = P {{ a: x }} entry f")), ["E-RECORD-MISSING-FIELD"]);
    assert_eq!(codes(&format!("{h}fn f(x: Int) -> P = P {{ a: x, a: x, b: true }} entry f")), ["E-RECORD-DUPLICATE-FIELD"]);
    assert_eq!(codes(&format!("{h}type Q = {{ a: Int }}\nfn f(x: Int) -> Int = x entry f")), ["E-RECORD-FIELD-CONFLICT"]);
    assert_eq!(codes(&format!("{h}type P = {{ c: Int }}\nfn f(x: Int) -> Int = x entry f")), ["E-RECORD-DUPLICATE-TYPE"]);
    assert_eq!(codes(&format!("{h}fn f(p: P) -> Int = add(p.b, 1) entry f")), ["E-TYPE-ARG"]);
    assert_eq!(codes(&format!("{h}fn f(x: Int) -> Int = x.a entry f")), ["E-TYPE-FIELD-ACCESS"]);
    // 形が同じでも、型注釈の名前が違えば別のレコード
    assert_eq!(codes(&format!("{h}type Q = {{ c: Int, d: Bool }}\nfn f(q: Q) -> Int = q.a entry f")), ["E-TYPE-FIELD-ACCESS"]);
    // 型は使う前に宣言する（再帰型を作らない）
    assert_eq!(codes("type A = { x: B }\ntype B = { y: Int }\nfn f(x: Int) -> Int = x entry f"), ["E-RECORD-UNKNOWN-TYPE"]);
    // type は宣言の先頭でだけキーワード。名前としては使える
    assert_eq!(codes("fn f(type: Int) -> Int = type entry f"), Vec::<&str>::new());
}

#[test]
fn fmt_and_ast() {
    with_file(STATS, |p| {
        let (code, out, _) = tlvm(&["fmt", p]);
        assert_eq!(code, 0);
        assert!(out.starts_with("type Stats = { count: Int, total: Int, best: Option<Int> }\n"), "{out}");
        assert_eq!(codes(&out), Vec::<&str>::new());
        let (code, out, _) = tlvm(&["ast", p]);
        assert_eq!(code, 0);
        assert!(out.contains(r#""callee":"fst""#), "{out}");
    });
}
