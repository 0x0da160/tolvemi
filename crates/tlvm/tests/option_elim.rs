//! v1.1 の Option 消去（match_option）と安全リスト分解（uncons）。

use std::process::Command;
use tlvm::api::*;
use tlvm::profiles::*;

fn tlvm(args: &[&str]) -> (i32, String, String) {
    let o = Command::new(env!("CARGO_BIN_EXE_tlvm")).args(args).output().unwrap();
    (o.status.code().unwrap(), String::from_utf8(o.stdout).unwrap(), String::from_utf8(o.stderr).unwrap())
}

fn with_file<T>(src: &str, f: impl FnOnce(&str) -> T) -> T {
    let path = std::env::temp_dir().join(format!("tlvm-oe-{}-{}.tlvm", std::process::id(), src.len()));
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
        SourceCompile::SourceBoundaryFailure => panic!("boundary"),
    }
}

const ZIP: &str = "fn solve(p: Pair<List<Int>, List<Int>>) -> List<Int> =
  reverse(fst(fold(fst(p), pair(list[Int](), snd(p)), |acc, x|
    match_option(uncons(snd(acc)), acc, |h|
      pair(cons(add(x, fst(h)), fst(acc)), snd(h))))))
entry solve
";

#[test]
fn uncons_and_match_option_evaluate() {
    let un = "fn f(xs: List<Int>) -> Option<Pair<Int, List<Int>>> = uncons(xs) entry f";
    assert_eq!(run(un, "[]"), "null");
    assert_eq!(run(un, "[1,2,3]"), "[1,[2,3]]");
    assert_eq!(run(un, "[7]"), "[7,[]]");
    let m = "fn f(x: Option<Int>) -> Int = match_option(x, neg(1), |v| add(v, 1)) entry f";
    assert_eq!(run(m, "null"), "-1");
    assert_eq!(run(m, "41"), "42");
    assert_eq!(run(ZIP, "[[1,2,3],[10,20,30]]"), "[11,22,33]");
    assert_eq!(run(ZIP, "[[],[]]"), "[]");
    // 選ばれなかった分岐は評価しない（none 側の uncons 結果を使う式が some 側の束縛を参照しない）
    let head = "fn f(xs: List<Int>) -> Int = match_option(uncons(xs), 0, |c| fst(c)) entry f";
    assert_eq!(run(head, "[5,6]"), "5");
    assert_eq!(run(head, "[]"), "0");
}

#[test]
fn type_errors() {
    assert_eq!(codes("fn f(x: Int) -> Int = match_option(x, 0, |v| v) entry f"), ["E-TYPE-MATCH-SCRUTINEE"]);
    assert_eq!(codes("fn f(x: Option<Int>) -> Int = match_option(x, 0, |v| lt(v, 1)) entry f"), ["E-TYPE-MATCH-BRANCH"]);
    assert_eq!(codes("fn f(x: Option<Int>) -> Bool = match_option(x, 0, |v| v) entry f"), ["E-TYPE-RETURN"]);
    assert_eq!(codes("fn f(x: Int) -> Int = length(uncons(list[Int]())) entry f"), ["E-TYPE-EXPECTED-LIST"]);
    assert_eq!(codes("fn f(x: Int) -> Int = uncons(x, x) entry f"), ["E-ARITY-BUILTIN"]);
    assert_eq!(codes("fn f(x: Option<Int>) -> Int = match_option(x, 0, |v|) entry f")[0], "E-PARSE-EXPECTED-EXPR");
    assert_eq!(codes("fn f(x: Option<Int>) -> Int = match_option(x, 0, v) entry f")[0], "E-PARSE-EXPECTED-TOKEN");
}

#[test]
fn fmt_and_ast_roundtrip() {
    with_file(ZIP, |p| {
        let (code, out, _) = tlvm(&["fmt", p]);
        assert_eq!(code, 0);
        assert!(out.contains("match_option(uncons(snd(acc)), acc, |h| pair("), "{out}");
        let (code, ast, _) = tlvm(&["ast", p]);
        assert_eq!(code, 0);
        assert!(ast.contains(r#"{"tag":"match_option","scrutinee":{"tag":"call","callee":"uncons""#), "{ast}");
        assert!(ast.contains(r#""binder":"h","on_some":"#), "{ast}");
        match compile_ast(ast.trim_end().as_bytes(), &StaticProfile::default(), &AstTransportProfile::default()) {
            AstCompile::Result(r) => assert!(r.errors().is_empty(), "{:?}", r.errors()),
            _ => panic!("transport failure"),
        }
    });
}
