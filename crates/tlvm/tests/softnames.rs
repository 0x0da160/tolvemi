//! v1.1 の文脈キーワード：組み込み関数と値の構築子の名前を変数・引数・束縛・field の名前に使う。

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
    let path = std::env::temp_dir().join(format!("tlvm-soft-{}-{n}.tlvm", std::process::id()));
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

const SOFT: &str = "type S = { length: Int, pair: Int }
fn f(length: Int, list: List<Int>) -> Int =
  let pair = pair(length, length(list)) in
  let some = S { length: fst(pair), pair: snd(pair) } in
  fold(list, add(some.length, some.pair), |add, none| add(add, none))
fn solve(xs: List<Int>) -> Int = match_option(uncons(xs), 0, |pair| f(fst(pair), snd(pair)))
entry solve
";

#[test]
fn builtin_names_as_variables() {
    assert_eq!(run(SOFT, "[3, 1, 2]"), "8");
    assert_eq!(run(SOFT, "[]"), "0");
    // 付け替え先の名前がすでに使われていても衝突しない
    let src = "fn solve(length_kw: Int) -> Int = let length = add(length_kw, 1) in mul(length, length_kw) entry solve";
    assert_eq!(run(src, "3"), "12");
}

#[test]
fn name_rules_still_apply() {
    // 関数名と entry は呼び出しの名前なので予約語のまま
    assert_eq!(codes("fn length(x: Int) -> Int = x entry length"), ["E-PARSE-EXPECTED-IDENT", "E-PARSE-EXPECTED-IDENT"]);
    // 構文の予約語は使えない
    assert_eq!(codes("fn f(x: Int) -> Int = let in = 1 in x entry f"), ["E-PARSE-EXPECTED-IDENT"]);
    // 名前の規則（シャドー禁止、未束縛）は付け替えの前後で同じ
    assert_eq!(codes("fn f(x: Int) -> Int = let pair = 1 in let pair = 2 in x entry f"), ["E-NAME-SHADOW"]);
    assert_eq!(codes("fn f(x: Int) -> Int = length entry f"), ["E-NAME-UNBOUND-VARIABLE"]);
    assert_eq!(codes("fn f(length: List<Int>) -> Int = length(length) entry f"), Vec::<&str>::new());
}

#[test]
fn fmt_and_ast() {
    with_file(SOFT, |p| {
        let (code, out, _) = tlvm(&["fmt", p]);
        assert_eq!(code, 0);
        assert!(out.contains("|add, none| add(add, none)"), "{out}");
        assert_eq!(codes(&out), Vec::<&str>::new());
        let (code, out, _) = tlvm(&["ast", p]);
        assert_eq!(code, 0);
        assert!(out.contains(r#""name":"length_kw""#), "{out}");
        match compile_ast(out.trim_end().as_bytes(), &StaticProfile::default(), &AstTransportProfile::default()) {
            AstCompile::Result(r) => assert!(r.errors().is_empty(), "{:?}", r.errors()),
            _ => panic!("transport failure"),
        }
    });
}
