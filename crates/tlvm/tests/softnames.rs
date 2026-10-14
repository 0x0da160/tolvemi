//! v1.1 の文脈キーワード：組み込み関数と値の構築子の名前を変数・引数・束縛・field の名前に使う。

use std::process::Command;
use tlvm::api::*;
use tlvm::formatter::encode_ast;
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
    // `_kw` で終わる名前は普通の名前として使える（付け替えはしない）
    let src = "fn solve(length_kw: Int) -> Int = let length = add(length_kw, 1) in mul(length, length_kw) entry solve";
    assert_eq!(run(src, "3"), "12");
}

#[test]
fn name_rules_still_apply() {
    // 関数名と entry は呼び出しの名前なので予約語のまま
    assert_eq!(codes("fn length(x: Int) -> Int = x entry length"), ["E-PARSE-EXPECTED-IDENT", "E-PARSE-EXPECTED-IDENT"]);
    // 構文の予約語は使えない
    assert_eq!(codes("fn f(x: Int) -> Int = let in = 1 in x entry f"), ["E-PARSE-EXPECTED-IDENT"]);
    // 名前の規則（シャドー禁止、未束縛）
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
        // AST の名前には字句表の語を使えないので、付け替えずに拒否する（E-AST-IDENTIFIER）
        let (code, out, err) = tlvm(&["ast", p]);
        assert_eq!(code, 1);
        assert!(out.is_empty(), "{out}");
        assert!(err.contains("\"code\":\"E-AST-IDENTIFIER\"") && err.contains("\"actual\":\"length\""), "{err}");
    });
}

#[test]
fn ast_refuses_keyword_names() {
    // 字句表の語をすべて除く。付け替えず、ソース順で最初の使われ方を診断にする（§4.2）
    let src = "fn f(x: Int) -> Int = let length = x in length entry f";
    let SourceCompile::Result(CompileResult::Accepted { program, .. }) = compile(src.as_bytes(), &StaticProfile::default()) else {
        panic!("not accepted");
    };
    let ds = encode_ast(&program.program).unwrap_err();
    assert_eq!(ds.len(), 1);
    assert_eq!((ds[0].code, ds[0].actual.as_deref()), ("E-AST-IDENTIFIER", Some("length")));
    assert_eq!(&src[ds[0].span.0..ds[0].span.1], "length");
    // 名前を変えれば出せる
    let renamed = src.replace("length", "len");
    let SourceCompile::Result(CompileResult::Accepted { program, .. }) = compile(renamed.as_bytes(), &StaticProfile::default()) else {
        panic!("not accepted");
    };
    assert!(encode_ast(&program.program).is_ok());
}

#[test]
fn entry_as_name() {
    // entry は宣言の先頭でだけキーワード。式の中では変数・束縛・引数の名前に使える
    let src = "fn hit(k: Int, entry: Pair<Int, Int>) -> Bool = eq(fst(entry), k)
fn solve(x: Pair<Int, List<Pair<Int, Int>>>) -> Int =
  fold(snd(x), 0, |acc, entry| if(hit(fst(x), entry), snd(entry), acc))
entry solve
";
    assert_eq!(run(src, "[2, [[1, 10], [2, 20]]]"), "20");
    with_file(src, |p| {
        let (code, out, _) = tlvm(&["fmt", p]);
        assert_eq!(code, 0);
        assert!(out.contains("|acc, entry|"), "{out}");
    });
    // 関数名には使えない
    let c = codes("fn entry(x: Int) -> Int = x entry entry");
    assert!(!c.is_empty() && c.iter().all(|c| *c == "E-PARSE-EXPECTED-IDENT"), "{c:?}");
    // 式が途中で終わったときは、次の entry 宣言を変数と読んでも誤りのまま
    assert!(!codes("fn f(x: Int) -> Int = let y = 1 in\nentry f").is_empty());
}
