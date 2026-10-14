//! v1.8 の組み込み関数 div（正の除数に対する床除算の商。mod と組になる）。

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
    let path = std::env::temp_dir().join(format!("tlvm-div-{}-{n}.tlvm", std::process::id()));
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

fn errors(src: &str) -> Vec<tlvm::diagnostics::Diagnostic> {
    match compile(src.as_bytes(), &StaticProfile::default()) {
        SourceCompile::Result(r) => r.errors().to_vec(),
        SourceCompile::SourceBoundaryFailure => panic!("boundary"),
    }
}

fn codes(src: &str) -> Vec<&'static str> {
    errors(src).iter().map(|d| d.code).collect()
}

const DIV: &str = "fn f(p: Pair<Int, Int>) -> Option<Int> = div(fst(p), snd(p))\nentry f\n";

#[test]
fn floor_quotient() {
    assert_eq!(run(DIV, "[7, 2]"), "3");
    assert_eq!(run(DIV, "[-7, 2]"), "-4");
    assert_eq!(run(DIV, "[6, 3]"), "2");
    assert_eq!(run(DIV, "[-6, 3]"), "-2");
    assert_eq!(run(DIV, "[0, 5]"), "0");
    assert_eq!(run(DIV, "[4, 9]"), "0");
    assert_eq!(run(DIV, "[-1, 9]"), "-1");
    // 除数が 0 以下なら none（mod と同じ）
    assert_eq!(run(DIV, "[7, 0]"), "null");
    assert_eq!(run(DIV, "[7, -2]"), "null");
    assert_eq!(run(DIV, "[-7, -2]"), "null");
}

#[test]
fn big_integers() {
    // 大きい整数は plain JSON では文字列で出る
    let a = "123456789012345678901234567890123456789";
    assert_eq!(run(DIV, &format!("[\"{a}\", 1000000000]")), "\"123456789012345678901234567890\"");
    assert_eq!(run(DIV, &format!("[\"-{a}\", 1000000000]")), "\"-123456789012345678901234567891\"");
    assert_eq!(run(DIV, &format!("[\"{a}\", \"{a}\"]")), "1");
    assert_eq!(run(DIV, &format!("[1, \"{a}\"]")), "0");
}

#[test]
fn div_mod_identity() {
    // a = q * b + r、0 <= r < b
    let src = "fn f(p: Pair<Int, Int>) -> Bool =
  match_option(div(fst(p), snd(p)), false, |q| match_option(mod(fst(p), snd(p)), false, |r|
    if(eq(add(mul(q, snd(p)), r), fst(p)), if(le(0, r), lt(r, snd(p)), false), false)))
entry f
";
    for (a, b) in [(7, 2), (-7, 2), (0, 1), (13, 13), (-13, 13), (100, 7), (-100, 7), (5, 11), (-5, 11)] {
        assert_eq!(run(src, &format!("[{a}, {b}]")), "true", "{a} {b}");
    }
}

#[test]
fn types() {
    assert!(codes(DIV).is_empty());
    assert_eq!(codes("fn f(x: Int) -> Int = div(x, 2) entry f"), ["E-TYPE-RETURN"]);
    assert_eq!(codes("fn f(x: Bool) -> Option<Int> = div(x, 2) entry f"), ["E-TYPE-ARG"]);
    assert_eq!(codes("fn f(x: Int) -> Option<Int> = div(x) entry f"), ["E-ARITY-BUILTIN"]);
}

#[test]
fn soft_name() {
    // 変数名には使える
    let src = "fn f(x: Int) -> Int = let div = add(x, 1) in match_option(div(div, 2), 0, |q| q) entry f";
    assert_eq!(run(src, "9"), "5");
    assert_eq!(run("fn f(div: Int) -> Int = mul(div, 2) entry f", "4"), "8");
    // 関数名には使えない
    assert_eq!(codes("fn div(x: Int) -> Int = x entry div"), ["E-PARSE-EXPECTED-IDENT", "E-PARSE-EXPECTED-IDENT"]);
}

#[test]
fn fmt_round_trip() {
    let src = "fn f(div: Pair<Int, Int>) -> Option<Int> =   div( fst(div),snd(div) )\nentry   f\n";
    with_file(src, |p| {
        let (code, out, err) = tlvm(&["fmt", p]);
        assert_eq!(code, 0, "{err}");
        assert!(out.contains("div(fst(div), snd(div))"), "{out}");
        assert!(codes(&out).is_empty());
        with_file(&out, |q| {
            let (code, again, _) = tlvm(&["fmt", q]);
            assert_eq!(code, 0);
            assert_eq!(again, out);
        });
        // 字句表の語を変数名に使った AST は拒否する（§4.2）。組込みの div の呼出しは、変数名を変えれば受理される
        let (code, ast, err) = tlvm(&["ast", p]);
        assert_eq!(code, 1);
        assert!(ast.is_empty() && err.contains("E-AST-IDENTIFIER"), "{err}");
        let renamed = "fn f(d: Pair<Int, Int>) -> Option<Int> = div(fst(d), snd(d))\nentry f\n";
        with_file(renamed, |q| {
            let (code, ast, _) = tlvm(&["ast", q]);
            assert_eq!(code, 0);
            assert!(ast.contains(r#""callee":"div""#), "{ast}");
            match compile_ast(ast.trim_end().as_bytes(), &StaticProfile::default(), &AstTransportProfile::default()) {
                AstCompile::Result(r) => assert!(r.errors().is_empty(), "{:?}", r.errors()),
                _ => panic!("transport failure"),
            }
        });
    });
}

#[test]
fn slash_hint() {
    let ds = errors("fn f(x: Int) -> Int = x / 2 entry f");
    assert_eq!(ds[0].code, "E-LEX-UNEXPECTED-CHARACTER");
    let r = ds[0].repair.as_ref().unwrap();
    assert!(r.constraint.contains("div(a, b)"), "{}", r.constraint);
    // 他の文字には付けない
    let ds = errors("fn f(x: Int) -> Int = x @ 2 entry f");
    assert_eq!(ds[0].code, "E-LEX-UNEXPECTED-CHARACTER");
    assert!(ds[0].repair.is_none());
}
