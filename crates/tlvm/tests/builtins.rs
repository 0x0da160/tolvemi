//! v1.1 で加えた組み込み関数（min、max、range、contains、sort）。

use std::process::Command;
use tlvm::api::*;
use tlvm::profiles::*;

fn with_file<T>(src: &str, f: impl FnOnce(&str) -> T) -> T {
    static N: std::sync::atomic::AtomicUsize = std::sync::atomic::AtomicUsize::new(0);
    let n = N.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
    let path = std::env::temp_dir().join(format!("tlvm-bi-{}-{n}.tlvm", std::process::id()));
    std::fs::write(&path, src).unwrap();
    let r = f(path.to_str().unwrap());
    std::fs::remove_file(&path).unwrap();
    r
}

fn run(src: &str, input: &str) -> String {
    with_file(src, |p| {
        let o = Command::new(env!("CARGO_BIN_EXE_tlvm")).args(["run", p, input, "--plain"]).output().unwrap();
        String::from_utf8(o.stdout).unwrap().trim_end().to_string() + &String::from_utf8(o.stderr).unwrap()
    })
}

fn codes(src: &str) -> Vec<&'static str> {
    match compile(src.as_bytes(), &StaticProfile::default()) {
        SourceCompile::Result(r) => r.errors().iter().map(|d| d.code).collect(),
        _ => vec!["boundary"],
    }
}

#[test]
fn values() {
    let f = |body: &str, ty: &str| format!("fn solve(xs: List<Int>) -> {ty} = {body}\nentry solve\n");
    assert_eq!(run(&f("pair(min(3, -2), max(3, -2))", "Pair<Int, Int>"), "[]"), "[-2,3]");
    assert_eq!(run(&f("range(-2, 3)", "List<Int>"), "[]"), "[-2,-1,0,1,2]");
    assert_eq!(run(&f("range(3, 3)", "List<Int>"), "[]"), "[]");
    assert_eq!(run(&f("range(5, 1)", "List<Int>"), "[]"), "[]");
    assert_eq!(run(&f("pair(contains(xs, 5), contains(xs, 4))", "Pair<Bool, Bool>"), "[1, 5, 2]"), "[true,false]");
    assert_eq!(run(&f("sort(xs)", "List<Int>"), "[5, 3, -1, 3, 10, 0]"), "[-1,0,3,3,5,10]");
    assert_eq!(run(&f("sort(xs)", "List<Int>"), "[]"), "[]");
    // contains は等値で比べる任意の要素型に使える
    let src = "fn solve(xs: List<Pair<Int, Bool>>) -> Bool = contains(xs, pair(2, true))\nentry solve\n";
    assert_eq!(run(src, "[[1, true], [2, true]]"), "true");
    // 文脈キーワードなので変数名に使える
    assert_eq!(run(&f("let max = fold(xs, 0, |m, x| max(m, x)) in max", "Int"), "[4, 9, 2]"), "9");
}

#[test]
fn types_and_resources() {
    assert_eq!(codes("fn f(xs: List<Bool>) -> List<Bool> = sort(xs) entry f"), ["E-TYPE-ARG"]);
    assert_eq!(codes("fn f(xs: List<Int>) -> Bool = contains(xs, true) entry f"), ["E-TYPE-ARG"]);
    assert_eq!(codes("fn f(x: Int) -> Bool = contains(x, 1) entry f"), ["E-TYPE-EXPECTED-LIST"]);
    assert_eq!(codes("fn f(x: Int) -> Int = min(x) entry f"), ["E-ARITY-BUILTIN"]);
    assert_eq!(codes("fn min(x: Int) -> Int = x entry min"), ["E-PARSE-EXPECTED-IDENT", "E-PARSE-EXPECTED-IDENT"]);
    // range の大きさは allocated nodes の上限で止まる
    assert!(run("fn f(n: Int) -> Int = length(range(0, n)) entry f", "100000000").contains("AllocatedNodes"));
}
