//! ホスト組み込み API（`tlvm::embed`）のテスト。

use tlvm::embed::{diagnostic_json, Limits, Program, RunError};

const SUM: &str = "fn solve(xs: List<Int>) -> Int = fold(xs, 0, |acc, x| add(acc, x))\nentry solve\n";

#[test]
fn compile_and_run() {
    let p = Program::compile(SUM).expect("accepted");
    assert_eq!(p.entry(), "solve");
    assert_eq!(p.input_type(), "List<Int>");
    assert_eq!(p.output_type(), "Int");
    assert_eq!(p.run_json("[1, 2, 3]").unwrap(), "6");
    assert_eq!(p.run_json("[]").unwrap(), "0");
    // 2^53 を超える整数は十進文字列で出る（入力は十進文字列も受理する）。run_json_exact は number のまま
    assert_eq!(p.run_json(r#"[9007199254740993, "1"]"#).unwrap(), r#""9007199254740994""#);
    assert_eq!(p.run_json_exact(r#"[9007199254740993, "1"]"#).unwrap(), "9007199254740994");
}

#[test]
fn structured_output() {
    let src = "fn f(xs: List<Int>) -> Pair<Int, List<Int>> = pair(length(xs), reverse(xs))\nentry f\n";
    let p = Program::compile(src).unwrap();
    assert_eq!(p.output_type(), "Pair<Int, List<Int>>");
    assert_eq!(p.run_json("[1,2,3]").unwrap(), "[3,[3,2,1]]");

    let src = "fn m(p: Pair<Int, Int>) -> Option<Int> = mod(fst(p), snd(p))\nentry m\n";
    let p = Program::compile(src).unwrap();
    assert_eq!(p.input_type(), "Pair<Int, Int>");
    assert_eq!(p.run_json("[7, 3]").unwrap(), "1");
    assert_eq!(p.run_json("[7, 0]").unwrap(), "null");
}

#[test]
fn compile_error() {
    let errs = Program::compile("fn solve(xs: List<Int>) -> Int = add(xs, 1)\nentry solve\n").unwrap_err();
    assert!(!errs.is_empty());
    assert!(errs.iter().all(|d| d.severity == "error"));
    let line = diagnostic_json(&errs[0]);
    assert!(line.starts_with("{\"severity\":\"error\",\"phase\":"), "{line}");
    assert!(!line.contains('\n'));

    let errs = Program::compile("fn solve(xs: List<Int>) -> Int = \nentry solve\n").unwrap_err();
    assert!(errs.iter().any(|d| d.phase == "parse"), "{:?}", errs.iter().map(diagnostic_json).collect::<Vec<_>>());
}

#[test]
fn input_error() {
    let p = Program::compile(SUM).unwrap();
    for bad in ["[1, true]", "{\"a\":1}", "[1,", "1.5"] {
        match p.run_json(bad) {
            Err(RunError::Input(ds)) => {
                assert!(!ds.is_empty(), "{bad}");
                assert!(RunError::Input(ds).to_string().starts_with("InputError\n{"));
            }
            other => panic!("{bad}: {other:?}"),
        }
    }
}

#[test]
fn resource_exhausted() {
    let p = Program::compile(SUM).unwrap();
    let mut limits = Limits::default();
    limits.execution.steps = 10;
    match p.run_json_with("[1,2,3,4,5,6,7,8,9,10]", &limits) {
        Err(e @ RunError::ResourceExhausted { .. }) => {
            let RunError::ResourceExhausted { kind, limit, observed } = e else { unreachable!() };
            assert_eq!(limit, 10);
            assert!(observed > limit);
            assert!(!kind.is_empty());
            assert!(e.to_string().starts_with("ResourceExhausted "));
        }
        other => panic!("{other:?}"),
    }
}
