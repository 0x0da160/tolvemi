//! v1.6 の上限つき反復 `loop(init, max, |s| e)`（差分仕様 §1〜§3）。

use std::io::Write;
use std::process::{Command, Stdio};
use tlvm::api::*;
use tlvm::checker::check_program;
use tlvm::formatter::format_program;
use tlvm::profiles::*;

fn tlvm(args: &[&str]) -> (i32, String, String) {
    let o = Command::new(env!("CARGO_BIN_EXE_tlvm")).args(args).output().unwrap();
    (o.status.code().unwrap(), String::from_utf8(o.stdout).unwrap(), String::from_utf8(o.stderr).unwrap())
}

fn with_file<T>(src: &str, ext: &str, f: impl FnOnce(&str) -> T) -> T {
    static N: std::sync::atomic::AtomicUsize = std::sync::atomic::AtomicUsize::new(0);
    let n = N.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
    let path = std::env::temp_dir().join(format!("tlvm-loop-{}-{n}.{ext}", std::process::id()));
    std::fs::write(&path, src).unwrap();
    let r = f(path.to_str().unwrap());
    std::fs::remove_file(&path).unwrap();
    r
}

/// plain JSON で実行した（終了コード、出力）。
fn run_code(src: &str, input: &str) -> (i32, String) {
    with_file(src, "tlvm", |p| {
        let (code, out, err) = tlvm(&["run", p, input, "--plain"]);
        (code, format!("{}{}", out.trim_end(), err.trim_end()))
    })
}

/// plain JSON で実行した出力。
fn run(src: &str, input: &str) -> String {
    let (code, out) = run_code(src, input);
    assert_eq!(code, 0, "{out}");
    out
}

fn compiled(src: &str) -> CompileResult {
    match compile(src.as_bytes(), &StaticProfile::default()) {
        SourceCompile::Result(r) => r,
        _ => panic!("boundary"),
    }
}

fn codes(src: &str) -> Vec<&'static str> {
    compiled(src).errors().iter().map(|d| d.code).collect()
}

fn accepted(src: &str) -> tlvm::checker::TypedProgram {
    match compiled(src) {
        CompileResult::Accepted { program, .. } => program,
        r => panic!("rejected: {:?}", r.errors()),
    }
}

/// 検証済み部品へ渡す、書き換え後のソース。
fn lowered(src: &str) -> String {
    let p = match parse_source(src.as_bytes(), &StaticProfile::default()) {
        Parsed::Program(p) => p,
        _ => panic!("parse"),
    };
    let px = expand(&p).unwrap();
    let o = check_program(&px, src.len(), &StaticProfile::default());
    assert!(o.typed.is_some(), "{:?}", o.diagnostics);
    format_program(&lower(&tlvm::hof::lower(&px, &o.hof)))
}

// ---------------------------------------------------------------- 型と評価

/// 差分仕様 §1 の例（上限を引数にする）。
const DOUBLING: &str = "fn f(n: Int) -> Option<Int> = loop(1, n, |x| if(lt(x, 1000), some(mul(x, 2)), none<Int>()))
entry f
";

#[test]
fn stop_and_exhaust() {
    // 止まったときはその時点の状態：1 を 10 回倍にして 1024、11 回目の本体で止まる
    assert_eq!(run(DOUBLING, "64"), "1024");
    assert_eq!(run(DOUBLING, "11"), "1024");
    // 本体を max 回評価しても止まらなければ none
    assert_eq!(run(DOUBLING, "10"), "null");
    assert_eq!(run(DOUBLING, "1"), "null");
    // max <= 0 なら none
    assert_eq!(run(DOUBLING, "0"), "null");
    assert_eq!(run(DOUBLING, "-7"), "null");
    // 最初の歩で止まれば some(init)
    assert_eq!(run("fn f(n: Int) -> Option<Int> = loop(n, 5, |x| none<Int>()) entry f", "42"), "42");
    assert_eq!(accepted(DOUBLING).output_type.to_string(), "Option<Int>");
}

#[test]
fn result_types() {
    let ty = |body: &str, t: &str| {
        let p = accepted(&format!("fn f(xs: List<Int>) -> {t} = {body} entry f"));
        assert_eq!(p.output_type.to_string(), t);
    };
    ty("loop(xs, 3, |s| some(s))", "Option<List<Int>>");
    ty("loop(pair(0, true), 3, |s| none<Pair<Int, Bool>>())", "Option<Pair<Int, Bool>>");
    ty(r#"loop("", 3, |s| some(concat(s, "a")))"#, "Option<String>");
    // 状態は Pair でも：Fibonacci で 100 を超える最初の項と、その番号
    let fib = "fn f(n: Int) -> Option<Pair<Int, Pair<Int, Int>>> =
  loop(pair(0, pair(0, 1)), n, |s| if(lt(100, fst(snd(s))), none<Pair<Int, Pair<Int, Int>>>(),
    some(pair(add(fst(s), 1), pair(snd(snd(s)), add(fst(snd(s)), snd(snd(s))))))))
entry f
";
    assert_eq!(run(fib, "50"), "[12,[144,233]]");
    assert_eq!(run(fib, "12"), "null");
    // 本体は外側の変数を参照できる
    let outer = "fn f(p: Pair<Int, Int>) -> Option<Int> = loop(0, 100, |s| if(lt(s, fst(p)), some(add(s, snd(p))), none<Int>())) entry f";
    assert_eq!(run(outer, "[10, 3]"), "12");
}

#[test]
fn body_not_evaluated_after_stop_or_without_steps() {
    // 状態 3 で本体を評価すると 30 万個の node を作る。止まった後の歩でも本体を評価すれば資源（100 万 node）を使い切る
    let heavy = "fn heavy(s: Int) -> Option<Int> =
  if(lt(s, 3), some(add(s, 1)), if(lt(0, length(range(0, 300000))), none<Int>(), none<Int>()))
";
    let src = format!("{heavy}fn f(n: Int) -> Option<Int> = loop(0, n, |s| heavy(s))\nentry f\n");
    assert_eq!(run(&src, "100"), "3");
    // 対照：同じ本体を毎歩評価する fold は資源を使い切る
    let every = format!("{heavy}fn f(n: Int) -> Int = fold(range(0, n), 0, |acc, i| match_option(heavy(3), acc, |v| v))\nentry f\n");
    let (code, out) = run_code(&every, "100");
    assert_eq!(code, 2, "{out}");
    assert!(out.contains("ResourceExhausted"), "{out}");
    // max <= 0 なら本体を評価しない（評価すれば range(0, 10^12) で資源を使い切る）
    let huge = "fn f(n: Int) -> Option<Int> = loop(5, n, |s| if(lt(0, length(range(0, 1000000000000))), none<Int>(), some(s))) entry f";
    assert_eq!(run(huge, "0"), "null");
    assert_eq!(run(huge, "-1"), "null");
    let (code, out) = run_code(huge, "1");
    assert_eq!(code, 2, "{out}");
}

#[test]
fn nesting() {
    // loop の本体に loop：各 k について 2^m >= k となる最小の m
    let nested = "fn f(n: Int) -> Option<Int> =
  loop(0, n, |k| match_option(loop(pair(1, 0), 64, |p| if(lt(fst(p), k), some(pair(mul(fst(p), 2), add(snd(p), 1))), none<Pair<Int, Int>>())), none<Int>(),
    |q| if(lt(snd(q), 4), some(add(k, 1)), none<Int>())))
entry f
";
    // k = 0..8 の m は 0,0,1,2,2,3,3,3,3：m が 4 になる最初の k は 9
    assert_eq!(run(nested, "100"), "9");
    assert_eq!(run(nested, "5"), "null");
    // map の本体に loop、loop の本体に map・all、max に loop
    let mixed = "fn solve(xs: List<Int>) -> Pair<List<Int>, Option<List<Int>>> =
  pair(map(xs, |x| match_option(loop(x, 50, |v| if(lt(v, 10), none<Int>(), some(sub(v, 7)))), -1, |v| v)),
    loop(xs, match_option(loop(0, 10, |c| if(lt(c, 3), some(add(c, 1)), none<Int>())), 0, |c| c), |ys|
      if(all(ys, |y| eq(y, 0)), none<List<Int>>(), some(map(ys, |y| max(0, sub(y, 1)))))))
entry solve
";
    // 上限は 3：3 歩で全部 0 になっても、それを確かめる 4 回目の本体は評価されないので none
    assert_eq!(run(mixed, "[35, 7, 120]"), "[[7,7,8],null]");
    assert_eq!(run(mixed, "[2, 1, 0]"), "[[2,1,0],[0,0,0]]");
    assert_eq!(run(mixed, "[3, 1, 0]"), "[[3,1,0],null]");
    // init に loop と map
    let init = "fn f(xs: List<Int>) -> Option<Int> =
  loop(match_option(loop(length(map(xs, |x| x)), 5, |n| none<Int>()), 0, |n| n), 100, |s| if(lt(s, 20), some(mul(s, 3)), none<Int>()))
entry f
";
    assert_eq!(run(init, "[1, 2]"), "54");
    assert_eq!(run(init, "[]"), "null");
}

#[test]
fn records_and_sums() {
    // 状態がレコード、本体で直和型と match を使う
    let src = "type Acc = { n: Int, steps: Int, log: List<Int> }
type Step = Done | Next(Int)
fn step(n: Int) -> Step = if(eq(n, 1), Done, if(lt(n, 5), Next(sub(n, 1)), Next(sub(n, 4))))
fn solve(n: Int) -> Option<Acc> =
  loop(Acc { n: n, steps: 0, log: list<Int>() }, 10, |a| match step(a.n) {
    Done => none<Acc>(),
    Next(m) => some(Acc { n: m, steps: add(a.steps, 1), log: cons(a.n, a.log) }),
  })
entry solve
";
    assert_eq!(run(src, "1"), r#"{"n":1,"steps":0,"log":[]}"#);
    assert_eq!(run(src, "11"), r#"{"n":1,"steps":4,"log":[2,3,7,11]}"#);
    assert_eq!(run(src, "100"), "null");
    // 直和型を状態にする
    let sum = "type S = Go(Int) | Stop(Int)
fn f(n: Int) -> Option<S> = loop(Go(n), 10, |s| match s { Go(k) => some(if(lt(k, 3), Stop(k), Go(sub(k, 3)))), Stop(k) => none<S>() })
entry f
";
    assert_eq!(run(sum, "10"), r#"{"Stop":[1]}"#);
    assert_eq!(run(sum, "100"), "null");
}

#[test]
fn names() {
    // loop は文脈キーワード：変数・引数・binder・field の名前に使える（直後が `(` のときだけ特殊形式）
    let soft = "type R = { loop: Int }
fn solve(loop: Int) -> Pair<Option<Int>, R> =
  let max = 5 in
  pair(loop(loop, max, |map| if(lt(map, 10), some(add(map, loop)), none<Int>())), R { loop: loop })
entry solve
";
    assert_eq!(run(soft, "3"), r#"[12,{"loop":3}]"#);
    // 書き換えで導入する名前（hof1 など）は、プログラム中の名前と重ならない
    let clash = "fn hof3(hof1: Int) -> Option<Int> = let hof2 = 1 in loop(hof1, 10, |hof4| if(lt(hof4, 5), some(add(hof4, hof2)), none<Int>())) entry hof3";
    assert_eq!(run(clash, "0"), "5");
    // 関数名と entry の名前には使えない
    assert_eq!(codes("fn loop(x: Int) -> Int = x entry loop"), ["E-PARSE-EXPECTED-IDENT", "E-PARSE-EXPECTED-IDENT"]);
    // binder：外側の名前をシャドーできず、本体の外では見えない
    let c = |body: &str| codes(&format!("fn f(n: Int) -> Option<Int> = {body} entry f"));
    assert_eq!(c("loop(0, n, |n| none<Int>())"), ["E-NAME-SHADOW"]);
    assert_eq!(c("loop(0, n, |s| loop(s, n, |s| none<Int>()))"), ["E-NAME-SHADOW"]);
    assert_eq!(c("loop(s, n, |s| none<Int>())"), ["E-NAME-UNBOUND-VARIABLE"]);
    assert_eq!(c("loop(0, s, |s| none<Int>())"), ["E-NAME-UNBOUND-VARIABLE"]);
    // 兄弟の loop では同じ binder の名前を使える
    assert!(c("match_option(loop(0, n, |s| none<Int>()), loop(1, n, |s| none<Int>()), |v| some(v))").is_empty());
    // 名前の候補に loop も出す
    let d = compiled("fn f(n: Int) -> Int = lop(n) entry f").errors()[0].clone();
    assert_eq!(d.code, "E-NAME-UNKNOWN-FUNCTION");
    assert!(d.repair.as_ref().unwrap().constraint.contains("loop"), "{d:?}");
}

#[test]
fn lowering_uses_fold_and_passes_verified_formatter() {
    let text = lowered(DOUBLING);
    assert!(!text.contains("loop("), "{text}");
    assert!(
        text.contains(
            "match_result(fold(range(0, n), ok<Int, Int>(1), |hof1, hof2| match_result(hof1, |x| match_option(if(lt(x, 1000), some(mul(x, 2)), none<Int>()), err<Int, Int>(x), |hof3| ok<Int, Int>(hof3)), |hof4| err<Int, Int>(hof4))), |hof5| none<Int>(), |hof4| some(hof4))"
        ),
        "{text}"
    );
    assert_eq!(canonical(&text, &StaticProfile::default()).as_deref(), Some(text.as_str()));
    // 入れ子でも本体はソースに一度だけ現れる（書き換え後のソースは入れ子の深さに比例する大きさ）
    let mut body = "none<Int>()".to_string();
    for i in (1..=12).rev() {
        body = format!("loop(s{}, 3, |s{i}| {body})", i - 1);
    }
    let deep = format!("fn f(s0: Int) -> Option<Int> = {body} entry f");
    let text = lowered(&deep);
    assert!(text.len() < 40 * deep.len(), "{} vs {}", text.len(), deep.len());
    assert_eq!(canonical(&text, &StaticProfile::default()).as_deref(), Some(text.as_str()));
    // 一番内側の loop は some、その外は本体が some のままなので none、…と交互になり、12 段目の外側は none
    assert_eq!(run(&deep, "0"), "null");
    // レコード・直和型と一緒でも、書き換え後のソースは検証済み formatter の正準形
    let mixed = "type P = { a: Int, b: Int }
type S = X(Int) | Y
fn classify(a: Int) -> S = if(lt(a, 10), X(a), Y)
fn f(p: P) -> Option<P> = loop(p, p.b, |q| match classify(q.a) { X(a) => some(P { a: add(a, 1), ..q }), Y => none<P>() })
entry f
";
    let text = lowered(mixed);
    assert!(text.contains("fold(range(0, ") && !text.contains("loop("), "{text}");
    assert_eq!(canonical(&text, &StaticProfile::default()).as_deref(), Some(text.as_str()));
    assert_eq!(run(mixed, r#"{"a": 3, "b": 100}"#), r#"{"a":10,"b":100}"#);
    assert_eq!(run(mixed, r#"{"a": 3, "b": 7}"#), "null");
}

// ---------------------------------------------------------------- 診断

#[test]
fn diagnostics() {
    let c = |body: &str| codes(&format!("fn f(xs: List<Int>, n: Int) -> Option<Int> = {body} entry g fn g(x: Int) -> Option<Int> = f(list<Int>(), x)"));
    assert_eq!(c("loop(0, xs, |s| some(s))"), ["E-TYPE-LOOP-MAX"]);
    assert_eq!(c("loop(0, true, |s| some(s))"), ["E-TYPE-LOOP-MAX"]);
    assert_eq!(c("loop(0, n, |s| s)"), ["E-TYPE-LOOP-BODY"]);
    assert_eq!(c("loop(0, n, |s| some(eq(s, 1)))"), ["E-TYPE-LOOP-BODY"]);
    assert_eq!(c("loop(0, n, |s| none<Bool>())"), ["E-TYPE-LOOP-BODY"]);
    assert_eq!(c("loop(0, xs, |s| s)"), ["E-TYPE-LOOP-MAX", "E-TYPE-LOOP-BODY"]);
    assert_eq!(c("loop(true, n, |s| some(s))"), ["E-TYPE-RETURN"]);
    // init が型の誤りなら、本体の型の誤りは重ねて出さない
    assert_eq!(c("loop(add(true, 1), n, |s| s)"), ["E-TYPE-ARG"]);
    // 期待した型と実際の型
    let d = |body: &str| {
        let src = format!("fn f(xs: List<Int>, n: Int) -> Option<Int> = {body}\nentry g\nfn g(x: Int) -> Option<Int> = f(list<Int>(), x)\n");
        compiled(&src).errors()[0].clone()
    };
    let e = d("loop(0, n, |s| s)");
    assert_eq!((e.phase, e.expected.as_deref(), e.actual.as_deref()), ("typecheck", Some("Option<Int>"), Some("Int")));
    assert_eq!(e.repair.as_ref().unwrap().constraint, "expression of type Option<Int>");
    let e = d("loop(0, xs, |s| some(s))");
    assert_eq!((e.phase, e.expected.as_deref(), e.actual.as_deref()), ("typecheck", Some("Int"), Some("List<Int>")));
    assert_eq!(e.repair.as_ref().unwrap().constraint, "expression of type Int");
    // 第 3 引数がラムダでない
    assert_eq!(c("loop(0, n, step)"), ["E-PARSE-EXPECTED-LAMBDA"]);
    assert_eq!(c("loop(0, n, some(1))"), ["E-PARSE-EXPECTED-LAMBDA"]);
    assert_eq!(c("loop(0, n)"), ["E-PARSE-EXPECTED-LAMBDA"]);
    assert_eq!(c("loop(0, n, |acc, s| none<Int>())"), ["E-PARSE-EXPECTED-LAMBDA"]);
    assert_eq!(c("loop(0, n, || none<Int>())"), ["E-PARSE-EXPECTED-LAMBDA"]);
    assert_eq!(c("loop(0, |s| none<Int>())"), ["E-PARSE-EXPECTED-EXPR"]);
    assert_eq!(c("loop(0, n, |s| none<Int>(), 1)"), ["E-PARSE-EXPECTED-TOKEN"]);
}

#[test]
fn lambda_repair_hints() {
    let first = |body: &str| {
        let src = format!("fn step(s: Int) -> Option<Int> = none<Int>()\nfn f(n: Int) -> Option<Int> = {body}\nentry f\n");
        let d = compiled(&src).errors()[0].clone();
        assert_eq!(d.code, "E-PARSE-EXPECTED-LAMBDA");
        assert_eq!(d.phase, "parse");
        let r = d.repair.clone().expect("repair");
        (d, r)
    };
    let (d, r) = first("loop(0, n, step)");
    assert_eq!(d.expected.as_deref(), Some("|s| e"));
    assert_eq!(d.actual.as_deref(), Some("step"));
    assert_eq!(r.kind, "replace_expression");
    assert!(r.constraint.starts_with("|s| step(s)") && r.constraint.contains("state"), "{}", r.constraint);
    let (_, r) = first("loop(0, n, step(s))");
    assert_eq!(r.kind, "insert_text");
    assert!(r.constraint.contains("'|s| '") && r.constraint.contains("loop(init, max, |s| e)"), "{}", r.constraint);
    let (d, r) = first("loop(0, n)");
    assert_eq!(d.actual.as_deref(), Some(")"));
    assert_eq!((r.kind, r.target_span.0, r.target_span.1), ("insert_text", d.span.0, d.span.0));
    assert!(r.constraint.contains("third argument"), "{}", r.constraint);
    let (d, r) = first("loop(0, n, |acc, s| none<Int>())");
    assert_eq!(d.actual.as_deref(), Some(","));
    assert!(r.constraint.contains("exactly one binder") && r.constraint.contains("state"), "{}", r.constraint);
    // map などの修復ヒントは従来どおり
    let src = "fn f(xs: List<Int>) -> List<Int> = map(xs, neg)\nentry f\n";
    let r = compiled(src).errors()[0].repair.clone().unwrap();
    assert!(r.constraint.starts_with("|x| neg(x)"), "{}", r.constraint);
}

#[test]
fn ast_codec_tag() {
    let src = "fn f(loop: Int) -> Option<Int> = loop(loop, 10, |max| if(lt(max, 5), some(add(max, 1)), none<Int>())) entry f";
    with_file(src, "tlvm", |p| {
        let (code, ast, err) = tlvm(&["ast", p]);
        assert_eq!(code, 0, "{err}");
        // tag は loop、field は init・max・binder・body。文脈キーワードの変数名は付け替える
        assert!(ast.contains(r#"{"tag":"loop","init":{"tag":"var","name":"loop_kw"},"max":{"tag":"int","value":"10"},"binder":"max_kw","body":"#), "{ast}");
        with_file(ast.trim_end(), "json", |j| {
            let (code, out, err) = tlvm(&["run", j, "2", "--plain"]);
            assert_eq!(code, 0, "{err}");
            assert_eq!(out.trim_end(), "5");
            let (code, fmt, _) = tlvm(&["fmt", j]);
            assert_eq!(code, 0);
            assert!(fmt.contains("loop(loop_kw, 10, |max_kw| "), "{fmt}");
        });
    });
    let ast = |body: &str| {
        format!(
            r#"{{"codec":"ast_codec_v1","declarations":[{{"tag":"fn","name":"f","params":[{{"name":"n","type":{{"tag":"int"}}}}],"return_type":{{"tag":"option","element":{{"tag":"int"}}}},"body":{body}}},{{"tag":"entry","name":"f"}}]}}"#
        )
    };
    let ast_codes = |body: &str| match compile_ast(ast(body).as_bytes(), &StaticProfile::default(), &AstTransportProfile::default()) {
        AstCompile::Result(r) => r.errors().iter().map(|d| d.code).collect::<Vec<_>>(),
        AstCompile::AstInvalid(d) => d.iter().map(|d| d.code).collect(),
        AstCompile::AstBoundaryFailure => vec!["boundary"],
    };
    let n = r#"{"tag":"var","name":"n"}"#;
    let none = r#"{"tag":"none","element_type":{"tag":"int"}}"#;
    assert!(ast_codes(&format!(r#"{{"tag":"loop","init":{n},"max":{n},"binder":"s","body":{none}}}"#)).is_empty());
    assert_eq!(ast_codes(&format!(r#"{{"tag":"loop","init":{n},"binder":"s","body":{none}}}"#)), ["E-AST-MISSING-FIELD"]);
    assert_eq!(ast_codes(&format!(r#"{{"tag":"loop","init":{n},"max":{n},"binder":"loop","body":{none}}}"#)), ["E-AST-IDENTIFIER"]);
    assert_eq!(ast_codes(&format!(r#"{{"tag":"loop","init":{n},"max":{n},"list":{n},"binder":"s","body":{none}}}"#)), ["E-AST-UNKNOWN-FIELD"]);
    assert_eq!(ast_codes(&format!(r#"{{"tag":"loop","init":{n},"max":{n},"binder":"s","body":{n}}}"#)), ["E-TYPE-LOOP-BODY"]);
    assert_eq!(
        ast_codes(&format!(r#"{{"tag":"loop","init":{n},"max":{{"tag":"bool","value":true}},"binder":"s","body":{none}}}"#)),
        ["E-TYPE-LOOP-MAX"]
    );
}

// ---------------------------------------------------------------- tlvm fmt・test・exec

#[test]
fn fmt_round_trip() {
    let src = "// 1000 以上になるまで倍にする
fn f(n: Int) -> Option<Int> = loop(1, n, |x|
    if(lt(x, 1000), some(mul(x, 2)),
      none<Int>()))
entry f
";
    with_file(src, "tlvm", |p| {
        let (code, out, err) = tlvm(&["fmt", p]);
        assert_eq!(code, 0, "{err}");
        assert_eq!(out, DOUBLING);
    });
    with_file(DOUBLING, "tlvm", |p| {
        let (code, out, _) = tlvm(&["fmt", p]);
        assert_eq!(code, 0);
        assert_eq!(out, DOUBLING);
    });
    // loop を変数名に使い、呼ばないプログラムは従来どおり検証済み formatter
    let plain = "fn f(loop: Int) -> Int = add(loop, 1)\nentry f\n";
    with_file(plain, "tlvm", |p| {
        let (code, out, err) = tlvm(&["fmt", p]);
        assert_eq!(code, 0, "{err}");
        assert_eq!(out, plain);
    });
}

#[test]
fn cli_test_and_exec() {
    with_file(DOUBLING, "tlvm", |p| {
        let cases = r#"[{"name": "stops", "input": 64, "expected": 1024}, {"name": "limit", "input": 10, "expected": null}, {"name": "zero", "input": 0, "expected": null}]"#;
        with_file(cases, "json", |c| {
            let (code, out, err) = tlvm(&["test", p, c]);
            assert_eq!(code, 0, "{out}{err}");
            assert!(out.contains(r#"{"passed":3,"failed":0}"#), "{out}");
        });
    });
    // exec：標準入力の数から 1 になるまでの Collatz の歩数
    let collatz = r#"fn next(n: Int) -> Int = match_option(mod(n, 2), n, |r| if(eq(r, 0), fold(range(0, n), 0, |h, i| if(eq(add(i, i), n), i, h)), add(mul(3, n), 1)))
fn solve(text: String) -> String =
  match_option(parse_int(filter(text, |c| if(eq(c, '\n'), false, true))), "bad\n", |n|
    match_option(loop(pair(n, 0), 1000, |s| if(eq(fst(s), 1), none<Pair<Int, Int>>(), some(pair(next(fst(s)), add(snd(s), 1))))),
      "limit\n", |s| concat(to_string(snd(s)), "\n")))
entry solve
"#;
    with_file(collatz, "tlvm", |p| {
        let exec = |input: &[u8]| {
            let mut c = Command::new(env!("CARGO_BIN_EXE_tlvm"))
                .args(["exec", p])
                .stdin(Stdio::piped())
                .stdout(Stdio::piped())
                .stderr(Stdio::piped())
                .spawn()
                .unwrap();
            c.stdin.take().unwrap().write_all(input).unwrap();
            let o = c.wait_with_output().unwrap();
            assert_eq!(o.status.code(), Some(0), "{}", String::from_utf8_lossy(&o.stderr));
            String::from_utf8(o.stdout).unwrap()
        };
        assert_eq!(exec(b"6\n"), "8\n");
        assert_eq!(exec(b"27\n"), "111\n");
        assert_eq!(exec(b"1\n"), "0\n");
    });
}
