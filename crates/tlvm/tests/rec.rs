//! v1.7 の印をつけた関数の再帰 `rec fn`（差分仕様 §1〜§4）。

use std::io::Write;
use std::process::{Command, Stdio};
use tlvm::api::*;
use tlvm::checker::check_program;
use tlvm::evaluator::RunResult;
use tlvm::formatter::format_program;
use tlvm::profiles::*;

fn tlvm(args: &[&str]) -> (i32, String, String) {
    let o = Command::new(env!("CARGO_BIN_EXE_tlvm")).args(args).output().unwrap();
    (o.status.code().unwrap(), String::from_utf8(o.stdout).unwrap(), String::from_utf8(o.stderr).unwrap())
}

fn with_file<T>(src: &str, ext: &str, f: impl FnOnce(&str) -> T) -> T {
    static N: std::sync::atomic::AtomicUsize = std::sync::atomic::AtomicUsize::new(0);
    let n = N.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
    let path = std::env::temp_dir().join(format!("tlvm-rec-{}-{n}.{ext}", std::process::id()));
    std::fs::write(&path, src).unwrap();
    let r = f(path.to_str().unwrap());
    std::fs::remove_file(&path).unwrap();
    r
}

/// plain JSON で実行した（終了コード、出力と stderr）。
fn run_code(src: &str, input: &str) -> (i32, String) {
    with_file(src, "tlvm", |p| {
        let (code, out, err) = tlvm(&["run", p, input, "--plain"]);
        (code, format!("{}{}", out.trim_end(), err.trim_end()))
    })
}

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

/// 値 JSON の Int。
fn int(n: i64) -> String {
    format!(r#"{{"tag":"int","value":"{n}"}}"#)
}

/// API で実行する（資源プロファイルを指定できる）。
fn run_api(src: &str, input: &str, prof: &ExecutionProfile) -> RunResult {
    let p = accepted(src);
    let tv = match decode_input(&p.input_type, input.as_bytes(), &InputProfile::default()) {
        tlvm::DecodeResult::Decoded(tv) => tv,
        _ => panic!("input"),
    };
    tlvm::api::run(&p, &tv, prof, &HostPolicy::default()).unwrap()
}

const FACT: &str = "rec fn fact(n: Int) -> Int = if(le(n, 0), 1, mul(n, fact(sub(n, 1))))
fn solve(n: Int) -> Int = fact(n)
entry solve
";

/// 差分仕様 §1 の例。
const GCD: &str = "rec fn gcd(a: Int, b: Int) -> Int = match mod(a, b) { some(r) => if(eq(r, 0), b, gcd(b, r)), none => a }
fn solve(p: Pair<Int, Int>) -> Int = gcd(fst(p), snd(p))
entry solve
";

const EVEN_ODD: &str = "rec fn even(n: Int) -> Bool = if(eq(n, 0), true, odd(sub(n, 1)))
rec fn odd(n: Int) -> Bool = if(eq(n, 0), false, even(sub(n, 1)))
fn solve(n: Int) -> Pair<Bool, Bool> = pair(even(n), odd(n))
entry solve
";

/// 前置記法の式（直和型の token の List）を uncons で再帰的に評価する。型は再帰できないので、
/// 再帰は List の上で行い、残りの token を返す。
const PREFIX: &str = "type Tok = Num(Int) | Plus | Times | Neg
rec fn ev(ts: List<Tok>) -> Pair<Int, List<Tok>> =
  match uncons(ts) {
    none => pair(0, list<Tok>()),
    some(p) => match fst(p) {
      Num(n) => pair(n, snd(p)),
      Neg => let r = ev(snd(p)) in pair(neg(fst(r)), snd(r)),
      Plus => let a = ev(snd(p)) in let b = ev(snd(a)) in pair(add(fst(a), fst(b)), snd(b)),
      Times => let a = ev(snd(p)) in let b = ev(snd(a)) in pair(mul(fst(a), fst(b)), snd(b))
    }
  }
fn solve(ts: List<Tok>) -> Int = fst(ev(ts))
entry solve
";

// ---------------------------------------------------------------- 評価

#[test]
fn factorial_gcd_mutual() {
    assert_eq!(run(FACT, "0"), "1");
    assert_eq!(run(FACT, "5"), "120");
    assert_eq!(run(FACT, "25"), "\"15511210043330985984000000\"");
    assert_eq!(run(GCD, "[12, 18]"), "6");
    assert_eq!(run(GCD, "[17, 5]"), "1");
    assert_eq!(run(GCD, "[7, 0]"), "7");
    assert_eq!(run(EVEN_ODD, "10"), "[true,false]");
    assert_eq!(run(EVEN_ODD, "7"), "[false,true]");
    // 自分を直接呼ばない相互再帰でも、印のない関数から呼べる
    let p = accepted(EVEN_ODD);
    assert!(p.verified.is_some());
    assert!(!p.terminates());
    assert_eq!(p.rec_functions(), ["even", "odd"]);
}

#[test]
fn recursion_through_sums_records_and_lambdas() {
    assert_eq!(run(PREFIX, r#"[{"Plus": []}, {"Num": [2]}, {"Times": []}, {"Num": [3]}, {"Num": [4]}]"#), "14");
    assert_eq!(run(PREFIX, r#"[{"Neg": []}, {"Times": []}, {"Neg": []}, {"Num": [5]}, {"Num": [6]}]"#), "30");
    assert_eq!(run(PREFIX, "[]"), "0");
    // map のラムダから rec fn を呼ぶ。レコードの field と binder に rec という名前を使う
    let src = "type R = { rec: Int, even: Bool }
rec fn even(n: Int) -> Bool = if(eq(n, 0), true, odd(sub(n, 1)))
rec fn odd(n: Int) -> Bool = if(eq(n, 0), false, even(sub(n, 1)))
fn solve(xs: List<Int>) -> List<R> = map(xs, |rec| R { rec: rec, even: even(rec) })
entry solve
";
    assert_eq!(run(src, "[1, 2, 3]"), r#"[{"rec":1,"even":false},{"rec":2,"even":true},{"rec":3,"even":false}]"#);
    // loop と fold の本体から呼ぶ。rec fn の中で loop・filter を使う
    let src = "rec fn tri(n: Int) -> Int = if(le(n, 0), 0, add(n, fold(range(0, 1), 0, |a, x| tri(sub(n, 1)))))
fn solve(xs: List<Int>) -> Pair<List<Int>, Option<Int>> =
  pair(map(filter(xs, |x| lt(tri(x), 100)), |x| tri(x)), loop(0, 50, |s| if(lt(tri(s), 40), some(add(s, 1)), none<Int>())))
entry solve
";
    assert_eq!(run(src, "[1, 5, 20, 3]"), "[[1,15,6],9]");
}

#[test]
fn lowering_and_cross_check_without_marker() {
    // 書き換え後のソース（検証済み部品が読むもの）に印は残らず、検証済み formatter の正準形
    let p = match parse_source(PREFIX.as_bytes(), &StaticProfile::default()) {
        Parsed::Program(p) => p,
        _ => panic!("parse"),
    };
    assert!(p.has_rec());
    let px = expand(&p).unwrap();
    let o = check_program(&px, PREFIX.len(), &StaticProfile::default());
    assert!(o.typed.is_some(), "{:?}", o.diagnostics);
    let text = format_program(&lower(&tlvm::hof::lower(&px, &o.hof)).unmarked());
    assert!(text.starts_with("fn ev("), "{text}");
    assert_eq!(canonical(&text, &StaticProfile::default()).as_deref(), Some(text.as_str()));
    // source の印は同じ長さの空白に置き換わる（変数名の rec は残る）
    let src = "rec fn f(rec: Int) -> Int = if(le(rec, 0), 0, f(sub(rec, 1)))\nentry f\n";
    let p = match parse_source(src.as_bytes(), &StaticProfile::default()) {
        Parsed::Program(p) => p,
        _ => panic!("parse"),
    };
    let bare = without_rec_markers(src, &p);
    assert_eq!(bare, "    fn f(rec: Int) -> Int = if(le(rec, 0), 0, f(sub(rec, 1)))\nentry f\n");
    assert!(canonical(&bare, &StaticProfile::default()).is_some());
    assert!(canonical(src, &StaticProfile::default()).is_none(), "verified parser does not know rec");
    assert_eq!(run(src, "4"), "0");
}

#[test]
fn ranks_exempt_only_marked_callees() {
    // 印のある f と印のない g の相互呼出し：g → f の辺を除けば DAG なので受理（検証済み部品も受理）
    let src = "rec fn f(n: Int) -> Int = if(le(n, 0), 0, g(sub(n, 1)))
fn g(n: Int) -> Int = add(1, f(n))
fn solve(n: Int) -> Int = add(f(n), g(n))
entry solve
";
    let p = accepted(src);
    assert!(p.verified.is_some());
    assert!(p.rank["f"] > p.rank["g"]);
    assert_eq!(run(src, "3"), "7");
    // 印のない関数の自己呼出しと、印のない関数どうしの循環は拒否
    assert_eq!(codes("fn f(n: Int) -> Int = f(n)\nentry f\n"), ["E-CYCLE-CALL"]);
    assert_eq!(codes("rec fn h(n: Int) -> Int = f(n)\nfn f(n: Int) -> Int = g(n)\nfn g(n: Int) -> Int = f(n)\nentry h\n"), ["E-CYCLE-CALL"]);
    // 印のある関数からしか呼ばれない関数も、未使用の警告を受けない
    let r = compiled("rec fn f(n: Int) -> Int = if(le(n, 0), h(n), f(sub(n, 1)))\nfn h(n: Int) -> Int = n\nfn unused(n: Int) -> Int = n\nentry f\n");
    let w: Vec<_> = r.warnings().iter().map(|d| (d.code, d.span)).collect();
    assert_eq!(w.len(), 1, "{w:?}");
    assert_eq!(w[0].0, "W-UNUSED-FUNCTION");
}

// ---------------------------------------------------------------- 資源上限

// debug のフレームは release より大きく、既定の 1 GiB の評価スレッドが深さの上限（400,000）に届く前に溢れる。
// そのため debug では ignore し、release の CI で実行する。
#[test]
#[cfg_attr(debug_assertions, ignore = "debug では 1 GiB の評価スレッドが深さの上限より先に溢れる（release の CI で実行）")]
fn runaway_recursion_hits_the_default_depth_limit() {
    // 深さ：止まらない再帰はホストの既定の深さ上限で打ち切る（スタックあふれで落ちない）
    let deep = "rec fn f(n: Int) -> Int = add(f(add(n, 1)), 1)\nentry f\n";
    assert_eq!(run_code(deep, "0"), (2, r#"{"result":"HostAborted","reason":"eval-depth"}"#.to_string()));
    let tail = "rec fn f(n: Int) -> Int = f(n)\nentry f\n";
    assert_eq!(run_code(tail, "0"), (2, r#"{"result":"HostAborted","reason":"eval-depth"}"#.to_string()));
    assert_eq!(run_api(tail, &int(0), &ExecutionProfile::default()), RunResult::HostAborted("eval-depth".into()));
}

#[test]
fn runaway_recursion_stops_at_resource_limits() {
    // 深さの上限を小さくしたホストでも同じ（debug でも実行する）
    let tail = "rec fn f(n: Int) -> Int = f(n)\nentry f\n";
    let p = accepted(tail);
    let tv = match decode_input(&p.input_type, int(0).as_bytes(), &InputProfile::default()) {
        tlvm::DecodeResult::Decoded(tv) => tv,
        _ => panic!("input"),
    };
    let host = HostPolicy { max_eval_depth: 1000, ..HostPolicy::default() };
    assert_eq!(tlvm::api::run(&p, &tv, &ExecutionProfile::default(), &host).unwrap(), RunResult::HostAborted("eval-depth".into()));
    // step 数：浅いが指数的に増える再帰
    let fib = "rec fn fib(n: Int) -> Int = if(lt(n, 2), n, add(fib(sub(n, 1)), fib(sub(n, 2))))\nentry fib\n";
    let small = ExecutionProfile { steps: 100_000, ..ExecutionProfile::default() };
    assert!(matches!(run_api(fib, &int(30), &small), RunResult::ResourceExhausted { kind: "Steps", .. }));
    assert!(matches!(run_api(fib, &int(15), &small), RunResult::Completed { ref output, .. } if output == &int(610)));
    let (code, out) = run_code(fib, "40");
    assert_eq!(code, 2, "{out}");
    assert!(out.starts_with(r#"{"result":"ResourceExhausted""#), "{out}");
}

// debug のフレームは release より大きく、深さ 100,000 の再帰は既定の 1 GiB の評価スレッドに収まらない。
// そのため debug では ignore し、release の CI で実行する。
#[test]
#[cfg_attr(debug_assertions, ignore = "debug では深さ 100,000 の再帰が 1 GiB の評価スレッドに収まらない（release の CI で実行）")]
fn deep_recursion_within_the_limit_is_evaluated_to_the_end() {
    // 深い（が上限内の）再帰は最後まで評価できる
    let sum = "rec fn s(n: Int) -> Int = if(le(n, 0), 0, add(n, s(sub(n, 1))))\nentry s\n";
    assert_eq!(run(sum, "100000"), "5000050000");
}

// debug のフレームは release より大きく、既定の 1 GiB の評価スレッドが深さの上限に届く前に溢れる。
// そのため debug では ignore し、release の CI で実行する。
#[test]
#[cfg_attr(debug_assertions, ignore = "debug では 1 GiB の評価スレッドが深さの上限より先に溢れる（release の CI で実行）")]
fn exec_runaway_recursion_hits_the_default_depth_limit() {
    // exec でも止まらない再帰は深さの上限で打ち切る
    let runaway = "rec fn f(args: List<String>) -> String = f(args)\nentry f\n";
    with_file(runaway, "tlvm", |p| {
        let (code, out, err) = tlvm(&["exec", p, "x"]);
        assert_eq!(code, 2);
        assert_eq!(out, "");
        assert_eq!(err.trim_end(), r#"{"result":"HostAborted","reason":"eval-depth"}"#);
    });
}

// ---------------------------------------------------------------- 診断

#[test]
fn cycle_hint_suggests_rec() {
    let src = "fn solve(n: Int) -> Int = f(n)\nfn f(n: Int) -> Int = g(n)\nfn g(n: Int) -> Int = f(n)\nentry solve\n";
    let r = compiled(src);
    assert_eq!(r.errors().len(), 1);
    let d = &r.errors()[0];
    assert_eq!(d.code, "E-CYCLE-CALL");
    assert_eq!(d.actual.as_deref(), Some("f, g"));
    let fix = d.repair.as_ref().unwrap();
    assert_eq!(fix.kind, "insert_text");
    let at = src.find("fn f").unwrap();
    assert_eq!(fix.target_span, (at, at));
    assert!(fix.constraint.contains("'rec ' before 'fn'") && fix.constraint.contains("(f, g)"), "{}", fix.constraint);
    assert!(fix.constraint.contains("fold or loop"), "{}", fix.constraint);
    // ヒントどおりに直すと受理
    let fixed = src.replace("fn f", "rec fn f").replace("fn g", "rec fn g");
    assert!(accepted(&fixed).verified.is_some());
    // AST API では修復ヒントを出さない
    let json = with_file(src, "tlvm", |p| tlvm(&["ast", p]).1);
    match compile_ast(json.as_bytes(), &StaticProfile::default(), &AstTransportProfile::default()) {
        AstCompile::Result(r) => {
            assert_eq!(r.errors()[0].code, "E-CYCLE-CALL");
            assert!(r.errors()[0].repair.is_none());
        }
        _ => panic!("ast"),
    }
}

#[test]
fn rec_entry_is_rejected() {
    let src = "rec fn f(x: Int) -> Int = x\nrec entry f\n";
    let r = compiled(src);
    assert_eq!(r.errors().len(), 1, "{:?}", r.errors());
    let d = &r.errors()[0];
    assert_eq!(d.code, "E-PARSE-REC-ENTRY");
    assert_eq!(d.phase, "parse");
    let at = src.find("rec entry").unwrap();
    assert_eq!(d.span, (at, at + 3));
    let fix = d.repair.as_ref().unwrap();
    assert_eq!(fix.kind, "delete_span");
    assert_eq!(fix.target_span, (at, at + 3));
    // 他の位置の rec は普通の名前：最上位で直後が fn・entry でなければ構文の誤り
    assert_eq!(codes("rec type T = { a: Int }\nfn f(x: Int) -> Int = x\nentry f\n"), ["E-PARSE-UNEXPECTED-TOKEN"]);
}

#[test]
fn rec_is_a_soft_keyword() {
    // 変数・引数・束縛・field・関数の名前に使える
    let src = "type R = { rec: Int }
fn rec(rec: Int) -> Int = let r = R { rec: rec } in r.rec
rec fn down(n: Int) -> Int = if(le(n, 0), rec(n), down(sub(n, 1)))
fn solve(xs: List<Int>) -> Int = fold(xs, 0, |rec, x| add(rec, add(down(x), rec(x))))
entry solve
";
    assert_eq!(run(src, "[1, 2, 3]"), "6");
    let p = accepted(src);
    assert_eq!(p.rec_functions(), ["down"]);
    // 本体の最後の変数 rec の直後に次の宣言 fn が来ても、rec は変数（印ではない）
    let src = "fn id(rec: Int) -> Int = rec\nfn solve(x: Int) -> Int = id(x)\nentry solve\n";
    assert!(accepted(src).terminates());
    assert_eq!(run(src, "5"), "5");
    // 印のある関数の名前を rec にしてもよい
    let src = "rec fn rec(n: Int) -> Int = if(le(n, 0), 0, rec(sub(n, 1)))\nentry rec\n";
    assert_eq!(run(src, "3"), "0");
    // 文脈キーワードなので予約語の一覧には入らない（AST の識別子にも使える）
    assert!(!tlvm::syntax::is_keyword("rec"));
}

// ---------------------------------------------------------------- 整形・AST・報告

#[test]
fn fmt_round_trip() {
    let messy = "rec   fn fact( n : Int ) -> Int =\n  if(le(n, 0), 1,\n     mul(n, fact(sub(n, 1))))\nfn solve(n: Int) -> Int = fact(n)  entry solve";
    let (code, out, err) = with_file(messy, "tlvm", |p| tlvm(&["fmt", p]));
    assert_eq!(code, 0, "{err}");
    assert_eq!(out, FACT);
    let (code, again, _) = with_file(&out, "tlvm", |p| tlvm(&["fmt", p]));
    assert_eq!(code, 0);
    assert_eq!(again, out);
    // 直和型などと一緒（診断用 formatter）でも印を出す
    let (code, out, err) = with_file(PREFIX, "tlvm", |p| tlvm(&["fmt", p]));
    assert_eq!(code, 0, "{err}");
    assert!(out.contains("\nrec fn ev(ts: List<Tok>) -> Pair<Int, List<Tok>> = match uncons(ts) {"), "{out}");
    assert!(accepted(&out).verified.is_some());
}

#[test]
fn ast_round_trip() {
    let (code, json, err) = with_file(EVEN_ODD, "tlvm", |p| tlvm(&["ast", p]));
    assert_eq!(code, 0, "{err}");
    assert!(json.contains(r#""body":{"tag":"if","#));
    assert_eq!(json.matches(r#","rec":true}"#).count(), 2, "{json}");
    // 印のない関数には rec を書かない（v1.6 までの AST JSON と同じ）
    assert!(!json.contains(r#""name":"solve","params":[{"name":"n","type":{"tag":"int"}}],"return_type":{"tag":"pair","left":{"tag":"bool"},"right":{"tag":"bool"}},"body":{"tag":"pair","left":{"tag":"call","callee":"even","args":[{"tag":"var","name":"n"}]},"right":{"tag":"call","callee":"odd","args":[{"tag":"var","name":"n"}]}},"rec""#));
    let (_, plain, _) = with_file(GCD.replace("rec fn", "fn").replace("gcd(b, r)", "b").as_str(), "tlvm", |p| tlvm(&["ast", p]));
    assert!(!plain.contains("\"rec\""), "{plain}");
    let compile_json = |j: &str| match compile_ast(j.as_bytes(), &StaticProfile::default(), &AstTransportProfile::default()) {
        AstCompile::Result(r) => r,
        AstCompile::AstInvalid(d) => panic!("invalid: {d:?}"),
        _ => panic!("boundary"),
    };
    match compile_json(json.trim_end()) {
        CompileResult::Accepted { program, .. } => {
            assert!(!program.terminates());
            assert!(program.verified.is_some());
            assert_eq!(tlvm::formatter::encode_ast(&program.program).unwrap(), json.trim_end());
            assert_eq!(format_program(&program.program), EVEN_ODD);
        }
        r => panic!("{:?}", r.errors()),
    }
    // CLI：AST JSON からの check・fmt・run
    with_file(json.trim_end(), "json", |p| {
        let (code, out, _) = tlvm(&["check", p]);
        assert_eq!(code, 0);
        assert!(out.contains(r#""terminates":false"#), "{out}");
        assert_eq!(tlvm(&["fmt", p]).1, EVEN_ODD);
        assert_eq!(tlvm(&["run", p, "4", "--plain"]).1, "[true,false]\n");
    });
    // rec: false は省略と同じ。印を落とすと循環として拒否（安全側）
    let off = json.replace(r#","rec":true}"#, r#","rec":false}"#);
    assert_eq!(compile_json(off.trim_end()).errors().iter().map(|d| d.code).collect::<Vec<_>>(), ["E-CYCLE-CALL"]);
    // rec は真偽値
    let bad = json.replacen(r#","rec":true}"#, r#","rec":1}"#, 1);
    match compile_ast(bad.trim_end().as_bytes(), &StaticProfile::default(), &AstTransportProfile::default()) {
        AstCompile::AstInvalid(d) => assert_eq!(d[0].code, "E-AST-FIELD-TYPE"),
        _ => panic!("expected AstInvalid"),
    }
    // entry には rec を書けない
    let bad = json.replace(r#"{"tag":"entry","name":"solve"}"#, r#"{"tag":"entry","name":"solve","rec":true}"#);
    match compile_ast(bad.trim_end().as_bytes(), &StaticProfile::default(), &AstTransportProfile::default()) {
        AstCompile::AstInvalid(d) => assert_eq!(d[0].code, "E-AST-UNKNOWN-FIELD"),
        _ => panic!("expected AstInvalid"),
    }
}

#[test]
fn check_reports_termination() {
    let (code, out, _) = with_file(FACT, "tlvm", |p| tlvm(&["check", p]));
    assert_eq!(code, 0);
    assert_eq!(out, "{\"result\":\"Accepted\",\"entry\":\"solve\",\"input_type\":\"Int\",\"output_type\":\"Int\",\"terminates\":false}\n");
    let (_, out, err) = with_file(FACT, "tlvm", |p| tlvm(&["check", p, "--human"]));
    assert!(out.contains(r#""terminates":false"#));
    assert!(err.contains("termination is not guaranteed") && err.contains("rec fn fact"), "{err}");
    let plain = "fn solve(n: Int) -> Int = add(n, 1)\nentry solve\n";
    let (_, out, err) = with_file(plain, "tlvm", |p| tlvm(&["check", p, "--human"]));
    assert!(out.contains(r#""terminates":true"#), "{out}");
    assert!(err.is_empty(), "{err}");
    assert!(accepted(plain).terminates());
    // 組込み用の API
    let p = tlvm::embed::Program::compile(FACT).unwrap();
    assert!(!p.terminates());
    assert_eq!(p.run_json("6").unwrap(), "720");
}

#[test]
fn cli_test_and_exec() {
    let src = "rec fn rev(cs: String) -> String = match uncons(cs) { none => \"\", some(p) => concat(rev(snd(p)), list<Char>(fst(p))) }
fn solve(text: String) -> String = rev(text)
entry solve
";
    with_file(src, "tlvm", |p| {
        let mut child = Command::new(env!("CARGO_BIN_EXE_tlvm"))
            .args(["exec", p])
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::piped())
            .spawn()
            .unwrap();
        child.stdin.take().unwrap().write_all("abc\n".as_bytes()).unwrap();
        let o = child.wait_with_output().unwrap();
        assert_eq!(o.status.code(), Some(0));
        assert_eq!(String::from_utf8(o.stdout).unwrap(), "\ncba");
    });
    let cases = r#"[{"name": "five", "input": 5, "expected": 120}, {"input": 0, "expected": 1}]"#;
    with_file(FACT, "tlvm", |p| {
        with_file(cases, "json", |c| {
            let (code, out, _) = tlvm(&["test", p, c]);
            assert_eq!(code, 0, "{out}");
            assert!(out.ends_with("{\"passed\":2,\"failed\":0}\n"), "{out}");
        })
    });
}
