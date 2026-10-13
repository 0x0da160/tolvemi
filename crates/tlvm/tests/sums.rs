//! v1.4 の Result（`Result<T, E>`、`ok`、`err`、`match_result`）、ユーザー定義の直和型と `match`、
//! `tlvm exec` の Result 出力。

use std::io::Write;
use std::process::{Command, Stdio};
use tlvm::api::*;
use tlvm::formatter::format_program;
use tlvm::profiles::*;

fn tlvm(args: &[&str]) -> (i32, String, String) {
    let o = Command::new(env!("CARGO_BIN_EXE_tlvm")).args(args).output().unwrap();
    (o.status.code().unwrap(), String::from_utf8(o.stdout).unwrap(), String::from_utf8(o.stderr).unwrap())
}

fn with_file<T>(src: &str, ext: &str, f: impl FnOnce(&str) -> T) -> T {
    static N: std::sync::atomic::AtomicUsize = std::sync::atomic::AtomicUsize::new(0);
    let n = N.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
    let path = std::env::temp_dir().join(format!("tlvm-sum-{}-{n}.{ext}", std::process::id()));
    std::fs::write(&path, src).unwrap();
    let r = f(path.to_str().unwrap());
    std::fs::remove_file(&path).unwrap();
    r
}

/// plain JSON で実行した出力。
fn run(src: &str, input: &str) -> String {
    with_file(src, "tlvm", |p| {
        let (code, out, err) = tlvm(&["run", p, input, "--plain"]);
        assert_eq!(code, 0, "{err}");
        out.trim_end().to_string()
    })
}

/// 値 JSON で実行した出力。
fn run_canonical(src: &str, input: &str) -> String {
    with_file(src, "tlvm", |p| {
        let (code, out, err) = tlvm(&["run", p, input]);
        assert_eq!(code, 0, "{err}");
        out.trim_end().to_string()
    })
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

/// （終了コード、標準出力、標準エラー）
fn exec(src: &str, args: &[&str], stdin: &[u8]) -> (i32, String, String) {
    with_file(src, "tlvm", |p| {
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
        (o.status.code().unwrap(), String::from_utf8(o.stdout).unwrap(), String::from_utf8(o.stderr).unwrap())
    })
}

// ---------------------------------------------------------------- Result（組み込み）

const HALF: &str = "fn half(x: Int) -> Result<Int, String> =
  match_option(mod(x, 2), err<Int, String>(\"no\"), |r| if(eq(r, 0), ok<Int, String>(x), err<Int, String>(\"odd\")))
fn solve(x: Int) -> Result<Int, String> = match_result(half(x), |v| ok<Int, String>(add(v, 1)), |e| err<Int, String>(concat(\"E:\", e)))
entry solve
";

#[test]
fn result_typing_and_eval() {
    let p = accepted(HALF);
    assert_eq!(p.output_type.to_string(), "Result<Int, String>");
    assert_eq!(run(HALF, "4"), r#"{"ok":5}"#);
    assert_eq!(run(HALF, "3"), r#"{"err":"E:odd"}"#);
    // 値 JSON
    assert_eq!(run_canonical(HALF, r#"{"tag":"int","value":"4"}"#), r#"{"tag":"ok","value":{"tag":"int","value":"5"}}"#);
    // 入力の Result（plain と値 JSON）
    let src = "fn f(r: Result<Int, Bool>) -> Int = match_result(r, |n| n, |b| if(b, 1, 0)) entry f";
    assert_eq!(run(src, r#"{"ok": 7}"#), "7");
    assert_eq!(run(src, r#"{"err": true}"#), "1");
    assert_eq!(run_canonical(src, r#"{"tag":"err","value":{"tag":"bool","value":false}}"#), r#"{"tag":"int","value":"0"}"#);
    // 選ばれなかった枝は評価しない（0 による mod は none だが、ここでは呼ばれない）
    let lazy = "fn f(r: Result<Int, Int>) -> Int = match_result(r, |a| a, |b| match_option(mod(1, b), 0, |x| x)) entry f";
    assert_eq!(run(lazy, r#"{"ok": 3}"#), "3");
    // binder は二つの枝で同じ名前でもよい。ok／err は変数名にも使える
    let same = "fn f(r: Result<Int, Int>) -> Int = match_result(r, |x| x, |x| neg(x)) entry f";
    assert_eq!(run(same, r#"{"err": 3}"#), "-3");
    let soft = "fn f(ok: Int) -> Result<Int, Int> = let err = add(ok, 1) in ok<Int, Int>(err) entry f";
    assert_eq!(run(soft, "1"), r#"{"ok":2}"#);
}

#[test]
fn result_diagnostics() {
    assert_eq!(codes("fn f(x: Int) -> Int = match_result(x, |a| a, |b| b) entry f"), ["E-TYPE-MATCH-SCRUTINEE"]);
    assert_eq!(codes("fn f(r: Result<Int, Bool>) -> Int = match_result(r, |a| a, |b| b) entry f"), ["E-TYPE-MATCH-BRANCH"]);
    assert_eq!(codes("fn f(x: Int) -> Result<Int, Int> = ok<Int, Bool>(x) entry f"), ["E-TYPE-RETURN"]);
    assert_eq!(codes("fn f(x: Int) -> Result<Int, Bool> = err<Int, Bool>(x) entry f"), ["E-TYPE-ARG"]);
    assert_eq!(codes("fn f(r: Result<Int, Int>) -> Int = match_result(r, |r| r, |b| b) entry f"), ["E-NAME-SHADOW"]);
    // 型引数を書かない ok(x)：修復ヒントで ok<T, E>(x) を示す
    let r = compiled("fn f(x: Int) -> Result<Int, Int> = ok(x) entry f");
    assert_eq!(r.errors()[0].code, "E-PARSE-EXPECTED-TOKEN");
    assert!(r.errors()[0].repair.as_ref().unwrap().constraint.contains("ok<T, E>(x)"));
    // Result と match_result は予約語
    assert_eq!(codes("fn f(Result: Int) -> Int = 1 entry f"), ["E-PARSE-EXPECTED-IDENT"]);
    assert_eq!(codes("fn f(match_result: Int) -> Int = 1 entry f"), ["E-PARSE-EXPECTED-IDENT"]);
}

#[test]
fn result_formatting_and_ast_round_trip() {
    let src = "fn f(r: Result<Int, String>) -> Result<String, Int> = match_result(r, |v| err<String, Int>(v), |e| ok<String, Int>(e))\nentry f\n";
    // 診断用 formatter と検証済み formatter が一致する
    with_file(src, "tlvm", |p| {
        let (code, out, err) = tlvm(&["fmt", p]);
        assert_eq!(code, 0, "{err}");
        assert_eq!(out, src);
        let (code, ast, _) = tlvm(&["ast", p]);
        assert_eq!(code, 0);
        assert!(ast.contains(r#"{"tag":"result","ok":{"tag":"int"},"err":{"tag":"string"}}"#), "{ast}");
        assert!(ast.contains(r#""tag":"match_result","scrutinee":{"tag":"var","name":"r"},"ok_binder":"v""#), "{ast}");
        assert!(ast.contains(r#"{"tag":"err","ok_type":{"tag":"string"},"err_type":{"tag":"int"},"value":"#), "{ast}");
        with_file(ast.trim_end(), "json", |j| {
            let (code, out, err) = tlvm(&["fmt", j]);
            assert_eq!(code, 0, "{err}");
            assert_eq!(out, src);
            let (code, out, _) = tlvm(&["run", j, r#"{"ok": 4}"#, "--plain"]);
            assert_eq!(code, 0);
            assert_eq!(out.trim_end(), r#"{"err":4}"#);
        });
    });
}

// ---------------------------------------------------------------- 直和型

const SHAPES: &str = "type Shape = Circle(Int) | Rect(Int, Int) | Empty
fn area(s: Shape) -> Int = match s { Circle(r) => mul(3, mul(r, r)), Rect(w, h) => mul(w, h), Empty => 0 }
fn solve(xs: List<Shape>) -> Int = fold(xs, 0, |acc, s| add(acc, area(s)))
entry solve
";

#[test]
fn sum_construct_match_and_plain_json() {
    assert_eq!(run(SHAPES, r#"[{"Circle": [2]}, {"Rect": [2, 3]}, {"Empty": []}]"#), "18");
    let p = accepted(SHAPES);
    assert_eq!(p.input_type.to_string(), "List<Shape>");
    // 構築と plain 出力
    let mk = "type Shape = Circle(Int) | Rect(Int, Int) | Empty
type Box = Box1(Shape)
fn solve(x: Int) -> Pair<List<Shape>, Box> = pair(list<Shape>(Circle(x), Rect(x, add(x, 1)), Empty), Box1(Empty))
entry solve
";
    assert_eq!(run(mk, "3"), r#"[[{"Circle":[3]},{"Rect":[3,4]},{"Empty":[]}],{"Box1":[{"Empty":[]}]}]"#);
    // 値 JSON は展開後の形（Result<Int, Result<Pair<Int, Int>, Unit>>）
    let one = "type Shape = Circle(Int) | Rect(Int, Int) | Empty\nfn solve(x: Int) -> Shape = Rect(x, 1)\nentry solve\n";
    assert_eq!(
        run_canonical(one, r#"{"tag":"int","value":"2"}"#),
        r#"{"tag":"err","value":{"tag":"ok","value":{"tag":"pair","left":{"tag":"int","value":"2"},"right":{"tag":"int","value":"1"}}}}"#
    );
    // plain 入力の誤り
    with_file(SHAPES, "tlvm", |p| {
        let (code, _, err) = tlvm(&["run", p, r#"[{"Square": [1]}]"#, "--plain"]);
        assert_eq!(code, 1);
        assert!(err.contains("E-INPUT-TAG") && err.contains("Circle | Rect | Empty"), "{err}");
        let (code, _, err) = tlvm(&["run", p, r#"[{"Rect": [1]}]"#, "--plain"]);
        assert_eq!(code, 1);
        assert!(err.contains("E-INPUT-FIELD-TYPE"), "{err}");
        let (code, _, err) = tlvm(&["run", p, r#"[{"Rect": [1, 2], "Empty": []}]"#, "--plain"]);
        assert_eq!(code, 1);
        assert!(err.contains("E-INPUT-FIELD-TYPE"), "{err}");
    });
}

#[test]
fn sum_records_and_single_variant() {
    // 直和型の中のレコード、レコードの中の直和型、variant が一つの型
    let src = "type P = { x: Int, y: Int }
type Shape = Dot(P) | Seg(P, P) | Nothing
type Tagged = { shape: Shape, label: String }
type Wrap = Wrap1(P)
fn len(s: Shape) -> Int = match s { Seg(a, b) => add(sub(b.x, a.x), sub(b.y, a.y)), _ => 0 }
fn solve(t: Tagged) -> Pair<Int, Wrap> = pair(len(t.shape), match t.shape { Dot(p) => Wrap1(p), Seg(p, _) => Wrap1(p), Nothing => Wrap1(P { x: 0, y: 0 }) })
entry solve
";
    assert_eq!(
        run(src, r#"{"shape": {"Seg": [{"x": 1, "y": 1}, {"x": 4, "y": 5}]}, "label": "s"}"#),
        r#"[7,{"Wrap1":[{"x":1,"y":1}]}]"#
    );
    assert_eq!(run(src, r#"{"shape": {"Nothing": []}, "label": ""}"#), r#"[0,{"Wrap1":[{"x":0,"y":0}]}]"#);
}

#[test]
fn match_on_result_and_option_and_wildcards() {
    let src = "fn f(p: Pair<Result<Int, String>, Option<Int>>) -> Int =
  add(match fst(p) { ok(v) => v, err(_) => -1 }, match snd(p) { some(x) => x, none => 100 })
entry f
";
    assert_eq!(run(src, r#"[{"ok": 5}, 2]"#), "7");
    assert_eq!(run(src, r#"[{"err": "x"}, null]"#), "99");
    // `_` で残りをまとめる（直和型の途中の variant、Result、Option）
    let w = "type T = A | B(Int) | C(Int, Int) | D
fn g(t: T) -> Int = match t { B(x) => x, D => 4, _ => 0 }
fn h(r: Result<Int, Int>) -> Int = match r { err(e) => e, _ => 1 }
fn k(o: Option<Int>) -> Int = match o { none => 0, _ => 1 }
fn always(t: T) -> Int = match t { _ => 9 }
fn solve(t: T) -> List<Int> = list<Int>(g(t), h(ok<Int, Int>(3)), h(err<Int, Int>(3)), k(none<Int>()), k(some(2)), always(t))
entry solve
";
    assert_eq!(run(w, r#"{"A": []}"#), "[0,1,3,0,1,9]");
    assert_eq!(run(w, r#"{"B": [7]}"#), "[7,1,3,0,1,9]");
    assert_eq!(run(w, r#"{"C": [1, 2]}"#), "[0,1,3,0,1,9]");
    assert_eq!(run(w, r#"{"D": []}"#), "[4,1,3,0,1,9]");
    // binder の `_`、入れ子の match、`match` を変数名に使う
    let n = "type T = A(Int, Int, Int) | B
fn f(match: T) -> Int = match match { A(_, y, _) => match match { B => 0, A(x, _, z) => add(x, add(y, z)) }, B => -1 }
entry f
";
    assert_eq!(run(n, r#"{"A": [1, 2, 3]}"#), "6");
    assert_eq!(run(n, r#"{"B": []}"#), "-1");
}

#[test]
fn sum_formatting_round_trip_and_lowering() {
    let src = "type Shape = Circle(Int) | Rect(Int, Int) | Empty
fn area(s: Shape) -> Int = match s { Circle(r) => r, Rect(w, h) => mul(w, h), _ => 0 }
fn mk(x: Int) -> Shape = if(lt(x, 0), Empty, Circle(x))
entry area
";
    with_file(src, "tlvm", |p| {
        let (code, out, err) = tlvm(&["fmt", p]);
        assert_eq!(code, 0, "{err}");
        assert_eq!(out, src);
        // tlvm ast は展開後（ok／err・match_result）の AST。検証済み部品が受理する
        let (code, ast, _) = tlvm(&["ast", p]);
        assert_eq!(code, 0);
        assert!(ast.contains("\"tag\":\"match_result\"") && !ast.contains("Circle"), "{ast}");
        with_file(ast.trim_end(), "json", |j| {
            let (code, out, err) = tlvm(&["check", j]);
            assert_eq!(code, 0, "{err}");
            assert!(out.contains("Accepted"));
        });
    });
    // 展開後のプログラムを整形したソースを、検証済み部品の正準 formatter も同じに整形する
    let p = match parse_source(src.as_bytes(), &StaticProfile::default()) {
        Parsed::Program(p) => p,
        _ => panic!(),
    };
    let text = format_program(&lower(&expand(&p).unwrap()));
    assert!(text.contains("match_result(s, |r| r, |sum"), "{text}");
    assert_eq!(canonical(&text, &StaticProfile::default()).as_deref(), Some(text.as_str()));
}

#[test]
fn sum_diagnostics() {
    let h = "type Shape = Circle(Int) | Rect(Int, Int) | Empty\n";
    let c = |body: &str| codes(&format!("{h}{body} entry f"));
    assert_eq!(c("fn f(s: Shape) -> Int = match s { Circle(r) => r, Rect(w, h) => w }"), ["E-MATCH-MISSING"]);
    assert_eq!(c("fn f(s: Shape) -> Int = match s { Circle(r) => r, Circle(q) => q, _ => 0 }"), ["E-MATCH-DUPLICATE"]);
    assert_eq!(c("fn f(s: Shape) -> Int = match s { _ => 0, Empty => 1 }"), ["E-MATCH-UNREACHABLE"]);
    assert_eq!(c("fn f(s: Shape) -> Int = match s { Circle(r) => r, Rect(w, h) => w, Empty => 0, _ => 1 }"), ["E-MATCH-UNREACHABLE"]);
    assert_eq!(c("fn f(s: Shape) -> Int = match s { Circle(r) => r, ok(x) => x, _ => 0 }"), ["E-MATCH-MIXED"]);
    assert_eq!(c("fn f(s: Shape) -> Int = match s { Circel(r) => r, _ => 0 }"), ["E-SUM-UNKNOWN-CTOR"]);
    assert_eq!(c("fn f(s: Int) -> Shape = Circel(s)"), ["E-SUM-UNKNOWN-CTOR"]);
    assert_eq!(c("fn f(s: Int) -> Shape = Emty"), ["E-SUM-UNKNOWN-CTOR"]);
    assert_eq!(c("fn f(s: Shape) -> Int = match s { Rect(w) => w, _ => 0 }"), ["E-SUM-CTOR-ARITY"]);
    assert_eq!(c("fn f(s: Shape) -> Int = match s { Empty() => 0, _ => 1 }"), ["E-SUM-CTOR-ARITY"]);
    assert_eq!(c("fn f(s: Int) -> Shape = Rect(s)"), ["E-SUM-CTOR-ARITY"]);
    assert_eq!(c("fn f(s: Int) -> Shape = Circle"), ["E-SUM-CTOR-ARITY"]);
    assert_eq!(c("fn f(s: Int) -> Shape = Empty()"), ["E-SUM-CTOR-ARITY"]);
    assert_eq!(c("fn f(Circle: Int) -> Int = 1"), ["E-SUM-NAME-CONFLICT"]);
    assert_eq!(c("fn f(s: Int) -> Int = let Empty = 1 in Empty"), ["E-SUM-NAME-CONFLICT"]);
    assert_eq!(c("fn Rect(s: Int) -> Int = 1 fn f(s: Int) -> Int = 1"), ["E-SUM-NAME-CONFLICT"]);
    assert_eq!(codes("type S = S | T fn f(s: Int) -> Int = 1 entry f"), ["E-SUM-NAME-CONFLICT"]);
    assert_eq!(c("type T = Empty | Full fn f(s: Int) -> Int = 1"), ["E-SUM-DUPLICATE-CTOR"]);
    assert_eq!(codes("type T = A | B | A fn f(s: Int) -> Int = 1 entry f"), ["E-SUM-DUPLICATE-CTOR"]);
    assert_eq!(c("fn f(s: Int) -> Int = match s { _ => 0 }"), ["E-TYPE-MATCH-SCRUTINEE"]);
    assert_eq!(c("fn f(s: Int) -> Int = match s { Empty => 0, _ => 1 }"), ["E-TYPE-MATCH-SCRUTINEE"]);
    assert_eq!(c("fn f(s: Shape) -> Int = match s { Circle(r) => r, _ => true }"), ["E-TYPE-MATCH-BRANCH"]);
    assert_eq!(c("fn f(s: Int) -> Shape = Circle(true)"), ["E-TYPE-ARG"]);
    assert_eq!(c("fn f(s: Shape) -> Int = match s { Rect(a, a) => a, _ => 0 }"), ["E-NAME-DUPLICATE-BINDER"]);
    assert_eq!(c("fn f(s: Shape) -> Int = match s { Circle(s) => s, _ => 0 }"), ["E-NAME-SHADOW"]);
    // 再帰型・宣言前の型・未知の型
    // v1.14：自分自身を項に含む型は再帰する型として受理する（tests/recursive.rs）
    assert!(codes("type L = Nil | Cons(Int, L) fn f(s: Int) -> Int = 1 entry f").is_empty());
    assert_eq!(codes("type S = A(P) | B type P = { x: Int } fn f(s: Int) -> Int = 1 entry f"), ["E-RECORD-UNKNOWN-TYPE"]);
    assert_eq!(codes("type S = A(Foo) | B fn f(s: Int) -> Int = 1 entry f"), ["E-RECORD-UNKNOWN-TYPE"]);
    assert_eq!(codes("type S = A | B type S = C fn f(s: Int) -> Int = 1 entry f"), ["E-RECORD-DUPLICATE-TYPE"]);
    // 構文：小文字の構築子、pattern、`=>`
    assert_eq!(codes("type S = a | B fn f(s: Int) -> Int = 1 entry f"), ["E-PARSE-EXPECTED-IDENT"]);
    assert_eq!(c("fn f(s: Shape) -> Int = match s { 1 => 0 }"), ["E-PARSE-EXPECTED-PATTERN"]);
    assert_eq!(c("fn f(s: Shape) -> Int = match s { Empty -> 0 }"), ["E-PARSE-EXPECTED-TOKEN"]);
}

#[test]
fn sum_repair_hints() {
    let h = "type Shape = Circle(Int) | Rect(Int, Int) | Empty\n";
    let first = |body: &str| compiled(&format!("{h}{body} entry f")).errors()[0].clone();
    let d = first("fn f(s: Shape) -> Int = match s { Circle(r) => r }");
    assert_eq!(d.expected.as_deref(), Some("Rect(_, _), Empty"));
    let r = d.repair.unwrap();
    assert_eq!(r.kind, "insert_text");
    assert!(r.constraint.contains("Rect(_, _) => ..., Empty => ..."), "{}", r.constraint);
    let d = first("fn f(s: Int) -> Shape = Rectt(s, s)");
    assert!(d.repair.unwrap().constraint.contains("Rect"));
    let d = first("fn f(s: Shape) -> Int = match s { Rect(w) => w, _ => 0 }");
    assert!(d.repair.unwrap().constraint.contains("Rect(_, _)"));
    let d = first("fn f(s: Shape) -> Int = match s { _ => 0, Empty => 1 }");
    assert_eq!(d.repair.unwrap().kind, "delete_span");
}

#[test]
fn sum_and_result_names_in_messages() {
    // 型の表示は直和型の名前を使う
    let r = compiled("type Shape = Circle(Int) | Empty\nfn f(s: Shape) -> Int = s entry f");
    let d = &r.errors()[0];
    assert_eq!(d.code, "E-TYPE-RETURN");
    assert_eq!(d.actual.as_deref(), Some("Shape"));
    // v1.15：型の等価性は型の名前で決まる（同じ形の Result とは別の型。文面は両方の名前で出る）
    let r = compiled("type Opt = Has(Int) | Nothing\nfn f(x: Result<Int, Unit>) -> Opt = x\nentry f\n");
    let d = &r.errors()[0];
    assert_eq!(d.code, "E-TYPE-RETURN");
    assert_eq!(d.expected.as_deref(), Some("Opt"));
    assert_eq!(d.actual.as_deref(), Some("Result<Int, Unit>"));
}

// ---------------------------------------------------------------- exec

const CHECK: &str = "fn solve(s: String) -> Result<String, String> =
  if(eq(s, \"\"), err<String, String>(\"empty input\\n\"), ok<String, String>(reverse(s)))
entry solve
";

#[test]
fn exec_result_output() {
    assert_eq!(exec(CHECK, &[], b"abc"), (0, "cba".into(), String::new()));
    assert_eq!(exec(CHECK, &[], b""), (1, String::new(), "empty input\n".into()));
    // 直和型・match を使うプログラムも exec できる
    let src = "type Cmd = Add(Int) | Neg
fn parse(w: String) -> Result<Cmd, String> =
  if(eq(w, \"neg\"), ok<Cmd, String>(Neg), match parse_int(w) { some(n) => ok<Cmd, String>(Add(n)), none => err<Cmd, String>(concat(\"bad: \", w)) })
fn step(acc: Result<Int, String>, w: String) -> Result<Int, String> =
  match acc { ok(v) => match parse(w) { ok(c) => ok<Int, String>(match c { Add(n) => add(v, n), Neg => neg(v) }), err(e) => err<Int, String>(e) }, err(e) => err<Int, String>(e) }
fn solve(args: List<String>) -> Result<String, String> =
  match fold(args, ok<Int, String>(0), |acc, w| step(acc, w)) { ok(v) => ok<String, String>(to_string(v)), err(e) => err<String, String>(e) }
entry solve
";
    assert_eq!(exec(src, &["1", "2", "neg"], b""), (0, "-3".into(), String::new()));
    assert_eq!(exec(src, &["1", "x"], b""), (1, String::new(), "bad: x".into()));
    // 他の Result 出力は従来どおり plain JSON
    let other = "fn solve(s: String) -> Result<Int, String> = ok<Int, String>(length(s)) entry solve";
    assert_eq!(exec(other, &[], b"abcd"), (0, "{\"ok\":4}\n".into(), String::new()));
}
