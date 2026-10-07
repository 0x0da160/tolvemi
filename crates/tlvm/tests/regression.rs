//! 設計書 §20.1 の必須回帰テストと §18 の trace fixture の照合。

use tlvm::api::*;
use tlvm::checker::TypedProgram;
use tlvm::formatter::{encode_ast, format_program};
use tlvm::profiles::*;
use tlvm::syntax::{Ty, TyTag};
use tlvm::{DecodeResult, RunResult};

fn sp() -> StaticProfile {
    StaticProfile::default()
}

fn compile_with(src: &[u8], p: &StaticProfile) -> CompileResult {
    match compile(src, p) {
        SourceCompile::Result(r) => r,
        SourceCompile::SourceBoundaryFailure => panic!("boundary failure"),
    }
}

fn c(src: &str) -> CompileResult {
    compile_with(src.as_bytes(), &sp())
}

fn codes(r: &CompileResult) -> Vec<&'static str> {
    r.errors().iter().map(|d| d.code).collect()
}

fn ccodes(src: &str) -> Vec<&'static str> {
    codes(&c(src))
}

fn accepted(src: &str) -> TypedProgram {
    match c(src) {
        CompileResult::Accepted { program, .. } => program,
        r => panic!("rejected: {:?}", codes(&r)),
    }
}

fn ilist(xs: &[i64]) -> String {
    let items: Vec<String> = xs.iter().map(|x| format!("{{\"tag\":\"int\",\"value\":\"{x}\"}}")).collect();
    format!("{{\"tag\":\"list\",\"items\":[{}]}}", items.join(","))
}

fn run_src_with(src: &str, input: &str, p: &ExecutionProfile) -> RunResult {
    let prog = accepted(src);
    let tv = match decode_input(&prog.input_type, input.as_bytes(), &InputProfile::default()) {
        DecodeResult::Decoded(tv) => tv,
        other => panic!("decode failed: {other:?}"),
    };
    run(&prog, &tv, p, &HostPolicy::default()).unwrap()
}

fn run_src(src: &str, input: &str) -> RunResult {
    run_src_with(src, input, &ExecutionProfile::default())
}

fn output(r: RunResult) -> (String, u64, u64) {
    match r {
        RunResult::Completed { output, steps, allocated_nodes } => (output, steps, allocated_nodes),
        other => panic!("not completed: {other:?}"),
    }
}

const SUM_EVEN: &str = include_str!("../../../examples/sum_even.tlvm");
const POSITIVE: &str = include_str!("../../../examples/positive_values.tlvm");

// ------------------------------------------------------------ entry・宣言境界・parse

#[test]
fn entry_rules() {
    assert_eq!(ccodes("fn f(x: Int) -> Int = x"), ["E-ENTRY-MISSING"]);
    let r = c("fn f(x: Int) -> Int = x entry missing entry f");
    assert_eq!(codes(&r), ["E-ENTRY-UNKNOWN"]);
    assert_eq!(r.errors()[0].phase, "name");
    let r = c("fn f(x: Int) -> Int = x entry f entry f");
    assert_eq!(codes(&r), ["E-ENTRY-DUPLICATE"]);
    assert_eq!(r.errors()[0].span, (32, 39));
    assert_eq!(ccodes("fn f() -> Int = 0 entry f"), ["E-ENTRY-ARITY"]);
}

#[test]
fn unused_function_warning() {
    let r = c("fn f(x: Int) -> Int = x fn g(y: Int) -> Int = y entry f");
    assert!(r.program().is_some());
    assert_eq!(r.warnings().iter().map(|d| d.code).collect::<Vec<_>>(), ["W-UNUSED-FUNCTION"]);
    assert_eq!(r.warnings()[0].span, (27, 28));
    assert_eq!(format_program(&r.program().unwrap().program), "fn f(x: Int) -> Int = x\nfn g(y: Int) -> Int = y\nentry f\n");
}

#[test]
fn parse_errors() {
    assert_eq!(ccodes("fn f(x: Int) -> Int = x 1 entry f"), ["E-PARSE-UNEXPECTED-TOKEN"]);
    assert_eq!(ccodes("fn f(x: Int) -> Option<Int> = none<Foo>() entry f"), ["E-RECORD-UNKNOWN-TYPE"]);
    assert_eq!(ccodes("fn if(x: Int) -> Int = x entry if"), ["E-PARSE-EXPECTED-IDENT"; 2]);
    assert_eq!(ccodes("fn f(x: Int) -> Int = if(true, 1) entry f"), ["E-PARSE-EXPECTED-TOKEN"]);
    assert_eq!(ccodes("fn f(x: Int) -> Int = add(1,"), ["E-PARSE-EXPECTED-EXPR"]);
}

#[test]
fn recovery() {
    let bad = "fn f(x: Int) -> Int = ) ".repeat(9);
    let r = c(&(bad + "fn g(x: Int) -> Int = ) entry g"));
    let mut want = vec!["E-PARSE-EXPECTED-EXPR"; 9];
    want.push("E-PARSE-RECOVERY-LIMIT");
    assert_eq!(codes(&r), want);
    let ok = "fn f(x: Int) -> Int = ) ".repeat(8) + "fn g(x: Int) -> Int = x entry g";
    assert_eq!(ccodes(&ok), vec!["E-PARSE-EXPECTED-EXPR"; 8]);
    let r = c("fn f(x: Int) -> Int = fn g(y: Int) -> Int = ) entry g");
    assert_eq!(codes(&r), ["E-PARSE-EXPECTED-EXPR"; 2]);
    assert_eq!(r.errors()[0].span, (22, 24));
}

// ------------------------------------------------------------ 字句

#[test]
fn lexical() {
    assert_eq!(ccodes("fn f(x: Int) -> Int = 12x entry f"), ["E-LEX-INVALID-NUMERIC-BOUNDARY"]);
    for body in ["1-2", "- 2", "--2"] {
        assert!(ccodes(&format!("fn f(x: Int) -> Int = {body} entry f"))[0].starts_with("E-LEX-"), "{body}");
    }
    accepted("fn f(x: Int) -> Int = sub(1,-2) entry f");
    for lit in ["-0", "+1", "01"] {
        assert_eq!(ccodes(&format!("fn f(x: Int) -> Int = {lit} entry f")), ["E-LEX-INVALID-INTEGER"], "{lit}");
    }
    accepted("fn f(x: Int) -> Int = x entry f // 日本語");
    assert_eq!(ccodes("fn f(x: Int) -> Int = é entry f"), ["E-LEX-NON-ASCII"]);
    assert_eq!(codes(&compile_with(b"\xef\xbb\xbffn f(x: Int) -> Int = x entry f", &sp())), ["E-LEX-NON-ASCII"]);
}

#[test]
fn lexical_limits() {
    let src = b"fn f(x: Int) -> Int = x entry f"; // 13 tokens
    assert!(compile_with(src, &StaticProfile { tokens: 13, ..sp() }).program().is_some());
    assert_eq!(codes(&compile_with(src, &StaticProfile { tokens: 12, ..sp() })), ["E-LIMIT-STATIC-TOKENS"]);
    let p = StaticProfile { source_bytes: 4, ..sp() };
    assert_eq!(codes(&compile_with(b"\xff\xff\xff\xff\xff", &p)), ["E-LIMIT-STATIC-SOURCE-BYTES"]);
    assert!(matches!(compile(b"\xff", &sp()), SourceCompile::SourceBoundaryFailure));
    let p = StaticProfile { integer_digits: 3, ..sp() };
    assert_eq!(codes(&compile_with(b"fn f(x: Int) -> Int = 1234 entry f", &p)), ["E-LIMIT-STATIC-INTEGER-DIGITS"]);
    assert_eq!(codes(&compile_with(b"fn f(x: Int) -> Int = 01234 entry f", &p)), ["E-LEX-INVALID-INTEGER"]);
}

// ------------------------------------------------------------ 型・arity・DAG

#[test]
fn types_arity_dag() {
    let pre = "fn f(x: Int) -> Int = x ";
    assert_eq!(ccodes(&format!("{pre}fn g(u: Unit) -> Int = f(1, true) entry g")), ["E-ARITY-USER"]);
    assert_eq!(ccodes("fn g(u: Unit) -> Int = add(1, true, 0) entry g"), ["E-ARITY-BUILTIN"]);
    let mut v = ccodes(&format!("{pre}fn g(u: Unit) -> Int = f(1, fst(unit)) entry g"));
    v.sort();
    assert_eq!(v, ["E-ARITY-USER", "E-TYPE-FST-ARG"]);
    assert_eq!(ccodes("fn f(xs: List<Int>) -> Int = fold(xs, 0, |a, x| f(xs)) entry f"), ["E-CYCLE-CALL"]);
    assert_eq!(ccodes("fn f(x: Int) -> Int = g(x) fn g(x: Int) -> Int = f(x) entry f"), ["E-CYCLE-CALL"]);
    assert_eq!(ccodes("fn g(u: Option<Pair<Int, List<Int>>>) -> Int = fst(fst(u)) entry g"), ["E-TYPE-FST-ARG"]);
    let r = c("fn g(u: Unit) -> Int = if(true, 1, none<Int>()) entry g");
    assert_eq!(codes(&r), ["E-TYPE-IF-BRANCH"]);
    assert_eq!(r.errors()[0].expected.as_deref(), Some("Int"));
    assert_eq!(r.errors()[0].actual.as_deref(), Some("Option<Int>"));
    assert_eq!(ccodes("fn g(u: Unit) -> Bool = eq(1, true) entry g"), ["E-TYPE-EQ-OPERANDS"]);
    assert_eq!(ccodes("fn g(u: Unit) -> List<Int> = concat(list<Int>(), list<Bool>()) entry g"), ["E-TYPE-ARG"]);
}

#[test]
fn names() {
    assert_eq!(ccodes("fn g(x: Int) -> Int = let x = 1 in x entry g"), ["E-NAME-SHADOW"]);
    assert_eq!(ccodes("fn g(xs: List<Int>) -> Int = fold(xs, 0, |a, a| a) entry g"), ["E-NAME-DUPLICATE-BINDER"]);
    assert_eq!(ccodes("fn g(x: Int) -> Int = let y = y in y entry g"), ["E-NAME-UNBOUND-VARIABLE"]);
    // v1.1：uncons は組込み、match_option の binder にも束縛規則が掛かる
    assert_eq!(ccodes("fn g(x: Int) -> Int = uncons(x) entry g"), ["E-TYPE-EXPECTED-LIST"]);
    assert_eq!(ccodes("fn uncons(x: Int) -> Int = x entry uncons"), ["E-PARSE-EXPECTED-IDENT", "E-PARSE-EXPECTED-IDENT"]);
    assert_eq!(ccodes("fn g(x: Option<Int>) -> Int = match_option(x, 0, |x| x) entry g"), ["E-NAME-SHADOW"]);
    assert_eq!(ccodes("fn g(x: Option<Int>) -> Int = match_option(x, 0, |v| y) entry g"), ["E-NAME-UNBOUND-VARIABLE"]);
    assert_eq!(ccodes("fn g(x: Option<Int>) -> Int = add(match_option(x, 0, |v| v), v) entry g"), ["E-NAME-UNBOUND-VARIABLE"]);
    let p = accepted("fn g(x: Int) -> Int = h(x) fn h(x: Int) -> Int = x entry g");
    assert_eq!(p.rank["h"], 0);
    assert_eq!(p.rank["g"], 1);
}

// ------------------------------------------------------------ SemanticWork

#[test]
fn semantic_work_trace_fixtures() {
    let cases = [
        ("fn f(x: Int) -> Int = x", (1, 0, 1)),
        ("fn f(x: Unit) -> Int = 0", (1, 1, 1)),
        ("fn f(x: Unit) -> Int = add(1, 2)", (3, 3, 3)),
        ("fn f(x: Unit) -> Option<Int> = some(0)", (2, 2, 2)),
        ("fn f(x: Unit) -> List<Int> = list<Int>(1, 2)", (3, 3, 4)),
        ("fn f(x: Unit) -> Option<Int> = none<Int>()", (1, 1, 2)),
    ];
    for (src, (v, b, cmp)) in cases {
        let r = c(&format!("{src} entry f"));
        let w = r.work().unwrap();
        assert!(r.program().is_some(), "{src}");
        assert_eq!((w.visit, w.build, w.compare), (v, b, cmp), "{src}");
    }
}

#[test]
fn semantic_limits() {
    let add = b"fn f(x: Unit) -> Int = add(1, 2) entry f";
    assert!(compile_with(add, &StaticProfile { semantic_work: 9, ..sp() }).program().is_some());
    assert_eq!(codes(&compile_with(add, &StaticProfile { semantic_work: 8, ..sp() })), ["E-LIMIT-STATIC-SEMANTIC-WORK"]);
    let ar = b"fn f(x: Unit) -> Int = add(1, true, 0) entry f";
    assert_eq!(codes(&compile_with(ar, &StaticProfile { semantic_work: 0, ..sp() })), ["E-LIMIT-STATIC-SEMANTIC-WORK"]);
    assert_eq!(
        codes(&compile_with(ar, &StaticProfile { semantic_work: 1, ..sp() })),
        ["E-ARITY-BUILTIN", "E-LIMIT-STATIC-SEMANTIC-WORK"]
    );
    let r = compile_with(b"fn f(x: Unit) -> Int = add(1, 2) fn g(y: Int) -> Int = y", &StaticProfile { semantic_work: 3, ..sp() });
    assert_eq!(codes(&r), ["E-LIMIT-STATIC-SEMANTIC-WORK"]);
    assert!(r.warnings().is_empty());
    let r = compile_with(b"fn f(x: Unit) -> Option<Int> = some(0) entry f", &StaticProfile { semantic_type_depth: 1, semantic_work: 3, ..sp() });
    assert_eq!(codes(&r), ["E-LIMIT-STATIC-SEMANTIC-TYPE-DEPTH"]);
}

// ------------------------------------------------------------ structural limits

#[test]
fn structural_limits() {
    let r = compile_with(b"fn f(x: Int) -> Int = some(unit", &StaticProfile { ast_nodes: 6, ..sp() });
    assert_eq!(codes(&r), ["E-LIMIT-STATIC-AST-NODES"]);
    let lets = b"fn f(x: Int) -> Int = let a = 1 in let b = 2 in a entry f";
    assert_eq!(codes(&compile_with(lets, &StaticProfile { let_depth: 1, ..sp() })), ["E-LIMIT-STATIC-LET-DEPTH"]);
    assert!(compile_with(lets, &StaticProfile { let_depth: 2, ..sp() }).program().is_some());
    let ty = b"fn f(x: List<List<Int>>) -> Int = 0 entry f";
    assert_eq!(codes(&compile_with(ty, &StaticProfile { type_depth: 2, ..sp() })), ["E-LIMIT-STATIC-TYPE-DEPTH"]);
}

#[test]
fn error_limit() {
    let body = vec!["fst(unit)"; 40].join(", ");
    let r = c(&format!("fn f(x: Unit) -> List<Int> = list<Int>({body}) entry f"));
    assert_eq!(r.errors().len(), 32);
    assert_eq!(r.errors()[31].code, "E-DIAG-LIMIT");
}

#[test]
fn formatter_boundary_fixture() {
    let name = "f".repeat(524_276);
    let src = format!("fn {name}(x:Int)->Int=x entry {name}");
    assert_eq!(src.len(), 1_048_576);
    let p = accepted(&src);
    let out = format_program(&p.program);
    assert_eq!(out.len(), 1_048_582);
    assert_eq!(ccodes(&out), ["E-LIMIT-STATIC-SOURCE-BYTES"]);
}

// ------------------------------------------------------------ AST transport

const IDENT: &str = r#"{"codec":"ast_codec_v1","declarations":[{"tag":"fn","name":"identity","params":[{"name":"x","type":{"tag":"int"}}],"return_type":{"tag":"int"},"body":{"tag":"var","name":"%s"}},{"tag":"entry","name":"identity"}]}"#;

fn ast(s: &str) -> AstCompile {
    compile_ast(s.as_bytes(), &sp(), &AstTransportProfile::default())
}

fn acodes(s: &str) -> Vec<&'static str> {
    match ast(s) {
        AstCompile::AstInvalid(d) => d.iter().map(|d| d.code).collect(),
        AstCompile::Result(r) => codes(&r),
        AstCompile::AstBoundaryFailure => vec!["AstBoundaryFailure"],
    }
}

fn ident(name: &str) -> String {
    IDENT.replace("%s", name)
}

#[test]
fn ast_transport() {
    match ast(&ident("x")) {
        AstCompile::Result(CompileResult::Accepted { program, .. }) => assert_eq!(encode_ast(&program.program), ident("x")),
        other => panic!("{other:?}"),
    }
    assert_eq!(acodes(r#"{"codec":"ast_codec_v1","codec":"ast_codec_v1","declarations":[]}"#), ["E-AST-DUPLICATE-KEY"]);
    assert_eq!(acodes(r#"{"codec":"ast_codec_v1","codec":"x","declarations":[]}"#), ["E-AST-DUPLICATE-KEY"]);
    assert_eq!(acodes(&IDENT.replace(r#""name":"%s"}"#, r#""name":"x","inferred_type":{"tag":"int"}}"#)), ["E-AST-UNKNOWN-FIELD"]);
    assert_eq!(acodes(&ident("if")), ["E-AST-IDENTIFIER"]);
    assert_eq!(acodes(&ident("\\u0078")), Vec::<&str>::new());
    for bad in ["x\\n", "x\\r", "x\\r\\n", "x\\t", " x", "\\u00e9", "x\\u2028"] {
        assert_eq!(acodes(&ident(bad)), ["E-AST-IDENTIFIER"], "{bad}");
    }
    let int_body = IDENT.replace(r#"{"tag":"var","name":"%s"}"#, r#"{"tag":"int","value":%s}"#);
    for bad in [r#""-0""#, r#""01""#, r#""+1""#] {
        assert_eq!(acodes(&int_body.replace("%s", bad)), ["E-AST-INTEGER"], "{bad}");
    }
    assert_eq!(acodes(&int_body.replace("%s", "1")), ["E-AST-FIELD-TYPE"]);
    assert_eq!(acodes(r#"{"codec":"ast_codec_v1","declarations":[]}"#), ["E-ENTRY-MISSING"]);
    let call = IDENT.replace(r#"{"tag":"var","name":"%s"}"#, r#"{"tag":"call","callee":"uncons","args":[{"tag":"var","name":"x"}]}"#);
    // v1.1：uncons は組込みなので、同名の利用者関数は定義できない
    assert_eq!(acodes(&call), ["E-TYPE-EXPECTED-LIST"]);
    let decl = r#"{"tag":"fn","name":"uncons","params":[{"name":"y","type":{"tag":"int"}}],"return_type":{"tag":"int"},"body":{"tag":"var","name":"y"}},"#;
    assert_eq!(acodes(&call.replace(r#""declarations":["#, &format!(r#""declarations":[{decl}"#))), ["E-AST-IDENTIFIER"]);
    assert_eq!(acodes(&IDENT.replace(r#"{"tag":"var","name":"%s"}"#, r#"{"tag":"some"}"#)), ["E-AST-MISSING-FIELD"]);
    assert_eq!(acodes(&ident("x").replace(r#"{"name":"x","type""#, r#"{"tag":"param","name":"x","type""#)), ["E-AST-UNKNOWN-FIELD"]);
    let s = ident("x").replace(r#""name":"identity","params""#, r#""name":"if","params""#).replace(r#""body":{"tag":"var","name":"x"}"#, r#""body":1"#);
    assert_eq!(acodes(&s), ["E-AST-FIELD-TYPE"]);
    match compile_ast(b"\xff\xff", &sp(), &AstTransportProfile { json_bytes: 1, ..Default::default() }) {
        AstCompile::AstInvalid(d) => assert_eq!(d[0].code, "E-AST-LIMIT-BYTES"),
        other => panic!("{other:?}"),
    }
    assert!(matches!(compile_ast(b"\xff", &sp(), &AstTransportProfile::default()), AstCompile::AstBoundaryFailure));
    assert_eq!(acodes(&ident("\\ud800")), ["E-AST-STRING-SCALAR"]);
    let deep = "[".repeat(1025) + &"]".repeat(1025);
    assert_eq!(acodes(&deep), ["E-AST-LIMIT-JSON-DEPTH"]);
}

#[test]
fn surface_ast_roundtrip() {
    for src in [SUM_EVEN, POSITIVE] {
        let p = accepted(src);
        let enc = encode_ast(&p.program);
        let p2 = match ast(&enc) {
            AstCompile::Result(CompileResult::Accepted { program, .. }) => program,
            other => panic!("{other:?}"),
        };
        assert_eq!(p2.program, p.program);
        let p3 = accepted(&format_program(&p2.program));
        assert_eq!(encode_ast(&p3.program), enc);
    }
}

// ------------------------------------------------------------ 入力 decode

fn dcodes(t: &Ty, s: &str, p: InputProfile) -> Vec<&'static str> {
    match decode_input(t, s.as_bytes(), &p) {
        DecodeResult::Decoded(_) => vec![],
        DecodeResult::Invalid(d) => d.iter().map(|d| d.code).collect(),
        DecodeResult::InputBoundaryFailure => vec!["InputBoundaryFailure"],
    }
}

#[test]
fn input_decode() {
    let int = Ty::int();
    let pu = Ty::pair(Ty::unit(), Ty::unit());
    let d = InputProfile::default;
    assert!(dcodes(&int, r#"{"value":"5","tag":"int"}"#, d()).is_empty());
    assert_eq!(dcodes(&int, r#"{"tag":"int","value":5}"#, d()), ["E-INPUT-FIELD-TYPE"]);
    assert_eq!(dcodes(&int, r#"{"tag":"int","tag":"int","value":"1"}"#, d()), ["E-INPUT-DUPLICATE-KEY"]);
    let s = r#"{"tag":"pair","left":{"tag":"unit","x":1},"right":{"tag":"unit"}}"#;
    assert_eq!(dcodes(&pu, s, InputProfile { value_depth: 1, ..d() }), ["E-INPUT-UNKNOWN-FIELD"]);
    let s = r#"{"tag":"pair","left":{"tag":"unit"},"right":{"tag":"unit"}}"#;
    assert_eq!(dcodes(&pu, s, InputProfile { value_depth: 1, ..d() }), ["E-LIMIT-INPUT-VALUE-DEPTH"]);
    assert_eq!(dcodes(&int, r#"{"tag":"int","value":"01"}"#, InputProfile { value_nodes: 0, ..d() }), ["E-LIMIT-INPUT-VALUE-NODES"]);
    assert_eq!(dcodes(&int, r#"{"tag":"int","value":"0123"}"#, InputProfile { integer_digits: 2, ..d() }), ["E-INPUT-INTEGER"]);
    assert_eq!(dcodes(&int, r#"{"tag":"int","value":5}"#, InputProfile { value_nodes: 0, ..d() }), ["E-INPUT-FIELD-TYPE"]);
    assert_eq!(dcodes(&int, r#"{"tag":"bool","tag":"bool"}"#, d()), ["E-INPUT-DUPLICATE-KEY"]);
    let big = format!("{{\"tag\":\"int\",\"value\":\"1{}\"}}", "0".repeat(4096));
    assert_eq!(dcodes(&int, &big, d()), ["E-LIMIT-INPUT-INTEGER-DIGITS"]);
    let opt = (0..127).fold(Ty::int(), |t, _| Ty::new(TyTag::Option, vec![t]));
    let deep = "{\"tag\":\"some\",\"value\":".repeat(127) + "{\"tag\":\"int\",\"value\":\"1\"}" + &"}".repeat(127);
    assert!(dcodes(&opt, &deep, d()).is_empty());
}

// ------------------------------------------------------------ 実行

#[test]
fn examples_run() {
    assert_eq!(output(run_src(SUM_EVEN, &ilist(&[1, 2, -4, 7]))).0, r#"{"tag":"int","value":"-2"}"#);
    assert_eq!(output(run_src(POSITIVE, &ilist(&[3, -2, 5]))).0, ilist(&[3, 5]));
}

#[test]
fn builtins_and_sharing() {
    let src = "fn f(p: Pair<Int, Int>) -> Option<Int> = mod(fst(p), snd(p)) entry f";
    let pair = |a: i64, b: i64| format!(r#"{{"tag":"pair","left":{{"tag":"int","value":"{a}"}},"right":{{"tag":"int","value":"{b}"}}}}"#);
    assert_eq!(output(run_src(src, &pair(-3, 2))).0, r#"{"tag":"some","value":{"tag":"int","value":"1"}}"#);
    assert_eq!(output(run_src(src, &pair(1, 0))).0, r#"{"tag":"none"}"#);
    let src = "fn f(p: Pair<List<Int>, List<Int>>) -> List<Int> = concat(fst(p), snd(p)) entry f";
    let inp = format!(r#"{{"tag":"pair","left":{},"right":{}}}"#, ilist(&[1, 2, 3]), ilist(&[4, 5]));
    let (out, _, alloc) = output(run_src(src, &inp));
    assert_eq!(alloc, 3);
    assert_eq!(out, ilist(&[1, 2, 3, 4, 5]));
    let (_, _, alloc) = output(run_src("fn f(u: Unit) -> List<Option<Int>> = list<Option<Int>>(none<Int>(), none<Int>()) entry f", r#"{"tag":"unit"}"#));
    assert_eq!(alloc, 2);
    let (_, _, alloc) = output(run_src("fn f(u: Unit) -> Pair<Int, Int> = let x = 7 in pair(x, x) entry f", r#"{"tag":"unit"}"#));
    assert_eq!(alloc, 2);
    let (_, steps, alloc) = output(run_src("fn f(x: Int) -> Int = x entry f", r#"{"tag":"int","value":"1"}"#));
    assert_eq!((steps, alloc), (2, 0));
    let (_, steps, _) = output(run_src(SUM_EVEN, &ilist(&[1, 2, -4, 7])));
    assert_eq!(steps, 94);
}

#[test]
fn eq_structural() {
    let src = "fn f(p: Pair<List<Int>, List<Int>>) -> Bool = eq(fst(p), snd(p)) entry f";
    let inp = |a: &[i64], b: &[i64]| format!(r#"{{"tag":"pair","left":{},"right":{}}}"#, ilist(a), ilist(b));
    assert_eq!(output(run_src(src, &inp(&[1, 2], &[1, 2]))).0, r#"{"tag":"bool","value":true}"#);
    assert_eq!(output(run_src(src, &inp(&[1, 2], &[1]))).0, r#"{"tag":"bool","value":false}"#);
}

#[test]
fn resource_exhausted() {
    let src = "fn f(xs: List<Int>) -> Int = fold(xs, 0, |a, x| add(a, x)) entry f";
    let xs: Vec<i64> = (0..100).collect();
    let ex = |r| match r {
        RunResult::ResourceExhausted { kind, observed, limit } => (kind, observed, limit),
        other => panic!("{other:?}"),
    };
    assert_eq!(ex(run_src_with(src, &ilist(&xs), &ExecutionProfile { steps: 50, ..Default::default() })), ("Steps", 51, 50));
    assert_eq!(ex(run_src_with(src, &ilist(&xs), &ExecutionProfile { allocated_nodes: 10, ..Default::default() })).0, "AllocatedNodes");
    let big = |n: u32| format!(r#"{{"tag":"int","value":"{}"}}"#, num_bigint::BigInt::from(2).pow(n));
    let r = run_src_with("fn f(x: Int) -> Int = mul(x, x) entry f", &big(40), &ExecutionProfile { integer_bits: 64, ..Default::default() });
    assert_eq!(ex(r), ("IntegerBits", 81, 64));
    let r = run_src_with("fn f(x: Int) -> Int = 0 entry f", &big(70), &ExecutionProfile { integer_bits: 64, ..Default::default() });
    assert_eq!(ex(r), ("IntegerBits", 71, 64));
    let r = run_src_with("fn f(x: Int) -> Int = x entry f", r#"{"tag":"int","value":"12345"}"#, &ExecutionProfile { output_bytes: 10, ..Default::default() });
    assert_eq!(ex(r), ("OutputBytes", 11, 10));
}

#[test]
fn long_lists_and_deep_values() {
    let xs: Vec<i64> = (0..100_000).collect();
    let (out, _, _) = output(run_src("fn f(xs: List<Int>) -> Int = length(reverse(concat(xs, xs))) entry f", &ilist(&xs)));
    assert_eq!(out, r#"{"tag":"int","value":"200000"}"#);
    // 長いリストの構造的比較と解放（型が単相なので値の深さはリスト長でしか伸びない）
    let src = "fn f(xs: List<Int>) -> Bool = let d = reverse(xs) in eq(d, reverse(reverse(d))) entry f";
    let (out, _, _) = output(run_src_with(src, &ilist(&xs), &ExecutionProfile::default()));
    assert_eq!(out, r#"{"tag":"bool","value":true}"#);
}
