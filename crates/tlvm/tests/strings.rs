//! v1.2 の文字と文字列（Char、String、文字・文字列リテラル、code／char／to_string／parse_int）。

use std::process::Command;
use tlvm::api::*;
use tlvm::formatter::{encode_ast, format_program};
use tlvm::plain::encode_plain;
use tlvm::profiles::*;
use tlvm::syntax::Ty;
use tlvm::values::encode_value;
use tlvm::DecodeResult;

const MISMATCH: &str = "E-INTERNAL-VERIFIED-MISMATCH";

fn with_file<T>(src: &str, f: impl FnOnce(&str) -> T) -> T {
    static N: std::sync::atomic::AtomicUsize = std::sync::atomic::AtomicUsize::new(0);
    let n = N.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
    let path = std::env::temp_dir().join(format!("tlvm-str-{}-{n}.tlvm", std::process::id()));
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

fn errors(src: &str) -> Vec<tlvm::diagnostics::Diagnostic> {
    match compile(src.as_bytes(), &StaticProfile::default()) {
        SourceCompile::Result(r) => r.errors().to_vec(),
        _ => panic!("source boundary failure"),
    }
}

/// 診断コードの列。検証済み部品との食い違いがないことも確かめる。
fn codes(src: &str) -> Vec<&'static str> {
    let cs: Vec<&'static str> = errors(src).iter().map(|d| d.code).collect();
    assert!(!cs.contains(&MISMATCH), "verified mismatch for {src:?}: {cs:?}");
    cs
}

fn accepted(body: &str, ty: &str) -> bool {
    codes(&format!("fn f(s: String) -> {ty} = {body}\nentry f\n")).is_empty()
}

#[test]
fn literals_lex() {
    // 受理：生の文字（非 ASCII を含む）、許されたエスケープ、区切りでない方の引用符
    for (body, ty) in [
        ("'a'", "Char"),
        ("'é'", "Char"),
        ("'😀'", "Char"),
        ("'\"'", "Char"),
        (r"'\''", "Char"),
        (r"'\\'", "Char"),
        (r"'\n'", "Char"),
        (r"'\t'", "Char"),
        (r"'\r'", "Char"),
        ("' '", "Char"),
        ("\"\"", "String"),
        ("\"héllo, 世界\"", "String"),
        ("\"it's\"", "String"),
        (r#""a\"b\\c\nd\te\rf""#, "String"),
        ("\"// not a comment\"", "String"),
    ] {
        assert!(accepted(body, ty), "{body}");
    }
    // 拒否
    let f = |body: &str| codes(&format!("fn f(s: String) -> String = {body}\nentry f\n"));
    assert_eq!(f(r#""a\qb""#), ["E-LEX-INVALID-ESCAPE"]);
    assert_eq!(f(r#""a\'b""#), ["E-LEX-INVALID-ESCAPE"]);
    assert_eq!(f(r"'\x'"), ["E-LEX-INVALID-ESCAPE"]);
    assert_eq!(f(r#"'\"'"#), ["E-LEX-INVALID-ESCAPE"]);
    assert_eq!(f("\"abc"), ["E-LEX-UNTERMINATED-STRING"]);
    assert_eq!(f("\"ab\ncd\""), ["E-LEX-UNTERMINATED-STRING"]);
    assert_eq!(codes("fn f(s: String) -> String = \"ab\\"), ["E-LEX-UNTERMINATED-STRING"]);
    assert_eq!(f("\"ab\\"), ["E-LEX-INVALID-ESCAPE"]);
    assert_eq!(f("\"a\tb\""), ["E-LEX-CONTROL-CHAR-IN-LITERAL"]);
    assert_eq!(f("\"a\u{1}b\""), ["E-LEX-CONTROL-CHAR-IN-LITERAL"]);
    assert_eq!(f("'\t'"), ["E-LEX-CONTROL-CHAR-IN-LITERAL"]);
    assert_eq!(f("''"), ["E-LEX-INVALID-CHAR-LITERAL"]);
    assert_eq!(f("'ab'"), ["E-LEX-INVALID-CHAR-LITERAL"]);
    assert_eq!(f("'a"), ["E-LEX-INVALID-CHAR-LITERAL"]);
    assert_eq!(f("'"), ["E-LEX-INVALID-CHAR-LITERAL"]);
    assert_eq!(f(r"'\'"), ["E-LEX-INVALID-CHAR-LITERAL"]);
    // リテラルの外の非 ASCII は従来どおり
    assert_eq!(f("é"), ["E-LEX-NON-ASCII"]);
}

#[test]
fn lex_spans_and_repairs() {
    let src = "fn f(s: String) -> String = \"ab\\qc\"\nentry f\n";
    let d = &errors(src)[0];
    assert_eq!(&src[d.span.0..d.span.1], "\\q");
    assert_eq!(d.repair.as_ref().unwrap().kind, "replace_expression");
    let src = "fn f(s: String) -> Char = 'xyz'\nentry f\n";
    let d = &errors(src)[0];
    assert_eq!(&src[d.span.0..d.span.1], "'xyz'");
    let src = "fn f(s: String) -> String = \"é\tx\"\nentry f\n";
    let d = &errors(src)[0];
    assert_eq!(&src[d.span.0..d.span.1], "\t");
    let src = "fn f(s: String) -> String = \"abc\nentry f\n";
    let d = &errors(src)[0];
    assert_eq!(&src[d.span.0..d.span.1], "\"abc");
    assert_eq!(d.repair.as_ref().unwrap().kind, "insert_text");
}

#[test]
fn string_type_spelling() {
    // List<Char> は String と書く（どこに現れても）
    for src in [
        "fn f(s: List<Char>) -> Int = 1 entry f",
        "fn f(s: String) -> Option<List<Char>> = none<String>() entry f",
        "fn f(s: String) -> Int = length(list<List<Char>>()) entry f",
        "fn f(s: Pair<Int, List<Char>>) -> Int = 1 entry f",
    ] {
        assert_eq!(codes(src), ["E-PARSE-STRING-TYPE"], "{src}");
    }
    let src = "fn f(s: List<Char>) -> Int = 1 entry f";
    let d = &errors(src)[0];
    assert_eq!(&src[d.span.0..d.span.1], "List<Char>");
    let r = d.repair.as_ref().unwrap();
    assert_eq!((r.kind, r.constraint.as_str()), ("replace_type", "String"));
    // 値の構築子の型引数には Char を書ける（list<Char>(...) は String）
    assert!(codes("fn f(c: Char) -> String = list<Char>(c, 'x') entry f").is_empty());
    assert!(codes("fn f(s: List<String>) -> Option<String> = none<String>() entry f").is_empty());
    // 型の表示は String
    let ds = errors("fn f(s: String) -> Int = s entry f");
    assert_eq!(ds[0].code, "E-TYPE-RETURN");
    assert_eq!(ds[0].actual.as_deref(), Some("String"));
    let ds = errors("fn f(s: List<String>) -> Int = some(s) entry f");
    assert_eq!(ds[0].actual.as_deref(), Some("Option<List<String>>"));
}

#[test]
fn keywords() {
    // Char、String は予約語。組み込み関数の名前は文脈キーワード（変数名に使える）
    assert_eq!(codes("fn f(String: Int) -> Int = 1 entry f"), ["E-PARSE-EXPECTED-IDENT"]);
    assert_eq!(codes("fn Char(x: Int) -> Int = 1 entry Char")[0], "E-PARSE-EXPECTED-IDENT");
    assert!(codes("fn f(code: Char) -> Int = let char = code(code) in char entry f").is_empty());
    assert!(codes("fn f(to_string: Int) -> String = let parse_int = to_string(to_string) in parse_int entry f").is_empty());
    assert_eq!(run("fn f(char: Int) -> Option<Char> = char(char) entry f", "97"), "\"a\"");
}

#[test]
fn builtin_types() {
    assert_eq!(codes("fn f(x: Int) -> Int = code(x) entry f"), ["E-TYPE-ARG"]);
    assert_eq!(codes("fn f(x: Char) -> Option<Char> = char(x) entry f"), ["E-TYPE-ARG"]);
    assert_eq!(codes("fn f(x: Char) -> String = to_string(x) entry f"), ["E-TYPE-ARG"]);
    assert_eq!(codes("fn f(x: List<Int>) -> Option<Int> = parse_int(x) entry f"), ["E-TYPE-ARG"]);
    assert_eq!(codes("fn f(x: Int) -> Int = code('a', 'b') entry f"), ["E-ARITY-BUILTIN"]);
    assert_eq!(codes("fn f(x: Int) -> Int = 'a' entry f"), ["E-TYPE-RETURN"]);
    assert_eq!(codes("fn f(x: Int) -> List<Int> = \"a\" entry f"), ["E-TYPE-RETURN"]);
    // String は List<Char> そのもの：リストの組み込み関数がそのまま使える
    assert!(codes("fn f(s: String) -> Bool = eq(concat(reverse(s), \"!\"), cons('x', \"y\")) entry f").is_empty());
    assert!(codes("fn f(s: String) -> Bool = contains(s, 'a') entry f").is_empty());
}

#[test]
fn builtin_values() {
    let f = |body: &str, ty: &str| format!("fn f(s: String) -> {ty} = {body}\nentry f\n");
    assert_eq!(run(&f("list<Int>(code('A'), code('é'), code('\\n'), code('😀'))", "List<Int>"), "\"\""), "[65,233,10,128512]");
    assert_eq!(
        run(&f("list<Option<Char>>(char(65), char(-1), char(55296), char(57343), char(57344), char(1114111), char(1114112))", "List<Option<Char>>"), "\"\""),
        "[\"A\",null,null,null,\"\u{e000}\",\"\u{10ffff}\",null]"
    );
    assert_eq!(run(&f("list<String>(to_string(0), to_string(-12), to_string(1234567890123456789012))", "List<String>"), "\"\""), "[\"0\",\"-12\",\"1234567890123456789012\"]");
    let p = f("parse_int(s)", "Option<Int>");
    for (input, out) in [
        ("\"42\"", "42"),
        ("\"-12\"", "-12"),
        ("\"007\"", "7"),
        ("\"-0\"", "0"),
        ("\"\"", "null"),
        ("\"-\"", "null"),
        ("\"+1\"", "null"),
        ("\" 1\"", "null"),
        ("\"1a\"", "null"),
        ("\"１\"", "null"),
        // JavaScript の number で表せない整数は plain JSON では十進文字列
        ("\"123456789012345678901234567890\"", "\"123456789012345678901234567890\""),
    ] {
        assert_eq!(run(&p, input), out, "parse_int({input})");
    }
    // 文字列リテラルの値とエスケープ
    assert_eq!(run(&f("\"a\\\"b\\\\c\\nd\\te\\rf'é\"", "String"), "\"\""), "\"a\\\"b\\\\c\\nd\\te\\rf'é\"");
    assert_eq!(run(&f("length(\"héllo😀\")", "Int"), "\"\""), "6");
    assert_eq!(run(&f("eq(s, \"abc\")", "Bool"), "\"abc\""), "true");
    // 文字列の組み立て（fold で各桁を足す）
    let src = "fn f(s: String) -> Int = fold(s, 0, |acc, c| add(acc, sub(code(c), code('0')))) entry f";
    assert_eq!(run(src, "\"1234\""), "10");
}

fn plain_decode(t: &Ty, s: &str) -> Result<String, Vec<&'static str>> {
    match decode_plain_input(t, s.as_bytes(), &InputProfile::default()) {
        DecodeResult::Decoded(tv) => Ok(encode_value(&tv.value)),
        DecodeResult::Invalid(d) => Err(d.iter().map(|d| d.code).collect()),
        DecodeResult::InputBoundaryFailure => Err(vec!["boundary"]),
    }
}

fn roundtrip(t: &Ty, plain: &str, canonical: &str) {
    assert_eq!(plain_decode(t, plain).as_deref(), Ok(canonical), "decode {plain} : {t}");
    assert_eq!(encode_plain(t, canonical).as_deref(), Ok(plain), "encode {canonical} : {t}");
}

fn ch(c: u32) -> String {
    format!(r#"{{"tag":"char","value":"{c}"}}"#)
}

#[test]
fn plain_json() {
    let s = Ty::string();
    roundtrip(&Ty::char(), "\"a\"", &ch(97));
    roundtrip(&Ty::char(), "\"😀\"", &ch(0x1F600));
    roundtrip(&Ty::char(), "\"\\\"\"", &ch(34));
    roundtrip(&s, "\"\"", r#"{"tag":"list","items":[]}"#);
    roundtrip(&s, "\"aé\"", &format!(r#"{{"tag":"list","items":[{},{}]}}"#, ch(97), ch(233)));
    roundtrip(&s, "\"\\n\\\\\\u0001\"", &format!(r#"{{"tag":"list","items":[{},{},{}]}}"#, ch(10), ch(92), ch(1)));
    roundtrip(&Ty::list(s.clone()), "[\"a\",\"\"]", &format!(r#"{{"tag":"list","items":[{{"tag":"list","items":[{}]}},{{"tag":"list","items":[]}}]}}"#, ch(97)));
    roundtrip(&Ty::option(s.clone()), "null", r#"{"tag":"none"}"#);
    roundtrip(&Ty::option(Ty::char()), "\"x\"", &format!(r#"{{"tag":"some","value":{}}}"#, ch(120)));
    // JSON の escape は読める
    assert_eq!(plain_decode(&Ty::char(), "\"\\u00e9\""), Ok(ch(233)));
    assert_eq!(plain_decode(&s, "\"\\ud83d\\ude00\""), Ok(format!(r#"{{"tag":"list","items":[{}]}}"#, ch(0x1F600))));
    // 形の誤り
    assert_eq!(plain_decode(&Ty::char(), "\"ab\""), Err(vec!["E-INPUT-FIELD-TYPE"]));
    assert_eq!(plain_decode(&Ty::char(), "\"\""), Err(vec!["E-INPUT-FIELD-TYPE"]));
    assert_eq!(plain_decode(&Ty::char(), "97"), Err(vec!["E-INPUT-FIELD-TYPE"]));
    assert_eq!(plain_decode(&s, "[\"a\"]"), Err(vec!["E-INPUT-FIELD-TYPE"]));
    assert_eq!(plain_decode(&s, "\"\\ud800\""), Err(vec!["E-INPUT-STRING-SCALAR"]));
    // 値の node 数は文字ごとに数える
    let p = InputProfile { value_nodes: 3, ..InputProfile::default() };
    assert!(matches!(decode_plain_input(&s, b"\"ab\"", &p), DecodeResult::Decoded(_)));
    match decode_plain_input(&s, b"\"abc\"", &p) {
        DecodeResult::Invalid(d) => assert_eq!(d[0].code, "E-LIMIT-INPUT-VALUE-NODES"),
        _ => panic!("expected limit"),
    }
}

#[test]
fn value_json_chars() {
    let dec = |t: &Ty, s: &str| match decode_input(t, s.as_bytes(), &InputProfile::default()) {
        DecodeResult::Decoded(tv) => Ok(encode_value(&tv.value)),
        DecodeResult::Invalid(d) => Err(d.iter().map(|d| d.code).collect::<Vec<_>>()),
        DecodeResult::InputBoundaryFailure => Err(vec!["boundary"]),
    };
    assert_eq!(dec(&Ty::char(), &ch(0)), Ok(ch(0)));
    assert_eq!(dec(&Ty::char(), &ch(0x10FFFF)), Ok(ch(0x10FFFF)));
    assert_eq!(dec(&Ty::char(), &ch(0xD800)), Err(vec!["E-INPUT-CHAR"]));
    assert_eq!(dec(&Ty::char(), &ch(0x110000)), Err(vec!["E-INPUT-CHAR"]));
    assert_eq!(dec(&Ty::char(), r#"{"tag":"char","value":"99999999999999999999"}"#), Err(vec!["E-INPUT-CHAR"]));
    assert_eq!(dec(&Ty::char(), r#"{"tag":"char","value":"-1"}"#), Err(vec!["E-INPUT-CHAR"]));
    assert_eq!(dec(&Ty::char(), r#"{"tag":"char","value":"065"}"#), Err(vec!["E-INPUT-INTEGER"]));
    assert_eq!(dec(&Ty::char(), r#"{"tag":"int","value":"65"}"#), Err(vec!["E-INPUT-TAG"]));
    assert_eq!(dec(&Ty::int(), &ch(65)), Err(vec!["E-INPUT-TAG"]));
}

#[test]
fn formatter_matches_verified_formatter() {
    let src = "fn f(s: String) -> Pair<List<String>, Option<Char>> =\n  pair(list<String>(\"a\\\"b\\\\c\\nd\\te\\r'é\", s), some('\\''))\nentry f\n";
    let p = match parse_source(src.as_bytes(), &StaticProfile::default()) {
        Parsed::Program(p) => p,
        _ => panic!("parse failed"),
    };
    let ours = format_program(&p);
    assert_eq!(canonical(src, &StaticProfile::default()).as_deref(), Some(ours.as_str()));
    assert!(ours.contains(r#""a\"b\\c\nd\te\r'é""#), "{ours}");
    assert!(ours.contains(r"'\''"), "{ours}");
    assert!(ours.contains("Pair<List<String>, Option<Char>>"), "{ours}");
    for c in ["'\"'", "'\\\\'", "'\\n'"] {
        let s = format!("fn f(s: String) -> Char = {c}\nentry f\n");
        assert_eq!(canonical(&s, &StaticProfile::default()), Some(s.clone()));
    }
}

#[test]
fn ast_codec() {
    let src = "fn f(s: String) -> Pair<Option<Int>, String> = pair(parse_int(s), cons('\\n', \"é\\\"x\")) entry f";
    let p = match parse_source(src.as_bytes(), &StaticProfile::default()) {
        Parsed::Program(p) => p,
        _ => panic!("parse failed"),
    };
    let ast = encode_ast(&p).unwrap();
    assert!(ast.contains(r#"{"tag":"string"}"#), "{ast}");
    assert!(ast.contains(r#"{"tag":"char","value":"10"}"#), "{ast}");
    assert!(ast.contains(r#"{"tag":"string","value":"é\"x"}"#), "{ast}");
    match compile_ast(ast.as_bytes(), &StaticProfile::default(), &AstTransportProfile::default()) {
        AstCompile::Result(CompileResult::Accepted { program, .. }) => assert_eq!(program.output_type.to_string(), "Pair<Option<Int>, String>"),
        r => panic!("{r:?}"),
    }
    let bad = |body: &str, ty: &str| {
        let a = format!(
            r#"{{"codec":"ast_codec_v1","declarations":[{{"tag":"fn","name":"f","params":[{{"name":"x","type":{ty}}}],"return_type":{{"tag":"int"}},"body":{body}}},{{"tag":"entry","name":"f"}}]}}"#
        );
        match compile_ast(a.as_bytes(), &StaticProfile::default(), &AstTransportProfile::default()) {
            AstCompile::AstInvalid(d) => d[0].code,
            AstCompile::Result(r) => r.errors().first().map(|d| d.code).unwrap_or("accepted"),
            AstCompile::AstBoundaryFailure => "boundary",
        }
    };
    let int = r#"{"tag":"int"}"#;
    assert_eq!(bad(r#"{"tag":"var","name":"x"}"#, r#"{"tag":"list","element":{"tag":"char"}}"#), "E-AST-STRING-TYPE");
    assert_eq!(bad(r#"{"tag":"call","callee":"code","args":[{"tag":"char","value":"1"}],"type_args":[]}"#, int), "E-AST-LITERAL");
    assert_eq!(bad(r#"{"tag":"call","callee":"code","args":[{"tag":"char","value":"55296"}],"type_args":[]}"#, int), "E-AST-LITERAL");
    assert_eq!(bad(r#"{"tag":"call","callee":"code","args":[{"tag":"char","value":"x"}],"type_args":[]}"#, int), "E-AST-LITERAL");
    assert_eq!(bad(r#"{"tag":"call","callee":"code","args":[{"tag":"char","value":"9"}],"type_args":[]}"#, int), "accepted");
    assert_eq!(bad(r#"{"tag":"call","callee":"length","args":[{"tag":"string","value":"a\u0001"}],"type_args":[]}"#, int), "E-AST-LITERAL");
    assert_eq!(bad(r#"{"tag":"call","callee":"length","args":[{"tag":"string","value":"a\n\"\\'"}],"type_args":[]}"#, int), "accepted");
    assert_eq!(bad(r#"{"tag":"call","callee":"parse_int","args":[{"tag":"var","name":"x"}],"type_args":[]}"#, r#"{"tag":"string"}"#), "E-TYPE-RETURN");
}

#[test]
fn cross_check_agreement() {
    // 受理・拒否のどちらでも、検証済み部品と判定が食い違わない（codes が確かめる）
    let accepted = [
        "fn f(s: String) -> String = s entry f",
        "fn f(c: Char) -> Bool = eq(c, '\\'') entry f",
        "fn f(s: String) -> List<String> = list<String>(s, \"\", \"\\\\\") entry f",
        "fn f(s: String) -> Option<Int> = match_option(parse_int(s), none<Int>(), |n| some(add(n, 1))) entry f",
        "fn f(n: Int) -> Option<Char> = char(n) entry f",
        "fn f(n: Int) -> String = concat(to_string(n), \"…\") entry f",
        "type R = { name: String, initial: Char }\nfn f(r: R) -> String = cons(r.initial, r.name) entry f",
        "fn f(s: String) -> Int = // comment with 'quotes\" and é\n length(s) entry f",
    ];
    for src in accepted {
        assert!(codes(src).is_empty(), "{src}: {:?}", codes(src));
    }
    let rejected = [
        "fn f(s: List<Char>) -> String = s entry f",
        "fn f(s: String) -> String = \"\\'\" entry f",
        "fn f(s: String) -> Char = '\\\"' entry f",
        "fn f(s: String) -> Char = 'ab' entry f",
        "fn f(s: String) -> String = \"a\nb\" entry f",
        "fn f(s: String) -> String = \"a\u{7}b\" entry f",
        "fn f(s: String) -> Char = '\u{7}' entry f",
        "fn f(s: String) -> Char = Char entry f",
        "fn f(String: String) -> Int = 1 entry f",
        "fn f(s: String) -> Int = code(s) entry f",
        "fn f(s: String) -> Int = to_string(1) entry f",
        "fn f(s: String) -> Int = s.x entry f",
    ];
    for src in rejected {
        assert!(!codes(src).is_empty(), "{src} should be rejected");
    }
}

#[test]
fn record_with_string_fields_plain() {
    let src = "type P = { name: String, tag: Char }\nfn f(p: P) -> P = P { name: concat(p.name, \"!\"), ..p }\nentry f\n";
    assert_eq!(run(src, r#"{"name": "héllo", "tag": "x"}"#), r#"{"name":"héllo!","tag":"x"}"#);
}
