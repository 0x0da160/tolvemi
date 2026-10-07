//! 設計書の外側の便宜（普通の JSON での入出力、修復ヒント、人間向けの診断表示、tlvm test）のテスト。

use std::process::Command;
use tlvm::api::*;
use tlvm::diagnostics::{line_col, render_human};
use tlvm::plain::encode_plain;
use tlvm::profiles::*;
use tlvm::syntax::Ty;
use tlvm::values::encode_value;
use tlvm::DecodeResult;

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

#[test]
fn plain_json_roundtrip() {
    let int = Ty::int;
    roundtrip(&int(), "-42", r#"{"tag":"int","value":"-42"}"#);
    roundtrip(&Ty::bool(), "true", r#"{"tag":"bool","value":true}"#);
    roundtrip(&Ty::unit(), "null", r#"{"tag":"unit"}"#);
    roundtrip(&Ty::list(int()), "[1,2]", r#"{"tag":"list","items":[{"tag":"int","value":"1"},{"tag":"int","value":"2"}]}"#);
    roundtrip(&Ty::pair(int(), Ty::bool()), "[1,false]", r#"{"tag":"pair","left":{"tag":"int","value":"1"},"right":{"tag":"bool","value":false}}"#);
    roundtrip(&Ty::option(int()), "null", r#"{"tag":"none"}"#);
    roundtrip(&Ty::option(int()), "7", r#"{"tag":"some","value":{"tag":"int","value":"7"}}"#);
    // null になりうる payload は {"some": v} で包む
    roundtrip(&Ty::option(Ty::unit()), r#"{"some":null}"#, r#"{"tag":"some","value":{"tag":"unit"}}"#);
    let oo = Ty::option(Ty::option(int()));
    roundtrip(&oo, r#"{"some":null}"#, r#"{"tag":"some","value":{"tag":"none"}}"#);
    roundtrip(&oo, r#"{"some":3}"#, r#"{"tag":"some","value":{"tag":"some","value":{"tag":"int","value":"3"}}}"#);
    roundtrip(&oo, "null", r#"{"tag":"none"}"#);
    // JavaScript の安全な整数（|n| <= 2^53 - 1）を超えると十進文字列で出す
    roundtrip(&int(), "9007199254740991", r#"{"tag":"int","value":"9007199254740991"}"#);
    roundtrip(&int(), "-9007199254740991", r#"{"tag":"int","value":"-9007199254740991"}"#);
    roundtrip(&int(), r#""9007199254740992""#, r#"{"tag":"int","value":"9007199254740992"}"#);
    roundtrip(&int(), r#""-123456789012345678901""#, r#"{"tag":"int","value":"-123456789012345678901"}"#);
}

#[test]
fn plain_json_accepts_whitespace_and_string_integers() {
    let t = Ty::list(Ty::int());
    let big = "123456789012345678901234567890";
    assert_eq!(
        plain_decode(&t, &format!(" [ \"{big}\" , -0 ] ")),
        Err(vec!["E-INPUT-INTEGER"]),
        "-0 は正規形ではない"
    );
    assert_eq!(plain_decode(&t, &format!(" [ \"{big}\" ] ")).unwrap(), format!(r#"{{"tag":"list","items":[{{"tag":"int","value":"{big}"}}]}}"#));
}

#[test]
fn plain_json_errors() {
    let int = Ty::int;
    assert_eq!(plain_decode(&int(), "1.0"), Err(vec!["E-INPUT-INTEGER"]));
    assert_eq!(plain_decode(&int(), "1e3"), Err(vec!["E-INPUT-INTEGER"]));
    assert_eq!(plain_decode(&int(), "\"01\""), Err(vec!["E-INPUT-INTEGER"]));
    assert_eq!(plain_decode(&int(), "true"), Err(vec!["E-INPUT-FIELD-TYPE"]));
    assert_eq!(plain_decode(&Ty::pair(int(), int()), "[1]"), Err(vec!["E-INPUT-FIELD-TYPE"]));
    assert_eq!(plain_decode(&Ty::option(Ty::unit()), "null").unwrap(), r#"{"tag":"none"}"#);
    assert_eq!(plain_decode(&Ty::option(Ty::unit()), "{}"), Err(vec!["E-INPUT-MISSING-FIELD"]));
    assert_eq!(plain_decode(&Ty::option(Ty::unit()), r#"{"some":null,"x":1}"#), Err(vec!["E-INPUT-UNKNOWN-FIELD"]));
    assert_eq!(plain_decode(&int(), "[1,"), Err(vec!["E-INPUT-JSON-SYNTAX"]));
    assert_eq!(plain_decode(&Ty::list(int()), r#"{"a":1,"a":2}"#), Err(vec!["E-INPUT-DUPLICATE-KEY"]));
    assert_eq!(plain_decode(&int(), "\u{0}"), Err(vec!["E-INPUT-JSON-SYNTAX"]));
}

#[test]
fn plain_json_limits_are_counted_on_plain_input() {
    let t = Ty::list(Ty::list(Ty::int()));
    let p = InputProfile { value_depth: 2, ..InputProfile::default() };
    match decode_plain_input(&t, b"[[1]]", &p) {
        DecodeResult::Invalid(d) => assert_eq!(d[0].code, "E-LIMIT-INPUT-VALUE-DEPTH"),
        other => panic!("{other:?}"),
    }
    let p = InputProfile { value_nodes: 3, ..InputProfile::default() };
    match decode_plain_input(&t, b"[[1,2]]", &p) {
        DecodeResult::Invalid(d) => assert_eq!(d[0].code, "E-LIMIT-INPUT-VALUE-NODES"),
        other => panic!("{other:?}"),
    }
    let p = InputProfile { json_bytes: 4, ..InputProfile::default() };
    match decode_plain_input(&t, b"[[1]]", &p) {
        DecodeResult::Invalid(d) => assert_eq!(d[0].code, "E-LIMIT-INPUT-JSON-BYTES"),
        other => panic!("{other:?}"),
    }
}

fn errors(src: &str) -> Vec<tlvm::diagnostics::Diagnostic> {
    match compile(src.as_bytes(), &StaticProfile::default()) {
        SourceCompile::Result(r) => r.errors().to_vec(),
        SourceCompile::SourceBoundaryFailure => panic!("boundary"),
    }
}

#[test]
fn repairs_on_source_diagnostics() {
    let d = &errors("fn f(x: Int) -> Int = lt(x, 1) entry f")[0];
    assert_eq!(d.code, "E-TYPE-RETURN");
    assert_eq!(
        d.to_json(),
        r#"{"severity":"error","phase":"typecheck","code":"E-TYPE-RETURN","span":{"start":22,"end":30},"expected":"Int","actual":"Bool","message":"関数本体の型が宣言した戻り型と一致しません","repair":{"kind":"replace_expression","target_span":{"start":22,"end":30},"constraint":"expression of type Int"}}"#
    );
    let d = &errors("fn f(xs: List<Int>) -> Int = fold(xs, 0, |acc, x| add(acc, y)) entry f")[0];
    assert_eq!(d.code, "E-NAME-UNBOUND-VARIABLE");
    assert_eq!(d.repair.as_ref().unwrap().constraint, "variable in scope: x, acc, xs");
    let d = &errors("fn f(x: Int) -> Int = ad(x, 1) entry f")[0];
    assert_eq!(d.repair.as_ref().unwrap().constraint, "defined function or builtin, e.g. add");
    let d = &errors("fn f(x: Int) -> Int = add(x) entry f")[0];
    assert_eq!(d.repair.as_ref().unwrap().constraint, "call with 2 arguments");
    let d = &errors("fn f(x: Int) -> Int = x")[0];
    let r = d.repair.as_ref().unwrap();
    assert_eq!((r.kind, r.target_span), ("insert_text", (23, 23)));
    // 予約語を名前に使ったときは、その語と別名を示す。回復後に続くエラーには付けない
    let ds = errors("fn f(xs: List<Int>) -> Int = fold(xs, 0, |acc, entry| add(acc, entry)) entry f");
    assert_eq!(ds[0].code, "E-PARSE-EXPECTED-IDENT");
    assert_eq!(ds[0].repair.as_ref().unwrap().constraint, "'entry' is a reserved word; use another name such as entry_ here and at every use");
    assert!(ds[1..].iter().all(|d| d.repair.is_none()));
    // 欠けた区切り記号の位置は一意に決まらないので出さない
    let d = &errors("fn f(x: Int) -> Int = add(x 1) entry f")[0];
    assert_eq!(d.code, "E-PARSE-EXPECTED-TOKEN");
    assert!(d.repair.is_none());
    // 括弧の過不足には、閉じようとしている開き括弧の位置を示す
    let d = &errors("fn f(x: Int) -> Int =\n  if(lt(x, 0), neg(x)), x)\nentry f")[0];
    let r = d.repair.as_ref().unwrap();
    assert_eq!((r.kind, r.target_span), ("delete_span", (43, 44)));
    assert!(r.constraint.contains("'if(' opened at line 2, column 3"), "{}", r.constraint);
    let d = &errors("fn f(x: Int) -> Pair<Int, Int> =\n  pair(add(x, 1), x, x)\nentry f")[0];
    assert!(d.repair.as_ref().unwrap().constraint.contains("'pair(' opened at line 2, column 3"));
    let d = &errors("fn f(x: Int) -> List<Int> = list<Int>(1, x\nentry f")[0];
    assert!(d.repair.as_ref().unwrap().constraint.contains("'list<...>(' opened at line 1, column 29"));
}

#[test]
fn no_repairs_on_ast_api() {
    let ast = br#"{"codec":"ast_codec_v1","declarations":[{"tag":"fn","name":"f","params":[{"name":"x","type":{"tag":"int"}}],"return_type":{"tag":"int"},"body":{"tag":"var","name":"y"}},{"tag":"entry","name":"f"}]}"#;
    match compile_ast(ast, &StaticProfile::default(), &AstTransportProfile::default()) {
        AstCompile::Result(r) => {
            assert_eq!(r.errors()[0].code, "E-NAME-UNBOUND-VARIABLE");
            assert!(r.errors().iter().all(|d| d.repair.is_none()));
        }
        _ => panic!("transport failure"),
    }
}

#[test]
fn human_rendering() {
    let src = "fn f(x: Int) -> Int =\n  lt(x, 1)\nentry f\n";
    assert_eq!(line_col(src.as_bytes(), 24), (2, 3));
    let d = &errors(src)[0];
    assert_eq!(
        render_human(d, "a.tlvm", src.as_bytes()),
        "a.tlvm:2:3: error[E-TYPE-RETURN]: 関数本体の型が宣言した戻り型と一致しません (expected Int, found Bool)\n 2 |   lt(x, 1)\n   |   ^^^^^^^^\n = repair (replace_expression): expression of type Int"
    );
}

fn tlvm(args: &[&str]) -> (i32, String, String) {
    let o = Command::new(env!("CARGO_BIN_EXE_tlvm"))
        .args(args)
        .current_dir(concat!(env!("CARGO_MANIFEST_DIR"), "/../.."))
        .output()
        .unwrap();
    (o.status.code().unwrap(), String::from_utf8(o.stdout).unwrap(), String::from_utf8(o.stderr).unwrap())
}

#[test]
fn cli_run_plain() {
    let (code, out, _) = tlvm(&["run", "examples/positive_values.tlvm", "[3,-1,2]", "--plain"]);
    assert_eq!((code, out.as_str()), (0, "[3,2]\n"));
    let (code, _, err) = tlvm(&["run", "examples/positive_values.tlvm", "[3,true]", "--plain", "--human"]);
    assert_eq!(code, 1);
    assert!(err.starts_with("<input>:1:4: error[E-INPUT-FIELD-TYPE]"), "{err}");
}

#[test]
fn cli_test_examples() {
    for f in ["examples/sum_even.tlvm", "examples/positive_values.tlvm"] {
        let (code, out, err) = tlvm(&["test", f]);
        assert_eq!(code, 0, "{f}: {out}{err}");
        assert!(out.ends_with("\"failed\":0}\n"), "{out}");
    }
}

#[test]
fn cli_test_reports_failures() {
    let dir = std::env::temp_dir().join(format!("tlvm-test-{}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    let cases = dir.join("cases.json");
    std::fs::write(&cases, r#"[{"name":"wrong","input":[1,2],"expected":[2]},{"input":[1,true],"expected":[]}]"#).unwrap();
    let (code, out, err) = tlvm(&["test", "examples/positive_values.tlvm", cases.to_str().unwrap()]);
    std::fs::remove_dir_all(&dir).unwrap();
    assert_eq!(code, 1);
    assert_eq!(
        out,
        "{\"case\":\"wrong\",\"result\":\"fail\",\"expected\":[2],\"actual\":[1,2]}\n{\"case\":\"#2\",\"result\":\"error\",\"reason\":\"input を型 List<Int> として読めません\"}\n{\"passed\":0,\"failed\":2}\n"
    );
    // 診断の span は cases ファイル上の位置
    assert!(err.contains("\"span\":{\"start\":59,\"end\":63}"), "{err}");
}
