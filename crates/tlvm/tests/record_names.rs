//! レコードと名前の parity corpus（stage 2・S0）。HEAD の trusted 側（Rust の処理系）の振る舞いを観測どおりに固定する。
//! 後のスライスは、ここでの観測と一致しつづけるかを確かめる。観測が仕様に合うかどうかは判定しない。
//!
//! F1・F2・F13・F15 は stage 2 の計画の危険（リスク）の番号。
//!
//! 覆うもの：
//! - レコードの名前診断 E-RECORD-*（7 コード）、名前の診断 E-NAME-*（6 コード）、field 参照の型の診断
//!   E-TYPE-FIELD-ACCESS。各コードに、それを出すプログラムを一つ以上置く。
//! - Dict の型の書き方（`Dict<K, V>`、引数のない `Dict`、引数の数の誤り）と、Dict と List<Pair> の混同（F15）。
//! - 文脈キーワードの field 名。宣言・構築・参照で、trusted の parser は受理する（F2）。
//! - 型の名前だけが違う、形の同じレコード二つ（F13）。
//! - レコードの宣言を含み、trusted の字句・構文の誤りで拒否するプログラム。検証済み parser との食い違いは出ない（F1）。
//!
//! 診断は (phase, code, expected, actual) で比べる。値のない欄は空文字。どのプログラムにも
//! E-INTERNAL-VERIFIED-MISMATCH が出ないことは `rejected` で確かめる。

use std::process::Command;
use tlvm::api::*;
use tlvm::profiles::*;

mod common;
use common::{rejected, row};

/// 受理したプログラムの (入力の型, 出力の型)。
fn tys(input: &str, output: &str) -> (String, String) {
    (input.into(), output.into())
}

/// 受理したプログラムの (入力の型, 出力の型)。拒否なら診断を出して失敗する。
fn typed(src: &str) -> (String, String) {
    match compile(src.as_bytes(), &StaticProfile::default()) {
        SourceCompile::Result(CompileResult::Accepted { program, .. }) => tys(
            &program.input_type.to_string(),
            &program.output_type.to_string(),
        ),
        SourceCompile::Result(CompileResult::Rejected { errors, .. }) => {
            panic!("拒否された: {src}\n{errors:?}")
        }
        _ => panic!("結果が出ない: {src}"),
    }
}

fn tlvm(args: &[&str]) -> (i32, String, String) {
    let o = Command::new(env!("CARGO_BIN_EXE_tlvm"))
        .args(args)
        .output()
        .unwrap();
    (
        o.status.code().unwrap(),
        String::from_utf8(o.stdout).unwrap(),
        String::from_utf8(o.stderr).unwrap(),
    )
}

fn with_file<T>(src: &str, f: impl FnOnce(&str) -> T) -> T {
    static N: std::sync::atomic::AtomicUsize = std::sync::atomic::AtomicUsize::new(0);
    let n = N.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
    let path = std::env::temp_dir().join(format!("tlvm-corpus-{}-{n}.tlvm", std::process::id()));
    std::fs::write(&path, src).unwrap();
    let r = f(path.to_str().unwrap());
    std::fs::remove_file(&path).unwrap();
    r
}

/// plain JSON で実行した出力。終了コードが 0 でなければ失敗する。
fn run(src: &str, input: &str) -> String {
    with_file(src, |p| {
        let (code, out, err) = tlvm(&["run", p, input, "--plain"]);
        assert_eq!(code, 0, "{err}");
        out.trim_end().to_string()
    })
}

// ---------------------------------------------------------------- 1. レコードの名前診断（E-RECORD-*）

#[test]
fn unknown_record_type_in_a_type_and_in_a_literal() {
    assert_eq!(
        rejected("type P = { a: Int }\nfn f(p: Q) -> Int = 1\nentry f\n"),
        [row("name", "E-RECORD-UNKNOWN-TYPE", "", "Q")]
    );
    assert_eq!(
        rejected("type P = { a: Int }\nfn f(x: Int) -> Int = Q { a: x }.a\nentry f\n"),
        [row("name", "E-RECORD-UNKNOWN-TYPE", "", "Q")]
    );
}

#[test]
fn duplicate_record_type() {
    assert_eq!(
        rejected("type P = { a: Int }\ntype P = { b: Int }\nfn f(p: P) -> Int = 1\nentry f\n"),
        [row("name", "E-RECORD-DUPLICATE-TYPE", "", "P")]
    );
}

#[test]
fn unknown_field_in_a_literal_and_in_an_access() {
    assert_eq!(
        rejected("type P = { a: Int, b: Int }\nfn f(x: Int) -> Int = P { a: x, b: x, z: x }.a\nentry f\n"),
        [row("name", "E-RECORD-UNKNOWN-FIELD", "", "z")]
    );
    assert_eq!(
        rejected("type P = { a: Int, b: Int }\nfn f(p: P) -> Int = p.z\nentry f\n"),
        [row("name", "E-RECORD-UNKNOWN-FIELD", "", "z")]
    );
    // どのレコードも持たない field を値に使う。E-TYPE-FIELD-ACCESS ではなく名前の段階で拒否する。
    assert_eq!(
        rejected("fn f(x: Int) -> Int = x.a\nentry f\n"),
        [row("name", "E-RECORD-UNKNOWN-FIELD", "", "a")]
    );
}

#[test]
fn duplicate_field_in_a_declaration_and_in_a_literal() {
    assert_eq!(
        rejected("type P = { a: Int, a: Int }\nfn f(p: P) -> Int = p.a\nentry f\n"),
        [row("name", "E-RECORD-DUPLICATE-FIELD", "", "a")]
    );
    assert_eq!(
        rejected("type P = { a: Int, b: Int }\nfn f(x: Int) -> Int = P { a: x, a: x, b: x }.a\nentry f\n"),
        [row("name", "E-RECORD-DUPLICATE-FIELD", "", "a")]
    );
}

#[test]
fn missing_field_lists_every_field_that_is_not_written() {
    assert_eq!(
        rejected("type P = { a: Int, b: Int }\nfn f(x: Int) -> Int = P { a: x }.a\nentry f\n"),
        [row("name", "E-RECORD-MISSING-FIELD", "b", "")]
    );
    assert_eq!(
        rejected(
            "type P = { a: Int, b: Int, c: Int }\nfn f(x: Int) -> Int = P { a: x }.a\nentry f\n"
        ),
        [row("name", "E-RECORD-MISSING-FIELD", "b, c", "")]
    );
}

#[test]
fn base_is_redundant_when_every_field_is_written() {
    assert_eq!(
        rejected("type P = { a: Int, b: Int }\nfn f(q: P, x: Int) -> Int = P { a: x, b: x, ..q }.a\nentry f\n"),
        [row("name", "E-RECORD-BASE-REDUNDANT", "", "")]
    );
}

#[test]
fn field_conflict_between_two_record_types() {
    assert_eq!(
        rejected("type P = { a: Int }\ntype Q = { a: Int }\nfn f(q: Q) -> Int = q.a\nentry f\n"),
        [row("name", "E-RECORD-FIELD-CONFLICT", "", "a")]
    );
}

// ---------------------------------------------------------------- 2. 名前の診断（E-NAME-*）と field 参照の型

#[test]
fn name_codes_for_variables_functions_and_parameters() {
    assert_eq!(
        rejected("fn f(x: Int) -> Int = y\nentry f\n"),
        [row("name", "E-NAME-UNBOUND-VARIABLE", "", "y")]
    );
    assert_eq!(
        rejected("fn f(x: Int) -> Int = g(x)\nentry f\n"),
        [row("name", "E-NAME-UNKNOWN-FUNCTION", "", "g")]
    );
    assert_eq!(
        rejected("fn f(x: Int) -> Int = x\nfn f(x: Int) -> Int = x\nentry f\n"),
        [row("name", "E-NAME-DUPLICATE-FUNCTION", "", "f")]
    );
    assert_eq!(
        rejected("fn f(x: Int, x: Int) -> Int = x\nentry f\n"),
        [row("name", "E-NAME-DUPLICATE-PARAM", "", "x")]
    );
}

#[test]
fn name_codes_for_binders_and_shadowing() {
    assert_eq!(
        rejected("fn f(xs: List<Int>) -> Int = fold(xs, 0, |a, a| a)\nentry f\n"),
        [row("name", "E-NAME-DUPLICATE-BINDER", "", "a")]
    );
    assert_eq!(
        rejected("fn f(x: Int) -> Int = let y = 1 in let y = 2 in x\nentry f\n"),
        [row("name", "E-NAME-SHADOW", "", "y")]
    );
}

#[test]
fn field_access_on_a_value_of_another_record_type() {
    assert_eq!(
        rejected("type P = { a: Int }\ntype Q = { b: Int }\nfn f(q: Q) -> Int = q.a\nentry f\n"),
        [row("typecheck", "E-TYPE-FIELD-ACCESS", "P", "Q")]
    );
}

// ---------------------------------------------------------------- 3. Dict の型の書き方と List<Pair> との違い（F15）

#[test]
fn dict_with_two_type_arguments_is_a_type() {
    assert_eq!(
        typed("fn f(d: Dict<Int, String>) -> Dict<Int, String> = d\nentry f\n"),
        tys("Dict<Int, String>", "Dict<Int, String>")
    );
}

#[test]
fn bare_dict_is_read_as_a_record_type_name() {
    // 引数のない Dict は、宣言されていない型の名前として拒否する（組み込みの Dict ではない）。
    for src in [
        "fn f(d: Dict) -> Int = 0\nentry f\n",
        "fn f(x: Int) -> Dict = x\nentry f\n",
        "type R = { d: Dict, n: Int }\nfn f(r: R) -> Int = r.n\nentry f\n",
    ] {
        assert_eq!(
            rejected(src),
            [row("name", "E-RECORD-UNKNOWN-TYPE", "", "Dict")],
            "{src}"
        );
    }
}

#[test]
fn dict_with_one_or_three_type_arguments_is_a_parse_error() {
    assert_eq!(
        rejected("fn f(d: Dict<Int>) -> Int = 0\nentry f\n"),
        [row("parse", "E-PARSE-EXPECTED-TOKEN", ",", ">")]
    );
    assert_eq!(
        rejected("fn f(d: Dict<Int, Int, Int>) -> Int = 0\nentry f\n"),
        [row("parse", "E-PARSE-EXPECTED-TOKEN", ">", ",")]
    );
}

#[test]
fn a_record_named_dict_takes_the_bare_name_only() {
    // Dict という名前のレコードを宣言すると、引数のない Dict はそのレコードを指す。Dict<K, V> は組み込みのまま。
    assert_eq!(
        typed("type Dict = { a: Int }\nfn f(x: Dict) -> Int = x.a\nentry f\n"),
        tys("Dict", "Int")
    );
    assert_eq!(
        typed("type Dict = { a: Int }\nfn f(x: Dict<Int, Int>) -> Int = 1\nentry f\n"),
        tys("Dict<Int, Int>", "Int")
    );
}

#[test]
fn record_with_a_dict_field_is_accepted_and_runs() {
    assert_eq!(
        typed("type Inv = { items: Dict<String, Int>, ops: Int }\nfn f(inv: Inv) -> Int = add(inv.ops, dict_size(inv.items))\nentry f\n"),
        tys("Inv", "Int")
    );
    let src = r#"type Inv = { items: Dict<String, Int>, ops: Int }
fn f(n: Int) -> Int = add(n, dict_size(Inv { items: dict_put(dict<String, Int>(), "a", n), ops: 1 }.items))
entry f
"#;
    assert_eq!(run(src, "5"), "6");
}

#[test]
fn dict_and_list_of_pairs_are_rejected_by_the_typechecker_in_every_position() {
    // 型検査は Dict を消去する前に行うので、Dict と List<Pair> の混同は trusted 側の型の診断になる。
    assert_eq!(
        rejected("fn g(d: Dict<Int, Int>) -> Int = dict_size(d)\nfn f(xs: List<Pair<Int, Int>>) -> Int = g(xs)\nentry f\n"),
        [row("typecheck", "E-TYPE-ARG", "Dict<Int, Int>", "List<Pair<Int, Int>>")]
    );
    assert_eq!(
        rejected("fn g(xs: List<Pair<Int, Int>>) -> Int = 1\nfn f(d: Dict<Int, Int>) -> Int = g(d)\nentry f\n"),
        [row("typecheck", "E-TYPE-ARG", "List<Pair<Int, Int>>", "Dict<Int, Int>")]
    );
    assert_eq!(
        rejected("fn f(d: Dict<String, Int>) -> List<Pair<String, Int>> = d\nentry f\n"),
        [row(
            "typecheck",
            "E-TYPE-RETURN",
            "List<Pair<String, Int>>",
            "Dict<String, Int>"
        )]
    );
    // Dict の field に List<Pair> を入れる。診断は field の値ではなく、レコードの構築の全体に付く（展開後の pair の型と比べる）。
    assert_eq!(
        rejected("type Inv = { items: Dict<String, Int>, ops: Int }\nfn f(xs: List<Pair<String, Int>>) -> Int = Inv { items: xs, ops: 1 }.ops\nentry f\n"),
        [row("typecheck", "E-TYPE-ARG", "Inv", "Pair<List<Pair<String, Int>>, Int>")]
    );
}

// ---------------------------------------------------------------- 4. 文脈キーワードの field 名（F2）

#[test]
fn context_keyword_field_names_are_accepted_in_declaration_literal_and_access() {
    let src = "type S = { dict: Int, length: Int, min: Int }\nfn f(s: S) -> S = S { dict: add(s.dict, 1), length: s.length, min: s.min }\nentry f\n";
    assert_eq!(typed(src), tys("S", "S"));
    assert_eq!(
        run(src, r#"{"dict":1,"length":2,"min":3}"#),
        r#"{"dict":2,"length":2,"min":3}"#
    );
    assert_eq!(
        typed("type S = { dict: Int, length: Int, min: Int }\nfn f(s: S) -> Int = add(s.dict, add(s.length, s.min))\nentry f\n"),
        tys("S", "Int")
    );
}

#[test]
fn reserved_words_are_rejected_as_field_names_and_other_words_are_accepted() {
    // 予約語（let・in・true）は field 名にできない。
    for w in ["let", "in", "true"] {
        let src = format!("type P = {{ {w}: Int }}\nfn f(p: P) -> Int = 1\nentry f\n");
        assert_eq!(
            rejected(&src),
            [row("parse", "E-PARSE-EXPECTED-IDENT", "identifier", w)],
            "{src}"
        );
    }
    // それ以外は field 名として受理する（entry・type・rec・_・大文字で始まる名・Dict）。
    for w in ["entry", "type", "rec", "_", "A", "Dict"] {
        let src = format!("type P = {{ {w}: Int }}\nfn f(p: P) -> Int = 1\nentry f\n");
        assert_eq!(typed(&src), tys("P", "Int"), "{src}");
    }
}

// ---------------------------------------------------------------- 5. 型の名前の書き方

#[test]
fn soft_word_in_a_type_position_is_a_parse_error() {
    assert_eq!(
        rejected("fn f(x: length) -> Int = 1\nentry f\n"),
        [row("parse", "E-PARSE-EXPECTED-TYPE", "type", "length")]
    );
    assert_eq!(
        rejected("type P = { a: length }\nfn f(p: P) -> Int = 1\nentry f\n"),
        [row("parse", "E-PARSE-EXPECTED-TYPE", "type", "length")]
    );
}

#[test]
fn soft_word_or_builtin_type_word_as_a_record_type_name_is_a_parse_error() {
    assert_eq!(
        rejected("type length = { a: Int }\nfn f(p: length) -> Int = p.a\nentry f\n"),
        [
            row("parse", "E-PARSE-EXPECTED-IDENT", "identifier", "length"),
            row("parse", "E-PARSE-EXPECTED-TYPE", "type", "length"),
        ]
    );
    assert_eq!(
        rejected("type Int = { a: Int }\nfn f(p: Int) -> Int = 1\nentry f\n"),
        [row("parse", "E-PARSE-EXPECTED-IDENT", "identifier", "Int")]
    );
}

#[test]
fn record_type_name_need_not_start_with_an_uppercase_letter() {
    assert_eq!(
        typed("type p = { a: Int }\nfn f(x: p) -> Int = x.a\nentry f\n"),
        tys("p", "Int")
    );
}

#[test]
fn type_parameters_must_start_with_an_uppercase_letter() {
    assert_eq!(
        rejected("type G<t> = { v: Int }\nfn f(g: G<Int>) -> Int = g.v\nentry f\n"),
        [row(
            "parse",
            "E-PARSE-EXPECTED-IDENT",
            "type parameter name starting with an uppercase letter",
            "t"
        )]
    );
    assert_eq!(
        typed("type G<T> = { v: T, w: Int }\nfn f(g: G<Int>) -> Int = add(g.v, g.w)\nentry f\n"),
        tys("G<Int>", "Int")
    );
}

#[test]
fn trailing_commas_in_record_declarations_and_literals_are_accepted() {
    assert_eq!(
        typed("type P = { a: Int, b: Int, }\nfn f(p: P) -> Int = p.a\nentry f\n"),
        tys("P", "Int")
    );
    assert_eq!(
        typed("type P = { a: Int, b: Int }\nfn f(x: Int) -> Int = P { a: x, b: x, }.a\nentry f\n"),
        tys("Int", "Int")
    );
}

// ---------------------------------------------------------------- 6. レコードの宣言を含み、構文の誤りで拒否するプログラム（F1）

#[test]
fn record_program_with_a_trusted_syntax_error_raises_no_verified_mismatch() {
    // 字句・構文で拒否したプログラムは、元の文字列を検証済み parser にも通す（api.rs の Failed の経路）。
    // 検証済み parser が受理すれば E-INTERNAL-VERIFIED-MISMATCH が付く。ここでは、どの場合も付かない。
    let cases = [
        (
            "type P = { a Int, b: Int }\nfn f(p: P) -> Int = p.b\nentry f\n",
            vec![row("parse", "E-PARSE-EXPECTED-TOKEN", ":", "Int")],
        ),
        (
            "type P = { a: Int, b: Int }\nfn f(x: Int) -> Int = P { a: x b: x }.a\nentry f\n",
            vec![row("parse", "E-PARSE-EXPECTED-TOKEN", "}", "b")],
        ),
        (
            "type P = { a: Int; b: Int }\nfn f(p: P) -> Int = p.a\nentry f\n",
            vec![row("lex", "E-LEX-UNEXPECTED-CHARACTER", "", "';'")],
        ),
        (
            "type P = { d: Dict<Int>, n: Int }\nfn f(p: P) -> Int = p.n\nentry f\n",
            vec![row("parse", "E-PARSE-EXPECTED-TOKEN", ",", ">")],
        ),
        (
            "type P = { let: Int }\nfn f(p: P) -> Int = 1\nentry f\n",
            vec![row("parse", "E-PARSE-EXPECTED-IDENT", "identifier", "let")],
        ),
        (
            "type G<t> = { v: Int }\nfn f(g: G<Int>) -> Int = g.v\nentry f\n",
            vec![row(
                "parse",
                "E-PARSE-EXPECTED-IDENT",
                "type parameter name starting with an uppercase letter",
                "t",
            )],
        ),
        (
            "type E = { }\nfn f(x: Int) -> Int = x\nentry f\n",
            vec![row("parse", "E-PARSE-EXPECTED-IDENT", "identifier", "}")],
        ),
    ];
    for (src, want) in cases {
        assert_eq!(rejected(src), want, "{src}");
    }
}

// ---------------------------------------------------------------- 7. 形の同じレコードが二つあるとき（F13）

#[test]
fn records_with_the_same_fields_cannot_both_be_declared() {
    // 型の名前だけが違い、形が同じ二つ。field 名が重なるので、宣言の段階（名前）で拒否し、型検査には進まない。
    assert_eq!(
        rejected("type A = { x: Int, y: Int }\ntype B = { x: Int, y: Int }\nfn f(a: A) -> B = a\nentry f\n"),
        [
            row("name", "E-RECORD-FIELD-CONFLICT", "", "x"),
            row("name", "E-RECORD-FIELD-CONFLICT", "", "y"),
        ]
    );
}

#[test]
fn records_with_different_fields_are_different_types() {
    assert_eq!(
        rejected("type A = { x: Int }\ntype B = { y: Int }\nfn f(a: A) -> B = a\nentry f\n"),
        [row("typecheck", "E-TYPE-RETURN", "B", "A")]
    );
}
