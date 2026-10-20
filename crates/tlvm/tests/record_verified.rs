//! 宣言の名前と番号の規則を、検証済みの部品と信頼側で突き合わせる（stage 2・S2a と S2b）。
//!
//! V1：宣言だけのプログラムで、検証済みの `parse_e` と `resolve_e` の受理が、信頼側の受理・拒否と一致する。
//!     対象は宣言の四つの符号（E-RECORD-UNKNOWN-TYPE、E-RECORD-DUPLICATE-TYPE、E-RECORD-DUPLICATE-FIELD、
//!     E-RECORD-FIELD-CONFLICT）と、それを出さない宣言の形（前方の型の参照、関数の注釈の前方参照、
//!     型名と関数名の一致、字段の型に既知の記録、直和型の中身に前の記録）。
//! V2：記録と直和型をまたぐ型名の重複（E-RECORD-DUPLICATE-TYPE）。宣言の順を変えても拒否する。
//! V3：記録、直和型、再帰する直和型を混ぜた corpus で、検証済みの宣言の番号（`decl_numbers_e`）が、
//!     信頼側の `Tags::of` の番号と宣言ごとに一致する。関数と entry を挟む形を含み、数え方が違えば食い違う。
//! S2c：再帰する直和型の項（記録と直和型の項は拒否する。recursive.rs:563）の parity。信頼側が受理するが
//!     設計の規則が禁じる形は、既知の食い違いとして固定する（信頼側は変えない）。
//!
//! V4（S3a）：式の符号（記録の構築と参照：UNKNOWN-FIELD、MISSING-FIELD、DUPLICATE-FIELD、BASE-REDUNDANT、
//!     UNKNOWN-TYPE）の受理・拒否が、信頼側の符号と一致する。
//! V5（S3a）：記録の式の実行。記録を展開せずに検証済みの compile_source と run_input_json に渡した出力が、
//!     信頼側の実行（展開してから検証済みの評価器で走らせる）と一致する。基を let で束縛する形を含む。
//!
//! S3b（V6）：印つきの写しの参照と更新（resolve_tagged_e と検証済みの型検査）。
//! S3c：入れ子の名前つきの字段（印つきの写し）。信頼側が受理する入れ子は受理し、拒否する入れ子は拒否する。
//! V7（S5a）：展開段階の名前の診断の corpus。突き合わせに入るコード（api.rs の CHECKED_EXPANSION_CODES）は、
//! 検証済みの parser が通り resolver が拒否する。どの例でも検証済みとの食い違い（E-INTERNAL-VERIFIED-MISMATCH）は出ない。
//! 検証済みの部品は直接呼ぶ（api の突き合わせは通さない）。直和型は核の型にまだ入らないので、
//! 直和型を関数の注釈や式に使うプログラムは含めない（段階 3）。

use tlvm::api::*;
use tlvm::nominal::Tags;
use tlvm::profiles::*;
use tlvm::syntax::Decl;
use tlvm::embed::Program;
use tlvm::plain::encode_plain_with;
use tlvm::values::DecodeResult;
use tlvm_verified::eval::Limits;
use tlvm_verified::pipeline::{compile_source, run_input_json, Compiled, InputRun};
use tlvm_verified::check::check_prog;
use tlvm_verified::ir::EProg;
use tlvm_verified::resolve::{decl_numbers_e, resolve_e, resolve_tagged_e};
use tlvm_verified::surface::{parse_e, SDecl};

mod common;
use common::rejected;

const MISMATCH: &str = "E-INTERNAL-VERIFIED-MISMATCH";

/// 信頼側の判定。受理なら None、拒否なら診断の (phase, code) の列。検証済み部品との食い違いは出てはいけない。
fn trusted(src: &str) -> Option<Vec<(String, String)>> {
    match compile(src.as_bytes(), &StaticProfile::default()) {
        SourceCompile::Result(CompileResult::Accepted { .. }) => None,
        SourceCompile::Result(CompileResult::Rejected { errors, .. }) => {
            let rows: Vec<(String, String)> = errors
                .iter()
                .map(|d| (d.phase.to_string(), d.code.to_string()))
                .collect();
            assert!(
                rows.iter().all(|r| r.1 != MISMATCH),
                "検証済み部品との食い違い: {src}\n{rows:?}"
            );
            Some(rows)
        }
        _ => panic!("結果が出ない: {src}"),
    }
}

/// 検証済みの解析。深さの上限は api の depth_bounds と同じ。
fn verified_parse(src: &str) -> Option<Vec<SDecl>> {
    let p = StaticProfile::default();
    let (d, td) = (p.expr_depth, p.type_depth.saturating_mul(2).saturating_add(2));
    let chars: Vec<char> = src.chars().collect();
    parse_e(&chars, d, td)
}

/// 検証済みの受理：parse_e が通り、resolve_e が通る。
fn verified_accepts(src: &str) -> bool {
    match verified_parse(src) {
        Some(sp) => resolve_e(&sp).is_some(),
        None => false,
    }
}

/// 信頼側が期待どおりに判定し（拒否なら、その符号だけを出す）、検証済みの受理が信頼側の受理と一致する。
fn check(src: &str, want: Option<&str>) {
    let t = trusted(src);
    match want {
        Some(code) => {
            let rows = t.clone().unwrap_or_else(|| panic!("受理された: {src}"));
            let codes: Vec<&str> = rows.iter().map(|r| r.1.as_str()).collect();
            assert_eq!(codes, [code], "信頼側の符号が違う: {src}");
        }
        None => assert!(t.is_none(), "拒否された: {src}\n{t:?}"),
    }
    assert_eq!(
        verified_accepts(src),
        want.is_none(),
        "検証済みの受理が信頼側と違う: {src}"
    );
}

// ---------------------------------------------------------------- V1：宣言の四つの符号と、それを出さない形

/// (プログラム, 信頼側の期待する拒否の符号。受理なら None)。関数は記録と直和型を式に使わない。
const V1: &[(&str, Option<&str>)] = &[
    // E-RECORD-UNKNOWN-TYPE：字段の型が未知、後で宣言、自己参照
    ("type P = { a: Q }\nfn f(a: Int) -> Int = a\nentry f\n", Some("E-RECORD-UNKNOWN-TYPE")),
    ("type P = { q: Q }\ntype Q = { a: Int }\nfn f(a: Int) -> Int = a\nentry f\n", Some("E-RECORD-UNKNOWN-TYPE")),
    ("type R = { r: R }\nfn f(a: Int) -> Int = a\nentry f\n", Some("E-RECORD-UNKNOWN-TYPE")),
    // E-RECORD-UNKNOWN-TYPE：直和型の中身が後で宣言した記録、後で宣言した直和型
    ("type S = V(B) | W\ntype B = { x: Int }\nfn f(a: Int) -> Int = a\nentry f\n", Some("E-RECORD-UNKNOWN-TYPE")),
    ("type T = V(S) | U\ntype S = X | Y\nfn f(a: Int) -> Int = a\nentry f\n", Some("E-RECORD-UNKNOWN-TYPE")),
    // E-RECORD-DUPLICATE-TYPE：同じ名前の記録が二つ
    ("type P = { a: Int }\ntype P = { b: Int }\nfn f(a: Int) -> Int = a\nentry f\n", Some("E-RECORD-DUPLICATE-TYPE")),
    // E-RECORD-DUPLICATE-FIELD：同じ記録の中で字段名が重なる
    ("type R = { s: Int, s: Int }\nfn f(a: Int) -> Int = a\nentry f\n", Some("E-RECORD-DUPLICATE-FIELD")),
    // E-RECORD-FIELD-CONFLICT：別の記録と字段名が重なる
    ("type A = { x: Int }\ntype B = { x: Int }\nfn f(a: Int) -> Int = a\nentry f\n", Some("E-RECORD-FIELD-CONFLICT")),
    // 受理：記録の字段が前の記録を使う。関数の注釈が後の記録を使う（現行の読み方）。型名と関数名の一致
    ("type A = { x: Int }\ntype B = { a: A, y: Int }\nfn f(b: B) -> Int = 1\nentry f\n", None),
    ("fn f(p: P) -> Int = 1\ntype P = { a: Int }\nentry f\n", None),
    ("type P = { a: Int }\nfn P(a: Int) -> Int = a\nentry P\n", None),
    // 受理：直和型の中身に前の記録、記録の字段に前の直和型（使わない）、直和型だけの宣言
    ("type B = { x: Int }\ntype S = V(B) | W\nfn f(a: Int) -> Int = a\nentry f\n", None),
    ("type S = X | Y\ntype R = { s: S, n: Int }\nfn f(a: Int) -> Int = a\nentry f\n", None),
    ("type S = V | W\nfn f(a: Int) -> Int = a\nentry f\n", None),
    // 受理：字段名の重なりがない二つの記録、字段が一つの記録を関数の注釈に使う
    ("type A = { x: Int }\ntype B = { y: Int }\nfn f(a: A) -> Int = 1\nentry f\n", None),
    ("type P = { a: Int, b: Bool }\nfn f(p: P) -> Int = 1\nentry f\n", None),
];

/// V2：記録と直和型をまたぐ型名の重複。宣言の順を変えても、どちらも拒否する。
const V2: &[(&str, Option<&str>)] = &[
    ("type A = { x: Int }\ntype A = V | W\nfn f(a: Int) -> Int = a\nentry f\n", Some("E-RECORD-DUPLICATE-TYPE")),
    ("type A = V | W\ntype A = { x: Int }\nfn f(a: Int) -> Int = a\nentry f\n", Some("E-RECORD-DUPLICATE-TYPE")),
    ("type A = V | W\ntype A = X | Y\nfn f(a: Int) -> Int = a\nentry f\n", Some("E-RECORD-DUPLICATE-TYPE")),
    ("type A = { x: Int }\ntype B = V | W\nfn f(a: Int) -> Int = a\nentry f\n", None),
];

#[test]
fn v1_declaration_codes_agree_with_the_verified_resolver() {
    for (src, want) in V1 {
        check(src, *want);
    }
}

#[test]
fn v2_record_and_sum_with_one_name_are_rejected_in_either_order() {
    for (src, want) in V2 {
        check(src, *want);
    }
}

// ---------------------------------------------------------------- V3：宣言の番号（記録と直和型）

/// 信頼側の宣言の並び：各宣言の種類（'R' 記録、'S' 直和型、'F' 関数、'E' entry）と、Tags::of の番号（型の宣言だけ）。
fn trusted_decls(src: &str) -> Vec<(char, Option<usize>)> {
    let p = match parse_source(src.as_bytes(), &StaticProfile::default()) {
        Parsed::Program(p) => p,
        Parsed::Failed(_) => panic!("解析できない: {src}"),
    };
    let tags = Tags::of(&p);
    p.declarations
        .iter()
        .map(|d| match d {
            Decl::Type(t) => ('R', tags.get(&t.name)),
            Decl::Sum(s) => ('S', tags.get(&s.name)),
            Decl::Fn(_) => ('F', None),
            Decl::Entry(_) => ('E', None),
        })
        .collect()
}

/// 検証済みの番号（宣言の順。型の宣言なら番号、関数と entry なら None）。解析と名前表が通るときだけ。
fn verified_numbers(src: &str) -> Option<Vec<Option<usize>>> {
    let sp = verified_parse(src)?;
    decl_numbers_e(&sp)
}

/// V3 の corpus：記録、直和型、再帰する直和型を混ぜ、関数と entry を挟む。どれも信頼側と検証済みの両方で受理される。
const V3: &[&str] = &[
    // 関数を挟む：宣言の位置で数えると、後の記録の番号がずれる
    "type A = { x: Int }\nfn f(a: Int) -> Int = a\ntype B = { y: Int }\nentry f\n",
    // 直和型を挟む：記録だけで数えると、後の記録の番号がずれる
    "type S = V | W\ntype R = { r: Int }\nfn f(a: Int) -> Int = a\nentry f\n",
    "type A = { x: Int }\ntype S = P(A) | Q\ntype B = { y: Int }\nfn f(a: Int) -> Int = a\nentry f\n",
    // 再帰する直和型：自分を参照する中身も、一つの番号を持つ
    "type L = Nil | Cons(Int, L)\ntype P = { a: Int }\nfn f(a: Int) -> Int = a\nentry f\n",
    "type P = { a: Int }\ntype L = Nil | Cons(Int, L)\ntype Q = { b: L }\nfn f(a: Int) -> Int = a\nentry f\n",
    // 関数を先頭に置く
    "fn f(a: Int) -> Int = a\ntype T = X(Int) | Y\ntype P = { a: Int }\nentry f\n",
];

#[test]
fn v3_numbers_agree_with_tags_of() {
    // 誤った数え方（宣言の位置で数える、記録だけを数える）と比べると、corpus のどこかで食い違う。
    let mut position_differs = false;
    let mut records_only_differs = false;
    for src in V3 {
        assert!(trusted(src).is_none(), "信頼側が拒否した: {src}");
        let decls = trusted_decls(src);
        let want: Vec<Option<usize>> = decls.iter().map(|x| x.1).collect();
        let got = verified_numbers(src).unwrap_or_else(|| panic!("検証済みの番号が出ない: {src}"));
        assert_eq!(got, want, "番号が違う: {src}");
        // 宣言の位置で数える（関数と entry も数える）。
        let by_position: Vec<Option<usize>> = decls
            .iter()
            .enumerate()
            .map(|(i, x)| if x.0 == 'R' || x.0 == 'S' { Some(i) } else { None })
            .collect();
        // 記録だけを数える（直和型は数えず、その時点の記録の数を番号にする）。
        let mut recs: usize = 0;
        let by_records: Vec<Option<usize>> = decls
            .iter()
            .map(|x| match x.0 {
                'R' => {
                    recs += 1;
                    Some(recs - 1)
                }
                'S' => Some(recs),
                _ => None,
            })
            .collect();
        position_differs |= by_position != want;
        records_only_differs |= by_records != want;
    }
    assert!(position_differs, "corpus に、宣言の位置で数えた番号と違う例がない");
    assert!(records_only_differs, "corpus に、記録だけで数えた番号と違う例がない");
}

// ---------------------------------------------------------------- S2c：再帰する直和型の項と、前方の参照

/// 再帰する直和型の項（v1.14）：項の型は Int、Bool、その型自身に限る。信頼側（recursive.rs:563）が拒否する形は、
/// 検証済みも拒否する。受理する形は両方が受理する。
const S2C_RECURSIVE: &[(&str, Option<&str>)] = &[
    // 記録の項（前に宣言した記録、後に宣言した記録）
    ("type P = { a: Int }\ntype L = Nil | Cons(P, L)\nfn f(a: Int) -> Int = a\nentry f\n", Some("E-REC-FIELD-TYPE")),
    ("type L = Nil | Cons(P, L)\ntype P = { a: Int }\nfn f(a: Int) -> Int = a\nentry f\n", Some("E-REC-FIELD-TYPE")),
    ("type R = { s: L }\ntype L = Nil | Cons(R, L)\nfn f(a: Int) -> Int = a\nentry f\n", Some("E-REC-FIELD-TYPE")),
    // 直和型の項（前に宣言した直和型）、Unit、List の項
    ("type S = V | W\ntype L = Nil | Cons(S, L)\nfn f(a: Int) -> Int = a\nentry f\n", Some("E-REC-FIELD-TYPE")),
    ("type L = Nil | Cons(Unit, L)\nfn f(a: Int) -> Int = a\nentry f\n", Some("E-REC-FIELD-TYPE")),
    ("type L = Nil | Cons(List<Int>, L)\nfn f(a: Int) -> Int = a\nentry f\n", Some("E-REC-FIELD-TYPE")),
    // 受理：Int、Bool、その型自身の項だけ（一つだけの自己参照も）
    ("type T = Leaf | Node(T, Int, T)\nfn f(a: Int) -> Int = a\nentry f\n", None),
    ("type T = Leaf | Node(T, Bool, T)\nfn f(a: Int) -> Int = a\nentry f\n", None),
    ("type L = Nil | Cons(L)\nfn f(a: Int) -> Int = a\nentry f\n", None),
    // 受理：再帰する直和型を字段の型に使う記録、再帰しない直和型が記録を項に持つ、再帰する直和型を項に持つ直和型
    ("type L = Nil | Cons(Int, L)\ntype Q = { b: L }\nfn f(a: Int) -> Int = a\nentry f\n", None),
    ("type P = { a: Int }\ntype S = V(P) | W\nfn f(a: Int) -> Int = a\nentry f\n", None),
    ("type L = Nil | Cons(Int, L)\ntype M = Q(L) | N\nfn f(a: Int) -> Int = a\nentry f\n", None),
];

/// 既知の食い違い：信頼側が受理するが、設計の規則（§3.1 行 125：字段と直和型の中身は前に宣言した型に限る。
/// v1.14：再帰する直和型の項は Int、Bool、その型自身に限る）が禁じる形。信頼側のコードは変えない。
/// 検証済みは規則に従って拒否する。信頼側が直ると、このテストが落ちて、食い違いが閉じたと分かる。
const KNOWN_GAPS: &[&str] = &[
    // 再帰する直和型の項に、別の再帰する直和型（v1.14 では自分自身だけ）。kind_of は再帰する型の名前を全部通す（recursive.rs:104-109）
    "type K = Z | S(Int, K)\ntype L = Nil | Cons(K, L)\nfn f(a: Int) -> Int = a\nentry f\n",
    // 相互再帰：後に宣言した型を項に持つ。両方とも再帰する直和型になり、kind_of が通す（recursive.rs:104-109）
    "type A = X(B) | Y\ntype B = Z(A)\nfn f(a: Int) -> Int = a\nentry f\n",
    // 再帰する直和型の項に、後に宣言した再帰する直和型。展開が前方の参照を書き換えてから検査する（recursive.rs:157、api.rs:325）
    "type M = Q(L, M) | N\ntype L = Nil | Cons(Int, L)\nfn f(a: Int) -> Int = a\nentry f\n",
    // 再帰しない直和型の項に、後に宣言した再帰する直和型。同じ理由で前方の参照が見えない（recursive.rs:157、api.rs:325）
    "type M = Q(L) | N\ntype L = Nil | Cons(Int, L)\nfn f(a: Int) -> Int = a\nentry f\n",
];

#[test]
fn s2c_recursive_sum_items_agree_with_the_trusted_side() {
    for (src, want) in S2C_RECURSIVE {
        check(src, *want);
    }
}

#[test]
fn s2c_known_gaps_trusted_accepts_what_the_rule_forbids() {
    for src in KNOWN_GAPS {
        assert!(trusted(src).is_none(), "信頼側が拒否した（既知の食い違いが閉じた。表を直す）: {src}");
        assert!(!verified_accepts(src), "検証済みが受理した（規則に反する）: {src}");
    }
}

// ---------------------------------------------------------------- V4：式の符号（記録の構築と参照）

/// (プログラム, 信頼側の期待する拒否の符号。受理なら None)。名前の段階の符号だけを選ぶ（型検査の符号は含めない）。
const V4: &[(&str, Option<&str>)] = &[
    ("type P = { a: Int, b: Int }\nfn g(x: Int) -> P = P { a: x, b: 2, c: 3 }\nentry g\n", Some("E-RECORD-UNKNOWN-FIELD")),
    ("type P = { a: Int, b: Int }\nfn g(x: Int) -> P = P { a: x }\nentry g\n", Some("E-RECORD-MISSING-FIELD")),
    ("type P = { a: Int, b: Int }\nfn g(x: Int) -> P = P { a: x, a: 2, b: 3 }\nentry g\n", Some("E-RECORD-DUPLICATE-FIELD")),
    ("type P = { a: Int, b: Int }\nfn g(p: P) -> P = P { a: 1, b: 2, ..p }\nentry g\n", Some("E-RECORD-BASE-REDUNDANT")),
    ("type P = { a: Int, b: Int }\nfn g(p: P) -> P = P { a: 1, c: 2, ..p }\nentry g\n", Some("E-RECORD-UNKNOWN-FIELD")),
    ("type P = { a: Int, b: Int }\nfn g(p: P) -> P = Q { a: 1, ..p }\nentry g\n", Some("E-RECORD-UNKNOWN-TYPE")),
    ("type P = { a: Int, b: Int }\nfn g(p: P) -> P = p.zz\nentry g\n", Some("E-RECORD-UNKNOWN-FIELD")),
    ("type P = { a: Int, b: Int }\nfn g(x: Int) -> P = P { a: x, b: 2 }\nentry g\n", None),
    ("type P = { a: Int, b: Int }\nfn g(p: P) -> P = P { a: 1, ..p }\nentry g\n", None),
    ("type P = { a: Int, b: Int }\nfn g(p: P) -> Int = p.a\nentry g\n", None),
    ("type T = { a: Int, b: Int, c: Int }\nfn mk(x: Int) -> T = T { a: x, b: 2, c: 3 }\nfn g(x: Int) -> T = T { a: 1, ..mk(x) }\nentry g\n", None),
];

#[test]
fn v4_record_expression_codes_agree_with_the_verified_resolver() {
    for &(src, want) in V4 {
        check(src, want);
    }
}

// ---------------------------------------------------------------- V5：記録の式の実行

/// 検証済みの入口：記録を展開せずに検証済みの compile_source（rank と rec は信頼側の型付きの値から）へ渡し、
/// 検証済みの run_input_json で実行する。
fn verified_run(src: &str, input: &str) -> String {
    let typed = match compile(src.as_bytes(), &StaticProfile::default()) {
        SourceCompile::Result(CompileResult::Accepted { program, .. }) => program,
        _ => panic!("信頼側が受理しない: {src}"),
    };
    let rank: Vec<usize> = typed
        .program
        .functions()
        .map(|f| typed.rank.get(&f.name).copied().unwrap_or(usize::MAX))
        .collect();
    let rec: Vec<bool> = typed.program.functions().map(|f| f.rec).collect();
    let p = StaticProfile::default();
    let (d, td) = (p.expr_depth, p.type_depth.saturating_mul(2).saturating_add(2));
    let chars: Vec<char> = src.chars().collect();
    let prog = match compile_source(&chars, d, td, rank, rec) {
        Compiled::Accepted(prog) => prog,
        _ => panic!("検証済みが受理しない: {src}"),
    };
    // 入力は信頼側の復号（embed.rs の run_plain と同じ）で値の JSON に直してから、検証済みの復号器へ渡す。
    let tv = match decode_plain_input(&typed.input_type, input.as_bytes(), &InputProfile::default()) {
        DecodeResult::Decoded(tv) => tv,
        _ => panic!("入力の復号が失敗: {src}"),
    };
    let lim = Limits {
        steps: 1_000_000,
        integer_bits: 4_096,
        allocated_nodes: 1_000_000,
        max_depth: 100_000,
        max_slots: 100_000,
    };
    match run_input_json(&prog, &tv.text, tv.json_depth, lim) {
        // 出力は正準の値の JSON なので、信頼側の run_json と同じく plain JSON に直して比べる。
        InputRun::Ran(Ok(out), _, _) => encode_plain_with(&typed.output_type, &out, false)
            .unwrap_or_else(|e| panic!("出力の plain JSON への写しが失敗 ({e}): {src}")),
        InputRun::NotWellFormed => panic!("検証済みの run が整形でないと判定: {src}"),
        InputRun::InputRejected => panic!("検証済みの run が入力を拒否: {src}"),
        InputRun::Ran(Err(_), _, _) => panic!("検証済みの run が打ち切られた: {src}"),
    }
}

/// (プログラム, 入力の plain JSON, 期待する出力)。二つ目は、基が呼出し（変数でない）で書いていない字段が二つの
/// 形（基を let で束縛する）と、一つの形（基を置く）を含む。
const V5: &[(&str, &str, &str)] = &[
    (
        "type P = { a: Int, b: Int }\nfn f(p: P) -> P = P { a: p.b, ..p }\nfn g(x: Int) -> Int = f(P { a: x, b: 7 }).a\nentry g\n",
        "3",
        "7",
    ),
    (
        "type T = { a: Int, b: Int, c: Int }\nfn mk(x: Int) -> T = T { a: x, b: 2, c: 3 }\nfn wl(x: Int) -> T = T { a: x, ..mk(x) }\nfn wr(x: Int) -> T = T { a: 1, b: x, ..mk(x) }\nfn g(x: Int) -> Int = add(wl(x).b, wr(x).c)\nentry g\n",
        "10",
        "5",
    ),
];

#[test]
fn v5_record_expressions_run_on_the_verified_path() {
    for &(src, input, want) in V5 {
        let trusted = Program::compile(src)
            .unwrap_or_else(|_| panic!("信頼側が受理しない: {src}"))
            .run_json(input)
            .unwrap_or_else(|_| panic!("信頼側の実行が失敗: {src}"));
        assert_eq!(trusted, want, "信頼側の出力が違う: {src}");
        assert_eq!(verified_run(src, input), want, "検証済みの出力が違う: {src}");
    }
}

/// V6（段階 2 の S3b）：記録の参照 x.v で、x の型の印と字段 v の持ち主の印が違うと、印つきの写しの eq の両辺の型が
/// 違い、検証済みの型検査（check_prog）が拒否する。印なしの写しは構造だけを見るので、同じ形なら受理する（対照）。
/// パイプラインは記録を信頼側の展開で消してから解決するため、ここは印つきの解決（resolve_tagged_e）と
/// 検証済みの型検査を直接使う。
const V6: &[(&str, bool)] = &[
    ("type A = { a: Int }\ntype B = { v: Int }\nfn f(x: A) -> Int = x.v\nentry f\n", false),
    ("type A = { a: Int }\ntype B = { v: Int }\nfn f(x: B) -> Int = x.v\nentry f\n", true),
    ("type A = { a: Int, b: Int }\ntype B = { v: Int, w: Int }\nfn f(x: A) -> Int = x.v\nentry f\n", false),
    ("type A = { a: Int, b: Int }\ntype B = { v: Int, w: Int }\nfn f(x: B) -> Int = add(x.v, x.w)\nentry f\n", true),
    // 更新（..base）：基底は同じ記録の値なので受理され、別の名前（同じ形）の記録の値は基底の印の検査で拒否される。
    ("type P = { a: Int, b: Int }\nfn f(p: P) -> P = P { a: p.b, ..p }\nentry f\n", true),
    ("type P = { a: Int, b: Int }\ntype Q = { c: Int, d: Int }\nfn f(q: Q) -> P = P { a: 1, ..q }\nentry f\n", false),
];

#[test]
fn v6_tagged_records_are_checked_by_the_verified_core() {
    for &(src, ok) in V6 {
        let sp = verified_parse(src).unwrap_or_else(|| panic!("検証済みの解析が通らない: {src}"));
        // 印なし（対照）：構造だけを見るので、受理される。
        let (funcs, entry) = resolve_e(&sp).unwrap_or_else(|| panic!("印なしの解決が通らない: {src}"));
        let n = funcs.len();
        let untagged = EProg { funcs, rank: vec![0; n], rec: vec![false; n], entry };
        assert!(check_prog(&untagged), "印なしの型検査が通らない（対照）: {src}");
        // 印つき：持ち主の印と値の印が違えば拒否される。
        let (funcs, entry) = resolve_tagged_e(&sp).unwrap_or_else(|| panic!("印つきの解決が通らない: {src}"));
        let n = funcs.len();
        let tagged = EProg { funcs, rank: vec![0; n], rec: vec![false; n], entry };
        assert_eq!(check_prog(&tagged), ok, "印つきの型検査の判定が違う: {src}");
    }
}

// ---------------------------------------------------------------- S3c：入れ子の名前つきの字段（印つきの写し）

/// 信頼側が受理する入れ子の形。印つきの写しも検証済みの型検査が受理する（S3b では拒否していた）。印なしの写しも受理する（対照）。
const S3C_ACCEPTED: &[&str] = &[
    // 入れ子の構築：字段 i は名前つきの記録 In の値（In の印を入れ子に付ける）
    "type In = { x: Int }\ntype Out = { i: In, n: Int }\nfn f(x: Int) -> Out = Out { i: In { x: x }, n: 2 }\nentry f\n",
    // 入れ子の参照：o.i の型は In の印つき、その x は持ち主 In の印の検査を通る
    "type In = { x: Int }\ntype Out = { i: In, n: Int }\nfn f(o: Out) -> Int = o.i.x\nentry f\n",
];

/// 信頼側が拒否する形。印つきの写しも拒否する。一つ目は、S3b の印つきの写しが受理していた（字段 i の In を Int で満たせた）。
/// 三つ目は V6 の六つ目の行（基 ..q が別の記録 Q の値）で、信頼側も拒否する。
const S3C_REJECTED: &[&str] = &[
    // 字段 i は In なのに Int の値（信頼側は E-TYPE-ARG）
    "type In = { x: Int }\ntype Out = { i: In, n: Int }\nfn f(x: Int) -> Out = Out { i: x, n: 2 }\nentry f\n",
    // 字段 i の持ち主は Out で、q の型は Q（信頼側は E-TYPE-FIELD-ACCESS）
    "type In = { x: Int }\ntype Out = { i: In, n: Int }\ntype Q = { j: Int }\nfn f(q: Q) -> Int = q.i.x\nentry f\n",
    // V6 の六つ目（信頼側は E-TYPE-FIELD-ACCESS）
    "type P = { a: Int, b: Int }\ntype Q = { c: Int, d: Int }\nfn f(q: Q) -> P = P { a: 1, ..q }\nentry f\n",
];

/// 入れ子の値を作り、参照する実行（入力と出力は Int）。信頼側の実行、印なしの検証済みの実行、印つきの検証済みの実行が一致する。
/// 二つ目は、基 ..o の入れ子の字段を新しい値で置き、基の字段 n を使う。
const S3C_RUN: &[(&str, &str, &str)] = &[
    (
        "type In = { x: Int }\ntype Out = { i: In, n: Int }\nfn mk(x: Int) -> Out = Out { i: In { x: x }, n: 2 }\nfn f(x: Int) -> Int = mk(x).i.x\nentry f\n",
        "7",
        "7",
    ),
    (
        "type In = { x: Int }\ntype Out = { i: In, n: Int }\nfn mk(x: Int) -> Out = Out { i: In { x: x }, n: 2 }\nfn up(o: Out, x: Int) -> Out = Out { i: In { x: x }, ..o }\nfn f(x: Int) -> Int = add(up(mk(x), 5).i.x, up(mk(x), 5).n)\nentry f\n",
        "3",
        "7",
    ),
];

/// 印つきの入口（S3c）：信頼側の受理から rank と rec を取り、印つきの解決（resolve_tagged_e）の結果を検証済みの型検査と
/// run_input_json に渡す。入力と出力は Int に限る（印つきの値の入出力は、この試験では比べない）。
fn tagged_run(src: &str, input: &str) -> String {
    let typed = match compile(src.as_bytes(), &StaticProfile::default()) {
        SourceCompile::Result(CompileResult::Accepted { program, .. }) => program,
        _ => panic!("信頼側が受理しない: {src}"),
    };
    let rank: Vec<usize> = typed
        .program
        .functions()
        .map(|f| typed.rank.get(&f.name).copied().unwrap_or(usize::MAX))
        .collect();
    let rec: Vec<bool> = typed.program.functions().map(|f| f.rec).collect();
    let sp = verified_parse(src).unwrap_or_else(|| panic!("検証済みの解析が通らない: {src}"));
    let (funcs, entry) = resolve_tagged_e(&sp).unwrap_or_else(|| panic!("印つきの解決が通らない: {src}"));
    let prog = EProg { funcs, rank, rec, entry };
    assert!(check_prog(&prog), "印つきの型検査が通らない: {src}");
    let tv = match decode_plain_input(&typed.input_type, input.as_bytes(), &InputProfile::default()) {
        DecodeResult::Decoded(tv) => tv,
        _ => panic!("入力の復号が失敗: {src}"),
    };
    let lim = Limits {
        steps: 1_000_000,
        integer_bits: 4_096,
        allocated_nodes: 1_000_000,
        max_depth: 100_000,
        max_slots: 100_000,
    };
    match run_input_json(&prog, &tv.text, tv.json_depth, lim) {
        InputRun::Ran(Ok(out), _, _) => encode_plain_with(&typed.output_type, &out, false)
            .unwrap_or_else(|e| panic!("出力の plain JSON への写しが失敗 ({e}): {src}")),
        InputRun::NotWellFormed => panic!("印つきの run が整形でないと判定: {src}"),
        InputRun::InputRejected => panic!("印つきの run が入力を拒否: {src}"),
        InputRun::Ran(Err(_), _, _) => panic!("印つきの run が打ち切られた: {src}"),
    }
}

#[test]
fn s3c_nested_named_fields_agree_with_trusted() {
    for src in S3C_ACCEPTED {
        assert!(trusted(src).is_none(), "信頼側が拒否した: {src}");
        let sp = verified_parse(src).unwrap_or_else(|| panic!("検証済みの解析が通らない: {src}"));
        let (funcs, entry) = resolve_e(&sp).unwrap_or_else(|| panic!("印なしの解決が通らない: {src}"));
        let n = funcs.len();
        assert!(check_prog(&EProg { funcs, rank: vec![0; n], rec: vec![false; n], entry }), "印なしの型検査が通らない（対照）: {src}");
        let (funcs, entry) = resolve_tagged_e(&sp).unwrap_or_else(|| panic!("印つきの解決が通らない: {src}"));
        let n = funcs.len();
        assert!(check_prog(&EProg { funcs, rank: vec![0; n], rec: vec![false; n], entry }), "印つきの型検査が受理しない: {src}");
    }
    for src in S3C_REJECTED {
        assert!(trusted(src).is_some(), "信頼側が受理した: {src}");
        let sp = verified_parse(src).unwrap_or_else(|| panic!("検証済みの解析が通らない: {src}"));
        let (funcs, entry) = resolve_tagged_e(&sp).unwrap_or_else(|| panic!("印つきの解決が通らない: {src}"));
        let n = funcs.len();
        assert!(
            !check_prog(&EProg { funcs, rank: vec![0; n], rec: vec![false; n], entry }),
            "印つきの型検査が受理した（信頼側は拒否する）: {src}"
        );
    }
    for &(src, input, want) in S3C_RUN {
        let trusted_out = Program::compile(src)
            .unwrap_or_else(|_| panic!("信頼側が受理しない: {src}"))
            .run_json(input)
            .unwrap_or_else(|_| panic!("信頼側の実行が失敗: {src}"));
        assert_eq!(trusted_out, want, "信頼側の出力が違う: {src}");
        assert_eq!(verified_run(src, input), want, "印なしの検証済みの出力が違う: {src}");
        assert_eq!(tagged_run(src, input), want, "印つきの検証済みの出力が違う: {src}");
    }
}

// ---------------------------------------------------------------- V7：展開段階の名前の診断と、検証済みの突き合わせ（S5a）

/// 展開段階の名前の診断の corpus：record_names.rs・records.rs・sums.rs の拒否する例と、diagnostic_registry.rs の例。
/// (プログラム, 出すべき符号)。
fn v7_corpus() -> Vec<(String, &'static str)> {
    let p = |s: &str, c: &'static str| (s.to_string(), c);
    let shape = "type Shape = Circle(Int) | Rect(Int, Int) | Empty\n";
    let h = "type P = { a: Int, b: Bool }\n";
    vec![
        // record_names.rs：レコードの名前の診断
        p("type P = { a: Int }\nfn f(p: Q) -> Int = 1\nentry f\n", "E-RECORD-UNKNOWN-TYPE"),
        p("type P = { a: Int }\nfn f(x: Int) -> Int = Q { a: x }.a\nentry f\n", "E-RECORD-UNKNOWN-TYPE"),
        p("type P = { a: Int }\ntype P = { b: Int }\nfn f(p: P) -> Int = 1\nentry f\n", "E-RECORD-DUPLICATE-TYPE"),
        p("type P = { a: Int, b: Int }\nfn f(x: Int) -> Int = P { a: x, b: x, z: x }.a\nentry f\n", "E-RECORD-UNKNOWN-FIELD"),
        p("type P = { a: Int, b: Int }\nfn f(p: P) -> Int = p.z\nentry f\n", "E-RECORD-UNKNOWN-FIELD"),
        p("fn f(x: Int) -> Int = x.a\nentry f\n", "E-RECORD-UNKNOWN-FIELD"),
        p("type P = { a: Int, a: Int }\nfn f(p: P) -> Int = p.a\nentry f\n", "E-RECORD-DUPLICATE-FIELD"),
        p("type P = { a: Int, b: Int }\nfn f(x: Int) -> Int = P { a: x, a: x, b: x }.a\nentry f\n", "E-RECORD-DUPLICATE-FIELD"),
        p("type P = { a: Int, b: Int }\nfn f(x: Int) -> Int = P { a: x }.a\nentry f\n", "E-RECORD-MISSING-FIELD"),
        p("type P = { a: Int, b: Int, c: Int }\nfn f(x: Int) -> Int = P { a: x }.a\nentry f\n", "E-RECORD-MISSING-FIELD"),
        p("type P = { a: Int, b: Int }\nfn f(q: P, x: Int) -> Int = P { a: x, b: x, ..q }.a\nentry f\n", "E-RECORD-BASE-REDUNDANT"),
        p("type P = { a: Int }\ntype Q = { a: Int }\nfn f(q: Q) -> Int = q.a\nentry f\n", "E-RECORD-FIELD-CONFLICT"),
        p("fn f(d: Dict) -> Int = 0\nentry f\n", "E-RECORD-UNKNOWN-TYPE"),
        p("fn f(x: Int) -> Dict = x\nentry f\n", "E-RECORD-UNKNOWN-TYPE"),
        p("type R = { d: Dict, n: Int }\nfn f(r: R) -> Int = r.n\nentry f\n", "E-RECORD-UNKNOWN-TYPE"),
        p("type A = { x: Int, y: Int }\ntype B = { x: Int, y: Int }\nfn f(a: A) -> B = a\nentry f\n", "E-RECORD-FIELD-CONFLICT"),
        // records.rs：レコードの名前の診断
        p(&format!("{h}fn f(p: P) -> Int = p.c entry f"), "E-RECORD-UNKNOWN-FIELD"),
        p(&format!("{h}fn f(p: R) -> Int = 1 entry f"), "E-RECORD-UNKNOWN-TYPE"),
        p(&format!("{h}fn f(x: Int) -> P = P {{ a: x }} entry f"), "E-RECORD-MISSING-FIELD"),
        p(&format!("{h}fn f(x: P) -> P = P {{ a: 1, b: true, ..x }} entry f"), "E-RECORD-BASE-REDUNDANT"),
        p(&format!("{h}fn f(x: Int) -> P = P {{ a: x, b: true, ..undefined }} entry f"), "E-RECORD-BASE-REDUNDANT"),
        p(&format!("{h}fn f(x: Int) -> P = P {{ a: x, a: x, b: true }} entry f"), "E-RECORD-DUPLICATE-FIELD"),
        p(&format!("{h}type Q = {{ a: Int }}\nfn f(x: Int) -> Int = x entry f"), "E-RECORD-FIELD-CONFLICT"),
        p(&format!("{h}type P = {{ c: Int }}\nfn f(x: Int) -> Int = x entry f"), "E-RECORD-DUPLICATE-TYPE"),
        p("type A = { x: B }\ntype B = { y: Int }\nfn f(x: Int) -> Int = x entry f\n", "E-RECORD-UNKNOWN-TYPE"),
        // sums.rs：直和型と match の診断（名前の段階のもの）
        p(&format!("{shape}fn f(s: Shape) -> Int = match s {{ Circle(r) => r, Rect(w, h) => w }} entry f"), "E-MATCH-MISSING"),
        p(&format!("{shape}fn f(s: Shape) -> Int = match s {{ Circle(r) => r, Circle(q) => q, _ => 0 }} entry f"), "E-MATCH-DUPLICATE"),
        p(&format!("{shape}fn f(s: Shape) -> Int = match s {{ _ => 0, Empty => 1 }} entry f"), "E-MATCH-UNREACHABLE"),
        p(&format!("{shape}fn f(s: Shape) -> Int = match s {{ Circle(r) => r, Rect(w, h) => w, Empty => 0, _ => 1 }} entry f"), "E-MATCH-UNREACHABLE"),
        p(&format!("{shape}fn f(s: Shape) -> Int = match s {{ Circle(r) => r, ok(x) => x, _ => 0 }} entry f"), "E-MATCH-MIXED"),
        p(&format!("{shape}fn f(s: Shape) -> Int = match s {{ Circel(r) => r, _ => 0 }} entry f"), "E-SUM-UNKNOWN-CTOR"),
        p(&format!("{shape}fn f(s: Int) -> Shape = Circel(s) entry f"), "E-SUM-UNKNOWN-CTOR"),
        p(&format!("{shape}fn f(s: Int) -> Shape = Emty entry f"), "E-SUM-UNKNOWN-CTOR"),
        p(&format!("{shape}fn f(s: Shape) -> Int = match s {{ Rect(w) => w, _ => 0 }} entry f"), "E-SUM-CTOR-ARITY"),
        p(&format!("{shape}fn f(s: Shape) -> Int = match s {{ Empty() => 0, _ => 1 }} entry f"), "E-SUM-CTOR-ARITY"),
        p(&format!("{shape}fn f(s: Int) -> Shape = Rect(s) entry f"), "E-SUM-CTOR-ARITY"),
        p(&format!("{shape}fn f(s: Int) -> Shape = Circle entry f"), "E-SUM-CTOR-ARITY"),
        p(&format!("{shape}fn f(s: Int) -> Shape = Empty() entry f"), "E-SUM-CTOR-ARITY"),
        p(&format!("{shape}fn f(Circle: Int) -> Int = 1 entry f"), "E-SUM-NAME-CONFLICT"),
        p(&format!("{shape}fn f(s: Int) -> Int = let Empty = 1 in Empty entry f"), "E-SUM-NAME-CONFLICT"),
        p(&format!("{shape}fn Rect(s: Int) -> Int = 1 fn f(s: Int) -> Int = 1 entry f"), "E-SUM-NAME-CONFLICT"),
        p("type S = S | T fn f(s: Int) -> Int = 1 entry f", "E-SUM-NAME-CONFLICT"),
        p(&format!("{shape}type T = Empty | Full fn f(s: Int) -> Int = 1 entry f"), "E-SUM-DUPLICATE-CTOR"),
        p("type T = A | B | A fn f(s: Int) -> Int = 1 entry f", "E-SUM-DUPLICATE-CTOR"),
        p("type S = A(P) | B type P = { x: Int } fn f(s: Int) -> Int = 1 entry f", "E-RECORD-UNKNOWN-TYPE"),
        p("type S = A(Foo) | B fn f(s: Int) -> Int = 1 entry f", "E-RECORD-UNKNOWN-TYPE"),
        p("type S = A | B type S = C fn f(s: Int) -> Int = 1 entry f", "E-RECORD-DUPLICATE-TYPE"),
        // diagnostic_registry.rs の例。構築子・match・総称の例は突き合わせに入らないので、食い違いが出ないことだけを見る
        p("type S = A | A\nfn f(x: Int) -> Int = x entry f\n", "E-SUM-DUPLICATE-CTOR"),
        p("type S = Add | B\nfn Add(x: Int) -> Int = x\nfn f(x: Int) -> Int = x entry f\n", "E-SUM-NAME-CONFLICT"),
        p("type S = A | B(Int)\nfn f(x: Int) -> S = B(1, 2) entry f\n", "E-SUM-CTOR-ARITY"),
        p("type S = A | B\nfn f(x: S) -> Int = match x { A => 0 } entry f\n", "E-MATCH-MISSING"),
        p("type T = Leaf | Node(String, T)\nfn f(x: Int) -> Int = x entry f\n", "E-REC-FIELD-TYPE"),
        p("type T<A> = Leaf | Node(Int, T<A>)\nfn f(x: Int) -> Int = x entry f\n", "E-REC-TYPE-PARAM"),
        p("type L = Nil | Cons(Int, L)\ntype L = Done | More(Int, L)\nfn f(a: Int) -> Int = a entry f\n", "E-RECORD-DUPLICATE-TYPE"),
        p("type S = A(P) | B\ntype P = { x: Int }\nfn f(s: Int) -> Int = 1 entry f\n", "E-RECORD-UNKNOWN-TYPE"),
        p("type P = { a: Int }\nfn f(x: P, y: Q) -> Int = 0 entry f\n", "E-RECORD-UNKNOWN-TYPE"),
        p("fn id<T>(x: T) -> T = x\nfn f(x: Int) -> Int = id<Int, Int>(x) entry f\n", "E-TYPE-GENERIC-ARITY"),
        p("fn g(x: U) -> Int = 0\nfn f(x: Int) -> Int = g(x) entry f\n", "E-TYPE-GENERIC-UNKNOWN-PARAM"),
        p("fn g<T, T>(x: T) -> T = x\nfn f(x: Int) -> Int = g(x) entry f\n", "E-TYPE-GENERIC-DUPLICATE-PARAM"),
        p("type T = { a: Int }\nfn g<T>(x: T) -> T = x\nfn f(x: Int) -> Int = x entry f\n", "E-TYPE-GENERIC-PARAM-CONFLICT"),
        p("type Box<T> = { value: Int }\nfn f(x: Int) -> Int = x entry f\n", "E-TYPE-GENERIC-UNUSED-PARAM"),
        p("fn mk<T>() -> List<T> = list<T>()\nfn f(x: Int) -> List<Int> = mk() entry f\n", "E-TYPE-GENERIC-INFER"),
        // 字段の型の中の未知の型（組込みの型の中も見る）と、再帰する直和型の項の形（S5a の補足）
        p("type R = { x: Option<Q> }\nfn f(r: R) -> Int = 0 entry f\n", "E-RECORD-UNKNOWN-TYPE"),
        p("type R = { x: Pair<Int, Q> }\nfn f(r: R) -> Int = 0 entry f\n", "E-RECORD-UNKNOWN-TYPE"),
        p("type R = { x: List<Q> }\nfn f(r: R) -> Int = 0 entry f\n", "E-RECORD-UNKNOWN-TYPE"),
        p("type R = { x: Dict<Q, Int> }\nfn f(r: R) -> Int = 0 entry f\n", "E-RECORD-UNKNOWN-TYPE"),
        p("type R = { x: Result<Q, Int> }\nfn f(r: R) -> Int = 0 entry f\n", "E-RECORD-UNKNOWN-TYPE"),
        p("type S = A(Option<Q>) | B\nfn f(s: Int) -> Int = 1 entry f\n", "E-RECORD-UNKNOWN-TYPE"),
        p("type R = { x: List<T> }\ntype T = { y: Int }\nfn f(r: R) -> Int = 0 entry f\n", "E-RECORD-UNKNOWN-TYPE"),
        p("type L = Nil | Cons(Option<Int>, L)\nfn f(a: Int) -> Int = a entry f\n", "E-REC-FIELD-TYPE"),
        p("type L = Nil | Cons(Pair<Int, Int>, L)\nfn f(a: Int) -> Int = a entry f\n", "E-REC-FIELD-TYPE"),
        p("type L = Nil | Cons(Dict<Int, Int>, L)\nfn f(a: Int) -> Int = a entry f\n", "E-REC-FIELD-TYPE"),
        p("type L = Nil | Cons(Char, L)\nfn f(a: Int) -> Int = a entry f\n", "E-REC-FIELD-TYPE"),
        p("type L = Nil | Cons(Q, L)\nfn f(a: Int) -> Int = a entry f\n", "E-REC-FIELD-TYPE"),
        p("type P = { a: Int }\ntype L = Nil | Cons(P, L)\nfn f(a: Int) -> Int = a entry f\n", "E-REC-FIELD-TYPE"),
        p("type P = { a: Int, a: Option<Int> }\nfn f(p: P) -> Int = 0 entry f\n", "E-RECORD-DUPLICATE-FIELD"),
        p("type P = { a: Int }\ntype Q = { b: Int }\nfn f(x: Int) -> Int = P { a: x, b: x }.a entry f\n", "E-RECORD-UNKNOWN-FIELD"),
        p("type P = { a: Int, b: Int }\nfn f(x: Int) -> P = P { c: x } entry f\n", "E-RECORD-MISSING-FIELD"),
        p("type P = { a: Int, b: Int }\nfn g(p: P) -> P = P { a: 1, zz: 2, ..p } entry g\n", "E-RECORD-UNKNOWN-FIELD"),
        p("type P = { a: Int }\ntype P = { b: Int }\nfn f(p: P) -> P = p entry f\n", "E-RECORD-DUPLICATE-TYPE"),
        p("type P = { a: Int, b: Int }\ntype Q = { a: Int }\ntype S = { b: Int }\nfn f(x: Int) -> Int = x entry f\n", "E-RECORD-FIELD-CONFLICT"),
    ]
}

#[test]
fn v7_expansion_name_diagnostics_have_no_verified_mismatch() {
    let corpus = v7_corpus();
    for (src, want) in &corpus {
        // 食い違いが出ないこと（rejected の検査）と、出すべき符号が出ること
        let rows = rejected(src);
        assert!(
            rows.iter().any(|r| r.1 == *want),
            "符号 {want} が出ない: {src}\n{rows:?}"
        );
    }
    // 出た符号が全部、突き合わせる（有効な）コードの例では、検証済みの parser が通り、resolver が拒否する。
    let mut gaps: Vec<String> = Vec::new();
    for (src, _) in &corpus {
        let rows = rejected(src);
        let checked = rows
            .iter()
            .all(|r| CHECKED_EXPANSION_CODES.contains(&r.1.as_str()));
        if checked {
            if verified_parse(src).is_none() {
                gaps.push(format!(
                    "parse が通らない: {src:?} {:?}",
                    rows.iter().map(|r| r.1.as_str()).collect::<Vec<_>>()
                ));
            } else if verified_accepts(src) {
                gaps.push(format!("resolver が受理した: {src:?}"));
            }
        }
    }
    assert!(
        gaps.is_empty(),
        "突き合わせが働かない、または食い違う例:\n{}",
        gaps.join("\n")
    );
}
