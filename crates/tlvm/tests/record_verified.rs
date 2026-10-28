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
//!
//! S5b：V8（範囲内の受理は源の文字列の二つの写しで検査し、添付の IR は源の印なしの IR と一致する。判定は HEAD と同じ）、
//! V10（範囲の外の混ぜたプログラムは HEAD の符号と出力のまま）、V11（rec fn が記録を引数に取る例と相互再帰）、
//! V13（枝の並びの後ろの `,` は範囲の外で、注釈の中の `,` は範囲の内）、V14（記録と直和型を混ぜたプログラムは範囲の内）。
//! V9 は tests/nominal.rs の hand_made_tag_shape_is_rejected_when_run にある。
//!
//! S5c：V7 の広い版（記録だけのプログラムの変異を本番の検査で判定し、検証済みの食い違いが出ないことを確かめる。
//! 全体の掃引は scratchpad の sweep.py が CLI で一度回した。ここは添字が SWEEP_STEP の倍数の変異）、
//! V12（宣言の数と書換えの大きさ。HEAD と同じ判定を返す）。

use std::collections::{BTreeMap, BTreeSet};
use std::process::Command;

use tlvm::api::*;
use tlvm::embed::Program;
use tlvm::nominal::Tags;
use tlvm::plain::encode_plain_with;
use tlvm::profiles::*;
use tlvm::syntax::Decl;
use tlvm::values::DecodeResult;
use tlvm_verified::check::check_prog;
use tlvm_verified::eval::Limits;
use tlvm_verified::ir::{ty_eq, EExpr, EProg};
use tlvm_verified::pipeline::{compile_source, run_input_json, Compiled, InputRun};
use tlvm_verified::resolve::{decl_numbers_e, resolve_e, resolve_tagged_e};
use tlvm_verified::surface::{parse_e, SDecl};

mod common;
use common::{rejected, row};

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
    let (d, td) = (
        p.expr_depth,
        p.type_depth.saturating_mul(2).saturating_add(2),
    );
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
    (
        "type P = { a: Q }\nfn f(a: Int) -> Int = a\nentry f\n",
        Some("E-RECORD-UNKNOWN-TYPE"),
    ),
    (
        "type P = { q: Q }\ntype Q = { a: Int }\nfn f(a: Int) -> Int = a\nentry f\n",
        Some("E-RECORD-UNKNOWN-TYPE"),
    ),
    (
        "type R = { r: R }\nfn f(a: Int) -> Int = a\nentry f\n",
        Some("E-RECORD-UNKNOWN-TYPE"),
    ),
    // E-RECORD-UNKNOWN-TYPE：直和型の中身が後で宣言した記録、後で宣言した直和型
    (
        "type S = V(B) | W\ntype B = { x: Int }\nfn f(a: Int) -> Int = a\nentry f\n",
        Some("E-RECORD-UNKNOWN-TYPE"),
    ),
    (
        "type T = V(S) | U\ntype S = X | Y\nfn f(a: Int) -> Int = a\nentry f\n",
        Some("E-RECORD-UNKNOWN-TYPE"),
    ),
    // E-RECORD-DUPLICATE-TYPE：同じ名前の記録が二つ
    (
        "type P = { a: Int }\ntype P = { b: Int }\nfn f(a: Int) -> Int = a\nentry f\n",
        Some("E-RECORD-DUPLICATE-TYPE"),
    ),
    // E-RECORD-DUPLICATE-FIELD：同じ記録の中で字段名が重なる
    (
        "type R = { s: Int, s: Int }\nfn f(a: Int) -> Int = a\nentry f\n",
        Some("E-RECORD-DUPLICATE-FIELD"),
    ),
    // E-RECORD-FIELD-CONFLICT：別の記録と字段名が重なる
    (
        "type A = { x: Int }\ntype B = { x: Int }\nfn f(a: Int) -> Int = a\nentry f\n",
        Some("E-RECORD-FIELD-CONFLICT"),
    ),
    // 受理：記録の字段が前の記録を使う。関数の注釈が後の記録を使う（現行の読み方）。型名と関数名の一致
    (
        "type A = { x: Int }\ntype B = { a: A, y: Int }\nfn f(b: B) -> Int = 1\nentry f\n",
        None,
    ),
    (
        "fn f(p: P) -> Int = 1\ntype P = { a: Int }\nentry f\n",
        None,
    ),
    (
        "type P = { a: Int }\nfn P(a: Int) -> Int = a\nentry P\n",
        None,
    ),
    // 受理：直和型の中身に前の記録、記録の字段に前の直和型（使わない）、直和型だけの宣言
    (
        "type B = { x: Int }\ntype S = V(B) | W\nfn f(a: Int) -> Int = a\nentry f\n",
        None,
    ),
    (
        "type S = X | Y\ntype R = { s: S, n: Int }\nfn f(a: Int) -> Int = a\nentry f\n",
        None,
    ),
    ("type S = V | W\nfn f(a: Int) -> Int = a\nentry f\n", None),
    // 受理：字段名の重なりがない二つの記録、字段が一つの記録を関数の注釈に使う
    (
        "type A = { x: Int }\ntype B = { y: Int }\nfn f(a: A) -> Int = 1\nentry f\n",
        None,
    ),
    (
        "type P = { a: Int, b: Bool }\nfn f(p: P) -> Int = 1\nentry f\n",
        None,
    ),
];

/// V2：記録と直和型をまたぐ型名の重複。宣言の順を変えても、どちらも拒否する。
const V2: &[(&str, Option<&str>)] = &[
    (
        "type A = { x: Int }\ntype A = V | W\nfn f(a: Int) -> Int = a\nentry f\n",
        Some("E-RECORD-DUPLICATE-TYPE"),
    ),
    (
        "type A = V | W\ntype A = { x: Int }\nfn f(a: Int) -> Int = a\nentry f\n",
        Some("E-RECORD-DUPLICATE-TYPE"),
    ),
    (
        "type A = V | W\ntype A = X | Y\nfn f(a: Int) -> Int = a\nentry f\n",
        Some("E-RECORD-DUPLICATE-TYPE"),
    ),
    (
        "type A = { x: Int }\ntype B = V | W\nfn f(a: Int) -> Int = a\nentry f\n",
        None,
    ),
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
            .map(|(i, x)| {
                if x.0 == 'R' || x.0 == 'S' {
                    Some(i)
                } else {
                    None
                }
            })
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
    assert!(
        position_differs,
        "corpus に、宣言の位置で数えた番号と違う例がない"
    );
    assert!(
        records_only_differs,
        "corpus に、記録だけで数えた番号と違う例がない"
    );
}

// ---------------------------------------------------------------- S2c：再帰する直和型の項と、前方の参照

/// 再帰する直和型の項（v1.14）：項の型は Int、Bool、その型自身に限る。信頼側（recursive.rs:563）が拒否する形は、
/// 検証済みも拒否する。受理する形は両方が受理する。
const S2C_RECURSIVE: &[(&str, Option<&str>)] = &[
    // 記録の項（前に宣言した記録、後に宣言した記録）
    (
        "type P = { a: Int }\ntype L = Nil | Cons(P, L)\nfn f(a: Int) -> Int = a\nentry f\n",
        Some("E-REC-FIELD-TYPE"),
    ),
    (
        "type L = Nil | Cons(P, L)\ntype P = { a: Int }\nfn f(a: Int) -> Int = a\nentry f\n",
        Some("E-REC-FIELD-TYPE"),
    ),
    (
        "type R = { s: L }\ntype L = Nil | Cons(R, L)\nfn f(a: Int) -> Int = a\nentry f\n",
        Some("E-REC-FIELD-TYPE"),
    ),
    // 直和型の項（前に宣言した直和型）、Unit、List の項
    (
        "type S = V | W\ntype L = Nil | Cons(S, L)\nfn f(a: Int) -> Int = a\nentry f\n",
        Some("E-REC-FIELD-TYPE"),
    ),
    (
        "type L = Nil | Cons(Unit, L)\nfn f(a: Int) -> Int = a\nentry f\n",
        Some("E-REC-FIELD-TYPE"),
    ),
    (
        "type L = Nil | Cons(List<Int>, L)\nfn f(a: Int) -> Int = a\nentry f\n",
        Some("E-REC-FIELD-TYPE"),
    ),
    // 受理：Int、Bool、その型自身の項だけ（一つだけの自己参照も）
    (
        "type T = Leaf | Node(T, Int, T)\nfn f(a: Int) -> Int = a\nentry f\n",
        None,
    ),
    (
        "type T = Leaf | Node(T, Bool, T)\nfn f(a: Int) -> Int = a\nentry f\n",
        None,
    ),
    (
        "type L = Nil | Cons(L)\nfn f(a: Int) -> Int = a\nentry f\n",
        None,
    ),
    // 受理：再帰する直和型を字段の型に使う記録、再帰しない直和型が記録を項に持つ、再帰する直和型を項に持つ直和型
    (
        "type L = Nil | Cons(Int, L)\ntype Q = { b: L }\nfn f(a: Int) -> Int = a\nentry f\n",
        None,
    ),
    (
        "type P = { a: Int }\ntype S = V(P) | W\nfn f(a: Int) -> Int = a\nentry f\n",
        None,
    ),
    (
        "type L = Nil | Cons(Int, L)\ntype M = Q(L) | N\nfn f(a: Int) -> Int = a\nentry f\n",
        None,
    ),
];

/// 既知の食い違い：信頼側が受理するが、設計の規則（§3.1 行 125：字段と直和型の中身は前に宣言した型に限る。
/// v1.14：再帰する直和型の項は Int、Bool、その型自身に限る）が禁じる形。信頼側のコードは変えない。
/// 検証済みは規則に従って拒否する。信頼側が直ると、このテストが落ちて、食い違いが閉じたと分かる。
const KNOWN_GAPS: &[&str] = &[
    // 再帰する直和型の項に、別の再帰する直和型（v1.14 では自分自身だけ）。kind_of は再帰する型の名前を全部通す（recursive.rs:104-109）
    "type K = Z | S(Int, K)\ntype L = Nil | Cons(K, L)\nfn f(a: Int) -> Int = a\nentry f\n",
    // 相互再帰：後に宣言した型を項に持つ。両方とも再帰する直和型になり、kind_of が通す（recursive.rs:104-109）
    "type A = X(B) | Y\ntype B = Z(A)\nfn f(a: Int) -> Int = a\nentry f\n",
    // 再帰する直和型の項に、後に宣言した再帰する直和型。展開が前方の参照を書き換えてから検査する（recursive.rs:157、api.rs:331）
    "type M = Q(L, M) | N\ntype L = Nil | Cons(Int, L)\nfn f(a: Int) -> Int = a\nentry f\n",
    // 再帰しない直和型の項に、後に宣言した再帰する直和型。同じ理由で前方の参照が見えない（recursive.rs:157、api.rs:331）
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
        assert!(
            trusted(src).is_none(),
            "信頼側が拒否した（既知の食い違いが閉じた。表を直す）: {src}"
        );
        assert!(
            !verified_accepts(src),
            "検証済みが受理した（規則に反する）: {src}"
        );
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
    let (d, td) = (
        p.expr_depth,
        p.type_depth.saturating_mul(2).saturating_add(2),
    );
    // 検証済みの parser は `rec` を知らないので、経路と同じく印を空白に置き換えた源を読ませる（api::without_rec_markers）。
    let sp = match parse_source(src.as_bytes(), &p) {
        Parsed::Program(sp) => sp,
        Parsed::Failed(_) => panic!("構文が通らない: {src}"),
    };
    let chars: Vec<char> = without_rec_markers(src, &sp).chars().collect();
    let prog = match compile_source(&chars, d, td, rank, rec, false) {
        Compiled::Accepted(prog) => prog,
        _ => panic!("検証済みが受理しない: {src}"),
    };
    // 入力は信頼側の復号（embed.rs の run_plain と同じ）で値の JSON に直してから、検証済みの復号器へ渡す。
    let tv = match decode_plain_input(
        &typed.input_type,
        input.as_bytes(),
        &InputProfile::default(),
    ) {
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
        assert_eq!(
            verified_run(src, input),
            want,
            "検証済みの出力が違う: {src}"
        );
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
        let (funcs, entry) =
            resolve_e(&sp).unwrap_or_else(|| panic!("印なしの解決が通らない: {src}"));
        let n = funcs.len();
        let untagged = EProg {
            funcs,
            rank: vec![0; n],
            rec: vec![false; n],
            entry,
        };
        assert!(
            check_prog(&untagged),
            "印なしの型検査が通らない（対照）: {src}"
        );
        // 印つき：持ち主の印と値の印が違えば拒否される。
        let (funcs, entry) =
            resolve_tagged_e(&sp).unwrap_or_else(|| panic!("印つきの解決が通らない: {src}"));
        let n = funcs.len();
        let tagged = EProg {
            funcs,
            rank: vec![0; n],
            rec: vec![false; n],
            entry,
        };
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
    let (funcs, entry) =
        resolve_tagged_e(&sp).unwrap_or_else(|| panic!("印つきの解決が通らない: {src}"));
    let prog = EProg {
        funcs,
        rank,
        rec,
        entry,
    };
    assert!(check_prog(&prog), "印つきの型検査が通らない: {src}");
    let tv = match decode_plain_input(
        &typed.input_type,
        input.as_bytes(),
        &InputProfile::default(),
    ) {
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
        let (funcs, entry) =
            resolve_e(&sp).unwrap_or_else(|| panic!("印なしの解決が通らない: {src}"));
        let n = funcs.len();
        assert!(
            check_prog(&EProg {
                funcs,
                rank: vec![0; n],
                rec: vec![false; n],
                entry
            }),
            "印なしの型検査が通らない（対照）: {src}"
        );
        let (funcs, entry) =
            resolve_tagged_e(&sp).unwrap_or_else(|| panic!("印つきの解決が通らない: {src}"));
        let n = funcs.len();
        assert!(
            check_prog(&EProg {
                funcs,
                rank: vec![0; n],
                rec: vec![false; n],
                entry
            }),
            "印つきの型検査が受理しない: {src}"
        );
    }
    for src in S3C_REJECTED {
        assert!(trusted(src).is_some(), "信頼側が受理した: {src}");
        let sp = verified_parse(src).unwrap_or_else(|| panic!("検証済みの解析が通らない: {src}"));
        let (funcs, entry) =
            resolve_tagged_e(&sp).unwrap_or_else(|| panic!("印つきの解決が通らない: {src}"));
        let n = funcs.len();
        assert!(
            !check_prog(&EProg {
                funcs,
                rank: vec![0; n],
                rec: vec![false; n],
                entry
            }),
            "印つきの型検査が受理した（信頼側は拒否する）: {src}"
        );
    }
    for &(src, input, want) in S3C_RUN {
        let trusted_out = Program::compile(src)
            .unwrap_or_else(|_| panic!("信頼側が受理しない: {src}"))
            .run_json(input)
            .unwrap_or_else(|_| panic!("信頼側の実行が失敗: {src}"));
        assert_eq!(trusted_out, want, "信頼側の出力が違う: {src}");
        assert_eq!(
            verified_run(src, input),
            want,
            "印なしの検証済みの出力が違う: {src}"
        );
        assert_eq!(
            tagged_run(src, input),
            want,
            "印つきの検証済みの出力が違う: {src}"
        );
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

// ---------------------------------------------------------------- V8（S5b）：名義の判定の振り分け

/// nominal.rs と record_names.rs の全部のプログラム（HEAD の判定を記録した表。tests/data/route_corpus.tsv）。
/// 各行は 出典、判定（ACCEPT または REJECT と符号の列）、プログラム（\n \t \\ を逸らした形）。
const ROUTE_CORPUS: &str = include_str!("data/route_corpus.tsv");

/// 信頼側の判定：受理なら ACCEPT、拒否なら REJECT と符号の列（順は診断の順）。
fn verdict(src: &str) -> String {
    match compile(src.as_bytes(), &StaticProfile::default()) {
        SourceCompile::Result(CompileResult::Accepted { .. }) => "ACCEPT".to_string(),
        SourceCompile::Result(CompileResult::Rejected { errors, .. }) => {
            let codes: Vec<&str> = errors.iter().map(|d| d.code).collect();
            format!("REJECT {}", codes.join(","))
        }
        _ => "BOUNDARY".to_string(),
    }
}

/// tests/data/route_corpus.tsv の一行の逸らしを戻す。
fn unescape_tsv(s: &str) -> String {
    let mut out = String::new();
    let mut it = s.chars();
    while let Some(c) = it.next() {
        if c == '\\' {
            match it.next() {
                Some('n') => out.push('\n'),
                Some('t') => out.push('\t'),
                Some(other) => out.push(other),
                None => out.push('\\'),
            }
        } else {
            out.push(c);
        }
    }
    out
}

#[test]
fn v8_joint_verdicts_match_head() {
    let mut bad: Vec<String> = Vec::new();
    let mut n = 0;
    for line in ROUTE_CORPUS.lines().filter(|l| !l.is_empty()) {
        let mut parts = line.splitn(3, '\t');
        let (origin, want, esc) = (
            parts.next().unwrap(),
            parts.next().unwrap(),
            parts.next().unwrap(),
        );
        let src = unescape_tsv(esc);
        n += 1;
        let got = verdict(&src);
        if got != want {
            bad.push(format!("{origin}: HEAD は {want}、今は {got}: {src:?}"));
        }
    }
    assert!(n >= 78, "表の行数が少ない: {n}");
    assert!(bad.is_empty(), "判定が HEAD と違う:\n{}", bad.join("\n"));
}

/// 信頼側の実行（CLI の run と同じ経路）。出力は plain JSON の一行。
fn cli_run(src: &str, input: &str) -> String {
    static N: std::sync::atomic::AtomicUsize = std::sync::atomic::AtomicUsize::new(0);
    let n = N.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
    let path = std::env::temp_dir().join(format!("tlvm-rv-{}-{n}.tlvm", std::process::id()));
    std::fs::write(&path, src).unwrap();
    let o = Command::new(env!("CARGO_BIN_EXE_tlvm"))
        .args(["run", path.to_str().unwrap(), input, "--plain"])
        .output()
        .unwrap();
    std::fs::remove_file(&path).unwrap();
    assert_eq!(
        o.status.code(),
        Some(0),
        "{}",
        String::from_utf8_lossy(&o.stderr)
    );
    String::from_utf8(o.stdout).unwrap().trim_end().to_string()
}

/// 検証済みの IR の構造の等しさ。EProg と EExpr には比べる導出が無いので、変種ごとに比べる（Int は十進の文字列）。
fn same_prog(a: &EProg, b: &EProg) -> bool {
    a.entry == b.entry
        && a.rank == b.rank
        && a.rec == b.rec
        && a.funcs.len() == b.funcs.len()
        && a.funcs.iter().zip(b.funcs.iter()).all(|(f, g)| {
            f.params.len() == g.params.len()
                && f.params
                    .iter()
                    .zip(g.params.iter())
                    .all(|(p, q)| p.0 == q.0 && ty_eq(&p.1, &q.1))
                && ty_eq(&f.ret, &g.ret)
                && same_expr(&f.body, &g.body)
        })
}

fn same_exprs(xs: &[EExpr], ys: &[EExpr]) -> bool {
    xs.len() == ys.len() && xs.iter().zip(ys.iter()).all(|(x, y)| same_expr(x, y))
}

fn same_expr(a: &EExpr, b: &EExpr) -> bool {
    match (a, b) {
        (EExpr::Int(x), EExpr::Int(y)) => x.to_dec() == y.to_dec(),
        (EExpr::Bool(x), EExpr::Bool(y)) => x == y,
        (EExpr::Unit, EExpr::Unit) => true,
        (EExpr::Char(x), EExpr::Char(y)) => x == y,
        (EExpr::Var(x), EExpr::Var(y)) => x == y,
        (EExpr::List(t, xs), EExpr::List(u, ys)) => ty_eq(t, u) && same_exprs(xs, ys),
        (EExpr::Some(x), EExpr::Some(y)) => same_expr(x, y),
        (EExpr::None(t), EExpr::None(u)) => ty_eq(t, u),
        (EExpr::Pair(x1, x2), EExpr::Pair(y1, y2)) => same_expr(x1, y1) && same_expr(x2, y2),
        (EExpr::Builtin(f, xs), EExpr::Builtin(g, ys)) => f == g && same_exprs(xs, ys),
        (EExpr::Call(f, xs), EExpr::Call(g, ys)) => f == g && same_exprs(xs, ys),
        (EExpr::Let(x, a1, b1), EExpr::Let(y, a2, b2)) => {
            x == y && same_expr(a1, a2) && same_expr(b1, b2)
        }
        (EExpr::If(c1, t1, e1), EExpr::If(c2, t2, e2)) => {
            same_expr(c1, c2) && same_expr(t1, t2) && same_expr(e1, e2)
        }
        (EExpr::Fold(l1, i1, a1, x1, b1), EExpr::Fold(l2, i2, a2, x2, b2)) => {
            same_expr(l1, l2) && same_expr(i1, i2) && a1 == a2 && x1 == x2 && same_expr(b1, b2)
        }
        (EExpr::Match(m1, n1, x1, s1), EExpr::Match(m2, n2, x2, s2)) => {
            same_expr(m1, m2) && same_expr(n1, n2) && x1 == x2 && same_expr(s1, s2)
        }
        (EExpr::Inj(o1, t1, u1, x1), EExpr::Inj(o2, t2, u2, x2)) => {
            o1 == o2 && ty_eq(t1, t2) && ty_eq(u1, u2) && same_expr(x1, x2)
        }
        (EExpr::MatchR(m1, x1, a1, y1, b1), EExpr::MatchR(m2, x2, a2, y2, b2)) => {
            same_expr(m1, m2) && x1 == x2 && same_expr(a1, a2) && y1 == y2 && same_expr(b1, b2)
        }
        _ => false,
    }
}

/// 範囲内の受理（S5b）：源の文字列の印つきの写しと印なしの写しが両方受理し、添付の IR（program.verified）は
/// 源の印なしの写しの IR と構造で一致する。範囲の外と、ゲートが拒否する例は、この検査の対象にしない。
/// 限界：展開の文字列の IR を添付した場合も、この 23 件では同じ構造になる（確かめた結果）。この検査が区別するのは
/// 印つきの写しの IR を添付した場合だけ。経路を選ぶ代入（api.rs の verified_from_source）は、読んで確かめる。
/// 範囲内の形を広げる例（表には無い）：基の形（`..`）、字段の順を変える形、let と if の中の記録、入れ子、rec fn。
const V8_EXTRA: &[&str] = &[
    "type P = { a: Int, b: Int }\nfn f(x: Int) -> Int = P { ..P { a: x, b: 2 } }.a\nentry f\n",
    "type P = { a: Int, b: Int }\nfn f(x: Int) -> Int = P { a: x, ..P { a: 1, b: 2 } }.a\nentry f\n",
    "type P = { a: Int, b: Int }\nfn f(x: Int) -> Int = P { ..P { a: 1, b: x } }.b\nentry f\n",
    "type P = { a: Int, b: Int }\nfn f(x: Int) -> Int = P { b: x, a: 1 }.a\nentry f\n",
    "type P = { a: Int, b: Int }\nfn f(x: Int) -> Int = add(P { b: 1, a: x }.a, P { a: 2, b: x }.b)\nentry f\n",
    "type P = { a: Int, b: Int }\nfn f(x: Int) -> Int = let p = P { a: x, b: 1 } in p.a\nentry f\n",
    "type P = { a: Int, b: Int }\nfn f(x: Int) -> Int = if(le(x, 0), P { a: 0, b: 1 }.a, P { a: x, b: 1 }.a)\nentry f\n",
    "type I = { v: Int }\ntype P = { a: I, b: Int }\nfn f(x: Int) -> Int = P { a: I { v: x }, b: 2 }.a.v\nentry f\n",
    "type P = { a: Int }\nrec fn g(p: P, n: Int) -> Int = if(le(n, 0), p.a, add(n, g(p, sub(n, 1))))\nfn f(x: Int) -> Int = g(P { a: x }, 3)\nentry f\n",
    "type P = { list: Int, rec: Int }\nfn f(x: Int) -> Int = P { list: x, rec: 2 }.list\nentry f\n",
];

#[test]
fn v8_in_route_programs_are_checked_from_their_source() {
    let p = StaticProfile::default();
    let (d, td) = (
        p.expr_depth,
        p.type_depth.saturating_mul(2).saturating_add(2),
    );
    let mut all: Vec<(String, String)> = ROUTE_CORPUS
        .lines()
        .filter(|l| !l.is_empty())
        .map(|line| {
            let mut parts = line.splitn(3, '\t');
            let (origin, _want, esc) = (
                parts.next().unwrap(),
                parts.next().unwrap(),
                parts.next().unwrap(),
            );
            (origin.to_string(), unescape_tsv(esc))
        })
        .collect();
    all.extend(
        V8_EXTRA
            .iter()
            .enumerate()
            .map(|(i, s)| (format!("V8_EXTRA[{i}]"), s.to_string())),
    );
    let mut checked = 0;
    for (origin, src) in &all {
        let origin = origin.as_str();
        let src = src.as_str();
        if !in_verified_route(src.as_bytes(), &p) {
            continue;
        }
        let SourceCompile::Result(CompileResult::Accepted { program, .. }) =
            compile(src.as_bytes(), &p)
        else {
            continue;
        };
        let sp = match parse_source(src.as_bytes(), &p) {
            Parsed::Program(sp) => sp,
            Parsed::Failed(_) => panic!("範囲の判定と構文の結果が食い違う: {origin}"),
        };
        // rank と rec は源の関数の順（経路と同じ。展開が足す補助関数は数えない）。
        let rank: Vec<usize> = sp
            .functions()
            .map(|f| program.rank.get(&f.name).copied().unwrap_or(usize::MAX))
            .collect();
        let rec: Vec<bool> = sp.functions().map(|f| f.rec).collect();
        let chars: Vec<char> = without_rec_markers(&src, &sp).chars().collect();
        assert!(
            matches!(
                compile_source(&chars, d, td, rank.clone(), rec.clone(), true),
                Compiled::Accepted(_)
            ),
            "印つきの写しが受理しない: {origin}"
        );
        let untagged = match compile_source(&chars, d, td, rank, rec, false) {
            Compiled::Accepted(e) => e,
            _ => panic!("印なしの写しが受理しない: {origin}"),
        };
        let attached = program
            .verified
            .as_ref()
            .unwrap_or_else(|| panic!("添付の IR が無い: {origin}"));
        assert!(
            same_prog(&attached.0, &untagged),
            "添付の IR が源の印なしの IR と違う: {origin}"
        );
        checked += 1;
    }
    assert!(
        checked >= 20,
        "範囲内で受理するプログラムが少ない: {checked}"
    );
    println!("V8: 範囲内で受理し、源の二つの写しと IR を検査したプログラム {checked} 件");
}

/// 末尾の `,` の記録の式は、信頼側の構文器が拒否する（設計書の record_items に合わせた。オーナーの決定 2026-10-20）。
/// 検証済みの文法も `,` の後ろに字段を要求するので、この形は経路の判定に届かない。宣言の末尾の `,` は範囲の内（検証済みも受ける）。
#[test]
fn v8_record_literal_with_trailing_comma_is_rejected_before_the_route() {
    let p = StaticProfile::default();
    let lit = "type P = { a: Int, b: Int }\nfn f(x: Int) -> Int = P { a: x, b: x, }.a\nentry f\n";
    assert_eq!(
        rejected(lit),
        vec![row("parse", "E-PARSE-EXPECTED-IDENT", "identifier", "}")]
    );
    let decl = "type P = { a: Int, b: Int, }\nfn f(p: P) -> Int = p.a\nentry f\n";
    assert!(
        in_verified_route(decl.as_bytes(), &p),
        "宣言の末尾の , は範囲の内のはず"
    );
}

/// V10（S5b）：記録と、総称・Dict・hof・再帰を混ぜたプログラム。範囲の外なので、HEAD と同じ経路で、
/// 符号と出力は HEAD の記録と同じ（HEAD の値を直書きする）。
#[test]
fn v10_mixed_programs_keep_head_codes_and_outputs() {
    const OK: &[(&str, &str, &str)] = &[
        // 総称（id<T>）：HEAD は受理し、出力 5
        (
            "type P = { a: Int, b: Int }\nfn id<T>(x: T) -> T = x\nfn f(x: Int) -> Int = id(P { a: x, b: 2 }).a\nentry f\n",
            "5",
            "5",
        ),
        // Dict：HEAD は受理し、出力 1
        (
            "type P = { a: Int, b: Int }\nfn f(x: Int) -> Int = dict_size(dict_put(dict<String, Int>(), \"k\", P { a: x, b: 1 }.a))\nentry f\n",
            "5",
            "1",
        ),
        // hof（map）：HEAD は受理し、出力 6（fold は核の形なので hof ではない）
        (
            "type P = { a: Int, b: Int }\nfn f(xs: List<Int>) -> Int = fold(map(xs, |x| P { a: x, b: 1 }.a), 0, |acc, x| add(acc, x))\nentry f\n",
            "[1, 2, 3]",
            "6",
        ),
    ];
    for (src, input, want) in OK {
        assert!(
            !in_verified_route(src.as_bytes(), &StaticProfile::default()),
            "範囲の外のはず: {src}"
        );
        assert_eq!(cli_run(src, input), *want, "出力が HEAD と違う: {src}");
    }
    // 再帰する型：HEAD は E-TYPE-RETURN で拒否する
    let rec_src =
        "type P = { a: Int }\ntype L = Nil | Cons(Int, L)\nfn f(x: Int) -> P = x\nentry f\n";
    assert!(
        !in_verified_route(rec_src.as_bytes(), &StaticProfile::default()),
        "範囲の外のはず"
    );
    let codes: Vec<String> = rejected(rec_src).into_iter().map(|r| r.1).collect();
    assert_eq!(codes, ["E-TYPE-RETURN"]);
}

/// V13（S5b）：枝の並びの後ろの `,` は範囲の外（検証済みの構文器が読まない）。同じ match を `,` なしで書けば範囲の内で、
/// 注釈（`//`）の中の `,` は末尾の `,` ではない。
#[test]
fn v13_trailing_comma_after_the_last_arm_is_outside_the_route() {
    let p = StaticProfile::default();
    let head = "type Shape = Circle(Int) | Rect(Int, Int) | Empty\nfn mid(s: Shape) -> Int = match s { Circle(r) => r, Rect(w, h) => add(w, h), Empty => 0";
    let trailing = format!("{head}, }}\nentry mid\n");
    let plain = format!("{head} }}\nentry mid\n");
    let comment = format!("{head} // , 注釈\n}}\nentry mid\n");
    assert!(
        !in_verified_route(trailing.as_bytes(), &p),
        "末尾の , は範囲の外のはず"
    );
    assert!(
        in_verified_route(plain.as_bytes(), &p),
        "末尾の , がなければ範囲の内のはず"
    );
    assert!(
        in_verified_route(comment.as_bytes(), &p),
        "注釈の中の , は末尾の , ではない"
    );
    assert_eq!(verified_run(&plain, r#"{"Rect": [2, 3]}"#), "5");
    assert_eq!(verified_run(&comment, r#"{"Rect": [2, 3]}"#), "5");
}

/// V14（S5b）：記録と直和型を混ぜたプログラムは範囲の内（resolve_sound は表の形によらない）。検証済みの経路が受理し、
/// 検証済みの実行の出力は HEAD と同じ。字段の記録を枝に入れる、基ありの記録の構築、記録を持つ構築子を含む。
#[test]
fn v14_mixed_records_and_sums_run_on_the_verified_route() {
    const MIXED: &[(&str, &str, &str)] = &[
        (
            "type P = { a: Int, b: Int }\ntype S = Circle(Int) | Empty\nfn g(s: S) -> Int = match s { Circle(r) => P { a: r, b: 1 }.a, Empty => 0 }\nfn f(x: Int) -> Int = g(Circle(x))\nentry f\n",
            "5",
            "5",
        ),
        (
            "type P = { a: Int, b: Int }\ntype S = Circle(Int) | Empty\nfn g(s: S, q: P) -> P = match s { Circle(r) => P { a: r, ..q }, Empty => q }\nfn f(x: Int) -> Int = g(Circle(x), P { a: 0, b: 2 }).b\nentry f\n",
            "5",
            "2",
        ),
        (
            "type P = { a: Int, b: Int }\ntype S = Circle(P) | Empty\nfn f(x: Int) -> Int = match Circle(P { a: x, b: 1 }) { Circle(p) => p.a, Empty => 0 }\nentry f\n",
            "5",
            "5",
        ),
        (
            "type P = { a: Int, b: Int }\ntype S = Circle(Int) | Pt(P)\nfn g(s: S) -> Int = match s { Circle(r) => r, Pt(p) => add(p.a, p.b) }\nfn f(x: Int) -> Int = add(g(Circle(x)), g(Pt(P { a: 1, b: x })))\nentry f\n",
            "5",
            "11",
        ),
    ];
    let p = StaticProfile::default();
    for (src, input, want) in MIXED {
        assert!(
            in_verified_route(src.as_bytes(), &p),
            "範囲の内のはず: {src}"
        );
        assert_eq!(cli_run(src, input), *want, "出力が HEAD と違う: {src}");
        assert_eq!(
            verified_run(src, input),
            *want,
            "検証済みの出力が違う: {src}"
        );
    }
}

/// V11（S5b）：rec fn が記録を引数に取る例（HEAD は 11 を返す）は、範囲の内で、検証済みの実行も 11 を返す。
/// 相互再帰は、印のない循環を E-CYCLE-CALL で拒否し（HEAD と同じ）、印を付けた循環は HEAD と同じ出力を返す。
#[test]
fn v11_rec_functions_over_records_and_mutual_recursion_match_head() {
    let p = StaticProfile::default();
    let rec_src = "type P = { a: Int }\nrec fn g(p: P, n: Int) -> Int = if(le(n, 0), p.a, add(n, g(p, sub(n, 1))))\nfn f(x: Int) -> Int = g(P { a: x }, 3)\nentry f\n";
    assert!(
        in_verified_route(rec_src.as_bytes(), &p),
        "rec fn と記録は範囲の内のはず"
    );
    assert_eq!(cli_run(rec_src, "5"), "11");
    assert_eq!(verified_run(rec_src, "5"), "11");

    // 一方だけに印：HEAD は受理し、出力 5
    let one = "type P = { a: Int }\nrec fn ev(p: P, n: Int) -> Int = if(eq(n, 0), p.a, od(p, sub(n, 1)))\nfn od(p: P, n: Int) -> Int = ev(p, n)\nfn f(x: Int) -> Int = ev(P { a: x }, 3)\nentry f\n";
    assert_eq!(cli_run(one, "5"), "5");
    assert_eq!(verified_run(one, "5"), "5");

    // 両方に印：HEAD は受理し、出力 0
    let both = "type P = { a: Int }\nrec fn ev(p: P, n: Int) -> Int = if(eq(n, 0), p.a, od(p, sub(n, 1)))\nrec fn od(p: P, n: Int) -> Int = if(eq(n, 0), 0, ev(p, sub(n, 1)))\nfn f(x: Int) -> Int = ev(P { a: x }, 3)\nentry f\n";
    assert_eq!(cli_run(both, "5"), "0");
    assert_eq!(verified_run(both, "5"), "0");

    // 印のない循環：HEAD と同じく E-CYCLE-CALL で拒否する（記録の有無によらない）
    let cyc = "type P = { a: Int }\nfn ga(p: P) -> Int = gb(p)\nfn gb(p: P) -> Int = ga(p)\nfn f(x: Int) -> Int = ga(P { a: x })\nentry f\n";
    let codes: Vec<String> = rejected(cyc).into_iter().map(|r| r.1).collect();
    assert_eq!(codes, ["E-CYCLE-CALL"]);
    let cyc_plain = "fn ga(n: Int) -> Int = gb(n)\nfn gb(n: Int) -> Int = ga(n)\nfn f(x: Int) -> Int = ga(x)\nentry f\n";
    let codes: Vec<String> = rejected(cyc_plain).into_iter().map(|r| r.1).collect();
    assert_eq!(codes, ["E-CYCLE-CALL"]);
}

// ---------------------------------------------------------------- S5c：名前の変異の掃引（V7 の広い版）と V12

/// 変異の種類（掃引の順）。scratchpad の sweep.py（CLI で全体を一度回した）と同じ生成規則を使う。
const MUTANT_KINDS: [&str; 7] = [
    "unknown-type",
    "dup-type",
    "dup-field",
    "drop-field",
    "add-base",
    "drop-base",
    "rename-field",
];

/// この添字の段の変異だけを本体の掃引に使う（各プログラムの変異の添字が SWEEP_STEP の倍数のもの）。
const SWEEP_STEP: usize = 2;

#[derive(Clone, Copy, PartialEq, Eq)]
enum MK {
    Id,
    Num,
    Str,
    P,
}

#[derive(Clone, Copy)]
struct MTok<'a> {
    k: MK,
    t: &'a str,
    s: usize,
    e: usize,
}

/// 字句（識別子、数、文字列、`..`、`->`、一字の記号。空白は捨てる）。位置はバイトの添字。
fn mlex(src: &str) -> Vec<MTok<'_>> {
    let b = src.as_bytes();
    let n = b.len();
    let mut out = Vec::new();
    let mut i = 0;
    while i < n {
        let c = src[i..].chars().next().unwrap();
        if c.is_whitespace() {
            i += c.len_utf8();
            continue;
        }
        let (k, end) = if c.is_ascii_alphabetic() || c == '_' {
            let mut j = i + 1;
            while j < n && (b[j].is_ascii_alphanumeric() || b[j] == b'_') {
                j += 1;
            }
            (MK::Id, j)
        } else if c.is_ascii_digit() {
            let mut j = i + 1;
            while j < n && b[j].is_ascii_digit() {
                j += 1;
            }
            (MK::Num, j)
        } else if c == '"' {
            let mut j = i + 1;
            while j < n && b[j] != b'"' {
                j += if b[j] == b'\\' { 2 } else { 1 };
            }
            (MK::Str, (j + 1).min(n))
        } else if src[i..].starts_with("..") || src[i..].starts_with("->") {
            (MK::P, i + 2)
        } else {
            (MK::P, i + c.len_utf8())
        };
        out.push(MTok {
            k,
            t: &src[i..end],
            s: i,
            e: end,
        });
        i = end;
    }
    out
}

/// toks[i] の開き括弧に対応する閉じ括弧の添字。
fn mmatch_close(toks: &[MTok<'_>], i: usize) -> Option<usize> {
    let (open, close) = match toks[i].t {
        "{" => ("{", "}"),
        "(" => ("(", ")"),
        "<" => ("<", ">"),
        _ => return None,
    };
    let mut depth: i64 = 0;
    for j in i..toks.len() {
        if toks[j].k == MK::P {
            if toks[j].t == open {
                depth += 1;
            } else if toks[j].t == close {
                depth -= 1;
                if depth == 0 {
                    return Some(j);
                }
            }
        }
    }
    None
}

/// 括弧 lo..hi（lo は開き、hi は閉じ括弧の添字）の中の要素。深さ 0 のコンマで区切る（要素の範囲は添字の半開区間）。
fn mentries(toks: &[MTok<'_>], lo: usize, hi: usize) -> Vec<(usize, usize)> {
    let mut out = Vec::new();
    let mut depth: i64 = 0;
    let mut start = lo + 1;
    for j in lo + 1..hi {
        if toks[j].k != MK::P {
            continue;
        }
        match toks[j].t {
            "(" | "{" | "<" => depth += 1,
            ")" | "}" | ">" => depth -= 1,
            "," if depth == 0 => {
                out.push((start, j));
                start = j + 1;
            }
            _ => {}
        }
    }
    if start < hi {
        out.push((start, hi));
    }
    out.retain(|&(a, b)| a < b);
    out
}

/// 記録の宣言（総称でないもの）：(`type` の添字, `{` の添字, `}` の添字, 名前)。
fn mrecord_decls<'a>(toks: &[MTok<'a>]) -> Vec<(usize, usize, usize, &'a str)> {
    let mut out = Vec::new();
    if toks.len() < 4 {
        return out;
    }
    for i in 0..toks.len() - 3 {
        if toks[i].k == MK::Id
            && toks[i].t == "type"
            && toks[i + 1].k == MK::Id
            && toks[i + 2].t == "="
            && toks[i + 3].t == "{"
        {
            if let Some(c) = mmatch_close(toks, i + 3) {
                out.push((i, i + 3, c, toks[i + 1].t));
            }
        }
    }
    out
}

/// 記録だけのプログラム：`type` の宣言が一つ以上あり、すべて記録（`= {`）。
fn mrecord_only(src: &str) -> bool {
    let toks = mlex(src);
    let mut decls = 0;
    for i in 0..toks.len() {
        if toks[i].k == MK::Id
            && toks[i].t == "type"
            && i + 1 < toks.len()
            && toks[i + 1].k == MK::Id
        {
            decls += 1;
            let mut j = i + 2;
            if j < toks.len() && toks[j].t == "<" {
                while j < toks.len() && toks[j].t != ">" {
                    j += 1;
                }
                j += 1;
            }
            if !(j + 1 < toks.len() && toks[j].t == "=" && toks[j + 1].t == "{") {
                return false;
            }
        }
    }
    decls > 0
}

/// 記録の式の末尾のコンマ（`P { a: x, }`）。関数の本体（最初の `fn` より後）にあるものだけを数える。
fn mliteral_trailing_comma(src: &str) -> bool {
    let Some(i) = src.find("fn ") else {
        return false;
    };
    let b = src[i..].as_bytes();
    (0..b.len()).any(|j| {
        b[j] == b',' && {
            let mut k = j + 1;
            while k < b.len() && b[k].is_ascii_whitespace() {
                k += 1;
            }
            k < b.len() && b[k] == b'}'
        }
    })
}

/// 一つのプログラムの変異（種類と変異後の文字列）。種類の順に、宣言の順・式の順に並べる。
/// unknown-type：型の参照（`type` の後ろ以外）を、宣言されていない名前 ZQ にする。
/// dup-type：記録の宣言を、その直後にもう一度書く。dup-field：宣言の字段を、その直後にもう一度書く。
/// drop-field：記録の式の字段を一つ、隣のコンマと一緒に落とす。add-base：基のない記録の式に `..ZQ` を足す。
/// drop-base：記録の式の基を落とす。rename-field：宣言・記録の式の字段名（`:` の前）と `.` の後ろの字段名を fz にする。
fn record_mutants(src: &str) -> Vec<(&'static str, String)> {
    let toks = mlex(src);
    let decls = mrecord_decls(&toks);
    let dnames: BTreeSet<&str> = decls.iter().map(|d| d.3).collect();
    let mut dfields: BTreeSet<&str> = BTreeSet::new();
    let mut decl_spans = Vec::new();
    for &(_, ob, cb, _) in &decls {
        decl_spans.push((toks[ob].s, toks[cb].e));
        for (a, b) in mentries(&toks, ob, cb) {
            if toks[a].k == MK::Id && a + 1 < b && toks[a + 1].t == ":" {
                dfields.insert(toks[a].t);
            }
        }
    }
    let mut lits: Vec<(usize, usize)> = Vec::new();
    for i in 1..toks.len().saturating_sub(1) {
        if toks[i].k == MK::Id
            && dnames.contains(toks[i].t)
            && toks[i + 1].k == MK::P
            && toks[i + 1].t == "{"
            && !(toks[i - 1].k == MK::Id && toks[i - 1].t == "type")
        {
            if let Some(c) = mmatch_close(&toks, i + 1) {
                lits.push((i + 1, c));
            }
        }
    }
    let lit_spans: Vec<(usize, usize)> = lits
        .iter()
        .map(|&(ob, cb)| (toks[ob].s, toks[cb].e))
        .collect();
    let inside =
        |pos: usize, spans: &[(usize, usize)]| spans.iter().any(|&(a, b)| a <= pos && pos < b);
    let mut out: Vec<(&'static str, String)> = Vec::new();
    for (i, t) in toks.iter().enumerate() {
        if t.k == MK::Id
            && dnames.contains(t.t)
            && !(i > 0 && toks[i - 1].k == MK::Id && toks[i - 1].t == "type")
        {
            out.push(("unknown-type", format!("{}ZQ{}", &src[..t.s], &src[t.e..])));
        }
    }
    for &(ti, _, cb, _) in &decls {
        let (a, b) = (toks[ti].s, toks[cb].e);
        out.push((
            "dup-type",
            format!("{}\n{}{}", &src[..b], &src[a..b], &src[b..]),
        ));
    }
    for &(_, ob, cb, _) in &decls {
        for (a, b) in mentries(&toks, ob, cb) {
            if toks[a].k == MK::Id && a + 1 < b && toks[a + 1].t == ":" {
                let (s, e) = (toks[a].s, toks[b - 1].e);
                out.push((
                    "dup-field",
                    format!("{}, {}{}", &src[..e], &src[s..e], &src[e..]),
                ));
            }
        }
    }
    for &(ob, cb) in &lits {
        let ents = mentries(&toks, ob, cb);
        let base: Vec<(usize, usize)> = ents
            .iter()
            .copied()
            .filter(|&(a, _)| toks[a].k == MK::P && toks[a].t == "..")
            .collect();
        let fields: Vec<(usize, usize)> = ents
            .iter()
            .copied()
            .filter(|&(a, b)| toks[a].k == MK::Id && a + 1 < b && toks[a + 1].t == ":")
            .collect();
        for &(a, b) in &fields {
            let k = ents.iter().position(|&x| x == (a, b)).unwrap();
            let m = if k + 1 < ents.len() {
                format!("{}{}", &src[..toks[a].s], &src[toks[ents[k + 1].0].s..])
            } else if k > 0 {
                format!("{}{}", &src[..toks[ents[k - 1].1].s], &src[toks[b - 1].e..])
            } else {
                format!("{}{}", &src[..toks[a].s], &src[toks[b - 1].e..])
            };
            out.push(("drop-field", m));
        }
        if base.is_empty() {
            let close = toks[cb].s;
            let sep = if ents.is_empty() { " " } else { ", " };
            out.push((
                "add-base",
                format!("{}{}..ZQ {}", src[..close].trim_end(), sep, &src[close..]),
            ));
        } else {
            let (a, b) = base[0];
            let k = ents.iter().position(|&x| x == (a, b)).unwrap();
            let m = if k > 0 {
                format!("{}{}", &src[..toks[ents[k - 1].1].s], &src[toks[b - 1].e..])
            } else {
                format!("{}{}", &src[..toks[a].s], &src[toks[b - 1].e..])
            };
            out.push(("drop-base", m));
        }
    }
    for (i, t) in toks.iter().enumerate() {
        if t.k == MK::Id && dfields.contains(t.t) {
            let after_dot = i > 0 && toks[i - 1].k == MK::P && toks[i - 1].t == ".";
            let colon = i + 1 < toks.len() && toks[i + 1].k == MK::P && toks[i + 1].t == ":";
            if after_dot || (colon && (inside(t.s, &decl_spans) || inside(t.s, &lit_spans))) {
                out.push(("rename-field", format!("{}fz{}", &src[..t.s], &src[t.e..])));
            }
        }
    }
    out
}

/// 掃引のプログラム：route_corpus.tsv と v7_corpus() の記録だけのもの（重複を除く）。末尾のコンマの記録の式は除く（構文で拒否するので、検証済みの経路に届かない）。
/// 戻り値は (出典, プログラム) の列と、除いたものの出典。
fn sweep_programs() -> (Vec<(String, String)>, Vec<String>) {
    let mut all: Vec<(String, String)> = Vec::new();
    for line in ROUTE_CORPUS.lines().filter(|l| !l.is_empty()) {
        let mut parts = line.splitn(3, '\t');
        let origin = parts.next().unwrap();
        let _verdict = parts.next().unwrap();
        let esc = parts.next().unwrap();
        all.push((origin.to_string(), unescape_tsv(esc)));
    }
    for (src, _) in v7_corpus() {
        all.push(("v7".to_string(), src));
    }
    let mut seen: BTreeSet<String> = BTreeSet::new();
    let (mut out, mut excluded) = (Vec::new(), Vec::new());
    for (origin, src) in all {
        if !mrecord_only(&src) {
            continue;
        }
        if mliteral_trailing_comma(&src) {
            excluded.push(origin);
            continue;
        }
        if seen.insert(src.clone()) {
            out.push((origin, src));
        }
    }
    (out, excluded)
}

/// S5c（V7 の広い版）：記録だけのプログラムの変異を本番の検査（api::compile）で判定する。どの変異でも、
/// 展開段階の名前の診断に検証済みの符号（E-INTERNAL-VERIFIED-MISMATCH と verified-*）が付かないこと。
#[test]
fn v7_record_mutations_get_no_verified_mismatch() {
    let (progs, excluded) = sweep_programs();
    assert!(progs.len() >= 70, "プログラムが少ない: {}", progs.len());
    assert_eq!(
        excluded,
        ["record_names.rs:383"],
        "除くのは末尾のコンマの記録の式だけ（構文で拒否する）"
    );
    let mut per_kind: BTreeMap<&str, usize> = BTreeMap::new();
    let (mut total, mut name_checked) = (0, 0);
    for (origin, src) in &progs {
        for (mi, (kind, text)) in record_mutants(src).into_iter().enumerate() {
            if mi % SWEEP_STEP != 0 {
                continue;
            }
            total += 1;
            *per_kind.entry(kind).or_insert(0) += 1;
            match compile(text.as_bytes(), &StaticProfile::default()) {
                SourceCompile::Result(CompileResult::Rejected { errors, .. }) => {
                    for d in &errors {
                        let actual = d.actual.as_deref().unwrap_or("");
                        assert!(
                            !(d.code == MISMATCH && actual.starts_with("verified-")),
                            "{origin} の変異 {kind} で検証済みの食い違い（{actual}）: {text:?}"
                        );
                    }
                    if errors
                        .iter()
                        .any(|d| CHECKED_EXPANSION_CODES.contains(&d.code))
                    {
                        name_checked += 1;
                    }
                }
                SourceCompile::Result(CompileResult::Accepted { .. }) => {}
                _ => panic!("結果が出ない: {text:?}"),
            }
        }
    }
    assert_eq!(
        per_kind.len(),
        MUTANT_KINDS.len(),
        "全部の種類が掃引に入る: {per_kind:?}"
    );
    assert!(
        name_checked >= 100,
        "名前の符号の変異が少ない（突き合わせが働かない）: {name_checked} / {total}"
    );
}

/// S5c（V12）：宣言の数と書換えの大きさ。HEAD（9a96889 の CLI）の判定と同じ符号・値を返す。
/// (1) 200 の平らな記録の宣言（使うのは R0 だけ）。HEAD は宣言の型の深さの上限（128）で拒否する
///     （E-LIMIT-STATIC-SEMANTIC-TYPE-DEPTH、実際 129、span 4458..4495）。使わない宣言も検査する。
/// (2) 60 段の鎖の記録と、R59 を引数に取る 200 の関数。書換え後の大きさが 4 MiB を超え、HEAD は 5663489 bytes で
///     拒否する（E-LIMIT-STATIC-REWRITTEN-BYTES）。大きさの判定は、ゲートの書換え後の文字列にだけ掛かる。
#[test]
fn v12_declaration_count_and_rewritten_size_decisions_match_head() {
    let p = StaticProfile::default();
    let flat: String = (0..200)
        .map(|k| format!("type R{k} = {{ a{k}: Int, b{k}: Bool }}\n"))
        .collect::<String>()
        + "fn g0(x: R0) -> Int = 0\nentry g0\n";
    match compile(flat.as_bytes(), &p) {
        SourceCompile::Result(CompileResult::Rejected { errors, .. }) => {
            assert_eq!(errors.len(), 1, "HEAD は一つの符号で拒否する: {errors:?}");
            let d = &errors[0];
            assert_eq!(d.code, "E-LIMIT-STATIC-SEMANTIC-TYPE-DEPTH");
            assert_eq!(d.expected.as_deref(), Some("128"));
            assert_eq!(d.actual.as_deref(), Some("129"));
            assert_eq!(d.span, (4458, 4495));
        }
        _ => panic!("HEAD は 200 の宣言を型の深さの上限で拒否する"),
    }
    let mut chain = String::from("type R0 = { v0: Int }\n");
    for k in 1..60 {
        chain += &format!("type R{k} = {{ p{k}: R{}, v{k}: Int }}\n", k - 1);
    }
    for i in 0..200 {
        chain += &format!("fn g{i}(x: R59) -> Int = 0\n");
    }
    chain += "entry g0\n";
    match compile(chain.as_bytes(), &p) {
        SourceCompile::Result(CompileResult::Rejected { errors, .. }) => {
            assert_eq!(errors.len(), 1, "HEAD は一つの符号で拒否する: {errors:?}");
            let d = &errors[0];
            assert_eq!(d.code, "E-LIMIT-STATIC-REWRITTEN-BYTES");
            assert_eq!(d.expected.as_deref(), Some("4194304"));
            assert_eq!(d.actual.as_deref(), Some("5663489"));
        }
        _ => panic!("HEAD は書換え後の大きさの上限で拒否する"),
    }
}
