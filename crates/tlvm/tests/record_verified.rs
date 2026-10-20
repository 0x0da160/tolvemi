//! 宣言の名前の規則を、検証済みの部品と信頼側で突き合わせる（stage 2・S2a）。
//!
//! V1：宣言だけのプログラムで、検証済みの `parse_e` と `resolve_e` の受理が、信頼側の受理・拒否と一致する。
//!     対象は宣言の四つの符号（E-RECORD-UNKNOWN-TYPE、E-RECORD-DUPLICATE-TYPE、E-RECORD-DUPLICATE-FIELD、
//!     E-RECORD-FIELD-CONFLICT）と、それを出さない宣言の形（前方の型の参照、関数の注釈の前方参照、
//!     型名と関数名の一致、字段の型に既知の記録、直和型の中身に前の記録）。
//! V2：記録と直和型をまたぐ型名の重複（E-RECORD-DUPLICATE-TYPE）。宣言の順を変えても拒否する。
//!
//! 検証済みの部品は直接呼ぶ（api の突き合わせは通さない）。直和型は核の型にまだ入らないので、
//! 直和型を関数の注釈や式に使うプログラムは含めない（段階 3）。

use tlvm::api::*;
use tlvm::profiles::*;
use tlvm_verified::resolve::resolve_e;
use tlvm_verified::surface::parse_e;

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

/// 検証済みの受理：parse_e が通り、resolve_e が通る。深さの上限は api の depth_bounds と同じ。
fn verified_accepts(src: &str) -> bool {
    let p = StaticProfile::default();
    let (d, td) = (p.expr_depth, p.type_depth.saturating_mul(2).saturating_add(2));
    let chars: Vec<char> = src.chars().collect();
    match parse_e(&chars, d, td) {
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
