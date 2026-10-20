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
//! 検証済みの部品は直接呼ぶ（api の突き合わせは通さない）。直和型は核の型にまだ入らないので、
//! 直和型を関数の注釈や式に使うプログラムは含めない（段階 3）。

use tlvm::api::*;
use tlvm::nominal::Tags;
use tlvm::profiles::*;
use tlvm::syntax::Decl;
use tlvm_verified::resolve::{decl_numbers_e, resolve_e};
use tlvm_verified::surface::{parse_e, SDecl};

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
