//! §18.1c：v1.1〜v1.16 の追加分の型検査の論理仕事量（規則 R・G・L）の固定値。
//! 期待値は `docs/typecheck-counting-design.md` の §2、§5、§6 の規則から手で求めたものであり、処理系の出力を写したものではない。

use tlvm::api::{compile, expand, parse_source, CompileResult, Parsed, SourceCompile};
use tlvm::checker::{CheckOptions, TypeSharing, WorkCounter};
use tlvm::generics::check_with;
use tlvm::profiles::StaticProfile;

fn sp(semantic_work: u64) -> StaticProfile {
    StaticProfile {
        semantic_work,
        ..StaticProfile::default()
    }
}

fn total(w: Option<WorkCounter>) -> u64 {
    w.map_or(0, |w| w.total())
}

/// 受理したか、報告された仕事量の総計、診断の code。
fn outcome(src: &str, profile: &StaticProfile) -> (bool, u64, Vec<&'static str>) {
    match compile(src.as_bytes(), profile) {
        SourceCompile::Result(CompileResult::Accepted { work, .. }) => (true, total(work), vec![]),
        SourceCompile::Result(CompileResult::Rejected { work, errors, .. }) => {
            (false, total(work), errors.iter().map(|d| d.code).collect())
        }
        _ => panic!("結果が出ない: {src}"),
    }
}

/// 型検査器の論理 trace（イベントの名前だけ）。`sharing` は比較 cache の切替。
fn trace(src: &str, sharing: TypeSharing) -> Vec<&'static str> {
    let p = match parse_source(src.as_bytes(), &StaticProfile::default()) {
        Parsed::Program(p) => p,
        Parsed::Failed(_) => panic!("解析できない: {src}"),
    };
    let px = expand(&p).unwrap_or_else(|_| panic!("展開できない: {src}"));
    let (o, _) = check_with(&px, src.len(), &StaticProfile::default(), &CheckOptions { sharing, trace: true });
    o.trace.expect("trace は要求した").into_iter().map(|(n, _)| n).collect()
}

/// §2 の 15 件（entry は `f`）。受理するものと、拒否するもの（4 件目）。仕事量は規則から手で求めた総計。
const FIFTEEN: [(&str, bool, u64); 15] = [
    ("fn f(x: Int) -> Int = x", true, 2),
    ("fn f(x: List<Int>) -> List<Int> = map(x, |y| add(y, 1))", true, 13),
    ("fn g<T>(x: T) -> T = x\nfn f(x: Int) -> Int = x", true, 4),
    ("fn f(x: Int) -> Option<Int> = loop(x, true, |s| none<Int>())", false, 9),
    ("type S = Circle(Int) | Sq(Bool)\nfn f(x: Int) -> S = Sq(true)", true, 8),
    ("type P = { x: Int, y: Bool }\nfn f(p: Int) -> P = P { x: p, y: true }", true, 8),
    (
        "fn f(x: Int) -> Option<Int> = dict_get(dict_put(dict<Int, Int>(), 1, x), 1)",
        true,
        17,
    ),
    ("fn f(x: Option<Int>) -> Int = match_option(x, 0, |y| y)", true, 8),
    ("fn f(x: List<Int>) -> Option<Pair<Int, List<Int>>> = uncons(x)", true, 10),
    ("fn id<T>(x: T) -> T = x\nfn f(x: Int) -> Int = id(x)", true, 10),
    ("fn f(x: Int) -> String = \"ab\"", true, 5),
    ("fn f(x: Int) -> Option<Int> = div(x, 2)", true, 10),
    ("fn f(x: List<Int>) -> List<Int> = sort(x)", true, 6),
    ("fn f(x: Int) -> List<Int> = range(0, x)", true, 10),
    ("fn f(x: List<Int>) -> Bool = contains(x, 1)", true, 8),
];

#[test]
fn fifteen_addition_families_have_fixed_totals() {
    for (src, accepted, want) in FIFTEEN {
        let src = format!("{src}\nentry f");
        let (ok, got, codes) = outcome(&src, &sp(2_000_000));
        assert_eq!(ok, accepted, "{src}: {codes:?}");
        assert_eq!(got, want, "{src}");
    }
}

#[test]
fn sharing_does_not_change_counts_or_trace() {
    // 比較 cache の On と Off で、論理 trace と仕事量が同じ（規則 G の数えない関数も cache の記録に入る）
    for (src, _, _) in FIFTEEN {
        let src = format!("{src}\nentry f");
        let off = trace(&src, TypeSharing::Off);
        let on = trace(&src, TypeSharing::On);
        assert_eq!(off, on, "{src}");
    }
}

#[test]
fn unused_generic_counts_its_declared_form() {
    // 使われない総称の関数も、宣言の形で一度数える（規則 G）。g の本体 2 と f の本体 2。
    let src = "fn g<T>(x: T) -> T = x\nfn f(x: Int) -> Int = x\nentry f";
    assert_eq!(outcome(src, &sp(2_000_000)), (true, 4, vec![]));
    let (ok, total, codes) = outcome(src, &sp(3));
    assert!(!ok);
    assert_eq!(codes, ["E-LIMIT-STATIC-SEMANTIC-WORK"]);
    assert_eq!(total, 3);
}

#[test]
fn generic_call_counts_declared_form_plus_one_copy() {
    // 第一パス 8（id の本体 2、f の 6：呼出し 2、引数の束縛 1、型引数と戻り型の BuildType 2、戻り 1）と、
    // 複製 id の本体 2 の和。非総称の f は複製の方では数え直さない。
    let src = "fn id<T>(x: T) -> T = x\nfn f(x: Int) -> Int = id(x)\nentry f";
    assert_eq!(outcome(src, &sp(2_000_000)), (true, 10, vec![]));
    assert_eq!(
        trace(src, TypeSharing::Off),
        ["visit", "compare", "visit", "visit", "compare", "build", "build", "compare", "visit", "compare"]
    );
}

#[test]
fn generic_copies_are_inside_the_running_total() {
    // 上限は第一パスと複製の和に対して検査する。第一パスの 8 の後で、複製の本体の一つ目（9）と二つ目（10）を数える。
    let src = "fn id<T>(x: T) -> T = x\nfn f(x: Int) -> Int = id(x)\nentry f";
    assert_eq!(outcome(src, &sp(10)), (true, 10, vec![]));
    assert_eq!(outcome(src, &sp(9)), (false, 9, vec!["E-LIMIT-STATIC-SEMANTIC-WORK"]));
    assert_eq!(outcome(src, &sp(8)), (false, 8, vec!["E-LIMIT-STATIC-SEMANTIC-WORK"]));
    assert_eq!(outcome(src, &sp(7)), (false, 7, vec!["E-LIMIT-STATIC-SEMANTIC-WORK"]));
}

#[test]
fn loop_result_type_is_counted_last_when_accepted() {
    // 規則 L：Option<Int> の BuildType は、比較の後の最後に一つ。総計は 12（視認 4、構成 3、比較 5）。
    let src = "fn f(x: Int) -> Option<Int> = loop(x, 3, |s| none<Int>())\nentry f";
    assert_eq!(outcome(src, &sp(2_000_000)), (true, 12, vec![]));
    assert_eq!(
        trace(src, TypeSharing::Off),
        ["visit", "visit", "visit", "build", "compare", "visit", "build", "compare", "compare", "build", "compare", "compare"]
    );
}

#[test]
fn loop_result_type_is_not_counted_when_the_loop_is_wrong() {
    // 規則 L：最大回数が Int でないとき、結果型の BuildType は数えない（10 から 9 に減る）。
    let (ok, total, codes) = outcome(
        "fn f(x: Int) -> Option<Int> = loop(x, true, |s| none<Int>())\nentry f",
        &sp(2_000_000),
    );
    assert!(!ok);
    assert_eq!(codes, ["E-TYPE-LOOP-MAX"]);
    assert_eq!(total, 9);
    // 本体が Option<S> でないときも同じ。
    let (ok, total, codes) = outcome("fn f(x: Int) -> Option<Int> = loop(x, 3, |s| 0)\nentry f", &sp(2_000_000));
    assert!(!ok);
    assert_eq!(codes, ["E-TYPE-LOOP-BODY"]);
    assert_eq!(total, 8);
}
