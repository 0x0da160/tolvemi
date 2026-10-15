//! §18.1c：v1.1〜v1.16 の追加分の型検査の論理仕事量（規則 R・G・L）の固定値。
//! 期待値は `docs/typecheck-counting-design.md` の §2、§5、§6 の規則から手で求めたものであり、処理系の出力を写したものではない。

use tlvm::api::{compile, expand, parse_source, CompileResult, Parsed, SourceCompile};
use tlvm::checker::{CheckOptions, TypeSharing, WorkCounter};
use tlvm::generics::check_with;
use tlvm::profiles::{ExecutionProfile, HostPolicy, InputProfile, StaticProfile};

/// 代表 program（TREE_SIZE、入力 3）の Steps と AllocatedNodes。処理系の出力を固定した値（手計算ではない）。
const STEPS_TREE_SIZE: u64 = 2212;
const ALLOCS_TREE_SIZE: u64 = 305;

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
    let (o, _) = check_with(
        &px,
        src.len(),
        &StaticProfile::default(),
        &CheckOptions {
            sharing,
            trace: true,
        },
    );
    o.trace
        .expect("trace は要求した")
        .into_iter()
        .map(|(n, _)| n)
        .collect()
}

/// §2 の 15 件（entry は `f`）。受理するものと、拒否するもの（4 件目）。仕事量は規則から手で求めた総計。
const FIFTEEN: [(&str, bool, u64); 15] = [
    ("fn f(x: Int) -> Int = x", true, 2),
    (
        "fn f(x: List<Int>) -> List<Int> = map(x, |y| add(y, 1))",
        true,
        13,
    ),
    ("fn g<T>(x: T) -> T = x\nfn f(x: Int) -> Int = x", true, 4),
    (
        "fn f(x: Int) -> Option<Int> = loop(x, true, |s| none<Int>())",
        false,
        9,
    ),
    (
        "type S = Circle(Int) | Sq(Bool)\nfn f(x: Int) -> S = Sq(true)",
        true,
        8,
    ),
    (
        "type P = { x: Int, y: Bool }\nfn f(p: Int) -> P = P { x: p, y: true }",
        true,
        8,
    ),
    (
        "fn f(x: Int) -> Option<Int> = dict_get(dict_put(dict<Int, Int>(), 1, x), 1)",
        true,
        17,
    ),
    (
        "fn f(x: Option<Int>) -> Int = match_option(x, 0, |y| y)",
        true,
        8,
    ),
    (
        "fn f(x: List<Int>) -> Option<Pair<Int, List<Int>>> = uncons(x)",
        true,
        10,
    ),
    (
        "fn id<T>(x: T) -> T = x\nfn f(x: Int) -> Int = id(x)",
        true,
        10,
    ),
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
        [
            "visit", "compare", "visit", "visit", "compare", "build", "build", "compare", "visit",
            "compare"
        ]
    );
}

#[test]
fn generic_copies_are_inside_the_running_total() {
    // 上限は第一パスと複製の和に対して検査する。第一パスの 8 の後で、複製の本体の一つ目（9）と二つ目（10）を数える。
    let src = "fn id<T>(x: T) -> T = x\nfn f(x: Int) -> Int = id(x)\nentry f";
    assert_eq!(outcome(src, &sp(10)), (true, 10, vec![]));
    assert_eq!(
        outcome(src, &sp(9)),
        (false, 9, vec!["E-LIMIT-STATIC-SEMANTIC-WORK"])
    );
    assert_eq!(
        outcome(src, &sp(8)),
        (false, 8, vec!["E-LIMIT-STATIC-SEMANTIC-WORK"])
    );
    assert_eq!(
        outcome(src, &sp(7)),
        (false, 7, vec!["E-LIMIT-STATIC-SEMANTIC-WORK"])
    );
}

#[test]
fn loop_result_type_is_counted_last_when_accepted() {
    // 規則 L：Option<Int> の BuildType は、比較の後の最後に一つ。総計は 12（視認 4、構成 3、比較 5）。
    let src = "fn f(x: Int) -> Option<Int> = loop(x, 3, |s| none<Int>())\nentry f";
    assert_eq!(outcome(src, &sp(2_000_000)), (true, 12, vec![]));
    assert_eq!(
        trace(src, TypeSharing::Off),
        [
            "visit", "visit", "visit", "build", "compare", "visit", "build", "compare", "compare",
            "build", "compare", "compare"
        ]
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
    let (ok, total, codes) = outcome(
        "fn f(x: Int) -> Option<Int> = loop(x, 3, |s| 0)\nentry f",
        &sp(2_000_000),
    );
    assert!(!ok);
    assert_eq!(codes, ["E-TYPE-LOOP-BODY"]);
    assert_eq!(total, 8);
}

/// 型検査器の論理 trace（イベントの名前だけ）。比較 cache は Off。
fn trace_of(px: &tlvm::syntax::Program, len: usize) -> Vec<&'static str> {
    let (o, _) = check_with(
        px,
        len,
        &StaticProfile::default(),
        &CheckOptions {
            sharing: TypeSharing::Off,
            trace: true,
        },
    );
    o.trace
        .expect("trace は要求した")
        .into_iter()
        .map(|(n, _)| n)
        .collect()
}

#[test]
fn rec_mark_does_not_change_the_trace() {
    // 関数の印 `rec`（v1.7）を外しても、論理 trace と仕事量は同じ。名義の型の印つきの写しは別の問題で、下の
    // tagged_copy_is_reported_only_when_rejected で扱う。
    let srcs = [
        "rec fn f(n: Int) -> Int = if(le(n, 0), 0, f(sub(n, 1)))\nentry f",
        "rec fn even(n: Int) -> Bool = if(eq(n, 0), true, odd(sub(n, 1)))\nrec fn odd(n: Int) -> Bool = if(eq(n, 0), false, even(sub(n, 1)))\nfn solve(n: Int) -> Pair<Bool, Bool> = pair(even(n), odd(n))\nentry solve",
        "type Tree = Leaf | Node(Tree, Int, Tree)\nrec fn size(t: Tree) -> Int = match t { Leaf => 0, Node(l, v, r) => add(size(l), add(v, size(r))) }\nfn solve(t: Tree) -> Int = size(t)\nentry solve",
    ];
    for src in srcs {
        let p = match parse_source(src.as_bytes(), &StaticProfile::default()) {
            Parsed::Program(p) => p,
            Parsed::Failed(_) => panic!("解析できない: {src}"),
        };
        let marked = expand(&p).unwrap_or_else(|_| panic!("展開できない: {src}"));
        let unmarked = marked.unmarked();
        assert_eq!(
            trace_of(&marked, src.len()),
            trace_of(&unmarked, src.len()),
            "{src}"
        );
    }
}

#[test]
fn reference_events_of_small_programs_are_fixed() {
    // §18.3 の参照イベントを手で数えた値。式 node、関数入場、組込みの適用、割当（新規整数の確保）の各一つが一 step。
    // P1：入場 1、x の node 1 で 2 step。割当 0。
    // P2：入場 1、add の node 1、組込み 1、x の node 1、1 の node 1 で 5 step。割当は 1 と結果の 2 で、さらに 2 step。計 7。
    // P3：入場 1、add の node 2、組込み 2、x・1・2 の node 3 で 8 step。割当は 1、内側の結果、2、外側の結果の 4 で、さらに 4 step。計 12。
    let cases = [
        ("fn f(x: Int) -> Int = x\nentry f", 2, 0),
        ("fn f(x: Int) -> Int = add(x, 1)\nentry f", 7, 2),
        ("fn f(x: Int) -> Int = add(add(x, 1), 2)\nentry f", 12, 4),
    ];
    for (src, steps, alloc) in cases {
        let program = match compile(src.as_bytes(), &StaticProfile::default()) {
            SourceCompile::Result(CompileResult::Accepted { program, .. }) => program,
            _ => panic!("受理されない: {src}"),
        };
        let input = match tlvm::api::decode_input(
            &program.input_type,
            br#"{"tag":"int","value":"0"}"#,
            &tlvm::profiles::InputProfile::default(),
        ) {
            tlvm::DecodeResult::Decoded(tv) => tv,
            _ => panic!("入力"),
        };
        let r = tlvm::api::run(
            &program,
            &input,
            &tlvm::profiles::ExecutionProfile::default(),
            &tlvm::profiles::HostPolicy::default(),
        );
        assert!(
            matches!(r, Ok(tlvm::evaluator::RunResult::Completed { steps: s, allocated_nodes: a, .. }) if (s, a) == (steps, alloc)),
            "{src}: {r:?}"
        );
    }
}

/// 宣言が再帰する型の代表 program（`size` の木の和）。
const TREE_SIZE: &str = "type Tree = Leaf | Node(Tree, Int, Tree)\nrec fn size(t: Tree) -> Int = match t { Leaf => 0, Node(l, v, r) => add(size(l), add(v, size(r))) }\nfn solve(n: Int) -> Int = size(Node(Leaf, n, Leaf))\nentry solve\n";

/// 受理したプログラムを、入力の JSON で一度走らせ、(steps, allocated_nodes) を返す。
fn steps_and_allocs(src: &str, input: &str) -> (u64, u64) {
    let program = match compile(src.as_bytes(), &StaticProfile::default()) {
        SourceCompile::Result(CompileResult::Accepted { program, .. }) => program,
        _ => panic!("受理されない: {src}"),
    };
    let input = match tlvm::api::decode_input(
        &program.input_type,
        input.as_bytes(),
        &InputProfile::default(),
    ) {
        tlvm::DecodeResult::Decoded(tv) => tv,
        _ => panic!("入力"),
    };
    match tlvm::api::run(
        &program,
        &input,
        &ExecutionProfile::default(),
        &HostPolicy::default(),
    ) {
        Ok(tlvm::evaluator::RunResult::Completed {
            steps,
            allocated_nodes,
            ..
        }) => (steps, allocated_nodes),
        r => panic!("{src}: {r:?}"),
    }
}

#[test]
fn none_repeated_in_a_fold_allocates_nothing() {
    // §20.1 の対応表の行 31：none の反復評価は、none 由来の割当を作らない（§18.3 の割当は新規の整数・cons・pair・some だけ）。
    // fold の反復の step は、入力の cons の読取りと body の評価で、長さに比例する（一反復の増分は一定）。
    let src = "fn f(x: List<Int>) -> Option<Int> = fold(x, none<Int>(), |acc, item| none<Int>())\nentry f\n";
    let list = |n: usize| {
        let items: Vec<String> = (0..n)
            .map(|k| format!(r#"{{"tag":"int","value":"{k}"}}"#))
            .collect();
        format!(r#"{{"tag":"list","items":[{}]}}"#, items.join(","))
    };
    let (s0, a0) = steps_and_allocs(src, &list(0));
    let (s1, a1) = steps_and_allocs(src, &list(1));
    let (s3, a3) = steps_and_allocs(src, &list(3));
    assert_eq!((a0, a1, a3), (0, 0, 0));
    assert_eq!(s3 - s1, 2 * (s1 - s0));
}

#[test]
fn reference_events_of_a_recursive_program_are_fixed() {
    // 再帰する型の代表 program の Steps と AllocatedNodes。補助関数の本体を含む書換えの形で決まるので、形を
    // recursive_helper_shapes_match_the_deltas で固定したうえで、処理系の出力を固定する。手計算ではない
    // （§18.3 の規則の手計算は、上の P1〜P3 で照合した）。
    assert_eq!(
        steps_and_allocs(TREE_SIZE, r#"{"tag":"int","value":"3"}"#),
        (STEPS_TREE_SIZE, ALLOCS_TREE_SIZE)
    );
}

/// 型検査の仕事量と、論理 trace の名前の列（`CheckOptions` は比較 cache Off）。
fn check_of(px: &tlvm::syntax::Program, len: usize) -> (Vec<&'static str>, u64) {
    let (mut o, _) = check_with(
        px,
        len,
        &StaticProfile::default(),
        &CheckOptions {
            sharing: TypeSharing::Off,
            trace: false,
        },
    );
    (
        o.diagnostics.iter().map(|d| d.code).collect(),
        total(o.work.take()),
    )
}

/// 宣言が再帰する型だけのプログラムの、印つきの写しと印なしの写し（名義の型の印は `recursive::expand` が付ける）。
fn tagged_and_untagged(src: &str) -> (tlvm::syntax::Program, tlvm::syntax::Program) {
    let p = match parse_source(src.as_bytes(), &StaticProfile::default()) {
        Parsed::Program(p) => p,
        Parsed::Failed(_) => panic!("解析できない: {src}"),
    };
    let tagged = tlvm::recursive::expand(&p, Some(&tlvm::nominal::Tags::of(&p)));
    let untagged = expand(&p);
    (
        tagged.unwrap_or_else(|_| panic!("展開できない: {src}")),
        untagged.unwrap_or_else(|_| panic!("展開できない: {src}")),
    )
}

#[test]
fn tagged_copy_is_reported_only_when_rejected() {
    // §18.1c の規則 T（v1.15）：受理のときは印なしの写しの仕事量、拒否のときは印つきの写しの仕事量を報告する。
    // 印つきと印なしの trace は一致しない（O-3 の答え）。印つきは、印の型 Pair<Pair<Unit, Unit>, List<Int>> と
    // tree_flat の呼出しの分だけ多い。下の数は処理系の出力を固定したもので、手計算ではない。
    let (tagged, untagged) = tagged_and_untagged(TREE_SIZE);
    let (tcodes, tw) = check_of(&tagged, TREE_SIZE.len());
    let (ucodes, uw) = check_of(&untagged, TREE_SIZE.len());
    assert!(tcodes.is_empty() && ucodes.is_empty());
    assert_eq!((tw, uw), (472, 356));
    assert_ne!(
        trace_of(&tagged, TREE_SIZE.len()),
        trace_of(&untagged, TREE_SIZE.len())
    );
    // 受理：印なしの写しの仕事量を報告する。
    assert_eq!(outcome(TREE_SIZE, &sp(2_000_000)), (true, uw, vec![]));
    // 拒否：List<Int> の値を Tree の位置へ渡す。印なしの写しは受理し、印つきの写しだけが拒否する。
    // 報告は印つきの写しの、拒否までの仕事量。
    let rej = "type Tree = Leaf | Node(Tree, Int, Tree)\nrec fn size(t: Tree) -> Int = match t { Leaf => 0, Node(l, v, r) => add(size(l), add(v, size(r))) }\nfn solve(xs: List<Int>) -> Int = size(xs)\nentry solve\n";
    let (rejected, untagged_rej) = tagged_and_untagged(rej);
    assert_eq!(check_of(&untagged_rej, rej.len()).0, Vec::<&str>::new());
    let (rcodes, rw) = check_of(&rejected, rej.len());
    assert_eq!(rcodes, ["E-TYPE-ARG"]);
    assert_eq!(
        outcome(rej, &sp(2_000_000)),
        (false, rw, vec!["E-TYPE-ARG"])
    );
    assert_eq!(rw, 426);
}
