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
    // 比較 cache の On と、それに正準化を加えた Interned で、論理 trace と仕事量が Off と同じ（規則 G の数えない
    // 関数も cache の記録に入る）
    for (src, _, _) in FIFTEEN {
        let src = format!("{src}\nentry f");
        let off = trace(&src, TypeSharing::Off);
        assert_eq!(off, trace(&src, TypeSharing::On), "{src}");
        assert_eq!(off, trace(&src, TypeSharing::Interned), "{src}");
    }
}

/// 総称の二つのパス（`check_with`）の受理・仕事量・診断の code。`sharing` の方式で検査する。
fn two_pass(src: &str, sharing: TypeSharing, semantic_work: u64) -> (bool, u64, Vec<&'static str>) {
    let profile = sp(semantic_work);
    let p = match parse_source(src.as_bytes(), &profile) {
        Parsed::Program(p) => p,
        Parsed::Failed(_) => panic!("解析できない: {src}"),
    };
    let px = expand(&p).unwrap_or_else(|_| panic!("展開できない: {src}"));
    let opts = CheckOptions {
        sharing,
        trace: false,
    };
    let (o, _) = check_with(&px, src.len(), &profile, &opts);
    let codes = o.diagnostics.iter().map(|d| d.code).collect();
    (o.typed.is_some(), total(o.work), codes)
}

#[test]
fn interned_keeps_the_generic_cutoffs_of_both_passes() {
    // §18.1c の境界（第一パスと複製の和）の fixture を、正準化の有無で比べる
    let src = "fn id<T>(x: T) -> T = x\nfn f(x: Int) -> Int = id(x)\nentry f";
    for work in [10, 9, 8, 7, 3, 0] {
        let off = two_pass(src, TypeSharing::Off, work);
        assert_eq!(off, two_pass(src, TypeSharing::On, work), "{work}");
        assert_eq!(off, two_pass(src, TypeSharing::Interned, work), "{work}");
    }
    assert!(two_pass(src, TypeSharing::Interned, 10).0);
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
    // P4（min）・P5（max）：P2 と同じ形。選んだ引数の値を返しても、結果の整数を新しい node として一つ確保する（§18.3 の規則 7）。計 7、割当 2。
    let cases = [
        ("fn f(x: Int) -> Int = x\nentry f", 2, 0),
        ("fn f(x: Int) -> Int = add(x, 1)\nentry f", 7, 2),
        ("fn f(x: Int) -> Int = add(add(x, 1), 2)\nentry f", 12, 4),
        ("fn f(x: Int) -> Int = min(x, 1)\nentry f", 7, 2),
        ("fn f(x: Int) -> Int = max(x, 1)\nentry f", 7, 2),
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

// 書換えの族ごとの Steps と AllocatedNodes。§18.3 の参照イベント（式 node の評価開始、関数本体への入場、組込みの
// 適用開始、spine の読取り（cons と末尾の nil）、list の push と pop、eq の比較、新規の整数・cons・pair・some の
// 割当。割当は一つで step も一つ）と v1.1 差分 §7（match_option は node の 1 step だけ）を、書換え後の木に当てて
// 手で数えた。書換え後の形は hof.rs・dict.rs（v1.9 差分 §2）・sums.rs・records.rs・recursive.rs のもの。
// 下の注釈で「node」は式 node の評価開始、「組込み」は組込みの適用開始、「読取り」は spine の読取り。

const INT5: &str = r#"{"tag":"int","value":"5"}"#;

/// 整数のリストの値 JSON。
fn int_list(xs: &[i64]) -> String {
    let items: Vec<String> = xs
        .iter()
        .map(|k| format!(r#"{{"tag":"int","value":"{k}"}}"#))
        .collect();
    format!(r#"{{"tag":"list","items":[{}]}}"#, items.join(","))
}

#[test]
fn reference_events_of_function_taking_builtins_are_fixed() {
    // 値はすべて手計算（処理系の出力を写したものではない）。
    // map、入力 [5, 7]。書換え後 reverse(fold(x, list<Int>(), |acc, y| cons(add(y, 1), acc)))
    //   入場 1、node 4（reverse、fold、x、list）、fold の nil の読取り 1
    //   反復 2 回 × 11：読取り 1、node 5（cons、add、y、1、acc）、組込み 2（add、cons）、割当 3（1、和、cons）
    //   reverse：組込み 1、セル 2 個の読取りと割当 4、nil の読取り 1 → 計 34 step、割当 8
    let map = "fn f(x: List<Int>) -> List<Int> = map(x, |y| add(y, 1))\nentry f\n";
    assert_eq!(steps_and_allocs(map, &int_list(&[5, 7])), (34, 8));
    // filter、入力 [1, 3]。書換え後 reverse(fold(x, list<Int>(), |acc, y| if(lt(y, 2), cons(y, acc), acc)))
    //   入場 1、node 4、nil の読取り 1
    //   y = 1：読取り 1、node 4（if、lt、y、2）、2 の割当 1、lt 1、cons(y, acc) の node 3・組込み 1・割当 1 → 12
    //   y = 3：読取り 1、node 4、割当 1、lt 1、acc の node 1 → 8
    //   reverse：組込み 1、セル 1 個の読取りと割当 2、nil の読取り 1 → 計 30 step、割当 4
    let filter = "fn f(x: List<Int>) -> List<Int> = filter(x, |y| lt(y, 2))\nentry f\n";
    assert_eq!(steps_and_allocs(filter, &int_list(&[1, 3])), (30, 4));
    // any、入力 [1, 3]。書換え後 fold(x, false, |acc, y| if(acc, true, lt(y, 2)))
    //   入場 1、node 3（fold、x、false）、nil の読取り 1
    //   y = 1：読取り 1、node 5（if、acc、lt、y、2）、2 の割当 1、lt 1 → 8 ／ y = 3：読取り 1、node 3（if、acc、true）→ 4
    //   計 17 step、割当 1
    let any = "fn f(x: List<Int>) -> Bool = any(x, |y| lt(y, 2))\nentry f\n";
    assert_eq!(steps_and_allocs(any, &int_list(&[1, 3])), (17, 1));
    // all、入力 [3, 1]。書換え後 fold(x, true, |acc, y| if(acc, lt(y, 2), false))
    //   入場 1、node 3（fold、x、true）、nil の読取り 1
    //   y = 3：読取り 1、node 5、割当 1、lt 1 → 8 ／ y = 1：読取り 1、node 3（if、acc、false）→ 4
    //   計 17 step、割当 1
    let all = "fn f(x: List<Int>) -> Bool = all(x, |y| lt(y, 2))\nentry f\n";
    assert_eq!(steps_and_allocs(all, &int_list(&[3, 1])), (17, 1));
    // find、入力 [3, 1, 0]。書換え後
    // fold(x, none<Int>(), |acc, y| match_option(acc, if(lt(y, 2), some(y), none<Int>()), |z| some(z)))
    //   入場 1、node 3（fold、x、none）、nil の読取り 1
    //   y = 3：読取り 1、node 7（match_option、acc、if、lt、y、2、none）、割当 1、lt 1 → 10
    //   y = 1：読取り 1、node 8（…、some、y）、割当 2（2、some）、lt 1 → 12
    //   y = 0：読取り 1、node 4（match_option、acc、some、z）、some の割当 1 → 6
    //   計 33 step、割当 4
    let find = "fn f(x: List<Int>) -> Option<Int> = find(x, |y| lt(y, 2))\nentry f\n";
    assert_eq!(steps_and_allocs(find, &int_list(&[3, 1, 0])), (33, 4));
    // sort_by、入力 [2, 1]（hof.rs の安定な挿入整列。e は外側の要素、st は内側の fold の状態）
    //   入場 1、外側の node 3（fold、x、list）、外側の nil の読取り 1
    //   外側の反復ごと：読取り 1、let の node 1、内側の fold の node 1、cons(e, acc) 5（割当 1）、
    //     init pair(none, pair(list, false)) 7（割当 2）、内側の nil の読取り 1
    //   内側の本体：鍵を決める最初の要素 22（node 16、組込み 4、割当 2：some、pair）、
    //     比べて e を入れる要素 40（node 27、組込み 9、割当 4：cons 2、pair 2）
    //   終わりの reverse(if(snd(snd(r)), fst(snd(r)), cons(e, fst(snd(r)))))：
    //     e を入れていないとき 20（cons とセル 1 個で割当 2）、入れたとき 18（セル 2 個で割当 2）
    //   e = 2：1 + 1 + (1 + 5 + 7 + 23 + 1) + 20 = 59（割当 7）
    //   e = 1：1 + 1 + (1 + 5 + 7 + 23 + 41 + 1) + 18 = 98（割当 11）
    //   計 162 step、割当 18
    let sort_by = "fn f(x: List<Int>) -> List<Int> = sort_by(x, |y| y)\nentry f\n";
    assert_eq!(steps_and_allocs(sort_by, &int_list(&[2, 1])), (162, 18));
}

#[test]
fn reference_events_of_dict_operations_are_fixed() {
    // 手計算。dict_get(dict_put(dict<Int, Int>(), 1, x), 1)、入力 5。書換え後（v1.9 差分 §2 の形）
    // let d = (let dd = list<Pair<Int, Int>>() in let kk = 1 in let vv = x in
    //          let r = fold(dd, pair(list<Pair<Int, Int>>(), false), …) in
    //          reverse(if(snd(r), fst(r), cons(pair(kk, vv), fst(r)))))
    // in let k = 1 in fold(d, none<Int>(), |acc, e| if(eq(fst(e), k), some(snd(e)), acc))
    //   入場 1、let d の node 1
    //   dict_put 34：let 4 個の node 4、list・1・x の node 3 と 1 の割当 1、空の fold 7（fold・dd の node 2、
    //     init 4（node 3、割当 1）、nil の読取り 1）、reverse(if(…)) 19（node 10、組込み 4：snd・fst・cons・reverse、
    //     セル 1 個と nil の読取り 2、割当 3：pair、cons、reverse のセル）
    //   dict_get 21：let k と 1 の node 2・割当 1、fold・d・none の node 3、nil の読取り 1、
    //     反復 1 回 14（読取り 1、node 8：if・eq・fst・e・k・some・snd・e、組込み 3：fst・eq・snd、eq の比較 1、some の割当 1）
    //   計 57 step、割当 7
    let src =
        "fn f(x: Int) -> Option<Int> = dict_get(dict_put(dict<Int, Int>(), 1, x), 1)\nentry f\n";
    assert_eq!(steps_and_allocs(src, INT5), (57, 7));
}

#[test]
fn reference_events_of_loop_are_fixed() {
    // 書換え後の形は hof.rs の loop（16 段の fold。段 1 は if(lt(16^15, m), rg, one)、段 2〜15 は
    // if(lt(fst(a), m), if(lt(W, sub(m, fst(a))), rg, one), nil)、一番内側は min(16, …) 歩の fold）。
    // k は ok／err の構築の回数。§18.3 の規則 7 と v1.4 差分は ok／err の割当を書いていない。ここでは some と同じく
    // 一つの node の確保（step 1、割当 1）と読む。この読みのほかは手計算である。
    //
    // max = 0、本体 none<Int>()、入力 5（本体を評価しない。段 2 は nil を辿る）。k = 1（init の ok(x)）
    //   入場 1、let 4 個の node 4、m の 0 の node 1 と割当 1
    //   range(0, 16) 38（node 3、割当 2、組込み 1、要素の整数と cons の割当 32）、range(0, 1) 8、list<Int>() の node 1
    //   match_result・snd・fold の node 3、snd の組込み 1、ok 枝の none の node 1
    //   段 1：list 7（node 5、2^60 の割当 1、lt 1）、init pair(0, ok(x)) 6 + k（node 4、0 と pair の割当 2）、
    //     反復 1 回 12（読取り 1、段 2 の fold の node 1、list の node 6 と組込み 2、init の node 1、nil の読取り 1）、
    //     nil の読取り 1
    //   計 85 + k step、割当 42 + k
    let k = 1;
    let max0 = "fn f(x: Int) -> Option<Int> = loop(x, 0, |s| none<Int>())\nentry f\n";
    assert_eq!(steps_and_allocs(max0, INT5), (85 + k, 42 + k));
    // 本体を評価する loop（max >= 1）は固定していない。一番内側の min(16, …) の結果の整数を、§8.4 は新しい node と
    // 数え、評価器は引数の node を返して数えないので、手計算と処理系の出力が一つずつ違う。
}

#[test]
fn reference_events_of_matches_are_fixed() {
    // 手計算。match の書換え（sums.rs）は match_result・match_option と let の入れ子。match_result も
    // match_option と同じく node の 1 step だけを数える（§18.3 の規則 1。binder の設定は step ではない）。
    // 直和型の match（変種 3）。書換え後 match_result(t, |a| a, |s1| match_result(s1, |b| 0, |s2| let c = s2 in c))
    //   C(7) = err(err(7))：入場 1、node 7（match_result、t、match_result、s1、let、s2、c）→ 8 step、割当 0
    //   B(true) = err(ok(true))：入場 1、node 5（match_result、t、match_result、s1、0）、0 の割当 1 → 7 step、割当 1
    let sum = "type T = A(Int) | B(Bool) | C(Int)\nfn f(t: T) -> Int = match t { A(a) => a, B(b) => 0, C(c) => c }\nentry f\n";
    assert_eq!(
        steps_and_allocs(
            sum,
            r#"{"tag":"err","value":{"tag":"err","value":{"tag":"int","value":"7"}}}"#
        ),
        (8, 0)
    );
    assert_eq!(
        steps_and_allocs(
            sum,
            r#"{"tag":"err","value":{"tag":"ok","value":{"tag":"bool","value":true}}}"#
        ),
        (7, 1)
    );
    // Option の match。書換え後 match_option(o, 0, |v| v)
    //   some(5)：入場 1、node 3（match_option、o、v）→ 4 step、割当 0
    //   none：入場 1、node 3（match_option、o、0）、0 の割当 1 → 5 step、割当 1
    let opt = "fn f(o: Option<Int>) -> Int = match o { some(v) => v, none => 0 }\nentry f\n";
    assert_eq!(
        steps_and_allocs(opt, r#"{"tag":"some","value":{"tag":"int","value":"5"}}"#),
        (4, 0)
    );
    assert_eq!(steps_and_allocs(opt, r#"{"tag":"none"}"#), (5, 1));
    // Result の match。書換え後 match_result(r, |v| v, |e| 0)
    //   ok(5)：入場 1、node 3（match_result、r、v）→ 4 step、割当 0
    //   err(true)：入場 1、node 3（match_result、r、0）、0 の割当 1 → 5 step、割当 1
    let res = "fn f(r: Result<Int, Bool>) -> Int = match r { ok(v) => v, err(e) => 0 }\nentry f\n";
    assert_eq!(
        steps_and_allocs(res, r#"{"tag":"ok","value":{"tag":"int","value":"5"}}"#),
        (4, 0)
    );
    assert_eq!(
        steps_and_allocs(res, r#"{"tag":"err","value":{"tag":"bool","value":true}}"#),
        (5, 1)
    );
}

#[test]
fn reference_events_of_sum_construction_are_fixed() {
    // 直和型の構築は ok／err の入れ子。B(true) は err<Int, Result<Bool, Int>>(ok<Bool, Int>(true))。
    // k は ok／err の構築の回数（2）。§18.3 は ok／err の割当を書いていないので、loop と同じく some と同じ読み
    // （step 1、割当 1）で数えた。そのほかは手計算：入場 1、node 3（err、ok、true）→ 4 + k step、割当 0 + k
    let k = 2;
    let src = "type T = A(Int) | B(Bool) | C(Int)\nfn f(x: Int) -> T = B(true)\nentry f\n";
    assert_eq!(steps_and_allocs(src, INT5), (4 + k, k));
}

#[test]
fn reference_events_of_records_are_fixed() {
    // 手計算。レコードの構築は pair の入れ子、参照は fst／snd（records.rs）。
    // 書換え後 let p = pair(n, true) in fst(p)
    //   入場 1、node 6（let、pair、n、true、fst、p）、pair の割当 1、fst の組込み 1 → 9 step、割当 1
    let two = "type P = { x: Int, y: Bool }\nfn f(n: Int) -> Int = let p = P { x: n, y: true } in p.x\nentry f\n";
    assert_eq!(steps_and_allocs(two, INT5), (9, 1));
    // 書換え後 let q = pair(n, pair(true, 2)) in snd(snd(q))
    //   入場 1、node 9（let、pair、n、pair、true、2、snd、snd、q）、割当 3（2、内側の pair、外側の pair）、
    //   snd の組込み 2 → 15 step、割当 3
    let three = "type Q = { a: Int, b: Bool, c: Int }\nfn f(n: Int) -> Int = let q = Q { a: n, b: true, c: 2 } in q.c\nentry f\n";
    assert_eq!(steps_and_allocs(three, INT5), (15, 3));
}

#[test]
fn reference_events_of_recursive_helpers_are_fixed() {
    // 手計算。再帰する型 Chain = End | Link(Chain) の値は整数の列（recursive.rs）。補助関数の全文は
    // recursive.rs の recursive_helper_shapes_match_the_deltas で固定した形と同じもの。
    // 構築 Link(End)：書換え後 link_new(list<Int>(0))、
    // link_new(a) = concat(list<Int>(1), concat(list<Int>(length(a)), a))、結果 [1, 1, 0]
    //   入場 1、呼出しの node 1、list<Int>(0) 6（node 2、push 1、pop 1、割当 2：0 と cons）
    //   link_new 32：入場 1、concat の node 2、list<Int>(1) 6（割当 2）、list<Int>(length(a)) 10（length 6：node 2、
    //     組込み 1、読取り 2、割当 1。list の node 1、push 1、pop 1、割当 1）、a の node 1、concat 2 回 × 6（組込み 1、
    //     セル 1 個の読取りと push 2、nil の読取り 1、pop と割当 2）
    //   計 40 step、割当 8
    let build = "type Chain = End | Link(Chain)\nfn f(x: Int) -> Chain = Link(End)\nentry f\n";
    assert_eq!(steps_and_allocs(build, INT5), (40, 8));
    // match。書換え後 let scrut = link_new(list<Int>(0)) in let tag = rec_at(scrut, 0) in
    // if(eq(tag, 0), 0, let rest = rec_drop(scrut, 1) in let len = rec_at(rest, 0) in
    //   let data = rec_take(rec_drop(rest, 1), len) in let c = data in 1)
    // 補助関数の手間（呼出しの node と引数を除き、入場を含む。L は列の長さ）：
    //   rec_drop(xs, n) = 14 + 21 × 落とす個数 + 22 × 残す個数、割当 2 + 3L
    //   rec_take(xs, n) = 14 + 27 × 取る個数 + 9 × 残りの個数、割当 2 + 5 × 取る個数
    //   rec_at(xs, i) = 11 + rec_drop(xs, i) + rec_take(·, 1) + 2 × 取った個数、割当 2 + 両方の割当
    //   入場 1、let 2 個の node 2、scrut の値 39（割当 8）
    //   rec_at(scrut, 0) 156：node 2、0 の割当込み 2、rec_at 152（rec_drop 80、rec_take 59）、割当 21
    //   if 1、eq(tag, 0) 6（node 3、0 の割当 1、組込み 1、比較 1）→ 偽
    //   else 319：let 4 個の node 4、rec_drop(scrut, 1) 83（割当 12）、rec_at(rest, 0) 125（割当 18）、
    //     rec_take(rec_drop(rest, 1), len) 104（割当 16）、data の node 1、1 の node と割当 2
    //   計 524 step、割当 77
    let matched = "type Chain = End | Link(Chain)\nfn f(x: Int) -> Int = match Link(End) { End => 0, Link(c) => 1 }\nentry f\n";
    assert_eq!(steps_and_allocs(matched, INT5), (524, 77));
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
