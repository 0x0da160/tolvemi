//! v1.15 の名義の型（差分仕様 `spec/lptl-v1.15`）：宣言した型は、展開後の構造が同じでも型の名前で区別する。
//! 混ぜると型検査で拒否され、文面は型の名前で出る。構造だけの値（`pair`）は名義の型にならない。総称の型の
//! 型引数の違いは別の型。印の付いた写しの検査のあとも、実行の結果は従来どおり。

use std::process::Command;
use tlvm::api::*;
use tlvm::profiles::*;
use tlvm_verified::pipeline::{compile_source, Compiled};

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

fn with_file<T>(src: &str, ext: &str, f: impl FnOnce(&str) -> T) -> T {
    static N: std::sync::atomic::AtomicUsize = std::sync::atomic::AtomicUsize::new(0);
    let n = N.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
    let path = std::env::temp_dir().join(format!("tlvm-nom-{}-{n}.{ext}", std::process::id()));
    std::fs::write(&path, src).unwrap();
    let r = f(path.to_str().unwrap());
    std::fs::remove_file(&path).unwrap();
    r
}

/// plain JSON の入力で実行した出力（終了コードは 0 であること）。
fn run(src: &str, input: &str) -> String {
    with_file(src, "tlvm", |p| {
        let (code, out, err) = tlvm(&["run", p, input, "--plain"]);
        assert_eq!(code, 0, "{err}");
        out.trim_end().to_string()
    })
}

fn compiled(src: &str) -> CompileResult {
    match compile(src.as_bytes(), &StaticProfile::default()) {
        SourceCompile::Result(r) => r,
        _ => panic!("boundary"),
    }
}

fn codes(src: &str) -> Vec<&'static str> {
    compiled(src).errors().iter().map(|d| d.code).collect()
}

/// 最初の診断の（期待，実際）の型の文面。
fn expected_actual(src: &str) -> (String, String) {
    let r = compiled(src);
    let d = &r.errors()[0];
    (
        d.expected.clone().unwrap_or_default(),
        d.actual.clone().unwrap_or_default(),
    )
}

#[test]
fn records_with_the_same_shape_do_not_mix() {
    // 形が同じ（Int の field が一つ）でも、名前が違えば別の型
    let src = "type A = { x: Int }\ntype B = { z: Int }\nfn f(a: A) -> Int = a.x\nfn g(b: B) -> Int = f(b)\nentry g\n";
    assert_eq!(codes(src), ["E-TYPE-ARG"]);
    assert_eq!(expected_actual(src), ("A".to_string(), "B".to_string()));
}

#[test]
fn sums_with_the_same_shape_do_not_mix() {
    let src = "type Sa = P(Int) | Q\ntype Sb = R(Int) | T\nfn f(s: Sa) -> Int = match s { P(n) => n, Q => 0 }\nfn g(s: Sb) -> Int = f(s)\nentry g\n";
    assert_eq!(codes(src), ["E-TYPE-ARG"]);
    assert_eq!(expected_actual(src), ("Sa".to_string(), "Sb".to_string()));
}

#[test]
fn a_plain_result_is_not_a_named_sum() {
    let src = "type Opt = Has(Int) | Nothing\nfn f(x: Result<Int, Unit>) -> Opt = x\nentry f\n";
    assert_eq!(codes(src), ["E-TYPE-RETURN"]);
    assert_eq!(
        expected_actual(src),
        ("Opt".to_string(), "Result<Int, Unit>".to_string())
    );
}

#[test]
fn a_raw_pair_is_not_a_record() {
    // `pair` は構造だけの値。レコードの型には、構築（`Box { ... }`）で作った値だけが合う
    let src = "type Box = { v: Int, n: Int }\nfn f(b: Box) -> Int = b.v\nfn g(x: Int) -> Int = f(pair(x, 2))\nentry g\n";
    assert_eq!(codes(src), ["E-TYPE-ARG"]);
    assert_eq!(
        expected_actual(src),
        ("Box".to_string(), "Pair<Int, Int>".to_string())
    );
}

#[test]
fn hand_made_tag_shape_is_rejected_when_run() {
    // 印の形を手で書いた値は、印つきの写しを通っても印なしの写しで拒否される（文面は構造で出る）
    let src = "type Box = { v: Int, n: Int }\nfn f(b: Box) -> Int = b.v\nfn g(x: Int) -> Int = f(pair(pair(unit, unit), pair(x, 2)))\nentry g\n";
    assert_eq!(codes(src), ["E-TYPE-ARG"]);
    // S5b（V9）：検証済みの二つの写し。印つきは受理し、印なしは型検査で拒否する（拒否するのは印なしの写し）。
    // 信頼側のゲートが先に拒否するので、この値は経路の判定まで届かない。rank は f（葉）が 0、g（f を呼ぶ）が 1。
    let p = StaticProfile::default();
    let (d, td) = (
        p.expr_depth,
        p.type_depth.saturating_mul(2).saturating_add(2),
    );
    let chars: Vec<char> = src.chars().collect();
    let (rank, rec) = (vec![0, 1], vec![false, false]);
    assert!(
        matches!(
            compile_source(&chars, d, td, rank.clone(), rec.clone(), true),
            Compiled::Accepted(_)
        ),
        "印つきの写しが受理しない"
    );
    assert!(
        matches!(
            compile_source(&chars, d, td, rank, rec, false),
            Compiled::NotWellFormed
        ),
        "印なしの写しが拒否しない"
    );
}

#[test]
fn three_same_shape_types_do_not_mix() {
    // 字段一つの Int の型三つ（A、B、C）。字段の名前は a、b、c で別（同じ名前だと字段の衝突で別の符号になる）。
    const DECLS: &str = "type A = { a: Int }\ntype B = { b: Int }\ntype C = { c: Int }\n";
    let cases = [
        (
            "fn fa(v: A) -> Int = v.a\nfn fb(v: B) -> Int = fa(v)\nentry fb\n",
            "A",
            "B",
        ),
        (
            "fn fa(v: A) -> Int = v.a\nfn fc(v: C) -> Int = fa(v)\nentry fc\n",
            "A",
            "C",
        ),
        (
            "fn fb(v: B) -> Int = v.b\nfn fc(v: C) -> Int = fb(v)\nentry fc\n",
            "B",
            "C",
        ),
    ];
    for (body, want, got) in cases {
        let src = format!("{DECLS}{body}");
        assert_eq!(codes(&src), ["E-TYPE-ARG"], "{src}");
        assert_eq!(
            expected_actual(&src),
            (want.to_string(), got.to_string()),
            "{src}"
        );
    }
}

#[test]
fn three_same_shape_types_each_run_with_their_own_field() {
    // 三つの型を一つの関数で使う形は受理し、同じ入力（5）から 5 + 5 + 5 = 15 を返す
    let src = "type A = { a: Int }\ntype B = { b: Int }\ntype C = { c: Int }\nfn fa(v: A) -> Int = v.a\nfn fb(v: B) -> Int = v.b\nfn fc(v: C) -> Int = v.c\nfn f(x: Int) -> Int = add(fa(A { a: x }), add(fb(B { b: x }), fc(C { c: x })))\nentry f\n";
    assert_eq!(run(src, "5"), "15");
}

#[test]
fn generic_instances_are_distinct_types() {
    let src = "type Box<T> = { v: T, n: Int }\nfn f(b: Box<Int>) -> Int = b.v\nfn g(b: Box<Bool>) -> Int = f(b)\nentry g\n";
    assert_eq!(codes(src), ["E-TYPE-ARG"]);
    assert_eq!(
        expected_actual(src),
        ("Box<Int>".to_string(), "Box<Bool>".to_string())
    );
}

#[test]
fn the_same_generic_instance_is_accepted_and_runs() {
    let src = "type Box<T> = { v: T, n: Int }\nfn f(b: Box<Int>) -> Int = add(b.v, b.n)\nfn g(x: Int) -> Int = f(Box { v: x, n: 2 })\nentry g\n";
    assert_eq!(run(src, "5"), "7");
}

#[test]
fn field_access_on_another_type_names_both() {
    let src = "type A = { x: Int }\ntype B = { z: Int }\nfn f(b: B) -> Int = b.z\nfn g(a: A) -> Int = f(a)\nentry g\n";
    assert_eq!(codes(src), ["E-TYPE-ARG"]);
    let src = "type Box = { v: Int, n: Int }\nfn f(x: Int) -> Int = x.v\nentry f\n";
    assert_eq!(codes(src), ["E-TYPE-FIELD-ACCESS"]);
    assert_eq!(expected_actual(src), ("Box".to_string(), "Int".to_string()));
}

#[test]
fn match_on_another_type_is_rejected_by_name() {
    let src = "type S = P(Int) | Q\nfn f(x: Int) -> Int = match x { P(n) => n, Q => 0 }\nentry f\n";
    assert_eq!(codes(src), ["E-TYPE-MATCH-SCRUTINEE"]);
    assert_eq!(expected_actual(src), ("S".to_string(), "Int".to_string()));
}

#[test]
fn record_update_and_sums_run_after_the_check() {
    let src = "type P = { a: Int, b: Int }\nfn f(p: P) -> P = P { a: p.b, ..p }\nfn g(x: Int) -> Int = f(P { a: x, b: 7 }).a\nentry g\n";
    assert_eq!(run(src, "3"), "7");
    let src = "type Shape = Circle(Int) | Rect(Int, Int) | Empty\nfn area(s: Shape) -> Int = match s { Circle(r) => mul(r, r), Rect(w, h) => mul(w, h), Empty => 0 }\nfn g(n: Int) -> Int = add(area(Rect(n, 3)), area(Circle(2)))\nentry g\n";
    assert_eq!(run(src, "4"), "16");
}

#[test]
fn a_record_inside_a_sum_keeps_both_names() {
    let src = "type R = { a: Int }\ntype S = W(R) | E\nfn f(s: S) -> Int = match s { W(r) => r.a, E => 0 }\nfn g(x: Int) -> Int = f(W(R { a: x }))\nentry g\n";
    assert_eq!(run(src, "9"), "9");
    let src = "type R = { a: Int }\ntype Q = { b: Int }\ntype S = W(R) | E\nfn f(s: S) -> Int = match s { W(r) => r.a, E => 0 }\nfn g(q: Q) -> Int = f(W(q))\nentry g\n";
    assert_eq!(codes(src), ["E-TYPE-ARG"]);
    assert_eq!(expected_actual(src), ("R".to_string(), "Q".to_string()));
}

#[test]
fn fst_and_snd_do_not_read_through_a_named_type() {
    // 名義の型は Pair の別名ではない（印の後ろの構造を fst・snd で取り出させない）。中身は `e.f` で取り出す
    let src = "type Box = { v: Int, n: Int }\nfn f(b: Box) -> Int = fst(b)\nentry f\n";
    assert_eq!(codes(src), ["E-TYPE-FST-ARG"]);
    assert_eq!(
        expected_actual(src),
        ("Pair".to_string(), "Box".to_string())
    );
    let src = "type Box = { v: Int, n: Int }\nfn f(b: Box) -> Int = snd(b)\nentry f\n";
    assert_eq!(codes(src), ["E-TYPE-SND-ARG"]);
    let src = "type Box = { v: Int, n: Int }\nfn f(b: Box) -> Int = b.v\nentry f\n";
    assert_eq!(run(src, "{\"v\": 4, \"n\": 0}"), "4");
}
