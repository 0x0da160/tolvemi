//! §18.1：書換え後のプログラムの大きさの上限（`E-LIMIT-STATIC-REWRITTEN-BYTES`）。型検査を通ったプログラムの、
//! 検証済み部品へ渡す文字列の bytes が上限を超えれば拒否する。境界は、観測値が上限以下なら通過する。

use tlvm::api::{
    compile, compile_ast, parse_source, AstCompile, CompileResult, Parsed, SourceCompile,
};
use tlvm::formatter::encode_ast;
use tlvm::profiles::{AstTransportProfile, StaticProfile};

const CODE: &str = "E-LIMIT-STATIC-REWRITTEN-BYTES";
const LOOP: &str = "fn f(x: Int) -> Option<Int> = loop(x, 3, |s| none<Int>())\nentry f";

fn sp(rewritten_bytes: usize) -> StaticProfile {
    StaticProfile {
        rewritten_bytes,
        ..StaticProfile::default()
    }
}

/// 受理したか、拒否したときの診断の code、上限の超過の診断の act（書換え後の bytes）。
fn outcome(src: &str, profile: &StaticProfile) -> (bool, Vec<&'static str>, Option<String>) {
    match compile(src.as_bytes(), profile) {
        SourceCompile::Result(CompileResult::Accepted { .. }) => (true, vec![], None),
        SourceCompile::Result(CompileResult::Rejected { errors, .. }) => {
            let act = errors
                .iter()
                .find(|d| d.code == CODE)
                .and_then(|d| d.actual.clone());
            (false, errors.iter().map(|d| d.code).collect(), act)
        }
        _ => panic!("結果が出ない: {src}"),
    }
}

/// `outcome` の AST の入口版。
fn ast_outcome(json: &str, profile: &StaticProfile) -> (bool, Vec<&'static str>, Option<String>) {
    match compile_ast(json.as_bytes(), profile, &AstTransportProfile::default()) {
        AstCompile::Result(CompileResult::Accepted { .. }) => (true, vec![], None),
        AstCompile::Result(CompileResult::Rejected { errors, .. }) => {
            let act = errors
                .iter()
                .find(|d| d.code == CODE)
                .and_then(|d| d.actual.clone());
            (false, errors.iter().map(|d| d.code).collect(), act)
        }
        _ => panic!("AST の検査が結果を返さない"),
    }
}

/// 関数を `functions` 個並べ、それぞれに loop を四つ置く。書換え後は loop 一つあたり約 2.7 KB になる。
fn many_loops(functions: usize) -> String {
    let t = "match_option(loop(x, 3, |s| none<Int>()), 0, |v| v)";
    let mut src = String::new();
    for k in 0..functions {
        src.push_str(&format!(
            "fn g{k}(x: Int) -> Int = add(add({t}, {t}), add({t}, {t}))\n"
        ));
    }
    src.push_str("entry g0\n");
    src
}

#[test]
fn rewritten_size_is_checked_at_its_exact_boundary() {
    // 上限 0 で拒否すると、上限の超過の診断の act に書換え後の bytes が出る。
    let (ok, codes, act) = outcome(LOOP, &sp(0));
    assert!(!ok);
    assert_eq!(codes, [CODE]);
    let size: usize = act.expect("act は書換え後の bytes").parse().unwrap();
    assert!(size > 0);
    // 観測値以下なら通過し、一つ下の上限では拒否する（act は同じ大きさ）。
    assert!(outcome(LOOP, &sp(size)).0);
    assert_eq!(
        outcome(LOOP, &sp(size - 1)),
        (false, vec![CODE], Some(size.to_string()))
    );
}

#[test]
fn programs_rejected_by_the_typecheck_are_not_measured() {
    // 型検査で拒否したプログラムは書換えが途中までなので、大きさを測らない。
    let src = "fn f(x: Int) -> Option<Int> = loop(x, true, |s| none<Int>())\nentry f";
    assert_eq!(outcome(src, &sp(0)), (false, vec!["E-TYPE-LOOP-MAX"], None));
}

#[test]
fn rewritten_size_is_checked_on_the_ast_path() {
    let program = match parse_source(LOOP.as_bytes(), &StaticProfile::default()) {
        Parsed::Program(p) => p,
        Parsed::Failed(_) => panic!("解析できない"),
    };
    let json = encode_ast(&program).unwrap();
    let (ok, codes, act) = ast_outcome(&json, &sp(0));
    assert!(!ok);
    assert_eq!(codes, [CODE]);
    let size: usize = act.expect("act は書換え後の bytes").parse().unwrap();
    assert!(ast_outcome(&json, &sp(size)).0);
    assert_eq!(
        ast_outcome(&json, &sp(size - 1)),
        (false, vec![CODE], Some(size.to_string()))
    );
}

#[test]
fn default_limit_is_four_mebibytes() {
    // 既定の上限は spec §18.1 の表の値（4 MiB）。
    assert_eq!(StaticProfile::default().rewritten_bytes, 4_194_304);
    // 小さなものは既定の上限の内に入る。
    assert!(outcome(&many_loops(2), &StaticProfile::default()).0);
}

#[test]
fn default_limit_rejects_a_large_rewrite() {
    // loop を 1600 個（書換え後は約 4.4 MB）並べた program は、既定の上限で検証済み部品に渡る前に拒否する。
    let (ok, codes, act) = outcome(&many_loops(400), &StaticProfile::default());
    assert!(!ok);
    assert_eq!(codes, [CODE]);
    let size: usize = act.expect("act は書換え後の bytes").parse().unwrap();
    assert!(size > 4_194_304);
}

/// `loop` を `n` 段入れ子にした program（最も内側は `none`）。
fn nested_loops(n: usize) -> String {
    let mut e = "none<Int>()".to_string();
    for k in 1..=n {
        e = format!("loop(x, 2, |s{k}| {e})");
    }
    format!("fn f(x: Int) -> Option<Int> = {e}\nentry f\n")
}

#[test]
fn rewritten_expression_depth_is_checked_after_lowering() {
    // 20 段の入れ子は、原文の式の深さは上限（256）の内だが、書換えの後の式の深さが超えて拒否する（§18.1c の O-1）。
    let src = nested_loops(20);
    assert!(
        matches!(
            parse_source(src.as_bytes(), &StaticProfile::default()),
            Parsed::Program(_)
        ),
        "原文は上限の内"
    );
    match compile(src.as_bytes(), &StaticProfile::default()) {
        SourceCompile::Result(CompileResult::Rejected { errors, .. }) => {
            let d = errors
                .iter()
                .find(|d| d.code == "E-LIMIT-STATIC-EXPR-DEPTH")
                .expect("式の深さの診断");
            let need: usize = d
                .actual
                .as_ref()
                .expect("act は書換え後の深さ")
                .parse()
                .unwrap();
            assert!(need > 256, "書換え後の深さ {need}");
        }
        _ => panic!("拒否されない: {src}"),
    }
    // 十段なら書換えの後の深さも上限の内で受理する。
    assert!(outcome(&nested_loops(10), &StaticProfile::default()).0);
}
