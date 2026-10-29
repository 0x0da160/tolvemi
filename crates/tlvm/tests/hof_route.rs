//! hof を含むプログラムの検証済みの経路（DECISION-43）。源を検証済みの構文器と解決器（hof を含む）で読み、表で書き換え、
//! 核のプログラムを検証済みの型検査器に通す。受理したプログラムは検証済みの IR を持つ（program.verified）。
//! 範囲内のプログラムが拒否されず、検証済みの IR を持ち、実行の出力が源どおりであることを確かめる。

use std::process::Command;
use tlvm::api::*;
use tlvm::profiles::*;

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
    let path =
        std::env::temp_dir().join(format!("tlvm-hof-route-{}-{n}.{ext}", std::process::id()));
    std::fs::write(&path, src).unwrap();
    let r = f(path.to_str().unwrap());
    std::fs::remove_file(&path).unwrap();
    r
}

/// plain JSON で実行した出力。
fn run(src: &str, input: &str) -> String {
    with_file(src, "tlvm", |p| {
        let (code, out, err) = tlvm(&["run", p, input, "--plain"]);
        assert_eq!(code, 0, "{err}");
        out.trim_end().to_string()
    })
}

/// 源を受理し、検証済みの IR を持つことを確かめて、そのプログラムの出力型を返す。
fn verified_output_type(src: &str) -> String {
    match compile(src.as_bytes(), &StaticProfile::default()) {
        SourceCompile::Result(CompileResult::Accepted { program, .. }) => {
            assert!(program.verified.is_some(), "no verified IR for:\n{src}");
            program.output_type.to_string()
        }
        SourceCompile::Result(r) => panic!("rejected: {:?}\n{src}", r.errors()),
        _ => panic!("boundary"),
    }
}

const SIX_FORMS: &str = "fn solve(xs: List<Int>) -> Pair<List<Int>, Pair<List<Int>, Pair<Bool, Pair<Bool, Pair<Option<Int>, List<Int>>>>>> =
  pair(map(xs, |x| mul(x, 2)),
  pair(filter(xs, |x| lt(0, x)),
  pair(any(xs, |x| eq(x, 3)),
  pair(all(xs, |x| lt(-10, x)),
  pair(find(xs, |x| lt(5, x)),
  sort_by(xs, |x| neg(x)))))))
entry solve
";

#[test]
fn six_forms_take_the_verified_route() {
    assert_eq!(
        verified_output_type(SIX_FORMS),
        "Pair<List<Int>, Pair<List<Int>, Pair<Bool, Pair<Bool, Pair<Option<Int>, List<Int>>>>>>"
    );
    assert_eq!(
        run(SIX_FORMS, "[3, -1, 7, 2, 9, 7]"),
        "[[6,-2,14,4,18,14],[[3,7,2,9,7],[true,[true,[7,[9,7,7,3,2,-1]]]]]]"
    );
}

#[test]
fn fold_over_a_map_runs_on_the_verified_route() {
    let src = "fn solve(xs: List<Int>) -> Int = fold(map(xs, |x| mul(x, 2)), 0, |a, x| add(a, x))
entry solve
";
    assert_eq!(verified_output_type(src), "Int");
    assert_eq!(run(src, "[1, 2, 3]"), "12");
}

#[test]
fn find_result_is_an_option() {
    let src = "fn solve(xs: List<Int>) -> Option<Int> = find(map(xs, |x| mul(x, 3)), |y| lt(10, y))
entry solve
";
    assert_eq!(verified_output_type(src), "Option<Int>");
    assert_eq!(run(src, "[1, 2, 5]"), "15");
    assert_eq!(run(src, "[1, 2]"), "null");
}

#[test]
fn hof_under_a_user_call_takes_the_verified_route() {
    let src = "fn twice(xs: List<Int>) -> List<Int> = map(xs, |x| mul(x, 2))
fn solve(xs: List<Int>) -> List<Int> = map(twice(xs), |y| add(y, 1))
entry solve
";
    assert_eq!(verified_output_type(src), "List<Int>");
    assert_eq!(run(src, "[1, 2]"), "[3,5]");
}

#[test]
fn let_binder_before_a_hof_keeps_the_numbering() {
    let src = "fn solve(xs: List<Int>) -> List<Int> = let k = 2 in map(xs, |x| mul(x, k))
entry solve
";
    assert_eq!(verified_output_type(src), "List<Int>");
    assert_eq!(run(src, "[1, 2]"), "[2,4]");
}

#[test]
fn hof_and_let_inside_a_fold_body() {
    // 各 x について、xs の各 z に x を足した列の和を、累積に足す。[1, 2] なら (1+1)+(2+1) と (1+2)+(2+2) の和。
    let src = "fn solve(xs: List<Int>) -> Int = fold(xs, 0, |a, x| let k = fold(map(xs, |z| add(z, x)), 0, |p, q| add(p, q)) in add(a, k))
entry solve
";
    assert_eq!(verified_output_type(src), "Int");
    assert_eq!(run(src, "[1, 2]"), "12");
}

#[test]
fn result_match_with_a_hof_in_the_success_branch() {
    let src = "fn solve(r: Result<List<Int>, Bool>) -> List<Int> = match r { ok(v) => map(v, |x| add(x, 1)), err(e) => list<Int>() }
entry solve
";
    assert_eq!(verified_output_type(src), "List<Int>");
}

#[test]
fn option_match_with_a_hof_in_the_some_branch() {
    let src = "fn solve(x: Option<List<Int>>) -> List<Int> = match_option(x, list<Int>(), |ys| map(ys, |y| mul(y, 3)))
entry solve
";
    assert_eq!(verified_output_type(src), "List<Int>");
}
