//! 値 JSON の入力（`tlvm run` と `tlvm test` の入力）の結果を固定する。
//!
//! 入力は検証済みの復号器が一度読み、その検査で受理した値をそのまま評価する（以前は評価の前にもう一度読んでいた）。
//! ここでは `api::run_input` の結果を、`decode_input` の後に `run` を呼ぶ経路（復号が二度走る）の結果と比べる。
//! 出力・step・割当・資源の上限・入力の診断・UTF-8 の境界が同じになることを確かめ、CLI の `run` と `test` の出力を固定する。
//! 復号の回数そのものは、この試験からは直接見えない。

use std::process::Command;

use tlvm::api::*;
use tlvm::checker::TypedProgram;
use tlvm::evaluator::RunResult;
use tlvm::profiles::*;

/// 整数のリストの合計。
const SUM: &str =
    "fn solve(xs: List<Int>) -> Int = fold(xs, 0, |acc, x| add(acc, x))\nentry solve\n";

/// 整数の入力をそのまま返す。
const ID: &str = "fn solve(n: Int) -> Int = n\nentry solve\n";

/// リストをそのまま返す（`tlvm test` の期待値との照合に使う）。
const ECHO: &str = "fn solve(xs: List<Int>) -> List<Int> = xs\nentry solve\n";

/// `[1, 2, -5]` の値 JSON（合計は -2）。
const LIST: &str = r#"{"tag":"list","items":[{"tag":"int","value":"1"},{"tag":"int","value":"2"},{"tag":"int","value":"-5"}]}"#;

fn accepted(src: &str) -> TypedProgram {
    match compile(src.as_bytes(), &StaticProfile::default()) {
        SourceCompile::Result(CompileResult::Accepted { program, .. }) => program,
        _ => panic!("受理されない: {src}"),
    }
}

/// 旧い経路：`decode_input` で読み、読んだ値を `run` で評価する。結果は `run_input` と同じ `InputOutcome` に写す。
fn decode_then_run(program: &TypedProgram, json: &[u8], p: &ExecutionProfile) -> InputOutcome {
    match decode_input(&program.input_type, json, &InputProfile::default()) {
        tlvm::DecodeResult::Decoded(tv) => {
            InputOutcome::Ran(run(program, &tv, p, &HostPolicy::default()).unwrap())
        }
        tlvm::DecodeResult::Invalid(d) => InputOutcome::Invalid(d),
        tlvm::DecodeResult::InputBoundaryFailure => InputOutcome::InputBoundaryFailure,
    }
}

/// `run_input` で実行し、旧い経路と結果が同じことを確かめて、その結果を返す。
fn same_outcome(src: &str, json: &[u8], p: &ExecutionProfile) -> InputOutcome {
    let program = accepted(src);
    let new = run_input(
        &program,
        json,
        false,
        &InputProfile::default(),
        p,
        &HostPolicy::default(),
    )
    .unwrap();
    assert_eq!(new, decode_then_run(&program, json, p), "{src}");
    new
}

#[test]
fn completed_run_matches_decode_then_run() {
    match same_outcome(SUM, LIST.as_bytes(), &ExecutionProfile::default()) {
        InputOutcome::Ran(RunResult::Completed { output, .. }) => {
            assert_eq!(output, r#"{"tag":"int","value":"-2"}"#);
        }
        r => panic!("{r:?}"),
    }
}

#[test]
fn resource_limits_match_decode_then_run() {
    // 入力の整数の桁数が上限を超える：実行せずに打ち切る
    let narrow = ExecutionProfile {
        integer_bits: 8,
        ..ExecutionProfile::default()
    };
    assert!(matches!(
        same_outcome(ID, br#"{"tag":"int","value":"1024"}"#, &narrow),
        InputOutcome::Ran(RunResult::ResourceExhausted {
            kind: "IntegerBits",
            ..
        })
    ));
    // 評価の step の上限
    let short = ExecutionProfile {
        steps: 3,
        ..ExecutionProfile::default()
    };
    assert!(matches!(
        same_outcome(SUM, LIST.as_bytes(), &short),
        InputOutcome::Ran(RunResult::ResourceExhausted { kind: "Steps", .. })
    ));
}

#[test]
fn rejected_input_matches_decode_then_run() {
    let bad = br#"{"tag":"list","items":[{"tag":"int","value":"1"},{"tag":"bool","value":true}]}"#;
    match same_outcome(SUM, bad, &ExecutionProfile::default()) {
        InputOutcome::Invalid(d) => assert!(!d.is_empty()),
        r => panic!("{r:?}"),
    }
    // UTF-8 でない bytes は入力の境界で拒否する
    assert_eq!(
        same_outcome(SUM, &[0xff], &ExecutionProfile::default()),
        InputOutcome::InputBoundaryFailure
    );
}

/// 一時のディレクトリに `files` を書き、`f` にそのパスを渡す。終わったらディレクトリを消す。
fn in_temp<T>(files: &[(&str, &str)], f: impl FnOnce(&std::path::Path) -> T) -> T {
    static N: std::sync::atomic::AtomicUsize = std::sync::atomic::AtomicUsize::new(0);
    let n = N.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
    let dir = std::env::temp_dir().join(format!("tlvm-value-input-{}-{n}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    for (name, text) in files {
        std::fs::write(dir.join(name), text).unwrap();
    }
    let r = f(&dir);
    std::fs::remove_dir_all(&dir).unwrap();
    r
}

/// `tlvm` を起動した（終了コード、標準出力、標準エラー）。
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

#[test]
fn cli_run_value_json_keeps_output_and_stats() {
    in_temp(&[("sum.tlvm", SUM)], |dir| {
        let p = dir.join("sum.tlvm");
        let (code, out, err) = tlvm(&["run", p.to_str().unwrap(), LIST, "--stats"]);
        assert_eq!(
            (code, out.as_str()),
            (0, "{\"tag\":\"int\",\"value\":\"-2\"}\n")
        );
        // --stats の step と割当は、旧い経路（復号の後の run）と同じ
        let InputOutcome::Ran(RunResult::Completed {
            steps,
            allocated_nodes,
            ..
        }) = decode_then_run(
            &accepted(SUM),
            LIST.as_bytes(),
            &ExecutionProfile::default(),
        )
        else {
            panic!("実行しない");
        };
        assert_eq!(
            err,
            format!("{{\"steps\":{steps},\"allocated_nodes\":{allocated_nodes}}}\n")
        );
    });
}

#[test]
fn cli_test_reports_invalid_expected_and_input() {
    let cases = r#"[{"input":[1,2],"expected":[1,true]},{"input":[1,"x"],"expected":[]}]"#;
    in_temp(&[("echo.tlvm", ECHO), ("cases.json", cases)], |dir| {
        let p = dir.join("echo.tlvm");
        let c = dir.join("cases.json");
        let (code, out, err) = tlvm(&["test", p.to_str().unwrap(), c.to_str().unwrap()]);
        assert_eq!(code, 1);
        assert_eq!(
            out,
            "{\"case\":\"#1\",\"result\":\"error\",\"reason\":\"expected を型 List<Int> として読めません\"}\n\
             {\"case\":\"#2\",\"result\":\"error\",\"reason\":\"input を型 List<Int> として読めません\"}\n\
             {\"passed\":0,\"failed\":2}\n"
        );
        // 診断の span は cases ファイル上の位置（配列の位置に、配列の中の span を足す）
        for (text, at) in [(r#"[1,true]"#, "expected"), (r#"[1,"x"]"#, "input")] {
            let base = cases.find(text).unwrap();
            // `tlvm test` の期待値と入力は普通の JSON で読む（診断の span は普通の JSON の bytes 上）
            let tlvm::DecodeResult::Invalid(d) = decode_plain_input(
                &accepted(ECHO).input_type,
                text.as_bytes(),
                &InputProfile::default(),
            ) else {
                panic!("{at} が読めている");
            };
            let (s, e) = d[0].span;
            assert!(
                err.contains(&format!(
                    "\"span\":{{\"start\":{},\"end\":{}}}",
                    base + s,
                    base + e
                )),
                "{at}: {err}"
            );
        }
    });
}

/// 整数の値 JSON のリスト `[1, 2]`。
const GOOD: &str =
    r#"{"tag":"list","items":[{"tag":"int","value":"1"},{"tag":"int","value":"2"}]}"#;

/// 整数でない要素（真偽値）を含む値 JSON のリスト。
const BAD: &str =
    r#"{"tag":"list","items":[{"tag":"int","value":"1"},{"tag":"bool","value":true}]}"#;

#[test]
fn cli_test_canonical_reports_invalid_expected_and_input() {
    // 値 JSON（`--canonical`）の cases：一件は通り、期待値と入力がそれぞれ読めない二件
    let cases = r#"[{"input":@GOOD@,"expected":@GOOD@},{"input":@GOOD@,"expected":@BAD@},{"input":@BAD@,"expected":@GOOD@}]"#
        .replace("@GOOD@", GOOD)
        .replace("@BAD@", BAD);
    in_temp(&[("echo.tlvm", ECHO), ("cases.json", &cases)], |dir| {
        let p = dir.join("echo.tlvm");
        let c = dir.join("cases.json");
        let (code, out, err) = tlvm(&[
            "test",
            p.to_str().unwrap(),
            c.to_str().unwrap(),
            "--canonical",
        ]);
        assert_eq!(code, 1);
        assert_eq!(
            out,
            "{\"case\":\"#1\",\"result\":\"pass\"}\n\
             {\"case\":\"#2\",\"result\":\"error\",\"reason\":\"expected を型 List<Int> として読めません\"}\n\
             {\"case\":\"#3\",\"result\":\"error\",\"reason\":\"input を型 List<Int> として読めません\"}\n\
             {\"passed\":1,\"failed\":2}\n"
        );
        // 診断の span は cases ファイル上の位置（値 JSON の復号器の span に、配列の位置を足す）
        let tlvm::DecodeResult::Invalid(d) = decode_input(
            &accepted(ECHO).input_type,
            BAD.as_bytes(),
            &InputProfile::default(),
        ) else {
            panic!("読めている");
        };
        let (s, e) = d[0].span;
        // 同じ BAD の文字列は、期待値（#2）と入力（#3）の二か所にある
        for base in [cases.find(BAD).unwrap(), cases.rfind(BAD).unwrap()] {
            let span = format!("\"span\":{{\"start\":{},\"end\":{}}}", base + s, base + e);
            assert!(err.contains(&span), "{span}: {err}");
        }
    });
}
