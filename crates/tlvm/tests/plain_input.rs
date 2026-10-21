//! 普通の JSON の入力（`tlvm run --plain` と埋め込み API の `run_json`）の結果を固定する。
//!
//! 入力は検証済みの復号器が一度読み、その検査で受理した値をそのまま評価する（以前は評価の前にもう一度読んでいた）。
//! ここでは値の順序、大きな整数、拒否の診断（符号・span・終了コード）と資源の上限の結果を固定し、経路を変えても
//! 同じ出力になることを確かめる。復号の回数そのものは、この試験からは直接見えない。

use std::process::Command;

use tlvm::embed::{Limits, Program, RunError};
use tlvm::profiles::ExecutionProfile;

/// 鍵の挿入順に `鍵=値` の行を連ねる（値は String）。
const RENDER: &str = "fn render(d: Dict<String, String>) -> String = fold(dict_entries(d), \"\", |acc, e| concat(acc, concat(fst(e), concat(\"=\", concat(snd(e), \"\\n\")))))\nentry render\n";

/// 値の合計（Int の辞書）。
const TOTAL: &str = "fn total(d: Dict<String, Int>) -> Int = fold(dict_values(d), 0, |a, v| add(a, v))\nentry total\n";

/// 整数のリストの合計。
const SUM: &str =
    "fn solve(xs: List<Int>) -> Int = fold(xs, 0, |acc, x| add(acc, x))\nentry solve\n";

/// 重複した鍵の診断（span は入力 JSON の bytes 上の 3 番目の鍵）。
const DUP_LINE: &str = "{\"severity\":\"error\",\"phase\":\"input-decode\",\"code\":\"E-INPUT-DICT-DUPLICATE-KEY\",\"span\":{\"start\":18,\"end\":21},\"expected\":null,\"actual\":\"a\",\"message\":\"入力の辞書（Dict）に同じ鍵が二度あります\",\"repair\":null}\n";

/// 値が文字列の所に整数を置いた診断。
const TYPE_LINE: &str = "{\"severity\":\"error\",\"phase\":\"input-decode\",\"code\":\"E-INPUT-INTEGER\",\"span\":{\"start\":6,\"end\":9},\"expected\":null,\"actual\":\"x\",\"message\":\"入力整数が正規形ではありません\",\"repair\":null}\n";

/// 閉じていない配列の診断。
const SYNTAX_LINE: &str = "{\"severity\":\"error\",\"phase\":\"input-parse\",\"code\":\"E-INPUT-JSON-SYNTAX\",\"span\":{\"start\":8,\"end\":8},\"expected\":null,\"actual\":null,\"message\":\"入力 JSON の文法が不正です\",\"repair\":null}\n";

fn with_file<T>(src: &str, f: impl FnOnce(&str) -> T) -> T {
    static N: std::sync::atomic::AtomicUsize = std::sync::atomic::AtomicUsize::new(0);
    let n = N.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
    let path =
        std::env::temp_dir().join(format!("tlvm-plain-input-{}-{n}.tlvm", std::process::id()));
    std::fs::write(&path, src).unwrap();
    let r = f(path.to_str().unwrap());
    std::fs::remove_file(&path).unwrap();
    r
}

/// `tlvm run FILE JSON --plain` に `extra` を足して実行した（終了コード、標準出力、標準エラー）。
fn run_plain(src: &str, json: &str, extra: &[&str]) -> (i32, String, String) {
    with_file(src, |p| {
        let mut args = vec!["run", p, json, "--plain"];
        args.extend_from_slice(extra);
        let o = Command::new(env!("CARGO_BIN_EXE_tlvm"))
            .args(&args)
            .output()
            .unwrap();
        (
            o.status.code().unwrap(),
            String::from_utf8(o.stdout).unwrap(),
            String::from_utf8(o.stderr).unwrap(),
        )
    })
}

#[test]
fn string_dict_keeps_insertion_order_and_non_ascii_keys() {
    let (code, out, err) = run_plain(RENDER, r#"[["b","2"],["a","1"],["日本語","x"]]"#, &[]);
    assert_eq!((code, err.as_str()), (0, ""));
    assert_eq!(out, "\"b=2\\na=1\\n日本語=x\\n\"\n");
}

#[test]
fn int_dict_keeps_negative_and_large_values() {
    let json = r#"[["a",1],["b",-5],["c",123456789012345678901234567890]]"#;
    let (code, out, err) = run_plain(TOTAL, json, &["--stats"]);
    assert_eq!(code, 0);
    assert_eq!(out, "\"123456789012345678901234567886\"\n");
    // --stats の step と割当 node は評価の数（入力の復号は数えない）
    assert_eq!(err, "{\"steps\":60,\"allocated_nodes\":10}\n");
}

#[test]
fn rejected_plain_input_keeps_code_span_and_exit_code() {
    let (code, out, err) = run_plain(TOTAL, r#"[["a",1],["b",2],["a",3]]"#, &[]);
    assert_eq!((code, out.as_str()), (1, ""));
    assert_eq!(err, DUP_LINE);
    let (code, out, err) = run_plain(TOTAL, r#"[["a","x"]]"#, &[]);
    assert_eq!((code, out.as_str()), (1, ""));
    assert_eq!(err, TYPE_LINE);
    let (code, out, err) = run_plain(TOTAL, r#"[["a",1]"#, &[]);
    assert_eq!((code, out.as_str()), (1, ""));
    assert_eq!(err, SYNTAX_LINE);
}

#[test]
fn deep_plain_input_is_rejected_by_the_depth_limit() {
    let json = format!("{}{}", "[".repeat(600), "]".repeat(600));
    let (code, out, err) = run_plain(SUM, &json, &[]);
    assert_eq!((code, out.as_str()), (1, ""));
    assert!(
        err.contains("\"code\":\"E-LIMIT-INPUT-JSON-DEPTH\""),
        "{err}"
    );
}

#[test]
fn embed_run_json_gives_the_same_values_and_limit_errors() {
    let p = Program::compile(SUM).unwrap();
    assert_eq!(p.run_json("[1, 2, 3]").unwrap(), "6");

    let p = Program::compile(TOTAL).unwrap();
    assert_eq!(p.run_json(r#"[["a",1],["b",-5]]"#).unwrap(), "-4");
    match p.run_json(r#"[["a",1],["a",2]]"#) {
        Err(RunError::Input(ds)) => {
            assert_eq!(ds.len(), 1);
            assert_eq!(ds[0].code, "E-INPUT-DICT-DUPLICATE-KEY");
            assert_eq!(ds[0].span, (10, 13));
        }
        other => panic!("{other:?}"),
    }

    // 入力の整数の bit 長（10）が上限（8）を超えると、実行せずに IntegerBits で打ち切る
    let p = Program::compile(SUM).unwrap();
    let limits = Limits {
        execution: ExecutionProfile {
            integer_bits: 8,
            ..ExecutionProfile::default()
        },
        ..Limits::default()
    };
    match p.run_json_with("[1000]", &limits) {
        Err(RunError::ResourceExhausted {
            kind,
            observed,
            limit,
        }) => assert_eq!((kind, observed, limit), ("IntegerBits", 10, 8)),
        other => panic!("{other:?}"),
    }

    // 評価の step の上限は、入力の復号を含まない評価の数で決まる
    let limits = Limits {
        execution: ExecutionProfile {
            steps: 5,
            ..ExecutionProfile::default()
        },
        ..Limits::default()
    };
    match p.run_json_with("[1,2,3,4,5,6,7,8,9,10]", &limits) {
        Err(RunError::ResourceExhausted {
            kind,
            observed,
            limit,
        }) => assert_eq!((kind, observed, limit), ("Steps", 6, 5)),
        other => panic!("{other:?}"),
    }
}
