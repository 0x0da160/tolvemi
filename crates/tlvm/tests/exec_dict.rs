//! v1.13 の `tlvm exec` の辞書の入力。標準入力の行 `key<TAB>value` を `Dict<String, V>` にして渡す。
//! `tlvm run --plain` に同じ辞書を渡したときと同じ結果になること、行の誤りと鍵の重複の拒否を確かめる。

use std::process::{Command, Stdio};
use std::io::Write;

fn with_file<T>(src: &str, f: impl FnOnce(&str) -> T) -> T {
    static N: std::sync::atomic::AtomicUsize = std::sync::atomic::AtomicUsize::new(0);
    let n = N.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
    let path = std::env::temp_dir().join(format!("tlvm-exec-dict-{}-{n}.tlvm", std::process::id()));
    std::fs::write(&path, src).unwrap();
    let r = f(path.to_str().unwrap());
    std::fs::remove_file(&path).unwrap();
    r
}

/// `tlvm exec FILE` を標準入力 `stdin` で実行した（終了コード、標準出力、標準エラー）。
fn exec(src: &str, stdin: &[u8]) -> (i32, String, String) {
    with_file(src, |p| {
        let mut c = Command::new(env!("CARGO_BIN_EXE_tlvm"))
            .args(["exec", p])
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::piped())
            .spawn()
            .unwrap();
        c.stdin.take().unwrap().write_all(stdin).unwrap();
        let o = c.wait_with_output().unwrap();
        (o.status.code().unwrap(), String::from_utf8(o.stdout).unwrap(), String::from_utf8(o.stderr).unwrap())
    })
}

/// `tlvm run FILE JSON --plain` の（終了コード、標準出力、標準エラー）。
fn run_plain(src: &str, json: &str) -> (i32, String, String) {
    with_file(src, |p| {
        let o = Command::new(env!("CARGO_BIN_EXE_tlvm")).args(["run", p, json, "--plain"]).output().unwrap();
        (o.status.code().unwrap(), String::from_utf8(o.stdout).unwrap(), String::from_utf8(o.stderr).unwrap())
    })
}

/// 値が文字列の辞書を普通の JSON `[["鍵","値"], ...]` にする（鍵と値は JSON の文字列に入る文字だけ）。
fn json_str_pairs(pairs: &[(&str, &str)]) -> String {
    let items: Vec<String> = pairs.iter().map(|(k, v)| format!("[\"{k}\",\"{v}\"]")).collect();
    format!("[{}]", items.join(","))
}

/// 値が整数の辞書を普通の JSON `[["鍵", 値], ...]` にする。
fn json_int_pairs(pairs: &[(&str, &str)]) -> String {
    let items: Vec<String> = pairs.iter().map(|(k, v)| format!("[\"{k}\",{v}]")).collect();
    format!("[{}]", items.join(","))
}

/// 鍵ごとに `鍵=値` の行を挿入順に出す（値は String）。
const RENDER: &str = "fn render(d: Dict<String, String>) -> String = fold(dict_entries(d), \"\", |acc, e| concat(acc, concat(fst(e), concat(\"=\", concat(snd(e), \"\\n\")))))\nentry render\n";

/// 鍵の数と、鍵 "cat" の値（String の辞書）。出力は plain JSON。
const LOOKUP: &str = "fn lookup(d: Dict<String, String>) -> Pair<Int, Option<String>> = pair(dict_size(d), dict_get(d, \"cat\"))\nentry lookup\n";

/// 鍵 "x" の値（String の辞書）。
const GET: &str = "fn get(d: Dict<String, String>) -> Option<String> = dict_get(d, \"x\")\nentry get\n";

/// 値の合計（Int の辞書）。
const TOTAL: &str = "fn total(d: Dict<String, Int>) -> Int = fold(dict_values(d), 0, |a, v| add(a, v))\nentry total\n";

/// 鍵 "hello world" と "日本語" の値（Int の辞書）。
const PAIR_INTS: &str = "fn look(d: Dict<String, Int>) -> Pair<Option<Int>, Option<Int>> = pair(dict_get(d, \"hello world\"), dict_get(d, \"日本語\"))\nentry look\n";

/// 鍵 "日本語" の値（String の辞書）。
const JA: &str = "fn ja(d: Dict<String, String>) -> Option<String> = dict_get(d, \"日本語\")\nentry ja\n";

/// 鍵 "x" があるかで `ok` か `err`（出力型 Result<String, String>）。
const HAS_X: &str = "fn has_x(d: Dict<String, Int>) -> Result<String, String> = if(dict_has(d, \"x\"), ok<String, String>(\"found x\"), err<String, String>(\"no x\"))\nentry has_x\n";

const DUPLICATE_KEY: &str = "E-INPUT-DICT-DUPLICATE-KEY";

#[test]
fn string_values_match_run_plain() {
    let (code, out, err) = exec(RENDER, b"cat\tanimal\ndog\tanimal\nbird\tflying animal\n");
    assert_eq!((code, err.as_str()), (0, ""));
    assert_eq!(out, "cat=animal\ndog=animal\nbird=flying animal\n");
    // 同じ辞書を run --plain に渡すと、同じ内容の文字列が plain JSON で返る
    let (code, out, _) = run_plain(RENDER, &json_str_pairs(&[("cat", "animal"), ("dog", "animal"), ("bird", "flying animal")]));
    assert_eq!(code, 0);
    assert_eq!(out.trim_end(), r#""cat=animal\ndog=animal\nbird=flying animal\n""#);
    // 鍵を引く（word の辞書の使い方）：件数と値
    assert_eq!(exec(LOOKUP, b"cat\tanimal\ndog\tanimal\nbird\tflying animal\n").1, "[3,\"animal\"]\n");
}

#[test]
fn int_values_with_negatives_match_run_plain() {
    assert_eq!(exec(TOTAL, b"a\t1\nb\t-5\nc\t0\n"), (0, "-4\n".into(), String::new()));
    let (code, out, _) = run_plain(TOTAL, &json_int_pairs(&[("a", "1"), ("b", "-5"), ("c", "0")]));
    assert_eq!((code, out.trim_end()), (0, "-4"));
    // 値の正規の表記（0、-1、大きな整数）は受理する
    assert_eq!(exec(TOTAL, b"a\t0\nb\t-1\nc\t123456789012345678901234567890\n").1, "\"123456789012345678901234567889\"\n");
}

#[test]
fn empty_stdin_is_the_empty_dict() {
    for stdin in [&b""[..], &b"\n"[..], &b"\n\n"[..], &b"\r\n\n"[..]] {
        assert_eq!(exec(LOOKUP, stdin), (0, "[0,null]\n".into(), String::new()), "stdin {stdin:?}");
    }
    assert_eq!(run_plain(LOOKUP, "[]").1.trim_end(), "[0,null]");
}

#[test]
fn trailing_newline_and_crlf_do_not_add_lines() {
    let want = (0, "[1,\"animal\"]\n".to_string(), String::new());
    for stdin in [&b"cat\tanimal"[..], &b"cat\tanimal\n"[..], &b"cat\tanimal\n\n\n"[..], &b"cat\tanimal\r\n"[..], &b"cat\tanimal\r\n\r\n"[..]] {
        assert_eq!(exec(LOOKUP, stdin), want, "stdin {stdin:?}");
    }
    // CR は行末の一つだけを取る。行の途中の CR は値の一部
    assert_eq!(exec(GET, b"x\tp\rq\n").1, "\"p\\rq\"\n");
    assert_eq!(exec(GET, b"x\tp\r\r\n").1, "\"p\\r\"\n");
}

#[test]
fn empty_string_value_is_allowed() {
    assert_eq!(exec(LOOKUP, b"cat\t\n").1, "[1,\"\"]\n");
    assert_eq!(exec(GET, b"x\t\n").1, "\"\"\n");
}

#[test]
fn keys_with_spaces_and_non_ascii() {
    let stdin = "hello world\t1\n日本語\t2\n".as_bytes();
    assert_eq!(exec(PAIR_INTS, stdin), (0, "[1,2]\n".into(), String::new()));
    let (_, out, _) = run_plain(PAIR_INTS, r#"[["hello world",1],["日本語",2]]"#);
    assert_eq!(out.trim_end(), "[1,2]");
    // 値も非 ASCII。鍵の前後の空白は取らない
    assert_eq!(exec(JA, "日本語\t値\n".as_bytes()).1, "\"値\"\n");
    assert_eq!(exec(PAIR_INTS, "hello world \t1\n".as_bytes()).1, "[null,null]\n");
}

#[test]
fn missing_tab_is_an_input_boundary_failure() {
    let (code, out, err) = exec(TOTAL, b"a\t1\nb 2\n");
    assert_eq!((code, out.as_str()), (1, ""));
    assert_eq!(err, "{\"result\":\"InputBoundaryFailure\",\"reason\":\"行 2: 鍵と値を分ける TAB がありません\"}\n");
}

#[test]
fn malformed_lines_name_the_line_and_the_reason() {
    // (標準入力, 行番号, 理由の一部) ― TOTAL（Int の辞書）
    let cases: [(&str, usize, &str); 10] = [
        ("\t1\n", 1, "鍵が空です"),
        ("a\t1\tx\n", 1, "値に TAB があります"),
        ("a\t1\nb\t007\n", 2, "Int の正規の表記ではありません"),
        ("a\t-0\n", 1, "Int の正規の表記ではありません"),
        ("a\t+1\n", 1, "Int の正規の表記ではありません"),
        ("a\t\n", 1, "Int の正規の表記ではありません"),
        ("a\t 1\n", 1, "Int の正規の表記ではありません"),
        ("a\t1.5\n", 1, "Int の正規の表記ではありません"),
        ("a\tx\n", 1, "Int の正規の表記ではありません"),
        ("a\t1\n\n\nbad\n", 4, "鍵と値を分ける TAB がありません"),
    ];
    for (stdin, line, why) in cases {
        let (code, out, err) = exec(TOTAL, stdin.as_bytes());
        assert_eq!((code, out.as_str()), (1, ""), "stdin {stdin:?}");
        let want = format!("{{\"result\":\"InputBoundaryFailure\",\"reason\":\"行 {line}: ");
        assert!(err.starts_with(&want) && err.contains(why), "stdin {stdin:?}: {err}");
    }
    // 文字列の値の辞書では空の値は正しく、TAB がなければ誤り
    let (code, _, err) = exec(RENDER, b"a\tb\nc\n");
    assert_eq!(code, 1);
    assert!(err.contains("行 2: 鍵と値を分ける TAB がありません"), "{err}");
}

#[test]
fn blank_lines_are_skipped_but_counted() {
    let (code, _, err) = exec(TOTAL, b"a\t1\n\n\nbad\n");
    assert_eq!(code, 1);
    assert!(err.contains("行 4:"), "{err}");
    assert_eq!(exec(TOTAL, b"a\t1\n\n\nb\t2\n"), (0, "3\n".into(), String::new()));
}

#[test]
fn duplicate_key_is_rejected_as_in_run_plain() {
    let (code, out, err) = exec(TOTAL, b"a\t1\nb\t2\na\t3\n");
    assert_eq!((code, out.as_str()), (1, ""));
    assert!(err.contains(DUPLICATE_KEY) && !err.contains("MISMATCH"), "{err}");
    // 診断の span は重複した行（3 行目、標準入力の 8 から 11 の byte）。鍵は "a"
    assert!(err.contains("\"span\":{\"start\":8,\"end\":11}") && err.contains("\"actual\":\"a\""), "{err}");
    // run --plain に同じ鍵の重なる辞書を渡すと同じ診断コードで拒否される
    let (code, _, err) = run_plain(TOTAL, r#"[["a",1],["b",2],["a",3]]"#);
    assert_eq!(code, 1);
    assert!(err.contains(DUPLICATE_KEY) && !err.contains("MISMATCH"), "{err}");
    // 文字列の値でも同じ
    let (code, _, err) = exec(RENDER, b"a\tx\na\ty\n");
    assert_eq!(code, 1);
    assert!(err.contains(DUPLICATE_KEY), "{err}");
}

#[test]
fn int_digit_limit_is_reported_on_its_line() {
    // 4096 桁までは受理し（出力は JSON の文字列）、4097 桁は拒否する（2 行目の範囲を指す）
    let d4096 = "1".repeat(4096);
    let (code, out, _) = exec(TOTAL, format!("a\t{d4096}\n").as_bytes());
    assert_eq!(code, 0);
    assert_eq!(out.len(), 4096 + 3, "quoted digits and a newline");
    let d4097 = "1".repeat(4097);
    let (code, _, err) = exec(TOTAL, format!("x\t0\na\t{d4097}\n").as_bytes());
    assert_eq!(code, 1);
    assert!(err.contains("E-LIMIT-INPUT-INTEGER-DIGITS") && err.contains("\"span\":{\"start\":4,\"end\":4103}"), "{err}");
}

#[test]
fn result_output_with_dict_input() {
    assert_eq!(exec(HAS_X, b"x\t1\n"), (0, "found x".into(), String::new()));
    assert_eq!(exec(HAS_X, b"y\t1\n"), (1, String::new(), "no x".into()));
}

#[test]
fn unsupported_dict_entries_keep_unsupported_entry() {
    for ty in ["Dict<Int, String>", "Dict<Bool, Int>", "Dict<String, Bool>", "Dict<String, List<String>>", "Dict<String, Pair<Int, Int>>"] {
        let src = format!("fn solve(d: {ty}) -> Int = dict_size(d)\nentry solve\n");
        let (code, out, err) = exec(&src, b"");
        assert_eq!((code, out.as_str()), (64, ""), "{ty}");
        assert!(err.contains("UnsupportedEntry") && err.contains(&format!("（この entry は {ty}）")), "{ty}: {err}");
        assert!(err.contains("Dict<String, String>、Dict<String, Int>"), "{err}");
    }
}

#[test]
fn exec_and_run_agree_on_the_same_dict() {
    let cases: [(&str, &str); 3] = [
        ("a\t1\nb\t-5\nc\t0\n", r#"[["a",1],["b",-5],["c",0]]"#),
        ("", "[]"),
        ("big\t1000000000000000000000000\n", r#"[["big",1000000000000000000000000]]"#),
    ];
    for (stdin, json) in cases {
        let (code, out, _) = exec(TOTAL, stdin.as_bytes());
        let (rcode, rout, _) = run_plain(TOTAL, json);
        assert_eq!((code, out.trim_end()), (rcode, rout.trim_end()), "stdin {stdin:?}");
    }
    let (code, out, _) = exec(LOOKUP, b"dog\tbark\ncat\tmeow\n");
    let (rcode, rout, _) = run_plain(LOOKUP, &json_str_pairs(&[("dog", "bark"), ("cat", "meow")]));
    assert_eq!((code, out.trim_end()), (rcode, rout.trim_end()));
    assert_eq!(out, "[2,\"meow\"]\n");
}

#[test]
fn larger_input_is_summed() {
    let mut stdin = String::new();
    let mut want = 0i64;
    for i in 0..5000i64 {
        stdin.push_str(&format!("k{i}\t{i}\n"));
        want += i;
    }
    assert_eq!(exec(TOTAL, stdin.as_bytes()), (0, format!("{want}\n"), String::new()));
}
