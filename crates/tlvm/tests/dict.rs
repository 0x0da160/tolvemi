//! v1.9 の辞書 `Dict<K, V>`（差分仕様 §1〜§3）。

use std::io::Write;
use std::process::{Command, Stdio};
use tlvm::api::*;
use tlvm::checker::check_program;
use tlvm::formatter::format_program;
use tlvm::profiles::*;

fn tlvm(args: &[&str]) -> (i32, String, String) {
    let o = Command::new(env!("CARGO_BIN_EXE_tlvm")).args(args).output().unwrap();
    (o.status.code().unwrap(), String::from_utf8(o.stdout).unwrap(), String::from_utf8(o.stderr).unwrap())
}

fn with_file<T>(src: &str, ext: &str, f: impl FnOnce(&str) -> T) -> T {
    static N: std::sync::atomic::AtomicUsize = std::sync::atomic::AtomicUsize::new(0);
    let n = N.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
    let path = std::env::temp_dir().join(format!("tlvm-dict-{}-{n}.{ext}", std::process::id()));
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

/// plain JSON で実行したときの（終了コード、標準エラー）。
fn run_err(src: &str, input: &str, plain: bool) -> (i32, String) {
    with_file(src, "tlvm", |p| {
        let mut args = vec!["run", p, input];
        if plain {
            args.push("--plain");
        }
        let (code, _, err) = tlvm(&args);
        (code, err)
    })
}

fn compiled(src: &str) -> CompileResult {
    match compile(src.as_bytes(), &StaticProfile::default()) {
        SourceCompile::Result(r) => r,
        _ => panic!("boundary"),
    }
}

fn errors(src: &str) -> Vec<tlvm::diagnostics::Diagnostic> {
    compiled(src).errors().to_vec()
}

fn codes(src: &str) -> Vec<&'static str> {
    errors(src).iter().map(|d| d.code).collect()
}

fn accepted(src: &str) -> tlvm::checker::TypedProgram {
    match compiled(src) {
        CompileResult::Accepted { program, .. } => program,
        r => panic!("rejected: {:?}", r.errors()),
    }
}

/// 検証済み部品へ渡す、書き換え後のソース。
fn lowered(src: &str) -> String {
    let p = match parse_source(src.as_bytes(), &StaticProfile::default()) {
        Parsed::Program(p) => p,
        _ => panic!("parse"),
    };
    let px = expand(&p).unwrap();
    let o = check_program(&px, src.len(), &StaticProfile::default());
    assert!(o.typed.is_some(), "{:?}", o.diagnostics);
    format_program(&tlvm::dict::erase(&lower(&tlvm::hof::lower(&px, &o.hof))))
}

// ---------------------------------------------------------------- 意味

/// 語を数える（挿入順。既にある鍵の更新は位置を変えない）。
const COUNT: &str = "fn count(ws: List<String>) -> Dict<String, Int> =
  fold(ws, dict<String, Int>(), |d, w| dict_put(d, w, add(match_option(dict_get(d, w), 0, |c| c), 1)))
fn solve(ws: List<String>) -> Dict<String, Int> = count(ws)
entry solve
";

#[test]
fn put_get_and_insertion_order() {
    assert_eq!(run(COUNT, r#"["b","a","b","c","a","b"]"#), r#"[["b",3],["a",2],["c",1]]"#);
    assert_eq!(run(COUNT, "[]"), "[]");
    let p = accepted(COUNT);
    assert_eq!(p.output_type.to_string(), "Dict<String, Int>");
    assert!(p.terminates());
}

#[test]
fn replace_keeps_position_and_remove() {
    let src = "fn solve(d: Dict<Int, String>) -> List<Dict<Int, String>> =
  list<Dict<Int, String>>(
    dict_put(d, 2, \"B\"),
    dict_put(d, 9, \"new\"),
    dict_remove(d, 2),
    dict_remove(d, 7),
    dict_put(dict_remove(d, 1), 1, \"back\"))
entry solve
";
    assert_eq!(
        run(src, r#"[[1,"a"],[2,"b"],[3,"c"]]"#),
        r#"[[[1,"a"],[2,"B"],[3,"c"]],[[1,"a"],[2,"b"],[3,"c"],[9,"new"]],[[1,"a"],[3,"c"]],[[1,"a"],[2,"b"],[3,"c"]],[[2,"b"],[3,"c"],[1,"back"]]]"#
    );
    assert_eq!(run(src, "[]"), r#"[[[2,"B"]],[[9,"new"]],[],[],[[1,"back"]]]"#);
}

#[test]
fn queries() {
    let src = "fn solve(d: Dict<String, Int>) -> Pair<Pair<Option<Int>, Option<Int>>, Pair<Pair<Bool, Bool>, Pair<Int, Pair<List<String>, Pair<List<Int>, List<Pair<String, Int>>>>>>> =
  pair(pair(dict_get(d, \"y\"), dict_get(d, \"q\")),
  pair(pair(dict_has(d, \"x\"), dict_has(d, \"q\")),
  pair(dict_size(d), pair(dict_keys(d), pair(dict_values(d), dict_entries(d))))))
entry solve
";
    assert_eq!(
        run(src, r#"[["x",1],["y",-5],["z",0]]"#),
        r#"[[-5,null],[[true,false],[3,[["x","y","z"],[[1,-5,0],[["x",1],["y",-5],["z",0]]]]]]]"#
    );
    assert_eq!(run(src, "[]"), "[[null,null],[[false,false],[0,[[],[[],[]]]]]]");
}

#[test]
fn from_with_duplicates_keeps_first_position_and_last_value() {
    let src = "fn solve(xs: List<Pair<String, Int>>) -> Dict<String, Int> = dict_from(xs)\nentry solve\n";
    assert_eq!(run(src, r#"[["a",1],["b",2],["a",3],["c",4],["b",5]]"#), r#"[["a",3],["b",5],["c",4]]"#);
    assert_eq!(run(src, "[]"), "[]");
}

#[test]
fn key_types_int_pair_record_and_dict() {
    // Int・Pair・レコード・Dict（挿入順で比べる）を鍵にする
    let src = "type P = { x: Int, y: Int }
fn solve(xs: List<Int>) -> Pair<Pair<Int, Int>, Pair<Option<Int>, Pair<List<P>, Int>>> =
  let byint = dict_from(map(xs, |x| pair(mod_or(x), x))) in
  let bypair = dict_put(dict_put(dict<Pair<Int, Bool>, Int>(), pair(1, true), 10), pair(1, false), 20) in
  let byrec = fold(xs, dict<P, Int>(), |d, x| dict_put(d, P { x: x, y: neg(x) }, x)) in
  let bydict = dict_put(dict_put(dict<Dict<Int, Int>, Int>(), dict_from(list<Pair<Int, Int>>(pair(1, 1), pair(2, 2))), 1),
    dict_from(list<Pair<Int, Int>>(pair(2, 2), pair(1, 1))), 2) in
  pair(pair(dict_size(byint), dict_size(bypair)),
    pair(dict_get(bypair, pair(1, false)), pair(dict_keys(byrec), dict_size(bydict))))
fn mod_or(x: Int) -> Int = match_option(mod(x, 3), 0, |r| r)
entry solve
";
    assert_eq!(run(src, "[1, 4, 2, 4, 7]"), r#"[[2,2],[20,[[{"x":1,"y":-1},{"x":4,"y":-4},{"x":2,"y":-2},{"x":7,"y":-7}],2]]]"#);
}

#[test]
fn eq_compares_in_insertion_order() {
    let src = "fn solve(u: Unit) -> Pair<Bool, Pair<Bool, Bool>> =
  let a = dict_put(dict_put(dict<Int, Int>(), 1, 10), 2, 20) in
  let b = dict_put(dict_put(dict<Int, Int>(), 2, 20), 1, 10) in
  let c = dict_put(a, 1, 10) in
  pair(eq(a, b), pair(eq(a, c), eq(dict_entries(a), dict_entries(b))))
entry solve
";
    assert_eq!(run(src, "null"), "[false,[true,false]]");
}

#[test]
fn nested_dict_values() {
    // 語を頭文字ごとに分けて数える：Dict<Char, Dict<String, Int>>
    let src = "fn bump(d: Dict<String, Int>, w: String) -> Dict<String, Int> = dict_put(d, w, add(match_option(dict_get(d, w), 0, |c| c), 1))
fn solve(ws: List<String>) -> Dict<Char, Dict<String, Int>> =
  fold(filter(ws, |w| lt(0, length(w))), dict<Char, Dict<String, Int>>(), |d, w|
    match uncons(w) {
      some(p) => dict_put(d, fst(p), bump(match_option(dict_get(d, fst(p)), dict<String, Int>(), |inner| inner), w)),
      none => d
    })
entry solve
";
    assert_eq!(
        run(src, r#"["apple","bee","avocado","apple","","bee","cat"]"#),
        r#"[["a",[["apple",2],["avocado",1]]],["b",[["bee",2]]],["c",[["cat",1]]]]"#
    );
}

#[test]
fn inside_map_filter_loop_rec_and_sums() {
    // map・filter・sort_by の中、loop の状態、rec fn の引数、直和型の中身、レコードの field に辞書を使う
    let src = "type Inv = { items: Dict<String, Int>, ops: Int }
type Op = Add(String, Int) | Drop(String)
fn apply(inv: Inv, op: Op) -> Inv = match op {
  Add(k, n) => Inv { items: dict_put(inv.items, k, add(match_option(dict_get(inv.items, k), 0, |c| c), n)), ops: add(inv.ops, 1) },
  Drop(k) => Inv { items: dict_remove(inv.items, k), ..inv }
}
rec fn total(ks: List<String>, d: Dict<String, Int>) -> Int =
  match uncons(ks) { some(p) => add(match_option(dict_get(d, fst(p)), 0, |c| c), total(snd(p), d)), none => 0 }
fn solve(xs: List<Pair<String, Int>>) -> Pair<Inv, Pair<Int, Pair<List<Int>, Option<Dict<Int, Int>>>>> =
  let inv = fold(xs, Inv { items: dict<String, Int>(), ops: 0 }, |s, x|
    apply(s, if(lt(snd(x), 0), Drop(fst(x)), Add(fst(x), snd(x))))) in
  let sizes = map(xs, |x| dict_size(dict_from(list<Pair<String, Int>>(x, pair(\"k\", 0))))) in
  let squares = loop(dict<Int, Int>(), 5, |d| if(lt(dict_size(d), 4), some(dict_put(d, dict_size(d), mul(dict_size(d), dict_size(d)))), none<Dict<Int, Int>>())) in
  pair(inv, pair(total(dict_keys(inv.items), inv.items), pair(map(sort_by(dict_entries(inv.items), |e| snd(e)), |e| snd(e)), squares)))
entry solve
";
    assert_eq!(
        run(src, r#"[["a",3],["b",1],["a",2],["c",-1],["b",-1],["d",4]]"#),
        r#"[{"items":[["a",5],["d",4]],"ops":4},[9,[[4,5],[[0,0],[1,1],[2,4],[3,9]]]]]"#
    );
}

#[test]
fn larger_dict_from_within_default_limits() {
    // O(n²) の書き換えでも、数百件の辞書は既定の資源上限に十分収まる
    let src = "fn solve(n: Int) -> Pair<Int, Option<Int>> =
  let d = dict_from(map(range(0, n), |i| pair(match_option(mod(i, 150), 0, |r| r), i))) in
  pair(dict_size(d), dict_get(d, 149))
entry solve
";
    with_file(src, "tlvm", |p| {
        let (code, out, err) = tlvm(&["run", p, "400", "--plain", "--stats"]);
        assert_eq!(code, 0, "{err}");
        assert_eq!(out.trim_end(), "[150,299]");
        let steps: u64 = err.split("\"steps\":").nth(1).unwrap().split(',').next().unwrap().parse().unwrap();
        assert!(steps < 2_000_000, "{steps}");
    });
}

// ---------------------------------------------------------------- 書き換え

#[test]
fn lowering_removes_dict() {
    let text = lowered(COUNT);
    assert!(!text.contains("Dict") && !text.contains("dict"), "{text}");
    assert!(text.contains("List<Pair<String, Int>>"), "{text}");
    assert!(text.contains("hof1"), "{text}");
    // 書き換え後のソースは検証済み formatter の正準形
    assert_eq!(canonical(&text, &StaticProfile::default()).as_deref(), Some(text.as_str()));
}

#[test]
fn soft_keyword_names() {
    // dict と操作の名前は変数・引数・束縛・field の名前に使える。`Dict` は予約語でなくレコード型の名前にも使える
    let src = "type Dict = { dict: Int, dict_get: Bool }
fn solve(dict_put: Int) -> Pair<Dict, Pair<Int, Int>> =
  let dict = dict_put in
  let dict_size = dict_size(dict_put(dict<Int, Int>(), dict, 1)) in
  pair(Dict { dict: dict, dict_get: true }, pair(dict_size, fold(list<Int>(1, 2), 0, |dict_keys, dict_from| add(dict_keys, dict_from))))
entry solve
";
    assert_eq!(run(src, "7"), r#"[{"dict":7,"dict_get":true},[1,3]]"#);
    // 関数名には使えない（検証済み parser との食い違いにはならない）
    let c = codes("fn dict_get(x: Int) -> Int = x\nentry dict_get\n");
    assert!(c.contains(&"E-PARSE-EXPECTED-IDENT") && !c.contains(&"E-INTERNAL-VERIFIED-MISMATCH"), "{c:?}");
    let c = codes("fn f(x: Int) -> Int = dict_lookup(x)\nentry f\n");
    assert_eq!(c, ["E-NAME-UNKNOWN-FUNCTION"]);
    // ast は予約語の変数名を付け替える
    let renamed = "fn solve(dict: Int) -> Int = dict_size(dict_put(dict<Int, Int>(), dict, 1))\nentry solve\n";
    with_file(renamed, "tlvm", |p| {
        let (code, out, err) = tlvm(&["ast", p]);
        assert_eq!(code, 0, "{err}");
        assert!(out.contains("\"name\":\"dict_kw\"") && out.contains("\"callee\":\"dict_put\""), "{out}");
    });
}

#[test]
fn fmt_round_trip() {
    let src = "fn solve(d: Dict<String,Int>)->Dict<String,List<Int>> =
    fold(dict_keys(d), dict<String,List<Int>>(), |acc, k| dict_put(acc, k, list<Int>(match_option(dict_get(d, k), 0, |v| v))))
entry solve
";
    with_file(src, "tlvm", |p| {
        let (code, out, err) = tlvm(&["fmt", p]);
        assert_eq!(code, 0, "{err}");
        assert!(out.starts_with("fn solve(d: Dict<String, Int>) -> Dict<String, List<Int>> = fold(dict_keys(d), dict<String, List<Int>>(), "), "{out}");
        with_file(&out, "tlvm", |q| {
            assert_eq!(tlvm(&["fmt", q]).1, out);
            assert_eq!(tlvm(&["run", q, r#"[["a",1],["b",2]]"#, "--plain"]).1.trim_end(), r#"[["a",[1]],["b",[2]]]"#);
        });
    });
}

#[test]
fn ast_codec_tags() {
    let src = "fn solve(d: Dict<Int, Bool>) -> Pair<Dict<Int, Bool>, Bool> = pair(dict_put(d, 0, true), dict_has(dict<Int, Bool>(), 1))\nentry solve\n";
    with_file(src, "tlvm", |p| {
        let (code, json, err) = tlvm(&["ast", p]);
        assert_eq!(code, 0, "{err}");
        assert!(json.contains(r#"{"tag":"dict","key":{"tag":"int"},"value":{"tag":"bool"}}"#), "{json}");
        assert!(json.contains(r#"{"tag":"dict","key_type":{"tag":"int"},"value_type":{"tag":"bool"}}"#), "{json}");
        assert!(json.contains(r#""callee":"dict_put""#), "{json}");
        with_file(json.trim_end(), "json", |q| {
            let (code, out, err) = tlvm(&["run", q, "[[1,false]]", "--plain"]);
            assert_eq!(code, 0, "{err}");
            assert_eq!(out.trim_end(), "[[[1,false],[0,true]],false]");
            // AST から整形しても同じソース
            assert_eq!(tlvm(&["fmt", q]).1, tlvm(&["fmt", p]).1);
        });
    });
    // AST の型 tag の検査
    let bad = r#"{"codec":"ast_codec_v1","declarations":[{"tag":"fn","name":"f","params":[{"name":"d","type":{"tag":"dict","key":{"tag":"int"}}}],"return_type":{"tag":"int"},"body":{"tag":"int","value":"0"}},{"tag":"entry","name":"f"}]}"#;
    match compile_ast(bad.as_bytes(), &StaticProfile::default(), &AstTransportProfile::default()) {
        AstCompile::AstInvalid(d) => assert_eq!(d[0].code, "E-AST-MISSING-FIELD"),
        _ => panic!("accepted"),
    }
}

// ---------------------------------------------------------------- 入出力

#[test]
fn dict_input_value_and_plain_json() {
    let src = "fn solve(d: Dict<String, Int>) -> Int = fold(dict_values(d), 0, |a, v| add(a, v))\nentry solve\n";
    assert_eq!(run(src, r#"[["a",1],["b",2]]"#), "3");
    // 鍵が重なる入力は拒否する（plain JSON と値 JSON のどちらでも）
    let (code, err) = run_err(src, r#"[["a",1],["b",2],["a",3]]"#, true);
    assert_eq!(code, 1);
    assert!(err.contains("E-INPUT-DICT-DUPLICATE-KEY") && !err.contains("MISMATCH"), "{err}");
    let pair = |k: &str, v: i32| format!(r#"{{"tag":"pair","left":{{"tag":"list","items":[{{"tag":"char","value":"{}"}}]}},"right":{{"tag":"int","value":"{v}"}}}}"#, k.chars().next().unwrap() as u32);
    let dup = format!(r#"{{"tag":"list","items":[{},{}]}}"#, pair("a", 1), pair("a", 2));
    let (code, err) = run_err(src, &dup, false);
    assert_eq!(code, 1);
    assert!(err.contains("E-INPUT-DICT-DUPLICATE-KEY") && !err.contains("MISMATCH"), "{err}");
    let ok = format!(r#"{{"tag":"list","items":[{},{}]}}"#, pair("a", 1), pair("b", 2));
    with_file(src, "tlvm", |p| assert_eq!(tlvm(&["run", p, &ok]).1.trim_end(), r#"{"tag":"int","value":"3"}"#));
    // 形の誤り
    let (_, err) = run_err(src, r#"[["a",1,2]]"#, true);
    assert!(err.contains("E-INPUT-FIELD-TYPE") && err.contains("[key, value]"), "{err}");
    let (_, err) = run_err(src, r#"{"a":1}"#, true);
    assert!(err.contains("array of [key, value] arrays"), "{err}");
}

#[test]
fn tlvm_test_with_dict_cases() {
    let src = "fn solve(d: Dict<Int, Int>) -> Dict<Int, Int> = dict_put(dict_remove(d, 1), 5, 50)\nentry solve\n";
    let cases = r#"[{"name": "a", "input": [[1, 10], [2, 20]], "expected": [[2, 20], [5, 50]]},
{"name": "b", "input": [], "expected": [[5, 50]]},
{"name": "dup", "input": [[1, 1], [1, 2]], "expected": []}]"#;
    with_file(src, "tlvm", |p| {
        with_file(cases, "json", |c| {
            let (code, out, _) = tlvm(&["test", p, c]);
            assert_eq!(code, 1);
            assert!(out.contains(r#"{"case":"a","result":"pass"}"#) && out.contains(r#"{"case":"b","result":"pass"}"#), "{out}");
            assert!(out.contains(r#""case":"dup","result":"error""#), "{out}");
        })
    });
}

#[test]
fn exec_with_dict_inside() {
    // 単語の出現回数を数える（入出力は String、辞書は中だけ）
    let src = "fn words(s: String) -> List<String> =
  let r = fold(s, pair(list<String>(), \"\"), |st, c| if(eq(c, ' '), pair(if(eq(snd(st), \"\"), fst(st), cons(reverse(snd(st)), fst(st))), \"\"), pair(fst(st), cons(c, snd(st))))) in
  reverse(if(eq(snd(r), \"\"), fst(r), cons(reverse(snd(r)), fst(r))))
fn solve(s: String) -> String =
  let d = fold(words(s), dict<String, Int>(), |d, w| dict_put(d, w, add(match_option(dict_get(d, w), 0, |c| c), 1))) in
  fold(dict_entries(d), \"\", |out, e| concat(out, concat(fst(e), concat(\"=\", concat(to_string(snd(e)), \"\\n\")))))
entry solve
";
    with_file(src, "tlvm", |p| {
        let mut c = Command::new(env!("CARGO_BIN_EXE_tlvm"))
            .args(["exec", p])
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::piped())
            .spawn()
            .unwrap();
        c.stdin.take().unwrap().write_all(b"to be or not to be").unwrap();
        let o = c.wait_with_output().unwrap();
        assert_eq!(String::from_utf8(o.stdout).unwrap(), "to=2\nbe=2\nor=1\nnot=1\n");
    });
    // Dict は exec の入力型にはならない
    with_file("fn solve(d: Dict<String, Int>) -> String = \"\"\nentry solve\n", "tlvm", |p| {
        let (code, _, err) = tlvm(&["exec", p]);
        assert_eq!(code, 64);
        assert!(err.contains("UnsupportedEntry") && err.contains("Dict<String, Int>"), "{err}");
    });
}

#[test]
fn check_reports_dict_types() {
    with_file(COUNT, "tlvm", |p| {
        let (code, out, _) = tlvm(&["check", p]);
        assert_eq!(code, 0);
        assert!(out.contains(r#""input_type":"List<String>","output_type":"Dict<String, Int>""#), "{out}");
    });
}

// ---------------------------------------------------------------- 診断

#[test]
fn diagnostics_and_repairs() {
    // 第 1 引数が辞書でない。List<Pair<K, V>> なら dict_from を示す
    let e = errors("fn f(xs: List<Pair<String, Int>>) -> Option<Int> = dict_get(xs, \"a\")\nentry f\n");
    assert_eq!(e[0].code, "E-TYPE-DICT-ARG");
    assert_eq!(e[0].actual.as_deref(), Some("List<Pair<String, Int>>"));
    assert!(e[0].repair.as_ref().unwrap().constraint.contains("dict_from(xs)"), "{:?}", e[0].repair);
    let e = errors("fn f(n: Int) -> Int = dict_size(n)\nentry f\n");
    assert_eq!(e[0].code, "E-TYPE-DICT-ARG");
    assert!(e[0].repair.as_ref().unwrap().constraint.contains("dict<K, V>()"));
    // 鍵・値の型
    let e = errors("fn f(d: Dict<String, Int>) -> Dict<String, Int> = dict_put(d, 1, true)\nentry f\n");
    assert_eq!(e.iter().map(|d| d.code).collect::<Vec<_>>(), ["E-TYPE-ARG", "E-TYPE-ARG"]);
    assert_eq!((e[0].expected.as_deref(), e[1].expected.as_deref()), (Some("String"), Some("Int")));
    // dict_from の引数
    let e = errors("fn f(xs: List<Int>) -> Dict<Int, Int> = dict_from(xs)\nentry f\n");
    assert_eq!(e[0].code, "E-TYPE-DICT-FROM");
    assert_eq!(e[0].expected.as_deref(), Some("List<Pair<K, V>>"));
    let e = errors("fn f(d: Dict<Int, Int>) -> Dict<Int, Int> = dict_from(d)\nentry f\n");
    assert!(e[0].repair.as_ref().unwrap().constraint.contains("already a Dict"));
    // 辞書をリストとして使う
    let e = errors("fn f(d: Dict<Int, Int>) -> List<Int> = map(d, |e| 1)\nentry f\n");
    assert_eq!(e[0].code, "E-TYPE-HOF-LIST");
    assert!(e[0].repair.as_ref().unwrap().constraint.contains("dict_entries(d)"));
    let e = errors("fn f(d: Dict<Int, Int>) -> Int = length(d)\nentry f\n");
    assert_eq!(e[0].code, "E-TYPE-EXPECTED-LIST");
    // Dict と List<Pair<K, V>> は別の型
    let e = errors("fn f(d: Dict<Int, Int>) -> List<Pair<Int, Int>> = d\nentry f\n");
    assert_eq!(e[0].code, "E-TYPE-RETURN");
    assert!(e[0].repair.as_ref().unwrap().constraint.contains("dict_entries(d)"));
    let e = errors("fn g(d: Dict<Int, Int>) -> Int = 0\nfn f(xs: List<Pair<Int, Int>>) -> Int = g(xs)\nentry f\n");
    assert_eq!(e[0].code, "E-TYPE-ARG");
    assert!(e[0].repair.as_ref().unwrap().constraint.contains("dict_from(xs)"));
    // 引数の数
    assert_eq!(codes("fn f(d: Dict<Int, Int>) -> Dict<Int, Int> = dict_put(d, 1)\nentry f\n"), ["E-ARITY-BUILTIN"]);
    // 型引数のない dict()、() のない dict<K, V>
    let e = errors("fn f(u: Unit) -> Dict<Int, Int> = dict()\nentry f\n");
    assert_eq!(e[0].code, "E-PARSE-EXPECTED-TOKEN");
    assert!(e[0].repair.as_ref().unwrap().constraint.contains("dict<K, V>()"));
    let e = errors("fn f(u: Unit) -> Dict<Int, Int> = dict<Int, Int>\nentry f\n");
    assert_eq!(e[0].code, "E-PARSE-EXPECTED-TOKEN");
    assert!(e[0].repair.as_ref().unwrap().constraint.contains("dict<String, Int>()"));
    // 型の Dict は型引数を二つ取る
    assert_eq!(codes("fn f(d: Dict<Int>) -> Int = 0\nentry f\n"), ["E-PARSE-EXPECTED-TOKEN"]);
    // `Dict` だけ（型引数なし）はレコード型の名前として読む
    assert_eq!(codes("fn f(d: Dict) -> Int = 0\nentry f\n"), ["E-RECORD-UNKNOWN-TYPE"]);
    // どの拒否も検証済み部品との食い違いにはならない
    for src in [
        "fn f(u: Unit) -> Int = dict_size(dict<Int, Int>)\nentry f\n",
        "fn dict(x: Int) -> Int = x\nentry dict\n",
        "fn f(x: Int) -> Int = add(dict_size(y), x)\nentry f\n",
    ] {
        assert!(!codes(src).contains(&"E-INTERNAL-VERIFIED-MISMATCH"), "{src}: {:?}", codes(src));
    }
}
