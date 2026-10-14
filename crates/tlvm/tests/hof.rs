//! v1.5 の関数を渡す組み込み `map`・`filter`・`any`・`all`・`find`・`sort_by`（差分仕様 §1〜§3）。

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
    let path = std::env::temp_dir().join(format!("tlvm-hof-{}-{n}.{ext}", std::process::id()));
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

fn compiled(src: &str) -> CompileResult {
    match compile(src.as_bytes(), &StaticProfile::default()) {
        SourceCompile::Result(r) => r,
        _ => panic!("boundary"),
    }
}

fn codes(src: &str) -> Vec<&'static str> {
    compiled(src).errors().iter().map(|d| d.code).collect()
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
    format_program(&lower(&tlvm::hof::lower(&px, &o.hof)))
}

// ---------------------------------------------------------------- 型と評価

const ALL_SIX: &str = "fn solve(xs: List<Int>) -> Pair<List<Int>, Pair<List<Int>, Pair<Bool, Pair<Bool, Pair<Option<Int>, List<Int>>>>>> =
  pair(map(xs, |x| mul(x, 2)),
  pair(filter(xs, |x| lt(0, x)),
  pair(any(xs, |x| eq(x, 3)),
  pair(all(xs, |x| lt(-10, x)),
  pair(find(xs, |x| lt(5, x)),
  sort_by(xs, |x| neg(x)))))))
entry solve
";

#[test]
fn six_forms_evaluate() {
    assert_eq!(run(ALL_SIX, "[3, -1, 7, 2, 9, 7]"), "[[6,-2,14,4,18,14],[[3,7,2,9,7],[true,[true,[7,[9,7,7,3,2,-1]]]]]]");
    // 空のリスト：any は false、all は true、find は none
    assert_eq!(run(ALL_SIX, "[]"), "[[],[[],[false,[true,[null,[]]]]]]");
    assert_eq!(run(ALL_SIX, "[-20]"), "[[-40],[[],[false,[false,[null,[-20]]]]]]");
    let p = accepted(ALL_SIX);
    assert_eq!(p.output_type.to_string(), "Pair<List<Int>, Pair<List<Int>, Pair<Bool, Pair<Bool, Pair<Option<Int>, List<Int>>>>>>");
}

#[test]
fn result_types() {
    let ty = |body: &str, t: &str| {
        let p = accepted(&format!("fn f(xs: List<Int>) -> {t} = {body} entry f"));
        assert_eq!(p.output_type.to_string(), t);
    };
    ty("map(xs, |x| pair(x, eq(x, 0)))", "List<Pair<Int, Bool>>");
    ty("map(xs, |x| to_string(x))", "List<String>");
    ty("filter(xs, |x| true)", "List<Int>");
    ty("any(xs, |x| true)", "Bool");
    ty("all(xs, |x| true)", "Bool");
    ty("find(xs, |x| true)", "Option<Int>");
    ty("sort_by(xs, |x| x)", "List<Int>");
    // 本体は外側の変数を参照できる
    assert_eq!(run("fn f(p: Pair<Int, List<Int>>) -> List<Int> = map(snd(p), |x| add(x, fst(p))) entry f", "[10, [1, 2]]"), "[11,12]");
}

#[test]
fn strings() {
    // String は List<Char>：map で文字ごとに、filter は String のまま
    let src = r#"fn solve(s: String) -> Pair<List<Int>, Pair<String, Pair<Bool, Pair<Option<Char>, String>>>> =
  pair(map(s, |c| code(c)),
  pair(filter(s, |c| if(eq(c, ' '), false, true)),
  pair(all(s, |c| le(code('a'), code(c))),
  pair(find(s, |c| eq(c, 'b')),
  sort_by(s, |c| code(c))))))
entry solve
"#;
    assert_eq!(run(src, r#""cab a""#), r#"[[99,97,98,32,97],["caba",[false,["b"," aabc"]]]]"#);
    assert_eq!(run(src, r#""""#), r#"[[],["",[true,[null,""]]]]"#);
    // 文字列のリスト：長さで並べ、大文字にした単語
    let words = r#"fn upper(c: Char) -> Char =
  if(le(code('a'), code(c)), match_option(char(sub(code(c), 32)), c, |u| u), c)
fn solve(ws: List<String>) -> List<String> = map(sort_by(ws, |w| length(w)), |w| map(w, |c| upper(c)))
entry solve
"#;
    assert_eq!(run(words, r#"["ccc", "a", "bb", "dd"]"#), r#"["A","BB","DD","CCC"]"#);
}

#[test]
fn sort_by_is_stable() {
    // 鍵が等しい要素は元の順（名前で確かめる）。降順は鍵を neg にする
    let src = "fn solve(xs: List<Pair<String, Int>>) -> Pair<List<String>, List<String>> =
  pair(map(sort_by(xs, |p| snd(p)), |p| fst(p)), map(sort_by(xs, |p| neg(snd(p))), |p| fst(p)))
entry solve
";
    let input = r#"[["a", 2], ["b", 1], ["c", 2], ["d", 1], ["e", 3], ["f", 2]]"#;
    assert_eq!(run(src, input), r#"[["b","d","a","c","f","e"],["e","a","c","f","b","d"]]"#);
    // すでに整列済み、逆順、全部同じ鍵
    let ints = "fn f(xs: List<Int>) -> List<Int> = sort_by(xs, |x| x) entry f";
    assert_eq!(run(ints, "[1, 2, 3, 4]"), "[1,2,3,4]");
    assert_eq!(run(ints, "[4, 3, 2, 1]"), "[1,2,3,4]");
    assert_eq!(run(ints, "[5, -5, 0, 5, -5]"), "[-5,-5,0,5,5]");
    let same = "fn f(xs: List<Int>) -> List<Int> = sort_by(xs, |x| 0) entry f";
    assert_eq!(run(same, "[3, 1, 2]"), "[3,1,2]");
}

#[test]
fn short_circuit() {
    // 答えが決まった後の要素では本体を評価しない：評価すれば range(0, 10^12) で資源を使い切る
    let src = "fn big(x: Int) -> Bool = lt(0, length(range(0, x)))
fn solve(xs: List<Int>) -> Pair<Bool, Pair<Bool, Option<Int>>> =
  pair(any(xs, |x| big(x)), pair(all(xs, |x| eq(big(x), false)), find(xs, |x| big(x))))
entry solve
";
    assert_eq!(run(src, "[1, 1000000000000]"), "[true,[false,1]]");
    // 本体を評価し続ければ資源を使い切る（上の結果が評価の省略によることの確認）
    with_file("fn f(xs: List<Int>) -> List<Bool> = map(xs, |x| lt(0, length(range(0, x)))) entry f", "tlvm", |p| {
        let (code, _, err) = tlvm(&["run", p, "[1, 1000000000000]", "--plain"]);
        assert_eq!(code, 2, "{err}");
        assert!(err.contains("ResourceExhausted"), "{err}");
    });
    // 評価の順：要素の順に本体を評価し、最初に見つかったもの
    assert_eq!(run("fn f(xs: List<Int>) -> Option<Int> = find(xs, |x| lt(2, x)) entry f", "[1, 5, 3, 9]"), "5");
}

#[test]
fn nesting_and_names() {
    // 入れ子：binder は相異なる名前。外側の binder を内側の本体から参照できる
    let src = "fn solve(xs: List<Int>) -> List<List<Int>> =
  map(filter(xs, |x| any(xs, |y| lt(x, y))), |x| sort_by(map(xs, |y| mul(x, y)), |z| neg(z)))
entry solve
";
    assert_eq!(run(src, "[1, 3, 2]"), "[[3,2,1],[6,4,2]]");
    // 兄弟の形では同じ binder の名前を使える。sort_by の鍵の中の入れ子の形（鍵は二度書き換え後に現れる）
    let sib = "fn solve(xs: List<List<Int>>) -> Pair<List<Int>, List<List<Int>>> =
  pair(map(xs, |x| length(x)), sort_by(xs, |x| length(filter(x, |v| lt(0, v)))))
entry solve
";
    assert_eq!(run(sib, "[[1, 2, -3], [5], [-1, -2], [4, 4, 4]]"), "[[3,1,2,3],[[-1,-2],[5],[1,2,-3],[4,4,4]]]");
    // 書き換えで導入する名前（hof1 など）は、プログラム中の名前と重ならない
    let clash = "fn hof3(hof1: List<Int>) -> List<Int> = let hof2 = 1 in sort_by(hof1, |hof4| sub(hof4, hof2)) entry hof3";
    assert_eq!(run(clash, "[3, 1, 2]"), "[1,2,3]");
    // 6 語は文脈キーワード：変数・引数・binder・field の名前に使える（直後が `(` のときだけ特殊形式）
    let soft = "type R = { map: Int, all: Bool }
fn solve(map: List<Int>) -> Pair<List<Int>, R> =
  let filter = 2 in
  let any = map(map, |sort_by| mul(sort_by, filter)) in
  pair(any, R { map: length(any), all: all(any, |find| lt(0, find)) })
entry solve
";
    assert_eq!(run(soft, "[1, 2]"), r#"[[2,4],{"map":2,"all":true}]"#);
}

#[test]
fn records_and_sums() {
    // ラムダの本体でレコードの構築・field の参照、構築子、match、入れ子の map を使う
    let src = "type Item = { name: String, qty: Int }
type Shape = Circle(Int) | Rect(Int, Int) | Empty
fn area(s: Shape) -> Int = match s { Circle(r) => mul(3, mul(r, r)), Rect(w, h) => mul(w, h), Empty => 0 }
fn solve(items: List<Item>) -> Pair<List<Shape>, Pair<Option<Item>, List<Item>>> =
  let shapes = map(items, |it| match parse_int(it.name) { some(n) => Rect(n, it.qty), none => if(lt(0, it.qty), Circle(it.qty), Empty) }) in
  pair(filter(shapes, |s| lt(0, area(s))),
  pair(find(items, |it| any(map(range(0, it.qty), |i| i), |i| eq(i, 2))),
  sort_by(map(items, |it| Item { qty: neg(it.qty), ..it }), |it| it.qty)))
entry solve
";
    let input = r#"[{"name": "4", "qty": 2}, {"name": "x", "qty": 0}, {"name": "y", "qty": 3}, {"name": "z", "qty": 2}]"#;
    assert_eq!(
        run(src, input),
        r#"[[{"Rect":[4,2]},{"Circle":[3]},{"Circle":[2]}],[{"name":"y","qty":3},[{"name":"y","qty":-3},{"name":"4","qty":-2},{"name":"z","qty":-2},{"name":"x","qty":0}]]]"#
    );
    // match の枝の中、sum の中身を binder にした map
    let m = "type T = Many(List<Int>) | One(Int)
fn f(t: T) -> List<Int> = match t { Many(xs) => map(xs, |x| add(x, 1)), One(x) => list<Int>(x) }
entry f
";
    assert_eq!(run(m, r#"{"Many": [[1, 2]]}"#), "[2,3]");
    assert_eq!(run(m, r#"{"One": [7]}"#), "[7]");
    // 構築子は binder の名前に使えない
    assert_eq!(codes("type T = A | B fn f(xs: List<Int>) -> List<Int> = map(xs, |A| A) entry f"), ["E-SUM-NAME-CONFLICT"]);
}

#[test]
fn lowering_uses_fold_and_passes_verified_formatter() {
    let text = lowered(ALL_SIX);
    for w in ["map(", "filter(", "any(", "all(", "find(", "sort_by("] {
        assert!(!text.contains(w), "{w} in {text}");
    }
    assert!(text.contains("reverse(fold(xs, list<Int>(), |hof1, x| cons(mul(x, 2), hof1)))"), "{text}");
    assert!(text.contains("fold(xs, false, |hof3, x| if(hof3, true, eq(x, 3)))"), "{text}");
    assert!(text.contains("fold(xs, true, |hof4, x| if(hof4, lt(-10, x), false))"), "{text}");
    assert!(text.contains("fold(xs, none<Int>(), |hof5, x| match_option(hof5, if(lt(5, x), some(x), none<Int>()), |hof6| some(hof6)))"), "{text}");
    // sort_by：鍵は let x = 要素 in 本体（ユーザーの binder はシャドーされない）。本体はソースに一度だけ現れる
    assert!(text.contains("let hof11 = let x = hof10 in neg(x) in match_option(fst(hof9), pair(some(hof11), snd(hof9)), |hof12|"), "{text}");
    assert_eq!(text.matches("neg(x)").count(), 1, "{text}");
    assert_eq!(canonical(&text, &StaticProfile::default()).as_deref(), Some(text.as_str()));
    // 鍵の中に sort_by を入れ子にしても、書き換え後のソースは入れ子の深さに比例する大きさ
    let mut key = "0".to_string();
    for i in (1..=12).rev() {
        key = format!("length(sort_by(xs, |x{i}| add(x{i}, {key})))");
    }
    let deep = format!("fn f(xs: List<Int>) -> List<Int> = sort_by(xs, |x0| add(x0, {key})) entry f");
    let text = lowered(&deep);
    assert!(text.len() < 40 * deep.len(), "{} vs {}", text.len(), deep.len());
    assert_eq!(canonical(&text, &StaticProfile::default()).as_deref(), Some(text.as_str()));
    assert_eq!(run(&deep, "[]"), "[]");
    // レコード・直和型と一緒でも、書き換え後のソースは検証済み formatter の正準形
    let mixed = "type P = { a: Int, b: Int }
type S = X(Int) | Y
fn f(xs: List<P>) -> List<S> = map(sort_by(xs, |p| p.b), |p| if(lt(0, p.a), X(p.a), Y))
entry f
";
    let text = lowered(mixed);
    assert!(text.contains("fold(") && !text.contains("sort_by("), "{text}");
    assert_eq!(canonical(&text, &StaticProfile::default()).as_deref(), Some(text.as_str()));
}

// ---------------------------------------------------------------- 診断

#[test]
fn diagnostics() {
    let c = |body: &str| codes(&format!("fn f(xs: List<Int>, n: Int) -> List<Int> = {body} entry g fn g(x: List<Int>) -> List<Int> = f(x, 0)"));
    assert_eq!(c("map(n, |x| x)"), ["E-TYPE-HOF-LIST"]);
    assert_eq!(c("filter(some(xs), |x| true)"), ["E-TYPE-HOF-LIST"]);
    assert_eq!(c("filter(xs, |x| x)"), ["E-TYPE-HOF-BODY"]);
    assert_eq!(c("sort_by(xs, |x| lt(x, 0))"), ["E-TYPE-HOF-BODY"]);
    assert_eq!(c("if(any(xs, |x| 1), xs, xs)"), ["E-TYPE-HOF-BODY"]);
    assert_eq!(c("if(all(xs, |x| x), xs, xs)"), ["E-TYPE-HOF-BODY"]);
    assert_eq!(c("match_option(find(xs, |x| unit), xs, |y| xs)"), ["E-TYPE-HOF-BODY"]);
    assert_eq!(c("map(xs, |x| eq(x, 1))"), ["E-TYPE-RETURN"]);
    // binder：外側の名前をシャドーできず、本体の外では見えない
    assert_eq!(c("map(xs, |n| n)"), ["E-NAME-SHADOW"]);
    assert_eq!(c("map(xs, |x| map(xs, |x| x))"), ["E-NAME-SHADOW"]);
    assert_eq!(c("concat(map(xs, |x| x), list<Int>(x))"), ["E-NAME-UNBOUND-VARIABLE"]);
    // 第 2 引数がラムダでない
    assert_eq!(c("map(xs, double)"), ["E-PARSE-EXPECTED-LAMBDA"]);
    assert_eq!(c("map(xs, add(x, 1))"), ["E-PARSE-EXPECTED-LAMBDA"]);
    assert_eq!(c("map(xs)"), ["E-PARSE-EXPECTED-LAMBDA"]);
    assert_eq!(c("sort_by(xs, |a, b| lt(a, b))"), ["E-PARSE-EXPECTED-LAMBDA"]);
    assert_eq!(c("filter(xs, || true)"), ["E-PARSE-EXPECTED-LAMBDA"]);
    assert_eq!(c("map(xs, |x| x, 1)"), ["E-PARSE-EXPECTED-TOKEN"]);
    // 関数名と entry の名前には使えない（検証済み部品との食い違いにはしない）
    assert_eq!(codes("fn map(x: Int) -> Int = x entry map"), ["E-PARSE-EXPECTED-IDENT", "E-PARSE-EXPECTED-IDENT"]);
    assert_eq!(codes("fn f(x: Int) -> Int = find(x, 1) entry f"), ["E-PARSE-EXPECTED-LAMBDA"]);
    // 名前の候補に 6 語も出す
    let d = compiled("fn f(xs: List<Int>) -> List<Int> = mapp(xs) entry f").errors()[0].clone();
    assert_eq!(d.code, "E-NAME-UNKNOWN-FUNCTION");
    assert!(d.repair.as_ref().unwrap().constraint.contains("map"), "{d:?}");
}

#[test]
fn lambda_repair_hints() {
    let first = |body: &str| {
        let src = format!("fn double(x: Int) -> Int = mul(x, 2)\nfn f(xs: List<Int>) -> List<Int> = {body}\nentry f\n");
        let d = compiled(&src).errors()[0].clone();
        assert_eq!(d.code, "E-PARSE-EXPECTED-LAMBDA");
        assert_eq!(d.phase, "parse");
        let r = d.repair.clone().expect("repair");
        (d, r)
    };
    let (d, r) = first("map(xs, double)");
    assert_eq!(d.expected.as_deref(), Some("|x| e"));
    assert_eq!(d.actual.as_deref(), Some("double"));
    assert_eq!(r.kind, "replace_expression");
    assert!(r.constraint.starts_with("|x| double(x)"), "{}", r.constraint);
    let (_, r) = first("map(xs, mul(x, 2))");
    assert_eq!(r.kind, "insert_text");
    assert!(r.constraint.contains("'|x| '"), "{}", r.constraint);
    let (d, r) = first("map(xs)");
    assert_eq!(d.actual.as_deref(), Some(")"));
    assert_eq!((r.kind, r.target_span.0, r.target_span.1), ("insert_text", d.span.0, d.span.0));
    let (d, r) = first("sort_by(xs, |a, b| lt(a, b))");
    assert_eq!(d.actual.as_deref(), Some(","));
    assert!(r.constraint.contains("exactly one binder") && r.constraint.contains("fold"), "{}", r.constraint);
    // AST API には修復ヒントを付けない（AST にはこの誤りを書けない）
}

#[test]
fn ast_codec_tags() {
    let src = "fn f(any: List<Int>) -> Pair<List<Int>, Option<Int>> = pair(sort_by(any, |all| neg(all)), find(any, |x| lt(1, x))) entry f";
    with_file(src, "tlvm", |p| {
        let (code, ast, err) = tlvm(&["ast", p]);
        assert_eq!(code, 0, "{err}");
        // 6 語の tag。文脈キーワードの変数名は AST transport の識別子に付け替える
        assert!(ast.contains(r#"{"tag":"sort_by","list":{"tag":"var","name":"any_kw"},"binder":"all_kw","body":"#), "{ast}");
        assert!(ast.contains(r#""tag":"find""#), "{ast}");
        with_file(ast.trim_end(), "json", |j| {
            let (code, out, err) = tlvm(&["run", j, "[3, 1, 2]", "--plain"]);
            assert_eq!(code, 0, "{err}");
            assert_eq!(out.trim_end(), "[[3,2,1],3]");
            // AST から整形したソースも同じ
            let (code, fmt, _) = tlvm(&["fmt", j]);
            assert_eq!(code, 0);
            assert!(fmt.contains("sort_by(any_kw, |all_kw| neg(all_kw))"), "{fmt}");
        });
    });
    let ast = |body: &str| {
        format!(
            r#"{{"codec":"ast_codec_v1","declarations":[{{"tag":"fn","name":"f","params":[{{"name":"xs","type":{{"tag":"list","element":{{"tag":"int"}}}}}}],"return_type":{{"tag":"list","element":{{"tag":"int"}}}},"body":{body}}},{{"tag":"entry","name":"f"}}]}}"#
        )
    };
    let ast_codes = |body: &str| match compile_ast(ast(body).as_bytes(), &StaticProfile::default(), &AstTransportProfile::default()) {
        AstCompile::Result(r) => r.errors().iter().map(|d| d.code).collect::<Vec<_>>(),
        AstCompile::AstInvalid(d) => d.iter().map(|d| d.code).collect(),
        AstCompile::AstBoundaryFailure => vec!["boundary"],
    };
    let x = r#"{"tag":"var","name":"x"}"#;
    let xs = r#"{"tag":"var","name":"xs"}"#;
    assert!(ast_codes(&format!(r#"{{"tag":"filter","list":{xs},"binder":"x","body":{{"tag":"call","callee":"lt","args":[{{"tag":"int","value":"0"}},{x}],"type_args":[]}}}}"#)).is_empty());
    assert_eq!(ast_codes(&format!(r#"{{"tag":"map","list":{xs},"body":{x}}}"#)), ["E-AST-MISSING-FIELD"]);
    assert_eq!(ast_codes(&format!(r#"{{"tag":"map","list":{xs},"binder":"map","body":{x}}}"#)), ["E-AST-IDENTIFIER"]);
    assert_eq!(ast_codes(&format!(r#"{{"tag":"map","list":{xs},"binder":"x","init":{x},"body":{x}}}"#)), ["E-AST-UNKNOWN-FIELD"]);
    assert_eq!(ast_codes(&format!(r#"{{"tag":"call","callee":"map","args":[{xs}],"type_args":[]}}"#)), ["E-AST-IDENTIFIER"]);
    assert_eq!(ast_codes(&format!(r#"{{"tag":"sort_by","list":{xs},"binder":"x","body":{{"tag":"bool","value":true}}}}"#)), ["E-TYPE-HOF-BODY"]);
}

// ---------------------------------------------------------------- tlvm fmt・test・exec

#[test]
fn fmt_round_trip() {
    let src = "type P = { name: String, score: Int }
// 50 点以上の名前を点の高い順に
fn top(ps: List<P>) -> List<String> = map(sort_by(filter(ps, |p|
    le(50, p.score)), |p| neg(p.score)), |p| p.name)
entry top
";
    let canon = "type P = { name: String, score: Int }
fn top(ps: List<P>) -> List<String> = map(sort_by(filter(ps, |p| le(50, p.score)), |p| neg(p.score)), |p| p.name)
entry top
";
    with_file(src, "tlvm", |p| {
        let (code, out, err) = tlvm(&["fmt", p]);
        assert_eq!(code, 0, "{err}");
        assert_eq!(out, canon);
    });
    with_file(canon, "tlvm", |p| {
        let (code, out, _) = tlvm(&["fmt", p]);
        assert_eq!(code, 0);
        assert_eq!(out, canon);
    });
    // 文脈キーワードだけのプログラム（map などを変数名に使い、呼ばない）は従来どおり検証済み formatter
    let plain = "fn f(map: Int) -> Int = add(map, 1)\nentry f\n";
    with_file(plain, "tlvm", |p| {
        let (code, out, err) = tlvm(&["fmt", p]);
        assert_eq!(code, 0, "{err}");
        assert_eq!(out, plain);
    });
}

#[test]
fn cli_test_and_exec() {
    let src = "fn f(xs: List<Int>) -> List<Int> = filter(xs, |x| eq(mod(x, 2), some(0))) entry f";
    with_file(src, "tlvm", |p| {
        let cases = r#"[{"name": "evens", "input": [1, 2, 3, 4], "expected": [2, 4]}, {"name": "none", "input": [], "expected": []}]"#;
        with_file(cases, "json", |c| {
            let (code, out, err) = tlvm(&["test", p, c]);
            assert_eq!(code, 0, "{out}{err}");
            assert!(out.contains(r#"{"passed":2,"failed":0}"#), "{out}");
        });
    });
    // exec：標準入力の行のうち空でないものを、長さの順に
    let lines = r#"type S = { lines: List<String>, cur: String }
fn solve(text: String) -> String =
  let s = fold(text, S { lines: list<String>(), cur: "" }, |s, c|
    if(eq(c, '\n'), S { lines: cons(reverse(s.cur), s.lines), cur: "" }, S { cur: cons(c, s.cur), ..s })) in
  let ls = filter(reverse(s.lines), |l| any(l, |c| if(eq(c, ' '), false, true))) in
  fold(sort_by(ls, |l| length(l)), "", |out, l| concat(out, concat(l, "\n")))
entry solve
"#;
    with_file(lines, "tlvm", |p| {
        let mut c = Command::new(env!("CARGO_BIN_EXE_tlvm"))
            .args(["exec", p])
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::piped())
            .spawn()
            .unwrap();
        c.stdin.take().unwrap().write_all(b"ccc\n  \na\nbb\nzz\n").unwrap();
        let o = c.wait_with_output().unwrap();
        assert_eq!(o.status.code(), Some(0), "{}", String::from_utf8_lossy(&o.stderr));
        assert_eq!(String::from_utf8(o.stdout).unwrap(), "a\nbb\nzz\nccc\n");
    });
}
