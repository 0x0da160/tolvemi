//! v1.10 のユーザー定義の型引数（総称の関数・レコード型・直和型。差分仕様 §1〜§3）。

use std::io::Write;
use std::process::{Command, Stdio};
use tlvm::api::*;
use tlvm::formatter::format_program;
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
    let path = std::env::temp_dir().join(format!("tlvm-generics-{}-{n}.{ext}", std::process::id()));
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

fn errors(src: &str) -> Vec<tlvm::diagnostics::Diagnostic> {
    compiled(src).errors().to_vec()
}

fn codes(src: &str) -> Vec<&'static str> {
    errors(src).iter().map(|d| d.code).collect()
}

/// 唯一の error（コードを確かめ、修復ヒントがあることも確かめる）。
fn only_error(src: &str, code: &str) -> tlvm::diagnostics::Diagnostic {
    let es = errors(src);
    assert_eq!(
        es.iter().map(|d| d.code).collect::<Vec<_>>(),
        [code],
        "{es:?}"
    );
    let d = es[0].clone();
    assert!(d.repair.is_some(), "{d:?}");
    d
}

fn accepted(src: &str) -> tlvm::checker::TypedProgram {
    match compiled(src) {
        CompileResult::Accepted { program, .. } => program,
        r => panic!("rejected: {:?}", r.errors()),
    }
}

/// 単相化した後の、検証済み部品へ渡すソース。
fn lowered(src: &str) -> String {
    let p = match parse_source(src.as_bytes(), &StaticProfile::default()) {
        Parsed::Program(p) => p,
        _ => panic!("parse"),
    };
    let px = expand(&p).unwrap();
    let (o, pm) = tlvm::generics::check(&px, src.len(), &StaticProfile::default());
    assert!(o.typed.is_some(), "{:?}", o.diagnostics);
    format_program(&tlvm::dict::erase(&lower(&tlvm::hof::lower(&pm, &o.hof))))
}

const FIRST: &str = "fn first<T>(xs: List<T>) -> Option<T> = match uncons(xs) { some(p) => some(fst(p)), none => none<T>() }\n";

// ---------------------------------------------------------------- 意味

#[test]
fn generic_function_at_three_types() {
    let src = format!(
        "{FIRST}fn main(xs: List<Int>) -> Pair<Option<Int>, Pair<Option<String>, Option<Pair<Bool, Char>>>> =
  pair(first(xs), pair(first(list<String>(\"a\", \"b\")), first(list<Pair<Bool, Char>>(pair(true, 'c')))))
entry main
"
    );
    assert_eq!(run(&src, "[3, 4]"), r#"[3,["a",[true,"c"]]]"#);
    assert_eq!(run(&src, "[]"), r#"[null,["a",[true,"c"]]]"#);
    // 三つの型ごとに一つずつ具体化され、総称の宣言そのものは残らない
    let low = lowered(&src);
    assert_eq!(low.matches("fn first_g").count(), 3, "{low}");
    assert!(
        !low.contains("fn first<") && !low.contains("fn first("),
        "{low}"
    );
    assert!(!low.contains("<T>"), "{low}");
}

#[test]
fn generic_calls_generic_and_multiple_params() {
    let src = format!(
        "{FIRST}fn swap<A, B>(p: Pair<A, B>) -> Pair<B, A> = pair(snd(p), fst(p))
fn twice<T>(x: T) -> List<T> = list<T>(x, x)
fn head_twice<T>(xs: List<T>) -> List<T> = match first(xs) {{ some(v) => twice(v), none => list<T>() }}
fn main(xs: List<Int>) -> Pair<List<Int>, Pair<String, Int>> = pair(head_twice(xs), swap(pair(length(xs), \"n\")))
entry main
"
    );
    assert_eq!(run(&src, "[7, 8]"), r#"[[7,7],["n",2]]"#);
    assert_eq!(run(&src, "[]"), r#"[[],["n",0]]"#);
    // 同じ型引数の組は一度だけ具体化する（first<Int> は head_twice<Int> からと main からで一つ）
    let src2 = format!(
        "{FIRST}fn g<T>(xs: List<T>) -> Option<T> = first(xs)\nfn main(xs: List<Int>) -> Pair<Option<Int>, Option<Int>> = pair(first(xs), g(xs))\nentry main\n"
    );
    assert_eq!(lowered(&src2).matches("fn first_g").count(), 1);
    assert_eq!(run(&src2, "[5]"), "[5,5]");
}

#[test]
fn explicit_and_inferred_type_arguments_agree() {
    let src = format!(
        "{FIRST}fn main(xs: List<Int>) -> Pair<Option<Int>, Option<Int>> = pair(first(xs), first<Int>(xs))\nentry main\n"
    );
    assert_eq!(run(&src, "[9]"), "[9,9]");
    // 戻り型だけに現れる型引数は明示する
    let src = "fn empty<T>(n: Int) -> List<T> = list<T>()\nfn main(x: Int) -> Int = add(length(empty<String>(x)), length(cons(x, empty<Int>(x))))\nentry main\n";
    assert_eq!(run(src, "3"), "1");
}

#[test]
fn eq_and_hof_dict_loop_inside_generic_bodies() {
    let src = "fn dedup<T>(xs: List<T>) -> List<T> = reverse(fold(xs, list<T>(), |acc, x| if(contains(acc, x), acc, cons(x, acc))))
fn count<T>(xs: List<T>) -> Dict<T, Int> = fold(xs, dict<T, Int>(), |d, x| dict_put(d, x, add(match_option(dict_get(d, x), 0, |c| c), 1)))
fn pairs<T>(xs: List<T>) -> List<Pair<T, T>> = map(filter(xs, |x| not_last(xs, x)), |x| pair(x, x))
fn not_last<T>(xs: List<T>, x: T) -> Bool = match uncons(reverse(xs)) { some(p) => if(eq(fst(p), x), false, true), none => false }
fn repeat<T>(x: T, n: Int) -> List<T> = match_option(loop(list<T>(), add(n, 1), |s| if(lt(length(s), n), some(cons(x, s)), none<List<T>>())), list<T>(), |s| s)
fn main(xs: List<Int>) -> Pair<List<Int>, Pair<List<String>, Pair<Dict<String, Int>, Pair<List<Pair<Int, Int>>, String>>>> =
  let ws = list<String>(\"a\", \"b\", \"a\") in
  pair(dedup(xs), pair(dedup(ws), pair(count(ws), pair(pairs(xs), repeat('z', 3)))))
entry main
";
    assert_eq!(
        run(src, "[1, 2, 1, 3]"),
        r#"[[1,2,3],[["a","b"],[[["a",2],["b",1]],[[[1,1],[2,2],[1,1]],"zzz"]]]]"#
    );
}

#[test]
fn rec_generic_function() {
    let src = "rec fn len<T>(xs: List<T>) -> Int = match uncons(xs) { none => 0, some(p) => add(1, len(snd(p))) }
rec fn even<T>(xs: List<T>) -> Bool = match uncons(xs) { none => true, some(p) => odd(snd(p)) }
rec fn odd<T>(xs: List<T>) -> Bool = match uncons(xs) { none => false, some(p) => even(snd(p)) }
fn main(xs: List<Int>) -> Pair<Int, Pair<Int, Bool>> = pair(len(xs), pair(len(list<String>(\"a\")), even(xs)))
entry main
";
    assert_eq!(run(src, "[1, 2, 3]"), "[3,[1,false]]");
    let p = accepted(src);
    assert!(!p.terminates());
    // rec の印は具体化した関数に移る
    let low = lowered(src);
    assert_eq!(low.matches("rec fn len_g").count(), 2, "{low}");
    assert!(
        low.contains("rec fn even_g") && low.contains("rec fn odd_g"),
        "{low}"
    );
    // 使われない rec の総称の関数はコードにならない（停止の保証は残る）
    let src = "rec fn len<T>(xs: List<T>) -> Int = match uncons(xs) { none => 0, some(p) => add(1, len(snd(p))) }\nfn main(x: Int) -> Int = x\nentry main\n";
    let p = accepted(src);
    assert!(p.terminates());
    assert!(!lowered(src).contains("len"));
}

#[test]
fn generic_record_and_sum_with_match() {
    let src = "type Box<T> = { value: T, n: Int }
type Tree<T> = Leaf | Node(T, Int)
type Either<A, B> = Left(A) | Right(B)
fn unbox<T>(b: Box<T>) -> T = b.value
fn weight<T>(t: Tree<T>) -> Int = match t { Leaf => 0, Node(_, n) => n }
fn label<T>(t: Tree<T>, d: T) -> T = match t { Leaf => d, Node(x, _) => x }
fn grow<T>(x: T) -> Tree<T> = Node(x, 1)
fn side<A, B>(e: Either<A, B>) -> Int = match e { Left(_) => 0, Right(_) => 1 }
fn main(xs: List<Int>) -> List<Int> =
  let b = Box { value: \"s\", n: 2 } in
  let t = Node(\"hi\", 3) in
  let l = Leaf<Bool>() in
  let e = Left<Int, String>(7) in
  list<Int>(length(unbox(b)), weight(t), weight(l), length(label(t, \"zz\")), weight(grow(xs)), side(e), side(Right<Int, Int>(1)),
    match e { Left(n) => n, Right(_) => 0 }, unbox(Box { value: 4, n: 0 }))
entry main
";
    assert_eq!(run(src, "[1]"), "[1,3,0,2,1,0,1,7,4]");
}

#[test]
fn generic_types_in_entry_io_and_display() {
    let src = "type Box<T> = { value: T, n: Int }
type Opt<T> = No | Yes(Box<T>)
fn wrap<T>(x: T) -> Opt<T> = Yes(Box { value: x, n: 1 })
fn get<T>(o: Opt<T>, d: T) -> T = match o { No => d, Yes(b) => b.value }
fn main(o: Opt<String>) -> Pair<Opt<Int>, String> = pair(wrap(3), get(o, \"none\"))
entry main
";
    let p = accepted(src);
    assert_eq!(p.input_type.to_string(), "Opt<String>");
    assert_eq!(p.output_type.to_string(), "Pair<Opt<Int>, String>");
    assert_eq!(
        run(src, r#"{"Yes": [{"value": "hi", "n": 2}]}"#),
        r#"[{"Yes":[{"value":3,"n":1}]},"hi"]"#
    );
    assert_eq!(
        run(src, r#"{"No": []}"#),
        r#"[{"Yes":[{"value":3,"n":1}]},"none"]"#
    );
    // 診断の型の表示も型引数つき
    let d = errors("type Box<T> = { v: T, w: Int }\nfn g(b: Box<Int>) -> Int = b.w\nfn main(x: Int) -> Int = g(Box { v: \"s\", w: 1 })\nentry main\n");
    assert_eq!(d[0].code, "E-TYPE-ARG");
    assert_eq!(d[0].expected.as_deref(), Some("Box<Int>"));
}

#[test]
fn mangled_names_do_not_clash() {
    // 利用者が first_g1 という名前を使っていても、具体化した関数は別の名前になる
    let src = format!(
        "{FIRST}fn first_g1(x: Int) -> Int = add(x, 100)\nfn main(xs: List<Int>) -> Pair<Option<Int>, Int> = let first_g12 = 1 in pair(first(xs), first_g1(first_g12))\nentry main\n"
    );
    assert_eq!(run(&src, "[2]"), "[2,101]");
    let low = lowered(&src);
    assert_eq!(low.matches("fn first_g1(").count(), 1, "{low}");
}

#[test]
fn generic_constructor_helper_function_is_hidden() {
    // 型引数を推論する構築のために作る関数は、使われなくても警告を出さない
    let src = "type Tree<T> = Leaf | Node(T, Int)\nfn main(x: Int) -> Int = match Node(x, 2) { Leaf => 0, Node(a, b) => add(a, b) }\nentry main\n";
    let r = compiled(src);
    assert!(
        r.errors().is_empty() && r.warnings().is_empty(),
        "{:?} {:?}",
        r.errors(),
        r.warnings()
    );
    assert_eq!(run(src, "5"), "7");
}

// ---------------------------------------------------------------- 診断

#[test]
fn arithmetic_on_type_parameter_is_an_error_with_hint() {
    let d = only_error(
        "fn f<T>(x: T) -> Int = add(x, 1)\nfn main(x: Int) -> Int = f(x)\nentry main\n",
        "E-TYPE-ARG",
    );
    assert_eq!(
        (d.expected.as_deref(), d.actual.as_deref()),
        (Some("Int"), Some("T"))
    );
    assert!(d
        .repair
        .unwrap()
        .constraint
        .contains("T is a type parameter of f"));
    // eq は全ての型に使える
    assert!(codes(
        "fn f<T>(x: T, y: T) -> Bool = eq(x, y)\nfn main(x: Int) -> Bool = f(x, x)\nentry main\n"
    )
    .is_empty());
}

#[test]
fn unknown_type_parameter() {
    let d = only_error(
        "fn f<T>(xs: List<U>) -> Int = length(xs)\nfn main(x: Int) -> Int = x\nentry main\n",
        "E-TYPE-GENERIC-UNKNOWN-PARAM",
    );
    assert_eq!(d.actual.as_deref(), Some("U"));
    assert!(d.repair.unwrap().constraint.contains("<T, U>"));
    // 型引数を宣言し忘れた（総称でない関数で T を使った）
    let d = only_error(
        "fn f(xs: List<T>) -> Int = length(xs)\nfn main(x: Int) -> Int = x\nentry main\n",
        "E-TYPE-GENERIC-UNKNOWN-PARAM",
    );
    let r = d.repair.unwrap();
    assert_eq!(r.target_span, (4, 4));
    assert!(r.constraint.contains("'<T>'"), "{}", r.constraint);
    // 本体の型の位置も
    assert_eq!(
        codes("fn f<T>(x: T) -> Int = length(list<V>())\nfn main(x: Int) -> Int = x\nentry main\n"),
        ["E-TYPE-GENERIC-UNKNOWN-PARAM"]
    );
}

#[test]
fn declaration_errors() {
    only_error(
        "fn f<T, T>(x: T) -> T = x\nfn main(x: Int) -> Int = f(x)\nentry main\n",
        "E-TYPE-GENERIC-DUPLICATE-PARAM",
    );
    only_error("type Pt = { x: Int }\nfn id<Pt>(x: Pt) -> Pt = x\nfn main(x: Int) -> Int = x\nentry main\n", "E-TYPE-GENERIC-PARAM-CONFLICT");
    only_error(
        "type Box<T> = { v: Int }\nfn main(x: Int) -> Int = x\nentry main\n",
        "E-TYPE-GENERIC-UNUSED-PARAM",
    );
    only_error(
        "type Box<T> = { v: T }\nfn main(x: Box<Int, Int>) -> Int = 1\nentry main\n",
        "E-TYPE-GENERIC-ARITY",
    );
    only_error(
        "type Box<T> = { v: T }\nfn main(x: Box) -> Int = 1\nentry main\n",
        "E-TYPE-GENERIC-ARITY",
    );
    only_error(
        "type Pt = { x: Int }\nfn main(x: Pt<Int>) -> Int = 1\nentry main\n",
        "E-TYPE-GENERIC-ARITY",
    );
    only_error(
        "fn f<T>(x: T<Int>) -> Int = 1\nfn main(x: Int) -> Int = x\nentry main\n",
        "E-TYPE-GENERIC-ARITY",
    );
    // 型引数の名前は大文字で始まる
    let es = errors("fn f<t>(x: t) -> Int = 1\nfn main(x: Int) -> Int = x\nentry main\n");
    assert_eq!(es[0].code, "E-PARSE-EXPECTED-IDENT");
    assert!(es[0]
        .repair
        .as_ref()
        .unwrap()
        .constraint
        .contains("uppercase"));
}

#[test]
fn call_errors() {
    // 型引数の数
    let d = only_error("fn mk<T>(x: Int) -> List<T> = list<T>()\nfn main(x: Int) -> Int = length(mk<Int, Int>(x))\nentry main\n", "E-TYPE-GENERIC-ARITY");
    assert_eq!(
        (d.expected.as_deref(), d.actual.as_deref()),
        (Some("1 type arguments"), Some("2 type arguments"))
    );
    only_error(
        "fn g(x: Int) -> Int = x\nfn main(x: Int) -> Int = g<Int>(x)\nentry main\n",
        "E-TYPE-GENERIC-ARITY",
    );
    // 推論できない（戻り型だけに現れる）
    let d = only_error("fn mk<T>(x: Int) -> List<T> = list<T>()\nfn main(x: Int) -> Int = length(mk(x))\nentry main\n", "E-TYPE-GENERIC-INFER");
    let r = d.repair.unwrap();
    assert!(r.constraint.contains("mk<T>(...)"), "{}", r.constraint);
    // 推論した型が引数ごとに違う
    let d = only_error("fn p<T>(a: T, b: T) -> List<T> = list<T>(a, b)\nfn main(x: Int) -> Int = length(p(x, \"s\"))\nentry main\n", "E-TYPE-GENERIC-MISMATCH");
    assert_eq!(
        (d.expected.as_deref(), d.actual.as_deref()),
        (Some("Int"), Some("String"))
    );
    // 明示した型引数と引数の型が違う
    let d = only_error("fn p<T>(a: T, b: T) -> List<T> = list<T>(a, b)\nfn main(x: Int) -> Int = length(p<Int>(x, \"s\"))\nentry main\n", "E-TYPE-ARG");
    assert_eq!(
        (d.expected.as_deref(), d.actual.as_deref()),
        (Some("Int"), Some("String"))
    );
    // 形が合わない（List<T> に Int）
    let d = only_error(&format!("{FIRST}fn main(x: Int) -> Int = match first(x) {{ some(v) => v, none => 0 }}\nentry main\n"), "E-TYPE-ARG");
    assert_eq!(
        (d.expected.as_deref(), d.actual.as_deref()),
        (Some("List<T>"), Some("Int"))
    );
    // 戻り値の型を取り違えた
    let d = only_error(
        "fn id<T>(x: T) -> T = x\nfn main(x: Int) -> String = id(x)\nentry main\n",
        "E-TYPE-RETURN",
    );
    assert_eq!(
        (d.expected.as_deref(), d.actual.as_deref()),
        (Some("String"), Some("Int"))
    );
}

#[test]
fn generic_constructor_errors() {
    let h = "type Tree<T> = Leaf | Node(T, Int)\n";
    // 中身のない構築子は型引数を書く
    let d = only_error(
        &format!(
            "{h}fn main(x: Int) -> Int = match Leaf {{ Leaf => 0, Node(n, _) => n }}\nentry main\n"
        ),
        "E-TYPE-GENERIC-INFER",
    );
    assert!(d.repair.unwrap().constraint.contains("Leaf<Int>()"));
    only_error(&format!("{h}fn main(x: Int) -> Int = match Leaf<Int, Int>() {{ Leaf => 0, Node(n, _) => n }}\nentry main\n"), "E-TYPE-GENERIC-ARITY");
    // 中身の型が型引数と食い違う
    let h2 = "type Two<T> = Both(T, T)\n";
    only_error(
        &format!(
            "{h2}fn main(x: Int) -> Int = match Both(x, \"s\") {{ Both(a, _) => a }}\nentry main\n"
        ),
        "E-TYPE-GENERIC-MISMATCH",
    );
    // 型引数を書いた構築子は書いた型で検査する
    only_error(&format!("{h}fn main(x: Int) -> Int = match Node<String>(x, 1) {{ Leaf => 0, Node(_, n) => n }}\nentry main\n"), "E-TYPE-ARG");
    // 推論できない型引数（Either の B）
    let h3 = "type Either<A, B> = Left(A) | Right(B)\n";
    let d = only_error(&format!("{h3}fn main(x: Int) -> Int = match Left(x) {{ Left(n) => n, Right(_) => 0 }}\nentry main\n"), "E-TYPE-GENERIC-INFER");
    assert!(d.repair.unwrap().constraint.contains("Left<Int, B>"));
    // `Leaf<Int>` には `()` が要る（none<T>() と同じ）
    let es = errors(&format!("{h}fn main(x: Int) -> Int = match Leaf<Int> {{ Leaf => 0, Node(n, _) => n }}\nentry main\n"));
    assert_eq!(es[0].code, "E-PARSE-EXPECTED-TOKEN");
    assert!(es[0]
        .repair
        .as_ref()
        .unwrap()
        .constraint
        .contains("Leaf<Int>()"));
}

#[test]
fn polymorphic_recursion_is_rejected() {
    let d = only_error(
        "rec fn g<T>(x: T, n: Int) -> Int = if(lt(n, 1), 0, g(list<T>(x), sub(n, 1)))\nfn main(x: Int) -> Int = g(x, 3)\nentry main\n",
        "E-TYPE-GENERIC-INFINITE",
    );
    assert_eq!(d.actual.as_deref(), Some("g<List<T>>"));
    // 相互再帰を通っても
    only_error(
        "rec fn a<T>(x: T, n: Int) -> Int = if(lt(n, 1), 0, b(some(x), sub(n, 1)))\nrec fn b<U>(y: U, n: Int) -> Int = a(y, n)\nfn main(x: Int) -> Int = a(x, 3)\nentry main\n",
        "E-TYPE-GENERIC-INFINITE",
    );
    // 型引数が大きくならない再帰と、再帰の外で大きくなるだけの呼び出しはよい
    let ok = "rec fn a<T>(x: T, n: Int) -> Int = if(lt(n, 1), 0, b(x, sub(n, 1)))\nrec fn b<U>(y: U, n: Int) -> Int = a(y, n)\nfn c<T>(x: T) -> Int = a(some(x), 2)\nfn main(x: Int) -> Int = add(c(x), a(x, 1))\nentry main\n";
    assert_eq!(run(ok, "1"), "0");
    // 型引数が大きくなるが、具体的な型で閉じる再帰はよい
    let ok = "rec fn f<T>(x: T, n: Int) -> Int = if(lt(n, 1), 0, g(list<T>(x), sub(n, 1)))\nrec fn g<U>(y: U, n: Int) -> Int = f(1, n)\nfn main(x: Int) -> Int = f(x, 3)\nentry main\n";
    assert_eq!(run(ok, "1"), "0");
}

#[test]
fn instantiation_limit() {
    // 型引数が関数ごとに倍になる（再帰なし）：型の大きさの上限で止める
    let mut src = String::from("fn f1<T>(x: T) -> Int = 1\n");
    for i in 2..=10 {
        src.push_str(&format!(
            "fn f{i}<T>(x: T) -> Int = f{}(pair(x, x))\n",
            i - 1
        ));
    }
    src.push_str("fn main(x: Int) -> Int = f10(x)\nentry main\n");
    let es = errors(&src);
    assert_eq!(
        es.iter().map(|d| d.code).collect::<Vec<_>>(),
        ["E-LIMIT-STATIC-GENERIC-INSTANCES"]
    );
    assert_eq!(es[0].phase, "semantic-limits");
    // 具体化の数の上限（型の違う 300 個の呼び出し）
    let vals = ["1", "true", "unit", "'c'", "\"s\""];
    let mut calls = vec![];
    'outer: for a in vals {
        for b in vals {
            for c in vals {
                for d in vals {
                    calls.push(format!("k(pair(pair({a}, {b}), pair({c}, {d})))"));
                    if calls.len() == 300 {
                        break 'outer;
                    }
                }
            }
        }
    }
    let src = format!(
        "fn k<T>(x: T) -> Int = 1\nfn main(x: Int) -> Int = length(list<Int>({}))\nentry main\n",
        calls.join(", ")
    );
    let es = errors(&src);
    assert_eq!(
        es.iter().map(|d| d.code).collect::<Vec<_>>(),
        ["E-LIMIT-STATIC-GENERIC-INSTANCES"]
    );
    assert!(
        es[0]
            .actual
            .as_deref()
            .unwrap()
            .contains("more than 256 instances"),
        "{es:?}"
    );
    // 上限以内なら受理する
    let src = format!(
        "fn k<T>(x: T) -> Int = 1\nfn main(x: Int) -> Int = length(list<Int>({}))\nentry main\n",
        calls[..200].join(", ")
    );
    assert_eq!(run(&src, "0"), "200");
}

#[test]
fn entry_cannot_be_generic() {
    let d = only_error("fn id<T>(x: T) -> T = x\nentry id\n", "E-ENTRY-GENERIC");
    assert_eq!(d.actual.as_deref(), Some("id<T>"));
}

#[test]
fn unused_generic_function_warns_and_produces_no_code() {
    let src = format!("{FIRST}fn main(x: Int) -> Int = x\nentry main\n");
    let r = compiled(&src);
    assert!(r.errors().is_empty());
    assert_eq!(
        r.warnings().iter().map(|d| d.code).collect::<Vec<_>>(),
        ["W-UNUSED-FUNCTION"]
    );
    assert!(!lowered(&src).contains("first"));
    // 使われない総称の関数も本体は検査する
    assert_eq!(
        codes("fn f<T>(x: T) -> T = add(x, 1)\nfn main(x: Int) -> Int = x\nentry main\n"),
        ["E-TYPE-ARG"]
    );
}

// ---------------------------------------------------------------- 道具

const TOOL: &str = "type Tree<T> = Leaf | Node(T, Int)
fn first<T>(xs: List<T>) -> Option<T> = match uncons(xs) { some(p) => some(fst(p)), none => none<T>() }
fn mk<T>(n: Int) -> List<T> = list<T>()
fn main(xs: List<Int>) -> Pair<Option<Int>, Int> = pair(first<Int>(xs), add(length(mk<String>(1)), match Leaf<Bool>() { Leaf => 0, Node(_, n) => n }))
entry main
";

#[test]
fn fmt_round_trip() {
    with_file(TOOL, "tlvm", |p| {
        let (code, out, err) = tlvm(&["fmt", p]);
        assert_eq!(code, 0, "{err}");
        assert_eq!(out, TOOL);
        with_file(&out, "tlvm", |q| {
            let (_, again, _) = tlvm(&["fmt", q]);
            assert_eq!(again, out);
        });
    });
    let src = "type Box<A, B> = { a: A, b: Pair<A, B> }\nfn f<K, V>(b: Box<K, V>, d: Dict<K, V>) -> Box<K, V> = b\nfn main(x: Int) -> Int = x\nentry main\n";
    with_file(src, "tlvm", |p| {
        let (_, out, _) = tlvm(&["fmt", p]);
        assert_eq!(out, src);
    });
}

#[test]
fn ast_round_trip() {
    let src = "fn first<T>(xs: List<T>) -> Option<T> = match_option(uncons(xs), none<T>(), |p| some(fst(p)))
fn mk<T>(n: Int) -> List<T> = list<T>()
fn main(xs: List<Int>) -> Pair<Option<Int>, Int> = pair(first(xs), length(mk<String>(1)))
entry main
";
    with_file(src, "tlvm", |p| {
        let (code, json, err) = tlvm(&["ast", p]);
        assert_eq!(code, 0, "{err}");
        assert!(json.contains(r#""type_params":["T"]"#), "{json}");
        assert!(json.contains(r#"{"tag":"param","name":"T"}"#), "{json}");
        assert!(json.contains(r#""type_args":[{"tag":"string"}]"#), "{json}");
        with_file(json.trim_end(), "json", |j| {
            let (code, out, err) = tlvm(&["run", j, "[4]", "--plain"]);
            assert_eq!(code, 0, "{err}");
            assert_eq!(out.trim_end(), "[4,0]");
            let (_, again, _) = tlvm(&["ast", j]);
            assert_eq!(again, json);
            let (_, src2, _) = tlvm(&["fmt", j]);
            assert_eq!(src2, src);
        });
    });
    // 直和型を含むものは展開して出す（構築子の関数も総称の関数として出る）
    with_file(TOOL, "tlvm", |p| {
        let (code, json, err) = tlvm(&["ast", p]);
        assert_eq!(code, 0, "{err}");
        with_file(json.trim_end(), "json", |j| {
            let (code, out, err) = tlvm(&["run", j, "[4]", "--plain"]);
            assert_eq!(code, 0, "{err}");
            assert_eq!(out.trim_end(), "[4,0]");
        });
    });
    // AST の型引数の検査
    let bad = r#"{"codec":"ast_codec_v1","declarations":[{"tag":"fn","name":"f","params":[{"name":"x","type":{"tag":"param","name":"U"}}],"return_type":{"tag":"int"},"body":{"tag":"int","value":"1"},"type_params":["T"]},{"tag":"fn","name":"main","params":[{"name":"x","type":{"tag":"int"}}],"return_type":{"tag":"int"},"body":{"tag":"var","name":"x"}},{"tag":"entry","name":"main"}]}"#;
    match compile_ast(
        bad.as_bytes(),
        &StaticProfile::default(),
        &AstTransportProfile::default(),
    ) {
        AstCompile::Result(r) => assert_eq!(r.errors()[0].code, "E-TYPE-GENERIC-UNKNOWN-PARAM"),
        _ => panic!("transport"),
    }
    let bad = bad.replace(r#""type_params":["T"]"#, r#""type_params":["t"]"#);
    match compile_ast(
        bad.as_bytes(),
        &StaticProfile::default(),
        &AstTransportProfile::default(),
    ) {
        AstCompile::AstInvalid(d) => assert_eq!(d[0].code, "E-AST-IDENTIFIER"),
        _ => panic!("schema"),
    }
}

#[test]
fn tlvm_test_and_exec() {
    let src = format!("{FIRST}fn main(xs: List<Int>) -> Option<Int> = first(xs)\nentry main\n");
    let cases = r#"[{"name": "a", "input": [3, 1], "expected": 3}, {"name": "empty", "input": [], "expected": null}]"#;
    with_file(&src, "tlvm", |p| {
        with_file(cases, "json", |c| {
            let (code, out, err) = tlvm(&["test", p, c]);
            assert_eq!(code, 0, "{out}{err}");
            assert_eq!(out.matches(r#""result":"pass""#).count(), 2, "{out}");
        })
    });
    // 一行目と最後の行（同じ総称の関数を String と List<String> で）
    let src = "fn first<T>(xs: List<T>) -> Option<T> = match uncons(xs) { some(p) => some(fst(p)), none => none<T>() }
fn last<T>(xs: List<T>) -> Option<T> = first(reverse(xs))
fn lines(s: String) -> List<String> =
  let r = fold(s, pair(list<String>(), \"\"), |st, c| if(eq(c, '\\n'), pair(cons(reverse(snd(st)), fst(st)), \"\"), pair(fst(st), cons(c, snd(st))))) in
  reverse(if(eq(snd(r), \"\"), fst(r), cons(reverse(snd(r)), fst(r))))
fn solve(s: String) -> String =
  let ls = lines(s) in
  concat(match_option(first(ls), \"\", |l| l), concat(\"|\", match_option(last(ls), \"\", |l| l)))
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
        c.stdin
            .take()
            .unwrap()
            .write_all(b"alpha\nbeta\ngamma\n")
            .unwrap();
        let o = c.wait_with_output().unwrap();
        assert_eq!(String::from_utf8(o.stdout).unwrap(), "alpha|gamma");
    });
}

#[test]
fn check_output_types() {
    with_file(TOOL, "tlvm", |p| {
        let (code, out, _) = tlvm(&["check", p]);
        assert_eq!(code, 0);
        assert!(out.contains(r#""input_type":"List<Int>","output_type":"Pair<Option<Int>, Int>","terminates":true"#), "{out}");
    });
}
