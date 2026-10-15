//! v1.14 の再帰する直和型（差分仕様 `spec/lptl-v1.14`）：書き換え（List<Int> の符号化、構築と match）、
//! 項の型の制限、match の網羅性と枝の誤り、実行（plain JSON の整数の列）と `tlvm exec` の拒否。

use std::io::Write;
use std::process::{Command, Stdio};
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
    let path = std::env::temp_dir().join(format!("tlvm-rec-{}-{n}.{ext}", std::process::id()));
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

fn accepted(src: &str) -> tlvm::checker::TypedProgram {
    match compiled(src) {
        CompileResult::Accepted { program, .. } => program,
        r => panic!("rejected: {:?}", r.errors()),
    }
}

/// 終了コード、標準出力、標準エラー
fn exec(src: &str, stdin: &[u8]) -> (i32, String, String) {
    with_file(src, "tlvm", |p| {
        let mut c = Command::new(env!("CARGO_BIN_EXE_tlvm"))
            .arg("exec")
            .arg(p)
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::piped())
            .spawn()
            .unwrap();
        c.stdin.take().unwrap().write_all(stdin).unwrap();
        let o = c.wait_with_output().unwrap();
        (
            o.status.code().unwrap(),
            String::from_utf8(o.stdout).unwrap(),
            String::from_utf8(o.stderr).unwrap(),
        )
    })
}

const TREE: &str = "type Tree = Leaf | Node(Tree, Int, Tree)\n";

#[test]
fn values_are_integer_lists_and_run_on_plain_input() {
    // 木 Node(Leaf, 3, Node(Leaf, 4, Leaf)) の符号化は [1, 1,0, 1,3, 7, 1,1,0, 1,4, 1,0]
    let src = r#"type Tree = Leaf | Node(Tree, Int, Tree)
rec fn size(t: Tree) -> Int = match t { Leaf => 0, Node(l, v, r) => add(size(l), add(v, size(r))) }
fn build(n: Int) -> Tree = Node(Leaf, n, Node(Leaf, add(n, 1), Leaf))
fn solve(t: Tree) -> Pair<Int, Tree> = pair(size(t), build(size(t)))
entry solve
"#;
    assert_eq!(
        run(src, "[1,1,0,1,3,7,1,1,0,1,4,1,0]"),
        "[7,[1,1,0,1,7,7,1,1,0,1,8,1,0]]"
    );
    // 引数のない構築子は [番号]、Int の項は [1, 値]、再帰する項は [長さ] ++ 中身
    let leaf = format!("{TREE}fn solve(n: Int) -> Tree = Node(Leaf, n, Leaf)\nentry solve\n");
    assert_eq!(run(&leaf, "3"), "[1,1,0,1,3,1,0]");
    let empty = format!("{TREE}fn solve(n: Int) -> Tree = Leaf\nentry solve\n");
    assert_eq!(run(&empty, "3"), "[0]");
}

#[test]
fn bool_fields_and_equality_and_wildcards() {
    let flag = r#"type Flag = Off | On(Bool, Flag)
rec fn n_on(f: Flag) -> Int = match f { Off => 0, On(b, rest) => add(if(b, 1, 0), n_on(rest)) }
entry n_on
"#;
    // On(true, On(false, Off))
    assert_eq!(run(flag, "[1,1,1,5,1,1,0,1,0]"), "1");
    let eq = format!("{TREE}fn mk(n: Int) -> Tree = Node(Leaf, n, Node(Leaf, 2, Leaf))\nfn solve(n: Int) -> Pair<Bool, Bool> = pair(eq(mk(n), mk(n)), eq(mk(n), mk(add(n, 1))))\nentry solve\n");
    assert_eq!(run(&eq, "3"), "[true,false]");
    let wild = format!("{TREE}fn firstval(t: Tree) -> Int = match t {{ Node(_, v, _) => v, _ => 0 }}\nfn solve(n: Int) -> Pair<Int, Int> = pair(firstval(Node(Leaf, n, Leaf)), firstval(Leaf))\nentry solve\n");
    assert_eq!(run(&wild, "9"), "[9,0]");
}

#[test]
fn nested_matches_records_dicts_and_generics() {
    let nested = format!(
        "{TREE}rec fn sum(t: Tree) -> Int = match t {{ Leaf => 0, Node(l, v, r) => add(sum(l), add(v, sum(r))) }}\n\
         fn leafsum(t: Tree) -> Int = match t {{ Node(l, v, r) => match l {{ Leaf => v, Node(a, w, b) => add(v, w) }}, Leaf => 0 }}\n\
         fn solve(n: Int) -> Pair<Int, Int> = pair(sum(Node(Node(Leaf, n, Leaf), 10, Node(Leaf, add(n, 100), Node(Leaf, 1000, Leaf)))), leafsum(Node(Node(Leaf, n, Leaf), 10, Leaf)))\n\
         entry solve\n"
    );
    assert_eq!(run(&nested, "5"), "[1120,15]");
    let record = format!(
        "{TREE}type Pack = {{ t: Tree, k: Int }}\nfn solve(n: Int) -> Int = let p = Pack {{ t: Node(Leaf, n, Leaf), k: 7 }} in match p.t {{ Leaf => p.k, Node(l, v, r) => add(v, p.k) }}\nentry solve\n"
    );
    assert_eq!(run(&record, "4"), "11");
    let dict = format!(
        "{TREE}fn solve(n: Int) -> Int = dict_size(dict_put(dict_put(dict<String, Tree>(), \"a\", Node(Leaf, n, Leaf)), \"b\", Leaf))\nentry solve\n"
    );
    assert_eq!(run(&dict, "4"), "2");
    let generic = format!("{TREE}fn ident<T>(x: T) -> T = x\nfn solve(n: Int) -> Int = match ident(Node(Leaf, n, Leaf)) {{ Leaf => 0, Node(l, v, r) => v }}\nentry solve\n");
    assert_eq!(run(&generic, "6"), "6");
}

#[test]
fn mutual_recursion_and_termination_flag() {
    let mutual = r#"type A = X(B) | Ea
type B = Y(A, Int) | Eb
rec fn count(a: A) -> Int = match a { Ea => 0, X(b) => count_b(b) }
rec fn count_b(b: B) -> Int = match b { Eb => 0, Y(a, n) => add(n, count(a)) }
entry count
"#;
    // rec の印のある関数を含むので、停止は保証されない
    assert!(accepted(mutual).program.has_rec());
    let rec_only = format!("{TREE}rec fn size(t: Tree) -> Int = match t {{ Leaf => 0, Node(l, v, r) => size(l) }}\nentry size\n");
    assert!(codes(&rec_only).is_empty());
    // rec のない再帰は、循環の呼び出しとして拒否される
    assert!(!codes(&format!("{TREE}fn size(t: Tree) -> Int = match t {{ Leaf => 0, Node(l, v, r) => size(l) }}\nentry size\n")).is_empty());
}

#[test]
fn warnings_are_not_emitted_for_generated_functions() {
    let src = format!("{TREE}fn f(x: Int) -> Int = x\nentry f\n");
    let r = compiled(&src);
    assert!(r.errors().is_empty());
    assert!(r.warnings().is_empty(), "{:?}", r.warnings());
}

#[test]
fn constructor_fields_must_be_encodable() {
    let string =
        format!("type Tree = Leaf | Name(String, Tree)\nfn f(x: Int) -> Int = 1\nentry f\n");
    assert_eq!(codes(&string), ["E-REC-FIELD-TYPE"]);
    let list =
        format!("type Tree = Leaf | Many(List<Int>, Tree)\nfn f(x: Int) -> Int = 1\nentry f\n");
    assert_eq!(codes(&list), ["E-REC-FIELD-TYPE"]);
    let other_sum = "type Color = Red | Green\ntype Tree = Leaf | Paint(Color, Tree)\nfn f(x: Int) -> Int = 1\nentry f\n";
    assert_eq!(codes(other_sum), ["E-REC-FIELD-TYPE"]);
    let through_record = "type S = X(R) | Y\ntype R = { s: S }\nfn f(x: Int) -> Int = 1\nentry f\n";
    assert_eq!(codes(through_record), ["E-REC-FIELD-TYPE"]);
}

#[test]
fn generic_recursive_types_are_rejected() {
    let src = "type Tree<T> = Leaf | Node(Tree<T>, T, Tree<T>)\nfn f(x: Int) -> Int = 1\nentry f\n";
    assert_eq!(codes(src), ["E-REC-TYPE-PARAM"]);
}

#[test]
fn names_and_arms_are_checked_as_for_sums() {
    let dup_type = format!("{TREE}type Tree = {{ a: Int }}\nfn f(x: Int) -> Int = 1\nentry f\n");
    assert_eq!(codes(&dup_type), ["E-RECORD-DUPLICATE-TYPE"]);
    let fn_name = format!("{TREE}fn Leaf(x: Int) -> Int = x\nfn f(x: Int) -> Int = 1\nentry f\n");
    assert_eq!(codes(&fn_name), ["E-SUM-NAME-CONFLICT"]);
    let binder = format!("{TREE}fn f(x: Int) -> Int = let Leaf = x in x\nentry f\n");
    assert_eq!(codes(&binder), ["E-SUM-NAME-CONFLICT"]);
    let missing = format!("{TREE}fn f(t: Tree) -> Int = match t {{ Leaf => 0 }}\nentry f\n");
    assert_eq!(codes(&missing), ["E-MATCH-MISSING"]);
    let dup = format!("{TREE}fn f(t: Tree) -> Int = match t {{ Leaf => 0, Leaf => 1, Node(l, v, r) => v }}\nentry f\n");
    assert_eq!(codes(&dup), ["E-MATCH-DUPLICATE"]);
    let unreachable = format!("{TREE}fn f(t: Tree) -> Int = match t {{ Leaf => 0, _ => 1, Node(l, v, r) => v }}\nentry f\n");
    assert_eq!(codes(&unreachable), ["E-MATCH-UNREACHABLE"]);
    let arity =
        format!("{TREE}fn f(t: Tree) -> Int = match t {{ Leaf => 0, Node(l, v) => v }}\nentry f\n");
    assert_eq!(codes(&arity), ["E-SUM-CTOR-ARITY"]);
    let call_arity = format!("{TREE}fn f(x: Int) -> Tree = Node(Leaf, x)\nentry f\n");
    assert_eq!(codes(&call_arity), ["E-SUM-CTOR-ARITY"]);
    let nullary = format!("{TREE}fn f(x: Int) -> Tree = Leaf(x)\nentry f\n");
    assert_eq!(codes(&nullary), ["E-SUM-CTOR-ARITY"]);
    let unknown =
        format!("{TREE}fn f(t: Tree) -> Int = match t {{ Leaf => 0, Foo(x) => x }}\nentry f\n");
    assert_eq!(codes(&unknown), ["E-SUM-UNKNOWN-CTOR"]);
    let mixed = format!("{TREE}type Opt2 = Some2(Int) | None2\nfn f(t: Tree) -> Int = match t {{ Leaf => 0, Some2(x) => x, _ => 1 }}\nentry f\n");
    assert_eq!(codes(&mixed), ["E-MATCH-MIXED"]);
}

#[test]
fn type_errors_name_the_recursive_type() {
    let src = format!("{TREE}fn f(t: Tree) -> Int = add(t, 1)\nentry f\n");
    let r = compiled(&src);
    assert_eq!(
        r.errors().iter().map(|d| d.code).collect::<Vec<_>>(),
        ["E-TYPE-ARG"]
    );
    assert_eq!(r.errors()[0].actual.as_deref(), Some("Tree"));
}

#[test]
fn a_list_of_int_is_not_a_tree() {
    // 木の値を整数の列として渡すと、型検査で拒否される（v1.14 の既知の制限を解消した）
    let src = format!("{TREE}fn size(t: Tree) -> Int = match t {{ Leaf => 0, _ => 1 }}\nfn f(xs: List<Int>) -> Int = size(xs)\nentry f\n");
    let r = compiled(&src);
    assert_eq!(
        r.errors().iter().map(|d| d.code).collect::<Vec<_>>(),
        ["E-TYPE-ARG"]
    );
    assert_eq!(r.errors()[0].expected.as_deref(), Some("Tree"));
    assert_eq!(r.errors()[0].actual.as_deref(), Some("List<Int>"));
}

#[test]
fn different_recursive_types_do_not_mix() {
    let src = format!("{TREE}type Chain = End | Link(Chain)\nfn size(t: Tree) -> Int = match t {{ Leaf => 0, _ => 1 }}\nfn f(c: Chain) -> Int = size(c)\nentry f\n");
    let r = compiled(&src);
    assert_eq!(
        r.errors().iter().map(|d| d.code).collect::<Vec<_>>(),
        ["E-TYPE-ARG"]
    );
    assert_eq!(r.errors()[0].expected.as_deref(), Some("Tree"));
    assert_eq!(r.errors()[0].actual.as_deref(), Some("Chain"));
}

#[test]
fn types_of_the_same_shape_do_not_mix() {
    let src = "type A = X(A) | Ea\ntype B = Y(B) | Eb\nfn f(a: A) -> Int = match a { X(_) => 1, Ea => 0 }\nfn g(b: B) -> Int = f(b)\nentry g\n";
    let r = compiled(src);
    assert_eq!(
        r.errors().iter().map(|d| d.code).collect::<Vec<_>>(),
        ["E-TYPE-ARG"]
    );
    assert_eq!(r.errors()[0].expected.as_deref(), Some("A"));
    assert_eq!(r.errors()[0].actual.as_deref(), Some("B"));
}

#[test]
fn match_on_another_recursive_type_is_rejected() {
    let src = format!("{TREE}type Chain = End | Link(Chain)\nfn f(c: Chain) -> Int = match c {{ Leaf => 0, _ => 1 }}\nentry f\n");
    let r = compiled(&src);
    assert_eq!(
        r.errors().iter().map(|d| d.code).collect::<Vec<_>>(),
        ["E-TYPE-ARG"]
    );
    assert_eq!(r.errors()[0].expected.as_deref(), Some("Tree"));
    assert_eq!(r.errors()[0].actual.as_deref(), Some("Chain"));
}

#[test]
fn exec_rejects_a_recursive_entry_input_and_fmt_keeps_the_source_form() {
    let src = format!("{TREE}rec fn size(t: Tree) -> Int = match t {{ Leaf => 0, Node(l, v, r) => add(size(l), add(1, size(r))) }}\nentry size\n");
    let (code, out, err) = exec(&src, b"");
    assert_eq!(code, 64, "{out}{err}");
    assert!(
        format!("{out}{err}").contains("UnsupportedEntry"),
        "{out}{err}"
    );
    with_file(&src, "tlvm", |p| {
        let (code, out, err) = tlvm(&["fmt", p]);
        assert_eq!(code, 0, "{err}");
        assert!(
            out.contains("type Tree = Leaf | Node(Tree, Int, Tree)"),
            "{out}"
        );
        assert!(!out.contains("rec_at"), "{out}");
    });
}

/// 次の program を、印なしの写しに展開した全文（v1.14 差分 §2〜§3 の形と、補助関数の本体）。
const EXPANDED_TREE: &str = r"rec fn size(t: List<Int>) -> Int = let scrut = t in let tag = rec_at(scrut, 0) in if(eq(tag, 0), 0, let rest = rec_drop(scrut, 1) in let len = rec_at(rest, 0) in let data = rec_take(rec_drop(rest, 1), len) in let l = data in let rest2 = rec_drop(rest, add(1, len)) in let len2 = rec_at(rest2, 0) in let data2 = rec_take(rec_drop(rest2, 1), len2) in let v = rec_at(data2, 0) in let rest3 = rec_drop(rest2, add(1, len2)) in let len3 = rec_at(rest3, 0) in let data3 = rec_take(rec_drop(rest3, 1), len3) in let r = data3 in add(size(l), add(v, size(r))))
fn solve(n: Int) -> Int = size(node_new(list<Int>(0), n, list<Int>(0)))
entry solve
fn leaf_new() -> List<Int> = list<Int>(0)
fn node_new(node_arg1: List<Int>, node_arg2: Int, node_arg3: List<Int>) -> List<Int> = concat(list<Int>(1), concat(concat(list<Int>(length(node_arg1)), node_arg1), concat(list<Int>(1, node_arg2), concat(list<Int>(length(node_arg3)), node_arg3))))
fn rec_drop(xs: List<Int>, n2: Int) -> List<Int> = reverse(snd(fold(xs, pair(0, list<Int>()), |acc, item| if(lt(fst(acc), n2), pair(add(fst(acc), 1), snd(acc)), pair(fst(acc), cons(item, snd(acc)))))))
fn rec_take(xs2: List<Int>, n3: Int) -> List<Int> = reverse(snd(fold(xs2, pair(0, list<Int>()), |acc2, item2| if(lt(fst(acc2), n3), pair(add(fst(acc2), 1), cons(item2, snd(acc2))), acc2))))
fn rec_at(xs3: List<Int>, i: Int) -> Int = fold(rec_take(rec_drop(xs3, i), 1), 0, |acc3, item3| item3)
";

#[test]
fn recursive_helper_shapes_match_the_deltas() {
    // v1.14 差分 §2〜§3 で固定した形：構築子は `<名前>_new`、引数のない構築子は `list<Int>(k)`（`[k]`）の定数、
    // match は `rec_at(s, 0)` と比べる `if` の連鎖、項の取り出しは `rec_drop`・`rec_take`・`rec_at`。
    // 補助関数の本体は仕様に文字として書いていないので、この全文を fixture とする（§18.1c の O-2）。
    let src = "type Tree = Leaf | Node(Tree, Int, Tree)\nrec fn size(t: Tree) -> Int = match t { Leaf => 0, Node(l, v, r) => add(size(l), add(v, size(r))) }\nfn solve(n: Int) -> Int = size(Node(Leaf, n, Leaf))\nentry solve\n";
    let p = match parse_source(src.as_bytes(), &StaticProfile::default()) {
        Parsed::Program(p) => p,
        Parsed::Failed(_) => panic!("解析できない"),
    };
    let px = expand(&p).unwrap_or_else(|_| panic!("展開できない"));
    assert_eq!(tlvm::formatter::format_program(&px), EXPANDED_TREE);
}
