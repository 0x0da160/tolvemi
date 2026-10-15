//! v1.11 の import（差分仕様 §1〜§3）。ファイルの対応表の API（compile_files）と、一時ディレクトリでの CLI。

use std::collections::BTreeMap;
use std::io::Write;
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};
use tlvm::api::*;
use tlvm::diagnostics::Diagnostic;
use tlvm::profiles::*;

fn map(files: &[(&str, &str)]) -> BTreeMap<String, String> {
    files
        .iter()
        .map(|(k, v)| (k.to_string(), v.to_string()))
        .collect()
}

fn compiled_with(files: &[(&str, &str)], profile: &StaticProfile) -> CompileResult {
    match compile_files(files[0].0, &map(files), profile) {
        SourceCompile::Result(r) => r,
        SourceCompile::SourceBoundaryFailure => panic!("boundary"),
    }
}

/// 先頭の組が根。
fn compiled(files: &[(&str, &str)]) -> CompileResult {
    compiled_with(files, &StaticProfile::default())
}

fn errors(files: &[(&str, &str)]) -> Vec<Diagnostic> {
    compiled(files).errors().to_vec()
}

fn codes(files: &[(&str, &str)]) -> Vec<&'static str> {
    errors(files).iter().map(|d| d.code).collect()
}

/// 唯一の error（コードを確かめ、修復ヒントがあることも確かめる）。
fn only_error(files: &[(&str, &str)], code: &str) -> Diagnostic {
    let es = errors(files);
    assert_eq!(
        es.iter().map(|d| d.code).collect::<Vec<_>>(),
        [code],
        "{es:?}"
    );
    assert!(es[0].repair.is_some(), "{:?}", es[0]);
    es[0].clone()
}

fn accepted(files: &[(&str, &str)]) -> tlvm::checker::TypedProgram {
    match compiled(files) {
        CompileResult::Accepted { program, .. } => program,
        r => panic!("rejected: {:?}", r.errors()),
    }
}

/// plain JSON で実行した出力。
fn run(files: &[(&str, &str)], input: &str) -> String {
    let src = map(files);
    let p =
        tlvm::embed::Program::compile_files(files[0].0, &src).unwrap_or_else(|e| panic!("{e:?}"));
    p.run_json(input).unwrap()
}

/// span が指す、そのファイルの中の文字列。
fn spelled<'a>(files: &'a [(&str, &str)], d: &Diagnostic) -> &'a str {
    let f = d.file.as_deref().expect("file");
    let src = files.iter().find(|(k, _)| *k == f).unwrap().1;
    &src[d.span.0..d.span.1]
}

const SQ: &str = "fn sq(x: Int) -> Int = mul(x, x)\n";

#[test]
fn basic_import() {
    let files = [
        (
            "main.tlvm",
            "import \"sq.tlvm\"\nfn solve(x: Int) -> Int = add(sq(x), 1)\nentry solve\n",
        ),
        ("sq.tlvm", SQ),
    ];
    assert_eq!(run(&files, "7"), "50");
    assert_eq!(accepted(&files).entry, "solve");
}

#[test]
fn transitive_and_subdirectories() {
    // パスは import を書いたファイルのディレクトリから解決する。lib/b.tlvm の "c.tlvm" は lib/c.tlvm、"../top.tlvm" は top.tlvm
    let files = [
        (
            "main.tlvm",
            "import \"lib/b.tlvm\"\nfn solve(x: Int) -> Int = quad(x)\nentry solve\n",
        ),
        (
            "lib/b.tlvm",
            "import \"c.tlvm\"\nimport \"../top.tlvm\"\nfn quad(x: Int) -> Int = twice(sq(x))\n",
        ),
        ("lib/c.tlvm", "fn twice(x: Int) -> Int = add(x, x)\n"),
        ("top.tlvm", SQ),
    ];
    assert_eq!(run(&files, "3"), "18");
    // "./" と途中の ".." は正規化する
    let files = [
        (
            "main.tlvm",
            "import \"./lib/../sq.tlvm\"\nfn solve(x: Int) -> Int = sq(x)\nentry solve\n",
        ),
        ("sq.tlvm", SQ),
    ];
    assert_eq!(run(&files, "4"), "16");
}

#[test]
fn root_in_a_subdirectory_of_the_map() {
    let files = [
        (
            "app/main.tlvm",
            "import \"util/sq.tlvm\"\nfn solve(x: Int) -> Int = sq(x)\nentry solve\n",
        ),
        ("app/util/sq.tlvm", SQ),
    ];
    assert_eq!(run(&files, "5"), "25");
    // 根の key のディレクトリ（app）より上は指せない
    let files = [
        (
            "app/main.tlvm",
            "import \"../sq.tlvm\"\nfn solve(x: Int) -> Int = sq(x)\nentry solve\n",
        ),
        ("sq.tlvm", SQ),
    ];
    let d = only_error(&files, "E-IMPORT-PATH");
    assert_eq!(d.file.as_deref(), Some("app/main.tlvm"));
}

#[test]
fn diamond_loads_each_file_once() {
    // a と b がどちらも c を import しても c は一度だけ読む（定義が重複しない）
    let files = [
        ("main.tlvm", "import \"a.tlvm\"\nimport \"b.tlvm\"\nfn solve(x: Int) -> Int = add(fa(x), fb(x))\nentry solve\n"),
        ("a.tlvm", "import \"c.tlvm\"\nfn fa(x: Int) -> Int = sq(x)\n"),
        ("b.tlvm", "import \"c.tlvm\"\nimport \"a.tlvm\"\nfn fb(x: Int) -> Int = add(sq(x), fa(1))\n"),
        ("c.tlvm", SQ),
    ];
    assert_eq!(run(&files, "3"), "19");
    // 同じファイルを二度書いても同じ
    let files = [("main.tlvm", "import \"sq.tlvm\"\nimport \"sq.tlvm\"\nimport \"./sq.tlvm\"\nfn solve(x: Int) -> Int = sq(x)\nentry solve\n"), ("sq.tlvm", SQ)];
    assert_eq!(run(&files, "2"), "4");
}

#[test]
fn cycles() {
    let files = [
        (
            "main.tlvm",
            "import \"a.tlvm\"\nfn solve(x: Int) -> Int = fa(x)\nentry solve\n",
        ),
        ("a.tlvm", "import \"b.tlvm\"\nfn fa(x: Int) -> Int = x\n"),
        ("b.tlvm", "import \"a.tlvm\"\nfn fb(x: Int) -> Int = x\n"),
    ];
    let d = only_error(&files, "E-IMPORT-CYCLE");
    assert_eq!(d.actual.as_deref(), Some("a.tlvm -> b.tlvm -> a.tlvm"));
    assert_eq!(d.file.as_deref(), Some("b.tlvm"));
    assert_eq!(spelled(&files, &d), "import \"a.tlvm\"");
    assert_eq!(d.phase, "import");
    // 根に戻る循環と、自分自身の import
    let files = [
        (
            "main.tlvm",
            "import \"a.tlvm\"\nfn solve(x: Int) -> Int = x\nentry solve\n",
        ),
        ("a.tlvm", "import \"main.tlvm\"\n"),
    ];
    assert_eq!(
        only_error(&files, "E-IMPORT-CYCLE").actual.as_deref(),
        Some("main.tlvm -> a.tlvm -> main.tlvm")
    );
    let files = [(
        "main.tlvm",
        "import \"main.tlvm\"\nfn solve(x: Int) -> Int = x\nentry solve\n",
    )];
    assert_eq!(
        only_error(&files, "E-IMPORT-CYCLE").actual.as_deref(),
        Some("main.tlvm -> main.tlvm")
    );
}

#[test]
fn missing_file() {
    let files = [
        (
            "main.tlvm",
            "import \"lib/a.tlvm\"\nfn solve(x: Int) -> Int = x\nentry solve\n",
        ),
        ("lib/b.tlvm", SQ),
    ];
    let d = only_error(&files, "E-IMPORT-NOT-FOUND");
    assert_eq!(d.file.as_deref(), Some("main.tlvm"));
    assert_eq!(spelled(&files, &d), "\"lib/a.tlvm\"");
    assert!(
        d.actual.as_deref().unwrap().starts_with("lib/a.tlvm"),
        "{d:?}"
    );
    // 根が対応表にない
    match compile_files(
        "nope.tlvm",
        &map(&[("main.tlvm", SQ)]),
        &StaticProfile::default(),
    ) {
        SourceCompile::Result(r) => assert_eq!(r.errors()[0].code, "E-IMPORT-NOT-FOUND"),
        _ => panic!(),
    }
}

#[test]
fn conflicts_name_both_files() {
    let files = [
        (
            "main.tlvm",
            "import \"a.tlvm\"\nimport \"b.tlvm\"\nfn solve(x: Int) -> Int = sq(x)\nentry solve\n",
        ),
        ("a.tlvm", SQ),
        ("b.tlvm", "fn sq(x: Int) -> Int = add(x, x)\n"),
    ];
    let d = only_error(&files, "E-IMPORT-CONFLICT");
    assert_eq!(d.file.as_deref(), Some("b.tlvm"));
    assert_eq!(spelled(&files, &d), "sq");
    assert_eq!(
        d.actual.as_deref(),
        Some("sq: defined in a.tlvm and in b.tlvm")
    );
    // 根の定義と import した定義、型・構築子の名前も同じ名前空間
    let files = [
        (
            "main.tlvm",
            "import \"a.tlvm\"\nfn sq(x: Int) -> Int = x\nentry sq\n",
        ),
        ("a.tlvm", SQ),
    ];
    assert_eq!(
        only_error(&files, "E-IMPORT-CONFLICT").file.as_deref(),
        Some("main.tlvm")
    );
    let files = [
        (
            "main.tlvm",
            "import \"a.tlvm\"\ntype P = { x: Int }\nfn solve(x: Int) -> Int = x\nentry solve\n",
        ),
        ("a.tlvm", "type P = { y: Int }\n"),
    ];
    assert_eq!(codes(&files), ["E-IMPORT-CONFLICT"]);
    let files = [
        ("main.tlvm", "import \"a.tlvm\"\ntype T = Leaf | Node(Int)\nfn solve(x: Int) -> Int = x\nentry solve\n"),
        ("a.tlvm", "type U = Leaf | Other\n"),
    ];
    let d = only_error(&files, "E-IMPORT-CONFLICT");
    assert_eq!(spelled(&files, &d), "Leaf");
    // 一つのファイルの中の重複は今までどおりの診断（file 付き）
    let files = [
        (
            "main.tlvm",
            "import \"a.tlvm\"\nfn solve(x: Int) -> Int = x\nentry solve\n",
        ),
        (
            "a.tlvm",
            "fn g(x: Int) -> Int = x\nfn g(x: Int) -> Int = x\n",
        ),
    ];
    let es = errors(&files);
    assert_eq!(
        es.iter().map(|d| d.code).collect::<Vec<_>>(),
        ["E-NAME-DUPLICATE-FUNCTION"]
    );
    assert_eq!(es[0].file.as_deref(), Some("a.tlvm"));
}

#[test]
fn import_after_declaration() {
    let src = "fn solve(x: Int) -> Int = x\nimport \"a.tlvm\"\nentry solve\n";
    // source の文字列の API でも、ファイルからでも同じ構文の誤り
    let r = match compile(src.as_bytes(), &StaticProfile::default()) {
        SourceCompile::Result(r) => r,
        _ => panic!(),
    };
    let es = r.errors();
    assert_eq!(
        es.iter().map(|d| d.code).collect::<Vec<_>>(),
        ["E-IMPORT-AFTER-DECL"]
    );
    assert_eq!(es[0].phase, "parse");
    assert_eq!(&src[es[0].span.0..es[0].span.1], "import \"a.tlvm\"");
    assert_eq!(es[0].repair.as_ref().unwrap().kind, "delete_span");
    assert_eq!(es[0].file, None);
    // entry の後、import の並びの途中に宣言があるときも
    let files = [
        (
            "main.tlvm",
            "import \"a.tlvm\"\nfn solve(x: Int) -> Int = sq(x)\nentry solve\nimport \"b.tlvm\"\n",
        ),
        ("a.tlvm", SQ),
        ("b.tlvm", SQ),
    ];
    assert_eq!(codes(&files), ["E-IMPORT-AFTER-DECL"]);
    // ライブラリの中の誤りはそのファイルに付く
    let files = [
        (
            "main.tlvm",
            "import \"a.tlvm\"\nfn solve(x: Int) -> Int = sq(x)\nentry solve\n",
        ),
        (
            "a.tlvm",
            "fn sq(x: Int) -> Int = mul(x, x)\nimport \"b.tlvm\"\n",
        ),
    ];
    let d = only_error(&files, "E-IMPORT-AFTER-DECL");
    assert_eq!(d.file.as_deref(), Some("a.tlvm"));
    assert_eq!(spelled(&files, &d), "import \"b.tlvm\"");
}

#[test]
fn bad_path_forms() {
    for (path, why) in [
        ("/etc/a.tlvm", "absolute"),
        ("../a.tlvm", "above the root"),
        ("lib/../../a.tlvm", "above the root"),
        ("a.txt", ".tlvm"),
        ("a", ".tlvm"),
        ("", "empty"),
        (".tlvm", "file name"),
        ("lib\\\\a.tlvm", "separator"),
        ("c:a.tlvm", "separator"),
        ("lib//a.tlvm", "empty path component"),
        ("lib/", ".tlvm"),
    ] {
        let root = format!("import \"{path}\"\nfn solve(x: Int) -> Int = x\nentry solve\n");
        let files = [("main.tlvm", root.as_str()), ("a.tlvm", SQ)];
        let d = only_error(&files, "E-IMPORT-PATH");
        assert!(d.actual.as_deref().unwrap().contains(why), "{path}: {d:?}");
        assert_eq!(d.file.as_deref(), Some("main.tlvm"));
    }
}

#[test]
fn definitions_of_every_kind_across_files() {
    let files = [
        (
            "main.tlvm",
            "import \"lib/types.tlvm\"\nimport \"lib/fns.tlvm\"\n\n\
fn solve(xs: List<Int>) -> Pair<Pair<Int, Option<Int>>, Pair<Int, Shape>> =\n\
  pair(pair(countdown(3), first(xs)), pair(area(Square(2)), dict_shape(tally(xs))))\n\
entry solve\n",
        ),
        ("lib/types.tlvm", "type Shape = Square(Int) | Circle(Int) | Empty\ntype Box<T> = { value: T, n: Int }\n"),
        (
            "lib/fns.tlvm",
            "import \"types.tlvm\"\n\
rec fn countdown(n: Int) -> Int = if(lt(n, 1), 0, add(1, countdown(sub(n, 1))))\n\
fn first<T>(xs: List<T>) -> Option<T> = match uncons(xs) { some(p) => some(fst(p)), none => none<T>() }\n\
fn area(s: Shape) -> Int = match s { Square(a) => mul(a, a), Circle(r) => mul(3, mul(r, r)), Empty => 0 }\n\
fn tally(xs: List<Int>) -> Dict<Int, Int> = fold(xs, dict<Int, Int>(), |d, x| dict_put(d, x, add(1, match_option(dict_get(d, x), 0, |c| c))))\n\
fn boxed<T>(x: T) -> Box<T> = Box { value: x, n: 1 }\n\
fn dict_shape(d: Dict<Int, Int>) -> Shape = if(lt(dict_size(d), 2), Empty, Circle(boxed(dict_size(d)).value))\n",
        ),
    ];
    let p = accepted(&files);
    assert!(
        !p.terminates(),
        "rec fn は import したファイルにあっても印が残る"
    );
    assert_eq!(
        p.output_type.to_string(),
        "Pair<Pair<Int, Option<Int>>, Pair<Int, Shape>>"
    );
    assert_eq!(run(&files, "[4, 4, 5]"), r#"[[3,4],[4,{"Circle":[2]}]]"#);
}

#[test]
fn library_entry_is_ignored() {
    // ライブラリの entry は根から import したときは無視する（根の entry だけが数える）
    let files = [
        (
            "main.tlvm",
            "import \"lib.tlvm\"\nfn solve(x: Int) -> Int = add(sq(x), 1)\nentry solve\n",
        ),
        (
            "lib.tlvm",
            "fn sq(x: Int) -> Int = mul(x, x)\nfn demo(x: Int) -> Int = sq(x)\nentry demo\n",
        ),
    ];
    assert_eq!(run(&files, "3"), "10");
    // 根に entry がなければ今までどおり E-ENTRY-MISSING（根に付く。ライブラリの entry は代わりにならない）
    let files = [
        (
            "main.tlvm",
            "import \"lib.tlvm\"\nfn solve(x: Int) -> Int = sq(x)\n",
        ),
        files[1],
    ];
    let d = only_error(&files, "E-ENTRY-MISSING");
    assert_eq!(d.file.as_deref(), Some("main.tlvm"));
    // entry のないライブラリを単独で検査すると E-ENTRY-MISSING（ライブラリは根から import して検査する）
    let files = [("lib.tlvm", SQ)];
    assert_eq!(codes(&files), ["E-ENTRY-MISSING"]);
}

#[test]
fn diagnostics_point_at_the_right_file() {
    let files = [
        (
            "main.tlvm",
            "import \"lib/a.tlvm\"\nfn solve(x: Int) -> Int = add(f(x), true)\nentry solve\n",
        ),
        ("lib/a.tlvm", "fn f(x: Int) -> Int = add(x, \"s\")\n"),
    ];
    let es = errors(&files);
    let got: Vec<_> = es
        .iter()
        .map(|d| (d.code, d.file.as_deref().unwrap(), spelled(&files, d)))
        .collect();
    assert!(
        got.contains(&("E-TYPE-ARG", "lib/a.tlvm", "\"s\"")),
        "{got:?}"
    );
    assert!(
        got.contains(&("E-TYPE-ARG", "main.tlvm", "true")),
        "{got:?}"
    );
    // 修復ヒントの位置もファイルの中
    for d in &es {
        let r = d.repair.as_ref().unwrap();
        assert_eq!(r.target_span, d.span);
    }
    // JSON の最後の key が file
    assert!(
        es[0].to_json().ends_with(",\"file\":\"lib/a.tlvm\"}")
            || es[0].to_json().ends_with(",\"file\":\"main.tlvm\"}"),
        "{}",
        es[0].to_json()
    );
    // ライブラリの構文の誤りは、そのファイルの位置と修復ヒント
    let files = [
        (
            "main.tlvm",
            "import \"lib/a.tlvm\"\nfn solve(x: Int) -> Int = x\nentry solve\n",
        ),
        ("lib/a.tlvm", "fn f(x: Int) -> Int = add(x 1)\n"),
    ];
    let es = errors(&files);
    assert_eq!(es[0].code, "E-PARSE-EXPECTED-TOKEN");
    assert_eq!(es[0].file.as_deref(), Some("lib/a.tlvm"));
    assert_eq!(spelled(&files, &es[0]), "1");
    // import のない単一ファイルの診断には file が付かず、JSON も今までと同じ
    let es = errors(&[(
        "main.tlvm",
        "fn solve(x: Int) -> Int = add(x, true)\nentry solve\n",
    )]);
    assert_eq!(es[0].file, None);
    assert!(!es[0].to_json().contains("\"file\""));
}

#[test]
fn unused_library_functions_do_not_warn() {
    let files = [
        ("main.tlvm", "import \"lib.tlvm\"\nfn solve(x: Int) -> Int = sq(x)\nfn spare(x: Int) -> Int = x\nentry solve\n"),
        ("lib.tlvm", "fn sq(x: Int) -> Int = mul(x, x)\nfn cube(x: Int) -> Int = mul(x, sq(x))\n"),
    ];
    let r = compiled(&files);
    let ws: Vec<_> = r
        .warnings()
        .iter()
        .map(|d| (d.code, d.file.as_deref().unwrap(), spelled(&files, d)))
        .collect();
    assert_eq!(ws, [("W-UNUSED-FUNCTION", "main.tlvm", "spare")]);
}

#[test]
fn source_string_apis_reject_imports() {
    let src = "import \"sq.tlvm\"\nfn solve(x: Int) -> Int = sq(x)\nentry solve\n";
    let r = match compile(src.as_bytes(), &StaticProfile::default()) {
        SourceCompile::Result(r) => r,
        _ => panic!(),
    };
    let es = r.errors();
    assert_eq!(
        es.iter().map(|d| d.code).collect::<Vec<_>>(),
        ["E-IMPORT-UNSUPPORTED"]
    );
    assert_eq!(&src[es[0].span.0..es[0].span.1], "import \"sq.tlvm\"");
    assert!(es[0].repair.is_some());
    let e = tlvm::embed::Program::compile(src).unwrap_err();
    assert_eq!(e[0].code, "E-IMPORT-UNSUPPORTED");
    // `import` は予約語ではない（変数名などに使える）
    let ok = "fn solve(import: Int) -> Int = import\nentry solve\n";
    assert!(tlvm::embed::Program::compile(ok).is_ok());
}

#[test]
fn limits() {
    let files = [
        (
            "main.tlvm",
            "import \"a.tlvm\"\nfn solve(x: Int) -> Int = fa(x)\nentry solve\n",
        ),
        (
            "a.tlvm",
            "import \"b.tlvm\"\nfn fa(x: Int) -> Int = fb(x)\n",
        ),
        ("b.tlvm", "fn fb(x: Int) -> Int = x\n"),
    ];
    assert_eq!(run(&files, "1"), "1");
    let p = StaticProfile {
        import_files: 2,
        ..StaticProfile::default()
    };
    let r = compiled_with(&files, &p);
    assert_eq!(
        r.errors().iter().map(|d| d.code).collect::<Vec<_>>(),
        ["E-LIMIT-STATIC-IMPORT-FILES"]
    );
    assert_eq!(r.errors()[0].file.as_deref(), Some("a.tlvm"));
    // bytes はファイルの合計を source_bytes で抑える
    let total: usize = files.iter().map(|(_, s)| s.len()).sum();
    let p = StaticProfile {
        source_bytes: total - 1,
        ..StaticProfile::default()
    };
    assert_eq!(
        compiled_with(&files, &p).errors()[0].code,
        "E-LIMIT-STATIC-SOURCE-BYTES"
    );
    let p = StaticProfile {
        source_bytes: total,
        ..StaticProfile::default()
    };
    assert!(compiled_with(&files, &p).program().is_some());
}

// ---------------------------------------------------------------- CLI（一時ディレクトリ）

struct Dir(PathBuf);

impl Dir {
    fn new(files: &[(&str, &str)]) -> Dir {
        static N: std::sync::atomic::AtomicUsize = std::sync::atomic::AtomicUsize::new(0);
        let n = N.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
        let d = std::env::temp_dir().join(format!("tlvm-import-{}-{n}", std::process::id()));
        let _ = std::fs::remove_dir_all(&d);
        for (k, v) in files {
            let p = d.join(k);
            std::fs::create_dir_all(p.parent().unwrap()).unwrap();
            std::fs::write(p, v).unwrap();
        }
        Dir(d)
    }
    fn path(&self, rel: &str) -> String {
        self.0.join(rel).to_string_lossy().into_owned()
    }
}

impl Drop for Dir {
    fn drop(&mut self) {
        let _ = std::fs::remove_dir_all(&self.0);
    }
}

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

const APP: [(&str, &str); 3] = [
    ("main.tlvm", "import \"lib/text.tlvm\"\n\nfn main(s: String) -> String = shout(s)\nentry main\n"),
    ("lib/text.tlvm", "import \"chars.tlvm\"\nfn shout(s: String) -> String = concat(map(s, |c| upper(c)), \"!\")\nfn demo(s: String) -> String = s\nentry demo\n"),
    ("lib/chars.tlvm", "fn upper(c: Char) -> Char = if(le(code('a'), code(c)), if(le(code(c), code('z')), match_option(char(sub(code(c), 32)), c, |u| u), c), c)\n"),
];

#[test]
fn cli_check_run_test_exec() {
    let d = Dir::new(&APP);
    let main = d.path("main.tlvm");
    let (code, out, err) = tlvm(&["check", &main]);
    assert_eq!(code, 0, "{err}");
    assert!(
        out.contains(r#""entry":"main","input_type":"String","output_type":"String""#),
        "{out}"
    );
    assert_eq!(err, "", "ライブラリの使わない関数は warning にしない");
    let (code, out, err) = tlvm(&["run", &main, "\"hi\"", "--plain"]);
    assert_eq!((code, out.trim_end()), (0, "\"HI!\""), "{err}");
    std::fs::write(
        d.path("main.tests.json"),
        r#"[{"name": "a", "input": "ab", "expected": "AB!"}]"#,
    )
    .unwrap();
    let (code, out, err) = tlvm(&["test", &main]);
    assert_eq!(code, 0, "{out}{err}");
    let mut c = Command::new(env!("CARGO_BIN_EXE_tlvm"))
        .args(["exec", &main])
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .unwrap();
    c.stdin.take().unwrap().write_all(b"ok").unwrap();
    let o = c.wait_with_output().unwrap();
    assert_eq!(String::from_utf8(o.stdout).unwrap(), "OK!");
    // ライブラリを根にすると、その entry で動く
    let (code, out, _) = tlvm(&["run", &d.path("lib/text.tlvm"), "\"x\"", "--plain"]);
    assert_eq!((code, out.trim_end()), (0, "\"x\""));
}

#[test]
fn cli_relative_root_path() {
    // CLI に相対パスで渡しても、import はそのファイルのディレクトリから解決する
    let d = Dir::new(&APP);
    let o = Command::new(env!("CARGO_BIN_EXE_tlvm"))
        .current_dir(&d.0)
        .args(["run", "main.tlvm", "\"a\"", "--plain"])
        .output()
        .unwrap();
    assert_eq!(String::from_utf8(o.stdout).unwrap().trim_end(), "\"A!\"");
    let o = Command::new(env!("CARGO_BIN_EXE_tlvm"))
        .current_dir(d.0.join("lib"))
        .args(["run", "../main.tlvm", "\"a\"", "--plain"])
        .output()
        .unwrap();
    assert_eq!(String::from_utf8(o.stdout).unwrap().trim_end(), "\"A!\"");
}

#[test]
fn cli_fmt_keeps_imports_and_ast_is_merged() {
    let d = Dir::new(&[
        ("main.tlvm", "import   \"lib/sq.tlvm\"\nimport \"lib/sq.tlvm\"\nfn   solve(x: Int) -> Int = sq( x )\nentry solve\n"),
        ("lib/sq.tlvm", "fn sq(x: Int) -> Int = mul(x, x)\nentry sq\n"),
    ]);
    let (code, out, err) = tlvm(&["fmt", &d.path("main.tlvm")]);
    assert_eq!(code, 0, "{err}");
    assert_eq!(out, "import \"lib/sq.tlvm\"\nimport \"lib/sq.tlvm\"\nfn solve(x: Int) -> Int = sq(x)\nentry solve\n");
    let (code, out, err) = tlvm(&["ast", &d.path("main.tlvm")]);
    assert_eq!(code, 0, "{err}");
    // まとめたプログラム：ライブラリの関数が先、entry は根のものだけ
    let sq = out.find("\"name\":\"sq\"").unwrap();
    let solve = out.find("\"name\":\"solve\"").unwrap();
    assert!(sq < solve, "{out}");
    assert_eq!(out.matches("\"tag\":\"entry\"").count(), 1, "{out}");
    assert!(
        out.contains("\"tag\":\"entry\",\"name\":\"solve\""),
        "{out}"
    );
    // まとめた AST はそのまま --ast で動く
    let ast = d.path("merged.json");
    std::fs::write(&ast, &out).unwrap();
    let (code, out, err) = tlvm(&["run", &ast, "6", "--plain"]);
    assert_eq!((code, out.trim_end()), (0, "36"), "{err}");
}

#[test]
fn cli_diagnostics_name_the_file() {
    let d = Dir::new(&[
        (
            "main.tlvm",
            "import \"lib/a.tlvm\"\nfn solve(x: Int) -> Int = f(x)\nentry solve\n",
        ),
        ("lib/a.tlvm", "fn f(x: Int) -> Int = add(x, true)\n"),
    ]);
    let (code, _, err) = tlvm(&["check", &d.path("main.tlvm")]);
    assert_eq!(code, 1);
    let lib = d.path("lib/a.tlvm");
    assert!(err.contains(&format!("\"file\":\"{lib}\"")), "{err}");
    let (_, _, err) = tlvm(&["check", &d.path("main.tlvm"), "--human"]);
    assert!(
        err.starts_with(&format!("{lib}:1:30: error[E-TYPE-ARG]")),
        "{err}"
    );
    assert!(err.contains("fn f(x: Int) -> Int = add(x, true)"), "{err}");
    // 見つからない・循環も、import を書いたファイルを指す
    let d = Dir::new(&[
        (
            "main.tlvm",
            "import \"a.tlvm\"\nfn solve(x: Int) -> Int = x\nentry solve\n",
        ),
        ("a.tlvm", "import \"nope.tlvm\"\n"),
    ]);
    let (_, _, err) = tlvm(&["check", &d.path("main.tlvm"), "--human"]);
    assert!(
        err.starts_with(&format!(
            "{}:1:8: error[E-IMPORT-NOT-FOUND]",
            d.path("a.tlvm")
        )),
        "{err}"
    );
    // ast も同じ診断
    let (code, out, err) = tlvm(&["ast", &d.path("main.tlvm")]);
    assert_eq!((code, out.as_str()), (1, ""));
    assert!(err.contains("E-IMPORT-NOT-FOUND"), "{err}");
}

#[test]
fn cli_library_without_entry() {
    let d = Dir::new(&[("lib.tlvm", SQ)]);
    let (code, _, err) = tlvm(&["check", &d.path("lib.tlvm")]);
    assert_eq!(code, 1);
    assert!(err.contains("E-ENTRY-MISSING"), "{err}");
    assert!(
        !err.contains("\"file\""),
        "import のないファイルの診断は今までと同じ形: {err}"
    );
}

#[cfg(unix)]
#[test]
fn cli_symlink_out_of_the_root_directory_is_not_read() {
    let outside = Dir::new(&[("secret.tlvm", SQ)]);
    let d = Dir::new(&[(
        "main.tlvm",
        "import \"link.tlvm\"\nfn solve(x: Int) -> Int = sq(x)\nentry solve\n",
    )]);
    std::os::unix::fs::symlink(
        Path::new(&outside.path("secret.tlvm")),
        d.0.join("link.tlvm"),
    )
    .unwrap();
    let (code, _, err) = tlvm(&["check", &d.path("main.tlvm")]);
    assert_eq!(code, 1);
    assert!(
        err.contains("E-IMPORT-NOT-FOUND") && err.contains("outside"),
        "{err}"
    );
}
