//! v1.16 のパッケージ（ローカルの依存、差分仕様 `spec/lptl-v1.16`）：マニフェスト `tlvm.json`、`@名前/パス` の import、
//! 依存の場所・名前・版の検査、診断。ファイルは一時ディレクトリに作り、CLI（`tlvm check`・`tlvm run`）で確かめる。

use std::path::PathBuf;
use std::process::Command;

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

/// 一時ディレクトリに、相対パスとファイルの中身の組でプロジェクトを作る。戻り値は根のファイルのパス（`main.tlvm`）。
/// 使い終わったら消す（`Project` の Drop）。
struct Project {
    dir: PathBuf,
}

impl Project {
    fn new(files: &[(&str, &str)]) -> Project {
        static N: std::sync::atomic::AtomicUsize = std::sync::atomic::AtomicUsize::new(0);
        let n = N.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
        let dir = std::env::temp_dir().join(format!("tlvm-pkg-{}-{n}", std::process::id()));
        std::fs::create_dir_all(&dir).unwrap();
        let p = Project { dir };
        for (rel, body) in files {
            let path = p.dir.join(rel);
            std::fs::create_dir_all(path.parent().unwrap()).unwrap();
            std::fs::write(path, body).unwrap();
        }
        p
    }
    fn root(&self) -> String {
        self.dir.join("main.tlvm").to_string_lossy().into_owned()
    }
}

impl Drop for Project {
    fn drop(&mut self) {
        let _ = std::fs::remove_dir_all(&self.dir);
    }
}

/// 根のファイルを検査した診断のコード（重複を除く）。
fn codes(p: &Project) -> Vec<String> {
    let (_, out, err) = tlvm(&["check", &p.root()]);
    let out = out + &err;
    let mut v: Vec<String> = out
        .split("\"code\":\"")
        .skip(1)
        .map(|s| s.split('"').next().unwrap().to_string())
        .collect();
    v.sort();
    v.dedup();
    v
}

/// 根のファイルを実行した出力（終了コードは 0 であること）。
fn run(p: &Project, input: &str) -> String {
    let (code, out, err) = tlvm(&["run", &p.root(), input, "--plain"]);
    assert_eq!(code, 0, "{err}");
    out.trim_end().to_string()
}

const STATS: &str = "fn total(xs: List<Int>) -> Int = fold(xs, 0, |acc, x| add(acc, x))\n";
const STATS_MANIFEST: &str = r#"{"name":"stats","version":"0.2.0"}"#;

fn app(deps: &str) -> Vec<(String, String)> {
    vec![
        ("main.tlvm".into(), "import \"@stats/summary.tlvm\"\nfn solve(xs: List<Int>) -> Int = total(xs)\nentry solve\n".into()),
        ("tlvm.json".into(), format!("{{\"dependencies\":{deps}}}")),
        ("deps/stats/tlvm.json".into(), STATS_MANIFEST.into()),
        ("deps/stats/summary.tlvm".into(), STATS.into()),
    ]
}

fn project(files: Vec<(String, String)>) -> Project {
    let refs: Vec<(&str, &str)> = files
        .iter()
        .map(|(a, b)| (a.as_str(), b.as_str()))
        .collect();
    Project::new(&refs)
}

#[test]
fn a_declared_dependency_is_imported_by_name_and_runs() {
    let p = project(app(r#"{"stats":{"path":"deps/stats","version":"0.2.0"}}"#));
    assert_eq!(run(&p, "[1,2,3]"), "6");
    assert!(codes(&p).is_empty());
}

#[test]
fn a_dependency_declares_its_own_dependencies() {
    // stats は text を宣言し、app は stats だけを宣言する。main は text を直接は使えない（E-PKG-UNKNOWN）が、
    // stats の中のファイルは text を使える（ファイルの属するパッケージの依存で解決する）。
    let p = project(vec![
        ("main.tlvm".into(), "import \"@stats/summary.tlvm\"\nfn solve(xs: List<Int>) -> Int = total(xs)\nentry solve\n".into()),
        ("tlvm.json".into(), r#"{"dependencies":{"stats":{"path":"deps/stats"}}}"#.into()),
        ("deps/stats/tlvm.json".into(), r#"{"name":"stats","dependencies":{"text":{"path":"../text"}}}"#.into()),
        ("deps/stats/summary.tlvm".into(), "import \"@text/double.tlvm\"\nfn total(xs: List<Int>) -> Int = fold(xs, 0, |acc, x| add(acc, double(x)))\n".into()),
        ("deps/text/tlvm.json".into(), r#"{"name":"text"}"#.into()),
        ("deps/text/double.tlvm".into(), "fn double(x: Int) -> Int = mul(x, 2)\n".into()),
    ]);
    assert_eq!(run(&p, "[1,2,3]"), "12");
    let q = project(vec![
        ("main.tlvm".into(), "import \"@text/double.tlvm\"\nfn solve(xs: List<Int>) -> Int = double(1)\nentry solve\n".into()),
        ("tlvm.json".into(), r#"{"dependencies":{"stats":{"path":"deps/stats"}}}"#.into()),
        ("deps/stats/tlvm.json".into(), r#"{"name":"stats","dependencies":{"text":{"path":"../text"}}}"#.into()),
        ("deps/text/tlvm.json".into(), r#"{"name":"text"}"#.into()),
        ("deps/text/double.tlvm".into(), "fn double(x: Int) -> Int = mul(x, 2)\n".into()),
    ]);
    assert_eq!(codes(&q), ["E-PKG-UNKNOWN"]);
}

#[test]
fn an_undeclared_package_is_rejected() {
    let p = project(app("{}"));
    assert_eq!(codes(&p), ["E-PKG-UNKNOWN"]);
    let q = Project::new(&[(
        "main.tlvm",
        "import \"@stats/summary.tlvm\"\nfn solve(xs: List<Int>) -> Int = total(xs)\nentry solve\n",
    )]);
    assert_eq!(codes(&q), ["E-PKG-UNKNOWN"]);
}

#[test]
fn a_missing_dependency_directory_is_rejected() {
    let p = project(app(r#"{"stats":{"path":"deps/nothere"}}"#));
    assert_eq!(codes(&p), ["E-PKG-NOT-FOUND"]);
}

#[test]
fn the_name_must_match_the_declared_key() {
    let mut files = app(r#"{"stats":{"path":"deps/stats"}}"#);
    files[2].1 = r#"{"name":"other"}"#.into();
    assert_eq!(codes(&project(files)), ["E-PKG-NAME"]);
}

#[test]
fn a_pinned_version_must_match() {
    let p = project(app(r#"{"stats":{"path":"deps/stats","version":"0.3.0"}}"#));
    assert_eq!(codes(&p), ["E-PKG-VERSION"]);
    let mut files = app(r#"{"stats":{"path":"deps/stats","version":"0.2.0"}}"#);
    files[2].1 = r#"{"name":"stats"}"#.into();
    assert_eq!(codes(&project(files)), ["E-PKG-VERSION"]);
}

#[test]
fn a_dependency_path_must_stay_inside_the_project() {
    assert_eq!(
        codes(&project(app(r#"{"stats":{"path":"../../outside"}}"#))),
        ["E-PKG-PATH"]
    );
    assert_eq!(
        codes(&project(app(r#"{"stats":{"path":"/abs/stats"}}"#))),
        ["E-PKG-PATH"]
    );
    assert_eq!(
        codes(&project(app(r#"{"stats":{"path":"."}}"#))),
        ["E-PKG-PATH"]
    );
}

#[test]
fn the_manifest_keys_and_shapes_are_checked() {
    assert_eq!(
        codes(&project(app(
            r#"{"stats":{"path":"deps/stats","versoin":"0.2.0"}}"#
        ))),
        ["E-PKG-MANIFEST"]
    );
    assert_eq!(
        codes(&project(app(
            r#"{"stats":{"path":"deps/stats","version":"0.2"}}"#
        ))),
        ["E-PKG-MANIFEST"]
    );
    assert_eq!(
        codes(&project(app(r#"{"Stats":{"path":"deps/stats"}}"#))),
        ["E-PKG-MANIFEST"]
    );
    assert_eq!(
        codes(&project(
            app(r#"{"stats":{"path":"deps/stats"}}"#)
                .into_iter()
                .map(|(a, b)| if a == "tlvm.json" {
                    (a, "{broken".into())
                } else {
                    (a, b)
                })
                .collect()
        )),
        ["E-PKG-MANIFEST"]
    );
}

#[test]
fn an_at_import_must_stay_inside_the_dependency() {
    let mut files = app(r#"{"stats":{"path":"deps/stats"}}"#);
    files[0].1 =
        "import \"@stats/../summary.tlvm\"\nfn solve(xs: List<Int>) -> Int = 0\nentry solve\n"
            .into();
    assert_eq!(codes(&project(files)), ["E-IMPORT-PATH"]);
    let mut files = app(r#"{"stats":{"path":"deps/stats"}}"#);
    files[0].1 = "import \"@stats\"\nfn solve(xs: List<Int>) -> Int = 0\nentry solve\n".into();
    assert_eq!(codes(&project(files)), ["E-IMPORT-PATH"]);
}

#[test]
fn a_stray_broken_manifest_does_not_affect_programs_without_packages() {
    let p = Project::new(&[
        (
            "main.tlvm",
            "import \"lib/u.tlvm\"\nfn solve(xs: List<Int>) -> Int = one()\nentry solve\n",
        ),
        ("lib/u.tlvm", "fn one() -> Int = 1\n"),
        ("tlvm.json", "{broken"),
    ]);
    assert_eq!(run(&p, "[]"), "1");
}

#[test]
fn package_files_share_the_namespace() {
    let mut files = app(r#"{"stats":{"path":"deps/stats"}}"#);
    files.push(("deps/other/tlvm.json".into(), r#"{"name":"other"}"#.into()));
    files.push((
        "deps/other/x.tlvm".into(),
        "fn total(xs: List<Int>) -> Int = 0\n".into(),
    ));
    files[1].1 =
        r#"{"dependencies":{"stats":{"path":"deps/stats"},"other":{"path":"deps/other"}}}"#.into();
    files[0].1 = "import \"@stats/summary.tlvm\"\nimport \"@other/x.tlvm\"\nfn solve(xs: List<Int>) -> Int = total(xs)\nentry solve\n".into();
    assert_eq!(codes(&project(files)), ["E-IMPORT-CONFLICT"]);
}

#[test]
fn an_import_cycle_across_packages_is_detected() {
    let p = project(vec![
        (
            "main.tlvm".into(),
            "import \"@a/x.tlvm\"\nfn solve(xs: List<Int>) -> Int = ax()\nentry solve\n".into(),
        ),
        (
            "tlvm.json".into(),
            r#"{"dependencies":{"a":{"path":"deps/a"}}}"#.into(),
        ),
        (
            "deps/a/tlvm.json".into(),
            r#"{"name":"a","dependencies":{"b":{"path":"../b"}}}"#.into(),
        ),
        (
            "deps/a/x.tlvm".into(),
            "import \"@b/y.tlvm\"\nfn ax() -> Int = 1\n".into(),
        ),
        (
            "deps/b/tlvm.json".into(),
            r#"{"name":"b","dependencies":{"a":{"path":"../a"}}}"#.into(),
        ),
        (
            "deps/b/y.tlvm".into(),
            "import \"@a/x.tlvm\"\nfn by() -> Int = 2\n".into(),
        ),
    ]);
    assert_eq!(codes(&p), ["E-IMPORT-CYCLE"]);
}
