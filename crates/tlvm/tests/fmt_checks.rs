//! `tlvm fmt` は `check` と同じ検査を通ったプログラムだけを整形する。型・構文の誤りがあれば整形せず、診断だけを出す。

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

fn with_file<T>(src: &str, f: impl FnOnce(&str) -> T) -> T {
    static N: std::sync::atomic::AtomicUsize = std::sync::atomic::AtomicUsize::new(0);
    let n = N.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
    let path =
        std::env::temp_dir().join(format!("tlvm-fmt-checks-{}-{n}.tlvm", std::process::id()));
    std::fs::write(&path, src).unwrap();
    let r = f(path.to_str().unwrap());
    let _ = std::fs::remove_file(&path);
    r
}

#[test]
fn fmt_refuses_a_type_error() {
    with_file("fn f(x: Int) -> Bool = x\nentry f\n", |p| {
        let (code, out, err) = tlvm(&["fmt", p]);
        assert_eq!(code, 1);
        assert_eq!(out, "");
        assert!(err.contains("E-TYPE-RETURN"), "{err}");
    });
}

#[test]
fn fmt_refuses_a_parse_error() {
    with_file("fn f(x: Int) -> Int = add(x,\nentry f\n", |p| {
        let (code, out, err) = tlvm(&["fmt", p]);
        assert_eq!(code, 1);
        assert_eq!(out, "");
        assert!(err.contains("E-PARSE"), "{err}");
    });
}

#[test]
fn fmt_formats_a_checked_program_and_stays_quiet_about_warnings() {
    // g は使われていないので警告になるが、整形は行い、警告は出さない
    let src = "fn g(y: Int) -> Int = y\nfn f(x: Int) -> Int = add(x,1)\nentry f\n";
    with_file(src, |p| {
        let (code, out, err) = tlvm(&["fmt", p]);
        assert_eq!(code, 0);
        assert_eq!(
            out,
            "fn g(y: Int) -> Int = y\nfn f(x: Int) -> Int = add(x, 1)\nentry f\n"
        );
        assert_eq!(err, "");
    });
}
