//! v1.12 の `tlvm repl`（差分仕様 §1）。build した binary の標準入力に入力を流し、標準出力を確かめる。

use std::io::Write;
use std::path::PathBuf;
use std::process::{Command, Stdio};

struct Dir(PathBuf);

impl Dir {
    fn new(name: &str, files: &[(&str, &str)]) -> Dir {
        let d = std::env::temp_dir().join(format!("tlvm-repl-{}-{name}", std::process::id()));
        let _ = std::fs::remove_dir_all(&d);
        std::fs::create_dir_all(&d).unwrap();
        for (k, v) in files {
            let p = d.join(k);
            std::fs::create_dir_all(p.parent().unwrap()).unwrap();
            std::fs::write(p, v).unwrap();
        }
        Dir(d)
    }
}

impl Drop for Dir {
    fn drop(&mut self) {
        let _ = std::fs::remove_dir_all(&self.0);
    }
}

/// REPL を `dir` で動かし、（終了コード、標準出力の行）を返す。
fn repl_in(dir: Option<&Dir>, args: &[&str], input: &str) -> (i32, Vec<String>) {
    let mut c = Command::new(env!("CARGO_BIN_EXE_tlvm"));
    c.arg("repl")
        .args(args)
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped());
    if let Some(d) = dir {
        c.current_dir(&d.0);
    }
    let mut child = c.spawn().unwrap();
    // FILE が読めない場合は、REPL が標準入力を読まずに終了する。その書き込みは EPIPE になりうるので許す。
    // 終了コードと出力は下の検査で確かめる。
    match child.stdin.take().unwrap().write_all(input.as_bytes()) {
        Ok(()) => {}
        Err(e) if e.kind() == std::io::ErrorKind::BrokenPipe => {}
        Err(e) => panic!("write stdin: {e}"),
    }
    let o = child.wait_with_output().unwrap();
    assert!(
        o.stderr.is_empty(),
        "stderr: {}",
        String::from_utf8_lossy(&o.stderr)
    );
    let out = String::from_utf8(o.stdout).unwrap();
    (
        o.status.code().unwrap(),
        out.lines().map(str::to_string).collect(),
    )
}

fn repl(input: &str) -> Vec<String> {
    let (code, lines) = repl_in(None, &[], input);
    assert_eq!(code, 0);
    lines
}

#[test]
fn expressions_print_value_and_type() {
    let out = repl(
        "add(1, 2)\n\"日本語\"\npair(1, true)\nlist<Int>(1, 2, 3)\nmap(list<Int>(1, 2, 3), |x| mul(x, x))\nnone<Int>()\nsome(3)\nunit\nok<Int, String>(1)\ndict_put(dict<String, Int>(), \"a\", 1)\n",
    );
    assert_eq!(
        out,
        [
            "3 : Int",
            "\"日本語\" : String",
            "[1,true] : Pair<Int, Bool>",
            "[1,2,3] : List<Int>",
            "[1,4,9] : List<Int>",
            "null : Option<Int>",
            "3 : Option<Int>",
            "null : Unit",
            "{\"ok\":1} : Result<Int, String>",
            "[[\"a\",1]] : Dict<String, Int>",
        ]
    );
}

#[test]
fn declarations_extend_the_session() {
    let out = repl(
        "fn double(x: Int) -> Int = mul(x, 2)\ndouble(21)\ntype P = { x: Int, y: Int }\nP { x: 1, y: 2 }\nfn mk(x: Int) -> P = P { x: x, y: x }\nmk(3).y\ntype Shape = Circle(Int) | Sq(Int)\nSq(2)\nfn first<T>(xs: List<T>) -> Option<T> = match uncons(xs) { some(p) => some(fst(p)), none => none<T>() }\nfirst(list<Int>(7, 8))\nrec fn count(n: Int) -> Int = if(le(n, 0), 0, add(1, count(sub(n, 1))))\ncount(5)\n",
    );
    assert_eq!(
        out,
        [
            "defined double",
            "42 : Int",
            "defined P",
            "{\"x\":1,\"y\":2} : P",
            "defined mk",
            "3 : Int",
            "defined Shape",
            "{\"Sq\":[2]} : Shape",
            "defined first",
            "7 : Option<Int>",
            "defined count",
            "5 : Int",
        ]
    );
}

#[test]
fn errors_keep_the_session() {
    let out = repl(
        "fn double(x: Int) -> Int = mul(x, 2)\nfn bad(x: Int) -> Int = true\nbad(1)\nadd(1, true)\nundefined_fn(3)\nfn double(x: Int) -> Int = true\ndouble(2)\n",
    );
    let text = out.join("\n");
    assert_eq!(out[0], "defined double");
    // 宣言の誤りは入力の位置で示す
    assert!(
        out[1].starts_with("<input>:1:25: error[E-TYPE-RETURN]"),
        "{text}"
    );
    assert!(
        text.contains("error[E-NAME-UNKNOWN-FUNCTION]") && text.contains("(found bad)"),
        "{text}"
    );
    assert!(text.contains("<input>:1:8: error[E-TYPE-ARG]"), "{text}");
    assert!(text.contains("(found undefined_fn)"), "{text}");
    // 修復ヒントも出す
    assert!(
        text.contains(" = repair (replace_expression): expression of type Int"),
        "{text}"
    );
    // 拒否された再定義は元の定義を残す
    assert_eq!(out.last().unwrap(), "4 : Int", "{text}");
    assert!(!text.contains("redefined"), "{text}");
}

#[test]
fn redefinition_replaces() {
    let out = repl("fn f(x: Int) -> Int = x\nfn g(x: Int) -> Int = f(add(x, 1))\nfn f(x: Int) -> Int = mul(x, 10)\ng(1)\n:list\n");
    assert_eq!(
        out,
        [
            "defined f",
            "defined g",
            "redefined f",
            "20 : Int",
            "fn g(x: Int) -> Int = f(add(x, 1))",
            "fn f(x: Int) -> Int = mul(x, 10)"
        ]
    );
}

#[test]
fn resource_exhaustion_keeps_the_session() {
    let out =
        repl("fn one(x: Unit) -> Int = 1\nloop(0, 1000000000, |s| some(add(s, 1)))\none(unit)\n");
    assert_eq!(out[0], "defined one");
    assert!(out[1].starts_with("error: ResourceExhausted "), "{out:?}");
    assert_eq!(out[2], "1 : Int");
}

#[test]
fn multiline_input() {
    let out = repl("fn f(x: Int) -> Int =\n  add(x,\n      1)\npair(\n  f(1),\n  \"a)\" // )\n)\nlet x = 2 in\n  mul(x, x)\n");
    assert_eq!(
        out,
        ["defined f", "[2,\"a)\"] : Pair<Int, String>", "4 : Int"]
    );
    // 閉じないまま EOF になれば、そこまでを検査して診断を出す
    let out = repl("fn f(x: Int) -> Int = add(x,\n");
    assert!(
        out[0].starts_with("<input>:1:29: error[E-PARSE-EXPECTED-EXPR]"),
        "{out:?}"
    );
}

#[test]
fn commands() {
    let out = repl(":help\n:type add(1, 2)\n:t pair(\"a\", 'b')\n:type\n:list\nfn f(x: Int) -> Int = x\n:list\n:reset\n:list\nf(1)\n:nope\n:quit\nadd(1, 1)\n");
    let help = out
        .iter()
        .position(|l| l.starts_with("Commands:"))
        .expect("help");
    let rest = &out[help..];
    assert!(rest.iter().any(|l| l.contains(":load FILE")));
    let after: Vec<&str> = out
        .iter()
        .skip_while(|l| *l != "Int")
        .map(String::as_str)
        .collect();
    assert_eq!(after[0], "Int");
    assert_eq!(after[1], "Pair<String, Char>");
    assert_eq!(after[2], "usage: :type EXPR");
    assert_eq!(after[3], "(no declarations)");
    assert_eq!(after[4], "defined f");
    assert_eq!(after[5], "fn f(x: Int) -> Int = x");
    assert_eq!(after[6], "session cleared");
    assert_eq!(after[7], "(no declarations)");
    assert!(
        after[8].contains("error[E-NAME-UNKNOWN-FUNCTION]"),
        "{after:?}"
    );
    assert_eq!(*after.last().unwrap(), "unknown command :nope (see :help)");
    // :quit の後の入力は読まない
    assert!(!out.iter().any(|l| l == "2 : Int"));
}

#[test]
fn entry_is_rejected_in_input() {
    let out = repl("entry f\n");
    assert_eq!(
        out,
        ["<input>:1:1: error: the REPL has no entry; type an expression to evaluate it"]
    );
}

#[test]
fn load_and_import() {
    let d = Dir::new(
        "load",
        &[
            ("lib/sq.tlvm", "fn sq(x: Int) -> Int = mul(x, x)\n"),
            ("lib/quad.tlvm", "import \"sq.tlvm\"\nfn quad(x: Int) -> Int = sq(sq(x))\nfn main(x: Int) -> Int = quad(x)\nentry main\n"),
            ("bad.tlvm", "fn oops(x: Int) -> Int = true\n"),
        ],
    );
    let (code, out) = repl_in(Some(&d), &[], ":load lib/quad.tlvm\nquad(2)\nimport \"lib/sq.tlvm\"\n:list\n:load bad.tlvm\nquad(1)\nimport \"missing.tlvm\"\n");
    assert_eq!(code, 0);
    assert_eq!(
        out[..4],
        [
            "imported \"lib/sq.tlvm\"",
            "defined quad",
            "defined main",
            "loaded 2 declaration(s) from lib/quad.tlvm"
        ]
    );
    assert_eq!(out[4], "16 : Int");
    // 同じ import は一度だけ
    assert_eq!(out[5], "imported \"lib/sq.tlvm\"");
    assert_eq!(
        out[6..9],
        [
            "import \"lib/sq.tlvm\"",
            "fn quad(x: Int) -> Int = sq(sq(x))",
            "fn main(x: Int) -> Int = quad(x)"
        ]
    );
    // 読んだファイルの誤りはそのファイルの位置で示す
    assert!(
        out[9].starts_with("bad.tlvm:1:26: error[E-TYPE-RETURN]"),
        "{out:?}"
    );
    assert!(out.contains(&"1 : Int".to_string()), "{out:?}");
    assert!(
        out.iter().any(|l| l.contains("error[E-IMPORT-NOT-FOUND]")),
        "{out:?}"
    );

    // FILE の引数は最初に :load する
    let (code, out) = repl_in(Some(&d), &["lib/quad.tlvm"], "main(3)\n");
    assert_eq!(code, 0);
    assert_eq!(out.last().unwrap(), "81 : Int");
    // 読めなければ終了コード 1
    let (code, out) = repl_in(Some(&d), &["bad.tlvm"], "1\n");
    assert_eq!(code, 1);
    assert!(out[0].contains("error[E-TYPE-RETURN]"), "{out:?}");
}

#[test]
fn no_prompt_when_not_a_terminal() {
    // 標準入力が端末でなければ prompt を出さない（出力は結果だけ）
    assert_eq!(repl("1\n"), ["1 : Int"]);
    assert!(repl("").is_empty());
}
