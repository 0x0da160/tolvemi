//! tlvm コマンド。
//!
//!   tlvm check FILE           静的検査（.tlvm source、.json は ast_codec_v1）。結果の terminates は
//!                             `rec fn` がなければ true（停止を保証）、あれば false（v1.7）
//!   tlvm run FILE INPUT       検査・入力 decode・実行（INPUT は JSON 文字列、@path、- は stdin）
//!   tlvm fmt FILE             正準ソースを出力（`check` と同じ検査に誤りがあれば出さず、終了コード 1）
//!   tlvm ast FILE             ast_codec_v1 JSON を出力（v1.11：import があればまとめたプログラム）
//!
//! v1.11：source のファイルの先頭の `import "path.tlvm"` は、check・run・test・exec・ast がたどって一つのプログラムに
//! まとめる（`tlvm::imports`）。fmt は与えたファイルだけを整形する（import の行は残す）。
//!   tlvm test FILE [CASES]    入力と期待出力の組を実行して照合（CASES の既定は FILE.tests.json）
//!   tlvm exec FILE [ARGS...]  コマンドとして実行（v1.3）。entry の入力型で渡すものが決まる：
//!                             String は標準入力の全文、List<String> はコマンドライン引数、
//!                             Pair<List<String>, String> はその両方。出力が String ならそのまま標準出力へ。
//!                             出力が Result<String, String> なら ok(s) は s を標準出力へ（終了コード 0）、
//!                             err(s) は s を標準エラーへ（終了コード 1）。
//!                             v1.13：Dict<String, String>・Dict<String, Int> は標準入力の行（key TAB value）の辞書
//!                             （規則は `tlvm::lines`）。行の誤りは InputBoundaryFailure（行番号つき）、復号の拒否は診断
//!
//! 診断は一行一 JSON object で stderr へ、結果は stdout へ出す。
//!
//! v1.12：対話的な道具（検証されていない front-end。判定と実行は上と同じ経路）
//!   tlvm repl [FILE]          REPL（宣言を加え、式を評価して `値 : 型` を出す。FILE の宣言を最初に読む）
//!   tlvm lsp                  Language Server（標準入出力の JSON-RPC。診断と整形）
//!
//!   --plain   run の入出力を普通の JSON で読み書きする（対応は plain モジュール）
//!   --human   診断を `file:行:列: error[CODE]: …` の形で、該当行と修復ヒントを添えて出す

use std::io::Read;
use std::process::ExitCode;
use std::sync::atomic::{AtomicBool, Ordering};
use tlvm::api::*;
use tlvm::diagnostics::{json_string, render_human, Diagnostic};
use tlvm::formatter::{encode_ast, format_program};
use tlvm::plain::encode_plain;
use tlvm::profiles::*;
use tlvm::strict_json::{self, JKind, JNode};
use tlvm::syntax::Program;
use tlvm::values::encode_value;
use tlvm::{DecodeResult, RunResult};

static HUMAN: AtomicBool = AtomicBool::new(false);

fn usage() -> ExitCode {
    eprintln!(
        "usage: tlvm check|fmt|ast FILE [--ast] [--human]\n       tlvm run FILE INPUT [--ast] [--stats] [--plain] [--human]\n       tlvm test FILE [CASES] [--ast] [--canonical] [--human]\n       tlvm exec FILE [ARGS...]\n       tlvm repl [FILE]\n       tlvm lsp"
    );
    ExitCode::from(64)
}

fn read(path: &str) -> Result<Vec<u8>, String> {
    if path == "-" {
        let mut v = vec![];
        std::io::stdin()
            .read_to_end(&mut v)
            .map_err(|e| e.to_string())?;
        Ok(v)
    } else {
        std::fs::read(path).map_err(|e| format!("{path}: {e}"))
    }
}

/// 診断を出す。`label` と `src` は --human のときの位置表示に使う（span が指す bytes）。
fn emit_in(ds: &[Diagnostic], label: &str, src: &[u8]) {
    for d in ds {
        if HUMAN.load(Ordering::Relaxed) {
            eprintln!("{}", render_human(d, label, src));
        } else {
            eprintln!("{}", d.to_json());
        }
    }
}

/// v1.11：import で複数のファイルからなるプログラムの診断を出す。`file` の付いた診断はそのファイルの source で表示する。
fn emit_files(ds: &[Diagnostic], files: &[(String, Vec<u8>)]) {
    for d in ds {
        let (label, src) = match d
            .file
            .as_deref()
            .and_then(|f| files.iter().find(|(n, _)| n == f))
        {
            Some((n, b)) => (n.as_str(), b.as_slice()),
            None => files
                .first()
                .map_or(("<program>", &[][..]), |(n, b)| (n.as_str(), b.as_slice())),
        };
        emit_in(std::slice::from_ref(d), label, src);
    }
}

fn envelope(name: &str, reason: &str) {
    eprintln!(
        "{{\"result\":{},\"reason\":{}}}",
        json_string(name),
        json_string(reason)
    );
}

/// 診断を出し、受理されていれば TypedProgram を返す。
fn compiled(
    r: CompileResult,
    label: &str,
    src: &[u8],
    warn: bool,
) -> Option<tlvm::checker::TypedProgram> {
    emit_in(r.errors(), label, src);
    if warn || !matches!(r, CompileResult::Accepted { .. }) {
        emit_in(r.warnings(), label, src);
    }
    match r {
        CompileResult::Accepted { program, .. } => Some(program),
        _ => None,
    }
}

fn compile_file(path: &str, as_ast: bool) -> Result<Option<tlvm::checker::TypedProgram>, String> {
    compile_checked(path, as_ast, true)
}

/// `fmt` の前の検査。`check` と同じ検査を通ったものだけを整形する。受理されたときは警告を出さない。
fn fmt_checks(path: &str, as_ast: bool) -> Result<bool, String> {
    Ok(compile_checked(path, as_ast, false)?.is_some())
}

/// 検査する。`warn` が偽なら、受理されたときの警告は出さない（拒否されたときは出す）。
fn compile_checked(
    path: &str,
    as_ast: bool,
    warn: bool,
) -> Result<Option<tlvm::checker::TypedProgram>, String> {
    let data = read(path)?;
    let sp = StaticProfile::default();
    Ok(if as_ast || path.ends_with(".json") {
        match compile_ast(&data, &sp, &AstTransportProfile::default()) {
            AstCompile::AstBoundaryFailure => {
                envelope("AstBoundaryFailure", "InvalidUtf8");
                None
            }
            AstCompile::AstInvalid(d) => {
                emit_in(&d, path, &data);
                None
            }
            AstCompile::Result(r) => compiled(r, path, &data, warn),
        }
    } else if path == "-" {
        match compile(&data, &sp) {
            SourceCompile::SourceBoundaryFailure => {
                envelope("SourceBoundaryFailure", "InvalidSourceEncoding");
                None
            }
            SourceCompile::Result(r) => compiled(r, path, &data, warn),
        }
    } else {
        // v1.11：import をたどって一つのプログラムにまとめて検査する（import がなければ今までどおり）
        match compile_path(path, &sp)? {
            (SourceCompile::SourceBoundaryFailure, _) => {
                envelope("SourceBoundaryFailure", "InvalidSourceEncoding");
                None
            }
            (SourceCompile::Result(r), files) => {
                emit_files(r.errors(), &files);
                if warn || !matches!(r, CompileResult::Accepted { .. }) {
                    emit_files(r.warnings(), &files);
                }
                match r {
                    CompileResult::Accepted { program, .. } => Some(program),
                    _ => None,
                }
            }
        }
    })
}

/// AST の JSON を標準出力に書く。字句表の語を変数名に使っていれば、その診断を出して終了コードは 1。
fn ast_out(p: &Program, file: &str) -> Result<ExitCode, String> {
    match encode_ast(p) {
        Ok(json) => {
            println!("{json}");
            Ok(ExitCode::SUCCESS)
        }
        Err(ds) => {
            emit_in(&ds, file, &read(file)?);
            Ok(ExitCode::from(1))
        }
    }
}

/// v1.11：`tlvm ast` 用。import があればまとめたプログラムを、なければ `parse_file` の結果を返す。
fn parse_merged_file(path: &str, as_ast: bool) -> Result<Option<Program>, String> {
    use tlvm::imports::{parse_merged, resolve, FsLoader, Resolved};
    if as_ast || path.ends_with(".json") || path == "-" {
        return parse_file(path, as_ast);
    }
    let data = read(path)?;
    let sp = StaticProfile::default();
    let rel = std::path::Path::new(path)
        .file_name()
        .map(|n| n.to_string_lossy().into_owned())
        .unwrap_or_default();
    match resolve(path, &rel, &data, &mut FsLoader::new(path), &sp) {
        Resolved::Single => parse_file(path, as_ast),
        Resolved::Merged(m) => match parse_merged(&m, &sp) {
            Ok(p) => {
                // 展開の誤りもファイルに戻して出す
                if needs_expansion(&p) {
                    if let Err(d) = expand(&p) {
                        emit_files(&m.attribute(d), &m.files);
                        return Ok(None);
                    }
                }
                // 字句表の語を変数名に使った箇所も、ファイルに戻して出す（encode_ast と同じ拒否）
                if let Some(d) = tlvm::softnames::keyword_name_error(&p) {
                    emit_files(&m.attribute(vec![d]), &m.files);
                    return Ok(None);
                }
                Ok(Some(p))
            }
            Err(d) => {
                emit_files(&d, &m.files);
                Ok(None)
            }
        },
        Resolved::Rejected { errors, files } => {
            emit_files(&errors, &files);
            Ok(None)
        }
        Resolved::SourceBoundaryFailure { .. } => {
            envelope("SourceBoundaryFailure", "InvalidSourceEncoding");
            Ok(None)
        }
    }
}

fn parse_file(path: &str, as_ast: bool) -> Result<Option<Program>, String> {
    let data = read(path)?;
    let sp = StaticProfile::default();
    Ok(if as_ast || path.ends_with(".json") {
        match parse_ast(&data, &sp, &AstTransportProfile::default()) {
            ParsedAst::Program(p) => Some(p),
            ParsedAst::Failed(AstCompile::AstInvalid(d)) => {
                emit_in(&d, path, &data);
                None
            }
            ParsedAst::Failed(AstCompile::Result(r)) => {
                compiled(r, path, &data, true).map(|t| t.program)
            }
            ParsedAst::Failed(_) => {
                envelope("AstBoundaryFailure", "InvalidUtf8");
                None
            }
        }
    } else {
        match parse_source(&data, &sp) {
            Parsed::Program(p) => Some(p),
            Parsed::Failed(SourceCompile::Result(r)) => {
                compiled(r, path, &data, true).map(|t| t.program)
            }
            Parsed::Failed(SourceCompile::SourceBoundaryFailure) => {
                envelope("SourceBoundaryFailure", "InvalidSourceEncoding");
                None
            }
        }
    })
}

/// 入力を読む。plain なら普通の JSON、そうでなければ値 JSON（§9.2）。
fn decode(t: &tlvm::syntax::Ty, data: &[u8], plain: bool) -> DecodeResult {
    if plain {
        decode_plain_input(t, data, &InputProfile::default())
    } else {
        decode_input(t, data, &InputProfile::default())
    }
}

/// 診断の span を `off` だけずらす（ファイルの一部を復号したときに、ファイル上の位置へ戻す）。
fn shifted(ds: Vec<Diagnostic>, off: usize) -> Vec<Diagnostic> {
    ds.into_iter()
        .map(|mut d| {
            d.span = (d.span.0 + off, d.span.1 + off);
            if let Some(r) = d.repair.as_mut() {
                r.target_span = (r.target_span.0 + off, r.target_span.1 + off);
            }
            d
        })
        .collect()
}

fn run_cmd(
    file: &str,
    input: &str,
    as_ast: bool,
    plain: bool,
    stats: bool,
) -> Result<ExitCode, String> {
    let Some(p) = compile_file(file, as_ast)? else {
        return Ok(ExitCode::from(1));
    };
    let (label, data) = if input == "-" {
        ("<stdin>".to_string(), read("-")?)
    } else if let Some(path) = input.strip_prefix('@') {
        (path.to_string(), read(path)?)
    } else {
        ("<input>".to_string(), input.as_bytes().to_vec())
    };
    // 入力は復号と評価を `run_input` が一つのスレッドで行う（検証済みの復号器は一度だけ走る）
    let outcome = run_input(
        &p,
        &data,
        plain,
        &InputProfile::default(),
        &ExecutionProfile::default(),
        &HostPolicy::default(),
    )?;
    let result = match outcome {
        InputOutcome::Ran(r) => r,
        InputOutcome::Invalid(d) => {
            emit_in(&d, &label, &data);
            return Ok(ExitCode::from(1));
        }
        InputOutcome::InputBoundaryFailure => {
            envelope("InputBoundaryFailure", "InvalidUtf8");
            return Ok(ExitCode::from(1));
        }
    };
    match result {
        RunResult::Completed {
            output,
            steps,
            allocated_nodes,
        } => {
            if plain {
                println!("{}", encode_plain(&p.output_type, &output)?);
            } else {
                println!("{output}");
            }
            if stats {
                eprintln!("{{\"steps\":{steps},\"allocated_nodes\":{allocated_nodes}}}");
            }
            Ok(ExitCode::SUCCESS)
        }
        RunResult::ResourceExhausted {
            kind,
            observed,
            limit,
        } => {
            eprintln!("{{\"result\":\"ResourceExhausted\",\"kind\":\"{kind}\",\"observed\":{observed},\"limit\":{limit}}}");
            Ok(ExitCode::from(2))
        }
        RunResult::HostAborted(r) => {
            envelope("HostAborted", &r);
            Ok(ExitCode::from(2))
        }
        RunResult::InternalFault(r) => {
            envelope("InternalFault", &r);
            Ok(ExitCode::from(3))
        }
    }
}

/// プログラムをコマンドとして実行する（v1.3 の入出力ランタイム。検証されていない接着部分）。
///
/// 入力（標準入力の全文、コマンドライン引数、または v1.13 の標準入力の行の辞書）を検証済みの復号器で読み、
/// 検証済みの評価器で実行する（辞書は `run --plain` と同じく普通の JSON を経由する）。出力が String なら、
/// その文字列をそのまま標準出力に書く。
fn exec_cmd(file: &str, args: &[String]) -> Result<ExitCode, String> {
    use tlvm::runtime::{exec, exec_input, ExecInput, ExecResult, ENTRY_SHAPES};
    let Some(p) = compile_file(file, false)? else {
        return Ok(ExitCode::from(1));
    };
    let Some(shape) = exec_input(&p) else {
        envelope(
            "UnsupportedEntry",
            &format!(
                "exec の entry の入力型は {ENTRY_SHAPES} のどれか（この entry は {}）",
                p.input_type
            ),
        );
        return Ok(ExitCode::from(64));
    };
    let stdin = if shape == ExecInput::Args {
        String::new()
    } else {
        match String::from_utf8(read("-")?) {
            Ok(t) => t,
            Err(_) => {
                envelope("InputBoundaryFailure", "InvalidUtf8");
                return Ok(ExitCode::from(1));
            }
        }
    };
    match exec(
        &p,
        args,
        &stdin,
        &ExecutionProfile::exec(),
        &HostPolicy::default(),
    )? {
        ExecResult::Output(o) => {
            use std::io::Write;
            let mut out = std::io::stdout().lock();
            out.write_all(o.as_bytes()).map_err(|e| e.to_string())?;
            out.flush().map_err(|e| e.to_string())?;
            Ok(ExitCode::SUCCESS)
        }
        // v1.4：出力型 Result<String, String> の err(s) は s を標準エラーへ、終了コード 1
        ExecResult::Failure(o) => {
            use std::io::Write;
            let mut err = std::io::stderr().lock();
            err.write_all(o.as_bytes()).map_err(|e| e.to_string())?;
            err.flush().map_err(|e| e.to_string())?;
            Ok(ExitCode::from(1))
        }
        // v1.13：標準入力の行の形が合わない（run の InputBoundaryFailure と同じ envelope と終了コード）
        ExecResult::InputBoundaryFailure(reason) => {
            envelope("InputBoundaryFailure", &reason);
            Ok(ExitCode::from(1))
        }
        // v1.13：辞書の復号の診断。span は標準入力の上の位置（`run` の診断と同じ形）
        ExecResult::InputInvalid(ds) => {
            emit_in(&ds, "<stdin>", stdin.as_bytes());
            Ok(ExitCode::from(1))
        }
        ExecResult::Stopped(RunResult::ResourceExhausted {
            kind,
            observed,
            limit,
        }) => {
            eprintln!("{{\"result\":\"ResourceExhausted\",\"kind\":\"{kind}\",\"observed\":{observed},\"limit\":{limit}}}");
            Ok(ExitCode::from(2))
        }
        ExecResult::Stopped(RunResult::HostAborted(r)) => {
            envelope("HostAborted", &r);
            Ok(ExitCode::from(2))
        }
        ExecResult::Stopped(r) => {
            envelope("InternalFault", &format!("{r:?}"));
            Ok(ExitCode::from(3))
        }
    }
}

/// `prog.tlvm` → `prog.tests.json`
fn default_cases(file: &str) -> String {
    let stem = file.rsplit_once('.').map_or(file, |(s, _)| s);
    format!("{stem}.tests.json")
}

enum Outcome {
    Pass,
    Fail { expected: String, actual: String },
    Error(String),
}

/// テストケースの一件を実行する。入力・期待出力は cases ファイルの一部として読み、診断の位置はファイル上に直す。
fn run_case(
    p: &tlvm::checker::TypedProgram,
    case: &JNode,
    data: &[u8],
    plain: bool,
    label: &str,
) -> Result<Outcome, String> {
    let (Some(input), Some(expected)) = (case.get("input"), case.get("expected")) else {
        return Ok(Outcome::Error(
            "case には \"input\" と \"expected\" が必要です".into(),
        ));
    };
    // 入力は一度だけ読んで評価する（`run_input`）。期待値は評価の結果と比べるために読む
    let outcome = match run_input(
        p,
        &data[input.start..input.end],
        plain,
        &InputProfile::default(),
        &ExecutionProfile::default(),
        &HostPolicy::default(),
    )? {
        InputOutcome::Ran(r) => r,
        InputOutcome::Invalid(d) => {
            emit_in(&shifted(d, input.start), label, data);
            return Ok(Outcome::Error(format!(
                "input を型 {} として読めません",
                p.input_type
            )));
        }
        InputOutcome::InputBoundaryFailure => {
            return Ok(Outcome::Error("input が UTF-8 ではありません".into()))
        }
    };
    let want = match decode(&p.output_type, &data[expected.start..expected.end], plain) {
        DecodeResult::Decoded(tv) => encode_value(&tv.value),
        DecodeResult::Invalid(d) => {
            emit_in(&shifted(d, expected.start), label, data);
            return Ok(Outcome::Error(format!(
                "expected を型 {} として読めません",
                p.output_type
            )));
        }
        DecodeResult::InputBoundaryFailure => {
            return Ok(Outcome::Error("expected が UTF-8 ではありません".into()))
        }
    };
    let show = |canonical: &str| -> Result<String, String> {
        if plain {
            encode_plain(&p.output_type, canonical)
        } else {
            Ok(canonical.to_string())
        }
    };
    Ok(match outcome {
        RunResult::Completed { output, .. } if output == want => Outcome::Pass,
        RunResult::Completed { output, .. } => Outcome::Fail {
            expected: show(&want)?,
            actual: show(&output)?,
        },
        RunResult::ResourceExhausted {
            kind,
            observed,
            limit,
        } => Outcome::Error(format!(
            "ResourceExhausted {kind} (observed {observed}, limit {limit})"
        )),
        RunResult::HostAborted(r) => Outcome::Error(format!("HostAborted {r}")),
        RunResult::InternalFault(r) => Outcome::Error(format!("InternalFault {r}")),
    })
}

fn test_cmd(
    file: &str,
    cases: Option<&str>,
    as_ast: bool,
    plain: bool,
) -> Result<ExitCode, String> {
    let Some(p) = compile_file(file, as_ast)? else {
        return Ok(ExitCode::from(1));
    };
    let cases_path = cases.map_or_else(|| default_cases(file), str::to_string);
    let data = read(&cases_path)?;
    let root = strict_json::parse(&data, 1024).map_err(|f| {
        format!(
            "{cases_path}: JSON として読めません（{:?}、byte {}）",
            f.kind, f.span.0
        )
    })?;
    if root.kind != JKind::Array {
        return Err(format!("{cases_path}: テストケースの配列が必要です"));
    }
    let human = HUMAN.load(Ordering::Relaxed);
    let (mut passed, mut failed) = (0usize, 0usize);
    for (i, case) in root.items.iter().enumerate() {
        let name = match case.get("name") {
            Some(n) if n.kind == JKind::String => n.text.clone(),
            _ => format!("#{}", i + 1),
        };
        let outcome = if case.kind == JKind::Object {
            run_case(&p, case, &data, plain, &cases_path)?
        } else {
            Outcome::Error("case は object でなければなりません".into())
        };
        let n = json_string(&name);
        match outcome {
            Outcome::Pass => {
                passed += 1;
                if human {
                    println!("PASS {name}");
                } else {
                    println!("{{\"case\":{n},\"result\":\"pass\"}}");
                }
            }
            Outcome::Fail { expected, actual } => {
                failed += 1;
                if human {
                    println!("FAIL {name}: expected {expected}, got {actual}");
                } else {
                    println!("{{\"case\":{n},\"result\":\"fail\",\"expected\":{expected},\"actual\":{actual}}}");
                }
            }
            Outcome::Error(why) => {
                failed += 1;
                if human {
                    println!("ERROR {name}: {why}");
                } else {
                    println!(
                        "{{\"case\":{n},\"result\":\"error\",\"reason\":{}}}",
                        json_string(&why)
                    );
                }
            }
        }
    }
    if human {
        println!("{passed} passed, {failed} failed");
    } else {
        println!("{{\"passed\":{passed},\"failed\":{failed}}}");
    }
    Ok(if failed == 0 {
        ExitCode::SUCCESS
    } else {
        ExitCode::from(1)
    })
}

fn real_main() -> Result<ExitCode, String> {
    let args: Vec<String> = std::env::args().skip(1).collect();
    // exec の FILE より後ろはプログラムへの引数なので、オプションとして読まない
    if args.first().map(String::as_str) == Some("exec") {
        return match args.get(1) {
            Some(file) => exec_cmd(file, &args[2..]),
            None => Ok(usage()),
        };
    }
    // v1.12：repl と lsp
    match args.first().map(String::as_str) {
        Some("repl") => {
            use std::io::IsTerminal;
            let file = match &args[1..] {
                [] => None,
                [f] if !f.starts_with("--") => Some(f.as_str()),
                _ => return Ok(usage()),
            };
            let prompt = std::io::stdin().is_terminal();
            let code = tlvm::repl::repl(
                file,
                &mut std::io::stdin().lock(),
                &mut std::io::stdout().lock(),
                prompt,
            )
            .map_err(|e| e.to_string())?;
            return Ok(ExitCode::from(code as u8));
        }
        Some("lsp") => {
            // editor が付ける --stdio は受け付けて無視する（通信は常に標準入出力）
            if args[1..].iter().any(|a| a != "--stdio") {
                return Ok(usage());
            }
            let code =
                tlvm::lsp::serve(&mut std::io::stdin().lock(), &mut std::io::stdout().lock())
                    .map_err(|e| e.to_string())?;
            return Ok(ExitCode::from(code as u8));
        }
        _ => {}
    }
    let flags: Vec<&str> = args
        .iter()
        .filter(|a| a.starts_with("--"))
        .map(|s| s.as_str())
        .collect();
    let pos: Vec<&str> = args
        .iter()
        .filter(|a| !a.starts_with("--"))
        .map(|s| s.as_str())
        .collect();
    let known = ["--ast", "--stats", "--plain", "--human", "--canonical"];
    if let Some(f) = flags.iter().find(|f| !known.contains(f)) {
        eprintln!("tlvm: unknown option {f}");
        return Ok(usage());
    }
    let as_ast = flags.contains(&"--ast");
    HUMAN.store(flags.contains(&"--human"), Ordering::Relaxed);
    match pos.as_slice() {
        ["check", file] => match compile_file(file, as_ast)? {
            Some(p) => {
                // v1.7：terminates は `rec fn` がないとき true（停止を証明済み）。あれば false（止まらない再帰は資源上限で打ち切る）
                println!(
                    "{{\"result\":\"Accepted\",\"entry\":{},\"input_type\":{},\"output_type\":{},\"terminates\":{}}}",
                    json_string(&p.entry),
                    json_string(&p.input_type.to_string()),
                    json_string(&p.output_type.to_string()),
                    p.terminates()
                );
                if HUMAN.load(Ordering::Relaxed) && !p.terminates() {
                    eprintln!(
                        "note: termination is not guaranteed: rec fn {} may recurse without bound (a runaway run stops at the steps or depth limit)",
                        p.rec_functions().join(", ")
                    );
                }
                Ok(ExitCode::SUCCESS)
            }
            None => Ok(ExitCode::from(1)),
        },
        // 検査を通ったプログラムだけを整形する（`check` と同じ検査）。拒否なら診断を出して終了コードは 1
        ["fmt", file] if !fmt_checks(file, as_ast)? => Ok(ExitCode::from(1)),
        ["fmt", file] => match parse_file(file, as_ast)? {
            // v1.1：レコード（v1.4：直和型と match、v1.5：map など、v1.6：loop）を含むプログラムは検証済み formatter の対象外。
            // 診断用 formatter で整形する
            // v1.11：import の行を含むファイルも（検証済み formatter は import を知らない）。整形するのは与えたファイルだけ
            Some(p) if needs_glue(&p) || !p.imports.is_empty() => {
                print!("{}", format_program(&p));
                Ok(ExitCode::SUCCESS)
            }
            Some(p) => {
                // 正準ソースは検証済み formatter が出す。source なら元の source を、AST なら診断用
                // formatter の出力を検証済み parser に通し、診断用 formatter の結果と照合する。
                // v1.7：検証済み formatter は `rec` を知らないので、印を外したもので照合し、印を付けた整形を出す
                let text = format_program(&p);
                let bare = format_program(&p.unmarked());
                let src = if as_ast || file.ends_with(".json") {
                    bare.clone()
                } else {
                    without_rec_markers(
                        &String::from_utf8(read(file)?).map_err(|e| e.to_string())?,
                        &p,
                    )
                };
                match canonical(&src, &StaticProfile::default()) {
                    Some(o) if o == bare => {
                        print!("{text}");
                        Ok(ExitCode::SUCCESS)
                    }
                    _ => {
                        envelope("InternalFault", "verified-formatter-mismatch");
                        Ok(ExitCode::from(3))
                    }
                }
            }
            None => Ok(ExitCode::from(1)),
        },
        // v1.11：import があれば、まとめたプログラムを出す
        ["ast", file] => match parse_merged_file(file, as_ast)? {
            // v1.1：AST transport にレコード（v1.4：直和型と match）の形はないので、展開・lower したものを出す
            // （v1.5 の map など・v1.6 の loop は AST transport の tag があるのでそのまま出す）。字句表の語を変数名に
            // 使ったプログラムは付け替えず、encode_ast が E-AST-IDENTIFIER で拒否する（§4.2）
            Some(p) if needs_expansion(&p) => match expand(&p) {
                Ok(px) => ast_out(&lower(&px), file),
                Err(d) => {
                    emit_in(&d, file, &read(file)?);
                    Ok(ExitCode::from(1))
                }
            },
            Some(p) => ast_out(&p, file),
            None => Ok(ExitCode::from(1)),
        },
        ["run", file, input] => run_cmd(
            file,
            input,
            as_ast,
            flags.contains(&"--plain"),
            flags.contains(&"--stats"),
        ),
        ["test", file] => test_cmd(file, None, as_ast, !flags.contains(&"--canonical")),
        ["test", file, cases] => {
            test_cmd(file, Some(cases), as_ast, !flags.contains(&"--canonical"))
        }
        _ => Ok(usage()),
    }
}

fn main() -> ExitCode {
    match real_main() {
        Ok(c) => c,
        Err(e) => {
            eprintln!("tlvm: {e}");
            ExitCode::from(66)
        }
    }
}
