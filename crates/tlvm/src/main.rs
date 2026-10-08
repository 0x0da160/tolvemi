//! tlvm コマンド。
//!
//!   tlvm check FILE           静的検査（.tlvm source、.json は ast_codec_v1）
//!   tlvm run FILE INPUT       検査・入力 decode・実行（INPUT は JSON 文字列、@path、- は stdin）
//!   tlvm fmt FILE             正準ソースを出力
//!   tlvm ast FILE             ast_codec_v1 JSON を出力
//!   tlvm test FILE [CASES]    入力と期待出力の組を実行して照合（CASES の既定は FILE.tests.json）
//!
//! 診断は一行一 JSON object で stderr へ、結果は stdout へ出す。
//!
//!   --plain   run の入出力を普通の JSON で読み書きする（対応は plain モジュール）
//!   --human   診断を `file:行:列: error[CODE]: …` の形で、該当行と修復ヒントを添えて出す

use std::io::Read;
use std::process::ExitCode;
use std::sync::atomic::{AtomicBool, Ordering};
use tlvm::api::*;
use tlvm::diagnostics::{json_string, render_human, Diagnostic};
use tlvm::plain::encode_plain;
use tlvm::strict_json::{self, JKind, JNode};
use tlvm::values::encode_value;
use tlvm::formatter::{encode_ast, format_program};
use tlvm::profiles::*;
use tlvm::syntax::Program;
use tlvm::{DecodeResult, RunResult};

static HUMAN: AtomicBool = AtomicBool::new(false);

fn usage() -> ExitCode {
    eprintln!(
        "usage: tlvm check|fmt|ast FILE [--ast] [--human]\n       tlvm run FILE INPUT [--ast] [--stats] [--plain] [--human]\n       tlvm test FILE [CASES] [--ast] [--canonical] [--human]"
    );
    ExitCode::from(64)
}

fn read(path: &str) -> Result<Vec<u8>, String> {
    if path == "-" {
        let mut v = vec![];
        std::io::stdin().read_to_end(&mut v).map_err(|e| e.to_string())?;
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

fn envelope(name: &str, reason: &str) {
    eprintln!("{{\"result\":{},\"reason\":{}}}", json_string(name), json_string(reason));
}

/// 診断を出し、受理されていれば TypedProgram を返す。
fn compiled(r: CompileResult, label: &str, src: &[u8]) -> Option<tlvm::checker::TypedProgram> {
    emit_in(r.errors(), label, src);
    emit_in(r.warnings(), label, src);
    match r {
        CompileResult::Accepted { program, .. } => Some(program),
        _ => None,
    }
}

fn compile_file(path: &str, as_ast: bool) -> Result<Option<tlvm::checker::TypedProgram>, String> {
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
            AstCompile::Result(r) => compiled(r, path, &data),
        }
    } else {
        match compile(&data, &sp) {
            SourceCompile::SourceBoundaryFailure => {
                envelope("SourceBoundaryFailure", "InvalidSourceEncoding");
                None
            }
            SourceCompile::Result(r) => compiled(r, path, &data),
        }
    })
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
            ParsedAst::Failed(AstCompile::Result(r)) => compiled(r, path, &data).map(|t| t.program),
            ParsedAst::Failed(_) => {
                envelope("AstBoundaryFailure", "InvalidUtf8");
                None
            }
        }
    } else {
        match parse_source(&data, &sp) {
            Parsed::Program(p) => Some(p),
            Parsed::Failed(SourceCompile::Result(r)) => compiled(r, path, &data).map(|t| t.program),
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

fn run_cmd(file: &str, input: &str, as_ast: bool, plain: bool, stats: bool) -> Result<ExitCode, String> {
    let Some(p) = compile_file(file, as_ast)? else { return Ok(ExitCode::from(1)) };
    let (label, data) = if input == "-" {
        ("<stdin>".to_string(), read("-")?)
    } else if let Some(path) = input.strip_prefix('@') {
        (path.to_string(), read(path)?)
    } else {
        ("<input>".to_string(), input.as_bytes().to_vec())
    };
    let tv = match decode(&p.input_type, &data, plain) {
        DecodeResult::Decoded(tv) => tv,
        DecodeResult::Invalid(d) => {
            emit_in(&d, &label, &data);
            return Ok(ExitCode::from(1));
        }
        DecodeResult::InputBoundaryFailure => {
            envelope("InputBoundaryFailure", "InvalidUtf8");
            return Ok(ExitCode::from(1));
        }
    };
    match run(&p, &tv, &ExecutionProfile::default(), &HostPolicy::default())? {
        RunResult::Completed { output, steps, allocated_nodes } => {
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
        RunResult::ResourceExhausted { kind, observed, limit } => {
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
fn run_case(p: &tlvm::checker::TypedProgram, case: &JNode, data: &[u8], plain: bool, label: &str) -> Result<Outcome, String> {
    let (Some(input), Some(expected)) = (case.get("input"), case.get("expected")) else {
        return Ok(Outcome::Error("case には \"input\" と \"expected\" が必要です".into()));
    };
    let mut values = vec![];
    for (node, ty, what) in [(input, &p.input_type, "input"), (expected, &p.output_type, "expected")] {
        match decode(ty, &data[node.start..node.end], plain) {
            DecodeResult::Decoded(tv) => values.push(tv),
            DecodeResult::Invalid(d) => {
                emit_in(&shifted(d, node.start), label, data);
                return Ok(Outcome::Error(format!("{what} を型 {ty} として読めません")));
            }
            DecodeResult::InputBoundaryFailure => return Ok(Outcome::Error(format!("{what} が UTF-8 ではありません"))),
        }
    }
    let want = encode_value(&values[1].value);
    let show = |canonical: &str| -> Result<String, String> {
        if plain {
            encode_plain(&p.output_type, canonical)
        } else {
            Ok(canonical.to_string())
        }
    };
    Ok(match run(p, &values[0], &ExecutionProfile::default(), &HostPolicy::default())? {
        RunResult::Completed { output, .. } if output == want => Outcome::Pass,
        RunResult::Completed { output, .. } => Outcome::Fail { expected: show(&want)?, actual: show(&output)? },
        RunResult::ResourceExhausted { kind, observed, limit } => {
            Outcome::Error(format!("ResourceExhausted {kind} (observed {observed}, limit {limit})"))
        }
        RunResult::HostAborted(r) => Outcome::Error(format!("HostAborted {r}")),
        RunResult::InternalFault(r) => Outcome::Error(format!("InternalFault {r}")),
    })
}

fn test_cmd(file: &str, cases: Option<&str>, as_ast: bool, plain: bool) -> Result<ExitCode, String> {
    let Some(p) = compile_file(file, as_ast)? else { return Ok(ExitCode::from(1)) };
    let cases_path = cases.map_or_else(|| default_cases(file), str::to_string);
    let data = read(&cases_path)?;
    let root = strict_json::parse(&data, 1024).map_err(|f| format!("{cases_path}: JSON として読めません（{:?}、byte {}）", f.kind, f.span.0))?;
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
                    println!("{{\"case\":{n},\"result\":\"error\",\"reason\":{}}}", json_string(&why));
                }
            }
        }
    }
    if human {
        println!("{passed} passed, {failed} failed");
    } else {
        println!("{{\"passed\":{passed},\"failed\":{failed}}}");
    }
    Ok(if failed == 0 { ExitCode::SUCCESS } else { ExitCode::from(1) })
}

fn real_main() -> Result<ExitCode, String> {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let flags: Vec<&str> = args.iter().filter(|a| a.starts_with("--")).map(|s| s.as_str()).collect();
    let pos: Vec<&str> = args.iter().filter(|a| !a.starts_with("--")).map(|s| s.as_str()).collect();
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
                println!(
                    "{{\"result\":\"Accepted\",\"entry\":{},\"input_type\":{},\"output_type\":{}}}",
                    json_string(&p.entry),
                    json_string(&p.input_type.to_string()),
                    json_string(&p.output_type.to_string())
                );
                Ok(ExitCode::SUCCESS)
            }
            None => Ok(ExitCode::from(1)),
        },
        ["fmt", file] => match parse_file(file, as_ast)? {
            // v1.1：レコードを含むプログラムは検証済み formatter の対象外。診断用 formatter で整形する
            Some(p) if tlvm::records::has_records(&p) => {
                print!("{}", format_program(&p));
                Ok(ExitCode::SUCCESS)
            }
            Some(p) => {
                // 正準ソースは検証済み formatter が出す。source なら元の source を、AST なら診断用
                // formatter の出力を検証済み parser に通し、診断用 formatter の結果と照合する。
                let text = format_program(&p);
                let src = if as_ast || file.ends_with(".json") {
                    text.clone()
                } else {
                    String::from_utf8(read(file)?).map_err(|e| e.to_string())?
                };
                match canonical(&src, &StaticProfile::default()) {
                    Some(o) if o == text => {
                        print!("{o}");
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
        ["ast", file] => match parse_file(file, as_ast)? {
            // v1.1：AST transport にレコードの形と文脈キーワードの変数名はないので、展開・付け替えしたものを出す
            Some(p) if tlvm::records::has_records(&p) => match tlvm::records::expand(&p) {
                Ok(px) => {
                    println!("{}", encode_ast(&tlvm::softnames::rename(&tlvm::records::lower(&px))));
                    Ok(ExitCode::SUCCESS)
                }
                Err(d) => {
                    emit_in(&d, file, &read(file)?);
                    Ok(ExitCode::from(1))
                }
            },
            Some(p) => {
                println!("{}", encode_ast(&tlvm::softnames::rename(&p)));
                Ok(ExitCode::SUCCESS)
            }
            None => Ok(ExitCode::from(1)),
        },
        ["run", file, input] => run_cmd(file, input, as_ast, flags.contains(&"--plain"), flags.contains(&"--stats")),
        ["test", file] => test_cmd(file, None, as_ast, !flags.contains(&"--canonical")),
        ["test", file, cases] => test_cmd(file, Some(cases), as_ast, !flags.contains(&"--canonical")),
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
