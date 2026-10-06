//! tlvm コマンド。
//!
//!   tlvm check FILE           静的検査（.tlvm source、.json は ast_codec_v1）
//!   tlvm run FILE INPUT       検査・入力 decode・実行（INPUT は JSON 文字列、@path、- は stdin）
//!   tlvm fmt FILE             正準ソースを出力
//!   tlvm ast FILE             ast_codec_v1 JSON を出力
//!
//! 診断は一行一 JSON object で stderr へ、結果は stdout へ出す。

use std::io::Read;
use std::process::ExitCode;
use tlvm::api::*;
use tlvm::diagnostics::{json_string, Diagnostic};
use tlvm::formatter::{encode_ast, format_program};
use tlvm::profiles::*;
use tlvm::syntax::Program;
use tlvm::{DecodeResult, RunResult};

fn usage() -> ExitCode {
    eprintln!("usage: tlvm check|fmt|ast FILE [--ast]\n       tlvm run FILE INPUT [--ast] [--stats]");
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

fn emit(ds: &[Diagnostic]) {
    for d in ds {
        eprintln!("{}", d.to_json());
    }
}

fn envelope(name: &str, reason: &str) {
    eprintln!("{{\"result\":{},\"reason\":{}}}", json_string(name), json_string(reason));
}

/// 診断を出し、受理されていれば TypedProgram を返す。
fn compiled(r: CompileResult) -> Option<tlvm::checker::TypedProgram> {
    emit(r.errors());
    emit(r.warnings());
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
                emit(&d);
                None
            }
            AstCompile::Result(r) => compiled(r),
        }
    } else {
        match compile(&data, &sp) {
            SourceCompile::SourceBoundaryFailure => {
                envelope("SourceBoundaryFailure", "InvalidSourceEncoding");
                None
            }
            SourceCompile::Result(r) => compiled(r),
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
                emit(&d);
                None
            }
            ParsedAst::Failed(AstCompile::Result(r)) => compiled(r).map(|t| t.program),
            ParsedAst::Failed(_) => {
                envelope("AstBoundaryFailure", "InvalidUtf8");
                None
            }
        }
    } else {
        match parse_source(&data, &sp) {
            Parsed::Program(p) => Some(p),
            Parsed::Failed(SourceCompile::Result(r)) => compiled(r).map(|t| t.program),
            Parsed::Failed(SourceCompile::SourceBoundaryFailure) => {
                envelope("SourceBoundaryFailure", "InvalidSourceEncoding");
                None
            }
        }
    })
}

fn real_main() -> Result<ExitCode, String> {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let flags: Vec<&str> = args.iter().filter(|a| a.starts_with("--")).map(|s| s.as_str()).collect();
    let pos: Vec<&str> = args.iter().filter(|a| !a.starts_with("--")).map(|s| s.as_str()).collect();
    let as_ast = flags.contains(&"--ast");
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
            Some(p) => {
                println!("{}", encode_ast(&p));
                Ok(ExitCode::SUCCESS)
            }
            None => Ok(ExitCode::from(1)),
        },
        ["run", file, input] => {
            let Some(p) = compile_file(file, as_ast)? else { return Ok(ExitCode::from(1)) };
            let data = if *input == "-" {
                read("-")?
            } else if let Some(path) = input.strip_prefix('@') {
                read(path)?
            } else {
                input.as_bytes().to_vec()
            };
            let tv = match decode_input(&p.input_type, &data, &InputProfile::default()) {
                DecodeResult::Decoded(tv) => tv,
                DecodeResult::Invalid(d) => {
                    emit(&d);
                    return Ok(ExitCode::from(1));
                }
                DecodeResult::InputBoundaryFailure => {
                    envelope("InputBoundaryFailure", "InvalidUtf8");
                    return Ok(ExitCode::from(1));
                }
            };
            match run(&p, &tv, &ExecutionProfile::default(), &HostPolicy::default())? {
                RunResult::Completed { output, steps, allocated_nodes } => {
                    println!("{output}");
                    if flags.contains(&"--stats") {
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
