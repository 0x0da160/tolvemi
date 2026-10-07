//! 公開 API：compile / compile_ast / decode_input / run（設計書 §9.1）。

use crate::ast_codec::{self, Transport};
use crate::checker::{check_program, CheckOutcome, TypedProgram, VerifiedProgram, WorkCounter};
use crate::diagnostics::{finalize, suggest_repairs, Diagnostic};
use crate::plain::{canonical_profile, decode_plain, PlainDecode};
use crate::evaluator::{self, RunResult};
use crate::lexer::lex;
use crate::parser::{ParseOutcome, Parser};
use crate::profiles::*;
use crate::{records, softnames};
use crate::syntax::{Program, Ty};
use crate::values::{self, DecodeResult, TypedValue};
use crate::formatter::format_program;
use std::sync::Arc;
use tlvm_verified::pipeline::{canonical_source, compile_source, Compiled};
use tlvm_verified::resolve::resolve_e;
use tlvm_verified::surface::parse_e;

#[derive(Debug)]
pub enum CompileResult {
    Accepted { program: TypedProgram, warnings: Vec<Diagnostic>, work: Option<WorkCounter> },
    Rejected { errors: Vec<Diagnostic>, warnings: Vec<Diagnostic>, work: Option<WorkCounter> },
}

impl CompileResult {
    pub fn errors(&self) -> &[Diagnostic] {
        match self {
            CompileResult::Accepted { .. } => &[],
            CompileResult::Rejected { errors, .. } => errors,
        }
    }
    pub fn warnings(&self) -> &[Diagnostic] {
        match self {
            CompileResult::Accepted { warnings, .. } | CompileResult::Rejected { warnings, .. } => warnings,
        }
    }
    pub fn work(&self) -> Option<WorkCounter> {
        match self {
            CompileResult::Accepted { work, .. } | CompileResult::Rejected { work, .. } => *work,
        }
    }
    pub fn program(&self) -> Option<&TypedProgram> {
        match self {
            CompileResult::Accepted { program, .. } => Some(program),
            _ => None,
        }
    }
}

#[derive(Debug)]
pub enum SourceCompile {
    SourceBoundaryFailure,
    Result(CompileResult),
}

#[derive(Debug)]
pub enum AstCompile {
    AstBoundaryFailure,
    AstInvalid(Vec<Diagnostic>),
    Result(CompileResult),
}

fn result(diags: Vec<Diagnostic>, outcome: Option<CheckOutcome>) -> CompileResult {
    let (errors, warnings) = finalize(diags);
    let work = outcome.as_ref().and_then(|o| o.work);
    match outcome.and_then(|o| o.typed) {
        Some(program) if errors.is_empty() => CompileResult::Accepted { program, warnings, work },
        _ => CompileResult::Rejected { errors, warnings, work },
    }
}

pub enum Parsed {
    Program(Program),
    Failed(SourceCompile),
}

/// source-boundary → lex → parse。
pub fn parse_source(source: &[u8], profile: &StaticProfile) -> Parsed {
    if source.len() > profile.source_bytes {
        let d = Diagnostic::error("source-boundary", "E-LIMIT-STATIC-SOURCE-BYTES", (0, 0))
            .exp(profile.source_bytes.to_string())
            .act(source.len().to_string());
        return Parsed::Failed(SourceCompile::Result(result(vec![d], None)));
    }
    if std::str::from_utf8(source).is_err() {
        return Parsed::Failed(SourceCompile::SourceBoundaryFailure);
    }
    let toks = match lex(source, profile) {
        Ok(t) => t,
        Err(d) => return Parsed::Failed(SourceCompile::Result(result(vec![d], None))),
    };
    match Parser::new(toks, profile).parse_program() {
        ParseOutcome::Ok(p) => Parsed::Program(p),
        ParseOutcome::Errors(d) | ParseOutcome::Cutoff(d) => Parsed::Failed(SourceCompile::Result(result(d, None))),
    }
}

pub fn compile(source: &[u8], profile: &StaticProfile) -> SourceCompile {
    match compile_unrepaired(source, profile) {
        SourceCompile::Result(r) => SourceCompile::Result(with_repairs(r, source)),
        f => f,
    }
}

/// source API の診断に修復ヒントを付ける（§10.1。AST API では付けない）。
fn with_repairs(r: CompileResult, source: &[u8]) -> CompileResult {
    match r {
        CompileResult::Rejected { mut errors, warnings, work } => {
            suggest_repairs(&mut errors, source);
            CompileResult::Rejected { errors, warnings, work }
        }
        accepted => accepted,
    }
}

fn compile_unrepaired(source: &[u8], profile: &StaticProfile) -> SourceCompile {
    match parse_source(source, profile) {
        Parsed::Failed(SourceCompile::Result(r)) => {
            // parse_source が SourceBoundaryFailure を返さなかったので UTF-8 として妥当
            let text = std::str::from_utf8(source).unwrap_or("");
            SourceCompile::Result(cross_check(text, r, profile))
        }
        Parsed::Failed(f) => f,
        Parsed::Program(p) if records::has_records(&p) || softnames::has_soft_names(&p) => {
            // v1.1：レコードを展開し、検証済み部品には fst／snd に書き換え、予約語の変数名を付け替えた
            // プログラムの整形ソースを渡す
            let px = if records::has_records(&p) { records::expand(&p) } else { Ok(p) };
            match px {
                Err(d) => SourceCompile::Result(result(d, None)),
                Ok(px) => {
                    let o = check_program(&px, source.len(), profile);
                    let r = result(o.diagnostics.clone(), Some(o));
                    let text = format_program(&softnames::rename(&records::lower(&px)));
                    SourceCompile::Result(cross_check(&text, r, profile))
                }
            }
        }
        Parsed::Program(p) => {
            let o = check_program(&p, source.len(), profile);
            let r = result(o.diagnostics.clone(), Some(o));
            let text = std::str::from_utf8(source).unwrap_or("");
            SourceCompile::Result(cross_check(text, r, profile))
        }
    }
}

// ---------------------------------------------------------------- 検証済み部品による確認

/// 検証済み parser に渡す式・型の入れ子の深さ上限。診断用 parser の上限（structural-limits）より
/// 大きく取り、診断用 parser が受理したものを深さの数え方の違いで拒否しないようにする。
fn depth_bounds(p: &StaticProfile) -> (usize, usize) {
    (p.expr_depth.saturating_mul(2).saturating_add(2), p.type_depth.saturating_mul(2).saturating_add(2))
}

/// 検証済み部品に渡せる長さ（tlvm_verified::surface::parse_e の前提）。
const VERIFIED_MAX_CHARS: usize = 0x1000_0000;

fn mismatch(why: &str) -> Diagnostic {
    Diagnostic::error("internal", "E-INTERNAL-VERIFIED-MISMATCH", (0, 0)).act(why)
}

/// 診断用の検査器（lexer・parser・checker）の判定を、検証済み部品で確かめる。
///
/// - 受理したなら、検証済みの lexer・parser・名前解決・型検査（compile_source）も受理し、
///   その結果の中間表現を実行に使う。受理しなければ E-INTERNAL-VERIFIED-MISMATCH で拒否する。
/// - 字句・構文・名前・entry の段階で拒否したなら（資源上限による打切りを除く）、
///   検証済み部品もその段階までに拒否することを確かめる（誤拒否の検出）。
fn cross_check(text: &str, r: CompileResult, profile: &StaticProfile) -> CompileResult {
    let chars: Vec<char> = text.chars().collect();
    if chars.len() >= VERIFIED_MAX_CHARS {
        return match r {
            CompileResult::Accepted { warnings, work, .. } => {
                CompileResult::Rejected { errors: vec![mismatch("source-too-long-for-verified-parser")], warnings, work }
            }
            rejected => rejected,
        };
    }
    let (d, td) = depth_bounds(profile);
    match r {
        CompileResult::Accepted { mut program, warnings, work } => {
            let rank: Vec<usize> =
                program.program.functions().map(|f| program.rank.get(&f.name).copied().unwrap_or(usize::MAX)).collect();
            match compile_source(&chars, d, td, rank) {
                Compiled::Accepted(p) => {
                    program.verified = Some(Arc::new(VerifiedProgram(p)));
                    CompileResult::Accepted { program, warnings, work }
                }
                Compiled::ParseRejected => {
                    CompileResult::Rejected { errors: vec![mismatch("verified-parser-rejected")], warnings, work }
                }
                Compiled::NameRejected => {
                    CompileResult::Rejected { errors: vec![mismatch("verified-resolver-rejected")], warnings, work }
                }
                Compiled::NotWellFormed => {
                    CompileResult::Rejected { errors: vec![mismatch("verified-typechecker-rejected")], warnings, work }
                }
            }
        }
        CompileResult::Rejected { mut errors, warnings, work } => {
            let cutoff = errors.iter().any(|e| e.is_cutoff() || e.phase == "diagnostic-limit");
            let syntax = errors.iter().any(|e| matches!(e.phase, "lex" | "parse"));
            let names = errors.iter().any(|e| matches!(e.phase, "name" | "entry"));
            if !cutoff && (syntax || names) {
                match parse_e(&chars, d, td) {
                    Some(sp) => {
                        if syntax {
                            errors.push(mismatch("verified-parser-accepted"));
                        } else if resolve_e(&sp).is_some() {
                            errors.push(mismatch("verified-resolver-accepted"));
                        }
                    }
                    None => {}
                }
            }
            CompileResult::Rejected { errors, warnings, work }
        }
    }
}

/// 正準ソース（検証済み formatter）。受理できない source なら None。
pub fn canonical(text: &str, profile: &StaticProfile) -> Option<String> {
    let chars: Vec<char> = text.chars().collect();
    if chars.len() >= VERIFIED_MAX_CHARS {
        return None;
    }
    let (d, td) = depth_bounds(profile);
    canonical_source(&chars, d, td).map(|o| o.into_iter().collect())
}

pub enum ParsedAst {
    Program(Program),
    Failed(AstCompile),
}

pub fn parse_ast(data: &[u8], profile: &StaticProfile, tp: &AstTransportProfile) -> ParsedAst {
    match ast_codec::transport(data, tp, profile) {
        Transport::BoundaryFailure => ParsedAst::Failed(AstCompile::AstBoundaryFailure),
        Transport::Invalid(d) => ParsedAst::Failed(AstCompile::AstInvalid(d)),
        Transport::Ok(root) => match ast_codec::build(&root, profile) {
            Ok(p) => ParsedAst::Program(p),
            Err(cutoff) => ParsedAst::Failed(AstCompile::Result(result(vec![cutoff], None))),
        },
    }
}

pub fn compile_ast(data: &[u8], profile: &StaticProfile, tp: &AstTransportProfile) -> AstCompile {
    match parse_ast(data, profile, tp) {
        ParsedAst::Failed(f) => f,
        ParsedAst::Program(p) => {
            let o = check_program(&p, data.len(), profile);
            let r = result(o.diagnostics.clone(), Some(o));
            // AST は正準ソースに整形してから検証済み部品に通す（整形は診断用 formatter）
            let text = format_program(&p);
            AstCompile::Result(without_repairs(cross_check(&text, r, profile)))
        }
    }
}

/// AST API は安全な JSON 部分木の置換を指定できないので repair を出さない（§10.1）。
fn without_repairs(r: CompileResult) -> CompileResult {
    let strip = |ds: Vec<Diagnostic>| ds.into_iter().map(|d| Diagnostic { repair: None, ..d }).collect::<Vec<_>>();
    match r {
        CompileResult::Rejected { errors, warnings, work } => {
            CompileResult::Rejected { errors: strip(errors), warnings: strip(warnings), work }
        }
        CompileResult::Accepted { program, warnings, work } => CompileResult::Accepted { program, warnings: strip(warnings), work },
    }
}

pub fn decode_input(t_in: &Ty, data: &[u8], profile: &InputProfile) -> DecodeResult {
    values::decode_input(t_in, data, profile)
}

/// 普通の JSON（`plain` モジュールの対応表）で入力を読む。値 JSON へ変換してから `decode_input` と同じ
/// 経路（診断付きの復号器と検証済みの復号器の突き合わせ）で復号する。診断の span は plain JSON の bytes 上。
pub fn decode_plain_input(t_in: &Ty, data: &[u8], profile: &InputProfile) -> DecodeResult {
    match decode_plain(t_in, data, profile) {
        PlainDecode::Canonical(text) => values::decode_input(t_in, text.as_bytes(), &canonical_profile(profile)),
        PlainDecode::Invalid(d) => DecodeResult::Invalid(d),
        PlainDecode::InputBoundaryFailure => DecodeResult::InputBoundaryFailure,
    }
}

/// 深い再帰に備えて host-policy のスタック量を持つスレッドで評価する。
pub fn run(program: &TypedProgram, input: &TypedValue, profile: &ExecutionProfile, host: &HostPolicy) -> Result<RunResult, String> {
    std::thread::scope(|s| {
        let h = std::thread::Builder::new()
            .stack_size(host.stack_bytes)
            .spawn_scoped(s, || evaluator::run(program, input, profile, host))
            .map_err(|e| e.to_string())?;
        match h.join() {
            Ok(r) => r,
            Err(_) => Ok(RunResult::InternalFault("evaluator-panic".into())),
        }
    })
}
