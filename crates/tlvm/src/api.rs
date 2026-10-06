//! 公開 API：compile / compile_ast / decode_input / run（設計書 §9.1）。

use crate::ast_codec::{self, Transport};
use crate::checker::{check_program, CheckOutcome, TypedProgram, WorkCounter};
use crate::diagnostics::{finalize, Diagnostic};
use crate::evaluator::{self, RunResult};
use crate::lexer::lex;
use crate::parser::{ParseOutcome, Parser};
use crate::profiles::*;
use crate::syntax::{Program, Ty};
use crate::values::{self, DecodeResult, TypedValue};

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
    match parse_source(source, profile) {
        Parsed::Failed(f) => f,
        Parsed::Program(p) => {
            let o = check_program(&p, source.len(), profile);
            SourceCompile::Result(result(o.diagnostics.clone(), Some(o)))
        }
    }
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
            AstCompile::Result(result(o.diagnostics.clone(), Some(o)))
        }
    }
}

pub fn decode_input(t_in: &Ty, data: &[u8], profile: &InputProfile) -> DecodeResult {
    values::decode_input(t_in, data, profile)
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
