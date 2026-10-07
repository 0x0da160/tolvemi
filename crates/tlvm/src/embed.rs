//! ホストに組み込むための小さな API（設計書の外側の便宜）。
//!
//! `api` の compile → decode_plain_input → run → encode_plain を既定の資源プロファイルでつなぎ、
//! 入出力を普通の JSON（`plain` モジュールの対応表）の文字列で受け渡す。診断は CLI と同じ一行 JSON
//! （[`Diagnostic::to_json`]）で取り出せる。
//!
//! ```
//! let p = tlvm::embed::Program::compile(
//!     "fn solve(xs: List<Int>) -> Int = fold(xs, 0, |acc, x| add(acc, x))\nentry solve\n",
//! ).unwrap();
//! assert_eq!(p.input_type(), "List<Int>");
//! assert_eq!(p.run_json("[1, 2, 3]").unwrap(), "6");
//! ```

use crate::api::{compile, decode_plain_input, run, CompileResult, SourceCompile};
use crate::checker::TypedProgram;
use crate::evaluator::RunResult;
use crate::plain::encode_plain;
use crate::profiles::{ExecutionProfile, HostPolicy, InputProfile, StaticProfile};
use crate::values::DecodeResult;
use std::fmt;

pub use crate::diagnostics::Diagnostic;

/// 診断の一行 JSON（CLI が stderr に出すものと同じ形）。
pub fn diagnostic_json(d: &Diagnostic) -> String {
    d.to_json()
}

/// 検査済みのプログラム。
#[derive(Debug)]
pub struct Program {
    typed: TypedProgram,
    warnings: Vec<Diagnostic>,
}

/// 実行に使う資源プロファイル。`Default` は CLI と同じ reference-1。
#[derive(Clone, Debug, Default)]
pub struct Limits {
    pub input: InputProfile,
    pub execution: ExecutionProfile,
    pub host: HostPolicy,
}

#[derive(Debug)]
pub enum RunError {
    /// 入力を入力型の値として読めない（診断の span は入力 JSON の bytes 上）
    Input(Vec<Diagnostic>),
    /// 実行の資源上限（steps、allocated nodes、整数の bit 数、出力 bytes）を超えた
    ResourceExhausted { kind: &'static str, observed: u64, limit: u64 },
    /// ホスト側の物理上限（評価の深さ）で中断した
    HostAborted(String),
    /// 処理系の内部の失敗（起きないはずのもの）
    Internal(String),
}

impl fmt::Display for RunError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            RunError::Input(ds) => {
                write!(f, "InputError")?;
                for d in ds {
                    write!(f, "\n{}", d.to_json())?;
                }
                Ok(())
            }
            RunError::ResourceExhausted { kind, observed, limit } => {
                write!(f, "ResourceExhausted {kind} (observed {observed}, limit {limit})")
            }
            RunError::HostAborted(r) => write!(f, "HostAborted {r}"),
            RunError::Internal(r) => write!(f, "InternalFault {r}"),
        }
    }
}

impl std::error::Error for RunError {}

impl Program {
    /// source を既定の静的プロファイルで検査する。拒否なら error の診断を返す。
    pub fn compile(source: &str) -> Result<Program, Vec<Diagnostic>> {
        Self::compile_with(source, &StaticProfile::default())
    }

    pub fn compile_with(source: &str, profile: &StaticProfile) -> Result<Program, Vec<Diagnostic>> {
        match compile(source.as_bytes(), profile) {
            SourceCompile::Result(CompileResult::Accepted { program, warnings, .. }) => {
                Ok(Program { typed: program, warnings })
            }
            SourceCompile::Result(CompileResult::Rejected { errors, .. }) => Err(errors),
            // &str は常に UTF-8 なので起きない
            SourceCompile::SourceBoundaryFailure => {
                Err(vec![Diagnostic::error("source-boundary", "E-INTERNAL-SOURCE-BOUNDARY", (0, 0))])
            }
        }
    }

    /// 受理時の warning の診断。
    pub fn warnings(&self) -> &[Diagnostic] {
        &self.warnings
    }

    pub fn entry(&self) -> &str {
        &self.typed.entry
    }

    /// entry の入力型（`List<Int>` の形）。
    pub fn input_type(&self) -> String {
        self.typed.input_type.to_string()
    }

    /// entry の出力型。
    pub fn output_type(&self) -> String {
        self.typed.output_type.to_string()
    }

    pub fn typed(&self) -> &TypedProgram {
        &self.typed
    }

    /// plain JSON の入力で実行し、plain JSON（最小空白）の出力を返す。
    pub fn run_json(&self, input_plain_json: &str) -> Result<String, RunError> {
        self.run_json_with(input_plain_json, &Limits::default())
    }

    pub fn run_json_with(&self, input_plain_json: &str, limits: &Limits) -> Result<String, RunError> {
        let p = &self.typed;
        let tv = match decode_plain_input(&p.input_type, input_plain_json.as_bytes(), &limits.input) {
            DecodeResult::Decoded(tv) => tv,
            DecodeResult::Invalid(d) => return Err(RunError::Input(d)),
            // &str は常に UTF-8 なので起きない
            DecodeResult::InputBoundaryFailure => return Err(RunError::Internal("input-boundary-failure".into())),
        };
        match run(p, &tv, &limits.execution, &limits.host).map_err(RunError::Internal)? {
            RunResult::Completed { output, .. } => encode_plain(&p.output_type, &output).map_err(RunError::Internal),
            RunResult::ResourceExhausted { kind, observed, limit } => Err(RunError::ResourceExhausted { kind, observed, limit }),
            RunResult::HostAborted(r) => Err(RunError::HostAborted(r)),
            RunResult::InternalFault(r) => Err(RunError::Internal(r)),
        }
    }
}
