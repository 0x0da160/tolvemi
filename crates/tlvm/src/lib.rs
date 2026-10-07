//! Tolvemi（tlvm）：LPTL v1 の実行層（exec）。
//!
//! 設計書 §11.1 の層分離のうち exec 層（lexer、parser、formatter、resolver、type checker、
//! DAG checker、evaluator、JSON codec、CLI）を Rust で実装する。数学的仕様と証明は
//! `verus/` の spec／proof 層にある。この crate 自体は Verus で検証されていない
//! （信頼境界は `trust-boundary.toml`）。

pub mod api;
pub mod ast_codec;
pub mod checker;
pub mod diagnostics;
pub mod embed;
pub mod evaluator;
pub mod formatter;
pub mod lexer;
pub mod parser;
pub mod plain;
pub mod profiles;
pub mod records;
pub mod strict_json;
pub mod syntax;
pub mod values;

pub use api::*;
pub use evaluator::RunResult;
pub use values::DecodeResult;
