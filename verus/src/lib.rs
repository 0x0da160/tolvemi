//! LPTL v1 の Verus 検証済み中核（設計書 §11）。
//!
//! - `spec`   : 型、値、名前解決済み AST、型付け、呼出しランク、燃料付き評価
//! - `proof`  : 停止性・型安全性・決定性
//! - `bigint` : 信頼する多倍長整数（V1-A）
//! - `ir`     : exec 用の名前解決済み AST とその spec への写像
//!
//! 信頼境界は trust-boundary.toml を参照。
#![allow(unused_imports)]

pub mod bigint;
pub mod bigstep;
pub mod check;
pub mod eval;
pub mod ir;
pub mod json;
pub mod pipeline;
pub mod proof;
pub mod resolve;
pub mod spec;
pub mod surface;
pub mod syntax;
pub mod syntax_proof;
pub mod parse_proof;
pub mod value;
