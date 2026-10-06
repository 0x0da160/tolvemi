//! LPTL v1 の Verus 証明層（設計書 §11）。
//!
//! - `spec`  : 型、値、名前解決済み AST、型付け、呼出しランク、燃料付き評価
//! - `proof` : 停止性・型安全性・決定性
//!
//! exec 層（crates/tlvm）との精緻化（refinement）は未証明。信頼境界は
//! trust-boundary.toml を参照。
#![allow(unused_imports)]

pub mod proof;
pub mod spec;
