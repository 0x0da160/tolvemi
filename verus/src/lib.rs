//! LPTL v1 の Verus 検証済み中核（設計書 §11）。
//!
//! - `spec`   : 型、値、名前解決済み AST、型付け、呼出しランク、燃料付き評価
//! - `proof`  : 停止性・型安全性・決定性
//! - `bigint` : 信頼する多倍長整数（V1-A）
//! - `ir`     : exec 用の名前解決済み AST とその spec への写像
//!
//! 信頼境界は trust-boundary.toml を参照。
#![allow(unused_imports, unused_variables)]

pub mod bigint;
pub mod bigstep;
pub mod check;
pub mod eval;
pub mod fold_meaning;
pub mod fresh;
pub mod input;
pub mod input_exec;
pub mod input_proof;
pub mod io;
pub mod ir;
pub mod json;
pub mod parse_proof;
pub mod pipeline;
pub mod proof;
pub mod records_exec;
pub mod records_proof;
pub mod resolve;
pub mod sortmeaning;
pub mod sortspec;
pub mod spec;
pub mod surface;
pub mod syntax;
pub mod syntax_proof;
pub mod value;
pub mod xmeaning;
pub mod xsem;
pub mod xshort;
pub mod xtyping;
pub mod records_meaning;
pub mod tagged_names;
pub mod records_commute;
pub mod guards;
pub mod simulation;
pub mod keysort;
pub mod hof_types;
pub mod hof_agree;
pub mod loop_types;
pub mod dict_types;
pub mod hof_total;
pub mod sh6_obligations;
pub mod sh6_stuck;
pub mod sh6_safe;
pub mod sh4_back;
pub mod hofrw;
pub mod hofex;
pub mod dictex;
pub mod loopex;
pub mod hofres;
pub mod hofresex;
pub mod hofprog;
pub mod hofroute;
