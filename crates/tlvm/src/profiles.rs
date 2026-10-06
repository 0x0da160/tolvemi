//! 資源プロファイル（設計書 §18）。数値は reference-1 の設計値。

#[derive(Clone, Debug)]
pub struct StaticProfile {
    pub id: &'static str,
    pub source_bytes: usize,
    pub tokens: usize,
    pub integer_digits: usize,
    pub functions: usize,
    pub ast_nodes: usize,
    pub type_depth: usize,
    pub expr_depth: usize,
    pub let_depth: usize,
    pub fold_depth: usize,
    pub semantic_type_depth: usize,
    pub semantic_work: u64,
}

impl Default for StaticProfile {
    fn default() -> Self {
        StaticProfile {
            id: "static-v1-reference-1",
            source_bytes: 1_048_576,
            tokens: 131_072,
            integer_digits: 4_096,
            functions: 1_024,
            ast_nodes: 131_072,
            type_depth: 64,
            expr_depth: 256,
            let_depth: 128,
            fold_depth: 32,
            semantic_type_depth: 128,
            semantic_work: 2_000_000,
        }
    }
}

#[derive(Clone, Debug)]
pub struct InputProfile {
    pub id: &'static str,
    pub json_bytes: usize,
    pub json_depth: usize,
    pub value_depth: usize,
    pub value_nodes: usize,
    pub integer_digits: usize,
}

impl Default for InputProfile {
    fn default() -> Self {
        InputProfile {
            id: "input-v1-reference-1",
            json_bytes: 4_194_304,
            json_depth: 512,
            value_depth: 128,
            value_nodes: 262_144,
            integer_digits: 4_096,
        }
    }
}

#[derive(Clone, Debug)]
pub struct AstTransportProfile {
    pub id: &'static str,
    pub json_bytes: usize,
    pub json_depth: usize,
}

impl Default for AstTransportProfile {
    fn default() -> Self {
        AstTransportProfile { id: "ast-transport-v1-reference-1", json_bytes: 16_777_216, json_depth: 1_024 }
    }
}

#[derive(Clone, Debug)]
pub struct ExecutionProfile {
    pub id: &'static str,
    pub steps: u64,
    pub allocated_nodes: u64,
    pub integer_bits: u64,
    pub output_bytes: u64,
}

impl Default for ExecutionProfile {
    fn default() -> Self {
        ExecutionProfile {
            id: "execution-v1-reference-1",
            steps: 10_000_000,
            allocated_nodes: 1_000_000,
            integer_bits: 65_536,
            output_bytes: 16_777_216,
        }
    }
}

/// ホスト側の物理上限。違反は HostAborted（参照 step とは別契約）。
#[derive(Clone, Debug)]
pub struct HostPolicy {
    pub id: &'static str,
    pub max_eval_depth: usize,
    pub stack_bytes: usize,
}

impl Default for HostPolicy {
    fn default() -> Self {
        HostPolicy { id: "tlvm-rust-host-v0", max_eval_depth: 400_000, stack_bytes: 1 << 30 }
    }
}
