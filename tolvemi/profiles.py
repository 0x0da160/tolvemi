"""資源プロファイル（設計書 §18）。数値は reference-1 の設計値。"""

from __future__ import annotations

from dataclasses import dataclass


@dataclass(frozen=True)
class StaticProfile:
    id: str = "static-v1-reference-1"
    source_bytes: int = 1_048_576
    tokens: int = 131_072
    integer_digits: int = 4_096
    functions: int = 1_024
    ast_nodes: int = 131_072
    type_depth: int = 64
    expr_depth: int = 256
    let_depth: int = 128
    fold_depth: int = 32
    semantic_type_depth: int = 128
    semantic_work: int = 2_000_000


@dataclass(frozen=True)
class InputProfile:
    id: str = "input-v1-reference-1"
    json_bytes: int = 4_194_304
    json_depth: int = 512
    value_depth: int = 128
    value_nodes: int = 262_144
    integer_digits: int = 4_096


@dataclass(frozen=True)
class AstTransportProfile:
    id: str = "ast-transport-v1-reference-1"
    json_bytes: int = 16_777_216
    json_depth: int = 1_024


@dataclass(frozen=True)
class ExecutionProfile:
    id: str = "execution-v1-reference-1"
    steps: int = 10_000_000
    allocated_nodes: int = 1_000_000
    integer_bits: int = 65_536
    output_bytes: int = 16_777_216


@dataclass(frozen=True)
class HostPolicy:
    """ホスト側の物理上限。違反は HostAborted（参照 step とは別契約）。"""

    id: str = "tolvemi-python-host-v0"
    max_eval_depth: int = 400_000


STATIC = StaticProfile()
INPUT = InputProfile()
AST_TRANSPORT = AstTransportProfile()
EXECUTION = ExecutionProfile()
HOST = HostPolicy()
