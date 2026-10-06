"""診断 schema・整列・件数上限（設計書 §10）。"""

from __future__ import annotations

import json
from dataclasses import dataclass, field

PHASE_ORDER = [
    "source-boundary",
    "lex",
    "lexical-limits",
    "parse",
    "structural-limits",
    "name",
    "call-graph",
    "typecheck",
    "semantic-limits",
    "entry",
    "warnings",
]
_PHASE_RANK = {p: i for i, p in enumerate(PHASE_ORDER)}

CUTOFF_PHASES = {"lexical-limits", "structural-limits", "semantic-limits"}

MAX_PER_SEVERITY = 32

# message テンプレート。正式な diagnostic registry は未作成（G0 未達）なので暫定版。
MESSAGES = {
    "E-LEX-NON-ASCII": "コメント外に非 ASCII 文字があります",
    "E-LEX-UNEXPECTED-CHARACTER": "この文字はトークンを開始できません",
    "E-LEX-INVALID-INTEGER": "整数リテラルが正規形ではありません",
    "E-LEX-INVALID-NUMERIC-BOUNDARY": "整数の直後に識別子文字や符号が続いています",
    "E-PARSE-UNEXPECTED-TOKEN": "ここには fn、entry、EOF のいずれかが必要です",
    "E-PARSE-EXPECTED-TOKEN": "必要な区切り記号がありません",
    "E-PARSE-EXPECTED-TYPE": "型が必要です",
    "E-PARSE-EXPECTED-IDENT": "識別子が必要です（予約語は使えません）",
    "E-PARSE-EXPECTED-EXPR": "式が必要です",
    "E-PARSE-RECOVERY-LIMIT": "parse error が多すぎるため解析を打ち切りました",
    "E-NAME-UNKNOWN-FUNCTION": "未定義の関数です",
    "E-NAME-UNBOUND-VARIABLE": "未束縛の変数です",
    "E-NAME-DUPLICATE-FUNCTION": "同名のトップレベル関数が既に定義されています",
    "E-NAME-DUPLICATE-PARAM": "同名の引数が既にあります",
    "E-NAME-DUPLICATE-BINDER": "fold の acc と item は相異なる名前でなければなりません",
    "E-NAME-SHADOW": "外側の変数をシャドーする束縛は書けません",
    "E-ENTRY-UNKNOWN": "entry が未定義の関数を指しています",
    "E-ENTRY-MISSING": "entry 宣言がありません",
    "E-ENTRY-DUPLICATE": "entry 宣言は一つだけにしてください",
    "E-ENTRY-ARITY": "entry 関数はちょうど一つの引数を取らなければなりません",
    "E-CYCLE-CALL": "関数呼出しが循環しています",
    "E-ARITY-USER": "関数の引数の数が一致しません",
    "E-ARITY-BUILTIN": "組込み関数の引数の数が一致しません",
    "E-TYPE-ARG": "引数の型が一致しません",
    "E-TYPE-EQ-OPERANDS": "eq の両引数は同じ型でなければなりません",
    "E-TYPE-FST-ARG": "fst の引数は Pair でなければなりません",
    "E-TYPE-SND-ARG": "snd の引数は Pair でなければなりません",
    "E-TYPE-EXPECTED-LIST": "List 型の値が必要です",
    "E-TYPE-LIST-ITEM": "リスト要素の型が注釈と一致しません",
    "E-TYPE-IF-CONDITION": "if の条件は Bool でなければなりません",
    "E-TYPE-IF-BRANCH": "if の両分岐は同じ型でなければなりません",
    "E-TYPE-FOLD-LIST": "fold の第1引数は List でなければなりません",
    "E-TYPE-FOLD-BODY": "fold 本体の型は初期値の型と一致しなければなりません",
    "E-TYPE-RETURN": "関数本体の型が宣言した戻り型と一致しません",
    "E-LIMIT-STATIC-SOURCE-BYTES": "source bytes が上限を超えました",
    "E-LIMIT-STATIC-TOKENS": "token 数が上限を超えました",
    "E-LIMIT-STATIC-INTEGER-DIGITS": "整数リテラルの桁数が上限を超えました",
    "E-LIMIT-STATIC-FUNCTIONS": "関数数が上限を超えました",
    "E-LIMIT-STATIC-AST-NODES": "AST node 数が上限を超えました",
    "E-LIMIT-STATIC-TYPE-DEPTH": "型構文の深さが上限を超えました",
    "E-LIMIT-STATIC-EXPR-DEPTH": "式の深さが上限を超えました",
    "E-LIMIT-STATIC-LET-DEPTH": "let のネスト深さが上限を超えました",
    "E-LIMIT-STATIC-FOLD-DEPTH": "fold のネスト深さが上限を超えました",
    "E-LIMIT-STATIC-SEMANTIC-TYPE-DEPTH": "推論された型の深さが上限を超えました",
    "E-LIMIT-STATIC-SEMANTIC-WORK": "型検査の仕事量が上限を超えました",
    "E-DIAG-LIMIT": "error が多すぎるため以降を省略しました",
    "W-DIAG-LIMIT": "warning が多すぎるため以降を省略しました",
    "W-UNUSED-FUNCTION": "entry から到達しない関数です",
    "E-INPUT-JSON-SYNTAX": "入力 JSON の文法が不正です",
    "E-INPUT-STRING-SCALAR": "入力 JSON の文字列に不正な Unicode scalar があります",
    "E-INPUT-DUPLICATE-KEY": "入力 JSON に重複キーがあります",
    "E-INPUT-FIELD-TYPE": "入力値の JSON 型が不正です",
    "E-INPUT-MISSING-FIELD": "入力値に必須キーがありません",
    "E-INPUT-TAG": "入力値の tag が期待型と一致しません",
    "E-INPUT-UNKNOWN-FIELD": "入力値に未知のキーがあります",
    "E-INPUT-INTEGER": "入力整数が正規形ではありません",
    "E-LIMIT-INPUT-JSON-BYTES": "入力 JSON bytes が上限を超えました",
    "E-LIMIT-INPUT-JSON-DEPTH": "入力 JSON の構造深さが上限を超えました",
    "E-LIMIT-INPUT-VALUE-DEPTH": "入力値の深さが上限を超えました",
    "E-LIMIT-INPUT-VALUE-NODES": "入力値の node 数が上限を超えました",
    "E-LIMIT-INPUT-INTEGER-DIGITS": "入力整数の桁数が上限を超えました",
    "E-AST-JSON-SYNTAX": "AST JSON の文法が不正です",
    "E-AST-STRING-SCALAR": "AST JSON の文字列に不正な Unicode scalar があります",
    "E-AST-DUPLICATE-KEY": "AST JSON に重複キーがあります",
    "E-AST-CODEC": "codec は \"ast_codec_v1\" でなければなりません",
    "E-AST-TAG": "この位置で許されない tag です",
    "E-AST-MISSING-FIELD": "必須キーがありません",
    "E-AST-UNKNOWN-FIELD": "未知のキーがあります",
    "E-AST-FIELD-TYPE": "JSON 型が不正です",
    "E-AST-IDENTIFIER": "識別子が不正です",
    "E-AST-INTEGER": "整数が正規形ではありません",
    "E-AST-LIMIT-BYTES": "AST JSON bytes が上限を超えました",
    "E-AST-LIMIT-JSON-DEPTH": "AST JSON の構造深さが上限を超えました",
    "E-AST-LIMIT-INTEGER-DIGITS": "整数の桁数が上限を超えました",
}


@dataclass
class Diagnostic:
    severity: str
    phase: str
    code: str
    span: tuple[int, int]
    expected: str | None = None
    actual: str | None = None
    message: str | None = None
    repair: dict | None = None
    node_index: int = 0
    seq: int = field(default=0, compare=False)

    def __post_init__(self) -> None:
        if self.message is None:
            self.message = MESSAGES.get(self.code, self.code)

    @property
    def is_cutoff(self) -> bool:
        return self.phase in CUTOFF_PHASES

    def to_dict(self) -> dict:
        return {
            "severity": self.severity,
            "phase": self.phase,
            "code": self.code,
            "span": {"start": self.span[0], "end": self.span[1]},
            "expected": self.expected,
            "actual": self.actual,
            "message": self.message,
            "repair": self.repair,
        }

    def to_json(self) -> str:
        return json.dumps(self.to_dict(), ensure_ascii=False, separators=(",", ":"))


def error(phase: str, code: str, span, expected=None, actual=None, node_index: int = 0) -> Diagnostic:
    return Diagnostic("error", phase, code, tuple(span), expected, actual, node_index=node_index)


def warning(phase: str, code: str, span, node_index: int = 0) -> Diagnostic:
    return Diagnostic("warning", phase, code, tuple(span), node_index=node_index)


def _sort_key(d: Diagnostic):
    rank = _PHASE_RANK.get(d.phase, len(PHASE_ORDER))
    if d.phase == "parse":
        return (rank, d.seq, 0, "", 0)
    return (rank, d.span[0], d.span[1], d.code, d.node_index)


def finalize(diags: list[Diagnostic]) -> tuple[list[Diagnostic], list[Diagnostic]]:
    """phase 順・span 順に整列し、重複を統合し、件数上限を適用する。"""
    seen = set()
    unique = []
    for d in diags:
        if d.phase == "parse":
            key = (d.phase, d.code, d.span, d.seq)
        else:
            key = (d.phase, d.code, d.span, d.node_index)
        if key in seen:
            continue
        seen.add(key)
        unique.append(d)
    unique.sort(key=_sort_key)
    errors = [d for d in unique if d.severity == "error"]
    warnings = [d for d in unique if d.severity == "warning"]
    return _limit(errors, "E-DIAG-LIMIT"), _limit(warnings, "W-DIAG-LIMIT")


def _limit(diags: list[Diagnostic], code: str) -> list[Diagnostic]:
    if len(diags) <= MAX_PER_SEVERITY:
        return diags
    severity = diags[0].severity
    cutoffs = [d for d in diags if d.is_cutoff]
    if cutoffs:
        kept = [d for d in diags if not d.is_cutoff][: MAX_PER_SEVERITY - 2] + cutoffs[:1]
    else:
        kept = diags[: MAX_PER_SEVERITY - 1]
    return kept + [Diagnostic(severity, "diagnostic-limit", code, (0, 0))]
