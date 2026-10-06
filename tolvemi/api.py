"""公開 API：compile / compile_ast / decode_input / run（設計書 §9.1）。"""

from __future__ import annotations

import sys
import threading
from dataclasses import dataclass, field

from . import ast_codec
from .checker import CheckOutcome, TypedProgram, WorkCounter, check_program
from .diagnostics import Diagnostic, error, finalize
from .evaluator import Completed, run as _run  # noqa: F401
from .lexer import LexFailure, lex
from .parser import Cutoff, Parser
from .profiles import AstTransportProfile, ExecutionProfile, HostPolicy, InputProfile, StaticProfile
from .syntax import Program, Ty
from .values import decode_input as _decode_input

sys.set_int_max_str_digits(0)
if sys.getrecursionlimit() < 20_000:
    sys.setrecursionlimit(20_000)


class SourceBoundaryFailure:
    reason = "InvalidSourceEncoding"

    def __repr__(self) -> str:
        return "SourceBoundaryFailure(InvalidSourceEncoding)"


@dataclass
class Accepted:
    program: TypedProgram
    warnings: list[Diagnostic] = field(default_factory=list)
    work: WorkCounter | None = None

    @property
    def errors(self) -> list[Diagnostic]:
        return []


@dataclass
class Rejected:
    errors: list[Diagnostic]
    warnings: list[Diagnostic] = field(default_factory=list)
    work: WorkCounter | None = None


def _result(diags: list[Diagnostic], outcome: CheckOutcome | None):
    errors, warnings = finalize(diags)
    work = outcome.work if outcome else None
    if outcome is not None and outcome.typed is not None and not errors:
        return Accepted(outcome.typed, warnings, work)
    return Rejected(errors, warnings, work)


def parse_source(source: bytes, profile: StaticProfile = StaticProfile()):
    """source-boundary → lex → parse。成功時は Program、失敗時は結果 envelope。"""
    if len(source) > profile.source_bytes:
        return Rejected([error("source-boundary", "E-LIMIT-STATIC-SOURCE-BYTES", (0, 0),
                               str(profile.source_bytes), str(len(source)))])
    try:
        source.decode("utf-8")
    except UnicodeDecodeError:
        return SourceBoundaryFailure()
    try:
        tokens = lex(source, profile)
    except LexFailure as f:
        return Rejected([f.diag])
    parser = Parser(tokens, profile)
    try:
        prog = parser.parse_program()
    except Cutoff as c:
        return _result(parser.diags + [c.diag], None)
    if prog is None:
        return _result(parser.diags, None)
    return prog


def compile(source: bytes, profile: StaticProfile = StaticProfile()):
    """compile(source_bytes, static_profile) -> SourceBoundaryFailure | Accepted | Rejected"""
    if isinstance(source, str):
        source = source.encode("utf-8")
    prog = parse_source(source, profile)
    if not isinstance(prog, Program):
        return prog
    outcome = check_program(prog, len(source), profile)
    return _result(outcome.diagnostics, outcome)


def compile_ast(data: bytes, profile: StaticProfile = StaticProfile(),
                transport: AstTransportProfile = AstTransportProfile()):
    """compile_ast -> AstBoundaryFailure | AstInvalid | Accepted | Rejected"""
    if isinstance(data, str):
        data = data.encode("utf-8")
    root = ast_codec.transport(data, transport, profile)
    if not isinstance(root, ast_codec.JNode):
        return root
    try:
        prog = ast_codec.build(root, profile)
    except Cutoff as c:
        return _result([c.diag], None)
    outcome = check_program(prog, len(data), profile)
    return _result(outcome.diagnostics, outcome)


def decode_input(t_in: Ty, data: bytes, profile: InputProfile = InputProfile()):
    if isinstance(data, str):
        data = data.encode("utf-8")
    return _decode_input(t_in, data, profile)


def run(program: TypedProgram, decoded, profile: ExecutionProfile = ExecutionProfile(),
        host: HostPolicy = HostPolicy()):
    """深い再帰に備えて大きなスタックのスレッドで評価する。"""
    box: dict = {}

    def target():
        try:
            box["result"] = _run(program, decoded, profile, host)
        except BaseException as exc:  # noqa: BLE001
            box["error"] = exc

    old = threading.stack_size()
    threading.stack_size(512 * 1024 * 1024)
    limit = sys.getrecursionlimit()
    sys.setrecursionlimit(max(limit, host.max_eval_depth * 4 + 1000))
    try:
        t = threading.Thread(target=target)
        t.start()
        t.join()
    finally:
        threading.stack_size(old)
        sys.setrecursionlimit(limit)
    if "error" in box:
        raise box["error"]
    return box["result"]
