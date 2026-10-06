"""字句解析と lexical-limits（設計書 §4.2、§18.1）。

入力は UTF-8 検査済みの bytes。span は bytes offset。lex は最初の error で停止する。
"""

from __future__ import annotations

from dataclasses import dataclass

from .diagnostics import Diagnostic, error
from .profiles import StaticProfile
from .syntax import KEYWORDS

_SINGLE = {ord(c): c for c in "()[]<>,:=|"}
_WS = {0x20, 0x09, 0x0D, 0x0A}


def _is_ident_start(b: int) -> bool:
    return (0x41 <= b <= 0x5A) or (0x61 <= b <= 0x7A) or b == 0x5F


def _is_ident_char(b: int) -> bool:
    return _is_ident_start(b) or (0x30 <= b <= 0x39)


def _is_digit(b: int) -> bool:
    return 0x30 <= b <= 0x39


@dataclass(frozen=True)
class Token:
    kind: str  # INT / IDENT / KW / PUNCT / EOF
    text: str
    start: int
    end: int

    @property
    def span(self) -> tuple[int, int]:
        return (self.start, self.end)

    def describe(self) -> str:
        return "EOF" if self.kind == "EOF" else self.text


class LexFailure(Exception):
    def __init__(self, diag: Diagnostic):
        super().__init__(diag.code)
        self.diag = diag


def _utf8_len(b: int) -> int:
    if b >= 0xF0:
        return 4
    if b >= 0xE0:
        return 3
    if b >= 0xC0:
        return 2
    return 1


def lex(src: bytes, profile: StaticProfile) -> list[Token]:
    """token 列（末尾に EOF）を返す。失敗時は LexFailure を送出する。"""
    toks: list[Token] = []
    n = len(src)
    i = 0

    def fail(phase, code, start, end, expected=None, actual=None):
        raise LexFailure(error(phase, code, (start, end), expected, actual))

    def push(tok: Token):
        toks.append(tok)
        if len(toks) > profile.tokens:
            fail("lexical-limits", "E-LIMIT-STATIC-TOKENS", tok.start, tok.end,
                 str(profile.tokens), str(len(toks)))

    while i < n:
        b = src[i]
        if b in _WS:
            i += 1
            continue
        if b == 0x2F:  # '/'
            if i + 1 < n and src[i + 1] == 0x2F:
                i += 2
                while i < n and src[i] not in (0x0A, 0x0D):
                    i += 1
                continue
            fail("lex", "E-LEX-UNEXPECTED-CHARACTER", i, i + 1, None, "/")
        if b >= 0x80:
            fail("lex", "E-LEX-NON-ASCII", i, min(n, i + _utf8_len(b)))
        if _is_ident_start(b):
            j = i + 1
            while j < n and _is_ident_char(src[j]):
                j += 1
            text = src[i:j].decode("ascii")
            push(Token("KW" if text in KEYWORDS else "IDENT", text, i, j))
            i = j
            continue
        if _is_digit(b) or (b == 0x2D and i + 1 < n and _is_digit(src[i + 1])) or (
            b == 0x2B and i + 1 < n and _is_digit(src[i + 1])
        ):
            start = i
            j = i + 1 if b in (0x2D, 0x2B) else i
            d0 = j
            while j < n and _is_digit(src[j]):
                j += 1
            digits = src[d0:j]
            # 正規形・数値境界を桁上限より先に判定する（§18.1）
            if b == 0x2B:
                fail("lex", "E-LEX-INVALID-INTEGER", start, j, None, src[start:j].decode("ascii"))
            if digits[0] == 0x30 and (len(digits) > 1 or b == 0x2D):
                fail("lex", "E-LEX-INVALID-INTEGER", start, j, None, src[start:j].decode("ascii"))
            if j < n and (_is_ident_start(src[j]) or src[j] == 0x2D or src[j] == 0x2E):
                k = j + 1
                while k < n and _is_ident_char(src[k]):
                    k += 1
                fail("lex", "E-LEX-INVALID-NUMERIC-BOUNDARY", start, k)
            if len(digits) > profile.integer_digits:
                fail("lexical-limits", "E-LIMIT-STATIC-INTEGER-DIGITS", start, j,
                     str(profile.integer_digits), str(len(digits)))
            push(Token("INT", src[start:j].decode("ascii"), start, j))
            i = j
            continue
        if b == 0x2D:  # '-'
            if i + 1 < n and src[i + 1] == 0x3E:
                push(Token("PUNCT", "->", i, i + 2))
                i += 2
                continue
            fail("lex", "E-LEX-UNEXPECTED-CHARACTER", i, i + 1, None, "-")
        if b in _SINGLE:
            push(Token("PUNCT", _SINGLE[b], i, i + 1))
            i += 1
            continue
        fail("lex", "E-LEX-UNEXPECTED-CHARACTER", i, i + 1, None, repr(chr(b)))
    toks.append(Token("EOF", "", n, n))
    return toks
