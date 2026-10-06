"""strict JSON transport（設計書 §9.3a、§19.3）。

段階順：JSON 文法／構造深さ → string scalar 妥当性 → 重複キー。
各段階が全体で成功した場合だけ次の段階へ進む。span は元 bytes 上の offset。
"""

from __future__ import annotations

from dataclasses import dataclass, field


@dataclass
class JNode:
    kind: str  # object / array / string / number / boolean / null
    start: int
    end: int
    value: object = None
    # object: [(key, key_start, key_end, JNode)]、array: [JNode]
    members: list = field(default_factory=list)

    @property
    def span(self) -> tuple[int, int]:
        return (self.start, self.end)

    def get(self, key: str) -> "JNode | None":
        for k, _, _, v in self.members:
            if k == key:
                return v
        return None

    def key_span(self, key: str) -> tuple[int, int]:
        for k, ks, ke, _ in self.members:
            if k == key:
                return (ks, ke)
        raise KeyError(key)


class JsonFailure(Exception):
    """kind は syntax / depth / scalar / duplicate。"""

    def __init__(self, kind: str, span: tuple[int, int]):
        super().__init__(kind)
        self.kind = kind
        self.span = span


_WS = b" \t\n\r"
_ESC = {ord('"'): '"', ord("\\"): "\\", ord("/"): "/", ord("b"): "\b", ord("f"): "\f",
        ord("n"): "\n", ord("r"): "\r", ord("t"): "\t"}
_HEX = set(b"0123456789abcdefABCDEF")


class _Parser:
    def __init__(self, data: bytes, max_depth: int):
        self.d = data
        self.n = len(data)
        self.i = 0
        self.max_depth = max_depth
        self.scalar_violation: tuple[int, int] | None = None

    def fail(self, at: int | None = None, width: int = 1):
        at = self.i if at is None else at
        raise JsonFailure("syntax", (at, min(self.n, at + width)))

    def ws(self):
        while self.i < self.n and self.d[self.i] in _WS:
            self.i += 1

    def value(self, depth: int) -> JNode:
        self.ws()
        if self.i >= self.n:
            self.fail(width=0)
        c = self.d[self.i]
        if c == 0x7B or c == 0x5B:
            if depth + 1 > self.max_depth:
                raise JsonFailure("depth", (self.i, self.i + 1))
            return self.obj(depth + 1) if c == 0x7B else self.arr(depth + 1)
        if c == 0x22:
            return self.string()
        if c == 0x2D or 0x30 <= c <= 0x39:
            return self.number()
        for lit, kind, val in ((b"true", "boolean", True), (b"false", "boolean", False),
                               (b"null", "null", None)):
            if self.d.startswith(lit, self.i):
                s = self.i
                self.i += len(lit)
                return JNode(kind, s, self.i, val)
        self.fail()

    def obj(self, depth: int) -> JNode:
        s = self.i
        self.i += 1
        node = JNode("object", s, s)
        self.ws()
        if self.i < self.n and self.d[self.i] == 0x7D:
            self.i += 1
            node.end = self.i
            return node
        while True:
            self.ws()
            if self.i >= self.n or self.d[self.i] != 0x22:
                self.fail(width=0 if self.i >= self.n else 1)
            key = self.string()
            self.ws()
            if self.i >= self.n or self.d[self.i] != 0x3A:
                self.fail(width=0 if self.i >= self.n else 1)
            self.i += 1
            v = self.value(depth)
            node.members.append((key.value, key.start, key.end, v))
            self.ws()
            if self.i < self.n and self.d[self.i] == 0x2C:
                self.i += 1
                continue
            if self.i < self.n and self.d[self.i] == 0x7D:
                self.i += 1
                node.end = self.i
                return node
            self.fail(width=0 if self.i >= self.n else 1)

    def arr(self, depth: int) -> JNode:
        s = self.i
        self.i += 1
        node = JNode("array", s, s)
        self.ws()
        if self.i < self.n and self.d[self.i] == 0x5D:
            self.i += 1
            node.end = self.i
            return node
        while True:
            node.members.append(self.value(depth))
            self.ws()
            if self.i < self.n and self.d[self.i] == 0x2C:
                self.i += 1
                continue
            if self.i < self.n and self.d[self.i] == 0x5D:
                self.i += 1
                node.end = self.i
                return node
            self.fail(width=0 if self.i >= self.n else 1)

    def number(self) -> JNode:
        s = self.i
        d = self.d
        if d[self.i] == 0x2D:
            self.i += 1
        if self.i >= self.n:
            self.fail(width=0)
        if d[self.i] == 0x30:
            self.i += 1
        elif 0x31 <= d[self.i] <= 0x39:
            while self.i < self.n and 0x30 <= d[self.i] <= 0x39:
                self.i += 1
        else:
            self.fail()
        if self.i < self.n and d[self.i] == 0x2E:
            self.i += 1
            if self.i >= self.n or not 0x30 <= d[self.i] <= 0x39:
                self.fail(width=0 if self.i >= self.n else 1)
            while self.i < self.n and 0x30 <= d[self.i] <= 0x39:
                self.i += 1
        if self.i < self.n and d[self.i] in (0x65, 0x45):
            self.i += 1
            if self.i < self.n and d[self.i] in (0x2B, 0x2D):
                self.i += 1
            if self.i >= self.n or not 0x30 <= d[self.i] <= 0x39:
                self.fail(width=0 if self.i >= self.n else 1)
            while self.i < self.n and 0x30 <= d[self.i] <= 0x39:
                self.i += 1
        return JNode("number", s, self.i, d[s:self.i].decode("ascii"))

    def string(self) -> JNode:
        s = self.i
        self.i += 1
        d = self.d
        out: list[str] = []
        bad = False
        while True:
            if self.i >= self.n:
                self.fail(width=0)
            c = d[self.i]
            if c == 0x22:
                self.i += 1
                break
            if c < 0x20:
                self.fail()
            if c == 0x5C:
                if self.i + 1 >= self.n:
                    self.fail(self.i + 1, 0)
                e = d[self.i + 1]
                if e in _ESC:
                    out.append(_ESC[e])
                    self.i += 2
                    continue
                if e != 0x75:
                    self.fail(self.i + 1)
                cu = self._hex4(self.i + 2)
                self.i += 6
                if 0xD800 <= cu <= 0xDBFF:
                    if (self.i + 1 < self.n and d[self.i] == 0x5C and d[self.i + 1] == 0x75):
                        lo = self._hex4(self.i + 2)
                        if 0xDC00 <= lo <= 0xDFFF:
                            self.i += 6
                            out.append(chr(0x10000 + ((cu - 0xD800) << 10) + (lo - 0xDC00)))
                            continue
                    bad = True
                    continue
                if 0xDC00 <= cu <= 0xDFFF:
                    bad = True
                    continue
                out.append(chr(cu))
                continue
            if c < 0x80:
                out.append(chr(c))
                self.i += 1
                continue
            ln = 2 if c < 0xE0 else 3 if c < 0xF0 else 4
            out.append(d[self.i:self.i + ln].decode("utf-8"))
            self.i += ln
        if bad and self.scalar_violation is None:
            self.scalar_violation = (s, self.i)
        return JNode("string", s, self.i, "".join(out))

    def _hex4(self, at: int) -> int:
        h = self.d[at:at + 4]
        if len(h) < 4 or any(b not in _HEX for b in h):
            bad_at = at + next((k for k, b in enumerate(h) if b not in _HEX), len(h))
            self.fail(bad_at, 0 if bad_at >= self.n else 1)
        return int(h, 16)


def parse(data: bytes, max_depth: int) -> JNode:
    """UTF-8 検査済みの bytes を strict に解析する。違反は JsonFailure。"""
    p = _Parser(data, max_depth)
    root = p.value(0)
    p.ws()
    if p.i != p.n:
        p.fail()
    if p.scalar_violation is not None:
        raise JsonFailure("scalar", p.scalar_violation)
    dup = _first_duplicate(root)
    if dup is not None:
        raise JsonFailure("duplicate", dup)
    return root


def _first_duplicate(root: JNode) -> tuple[int, int] | None:
    best = None
    stack = [root]
    while stack:
        n = stack.pop()
        if n.kind == "object":
            seen = set()
            for k, ks, ke, v in n.members:
                if k in seen and (best is None or ks < best[0]):
                    best = (ks, ke)
                seen.add(k)
                stack.append(v)
        elif n.kind == "array":
            stack.extend(n.members)
    return best


def scalar_key(s: str) -> list[int]:
    """unknown key の辞書順（scalar 整数値列の辞書順）。"""
    return [ord(c) for c in s]


def shallow_type(n: JNode) -> str:
    return n.kind
