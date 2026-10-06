"""実行時の値と値 JSON codec（設計書 §3.2、§8.4、§9）。

値は有限木の意味を持つ不変 DAG。Int は Python int、Bool は Python bool、
Unit／none／空リストは共有 singleton（割当0）。
"""

from __future__ import annotations

import re

from .diagnostics import Diagnostic, error
from .profiles import InputProfile
from .strict_json import JNode, JsonFailure, parse, scalar_key
from .syntax import Ty


class _Singleton:
    __slots__ = ("name",)

    def __init__(self, name: str):
        self.name = name

    def __repr__(self) -> str:
        return self.name


UNIT_V = _Singleton("unit")
NONE_V = _Singleton("none")
NIL = _Singleton("nil")


class SomeV:
    __slots__ = ("value",)

    def __init__(self, value):
        self.value = value


class PairV:
    __slots__ = ("left", "right")

    def __init__(self, left, right):
        self.left = left
        self.right = right


class Cons:
    __slots__ = ("head", "tail")

    def __init__(self, head, tail):
        self.head = head
        self.tail = tail


def from_python_list(items) -> object:
    out = NIL
    for v in reversed(list(items)):
        out = Cons(v, out)
    return out


def iter_list(v):
    while v is not NIL:
        yield v.head
        v = v.tail


# ---------------------------------------------------------------- encode


def encode_value(v) -> str:
    """正準 JSON（最小空白、正準 key 順）。深い値でも再帰しない。"""
    out: list[str] = []
    stack: list = [("v", v)]
    while stack:
        kind, x = stack.pop()
        if kind == "s":
            out.append(x)
            continue
        if isinstance(x, bool):
            out.append('{"tag":"bool","value":true}' if x else '{"tag":"bool","value":false}')
        elif isinstance(x, int):
            out.append('{"tag":"int","value":"%d"}' % x)
        elif x is UNIT_V:
            out.append('{"tag":"unit"}')
        elif x is NONE_V:
            out.append('{"tag":"none"}')
        elif isinstance(x, SomeV):
            out.append('{"tag":"some","value":')
            stack.append(("s", "}"))
            stack.append(("v", x.value))
        elif isinstance(x, PairV):
            out.append('{"tag":"pair","left":')
            stack.append(("s", "}"))
            stack.append(("v", x.right))
            stack.append(("s", ',"right":'))
            stack.append(("v", x.left))
        elif x is NIL or isinstance(x, Cons):
            out.append('{"tag":"list","items":[')
            items = list(iter_list(x))
            stack.append(("s", "]}"))
            for k in range(len(items) - 1, -1, -1):
                stack.append(("v", items[k]))
                if k:
                    stack.append(("s", ","))
        else:
            raise TypeError(f"not a value: {x!r}")
    return "".join(out)


# ---------------------------------------------------------------- decode

_INT_RE = re.compile(r"(0|-?[1-9][0-9]*)\Z")

_KEYS = {
    "int": [("value", "string")],
    "bool": [("value", "boolean")],
    "unit": [],
    "list": [("items", "array")],
    "some": [("value", "object")],
    "none": [],
    "pair": [("left", "object"), ("right", "object")],
}


def _tags_for(t: Ty) -> tuple[str, ...]:
    return {"Int": ("int",), "Bool": ("bool",), "Unit": ("unit",), "List": ("list",),
            "Option": ("some", "none"), "Pair": ("pair",)}[t.tag]


class InputBoundaryFailure:
    reason = "InvalidUtf8"

    def __repr__(self) -> str:
        return "InputBoundaryFailure(InvalidUtf8)"


class Decoded:
    def __init__(self, value, type_: Ty):
        self.value = value
        self.type = type_

    def __repr__(self) -> str:
        return f"Decoded({encode_value(self.value)})"


class Invalid:
    def __init__(self, diagnostics: list[Diagnostic]):
        self.diagnostics = diagnostics

    def __repr__(self) -> str:
        return f"Invalid({[d.code for d in self.diagnostics]})"


class _Fail(Exception):
    def __init__(self, diag: Diagnostic):
        self.diag = diag


def decode_input(t_in: Ty, data: bytes, profile: InputProfile = InputProfile()):
    if len(data) > profile.json_bytes:
        return Invalid([error("input-boundary", "E-LIMIT-INPUT-JSON-BYTES", (0, 0),
                              str(profile.json_bytes), str(len(data)))])
    try:
        data.decode("utf-8")
    except UnicodeDecodeError:
        return InputBoundaryFailure()
    try:
        root = parse(data, profile.json_depth)
    except JsonFailure as f:
        code = {"syntax": "E-INPUT-JSON-SYNTAX", "depth": "E-LIMIT-INPUT-JSON-DEPTH",
                "scalar": "E-INPUT-STRING-SCALAR", "duplicate": "E-INPUT-DUPLICATE-KEY"}[f.kind]
        return Invalid([error("input-parse", code, f.span)])
    dec = _ValueDecoder(profile)
    try:
        v = dec.value(root, t_in, 1)
    except _Fail as f:
        return Invalid([f.diag])
    return Decoded(v, t_in)


class _ValueDecoder:
    def __init__(self, profile: InputProfile):
        self.p = profile
        self.nodes = 0

    def fail(self, code, span, expected=None, actual=None):
        raise _Fail(error("input-decode", code, span, expected, actual))

    def value(self, n: JNode, t: Ty, depth: int):
        # 1. object であること
        if n.kind != "object":
            self.fail("E-INPUT-FIELD-TYPE", n.span, "object", n.kind)
        # 2. tag
        tag_node = n.get("tag")
        if tag_node is None:
            self.fail("E-INPUT-MISSING-FIELD", (n.end - 1, n.end - 1), "tag")
        allowed = _tags_for(t)
        if tag_node.kind != "string" or tag_node.value not in allowed:
            self.fail("E-INPUT-TAG", tag_node.span, " | ".join(allowed), str(t))
        tag = tag_node.value
        fields = _KEYS[tag]
        # 3. 必須キー → 余分キー
        present = {k for k, *_ in n.members}
        for k, _ in fields:
            if k not in present:
                self.fail("E-INPUT-MISSING-FIELD", (n.end - 1, n.end - 1), k)
        allowed_keys = {"tag"} | {k for k, _ in fields}
        extra = sorted((k for k in present if k not in allowed_keys), key=scalar_key)
        if extra:
            self.fail("E-INPUT-UNKNOWN-FIELD", n.key_span(extra[0]), None, extra[0])
        # 4. 浅い JSON 型（正準 key 順）
        for k, kind in fields:
            child = n.get(k)
            if child.kind != kind:
                self.fail("E-INPUT-FIELD-TYPE", child.span, kind, child.kind)
        # 5. InputAdmission（深さ超過を優先）
        if depth > self.p.value_depth:
            self.fail("E-LIMIT-INPUT-VALUE-DEPTH", n.span, str(self.p.value_depth), str(depth))
        if self.nodes + 1 > self.p.value_nodes:
            self.fail("E-LIMIT-INPUT-VALUE-NODES", n.span, str(self.p.value_nodes),
                      str(self.nodes + 1))
        self.nodes += 1
        # 6. 内容
        if tag == "int":
            s = n.get("value")
            if not _INT_RE.match(s.value):
                self.fail("E-INPUT-INTEGER", s.span)
            digits = len(s.value.lstrip("-"))
            if digits > self.p.integer_digits:
                self.fail("E-LIMIT-INPUT-INTEGER-DIGITS", s.span, str(self.p.integer_digits),
                          str(digits))
            return int(s.value)
        if tag == "bool":
            return n.get("value").value
        if tag == "unit":
            return UNIT_V
        if tag == "none":
            return NONE_V
        if tag == "some":
            return SomeV(self.value(n.get("value"), t.args[0], depth + 1))
        if tag == "pair":
            left = self.value(n.get("left"), t.args[0], depth + 1)
            right = self.value(n.get("right"), t.args[1], depth + 1)
            return PairV(left, right)
        items = [self.value(c, t.args[0], depth + 1) for c in n.get("items").members]
        return from_python_list(items)
