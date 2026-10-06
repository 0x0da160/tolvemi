"""ast_codec_v1 の decoder（設計書 §19.2–19.3、§18.1b の AST API Admission）。"""

from __future__ import annotations

import re

from .diagnostics import Diagnostic, error
from .parser import Admission
from .profiles import AstTransportProfile, StaticProfile
from .strict_json import JNode, JsonFailure, parse, scalar_key
from .syntax import (
    BUILTINS, KEYWORDS, BoolLit, Call, EntryDecl, FnDecl, Fold, If, IntLit, Let, ListLit,
    NoneE, PairE, Param, Program, SomeE, TypeNode, UnitLit, Var,
)

_IDENT_RE = re.compile(r"[A-Za-z_][A-Za-z0-9_]*\Z")
_INT_RE = re.compile(r"(0|-?[1-9][0-9]*)\Z")

PROGRAM_FIELDS = [("codec", "string"), ("declarations", "array")]
DECL_FIELDS = {
    "fn": [("name", "string"), ("params", "array"), ("return_type", "object"),
           ("body", "object")],
    "entry": [("name", "string")],
}
PARAM_FIELDS = [("name", "string"), ("type", "object")]
TYPE_FIELDS = {
    "int": [], "bool": [], "unit": [],
    "list": [("element", "object")], "option": [("element", "object")],
    "pair": [("left", "object"), ("right", "object")],
}
EXPR_FIELDS = {
    "int": [("value", "string")],
    "bool": [("value", "boolean")],
    "unit": [],
    "var": [("name", "string")],
    "list": [("element_type", "object"), ("items", "array")],
    "some": [("value", "object")],
    "none": [("element_type", "object")],
    "pair": [("left", "object"), ("right", "object")],
    "call": [("callee", "string"), ("args", "array")],
    "let": [("name", "string"), ("value", "object"), ("body", "object")],
    "if": [("condition", "object"), ("then", "object"), ("else", "object")],
    "fold": [("list", "object"), ("init", "object"), ("acc", "string"), ("item", "string"),
             ("body", "object")],
}
TYPE_TAG_NAME = {"int": "Int", "bool": "Bool", "unit": "Unit", "list": "List",
                 "option": "Option", "pair": "Pair"}


class AstBoundaryFailure:
    reason = "InvalidUtf8"

    def __repr__(self) -> str:
        return "AstBoundaryFailure(InvalidUtf8)"


class AstInvalid:
    def __init__(self, diagnostics: list[Diagnostic]):
        self.diagnostics = diagnostics

    def __repr__(self) -> str:
        return f"AstInvalid({[d.code for d in self.diagnostics]})"


class _Fail(Exception):
    def __init__(self, diag: Diagnostic):
        self.diag = diag


def transport(data: bytes, transport_profile: AstTransportProfile, static: StaticProfile):
    """transport 検査。成功時は JNode、失敗時は AstBoundaryFailure／AstInvalid。"""
    if len(data) > transport_profile.json_bytes:
        return AstInvalid([error("ast-boundary", "E-AST-LIMIT-BYTES", (0, 0),
                                 str(transport_profile.json_bytes), str(len(data)))])
    try:
        data.decode("utf-8")
    except UnicodeDecodeError:
        return AstBoundaryFailure()
    try:
        root = parse(data, transport_profile.json_depth)
    except JsonFailure as f:
        code = {"syntax": "E-AST-JSON-SYNTAX", "depth": "E-AST-LIMIT-JSON-DEPTH",
                "scalar": "E-AST-STRING-SCALAR", "duplicate": "E-AST-DUPLICATE-KEY"}[f.kind]
        return AstInvalid([error("ast-parse", code, f.span)])
    try:
        _SchemaChecker(static).program(root)
    except _Fail as f:
        return AstInvalid([f.diag])
    return root


class _SchemaChecker:
    def __init__(self, static: StaticProfile):
        self.static = static

    def fail(self, code, span, expected=None, actual=None):
        raise _Fail(error("ast-schema", code, span, expected, actual))

    def header(self, n: JNode, allowed: dict) -> str:
        if n.kind != "object":
            self.fail("E-AST-FIELD-TYPE", n.span, "object", n.kind)
        tag = n.get("tag")
        if tag is None:
            self.fail("E-AST-MISSING-FIELD", (n.end - 1, n.end - 1), "tag")
        if tag.kind != "string":
            self.fail("E-AST-TAG", tag.span, "string", tag.kind)
        if tag.value not in allowed:
            self.fail("E-AST-TAG", tag.span, " | ".join(allowed), tag.value)
        return tag.value

    def keys(self, n: JNode, fields: list, tagged: bool) -> None:
        present = {k for k, *_ in n.members}
        for k, _ in fields:
            if k not in present:
                self.fail("E-AST-MISSING-FIELD", (n.end - 1, n.end - 1), k)
        allowed = {k for k, _ in fields} | ({"tag"} if tagged else set())
        extra = sorted((k for k in present if k not in allowed), key=scalar_key)
        if extra:
            self.fail("E-AST-UNKNOWN-FIELD", n.key_span(extra[0]), None, extra[0])
        for k, kind in fields:
            child = n.get(k)
            if child.kind != kind:
                self.fail("E-AST-FIELD-TYPE", child.span, kind, child.kind)

    def ident(self, s: JNode) -> None:
        if not _IDENT_RE.match(s.value) or s.value in KEYWORDS:
            self.fail("E-AST-IDENTIFIER", s.span, "identifier", None)

    def program(self, n: JNode) -> None:
        if n.kind != "object":
            self.fail("E-AST-FIELD-TYPE", n.span, "object", n.kind)
        codec = n.get("codec")
        if codec is None:
            self.fail("E-AST-CODEC", (n.end - 1, n.end - 1), "ast_codec_v1")
        if codec.kind != "string" or codec.value != "ast_codec_v1":
            self.fail("E-AST-CODEC", codec.span, "ast_codec_v1")
        self.keys(n, PROGRAM_FIELDS, tagged=False)
        for d in n.get("declarations").members:
            self.decl(d)

    def decl(self, n: JNode) -> None:
        tag = self.header(n, DECL_FIELDS)
        self.keys(n, DECL_FIELDS[tag], tagged=True)
        self.ident(n.get("name"))
        if tag == "fn":
            for p in n.get("params").members:
                self.param(p)
            self.type(n.get("return_type"))
            self.expr(n.get("body"))

    def param(self, n: JNode) -> None:
        if n.kind != "object":
            self.fail("E-AST-FIELD-TYPE", n.span, "object", n.kind)
        self.keys(n, PARAM_FIELDS, tagged=False)
        self.ident(n.get("name"))
        self.type(n.get("type"))

    def type(self, n: JNode) -> None:
        tag = self.header(n, TYPE_FIELDS)
        fields = TYPE_FIELDS[tag]
        self.keys(n, fields, tagged=True)
        for k, _ in fields:
            self.type(n.get(k))

    def expr(self, n: JNode) -> None:
        tag = self.header(n, EXPR_FIELDS)
        fields = EXPR_FIELDS[tag]
        self.keys(n, fields, tagged=True)
        for k, _ in fields:
            c = n.get(k)
            if tag == "int" and k == "value":
                if not _INT_RE.match(c.value):
                    self.fail("E-AST-INTEGER", c.span)
                digits = len(c.value.lstrip("-"))
                if digits > self.static.integer_digits:
                    self.fail("E-AST-LIMIT-INTEGER-DIGITS", c.span,
                              str(self.static.integer_digits), str(digits))
            elif tag == "call" and k == "callee":
                if c.value not in BUILTINS:
                    self.ident(c)
            elif k in ("name", "acc", "item"):
                self.ident(c)
            elif k in ("element_type",):
                self.type(c)
            elif k in ("items", "args"):
                for item in c.members:
                    self.expr(item)
            elif c.kind == "object":
                self.expr(c)


class _Builder:
    """transport 通過後、共通 Admission を発行しながら表面 AST を構築する。"""

    def __init__(self, static: StaticProfile):
        self.adm = Admission(static)

    def program(self, n: JNode) -> Program:
        idx = self.adm.admit(n.span)
        decls = []
        for d in n.get("declarations").members:
            name = d.get("name")
            if d.get("tag").value == "entry":
                i = self.adm.admit(d.span)
                decls.append(EntryDecl(name.value, name_span=name.span, span=d.span, index=i))
                continue
            i = self.adm.admit(d.span, fn=True)
            params = []
            for p in d.get("params").members:
                pi = self.adm.admit(p.span)
                pn = p.get("name")
                params.append(Param(pn.value, self.type(p.get("type"), 1), name_span=pn.span,
                                    span=p.span, index=pi))
            ret = self.type(d.get("return_type"), 1)
            body = self.expr(d.get("body"), 1, 0, 0)
            decls.append(FnDecl(name.value, tuple(params), ret, body, name_span=name.span,
                                span=d.span, index=i))
        return Program(tuple(decls), span=n.span, index=idx)

    def type(self, n: JNode, depth: int) -> TypeNode:
        tag = n.get("tag").value
        i = self.adm.admit(n.span, type_depth=depth)
        args = tuple(self.type(n.get(k), depth + 1) for k, _ in TYPE_FIELDS[tag])
        return TypeNode(TYPE_TAG_NAME[tag], args, span=n.span, index=i)

    def expr(self, n: JNode, d: int, ld: int, fd: int):
        tag = n.get("tag").value
        sp = n.span
        if tag == "let":
            i = self.adm.admit(sp, expr_depth=d, let_depth=ld + 1)
            ld += 1
        elif tag == "fold":
            i = self.adm.admit(sp, expr_depth=d, fold_depth=fd + 1)
            fd += 1
        else:
            i = self.adm.admit(sp, expr_depth=d)
        sub = lambda key: self.expr(n.get(key), d + 1, ld, fd)  # noqa: E731
        if tag == "int":
            return IntLit(int(n.get("value").value), span=sp, index=i)
        if tag == "bool":
            return BoolLit(n.get("value").value, span=sp, index=i)
        if tag == "unit":
            return UnitLit(span=sp, index=i)
        if tag == "var":
            return Var(n.get("name").value, span=sp, index=i)
        if tag == "list":
            ty = self.type(n.get("element_type"), 1)
            items = tuple(self.expr(c, d + 1, ld, fd) for c in n.get("items").members)
            return ListLit(ty, items, span=sp, index=i)
        if tag == "some":
            return SomeE(sub("value"), span=sp, index=i)
        if tag == "none":
            return NoneE(self.type(n.get("element_type"), 1), span=sp, index=i)
        if tag == "pair":
            left = sub("left")
            return PairE(left, sub("right"), span=sp, index=i)
        if tag == "call":
            callee = n.get("callee")
            args = tuple(self.expr(c, d + 1, ld, fd) for c in n.get("args").members)
            return Call(callee.value, args, callee.value in BUILTINS, callee_span=callee.span,
                        span=sp, index=i)
        if tag == "let":
            value = sub("value")
            name = n.get("name")
            return Let(name.value, value, sub("body"), name_span=name.span, span=sp, index=i)
        if tag == "if":
            c = sub("condition")
            t = sub("then")
            return If(c, t, sub("else"), span=sp, index=i)
        if tag == "fold":
            xs = sub("list")
            init = sub("init")
            acc, item = n.get("acc"), n.get("item")
            return Fold(xs, init, acc.value, item.value, sub("body"), acc_span=acc.span,
                        item_span=item.span, span=sp, index=i)
        raise ValueError(tag)


def build(root: JNode, static: StaticProfile) -> Program:
    """Admission 付きで表面 AST を構築する。guard 超過は parser.Cutoff を送出する。"""
    return _Builder(static).program(root)
