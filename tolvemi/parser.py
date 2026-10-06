"""構文解析、parse Admission、bounded recovery（設計書 §4.1、§10.3、§18.1b）。"""

from __future__ import annotations

from .diagnostics import Diagnostic, error
from .lexer import Token
from .profiles import StaticProfile
from .syntax import (
    BUILTINS, BoolLit, Call, EntryDecl, FnDecl, Fold, If, IntLit, Let, ListLit, NoneE,
    PairE, Param, Program, SomeE, TypeNode, UnitLit, Var,
)

MAX_SYNCS = 8


class ParseError(Exception):
    def __init__(self, code: str, index: int, expected: str | None = None):
        super().__init__(code)
        self.code = code
        self.index = index
        self.expected = expected


class Cutoff(Exception):
    """structural-limits の guard 超過。parse／recovery を打ち切る。"""

    def __init__(self, diag: Diagnostic):
        super().__init__(diag.code)
        self.diag = diag


class Admission:
    """parse-admission-v1 の論理計数。Surface と AST API で共有する。"""

    def __init__(self, profile: StaticProfile):
        self.profile = profile
        self.ast_nodes = 0
        self.functions = 0
        self.index = 0

    def admit(self, span, *, fn=False, type_depth=None, expr_depth=None,
              let_depth=None, fold_depth=None) -> int:
        p = self.profile
        violation = None
        if fn and self.functions + 1 > p.functions:
            violation = ("E-LIMIT-STATIC-FUNCTIONS", p.functions, self.functions + 1)
        elif self.ast_nodes + 1 > p.ast_nodes:
            violation = ("E-LIMIT-STATIC-AST-NODES", p.ast_nodes, self.ast_nodes + 1)
        elif type_depth is not None and type_depth > p.type_depth:
            violation = ("E-LIMIT-STATIC-TYPE-DEPTH", p.type_depth, type_depth)
        elif expr_depth is not None and expr_depth > p.expr_depth:
            violation = ("E-LIMIT-STATIC-EXPR-DEPTH", p.expr_depth, expr_depth)
        elif let_depth is not None and let_depth > p.let_depth:
            violation = ("E-LIMIT-STATIC-LET-DEPTH", p.let_depth, let_depth)
        elif fold_depth is not None and fold_depth > p.fold_depth:
            violation = ("E-LIMIT-STATIC-FOLD-DEPTH", p.fold_depth, fold_depth)
        if violation:
            code, limit, observed = violation
            raise Cutoff(error("structural-limits", code, span, str(limit), str(observed),
                               node_index=self.index))
        self.ast_nodes += 1
        if fn:
            self.functions += 1
        idx = self.index
        self.index += 1
        return idx


class Parser:
    def __init__(self, tokens: list[Token], profile: StaticProfile):
        self.toks = tokens
        self.pos = 0
        self.adm = Admission(profile)
        self.diags: list[Diagnostic] = []
        self.prev_end = 0

    # ------------------------------------------------------------ helpers

    def peek(self, k: int = 0) -> Token:
        return self.toks[min(self.pos + k, len(self.toks) - 1)]

    def advance(self) -> Token:
        tok = self.toks[self.pos]
        if tok.kind != "EOF":
            self.pos += 1
            self.prev_end = tok.end
        return tok

    def is_punct(self, text: str, k: int = 0) -> bool:
        t = self.peek(k)
        return t.kind == "PUNCT" and t.text == text

    def is_kw(self, text: str, k: int = 0) -> bool:
        t = self.peek(k)
        return t.kind == "KW" and t.text == text

    def expect(self, text: str) -> Token:
        if self.is_punct(text) or self.is_kw(text):
            return self.advance()
        raise ParseError("E-PARSE-EXPECTED-TOKEN", self.pos, f'"{text}"')

    def expect_ident(self) -> Token:
        if self.peek().kind == "IDENT":
            return self.advance()
        raise ParseError("E-PARSE-EXPECTED-IDENT", self.pos, "identifier")

    def emit(self, code: str, index: int, expected: str | None = None) -> None:
        tok = self.toks[index]
        d = error("parse", code, tok.span, expected, tok.describe(), node_index=self.adm.index)
        d.seq = len(self.diags)
        self.diags.append(d)

    def at_decl_end(self) -> bool:
        t = self.peek()
        return t.kind == "EOF" or (t.kind == "KW" and t.text in ("fn", "entry"))

    # ------------------------------------------------------------ program

    def parse_program(self) -> Program | None:
        """成功時は Program、parse error 時は None（self.diags に診断）。Cutoff は送出。"""
        prog_idx = self.adm.admit((0, 0))
        decls = []
        syncs = 0
        while True:
            s = self.pos
            tok = self.peek()
            if tok.kind == "EOF":
                break
            try:
                if self.is_kw("fn"):
                    decls.append(self.parse_fn())
                elif self.is_kw("entry"):
                    decls.append(self.parse_entry())
                else:
                    raise ParseError("E-PARSE-UNEXPECTED-TOKEN", self.pos, "fn | entry")
            except ParseError as e:
                self.emit(e.code, e.index, e.expected)
                p = e.index
                if self.toks[p].kind == "EOF":
                    break
                if syncs == MAX_SYNCS:
                    self.emit("E-PARSE-RECOVERY-LIMIT", p)
                    break
                q = max(p, s + 1)
                while not (self.toks[q].kind == "EOF" or (
                        self.toks[q].kind == "KW" and self.toks[q].text in ("fn", "entry"))):
                    q += 1
                syncs += 1
                self.pos = q
                if self.toks[q].kind == "EOF":
                    break
        if self.diags:
            return None
        end = self.toks[-1].end
        return Program(tuple(decls), span=(0, end), index=prog_idx)

    def parse_fn(self) -> FnDecl:
        kw = self.advance()
        idx = self.adm.admit(kw.span, fn=True)
        name = self.expect_ident()
        self.expect("(")
        params = []
        if not self.is_punct(")"):
            while True:
                ptok = self.peek()
                if ptok.kind != "IDENT":
                    raise ParseError("E-PARSE-EXPECTED-IDENT", self.pos, "identifier")
                pidx = self.adm.admit(ptok.span)
                self.advance()
                self.expect(":")
                ty = self.parse_type(1)
                params.append(Param(ptok.text, ty, name_span=ptok.span,
                                    span=(ptok.start, self.prev_end), index=pidx))
                if self.is_punct(","):
                    self.advance()
                    continue
                break
        self.expect(")")
        self.expect("->")
        ret = self.parse_type(1)
        self.expect("=")
        body = self.parse_expr(1, 0, 0)
        if not self.at_decl_end():
            raise ParseError("E-PARSE-UNEXPECTED-TOKEN", self.pos, "fn | entry | EOF")
        return FnDecl(name.text, tuple(params), ret, body, name_span=name.span,
                      span=(kw.start, self.prev_end), index=idx)

    def parse_entry(self) -> EntryDecl:
        kw = self.advance()
        idx = self.adm.admit(kw.span)
        name = self.expect_ident()
        if not self.at_decl_end():
            raise ParseError("E-PARSE-UNEXPECTED-TOKEN", self.pos, "fn | entry | EOF")
        return EntryDecl(name.text, name_span=name.span, span=(kw.start, self.prev_end), index=idx)

    # ------------------------------------------------------------ types

    def parse_type(self, depth: int) -> TypeNode:
        tok = self.peek()
        if tok.kind != "KW" or tok.text not in ("Int", "Bool", "Unit", "List", "Option", "Pair"):
            raise ParseError("E-PARSE-EXPECTED-TYPE", self.pos, "type")
        idx = self.adm.admit(tok.span, type_depth=depth)
        self.advance()
        args: tuple = ()
        if tok.text in ("List", "Option"):
            self.expect("<")
            args = (self.parse_type(depth + 1),)
            self.expect(">")
        elif tok.text == "Pair":
            self.expect("<")
            a = self.parse_type(depth + 1)
            self.expect(",")
            b = self.parse_type(depth + 1)
            self.expect(">")
            args = (a, b)
        return TypeNode(tok.text, args, span=(tok.start, self.prev_end), index=idx)

    # ------------------------------------------------------------ expressions

    def parse_args(self, d: int, ld: int, fd: int) -> tuple:
        args = []
        if self.is_punct(")"):
            return ()
        while True:
            args.append(self.parse_expr(d, ld, fd))
            if self.is_punct(","):
                self.advance()
                continue
            return tuple(args)

    def parse_expr(self, d: int, ld: int, fd: int):
        tok = self.peek()
        start = tok.start
        k, t = tok.kind, tok.text

        def done(node_cls, *a, **kw):
            return node_cls(*a, span=(start, self.prev_end), **kw)

        if k == "INT":
            idx = self.adm.admit(tok.span, expr_depth=d)
            self.advance()
            return done(IntLit, int(t), index=idx)
        if k == "IDENT":
            idx = self.adm.admit(tok.span, expr_depth=d)
            self.advance()
            if self.is_punct("("):
                self.advance()
                args = self.parse_args(d + 1, ld, fd)
                self.expect(")")
                return done(Call, t, args, False, callee_span=tok.span, index=idx)
            return done(Var, t, index=idx)
        if k != "KW":
            raise ParseError("E-PARSE-EXPECTED-EXPR", self.pos, "expression")
        if t in ("true", "false"):
            idx = self.adm.admit(tok.span, expr_depth=d)
            self.advance()
            return done(BoolLit, t == "true", index=idx)
        if t == "unit":
            idx = self.adm.admit(tok.span, expr_depth=d)
            self.advance()
            return done(UnitLit, index=idx)
        if t == "list":
            idx = self.adm.admit(tok.span, expr_depth=d)
            self.advance()
            self.expect("[")
            ty = self.parse_type(1)
            self.expect("]")
            self.expect("(")
            items = self.parse_args(d + 1, ld, fd)
            self.expect(")")
            return done(ListLit, ty, items, index=idx)
        if t == "some":
            idx = self.adm.admit(tok.span, expr_depth=d)
            self.advance()
            self.expect("(")
            v = self.parse_expr(d + 1, ld, fd)
            self.expect(")")
            return done(SomeE, v, index=idx)
        if t == "none":
            idx = self.adm.admit(tok.span, expr_depth=d)
            self.advance()
            self.expect("[")
            ty = self.parse_type(1)
            self.expect("]")
            return done(NoneE, ty, index=idx)
        if t == "pair":
            idx = self.adm.admit(tok.span, expr_depth=d)
            self.advance()
            self.expect("(")
            a = self.parse_expr(d + 1, ld, fd)
            self.expect(",")
            b = self.parse_expr(d + 1, ld, fd)
            self.expect(")")
            return done(PairE, a, b, index=idx)
        if t == "let":
            idx = self.adm.admit(tok.span, expr_depth=d, let_depth=ld + 1)
            self.advance()
            name = self.expect_ident()
            self.expect("=")
            v = self.parse_expr(d + 1, ld + 1, fd)
            self.expect("in")
            body = self.parse_expr(d + 1, ld + 1, fd)
            return done(Let, name.text, v, body, name_span=name.span, index=idx)
        if t == "if":
            idx = self.adm.admit(tok.span, expr_depth=d)
            self.advance()
            self.expect("(")
            c = self.parse_expr(d + 1, ld, fd)
            self.expect(",")
            a = self.parse_expr(d + 1, ld, fd)
            self.expect(",")
            b = self.parse_expr(d + 1, ld, fd)
            self.expect(")")
            return done(If, c, a, b, index=idx)
        if t == "fold":
            idx = self.adm.admit(tok.span, expr_depth=d, fold_depth=fd + 1)
            self.advance()
            self.expect("(")
            xs = self.parse_expr(d + 1, ld, fd + 1)
            self.expect(",")
            init = self.parse_expr(d + 1, ld, fd + 1)
            self.expect(",")
            self.expect("|")
            acc = self.expect_ident()
            self.expect(",")
            item = self.expect_ident()
            self.expect("|")
            body = self.parse_expr(d + 1, ld, fd + 1)
            self.expect(")")
            return done(Fold, xs, init, acc.text, item.text, body,
                        acc_span=acc.span, item_span=item.span, index=idx)
        if t in BUILTINS:
            idx = self.adm.admit(tok.span, expr_depth=d)
            self.advance()
            self.expect("(")
            args = self.parse_args(d + 1, ld, fd)
            self.expect(")")
            return done(Call, t, args, True, callee_span=tok.span, index=idx)
        raise ParseError("E-PARSE-EXPECTED-EXPR", self.pos, "expression")
