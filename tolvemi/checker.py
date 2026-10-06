"""共通静的検査：name → call-graph → typecheck(+semantic-limits) → entry → warnings。

Surface（compile）と AST（compile_ast）の双方がこのモジュールを通る（設計書 §5、§6、
§10.2、§18.1a）。
"""

from __future__ import annotations

from dataclasses import dataclass, field

from .diagnostics import Diagnostic, error, warning
from .profiles import StaticProfile
from .syntax import (
    BOOL, BUILTIN_ARITY, ERROR, INT, BoolLit, Call, EntryDecl, FnDecl, Fold, If, IntLit,
    Let, ListLit, NoneE, PairE, Program, SomeE, Ty, UnitLit, Var, children, ty_of,
)

# ======================================================================= name


def check_names(prog: Program, fns: list[FnDecl], entries: list[EntryDecl]) -> list[Diagnostic]:
    diags: list[Diagnostic] = []
    known: set[str] = set()
    for f in fns:
        if f.name in known:
            diags.append(error("name", "E-NAME-DUPLICATE-FUNCTION", f.name_span, None, f.name,
                               f.index))
        known.add(f.name)

    def walk(e, env: frozenset):
        if isinstance(e, Var):
            if e.name not in env:
                diags.append(error("name", "E-NAME-UNBOUND-VARIABLE", e.span, None, e.name, e.index))
            return
        if isinstance(e, Call):
            if not e.builtin and e.callee not in known:
                diags.append(error("name", "E-NAME-UNKNOWN-FUNCTION", e.callee_span, None,
                                   e.callee, e.index))
            for a in e.args:
                walk(a, env)
            return
        if isinstance(e, Let):
            walk(e.value, env)
            if e.name in env:
                diags.append(error("name", "E-NAME-SHADOW", e.name_span, None, e.name, e.index))
            walk(e.body, env | {e.name})
            return
        if isinstance(e, Fold):
            walk(e.list, env)
            walk(e.init, env)
            if e.acc in env:
                diags.append(error("name", "E-NAME-SHADOW", e.acc_span, None, e.acc, e.index))
            if e.item == e.acc:
                diags.append(error("name", "E-NAME-DUPLICATE-BINDER", e.item_span, None, e.item,
                                   e.index))
            elif e.item in env:
                diags.append(error("name", "E-NAME-SHADOW", e.item_span, None, e.item, e.index))
            walk(e.body, env | {e.acc, e.item})
            return
        for c in children(e):
            walk(c, env)

    for d in prog.declarations:
        if isinstance(d, FnDecl):
            seen: set[str] = set()
            for p in d.params:
                if p.name in seen:
                    diags.append(error("name", "E-NAME-DUPLICATE-PARAM", p.name_span, None, p.name,
                                       p.index))
                seen.add(p.name)
            walk(d.body, frozenset(seen))
        else:
            if d.name not in known:
                diags.append(error("name", "E-ENTRY-UNKNOWN", d.name_span, None, d.name, d.index))
    return diags


# ================================================================= call graph


def user_calls(e):
    """本体中の全ての構文上のユーザー call（非選択枝・fold 本体を含む）を前順で返す。"""
    out = []
    stack = [e]
    while stack:
        x = stack.pop()
        if isinstance(x, Call) and not x.builtin:
            out.append(x)
        stack.extend(reversed(children(x)))
    return out


def check_call_graph(fns: list[FnDecl]) -> tuple[list[Diagnostic], dict[str, int] | None,
                                                  dict[str, list[Call]]]:
    edges = {f.name: user_calls(f.body) for f in fns}
    names = [f.name for f in fns]
    # Tarjan の強連結成分分解（反復版）
    index: dict[str, int] = {}
    low: dict[str, int] = {}
    on_stack: set[str] = set()
    stack: list[str] = []
    sccs: list[list[str]] = []
    counter = 0
    for root in names:
        if root in index:
            continue
        work = [(root, 0)]
        while work:
            v, i = work.pop()
            if i == 0:
                index[v] = low[v] = counter
                counter += 1
                stack.append(v)
                on_stack.add(v)
            succ = edges[v]
            if i < len(succ):
                work.append((v, i + 1))
                w = succ[i].callee
                if w not in index:
                    work.append((w, 0))
                elif w in on_stack:
                    low[v] = min(low[v], index[w])
                continue
            if low[v] == index[v]:
                comp = []
                while True:
                    w = stack.pop()
                    on_stack.discard(w)
                    comp.append(w)
                    if w == v:
                        break
                sccs.append(comp)
            if work:
                parent = work[-1][0]
                low[parent] = min(low[parent], low[v])
    diags = []
    for comp in sccs:
        members = set(comp)
        inner = [c for f in comp for c in edges[f] if c.callee in members]
        if not inner:
            continue
        primary = min(inner, key=lambda c: (c.callee_span[0], c.callee_span[1]))
        names_sorted = sorted(members)
        d = error("call-graph", "E-CYCLE-CALL", primary.callee_span, None, ", ".join(names_sorted),
                  primary.index)
        d.message = f"関数呼出しが循環しています: {', '.join(names_sorted)}"
        diags.append(d)
    if diags:
        return diags, None, edges
    rank: dict[str, int] = {}
    for comp in sccs:  # Tarjan は逆トポロジカル順に成分を返す
        (f,) = comp
        rank[f] = 1 + max((rank[c.callee] for c in edges[f]), default=-1)
    return diags, rank, edges


# ================================================================= typecheck


class SemanticCutoff(Exception):
    def __init__(self, diag: Diagnostic):
        super().__init__(diag.code)
        self.diag = diag


@dataclass
class WorkCounter:
    visit: int = 0
    build: int = 0
    compare: int = 0

    @property
    def total(self) -> int:
        return self.visit + self.build + self.compare


class TypeChecker:
    def __init__(self, fns: dict[str, FnDecl], profile: StaticProfile):
        self.fns = fns
        self.profile = profile
        self.work = WorkCounter()
        self.diags: list[Diagnostic] = []

    # ---------------------------------------------------------- events

    def _event(self, kind: str, node) -> None:
        if self.work.total + 1 > self.profile.semantic_work:
            raise SemanticCutoff(error("semantic-limits", "E-LIMIT-STATIC-SEMANTIC-WORK", node.span,
                                       str(self.profile.semantic_work),
                                       str(self.work.total + 1), node.index))
        setattr(self.work, kind, getattr(self.work, kind) + 1)

    def build(self, ty: Ty, node) -> Ty:
        if ty.depth > self.profile.semantic_type_depth:
            raise SemanticCutoff(error("semantic-limits", "E-LIMIT-STATIC-SEMANTIC-TYPE-DEPTH",
                                       node.span, str(self.profile.semantic_type_depth),
                                       str(ty.depth), node.index))
        self._event("build", node)
        return ty

    def equal(self, a: Ty, b: Ty, node) -> bool | None:
        """Equal(A,B)。ErrorType を含むなら 0 イベントで None。"""
        if a.is_error or b.is_error:
            return None
        todo = [(a, b)]
        while todo:
            x, y = todo.pop()
            self._event("compare", node)
            if x.tag != y.tag:
                return False
            todo.extend(reversed(list(zip(x.args, y.args))))
        return True

    def head(self, t: Ty, tag: str, node) -> bool | None:
        if t.is_error:
            return None
        self._event("compare", node)
        return t.tag == tag

    def report(self, code: str, node, expected=None, actual=None) -> None:
        self.diags.append(error("typecheck", code, node.span,
                                None if expected is None else str(expected),
                                None if actual is None else str(actual), node.index))

    # ---------------------------------------------------------- functions

    def check_function(self, f: FnDecl) -> None:
        env = {p.name: ty_of(p.type) for p in f.params}
        body_t = self.expr(f.body, env)
        ret = ty_of(f.return_type)
        if self.equal(body_t, ret, f.body) is False:
            self.report("E-TYPE-RETURN", f.body, ret, body_t)

    # ---------------------------------------------------------- expressions

    def expr(self, e, env: dict[str, Ty]) -> Ty:
        self._event("visit", e)
        if isinstance(e, IntLit):
            return self.build(INT, e)
        if isinstance(e, BoolLit):
            return self.build(BOOL, e)
        if isinstance(e, UnitLit):
            return self.build(Ty("Unit"), e)
        if isinstance(e, Var):
            return env[e.name]
        if isinstance(e, ListLit):
            elem = ty_of(e.element_type)
            item_ts = [self.expr(i, env) for i in e.items]
            ok = True
            for item, t in zip(e.items, item_ts):
                r = self.equal(t, elem, item)
                if r is False:
                    self.report("E-TYPE-LIST-ITEM", item, elem, t)
                if r is not True:
                    ok = False
            return self.build(Ty("List", elem), e) if ok else ERROR
        if isinstance(e, NoneE):
            return self.build(Ty("Option", ty_of(e.element_type)), e)
        if isinstance(e, SomeE):
            t = self.expr(e.value, env)
            return ERROR if t.is_error else self.build(Ty("Option", t), e)
        if isinstance(e, PairE):
            a = self.expr(e.left, env)
            b = self.expr(e.right, env)
            return ERROR if (a.is_error or b.is_error) else self.build(Ty("Pair", a, b), e)
        if isinstance(e, Let):
            vt = self.expr(e.value, env)
            bt = self.expr(e.body, {**env, e.name: vt})
            return ERROR if (vt.is_error or bt.is_error) else bt
        if isinstance(e, If):
            c = self.expr(e.condition, env)
            t = self.expr(e.then, env)
            f = self.expr(e.else_, env)
            ok = not (c.is_error or t.is_error or f.is_error)
            if self.equal(c, BOOL, e.condition) is False:
                self.report("E-TYPE-IF-CONDITION", e.condition, BOOL, c)
                ok = False
            if self.equal(t, f, e.else_) is False:
                self.report("E-TYPE-IF-BRANCH", e.else_, t, f)
                ok = False
            return t if ok else ERROR
        if isinstance(e, Fold):
            xt = self.expr(e.list, env)
            it = self.expr(e.init, env)
            ok = not (xt.is_error or it.is_error)
            h = self.head(xt, "List", e.list)
            if h is True:
                item_t = xt.args[0]
            else:
                item_t = ERROR
                if h is False:
                    self.report("E-TYPE-FOLD-LIST", e.list, "List", xt)
                    ok = False
            bt = self.expr(e.body, {**env, e.acc: it, e.item: item_t})
            if bt.is_error:
                ok = False
            if self.equal(bt, it, e.body) is False:
                self.report("E-TYPE-FOLD-BODY", e.body, it, bt)
                ok = False
            return it if ok else ERROR
        if isinstance(e, Call):
            return self.call(e, env)
        raise TypeError(f"unknown expression node {e!r}")

    def call(self, e: Call, env) -> Ty:
        if e.builtin:
            arity = BUILTIN_ARITY[e.callee]
            params = None
        else:
            params = [ty_of(p.type) for p in self.fns[e.callee].params]
            arity = len(params)
        if len(e.args) != arity:
            self.report("E-ARITY-BUILTIN" if e.builtin else "E-ARITY-USER", e,
                        f"{arity} arguments", f"{len(e.args)} arguments")
            for a in e.args:
                self.expr(a, env)
            return ERROR
        ts = [self.expr(a, env) for a in e.args]
        ok = not any(t.is_error for t in ts)

        def need(r, code, node, expected, actual):
            nonlocal ok
            if r is False:
                self.report(code, node, expected, actual)
                ok = False

        if not e.builtin:
            for a, t, p in zip(e.args, ts, params):
                need(self.equal(t, p, a), "E-TYPE-ARG", a, p, t)
            return ty_of(self.fns[e.callee].return_type) if ok else ERROR
        name = e.callee
        a = e.args
        if name in ("add", "sub", "mul", "lt", "le", "mod"):
            need(self.equal(ts[0], INT, a[0]), "E-TYPE-ARG", a[0], INT, ts[0])
            need(self.equal(ts[1], INT, a[1]), "E-TYPE-ARG", a[1], INT, ts[1])
            if not ok:
                return ERROR
            if name in ("lt", "le"):
                return self.build(BOOL, e)
            if name == "mod":
                inner = self.build(INT, e)
                return self.build(Ty("Option", inner), e)
            return self.build(INT, e)
        if name == "neg":
            need(self.equal(ts[0], INT, a[0]), "E-TYPE-ARG", a[0], INT, ts[0])
            return self.build(INT, e) if ok else ERROR
        if name == "eq":
            need(self.equal(ts[0], ts[1], a[1]), "E-TYPE-EQ-OPERANDS", a[1], ts[0], ts[1])
            return self.build(BOOL, e) if ok else ERROR
        if name in ("fst", "snd"):
            code = "E-TYPE-FST-ARG" if name == "fst" else "E-TYPE-SND-ARG"
            need(self.head(ts[0], "Pair", a[0]), code, a[0], "Pair", ts[0])
            return ts[0].args[0 if name == "fst" else 1] if ok else ERROR
        if name == "cons":
            h = self.head(ts[1], "List", a[1])
            need(h, "E-TYPE-EXPECTED-LIST", a[1], "List", ts[1])
            if h is True:
                need(self.equal(ts[0], ts[1].args[0], a[0]), "E-TYPE-ARG", a[0], ts[1].args[0],
                     ts[0])
            return ts[1] if ok else ERROR
        if name == "concat":
            h1 = self.head(ts[0], "List", a[0])
            need(h1, "E-TYPE-EXPECTED-LIST", a[0], "List", ts[0])
            h2 = self.head(ts[1], "List", a[1])
            need(h2, "E-TYPE-EXPECTED-LIST", a[1], "List", ts[1])
            if h1 is True and h2 is True:
                need(self.equal(ts[0].args[0], ts[1].args[0], a[1]), "E-TYPE-ARG", a[1], ts[0],
                     ts[1])
            return ts[0] if ok else ERROR
        if name in ("reverse", "length"):
            need(self.head(ts[0], "List", a[0]), "E-TYPE-EXPECTED-LIST", a[0], "List", ts[0])
            if not ok:
                return ERROR
            return ts[0] if name == "reverse" else self.build(INT, e)
        raise TypeError(f"unknown builtin {name}")


# ======================================================================= driver


@dataclass
class TypedProgram:
    """受理済みプログラム（不透明値）。"""

    program: Program
    functions: dict[str, FnDecl]
    entry: str
    input_type: Ty
    output_type: Ty
    rank: dict[str, int]
    spec_version: str | None = None


@dataclass
class CheckOutcome:
    diagnostics: list[Diagnostic] = field(default_factory=list)
    typed: TypedProgram | None = None
    work: WorkCounter | None = None


def check_program(prog: Program, eof: int, profile: StaticProfile) -> CheckOutcome:
    out = CheckOutcome()
    fns = [d for d in prog.declarations if isinstance(d, FnDecl)]
    entries = [d for d in prog.declarations if isinstance(d, EntryDecl)]

    # name
    name_diags = check_names(prog, fns, entries)
    if name_diags:
        out.diagnostics = name_diags
        return out
    fn_map = {f.name: f for f in fns}

    # call-graph（循環があっても typecheck と entry は実行する）
    cycle_diags, rank, edges = check_call_graph(fns)
    out.diagnostics.extend(cycle_diags)

    # typecheck + semantic-limits
    tc = TypeChecker(fn_map, profile)
    out.work = tc.work
    try:
        for f in fns:
            tc.check_function(f)
    except SemanticCutoff as c:
        out.diagnostics.extend(tc.diags)
        out.diagnostics.append(c.diag)
        return out
    out.diagnostics.extend(tc.diags)

    # entry
    entry_ok = False
    if not entries:
        out.diagnostics.append(error("entry", "E-ENTRY-MISSING", (eof, eof)))
    elif len(entries) >= 2:
        d = entries[1]
        out.diagnostics.append(error("entry", "E-ENTRY-DUPLICATE", d.span, None, None, d.index))
    else:
        d = entries[0]
        n = len(fn_map[d.name].params)
        if n != 1:
            out.diagnostics.append(error("entry", "E-ENTRY-ARITY", d.name_span, "1 parameter",
                                         f"{n} parameters", d.index))
        else:
            entry_ok = True

    # warnings
    if entry_ok:
        live = {entries[0].name}
        todo = [entries[0].name]
        while todo:
            f = todo.pop()
            for c in edges[f]:
                if c.callee not in live:
                    live.add(c.callee)
                    todo.append(c.callee)
        for f in fns:
            if f.name not in live:
                out.diagnostics.append(warning("warnings", "W-UNUSED-FUNCTION", f.name_span,
                                               f.index))

    if not any(d.severity == "error" for d in out.diagnostics):
        ef = fn_map[entries[0].name]
        out.typed = TypedProgram(prog, fn_map, ef.name, ty_of(ef.params[0].type),
                                 ty_of(ef.return_type), rank or {})
    return out
