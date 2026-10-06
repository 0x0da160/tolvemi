"""参照評価器（設計書 §7、§8.4、§18.3）。

左から右の call-by-value。execution-v1 の参照 step・AllocatedNodeCount・整数 bit 長を
規範どおりに計数し、上限超過は ResourceExhausted として返す。
"""

from __future__ import annotations

from dataclasses import dataclass

from .checker import TypedProgram
from .profiles import ExecutionProfile, HostPolicy
from .syntax import (
    BoolLit, Call, Fold, If, IntLit, Let, ListLit, NoneE, PairE, SomeE, UnitLit, Var,
)
from .values import NIL, NONE_V, UNIT_V, Cons, Decoded, PairV, SomeV, encode_value


# ---------------------------------------------------------------- RunResult


@dataclass
class Completed:
    output: str  # 正準 JSON
    steps: int
    allocated_nodes: int


@dataclass
class ResourceExhausted:
    kind: str  # Steps / AllocatedNodes / IntegerBits / OutputBytes
    observed: int
    limit: int


@dataclass
class HostAborted:
    reason: str


@dataclass
class InternalFault:
    code: str


class _Exhausted(Exception):
    def __init__(self, kind: str, observed: int, limit: int):
        self.result = ResourceExhausted(kind, observed, limit)


class _HostAbort(Exception):
    def __init__(self, reason: str):
        self.reason = reason


def bits(n: int) -> int:
    return abs(n).bit_length()


class Machine:
    def __init__(self, prog: TypedProgram, profile: ExecutionProfile, host: HostPolicy):
        self.prog = prog
        self.p = profile
        self.host = host
        self.steps = 0
        self.alloc = 0
        self.depth = 0

    # ---------------------------------------------------------- events

    def step(self) -> None:
        if self.steps + 1 > self.p.steps:
            raise _Exhausted("Steps", self.steps + 1, self.p.steps)
        self.steps += 1

    def allocate(self, int_value: int | None = None) -> None:
        """新規整数／cons／pair／some node の確保（step → bit → 割当数の順に判定）。"""
        if self.steps + 1 > self.p.steps:
            raise _Exhausted("Steps", self.steps + 1, self.p.steps)
        if int_value is not None:
            b = bits(int_value)
            if b > self.p.integer_bits:
                raise _Exhausted("IntegerBits", b, self.p.integer_bits)
        if self.alloc + 1 > self.p.allocated_nodes:
            raise _Exhausted("AllocatedNodes", self.alloc + 1, self.p.allocated_nodes)
        self.steps += 1
        self.alloc += 1

    # ---------------------------------------------------------- run

    def run_entry(self, arg):
        f = self.prog.functions[self.prog.entry]
        self.step()  # entry 関数本体への入場
        return self.eval(f.body, {f.params[0].name: arg})

    def eval(self, e, env: dict):
        self.step()  # 式 node の評価開始
        self.depth += 1
        if self.depth > self.host.max_eval_depth:
            raise _HostAbort("eval-depth")
        try:
            return self._eval(e, env)
        finally:
            self.depth -= 1

    def _eval(self, e, env: dict):
        if isinstance(e, Var):
            return env[e.name]
        if isinstance(e, IntLit):
            self.allocate(e.value)
            return e.value
        if isinstance(e, BoolLit):
            return e.value
        if isinstance(e, UnitLit):
            return UNIT_V
        if isinstance(e, NoneE):
            return NONE_V
        if isinstance(e, Call):
            args = [self.eval(a, env) for a in e.args]
            if e.builtin:
                self.step()  # 組込みの適用開始
                return self.builtin(e.callee, args)
            f = self.prog.functions[e.callee]
            self.step()  # ユーザー関数本体への入場
            return self.eval(f.body, {p.name: v for p, v in zip(f.params, args)})
        if isinstance(e, Let):
            v = self.eval(e.value, env)
            return self.eval(e.body, {**env, e.name: v})
        if isinstance(e, If):
            c = self.eval(e.condition, env)
            return self.eval(e.then if c else e.else_, env)
        if isinstance(e, Fold):
            cur = self.eval(e.list, env)
            acc = self.eval(e.init, env)
            while True:
                self.step()  # spine cursor の読取り
                if cur is NIL:
                    return acc
                acc = self.eval(e.body, {**env, e.acc: acc, e.item: cur.head})
                cur = cur.tail
        if isinstance(e, ListLit):
            refs = []
            for item in e.items:
                refs.append(self.eval(item, env))
                self.step()  # 一時要素参照の push
            out = NIL
            for v in reversed(refs):
                self.step()  # pop
                self.allocate()
                out = Cons(v, out)
            return out
        if isinstance(e, SomeE):
            v = self.eval(e.value, env)
            self.allocate()
            return SomeV(v)
        if isinstance(e, PairE):
            a = self.eval(e.left, env)
            b = self.eval(e.right, env)
            self.allocate()
            return PairV(a, b)
        raise TypeError(f"unknown expression node {e!r}")

    def builtin(self, name: str, a: list):
        if name in ("add", "sub", "mul"):
            r = a[0] + a[1] if name == "add" else a[0] - a[1] if name == "sub" else a[0] * a[1]
            self.allocate(r)
            return r
        if name == "neg":
            r = -a[0]
            self.allocate(r)
            return r
        if name == "lt":
            return a[0] < a[1]
        if name == "le":
            return a[0] <= a[1]
        if name == "eq":
            return self.equal(a[0], a[1])
        if name == "fst":
            return a[0].left
        if name == "snd":
            return a[0].right
        if name == "mod":
            x, y = a
            if y <= 0:
                return NONE_V
            r = x % y
            self.allocate(r)
            self.allocate()
            return SomeV(r)
        if name == "cons":
            self.allocate()
            return Cons(a[0], a[1])
        if name == "concat":
            refs = []
            cur = a[0]
            while True:
                self.step()  # セル読取り
                if cur is NIL:
                    break
                self.step()  # push
                refs.append(cur.head)
                cur = cur.tail
            out = a[1]
            for v in reversed(refs):
                self.step()  # pop
                self.allocate()
                out = Cons(v, out)
            return out
        if name == "reverse":
            out = NIL
            cur = a[0]
            while True:
                self.step()
                if cur is NIL:
                    return out
                self.allocate()
                out = Cons(cur.head, out)
                cur = cur.tail
        if name == "length":
            n = 0
            cur = a[0]
            while True:
                self.step()
                if cur is NIL:
                    break
                n += 1
                cur = cur.tail
            self.allocate(n)
            return n
        raise TypeError(f"unknown builtin {name}")

    def equal(self, x, y) -> bool:
        """構造的等値。共有 pointer 一致による短絡はしない。"""
        todo = [("v", x, y)]
        while todo:
            kind, a, b = todo.pop()
            self.step()
            if kind == "s":  # list spine セル／nil の対
                if a is NIL or b is NIL:
                    if not (a is NIL and b is NIL):
                        return False
                    continue
                todo.append(("s", a.tail, b.tail))
                todo.append(("v", a.head, b.head))
                continue
            if isinstance(a, bool) or isinstance(b, bool):
                if a is not b:
                    return False
            elif isinstance(a, int):
                if a != b:
                    return False
            elif a is UNIT_V:
                pass
            elif a is NONE_V or b is NONE_V:
                if a is not b:
                    return False
            elif isinstance(a, SomeV):
                todo.append(("v", a.value, b.value))
            elif isinstance(a, PairV):
                todo.append(("v", a.right, b.right))
                todo.append(("v", a.left, b.left))
            else:  # list の値根
                todo.append(("s", a, b))
        return True


def _check_input_bits(v, limit: int):
    stack = [v]
    while stack:
        x = stack.pop()
        if isinstance(x, bool):
            continue
        if isinstance(x, int):
            if bits(x) > limit:
                return bits(x)
        elif isinstance(x, SomeV):
            stack.append(x.value)
        elif isinstance(x, PairV):
            stack.append(x.right)
            stack.append(x.left)
        elif isinstance(x, Cons):
            stack.append(x.tail)
            stack.append(x.head)
    return None


def run(prog: TypedProgram, decoded: Decoded, profile: ExecutionProfile = ExecutionProfile(),
        host: HostPolicy = HostPolicy()):
    if not isinstance(prog, TypedProgram) or not isinstance(decoded, Decoded):
        raise TypeError("run は TypedProgram と Decoded を受け取る（API misuse）")
    if decoded.type != prog.input_type:
        raise TypeError(f"入力型 {decoded.type} が entry の入力型 {prog.input_type} と一致しない")
    too_big = _check_input_bits(decoded.value, profile.integer_bits)
    if too_big is not None:
        return ResourceExhausted("IntegerBits", too_big, profile.integer_bits)
    m = Machine(prog, profile, host)
    try:
        value = m.run_entry(decoded.value)
    except _Exhausted as x:
        return x.result
    except _HostAbort as h:
        return HostAborted(h.reason)
    except (RecursionError, MemoryError) as exc:
        return HostAborted(type(exc).__name__)
    out = encode_value(value)
    size = len(out.encode("utf-8"))
    if size > profile.output_bytes:
        return ResourceExhausted("OutputBytes", profile.output_bytes + 1, profile.output_bytes)
    return Completed(out, m.steps, m.alloc)
