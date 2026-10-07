"""LPTL の型と値を、評価用の各表現（plain JSON、LPTL のリテラル、Python の値）に写す補助。

plain JSON は tlvm の `--plain` と同じ対応（crates/tlvm/src/plain.rs）。評価タスクでは
`Option<Unit>` や `Option<Option<T>>` を使わないので、`{"some": v}` の形は扱わない。
"""

from __future__ import annotations

import random
from typing import Any

Type = tuple


def parse_type(s: str) -> Type:
    toks = s.replace("<", " < ").replace(">", " > ").replace(",", " , ").split()
    pos = 0

    def ty() -> Type:
        nonlocal pos
        name = toks[pos]
        pos += 1
        if name in ("Int", "Bool", "Unit"):
            return (name,)
        if name in ("List", "Option"):
            expect("<")
            a = ty()
            expect(">")
            return (name, a)
        if name == "Pair":
            expect("<")
            a = ty()
            expect(",")
            b = ty()
            expect(">")
            return (name, a, b)
        raise ValueError(f"unknown type {name!r} in {s!r}")

    def expect(t: str) -> None:
        nonlocal pos
        if toks[pos] != t:
            raise ValueError(f"expected {t!r} in {s!r}")
        pos += 1

    t = ty()
    if pos != len(toks):
        raise ValueError(f"trailing tokens in {s!r}")
    return t


def show_type(t: Type) -> str:
    if len(t) == 1:
        return t[0]
    return f"{t[0]}<{', '.join(show_type(a) for a in t[1:])}>"


def _check_nullable(t: Type) -> None:
    if t[0] == "Option" and t[1][0] in ("Unit", "Option"):
        raise ValueError("Option<Unit> / Option<Option<T>> are not used in eval tasks")


def lptl_literal(v: Any, t: Type) -> str:
    """plain JSON の値を LPTL の値リテラル（ソースに書ける式）にする。"""
    k = t[0]
    if k == "Int":
        return str(int(v))
    if k == "Bool":
        return "true" if v else "false"
    if k == "Unit":
        return "unit"
    if k == "List":
        return f"list<{show_type(t[1])}>({', '.join(lptl_literal(x, t[1]) for x in v)})"
    if k == "Option":
        _check_nullable(t)
        return f"none<{show_type(t[1])}>()" if v is None else f"some({lptl_literal(v, t[1])})"
    if k == "Pair":
        return f"pair({lptl_literal(v[0], t[1])}, {lptl_literal(v[1], t[2])})"
    raise ValueError(t)


def to_python(v: Any, t: Type) -> Any:
    """plain JSON の値を Python の値にする（Pair は tuple、Option は None か中身）。"""
    k = t[0]
    if k == "List":
        return [to_python(x, t[1]) for x in v]
    if k == "Pair":
        return (to_python(v[0], t[1]), to_python(v[1], t[2]))
    if k == "Option":
        _check_nullable(t)
        return None if v is None else to_python(v, t[1])
    if k == "Unit":
        return None
    return v


def python_literal(v: Any, t: Type) -> str:
    return repr(to_python(v, t))


def from_python(v: Any, t: Type) -> Any:
    """Python の値を型 t の plain JSON にする。型が合わなければ TypeError。"""
    k = t[0]
    if k == "Int":
        if isinstance(v, bool) or not isinstance(v, int):
            raise TypeError(f"expected int, got {type(v).__name__}")
        return v
    if k == "Bool":
        if not isinstance(v, bool):
            raise TypeError(f"expected bool, got {type(v).__name__}")
        return v
    if k == "Unit":
        if v is not None:
            raise TypeError(f"expected None, got {type(v).__name__}")
        return None
    if k == "List":
        if not isinstance(v, (list, tuple)):
            raise TypeError(f"expected list, got {type(v).__name__}")
        return [from_python(x, t[1]) for x in v]
    if k == "Pair":
        if not isinstance(v, (list, tuple)) or len(v) != 2:
            raise TypeError("expected a 2-tuple")
        return [from_python(v[0], t[1]), from_python(v[1], t[2])]
    if k == "Option":
        _check_nullable(t)
        return None if v is None else from_python(v, t[1])
    raise ValueError(t)


class Gen:
    """型から小さな乱数値を作る。整数は主に -20..20、たまに大きな値。"""

    def int(self, rng: random.Random) -> int:
        r = rng.random()
        if r < 0.05:
            return rng.choice([-1, 1]) * rng.randint(10**6, 10**12)
        return rng.randint(-20, 20)

    def value(self, t: Type, rng: random.Random, depth: int = 0) -> Any:
        k = t[0]
        if k == "Int":
            return self.int(rng)
        if k == "Bool":
            return rng.random() < 0.5
        if k == "Unit":
            return None
        if k == "List":
            n = rng.choice([0, 1, 2, 3, 4, 5, 6, 8]) if depth < 2 else rng.randint(0, 3)
            return [self.value(t[1], rng, depth + 1) for _ in range(n)]
        if k == "Pair":
            return (self.value(t[1], rng, depth + 1), self.value(t[2], rng, depth + 1))
        if k == "Option":
            _check_nullable(t)
            return None if rng.random() < 0.3 else self.value(t[1], rng, depth + 1)
        raise ValueError(t)
