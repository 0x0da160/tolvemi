"""表面 AST と意味論上の型（設計書 §3、§4.1、§19.2）。

AST node は span（UTF-8 bytes の半開区間）と論理 node index（前順 Admission index）
を持つが、構造的等価性の比較対象には含めない。
"""

from __future__ import annotations

from dataclasses import dataclass, field

KEYWORDS = frozenset(
    """fn entry Int Bool Unit List Option Pair true false unit list some none pair
    let in if fold add sub mul neg lt le eq mod fst snd cons concat reverse length""".split()
)

BUILTIN_ARITY = {
    "add": 2, "sub": 2, "mul": 2, "neg": 1, "lt": 2, "le": 2, "eq": 2, "mod": 2,
    "fst": 1, "snd": 1, "cons": 2, "concat": 2, "reverse": 1, "length": 1,
}
BUILTINS = frozenset(BUILTIN_ARITY)

TYPE_KEYWORDS = ("Int", "Bool", "Unit", "List", "Option", "Pair")


def _meta():
    return field(default=(0, 0), compare=False, repr=False)


def _idx():
    return field(default=0, compare=False, repr=False)


# ---------------------------------------------------------------- 型（構文）


@dataclass(eq=True)
class TypeNode:
    tag: str  # Int / Bool / Unit / List / Option / Pair
    args: tuple = ()
    span: tuple = _meta()
    index: int = _idx()


# ---------------------------------------------------------------- 式


@dataclass(eq=True)
class IntLit:
    value: int
    span: tuple = _meta()
    index: int = _idx()


@dataclass(eq=True)
class BoolLit:
    value: bool
    span: tuple = _meta()
    index: int = _idx()


@dataclass(eq=True)
class UnitLit:
    span: tuple = _meta()
    index: int = _idx()


@dataclass(eq=True)
class Var:
    name: str
    span: tuple = _meta()
    index: int = _idx()


@dataclass(eq=True)
class ListLit:
    element_type: TypeNode
    items: tuple
    span: tuple = _meta()
    index: int = _idx()


@dataclass(eq=True)
class SomeE:
    value: object
    span: tuple = _meta()
    index: int = _idx()


@dataclass(eq=True)
class NoneE:
    element_type: TypeNode
    span: tuple = _meta()
    index: int = _idx()


@dataclass(eq=True)
class PairE:
    left: object
    right: object
    span: tuple = _meta()
    index: int = _idx()


@dataclass(eq=True)
class Call:
    callee: str
    args: tuple
    builtin: bool
    callee_span: tuple = _meta()
    span: tuple = _meta()
    index: int = _idx()


@dataclass(eq=True)
class Let:
    name: str
    value: object
    body: object
    name_span: tuple = _meta()
    span: tuple = _meta()
    index: int = _idx()


@dataclass(eq=True)
class If:
    condition: object
    then: object
    else_: object
    span: tuple = _meta()
    index: int = _idx()


@dataclass(eq=True)
class Fold:
    list: object
    init: object
    acc: str
    item: str
    body: object
    acc_span: tuple = _meta()
    item_span: tuple = _meta()
    span: tuple = _meta()
    index: int = _idx()


# ---------------------------------------------------------------- 宣言


@dataclass(eq=True)
class Param:
    name: str
    type: TypeNode
    name_span: tuple = _meta()
    span: tuple = _meta()
    index: int = _idx()


@dataclass(eq=True)
class FnDecl:
    name: str
    params: tuple
    return_type: TypeNode
    body: object
    name_span: tuple = _meta()
    span: tuple = _meta()
    index: int = _idx()


@dataclass(eq=True)
class EntryDecl:
    name: str
    name_span: tuple = _meta()
    span: tuple = _meta()
    index: int = _idx()


@dataclass(eq=True)
class Program:
    declarations: tuple
    span: tuple = _meta()
    index: int = _idx()


def children(e):
    """式の子を左から右の順で返す。"""
    if isinstance(e, ListLit):
        return list(e.items)
    if isinstance(e, SomeE):
        return [e.value]
    if isinstance(e, PairE):
        return [e.left, e.right]
    if isinstance(e, Call):
        return list(e.args)
    if isinstance(e, Let):
        return [e.value, e.body]
    if isinstance(e, If):
        return [e.condition, e.then, e.else_]
    if isinstance(e, Fold):
        return [e.list, e.init, e.body]
    return []


# ---------------------------------------------------------------- 意味論上の型


class Ty:
    """単相型。ErrorType は tag "Error"（深さ0、ユーザー AST と値には現れない）。"""

    __slots__ = ("tag", "args", "depth", "_hash")

    def __init__(self, tag: str, *args: "Ty"):
        self.tag = tag
        self.args = args
        if tag == "Error":
            self.depth = 0
        else:
            self.depth = 1 + max((a.depth for a in args), default=0)
        self._hash = hash((tag, args))

    def __eq__(self, other):
        return isinstance(other, Ty) and self.tag == other.tag and self.args == other.args

    def __hash__(self):
        return self._hash

    @property
    def is_error(self) -> bool:
        return self.tag == "Error"

    def __str__(self) -> str:
        if not self.args:
            return self.tag
        return f"{self.tag}<{', '.join(str(a) for a in self.args)}>"

    __repr__ = __str__


INT = Ty("Int")
BOOL = Ty("Bool")
UNIT = Ty("Unit")
ERROR = Ty("Error")


def ty_of(node: TypeNode) -> Ty:
    return Ty(node.tag, *(ty_of(a) for a in node.args))
