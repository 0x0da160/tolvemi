"""正準フォーマッタ（設計書 §4.3）と AST codec の encoder（§19.4）。"""

from __future__ import annotations

import json

from .syntax import (
    BoolLit, Call, EntryDecl, FnDecl, Fold, If, IntLit, Let, ListLit, NoneE, PairE, Program,
    SomeE, TypeNode, UnitLit, Var,
)

FORMATTER_VERSION = "tolvemi-format-v1"


def format_type(t: TypeNode) -> str:
    if not t.args:
        return t.tag
    return f"{t.tag}<{', '.join(format_type(a) for a in t.args)}>"


def format_expr(e) -> str:
    if isinstance(e, IntLit):
        return str(e.value)
    if isinstance(e, BoolLit):
        return "true" if e.value else "false"
    if isinstance(e, UnitLit):
        return "unit"
    if isinstance(e, Var):
        return e.name
    if isinstance(e, ListLit):
        return f"list[{format_type(e.element_type)}]({', '.join(format_expr(i) for i in e.items)})"
    if isinstance(e, SomeE):
        return f"some({format_expr(e.value)})"
    if isinstance(e, NoneE):
        return f"none[{format_type(e.element_type)}]"
    if isinstance(e, PairE):
        return f"pair({format_expr(e.left)}, {format_expr(e.right)})"
    if isinstance(e, Call):
        return f"{e.callee}({', '.join(format_expr(a) for a in e.args)})"
    if isinstance(e, Let):
        return f"let {e.name} = {format_expr(e.value)} in {format_expr(e.body)}"
    if isinstance(e, If):
        return (f"if({format_expr(e.condition)}, {format_expr(e.then)}, "
                f"{format_expr(e.else_)})")
    if isinstance(e, Fold):
        return (f"fold({format_expr(e.list)}, {format_expr(e.init)}, "
                f"|{e.acc}, {e.item}| {format_expr(e.body)})")
    raise TypeError(f"unknown expression node {e!r}")


def format_program(prog: Program) -> str:
    lines = []
    for d in prog.declarations:
        if isinstance(d, FnDecl):
            params = ", ".join(f"{p.name}: {format_type(p.type)}" for p in d.params)
            lines.append(f"fn {d.name}({params}) -> {format_type(d.return_type)} = "
                         f"{format_expr(d.body)}")
        else:
            lines.append(f"entry {d.name}")
    return "".join(line + "\n" for line in lines)


# ---------------------------------------------------------------- AST encoder


def _type_json(t: TypeNode) -> dict:
    tag = t.tag.lower()
    if t.tag in ("List", "Option"):
        return {"tag": tag, "element": _type_json(t.args[0])}
    if t.tag == "Pair":
        return {"tag": tag, "left": _type_json(t.args[0]), "right": _type_json(t.args[1])}
    return {"tag": tag}


def _expr_json(e) -> dict:
    if isinstance(e, IntLit):
        return {"tag": "int", "value": str(e.value)}
    if isinstance(e, BoolLit):
        return {"tag": "bool", "value": e.value}
    if isinstance(e, UnitLit):
        return {"tag": "unit"}
    if isinstance(e, Var):
        return {"tag": "var", "name": e.name}
    if isinstance(e, ListLit):
        return {"tag": "list", "element_type": _type_json(e.element_type),
                "items": [_expr_json(i) for i in e.items]}
    if isinstance(e, SomeE):
        return {"tag": "some", "value": _expr_json(e.value)}
    if isinstance(e, NoneE):
        return {"tag": "none", "element_type": _type_json(e.element_type)}
    if isinstance(e, PairE):
        return {"tag": "pair", "left": _expr_json(e.left), "right": _expr_json(e.right)}
    if isinstance(e, Call):
        return {"tag": "call", "callee": e.callee, "args": [_expr_json(a) for a in e.args]}
    if isinstance(e, Let):
        return {"tag": "let", "name": e.name, "value": _expr_json(e.value),
                "body": _expr_json(e.body)}
    if isinstance(e, If):
        return {"tag": "if", "condition": _expr_json(e.condition), "then": _expr_json(e.then),
                "else": _expr_json(e.else_)}
    if isinstance(e, Fold):
        return {"tag": "fold", "list": _expr_json(e.list), "init": _expr_json(e.init),
                "acc": e.acc, "item": e.item, "body": _expr_json(e.body)}
    raise TypeError(f"unknown expression node {e!r}")


def encode_ast(prog: Program) -> str:
    decls = []
    for d in prog.declarations:
        if isinstance(d, FnDecl):
            decls.append({
                "tag": "fn",
                "name": d.name,
                "params": [{"name": p.name, "type": _type_json(p.type)} for p in d.params],
                "return_type": _type_json(d.return_type),
                "body": _expr_json(d.body),
            })
        elif isinstance(d, EntryDecl):
            decls.append({"tag": "entry", "name": d.name})
    return json.dumps({"codec": "ast_codec_v1", "declarations": decls},
                      ensure_ascii=False, separators=(",", ":"))
