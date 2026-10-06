"""tlvm コマンド。

  tlvm check FILE           静的検査（.tlvm source、または --ast で AST JSON）
  tlvm run FILE INPUT_JSON  検査・入力 decode・実行（INPUT_JSON は文字列、@path、- は stdin）
  tlvm fmt FILE             正準ソースを出力
  tlvm ast FILE             ast_codec_v1 JSON を出力

診断は一行一 JSON object で stderr へ、結果は stdout へ出す。
"""

from __future__ import annotations

import argparse
import json
import sys

from . import api
from .formatter import encode_ast, format_program
from .syntax import Program
from .values import Decoded


def _read(path: str) -> bytes:
    if path == "-":
        return sys.stdin.buffer.read()
    with open(path, "rb") as f:
        return f.read()


def _emit_diags(diags) -> None:
    for d in diags:
        print(d.to_json(), file=sys.stderr)


def _compile(path: str, is_ast: bool):
    data = _read(path)
    if is_ast or path.endswith(".json"):
        return api.compile_ast(data)
    return api.compile(data)


def _report_compile(result) -> bool:
    if isinstance(result, api.Accepted):
        _emit_diags(result.warnings)
        return True
    if isinstance(result, api.Rejected):
        _emit_diags(result.errors)
        _emit_diags(result.warnings)
    elif hasattr(result, "diagnostics"):
        _emit_diags(result.diagnostics)
    else:
        print(json.dumps({"result": type(result).__name__, "reason": result.reason}),
              file=sys.stderr)
    return False


def cmd_check(args) -> int:
    result = _compile(args.file, args.ast)
    ok = _report_compile(result)
    if ok:
        p = result.program
        print(json.dumps({"result": "Accepted", "entry": p.entry, "input_type": str(p.input_type),
                          "output_type": str(p.output_type)}, ensure_ascii=False))
    return 0 if ok else 1


def cmd_run(args) -> int:
    result = _compile(args.file, args.ast)
    if not _report_compile(result):
        return 1
    prog = result.program
    if args.input == "-":
        data = sys.stdin.buffer.read()
    elif args.input.startswith("@"):
        data = _read(args.input[1:])
    else:
        data = args.input.encode("utf-8")
    decoded = api.decode_input(prog.input_type, data)
    if not isinstance(decoded, Decoded):
        if hasattr(decoded, "diagnostics"):
            _emit_diags(decoded.diagnostics)
        else:
            print(json.dumps({"result": "InputBoundaryFailure", "reason": "InvalidUtf8"}),
                  file=sys.stderr)
        return 1
    out = api.run(prog, decoded)
    if isinstance(out, api.Completed):
        print(out.output)
        if args.stats:
            print(json.dumps({"steps": out.steps, "allocated_nodes": out.allocated_nodes}),
                  file=sys.stderr)
        return 0
    print(json.dumps({"result": type(out).__name__, **out.__dict__}), file=sys.stderr)
    return 2


def _parse_only(path: str):
    data = _read(path)
    if path.endswith(".json"):
        root = api.ast_codec.transport(data, api.AstTransportProfile(), api.StaticProfile())
        if not isinstance(root, api.ast_codec.JNode):
            return root
        return api.ast_codec.build(root, api.StaticProfile())
    return api.parse_source(data)


def cmd_fmt(args) -> int:
    prog = _parse_only(args.file)
    if not isinstance(prog, Program):
        _report_compile(prog)
        return 1
    sys.stdout.write(format_program(prog))
    return 0


def cmd_ast(args) -> int:
    prog = _parse_only(args.file)
    if not isinstance(prog, Program):
        _report_compile(prog)
        return 1
    print(encode_ast(prog))
    return 0


def main(argv=None) -> int:
    ap = argparse.ArgumentParser(prog="tlvm", description="Tolvemi (LPTL v1) reference toolchain")
    sub = ap.add_subparsers(dest="cmd", required=True)
    p = sub.add_parser("check", help="静的検査")
    p.add_argument("file")
    p.add_argument("--ast", action="store_true", help="入力を ast_codec_v1 JSON として扱う")
    p.set_defaults(fn=cmd_check)
    p = sub.add_parser("run", help="検査して実行")
    p.add_argument("file")
    p.add_argument("input", help="入力値 JSON（@path でファイル、- で stdin）")
    p.add_argument("--ast", action="store_true")
    p.add_argument("--stats", action="store_true", help="参照 step と割当数を stderr に出す")
    p.set_defaults(fn=cmd_run)
    p = sub.add_parser("fmt", help="正準ソースを出力")
    p.add_argument("file")
    p.set_defaults(fn=cmd_fmt)
    p = sub.add_parser("ast", help="ast_codec_v1 JSON を出力")
    p.add_argument("file")
    p.set_defaults(fn=cmd_ast)
    args = ap.parse_args(argv)
    return args.fn(args)


if __name__ == "__main__":
    sys.exit(main())
