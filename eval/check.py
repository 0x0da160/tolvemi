"""評価セットの整合性を検査する。

- 各タスクの参照解（reference.tlvm と reference.py）が公開例と隠しテストを全て通ること
- SKILL.md と SKILL-nolet.md の ```tlvm ブロックが全て tlvm check を通ること。SKILL-nolet.md のブロックは let を含まないこと
- ast_output.md（AST の arm の出力形式）の例の JSON が、同じ節の ```tlvm の例の tlvm ast と一致し、compile_ast で受理されること
- manifest.json（SKILL.md、arm ごとのプロンプトの部品、各タスクのファイルの SHA-256）が最新であること（--write で更新）

参照解が let を使う課題の数（lptl-nolet と比べる共通課題から外れる数）も表示する。

usage: python3 eval/check.py [--write]
"""

from __future__ import annotations

import argparse
import hashlib
import json
import re
import sys
from pathlib import Path

from runner import find_let, run_ast, run_lptl, run_python
from tasks_lib import EVAL, load_tasks, sha256_file

SKILL = EVAL / "SKILL.md"
SKILL_NOLET = EVAL / "SKILL-nolet.md"
AST_OUTPUT = EVAL / "ast_output.md"
PROMPT_FILES = (SKILL_NOLET, AST_OUTPUT)  # SKILL.md 以外の、arm の system を作る部品
MANIFEST = EVAL / "manifest.json"
TASK_FILES = ("task.json", "hidden.json", "reference.tlvm", "reference.py")
AST_PLACEHOLDERS = ("{{AST_ANSWER}}", "{{AST_CODEC_V1_SCHEMA}}")


def skill_blocks(path: Path = SKILL) -> list[str]:
    return re.findall(r"```tlvm\n(.*?)```", path.read_text(encoding="utf-8"), re.S)


def check_skill(path: Path, nolet: bool = False) -> bool:
    ok = True
    for i, block in enumerate(skill_blocks(path), 1):
        r = run_lptl(block, [], "?", "?")
        if not r["compile_ok"]:
            ok = False
            print(f"{path.name} block {i}: does not compile\n{r['diagnostics']}")
        if nolet and find_let(block) is not None:
            ok = False
            print(f"{path.name} block {i}: uses let")
    return ok


def check_ast_output() -> bool:
    text = AST_OUTPUT.read_text(encoding="utf-8")
    ok = True
    for p in AST_PLACEHOLDERS:
        if text.count(p) != 1:
            ok = False
            print(f"ast_output.md: {p} must appear exactly once")
    src = re.findall(r"```tlvm\n(.*?)```", text, re.S)
    examples = [b for b in re.findall(r"```json\n(.*?)```", text, re.S) if b.strip() not in AST_PLACEHOLDERS]
    if len(src) != 1 or len(examples) != 1:
        print("ast_output.md: needs exactly one ```tlvm example and one ```json example")
        return False
    got = run_ast(src[0])
    try:
        example = json.loads(examples[0])
    except ValueError as e:
        print(f"ast_output.md: the JSON example does not parse: {e}")
        return False
    if not got["ok"] or got["ast"] != example:
        ok = False
        print(f"ast_output.md: the JSON example is not `tlvm ast` of the tlvm example {got['diagnostics']}")
    r = run_lptl(examples[0], [], "?", "?", filename="solution.json")
    if not r["compile_ok"]:
        ok = False
        print(f"ast_output.md: the JSON example is not accepted by compile_ast\n{r['diagnostics']}")
    return ok


def build_manifest(tasks: list[dict]) -> dict:
    files = {}
    for t in tasks:
        for f in TASK_FILES:
            p = t["dir"] / f
            files[str(p.relative_to(EVAL))] = sha256_file(p)
    task_set = hashlib.sha256(json.dumps(files, sort_keys=True).encode()).hexdigest()
    skill = SKILL.read_bytes()
    return {
        "skill": {"path": "SKILL.md", "sha256": hashlib.sha256(skill).hexdigest(), "bytes": len(skill)},
        "prompts": {p.name: sha256_file(p) for p in PROMPT_FILES},
        "task_set_sha256": task_set,
        "tasks": len(tasks),
        "hidden_cases": sum(len(t["hidden"]) for t in tasks),
        "out_of_scope": len(json.loads((EVAL / "out_of_scope.json").read_text(encoding="utf-8"))["tasks"]),
        "files": files,
    }


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--write", action="store_true", help="manifest.json を書き直す")
    args = ap.parse_args()
    ok = check_skill(SKILL)
    ok = check_skill(SKILL_NOLET, nolet=True) and ok
    ok = check_ast_output() and ok
    tasks = load_tasks()
    for t in tasks:
        cases = [{"name": f"ex{i + 1}", **e} for i, e in enumerate(t["examples"])] + t["hidden"]
        for lang, run, f in (("tlvm", run_lptl, "reference.tlvm"), ("py", run_python, "reference.py")):
            src = (t["dir"] / f).read_text(encoding="utf-8")
            r = run(src, cases, t["input_type"], t["output_type"])
            if not r["all_pass"]:
                ok = False
                bad = [c for c in r["cases"] if c["result"] != "pass"][:3]
                print(f"{t['id']} {lang}: FAIL {r['diagnostics']} {bad}")
    with_let = [t["id"] for t in tasks if find_let((t["dir"] / "reference.tlvm").read_text(encoding="utf-8")) is not None]
    print(f"{len(tasks)} tasks, {len(skill_blocks())} SKILL.md blocks and {len(skill_blocks(SKILL_NOLET))} SKILL-nolet.md "
          f"blocks checked; {len(with_let)} references use let ({len(tasks) - len(with_let)} let-free)")
    m = build_manifest(tasks)
    if args.write:
        MANIFEST.write_text(json.dumps(m, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")
    elif not MANIFEST.exists() or json.loads(MANIFEST.read_text(encoding="utf-8")) != m:
        ok = False
        print("manifest.json is out of date (run: python3 eval/check.py --write)")
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
