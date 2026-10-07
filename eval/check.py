"""評価セットの整合性を検査する。

- 各タスクの参照解（reference.tlvm と reference.py）が公開例と隠しテストを全て通ること
- SKILL.md の ```tlvm ブロックが全て tlvm check を通ること
- manifest.json（SKILL.md と各タスクのファイルの SHA-256）が最新であること（--write で更新）

usage: python3 eval/check.py [--write]
"""

from __future__ import annotations

import argparse
import hashlib
import json
import re
import sys
from pathlib import Path

from runner import run_lptl, run_python
from tasks_lib import EVAL, load_tasks, sha256_file

SKILL = EVAL / "SKILL.md"
MANIFEST = EVAL / "manifest.json"
TASK_FILES = ("task.json", "hidden.json", "reference.tlvm", "reference.py")


def skill_blocks() -> list[str]:
    return re.findall(r"```tlvm\n(.*?)```", SKILL.read_text(encoding="utf-8"), re.S)


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
    ok = True
    for i, block in enumerate(skill_blocks(), 1):
        r = run_lptl(block, [], "?", "?")
        if not r["compile_ok"]:
            ok = False
            print(f"SKILL.md block {i}: does not compile\n{r['diagnostics']}")
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
    print(f"{len(tasks)} tasks, {len(skill_blocks())} SKILL.md blocks checked")
    m = build_manifest(tasks)
    if args.write:
        MANIFEST.write_text(json.dumps(m, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")
    elif not MANIFEST.exists() or json.loads(MANIFEST.read_text(encoding="utf-8")) != m:
        ok = False
        print("manifest.json is out of date (run: python3 eval/check.py --write)")
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
