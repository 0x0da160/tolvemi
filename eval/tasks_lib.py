"""評価タスクの読み込みと参照解の実行。"""

from __future__ import annotations

import hashlib
import importlib.util
import json
from pathlib import Path

from lptl_types import from_python, parse_type, to_python

EVAL = Path(__file__).resolve().parent
TASKS = EVAL / "tasks"


def task_dirs() -> list[Path]:
    return sorted(p for p in TASKS.iterdir() if (p / "task.json").exists())


def load_task(d: Path) -> dict:
    t = json.loads((d / "task.json").read_text(encoding="utf-8"))
    t["dir"] = d
    hidden = d / "hidden.json"
    t["hidden"] = json.loads(hidden.read_text(encoding="utf-8")) if hidden.exists() else []
    return t


def load_tasks(only: list[str] | None = None) -> list[dict]:
    tasks = [load_task(d) for d in task_dirs()]
    if only:
        tasks = [t for t in tasks if any(t["id"] == o or t["id"].split("-", 1)[1] == o for o in only)]
    return tasks


def reference_module(d: Path):
    spec = importlib.util.spec_from_file_location(f"ref_{d.name.replace('-', '_')}", d / "reference.py")
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


def reference_output(mod, task: dict, plain_input):
    """参照解（Python）で期待出力を plain JSON で求める。"""
    tin, tout = parse_type(task["input_type"]), parse_type(task["output_type"])
    return from_python(mod.solve(to_python(plain_input, tin)), tout)


def sha256_file(p: Path) -> str:
    return hashlib.sha256(p.read_bytes()).hexdigest()


def dump_cases(cases: list[dict]) -> str:
    """一件一行の JSON 配列（差分を読みやすくするため）。"""
    lines = [json.dumps(c, ensure_ascii=False) for c in cases]
    return "[\n" + ",\n".join("  " + l for l in lines) + "\n]\n"
