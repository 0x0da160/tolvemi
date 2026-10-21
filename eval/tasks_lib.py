"""評価タスクの読み込みと参照解の実行。

公開再現の課題集合（eval/tasks）の隠しテストは参照解から作り、乱数の種はタスク ID の SHA-256 から決める
（public_seed）。誰でも同じ hidden.json を作り直せる。最終評価はリポジトリの外に置く新しい課題集合で行い、
秘密の種は使わない（その課題集合はまだない。eval/README.md）。
"""

from __future__ import annotations

import hashlib
import importlib.util
import json
import random
from pathlib import Path

from lptl_types import Gen, from_python, parse_type, to_python

EVAL = Path(__file__).resolve().parent
TASKS = EVAL / "tasks"
HIDDEN_COUNT = 30


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


def public_seed(task_id: str) -> int:
    """公開再現の課題集合の種（タスク ID だけから決まる）。"""
    return int(hashlib.sha256(task_id.encode()).hexdigest()[:16], 16)


def generate_hidden(task: dict, mod, seed: int, count: int = HIDDEN_COUNT) -> list[dict]:
    """参照解（Python）から隠しテストを作る。reference.py に gen(rng, g) があればそれで入力を作り、無ければ入力型から作る。
    公開例と同じ入力や、重複した入力は使わない。"""
    tin = parse_type(task["input_type"])
    rng = random.Random(seed)
    g = Gen()
    seen = {json.dumps(e["input"]) for e in task["examples"]}
    hidden = []
    attempts = 0
    while len(hidden) < count and attempts < count * 50:
        attempts += 1
        v = mod.gen(rng, g) if hasattr(mod, "gen") else g.value(tin, rng)
        inp = from_python(v, tin)
        key = json.dumps(inp)
        if key in seen:
            continue
        seen.add(key)
        hidden.append({"name": f"h{len(hidden) + 1:02d}", "input": inp, "expected": reference_output(mod, task, inp)})
    return hidden


def sha256_file(p: Path) -> str:
    return hashlib.sha256(p.read_bytes()).hexdigest()


def dump_cases(cases: list[dict]) -> str:
    """一件一行の JSON 配列（差分を読みやすくするため）。"""
    lines = [json.dumps(c, ensure_ascii=False) for c in cases]
    return "[\n" + ",\n".join("  " + l for l in lines) + "\n]\n"
