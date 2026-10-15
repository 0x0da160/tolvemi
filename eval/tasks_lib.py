"""評価タスクの読み込みと参照解の実行。

隠しテストの乱数の種は二つある（evaluation-protocol-v1 草案 §6、§9 の 1）。
- 公開再現の課題集合（eval/tasks）：タスク ID の SHA-256 から決める。誰でも同じ hidden.json を作り直せる
- 秘密の最終評価の課題集合：環境変数 LPTL_EVAL_HIDDEN_SEED の秘密の値とタスク ID の HMAC-SHA256 から決める。
  値がなければ秘密の課題集合は読まない（fail closed）。値はリポジトリにも実行の記録にも書かない
"""

from __future__ import annotations

import hashlib
import hmac
import importlib.util
import json
import os
import random
from pathlib import Path

from lptl_types import Gen, from_python, parse_type, to_python

EVAL = Path(__file__).resolve().parent
TASKS = EVAL / "tasks"
HIDDEN_SEED_ENV = "LPTL_EVAL_HIDDEN_SEED"
HIDDEN_COUNT = 30


class SecretSeedMissing(RuntimeError):
    """秘密の課題集合の種（環境変数）がない。"""


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


def secret_seed(task_id: str, environ=None) -> int:
    """秘密の課題集合の種。秘密の値（環境変数）とタスク ID の HMAC-SHA256。値がなければ止まる。"""
    secret = (os.environ if environ is None else environ).get(HIDDEN_SEED_ENV, "")
    if not secret.strip():
        raise SecretSeedMissing(f"{HIDDEN_SEED_ENV} が設定されていないので、秘密の課題集合の隠しテストを作りません（fail closed）")
    return int(hmac.new(secret.encode(), task_id.encode(), hashlib.sha256).hexdigest()[:16], 16)


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


def load_secret_tasks(tasks_dir, count: int = HIDDEN_COUNT, environ=None) -> list[dict]:
    """秘密の最終評価の課題集合を読む。隠しテストは秘密の種からその場で作り、ファイルには書かない。

    各課題のディレクトリには task.json、reference.py、reference.tlvm を置く。hidden.json があれば、どちらの隠しテストを
    使うのかが曖昧になるので止まる。"""
    secret_seed("", environ)  # 何かを読む前に、種があることを確かめる
    root = Path(tasks_dir)
    if not root.is_dir():
        raise FileNotFoundError(f"秘密の課題集合のディレクトリがありません: {root}")
    tasks = []
    for d in sorted(p for p in root.iterdir() if (p / "task.json").exists()):
        if (d / "hidden.json").exists():
            raise RuntimeError(f"{d / 'hidden.json'}: 秘密の課題集合の隠しテストは種から作るので、ファイルを置かないでください")
        task = load_task(d)
        task["hidden"] = generate_hidden(task, reference_module(d), secret_seed(task["id"], environ), count)
        tasks.append(task)
    if not tasks:
        raise RuntimeError(f"秘密の課題集合に課題がありません: {root}")
    return tasks


def sha256_file(p: Path) -> str:
    return hashlib.sha256(p.read_bytes()).hexdigest()


def dump_cases(cases: list[dict]) -> str:
    """一件一行の JSON 配列（差分を読みやすくするため）。"""
    lines = [json.dumps(c, ensure_ascii=False) for c in cases]
    return "[\n" + ",\n".join("  " + l for l in lines) + "\n]\n"
