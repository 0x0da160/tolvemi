"""参照解（reference.py）から、公開例の期待出力と隠しテスト（hidden.json）を作る。

乱数の種はタスク ID から決めるので、何度実行しても同じテストになる。
reference.py に gen(rng, g) があればそれで入力を作り、無ければ入力型から作る。

usage: python3 eval/gen_tests.py [--count N]
"""

from __future__ import annotations

import argparse
import hashlib
import json
import random

from lptl_types import Gen, from_python, parse_type
from tasks_lib import dump_cases, load_task, reference_module, reference_output, task_dirs


def write_task_json(d, task: dict) -> None:
    meta = {k: v for k, v in task.items() if k not in ("dir", "hidden")}
    examples = meta.pop("examples")
    body = json.dumps(meta, ensure_ascii=False, indent=2)[:-2]
    ex = ",\n".join("    " + json.dumps(e, ensure_ascii=False) for e in examples)
    (d / "task.json").write_text(body + ',\n  "examples": [\n' + ex + "\n  ]\n}\n", encoding="utf-8")


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--count", type=int, default=30, help="隠しテストの件数")
    args = ap.parse_args()
    g = Gen()
    for d in task_dirs():
        task = load_task(d)
        mod = reference_module(d)
        tin = parse_type(task["input_type"])
        task["examples"] = [{"input": e["input"], "expected": reference_output(mod, task, e["input"])} for e in task["examples"]]
        write_task_json(d, task)
        seed = int(hashlib.sha256(task["id"].encode()).hexdigest()[:16], 16)
        rng = random.Random(seed)
        seen = {json.dumps(e["input"]) for e in task["examples"]}
        hidden = []
        attempts = 0
        while len(hidden) < args.count and attempts < args.count * 50:
            attempts += 1
            v = mod.gen(rng, g) if hasattr(mod, "gen") else g.value(tin, rng)
            inp = from_python(v, tin)
            key = json.dumps(inp)
            if key in seen:
                continue
            seen.add(key)
            hidden.append({"name": f"h{len(hidden) + 1:02d}", "input": inp, "expected": reference_output(mod, task, inp)})
        (d / "hidden.json").write_text(dump_cases(hidden), encoding="utf-8")
        print(f"{task['id']}: {len(task['examples'])} examples, {len(hidden)} hidden")


if __name__ == "__main__":
    main()
