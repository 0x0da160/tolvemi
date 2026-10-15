"""参照解（reference.py）から、公開例の期待出力と隠しテスト（hidden.json）を作る（公開再現の課題集合）。

乱数の種はタスク ID から決めるので（tasks_lib.public_seed）、何度実行しても同じテストになる。
reference.py に gen(rng, g) があればそれで入力を作り、無ければ入力型から作る。

usage: python3 eval/gen_tests.py [--count N]
"""

from __future__ import annotations

import argparse
import json

from tasks_lib import (HIDDEN_COUNT, dump_cases, generate_hidden, load_task, public_seed, reference_module,
                       reference_output, task_dirs)


def write_task_json(d, task: dict) -> None:
    meta = {k: v for k, v in task.items() if k not in ("dir", "hidden")}
    examples = meta.pop("examples")
    body = json.dumps(meta, ensure_ascii=False, indent=2)[:-2]
    ex = ",\n".join("    " + json.dumps(e, ensure_ascii=False) for e in examples)
    (d / "task.json").write_text(body + ',\n  "examples": [\n' + ex + "\n  ]\n}\n", encoding="utf-8")


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--count", type=int, default=HIDDEN_COUNT, help="隠しテストの件数")
    args = ap.parse_args()
    for d in task_dirs():
        task = load_task(d)
        mod = reference_module(d)
        task["examples"] = [{"input": e["input"], "expected": reference_output(mod, task, e["input"])} for e in task["examples"]]
        write_task_json(d, task)
        hidden = generate_hidden(task, mod, public_seed(task["id"]), args.count)
        (d / "hidden.json").write_text(dump_cases(hidden), encoding="utf-8")
        print(f"{task['id']}: {len(task['examples'])} examples, {len(hidden)} hidden")


if __name__ == "__main__":
    main()
