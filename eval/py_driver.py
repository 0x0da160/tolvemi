"""Python 対照群の候補を実行する（runner.py から別プロセスで呼ぶ）。

usage: python3 -I py_driver.py CANDIDATE.py CASES.json INPUT_TYPE OUTPUT_TYPE
結果を一つの JSON object で stdout に出す。
"""

import json
import os
import sys
import traceback

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from lptl_types import from_python, parse_type, to_python  # noqa: E402


def main() -> None:
    cand, cases_path, in_t, out_t = sys.argv[1:5]
    tin, tout = parse_type(in_t), parse_type(out_t)
    source = open(cand, encoding="utf-8").read()
    cases = json.load(open(cases_path, encoding="utf-8"))
    ns = {"__name__": "candidate"}
    try:
        exec(compile(source, "solution.py", "exec"), ns)
    except BaseException:
        print(json.dumps({"compile_ok": False, "error": traceback.format_exc(limit=3)}))
        return
    solve = ns.get("solve")
    if not callable(solve):
        print(json.dumps({"compile_ok": False, "error": "solution.py does not define a function solve(x)"}))
        return
    results = []
    for c in cases:
        try:
            out = solve(to_python(c["input"], tin))
            actual = from_python(out, tout)
            results.append({"name": c["name"], "result": "pass" if actual == c["expected"] else "fail", "actual": actual})
        except BaseException as e:  # noqa: BLE001 - 候補のどんな失敗も一件の失敗として記録する
            results.append({"name": c["name"], "result": "error", "reason": f"{type(e).__name__}: {e}"})
    print(json.dumps({"compile_ok": True, "cases": results}))


main()
