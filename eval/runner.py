"""候補プログラム（LPTL または Python）をテストケースで実行する。"""

from __future__ import annotations

import json
import os
import subprocess
import sys
import tempfile
from pathlib import Path

EVAL = Path(__file__).resolve().parent
REPO = EVAL.parent
TLVM = Path(os.environ.get("TLVM", REPO / "target" / "release" / "tlvm"))


def _tlvm(*args: str, cwd: str) -> subprocess.CompletedProcess:
    if not TLVM.exists():
        sys.exit(f"tlvm が見つかりません: {TLVM}（cargo build --release を実行するか TLVM を設定してください）")
    return subprocess.run([str(TLVM), *args], cwd=cwd, capture_output=True, text=True, timeout=120)


def _named(cases: list[dict]) -> list[dict]:
    return [{"name": c.get("name") or f"case{i + 1}", "input": c["input"], "expected": c["expected"]} for i, c in enumerate(cases)]


def run_lptl(source: str, cases: list[dict], input_type: str, output_type: str) -> dict:
    """LPTL の候補を検査・実行する。

    返す dict：compile_ok、diagnostics（--human の診断文）、codes（診断コード）、signature_ok、
    cases（name、result = pass | fail | error、actual、reason）、all_pass。
    """
    cases = _named(cases)
    with tempfile.TemporaryDirectory() as d:
        Path(d, "solution.tlvm").write_text(source, encoding="utf-8")
        human = _tlvm("check", "solution.tlvm", "--human", cwd=d)
        machine = _tlvm("check", "solution.tlvm", cwd=d)
        codes = []
        for line in machine.stderr.splitlines():
            try:
                obj = json.loads(line)
            except json.JSONDecodeError:
                continue
            if "code" in obj:
                codes.append(obj["code"])
        out = {"compile_ok": human.returncode == 0, "diagnostics": human.stderr.strip(), "codes": codes}
        if human.returncode != 0:
            return {**out, "signature_ok": False, "cases": [], "all_pass": False}
        sig = json.loads(machine.stdout.strip().splitlines()[-1])
        want = {"entry": "solve", "input_type": input_type, "output_type": output_type}
        got = {k: sig.get(k) for k in want}
        if got != want:
            msg = (
                f"The program compiles, but its entry is `{got['entry']}: {got['input_type']} -> {got['output_type']}`; "
                f"it must be `entry solve` with `fn solve(...: {input_type}) -> {output_type}`."
            )
            return {**out, "signature_ok": False, "diagnostics": msg, "cases": [], "all_pass": False}
        Path(d, "cases.json").write_text(json.dumps(cases), encoding="utf-8")
        t = _tlvm("test", "solution.tlvm", "cases.json", cwd=d)
        results = []
        for line in t.stdout.splitlines():
            obj = json.loads(line)
            if "case" in obj:
                results.append({"name": obj["case"], "result": obj["result"], "actual": obj.get("actual"), "reason": obj.get("reason")})
        return {**out, "signature_ok": True, "cases": results, "all_pass": len(results) == len(cases) and all(r["result"] == "pass" for r in results)}


def run_python(source: str, cases: list[dict], input_type: str, output_type: str, timeout: float = 20.0) -> dict:
    """Python の候補を別プロセスで実行する（同じ形の dict を返す。codes は例外の型名）。"""
    cases = _named(cases)
    with tempfile.TemporaryDirectory() as d:
        Path(d, "solution.py").write_text(source, encoding="utf-8")
        Path(d, "cases.json").write_text(json.dumps(cases), encoding="utf-8")
        try:
            p = subprocess.run(
                [sys.executable, "-I", str(EVAL / "py_driver.py"), "solution.py", "cases.json", input_type, output_type],
                cwd=d, capture_output=True, text=True, timeout=timeout,
            )
        except subprocess.TimeoutExpired:
            return {"compile_ok": True, "diagnostics": f"timed out after {timeout:.0f}s", "codes": ["Timeout"],
                    "signature_ok": True, "cases": [], "all_pass": False}
        try:
            r = json.loads(p.stdout.strip().splitlines()[-1])
        except (IndexError, json.JSONDecodeError):
            return {"compile_ok": False, "diagnostics": (p.stderr or p.stdout)[-2000:], "codes": ["Crash"],
                    "signature_ok": False, "cases": [], "all_pass": False}
        if not r["compile_ok"]:
            err = r["error"].strip()
            return {"compile_ok": False, "diagnostics": err, "codes": [err.splitlines()[-1].split(":")[0]],
                    "signature_ok": False, "cases": [], "all_pass": False}
        res = r["cases"]
        codes = sorted({c["reason"].split(":")[0] for c in res if c["result"] == "error"})
        return {"compile_ok": True, "diagnostics": "", "codes": codes, "signature_ok": True, "cases": res,
                "all_pass": len(res) == len(cases) and all(c["result"] == "pass" for c in res)}
