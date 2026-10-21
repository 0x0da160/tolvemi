"""候補プログラム（LPTL の表面構文、ast_codec_v1 の AST、または Python）をテストケースで実行する。"""

from __future__ import annotations

import json
import os
import re
import subprocess
import sys
import tempfile
from pathlib import Path

from protocol import Outcome, REJECTION_PHASE, classify_case

EVAL = Path(__file__).resolve().parent
REPO = EVAL.parent
TLVM = Path(os.environ.get("TLVM", REPO / "target" / "release" / "tlvm"))
TLVM_TIMEOUT = 120


def _tlvm(*args: str, cwd: str) -> subprocess.CompletedProcess:
    if not TLVM.exists():
        sys.exit(f"tlvm が見つかりません: {TLVM}（cargo build --release を実行するか TLVM を設定してください）")
    return subprocess.run([str(TLVM), *args], cwd=cwd, capture_output=True, text=True, timeout=TLVM_TIMEOUT)


def _named(cases: list[dict]) -> list[dict]:
    return [{"name": c.get("name") or f"case{i + 1}", "input": c["input"], "expected": c["expected"]} for i, c in enumerate(cases)]


def line_col(src: bytes, offset: int) -> tuple[int, int]:
    """byte 位置の行と列（1 から）。列は行頭からの文字数で、tlvm の diagnostics::line_col と同じ数え方。"""
    offset = max(0, min(offset, len(src)))
    before = src[:offset]
    start = before.rfind(b"\n") + 1
    return before.count(b"\n") + 1, len(src[start:offset].decode("utf-8", "replace")) + 1


def _json_objects(text: str) -> list[dict]:
    out = []
    for line in text.splitlines():
        try:
            obj = json.loads(line)
        except ValueError:
            continue
        if isinstance(obj, dict):
            out.append(obj)
    return out


def error_diagnostics(stderr: str, source: str) -> list[dict]:
    """tlvm check の JSON 出力から、error の診断を code、phase、message、span（行と列）、expected、found にして並べる。
    envelope（SourceBoundaryFailure、AstBoundaryFailure、InternalFault）も code と message の形で入れる。"""
    src = source.encode()
    out = []
    for obj in _json_objects(stderr):
        if "code" in obj:
            if obj.get("severity") != "error":
                continue
            d = {"code": obj["code"], "phase": obj.get("phase"), "message": obj.get("message") or "",
                 "expected": obj.get("expected"), "found": obj.get("actual")}
            span = obj.get("span") or {}
            if isinstance(span.get("start"), int) and isinstance(span.get("end"), int):
                d["start"], d["end"] = line_col(src, span["start"]), line_col(src, span["end"])
            out.append(d)
        elif "result" in obj:
            out.append({"code": obj["result"], "phase": "boundary", "message": obj.get("reason") or "", "expected": None,
                        "found": None})
    return out


def rejection_phase(errors: list[dict]) -> str:
    """拒否の段階（parse・name・type・entry・other）。最初の error の phase で決める。"""
    for e in errors:
        if e["phase"] == "boundary":
            return "parse"
        return REJECTION_PHASE.get(e["phase"], "other")
    return "other"


def _case_infra(results: list[dict]) -> str | None:
    """テストの結果のうち、候補ではなく試験基盤の事故を示すもの（InternalFault、課題のデータの誤り）。"""
    for r in results:
        if r["result"] == "error":
            outcome, detail = classify_case(r, "tlvm")
            if outcome is Outcome.INFRA_FAULT:
                return detail
    return None


def _entry_span(source: str, filename: str) -> tuple[int, int] | None:
    pattern = r'"tag"\s*:\s*"entry"' if filename.endswith(".json") else r"(?m)^[ \t]*entry\b"
    m = re.search(pattern, source)
    if not m:
        return None
    return len(source[:m.start()].encode()), len(source[:m.end()].encode())


def run_lptl(source: str, cases: list[dict], input_type: str, output_type: str, filename: str = "solution.tlvm",
             run_cases: bool = True) -> dict:
    """LPTL の候補を検査・実行する。filename が .json なら ast_codec_v1 の AST として読む（compile_ast）。

    返す dict：compile_ok、diagnostics（--human の診断文）、codes（診断コード）、errors（error の診断を構造化したもの）、
    phase（拒否の段階）、signature_ok、cases（name、result = pass | fail | error、actual、reason）、all_pass、
    infra（試験基盤の事故の kind。なければ None）。run_cases が偽なら検査だけしてケースは走らせない。
    """
    cases = _named(cases)
    out = {"compile_ok": False, "diagnostics": "", "codes": [], "errors": [], "phase": None, "signature_ok": False,
           "cases": [], "all_pass": False, "infra": None}
    try:
        with tempfile.TemporaryDirectory() as d:
            Path(d, filename).write_text(source, encoding="utf-8")
            human = _tlvm("check", filename, "--human", cwd=d)
            machine = _tlvm("check", filename, cwd=d)
            if {human.returncode, machine.returncode} - {0, 1} or human.returncode != machine.returncode:
                return {**out, "infra": "tlvm-exit",
                        "diagnostics": f"tlvm check exited {human.returncode}/{machine.returncode}: {machine.stderr[-300:]}"}
            errors = error_diagnostics(machine.stderr, source)
            if any(e["code"] == "InternalFault" for e in errors):
                return {**out, "infra": "tlvm-internal-fault", "diagnostics": machine.stderr[-300:]}
            codes = [o["code"] for o in _json_objects(machine.stderr) if "code" in o]
            out.update(compile_ok=human.returncode == 0, diagnostics=human.stderr.strip(), codes=codes, errors=errors)
            if human.returncode != 0:
                return {**out, "phase": rejection_phase(errors)}
            try:
                sig = json.loads(machine.stdout.strip().splitlines()[-1])
            except (IndexError, ValueError):
                return {**out, "infra": "tlvm-output", "diagnostics": machine.stdout[-300:]}
            want = {"entry": "solve", "input_type": input_type, "output_type": output_type}
            got = {k: sig.get(k) for k in want}
            if got != want:
                msg = (
                    f"The program compiles, but its entry is `{got['entry']}: {got['input_type']} -> {got['output_type']}`; "
                    f"it must be `entry solve` with `fn solve(...: {input_type}) -> {output_type}`."
                )
                err = {"code": "EntrySignature", "phase": "entry", "message": msg,
                       "expected": f"solve: {input_type} -> {output_type}",
                       "found": f"{got['entry']}: {got['input_type']} -> {got['output_type']}"}
                if span := _entry_span(source, filename):
                    err["start"], err["end"] = line_col(source.encode(), span[0]), line_col(source.encode(), span[1])
                return {**out, "diagnostics": msg, "errors": [err], "phase": "entry"}
            out["signature_ok"] = True
            if not run_cases:
                return out
            Path(d, "cases.json").write_text(json.dumps(cases), encoding="utf-8")
            t = _tlvm("test", filename, "cases.json", cwd=d)
            if t.returncode not in (0, 1):
                return {**out, "infra": "tlvm-exit", "diagnostics": f"tlvm test exited {t.returncode}: {t.stderr[-300:]}"}
            results = []
            for line in t.stdout.splitlines():
                try:
                    obj = json.loads(line)
                except ValueError:
                    return {**out, "infra": "tlvm-output", "diagnostics": line[:300]}
                if "case" in obj:
                    results.append({"name": obj["case"], "result": obj["result"], "actual": obj.get("actual"),
                                    "reason": obj.get("reason")})
            infra = _case_infra(results) or (None if len(results) == len(cases) else "tlvm-output")
            return {**out, "cases": results, "infra": infra,
                    "all_pass": infra is None and all(r["result"] == "pass" for r in results)}
    except subprocess.TimeoutExpired:
        return {**out, "infra": "tlvm-timeout", "diagnostics": f"tlvm did not finish in {TLVM_TIMEOUT}s"}


# ---------------------------------------------------------------------------------------------- let のない言語（lptl-nolet）


def find_let(source: str) -> int | None:
    """表面構文の `let`（予約語）の位置（文字の index）。コメントと文字・文字列リテラルの中は見ない。なければ None。

    tlvm ast の出力は直和型や match を展開した形で let を含むことがあるので、AST ではなく字句で見る。"""
    i, n = 0, len(source)
    while i < n:
        if source.startswith("//", i):
            j = source.find("\n", i)
            i = n if j < 0 else j
            continue
        c = source[i]
        if c in "\"'":
            j = i + 1
            while j < n and source[j] != c:
                j += 2 if source[j] == "\\" else 1
            i = j + 1
            continue
        if c.isalpha() or c == "_":
            j = i
            while j < n and (source[j].isalnum() or source[j] == "_"):
                j += 1
            if source[i:j] == "let":
                return i
            i = j
            continue
        i += 1
    return None


def nolet_rejection(source: str, index: int, filename: str = "solution.tlvm") -> dict:
    """let を使ったプログラムを、let のない言語の parse の拒否として返す（run_lptl と同じ形の dict）。"""
    src = source.encode()
    start = len(source[:index].encode())
    (line, col), end = line_col(src, start), line_col(src, start + 3)
    text = source.splitlines()[line - 1] if source.splitlines() else ""
    msg = "this language has no `let`"
    repair = "pass the value to a helper function as an argument instead of binding it with `let`"
    human = (f"{filename}:{line}:{col}: error[NoLet]: {msg} (found let)\n"
             f" {line} | {text}\n {' ' * len(str(line))} | {' ' * (col - 1)}^^^\n = repair: {repair}")
    err = {"code": "NoLet", "phase": "parse", "message": msg, "expected": None, "found": "let", "start": (line, col),
           "end": end}
    return {"compile_ok": False, "diagnostics": human, "codes": ["NoLet"], "errors": [err], "phase": "parse",
            "signature_ok": False, "cases": [], "all_pass": False, "infra": None}


def run_ast(source: str) -> dict:
    """`tlvm ast` で表面構文を AST の JSON にする（構文だけの検査）。Render と連結 arm の採点と、AST の arm の
    oracle に使う。受理されなければ診断と拒否の段階（phase）を返す。"""
    with tempfile.TemporaryDirectory() as d:
        Path(d, "solution.tlvm").write_text(source, encoding="utf-8")
        p = _tlvm("ast", "solution.tlvm", cwd=d)
    if p.returncode != 0:
        text = (p.stdout + p.stderr).strip()
        return {"ok": False, "ast": None, "diagnostics": text, "phase": rejection_phase(error_diagnostics(text, source))}
    try:
        return {"ok": True, "ast": json.loads(p.stdout), "diagnostics": "", "phase": None}
    except ValueError:
        return {"ok": False, "ast": None, "diagnostics": "tlvm ast did not print JSON: " + p.stdout[:200], "phase": "other"}


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
