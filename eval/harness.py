"""LLM 予備実験のハーネス（設計書 §12 の Surface モードと Repair モードの最小版）。

各タスクについて、モデルに解答を書かせ、公開例で検査し、失敗すれば診断や失敗例を返して直させる
（最大 --rounds 回）。各回の候補を隠しテストでも採点し、Success@1（初回）と Success@R（最終回）を記録する。

arm:
  lptl         SKILL.md を system に置き、LPTL で書かせる。修復時は tlvm の診断（--human）を返す
  lptl-nodiag  lptl と同じだが、修復時は「コンパイルできなかった」とだけ返す（診断の効果を見る対照）
  python       Python の solve(x) を書かせる（同じタスク・同じ公開例・同じ隠しテスト）

backend:
  anthropic    Claude API（ANTHROPIC_API_KEY などの認証が必要）
  claude-cli   Claude Code の CLI（claude -p）。サブスクリプションでログインした claude があれば API キーは不要
  oracle       参照解をそのまま返す（API を使わずにハーネスを空回しして検査する）

usage:
  python3 eval/harness.py --backend oracle
  python3 eval/harness.py --model claude-opus-5-5 --arms lptl,python --repeats 1 --rounds 3
  python3 eval/harness.py --backend claude-cli --arms lptl,python

これは事前登録した正式実験（§12.5、G4）ではない。LPTL が LLM に有利かどうかを主張する材料にはせず、
どこで失敗するかを知るための予備実験として使う。
"""

from __future__ import annotations

import argparse
import datetime as dt
import hashlib
import json
import math
import os
import re
import subprocess
import sys
import tempfile
import threading
from collections import Counter
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path

from lptl_types import lptl_literal, parse_type, python_literal
from runner import run_lptl, run_python
from tasks_lib import EVAL, load_tasks

ARMS = ("lptl", "lptl-nodiag", "python")
SKILL = (EVAL / "SKILL.md").read_text(encoding="utf-8")

PYTHON_SYSTEM = """You write Python 3 solutions to small programming tasks.

Define a function `solve(x)` that takes the single input value and returns the result. Values are represented as
follows: integers are `int`, booleans are `bool`, lists are `list`, `pair(a, b)` is the tuple `(a, b)`, `some(v)` is
just `v`, and `none` is `None`. Use only the standard library and do not read input or print output.

Answer with the complete solution in a single fenced code block tagged `python`."""


# ---------------------------------------------------------------------------------------------- prompts


def render_examples(task: dict, arm: str) -> str:
    tin, tout = parse_type(task["input_type"]), parse_type(task["output_type"])
    lines = []
    for e in task["examples"]:
        if arm == "python":
            lines.append(f"solve({python_literal(e['input'], tin)}) == {python_literal(e['expected'], tout)}")
        else:
            lines.append(f"solve({lptl_literal(e['input'], tin)}) = {lptl_literal(e['expected'], tout)}")
    return "\n".join(lines)


def task_prompt(task: dict, arm: str) -> str:
    if arm == "python":
        sig = f"def solve(x)  # x: {task['input_type']}, returns {task['output_type']}"
        lang = "python"
    else:
        sig = f"fn solve(x: {task['input_type']}) -> {task['output_type']}\nentry solve"
        lang = "tlvm"
    return (
        f"Task: {task['title']}\n\n{task['prompt']}\n\n"
        f"Signature (the parameter name is up to you):\n```{lang}\n{sig}\n```\n\n"
        f"Examples:\n```\n{render_examples(task, arm)}\n```"
    )


def feedback(arm: str, task: dict, r: dict, visible: list[dict]) -> str:
    """公開例での失敗を、次の回にモデルへ返す文にする。"""
    if not r["compile_ok"] or not r["signature_ok"]:
        if arm == "lptl-nodiag":
            return "The program was rejected by the checker. Fix it and answer with the complete corrected program."
        what = "checker" if arm.startswith("lptl") else "Python interpreter"
        return f"The {what} rejected the program:\n```\n{r['diagnostics']}\n```\nFix it and answer with the complete corrected program."
    tin, tout = parse_type(task["input_type"]), parse_type(task["output_type"])
    lit = python_literal if arm == "python" else lptl_literal
    by_name = {c["name"]: c for c in visible}
    lines = []
    for c in r["cases"]:
        if c["result"] == "pass":
            continue
        case = by_name[c["name"]]
        got = c["reason"] if c["result"] == "error" else lit(c["actual"], tout)
        lines.append(f"solve({lit(case['input'], tin)}): expected {lit(case['expected'], tout)}, got {got}")
    return "Some examples fail:\n```\n" + "\n".join(lines) + "\n```\nFix it and answer with the complete corrected program."


def extract_code(text: str, arm: str) -> str | None:
    tags = ("python", "py") if arm == "python" else ("tlvm", "lptl", "tolvemi")
    blocks = re.findall(r"```([A-Za-z0-9_-]*)[^\n]*\n(.*?)```", text, re.S)
    tagged = [b for t, b in blocks if t.lower() in tags]
    if tagged:
        return tagged[-1]
    return blocks[-1][1] if blocks else None


# ---------------------------------------------------------------------------------------------- backends


class OracleBackend:
    """参照解を返す。ハーネスと採点の経路を API なしで確かめるためのもの。"""

    name = "oracle"

    def complete(self, system: str, messages: list[dict], task: dict, arm: str) -> dict:
        f = "reference.py" if arm == "python" else "reference.tlvm"
        lang = "python" if arm == "python" else "tlvm"
        code = (task["dir"] / f).read_text(encoding="utf-8")
        return {"text": f"```{lang}\n{code}```", "content": f"```{lang}\n{code}```", "stop_reason": "end_turn",
                "usage": {"input_tokens": 0, "output_tokens": 0}, "model": "oracle", "fallback": False}


class AnthropicBackend:
    def __init__(self, model: str, effort: str, max_tokens: int, fallback: bool):
        import anthropic

        self.client = anthropic.Anthropic()
        self.model, self.effort, self.max_tokens, self.fallback = model, effort, max_tokens, fallback
        self.name = f"anthropic:{model}"

    def complete(self, system: str, messages: list[dict], task: dict, arm: str) -> dict:
        kwargs = dict(
            model=self.model,
            max_tokens=self.max_tokens,
            system=[{"type": "text", "text": system, "cache_control": {"type": "ephemeral"}}],
            messages=messages,
            output_config={"effort": self.effort},
        )
        if self.fallback:
            # 安全分類器が断ったときに推奨モデルで続ける。どのモデルが答えたかは episode に記録する
            kwargs.update(betas=["server-side-fallback-2026-07-01"], fallbacks="default")
        with self.client.beta.messages.stream(**kwargs) as stream:
            msg = stream.get_final_message()
        text = "".join(b.text for b in msg.content if b.type == "text")
        fallback_ran = any(getattr(e, "type", None) == "fallback_message" for e in (getattr(msg.usage, "iterations", None) or []))
        u = msg.usage
        return {
            "text": text,
            "content": msg.content,  # 思考ブロックを含めてそのまま次の回に渡す
            "stop_reason": msg.stop_reason,
            "usage": {
                "input_tokens": u.input_tokens,
                "output_tokens": u.output_tokens,
                "cache_read_input_tokens": getattr(u, "cache_read_input_tokens", 0) or 0,
                "cache_creation_input_tokens": getattr(u, "cache_creation_input_tokens", 0) or 0,
            },
            "model": msg.model,
            "fallback": fallback_ran,
        }


class ClaudeCliBackend:
    """Claude Code の CLI を非対話（claude -p）で呼ぶ。サブスクリプションのログインで動き、API キーは要らない。

    ツールをすべて無効にし、設定・MCP・CLAUDE.md を読まず、空の一時ディレクトリで動かすので、モデルは
    リポジトリ（参照解や隠しテスト）を見られない。CLI は呼び出しごとに 1 往復なので、修復の回では
    それまでの会話を 1 つのプロンプトに書き起こして渡す（思考ブロックは引き継がれない）。
    Claude Code が system prompt の前後に短い定型文を足すことがあり、API の arm と完全には同じ条件ではない。
    """

    def __init__(self, model: str, effort: str, binary: str = "claude", timeout: float = 900):
        self.model, self.effort, self.binary, self.timeout = model, effort, binary, timeout
        self.name = f"claude-cli:{model}"
        self.workdir = tempfile.mkdtemp(prefix="lptl-eval-")

    @staticmethod
    def render(messages: list[dict]) -> str:
        if len(messages) == 1:
            return messages[0]["content"]
        turns = "\n\n".join(f'<turn role="{m["role"]}">\n{m["content"]}\n</turn>' for m in messages)
        return ("This is a continuing conversation. The earlier turns are reproduced below; your own earlier answers "
                "are the assistant turns. Reply to the last user turn.\n\n" + turns)

    def complete(self, system: str, messages: list[dict], task: dict, arm: str) -> dict:
        cmd = [self.binary, "-p", "--system-prompt", system, "--tools", "", "--output-format", "json",
               "--no-session-persistence", "--strict-mcp-config", "--setting-sources", "",
               "--model", self.model, "--effort", self.effort]
        env = {k: v for k, v in os.environ.items() if k not in ("CLAUDE_CODE_SESSION_ID", "CLAUDECODE")}
        p = subprocess.run(cmd, input=self.render(messages), capture_output=True, text=True, cwd=self.workdir,
                           env=env, timeout=self.timeout)
        try:
            out = json.loads(p.stdout)
        except json.JSONDecodeError:
            raise RuntimeError(f"claude exited {p.returncode}: {(p.stderr or p.stdout).strip()[:500]}") from None
        if out.get("is_error"):
            raise RuntimeError(f"claude error ({out.get('subtype')}): {str(out.get('result'))[:500]}")
        u = out.get("usage") or {}
        models = [m for m in (out.get("modelUsage") or {}) if not m.startswith("claude-haiku")] or [self.model]
        text = out.get("result") or ""
        return {
            "text": text,
            "content": text,
            "stop_reason": out.get("stop_reason") or "end_turn",
            "usage": {
                "input_tokens": u.get("input_tokens", 0),
                "output_tokens": u.get("output_tokens", 0),
                "cache_read_input_tokens": u.get("cache_read_input_tokens", 0),
                "cache_creation_input_tokens": u.get("cache_creation_input_tokens", 0),
            },
            "model": ",".join(models),
            "fallback": any(e.get("type") == "fallback_message" for e in (u.get("iterations") or [])),
        }


# ---------------------------------------------------------------------------------------------- episodes


def run_candidate(arm: str, code: str | None, cases: list[dict], task: dict) -> dict:
    if code is None:
        return {"compile_ok": False, "signature_ok": False, "diagnostics": "No fenced code block was found in the answer.",
                "codes": ["NoCode"], "cases": [], "all_pass": False}
    run = run_python if arm == "python" else run_lptl
    return run(code, cases, task["input_type"], task["output_type"])


def episode(backend, task: dict, arm: str, rounds: int, rep: int) -> dict:
    system = PYTHON_SYSTEM if arm == "python" else SKILL
    visible = [{"name": f"ex{i + 1}", **e} for i, e in enumerate(task["examples"])]
    messages = [{"role": "user", "content": task_prompt(task, arm)}]
    log = []
    for k in range(1, rounds + 1):
        try:
            resp = backend.complete(system, messages, task, arm)
        except Exception as e:  # noqa: BLE001 - API の失敗は episode の失敗として記録して続ける
            log.append({"round": k, "api_error": f"{type(e).__name__}: {e}"})
            break
        code = extract_code(resp["text"], arm) if resp["stop_reason"] != "refusal" else None
        vis = run_candidate(arm, code, visible, task)
        hid = run_candidate(arm, code, task["hidden"], task)
        log.append({
            "round": k,
            "stop_reason": resp["stop_reason"],
            "model": resp["model"],
            "fallback": resp["fallback"],
            "usage": resp["usage"],
            "code": code,
            "compile_ok": vis["compile_ok"],
            "signature_ok": vis["signature_ok"],
            "codes": vis["codes"],
            "visible_pass": vis["all_pass"],
            "hidden_pass": hid["all_pass"],
            "hidden_passed": sum(c["result"] == "pass" for c in hid["cases"]),
            "hidden_total": len(task["hidden"]),
        })
        if vis["all_pass"] or resp["stop_reason"] == "refusal":
            break
        messages.append({"role": "assistant", "content": resp["content"]})
        messages.append({"role": "user", "content": feedback(arm, task, vis, visible)})
    done = [r for r in log if "api_error" not in r]
    return {
        "task": task["id"],
        "category": task["category"],
        "arm": arm,
        "repeat": rep,
        "success_at_1": bool(done) and done[0]["hidden_pass"],
        "success_final": bool(done) and done[-1]["hidden_pass"],
        "rounds_used": len(done),
        "api_error": next((r["api_error"] for r in log if "api_error" in r), None),
        "rounds": log,
    }


# ---------------------------------------------------------------------------------------------- summary


def wilson(k: int, n: int, z: float = 1.96) -> tuple[float, float]:
    if n == 0:
        return (0.0, 0.0)
    p = k / n
    d = 1 + z * z / n
    c = (p + z * z / (2 * n)) / d
    h = z * math.sqrt(p * (1 - p) / n + z * z / (4 * n * n)) / d
    return (max(0.0, c - h), min(1.0, c + h))


def summarize(episodes: list[dict], rounds: int) -> dict:
    out = {}
    for arm in sorted({e["arm"] for e in episodes}):
        es = [e for e in episodes if e["arm"] == arm]
        n = len(es)
        s1 = sum(e["success_at_1"] for e in es)
        sf = sum(e["success_final"] for e in es)
        first = [e["rounds"][0] for e in es if e["rounds"] and "api_error" not in e["rounds"][0]]
        failed_rounds = [r for e in es for r in e["rounds"] if "api_error" not in r and not r["visible_pass"]]
        usage = Counter()
        for e in es:
            for r in e["rounds"]:
                usage.update(r.get("usage", {}))
        out[arm] = {
            "episodes": n,
            "success_at_1": s1,
            "success_at_1_rate": s1 / n if n else 0,
            "success_at_1_ci95": wilson(s1, n),
            f"success_at_{rounds}": sf,
            f"success_at_{rounds}_rate": sf / n if n else 0,
            f"success_at_{rounds}_ci95": wilson(sf, n),
            "first_round_compile_fail": sum(not r["compile_ok"] or not r["signature_ok"] for r in first),
            "mean_rounds": sum(e["rounds_used"] for e in es) / n if n else 0,
            "api_errors": sum(e["api_error"] is not None for e in es),
            "refusals": sum(r.get("stop_reason") == "refusal" for e in es for r in e["rounds"]),
            "fallback_rounds": sum(bool(r.get("fallback")) for e in es for r in e["rounds"]),
            "failure_codes": Counter(c for r in failed_rounds for c in r["codes"]).most_common(15),
            "failed_tasks": sorted(e["task"] for e in es if not e["success_final"]),
            "usage": dict(usage),
        }
    return out


def summary_markdown(summary: dict, config: dict) -> str:
    r = config["rounds"]
    lines = [
        f"# Pilot run {config['run_id']}",
        "",
        f"backend `{config['backend']}`, effort `{config.get('effort')}`, rounds {r}, repeats {config['repeats']}, "
        f"{config['tasks']} tasks, SKILL.md sha256 `{config['skill_sha256'][:12]}`",
        "",
        f"| arm | episodes | Success@1 (95% CI) | Success@{r} (95% CI) | compile fail @1 | mean rounds | output tokens |",
        "|---|---|---|---|---|---|---|",
    ]
    for arm, s in summary.items():
        lo1, hi1 = s["success_at_1_ci95"]
        lof, hif = s[f"success_at_{r}_ci95"]
        lines.append(
            f"| {arm} | {s['episodes']} | {s['success_at_1']} ({s['success_at_1_rate']:.0%}, {lo1:.0%}–{hi1:.0%}) | "
            f"{s[f'success_at_{r}']} ({s[f'success_at_{r}_rate']:.0%}, {lof:.0%}–{hif:.0%}) | "
            f"{s['first_round_compile_fail']} | {s['mean_rounds']:.2f} | {s['usage'].get('output_tokens', 0)} |"
        )
    for arm, s in summary.items():
        lines += ["", f"## {arm}", "", f"- failed tasks: {', '.join(s['failed_tasks']) or 'none'}"]
        if s["failure_codes"]:
            lines.append("- codes on failing rounds: " + ", ".join(f"`{c}` ×{n}" for c, n in s["failure_codes"]))
        if s["api_errors"] or s["refusals"] or s["fallback_rounds"]:
            lines.append(f"- api errors {s['api_errors']}, refusals {s['refusals']}, rounds served by a fallback model {s['fallback_rounds']}")
    return "\n".join(lines) + "\n"


# ---------------------------------------------------------------------------------------------- main


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--backend", choices=("anthropic", "claude-cli", "oracle"), default="anthropic")
    ap.add_argument("--claude-bin", default="claude", help="claude-cli で使う claude コマンド")
    ap.add_argument("--model", default="claude-opus-5-5")
    ap.add_argument("--effort", default="high", choices=("low", "medium", "high", "xhigh", "max"))
    ap.add_argument("--max-tokens", type=int, default=32000)
    ap.add_argument("--no-fallback", action="store_true", help="安全分類器による拒否時のフォールバックを使わない")
    ap.add_argument("--arms", default="lptl,python", help=f"カンマ区切り（{', '.join(ARMS)}）")
    ap.add_argument("--tasks", default="", help="カンマ区切りのタスク ID または名前（既定は全件）")
    ap.add_argument("--rounds", type=int, default=3, help="初回を含む最大の回数（1 なら修復なし）")
    ap.add_argument("--repeats", type=int, default=1)
    ap.add_argument("--workers", type=int, default=4)
    ap.add_argument("--out", default=str(EVAL / "runs"))
    args = ap.parse_args()

    arms = [a for a in args.arms.split(",") if a]
    if bad := [a for a in arms if a not in ARMS]:
        ap.error(f"unknown arm: {bad}")
    tasks = load_tasks([t for t in args.tasks.split(",") if t])
    if not tasks:
        ap.error("no tasks selected")
    if args.backend == "oracle":
        backend = OracleBackend()
    elif args.backend == "claude-cli":
        backend = ClaudeCliBackend(args.model, args.effort, args.claude_bin)
    else:
        backend = AnthropicBackend(args.model, args.effort, args.max_tokens, not args.no_fallback)

    run_id = dt.datetime.now(dt.timezone.utc).strftime("%Y%m%dT%H%M%SZ") + f"-{args.backend}"
    out = Path(args.out) / run_id
    out.mkdir(parents=True)
    config = {
        "run_id": run_id,
        "backend": backend.name,
        "effort": args.effort if args.backend != "oracle" else None,
        "fallback": args.backend == "anthropic" and not args.no_fallback,
        "arms": arms,
        "rounds": args.rounds,
        "repeats": args.repeats,
        "tasks": len(tasks),
        "task_ids": [t["id"] for t in tasks],
        "skill_sha256": hashlib.sha256(SKILL.encode()).hexdigest(),
        "manifest": json.loads((EVAL / "manifest.json").read_text(encoding="utf-8")).get("task_set_sha256"),
    }
    (out / "config.json").write_text(json.dumps(config, indent=2) + "\n", encoding="utf-8")

    jobs = [(t, a, r) for r in range(1, args.repeats + 1) for a in arms for t in tasks]
    lock = threading.Lock()
    episodes = []
    with open(out / "episodes.jsonl", "w", encoding="utf-8") as f, ThreadPoolExecutor(args.workers) as pool:
        for ep in pool.map(lambda j: episode(backend, j[0], j[1], args.rounds, j[2]), jobs):
            with lock:
                episodes.append(ep)
                f.write(json.dumps(ep, ensure_ascii=False) + "\n")
                f.flush()
                mark = "ok " if ep["success_final"] else "NG "
                print(f"{mark}{ep['arm']:<12} {ep['task']:<24} rounds={ep['rounds_used']}", file=sys.stderr)
    summary = summarize(episodes, args.rounds)
    (out / "summary.json").write_text(json.dumps(summary, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")
    md = summary_markdown(summary, config)
    (out / "summary.md").write_text(md, encoding="utf-8")
    print(md)
    print(f"results: {out}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
