"""LLM 評価のハーネス（設計書 §12 の Surface モードと Repair モード、evaluation-protocol-v1 草案の決定に依らない規則）。

各タスクについて、モデルに解答を書かせ、公開例で検査し、失敗すれば診断や失敗例を返して直させる。最終候補は
草案 §3 の規則で一件だけ選ぶ：予算内に検証され、compile（AST の arm は compile_ast）で受理された最後の候補。
隠しテストの結果は候補ごとに記録するが、選択にも修復にも使わない。受理された候補がなければ失敗。

arm:
  lptl          SKILL.md を system に置き、LPTL で書かせる。修復時は tlvm の診断（--human）を返す
  lptl-nodiag   修復時は「拒否された」とだけ返す（診断の効果を見る対照）
  lptl-msg      修復時は診断の message だけを返す（span、コード、修復ヒントなし）
  lptl-code     修復時は診断のコードだけを返す
  lptl-span     修復時は span（行と列）と expected、found だけを返す
  lptl-noskill  SKILL.md を system に置かない（課題文と公開例は同じ）。修復時は lptl と同じ
  lptl-nolet    let のない言語：SKILL-nolet.md を置き、let を含むプログラムを拒否する（診断 NoLet）
  python        Python の solve(x) を書かせる（同じタスク・同じ公開例・同じ隠しテスト）
  ast           ast_codec_v1 の AST を JSON で書かせ、tlvm の compile_ast で検査する（制約なし）
  ast-schema    ast と同じだが、CLI の --json-schema で ast_codec_v1 の schema を渡す（claude-cli だけ）
  render        正解の AST（tlvm ast の JSON）を示し、同じ AST になる LPTL を一回だけ書かせる（AST 一致で採点）
  gen-render    連結 arm。lptl で一回生成し、その AST を render へ渡す。render とは別の行に報告する

backend:
  anthropic    Claude API（ANTHROPIC_API_KEY などの認証が必要）
  claude-cli   Claude Code の CLI（claude -p）。サブスクリプションでログインした claude があれば API キーは不要
  oracle       参照解をそのまま返す（API を使わずにハーネスを空回しして検査する）

usage:
  python3 eval/harness.py --backend oracle
  python3 eval/harness.py --model claude-opus-5-5 --arms lptl,python --repeats 1 --rounds 3
  python3 eval/harness.py --backend claude-cli --arms lptl,python
  python3 eval/harness.py --protocol CONFIG.json --backend claude-cli --model MODEL --effort EFFORT --arms lptl,python

--protocol を付けない実行は予備実験で、予算 B を使わず --rounds 回で止める。LPTL が LLM に有利かどうかを主張する
材料にはしない。--protocol の実行は事前登録の設定（反復数 K、予算 B など。既定値なし）を読み、欠けていれば止まる。
"""

from __future__ import annotations

import argparse
import datetime as dt
import hashlib
import json
import os
import re
import subprocess
import sys
import tempfile
import threading
from collections import Counter
from concurrent.futures import ThreadPoolExecutor
from dataclasses import dataclass
from pathlib import Path

from lptl_types import lptl_literal, parse_type, python_literal
from protocol import (BYTES_PER_TOKEN, CLI_ERROR_SUBTYPES, PUBLISHABLE, PYTHON_REJECTION_PHASE, Budget, BackendError,
                      BudgetMeter, Outcome, ProtocolConfigError, budget_end, classify_backend_error, classify_run,
                      episode_outcome, load_protocol_config)
from runner import find_let, nolet_rejection, run_ast, run_lptl, run_python
from stats import (BOOTSTRAP_LEVEL, BOOTSTRAP_RESAMPLES, RegistryError, bootstrap_seed, difference, interval,
                   load_registry, paired_bootstrap, primary_comparisons, task_scores, wilson)
from tasks_lib import EVAL, HIDDEN_SEED_ENV, SecretSeedMissing, load_secret_tasks, load_tasks

REPO = EVAL.parent
SKILL = (EVAL / "SKILL.md").read_text(encoding="utf-8")
SKILL_NOLET = (EVAL / "SKILL-nolet.md").read_text(encoding="utf-8")
AST_OUTPUT = (EVAL / "ast_output.md").read_text(encoding="utf-8")
AST_SCHEMA_PATH = REPO / "spec" / "lptl-v1" / "ast_codec_v1.schema.json"
# CLI の --json-schema とプロンプトに渡す ast_codec_v1 の schema（ファイルの内容そのものを詰めて書いたもの）
AST_SCHEMA = json.dumps(json.loads(AST_SCHEMA_PATH.read_text(encoding="utf-8")), ensure_ascii=False, separators=(",", ":"))

PYTHON_SYSTEM = """You write Python 3 solutions to small programming tasks.

Define a function `solve(x)` that takes the single input value and returns the result. Values are represented as
follows: integers are `int`, booleans are `bool`, lists are `list`, `pair(a, b)` is the tuple `(a, b)`, `some(v)` is
just `v`, and `none` is `None`. Use only the standard library and do not read input or print output.

Answer with the complete solution in a single fenced code block tagged `python`."""

OUTPUT_FORMAT_HEADING = "## Output format\n"


def split_output_format(skill: str) -> tuple[str, str]:
    """SKILL を、出力形式の節より前の本文と、出力形式の節の本文に分ける。"""
    i = skill.index("\n" + OUTPUT_FORMAT_HEADING)
    return skill[:i].rstrip() + "\n", skill[i + 1 + len(OUTPUT_FORMAT_HEADING):].strip()


SKILL_BODY, SKILL_OUTPUT_FORMAT = split_output_format(SKILL)
# lptl-noskill：言語の説明を置かず、名前と出力形式だけを伝える
NOSKILL_SYSTEM = "You write programs in Tolvemi (LPTL), a small programming language.\n\n" + SKILL_OUTPUT_FORMAT + "\n"
AST_ANSWER = {
    "ast": "Answer with the JSON object in a single fenced code block tagged `json`.",
    "ast-schema": "Give the JSON object as your structured output; it must match the schema below.",
}


def ast_system(arm: str) -> str:
    """AST の arm の system：SKILL の本文（言語の意味）と、AST を JSON で書く出力形式（schema を含む）。"""
    fmt = AST_OUTPUT.replace("{{AST_ANSWER}}", AST_ANSWER[arm]).replace("{{AST_CODEC_V1_SCHEMA}}", AST_SCHEMA)
    return SKILL_BODY + "\n" + fmt


@dataclass(frozen=True)
class Arm:
    """生成と修復の arm。lang は候補の形（tlvm、ast、python）、feedback は修復時に返す診断の形（草案 §2a）。"""

    name: str
    lang: str
    system: str
    feedback: str  # human | none | message | code | span
    nolet: bool = False
    schema: str | None = None  # CLI の --json-schema に渡す schema


ARM_SPECS = {a.name: a for a in (
    Arm("lptl", "tlvm", SKILL, "human"),
    Arm("lptl-nodiag", "tlvm", SKILL, "none"),
    Arm("lptl-msg", "tlvm", SKILL, "message"),
    Arm("lptl-code", "tlvm", SKILL, "code"),
    Arm("lptl-span", "tlvm", SKILL, "span"),
    Arm("lptl-noskill", "tlvm", NOSKILL_SYSTEM, "human"),
    Arm("lptl-nolet", "tlvm", SKILL_NOLET, "human", nolet=True),
    Arm("python", "python", PYTHON_SYSTEM, "human"),
    Arm("ast", "ast", ast_system("ast"), "human"),
    Arm("ast-schema", "ast", ast_system("ast-schema"), "human", schema=AST_SCHEMA),
)}
ARMS = (*ARM_SPECS, "render", "gen-render")
# 草案 §2 の arm のうち、オーナーの決定がないと定義できないもの（実装しない）
NOT_IMPLEMENTED = {
    "python-restricted": "§2b の制限の定義（再帰・while・副作用と I/O・標準ライブラリのどれを禁じるか）と ast の検査コード",
    "lptl-nolist-builtins": "除く組込みの集合（cons、concat、reverse で確定か）と、それで書ける共通課題の集合と、組込みを除いた SKILL",
    "notation": "別表記の定義（字句・構文）と正準形への変換",
}
SELECTION_RULE = ("§3: the final candidate is the last one accepted by compile (compile_ast for AST arms) within budget B; "
                  "hidden-test results are recorded per candidate and never used to choose. No accepted candidate, or B "
                  "exceeded: failure.")
VERIFICATION_RULE = ("Visible verification calls (§5, design §12.5): 1 per candidate for compile, then 2 per public example "
                     "(decode_input and run) when the candidate is accepted. Hidden tests are outside B.")


def let_free_tasks(tasks: list[dict]) -> list[str]:
    """参照解（reference.tlvm）が let を使わない課題（v1 ／ v1-no-let の共通課題。草案 §2）。"""
    return [t["id"] for t in tasks if find_let((t["dir"] / "reference.tlvm").read_text(encoding="utf-8")) is None]


# ---------------------------------------------------------------------------------------------- prompts


def render_examples(task: dict, lang: str) -> str:
    tin, tout = parse_type(task["input_type"]), parse_type(task["output_type"])
    lines = []
    for e in task["examples"]:
        if lang == "python":
            lines.append(f"solve({python_literal(e['input'], tin)}) == {python_literal(e['expected'], tout)}")
        else:
            lines.append(f"solve({lptl_literal(e['input'], tin)}) = {lptl_literal(e['expected'], tout)}")
    return "\n".join(lines)


def _lang(arm) -> str:
    if isinstance(arm, Arm):
        return arm.lang
    return ARM_SPECS[arm].lang if arm in ARM_SPECS else "tlvm"


def task_prompt(task: dict, arm) -> str:
    """課題文（全 arm で同じ。Python だけ署名と例を Python で書く）。"""
    lang = _lang(arm)
    if lang == "python":
        sig = f"def solve(x)  # x: {task['input_type']}, returns {task['output_type']}"
        tag = "python"
    else:
        sig = f"fn solve(x: {task['input_type']}) -> {task['output_type']}\nentry solve"
        tag = "tlvm"
    return (
        f"Task: {task['title']}\n\n{task['prompt']}\n\n"
        f"Signature (the parameter name is up to you):\n```{tag}\n{sig}\n```\n\n"
        f"Examples:\n```\n{render_examples(task, lang)}\n```"
    )


REPAIR = "Fix it and answer with the complete corrected program."
NO_CODE = "No fenced code block was found in the answer."


def _span_text(e: dict) -> str:
    if "start" not in e:
        place = "(no position)"
    else:
        (l1, c1), (l2, c2) = e["start"], e["end"]
        place = f"{l1}:{c1}-{l2}:{c2}"
    parts = [f"expected {e['expected']}"] if e.get("expected") is not None else []
    if e.get("found") is not None:
        parts.append(f"found {e['found']}")
    return place + (": " + ", ".join(parts) if parts else "")


def rejection_feedback(arm: Arm, r: dict) -> str:
    """受理されなかった候補への文面（草案 §2a）。"""
    if r.get("no_code"):
        return f"{NO_CODE} {REPAIR}"
    if arm.feedback == "human":
        what = "Python interpreter" if arm.lang == "python" else "checker"
        return f"The {what} rejected the program:\n```\n{r['diagnostics']}\n```\n{REPAIR}"
    errors = r.get("errors") or []
    if arm.feedback == "message" and (msgs := [e["message"] for e in errors if e.get("message")]):
        return "The checker rejected the program:\n```\n" + "\n".join(msgs) + f"\n```\n{REPAIR}"
    if arm.feedback == "code" and (codes := list(dict.fromkeys(e["code"] for e in errors))):
        return "The checker rejected the program with these diagnostic codes:\n```\n" + "\n".join(codes) + f"\n```\n{REPAIR}"
    if arm.feedback == "span" and errors:
        return "The checker rejected the program at these places:\n```\n" + "\n".join(map(_span_text, errors)) + f"\n```\n{REPAIR}"
    return f"The program was rejected by the checker. {REPAIR}"


def examples_feedback(arm: Arm, task: dict, r: dict, visible: list[dict]) -> str:
    """受理されたが公開例に失敗した候補への文面。どの arm でも同じ形（Python だけ値を Python で書く）。"""
    tin, tout = parse_type(task["input_type"]), parse_type(task["output_type"])
    lit = python_literal if arm.lang == "python" else lptl_literal
    by_name = {c["name"]: c for c in visible}
    lines = []
    for c in r["cases"]:
        if c["result"] == "pass":
            continue
        case = by_name[c["name"]]
        got = c["reason"] if c["result"] == "error" else lit(c["actual"], tout)
        lines.append(f"solve({lit(case['input'], tin)}): expected {lit(case['expected'], tout)}, got {got}")
    if not lines:  # Python の時間切れや処理系の異常終了
        lines.append(r.get("diagnostics") or "the examples did not finish")
    return "Some examples fail:\n```\n" + "\n".join(lines) + f"\n```\n{REPAIR}"


def extract_code(text: str, lang: str) -> str | None:
    tags = {"python": ("python", "py"), "ast": ("json",)}.get(lang, ("tlvm", "lptl", "tolvemi"))
    blocks = re.findall(r"```([A-Za-z0-9_-]*)[^\n]*\n(.*?)```", text, re.S)
    tagged = [b for t, b in blocks if t.lower() in tags]
    if tagged:
        return tagged[-1]
    return blocks[-1][1] if blocks else None


def _content_bytes(content) -> int:
    if isinstance(content, str):
        return len(content.encode())
    total = 0
    for b in content or []:
        for attr in ("text", "thinking"):
            v = getattr(b, attr, None) if not isinstance(b, dict) else b.get(attr)
            if isinstance(v, str):
                total += len(v.encode())
    return total


def prompt_bytes(system: str, messages: list[dict]) -> int:
    """要求の入力の大きさ（system と会話の本文の bytes）。予算の入力 tokens の見積りに使う。"""
    return len(system.encode()) + sum(_content_bytes(m["content"]) for m in messages)


# ---------------------------------------------------------------------------------------------- backends


def _response(text: str, usage: dict, model: str, stop_reason: str = "end_turn", structured=None) -> dict:
    return {"text": text, "content": text, "stop_reason": stop_reason, "usage": usage, "model": model,
            "fallback": False, "requests": 1, "structured": structured}


class OracleBackend:
    """参照解を返す。ハーネスと採点の経路を API なしで確かめるためのもの。AST の arm には参照解の tlvm ast を返す。"""

    name = "oracle"

    def complete(self, system: str, messages: list[dict], task: dict, arm: str, schema=None, max_output=None) -> dict:
        usage = {"input_tokens": 0, "output_tokens": 0}
        lang = _lang(arm)
        if lang == "ast":
            got = run_ast((task["dir"] / "reference.tlvm").read_text(encoding="utf-8"))
            if not got["ok"]:
                raise BackendError("backend-other", f"{task['id']}: reference.tlvm is not accepted by tlvm ast")
            text = json.dumps(got["ast"], ensure_ascii=False)
            if schema is not None:
                return _response(text, usage, "oracle", structured=got["ast"])
            return _response(f"```json\n{text}\n```", usage, "oracle")
        f, tag = ("reference.py", "python") if lang == "python" else ("reference.tlvm", "tlvm")
        code = (task["dir"] / f).read_text(encoding="utf-8")
        return _response(f"```{tag}\n{code}```", usage, "oracle")


class AnthropicBackend:
    def __init__(self, model: str, effort: str, max_tokens: int, fallback: bool):
        import anthropic

        self.client = anthropic.Anthropic()
        self.model, self.effort, self.max_tokens, self.fallback = model, effort, max_tokens, fallback
        self.name = f"anthropic:{model}"

    def complete(self, system: str, messages: list[dict], task: dict, arm: str, schema=None, max_output=None) -> dict:
        if schema is not None:
            # API の structured outputs は再帰する schema を扱えない。ast-schema は claude-cli で回す
            raise RuntimeError("ast-schema needs the claude-cli backend")
        # 予算 B の出力 tokens の残りを、この要求の最大出力にする（超えれば途中で切れ、その候補は受理しない）
        max_tokens = self.max_tokens if max_output is None else max(1, min(self.max_tokens, max_output))
        kwargs = dict(
            model=self.model,
            max_tokens=max_tokens,
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
            "requests": 1,
            "structured": None,
        }


class ClaudeCliBackend:
    """Claude Code の CLI を非対話（claude -p）で呼ぶ。サブスクリプションのログインで動き、API キーは要らない。

    ツールをすべて無効にし、設定・MCP・CLAUDE.md を読まず、空の一時ディレクトリで動かすので、モデルは
    リポジトリ（参照解や隠しテスト）を見られない。CLI は呼び出しごとに 1 往復なので、修復の回では
    それまでの会話を 1 つのプロンプトに書き起こして渡す（思考ブロックは引き継がれない）。
    Claude Code が system prompt の前後に短い定型文を足すことがあり、API の arm と完全には同じ条件ではない。
    schema を渡すと --json-schema で構造化出力を求める（CLI の中で検証と再試行があり、その要求も num_turns に入る）。
    """

    def __init__(self, model: str, effort: str, binary: str = "claude", timeout: float = 300, retries: int = 2):
        self.model, self.effort, self.binary, self.timeout, self.retries = model, effort, binary, timeout, retries
        self.name = f"claude-cli:{model}"
        self.workdir = tempfile.mkdtemp(prefix="lptl-eval-")

    @staticmethod
    def render(messages: list[dict]) -> str:
        if len(messages) == 1:
            return messages[0]["content"]
        turns = "\n\n".join(f'<turn role="{m["role"]}">\n{m["content"]}\n</turn>' for m in messages)
        return ("This is a continuing conversation. The earlier turns are reproduced below; your own earlier answers "
                "are the assistant turns. Reply to the last user turn.\n\n" + turns)

    def complete(self, system: str, messages: list[dict], task: dict, arm: str, schema=None, max_output=None) -> dict:
        # max_output は使えない（CLI に最大出力のオプションがない。草案 §8）。出力 tokens は事後に数える
        cmd = [self.binary, "-p", "--system-prompt", system, "--tools", "", "--output-format", "json",
               "--no-session-persistence", "--strict-mcp-config", "--setting-sources", "",
               "--model", self.model, "--effort", self.effort]
        if schema is not None:
            cmd += ["--json-schema", schema]
        env = {k: v for k, v in os.environ.items() if k not in ("CLAUDE_CODE_SESSION_ID", "CLAUDECODE")}
        # 予備実験では、混雑で応答が止まることがあるので時間切れを retries 回まで呼び直す（protocol の実行では 0 回）
        for attempt in range(self.retries + 1):
            try:
                p = subprocess.run(cmd, input=self.render(messages), capture_output=True, text=True, cwd=self.workdir,
                                   env=env, timeout=self.timeout)
                break
            except subprocess.TimeoutExpired:
                if attempt == self.retries:
                    raise
        try:
            out = json.loads(p.stdout)
        except json.JSONDecodeError:
            raise BackendError("cli-output", f"claude exited {p.returncode}: {(p.stderr or p.stdout).strip()[:500]}") from None
        if not isinstance(out, dict):
            raise BackendError("cli-output", f"claude printed {type(out).__name__}, not an object")
        usage, turns = out.get("usage"), out.get("num_turns")
        if out.get("is_error"):
            kind = CLI_ERROR_SUBTYPES.get(out.get("subtype"), "cli-unknown")
            raise BackendError(kind, f"{out.get('subtype')}: {str(out.get('result'))[:500]}", usage=usage, requests=turns)
        structured = None
        if schema is not None:
            structured = out.get("structured_output")
            if not isinstance(structured, dict):
                raise BackendError("cli-output", "no structured_output in the result", usage=usage, requests=turns)
        u = usage if isinstance(usage, dict) else {}
        mu = out.get("modelUsage") or {}
        # Claude Code は補助の処理に Haiku を使うことがある。評価するモデルが Haiku でなければ、それを除いて記録する
        aux = "haiku" not in self.model
        models = [m for m in mu if not (aux and "haiku" in m)] or [self.model]
        text = out.get("result") or ""
        if structured is not None:
            text = json.dumps(structured, ensure_ascii=False)
        return {
            "text": text,
            "content": text,
            "stop_reason": out.get("stop_reason") or "end_turn",
            "usage": usage,
            "model": ",".join(models),
            "fallback": any(e.get("type") == "fallback_message" for e in (u.get("iterations") or [])),
            "requests": turns,
            "structured": structured,
            "cost_usd": out.get("total_cost_usd"),
            "duration_ms": out.get("duration_ms"),
        }


# ---------------------------------------------------------------------------------------------- candidates


def _python_phase(r: dict) -> str:
    if r["diagnostics"].startswith("solution.py does not define"):
        return "entry"
    return PYTHON_REJECTION_PHASE.get((r["codes"] or [""])[0], "other")


def check_candidate(arm: Arm, task: dict, code: str, cases: list[dict], run_cases: bool = True) -> dict:
    """候補を検査し、run_cases なら cases を走らせる。返す dict は runner.run_lptl と同じ形。

    受理（accepted）は、検査を通り entry の署名が合うこと。Python では読み込めて solve があること。"""
    tin, tout = task["input_type"], task["output_type"]
    if arm.lang == "python":
        load = run_python(code, [], tin, tout)
        r = {"compile_ok": load["compile_ok"], "signature_ok": load["signature_ok"], "diagnostics": load["diagnostics"],
             "codes": load["codes"], "errors": [], "phase": None, "cases": [], "all_pass": False, "infra": None}
        if not load["compile_ok"]:
            return {**r, "phase": _python_phase(load)}
        if not run_cases:
            return r
        run = run_python(code, cases, tin, tout)
        # 読み込めた候補が例の実行中に処理系ごと落ちたもの（Crash）は、受理のまま失敗として扱う
        return {**r, "codes": run["codes"], "cases": run["cases"], "diagnostics": run["diagnostics"],
                "all_pass": run["compile_ok"] and run["all_pass"]}
    if arm.nolet and (i := find_let(code)) is not None:
        return nolet_rejection(code, i)
    filename = "solution.json" if arm.lang == "ast" else "solution.tlvm"
    return run_lptl(code, cases, tin, tout, filename=filename, run_cases=run_cases)


def accepted(r: dict) -> bool:
    return bool(r["compile_ok"] and r["signature_ok"] and not r.get("infra"))


def verify(arm: Arm, task: dict, code: str, visible: list[dict], meter: BudgetMeter) -> tuple[dict, int, bool]:
    """予算の中で候補を検証する。返すのは (結果, 可視検証の呼び出し回数, 公開例を走らせたか)。

    公開例まで走らせる余地（1 + 2n 回）がなければ、受理の検査（1 回）だけをする。"""
    full = 1 + 2 * len(visible)
    if meter.guard_verification(full) is None:
        r = check_candidate(arm, task, code, visible)
        ok = accepted(r)
        calls, ran = (full, True) if ok else (1, False)
    else:
        r = check_candidate(arm, task, code, visible, run_cases=False)
        calls, ran = 1, False
    meter.record_verification(calls)
    return r, calls, ran


def hidden_result(arm: Arm, task: dict, code: str) -> dict:
    """受理された候補を隠しテストで走らせ、記録だけする（予算 B の外。選択にも修復にも使わない）。"""
    h = check_candidate(arm, task, code, task["hidden"])
    outcome, detail = classify_run(h, "python" if arm.lang == "python" else "tlvm")
    return {"hidden_pass": outcome is Outcome.SUCCESS, "hidden_outcome": outcome.value, "hidden_detail": detail,
            "hidden_passed": sum(c["result"] == "pass" for c in h["cases"]), "hidden_total": len(task["hidden"])}


def _request(backend, arm_name: str, system: str, messages: list[dict], task: dict, meter: BudgetMeter, k: int,
             schema=None) -> tuple[dict | None, dict, tuple[str, str] | None]:
    """要求を一つ出す。返すのは (応答, その回の記録, 止める理由)。止める理由があれば応答は None のこともある。"""
    n_bytes = prompt_bytes(system, messages)
    est = meter.estimate_input(n_bytes)
    if guard := meter.guard_request(est):
        return None, {}, guard
    log = {"round": k, "estimated_input": est}
    try:
        resp = backend.complete(system, messages, task, arm_name, schema=schema, max_output=meter.remaining("output_tokens"))
    except Exception as e:  # noqa: BLE001 - backend の失敗は固定の表で分類し、episode をそこで止める（再試行しない）
        outcome, kind = classify_backend_error(e)
        usage = getattr(e, "usage", None)
        if usage is not None:
            meter.record_request(usage, getattr(e, "requests", None) or 1, n_bytes)
        else:
            meter.used["requests"] += 1
            if outcome is Outcome.GENERATION_FAILURE:
                meter.invalid.append("usage")  # 生成の失敗の tokens を数えられない：予算内と認めない
        log.update(api_error=f"{type(e).__name__}: {e}", error_kind=kind, usage=usage)
        return None, log, ("generation_failure" if outcome is Outcome.GENERATION_FAILURE else "infra_fault", kind)
    meter.record_request(resp["usage"], resp.get("requests", 1), n_bytes)
    log.update(stop_reason=resp["stop_reason"], model=resp["model"], fallback=resp["fallback"], usage=resp["usage"],
               requests=resp.get("requests", 1), answer=resp["text"])
    for key in ("cost_usd", "duration_ms"):
        if resp.get(key) is not None:
            log[key] = resp[key]
    if over := meter.exceeded():
        return resp, log, ("budget_exceeded", ",".join(over))
    if resp["stop_reason"] == "refusal":
        return resp, log, ("generation_failure", "refusal")
    if resp["stop_reason"] == "max_tokens":
        return resp, log, ("generation_failure", "truncated")
    return resp, log, None


def _candidate(log: dict, r: dict | None, has_code: bool, codes: list[str] | None = None) -> dict:
    """その回の候補の記録。r は検査の結果（検査しなかった回は None）。"""
    ok = r is not None and accepted(r)
    if codes is None:
        codes = r["codes"] if r else ["NoCode"]
    log.update(has_code=has_code, accepted=ok, compile_ok=bool(r and r["compile_ok"]),
               signature_ok=bool(r and r["signature_ok"]), codes=codes,
               phase=None if ok else (r.get("phase") if r else None))
    log.setdefault("hidden_pass", False)
    return log


def surface_episode(backend, task: dict, arm: Arm, rep: int, max_rounds: int | None, meter: BudgetMeter) -> dict:
    """生成と修復の episode。max_rounds が None なら予算 B だけで止まる（protocol の実行）。"""
    visible = [{"name": f"ex{i + 1}", **e} for i, e in enumerate(task["examples"])]
    messages = [{"role": "user", "content": task_prompt(task, arm)}]
    log: list[dict] = []
    stop = ("normal_stop", "")
    k = 0
    while max_rounds is None or k < max_rounds:
        k += 1
        resp, entry, halt = _request(backend, arm.name, arm.system, messages, task, meter, k, schema=arm.schema)
        if entry:
            log.append(entry)
        if resp is None or halt:
            stop = halt
            if resp is not None:
                _candidate(entry, None, False, codes=[])  # 予算超過・拒否・途中切れの回の出力は候補にしない
            break
        if resp.get("structured") is not None:
            code = json.dumps(resp["structured"], ensure_ascii=False)
        else:
            code = extract_code(resp["text"], arm.lang)
        entry["code"] = code
        if code is None:
            _candidate(entry, None, False)
            entry.update(verification_calls=0, feedback=rejection_feedback(arm, {"no_code": True}))
        else:
            r, calls, ran = verify(arm, task, code, visible, meter)
            _candidate(entry, r, True)
            entry.update(verification_calls=calls, visible_checked=ran, visible_pass=ran and r["all_pass"])
            if r.get("infra"):
                entry["infra"] = r["infra"]
                stop = ("infra_fault", r["infra"])
                break
            if entry["accepted"]:
                entry.update(hidden_result(arm, task, code))
                if not ran:
                    stop = ("operation_guarded", "verification_calls")  # 受理されたが公開例を走らせる余地がない
                    break
                if r["all_pass"]:
                    break
                entry["feedback"] = examples_feedback(arm, task, r, visible)
            else:
                entry["feedback"] = rejection_feedback(arm, r)
        messages.append({"role": "assistant", "content": resp["content"]})
        messages.append({"role": "user", "content": entry["feedback"]})
    return finish(task, arm.name, rep, log, stop, meter)


def finish(task: dict, arm: str, rep: int, log: list[dict], stop: tuple[str, str], meter: BudgetMeter,
           extra: dict | None = None) -> dict:
    """§3 の選択と §5 の予算終了を当て、episode の記録を作る。"""
    candidates = [r for r in log if "api_error" not in r]
    limit = meter.budget.vector() if meter.budget else None
    end = budget_end(None if meter.invalid else meter.observed(), limit, stop[0], candidates)
    final = candidates[end["selected"]] if end["selected"] is not None else None
    final_hidden = (Outcome(final["hidden_outcome"]), final["hidden_detail"]) if final and "hidden_outcome" in final else None
    last = {"has_code": candidates[-1]["has_code"], "phase": candidates[-1]["phase"]} if candidates else None
    outcome, detail = episode_outcome(end, final_hidden, stop[0], stop[1], last)
    first = candidates[0] if candidates else None
    return {
        "episode_id": f"{arm}/{task['id']}/r{rep}",
        "task": task["id"],
        "category": task.get("category"),
        "arm": arm,
        "repeat": rep,
        # 主指標（§3）：選んだ最終候補が隠しテストを全て通し、予算内であること
        "success_selected": outcome is Outcome.SUCCESS,
        "selected_round": final["round"] if final else None,
        "outcome": outcome.value,
        "outcome_detail": detail,
        "stop": {"reason": stop[0], "detail": stop[1]},
        "budget": {**meter.snapshot(), "end": end["reason"], "budget_ok": end["budget_ok"]},
        # 二次指標：初回の候補の隠しテスト、最後の回の候補の隠しテスト（旧 success_final）
        "success_at_1": bool(first and first["round"] == 1 and first.get("hidden_pass")),
        "hidden_last_round": bool(candidates and candidates[-1].get("hidden_pass")),
        "rounds_used": len(candidates),
        "api_error": next((r["api_error"] for r in log if "api_error" in r), None),
        **(extra or {}),
        "rounds": log,
    }


# ---------------------------------------------------------------------------------------------- render と連結 arm（§12.3）


def render_prompt(ast_obj) -> str:
    return (
        "Write an LPTL program whose abstract syntax tree is exactly the AST below. Keep every type annotation, binder, "
        "name and declaration order, and do not change the meaning. Answer with the complete program in a single fenced "
        "code block tagged `tlvm`.\n\n"
        f"AST (JSON):\n```json\n{json.dumps(ast_obj, ensure_ascii=False, indent=1)}\n```"
    )


def render_round(backend, task: dict, arm: str, ast_obj, ref_ast, meter: BudgetMeter, k: int) -> tuple[list[dict], tuple]:
    """Render を一回だけ書かせ、書かれた program の AST が ref_ast と一致するかで採点する。
    受理は tlvm ast が通ること（可視検証 1 回）。AST 一致を hidden_pass に入れる。"""
    messages = [{"role": "user", "content": render_prompt(ast_obj)}]
    resp, entry, halt = _request(backend, "render", SKILL, messages, task, meter, k)
    if resp is None or halt:
        if resp is not None:
            _candidate(entry, None, False, codes=[])
        return ([entry] if entry else []), halt
    code = extract_code(resp["text"], "tlvm")
    entry["code"] = code
    if code is None:
        _candidate(entry, None, False)
        return [entry], ("normal_stop", "")
    if meter.guard_verification(1):
        _candidate(entry, None, True)
        return [entry], ("operation_guarded", "verification_calls")
    meter.record_verification(1)
    got = run_ast(code)
    r = {"compile_ok": got["ok"], "signature_ok": got["ok"], "codes": [], "phase": got["phase"], "infra": None}
    _candidate(entry, r, True)
    match = got["ok"] and got["ast"] == ref_ast
    entry.update(verification_calls=1, diagnostics=got["diagnostics"], ast_match=match, visible_pass=match,
                 hidden_pass=match)
    if got["ok"]:
        entry.update(hidden_outcome=(Outcome.SUCCESS if match else Outcome.WRONG_ANSWER).value,
                     hidden_detail="" if match else "ast-mismatch")
    return [entry], ("normal_stop", "")


def episode(backend, task: dict, arm: str, rounds: int | None, rep: int, budget: Budget | None = None) -> dict:
    """一つの episode。budget が None なら予算なし（予備実験）、rounds が None なら予算だけで止まる。"""
    meter = BudgetMeter(budget)
    if arm == "render":
        # Render の入力は正解 AST。一回だけ書かせるので rounds は使わない
        ref = run_ast((task["dir"] / "reference.tlvm").read_text(encoding="utf-8"))
        if not ref["ok"]:
            raise RuntimeError(f"{task['id']}: 参照解が tlvm ast で受理されない: {ref['diagnostics']}")
        log, stop = render_round(backend, task, "render", ref["ast"], ref["ast"], meter, 1)
        return finish(task, "render", rep, log, stop, meter)
    if arm == "gen-render":
        return gen_render_episode(backend, task, rep, meter)
    return surface_episode(backend, task, ARM_SPECS[arm], rep, rounds, meter)


def gen_render_episode(backend, task: dict, rep: int, meter: BudgetMeter) -> dict:
    """連結 arm（gen-render）：lptl で一回だけ生成し（修復なし）、その AST を render へ渡す。予算は二段で一つ。
    採点は render の出力の AST が生成された AST と一致するか。生成の隠しテストの結果は generation_hidden_pass に残す。"""
    gen = surface_episode(backend, task, ARM_SPECS["lptl"], rep, 1, meter)
    calls = gen["rounds"]
    first = next((r for r in calls if "api_error" not in r), None)
    extra = {"generation_hidden_pass": bool(first and first.get("hidden_pass")), "generation_outcome": gen["outcome"]}
    for r in calls:
        # 生成の回は gen-render の候補にしない（候補は render の出力で、採点は AST の一致）。生成が受理されたのに
        # render へ進めなかったときは、gen-render の候補がない（拒否された生成は、その段階を残す）
        if r.get("accepted"):
            r["has_code"] = False
        r.update(accepted=False, hidden_pass=False)
    if first is None or first.get("code") is None or gen["stop"]["reason"] != "normal_stop":
        return finish(task, "gen-render", rep, calls, (gen["stop"]["reason"], gen["stop"]["detail"]), meter, extra)
    got = run_ast(first["code"])
    if not got["ok"]:
        return finish(task, "gen-render", rep, calls, ("normal_stop", ""), meter, extra)
    log, stop = render_round(backend, task, "gen-render", got["ast"], got["ast"], meter, len(calls) + 1)
    extra["success_at_1"] = bool(log and log[0].get("hidden_pass"))  # render の一回目の一致
    return finish(task, "gen-render", rep, calls + log, stop, meter, extra)


# ---------------------------------------------------------------------------------------------- summary

# 記述用の対（二次指標。主要比較は登録した一覧だけ）。草案 §2 の表の順
DESCRIPTIVE_PAIRS = (
    ("lptl", "lptl-nolet"), ("lptl", "ast"), ("ast", "ast-schema"), ("lptl", "ast-schema"),
    ("lptl", "lptl-nodiag"), ("lptl-msg", "lptl-nodiag"), ("lptl-code", "lptl-nodiag"), ("lptl-span", "lptl-nodiag"),
    ("lptl", "lptl-noskill"), ("lptl", "python"),
)


def _pair_tasks(a: str, b: str, by_arm: dict[str, set], let_free) -> list[str]:
    tasks = by_arm[a] & by_arm[b]
    if "lptl-nolet" in (a, b) and let_free is not None:
        tasks &= set(let_free)  # 草案 §2：v1 ／ v1-no-let の共通課題は、参照解が let を使わないもの
    return sorted(tasks)


def arm_summary(es: list[dict]) -> dict:
    n = len(es)
    k = sum(e["success_selected"] for e in es)
    outcomes = {o.value: 0 for o in Outcome}
    for e in es:
        outcomes[e["outcome"]] += 1
    infra = [e for e in es if e["outcome"] == Outcome.INFRA_FAULT.value]
    rounds = [r for e in es for r in e["rounds"] if "api_error" not in r]
    cands = [r for r in rounds if r.get("has_code")]
    used = Counter()
    breakdown = Counter()
    for e in es:
        used.update(e["budget"]["used"])
        breakdown.update(e["budget"]["input_breakdown"])
    s1 = sum(e["success_at_1"] for e in es)
    first = [e["rounds"][0] for e in es if e["rounds"] and "api_error" not in e["rounds"][0]]
    failing = [r for r in cands if not r.get("visible_pass")]
    cost = [r["cost_usd"] for r in rounds if isinstance(r.get("cost_usd"), (int, float))]
    return {
        "episodes": n,  # 分母：全 episode（失敗の分類も試験基盤の事故も落とさない）
        "success_selected": k,
        "success_selected_rate": k / n if n else 0,
        "success_selected_ci95": wilson(k, n),
        "outcomes": outcomes,
        "outcome_details": [[o, d, c] for (o, d), c in
                            Counter((e["outcome"], e["outcome_detail"]) for e in es if not e["success_selected"]).most_common()],
        "infra_faults": {"count": len(infra), "episodes": sorted(e["episode_id"] for e in infra),
                         "kinds": dict(Counter(e["outcome_detail"] for e in infra))},
        "failed_tasks": sorted({e["task"] for e in es if not e["success_selected"]}),
        "secondary": {
            "success_at_1": s1,
            "success_at_1_rate": s1 / n if n else 0,
            "success_at_1_ci95": wilson(s1, n),
            "hidden_last_round": sum(e["hidden_last_round"] for e in es),
            "repaired": sum(e["success_selected"] and (e["selected_round"] or 0) > 1 for e in es),
            "first_round_rejected": sum(r.get("has_code") and not r.get("accepted") for r in first),
            "candidates": len(cands),
            "accepted_candidates": sum(bool(r.get("accepted")) for r in cands),
            "mean_rounds": sum(e["rounds_used"] for e in es) / n if n else 0,
            "stop_reasons": dict(Counter(e["stop"]["reason"] for e in es)),
            "budget_used": dict(used),
            "input_breakdown": dict(breakdown),
            "cost_usd": sum(cost) if cost else None,
            "api_errors": sum(e["api_error"] is not None for e in es),
            "refusals": sum(r.get("stop_reason") == "refusal" for r in rounds),
            "fallback_rounds": sum(bool(r.get("fallback")) for r in rounds),
            "failure_codes": Counter(c for r in failing for c in r.get("codes", [])).most_common(15),
        },
    }


def summarize(episodes: list[dict], resamples: int = BOOTSTRAP_RESAMPLES, registry: dict | None = None,
              let_free: list[str] | None = None, level: float = BOOTSTRAP_LEVEL) -> dict:
    arms = sorted({e["arm"] for e in episodes})
    by_arm = {a: {e["task"] for e in episodes if e["arm"] == a} for a in arms}
    out = {"summary_format": 2, "selection_rule": SELECTION_RULE,
           "arms": {a: arm_summary([e for e in episodes if e["arm"] == a]) for a in arms}}
    common = sorted(set.intersection(*by_arm.values())) if arms else []
    boot = {"resamples": resamples, "level": level, "tasks": len(common),
            "seed": "sha256('lptl-eval-paired-bootstrap-v1' + sorted task IDs) (stats.bootstrap_seed)",
            "arms": {}, "differences": []}
    if common:
        means = paired_bootstrap({a: task_scores(episodes, a, common) for a in arms}, resamples, bootstrap_seed(common))
        for a in arms:
            lo, hi = interval(means[a], level)
            boot["arms"][a] = {"mean": sum(task_scores(episodes, a, common)) / len(common), "ci": [lo, hi]}
        for a, b in DESCRIPTIVE_PAIRS:
            if a not in by_arm or b not in by_arm:
                continue
            tasks = _pair_tasks(a, b, by_arm, let_free)
            if not tasks:
                continue
            if tasks == common:
                ma, mb = means[a], means[b]
            else:
                sub = paired_bootstrap({a: task_scores(episodes, a, tasks), b: task_scores(episodes, b, tasks)},
                                       resamples, bootstrap_seed(tasks))
                ma, mb = sub[a], sub[b]
            sa, sb = task_scores(episodes, a, tasks), task_scores(episodes, b, tasks)
            boot["differences"].append({"arms": [a, b], "tasks": len(tasks), "estimate": (sum(sa) - sum(sb)) / len(tasks),
                                        "ci": difference(ma, mb, level)["ci"]})
    out["paired_bootstrap"] = boot
    if registry is None:
        out["primary_comparisons"] = {"claimed": False, "note": "予備実験の実行なので、主要比較を計算しない", "results": []}
    else:
        reg = {**registry, "comparisons": [
            {**c, "tasks": _pair_tasks(*c["arms"], by_arm, let_free)}
            if "lptl-nolet" in c["arms"] and not c.get("tasks") and all(a in by_arm for a in c["arms"]) else c
            for c in registry["comparisons"]]}
        out["primary_comparisons"] = primary_comparisons(reg, episodes, resamples, level)
    return out


def _pct(x: float) -> str:
    return f"{x:.0%}"


def summary_markdown(summary: dict, config: dict) -> str:
    """要約の表。モデルの版の識別子は書かない（config.json にだけ記録する）。"""
    protocol = config.get("protocol")
    title = "Protocol run" if protocol else "Pilot run"
    head = (f"backend `{config['backend_kind']}`, effort `{config.get('effort')}`, repeats {config['repeats']}, "
            f"{config['tasks']} tasks ({config.get('task_set', 'public')}), SKILL.md sha256 `{config['skill_sha256'][:12]}`")
    if protocol:
        b = protocol["budget"]
        limits = (f"budget B: input ≤ {b['input_tokens']} tokens, output ≤ {b['output_tokens']} tokens, "
                  f"requests ≤ {b['requests']}, visible verification calls ≤ {b['verification_calls']}")
    else:
        limits = f"no budget B (pilot), at most {config['rounds']} rounds"
    lines = [f"# {title} {config['run_id']}", "", head + ".", "", limits + ".", "", f"Selection: {summary['selection_rule']}", ""]
    if config.get("task_filter"):
        lines += [f"Task subset: {config['task_filter']}. Not the registered task set.", ""]
    boot = summary["paired_bootstrap"]
    lines += [
        f"| arm | episodes | success (selected) | Wilson 95% CI | paired bootstrap {boot['level']:.0%} CI | infra faults |",
        "|---|---|---|---|---|---|",
    ]
    for arm, s in summary["arms"].items():
        lo, hi = s["success_selected_ci95"]
        b = boot["arms"].get(arm)
        bci = f"{_pct(b['ci'][0])}–{_pct(b['ci'][1])}" if b else "n/a"
        lines.append(f"| {arm} | {s['episodes']} | {s['success_selected']} ({_pct(s['success_selected_rate'])}) | "
                     f"{_pct(lo)}–{_pct(hi)} | {bci} | {s['infra_faults']['count']} |")
    cats = [o.value for o in Outcome]
    lines += ["", "## Outcomes (every episode is in the denominator)", "",
              "| arm | " + " | ".join(cats) + " |", "|---|" + "---|" * len(cats)]
    for arm, s in summary["arms"].items():
        lines.append(f"| {arm} | " + " | ".join(str(s["outcomes"][c]) for c in cats) + " |")
    faults = [(arm, s["infra_faults"]) for arm, s in summary["arms"].items() if s["infra_faults"]["count"]]
    lines += ["", "## Infrastructure faults", ""]
    lines += [f"- {arm}: {f['count']} ({', '.join(f'{k} ×{v}' for k, v in f['kinds'].items())}): {', '.join(f['episodes'])}"
              for arm, f in faults] or ["- none"]
    pc = summary["primary_comparisons"]
    lines += ["", "## Primary comparisons", ""]
    if not pc["results"]:
        lines.append(f"- {pc['note'] or 'none registered: no primary comparison is claimed'}")
    else:
        lines += [f"alpha {pc['alpha']}, Holm over the registered list. {pc['note']}".strip(), "",
                  "| id | arms | tasks | difference | 95% CI | p | p (Holm) |", "|---|---|---|---|---|---|---|"]
        for r in pc["results"]:
            if r["computed"]:
                lines.append(f"| {r['id']} | {r['arms'][0]} − {r['arms'][1]} | {r['tasks']} | {r['estimate']:+.3f} | "
                             f"{r['ci'][0]:+.3f}–{r['ci'][1]:+.3f} | {r['p']:.4f} | {r['p_holm']:.4f} |")
            else:
                lines.append(f"| {r['id']} | {r['arms'][0]} − {r['arms'][1]} | – | not computed: {r['note']} | | | |")
    if boot["differences"]:
        lines += ["", "## Descriptive differences (paired bootstrap, secondary)", "",
                  "| arms | tasks | difference | 95% CI |", "|---|---|---|---|"]
        for d in boot["differences"]:
            lines.append(f"| {d['arms'][0]} − {d['arms'][1]} | {d['tasks']} | {d['estimate']:+.3f} | "
                         f"{d['ci'][0]:+.3f}–{d['ci'][1]:+.3f} |")
    lines += ["", "## Secondary", "",
              "| arm | Success@1 | hidden at last round | repaired | accepted / candidates | mean rounds | requests | "
              "input tokens (cache read / write) | output tokens | verification calls |",
              "|---|---|---|---|---|---|---|---|---|---|"]
    for arm, s in summary["arms"].items():
        x = s["secondary"]
        u, ib = x["budget_used"], x["input_breakdown"]
        lines.append(
            f"| {arm} | {x['success_at_1']} ({_pct(x['success_at_1_rate'])}) | {x['hidden_last_round']} | {x['repaired']} | "
            f"{x['accepted_candidates']} / {x['candidates']} | {x['mean_rounds']:.2f} | {u.get('requests', 0)} | "
            f"{u.get('input_tokens', 0)} ({ib.get('cache_read_input_tokens', 0)} / {ib.get('cache_creation_input_tokens', 0)}) | "
            f"{u.get('output_tokens', 0)} | {u.get('verification_calls', 0)} |")
    for arm, s in summary["arms"].items():
        x = s["secondary"]
        lines += ["", f"### {arm}", "", f"- failed tasks: {', '.join(s['failed_tasks']) or 'none'}"]
        if s["outcome_details"]:
            lines.append("- failures: " + ", ".join(f"{o}" + (f" ({d})" if d else "") + f" ×{c}" for o, d, c in s["outcome_details"]))
        if x["failure_codes"]:
            lines.append("- codes on failing rounds: " + ", ".join(f"`{c}` ×{n}" for c, n in x["failure_codes"]))
        if x["api_errors"] or x["refusals"] or x["fallback_rounds"]:
            lines.append(f"- api errors {x['api_errors']}, refusals {x['refusals']}, rounds served by a fallback model {x['fallback_rounds']}")
    if "render" in summary["arms"] or "gen-render" in summary["arms"]:
        lines += ["", "render は AST 一致で採点する。gen-render は lptl の一回の生成結果を render へ渡す連結 arm で、render とは別の行に報告する。"]
    if config.get("publication"):
        lines += ["", f"Publication scope `{config['publication']['scope']}`: {', '.join(config['publication']['files'])}."]
    return "\n".join(lines) + "\n"


# ---------------------------------------------------------------------------------------------- main


def _explicit(argv: list[str]) -> set[str]:
    return {a.split("=", 1)[0] for a in argv if a.startswith("--")}


def _git_state() -> dict:
    """処理系とハーネスの版（§1）。作業ツリーに未コミットの変更があれば dirty。"""
    try:
        head = subprocess.run(["git", "-C", str(REPO), "rev-parse", "HEAD"], capture_output=True, text=True, timeout=10)
        status = subprocess.run(["git", "-C", str(REPO), "status", "--porcelain", "--untracked-files=no"],
                                capture_output=True, text=True, timeout=30)
    except (OSError, subprocess.TimeoutExpired):
        return {"commit": None, "dirty": None}
    return {"commit": head.stdout.strip() or None, "dirty": bool(status.stdout.strip()) if status.returncode == 0 else None}


def protocol_problems(args, explicit: set[str], cfg, arms: list[str]) -> list[str]:
    """protocol の実行の前提。一つでも欠ければ実行しない（fail closed）。"""
    problems = []
    if args.backend != "oracle":
        for opt in ("--model", "--effort"):
            if opt not in explicit:
                problems.append(f"{opt} を明示してください（§1：固定する版。値は eval/runs の config.json にだけ記録する）")
    for opt, why in (("--repeats", "反復数 K は設定の repeats から取る"), ("--rounds", "回数は予算 B（requests）で決まる"),
                     ("--retries", "protocol の実行では CLI の時間切れを呼び直さない")):
        if opt in explicit:
            problems.append(f"{opt} は使えません（{why}）")
    want = {"cli-defaults": "claude-cli", "api-fixed": "anthropic"}[cfg.cli_limits]
    if args.backend not in (want, "oracle"):
        problems.append(f"cli_limits が {cfg.cli_limits} なので --backend {want} で実行します（{args.backend} ではない）")
    if "ast-schema" in arms and args.backend == "anthropic":
        problems.append("ast-schema は claude-cli だけで動きます（API の structured outputs は再帰する schema を扱えない）")
    return problems


def main(argv: list[str] | None = None) -> int:
    argv = sys.argv[1:] if argv is None else argv
    # 省略形（--rep など）を許すと、protocol の実行で明示した引数を見分けられないので許さない
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter,
                                 allow_abbrev=False)
    ap.add_argument("--backend", choices=("anthropic", "claude-cli", "oracle"), default="anthropic")
    ap.add_argument("--claude-bin", default="claude", help="claude-cli で使う claude コマンド")
    ap.add_argument("--timeout", type=float, default=300, help="claude-cli の 1 呼び出しの秒数の上限")
    ap.add_argument("--retries", type=int, default=2, help="claude-cli が時間切れのとき呼び直す回数（予備実験だけ）")
    ap.add_argument("--model", default="claude-opus-5-5")
    ap.add_argument("--effort", default="high", choices=("low", "medium", "high", "xhigh", "max"))
    ap.add_argument("--max-tokens", type=int, default=32000)
    ap.add_argument("--no-fallback", action="store_true", help="安全分類器による拒否時のフォールバックを使わない")
    ap.add_argument("--arms", default="lptl,python", help=f"カンマ区切り（{', '.join(ARMS)}）")
    ap.add_argument("--tasks", default="", help="カンマ区切りのタスク ID または名前（既定は全件）")
    ap.add_argument("--category", default="", help="カンマ区切りのカテゴリ（例: hard）で絞る")
    ap.add_argument("--rounds", type=int, default=3, help="初回を含む最大の回数（1 なら修復なし。予備実験だけ）")
    ap.add_argument("--repeats", type=int, default=1, help="反復数（予備実験だけ。protocol では設定の repeats）")
    ap.add_argument("--workers", type=int, default=4)
    ap.add_argument("--out", default=str(EVAL / "runs"))
    ap.add_argument("--protocol", metavar="CONFIG.json", help="事前登録の設定（必須の項目が欠ければ実行しない）")
    ap.add_argument("--task-set", choices=("public", "secret"), default="public",
                    help=f"secret は設定の hidden_set_location の課題を、環境変数 {HIDDEN_SEED_ENV} の種で読む")
    ap.add_argument("--primary", default=str(EVAL / "primary_comparisons.json"), help="主要比較の一覧（protocol の実行）")
    args = ap.parse_args(argv)
    explicit = _explicit(argv)

    arms = [a for a in args.arms.split(",") if a]
    if todo := [a for a in arms if a in NOT_IMPLEMENTED]:
        ap.error("not implemented (needs an owner decision): " + "; ".join(f"{a}: {NOT_IMPLEMENTED[a]}" for a in todo))
    if bad := [a for a in arms if a not in ARMS]:
        ap.error(f"unknown arm: {bad}")
    if "ast-schema" in arms and args.backend == "anthropic":
        ap.error("ast-schema needs the claude-cli (or oracle) backend")

    cfg = registry = None
    if args.protocol:
        try:
            cfg = load_protocol_config(args.protocol)
            registry = load_registry(args.primary)
        except (ProtocolConfigError, RegistryError) as e:
            print(e, file=sys.stderr)
            return 2
        if problems := protocol_problems(args, explicit, cfg, arms):
            print("protocol の実行の前提が満たされていません（fail closed）:\n- " + "\n- ".join(problems), file=sys.stderr)
            return 2
    elif args.task_set == "secret":
        ap.error("--task-set secret needs --protocol (hidden_set_location)")

    if args.task_set == "secret":
        try:
            tasks = load_secret_tasks(cfg.hidden_set_location)
        except (SecretSeedMissing, OSError, RuntimeError) as e:
            print(f"秘密の課題集合を読めません（fail closed）: {e}", file=sys.stderr)
            return 2
    else:
        tasks = load_tasks()
    if only := [t for t in args.tasks.split(",") if t]:
        tasks = [t for t in tasks if any(t["id"] == o or t["id"].split("-", 1)[1] == o for o in only)]
    if cats := [c for c in args.category.split(",") if c]:
        tasks = [t for t in tasks if t.get("category") in cats]
    if not tasks:
        ap.error("no tasks selected")

    retries = 0 if cfg else args.retries
    fallback = args.backend == "anthropic" and not args.no_fallback and cfg is None  # protocol では別のモデルに答えさせない
    if args.backend == "oracle":
        backend = OracleBackend()
    elif args.backend == "claude-cli":
        backend = ClaudeCliBackend(args.model, args.effort, args.claude_bin, args.timeout, retries)
    else:
        backend = AnthropicBackend(args.model, args.effort, args.max_tokens, fallback)

    run_id = dt.datetime.now(dt.timezone.utc).strftime("%Y%m%dT%H%M%SZ") + f"-{args.backend}" + ("-protocol" if cfg else "")
    out = Path(args.out) / run_id
    out.mkdir(parents=True)
    repeats = cfg.repeats if cfg else args.repeats
    rounds = None if cfg else args.rounds
    budget = cfg.budget if cfg else None
    systems = {a: ARM_SPECS[a].system for a in arms if a in ARM_SPECS} | {a: SKILL for a in arms if a not in ARM_SPECS}
    config = {
        "run_id": run_id,
        "mode": "protocol" if cfg else "pilot",
        "backend": backend.name,  # モデルの版の識別子を含む（このファイルは git の対象外）
        "backend_kind": args.backend,
        "effort": args.effort if args.backend != "oracle" else None,
        "max_tokens": args.max_tokens if args.backend == "anthropic" else None,
        "fallback": fallback,
        "cli_retries": retries if args.backend == "claude-cli" else None,
        "cli_timeout": args.timeout if args.backend == "claude-cli" else None,
        "arms": arms,
        "rounds": rounds,
        "repeats": repeats,
        "tasks": len(tasks),
        "task_ids": [t["id"] for t in tasks],
        "task_set": args.task_set,
        "task_filter": ",".join(only + cats) or None,
        "hidden_seed": (f"HMAC-SHA256(${HIDDEN_SEED_ENV}, task id); the value is never recorded" if args.task_set == "secret"
                        else "sha256(task id) (tasks_lib.public_seed)"),
        "skill_sha256": hashlib.sha256(SKILL.encode()).hexdigest(),
        "system_sha256": {a: hashlib.sha256(s.encode()).hexdigest() for a, s in systems.items()},
        "ast_schema_sha256": hashlib.sha256(AST_SCHEMA_PATH.read_bytes()).hexdigest(),
        "manifest": json.loads((EVAL / "manifest.json").read_text(encoding="utf-8")).get("task_set_sha256"),
        "git": _git_state(),
        "selection_rule": SELECTION_RULE,
        "verification_rule": VERIFICATION_RULE,
        "bytes_per_token_estimate": BYTES_PER_TOKEN,
    }
    if cfg:
        config["protocol"] = cfg.as_dict()
        config["primary_comparisons"] = {"path": args.primary,
                                         "sha256": hashlib.sha256(Path(args.primary).read_bytes()).hexdigest()}
        files = list(PUBLISHABLE[cfg.publication_scope])
        if args.task_set == "secret":
            # 生データ（config.json の課題 ID、episodes.jsonl の回答とコード）は秘密の課題を明かすので、範囲によらず公開しない
            files = [f for f in files if f in PUBLISHABLE["summary-only"]]
        config["publication"] = {"scope": cfg.publication_scope, "task_set": args.task_set, "files": files}
    (out / "config.json").write_text(json.dumps(config, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")

    jobs = [(t, a, r) for r in range(1, repeats + 1) for a in arms for t in tasks]
    lock = threading.Lock()
    episodes = []
    with open(out / "episodes.jsonl", "w", encoding="utf-8") as f, ThreadPoolExecutor(args.workers) as pool:
        for ep in pool.map(lambda j: episode(backend, j[0], j[1], rounds, j[2], budget), jobs):
            with lock:
                episodes.append(ep)
                f.write(json.dumps(ep, ensure_ascii=False) + "\n")
                f.flush()
                mark = "ok " if ep["success_selected"] else "NG "
                print(f"{mark}{ep['arm']:<12} {ep['task']:<24} {ep['outcome']:<18} rounds={ep['rounds_used']}", file=sys.stderr)
    summary = summarize(episodes, BOOTSTRAP_RESAMPLES, registry, let_free_tasks(tasks))
    (out / "summary.json").write_text(json.dumps(summary, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")
    md = summary_markdown(summary, config)
    (out / "summary.md").write_text(md, encoding="utf-8")
    if cfg:
        (out / "publish.json").write_text(json.dumps(config["publication"], indent=2) + "\n", encoding="utf-8")
    print(md)
    print(f"results: {out}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
