"""ハーネスの採点と修復の経路を、API を使わない偽のモデルで確かめる（tlvm を使う）。

usage: python3 -m unittest discover -s eval -p 'test_*.py'
"""

import json
import os
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

import harness
import runner
from protocol import Budget, BackendError, estimate_tokens
from tasks_lib import EVAL, HIDDEN_SEED_ENV, load_tasks


class Scripted:
    """決めた答えを順に返す偽のモデル。受け取った会話・system・引数を記録する。

    答えは文字列か、text・stop_reason・usage・requests・structured を持つ dict か、投げる例外。"""

    name = "scripted"

    def __init__(self, answers):
        self.answers = list(answers)
        self.seen, self.systems, self.kwargs = [], [], []

    def complete(self, system, messages, task, arm, **kw):
        self.seen.append([dict(m) for m in messages])
        self.systems.append(system)
        self.kwargs.append(kw)
        a = self.answers.pop(0)
        if isinstance(a, BaseException):
            raise a
        if isinstance(a, str):
            a = {"text": a}
        text = a.get("text", "")
        return {"text": text, "content": text, "stop_reason": a.get("stop_reason", "end_turn"),
                "usage": a.get("usage", {"input_tokens": 1, "output_tokens": 1}), "model": "scripted",
                "fallback": False, "requests": a.get("requests", 1), "structured": a.get("structured")}


def fenced(lang, code):
    return f"Here you go.\n```{lang}\n{code}\n```\n"


SUM_TOTAL = "fn total(xs: List<Int>) -> Int = fold(xs, 0, |acc, x| add(acc, x))\n"
# 公開例の一件目（[1, 2, 3]）だけを間違え、隠しテストは全て通す（隠しテストは公開例と同じ入力を含まない）
VISIBLE_ONLY_WRONG = SUM_TOTAL + "fn solve(xs: List<Int>) -> Int = if(eq(xs, list<Int>(1, 2, 3)), 0, total(xs))\nentry solve"
WRONG = "fn solve(xs: List<Int>) -> Int = length(xs)\nentry solve"
TYPE_ERROR = "fn solve(xs: List<Int>) -> Int = xs\nentry solve"
UNBOUND = "fn solve(xs: List<Int>) -> Int = fold(xs, 0, |acc, x| add(acc, y))\nentry solve"


def big_budget(**over):
    b = {"input_tokens": 10 ** 7, "output_tokens": 10 ** 6, "requests": 3, "verification_calls": 100}
    b.update(over)
    return Budget(**b)


class HarnessTest(unittest.TestCase):
    def setUp(self):
        self.task = load_tasks(["sum"])[0]
        self.ref = (self.task["dir"] / "reference.tlvm").read_text()
        self.small = {**self.task, "hidden": self.task["hidden"][:3]}  # 遅い候補（深い再帰）を短く走らせる

    def test_oracle_passes_everything(self):
        for task in load_tasks():
            for arm in ("lptl", "python", "ast", "render", "gen-render"):
                ep = harness.episode(harness.OracleBackend(), task, arm, 3, 1)
                self.assertTrue(ep["success_selected"], (task["id"], arm, ep["outcome"], ep["outcome_detail"]))
                self.assertEqual(ep["outcome"], "success")
        for task in load_tasks(["sum", "shapes_area"]):
            for arm in ("lptl-nodiag", "lptl-msg", "lptl-code", "lptl-span", "lptl-noskill", "ast-schema"):
                ep = harness.episode(harness.OracleBackend(), task, arm, 3, 1)
                self.assertTrue(ep["success_selected"], (task["id"], arm, ep["outcome"]))

    def test_oracle_nolet_accepts_only_let_free_references(self):
        tasks = load_tasks()
        free = set(harness.let_free_tasks(tasks))
        self.assertTrue(0 < len(free) < len(tasks))
        for task in tasks:
            ep = harness.episode(harness.OracleBackend(), task, "lptl-nolet", 1, 1)
            if task["id"] in free:
                self.assertTrue(ep["success_selected"], task["id"])
            else:
                self.assertEqual((ep["outcome"], ep["outcome_detail"]), ("rejected", "parse"), task["id"])
                self.assertEqual(ep["rounds"][0]["codes"], ["NoLet"])

    # ------------------------------------------------------------------------------------------ §3 最終候補

    def test_final_candidate_is_the_last_accepted_not_the_best_hidden(self):
        # 1 回目は隠しテストを全て通すが公開例に失敗、2 回目は受理される誤答 → 選ぶのは 2 回目
        m = Scripted([fenced("tlvm", VISIBLE_ONLY_WRONG), fenced("tlvm", WRONG)])
        ep = harness.episode(m, self.task, "lptl", 2, 1)
        self.assertTrue(ep["rounds"][0]["hidden_pass"])
        self.assertFalse(ep["rounds"][0]["visible_pass"])
        self.assertEqual(ep["selected_round"], 2)
        self.assertFalse(ep["success_selected"])
        self.assertEqual((ep["outcome"], ep["outcome_detail"]), ("wrong_answer", "wrong-output"))
        self.assertTrue(ep["success_at_1"])
        self.assertFalse(ep["hidden_last_round"])
        self.assertNotIn("hidden", m.seen[1][-1]["content"].lower())  # 隠しテストは修復に返さない

    def test_rejected_last_round_does_not_replace_an_accepted_candidate(self):
        m = Scripted([fenced("tlvm", VISIBLE_ONLY_WRONG), fenced("tlvm", TYPE_ERROR)])
        ep = harness.episode(m, self.task, "lptl", 2, 1)
        self.assertEqual(ep["selected_round"], 1)
        self.assertTrue(ep["success_selected"])  # 最後に受理された候補（1 回目）が隠しテストを通す
        self.assertFalse(ep["hidden_last_round"])
        self.assertEqual(ep["budget"]["used"]["verification_calls"], 7 + 1)  # 1 + 2×3、拒否された候補は compile の 1 回

    def test_repair_with_diagnostics(self):
        m = Scripted([fenced("tlvm", UNBOUND), fenced("tlvm", self.ref)])
        ep = harness.episode(m, self.task, "lptl", 3, 1)
        self.assertFalse(ep["success_at_1"])
        self.assertTrue(ep["success_selected"])
        self.assertEqual((ep["rounds_used"], ep["selected_round"]), (2, 2))
        self.assertEqual(ep["rounds"][0]["codes"], ["E-NAME-UNBOUND-VARIABLE"])
        self.assertEqual(ep["rounds"][0]["phase"], "name")
        repair_msg = m.seen[1][-1]["content"]
        self.assertIn("E-NAME-UNBOUND-VARIABLE", repair_msg)
        self.assertIn("variable in scope: x, acc, xs", repair_msg)

    # ------------------------------------------------------------------------------------------ §3 分母と分類

    def test_rejection_phases(self):
        for code, phase in ((UNBOUND, "name"), (TYPE_ERROR, "type"), ("fn solve(xs: List<Int>) -> Int = )\nentry solve", "parse"),
                            ("fn main(xs: List<Int>) -> Int = 0\nentry main", "entry")):
            ep = harness.episode(Scripted([fenced("tlvm", code)]), self.task, "lptl", 1, 1)
            self.assertEqual((ep["outcome"], ep["outcome_detail"]), ("rejected", phase), code)
            self.assertIsNone(ep["selected_round"])

    def test_no_code_block(self):
        ep = harness.episode(Scripted(["I cannot do that."]), self.task, "lptl", 1, 1)
        self.assertEqual(ep["rounds"][0]["codes"], ["NoCode"])
        self.assertEqual(ep["outcome"], "no_candidate")
        self.assertEqual(ep["budget"]["used"]["verification_calls"], 0)

    def test_runtime_outcomes_of_the_selected_candidate(self):
        cases = (
            ("fn solve(xs: List<Int>) -> Int = length(range(0, 100000000))\nentry solve", "resource_exceeded"),
            ("rec fn f(n: Int) -> Int = add(1, f(n))\nfn solve(xs: List<Int>) -> Int = f(0)\nentry solve", "host_aborted"),
        )
        for code, outcome in cases:
            small = {**self.small, "examples": self.small["examples"][:1]}
            ep = harness.episode(Scripted([fenced("tlvm", code)]), small, "lptl", 1, 1)
            self.assertEqual(ep["outcome"], outcome, ep["outcome_detail"])
            self.assertEqual(ep["selected_round"], 1)

    def test_refusal_and_truncation_are_generation_failures(self):
        for stop, detail in (("refusal", "refusal"), ("max_tokens", "truncated")):
            m = Scripted([{"text": fenced("tlvm", self.ref), "stop_reason": stop}])
            ep = harness.episode(m, self.task, "lptl", 3, 1)
            self.assertEqual((ep["outcome"], ep["outcome_detail"]), ("generation_failure", detail))
            self.assertFalse(ep["rounds"][0]["accepted"])  # 途中で切れた出力は受理しない
            self.assertEqual(len(m.seen), 1)

    def test_backend_failures_follow_the_fixed_table_without_retry(self):
        m = Scripted([BackendError("cli-error", "overloaded")])
        ep = harness.episode(m, self.task, "lptl", 3, 1)
        self.assertEqual((ep["outcome"], ep["outcome_detail"]), ("infra_fault", "cli-error"))
        self.assertEqual(len(m.seen), 1)
        self.assertIn("cli-error", ep["api_error"])
        m = Scripted([subprocess.TimeoutExpired("claude", 1)])
        self.assertEqual(harness.episode(m, self.task, "lptl", 3, 1)["outcome_detail"], "cli-timeout")
        usage = {"input_tokens": 5, "output_tokens": 9}
        m = Scripted([BackendError("cli-structured-output-retries", "x", usage=usage, requests=4)])
        ep = harness.episode(m, self.task, "lptl", 3, 1, big_budget(requests=10))
        self.assertEqual((ep["outcome"], ep["outcome_detail"]), ("generation_failure", "cli-structured-output-retries"))
        self.assertEqual(ep["budget"]["used"]["requests"], 4)
        self.assertEqual(ep["budget"]["used"]["output_tokens"], 9)

    def test_tlvm_failure_is_an_infrastructure_fault(self):
        with tempfile.TemporaryDirectory() as d:
            fake = Path(d) / "tlvm"
            fake.write_text("#!/bin/sh\nexit 101\n")
            fake.chmod(0o755)
            saved = runner.TLVM
            runner.TLVM = fake
            try:
                ep = harness.episode(Scripted([fenced("tlvm", self.ref)]), self.task, "lptl", 3, 1)
            finally:
                runner.TLVM = saved
        self.assertEqual((ep["outcome"], ep["outcome_detail"]), ("infra_fault", "tlvm-exit"))
        self.assertEqual(ep["rounds_used"], 1)

    # ------------------------------------------------------------------------------------------ §5 予算 B

    def test_request_budget_stops_and_keeps_the_existing_candidate(self):
        m = Scripted([fenced("tlvm", WRONG), fenced("tlvm", self.ref)])
        ep = harness.episode(m, self.task, "lptl", None, 1, big_budget(requests=1))
        self.assertEqual(len(m.seen), 1)
        self.assertEqual(ep["stop"], {"reason": "budget_reached", "detail": "requests"})
        self.assertEqual((ep["outcome"], ep["selected_round"]), ("wrong_answer", 1))
        self.assertTrue(ep["budget"]["budget_ok"])

    def test_exceeding_the_budget_fails_even_with_a_correct_earlier_candidate(self):
        m = Scripted([fenced("tlvm", VISIBLE_ONLY_WRONG), {"text": fenced("tlvm", self.ref),
                                                          "usage": {"input_tokens": 1, "output_tokens": 501}}])
        ep = harness.episode(m, self.task, "lptl", None, 1, big_budget(output_tokens=500))
        self.assertTrue(ep["rounds"][0]["hidden_pass"])
        self.assertEqual(ep["stop"], {"reason": "budget_exceeded", "detail": "output_tokens"})
        self.assertEqual(ep["outcome"], "budget_exceeded")
        self.assertFalse(ep["success_selected"])
        self.assertFalse(ep["budget"]["budget_ok"])

    def test_exact_limit_is_within_budget(self):
        m = Scripted([{"text": fenced("tlvm", self.ref), "usage": {"input_tokens": 10, "output_tokens": 500}}])
        ep = harness.episode(m, self.task, "lptl", None, 1, big_budget(output_tokens=500, verification_calls=7))
        self.assertTrue(ep["success_selected"])
        self.assertEqual(ep["budget"]["used"]["verification_calls"], 7)

    def test_cache_tokens_are_input_tokens_recorded_apart(self):
        usage = {"input_tokens": 3, "output_tokens": 4, "cache_read_input_tokens": 100, "cache_creation_input_tokens": 20}
        ep = harness.episode(Scripted([{"text": fenced("tlvm", self.ref), "usage": usage}]), self.task, "lptl", None, 1,
                             big_budget())
        self.assertEqual(ep["budget"]["used"]["input_tokens"], 123)
        self.assertEqual(ep["budget"]["input_breakdown"],
                         {"input_tokens": 3, "cache_read_input_tokens": 100, "cache_creation_input_tokens": 20})
        # キャッシュを含めると上限を超える：キャッシュの割引で予算内にしない
        est = estimate_tokens(harness.prompt_bytes(harness.SKILL, [{"content": harness.task_prompt(self.task, "lptl")}]))
        usage = {"input_tokens": 3, "output_tokens": 4, "cache_read_input_tokens": est, "cache_creation_input_tokens": 20}
        m = Scripted([{"text": fenced("tlvm", self.ref), "usage": usage}])
        ep = harness.episode(m, self.task, "lptl", None, 1, big_budget(input_tokens=est + 22))
        self.assertEqual(len(m.seen), 1)  # 見積りは上限以内なので要求は出す
        self.assertEqual((ep["outcome"], ep["stop"]["detail"]), ("budget_exceeded", "input_tokens"))

    def test_input_guard_before_the_first_request(self):
        m = Scripted([fenced("tlvm", self.ref)])
        ep = harness.episode(m, self.task, "lptl", None, 1, big_budget(input_tokens=100))
        self.assertEqual(m.seen, [])  # SKILL だけで見積りが上限を超えるので、要求を出さない
        self.assertEqual(ep["stop"], {"reason": "operation_guarded", "detail": "input_tokens"})
        self.assertEqual((ep["outcome"], ep["outcome_detail"]), ("no_candidate", "input_tokens"))
        self.assertEqual(ep["budget"]["used"]["requests"], 0)

    def test_second_request_estimate_uses_the_measured_first_request(self):
        first = {"text": fenced("tlvm", WRONG), "usage": {"input_tokens": 50000, "output_tokens": 10}}
        m = Scripted([first, fenced("tlvm", self.ref)])
        ep = harness.episode(m, self.task, "lptl", None, 1, big_budget(input_tokens=50100))
        self.assertEqual(len(m.seen), 1)
        self.assertEqual(ep["stop"], {"reason": "operation_guarded", "detail": "input_tokens"})
        self.assertEqual(ep["rounds"][0]["estimated_input"], estimate_tokens(harness.prompt_bytes(harness.SKILL, m.seen[0])))

    def test_verification_budget_compiles_only_when_examples_do_not_fit(self):
        ep = harness.episode(Scripted([fenced("tlvm", self.ref)]), self.task, "lptl", None, 1,
                             big_budget(verification_calls=6))
        self.assertEqual(ep["stop"], {"reason": "operation_guarded", "detail": "verification_calls"})
        self.assertFalse(ep["rounds"][0]["visible_checked"])
        self.assertTrue(ep["success_selected"])  # compile で受理された最後の候補を選ぶ
        self.assertEqual(ep["budget"]["used"]["verification_calls"], 1)

    def test_backend_receives_the_remaining_output_budget(self):
        m = Scripted([{"text": fenced("tlvm", WRONG), "usage": {"input_tokens": 1, "output_tokens": 30}},
                      fenced("tlvm", self.ref)])
        harness.episode(m, self.task, "lptl", None, 1, big_budget(output_tokens=100))
        self.assertEqual([k["max_output"] for k in m.kwargs], [100, 70])

    # ------------------------------------------------------------------------------------------ §2a 修復の文面

    def repair_message(self, arm, first, task=None):
        m = Scripted([fenced("tlvm", first), fenced("tlvm", self.ref)])
        harness.episode(m, task or self.task, arm, 2, 1)
        return m.seen[1][-1]["content"]

    def test_feedback_variants(self):
        human = self.repair_message("lptl", UNBOUND)
        self.assertIn("error[E-NAME-UNBOUND-VARIABLE]", human)
        nodiag = self.repair_message("lptl-nodiag", UNBOUND)
        self.assertEqual(nodiag, f"The program was rejected by the checker. {harness.REPAIR}")
        msg = self.repair_message("lptl-msg", UNBOUND)
        code = self.repair_message("lptl-code", UNBOUND)
        span = self.repair_message("lptl-span", UNBOUND)
        diag = harness.run_lptl(UNBOUND, [], "List<Int>", "Int")["errors"][0]
        self.assertIn(diag["message"], msg)
        for text in ("E-NAME", "1:", "repair", "found"):
            self.assertNotIn(text, msg)
        self.assertIn("E-NAME-UNBOUND-VARIABLE", code)
        self.assertNotIn(diag["message"], code)
        self.assertNotIn(":", code.split("```")[1])  # コードだけ（位置なし）
        (l1, c1), (l2, c2) = diag["start"], diag["end"]
        self.assertIn(f"{l1}:{c1}-{l2}:{c2}: found y", span)
        for text in ("E-NAME", diag["message"], "repair"):
            self.assertNotIn(text, span)

    def test_span_feedback_shows_expected_and_found(self):
        span = self.repair_message("lptl-span", TYPE_ERROR)
        self.assertRegex(span, r"\d+:\d+-\d+:\d+: expected Int, found List<Int>")
        entry = self.repair_message("lptl-span", "fn main(xs: List<Int>) -> Int = 0\nentry main")
        self.assertIn("2:1-2:6: expected solve: List<Int> -> Int, found main: List<Int> -> Int", entry)

    def test_examples_feedback_is_the_same_for_every_arm(self):
        texts = {arm: self.repair_message(arm, WRONG) for arm in ("lptl", "lptl-nodiag", "lptl-msg", "lptl-code", "lptl-span")}
        self.assertEqual(len(set(texts.values())), 1, texts)
        self.assertIn("solve(list<Int>(1, 2, 3)): expected 6, got 3", texts["lptl"])

    def test_noskill_changes_only_the_system_prompt(self):
        a, b = Scripted([fenced("tlvm", self.ref)]), Scripted([fenced("tlvm", self.ref)])
        harness.episode(a, self.task, "lptl", 1, 1)
        harness.episode(b, self.task, "lptl-noskill", 1, 1)
        self.assertEqual(a.seen, b.seen)  # 課題文と公開例は同じ
        self.assertEqual(a.systems[0], harness.SKILL)
        self.assertNotIn("fold(", b.systems[0])
        self.assertIn("fenced code block tagged `tlvm`", b.systems[0])

    def test_nolet_rejects_let_and_uses_the_nolet_skill(self):
        with_let = "fn solve(xs: List<Int>) -> Int =\n  let n = length(xs) in n\nentry solve"
        m = Scripted([fenced("tlvm", with_let), fenced("tlvm", self.ref)])
        ep = harness.episode(m, self.task, "lptl-nolet", 2, 1)
        self.assertEqual(m.systems[0], harness.SKILL_NOLET)
        self.assertEqual(ep["rounds"][0]["codes"], ["NoLet"])
        self.assertIn("solution.tlvm:2:3: error[NoLet]", m.seen[1][-1]["content"])
        self.assertTrue(ep["success_selected"])
        self.assertNotIn("let x = e1 in e2", harness.SKILL_NOLET)

    def test_ast_arm(self):
        ast = harness.run_ast(self.ref)["ast"]
        m = Scripted([fenced("json", '{"codec": "ast_codec_v1", "declarations": ['), fenced("json", json.dumps(ast))])
        ep = harness.episode(m, self.task, "ast", 2, 1)
        self.assertEqual((ep["rounds"][0]["codes"], ep["rounds"][0]["phase"]), (["E-AST-JSON-SYNTAX"], "parse"))
        self.assertTrue(ep["success_selected"])
        self.assertIn(harness.AST_SCHEMA, m.systems[0])  # schema を system に含める
        self.assertNotIn("## Output format\n\nAnswer with the complete program", m.systems[0])
        self.assertNotIn("{{", m.systems[0])
        self.assertIn("fn solve(x: List<Int>) -> Int", m.seen[0][0]["content"])  # 課題文は lptl と同じ

    def test_ast_schema_uses_the_structured_output(self):
        ast = harness.run_ast(self.ref)["ast"]
        m = Scripted([{"text": "ignored", "structured": ast, "requests": 2}])
        ep = harness.episode(m, self.task, "ast-schema", 1, 1, big_budget())
        self.assertEqual(m.kwargs[0]["schema"], harness.AST_SCHEMA)
        self.assertEqual(json.loads(harness.AST_SCHEMA), json.loads(harness.AST_SCHEMA_PATH.read_text()))
        self.assertTrue(ep["success_selected"])
        self.assertEqual(ep["budget"]["used"]["requests"], 2)

    def test_python_arm(self):
        m = Scripted([fenced("python", "def solve(xs):\n    return sum(xs) + 1"), fenced("python", "def solve(xs):\n    return sum(xs)")])
        ep = harness.episode(m, self.task, "python", 3, 1)
        self.assertEqual((ep["success_at_1"], ep["success_selected"]), (False, True))
        self.assertIn("solve([1, 2, 3]) == 6", harness.task_prompt(self.task, "python"))
        self.assertIn("solve([1, 2, 3]): expected 6, got 7", m.seen[1][-1]["content"])

    def test_python_errors_and_bad_types(self):
        ep = harness.episode(Scripted([fenced("python", "def solve(xs):\n    return str(sum(xs))")]), self.task, "python", 1, 1)
        self.assertEqual(ep["rounds"][0]["codes"], ["TypeError"])
        self.assertEqual(ep["outcome"], "wrong_answer")
        ep = harness.episode(Scripted([fenced("python", "def solve(xs) return 1")]), self.task, "python", 1, 1)
        self.assertFalse(ep["rounds"][0]["compile_ok"])
        self.assertEqual((ep["outcome"], ep["outcome_detail"]), ("rejected", "parse"))
        ep = harness.episode(Scripted([fenced("python", "def main(xs):\n    return 1")]), self.task, "python", 1, 1)
        self.assertEqual((ep["outcome"], ep["outcome_detail"]), ("rejected", "entry"))

    def test_prompt_renders_lptl_literals(self):
        t = load_tasks(["min_max"])[0]
        p = harness.task_prompt(t, "lptl")
        self.assertIn("solve(list<Int>()) = none<Pair<Int, Int>>()", p)
        self.assertIn("fn solve(x: List<Int>) -> Option<Pair<Int, Int>>", p)

    def test_prompt_renders_result_literals(self):
        t = load_tasks(["parse_config"])[0]
        self.assertIn("= ok<Int, String>(7)", harness.task_prompt(t, "lptl"))
        self.assertIn("== {'err': \"line 2: missing '='\"}", harness.task_prompt(t, "python"))

    # ------------------------------------------------------------------------------------------ render と連結 arm

    def test_render_scores_the_ast(self):
        ep = harness.episode(harness.OracleBackend(), self.task, "render", 3, 1)
        self.assertTrue(ep["success_selected"])
        self.assertEqual(ep["rounds_used"], 1)
        # 受理されても AST の違う program は不合格
        ep = harness.episode(Scripted([fenced("tlvm", "fn zz(q: Int) -> Int = q\nentry zz")]), self.task, "render", 3, 1)
        self.assertFalse(ep["success_selected"])
        self.assertTrue(ep["rounds"][0]["compile_ok"])
        self.assertFalse(ep["rounds"][0]["ast_match"])
        self.assertEqual((ep["outcome"], ep["outcome_detail"]), ("wrong_answer", "ast-mismatch"))

    def test_gen_render_reports_generation_and_render_apart(self):
        ep = harness.episode(harness.OracleBackend(), self.task, "gen-render", 3, 1)
        self.assertTrue(ep["success_selected"])
        self.assertTrue(ep["success_at_1"])
        self.assertTrue(ep["generation_hidden_pass"])
        self.assertEqual(ep["rounds_used"], 2)
        s = harness.summarize([ep, harness.episode(harness.OracleBackend(), self.task, "render", 3, 1)], resamples=50)
        self.assertEqual(set(s["arms"]), {"gen-render", "render"})

    def test_gen_render_stops_when_generation_does_not_parse(self):
        ep = harness.episode(Scripted([fenced("tlvm", "fn zz(q: Int) -> Int = ) entry zz")]), self.task, "gen-render", 3, 1)
        self.assertFalse(ep["success_selected"])
        self.assertIsNone(ep["api_error"])
        self.assertEqual(ep["rounds_used"], 1)
        self.assertEqual(len(ep["rounds"]), 1)
        self.assertEqual((ep["outcome"], ep["outcome_detail"]), ("rejected", "parse"))

    # ------------------------------------------------------------------------------------------ 集計

    def test_summary(self):
        eps = [harness.episode(harness.OracleBackend(), self.task, "lptl", 3, 1),
               harness.episode(Scripted([fenced("tlvm", WRONG)]), self.task, "lptl", 1, 2),
               harness.episode(Scripted([BackendError("cli-error")]), self.task, "lptl", 1, 3),
               harness.episode(harness.OracleBackend(), self.task, "python", 3, 1)]
        s = harness.summarize(eps, resamples=100)
        a = s["arms"]["lptl"]
        self.assertEqual(s["summary_format"], 2)
        self.assertEqual((a["episodes"], a["success_selected"]), (3, 1))  # 試験基盤の事故も分母に入る
        self.assertEqual(a["outcomes"]["wrong_answer"], 1)
        self.assertEqual(a["infra_faults"], {"count": 1, "episodes": ["lptl/01-sum/r3"], "kinds": {"cli-error": 1}})
        self.assertEqual(a["secondary"]["success_at_1"], 1)
        self.assertFalse(s["primary_comparisons"]["claimed"])
        self.assertEqual(set(s["paired_bootstrap"]["arms"]), {"lptl", "python"})
        self.assertEqual(s["paired_bootstrap"]["differences"][0]["arms"], ["lptl", "python"])
        config = {"run_id": "x", "backend": "claude-cli:model-under-test", "backend_kind": "claude-cli", "effort": "low",
                  "rounds": 3, "repeats": 1, "tasks": 1, "skill_sha256": "0" * 64}
        md = harness.summary_markdown(s, config)
        self.assertIn("| lptl | 3 | 1 (33%) |", md)
        self.assertIn("lptl: 1 (cli-error ×1): lptl/01-sum/r3", md)
        self.assertNotIn("model-under-test", md)  # モデルの版の識別子は summary に書かない
        self.assertNotIn("model-under-test", json.dumps(s))

    def test_summary_restricts_nolet_comparisons_to_let_free_tasks(self):
        tasks = load_tasks(["sum", "shapes_area"])
        free = harness.let_free_tasks(tasks)
        self.assertEqual(free, ["01-sum"])
        eps = [harness.episode(harness.OracleBackend(), t, arm, 1, 1) for t in tasks for arm in ("lptl", "lptl-nolet")]
        reg = {"alpha": 0.05, "comparisons": [{"id": "v1-nolet", "arms": ["lptl", "lptl-nolet"]}]}
        s = harness.summarize(eps, resamples=100, registry=reg, let_free=free)
        diff = s["paired_bootstrap"]["differences"][0]
        self.assertEqual((diff["arms"], diff["tasks"], diff["estimate"]), (["lptl", "lptl-nolet"], 1, 0.0))
        self.assertEqual(s["primary_comparisons"]["results"][0]["tasks"], 1)


FAKE_CLI = """#!/usr/bin/env python3
import json, os, sys
prompt = sys.stdin.read()
with open({log!r}, "a") as f:
    f.write(json.dumps({{"argv": sys.argv[1:], "cwd": os.getcwd(), "files": os.listdir("."), "prompt": prompt}}) + "\\n")
mode = {mode!r}
usage = {{"input_tokens": 3, "output_tokens": 4, "cache_read_input_tokens": 50, "cache_creation_input_tokens": 7}}
out = {{"type": "result", "is_error": False, "stop_reason": "end_turn", "num_turns": 1, "usage": usage,
        "modelUsage": {{"model-under-test": {{}}, "aux-haiku-helper": {{}}}}, "total_cost_usd": 0.001}}
if mode == "repair":
    code = {ref!r} if "<turn" in prompt else "fn sum(xs: List<Int>) -> Int = xs entry sum"
    out["result"] = "```tlvm\\n" + code + "\\n```"
elif mode == "schema":
    schema = sys.argv[sys.argv.index("--json-schema") + 1]
    out.update(result="", num_turns=3, structured_output={ast})
elif mode == "error":
    out.update(is_error=True, subtype="error_during_execution", result="API Error: overloaded", num_turns=1)
print(json.dumps(out))
"""


class ClaudeCliTest(unittest.TestCase):
    def run_fake(self, mode, arm, **kw):
        task = load_tasks(["sum"])[0]
        ref = (task["dir"] / "reference.tlvm").read_text()
        ast = harness.run_ast(ref)["ast"]
        with tempfile.TemporaryDirectory() as d:
            log = Path(d) / "log.jsonl"
            fake = Path(d) / "claude"
            fake.write_text(FAKE_CLI.format(log=str(log), mode=mode, ref=ref, ast=repr(ast)))
            fake.chmod(0o755)
            backend = harness.ClaudeCliBackend(kw.pop("model", "model-under-test"), "low", str(fake), retries=0)
            ep = harness.episode(backend, task, arm, kw.pop("rounds", 3), 1, kw.pop("budget", big_budget(requests=5)))
            calls = [json.loads(line) for line in log.read_text().splitlines()]
        return ep, calls

    def test_cli_backend_repairs_through_transcript(self):
        """偽の claude で、引数・作業ディレクトリ・修復の回の書き起こし・使用量の記録を確かめる。"""
        ep, calls = self.run_fake("repair", "lptl")
        self.assertEqual((ep["success_at_1"], ep["success_selected"], ep["rounds_used"]), (False, True, 2))
        self.assertEqual(ep["rounds"][0]["model"], "model-under-test")  # 補助の Haiku は除く
        argv = calls[0]["argv"]
        self.assertEqual(argv[argv.index("--tools") + 1], "")
        self.assertEqual(argv[argv.index("--system-prompt") + 1], harness.SKILL)
        self.assertNotIn("--json-schema", argv)
        self.assertEqual(calls[0]["files"], [])
        self.assertNotEqual(os.path.realpath(calls[0]["cwd"]), os.path.realpath(harness.EVAL))
        self.assertNotIn("<turn", calls[0]["prompt"])
        self.assertIn('<turn role="assistant">', calls[1]["prompt"])
        self.assertIn("E-TYPE-RETURN", calls[1]["prompt"])
        self.assertEqual(ep["budget"]["used"]["input_tokens"], 2 * 60)
        self.assertEqual(ep["budget"]["input_breakdown"]["cache_read_input_tokens"], 100)
        self.assertEqual(ep["rounds"][0]["cost_usd"], 0.001)

    def test_cli_backend_keeps_a_haiku_model_under_test(self):
        ep, _ = self.run_fake("repair", "lptl", model="aux-haiku-helper", rounds=1)
        self.assertEqual(ep["rounds"][0]["model"], "model-under-test,aux-haiku-helper")

    def test_cli_backend_passes_the_schema_for_ast_schema(self):
        ep, calls = self.run_fake("schema", "ast-schema")
        argv = calls[0]["argv"]
        self.assertEqual(json.loads(argv[argv.index("--json-schema") + 1]), json.loads(harness.AST_SCHEMA_PATH.read_text()))
        self.assertTrue(ep["success_selected"])
        self.assertEqual(ep["budget"]["used"]["requests"], 3)  # CLI の中の要求（num_turns）も数える

    def test_cli_error_is_an_infrastructure_fault_and_is_not_retried(self):
        ep, calls = self.run_fake("error", "lptl")
        self.assertEqual(len(calls), 1)
        self.assertEqual((ep["outcome"], ep["outcome_detail"]), ("infra_fault", "cli-error"))
        self.assertEqual(ep["budget"]["used"]["output_tokens"], 4)


class MainTest(unittest.TestCase):
    """main（protocol の実行）を oracle で一題だけ回す。モデルは呼ばない。"""

    def run_main(self, *args, config=None, env_extra=None, model="model-under-test"):
        env = {k: v for k, v in os.environ.items() if k != HIDDEN_SEED_ENV}
        env.update(env_extra or {})
        with tempfile.TemporaryDirectory() as d:
            argv = [sys.executable, str(EVAL / "harness.py"), "--backend", "oracle", "--tasks", "sum", "--out", d, *args]
            if model is not None:
                argv += ["--model", model]
            if config is not None:
                cfg = Path(d) / "protocol.json"
                cfg.write_text(json.dumps(config), encoding="utf-8")
                argv += ["--protocol", str(cfg)]
            p = subprocess.run(argv, capture_output=True, text=True, env=env, timeout=600)
            runs = [r for r in Path(d).iterdir() if r.is_dir()]
            files = {f.name: f.read_text(encoding="utf-8") for r in runs for f in r.iterdir()}
        return p, runs, files

    def config(self, **over):
        cfg = {"hidden_set_location": "/nonexistent/secret-tasks", "repeats": 1,
               "budget": {"input_tokens": 200000, "output_tokens": 50000, "requests": 3, "verification_calls": 40},
               "cli_limits": "cli-defaults", "publication_scope": "summary-only"}
        cfg.update(over)
        return cfg

    def test_protocol_run_fails_closed_without_owner_decisions(self):
        cfg = self.config()
        del cfg["budget"], cfg["repeats"]
        p, runs, _ = self.run_main("--arms", "lptl", config=cfg)
        self.assertEqual(p.returncode, 2)
        self.assertIn("budget", p.stderr)
        self.assertIn("repeats", p.stderr)
        self.assertEqual(runs, [])

    def test_protocol_run_rejects_conflicting_options(self):
        for args, word in ((["--repeats", "2"], "--repeats"), (["--rounds", "2"], "--rounds"), (["--rep", "2"], "--rep")):
            p, runs, _ = self.run_main("--arms", "lptl", *args, config=self.config())
            self.assertEqual(p.returncode, 2, p.stderr)
            self.assertIn(word, p.stderr)
            self.assertEqual(runs, [])
        p, _, _ = self.run_main("--arms", "lptl", "--backend", "claude-cli", config=self.config())
        self.assertEqual(p.returncode, 2)
        self.assertIn("--effort", p.stderr)

    def test_model_has_no_default(self):
        # モデルの版の識別子はリポジトリに書かないので、既定値に頼る実行はできない
        for args in (["--backend", "claude-cli"], ["--backend", "anthropic"], []):
            p, runs, _ = self.run_main("--arms", "lptl", *args, model=None)
            self.assertEqual(p.returncode, 2, p.stderr)
            self.assertIn("--model", p.stderr)
            self.assertEqual(runs, [])

    def test_secret_task_set_fails_closed_without_the_seed(self):
        p, runs, _ = self.run_main("--arms", "lptl", "--task-set", "secret", config=self.config())
        self.assertEqual(p.returncode, 2)
        self.assertIn(HIDDEN_SEED_ENV, p.stderr)
        self.assertEqual(runs, [])

    def test_unimplemented_arms_name_the_missing_decision(self):
        p, _, _ = self.run_main("--arms", "python-restricted")
        self.assertEqual(p.returncode, 2)
        self.assertIn("§2b", p.stderr)

    def test_protocol_run_with_the_oracle(self):
        p, runs, files = self.run_main("--arms", "lptl,python", config=self.config())
        self.assertEqual(p.returncode, 0, p.stderr)
        self.assertEqual(len(runs), 1)
        config = json.loads(files["config.json"])
        self.assertEqual(config["mode"], "protocol")
        self.assertEqual(config["protocol"]["budget"]["requests"], 3)
        self.assertIsNone(config["rounds"])
        self.assertEqual(json.loads(files["publish.json"]),
                         {"scope": "summary-only", "task_set": "public", "files": ["summary.json", "summary.md"]})
        self.assertEqual(set(config["git"]), {"commit", "dirty"})
        summary = json.loads(files["summary.json"])
        self.assertEqual(summary["arms"]["lptl"]["success_selected"], 1)
        self.assertEqual(summary["paired_bootstrap"]["resamples"], 10_000)
        self.assertFalse(summary["primary_comparisons"]["claimed"])
        self.assertIn("budget B: input ≤ 200000 tokens", files["summary.md"])
        episode = json.loads(files["episodes.jsonl"].splitlines()[0])
        self.assertEqual(episode["budget"]["limit"]["verification_calls"], 40)

    def test_pilot_run_with_the_oracle(self):
        p, runs, files = self.run_main("--arms", "lptl", "--rounds", "2")
        self.assertEqual(p.returncode, 0, p.stderr)
        self.assertEqual(json.loads(files["config.json"])["mode"], "pilot")
        self.assertNotIn("publish.json", files)
        self.assertIn("no budget B (pilot)", files["summary.md"])


if __name__ == "__main__":
    unittest.main()
