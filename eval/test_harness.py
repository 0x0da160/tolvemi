"""ハーネスの採点と修復の経路を、API を使わない偽のモデルで確かめる。

usage: python3 -m unittest discover -s eval -p 'test_*.py'
"""

import os
import tempfile
import unittest
from pathlib import Path

import harness
from tasks_lib import load_tasks


class Scripted:
    """決めた答えを順に返す偽のモデル。受け取った会話を記録する。"""

    name = "scripted"

    def __init__(self, answers):
        self.answers = list(answers)
        self.seen = []

    def complete(self, system, messages, task, arm):
        self.seen.append([dict(m) for m in messages])
        text = self.answers.pop(0)
        return {"text": text, "content": text, "stop_reason": "end_turn", "usage": {"input_tokens": 1, "output_tokens": 1},
                "model": "scripted", "fallback": False}


def fenced(lang, code):
    return f"Here you go.\n```{lang}\n{code}\n```\n"


class HarnessTest(unittest.TestCase):
    def setUp(self):
        self.task = load_tasks(["sum"])[0]
        self.ref = (self.task["dir"] / "reference.tlvm").read_text()

    def test_oracle_passes_everything(self):
        for task in load_tasks():
            for arm in harness.ARMS:
                ep = harness.episode(harness.OracleBackend(), task, arm, 3, 1)
                self.assertTrue(ep["success_at_1"], (task["id"], arm, ep["rounds"][-1]))

    def test_repair_with_diagnostics(self):
        broken = "fn solve(xs: List<Int>) -> Int = fold(xs, 0, |acc, x| add(acc, y))\nentry solve"
        m = Scripted([fenced("tlvm", broken), fenced("tlvm", self.ref)])
        ep = harness.episode(m, self.task, "lptl", 3, 1)
        self.assertFalse(ep["success_at_1"])
        self.assertTrue(ep["success_final"])
        self.assertEqual(ep["rounds_used"], 2)
        self.assertEqual(ep["rounds"][0]["codes"], ["E-NAME-UNBOUND-VARIABLE"])
        repair_msg = m.seen[1][-1]["content"]
        self.assertIn("E-NAME-UNBOUND-VARIABLE", repair_msg)
        self.assertIn("variable in scope: x, acc, xs", repair_msg)

    def test_nodiag_hides_diagnostics(self):
        broken = "fn solve(xs: List<Int>) -> Int = add(xs)\nentry solve"
        m = Scripted([fenced("tlvm", broken), fenced("tlvm", broken), fenced("tlvm", broken)])
        ep = harness.episode(m, self.task, "lptl-nodiag", 3, 1)
        self.assertFalse(ep["success_final"])
        self.assertEqual(ep["rounds_used"], 3)
        self.assertNotIn("E-", m.seen[1][-1]["content"])

    def test_wrong_answer_feedback_shows_failing_examples(self):
        wrong = "fn solve(xs: List<Int>) -> Int = length(xs)\nentry solve"
        m = Scripted([fenced("tlvm", wrong), fenced("tlvm", self.ref)])
        ep = harness.episode(m, self.task, "lptl", 2, 1)
        self.assertTrue(ep["success_final"])
        self.assertIn("solve(list[Int](1, 2, 3)): expected 6, got 3", m.seen[1][-1]["content"])

    def test_wrong_signature(self):
        other = "fn main(xs: List<Int>) -> Int = 0\nentry main"
        m = Scripted([fenced("tlvm", other)])
        ep = harness.episode(m, self.task, "lptl", 1, 1)
        self.assertFalse(ep["rounds"][0]["signature_ok"])

    def test_python_arm(self):
        m = Scripted([fenced("python", "def solve(xs):\n    return sum(xs) + 1"), fenced("python", "def solve(xs):\n    return sum(xs)")])
        ep = harness.episode(m, self.task, "python", 3, 1)
        self.assertEqual((ep["success_at_1"], ep["success_final"]), (False, True))
        self.assertIn("solve([1, 2, 3]) == 6", harness.task_prompt(self.task, "python"))
        self.assertIn("solve([1, 2, 3]): expected 6, got 7", m.seen[1][-1]["content"])

    def test_python_errors_and_bad_types(self):
        m = Scripted([fenced("python", "def solve(xs):\n    return str(sum(xs))")])
        ep = harness.episode(m, self.task, "python", 1, 1)
        self.assertEqual(ep["rounds"][0]["codes"], ["TypeError"])
        m = Scripted([fenced("python", "def solve(xs) return 1")])
        ep = harness.episode(m, self.task, "python", 1, 1)
        self.assertFalse(ep["rounds"][0]["compile_ok"])

    def test_no_code_block(self):
        m = Scripted(["I cannot do that."])
        ep = harness.episode(m, self.task, "lptl", 1, 1)
        self.assertEqual(ep["rounds"][0]["codes"], ["NoCode"])

    def test_prompt_renders_lptl_literals(self):
        t = load_tasks(["min_max"])[0]
        p = harness.task_prompt(t, "lptl")
        self.assertIn("solve(list[Int]()) = none[Pair<Int, Int>]", p)
        self.assertIn("fn solve(x: List<Int>) -> Option<Pair<Int, Int>>", p)

    def test_summary(self):
        eps = [harness.episode(harness.OracleBackend(), self.task, "lptl", 3, 1)]
        s = harness.summarize(eps, 3)
        self.assertEqual(s["lptl"]["success_at_3"], 1)
        md = harness.summary_markdown(s, {"run_id": "x", "backend": "oracle", "rounds": 3, "repeats": 1, "tasks": 1, "skill_sha256": "0" * 64})
        self.assertIn("| lptl | 1 |", md)


class ClaudeCliTest(unittest.TestCase):
    def test_cli_backend_repairs_through_transcript(self):
        """偽の claude で、引数・作業ディレクトリ・修復の回の書き起こしを確かめる。"""
        task = load_tasks(["sum"])[0]
        ref = (task["dir"] / "reference.tlvm").read_text()
        with tempfile.TemporaryDirectory() as d:
            log = Path(d) / "log.jsonl"
            fake = Path(d) / "claude"
            fake.write_text(f"""#!/usr/bin/env python3
import json, os, sys
prompt = sys.stdin.read()
with open({str(log)!r}, "a") as f:
    f.write(json.dumps({{"argv": sys.argv[1:], "cwd": os.getcwd(), "files": os.listdir("."), "prompt": prompt}}) + "\\n")
code = {ref!r} if "<turn" in prompt else "fn sum(xs: List<Int>) -> Int = xs entry sum"
print(json.dumps({{"is_error": False, "result": "```tlvm\\n" + code + "\\n```", "stop_reason": "end_turn",
                  "usage": {{"input_tokens": 3, "output_tokens": 4}}, "modelUsage": {{"claude-opus-5-5": {{}}}}}}))
""")
            fake.chmod(0o755)
            backend = harness.ClaudeCliBackend("claude-opus-5-5", "low", str(fake))
            ep = harness.episode(backend, task, "lptl", rounds=3, rep=1)
            calls = [__import__("json").loads(line) for line in log.read_text().splitlines()]
        self.assertEqual((ep["success_at_1"], ep["success_final"], ep["rounds_used"]), (False, True, 2))
        self.assertEqual(ep["rounds"][0]["model"], "claude-opus-5-5")
        argv = calls[0]["argv"]
        self.assertEqual(argv[argv.index("--tools") + 1], "")
        self.assertEqual(argv[argv.index("--system-prompt") + 1], harness.SKILL)
        self.assertEqual(calls[0]["files"], [])
        self.assertNotEqual(os.path.realpath(calls[0]["cwd"]), os.path.realpath(harness.EVAL))
        self.assertNotIn("<turn", calls[0]["prompt"])
        self.assertIn('<turn role="assistant">', calls[1]["prompt"])
        self.assertIn("E-TYPE-RETURN", calls[1]["prompt"])


if __name__ == "__main__":
    unittest.main()
