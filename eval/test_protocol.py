"""evaluation-protocol-v1 草案の、オーナーの決定に依らない規則を確かめる（モデルも tlvm も使わない）。

- 必須の設定が欠けると止まること（§9）
- 予算 B の四成分の guard と事後の判定（§5、設計書 §12.5 の fixture と同じ答え）
- 最終候補の選び方（§3）と失敗の分類・試験基盤の事故の判定表
- 統計（§4）：課題単位の対応ブートストラップ、Holm 法、主要比較の一覧
- 秘密の課題集合の種（§6、§9 の 1）

usage: python3 -m unittest discover -s eval -p 'test_*.py'
"""

import json
import os
import subprocess
import tempfile
import unittest
from pathlib import Path

import protocol as P
import stats as S
import tasks_lib as T
from runner import find_let, line_col, nolet_rejection

REPO = T.EVAL.parent
SPEC_CASES = REPO / "spec" / "lptl-v1" / "v1_check_inputs.json"


def full_config(**over) -> dict:
    cfg = {
        "hidden_set_location": "/nonexistent/secret-tasks",
        "repeats": 3,
        "budget": {"input_tokens": 1000, "output_tokens": 500, "requests": 3, "verification_calls": 20},
        "cli_limits": "cli-defaults",
        "publication_scope": "summary-only",
    }
    cfg.update(over)
    return cfg


def spec_cases(kind: str) -> list[dict]:
    return [c for c in json.loads(SPEC_CASES.read_text(encoding="utf-8"))["cases"] if c["kind"] == kind]


class ConfigTest(unittest.TestCase):
    def test_complete_config_loads(self):
        c = P.load_protocol_config({**full_config(), "_comment": "free text"})
        self.assertEqual(c.repeats, 3)
        self.assertEqual(c.budget.vector(), [1000, 500, 3, 20])
        self.assertEqual(c.as_dict()["budget"]["requests"], 3)

    def test_every_owner_decision_is_required(self):
        for key in P.CONFIG_KEYS:
            for missing in ({k: v for k, v in full_config().items() if k != key}, full_config(**{key: None})):
                with self.assertRaises(P.ProtocolConfigError) as cm:
                    P.load_protocol_config(missing)
                self.assertIn(key, str(cm.exception))
        with self.assertRaises(P.ProtocolConfigError) as cm:
            P.load_protocol_config({})
        for key in P.CONFIG_KEYS:  # 欠けた項目をすべて並べる
            self.assertIn(key, str(cm.exception))

    def test_no_value_is_defaulted_or_coerced(self):
        bad = [
            full_config(repeats=0), full_config(repeats=True), full_config(repeats="3"), full_config(repeats=2.0),
            full_config(budget={"input_tokens": 1, "output_tokens": 1, "requests": 1}),
            full_config(budget={"input_tokens": 1, "output_tokens": 1, "requests": 1, "verification_calls": 0}),
            full_config(budget={"input_tokens": 1, "output_tokens": 1, "requests": True, "verification_calls": 1}),
            full_config(budget={"input_tokens": 1, "output_tokens": 1, "requests": 1, "verification_calls": 1, "usd": 1}),
            full_config(budget=[1, 1, 1, 1]),
            full_config(cli_limits="default"), full_config(publication_scope="everything"),
            full_config(hidden_set_location=""), full_config(hidden_set_location=3),
            {**full_config(), "seed": "x"},
        ]
        for cfg in bad:
            with self.assertRaises(P.ProtocolConfigError, msg=cfg):
                P.load_protocol_config(cfg)

    def test_config_file(self):
        with tempfile.TemporaryDirectory() as d:
            p = Path(d) / "protocol.json"
            p.write_text(json.dumps(full_config()), encoding="utf-8")
            self.assertEqual(P.load_protocol_config(p).cli_limits, "cli-defaults")
            p.write_text("{not json", encoding="utf-8")
            with self.assertRaises(P.ProtocolConfigError):
                P.load_protocol_config(p)
            with self.assertRaises(P.ProtocolConfigError):
                P.load_protocol_config(Path(d) / "missing.json")


class BudgetTest(unittest.TestCase):
    def meter(self, i=1000, o=500, r=3, v=20):
        return P.BudgetMeter(P.Budget(i, o, r, v))

    def test_input_estimate_uses_the_previous_actual(self):
        m = self.meter()
        self.assertEqual(P.estimate_tokens(11), 6)  # 11 / 2.0 を切り上げ
        self.assertEqual(m.estimate_input(11), 6)
        m.record_request({"input_tokens": 2, "output_tokens": 5, "cache_read_input_tokens": 90,
                          "cache_creation_input_tokens": 8}, n_bytes=200)
        self.assertEqual(m.estimate_input(300), 100 + P.estimate_tokens(100))

    def test_cache_tokens_count_as_input_and_are_recorded_apart(self):
        m = self.meter()
        u = m.record_request({"input_tokens": 3, "output_tokens": 7, "cache_read_input_tokens": 40,
                              "cache_creation_input_tokens": 50})
        self.assertEqual(u["logical_input_tokens"], 93)
        self.assertEqual(m.used, {"input_tokens": 93, "output_tokens": 7, "requests": 1, "verification_calls": 0})
        self.assertEqual(m.snapshot()["input_breakdown"],
                         {"input_tokens": 3, "cache_read_input_tokens": 40, "cache_creation_input_tokens": 50})
        self.assertTrue(m.snapshot()["measurement_valid"])

    def test_guard_before_each_request(self):
        m = self.meter(i=100, r=2)
        self.assertIsNone(m.guard_request(100))  # ちょうど上限は許す
        self.assertEqual(m.guard_request(101), ("operation_guarded", "input_tokens"))
        m.record_request({"input_tokens": 60, "output_tokens": 1})
        self.assertEqual(m.guard_request(41), ("operation_guarded", "input_tokens"))
        m.record_request({"input_tokens": 1, "output_tokens": 1})
        self.assertEqual(m.guard_request(0), ("budget_reached", "requests"))

    def test_guard_stops_when_output_or_verification_is_used_up(self):
        m = self.meter(o=10, v=5)
        m.record_request({"input_tokens": 1, "output_tokens": 10})
        self.assertEqual(m.guard_request(1), ("budget_reached", "output_tokens"))
        m = self.meter(v=5)
        self.assertIsNone(m.guard_verification(5))
        self.assertEqual(m.guard_verification(6), ("operation_guarded", "verification_calls"))
        m.record_verification(5)
        self.assertEqual(m.guard_request(1), ("budget_reached", "verification_calls"))

    def test_exceeding_any_component_is_detected_after_the_fact(self):
        m = self.meter(o=10)
        m.record_request({"input_tokens": 1, "output_tokens": 10})
        self.assertEqual(m.exceeded(), [])
        m = self.meter(o=10)
        m.record_request({"input_tokens": 1, "output_tokens": 11})
        self.assertEqual(m.exceeded(), ["output_tokens"])
        m = self.meter(r=1)
        m.record_request({"input_tokens": 1, "output_tokens": 1}, model_requests=3)  # CLI の中の再試行も要求に数える
        self.assertEqual(m.exceeded(), ["requests"])

    def test_unreadable_usage_invalidates_the_measurement(self):
        for usage in (None, {}, {"input_tokens": -1, "output_tokens": 1}, {"input_tokens": 1.5, "output_tokens": 1},
                      {"input_tokens": 1, "output_tokens": 1, "cache_read_input_tokens": "9"}):
            m = self.meter()
            m.record_request(usage)
            self.assertFalse(m.snapshot()["measurement_valid"], usage)
        m = self.meter()
        m.record_request({"input_tokens": 1, "output_tokens": 1}, model_requests=None)
        self.assertEqual(m.invalid, ["model_requests"])

    def test_no_budget_records_only(self):
        m = P.BudgetMeter(None)
        m.record_request({"input_tokens": 10 ** 9, "output_tokens": 10 ** 9})
        self.assertIsNone(m.guard_request(10 ** 9))
        self.assertEqual(m.exceeded(), [])
        self.assertIsNone(m.remaining("requests"))


class SelectionTest(unittest.TestCase):
    def test_last_accepted_candidate_ignoring_hidden_results(self):
        cands = [{"accepted": True, "hidden_pass": True}, {"accepted": True, "hidden_pass": False},
                 {"accepted": False, "hidden_pass": False}]
        self.assertEqual(P.select_final(cands), 1)
        end = P.budget_end([1, 1, 1, 1], [9, 9, 9, 9], "normal_stop", cands)
        self.assertEqual((end["selected"], end["success"]), (1, 0))  # 隠しテストを通した候補 0 を選び直さない
        self.assertIsNone(P.select_final([{"accepted": False, "hidden_pass": True}]))
        self.assertIsNone(P.select_final([]))

    def test_budget_end_matches_the_design_fixtures(self):
        cases = spec_cases("budget_end_model")
        self.assertEqual(len(cases), 5)
        for c in cases:
            a = c["input"]
            self.assertEqual(P.budget_end(a["observed"], a["limit"], a["stop_reason"], a["candidates"]), c["expected"], c["id"])

    def test_budget_vector_matches_the_design_fixtures(self):
        cases = spec_cases("budget_vector")
        self.assertEqual(len(cases), 4)
        for c in cases:
            self.assertEqual(P.budget_vector_ok(c["input"]["observed"], c["input"]["limit"]), c["expected"], c["id"])

    def test_episode_aggregation_matches_the_design_fixtures(self):
        for c in spec_cases("episode_aggregation"):
            a = c["input"]
            limit = [1, 1, 1, 1]
            end = P.budget_end(limit if a["budget_ok"] else [2, 1, 1, 1], limit, "normal_stop", a["candidates"])
            self.assertEqual((end["selected"], end["success"]), (c["expected"]["selected"], c["expected"]["successes"]),
                             c["id"])

    def test_budget_end_without_a_budget_or_with_a_bad_measurement(self):
        cands = [{"accepted": True, "hidden_pass": True}]
        self.assertEqual(P.budget_end(None, None, "normal_stop", cands)["success"], 1)
        self.assertEqual(P.budget_end(None, [1, 1, 1, 1], "normal_stop", cands)["reason"], "invalid_budget_measurement")
        over = P.budget_end([2, 1, 1, 1], [1, 1, 1, 1], "normal_stop", cands)
        self.assertEqual((over["reason"], over["success"]), ("budget_exceeded", 0))


class OutcomeTest(unittest.TestCase):
    ok_end = {"reason": "normal_stop", "budget_ok": True, "selected": 0, "success": 1}
    none_end = {"reason": "no_accepted_candidate", "budget_ok": True, "selected": None, "success": 0}

    def test_episode_outcome_rules(self):
        O = P.Outcome
        self.assertEqual(P.episode_outcome(self.ok_end, (O.SUCCESS, ""), "normal_stop", "", None), (O.SUCCESS, ""))
        self.assertEqual(P.episode_outcome(self.ok_end, (O.WRONG_ANSWER, "wrong-output"), "normal_stop", "", None)[0],
                         O.WRONG_ANSWER)
        self.assertEqual(P.episode_outcome(self.ok_end, (O.SUCCESS, ""), "infra_fault", "cli-error", None),
                         (O.INFRA_FAULT, "cli-error"))
        exceeded = {"reason": "budget_exceeded", "budget_ok": False, "selected": 0, "success": 0}
        self.assertEqual(P.episode_outcome(exceeded, (O.SUCCESS, ""), "budget_exceeded", "output_tokens", None),
                         (O.BUDGET_EXCEEDED, "output_tokens"))
        invalid = {"reason": "invalid_budget_measurement", "budget_ok": False, "selected": None, "success": 0}
        self.assertEqual(P.episode_outcome(invalid, None, "normal_stop", "", None)[0], O.INFRA_FAULT)
        # 受理された候補がなければ、生成の失敗・候補なし・最後の候補の拒否の段階
        self.assertEqual(P.episode_outcome(self.none_end, None, "generation_failure", "refusal", {"has_code": False}),
                         (O.GENERATION_FAILURE, "refusal"))
        self.assertEqual(P.episode_outcome(self.none_end, None, "operation_guarded", "input_tokens", None),
                         (O.NO_CANDIDATE, "input_tokens"))
        self.assertEqual(P.episode_outcome(self.none_end, None, "normal_stop", "", {"has_code": False, "phase": None})[0],
                         O.NO_CANDIDATE)
        self.assertEqual(P.episode_outcome(self.none_end, None, "normal_stop", "", {"has_code": True, "phase": "type"}),
                         (O.REJECTED, "type"))
        # 選んだ候補があれば、その後の生成の失敗では決まらない
        self.assertEqual(P.episode_outcome(self.ok_end, (O.HOST_ABORTED, "host-aborted"), "generation_failure",
                                           "refusal", None)[0], O.HOST_ABORTED)

    def test_every_failure_category_is_an_outcome(self):
        self.assertEqual(len(P.FAILURE_CATEGORIES), 8)
        self.assertEqual(set(P.Outcome) - set(P.FAILURE_CATEGORIES), {P.Outcome.SUCCESS, P.Outcome.INFRA_FAULT})

    def test_case_classification(self):
        O = P.Outcome
        lptl = [
            ({"result": "fail"}, O.WRONG_ANSWER),
            ({"result": "error", "reason": "HostAborted stack"}, O.HOST_ABORTED),
            ({"result": "error", "reason": "ResourceExhausted steps (observed 10, limit 10)"}, O.RESOURCE_EXCEEDED),
            ({"result": "error", "reason": "input を型 Int として読めません"}, O.INVALID_INPUT),
            ({"result": "error", "reason": "expected を型 Int として読めません"}, O.INFRA_FAULT),
            ({"result": "error", "reason": "InternalFault x"}, O.INFRA_FAULT),
            ({"result": "error", "reason": "something new"}, O.INFRA_FAULT),
        ]
        for case, want in lptl:
            self.assertEqual(P.classify_case(case, "tlvm")[0], want, case)
        self.assertEqual(P.classify_case({"result": "error", "reason": "RecursionError: deep"}, "python")[0],
                         O.RESOURCE_EXCEEDED)
        self.assertEqual(P.classify_case({"result": "error", "reason": "IndexError: list index"}, "python"),
                         (O.WRONG_ANSWER, "runtime-error:IndexError"))

    def test_run_classification(self):
        O = P.Outcome
        run = {"compile_ok": True, "signature_ok": True, "all_pass": False, "codes": [], "infra": None,
               "cases": [{"result": "fail"}, {"result": "error", "reason": "ResourceExhausted steps"},
                         {"result": "error", "reason": "HostAborted x"}]}
        self.assertEqual(P.classify_run(run, "tlvm")[0], O.HOST_ABORTED)  # 優先順：HostAborted が資源超過と誤答より先
        self.assertEqual(P.classify_run({**run, "all_pass": True, "cases": []}, "tlvm")[0], O.SUCCESS)
        self.assertEqual(P.classify_run({**run, "infra": "tlvm-exit"}, "tlvm"), (O.INFRA_FAULT, "tlvm-exit"))
        self.assertEqual(P.classify_run({**run, "compile_ok": False}, "tlvm"), (O.INFRA_FAULT, "rerun-rejected"))
        crash = {"compile_ok": False, "signature_ok": False, "all_pass": False, "codes": ["Crash"], "cases": []}
        self.assertEqual(P.classify_run(crash, "python"), (O.HOST_ABORTED, "python-crash"))
        timeout = {"compile_ok": True, "signature_ok": True, "all_pass": False, "codes": ["Timeout"], "cases": []}
        self.assertEqual(P.classify_run(timeout, "python"), (O.RESOURCE_EXCEEDED, "python-timeout"))

    def test_backend_failure_table(self):
        O = P.Outcome
        self.assertFalse(set(P.INFRA_TABLE) & set(P.GENERATION_FAILURE_TABLE))
        for kind in P.CLI_ERROR_SUBTYPES.values():
            self.assertIn(kind, {**P.INFRA_TABLE, **P.GENERATION_FAILURE_TABLE})

        class APIError(Exception):
            pass

        class APIStatusError(APIError):
            pass

        class APIConnectionError(APIError):
            pass

        class APITimeoutError(APIConnectionError):
            pass

        cases = [
            (P.BackendError("cli-error", "overloaded"), (O.INFRA_FAULT, "cli-error")),
            (P.BackendError("cli-structured-output-retries"), (O.GENERATION_FAILURE, "cli-structured-output-retries")),
            (P.BackendError("no-such-kind"), (O.INFRA_FAULT, "backend-other")),
            (subprocess.TimeoutExpired("claude", 1), (O.INFRA_FAULT, "cli-timeout")),
            (FileNotFoundError("claude"), (O.INFRA_FAULT, "cli-unavailable")),
            (APIStatusError("529"), (O.INFRA_FAULT, "api-status")),
            (APITimeoutError("t"), (O.INFRA_FAULT, "api-connection")),
            (ValueError("x"), (O.INFRA_FAULT, "backend-other")),
        ]
        for exc, want in cases:
            self.assertEqual(P.classify_backend_error(exc), want, exc)
        e = P.BackendError("cli-max-turns", "d", usage={"input_tokens": 1, "output_tokens": 2}, requests=2)
        self.assertEqual((e.usage["output_tokens"], e.requests), (2, 2))


class NoLetTest(unittest.TestCase):
    def test_find_let_is_lexical(self):
        self.assertEqual(find_let("fn f(x: Int) -> Int = let y = x in y"), 22)
        self.assertIsNone(find_let("// let me explain\nfn f(letter: Int) -> Int = add(letter, 1)"))
        self.assertIsNone(find_let('fn f(x: Int) -> String = "let it be" entry f'))
        self.assertIsNone(find_let("fn f(x: Char) -> Bool = eq(x, '\\'') entry f"))
        src = "fn f(x: Int) -> Int =\n  let_x(x)\n  let"
        self.assertEqual(find_let(src), src.rindex("let"))

    def test_rejection_points_at_the_let(self):
        src = "fn f(x: Int) -> Int =\n  let y = x in y\nentry f\n"
        r = nolet_rejection(src, find_let(src))
        self.assertEqual((r["compile_ok"], r["codes"], r["phase"]), (False, ["NoLet"], "parse"))
        self.assertEqual(r["errors"][0]["start"], (2, 3))
        self.assertIn("solution.tlvm:2:3: error[NoLet]", r["diagnostics"])
        self.assertIn("repair:", r["diagnostics"])
        self.assertEqual(line_col("aé\nb".encode(), 5), (2, 2))


class StatsTest(unittest.TestCase):
    def test_wilson(self):
        self.assertEqual(S.wilson(0, 0), (0.0, 0.0))
        lo, hi = S.wilson(8, 10)
        self.assertAlmostEqual(lo, 0.4902, places=3)
        self.assertAlmostEqual(hi, 0.9433, places=3)

    def test_percentile_interpolates(self):
        self.assertEqual(S.percentile([3, 1, 2, 4], 0.5), 2.5)
        self.assertEqual(S.percentile([5], 0.975), 5)
        lo, hi = S.interval(list(range(101)), 0.95)
        self.assertAlmostEqual(lo, 2.5)
        self.assertAlmostEqual(hi, 97.5)

    def test_paired_bootstrap_shares_resampled_tasks_across_arms(self):
        scores = {"a": [1.0, 0.0, 1.0, 0.5], "b": [1.0, 0.0, 1.0, 0.5], "c": [0.0, 1.0, 0.0, 0.5]}
        means = S.paired_bootstrap(scores, 500, seed=7)
        self.assertEqual(means["a"], means["b"])  # 同じ値の arm は、同じ再標本でまったく同じ平均になる
        # a と c は課題ごとに 1 − x の関係なので、同じ再標本なら平均の和は常に 1
        self.assertTrue(all(abs(x + y - 1) < 1e-12 for x, y in zip(means["a"], means["c"])))
        self.assertEqual(S.difference(means["a"], means["b"])["ci"], [0.0, 0.0])
        self.assertEqual(S.paired_bootstrap(scores, 500, seed=7), means)  # 同じ種なら同じ結果
        with self.assertRaises(ValueError):
            S.paired_bootstrap({"a": [1.0], "b": [1.0, 0.0]}, 10)

    def test_default_is_ten_thousand_resamples_at_95_percent(self):
        self.assertEqual((S.BOOTSTRAP_RESAMPLES, S.BOOTSTRAP_LEVEL), (10_000, 0.95))
        means = S.paired_bootstrap({"a": [1.0, 0.0, 1.0, 1.0, 0.0]}, seed=S.bootstrap_seed(["t1", "t2"]))
        self.assertEqual(len(means["a"]), 10_000)

    def test_bootstrap_on_synthetic_data_with_a_fixed_seed(self):
        tasks = [f"t{i:02d}" for i in range(40)]
        better = [1.0] * 30 + [0.0] * 10
        worse = [1.0] * 20 + [0.0] * 20
        seed = S.bootstrap_seed(tasks)
        self.assertEqual(seed, S.bootstrap_seed(list(reversed(tasks))))  # 課題の集合だけで決まる
        means = S.paired_bootstrap({"better": better, "worse": worse}, 2000, seed)
        d = S.difference(means["better"], means["worse"])
        self.assertGreater(d["ci"][0], 0)  # 差 0.25（課題 20〜29 だけが違う）の区間は 0 を含まない
        self.assertLess(d["ci"][1], 0.5)
        self.assertLess(d["p"], 0.01)
        same = S.difference(means["better"], means["better"])
        self.assertEqual(same["p"], 1.0)
        self.assertEqual(S.paired_bootstrap({"better": better, "worse": worse}, 2000, seed), means)

    def test_holm(self):
        adj = S.holm([0.01, 0.04, 0.03, 0.005])
        for got, want in zip(adj, [0.03, 0.06, 0.06, 0.02]):
            self.assertAlmostEqual(got, want)
        self.assertEqual(S.holm([]), [])
        self.assertEqual(S.holm([0.9, 0.8]), [1.0, 1.0])

    def test_task_scores_average_repeats(self):
        eps = [{"arm": "a", "task": "t1", "success_selected": True}, {"arm": "a", "task": "t1", "success_selected": False},
               {"arm": "a", "task": "t2", "success_selected": True}, {"arm": "b", "task": "t1", "success_selected": True}]
        self.assertEqual(S.task_scores(eps, "a", ["t2", "t1"]), [1.0, 0.5])

    def write(self, d, data) -> Path:
        p = Path(d) / "primary.json"
        p.write_text(json.dumps(data), encoding="utf-8")
        return p

    def test_empty_registry_claims_nothing(self):
        with tempfile.TemporaryDirectory() as d:
            reg = S.load_registry(self.write(d, {"comparisons": []}))
        r = S.primary_comparisons(reg, [{"arm": "a", "task": "t", "success_selected": True}])
        self.assertFalse(r["claimed"])
        self.assertEqual(r["results"], [])
        committed = S.load_registry(T.EVAL / "primary_comparisons.json")
        self.assertEqual(committed["comparisons"], [])  # 登録の前は主要比較を主張しない

    def test_registry_is_validated(self):
        bad = [{}, {"comparisons": {}}, {"comparisons": [{"id": "x", "arms": ["a", "b"]}]},  # alpha がない
               {"alpha": 0.05, "comparisons": [{"id": "x", "arms": ["a", "a"]}]},
               {"alpha": 0.05, "comparisons": [{"arms": ["a", "b"]}]},
               {"alpha": 1, "comparisons": [{"id": "x", "arms": ["a", "b"]}]},
               {"alpha": 0.05, "comparisons": [{"id": "x", "arms": ["a", "b"]}, {"id": "x", "arms": ["a", "c"]}]},
               {"alpha": 0.05, "comparisons": [{"id": "x", "arms": ["a", "b"], "tasks": []}]}]
        with tempfile.TemporaryDirectory() as d:
            for data in bad:
                with self.assertRaises(S.RegistryError, msg=data):
                    S.load_registry(self.write(d, data))
            with self.assertRaises(S.RegistryError):
                S.load_registry(Path(d) / "missing.json")

    def test_primary_comparisons_use_holm_over_the_list(self):
        tasks = [f"t{i:02d}" for i in range(30)]
        eps = []
        for i, t in enumerate(tasks):
            for arm, ok in (("x", i < 25), ("y", i < 10), ("z", i < 24)):
                eps.append({"arm": arm, "task": t, "success_selected": ok})
        reg = {"alpha": 0.05, "comparisons": [{"id": "x-y", "arms": ["x", "y"]}, {"id": "x-z", "arms": ["x", "z"]}]}
        r = S.primary_comparisons(reg, eps, resamples=1000)
        self.assertTrue(r["claimed"])
        xy, xz = r["results"]
        self.assertAlmostEqual(xy["estimate"], 0.5)
        self.assertTrue(xy["reject"])
        self.assertFalse(xz["reject"])
        self.assertEqual([xy["p_holm"], xz["p_holm"]], S.holm([xy["p"], xz["p"]]))
        # 一覧の arm が実行にないと、その比較を計算せず、主要比較を主張しない
        r = S.primary_comparisons({**reg, "comparisons": reg["comparisons"] + [{"id": "q", "arms": ["x", "q"]}]}, eps, 200)
        self.assertFalse(r["claimed"])
        self.assertFalse(r["results"][2]["computed"])


class HiddenSeedTest(unittest.TestCase):
    def test_public_seed_is_the_task_id_hash(self):
        import hashlib

        self.assertEqual(T.public_seed("01-sum"), int(hashlib.sha256(b"01-sum").hexdigest()[:16], 16))

    def test_secret_seed_fails_closed_without_the_variable(self):
        for env in ({}, {T.HIDDEN_SEED_ENV: ""}, {T.HIDDEN_SEED_ENV: "  "}):
            with self.assertRaises(T.SecretSeedMissing):
                T.secret_seed("01-sum", env)
            with self.assertRaises(T.SecretSeedMissing):
                T.load_secret_tasks(T.TASKS, environ=env)

    def test_secret_seed_depends_on_the_secret_and_the_task(self):
        a, b = os.urandom(16).hex(), os.urandom(16).hex()  # 種の値をリポジトリに書かない
        env_a, env_b = {T.HIDDEN_SEED_ENV: a}, {T.HIDDEN_SEED_ENV: b}
        self.assertEqual(T.secret_seed("01-sum", env_a), T.secret_seed("01-sum", env_a))
        self.assertNotEqual(T.secret_seed("01-sum", env_a), T.secret_seed("01-sum", env_b))
        self.assertNotEqual(T.secret_seed("01-sum", env_a), T.secret_seed("02-count_even", env_a))
        self.assertNotEqual(T.secret_seed("01-sum", env_a), T.public_seed("01-sum"))

    def test_secret_task_set_generates_hidden_tests_in_memory(self):
        env = {T.HIDDEN_SEED_ENV: os.urandom(16).hex()}
        src = T.TASKS / "01-sum"
        with tempfile.TemporaryDirectory() as d:
            dst = Path(d) / "s01-sum"
            dst.mkdir()
            for f in ("task.json", "reference.py", "reference.tlvm"):
                (dst / f).write_bytes((src / f).read_bytes())
            tasks = T.load_secret_tasks(d, count=5, environ=env)
            self.assertEqual(len(tasks[0]["hidden"]), 5)
            self.assertFalse((dst / "hidden.json").exists())  # 隠しテストはファイルに書かない
            self.assertEqual(T.load_secret_tasks(d, count=5, environ=env)[0]["hidden"], tasks[0]["hidden"])
            public = json.loads((src / "hidden.json").read_text(encoding="utf-8"))[:5]
            self.assertNotEqual([c["input"] for c in tasks[0]["hidden"]], [c["input"] for c in public])
            (dst / "hidden.json").write_text("[]", encoding="utf-8")
            with self.assertRaises(RuntimeError):
                T.load_secret_tasks(d, environ=env)
        with tempfile.TemporaryDirectory() as d:
            with self.assertRaises(RuntimeError):
                T.load_secret_tasks(d, environ=env)  # 課題がない
            with self.assertRaises(FileNotFoundError):
                T.load_secret_tasks(Path(d) / "missing", environ=env)

    def test_public_hidden_tests_are_unchanged(self):
        """公開の hidden.json は、種の関数を分けたあとも公開の種から同じものが作られる（5 題で確かめる）。"""
        for d in T.task_dirs()[:5]:
            task = T.load_task(d)
            again = T.generate_hidden(task, T.reference_module(d), T.public_seed(task["id"]), len(task["hidden"]))
            self.assertEqual(again, task["hidden"], task["id"])


if __name__ == "__main__":
    unittest.main()
