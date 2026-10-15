"""集計の統計（evaluation-protocol-v1 草案 §4）。CI の python3 だけで動くように numpy を使わない。

- 比率の区間：Wilson 区間（従来どおり）
- 課題単位の対応ブートストラップ：課題を復元抽出し、同じ再標本の課題番号を比較する全 arm に使う。
  10,000 回、95% のパーセンタイル区間（線形補間）
- 主要比較：登録した一覧（primary_comparisons.json）にある比較だけを、ブートストラップの p 値と Holm 法で扱う。
  一覧が空なら主要比較を主張しない
"""

from __future__ import annotations

import hashlib
import json
import math
import random
from pathlib import Path

BOOTSTRAP_RESAMPLES = 10_000
BOOTSTRAP_LEVEL = 0.95


def wilson(k: int, n: int, z: float = 1.96) -> tuple[float, float]:
    if n == 0:
        return (0.0, 0.0)
    p = k / n
    d = 1 + z * z / n
    c = (p + z * z / (2 * n)) / d
    h = z * math.sqrt(p * (1 - p) / n + z * z / (4 * n * n)) / d
    return (max(0.0, c - h), min(1.0, c + h))


def percentile(values, q: float) -> float:
    """q（0〜1）の分位点。並べた値の間を線形補間する（numpy の既定と同じ定義）。"""
    xs = sorted(values)
    if not xs:
        raise ValueError("empty")
    pos = q * (len(xs) - 1)
    lo, hi = math.floor(pos), math.ceil(pos)
    return xs[lo] + (xs[hi] - xs[lo]) * (pos - lo)


def interval(values, level: float = BOOTSTRAP_LEVEL) -> tuple[float, float]:
    a = (1 - level) / 2
    return (percentile(values, a), percentile(values, 1 - a))


def bootstrap_seed(task_ids) -> int:
    """再標本の乱数の種。課題の集合だけから決める（結果を見る前に決まり、同じ集計を誰でも再現できる）。"""
    text = "lptl-eval-paired-bootstrap-v1\0" + "\0".join(sorted(task_ids))
    return int(hashlib.sha256(text.encode()).hexdigest()[:16], 16)


def task_scores(episodes: list[dict], arm: str, tasks: list[str], metric: str = "success_selected") -> list[float]:
    """課題ごとの値（その arm の、その課題の全反復の平均）。tasks の順に並べる。"""
    acc: dict[str, list[float]] = {}
    for e in episodes:
        if e["arm"] == arm:
            acc.setdefault(e["task"], []).append(float(bool(e[metric])))
    return [sum(acc[t]) / len(acc[t]) for t in tasks]


def paired_bootstrap(scores: dict[str, list[float]], resamples: int = BOOTSTRAP_RESAMPLES, seed: int = 0) -> dict:
    """課題単位の対応ブートストラップ。scores は arm → 課題ごとの値（全 arm で同じ課題の並び）。

    各回で課題番号を一度だけ復元抽出し、その番号を全 arm に使う。返すのは arm → 各回の平均の列（resamples 個）。
    二つの arm の差の分布は、同じ回どうしの差で求める。"""
    arms = sorted(scores)
    if not arms:
        return {}
    n = len(scores[arms[0]])
    if n == 0 or any(len(scores[a]) != n for a in arms):
        raise ValueError("every arm needs the same non-empty list of tasks")
    rng = random.Random(seed)
    population = range(n)
    means: dict[str, list[float]] = {a: [] for a in arms}
    for _ in range(resamples):
        idx = rng.choices(population, k=n)
        for a in arms:
            s = scores[a]
            means[a].append(sum(s[i] for i in idx) / n)
    return means


def difference(means_a: list[float], means_b: list[float], level: float = BOOTSTRAP_LEVEL) -> dict:
    """同じ再標本どうしの差（a − b）の区間と、両側の p 値（区間の反転。0 を含む側の割合の 2 倍、+1 の補正つき）。"""
    d = [x - y for x, y in zip(means_a, means_b)]
    lo, hi = interval(d, level)
    le = sum(1 for v in d if v <= 0)
    ge = sum(1 for v in d if v >= 0)
    p = min(1.0, 2 * (min(le, ge) + 1) / (len(d) + 1))
    return {"ci": [lo, hi], "p": p}


def holm(pvalues: list[float]) -> list[float]:
    """Holm 法で調整した p 値（入力と同じ順）。"""
    m = len(pvalues)
    order = sorted(range(m), key=lambda i: pvalues[i])
    adjusted = [0.0] * m
    running = 0.0
    for rank, i in enumerate(order):
        running = max(running, min(1.0, (m - rank) * pvalues[i]))
        adjusted[i] = running
    return adjusted


# ---------------------------------------------------------------------------------------------- 主要比較の一覧


class RegistryError(ValueError):
    pass


def load_registry(path) -> dict:
    """主要比較の一覧を読む。comparisons が空なら主要比較を主張しない。空でなければ alpha（有意水準）が要る。"""
    try:
        data = json.loads(Path(path).read_text(encoding="utf-8"))
    except (OSError, ValueError) as e:
        raise RegistryError(f"主要比較の一覧を読めません: {path}: {e}") from None
    comps = data.get("comparisons") if isinstance(data, dict) else None
    if not isinstance(comps, list):
        raise RegistryError("主要比較の一覧には comparisons（list）が要ります")
    problems = []
    ids = set()
    for c in comps:
        arms = c.get("arms") if isinstance(c, dict) else None
        if not isinstance(c, dict) or not isinstance(c.get("id"), str) or not c["id"]:
            problems.append(f"比較には id が要ります: {c!r}")
            continue
        if c["id"] in ids:
            problems.append(f"id が重複しています: {c['id']}")
        ids.add(c["id"])
        if not (isinstance(arms, list) and len(arms) == 2 and all(isinstance(a, str) for a in arms) and arms[0] != arms[1]):
            problems.append(f"{c['id']}: arms は異なる二つの arm の名前です")
        tasks = c.get("tasks")
        if tasks is not None and not (isinstance(tasks, list) and tasks and all(isinstance(t, str) for t in tasks)):
            problems.append(f"{c['id']}: tasks は課題 ID の空でない list（省略すると両 arm に共通の全課題）です")
    alpha = data.get("alpha")
    if comps and not (isinstance(alpha, (int, float)) and not isinstance(alpha, bool) and 0 < alpha < 1):
        problems.append("主要比較があるときは alpha（0 と 1 の間）が要ります")
    if problems:
        raise RegistryError("主要比較の一覧が不正です:\n- " + "\n- ".join(problems))
    return {"comparisons": comps, "alpha": alpha if comps else None}


def primary_comparisons(registry: dict, episodes: list[dict], resamples: int = BOOTSTRAP_RESAMPLES,
                        level: float = BOOTSTRAP_LEVEL, metric: str = "success_selected") -> dict:
    """一覧の比較ごとに、課題単位の対応ブートストラップで差（arms[0] − arms[1]）の区間と p 値を求め、Holm 法で調整する。"""
    comps = registry["comparisons"]
    if not comps:
        return {"claimed": False, "note": "主要比較は一覧にないので、主張しない", "results": []}
    present = {e["arm"] for e in episodes}
    results = []
    for c in comps:
        a, b = c["arms"]
        if a not in present or b not in present:
            results.append({"id": c["id"], "arms": [a, b], "computed": False, "note": "この実行にない arm がある"})
            continue
        tasks_a = {e["task"] for e in episodes if e["arm"] == a}
        tasks_b = {e["task"] for e in episodes if e["arm"] == b}
        tasks = sorted(c["tasks"]) if c.get("tasks") else sorted(tasks_a & tasks_b)
        missing = [t for t in tasks if t not in tasks_a or t not in tasks_b]
        if missing or not tasks:
            results.append({"id": c["id"], "arms": [a, b], "computed": False, "note": f"課題が欠けている: {missing[:5]}"})
            continue
        sa, sb = task_scores(episodes, a, tasks, metric), task_scores(episodes, b, tasks, metric)
        means = paired_bootstrap({"a": sa, "b": sb}, resamples, bootstrap_seed(tasks))
        diff = difference(means["a"], means["b"], level)
        results.append({"id": c["id"], "arms": [a, b], "computed": True, "tasks": len(tasks),
                        "estimate": sum(sa) / len(sa) - sum(sb) / len(sb), "ci": diff["ci"], "p": diff["p"]})
    done = [r for r in results if r["computed"]]
    for r, adj in zip(done, holm([r["p"] for r in done])):
        r["p_holm"] = adj
        r["reject"] = adj <= registry["alpha"]
    complete = len(done) == len(comps)
    return {"claimed": complete, "alpha": registry["alpha"], "level": level, "resamples": resamples,
            "note": "" if complete else "一覧の比較の一部を計算できなかったので、主要比較を主張しない", "results": results}
