"""tlvm の速度の基準：計測値を記録し、基準の二倍を超える退行を検出する。

v1.0.0 の速度の基準は、いまの計測値を基準として記録し、後の変更がその二倍を超えたら検出することにする
（絶対の時間の目標は置かない）。手順と判定の規則は docs/speed-baseline.md に書く。

- W1：eval/tasks の参照プログラムを、各 hidden.json のケースで実行する（小さい入力）。
- W2：総和・二乗の和・並べ替えを、100〜10 万要素の入力で実行する（規模を変える）。

時間は一回のプロセスの壁時計時間（検査から符号化まで）。論理量は `run --stats` の steps と allocated_nodes。
論理量は決定的なので、どの機械でも比べられる。時間は同じ機械（cpu と nproc が同じ）のときだけ比べる。

usage（リポジトリの根から）:
  python3 bench/speed_baseline.py record bench/baseline.json   # 計測して基準を書く
  python3 bench/speed_baseline.py check bench/baseline.json    # 計測して基準と比べる（退行があれば終了コード 1）

環境変数：TLVM_BIN（既定は target/release/tlvm）、REPEATS（既定 5。各ケースの実行回数）。
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import platform
import statistics
import subprocess
import tempfile
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
BIN = Path(os.environ.get("TLVM_BIN", ROOT / "target/release/tlvm"))
REPEATS = int(os.environ.get("REPEATS", "5"))
FACTOR = 2.0  # 基準の二倍を超えたら退行
NOISE_MS = 20.0  # 基準の中央値がこれ未満のケースは時間を比べない（起動の揺れ）
SIZES = (100, 300, 1000, 10000, 100000)
W2_PROGS = {
    "sum_all": (
        "fn sum_all(xs: List<Int>) -> Int = fold(xs, 0, |acc, x| add(acc, x))\nentry sum_all\n",
        lambda xs: sum(xs),
    ),
    "square_filter_sum": (
        "fn sq_sum(xs: List<Int>) -> Int =\n"
        "  fold(filter(map(xs, |x| mul(x, x)), |y| le(100, y)), 0, |acc, y| add(acc, y))\n"
        "entry sq_sum\n",
        lambda xs: sum(x * x for x in xs if x * x >= 100),
    ),
    "sort_max": (
        "fn sort_max(xs: List<Int>) -> Int = fold(sort_by(xs, |x| x), 0, |acc, x| x)\nentry sort_max\n",
        lambda xs: max(xs),
    ),
}


def run_once(prog: Path, arg: str) -> dict:
    t0 = time.perf_counter()
    p = subprocess.run(
        [str(BIN), "run", str(prog), arg, "--plain", "--stats"],
        capture_output=True,
        text=True,
        timeout=300,
    )
    ms = (time.perf_counter() - t0) * 1000.0
    stats = None
    lines = p.stderr.strip().splitlines()
    if lines and lines[-1].startswith("{"):
        try:
            stats = json.loads(lines[-1])
        except json.JSONDecodeError:
            stats = None
    return {"rc": p.returncode, "out": p.stdout.strip(), "stats": stats, "ms": ms}


def measure(prog: Path, arg: str, expected) -> dict:
    runs = [run_once(prog, arg) for _ in range(REPEATS)]
    first = runs[0]
    stable = all(r["rc"] == first["rc"] and r["stats"] == first["stats"] for r in runs)
    ok = None
    if first["rc"] == 0:
        try:
            got = json.loads(first["out"])
        except json.JSONDecodeError:
            got = None
        # `run --plain` は大きい整数を JSON の文字列で出すので、十進の表記で比べる。
        if isinstance(expected, int) and isinstance(got, str):
            ok = got == str(expected)
        else:
            ok = got == expected
    return {
        "rc": first["rc"],
        "stats": first["stats"],
        "ok": ok,
        "stable": stable,
        "ms": statistics.median(r["ms"] for r in runs),
    }


def measure_all() -> list[dict]:
    rows = []
    for d in sorted((ROOT / "eval/tasks").iterdir()):
        prog = d / "reference.tlvm"
        hidden = d / "hidden.json"
        if not (prog.exists() and hidden.exists()):
            continue
        for c in json.loads(hidden.read_text()):
            m = measure(prog, json.dumps(c["input"], ensure_ascii=False), c["expected"])
            rows.append({"w": "W1", "task": d.name, "case": c["name"], **m})
    with tempfile.TemporaryDirectory() as tmp:
        tmp = Path(tmp)
        for n in SIZES:
            xs = [((i * 7919) % 2001) - 1000 for i in range(n)]
            inp = tmp / f"list_{n}.json"
            inp.write_text(json.dumps(xs))
            for name, (src, ref) in W2_PROGS.items():
                prog = tmp / f"{name}.tlvm"
                prog.write_text(src)
                m = measure(prog, "@" + str(inp), ref(xs))
                rows.append({"w": "W2", "task": name, "case": f"n={n}", **m})
    return rows


def clean(r: dict) -> dict:
    out = {k: r[k] for k in ("w", "task", "case", "rc", "stats", "ok", "stable")}
    out["ms"] = round(r["ms"], 2)
    return out


def env() -> dict:
    cpu = platform.processor() or "unknown"
    try:
        with open("/proc/cpuinfo") as f:
            for line in f:
                if line.startswith("model name"):
                    cpu = line.split(":", 1)[1].strip()
                    break
    except OSError:
        pass
    rust = subprocess.run(["rustc", "--version"], capture_output=True, text=True).stdout.strip()
    head = subprocess.run(["git", "-C", str(ROOT), "rev-parse", "--short", "HEAD"], capture_output=True, text=True).stdout.strip()
    return {
        "git_head": head,
        "binary_sha256_prefix": hashlib.sha256(BIN.read_bytes()).hexdigest()[:16],
        "rustc": rust,
        "python": platform.python_version(),
        "kernel": platform.release(),
        "cpu": cpu,
        "nproc": os.cpu_count(),
        "repeats": REPEATS,
    }


def floor_ms() -> float:
    prog = ROOT / "examples/sum_even.tlvm"
    return round(statistics.median(run_once(prog, "[]")["ms"] for _ in range(20)), 2)


def report(rows: list[dict]) -> None:
    w1 = sorted(r["ms"] for r in rows if r["w"] == "W1")
    print(f"W1: {len(w1)} cases, sum {sum(w1):.0f} ms, median {statistics.median(w1):.2f} ms, "
          f"p90 {w1[int(0.9 * (len(w1) - 1))]:.2f} ms, max {w1[-1]:.2f} ms")
    for r in rows:
        if r["w"] == "W2":
            print(f"W2 {r['task']} {r['case']} rc={r['rc']} stats={r['stats']} ms={r['ms']:.1f} ok={r['ok']}")


def record(path: Path) -> None:
    rows = [clean(r) for r in measure_all()]
    body = ",\n".join(json.dumps(r, ensure_ascii=False) for r in rows)
    text = (
        '{\n"env": ' + json.dumps(env(), ensure_ascii=False)
        + f',\n"floor_ms": {floor_ms()},\n"rows": [\n{body}\n]\n}}\n'
    )
    path.write_text(text)
    print(f"wrote {path} ({len(rows)} cases)")
    report(rows)


def compare(base_rows: list[dict], now_rows: list[dict], same_machine: bool) -> list[str]:
    base = {(r["w"], r["task"], r["case"]): r for r in base_rows}
    now = {(r["w"], r["task"], r["case"]): r for r in now_rows}
    problems = []
    for key in base:
        if key not in now:
            problems.append(f"{' '.join(key)}: missing from this run")
    for key, r in now.items():
        name = " ".join(key)
        b = base.get(key)
        if b is None:
            problems.append(f"{name}: not in the baseline (record again if this is intended)")
            continue
        if r["ok"] is False:
            problems.append(f"{name}: output differs from the expected value")
        if not r["stable"]:
            problems.append(f"{name}: counters differ between repeats")
        if r["rc"] != b["rc"]:
            if b["rc"] == 0:
                problems.append(f"{name}: no longer completes (rc {r['rc']}, was 0)")
            continue
        if r["rc"] != 0:
            continue
        for k in ("steps", "allocated_nodes"):
            was, now_v = b["stats"][k], r["stats"][k]
            if now_v > FACTOR * was:
                problems.append(f"{name}: {k} {was} -> {now_v} (more than {FACTOR:g}x)")
        if same_machine and b["ms"] >= NOISE_MS and r["ms"] > FACTOR * b["ms"]:
            problems.append(f"{name}: time {b['ms']:.1f} -> {r['ms']:.1f} ms (more than {FACTOR:g}x)")
    if same_machine:
        was = sum(r["ms"] for r in base.values() if r["w"] == "W1")
        now_t = sum(r["ms"] for r in now.values() if r["w"] == "W1")
        if now_t > FACTOR * was:
            problems.append(f"W1 total time {was:.0f} -> {now_t:.0f} ms (more than {FACTOR:g}x)")
    return problems


def check(path: Path) -> int:
    base = json.loads(path.read_text())
    now = env()
    same_machine = (now["cpu"], now["nproc"]) == (base["env"]["cpu"], base["env"]["nproc"])
    if not same_machine:
        print("note: 基準と機械が違うため、時間は比べない（論理量だけを比べる）")
    now_rows = [clean(r) for r in measure_all()]
    problems = compare(base["rows"], now_rows, same_machine)
    for p in problems:
        print("regression:", p)
    if problems:
        print(f"FAILED: {len(problems)} problem(s) against {path}")
        return 1
    print(f"OK: {len(now_rows)} cases within {FACTOR:g}x of {path}")
    return 0


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    sub = ap.add_subparsers(dest="cmd", required=True)
    rec = sub.add_parser("record", help="計測して基準を書く")
    rec.add_argument("path", type=Path)
    chk = sub.add_parser("check", help="計測して基準と比べる（退行があれば終了コード 1）")
    chk.add_argument("path", type=Path)
    args = ap.parse_args()
    if args.cmd == "record":
        record(args.path)
        return 0
    return check(args.path)


if __name__ == "__main__":
    raise SystemExit(main())
