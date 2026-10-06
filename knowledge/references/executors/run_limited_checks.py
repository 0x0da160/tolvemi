"""Executor for the LPTL v1 limited checks (see /conformance/limited-checks.md).

Copies the sanctioned bundle files into a fresh temporary directory, runs
v1_limited_checks.py there unchanged, and prints a receipt as JSON.

Usage: python3 -I run_limited_checks.py <spec-dir> > receipt.json
"""
import csv
import hashlib
import json
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

COMPUTATION = "v1_limited_checks.py"
INPUTS = ["ast_codec_v1.schema.json", "v1_check_inputs.json"]


def sha256(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main(spec_dir):
    spec_dir = Path(spec_dir).resolve()
    with tempfile.TemporaryDirectory() as tmp:
        work = Path(tmp) / "run"
        work.mkdir()
        for name in [COMPUTATION, *INPUTS]:
            shutil.copyfile(spec_dir / name, work / name)
        proc = subprocess.run(
            [sys.executable, "-I", str(work / COMPUTATION)],
            cwd=tmp, capture_output=True, text=True,
        )
        if proc.returncode != 0:
            sys.stderr.write(proc.stderr)
        summary = json.loads(proc.stdout.strip().splitlines()[-1])
        checks_csv = work / "v1_checks.csv"
        with checks_csv.open(encoding="utf-8", newline="") as f:
            checks = [
                {"case": r["case"], "kind": r["kind"], "pass": r["pass"] == "True"}
                for r in csv.DictReader(f)
            ]
        receipt = {
            "computation_sha256": sha256(work / COMPUTATION),
            "inputs_sha256": {name: sha256(work / name) for name in INPUTS},
            "python": summary["python"],
            "jsonschema": summary["jsonschema"],
            "summary": {"cases": summary["cases"], "passed": summary["passed"]},
            "checks_csv_sha256": sha256(checks_csv),
            "checks": checks,
            "returncode": proc.returncode,
        }
    json.dump(receipt, sys.stdout, ensure_ascii=False, indent=1)
    sys.stdout.write("\n")


if __name__ == "__main__":
    main(sys.argv[1])
