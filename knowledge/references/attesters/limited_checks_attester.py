"""Deterministic attester for /conformance/limited-checks.md (no LLM).

Checks that the receipt was produced by the sanctioned computation and
inputs recorded in the bundle manifest, and that the reported pass count
matches the per-case results.

Usage: python3 -I limited_checks_attester.py <manifest.json> <receipt.json>
Exits 0 and prints {"verdict": "pass", ...} on success, 1 otherwise.
"""
import json
import sys

EXPECTED_CASES = 92


def attest(manifest, receipt):
    recorded = {o["name"]: o["sha256"] for o in manifest["outputs"]}
    problems = []
    if receipt.get("returncode") != 0:
        problems.append("computation exited non-zero")
    if receipt["computation_sha256"] != recorded["v1_limited_checks.py"]:
        problems.append("computation differs from manifest")
    for name, digest in receipt["inputs_sha256"].items():
        if digest != recorded.get(name):
            problems.append(f"input {name} differs from manifest")
    if set(receipt["inputs_sha256"]) != {"ast_codec_v1.schema.json", "v1_check_inputs.json"}:
        problems.append("unexpected input set")
    checks = receipt["checks"]
    cases = [c["case"] for c in checks]
    if len(cases) != EXPECTED_CASES or len(set(cases)) != EXPECTED_CASES:
        problems.append(f"expected {EXPECTED_CASES} distinct cases, got {len(cases)}")
    passed = sum(1 for c in checks if c["pass"])
    if receipt["summary"] != {"cases": len(checks), "passed": passed}:
        problems.append("summary does not match per-case results")
    return {
        "verdict": "fail" if problems else "pass",
        "cases": len(checks),
        "passed": passed,
        "problems": problems,
    }


def main(manifest_path, receipt_path):
    with open(manifest_path, encoding="utf-8") as f:
        manifest = json.load(f)
    with open(receipt_path, encoding="utf-8") as f:
        receipt = json.load(f)
    verdict = attest(manifest, receipt)
    print(json.dumps(verdict, ensure_ascii=False))
    return 0 if verdict["verdict"] == "pass" else 1


if __name__ == "__main__":
    sys.exit(main(sys.argv[1], sys.argv[2]))
