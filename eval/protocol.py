"""評価の事前登録（evaluation-protocol-v1 草案）のうち、オーナーの決定に依らない規則。

- 必須の設定（草案 §9）：秘密の課題集合の場所、反復数 K、予算 B、CLI の限界の扱い、公開の範囲。
  既定値を持たず、一つでも欠けるか不正なら実行しない（fail closed）。値はオーナーが登録の時に決める
- 予算 B（草案 §5、設計書 §12.5）：四成分の上限。操作の前に guard し、実測の累積が一成分でも上限を
  超えた episode は budget 失敗とする（ちょうど上限は許す）
- 最終候補（草案 §3）：予算内に検証され、compile／compile_ast で受理された最後の候補を一件だけ選ぶ。
  隠しテストの結果は記録するが、選択には使わない
- 失敗の分類（草案 §3）と、試験基盤の事故を見分ける固定の判定表

このモジュールは tlvm もモデルも呼ばない。
"""

from __future__ import annotations

import json
import math
import subprocess
from dataclasses import asdict, dataclass
from enum import Enum
from pathlib import Path

# ---------------------------------------------------------------------------------------------- 必須の設定（§9）

CONFIG_KEYS = {
    "hidden_set_location": "§9 の 1：秘密の最終評価の課題集合を置くディレクトリ",
    "repeats": "§9 の 2：反復数 K（1 以上の整数）",
    "budget": "§9 の 2：予算 B（input_tokens、output_tokens、requests、verification_calls の四つ。どれも 1 以上の整数）",
    "cli_limits": "§9 の 3：温度・seed・最大出力を CLI で固定できないことの扱い（cli-defaults か api-fixed）",
    "publication_scope": "§9 の 4：結果を公開する範囲（summary-only か summary-and-raw）",
}
# cli-defaults：claude -p のまま、温度・seed・最大出力は CLI の既定値で、限界として公開する
# api-fixed：API バックエンド（API キーが要る）で、固定できるものを固定する
CLI_LIMITS = ("cli-defaults", "api-fixed")
PUBLICATION_SCOPES = ("summary-only", "summary-and-raw")
# 設計書 §12.5 の順：累積モデル入力 tokens、累積モデル出力 tokens、モデル要求回数、可視検証の呼び出し回数
BUDGET_COMPONENTS = ("input_tokens", "output_tokens", "requests", "verification_calls")
# 公開の範囲ごとに、実行のディレクトリから公開してよいファイル（生データにはモデルの版の識別子が含まれる）
PUBLISHABLE = {
    "summary-only": ("summary.json", "summary.md"),
    "summary-and-raw": ("summary.json", "summary.md", "config.json", "episodes.jsonl"),
}


class ProtocolConfigError(ValueError):
    """事前登録の設定が欠けているか不正。見つけた問題をすべて並べる。"""


@dataclass(frozen=True)
class Budget:
    input_tokens: int
    output_tokens: int
    requests: int
    verification_calls: int

    def vector(self) -> list[int]:
        return [getattr(self, c) for c in BUDGET_COMPONENTS]


@dataclass(frozen=True)
class ProtocolConfig:
    hidden_set_location: str
    repeats: int
    budget: Budget
    cli_limits: str
    publication_scope: str

    def as_dict(self) -> dict:
        return asdict(self)


def _positive_int(v) -> bool:
    return type(v) is int and v >= 1  # bool は int の部分型なので type で比べる


def load_protocol_config(source) -> ProtocolConfig:
    """事前登録の設定を読む。dict か JSON ファイルのパスを受け取る。既定値は一つも補わない。"""
    if isinstance(source, (str, Path)):
        try:
            data = json.loads(Path(source).read_text(encoding="utf-8"))
        except (OSError, ValueError) as e:
            raise ProtocolConfigError(f"事前登録の設定を読めません（fail closed）: {source}: {e}") from None
    else:
        data = source
    if not isinstance(data, dict):
        raise ProtocolConfigError("事前登録の設定は JSON の object でなければなりません（fail closed）")
    problems = []
    for key, what in CONFIG_KEYS.items():
        if data.get(key) is None:
            problems.append(f"{key} がありません（{what}）")
    for key in sorted(set(data) - set(CONFIG_KEYS) - {"_comment"}):
        problems.append(f"{key} は知らない項目です")
    loc = data.get("hidden_set_location")
    if loc is not None and (not isinstance(loc, str) or not loc.strip()):
        problems.append("hidden_set_location は空でない文字列（ディレクトリのパス）でなければなりません")
    k = data.get("repeats")
    if k is not None and not _positive_int(k):
        problems.append(f"repeats は 1 以上の整数でなければなりません（{k!r}）")
    b = data.get("budget")
    if b is not None:
        if not isinstance(b, dict):
            problems.append("budget は object でなければなりません")
        else:
            for c in BUDGET_COMPONENTS:
                if b.get(c) is None:
                    problems.append(f"budget.{c} がありません")
                elif not _positive_int(b[c]):
                    problems.append(f"budget.{c} は 1 以上の整数でなければなりません（{b[c]!r}）")
            for c in sorted(set(b) - set(BUDGET_COMPONENTS)):
                problems.append(f"budget.{c} は知らない成分です")
    cl = data.get("cli_limits")
    if cl is not None and cl not in CLI_LIMITS:
        problems.append(f"cli_limits は {' か '.join(CLI_LIMITS)} です（{cl!r}）")
    ps = data.get("publication_scope")
    if ps is not None and ps not in PUBLICATION_SCOPES:
        problems.append(f"publication_scope は {' か '.join(PUBLICATION_SCOPES)} です（{ps!r}）")
    if problems:
        raise ProtocolConfigError("事前登録の設定が不完全です（fail closed）:\n- " + "\n- ".join(problems))
    return ProtocolConfig(loc, k, Budget(**{c: b[c] for c in BUDGET_COMPONENTS}), cl, ps)


# ---------------------------------------------------------------------------------------------- 予算 B（§5）

# 要求の前の入力 tokens の見積り（初回の要求は全体を、二回目からは直前の実測に増えた分を足す）。
# 予備実験の claude -p の実測（eval/runs、SKILL.md の 11 の版）では、初回の論理入力 tokens ≈ 1,450 + SKILL の bytes ÷ 2.2
# だった（CLI が足す定型文を含む）。2.0 bytes で数えると、現在の SKILL.md（29,214 bytes）で実測の 14,705 tokens を
# 1% ほど上回る。見積りが外れて実測が上限を超えた episode は、事後の判定で budget 失敗になる
BYTES_PER_TOKEN = 2.0


def estimate_tokens(n_bytes: int) -> int:
    return math.ceil(max(0, n_bytes) / BYTES_PER_TOKEN)


def read_usage(raw) -> dict | None:
    """backend の usage から、キャッシュを含まない入力、キャッシュの読み・書き、出力を分けて取り出す。

    論理入力 tokens（予算 B の入力の成分）は三つの入力の和。キャッシュによる料金の割引と論理 tokens を混同しない
    （設計書 §12.5）。数として読めなければ None（計測不正）。"""
    if not isinstance(raw, dict):
        return None
    out = {}
    for k in ("input_tokens", "output_tokens"):
        v = raw.get(k)
        if type(v) is not int or v < 0:
            return None
        out[k] = v
    for k in ("cache_read_input_tokens", "cache_creation_input_tokens"):
        v = raw.get(k) or 0
        if type(v) is not int or v < 0:
            return None
        out[k] = v
    out["logical_input_tokens"] = out["input_tokens"] + out["cache_read_input_tokens"] + out["cache_creation_input_tokens"]
    return out


class BudgetMeter:
    """一つの episode の予算 B の使用量。budget が None なら上限なし（予備実験）で、記録だけする。"""

    def __init__(self, budget: Budget | None):
        self.budget = budget
        self.used = dict.fromkeys(BUDGET_COMPONENTS, 0)
        self.breakdown = dict.fromkeys(("input_tokens", "cache_read_input_tokens", "cache_creation_input_tokens"), 0)
        self.invalid: list[str] = []  # 計測できなかったもの。一つでもあれば予算内と認めない
        self._prev: tuple[int, int] | None = None  # 直前の要求の (見積りに使った bytes, 実測の論理入力 tokens)

    def estimate_input(self, n_bytes: int) -> int:
        """次の要求の論理入力 tokens の見積り。直前の要求の実測に、増えた文の分の見積りを足す（初回は全体を見積もる）。"""
        if self._prev is None:
            return estimate_tokens(n_bytes)
        prev_bytes, prev_tokens = self._prev
        return prev_tokens + estimate_tokens(n_bytes - prev_bytes)

    def guard_request(self, estimated_input: int) -> tuple[str, str] | None:
        """要求の前の guard。発行できなければ (終了理由, 成分)、できれば None。

        budget_reached：成分が上限に達していて、次の要求の余地がない。operation_guarded：次の要求で上限を超える見込み。
        出力 tokens は事前に数えられないので、残りが 0 なら止める。可視検証の余地がなければ、候補を検証できないので
        要求も出さない。"""
        b = self.budget
        if b is None:
            return None
        for c in ("requests", "output_tokens", "verification_calls", "input_tokens"):
            if self.used[c] >= getattr(b, c):
                return ("budget_reached", c)
        if self.used["input_tokens"] + estimated_input > b.input_tokens:
            return ("operation_guarded", "input_tokens")
        return None

    def record_request(self, raw_usage, model_requests=1, n_bytes: int | None = None) -> dict | None:
        """要求を一つ数える。CLI の中で複数回の要求になったときは model_requests にその数を渡す。"""
        if type(model_requests) is not int or model_requests < 1:
            self.invalid.append("model_requests")
            model_requests = 1
        self.used["requests"] += model_requests
        u = read_usage(raw_usage)
        if u is None:
            self.invalid.append("usage")
            self._prev = None
            return None
        self.used["input_tokens"] += u["logical_input_tokens"]
        self.used["output_tokens"] += u["output_tokens"]
        for k in self.breakdown:
            self.breakdown[k] += u[k]
        if n_bytes is not None:
            self._prev = (n_bytes, u["logical_input_tokens"])
        return u

    def remaining(self, component: str) -> int | None:
        if self.budget is None:
            return None
        return getattr(self.budget, component) - self.used[component]

    def guard_verification(self, calls: int) -> tuple[str, str] | None:
        if self.budget is None or self.used["verification_calls"] + calls <= self.budget.verification_calls:
            return None
        return ("operation_guarded", "verification_calls")

    def record_verification(self, calls: int) -> None:
        self.used["verification_calls"] += calls

    def observed(self) -> list[int]:
        return [self.used[c] for c in BUDGET_COMPONENTS]

    def exceeded(self) -> list[str]:
        if self.budget is None:
            return []
        return [c for c in BUDGET_COMPONENTS if self.used[c] > getattr(self.budget, c)]

    def snapshot(self) -> dict:
        return {
            "limit": asdict(self.budget) if self.budget else None,
            "used": dict(self.used),
            "input_breakdown": dict(self.breakdown),
            "measurement_valid": not self.invalid,
        }


def budget_vector_ok(observed, limit) -> bool:
    """実測の累積が全成分で上限以内か（ちょうど上限は許す）。成分の欠落・長さの違い・負の値は予算内としない。"""
    return (isinstance(observed, list) and isinstance(limit, list) and len(observed) == len(limit) == len(BUDGET_COMPONENTS)
            and all(type(v) is int and v >= 0 for v in observed + limit)
            and all(a <= b for a, b in zip(observed, limit)))


def select_final(candidates: list[dict]) -> int | None:
    """§3：最後に受理された候補の位置。隠しテストの結果（hidden_pass）は見ない。なければ None。

    candidates は episode の候補の記録で、予算内に検証できた候補だけが accepted を真にできる。"""
    return next((i for i in range(len(candidates) - 1, -1, -1) if candidates[i].get("accepted")), None)


def budget_end(observed, limit, stop_reason: str, candidates: list[dict]) -> dict:
    """設計書 §12.5 の予算終了（spec/lptl-v1/v1_limited_checks.py の budget_end_model と同じ規則）。

    limit が None なら予算なし（予備実験）で、予算内として扱う。実測が一成分でも上限を超えたら、既に正しい候補が
    あっても成功にしない。"""
    if limit is None:
        budget_ok = True
    else:
        valid = (isinstance(observed, list) and isinstance(limit, list) and len(observed) == len(limit) == len(BUDGET_COMPONENTS)
                 and all(type(v) is int and v >= 0 for v in observed + limit))
        if not valid:
            return {"reason": "invalid_budget_measurement", "budget_ok": False, "selected": None, "success": 0}
        budget_ok = budget_vector_ok(observed, limit)
    selected = select_final(candidates)
    if not budget_ok:
        reason = "budget_exceeded"
    elif selected is None:
        reason = "no_accepted_candidate"
    else:
        reason = stop_reason
    success = int(budget_ok and selected is not None and bool(candidates[selected].get("hidden_pass")))
    return {"reason": reason, "budget_ok": budget_ok, "selected": selected, "success": success}


# ---------------------------------------------------------------------------------------------- 失敗の分類（§3）


class Outcome(str, Enum):
    """episode の結果。SUCCESS と INFRA_FAULT 以外の八つが §3 の失敗の分類で、どれも分母から落とさない。"""

    SUCCESS = "success"
    GENERATION_FAILURE = "generation_failure"  # 生成の失敗（拒否、出力の途中切れ、CLI が出力を作れなかった）
    REJECTED = "rejected"  # parse・name・type・entry の拒否（どの段階かは detail）
    INVALID_INPUT = "invalid_input"  # 入力の不正（テストの入力を候補の入力型として読めない）
    RESOURCE_EXCEEDED = "resource_exceeded"  # 資源超過（tlvm の ResourceExhausted、Python の時間切れ・再帰の上限）
    NO_CANDIDATE = "no_candidate"  # 候補がない（回答にプログラムがない、要求を一度も出せなかった）
    BUDGET_EXCEEDED = "budget_exceeded"  # 予算超過（実測の累積が一成分でも B を超えた）
    WRONG_ANSWER = "wrong_answer"  # 誤答（Python の実行時例外を含む。detail に例外の型）
    HOST_ABORTED = "host_aborted"  # 候補の実行による HostAborted（Python の処理系ごとの異常終了を含む）
    INFRA_FAULT = "infra_fault"  # 試験基盤の事故（失敗の分類とは別に、件数と episode を公開する）


FAILURE_CATEGORIES = (
    Outcome.GENERATION_FAILURE, Outcome.REJECTED, Outcome.INVALID_INPUT, Outcome.RESOURCE_EXCEEDED,
    Outcome.NO_CANDIDATE, Outcome.BUDGET_EXCEEDED, Outcome.WRONG_ANSWER, Outcome.HOST_ABORTED,
)

# 拒否の段階：tlvm の診断の phase（とハーネスが作る擬似コード）を、parse・name・type・entry に寄せる
REJECTION_PHASE = {
    "lex": "parse", "parse": "parse", "import": "parse", "structural-limits": "parse",
    "ast-parse": "parse", "ast-schema": "parse",
    "name": "name", "call-graph": "name",
    "typecheck": "type", "semantic-limits": "type",
    "entry": "entry",
}
# Python の候補を読み込めなかったときの例外（codes の先頭）の段階
PYTHON_REJECTION_PHASE = {
    "SyntaxError": "parse", "IndentationError": "parse", "TabError": "parse",
    "NameError": "name", "ImportError": "name", "ModuleNotFoundError": "name",
}

# ---------------------------------------------------------------------------------------------- 試験基盤の事故の判定表

# 結果と独立に固定した表。kind → (どこで起きるか, 何を含むか)。backend の事故は episode をそこで止め、
# 特定の arm だけを再試行しない（ハーネスに再試行はない。protocol の実行では CLI の時間切れの呼び直しもしない）
INFRA_TABLE = {
    "tlvm-internal-fault": ("tlvm", "InternalFault の envelope、またはテストケースの InternalFault"),
    "tlvm-exit": ("tlvm", "tlvm が 0 と 1 以外の終了コードで終わった（64 使い方、66 入出力、101 panic など）"),
    "tlvm-timeout": ("tlvm", "tlvm の処理がハーネスの時間上限を超えた"),
    "tlvm-output": ("tlvm", "tlvm の出力が読めない（JSON でない行、結果のないケース）"),
    "task-data": ("tlvm", "ケースの expected や形を読めない（課題のデータの誤りで、候補の誤りではない）"),
    "rerun-rejected": ("tlvm", "公開例で受理された候補が、隠しテストの実行では受理されなかった"),
    "cli-timeout": ("backend", "claude -p が --timeout の秒数を超えた"),
    "cli-unavailable": ("backend", "claude を起動できない"),
    "cli-output": ("backend", "claude -p が JSON の結果を出さなかった"),
    "cli-error": ("backend", "claude -p の is_error（subtype error_during_execution：API の過負荷、回数制限、通信、認証など）"),
    "cli-unknown": ("backend", "表にない subtype の is_error"),
    "api-connection": ("backend", "API の通信の失敗・時間切れ（APIConnectionError、APITimeoutError）"),
    "api-status": ("backend", "API の HTTP エラー（400、401、403、404、429、5xx、529 など。APIStatusError）"),
    "backend-other": ("backend", "backend が投げたその他の例外"),
}
# 生成の失敗の表。backend の例外のうち、モデルの出力の側の失敗
GENERATION_FAILURE_TABLE = {
    "refusal": "stop_reason が refusal（安全分類器が断った）",
    "truncated": "stop_reason が max_tokens（出力が途中で切れた。その候補は受理しない）",
    "cli-structured-output-retries": "claude -p の error_max_structured_output_retries（schema に合う出力を作れなかった）",
    "cli-max-turns": "claude -p の error_max_turns",
    "cli-max-budget-usd": "claude -p の error_max_budget_usd（--max-budget-usd の上限で止まった）",
}
# claude -p の結果の is_error の subtype → 表の kind
CLI_ERROR_SUBTYPES = {
    "error_during_execution": "cli-error",
    "error_max_structured_output_retries": "cli-structured-output-retries",
    "error_max_turns": "cli-max-turns",
    "error_max_budget_usd": "cli-max-budget-usd",
}


class BackendError(RuntimeError):
    """backend の失敗。kind は INFRA_TABLE か GENERATION_FAILURE_TABLE の鍵。

    失敗した要求でも backend が使用量を返したとき（claude -p の is_error の結果など）は、usage と requests
    （モデル要求の回数）に入れる。予算 B はそれも数える。"""

    def __init__(self, kind: str, detail: str = "", usage=None, requests=None):
        super().__init__(f"{kind}: {detail}" if detail else kind)
        self.kind = kind
        self.detail = detail
        self.usage = usage
        self.requests = requests


def classify_backend_error(exc: BaseException) -> tuple[Outcome, str]:
    """backend の例外を、生成の失敗か試験基盤の事故に分ける（固定の表で）。"""
    if isinstance(exc, BackendError):
        kind = exc.kind
    elif isinstance(exc, subprocess.TimeoutExpired):
        kind = "cli-timeout"
    elif isinstance(exc, OSError):
        kind = "cli-unavailable"
    else:
        names = {c.__name__ for c in type(exc).__mro__}  # anthropic の SDK を import せずに型の名前で見分ける
        if names & {"APIConnectionError", "APITimeoutError"}:
            kind = "api-connection"
        elif "APIStatusError" in names:
            kind = "api-status"
        else:
            kind = "backend-other"
    if kind in GENERATION_FAILURE_TABLE:
        return Outcome.GENERATION_FAILURE, kind
    if kind in INFRA_TABLE:
        return Outcome.INFRA_FAULT, kind
    return Outcome.INFRA_FAULT, "backend-other"


# tlvm test の error の reason の先頭 → 分類（main.rs の run_case の文言）。上から順に照合する
LPTL_CASE_REASONS = (
    ("InternalFault", Outcome.INFRA_FAULT, "tlvm-internal-fault"),
    ("HostAborted", Outcome.HOST_ABORTED, "host-aborted"),
    ("ResourceExhausted", Outcome.RESOURCE_EXCEEDED, "resource-exhausted"),
    ("input を型", Outcome.INVALID_INPUT, "input-decode"),
    ("input が UTF-8", Outcome.INVALID_INPUT, "input-utf8"),
    ("expected を型", Outcome.INFRA_FAULT, "task-data"),
    ("expected が UTF-8", Outcome.INFRA_FAULT, "task-data"),
    ("case ", Outcome.INFRA_FAULT, "task-data"),
)
PYTHON_RESOURCE_ERRORS = ("RecursionError", "MemoryError")
# 一つの候補の失敗したケースが複数の分類にまたがるときの優先順（先が強い）
CASE_PRECEDENCE = (Outcome.INFRA_FAULT, Outcome.HOST_ABORTED, Outcome.RESOURCE_EXCEEDED, Outcome.INVALID_INPUT,
                   Outcome.WRONG_ANSWER)


def classify_case(case: dict, lang: str) -> tuple[Outcome, str]:
    if case.get("result") == "fail":
        return Outcome.WRONG_ANSWER, "wrong-output"
    reason = str(case.get("reason") or "")
    if lang == "python":
        name = reason.split(":")[0].strip()
        if name in PYTHON_RESOURCE_ERRORS:
            return Outcome.RESOURCE_EXCEEDED, f"python-{name}"
        return Outcome.WRONG_ANSWER, f"runtime-error:{name or 'unknown'}"
    for prefix, outcome, detail in LPTL_CASE_REASONS:
        if reason.startswith(prefix):
            return outcome, detail
    return Outcome.INFRA_FAULT, "tlvm-output"


def classify_run(result: dict, lang: str) -> tuple[Outcome, str]:
    """受理された候補をテストで走らせた結果の分類（最終候補の隠しテストに使う）。"""
    if result.get("infra"):
        return Outcome.INFRA_FAULT, result["infra"]
    codes = result.get("codes") or []
    # Python の処理系ごとの異常終了と時間切れは、候補の実行が起こしたもの（受理の再検査より先に見る）
    if lang == "python" and "Crash" in codes:
        return Outcome.HOST_ABORTED, "python-crash"
    if lang == "python" and "Timeout" in codes:
        return Outcome.RESOURCE_EXCEEDED, "python-timeout"
    if not result.get("compile_ok") or not result.get("signature_ok"):
        return Outcome.INFRA_FAULT, "rerun-rejected"
    if result.get("all_pass"):
        return Outcome.SUCCESS, ""
    found = [classify_case(c, lang) for c in result.get("cases", []) if c.get("result") != "pass"]
    if not found:
        return Outcome.INFRA_FAULT, "tlvm-output"
    return min(found, key=lambda od: CASE_PRECEDENCE.index(od[0]))


def episode_outcome(end: dict, final_hidden: tuple[Outcome, str] | None, stop_reason: str, stop_detail: str,
                    last: dict | None) -> tuple[Outcome, str]:
    """episode の結果を一つに決める（固定の規則）。

    end は budget_end の結果、final_hidden は選んだ候補の隠しテストの分類、last は最後に要求を出した回の候補
    （has_code、phase）で、要求を一度も出していなければ None。"""
    if stop_reason == "infra_fault":
        return Outcome.INFRA_FAULT, stop_detail
    if end["reason"] == "invalid_budget_measurement":
        return Outcome.INFRA_FAULT, "budget-measurement"
    if not end["budget_ok"]:
        return Outcome.BUDGET_EXCEEDED, stop_detail
    if end["selected"] is not None:
        if final_hidden is None:
            return Outcome.INFRA_FAULT, "hidden-not-run"
        return final_hidden
    if stop_reason == "generation_failure":
        return Outcome.GENERATION_FAILURE, stop_detail
    if last is None or not last.get("has_code"):
        return Outcome.NO_CANDIDATE, stop_detail if last is None else ""
    return Outcome.REJECTED, last.get("phase") or "other"
