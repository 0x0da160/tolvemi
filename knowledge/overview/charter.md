---
type: Language Charter
title: LPTL 憲章と中心定理
description: LPTL は有限データ上の純粋な計算のための静的型付き・決定的・全域な DSL であり、受理済みプログラムは有効入力で必ず一意の値に停止する。
tags: [lptl, charter, totality, determinism, purity]
status: draft
generated: { by: claude-code/2026-10-06, at: 2026-10-06T16:00:00Z }
sources:
  - id: lptl-design
    resource: ../../spec/lptl-v1/LPTL_design_v1.md
    title: LLM向け純粋・全域言語：設計方針 v1（§0、§2、§8.1）
    last_modified: 2026-10-01T00:00:00Z
---

# 定義

**LPTL（LLM-Pure Total Language）** は、有限データ上の純粋な計算のための、静的型付き・決定的・全域な DSL である。[^lptl-design] 公開名称は [Tolvemi](naming.md)。

# 中心定理

整形式かつ受理済みのプログラム `P` の entry 関数を、有効な有限入力 `i` に適用すると、数学的意味論において必ず停止し、宣言戻り型に属する一意の有限値 `v` を返す。

```text
well_formed(P) ∧ i ∈ Value(T_in)
  ⇒ ∃! v ∈ Value(T_out). P(i) ⇓ v
```

- `well_formed` は名前・scope・型・DAG・唯一の arity=1 entry の成立を含む。
- 「受理済みなら well_formed」は処理系適合の証明対象。逆に well_formed でも有限 profile により静的拒否され得る。
- 定理の前提は固定した数学的仕様・整形式プログラム・型に属する有限入力であり、物理ホストや処理系ではない。証明構造は [停止性の証明構造](../guarantees/termination-proof.md)。

# 数学的停止と実装上の成功の区別

実装上の成功には、検証済み実装範囲、明示的な信頼境界、十分な参照予算とホスト資源、出力 codec の完了が別に必要。次はいずれも言語意味論上の値・例外・非停止ではなく、**ホスト結果**である。

| ホスト結果 | 対応する API 結果 |
|---|---|
| ソース不正・静的拒否 | `CompileResult::Rejected` / `SourceBoundaryFailure` |
| 入力デコード失敗 | `DecodeResult::Invalid` / `InputBoundaryFailure` |
| 資源超過 | `RunResult::ResourceExhausted` |
| タイムアウト・物理資源 | `RunResult::HostAborted` |
| 処理系障害 | `RunResult::InternalFault` |

詳細は [API 分離](../api/api-separation.md)。

# 用途

1. **第一の用途：高保証計算カーネル。** LLM を含む外部提案器が生成した有限・純粋・決定的ロジックを、型・停止性・決定性・資源契約の下で受理・実行する。
2. **第二の用途：研究基盤。** LLM の生成・修復に対する構文、意味論、診断、Skill、表記の寄与を分解して測定する。[評価モードと比較](../llm-evaluation/evaluation-modes.md) を参照。

第一用途の受理・実行契約を、第二用途の成功率のために緩めない。

# 主張の境界

- LPTL は一般目的言語ではない。
- 「LLM に最適」「LLM の意味的成功率を改善する」「実運用で優位」といった経験的主張は形式保証から導かれない。仕様・Skill・評価器・予算・対照・最終タスクを固定した比較実験でのみ判断する。
- 一意な結果を返すことと、ユーザーの要求に合う正解を返すことは別である。

[^lptl-design]: LLM向け純粋・全域言語：設計方針 v1
