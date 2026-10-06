---
type: Metric
title: 事前登録と指標
description: evaluation-protocol-v1 の episode 定義、4成分の予算ベクトル B、最終候補の選択規則、主要指標 Success@B とその分母から落とさない失敗の扱い。
tags: [lptl, llm, evaluation, metrics, preregistration]
status: draft
generated: { by: claude-code/2026-10-06, at: 2026-10-06T16:00:00Z }
sources:
  - id: lptl-design
    resource: ../../spec/lptl-v1/LPTL_design_v1.md
    title: LLM向け純粋・全域言語：設計方針 v1（§12.5）
    last_modified: 2026-10-01T00:00:00Z
---

# 事前登録

`evaluation-protocol-v1` は実験計画の契約識別子であり、実行済み実験を意味しない。仕様、Skill、処理系、全 profile、モデル版、温度、最大出力、反復数 K、task 集合、候補選択、可視ツール、生成器、seed、隠し検査、閾値、除外基準、失敗集計を秘密 seed 最終評価前に固定する。[^lptl-design]

# episode

- 一試行は一つの `(task_id, replicate_id, arm_id)`。初回生成とその後の全修復・候補生成を同じ episode に含める。
- 各 task に同じ K を割り付ける。候補一件を新たな試行と数えない（3失敗候補後に1成功候補なら S=1、分母へ4を加えない）。
- Repair を固定失敗候補から始める場合、修復単独指標と生成を含む連結指標を分ける。

# 予算 B

B は上限ベクトル：(累積モデル入力 tokens、累積モデル出力 tokens、モデル要求回数、可視検証 API 呼出し回数)。

- compile／compile_ast／decode_input／run の可視呼出しはそれぞれ一回。Skill・診断・schema・修復履歴を含む実際の context を各要求で課金する。cache 割引と論理 tokens を混同しない。
- 全成分が上限以内のときだけ予算内。ちょうど上限は許す。欠落成分・長さ不一致は無視せず設定不正。
- 次の操作に予算がなければ発行せず、既存候補で通常終了する（guard で禁止されただけでは budget 失敗にしない）。

| 終了理由 | 扱い |
|---|---|
| normal_stop／budget_reached／operation_guarded | 実測が全成分以内なら予算内。既存候補を選択できる |
| budget_exceeded | 一成分でも実測超過。S=0（既存正解候補も成功にしない） |
| 予算内終了で Accepted 候補なし | no_accepted_candidate、S=0 |

B は LPTL の input／execution profile とは別の探索予算。

# 最終候補の選択

- 隠しテストを一切参照せず一件だけ選ぶ。主評価では予算内に検証された候補のうち、**最後に Accepted となった候補**。なければ失敗。
- 全候補を隠しテストで評価して最良を選ぶことは禁止。採点結果を修復へ返さない。
- 既に Accepted と検証済みなら選択時の重複 compile は不要。再検証するなら B に計上。

# Success@B

```text
S(task, replicate, arm; B) = 1
  iff budget内に選択した最終候補がAcceptedであり、
      固定した全隠しテスト・性質検査・参照資源条件に通過する
それ以外は0

Success@B(arm) = (1 / task数) * Σ_task ((1 / K) * Σ_replicate S)
```

生成失敗、parse/name/type/entry 拒否、入力不正、参照資源超過、候補なし、budget 超過、誤答、候補実行による HostAborted を分母から落とさない。受理率は別指標で、意味的成功の代替にしない。評価器の InternalFault 等の試験基盤事故は事前登録規則で区別して公開し、一方の arm だけ再試行しない。

# 二次指標と統計

初回 phase 通過率、固定失敗候補からの修復成功、候補単位の受理率、条件付き・無条件費用、検証回数、診断別修復率、深さ別成功、資源超過率を別名で報告する。task 単位ブートストラップで、対応比較では同じ再標本 task を全 arm に適用する。公開再現課題と秘密 seed 最終課題を分離し汚染検査を記録する。G4 完了は事前登録に沿う実験と結果公開であり、正の優位性は必須にしない。

[^lptl-design]: LLM向け純粋・全域言語：設計方針 v1
