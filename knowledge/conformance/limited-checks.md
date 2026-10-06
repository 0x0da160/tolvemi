---
type: Attested Computation
title: 限定検査の合格数
description: LPTL v1 検証バンドルの限定検査 v1_limited_checks.py を実行し、92件の fixture のうち期待値と一致した件数を得る計算。
tags: [lptl, verification, fixtures, python]
status: draft
runtime: python
computation: ../../spec/lptl-v1/v1_limited_checks.py
parameters: []
executor:
  resource: ../references/run-limited-checks.md
  receipt: [computation_sha256, inputs_sha256, python, jsonschema, summary, checks_csv_sha256, checks]
attester:
  resource: ../references/attesters/limited_checks_attester.py
generated: { by: claude-code/2026-10-06, at: 2026-10-06T16:00:00Z }
verified: { by: process:limited-checks-attester, at: 2026-10-06T16:00:00Z }
sources:
  - id: manifest
    resource: ../../spec/lptl-v1/v1_artifact_manifest.json
    title: v1 artifact manifest
  - id: verification-report
    resource: ../../spec/lptl-v1/LPTL_v1_verification_report.md
    title: LPTL v1 統一版：突き合わせ確認報告
    last_modified: 2026-10-01T00:00:00Z
---

# Computation

計算本体は `computation` が指す `v1_limited_checks.py`（manifest 記録の SHA-256 `a3c183f8…13791dc`）。エージェントはこのコードを書き換えてはならず、パラメータもない。同じディレクトリの `ast_codec_v1.schema.json` と `v1_check_inputs.json` を読み、各 case の観測値を期待値と比較して `v1_checks.csv` を再生成し、要約 JSON を標準出力へ出す。

# 検査の内訳

92件の kind 別件数（2026-10-06 の実行で集計）：

| kind | 件数 | 対象 |
|---|---:|---|
| schema | 29 | AST schema の受理・拒否（識別子・整数 pattern、param、tag 等） |
| input_admission_model | 17 | 入力値の検査順と Admission |
| type_trace_model | 10 | 型検査仕事量の trace 期待値と cutoff |
| json_scalar_stage_model | 7 | string scalar と重複キーの段階順 |
| recovery_model | 5 | parser recovery の同期手順 |
| budget_end_model | 5 | 探索予算の終了理由 |
| ast_shape_model | 4 | AST header／field 検査順 |
| budget_vector | 4 | 予算ベクトルの厳密比較 |
| spec_bound_preimage_model | 3 | 仕様結合 hash の preimage |
| admission_model | 2 | parse Admission の cutoff |
| episode_aggregation | 2 | episode の成功集計 |
| source_boundary | 1 | formatter 境界 fixture |
| int_boundary | 1 | `10^4096` の桁数・bit 数 |
| decoded_duplicate_demo | 1 | escape 違いの重複キー |
| spec_bound_version_separation | 1 | spec_version 差の分離 |

末尾 LF に関する2件は別 pattern を使う対照 schema の確認であり、v1 受理 schema が末尾 LF を許すことを意味しない。[^verification-report]

# 結果

| 実行 | 環境 | 結果 |
|---|---|---|
| 2026-10-01（バンドル作成時） | Python 3.12.8、jsonschema 4.23.0 | 92/92 通過[^manifest] |
| 2026-10-06（本バンドル作成時に再実行） | Python 3.13.16、jsonschema 4.26.0 | 92/92 通過、attester も pass |

# 範囲

これは限定 schema fixture と補助モデルの検査であり、strict JSON parser、完全な入力 codec、LPTL コンパイラ、encoder、BLAKE3 digest 検証、証明、LLM 実験ではない。byte span、message／repair、transport の bytes／深さ guard、host behavior を含まない。G0 などの [出荷ゲート](../overview/status-and-gates.md) の代用にしない。

[^manifest]: v1 artifact manifest
[^verification-report]: LPTL v1 統一版：突き合わせ確認報告
