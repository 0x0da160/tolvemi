---
type: Artifact Manifest
title: 検証バンドル
description: LPTL_v1_verification_bundle.zip の配布ファイルと SHA-256、v1 名前空間統一の突き合わせ確認（構造照合34/34、限定 fixture 92/92）と、検証していない範囲。
tags: [lptl, verification, manifest, artifacts]
status: draft
resource: ../../spec/lptl-v1/v1_artifact_manifest.json
generated: { by: claude-code/2026-10-06, at: 2026-10-06T16:00:00Z }
verified: { by: process:sha256sum-vs-manifest, at: 2026-10-06T15:20:00Z }
sources:
  - id: manifest
    resource: ../../spec/lptl-v1/v1_artifact_manifest.json
    title: v1 artifact manifest
  - id: verification-report
    resource: ../../spec/lptl-v1/LPTL_v1_verification_report.md
    title: LPTL v1 統一版：突き合わせ確認報告
    last_modified: 2026-10-01T00:00:00Z
  - id: lptl-design
    resource: ../../spec/lptl-v1/LPTL_design_v1.md
    title: LLM向け純粋・全域言語：設計方針 v1（§20.3–§20.5）
    last_modified: 2026-10-01T00:00:00Z
---

# Schema

リポジトリの [`spec/lptl-v1/`](../../spec/lptl-v1/) に展開済み。manifest が記録する bytes と SHA-256：[^manifest]

| ファイル | 役割 | bytes | SHA-256 |
|---|---|---:|---|
| `LPTL_design_v1.md` | 設計本文 | 144,238 | `f5290a35ab614f75f609930e12117e38adf88862ce22dad81ba2d4ba2995c87d` |
| `LPTL_v1_verification_report.md` | 突き合わせ確認報告 | 8,730 | `a8ef7c781ad03509da868e289ea0b6aff53a009ff7e3602d22dd575c796546d0` |
| `ast_codec_v1.schema.json` | AST schema | 22,699 | `ff8ad602c3b5889acd8146a6b487aa81c0d93f88ed3e4680d9440da7e4085f4a` |
| `v1_limited_checks.py` | 限定検査コード | 13,396 | `a3c183f8870c97d2e6be7f60c0f3da7f838ca54fb5a0bed29fac4814c13791dc` |
| `v1_check_inputs.json` | 検査入力・期待値 | 46,915 | `6de560583a06d54e08c4cfa56630563abb616b3a47e00ebe6fee6eab4a5077d2` |
| `v1_checks.csv` | 観測結果（再生成される） | 11,639 | `a15f3f2e09e59bd815adfdb7fc0e0f0c55327824e67b7fcfb8de3e21aabe403d` |
| `v1_fixture_correspondence.csv` | fixture 対応表 | 3,650 | `c282e4a22bee20af5fc046626953b1d5d97f31f5a4106f873bc28bbfb7dcfafb` |
| `v1_namespace_registry.json` | 識別子レジストリ | 1,330 | `2a350962743a5592f4769cc7dc17860209207d5604deffee7b9d2ebca92216ab` |
| `v1_structure_checks.json` | 構造照合 | 6,692 | `f0e2eebdb3c0bb226a8ea147870a8d7ff572878376ef5f51a0b30b61eb6c99bb` |
| `v1_edit_ranges.csv` | 編集範囲一覧 | 4,006 | `9a4066ff2abd7c42fdf9dac0d3743e2c57b766998d3000b2b9e74cbf70939a04` |

manifest 自身は自己 hash を持たない。2026-10-14 に、リポジトリ内の全10ファイルの bytes と SHA-256 が上表と一致することを確認した（v1.x の全 node を反映し、名前の除外語を 68 語へ改めた後）（`verified` の process）。

# 突き合わせ確認の結果

v1 統一版では、文書版だけでなく codec、schema の ID・title・codec 固定値、10設計契約 ID、研究 arm、検証段階、ハッシュ domain、ファイル名を v1 名前空間へ統一した。計算意味論、文法、型規則、評価順、資源上限、診断コード、検査順、評価集計条件は保持した。[^verification-report]

| 確認 | 結果 |
|---|---|
| 構造・名前空間・契約照合 | 34項目中34通過 |
| 第0–20節 | 21主要節を保持 |
| コードブロック | 34ブロック。codec／domain の v1 置換以外は内容・順序一致 |
| 診断コード | 52種類、追加・欠落なし |
| schema 構造 | 変更は `$id`・`title`・`properties.codec.const` の3箇所 |
| 限定 fixture | 比較基準の92件、v1 化後の92件ともに通過（Python 3.12.8、jsonschema 4.23.0） |

旧名前空間との codec 互換は維持しない（旧 codec を alias として受理しない）。旧 hash を v1 の hash として流用しない。

# 検証していない範囲

Rust/Verus spec との照合、LPTL 処理系、strict JSON token parser、全型 input decoder／encoder、元 byte span、message／repair、transport guard、host behavior、追加予算成分・provider usage 集計、reproducibility record の実装適合、機械証明、LLM 実験。BLAKE3 digest は計算・検証していない。有限 fixture 通過を無欠陥・実装適合・形式証明・出荷の宣言へ代用しない。[^lptl-design]

[^manifest]: v1 artifact manifest
[^verification-report]: LPTL v1 統一版：突き合わせ確認報告
[^lptl-design]: LLM向け純粋・全域言語：設計方針 v1
