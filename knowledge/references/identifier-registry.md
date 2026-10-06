---
type: Reference
title: 識別子レジストリ
description: LPTL v1 名前空間の固定識別子（codec、schema ID、10の契約 ID、研究 arm、検証段階、4つのハッシュ domain）と、spec_version が null である状態。
tags: [lptl, identifiers, namespace, registry]
status: draft
resource: ../../spec/lptl-v1/v1_namespace_registry.json
generated: { by: claude-code/2026-10-06, at: 2026-10-06T16:00:00Z }
sources:
  - id: namespace-registry
    resource: ../../spec/lptl-v1/v1_namespace_registry.json
    title: v1 namespace registry
  - id: verification-report
    resource: ../../spec/lptl-v1/LPTL_v1_verification_report.md
    title: LPTL v1 統一版：突き合わせ確認報告
    last_modified: 2026-10-01T00:00:00Z
---

# Schema

各識別子は用途ごとに独立した固定文字列で、別名前空間の同名 ID を同一として受理・解釈しない。[^namespace-registry]

| 対象 | 識別子 |
|---|---|
| 文書・言語ラベル | `v1` |
| AST codec | `ast_codec_v1` |
| AST schema ファイル | `ast_codec_v1.schema.json` |
| Schema ID / title | `urn:lptl:ast-codec:v1` / `LPTL ast_codec_v1` |
| Static profile | `static-v1-reference-1` |
| Parse Admission | `parse-admission-v1` |
| Typecheck cost | `typecheck-cost-v1` |
| Input profile | `input-v1-reference-1` |
| Input Admission | `input-admission-v1` |
| Diagnostic pipeline | `diagnostic-pipeline-v1` |
| Evaluation protocol | `evaluation-protocol-v1` |
| Reference cost model | `resource-profile-v1-reference-1` |
| AST transport profile | `ast-transport-v1-reference-1` |
| Execution profile | `execution-v1-reference-1` |
| 研究 arm | `v1-no-let`、`v1-no-cons-concat-reverse` |
| 検証段階 | `V1-A`、`V1-B`、`V1-C` |
| `spec_version` | `null`（未確定） |

| ハッシュ用途 | domain（`\0` は NUL byte） |
|---|---|
| 言語成果物 | `LPTL-artifact-v1\0` |
| AST 構文 | `LPTL-AST-v1\0` |
| 規範仕様結合 | `LPTL-spec-bound-syntax-v1\0` |
| 再現 record | `LPTL-reproducibility-v1\0` |

# 規則

- 表の "reference-1" は数値設定の略記であって版識別子の代用ではない。これらは実装済み spec_version や凍結済み profile ではない。
- 限定検査で使う `spec-test-a`／`spec-test-b` は版分離を試す架空 fixture ID で、公表版ではない。[^verification-report]
- JSON Schema Draft 2020-12、Python、jsonschema の実際の版は外部規格・依存ソフトの識別であり、v1 へ偽装しない。
- 公開名称が [Tolvemi](/overview/naming.md) になっても、これらの `LPTL` を含む固定識別子は一括置換しない。変更が必要なら凍結状態・成果物・互換性・移行規則への影響を確認する。

[^namespace-registry]: v1 namespace registry
[^verification-report]: LPTL v1 統一版：突き合わせ確認報告
