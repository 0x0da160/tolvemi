---
type: Identity Contract
title: ハッシュと同一性
description: LPTL の4種のハッシュ（成果物 hash、structural_hash、spec_bound_syntax_hash、reproducibility_hash）の preimage と用途、spec_version 未確定時は正式な仕様結合・再現 hash を発行しない規則。
tags: [lptl, hash, blake3, reproducibility]
status: draft
generated: { by: claude-code/2026-10-06, at: 2026-10-06T16:00:00Z }
sources:
  - id: lptl-design
    resource: ../../spec/lptl-v1/LPTL_design_v1.md
    title: LLM向け純粋・全域言語：設計方針 v1（§4.3、§19.4、§20.4）
    last_modified: 2026-10-01T00:00:00Z
  - id: namespace-registry
    resource: ../../spec/lptl-v1/v1_namespace_registry.json
    title: v1 namespace registry
---

# 4種のハッシュ

`\0` は NUL byte を表す（文字 `\` と `0` の2 byte ではない）。[^namespace-registry]

## 成果物 hash（実験・配布・改竄検知）

```text
BLAKE3(
  "LPTL-artifact-v1\0" ||
  spec_version || "\0" ||
  canonical_source(P) || "\0" ||
  resource_profile_id || "\0" ||
  skill_hash
)
```

`canonical_source(P)` は [正準フォーマット](../language/canonical-formatting.md) の出力。[^lptl-design]

## structural_hash（codec レベルの構文同一性）

```text
structural_hash(A) = BLAKE3("LPTL-AST-v1\0" || encode_ast(A))
```

domain はcodec／構文の版を識別し、spec_version ではない。spec_version・診断・静的検査・実行 profile の互換性を表さない。

## spec_bound_syntax_hash（規範仕様への結合）

```text
spec_bound_syntax_hash(spec_version,A) = BLAKE3(
  "LPTL-spec-bound-syntax-v1\0" ||
  canonical_json([spec_version, "ast_codec_v1", structural_hash(A).lower_hex])
)
```

spec_version が未確定（本成果物では null）の場合は**発行しない**。null、仮の文書版、言語ラベルで代用しない。

## reproducibility_hash（診断・cutoff・運用結果の再現）

reproducibility record の必須 fields（正準 key 順）：`spec_version`、`codec_id`、`structural_hash`、`static_profile_id`、`parse_admission_id`、`typecheck_cost_id`、`input_profile_id`、`input_admission_id`、`ast_transport_profile_id`、`execution_profile_id`、`diagnostic_pipeline_id`、`host_policy_hash`、`skill_hash`。`host_policy_hash`／`skill_hash` は公開 bytes の SHA-256。record の canonical JSON bytes を domain `"LPTL-reproducibility-v1\0"` に連結した BLAKE3 が reproducibility_hash。spec_version 未確定なら正式 record／hash を発行しない。実験再現にはさらにモデル、task、予算 B、seed 等が必要。

# 意味と限界

- いずれも**構文の** hash であり、意味等価性を判定しない。alpha-renaming、宣言の並べ替え、等価な書換えを同一視しない。
- コメント、入力時の空白、JSON object の入力順序、escape の差は正準化で消える。宣言順と binder 名は消えない。
- 同 AST／codec で spec_version が異なれば、structural_hash は同じで spec_bound_syntax_hash の preimage は異なる。
- record の一致は同じ入力や物理 host を意味せず、host 結果の機種間一致も保証しない。
- 名前空間 v1 を要求し、別名前空間との hash 同一性を保証しない（[識別子レジストリ](../references/identifier-registry.md)）。

# ファイル実体の同一性

文書、schema、検査入力、検査コード、検査結果は別ファイル実体として manifest に bytes と SHA-256 を記録する。ファイルの SHA-256 は BLAKE3 の言語成果物 hash や spec_version の代用ではない。文書・manifest は自己 hash を埋め込まない。BLAKE3 digest は本成果物では計算・検証していない（[検証バンドル](../conformance/verification-bundle.md)）。

[^lptl-design]: LLM向け純粋・全域言語：設計方針 v1
[^namespace-registry]: v1 namespace registry
