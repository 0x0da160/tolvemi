---
type: Data Format
title: 診断 schema
description: LPTL の各診断は severity・phase・code・span・expected・actual・message・repair の8キーを正準順に持つ一行の JSON object で、span は UTF-8 byte の半開区間、repair は保証のない修復 hint である。
tags: [lptl, diagnostics, json, repair]
status: draft
generated: { by: claude-code/2026-10-06, at: 2026-10-06T16:00:00Z }
sources:
  - id: lptl-design
    resource: ../../spec/lptl-v1/LPTL_design_v1.md
    title: LLM向け純粋・全域言語：設計方針 v1（§10.1）
    last_modified: 2026-10-01T00:00:00Z
---

# Schema

各診断は JSON object 一つを一行で出す。必須キーと正準出力順は次の通りで、未知キーは禁止。[^lptl-design]

| キー | 内容 |
|---|---|
| `severity` | `error` または `warning` |
| `phase` | 版付き台帳の列挙（[パイプライン](/diagnostics/pipeline.md)） |
| `code` | 版付き台帳の列挙（[コード一覧](/diagnostics/diagnostic-codes.md)）。prefix は対象領域で phase と一対一ではない（例：`E-ENTRY-UNKNOWN` の phase は `name`） |
| `span` | `{"start":非負整数,"end":非負整数}`、start<=end。UTF-8 **bytes** の半開区間。source API は source bytes、AST API は元 JSON bytes、input API は元入力 JSON bytes を対象とする（文字数ではない） |
| `expected` | 正準型・制約の string または null |
| `actual` | 同上 |
| `message` | 版固定のテンプレートから生成 |
| `repair` | null または下記 object |

```text
repair = {
  "kind": "replace_expression" | "replace_identifier" |
          "replace_type" | "insert_text" | "delete_span",
  "target_span": {"start": Nat, "end": Nat},
  "constraint": String
}
```

- repair の3キーは全て必須、余分なキー禁止。`insert_text` はゼロ幅 span。
- **hint は修復の正しさ・唯一性を保証しない。** 未実装の repair を推測して出さない。AST API は安全な JSON 部分木置換を指定できなければ repair=null。

型表示は `Int`、`Bool`、`Unit`、`List<Int>`、`Option<List<Int>>`、`Pair<Int, List<Option<Bool>>>` の形式。

# Examples

```json
{"severity":"error","phase":"typecheck","code":"E-TYPE-IF-BRANCH","span":{"start":84,"end":101},"expected":"Int","actual":"Option<Int>","message":"if の両分岐は同じ型でなければなりません","repair":{"kind":"replace_expression","target_span":{"start":84,"end":101},"constraint":"expression of type Int"}}
```

# 設計意図

安定コード・byte 位置・期待制約・決定論的順序を返すことで、LLM などの修復器が局所的に直せるようにする（設計目標「局所修復可能性」、[設計目標](/overview/scope.md)）。RunResult と UTF-8 境界失敗は診断列ではなく結果 envelope として返す。

[^lptl-design]: LLM向け純粋・全域言語：設計方針 v1
