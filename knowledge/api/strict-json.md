---
type: Data Format
title: strict JSON と decode 順序
description: input と AST transport に共通の strict JSON 契約（bytes→UTF-8→文法・深さ→string scalar→重複キー→内容の段階順）と、値位置ごとの決定論的な検査順・最初の一件の選択規則。
tags: [lptl, json, decoder, diagnostics]
status: draft
generated: { by: claude-code/2026-10-06, at: 2026-10-06T16:00:00Z }
sources:
  - id: lptl-design
    resource: ../../spec/lptl-v1/LPTL_design_v1.md
    title: LLM向け純粋・全域言語：設計方針 v1（§9.3a、§9.4、§18.2）
    last_modified: 2026-10-01T00:00:00Z
---

# 共通の段階順

input と AST transport の両方に適用する。[^lptl-design]

```text
JSON bytes → UTF-8 → JSON 文法／構造深さ → string scalar 妥当性 → 重複キー → object／値内容
```

- 各段階は全体で成功した場合だけ次へ進む。文法／深さ段階は元 bytes 上の最初の観測違反で停止する。streaming で候補を集めてもこの順を変えて返さない。
- 全ての JSON string（key、tag、payload、未知 field 内を含む）を escape decode 後の Unicode scalar 列として扱う。正しい surrogate 対は復号し、単独 high・単独 low・不正な対を拒否する。scalar 違反が複数なら最初の不正 string token を選び、引用符を含む token 全体を主 span とする。
- キーは decode 後の scalar 列の完全一致で比較し、Unicode 正規化・case 変換・trim をしない。`"name"` と `"name"` は重複。重複候補は二番目の key token の開始位置で最初の一件を選ぶ。
- unknown key の辞書順は scalar 整数値列の辞書順（prefix が同じなら短い方が先）。

| 違反 | input のコード（phase） | AST のコード（phase） |
|---|---|---|
| JSON 文法 | `E-INPUT-JSON-SYNTAX`（input-parse） | `E-AST-JSON-SYNTAX`（ast-parse） |
| string scalar | `E-INPUT-STRING-SCALAR`（input-parse） | `E-AST-STRING-SCALAR`（ast-parse） |
| 重複キー | `E-INPUT-DUPLICATE-KEY`（input-parse） | `E-AST-DUPLICATE-KEY`（ast-parse） |
| bytes 上限 | `E-LIMIT-INPUT-JSON-BYTES`（input-boundary） | `E-AST-LIMIT-BYTES` |
| JSON 深さ上限 | `E-LIMIT-INPUT-JSON-DEPTH`（input-parse） | `E-AST-LIMIT-JSON-DEPTH` |

# 入力値の decode 順序（値位置ごと）

全体 transport 段階の通過後、期待型を伴う root 値デコードを開始し、全体で最初の一件のみ返す。各値位置で次を順に行う。

1. object であること
2. `tag` キーの存在、string 型、期待型に対応する tag
3. 必須キー、次に余分キー
4. 全直接 field の浅い JSON 型（正準 key 順。子の内部はまだ見ない）
5. InputAdmission：値深さと累積 SemanticTreeNodes を guard（深さ超過を優先）。成功時だけ一値 node の Admission を発行
6. 内容検査：Int は正規形 → 桁数 guard → 整数変換。pair は left→right、list は items 入力順、some は value へ再帰

| 違反 | コード | 主 span |
|---|---|---|
| object でない／浅い JSON 型 | `E-INPUT-FIELD-TYPE` | 該当 field 値（root 非 object は root 全体） |
| tag 欠落、その他の欠落 | `E-INPUT-MISSING-FIELD` | object 閉じ括弧直前のゼロ幅 |
| tag 型／不一致 | `E-INPUT-TAG` | 対応 string／JSON 値 token |
| 余分キー | `E-INPUT-UNKNOWN-FIELD` | 選択 key token |
| 整数正規形 | `E-INPUT-INTEGER` | value string token |
| 値深さ／node 数 | `E-LIMIT-INPUT-VALUE-DEPTH` / `-VALUE-NODES` | 当該値 object 全体 |
| 整数桁数 | `E-LIMIT-INPUT-INTEGER-DIGITS` | value string token |

phase はいずれも input-decode。欠落キーは正準 key 順、余分キーは scalar 辞書順で最初を選び、member 入力順を選択に混ぜない。

# 境界例

| 入力 | 主結果 |
|---|---|
| `Pair<Unit,Unit>`、深さ上限1、left に余分キー | 子のキー検査が子 Admission より先 → `E-INPUT-UNKNOWN-FIELD` |
| `Pair<Unit,Unit>`、深さ上限1、子は正常 | 子 Admission で `E-LIMIT-INPUT-VALUE-DEPTH` |
| Int 正規形違反と node 数超過 | Admission の VALUE-NODES が先（正規形は未検査） |
| Int 正規形違反と桁上限超過 | `E-INPUT-INTEGER` が先 |
| Int.value が number、node 数上限0 | 浅い型違反 `E-INPUT-FIELD-TYPE` が先 |
| 重複キーと root tag 違反 | 全体重複段階が先 → `E-INPUT-DUPLICATE-KEY` |

InputAdmission は入力 codec の論理イベント（識別子 `input-admission-v1`）であり、物理 allocation とは別。上限値は [input profile](../resources/input-and-transport-profiles.md)。

[^lptl-design]: LLM向け純粋・全域言語：設計方針 v1
