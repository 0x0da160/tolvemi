---
type: Resource Profile
title: input と AST transport の profile
description: input-v1-reference-1（JSON 4 MiB・構造深さ512・値深さ128・262,144 node・4,096 桁）と ast-transport-v1-reference-1（JSON 16 MiB・構造深さ1,024）の上限と数え方。
tags: [lptl, resources, input, json]
status: draft
generated: { by: claude-code/2026-10-06, at: 2026-10-06T16:00:00Z }
sources:
  - id: lptl-design
    resource: ../../spec/lptl-v1/LPTL_design_v1.md
    title: LLM向け純粋・全域言語：設計方針 v1（§18.2）
    last_modified: 2026-10-01T00:00:00Z
---

# Schema

| profile | 項目 | 上限 |
|---|---|---:|
| input-v1-reference-1 | JSON bytes | 4,194,304 |
| input-v1-reference-1 | JSON 構造深さ | 512 |
| input-v1-reference-1 | 値深さ | 128 |
| input-v1-reference-1 | SemanticTreeNodes | 262,144 |
| input-v1-reference-1 | Int 桁数 | 4,096 |
| ast-transport-v1-reference-1 | JSON bytes | 16,777,216 |
| ast-transport-v1-reference-1 | JSON 構造深さ | 1,024 |

[^lptl-design]

# 数え方

- JSON 構造深さは object／array の開き括弧について、根の container を1とする。
- 値深さは各値の根を1とする。
- SemanticTreeNodes は int、bool、unit、none、some、pair、list をそれぞれ一つとし、list の要素値を加算する（cons spine の物理 node 数ではない）。

# input のコードと検査時点

`E-LIMIT-INPUT-JSON-DEPTH`、`E-LIMIT-INPUT-VALUE-DEPTH`、`E-LIMIT-INPUT-VALUE-NODES`、`E-LIMIT-INPUT-INTEGER-DIGITS`（bytes は `E-LIMIT-INPUT-JSON-BYTES`）。値 node・深さの guard は InputAdmission 直前、つまり object header・キー集合・全直接 field の浅い型検査後かつ内容再帰前。同時超過は値深さを優先。整数桁数 guard は同じ値の Admission と正規形検査の後。手順全体は [strict JSON と decode 順序](/api/strict-json.md)。

# AST transport

AST transport の上限は表記に固有で、source bytes と同じ数値にはしない。共通の AST node・型・式上限は Surface と同一（[static profile](/resources/static-profile.md)）。AST と Surface の transport byte 数は別々に記録し、表記の長さが同じだったと見なさない。

[^lptl-design]: LLM向け純粋・全域言語：設計方針 v1
