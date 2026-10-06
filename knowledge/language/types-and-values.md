---
type: Language Specification
title: 型と値
description: LPTL v1 の型は Int・Bool・Unit・List<T>・Option<T>・Pair<A,B> の6種で、値は循環・参照・関数を持たない有限木である。
tags: [lptl, types, values]
status: draft
generated: { by: claude-code/2026-10-06, at: 2026-10-06T16:00:00Z }
sources:
  - id: lptl-design
    resource: ../../spec/lptl-v1/LPTL_design_v1.md
    title: LLM向け純粋・全域言語：設計方針 v1（§3.1、§3.2）
    last_modified: 2026-10-01T00:00:00Z
---

# Schema

```text
T, A, B ::= Int | Bool | Unit
    | List<T>
    | Option<T>
    | Pair<A, B>
```

| 型 | 値 | 備考 |
|---|---|---|
| `Int` | 整数 | 数学的任意精度整数 |
| `Bool` | `true`、`false` | |
| `Unit` | `unit` | 唯一の値 |
| `List<T>` | `list[T](v, ...)` | 有限個の `T` 値からなる順序付き同種リスト |
| `Option<T>` | `some(v)`、`none[T]` | 一般 payload の取り出しは不可（[Option の境界](option-boundary.md)） |
| `Pair<A,B>` | `pair(v, w)` | 二成分は独立した型 |

# 規則

- **型等価性は構文的等価性。** サブタイピングや暗黙変換はない。[^lptl-design]
- **v1 の全型は構造的等値可能**（`eq` が使える）。ただし将来導入される型が自動的に等値可能になることはなく、型ごとに明示する。
- **値は有限木としての数学的値。** 実装は共有を持つ不変 DAG 表現を使ってよいが、観測可能な意味は有限木の展開で定義する。
- 循環値、参照値、関数値、未初期化値は存在しない。
- 値の文法：`v ::= 整数 | true | false | unit | list[T](v, ...) | some(v) | none[T] | pair(v, v)`

意味論上の木展開量と物理割当量の区別は [資源モデル](../resources/resource-model.md)、JSON 表現は [値 JSON codec](../api/value-json-codec.md) を参照。

[^lptl-design]: LLM向け純粋・全域言語：設計方針 v1
