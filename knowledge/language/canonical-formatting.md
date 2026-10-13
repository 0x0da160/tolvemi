---
type: Language Specification
title: 正準フォーマット
description: LPTL の formatter はバージョン付き公開成果物で、AST の意味を保存し、各宣言を一行・カンマ後に空白一つ・コメント除去で出力する。
tags: [lptl, formatter, canonical-source]
status: draft
generated: { by: claude-code/2026-10-06, at: 2026-10-06T16:00:00Z }
sources:
  - id: lptl-design
    resource: ../../spec/lptl-v1/LPTL_design_v1.md
    title: LLM向け純粋・全域言語：設計方針 v1（§4.3、§19.4）
    last_modified: 2026-10-01T00:00:00Z
---

# 出力規則

フォーマッタはバージョン付き公開成果物である。[^lptl-design]

| 対象 | 正準形 |
|---|---|
| 関数 | `fn NAME(PARAMS) -> TYPE = EXPR` |
| entry | `entry NAME` |
| 引数 | `NAME: TYPE` |
| let | `let NAME = EXPR in EXPR` |
| fold lambda | `\|ACC, ITEM\| EXPR` |
| call | `NAME(ARGS)` |
| 型引数付き構成子 | `list[TYPE](ARGS)`、`none[TYPE]` |
| Pair 型 | `Pair<A, B>` |

- `,` の直後に ASCII space を一つ置く。それ以外の句読点周辺には空白を挿入しない。
- 整数は `INT` の正規形で出力する。
- コメントは除去する。
- 名前・型に依存する書換えをせず、AST の意味を保存する。宣言順序・名前・型注釈を保持する。
- 各宣言を一行に出力し、宣言間は LF 一つ、末尾も LF 一つ。インデント・空行・CR は出力しない。

`canonical_source(P)` は、受理済み AST を formatter が UTF-8 で出力した値で、[成果物ハッシュ](../api/hashes-and-identity.md) の入力になる。

# 往復性と有限 profile

抽象的には `parse(format(A)) = A`（source span・コメント・元の空白を除いた構文 AST について）。ただし同一 profile で受理した source の formatter 出力が同一 profile で再受理される保証はない。

境界 fixture：関数名を 524,276 文字の `f` 列とすると、`fn N(x:Int)->Int=x entry N` は 1,048,576 bytes で source 上限を通過するが、format 出力は 1,048,582 bytes になり同じ profile へ再投入すると `SOURCE-BYTES` で拒否される。これは抽象往復を否定しない。


# v1.4 の追加

`Result<A, B>`、`ok<A, B>(EXPR)`、`err<A, B>(EXPR)`、`match_result(EXPR, |X| EXPR, |Y| EXPR)` は検証済み formatter が
この形に整形する。直和型・`match` を含むプログラムは診断用 formatter が `type S = A(T) | B`、
`match EXPR { P => EXPR, ... }` の形に整形する（レコードと同じく検証済み formatter の対象外）。


# v1.5 の追加

`map(EXPR, |X| EXPR)`（`filter`、`any`、`all`、`find`、`sort_by` も同じ形）。これを含むプログラムは検証済み formatter の
対象外で、`tlvm fmt` は診断用 formatter の出力を出す（レコード・直和型と同じ）。

# v1.6 の追加

`loop(EXPR, EXPR, |X| EXPR)`。これを含むプログラムも検証済み formatter の対象外で、`tlvm fmt` は診断用 formatter の
出力を出す。

# v1.7 の追加

`rec fn NAME(...) -> T = EXPR`（`rec` と `fn` の間は空白一つ）。検証済み formatter は `rec` を知らないので、`tlvm fmt` は
印を外したものを検証済み formatter で照合し、印を付けて出す（レコードなどを含むときは診断用 formatter の出力）。

# v1.9 の追加

型は `Dict<T, T>`、空の辞書は `dict<T, T>()`、操作は組み込み関数の呼び出しと同じ形。これを含むプログラムも検証済み
formatter の対象外で、`tlvm fmt` は診断用 formatter の出力を出す。

# v1.10 の追加

`fn f<T, U>(...)`、`type Box<T> = ...`、型 `Box<Int>`、呼び出し `f<Int>(x)`、構築 `Leaf<Int>()`（`<` の前後に空白なし、
`,` の後に空白一つ）。総称の構文を含むプログラムは検証済み formatter の対象外で、`tlvm fmt` は診断用 formatter の出力を出す。

[^lptl-design]: LLM向け純粋・全域言語：設計方針 v1
