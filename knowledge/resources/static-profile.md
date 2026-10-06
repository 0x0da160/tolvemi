---
type: Resource Profile
title: static profile と型検査仕事量
description: static-v1-reference-1 の11項目の静的上限と検査点、および typecheck-cost-v1 が定める VisitExpr・BuildType・CompareType による型検査の論理仕事量の数え方。
tags: [lptl, resources, static-limits, typecheck]
status: draft
generated: { by: claude-code/2026-10-06, at: 2026-10-06T16:00:00Z }
sources:
  - id: lptl-design
    resource: ../../spec/lptl-v1/LPTL_design_v1.md
    title: LLM向け純粋・全域言語：設計方針 v1（§18.1、§18.1a）
    last_modified: 2026-10-01T00:00:00Z
---

# Schema

識別子 `static-v1-reference-1`。全コードは `E-LIMIT-STATIC-` に末尾を連結する。[^lptl-design]

| static 項目 | 上限 | コード末尾 | 検査点 |
|---|---:|---|---|
| source bytes | 1,048,576 | SOURCE-BYTES | source-boundary |
| token 数（EOF 除外） | 131,072 | TOKENS | lexical-limits |
| 整数リテラル桁数（符号除外） | 4,096 | INTEGER-DIGITS | lexical-limits |
| 関数数 | 1,024 | FUNCTIONS | structural-limits |
| AST node 数 | 131,072 | AST-NODES | structural-limits |
| 型構文深さ | 64 | TYPE-DEPTH | structural-limits |
| 式深さ | 256 | EXPR-DEPTH | structural-limits |
| let ネスト深さ | 128 | LET-DEPTH | structural-limits |
| fold ネスト深さ | 32 | FOLD-DEPTH | structural-limits |
| 推論された型深さ | 128 | SEMANTIC-TYPE-DEPTH | semantic-limits |
| 型検査イベント数 | 2,000,000 | SEMANTIC-WORK | semantic-limits |

# 数え方

- AST node は program、各 fn／entry、param、各型構成子、各式をそれぞれ一つ。lambda は fold node の binder field で独立 node ではない。名前 string、整数 string、配列、span は数えない。
- 型・式深さは根を1とし、同種の子へ進むごとに1増加。関数本体の式深さは1から。let／fold 深さは一つの式経路上の該当 node 数（兄弟の合計ではない）。
- 明示された型の出現は全て別 node と数え、interning で減らさない。
- 同じ token で正規形・境界違反と桁上限が競合したら正規形・境界を先に判定。同じ token の桁超過を token count より先に返す。

# 型検査の論理仕事量（typecheck-cost-v1）

SemanticWork は次の論理イベント数の合計。実装の型オブジェクト確保・共有・interning・cache hit 数は数えない。

| イベント | 意味 |
|---|---|
| VisitExpr | 一つの式 node の型検査開始 |
| BuildType | 結果型の外側構成子一つを論理的に構成 |
| CompareType | 型等価性検査の一つの構成子対、または外側 tag の検査 |

BuildType の発行：literal は1、list・none・some・pair は外側1、add/sub/mul/neg/length/lt/le/eq は結果1、mod は2（内側 Int、外側 Option）、var・let・if・fold・ユーザー call・fst・snd・cons・concat・reverse・ErrorType は0。

CompareType：完全型の比較 `Equal(A,B)` は根から走査し、Pair は left→right、最初の不一致で停止。外側 tag の検査 `Head(T,Tag)` は1イベント。ErrorType との比較は0イベントで二次診断なし。

| builtin | 引数制約の比較順 |
|---|---|
| add、sub、mul、lt、le、mod | Equal(arg1,Int) → Equal(arg2,Int) |
| neg | Equal(arg1,Int) |
| eq | Equal(arg1,arg2) |
| fst、snd | Head(arg1,Pair) |
| cons | Head(arg2,List)、成功時に Equal(arg1,arg2.element) |
| concat | Head(arg1,List) → Head(arg2,List)、両方成功時に Equal(要素型) |
| reverse、length | Head(arg1,List) |

各論理イベントの直前に上限を検査し、超過イベントを発行せず `E-LIMIT-STATIC-SEMANTIC-WORK` で停止する。BuildType では型深さを先に検査し、同時超過は SEMANTIC-TYPE-DEPTH を優先。cutoff 後は entry／warnings を実行しない。

# Examples

規則から導く trace の期待値（処理系の測定値ではない）。[限定検査](../conformance/limited-checks.md) の type_trace_model で照合されている。

| 関数 | VisitExpr | BuildType | CompareType | 合計 |
|---|---:|---:|---:|---:|
| `fn f(x: Int) -> Int = x` | 1 | 0 | 1 | 2 |
| `fn f(x: Unit) -> Int = 0` | 1 | 1 | 1 | 3 |
| `fn f(x: Unit) -> Int = add(1, 2)` | 3 | 3 | 3 | 9 |
| `fn f(x: Unit) -> Option<Int> = some(0)` | 2 | 2 | 2 | 6 |
| `fn f(x: Unit) -> List<Int> = list[Int](1, 2)` | 3 | 3 | 4 | 10 |
| `fn f(x: Unit) -> Option<Int> = none[Int]` | 1 | 1 | 2 | 4 |

`add` 例で SemanticWork 上限9なら完了、8なら SEMANTIC-WORK cutoff。`add(1,true,0)` で上限0なら call の VisitExpr 前 cutoff のみ、1なら `E-ARITY-BUILTIN` を保持して最初の子の VisitExpr 前で cutoff。

[^lptl-design]: LLM向け純粋・全域言語：設計方針 v1
