---
type: Language Specification
title: 名前解決とスコープ
description: トップレベル関数名と引数名は一意、let は非再帰、let/fold binder は外側の変数をシャドーできず、トップレベル関数は前方参照できる。
tags: [lptl, names, scope]
status: draft
generated: { by: claude-code/2026-10-06, at: 2026-10-06T16:00:00Z }
sources:
  - id: lptl-design
    resource: ../../spec/lptl-v1/LPTL_design_v1.md
    title: LLM向け純粋・全域言語：設計方針 v1（§5.1、§10.3）
    last_modified: 2026-10-01T00:00:00Z
---

# 規則

- トップレベル関数名は一意。同一関数の引数名は一意。[^lptl-design]
- `let x = e1 in e2` の `x` は `e2` だけで束縛され、`e1` には可視でない（自己参照 let なし）。
- `fold(xs, init, |acc, item| body)` の binder は `body` だけで可視。二 binder は相異なる。
- `let` binder と `fold` binder は、外側の可視変数を**シャドーできない**。
- 外側の関数引数、外側 `let`、外側 `fold` binder は参照できる。
- 全トップレベル関数は全プログラムで可視であり、**前方参照を許可**する。
- オーバーロード、局所関数、名前空間、メソッド記法はない。

# name phase の走査と診断

- トップレベル、各関数の引数と式を入力・前順で走査する。
- 重複名は後続定義を診断し、曖昧名の使用に派生 unknown を出さない。
- shadow binder は診断した上でその局所範囲に導入し、未束縛由来の派生診断を避ける。
- 未知 call は name error だけで後続を停止する。name error がある木は受理せず、call-graph 以降を実行しない（[パイプライン](../diagnostics/pipeline.md)）。
- 代表コード：`E-NAME-UNKNOWN-FUNCTION`（未定義の合法 callee 名）、fold の `acc` と `item` が同名なら binder 重複。

entry 名の解決は [entry と到達可能性](entry-and-reachability.md) を参照。


# v1.4 の追加：match_result、構築子、match

- `match_result(m, |x| a, |y| b)` の x と y はそれぞれの枝でだけ見え、外側の可視変数をシャドーできない（x と y は同じ
  名前でもよい）。
- 直和型の構築子の名前はプログラム全体で一意（`E-SUM-DUPLICATE-CTOR`）で、関数・変数・型と同じ名前は使えない
  （`E-SUM-NAME-CONFLICT`）。知らない構築子は `E-SUM-UNKNOWN-CTOR`、中身の数の違いは `E-SUM-CTOR-ARITY`。
- `match` の pattern が束縛する名前はその枝でだけ見え、外側の名前をシャドーできず、一つの枝の中で相異なる（`_` は束縛しない）。
- `match` は全部の場合を一度ずつ書くか最後の `_` で残りをまとめる。足りない場合 `E-MATCH-MISSING`、重複
  `E-MATCH-DUPLICATE`、届かない枝 `E-MATCH-UNREACHABLE`、型の違う pattern の混在 `E-MATCH-MIXED`（いずれも name phase）。


# v1.5 の追加：map などの binder

`map(xs, |x| e)` などの x は e の中でだけ見え、外側の可視変数をシャドーできない（`E-NAME-SHADOW`。`match_option` の
binder と同じ規則）。e は外側の変数を参照できる。書き換えで導入する名前（`hof1` など）はプログラム中のどの名前とも
重ならない。

[^lptl-design]: LLM向け純粋・全域言語：設計方針 v1
