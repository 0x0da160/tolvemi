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

[^lptl-design]: LLM向け純粋・全域言語：設計方針 v1
