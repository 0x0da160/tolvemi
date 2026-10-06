---
type: Language Specification
title: 呼出しグラフと DAG
description: ユーザー関数の呼出しグラフは自己辺を含む全循環を拒否する DAG でなければならず、fold 本体や非選択枝の call も辺に含めて rank を構成する。
tags: [lptl, call-graph, dag, termination]
status: draft
generated: { by: claude-code/2026-10-06, at: 2026-10-06T16:00:00Z }
sources:
  - id: lptl-design
    resource: ../../spec/lptl-v1/LPTL_design_v1.md
    title: LLM向け純粋・全域言語：設計方針 v1（§5.4、§10.2）
    last_modified: 2026-10-01T00:00:00Z
---

# 受理条件

ユーザー関数集合を `F` とし、`f` の本体が `g(...)` を含むとき辺 `f -> g` を置く。[^lptl-design]

```text
受理条件：call_graph(P) は DAG である。
```

- 自己辺を含む全循環を拒否する。一般再帰・相互再帰はここで排除される。
- 辺は**全ての構文上のユーザー call** から収集する：非選択枝、未到達関数、fold 本体を含む。
- 循環時は `E-CYCLE-CALL`（phase `call-graph`）。`E-CYCLE-*` は分類プレフィックスで、v1 の具体コードはこれ一つ。

# rank

DAG なら実装はトポロジカルランク `rank : F -> Nat` を構築する。

```text
f -> g ならば rank(g) < rank(f)
```

呼出し先のない関数を 0、その他を `1 + max(rank(callee))` とする。循環がある場合は rank を生成せず、実行可能プログラムを受理しない。rank は [停止性の証明](/guarantees/termination-proof.md) の外側の帰納に使う。

# 循環診断

- 循環を持つ強連結成分ごとに一件。
- 成分内の辺の call-name span が最小のものを主 span とし、関数名の関連情報は ASCII 辞書順。
- cycle error があっても typecheck と entry は実行する（name error の場合と異なる）。

例：fold 内から現在関数を呼ぶ → `E-CYCLE-CALL`。

[^lptl-design]: LLM向け純粋・全域言語：設計方針 v1
