---
type: Proof Strategy
title: 停止性の証明構造
description: LPTL の停止性は単一の仕事量測度ではなく、関数 rank 帰納・式構造帰納・fold のリスト長帰納・組込み全域性の入れ子で示し、燃料付き評価の存在と単調性で実装適合に接続する。
tags: [lptl, termination, proof, totality]
status: draft
generated: { by: claude-code/2026-10-06, at: 2026-10-06T16:00:00Z }
sources:
  - id: lptl-design
    resource: ../../spec/lptl-v1/LPTL_design_v1.md
    title: LLM向け純粋・全域言語：設計方針 v1（§8.1、§8.2）
    last_modified: 2026-10-01T00:00:00Z
---

# 中心定理

entry 型が `T_in -> T_out` の整形式プログラム `P` と有効入力 `i:T_in` に対し、一意の `v:T_out` が存在して `P(i) ⇓ v`。[^lptl-design]（[憲章](../overview/charter.md)）

# 入れ子の帰納

曖昧な単一の「残余式仕事量」測度に依存させず、次の入れ子で証明する。

1. **関数ランク帰納**：[呼出しグラフ](../language/call-graph.md) の rank について帰納する。関数 `f` からのユーザー関数呼出しは必ずより小さい rank へ進む。
2. **式構造帰納**：固定した関数本体・環境の各式について構造帰納する。`let` は束縛式と本体の有限構文へ、strict call は有限個の引数と呼出し先へ還元される。
3. **リスト長帰納**：`fold` は入力リスト長について帰納する。各反復後、未処理要素数は一つ減る。
4. **組込み全域性**：算術、構造演算、構造的等値は数学的整数・有限木に対して全域である。

fold 本体内の call も現在関数からの辺なので、呼出し先は厳密に低い rank を持つ。現在関数の直接・間接呼出しは DAG 条件が拒否する。低 rank 関数の停止性を仮定した式構造帰納の中で、fold ケースをリスト長帰納で示す。累積値が増大しても反復対象の入力リストは変更しない。

# 実装適合への接続

燃料付き評価 `eval_fuel(P,input,n)` を定義し、停止性から存在を、さらに燃料単調性を示す。

```text
∃n,v. eval_fuel(P,input,n) = Done(v)

eval_fuel(P,input,n)=Done(v) ∧ m>=n
  ⇒ eval_fuel(P,input,m)=Done(v)
```

# 設計判断の要点

- 全域性は「言語から一般再帰を除き、反復を有限リスト上の `fold` に限る」ことで構文的に保証される。
- 決定性は純粋性と固定評価順から来る。
- 数学的停止は、物理ホストでのタイムアウトや資源不足が起こらないことを意味しない（[資源モデル](../resources/resource-model.md)）。

[^lptl-design]: LLM向け純粋・全域言語：設計方針 v1
