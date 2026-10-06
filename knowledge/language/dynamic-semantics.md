---
type: Language Specification
title: 動的意味論
description: LPTL の評価は純粋・決定的・左から右の call-by-value で、if は選択枝だけ、let は束縛式を一度だけ、fold はリスト・初期値・各反復本体の順に評価する。
tags: [lptl, semantics, evaluation]
status: draft
generated: { by: claude-code/2026-10-06, at: 2026-10-06T16:00:00Z }
sources:
  - id: lptl-design
    resource: ../../spec/lptl-v1/LPTL_design_v1.md
    title: LLM向け純粋・全域言語：設計方針 v1（§7）
    last_modified: 2026-10-01T00:00:00Z
---

# 評価順序

評価は純粋・決定的・左から右の call-by-value である。[^lptl-design]

- **strict call**（組込み・ユーザー関数）：全引数を左から右へ評価後に組込みまたは関数本体を評価する。
- **`if`**：条件を評価し、選択された枝のみを評価する。
- **`let`**：束縛式を一度評価してから本体を評価する。
- **`fold`**：リスト式、初期値、各反復本体の順に評価する。

# let

`let x = e1 in e2` は `e1` をちょうど一度評価して値 `v` を得た後、`x=v` を環境に追加して `e2` を評価する。非再帰・不変・局所であり、代入、共有可変セル、関数再帰を導入しない。

# if と fold

```text
if(true, t, f)  -> t
if(false, t, f) -> f

fold(list[T](), init, body) = init
fold(list[T](x1, ..., xn), init, body)
  = body(...body(body(init, x1), x2)..., xn)
```

各 fold ステップでは現在累積値を `acc`、現在要素を `item` として `body` を評価する。fold は左畳み込みで、入力リストは反復中に変更されない。

組込みの意味は [組込み関数](/language/builtins.md)、停止性は [停止性の証明構造](/guarantees/termination-proof.md)、参照コストは [execution profile](/resources/execution-profile.md) を参照。

[^lptl-design]: LLM向け純粋・全域言語：設計方針 v1
