---
type: Language Specification
title: Option の境界
description: v1 の Option<T> は部分性を値へ写す構成子で、生成・保存・定数との比較はできるが、一般 payload を束縛して取り出す消去構文はない。
tags: [lptl, option, expressiveness, limitation]
status: draft
generated: { by: claude-code/2026-10-06, at: 2026-10-06T16:00:00Z }
sources:
  - id: lptl-design
    resource: ../../spec/lptl-v1/LPTL_design_v1.md
    title: LLM向け純粋・全域言語：設計方針 v1（§3.3、§12.2、§13.3、§17）
    last_modified: 2026-10-01T00:00:00Z
---

# できること

v1 の `Option<T>` は、部分性を言語エラーではなく値へ写すための構成子である。[^lptl-design]

- **生成**：`some(e)`、`none[T]`、`mod`（除数が正でなければ `none[Int]`）。
- **保存・伝達**：`let`、`pair`、`list` 等で保持できる。
- **比較**：`eq` により、`none[T]` または有限個の既知 payload を持つ `some(c)` と比較できる。

# できないこと

**一般 payload を束縛して取り出す消去構文はない。** 従って v1 は次を対象にしない。

- 任意の `some(x)` から未知の `x` を抽出する処理
- `uncons` の結果から先頭要素を取得する処理
- 動的除数の `mod` 結果を一般の整数計算へ渡す処理

例：「`mod(a,b)` が `some(r)` のとき `r+1`、`none` のとき `0`」は v1 では書けない。

# 実務上の帰結

- 定数除数なら比較で回避できる：`eq(mod(x, 2), some(0))` は偶奇判定として書ける（[例](/language/examples.md)）。
- Skill（LLM 向け説明）は、Option に一般 payload 消去がないことを明記し、`uncons` や `match_option` を使わせない（[LLM 統合と Skill](/llm-evaluation/integration-and-skill.md)）。
- Option 消去が必要な課題は v1 最終タスクに含めず、[将来の独立拡張](/future/option-elimination.md) の実験へ分離する。
- この境界を隠さないことで、実装・Verus 証明・Skill・ベンチマーク・LLM の期待能力が同じ言語を対象にする。

[^lptl-design]: LLM向け純粋・全域言語：設計方針 v1
