---
type: Extension Proposal
title: Option 消去と安全リスト分解
description: match_option（局所 binder 特殊形式）と uncons を v1 コアに含めず、型規則・停止性・診断・codec・LLM 評価・証明義務を揃えた別バージョンとして一体で審査する拡張候補。
tags: [lptl, future, option, match-option, uncons]
status: draft
generated: { by: claude-code/2026-10-06, at: 2026-10-06T16:00:00Z }
sources:
  - id: lptl-design
    resource: ../../spec/lptl-v1/LPTL_design_v1.md
    title: LLM向け純粋・全域言語：設計方針 v1（§14、§19.6）
    last_modified: 2026-10-01T00:00:00Z
---

# 候補

次の機能は一体としてのみ検討する。[^lptl-design]

```text
match_option(e, on_none, |x| on_some)
uncons(xs) : Option<Pair<T, List<T>>>
```

- `match_option` は自由な第一級関数ではなく、`fold` と同様の局所 binder 特殊形式。
- 導入時には型規則、選択的評価順序、停止性、診断、codec、LLM 評価、Skill、証明義務を追加する。
- `option_fold` も v1 コア外。
- 現在 `uncons` は予約語ではなく、合法なユーザー関数名として扱われる。組込みとして導入する場合は予約語・名前互換性への影響も審査する。

この拡張で、[v1 の Option の境界](../language/option-boundary.md) にある「`mod(a,b)` が `some(r)` のとき `r+1`」のような課題が書けるようになる。

# 機能追加の条件

機能追加は次を満たす別バージョンとしてのみ許される。

1. 規範 `spec` の文法、型、評価、資源、診断を更新する。
2. 全域性、型安全性、決定性、実装適合の証明を更新する。
3. TCB と資源プロファイルへの影響を公開する。
4. 既存コアと混同しないタスク分布・消去実験で LLM 効果を測定する。

G0 は v1 と後続の Option 消去候補を混在させないことを要求する（[出荷ゲート](../overview/status-and-gates.md)）。

[^lptl-design]: LLM向け純粋・全域言語：設計方針 v1
