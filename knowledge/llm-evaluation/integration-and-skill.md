---
type: Operating Principle
title: LLM 統合と Skill
description: LLM は候補生成・修復器であって信頼実行主体ではなく、受理判断はコンパイラ・codec・評価器・資源 profile・隠しテストに属する。SKILL.md は仕様から生成・照合しハッシュとトークン数を固定する。
tags: [lptl, llm, skill, trust]
status: draft
generated: { by: claude-code/2026-10-06, at: 2026-10-06T16:00:00Z }
sources:
  - id: lptl-design
    resource: ../../spec/lptl-v1/LPTL_design_v1.md
    title: LLM向け純粋・全域言語：設計方針 v1（§12.1、§12.2、§12.6）
    last_modified: 2026-10-01T00:00:00Z
---

# 運用原則

LLM は候補生成・修復器であって、信頼実行主体ではない。受理判断はコンパイラ、codec、評価器、資源プロファイル、隠しテスト、性質検査に属する。[^lptl-design]

```text
LLM（提案） → compile / compile_ast（静的受理） → decode_input（入力） → run（実行・資源） → 隠しテスト（タスク評価）
```

各段は別の検査責務・別の結果型を持つ（[API 分離](../api/api-separation.md)）。

# Skill（SKILL.md）

- 仕様から生成・照合し、ハッシュとトークン数を固定する。`skill_hash` は成果物 hash と再現 record に入る（[ハッシュ](../api/hashes-and-identity.md)）。
- v1 Skill は Option に一般 payload 消去がないことを明記し、`uncons` や `match_option` を使わせない。
- **含めるもの**：最小文法、型、組込み規則、`let`・`fold`・`Pair`・`cons`／`reverse` の例、禁止事項、出力形式、主要診断コード。
- **含めないもの**：最終評価の解法・近傍例・手書き例外規則。

# 高保証カーネルとしての採用判断

- 第一用途の受理・実行契約を、第二用途の成功率のために緩めない。
- 初期の代表 workload は、現行コアで表せる集計、条件付きリスト抽出、有限構造の変換・等値・Option 状態伝達。Option 一般 payload 消去、I/O、一般再帰を要する用途へ成功保証を拡張しない。
- G0 で fixture の型・入力長・深さ・整数規模・出力規模を記録し、G2／profile 凍結で正準化・診断・shadow accounting・出力展開を含む費用を測定する。論理カウンタと物理時間・ヒープを別報告する。
- 実用採用の閾値は対象環境と実測に基づき別に判断し、恣意的な性能目標を設定しない。

[^lptl-design]: LLM向け純粋・全域言語：設計方針 v1
