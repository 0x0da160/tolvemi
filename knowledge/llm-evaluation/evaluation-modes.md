---
type: Experiment Design
title: 評価モードと比較
description: LLM 評価の5モード（Surface・AST・Render・Repair・Spec）と、v1/v1-no-let など介入ごとに報告できる効果を限定した必須比較・研究 arm の一覧。
tags: [lptl, llm, evaluation, ablation]
status: draft
generated: { by: claude-code/2026-10-06, at: 2026-10-06T16:00:00Z }
sources:
  - id: lptl-design
    resource: ../../spec/lptl-v1/LPTL_design_v1.md
    title: LLM向け純粋・全域言語：設計方針 v1（§12.3、§12.4、§20.2）
    last_modified: 2026-10-01T00:00:00Z
---

# 評価モード

モードは出力・入力条件の名称であり、それだけで因果要因を分離した証拠ではない。[^lptl-design]

| モード | 入出力 | 評価する対象と限界 |
|---|---|---|
| Surface | LLM が LPTL source を出力 | 要求理解から表面構文・型・意味構成までの総合成功 |
| AST | LLM が JSON AST を出力 | 要求理解と AST 生成の総合成功。制約付き／制約なしを別 arm |
| Render | 正解の未型検査 AST を入力し LLM が source を出力 | 構文構造の保持と表記生成。解法生成能力は測らない |
| Repair | 可視診断に基づく局所差分または再生成 | 固定初期候補・診断条件からの修復効果 |
| Spec | 要求から形式仕様と実装を出力 | 要求理解・仕様化の別評価。主 Success@B へ混ぜない |

Render は episode 単位の構文 AST 一致率を別報告する。モデル生成 AST からの Render は連結 arm として別報告し、deterministic formatter は対照であって LLM Render の成績に混ぜない。

# 必須比較

全 arm で仕様・モデル版・温度・seed 割付・候補選択・可視ツール・input／execution 条件を事前登録する。

| 比較 | 主な介入 | 報告できる効果 |
|---|---|---|
| v1／v1-no-let | let の有無 | 表記・共有評価・資源差を含む総合効果（純粋な表記効果とは呼ばない） |
| Surface／AST（双方制約なし） | 表記・prompt・長さ | 表記パッケージの差 |
| AST 制約なし／制約付き | schema 制約生成 | 制約付き生成の総合効果 |
| Surface／制約付き AST | 表記と制約生成の同時介入 | 運用パッケージの総合差のみ |
| Render | 正解 AST が既知 | 構文保持・表記生成 |
| 同意味論・別表記 | 表記を変更 | 固定条件下の表記効果 |
| 診断なし／文章のみ／コードのみ／span＋制約 | 可視診断 | 同じ失敗候補からの修復効果 |
| Skill あり／なし | Skill の提示 | Skill 内容と増分 context 費用を含む総合効果 |
| 通常 Python／制限 Python／LPTL | 言語・制限・tooling | 同一問題の総合差（Python の物理時間を LPTL の参照 step と同一視しない） |
| リスト構築組込みあり／なし | cons、concat、reverse を一体的に除く | 研究 arm `v1-no-cons-concat-reverse` |

# 規則

- アブレーションは研究 arm の契約であり、出荷する v1 言語コアを変更しない。未提示 arm を実装済みと扱わない。
- 比較課題は各 arm で解けることを、モデル結果と独立した参照解で事前確認する（参照解はモデルへ渡さない）。表現できない課題は事前に分離し件数・理由を公開する。失敗結果を見て後から除外しない。
- Option 一般 payload 消去を要する課題は v1 最終タスクに含めない。
- 実験のコア対照は v1／`v1-no-let`。診断・profile 差だけの比較を言語意味論の改善実験と呼ばない。

[^lptl-design]: LLM向け純粋・全域言語：設計方針 v1
