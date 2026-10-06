---
type: Naming Policy
title: Tolvemi の名称と表記
description: 正式名称 Tolvemi（トルベミ）、省略表記・CLI 名 tlvm、ソース拡張子 .tlvm の方針と、仕様内部の LPTL 識別子を一括置換しない規則。
tags: [tolvemi, naming, cli, branding]
status: draft
generated: { by: claude-code/2026-10-06, at: 2026-10-06T16:00:00Z }
sources:
  - id: tolvemi-name
    resource: ../../spec/Tolvemi_name_explanation_clean.md
    title: Tolvemi：名称・表記・設計思想
    last_modified: 2026-10-03T00:00:00Z
---

# 表記

| 用途 | 表記 |
|---|---|
| 言語名・ブランド名 | Tolvemi（先頭のみ大文字） |
| 日本語の読み | トルベミ（4拍。「トルヴェミ」へ自動変更しない） |
| 文書の初出 | Tolvemi（省略表記：tlvm） |
| CLI 実行ファイル名 | `tlvm` |
| ソース拡張子 | `.tlvm` |
| パッケージ名・ドメイン名 | 各配布先の利用可能性を確認して別途決定 |

短い紹介文：「Tolvemi（トルベミ）は、有限データ上の純粋・全域・決定的計算のための DSL です。公式省略表記は tlvm です。」[^tolvemi-name]

# 由来

total（全域性）と value（値）を着想源として響きを整えた造語。頭字語でも二語の連結でもなく、文字や音節に機能名を割り当てない。`tlvm` は `Tolvemi` から母音 o・e・i を除いた子音列で、これも頭字語ではない。省略表記の使用によって正式名称を TLVM に変更しない。

英語の発音案は tol-VEH-mee（3音節、第2音節に主アクセント、英 /tɒlˈvɛmi/、米 /tɑlˈvɛmi/）。利用者試験の結果ではない。

# 設計思想との対応

名称は「結果まで到達する値計算」を象徴する。全域性・純粋性・決定性・提案と受理の分離という設計思想は [LPTL 憲章](charter.md) と同じ。説明文「生成されたロジックを、契約の下で評価する。」は名称の頭字語展開ではない。

# CLI の表記例

`tlvm check example.tlvm`、`tlvm run example.tlvm` は表記例にすぎず、サブコマンド・引数・入出力・実装の存在を確定しない。

# 識別子の扱い

公開名称の決定と、仕様内部の固定識別子の変更は別の判断である。`LPTL-artifact-v1` などハッシュ domain・codec・契約を同定する文字列は一括置換しない（[識別子レジストリ](../references/identifier-registry.md)）。名称の採用は商標・ドメイン確保・先行名称との非類似性・記憶試験の合格を意味しない。「LLMに最適」「完全に形式検証済み」といった主張を名称から導かない。

[^tolvemi-name]: Tolvemi：名称・表記・設計思想
