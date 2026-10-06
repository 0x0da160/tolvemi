---
type: Resource Profile
title: parse Admission
description: parse-admission-v1 は AST node 数を物理確保数ではなく前順の論理 Admission イベント列で数え、Surface と AST の正常入力で同じ列・node 数・深さになるようにする安全計数契約である。
tags: [lptl, resources, parser, ast]
status: draft
generated: { by: claude-code/2026-10-06, at: 2026-10-06T16:00:00Z }
sources:
  - id: lptl-design
    resource: ../../spec/lptl-v1/LPTL_design_v1.md
    title: LLM向け純粋・全域言語：設計方針 v1（§18.1b）
    last_modified: 2026-10-01T00:00:00Z
---

# 契約

AST node 数は次の規範的 Admission の累積数とする。Admission は前順に一 node ずつ発行し、イベント直前に該当する全ての次値を同時に検査する。超過時は [パイプライン](../diagnostics/pipeline.md) の優先順位で一件だけ cutoff し、当該イベントと後続イベントを発行しない。正常入力では完成 AST の node 数に一致する。[^lptl-design]

| 構文上の対象 | Surface での Admission 時点 | 同時に検査する量 |
|---|---|---|
| program | lex と lexical-limits 完了後、最初の宣言試行より前（空 program にも一回） | AST 数 |
| fn／entry | 対応 keyword を認識した時、子を読む前 | AST 数、fn は関数数 |
| param | params 位置で合法 IDENT を認識した時 | AST 数 |
| 型構成子 | Int／Bool／Unit／List／Option／Pair を認識した時 | AST 数、型構文深さ |
| 各式構成子 | 合法な先頭を認識し構成子を決めた時、子を読む前 | AST 数、式深さ、let／fold はネスト深さ |

# 規則

- IDENT 式は一 token 先読みで call か var を決め、一度だけ Admission する。
- 合法な先頭を認識できない位置（type 位置の `Foo`、expr 位置の `fn` 等）では Admission せず parse error。
- 先頭が合法で後続が不正でも、既に発行した親 Admission は取り消さない。例：Admission 済み some の子 unit が budget を超える不完全構文は、閉じ括弧欠落より先に AST-NODES cutoff。
- fold lambda、名前、文字列、配列、括弧には追加 Admission を発行しない。
- 失敗した宣言の回復時は深さ context をトップレベルに戻すが、累積 AST 数と関数数は戻さない。先読み・再検査・物理 node の作成破棄・共有・cache は計数しない。
- 同期で飛ばした token は新しい宣言試行が始まるまで計数しない。
- Surface の cutoff 主 span は対象先頭 token（program は source 開始のゼロ幅）。

# AST API での適用

transport 検査を全て通過した後、物理 AST 全体を作る前に program → declarations 入力順の前順 Admission を発行する。子の順は fn で params → return_type → body、param で type、型は element または left→right、式は schema の子 field 順。param は tag がないが一 node。AST cutoff 主 span は対象 object 全体。Surface の不正構文にだけある失敗試行を AST API へ合成しない。

[^lptl-design]: LLM向け純粋・全域言語：設計方針 v1
