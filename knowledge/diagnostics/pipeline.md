---
type: Pipeline Specification
title: 診断パイプライン
description: コンパイル検査は source-boundary・lex・lexical-limits・parse・structural-limits・name・call-graph・typecheck・semantic-limits・entry・warnings の順で、段階ごとに失敗後の継続・停止規則が決まっている。
tags: [lptl, diagnostics, pipeline, compiler]
status: draft
generated: { by: claude-code/2026-10-06, at: 2026-10-06T16:00:00Z }
sources:
  - id: lptl-design
    resource: ../../spec/lptl-v1/LPTL_design_v1.md
    title: LLM向け純粋・全域言語：設計方針 v1（§10.2）
    last_modified: 2026-10-01T00:00:00Z
---

# 段階

```text
source-boundary → lex → lexical-limits → parse → structural-limits
  → name → call-graph → typecheck → semantic-limits → entry → warnings
```

lexical-limits は lex と、structural-limits の guard は parse と、semantic-limits は typecheck と一体で実行する。矢印は検査責務の順序であり、巨大な中間物を全部作ってから測る意味ではない。契約識別子は `diagnostic-pipeline-v1`。[^lptl-design]

| 段階 | 検査 | 失敗後の規則 |
|---|---|---|
| source-boundary | source bytes 上限、続いて UTF-8 | bytes 超過は静的拒否、UTF-8 不正は境界失敗。以後停止 |
| lex | ASCII、トークン形式 | 最初の字句 error で停止。parse しない |
| lexical-limits | token 数と整数桁数 | 上限を超える token 確定時に cutoff。parse しない |
| parse | EBNF、宣言終端 | parse error のみなら bounded recovery。name 以後なし |
| structural-limits | 関数数、AST node 数、型・式・let・fold 深さ | guard 超過時点で parse／recovery を打切り、以後停止 |
| name | 全宣言・全式の名前と entry 参照 | error があれば call-graph 以後停止 |
| call-graph | 全関数の DAG | cycle error があっても typecheck と entry を実行 |
| typecheck | arity と型制約 | 通常の型 error なら entry まで継続 |
| semantic-limits | 推論型深さ・検査仕事量 | 超過時に typecheck を中断し、entry と warnings も停止 |
| entry | 構文個数と唯一の関数の arity | 不正なら到達性 warning なし |
| warnings | 唯一の有効 entry からの到達性 | W-UNUSED-FUNCTION |

# 競合と cutoff

- 競合時は source size → UTF-8 → 入力順の lex／parse の観測順。
- 既に生成した通常診断は保持する。cutoff は一件だけ発行し、未実施の後続診断は追加しない。未実行の検査を成功とは扱わない。
- 同じイベントで複数の structural 上限を超えたら、関数数 → AST 数 → 型深さ → 式深さ → let 深さ → fold 深さ の順で一つだけ選ぶ。
- structural guard は [parse Admission](/resources/parse-admission.md) イベントの直前に検査し、安全上限を超えた木を割り当てない。
- warnings は name 成功・唯一の arity=1 entry 有効・cutoff なしの場合に実行する。
- **Accepted は全必須 phase が完了し error が0件の場合だけ。**

# phase 名の対応

`E-CYCLE-CALL` は `call-graph`、通常 arity は `typecheck`、静的上限は対応する `source-boundary`／`lexical-limits`／`structural-limits`／`semantic-limits`。AST transport は `ast-boundary`、`ast-parse`、`ast-schema`、入力は `input-boundary`、`input-parse`、`input-decode`（[strict JSON](/api/strict-json.md)）。

[^lptl-design]: LLM向け純粋・全域言語：設計方針 v1
