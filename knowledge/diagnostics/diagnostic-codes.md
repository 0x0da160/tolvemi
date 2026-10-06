---
type: Code Catalog
title: 診断コード一覧
description: LPTL v1 設計書に現れる具体的な診断コードと分類プレフィックスの一覧。完全な一覧と message template は G0 で固定する diagnostic registry に委ねられている。
tags: [lptl, diagnostics, error-codes]
status: draft
generated: { by: claude-code/2026-10-06, at: 2026-10-06T16:00:00Z }
sources:
  - id: lptl-design
    resource: ../../spec/lptl-v1/LPTL_design_v1.md
    title: LLM向け純粋・全域言語：設計方針 v1（§10.4、§18、§19.3、§20.1）
    last_modified: 2026-10-01T00:00:00Z
  - id: verification-report
    resource: ../../spec/lptl-v1/LPTL_v1_verification_report.md
    title: LPTL v1 統一版：突き合わせ確認報告
    last_modified: 2026-10-01T00:00:00Z
---

# 注意

`E-ARITY-USER` と `E-ARITY-BUILTIN` は正式な具体コード。その他の型／name／lex／parse の具体コード、message template、repair 生成規則は版付き diagnostic registry に列挙して G0 で照合する（registry は未作成）。下表は設計書本文に現れるコードの抽出であり、registry の代用ではない。[^lptl-design] 突き合わせ報告は本文の診断コードを52種類と数えている。[^verification-report]

# 分類プレフィックス

| プレフィックス | 対象 |
|---|---|
| `E-LEX-*` | 字句不正、数値境界、整数正規形 |
| `E-PARSE-*` | 構文不正、予約語位置、区切り不整合 |
| `E-NAME-*` | 未束縛変数、未知関数、重複束縛、シャドー |
| `E-ARITY-*` | ユーザー関数・組込みの引数数不一致 |
| `E-TYPE-*` | 型不一致、if、let、fold、組込み規則違反 |
| `E-CYCLE-CALL` | ユーザー関数呼出し循環（`E-CYCLE-*` の唯一の具体コード） |
| `E-ENTRY-*` | entry の未知名、欠落、重複、引数数不正 |
| `E-LIMIT-STATIC-*` | コンパイル静的上限超過 |
| `E-INPUT-*` | JSON 構文、重複キー、tag、キー集合、型、整数正規形 |
| `E-LIMIT-INPUT-*` | 入力境界上限超過 |
| `E-AST-*` | AST transport |
| `W-UNUSED-FUNCTION` | 未到達トップレベル関数 |

# Schema

| コード | phase | 意味 |
|---|---|---|
| `E-LEX-INVALID-NUMERIC-BOUNDARY` | lex | `12x` のような整数直後の識別子文字 |
| `E-LEX-NON-ASCII` | lex | 非コメント部の非 ASCII |
| `E-PARSE-UNEXPECTED-TOKEN` | parse | 完成した式の後に fn/entry/EOF 以外 |
| `E-PARSE-EXPECTED-TYPE` | parse | `none[Foo]` など閉じた型文法外 |
| `E-PARSE-EXPECTED-IDENT` | parse | 予約語を名前位置に置いた |
| `E-PARSE-RECOVERY-LIMIT` | parse | recovery 8回の後に更に error |
| `E-NAME-UNKNOWN-FUNCTION` | name | 未定義の関数名 |
| `E-ENTRY-UNKNOWN` | name | entry 名が未知 |
| `E-ENTRY-MISSING` | entry | entry 宣言なし |
| `E-ENTRY-DUPLICATE` | entry | entry 宣言が複数 |
| `E-ENTRY-ARITY` | entry | entry 関数の引数が一つでない |
| `E-CYCLE-CALL` | call-graph | 呼出し循環 |
| `E-ARITY-USER` | typecheck | ユーザー関数の引数数不一致 |
| `E-ARITY-BUILTIN` | typecheck | 組込みの引数数不一致 |
| `E-TYPE-IF-BRANCH` | typecheck | if の両分岐の型不一致 |
| `E-TYPE-FST-ARG` | typecheck | fst の引数が Pair でない |
| `E-LIMIT-STATIC-SOURCE-BYTES` | source-boundary | source bytes 上限 |
| `E-LIMIT-STATIC-TOKENS`、`-INTEGER-DIGITS` | lexical-limits | token 数、整数桁数 |
| `E-LIMIT-STATIC-FUNCTIONS`、`-AST-NODES`、`-TYPE-DEPTH`、`-EXPR-DEPTH`、`-LET-DEPTH`、`-FOLD-DEPTH` | structural-limits | 構造上限 |
| `E-LIMIT-STATIC-SEMANTIC-TYPE-DEPTH`、`-SEMANTIC-WORK` | semantic-limits | 推論型深さ、型検査仕事量 |
| `E-DIAG-LIMIT`／`W-DIAG-LIMIT` | — | 診断件数上限 |
| `W-UNUSED-FUNCTION` | warnings | 未到達関数 |
| `E-INPUT-JSON-SYNTAX`、`-STRING-SCALAR`、`-DUPLICATE-KEY` | input-parse | 入力 JSON transport |
| `E-INPUT-FIELD-TYPE`、`-MISSING-FIELD`、`-TAG`、`-UNKNOWN-FIELD`、`-INTEGER` | input-decode | 入力値 |
| `E-LIMIT-INPUT-JSON-BYTES` | input-boundary | 入力 bytes 上限 |
| `E-LIMIT-INPUT-JSON-DEPTH` | input-parse | 入力 JSON 深さ |
| `E-LIMIT-INPUT-VALUE-DEPTH`、`-VALUE-NODES`、`-INTEGER-DIGITS` | input-decode | 入力値上限 |
| `E-AST-JSON-SYNTAX`、`-STRING-SCALAR`、`-DUPLICATE-KEY` | ast-parse | AST JSON transport |
| `E-AST-CODEC`、`-TAG`、`-MISSING-FIELD`、`-UNKNOWN-FIELD`、`-FIELD-TYPE`、`-IDENTIFIER`、`-INTEGER` | ast-schema | AST node |
| `E-AST-LIMIT-BYTES`、`-JSON-DEPTH`、`-INTEGER-DIGITS` | ast-boundary 等 | AST transport 上限 |

各コードの出る文脈は [static profile](/resources/static-profile.md)、[strict JSON](/api/strict-json.md)、[AST codec](/api/ast-codec.md)、[回帰テスト](/conformance/regression-tests.md) を参照。

[^lptl-design]: LLM向け純粋・全域言語：設計方針 v1
[^verification-report]: LPTL v1 統一版：突き合わせ確認報告
