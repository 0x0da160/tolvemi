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
| `E-SUM-*`、`E-MATCH-*` | v1.4 の直和型と `match`（name phase） |
| `E-AST-*` | AST transport |
| `W-UNUSED-FUNCTION` | 未到達トップレベル関数 |

# Schema

| コード | phase | 意味 |
|---|---|---|
| `E-LEX-INVALID-NUMERIC-BOUNDARY` | lex | `12x` のような整数直後の識別子文字 |
| `E-LEX-INVALID-ESCAPE`、`E-LEX-UNTERMINATED-STRING`、`E-LEX-INVALID-CHAR-LITERAL`、`E-LEX-CONTROL-CHAR-IN-LITERAL` | lex | v1.2 の文字・文字列リテラルの不正（[v1.2 差分仕様](../../spec/lptl-v1.2/LPTL_v1.2_delta.md) §6a） |
| `E-PARSE-STRING-TYPE` | parse | 型に `List<Char>` と書いた（`String` と書く） |
| `E-LEX-NON-ASCII` | lex | 非コメント部の非 ASCII |
| `E-LEX-UNEXPECTED-CHARACTER` | lex | トークンを開始できない ASCII 文字（演算子 `+`、`-`、`*`、`/` など）。v1.8：`/` には `div(a, b)` を示す修復ヒント |
| `E-PARSE-EXPECTED-PATTERN` | parse | v1.4：`match` の枝の先頭が pattern でない |
| `E-SUM-DUPLICATE-CTOR` | name | v1.4：構築子の名前が重複している |
| `E-SUM-UNKNOWN-CTOR` | name | v1.4：知らない構築子（修復ヒントで近い名前） |
| `E-SUM-CTOR-ARITY` | name | v1.4：構築・pattern の中身の数が宣言と違う |
| `E-SUM-NAME-CONFLICT` | name | v1.4：構築子と同じ名前の関数・変数・型 |
| `E-MATCH-MISSING` | name | v1.4：`match` に足りない場合がある（修復ヒントで足りない枝） |
| `E-MATCH-DUPLICATE` | name | v1.4：同じ場合の枝が二つある |
| `E-MATCH-UNREACHABLE` | name | v1.4：`_` の後の枝、または全部の場合を書いた後の `_` |
| `E-MATCH-MIXED` | name | v1.4：一つの `match` に違う型の pattern が混ざっている |
| `E-TYPE-MATCH-SCRUTINEE`、`E-TYPE-MATCH-BRANCH` | typecheck | `match_option`／`match_result`／`match` の対象の型が違う、枝の型が違う |
| `E-PARSE-EXPECTED-LAMBDA` | parse | v1.5：`map`・`filter`・`any`・`all`・`find`・`sort_by` の第 2 引数が一つの binder のラムダ `\|x\| e` でない（関数名だけ、ラムダの頭がない式、binder が二つ、第 2 引数がない。修復ヒント付き） |
| `E-TYPE-HOF-LIST` | typecheck | v1.5：`map` などの第 1 引数がリストでない |
| `E-TYPE-HOF-BODY` | typecheck | v1.5：ラムダの本体の型が違う（`filter`・`any`・`all`・`find` で Bool でない、`sort_by` で Int でない） |
| `E-TYPE-LOOP-MAX` | typecheck | v1.6：`loop` の第 2 引数（上限）が Int でない |
| `E-TYPE-LOOP-BODY` | typecheck | v1.6：`loop` の本体が `Option<S>`（S は init の型）でない。`loop` の第 3 引数がラムダでないときは `E-PARSE-EXPECTED-LAMBDA` |
| `E-PARSE-UNEXPECTED-TOKEN` | parse | 完成した式の後に fn/entry/EOF 以外 |
| `E-PARSE-EXPECTED-TYPE` | parse | `none[Foo]` など閉じた型文法外 |
| `E-PARSE-EXPECTED-IDENT` | parse | 予約語を名前位置に置いた |
| `E-PARSE-RECOVERY-LIMIT` | parse | recovery 8回の後に更に error |
| `E-PARSE-REC-ENTRY` | parse | v1.7：`rec entry f`（`rec` は関数の宣言にだけ付ける。修復ヒント：`rec` を消す） |
| `E-NAME-UNKNOWN-FUNCTION` | name | 未定義の関数名 |
| `E-ENTRY-UNKNOWN` | name | entry 名が未知 |
| `E-ENTRY-MISSING` | entry | entry 宣言なし |
| `E-ENTRY-DUPLICATE` | entry | entry 宣言が複数 |
| `E-ENTRY-ARITY` | entry | entry 関数の引数が一つでない |
| `E-CYCLE-CALL` | call-graph | 呼出し循環（v1.7：`rec fn` の印のない関数を含む循環。修復ヒント：循環にある関数に `rec` を付ける） |
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

各コードの出る文脈は [static profile](../resources/static-profile.md)、[strict JSON](../api/strict-json.md)、[AST codec](../api/ast-codec.md)、[回帰テスト](../conformance/regression-tests.md) を参照。

[^lptl-design]: LLM向け純粋・全域言語：設計方針 v1
[^verification-report]: LPTL v1 統一版：突き合わせ確認報告
