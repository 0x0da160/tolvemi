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

`E-ARITY-USER` と `E-ARITY-BUILTIN` は正式な具体コード。その他の型／name／lex／parse の具体コード、message template、repair 生成規則は版付き diagnostic registry に列挙して G0 で照合する。registry は [registry-v1.json](registry-v1.json) に作成した（2026-10-15）。各コードの severity、phase、message template、repair 規則、発生箇所を持つ。ソースと fixture への照合は `crates/tlvm/tests/diagnostic_registry.rs` が行う。下表は設計書本文に現れるコードの抽出であり、registry の代用ではない。[^lptl-design] 突き合わせ報告は本文の診断コードを52種類と数えている。[^verification-report]

2026-10-14 に、処理系のソースで発生する具体コードのうち、上の表に完全な形で載っていなかった 57 件を末尾の表に加えた。message template と repair 生成規則は、2026-10-15 に registry-v1.json で固定した（上の注意を見る）。

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
| `E-REC-FIELD-TYPE` | name | v1.14：再帰する型の構築子の中身が `Int`、`Bool`、再帰する型そのもの以外（[v1.14 差分仕様](../../spec/lptl-v1.14/LPTL_v1.14_delta.md) §2） |
| `E-REC-TYPE-PARAM` | name | v1.14：再帰する型に型引数を付けた宣言（総称の再帰する型は未対応） |
| `E-TYPE-MATCH-SCRUTINEE`、`E-TYPE-MATCH-BRANCH` | typecheck | `match_option`／`match_result`／`match` の対象の型が違う、枝の型が違う |
| `E-PARSE-EXPECTED-LAMBDA` | parse | v1.5：`map`・`filter`・`any`・`all`・`find`・`sort_by` の第 2 引数が一つの binder のラムダ `\|x\| e` でない（関数名だけ、ラムダの頭がない式、binder が二つ、第 2 引数がない。修復ヒント付き） |
| `E-TYPE-HOF-LIST` | typecheck | v1.5：`map` などの第 1 引数がリストでない |
| `E-TYPE-HOF-BODY` | typecheck | v1.5：ラムダの本体の型が違う（`filter`・`any`・`all`・`find` で Bool でない、`sort_by` で Int でない） |
| `E-TYPE-LOOP-MAX` | typecheck | v1.6：`loop` の第 2 引数（上限）が Int でない |
| `E-TYPE-DICT-ARG` | typecheck | v1.9：`dict_get` などの第 1 引数が辞書でない（`List<Pair<K, V>>` なら修復ヒントで `dict_from`） |
| `E-TYPE-DICT-FROM` | typecheck | v1.9：`dict_from` の引数が `List<Pair<K, V>>` でない |
| `E-TYPE-LOOP-BODY` | typecheck | v1.6：`loop` の本体が `Option<S>`（S は init の型）でない。`loop` の第 3 引数がラムダでないときは `E-PARSE-EXPECTED-LAMBDA` |
| `E-TYPE-GENERIC-UNKNOWN-PARAM`、`-DUPLICATE-PARAM`、`-PARAM-CONFLICT`、`-UNUSED-PARAM` | name | v1.10：宣言されていない型引数、同じ名前の型引数、型の名前と同じ型引数、型の宣言で使われない型引数 |
| `E-TYPE-GENERIC-ARITY` | name／typecheck | v1.10：型・呼び出し・構築の型引数の数が違う |
| `E-TYPE-GENERIC-INFER` | typecheck（中身のない構築子は name） | v1.10：型引数を推論できない（修復ヒントで `f<Int>(...)`・`Leaf<Int>()`） |
| `E-TYPE-GENERIC-MISMATCH` | typecheck | v1.10：同じ型引数に引数によって違う型が当たった |
| `E-TYPE-GENERIC-INFINITE` | typecheck | v1.10：多相再帰（呼ぶたびに型引数が大きくなる） |
| `E-PARSE-UNEXPECTED-TOKEN` | parse | 完成した式の後に fn/entry/EOF 以外 |
| `E-PARSE-EXPECTED-TYPE` | parse | `none[Foo]` など閉じた型文法外 |
| `E-PARSE-EXPECTED-IDENT` | parse | 予約語を名前位置に置いた |
| `E-PARSE-RECOVERY-LIMIT` | parse | recovery 8回の後に更に error |
| `E-PARSE-REC-ENTRY` | parse | v1.7：`rec entry f`（`rec` は関数の宣言にだけ付ける。修復ヒント：`rec` を消す） |
| `E-IMPORT-AFTER-DECL` | parse | v1.11：宣言の後の `import`（修復ヒント：ファイルの先頭へ移す） |
| `E-IMPORT-PATH` | import | v1.11：import のパスの形（絶対パス、`.tlvm` 以外、根のファイルのディレクトリより上への `..` など） |
| `E-IMPORT-NOT-FOUND` | import | v1.11：import したファイルが無い |
| `E-IMPORT-CYCLE` | import | v1.11：import の循環（actual に `a.tlvm -> b.tlvm -> a.tlvm`） |
| `E-IMPORT-CONFLICT` | import | v1.11：二つのファイルが同じ名前を定義（actual に両方のファイル） |
| `E-IMPORT-UNSUPPORTED` | import | v1.11：source の文字列だけを受け取る API に import |
| `E-PKG-MANIFEST` | import | v1.16：`tlvm.json` が JSON でない、大きすぎる、未知の鍵、名前・版の形が違う（[v1.16 差分仕様](../../spec/lptl-v1.16/LPTL_v1.16_delta.md) §5） |
| `E-PKG-PATH` | import | v1.16：依存の `path` が不正（絶対パス、根の外、根や自分自身を指す、区切りの誤り） |
| `E-PKG-NOT-FOUND` | import | v1.16：依存のディレクトリに `tlvm.json` がない |
| `E-PKG-NAME` | import | v1.16：依存の `tlvm.json` の `name` が宣言した依存の名前と違う |
| `E-PKG-VERSION` | import | v1.16：版の固定と依存の版が違う（依存に版がない場合も含む） |
| `E-PKG-UNKNOWN` | import | v1.16：`@名前/…` の名前が、そのファイルのパッケージの依存として宣言されていない |
| `E-NAME-UNKNOWN-FUNCTION` | name | 未定義の関数名 |
| `E-ENTRY-UNKNOWN` | name | entry 名が未知 |
| `E-ENTRY-MISSING` | entry | entry 宣言なし |
| `E-ENTRY-DUPLICATE` | entry | entry 宣言が複数 |
| `E-ENTRY-ARITY` | entry | entry 関数の引数が一つでない |
| `E-ENTRY-GENERIC` | entry | v1.10：entry の関数が総称 |
| `E-CYCLE-CALL` | call-graph | 呼出し循環（v1.7：`rec fn` の印のない関数を含む循環。修復ヒント：循環にある関数に `rec` を付ける） |
| `E-ARITY-USER` | typecheck | ユーザー関数の引数数不一致 |
| `E-ARITY-BUILTIN` | typecheck | 組込みの引数数不一致 |
| `E-TYPE-IF-BRANCH` | typecheck | if の両分岐の型不一致 |
| `E-TYPE-FST-ARG` | typecheck | fst の引数が Pair でない |
| `E-LIMIT-STATIC-SOURCE-BYTES` | source-boundary | source bytes 上限（v1.11：import したファイルの合計は phase import） |
| `E-LIMIT-STATIC-IMPORT-FILES` | import | v1.11：import で読むファイルの数（根を含めて 64）の上限 |
| `E-LIMIT-STATIC-TOKENS`、`-INTEGER-DIGITS` | lexical-limits | token 数、整数桁数 |
| `E-LIMIT-STATIC-FUNCTIONS`、`-AST-NODES`、`-TYPE-DEPTH`、`-EXPR-DEPTH`、`-LET-DEPTH`、`-FOLD-DEPTH` | structural-limits | 構造上限 |
| `E-LIMIT-STATIC-SEMANTIC-TYPE-DEPTH`、`-SEMANTIC-WORK` | semantic-limits | 推論型深さ、型検査仕事量 |
| `E-LIMIT-STATIC-GENERIC-INSTANCES` | semantic-limits | v1.10：単相化の複製が 256 個、型引数の大きさが型の node 256 個を超えた |
| `E-LIMIT-STATIC-REWRITTEN-BYTES` | semantic-limits | 書換え後のプログラムの bytes が 4,194,304 を超えた（型検査を通ったプログラムだけ） |
| `E-DIAG-LIMIT`／`W-DIAG-LIMIT` | — | 診断件数上限 |
| `W-UNUSED-FUNCTION` | warnings | 未到達関数 |
| `E-INPUT-JSON-SYNTAX`、`-STRING-SCALAR`、`-DUPLICATE-KEY` | input-parse | 入力 JSON transport |
| `E-INPUT-FIELD-TYPE`、`-MISSING-FIELD`、`-TAG`、`-UNKNOWN-FIELD`、`-INTEGER` | input-decode | 入力値 |
| `E-INPUT-DICT-DUPLICATE-KEY` | input-decode | v1.9：入力の辞書に同じ鍵が二度ある（plain JSON・値 JSON とも）。v1.13：`tlvm exec` の標準入力の行にも（[v1.13 差分仕様](../../spec/lptl-v1.13/LPTL_v1.13_delta.md)） |
| `E-LIMIT-INPUT-JSON-BYTES` | input-boundary | 入力 bytes 上限 |
| `E-LIMIT-INPUT-JSON-DEPTH` | input-parse | 入力 JSON 深さ |
| `E-LIMIT-INPUT-VALUE-DEPTH`、`-VALUE-NODES`、`-INTEGER-DIGITS` | input-decode | 入力値上限 |
| `E-AST-JSON-SYNTAX`、`-STRING-SCALAR`、`-DUPLICATE-KEY` | ast-parse | AST JSON transport |
| `E-AST-CODEC`、`-TAG`、`-MISSING-FIELD`、`-UNKNOWN-FIELD`、`-FIELD-TYPE`、`-IDENTIFIER`、`-INTEGER` | ast-schema | AST node |
| `E-AST-LIMIT-BYTES`、`-JSON-DEPTH`、`-INTEGER-DIGITS` | ast-boundary 等 | AST transport 上限 |

各コードの出る文脈は [static profile](../resources/static-profile.md)、[strict JSON](../api/strict-json.md)、[AST codec](../api/ast-codec.md)、[回帰テスト](../conformance/regression-tests.md) を参照。

# 追加の一覧（2026-10-14）

上の表に完全な形で載っていないコードを、処理系のソースから拾った。省略形の行に含まれるコードも、ここでは完全な形で挙げる。phase はソースが設定する値、発生箇所はソースのファイル名（`crates/tlvm/src/` の下）、意味は `diagnostics.rs` の説明文を短く言い換えたもの。repair の形は書かない。

| コード | phase | 発生箇所 | 意味 |
|---|---|---|---|
| `E-AST-DUPLICATE-KEY` | ast-parse | `ast_codec.rs` | AST JSON に重複キーがある |
| `E-AST-FIELD-TYPE` | ast-schema | `ast_codec.rs` | JSON の型が期待と違う |
| `E-AST-IDENTIFIER` | ast-schema | `ast_codec.rs`、`softnames.rs` | 識別子が不正（型引数の名は大文字で始める） |
| `E-AST-INTEGER` | ast-schema | `ast_codec.rs` | 整数が正規形でない |
| `E-AST-LIMIT-INTEGER-DIGITS` | ast-schema | `ast_codec.rs` | 整数の桁数が上限を超える |
| `E-AST-LIMIT-JSON-DEPTH` | ast-parse | `ast_codec.rs` | AST JSON の構造深さが上限を超える |
| `E-AST-LITERAL` | ast-schema | `ast_codec.rs` | 文字・文字列リテラルに書けない文字がある |
| `E-AST-MISSING-FIELD` | ast-schema | `ast_codec.rs` | 必須キーがない |
| `E-AST-STRING-SCALAR` | ast-parse | `ast_codec.rs` | AST JSON の文字列に不正な Unicode scalar がある |
| `E-AST-STRING-TYPE` | ast-schema | `ast_codec.rs` | `List<Char>` は `{"tag":"string"}` と書く |
| `E-AST-TAG` | ast-schema | `ast_codec.rs` | この位置で許されない tag |
| `E-AST-UNKNOWN-FIELD` | ast-schema | `ast_codec.rs` | 未知のキーがある |
| `E-INPUT-CHAR` | input-decode | `values.rs` | 入力の文字が Unicode scalar value でない |
| `E-INPUT-DUPLICATE-KEY` | input-parse | `plain.rs`、`values.rs` | 入力 JSON に重複キーがある |
| `E-INPUT-INTEGER` | input-decode | `plain.rs`、`values.rs` | 入力整数が正規形でない |
| `E-INPUT-MISSING-FIELD` | input-decode | `plain.rs`、`values.rs` | 入力値に必須キーがない |
| `E-INPUT-STRING-SCALAR` | input-parse | `plain.rs`、`values.rs` | 入力 JSON の文字列に不正な Unicode scalar がある |
| `E-INPUT-TAG` | input-decode | `plain.rs`、`values.rs` | 入力値の tag が期待型と一致しない |
| `E-INPUT-UNKNOWN-FIELD` | input-decode | `plain.rs`、`values.rs` | 入力値に未知のキーがある |
| `E-INTERNAL-SOURCE-BOUNDARY` | source-boundary | `embed.rs` | `&str` は常に UTF-8 なので起きないはずの内部の不変条件の破れ |
| `E-INTERNAL-VERIFIED-MISMATCH` | internal | `api.rs`、`values.rs` | 検証済み部品と診断用の検査器の判定が食い違った（処理系の不具合） |
| `E-LEX-INVALID-INTEGER` | lex | `lexer.rs` | 整数リテラルが正規形でない |
| `E-LIMIT-INPUT-INTEGER-DIGITS` | input-decode | `plain.rs`、`values.rs` | 入力整数の桁数が上限を超える |
| `E-LIMIT-INPUT-VALUE-NODES` | input-decode | `plain.rs`、`values.rs` | 入力値の node 数が上限を超える |
| `E-LIMIT-STATIC-AST-NODES` | structural-limits | `parser.rs` | AST node 数が上限を超える |
| `E-LIMIT-STATIC-EXPR-DEPTH` | structural-limits、semantic-limits | `parser.rs`、`api.rs` | 式の深さが上限を超える（`api.rs` は書換え後の式） |
| `E-LIMIT-STATIC-FOLD-DEPTH` | structural-limits | `parser.rs` | fold のネスト深さが上限を超える |
| `E-LIMIT-STATIC-INTEGER-DIGITS` | lexical-limits | `lexer.rs` | 整数リテラルの桁数が上限を超える |
| `E-LIMIT-STATIC-LET-DEPTH` | structural-limits | `parser.rs` | let のネスト深さが上限を超える |
| `E-LIMIT-STATIC-SEMANTIC-WORK` | semantic-limits | `checker.rs` | 型検査の仕事量が上限を超える |
| `E-LIMIT-STATIC-TYPE-DEPTH` | structural-limits | `parser.rs` | 型構文の深さが上限を超える |
| `E-NAME-DUPLICATE-BINDER` | name | `checker.rs` | fold の acc と item、または match の一つの枝の束縛が同じ名前 |
| `E-NAME-DUPLICATE-FUNCTION` | name | `checker.rs` | 同名のトップレベル関数が既にある |
| `E-NAME-DUPLICATE-PARAM` | name | `checker.rs` | 同名の引数が既にある |
| `E-NAME-SHADOW` | name | `checker.rs` | 外側の変数をシャドーする束縛 |
| `E-NAME-UNBOUND-VARIABLE` | name | `checker.rs` | 未束縛の変数 |
| `E-PARSE-EXPECTED-EXPR` | parse | `parser.rs` | 式がある位置に式がない |
| `E-PARSE-EXPECTED-TOKEN` | parse | `parser.rs` | 必要な区切り記号がない |
| `E-RECORD-BASE-REDUNDANT` | name | `records.rs` | すべての field を書いたので、`..base` で写す field がない |
| `E-RECORD-DUPLICATE-FIELD` | name | `records.rs` | 同じ field が二度書かれている |
| `E-RECORD-DUPLICATE-TYPE` | name | `records.rs`、`sums.rs`、`recursive.rs` | 同じ名前のレコード型が二度宣言されている |
| `E-RECORD-FIELD-CONFLICT` | name | `records.rs` | field 名が別のレコード型の field と重なる |
| `E-RECORD-MISSING-FIELD` | name | `records.rs` | レコードの構築に書かれていない field がある |
| `E-RECORD-UNKNOWN-FIELD` | name | `records.rs` | この名前の field はない |
| `E-RECORD-UNKNOWN-TYPE` | name | `records.rs`、`sums.rs` | レコード型が宣言されていない（型は使うより前に宣言する） |
| `E-TYPE-ARG` | typecheck | `checker.rs` | 引数の型が一致しない |
| `E-TYPE-EQ-OPERANDS` | typecheck | `checker.rs` | `eq` の両引数が同じ型でない |
| `E-TYPE-EXPECTED-LIST` | typecheck | `checker.rs` | List 型の値が必要な位置に別の型がある |
| `E-TYPE-FIELD-ACCESS` | typecheck | `checker.rs` | field を参照する式の型が、その field を持つレコード型でない |
| `E-TYPE-FOLD-BODY` | typecheck | `checker.rs` | fold 本体の型が初期値の型と一致しない |
| `E-TYPE-FOLD-LIST` | typecheck | `checker.rs` | fold の第 1 引数が List でない |
| `E-TYPE-GENERIC-DUPLICATE-PARAM` | name | `generics.rs` | 同じ名前の型引数が二度宣言されている |
| `E-TYPE-GENERIC-PARAM-CONFLICT` | name | `generics.rs` | 型引数の名前が宣言された型の名前と重なる |
| `E-TYPE-GENERIC-UNUSED-PARAM` | name | `generics.rs` | 型の宣言の型引数が field・variant のどこにも使われていない |
| `E-TYPE-IF-CONDITION` | typecheck | `checker.rs` | if の条件が Bool でない |
| `E-TYPE-LIST-ITEM` | typecheck | `checker.rs` | リスト要素の型が注釈と一致しない |
| `E-TYPE-RETURN` | typecheck | `checker.rs` | 関数本体の型が宣言した戻り型と一致しない |
| `E-TYPE-SND-ARG` | typecheck | `checker.rs` | snd の引数が Pair でない |

[^lptl-design]: LLM向け純粋・全域言語：設計方針 v1
[^verification-report]: LPTL v1 統一版：突き合わせ確認報告
