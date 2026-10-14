---
type: Data Format
title: AST codec
description: ast_codec_v1 はプログラムの未型検査表面 AST を表す JSON transport で、node ごとに許可キー・必須キー・正準順を固定し、Surface と同じ共通静的検査を省略せずに適用する。
tags: [lptl, ast, json-schema, codec]
status: draft
resource: ../../spec/lptl-v1/ast_codec_v1.schema.json
generated: { by: claude-code/2026-10-06, at: 2026-10-06T16:00:00Z }
sources:
  - id: lptl-design
    resource: ../../spec/lptl-v1/LPTL_design_v1.md
    title: LLM向け純粋・全域言語：設計方針 v1（§19）
    last_modified: 2026-10-01T00:00:00Z
  - id: ast-schema
    resource: ../../spec/lptl-v1/ast_codec_v1.schema.json
    title: ast_codec_v1.schema.json（urn:lptl:ast-codec:v1、JSON Schema Draft 2020-12）
---

# 位置付け

- `ast_codec_v1` はプログラム AST 専用で、[値 JSON codec](value-json-codec.md) と混用しない。[^lptl-design]
- AST は**未型検査の表面 AST**。明示注釈を source と同じ位置にだけ持ち、内部型・推論結果・rank・symbol ID・source span・実行値・暗黙 default を入力できない。型・name・DAG の検査を省略しない。

# Schema

表の keys は許可集合・全て必須・正準出力順を同時に示す。どの object も余分なキーを拒否する。

| node | keys／fields |
|---|---|
| program | `codec`, `declarations`。codec は固定 string `ast_codec_v1`、declarations は fn／entry 配列 |
| fn | `tag`, `name`, `params`, `return_type`, `body`。任意：`rec`（boolean。省略は false。v1.7）、`type_params`（大文字で始まる名前の配列。省略は型引数なし。v1.10） |
| entry | `tag`, `name` |
| param | `name`, `type` |
| type int／bool／unit／char／string | `tag` |
| type list／option | `tag`, `element`（type） |
| type pair | `tag`, `left`, `right`（type） |
| type result | `tag`, `ok`, `err`（type。v1.4） |
| type dict | `tag`, `key`, `value`（type。v1.9） |
| type param | `tag`, `name`（型引数の名前。v1.10） |
| expr int | `tag`, `value`（正規十進 string） |
| expr char | `tag`, `value`（スカラー値の十進 string。v1.2） |
| expr string | `tag`, `value`（文字列の値。JSON 文字列の規則。v1.2） |
| expr bool | `tag`, `value`（JSON boolean） |
| expr unit | `tag` |
| expr var | `tag`, `name` |
| expr list | `tag`, `element_type`, `items`（expr 配列） |
| expr some | `tag`, `value`（expr） |
| expr none | `tag`, `element_type` |
| expr pair | `tag`, `left`, `right`（expr） |
| expr call | `tag`, `callee`（名前 string）, `args`（expr 配列）, `type_args`（type 配列。明示しない call は空配列。v1.10） |
| expr let | `tag`, `name`, `value`, `body`（expr） |
| expr if | `tag`, `condition`, `then`, `else`（expr） |
| expr fold | `tag`, `list`, `init`, `acc`, `item`, `body` |
| expr match_option | `tag`, `scrutinee`, `on_none`, `binder`, `on_some`（v1.1） |
| expr ok／err | `tag`, `ok_type`, `err_type`, `value`（type、type、expr。v1.4） |
| expr match_result | `tag`, `scrutinee`, `ok_binder`, `on_ok`, `err_binder`, `on_err`（v1.4） |
| expr map／filter／any／all／find／sort_by | `tag`, `list`, `binder`, `body`（v1.5） |
| expr loop | `tag`, `init`, `max`, `binder`, `body`（v1.6） |
| expr dict | `tag`, `key_type`, `value_type`（空の辞書。v1.9） |
| expr call の `type_args`（v1.10、この処理系の拡張） | 必ず出す型の配列。明示しない call は空配列。型引数を明示した構築子（`Leaf<Int>()`）は展開後の値の形で出す。レコード型・直和型の宣言は transport にないので、`tlvm ast` は展開したもの（構築子のための総称の関数を含む）を出す |

- `callee` は通常 builtin 名または合法ユーザー関数名。some／pair／if 等の専用構文を call node で代用しない。
- 識別子は decode 後の文字列全体が IDENT に一致すること（schema pattern `^[A-Za-z_][A-Za-z0-9_]*(?![\s\S])`）。変数・引数・束縛・関数名・entry 名・組込みでない callee・型引数の名前は、いずれも字句表の 68 語（予約語と文脈キーワード）をすべて除く。Surface は文脈キーワードを変数・引数・束縛に使えるが、AST では使えない（§4.2）。`tlvm ast` は出力の変数名を `<語>_kw` に付け替える（[字句の仕様](../language/lexical-syntax.md)）。整数は `^(0|-?[1-9][0-9]*)(?![\s\S])`。否定先読みで末尾 LF を許す処理系差を塞ぐ。`"x"` は `x` として受理、`"x\n"` は拒否。[^ast-schema]
- 同梱 schema 実体：22,699 bytes、SHA-256 `ff8ad602c3b5889acd8146a6b487aa81c0d93f88ed3e4680d9440da7e4085f4a`。

JSON Schema 単体では重複キー、bytes、深さ、UTF-8、不対 surrogate、整数桁上限、byte span、正準キー順、共通静的検査は保証されず、strict parser・コンパイラ・encoder が別途行う。validator のエラー順を規範的診断順に代用しない。

# transport 拒否の手順

1. JSON bytes 上限 → UTF-8
2. token stream 解析（構造深さを開始括弧で guard）
3. [strict JSON 契約](strict-json.md)（scalar → 重複キー）
4. root を program として object 検査。declarations と配列は入力順、子 field は表の key 順に再帰。全体で最初の一件だけ返す
5. 成功後、[parse Admission](../resources/parse-admission.md) を適用しながら表面 AST と byte span map を構築し、structural-limits 最終整合 → name → call-graph → typecheck → semantic-limits → entry → warnings

各 object の検査順：

| object 種別 | header 検査 |
|---|---|
| program | object → codec 存在 → string 型 → 固定値 |
| param | object であることだけ（tag を検査しない） |
| fn／entry／型／式 | object → tag 存在 → string 型 → 位置で許される tag 列挙 |

header の後は **必須キー → 余分キー → 全直接 field の浅い JSON 型 → field 内容**。複数欠落は表の key 順、複数余分は decoded scalar 辞書順で最初を選ぶ。

| 違反 | コード |
|---|---|
| codec | `E-AST-CODEC` |
| tag 欠落 / その他の欠落 | `E-AST-MISSING-FIELD` |
| tag 型・列挙 | `E-AST-TAG` |
| object でない／浅い型 | `E-AST-FIELD-TYPE` |
| 余分キー（param への tag 追加を含む） | `E-AST-UNKNOWN-FIELD` |
| 識別子・callee | `E-AST-IDENTIFIER` |
| 整数正規形 | `E-AST-INTEGER` |
| 上限 | `E-AST-LIMIT-BYTES`、`E-AST-LIMIT-JSON-DEPTH`、`E-AST-LIMIT-INTEGER-DIGITS` |

# schema 適合と静的受理の区別

| schema 適合する構造 | 共通検査での扱い |
|---|---|
| `declarations: []` | entry で `E-ENTRY-MISSING` |
| 通常 call の実引数不足・過剰 | typecheck で `E-ARITY-*` |
| 未定義の合法 callee 名 | name で `E-NAME-UNKNOWN-FUNCTION` |
| fold の `acc` と `item` が同名 | name で binder 重複 |
| `callee: "uncons"` | 組込みとして解決する（v1.1）。文脈キーワードなので、同名の関数は宣言できない |

# 正準化と往復

encoder は UTF-8、最小空白、表の key 順、配列順保持、不要 escape なし、末尾改行なし。

```text
decode_ast(encode_ast(A)) = A
parse(format(A)) = A
encode_ast(parse(format(A))) = encode_ast(A)
```

profile による失敗を含めない抽象関係であり、span・コメント・空白を除く構文 AST について主張する。

# Surface との公平性

Surface と AST は同じ型注釈、名前規則、DAG、組込み、entry、静的 AST／semantic 上限、input／execution profile を使う。AST 側で型推論追加・注釈補完・未知 field 無視・binder 自動改名・循環除去を行わない。transport 上限は表記固有として別に公開する。

[^lptl-design]: LLM向け純粋・全域言語：設計方針 v1
[^ast-schema]: ast_codec_v1.schema.json
