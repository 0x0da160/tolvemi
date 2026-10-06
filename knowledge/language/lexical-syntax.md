---
type: Language Specification
title: 字句規則
description: LPTL の字句は ASCII のみで、符号を含む INT を単一トークンとし、12x のような数値境界違反や -0・先頭ゼロを拒否する。
tags: [lptl, lexer, syntax]
status: draft
generated: { by: claude-code/2026-10-06, at: 2026-10-06T16:00:00Z }
sources:
  - id: lptl-design
    resource: ../../spec/lptl-v1/LPTL_design_v1.md
    title: LLM向け純粋・全域言語：設計方針 v1（§4 冒頭、§4.2、§18.1）
    last_modified: 2026-10-01T00:00:00Z
---

# ソース境界

compile API は任意の `source_bytes` を受け取り、次の順で検査する。[^lptl-design]

1. source bytes 上限（超過は `CompileResult::Rejected(E-LIMIT-STATIC-SOURCE-BYTES)`。UTF-8 は検査しない）
2. UTF-8 妥当性（不正は `SourceBoundaryFailure(InvalidSourceEncoding)`）
3. UTF-8 検査に成功した列だけを lexer に渡す

# トークン

```text
IDENT ::= [A-Za-z_][A-Za-z0-9_]*
INT   ::= 0 | -?[1-9][0-9]*
```

- `INT` は先行する `-` を含む**単一の字句トークン**。`-` は独立トークンではないため `1-2`、`- 2`、`--2` は字句不正。`sub(1,-2)`、`f(-2)` は受理。
- 最大一致。ただし整数直後に IDENT 開始文字が続く列（例 `12x`）は分割せず `E-LEX-INVALID-NUMERIC-BOUNDARY`。
- `-0`、`+1`、先頭ゼロ付き非零整数、指数表記、桁区切り、16進表記を拒否。
- 予約語は EBNF 中の全固定語。lexer は予約語を IDENT として返さない。予約語を関数名・変数名・型名に置くと parser が `E-PARSE-EXPECTED-IDENT`。

# 空白・コメント・文字集合

- コメントを除く受理文字は ASCII のみ。非コメント部の非 ASCII は `E-LEX-NON-ASCII`。UTF-8 BOM も拒否。
- 空白は ASCII space、tab、CR、LF のみ。改行は空白であり宣言終端ではない。
- コメントは `//` から次の CR、LF、EOF の直前までの行コメントのみ。コメント内は有効 UTF-8 を許す。ブロックコメントはない。
- Unicode 識別子、文字列リテラル、Unicode 正規化、エスケープ構文は対象外。

# トークン数の数え方

EOF とコメント・空白はトークン数に含めない。予約語、識別子、整数、句読点をそれぞれ一トークンとする。トークン数（上限 131,072）と整数リテラル桁数（上限 4,096、符号除外）は lexical-limits で検査し、同じ token の正規形・境界違反を桁上限より先に判定する。巨大な列を BigInt に変換しない。詳細は [static profile](/resources/static-profile.md)。

# 予約語一覧

AST schema の識別子定義が除外する語（33語）：

```text
fn entry Int Bool Unit List Option Pair true false unit list some none pair
let in if fold add sub mul neg lt le eq mod fst snd cons concat reverse length
```

`uncons` は予約語ではなく、同名の合法ユーザー関数を定義・呼出しできる（組込みの安全リスト分解は提供しない）。

[^lptl-design]: LLM向け純粋・全域言語：設計方針 v1
