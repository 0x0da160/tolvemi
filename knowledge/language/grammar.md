---
type: Language Specification
title: 文法と宣言終端
description: LPTL の表面文法（EBNF）と、完成した式の直後の fn・entry・EOF だけを宣言終端とする規則（v1.7 の rec fn を含む）。演算子構文はなく全てが前置形式である。
tags: [lptl, grammar, ebnf, parser]
status: draft
generated: { by: claude-code/2026-10-06, at: 2026-10-06T16:00:00Z }
sources:
  - id: lptl-design
    resource: ../../spec/lptl-v1/LPTL_design_v1.md
    title: LLM向け純粋・全域言語：設計方針 v1（§4.1）
    last_modified: 2026-10-01T00:00:00Z
---

# Schema

```ebnf
program      ::= { top_decl } EOF
top_decl     ::= function_def | entry_def

function_def ::= "fn" IDENT "(" [ params ] ")" "->" type "=" expr
entry_def    ::= "entry" IDENT

params       ::= param { "," param }
param        ::= IDENT ":" type

type         ::= "Int" | "Bool" | "Unit"
               | "List" "<" type ">"
               | "Option" "<" type ">"
               | "Pair" "<" type "," type ">"

expr         ::= INT | "true" | "false" | "unit" | IDENT
               | "list" "[" type "]" "(" [ arguments ] ")"
               | "some" "(" expr ")"
               | "none" "[" type "]"
               | "pair" "(" expr "," expr ")"
               | builtin "(" [ arguments ] ")"
               | "let" IDENT "=" expr "in" expr
               | "if" "(" expr "," expr "," expr ")"
               | "fold" "(" expr "," expr "," lambda ")"
               | IDENT "(" [ arguments ] ")"

builtin      ::= "add" | "sub" | "mul" | "neg"
               | "lt" | "le" | "eq" | "mod"
               | "fst" | "snd"
               | "cons" | "concat" | "reverse" | "length"

lambda       ::= "|" IDENT "," IDENT "|" expr
arguments    ::= expr { "," expr }
```

[^lptl-design]

# 構文上の要点

- `if`、`fold`、`let` は**特殊形式**。`builtin` とユーザー関数呼出しは **strict call**。
- `some`、`pair`、`list`、`none`、`if`、`fold` は専用構文。固定位置の欠落・過剰要素は **parse error** であり、通常の組込み call の arity error と混同しない。
- `lambda` は `fold` の第3引数にしか現れない。自由ラムダや第一級関数ではない。
- `none[T]` の `T` は閉じた `type` 非終端記号で parse する。`none[Foo]` は `E-PARSE-EXPECTED-TYPE`。
- IDENT 式は一 token 先読みで、次が `(` なら call、そうでなければ var。

# 宣言終端

`fn` と `entry` は `expr` を開始できない予約トークンである。

- function_def は完全な一つの expr を読み、開いた構文構造を全て閉じた後、次トークンが `fn`、`entry`、EOF のいずれかなら終了する。
- その他が続けば `E-PARSE-UNEXPECTED-TOKEN`（例：`fn f(x: Int) -> Int = x 1 entry f`）。
- 未完の式の途中の `fn`／`entry` は正常終端ではなく parse error。
- entry_def も IDENT の直後に同じ終端集合を要求する。

# Examples

改行なしの宣言列を受理する（formatter は宣言ごとに改行する）。

```text
fn f(x: Int) -> Int = x fn g(y: Int) -> Int = y entry f
```

parse error 時の回復規則は [診断件数と recovery](../diagnostics/limits-and-recovery.md)、正準出力は [正準フォーマット](canonical-formatting.md)。


# v1.4 の追加：Result、直和型、match

```ebnf
type      ::= ... | "Result" "<" type "," type ">" | IDENT
expr      ::= ... | ("ok" | "err") "<" type "," type ">" "(" expr ")"
            | "match_result" "(" expr "," "|" IDENT "|" expr "," "|" IDENT "|" expr ")"
            | CTOR | CTOR "(" expr ("," expr)* ")"
            | "match" expr "{" arm ("," arm)* ","? "}"
top_decl  ::= ... | "type" IDENT "=" variant ("|" variant)*
variant   ::= CTOR | CTOR "(" type ("," type)* ")"
arm       ::= pattern "=>" expr
pattern   ::= CTOR | CTOR "(" bind ("," bind)* ")" | "ok" "(" bind ")" | "err" "(" bind ")"
            | "some" "(" bind ")" | "none" | "_"
bind      ::= IDENT | "_"
```

- `Result`、`ok`／`err`、`match_result` は検証済み部品の構文にある。直和型と `match` は検証されていない接着部分
  （`crates/tlvm/src/sums.rs`）が `ok`／`err` の入れ子と `match_result`／`match_option`、`fst`／`snd` の `let` に
  書き換えてから検証済み部品に渡す。
- `match` の対象の位置では `Name {` をレコードの構築として読まない（`match p { ... }` の `{` は枝の始まり）。
- 詳細は [v1.4 差分仕様](../../spec/lptl-v1.4/LPTL_v1.4_delta.md)。


# v1.5 の追加：map などの特殊形式

```ebnf
expr      ::= ... | hof "(" expr "," "|" IDENT "|" expr ")"
hof       ::= "map" | "filter" | "any" | "all" | "find" | "sort_by"
```

- 6 語は文脈キーワードで、直後が `(` のときだけ特殊形式。それ以外の位置では変数の参照（`<` が続いても組み込みにはならない）。
- 第 2 引数は一つの binder のラムダ `|x| e` に限る。関数名だけ（`map(xs, f)`）、ラムダの頭がない式、binder が二つ
  （`|a, b|`）、第 2 引数がない（`map(xs)`）は `E-PARSE-EXPECTED-LAMBDA`（修復ヒント付き）。
- 検証済み部品の構文にはなく、型検査の後に `crates/tlvm/src/hof.rs` が `fold` などに書き換えてから渡す。
  詳細は [v1.5 差分仕様](../../spec/lptl-v1.5/LPTL_v1.5_delta.md)。

# v1.6 の追加：loop の特殊形式

```ebnf
expr      ::= ... | "loop" "(" expr "," expr "," "|" IDENT "|" expr ")"
```

- `loop` は文脈キーワードで、直後が `(` のときだけ特殊形式。それ以外の位置では変数の参照。
- 第 3 引数は一つの binder のラムダ `|s| e` に限る。関数名だけ、ラムダの頭がない式、binder が二つ、第 3 引数がない
  （`loop(init, max)`）は `E-PARSE-EXPECTED-LAMBDA`（修復ヒント付き）。
- 検証済み部品の構文にはなく、型検査の後に `crates/tlvm/src/hof.rs` が `fold` などに書き換えてから渡す。詳細は [v1.6 差分仕様](../../spec/lptl-v1.6/LPTL_v1.6_delta.md)。

# v1.7 の追加：rec fn

```ebnf
top_decl  ::= ... | "rec" function_def
```

- `rec` は文脈キーワードで、宣言の先頭で直後が `fn` のときだけ印。それ以外の位置では普通の名前（変数・引数・束縛・field・関数の名前に使える）。
- 宣言の終端の規則は、次の token が `fn`、`entry`、`type`（宣言の先頭）、EOF に加えて、直後が `fn` か `entry` の `rec` でもよい。
- `rec entry f` は `E-PARSE-REC-ENTRY`（修復ヒント付き：`rec` を消す）。
- 検証済み部品の構文にはなく、接着部分が印を外したテキストと関数ごとの印の列を渡す。詳細は [v1.7 差分仕様](../../spec/lptl-v1.7/LPTL_v1.7_delta.md)。

[^lptl-design]: LLM向け純粋・全域言語：設計方針 v1
