---
type: Language Specification
title: 文法と宣言終端
description: LPTL の表面文法（EBNF）と、完成した式の直後の fn・entry・EOF だけを宣言終端とする規則。演算子構文はなく全てが前置形式である。
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

[^lptl-design]: LLM向け純粋・全域言語：設計方針 v1
