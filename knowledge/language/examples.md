---
type: Code Examples
title: プログラム例
description: 設計書に載る LPTL v1 の例（偶数の合計、正の値の順序保存抽出）と、v1 で表せない Option payload 消去の例。
tags: [lptl, examples]
status: draft
generated: { by: claude-code/2026-10-06, at: 2026-10-06T16:00:00Z }
sources:
  - id: lptl-design
    resource: ../../spec/lptl-v1/LPTL_design_v1.md
    title: LLM向け純粋・全域言語：設計方針 v1（§13、§19.1）
    last_modified: 2026-10-01T00:00:00Z
---

# Examples

## 偶数の合計

```text
fn sum_even(xs: List<Int>) -> Int =
  fold(xs, 0, |acc, x|
    let r = mod(x, 2) in
    if(eq(r, some(0)), add(acc, x), acc))
entry sum_even
```

正の定数除数 `2` に対して `mod` は常に `some(r)` を返す。`r` を未知 payload として取り出さず `some(0)` と比較しているため、v1 で表現できる。[^lptl-design]

## 正の値だけを順序保存で抽出

```text
fn positive_values(xs: List<Int>) -> List<Int> =
  let reversed = fold(xs, list[Int](), |acc, x|
    if(lt(0, x), cons(x, acc), acc)) in
  reverse(reversed)
entry positive_values
```

`fold` と `cons` で逆順に構築し、`reverse` で入力順へ戻す定石。全操作は有限リストに対し全域。

## v1 で表せない要求

```text
// mod(a,b) が some(r) のとき r+1、none のとき 0
```

`Option<Int>` の一般 payload `r` を束縛する `match_option` がないため書けない（[Option の境界](/language/option-boundary.md)、[将来拡張](/future/option-elimination.md)）。

## AST JSON 形式の例

恒等関数を [AST codec](/api/ast-codec.md) で表したもの：

```json
{"codec":"ast_codec_v1","declarations":[{"tag":"fn","name":"identity","params":[{"name":"x","type":{"tag":"int"}}],"return_type":{"tag":"int"},"body":{"tag":"var","name":"x"}},{"tag":"entry","name":"identity"}]}
```

# 書き方の要点（設計書の規則からの帰結）

- 演算子はなく、`add(a, b)`、`lt(0, x)` のように全て前置 call で書く。
- 空リストも `list[Int]()` と型を明示する。`none` も `none[Int]` と書く。
- 再帰の代わりに `fold` を使う。関数呼出しは DAG（自己呼出し不可）。
- `let` と `fold` の binder は外側の名前と被せない。
- 負の整数は `-2` を一トークンで書き、`- 2` や `1-2` は不正。

[^lptl-design]: LLM向け純粋・全域言語：設計方針 v1
