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

`Option<Int>` の一般 payload `r` を束縛する `match_option` がないため書けない（[Option の境界](option-boundary.md)、[将来拡張](../future/option-elimination.md)）。

## AST JSON 形式の例

恒等関数を [AST codec](../api/ast-codec.md) で表したもの：

```json
{"codec":"ast_codec_v1","declarations":[{"tag":"fn","name":"identity","params":[{"name":"x","type":{"tag":"int"}}],"return_type":{"tag":"int"},"body":{"tag":"var","name":"x"}},{"tag":"entry","name":"identity"}]}
```

# 書き方の要点（設計書の規則からの帰結）

- 演算子はなく、`add(a, b)`、`lt(0, x)` のように全て前置 call で書く。
- 空リストも `list[Int]()` と型を明示する。`none` も `none[Int]` と書く。
- 再帰の代わりに `fold` を使う。関数呼出しは DAG（自己呼出し不可）。
- `let` と `fold` の binder は外側の名前と被せない。
- 負の整数は `-2` を一トークンで書き、`- 2` や `1-2` は不正。


# v1.5 の例

```text
// 50 点以上の名前を、点の高い順に（同点は入力の順）
fn top(xs: List<Pair<String, Int>>) -> List<String> =
  map(sort_by(filter(xs, |p| le(50, snd(p))), |p| neg(snd(p))), |p| fst(p))
entry top
```

# v1.6 の例

```text
// start から倍にして 1000 以上になった最初の値（64 歩で届かなければ none）
fn first_power(start: Int) -> Option<Int> = loop(start, 64, |n| if(lt(n, 1000), some(mul(n, 2)), none<Int>()))
entry first_power
```

入力 1 で `some(1024)`、0 で `none`（0 は倍にしても 0 のまま）。

# v1.7 の例

```text
// ユークリッドの互除法
rec fn gcd(a: Int, b: Int) -> Int = match mod(a, b) { some(r) => if(eq(r, 0), b, gcd(b, r)), none => a }
fn solve(p: Pair<Int, Int>) -> Int = gcd(fst(p), snd(p))
entry solve

// 相互再帰（循環にある関数すべてに rec を付ける）
rec fn even(n: Int) -> Bool = if(eq(n, 0), true, odd(sub(n, 1)))
rec fn odd(n: Int) -> Bool = if(eq(n, 0), false, even(sub(n, 1)))
```

入力 `[12, 18]` で 6。`tlvm check` は `"terminates":false` と報告する。

# v1.9 の例

```text
// 語の出現回数（初めて現れた順）
fn count(ws: List<String>) -> List<Pair<String, Int>> =
  dict_entries(fold(ws, dict<String, Int>(), |d, w| dict_put(d, w, add(match_option(dict_get(d, w), 0, |n| n), 1))))
entry count
```

入力 `["to", "be", "or", "to", "be"]` で `[["to", 2], ["be", 2], ["or", 1]]`。

# v1.10 の例

```text
// 一つの補助関数を二つの型で使う
fn dedup<T>(xs: List<T>) -> List<T> = reverse(fold(xs, list<T>(), |seen, x| if(contains(seen, x), seen, cons(x, seen))))
fn solve(p: Pair<List<Int>, List<String>>) -> Pair<List<Int>, List<String>> = pair(dedup(fst(p)), dedup(snd(p)))
entry solve
```

入力 `[[1, 2, 1], ["a", "a"]]` で `[[1, 2], ["a"]]`。

# v1.11 の例

```text
// examples/lib/stats.tlvm（entry のないライブラリ）
type Summary = { count: Int, total: Int, low: Option<Int>, high: Option<Int> }
fn first<T>(xs: List<T>) -> Option<T> = match uncons(xs) { some(p) => some(fst(p)), none => none<T>() }
fn summarize(xs: List<Int>) -> Summary =
  let sorted = sort(xs) in
  Summary { count: length(xs), total: fold(xs, 0, |acc, x| add(acc, x)), low: first(sorted), high: first(reverse(sorted)) }

// examples/stats.tlvm
import "lib/stats.tlvm"
fn stats(xs: List<Int>) -> Summary = summarize(xs)
entry stats
```

入力 `[3, -1, 7, 2]` で `{"count": 4, "total": 11, "low": -1, "high": 7}`。

[^lptl-design]: LLM向け純粋・全域言語：設計方針 v1
