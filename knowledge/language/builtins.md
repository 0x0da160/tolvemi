---
type: Language Specification
title: 組込み関数
description: LPTL v1 の14個の組込み（算術・比較・構造的等値・剰余・Pair 射影・リスト操作）の型規則スキームと数学的意味。全て有限値に対して全域である。
tags: [lptl, builtins, semantics]
status: draft
generated: { by: claude-code/2026-10-06, at: 2026-10-06T16:00:00Z }
sources:
  - id: lptl-design
    resource: ../../spec/lptl-v1/LPTL_design_v1.md
    title: LLM向け純粋・全域言語：設計方針 v1（§6.2、§7.4）
    last_modified: 2026-10-01T00:00:00Z
---

# Schema

`A`、`B` は仕様記述のメタ変数であり、ユーザーが書ける型変数でも let 多相性でもない。各適用箇所で引数型から一意に具体型へインスタンス化される。[^lptl-design]

| 名前 | 型規則スキーム | 意味 |
|---|---|---|
| `add` | `Int × Int -> Int` | `a+b` |
| `sub` | `Int × Int -> Int` | `a-b` |
| `mul` | `Int × Int -> Int` | `a*b` |
| `neg` | `Int -> Int` | `-a` |
| `lt` | `Int × Int -> Bool` | `a < b` |
| `le` | `Int × Int -> Bool` | `a <= b` |
| `eq` | `A × A -> Bool` | 構造的等値 |
| `fst` | `Pair<A,B> -> A` | 第1成分 |
| `snd` | `Pair<A,B> -> B` | 第2成分 |
| `mod` | `Int × Int -> Option<Int>` | 正の除数に対する非負剰余 |
| `cons` | `A × List<A> -> List<A>` | 先頭追加 |
| `concat` | `List<A> × List<A> -> List<A>` | 連結 |
| `reverse` | `List<A> -> List<A>` | 逆順 |
| `length` | `List<A> -> Int` | 有限長 |

除算、`head`、`tail`、添字アクセスは部分関数なので存在しない。

# mod

```text
b > 0 なら mod(a,b) = some(r)
  ただし a = b*q + r、0 <= r < b を満たす一意の r
b <= 0 なら mod(a,b) = none[Int]
```

`mod(-3,2)=some(1)`、`mod(1,0)=none[Int]`。結果の payload は一般には取り出せない（[Option の境界](option-boundary.md)）。

# リスト操作

```text
cons(x, list[T](x1, ..., xn)) = list[T](x, x1, ..., xn)
concat(list[T](x1, ..., xm), list[T](y1, ..., yn))
  = list[T](x1, ..., xm, y1, ..., yn)
reverse(list[T](x1, ..., xn)) = list[T](xn, ..., x1)
length(list[T](x1, ..., xn)) = n
```

# eq

同型値に対する構造的等値。リスト・ペア・Option を左から右、浅い構造から深い構造の順に比較し、最初の不一致で `false`。等しい場合だけ全構造を走査する。実装は共有 pointer 一致による短絡・memoization をしてはならない（参照コストを変えるため。[execution profile](../resources/execution-profile.md)）。

[^lptl-design]: LLM向け純粋・全域言語：設計方針 v1
