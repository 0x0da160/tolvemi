---
type: Language Specification
title: 組込み関数
description: LPTL v1 の14個の組込み（算術・比較・構造的等値・剰余・Pair 射影・リスト操作）の型規則スキームと数学的意味（v1.1 以降の追加と v1.8 の除算 div を含む）。全て有限値に対して全域である。
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

`head`、`tail`、添字アクセスは部分関数なので存在しない。除算は v1.8 で `mod` と同じく `Option<Int>` を返す全域の `div` として加えた（下の節）。

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

# v1.2 の追加

| 名前 | 型規則 | 意味 |
|---|---|---|
| `code` | `Char -> Int` | 文字の番号 |
| `char` | `Int -> Option<Char>` | スカラー値なら `some`、そうでなければ `none` |
| `to_string` | `Int -> String` | 正準十進表記 |
| `parse_int` | `String -> Option<Int>` | 省略可能な `-` と 1 文字以上の数字なら `some` |

`String` は `List<Char>` なので、リストの組み込みがそのまま文字列に使える。詳細は
[v1.2 差分仕様](../../spec/lptl-v1.2/LPTL_v1.2_delta.md)。


# v1.5 の追加：関数を渡す組み込み

| 形 | 型 | 意味 |
|---|---|---|
| `map(xs, \|x\| e)` | `List<A> -> List<B>` | 各要素に e を当てた列（順序を保つ） |
| `filter(xs, \|x\| p)` | `List<A> -> List<A>` | p が true の要素だけ（順序を保つ） |
| `any(xs, \|x\| p)` | `List<A> -> Bool` | p が true の要素がある |
| `all(xs, \|x\| p)` | `List<A> -> Bool` | すべての要素で p が true（空なら true） |
| `find(xs, \|x\| p)` | `List<A> -> Option<A>` | p が true の最初の要素 |
| `sort_by(xs, \|x\| k)` | `List<A> -> List<A>` | k（Int）の昇順。k が等しい要素は元の順（安定） |

`fold` と同じ特殊形式で、`|x| e` は第一級の関数ではない。`String` も `List<Char>` として渡せる。型検査の後に
`fold`・`reverse`・`cons`・`if`・`match_option`・`let` の組み合わせへ書き換えてから検証済み部品に渡す
（`crates/tlvm/src/hof.rs`）。詳細は [v1.5 差分仕様](../../spec/lptl-v1.5/LPTL_v1.5_delta.md)。

# v1.6 の追加：上限つき反復

| 形 | 型 | 意味 |
|---|---|---|
| `loop(init, max, \|s\| e)` | `S, Int -> Option<S>` | s = init から始め、e（`Option<S>`）が `some(s2)` なら s2 で続け、`none` なら止まる。止まったときの状態を `some(s)` で返し、e を max 回評価しても止まらなければ `none<S>()` |

`|s| e` は `map` などと同じ局所の binder（第一級の関数ではない）。`max <= 0` なら本体を評価せず `none<S>()`。型検査の後に
`range(0, max)` 上の `fold` と `match_result`・`match_option` へ書き換えてから検証済み部品に渡す
（`crates/tlvm/src/hof.rs`）。詳細は [v1.6 差分仕様](../../spec/lptl-v1.6/LPTL_v1.6_delta.md)。

# v1.8 の追加：div

| 名前 | 型規則 | 意味 |
|---|---|---|
| `div` | `Int × Int -> Option<Int>` | 正の除数に対する床除算の商 |

```text
b > 0 なら div(a,b) = some(q)
  ただし a = b*q + r、0 <= r < b を満たす一意の q（r は mod(a,b) の値）
b <= 0 なら div(a,b) = none[Int]
```

`div(7,2)=some(3)`、`div(-7,2)=some(-4)`（`mod(-7,2)=some(1)`）、`div(1,0)=none[Int]`。`mod` と同じく検証済みの中核の
組込みで（spec の `Builtin::Div`、`apply_sound` の場合）、exec は信頼する多倍長整数の `div_pos`（num-integer の `div_floor`）
を使う。`div` は文脈キーワード（変数名などに使え、関数名には使えない）。詳細は [v1.8 差分仕様](../../spec/lptl-v1.8/LPTL_v1.8_delta.md)。

[^lptl-design]: LLM向け純粋・全域言語：設計方針 v1
