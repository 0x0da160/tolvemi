---
type: Language Specification
title: 型と値
description: LPTL v1 の型は Int・Bool・Unit・List<T>・Option<T>・Pair<A,B> の6種で、値は循環・参照・関数を持たない有限木である。
tags: [lptl, types, values]
status: draft
generated: { by: claude-code/2026-10-06, at: 2026-10-06T16:00:00Z }
sources:
  - id: lptl-design
    resource: ../../spec/lptl-v1/LPTL_design_v1.md
    title: LLM向け純粋・全域言語：設計方針 v1（§3.1、§3.2）
    last_modified: 2026-10-01T00:00:00Z
---

# Schema

```text
T, A, B ::= Int | Bool | Unit
    | List<T>
    | Option<T>
    | Pair<A, B>
```

| 型 | 値 | 備考 |
|---|---|---|
| `Int` | 整数 | 数学的任意精度整数 |
| `Bool` | `true`、`false` | |
| `Unit` | `unit` | 唯一の値 |
| `List<T>` | `list[T](v, ...)` | 有限個の `T` 値からなる順序付き同種リスト |
| `Option<T>` | `some(v)`、`none[T]` | 一般 payload の取り出しは不可（[Option の境界](option-boundary.md)） |
| `Pair<A,B>` | `pair(v, w)` | 二成分は独立した型 |

# 規則

- **型等価性は構文的等価性。** サブタイピングや暗黙変換はない。[^lptl-design]
- **v1 の全型は構造的等値可能**（`eq` が使える）。ただし将来導入される型が自動的に等値可能になることはなく、型ごとに明示する。
- **値は有限木としての数学的値。** 実装は共有を持つ不変 DAG 表現を使ってよいが、観測可能な意味は有限木の展開で定義する。
- 循環値、参照値、関数値、未初期化値は存在しない。
- 値の文法：`v ::= 整数 | true | false | unit | list[T](v, ...) | some(v) | none[T] | pair(v, v)`

意味論上の木展開量と物理割当量の区別は [資源モデル](../resources/resource-model.md)、JSON 表現は [値 JSON codec](../api/value-json-codec.md) を参照。

# v1.2 の追加：文字と文字列

[v1.2 差分仕様](../../spec/lptl-v1.2/LPTL_v1.2_delta.md) で `Char`（Unicode のスカラー値）と `String` を加えた。`String` は
`List<Char>` の唯一の綴りで、ソースに `List<Char>` とは書けない。値は `'a'`、`"text"`（文字のリスト）。
値 JSON では文字は `{"tag":"char","value":"<番号>"}`、plain JSON では文字列は JSON の文字列。


# v1.4 の追加：Result と直和型

[v1.4 差分仕様](../../spec/lptl-v1.4/LPTL_v1.4_delta.md) で型 `Result<T, E>`（値は `ok(v)` か `err(e)`）を加えた。式では `ok<T, E>(x)`、`err<T, E>(x)` と
型引数を二つとも書く。値 JSON は `{"tag":"ok","value":V}`、`{"tag":"err","value":V}`、plain JSON は `{"ok": v}`、`{"err": e}`。

ユーザー定義の直和型 `type Shape = Circle(Int) | Rect(Int, Int) | Empty` は、variant が n 個（n ≥ 2）なら
`Result<P1, Result<P2, ... Result<Pn-1, Pn>>>` の名前である（Pk は k 番目の中身の型。中身なしは `Unit`、一つはその型、
複数は右に入れ子の `Pair`。n = 1 なら P1）。型の等価性は展開後の構造で決まり、名前は表示と plain JSON に使う。
値 JSON は展開後の形、plain JSON は `{"Rect": [2, 3]}`、`{"Empty": []}`（variant 名を key に、中身を配列に）。
再帰する型は作れない（型名は使う前に宣言する）。

# v1.9 の追加：辞書 Dict

型 `Dict<K, V>`（K は任意の型）を加えた。値は鍵が相異なる `(鍵, 値)` の列で、挿入順を保つ（Python の dict と同じ）。
空の辞書は `dict<K, V>()`（型引数を二つとも書く）。`List<Pair<K, V>>` とは別の型で、型検査の後に
`List<Pair<K, V>>` へ書き換えてから検証済み部品に渡す。値 JSON は `List<Pair<K, V>>` と同じ、plain JSON は
`[key, value]` の配列の配列（`[["a", 1], ["b", 2]]`）。入力に同じ鍵が二度あれば `E-INPUT-DICT-DUPLICATE-KEY`。
`eq` は辞書を挿入順も含めて比べる。詳細は [v1.9 差分仕様](../../spec/lptl-v1.9/LPTL_v1.9_delta.md)。
v1.13：`tlvm exec` の entry の入力は `Dict<String, String>` と `Dict<String, Int>` も使える。標準入力の行（`鍵<TAB>値`）を
plain JSON の `[["鍵", "値"], ...]` にして同じ経路で読む（[v1.13 差分仕様](../../spec/lptl-v1.13/LPTL_v1.13_delta.md)）。
v1.14：自分自身を項に含む直和型（再帰する型）は、実行では整数の列 `List<Int>` として扱う（型の区別は、型ごとの印を付けた写しを検査して行う）。値は構築子の番号、そのあとに
項ごとの `[長さ] ++ 中身` が並ぶ（`Leaf` は `[0]`、`Node(Leaf, 3, Leaf)` は `[1, 1, 0, 1, 3, 1, 0]`）。項の型は Int、Bool、
再帰する型だけ。異なる再帰する型どうしは型検査で区別され、混ぜると拒否される。型エラーの文面は型の名前（`Tree`）で出る。詳細は
[v1.14 差分仕様](../../spec/lptl-v1.14/LPTL_v1.14_delta.md)。

# v1.10 の追加：型引数（総称）

関数と型の宣言は型引数（大文字で始まる名前）を取れる：`fn first<T>(xs: List<T>) -> Option<T>`、`type Box<T> = { value: T, n: Int }`、
`type Tree<T> = Leaf | Node(T, Int)`。型引数は宣言の中の型を書く位置すべてで使え、型引数は型引数を取らない。総称の型の使用
`Box<Int>` は、宣言の展開後の構造の型引数を置き換えたものの別名（型は構造的なまま）。再帰する型は今までどおり作れない。
entry の入出力にも使え、plain JSON・値 JSON は展開後の構造と同じ。値に型引数の情報は残らない（単相化してから実行する）。
詳細は [v1.10 差分仕様](../../spec/lptl-v1.10/LPTL_v1.10_delta.md)。

[^lptl-design]: LLM向け純粋・全域言語：設計方針 v1
