# LPTL v1.4 差分仕様：直和型と match

本書は [v1.3 差分仕様](../lptl-v1.3/LPTL_v1.3_delta.md) に対する差分である。ここに書かれていない事項は
v1.3 以前のとおりとする。汎用言語にするロードマップの 3 段目で、「いくつかの形のどれか」を表す値と、
失敗を値として返す `Result` を入れる。

状態：草案。処理系は本書どおりに実装済み。

## 1. 追加するもの

```text
Result<T, E>                            型：成功 ok(T) か失敗 err(E)
ok<T, E>(x)    err<T, E>(x)             Result の値（型引数は両方書く）
match_result(r, |v| on_ok, |e| on_err)  Result の分解

type Shape = Circle(Int) | Rect(Int, Int) | Empty     ユーザー定義の直和型
Circle(5)   Rect(2, 3)   Empty                         構築
match s { Circle(r) => ..., Rect(w, h) => ..., Empty => ... }   分解
```

`match` は直和型のほか、`Result`（`ok(v)`、`err(e)`）と `Option`（`some(v)`、`none`）にも使える。

## 2. 検証済みの中核（`verus/`）

- 型 `Result<T, E>`、値 `ok(v)`、`err(v)`。式 `ok<T, E>(x)`、`err<T, E>(x)`、`match_result(m, |x| a, |y| b)`。
- 型規則：`ok<T, E>(x)` は x : T のとき `Result<T, E>`（`err` は x : E）。`match_result` は m : `Result<T, E>`、
  x : T のもとで a : A、y : E のもとで b : A のとき A。
- 評価：`match_result` は m を評価し、ok なら a だけを、err なら b だけを評価する。
- 名前解決：二つの binder はそれぞれの枝でだけ見え、外側の可視変数をシャドーできない（同じ名前でもよい）。
- 字句：`Result`、`match_result` は予約語。`ok`、`err` は文脈キーワード（変数名などに使える。直後が `<` の
  ときだけ構築子）。
- 値 JSON：`{"tag":"ok","value":V}`、`{"tag":"err","value":V}`。plain JSON：`{"ok": v}`、`{"err": e}`。
- 証明：型安全性・停止性・決定性（v1 §11.2）、parser の健全性・完全性、formatter の AST 保存性、JSON の往復性を
  新しい形に広げた（`assume`・`admit` なし）。

## 3. ユーザー定義の直和型（検証されていない接着部分）

```text
decl    ::= ... | "type" IDENT "=" variant ("|" variant)*
variant ::= CTOR | CTOR "(" type ("," type)* ")"
expr    ::= ... | CTOR | CTOR "(" expr ("," expr)* ")"
          | "match" expr "{" arm ("," arm)* ","? "}"
arm     ::= pattern "=>" expr
pattern ::= CTOR | CTOR "(" bind ("," bind)* ")" | "ok" "(" bind ")" | "err" "(" bind ")"
          | "some" "(" bind ")" | "none" | "_"
bind    ::= IDENT | "_"
```

- 構築子の名前（CTOR）は大文字で始まる IDENT で、プログラム全体で一意。関数名・変数名・型名と同じ名前は使えない。
- 意味：variant が n 個（n ≥ 2）の型は `Result<P1, Result<P2, ... Result<Pn-1, Pn>>>` の名前である。Pk は k 番目の
  variant の中身の型で、中身がなければ `Unit`、一つなら その型、複数ならレコードと同じく右に入れ子にした
  `Pair`。n = 1 なら P1 そのもの。構築は `ok`／`err` の入れ子に、`match` は `match_result` の入れ子と、中身を
  取り出す `fst`／`snd` の `let` に書き換える（`crates/tlvm/src/sums.rs`）。型の等価性は展開後の構造で決まる。
- `match` は全部の場合を一度ずつ書くか、最後の `_ => e` で残りをまとめる。足りない場合、重複、届かない `_` は
  診断（§5）。
- 再帰する型（自分自身を中身に持つ型）は作れない（型名は使う前に宣言する）。
- 入出力：値 JSON は展開後の形。plain JSON は `{"Circle": [5]}`、`{"Rect": [2, 3]}`、`{"Empty": []}`
  （variant 名を key にし、中身を配列で書く）。

## 4. `tlvm exec` の追加

出力型が `Result<String, String>` なら、`ok(s)` は s を標準出力に書いて終了コード 0、`err(s)` は s を
標準エラーに書いて終了コード 1。

## 5. 診断

| コード | phase | 意味 |
|---|---|---|
| `E-SUM-DUPLICATE-CTOR` | name | 構築子の名前が重複している |
| `E-SUM-UNKNOWN-CTOR` | name | 知らない構築子（修復ヒントで近い名前） |
| `E-SUM-CTOR-ARITY` | name | 構築・パターンの中身の数が宣言と違う |
| `E-SUM-NAME-CONFLICT` | name | 構築子と同じ名前の関数・変数・型 |
| `E-MATCH-MISSING` | name | `match` に足りない場合がある（修復ヒントで足りない枝） |
| `E-MATCH-DUPLICATE` | name | 同じ場合の枝が二つある |
| `E-MATCH-UNREACHABLE` | name | `_` の後の枝、または全部の場合を書いた後の `_` |
| `E-MATCH-MIXED` | name | 一つの `match` に違う型の構築子が混ざっている |
| `E-TYPE-MATCH-SCRUTINEE` | typecheck | `match` の対象が直和型・`Result`・`Option` でない |

## 6. LLM での確認

`eval/tasks/89-shapes_area`、`90-parse_config`（カテゴリ `sum`）を Haiku（effort low）で各 1 回解かせ、2 問とも初回で
全テストを通した（2026-10-13）。Haiku は `Result`・`ok`・`match_result` を使い、ユーザー定義の直和型と `match` は
使わなかった（`fold` と `if` で書いた）。

## 7. 検証の結果

検証済み部品は全体で 622 件の検証を通した（`assume`・`admit` なし）。§3 の展開と `match` の書き換えは検証されていない
接着部分で、§2 の保証は書き換え後のプログラムについて成り立つ（レコードと同じ扱い）。
