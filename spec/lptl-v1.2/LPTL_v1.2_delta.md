# LPTL v1.2 差分仕様：文字と文字列

本書は [v1.1 差分仕様](../lptl-v1.1/LPTL_v1.1_delta.md)（以下 v1.1）に対する差分である。ここに書かれていない事項は
v1.1 と v1 のとおりとする。汎用言語にするロードマップの最初の段階で、テキストを扱えるようにする。

状態：草案。処理系（crates/tlvm と verus/ の検証済み部品）は本書どおりに実装済みで、Verus の証明も更新済み（§7）。

## 1. 追加するもの

```text
Char                      型：Unicode のスカラー値（0〜0x10FFFF、surrogate 0xD800〜0xDFFF を除く）
String                    型：List<Char> の名前。ソースでは必ず String と書く
'a'  '\n'                 文字リテラル
"hello\n"                 文字列リテラル（型は String）
code(c)                   Char -> Int          文字の番号
char(n)                   Int -> Option<Char>  n がスカラー値なら some、そうでなければ none
to_string(n)              Int -> String        正準十進表記（負なら先頭に '-'）
parse_int(s)              String -> Option<Int>
```

文字列は文字のリストそのものなので、リストの組み込み（`concat`、`length`、`reverse`、`uncons`、`contains`、`eq`）と
`fold` がそのまま文字列に使える。例：`concat("ab", "c")`、`length(s)`、`eq(s, "yes")`。

## 2. 型（v1 §3 の追加）

- `Char` を基本型に加える。値は Unicode のスカラー値。
- `String` は `List<Char>` と同じ型の別名ではなく、**その型の唯一の綴り**である。`List<Char>` と書くと構文エラー
  （検証済み部品の `pt` が拒否する）。診断は書き換え先 `String` を修復ヒントで返す。型の表示も `String` を使う
  （`List<String>`、`Option<String>` など）。
- 正準性：型の綴りは一意のまま（`String` の綴りは一つ、`List<Char>` は書けない）。

## 3. 字句（v1 §4.2 の変更）

予約語に `Char`、`String`（型名）と `code`、`char`、`to_string`、`parse_int`（組み込み関数）を加える。組み込み関数の
4 語は v1.1 §2a の文脈キーワードで、変数名などに使える。

```text
char_lit   ::= "'" (raw_c | escape_c) "'"
string_lit ::= '"' (raw_s | escape_s)* '"'
raw_c      ::= 0x20 以上の文字で、\ と ' 以外
raw_s      ::= 0x20 以上の文字で、\ と " 以外
escape_c   ::= "\\" | "\'" | "\n" | "\t" | "\r"
escape_s   ::= "\\" | "\"" | "\n" | "\t" | "\r"
```

- 改行・タブなどの制御文字は、リテラルの中に生のまま書けない（エスケープで書く）。0x20 未満のその他の制御文字は
  リテラルでは書けない（`char(n)` で作る）。
- 文字リテラルの中の `"`、文字列リテラルの中の `'` はそのまま書く（`\"` は文字リテラルでは不正、`\'` は文字列
  リテラルでは不正）。
- 非 ASCII 文字はリテラルの中でだけ書ける（リテラルとコメントの外では従来どおり `E-LEX-NON-ASCII`）。
- 正準整形：上の 5 つのエスケープ（区切りの引用符、`\`、改行、タブ、復帰）だけを使い、ほかの文字は生で書く。

## 4. 文法と名前解決（v1 §4.1、§5 の追加）

```ebnf
expr ::= ... | char_lit | string_lit
type ::= ... | "Char" | "String"
```

名前解決は文字列リテラル `"c1...cn"` を `list<Char>(c1, ..., cn)` の文字の式にする（`verus/src/resolve.rs` の
`str_exprs`）。文字リテラルは文字の値の式になる。

## 5. 型規則と評価（v1 §6.3、§7 の追加）

```text
'c' : Char        "..." : String
code      : Char -> Int
char      : Int -> Option<Char>
to_string : Int -> String
parse_int : String -> Option<Int>
```

- `code(c)` は c の番号。`char(n)` は n がスカラー値なら `some(c)`、そうでなければ `none<Char>()`。
- `to_string(n)` は値 JSON の整数と同じ正準十進表記（`0`、`-12` など）。
- `parse_int(s)` は、先頭に `-` が一つあってもよい 1 文字以上の ASCII 数字の列なら `some(値)`、それ以外（空、
  `-` だけ、`+`、空白、数字以外を含む）は `none`。先頭の `0` は許す（`"007"` は 7、`"-0"` は 0）。
- 停止性・型安全性・決定性（v1 §11.2）はそのまま成り立つ（§7）。

## 6. 値の JSON（v1 §9.2 の追加）

- 値 JSON：文字は `{"tag":"char","value":"<十進の番号>"}`。文字列は文字のリスト。復号はスカラー値でない番号を拒否する。
- plain JSON（検証されていない便宜の形式）：`String` の値は JSON の文字列、`Char` の値は 1 文字の JSON 文字列で書く。

## 7. 証明義務（v1 §11.2 の更新）

検証済み部品（`verus/`）に次を入れ、全体で 587 件の検証を通した（`assume`・`admit` なし）。

- spec：`Ty::Char`、`Val::Char`（型はスカラー値であることを含む）、4 つの組み込みの型規則と意味（`apply`）。
- 型安全性：`apply_sound` に 4 つの組み込みを追加（`to_string` の結果がスカラー値の列であることを含む）。
- 実行：exec 評価器が spec と同じ値を返す（`to_string_e`、`parse_int_e`、`char` の範囲検査）。
- 字句・構文：`lex` に文字・文字列リテラル（`slit`、`unesc`）、正準形 `fe` にエスケープ（`esc`、`escs`）。
  字句の往復（`lchr`、`lstr`）、parser の健全性・完全性、formatter の AST 保存性、exec の字句解析器・formatter・
  名前解決が spec と一致することを証明。
- JSON：出力の往復（`roundtrip_char`）と、入力の復号の往復（`rt_char`）。

信頼境界の追加：多倍長整数の `to_u32`（`char` の範囲判定に使う。num-traits の `ToPrimitive::to_u32`）を
`trust-boundary.toml` の `[bigint]` に加える。
