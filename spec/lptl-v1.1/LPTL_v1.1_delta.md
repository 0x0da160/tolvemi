# LPTL v1.1 差分仕様：Option 消去と安全リスト分解

本書は [LPTL v1 設計書](../lptl-v1/LPTL_design_v1.md)（以下 v1）に対する差分である。v1 は凍結候補のまま変更しない。
ここに書かれていない事項は v1 のとおりとする。v1 §14.1 の候補「`match_option` と `uncons` を一体で導入する」を具体化したもので、
§14.2 の条件（規範の更新、証明の更新、TCB と資源への影響の公開、LLM 効果の測定）を満たすことを目標とする。

状態：草案。処理系（crates/tlvm と verus/ の検証済み部品）は本書どおりに実装済みで、Verus の証明も v1.1 の言語に更新済み（§8）。

## 1. 追加するもの

```text
match_option(e, e_none, |x| e_some)     特殊形式（局所 binder を一つ持つ）
uncons(xs)                              組込み関数
```

`option_fold` は導入しない（`match_option` で表せる）。

## 1a. 値の型引数の括弧（v1 §4.1 の変更）

値の型引数を型と同じ山括弧で書く。`none` は `list` と同じく呼び出しの形を取る。

```text
v1                     v1.1
list[T](e1, ...)       list<T>(e1, ...)
none[T]                none<T>()
```

`[` と `]` はソースに現れなくなる（字句としては残し、v1 の書き方には `E-PARSE-EXPECTED-TOKEN` と
書き換え先を示す修復ヒントを返す）。`none<T>` の後の `()` が欠けたときは expected を `()` とする。
予備実験で LLM の初回失敗の大半が、型の `<>` と値の `[]` の混同と `none[T]()` の余計な括弧だったことによる。

## 1b. レコード型

```text
decl     ::= ... | "type" IDENT "=" "{" field_decl ("," field_decl)* ","? "}"
field_decl ::= IDENT ":" type
type     ::= ... | IDENT                                   レコード型の名前
expr     ::= ... | IDENT "{" (IDENT ":" expr ("," IDENT ":" expr)*)? ("," ".." expr | ".." expr)? "}"
           | expr "." IDENT                              後置、左結合
```

- **意味**：`type R = { f1: T1, ..., fn: Tn }` は `Pair<T1, Pair<T2, ... Tn>>`（n = 1 なら `T1`）の名前である。
  構築 `R { ... }` はその pair の入れ子、`e.fi` は `fst`／`snd` の並びに等しい。型の等価性は展開後の構造で決まる
  （ただし型注釈から来たレコード名が field の持ち主と違えば `E-TYPE-FIELD-ACCESS`）。
- **名前**：`type` は宣言の先頭でだけキーワード（予約語ではない）。型名は使う前に宣言する（再帰型を作らない）。
  field 名はプログラム全体で一意で、`e.f` の持ち主は field 名で決まる。構築ではすべての field を一度ずつ書くか、
  `..base` で残りを base から写す。
- **診断**（phase は name）：`E-RECORD-UNKNOWN-TYPE`、`E-RECORD-UNKNOWN-FIELD`、`E-RECORD-MISSING-FIELD`、
  `E-RECORD-DUPLICATE-FIELD`、`E-RECORD-DUPLICATE-TYPE`、`E-RECORD-FIELD-CONFLICT`。typecheck に `E-TYPE-FIELD-ACCESS`。
- **入出力**：値 JSON（§9.2）では pair の入れ子のまま。plain JSON では field 名を key にした object。
- **検証との関係**：展開は検証されていない接着部分（`crates/tlvm/src/records.rs`）。検証済み部品には、展開して
  `fst`／`snd` に書き換えたプログラムの整形ソースを渡し、それを検査・実行する。したがって §11.2 の保証は書き換え後の
  プログラムについて成り立つ。`tlvm fmt` はレコードを含むプログラムを診断用 formatter で整形する。AST API には
  レコードの形がない（`tlvm ast` は展開後の AST を出す）。

## 2. 字句と予約語（v1 §4.2 の変更）

予約語に `uncons` と `match_option` を加える（計 35 語）。`match_option` は `_` を含む一つの予約語トークンである。

**互換性**：v1 で `uncons` や `match_option` を関数名・変数名に使っていたプログラムは、v1.1 では
`E-PARSE-EXPECTED-IDENT`（AST API では `E-AST-IDENTIFIER`）で拒否される。v1 §19 の「AST の `callee:"uncons"` は
利用者関数名として解決する」という規則は廃止し、`uncons` は組込みとして扱う。v1.1 は v1 の上位互換ではない。

## 3. 文法（v1 §4.1 の変更）

```ebnf
expr     ::= ... v1 の各形 ...
           | "match_option" "(" expr "," expr "," "|" IDENT "|" expr ")"

builtin  ::= ... v1 の 14 個 ... | "uncons"
```

`match_option` は `if`、`fold`、`let` と同じく特殊形式で、固定位置の欠落・過剰要素は parse error であり、arity error ではない。
`|x| e` は `match_option` の第 3 位置にだけ現れ、第一級の関数ではない。

正準整形（v1 §4.3）は `match_option(e, e_none, |x| e_some)`（カンマの後に空白一つ、`|x|` の後に空白一つ）とする。

## 4. 名前（v1 §5.1 の変更）

`match_option(e, e_none, |x| e_some)` の `x` は `e_some` の中でだけ見える。`e` と `e_none` からは見えない。
`x` は外側の可視変数（引数、`let`、`fold`、外側の `match_option` の binder）をシャドーできない（`E-NAME-SHADOW`）。

## 5. 型規則（v1 §6.3 の追加）

```text
Γ ⊢ e : Option<A>    Γ ⊢ e_none : R    Γ, x:A ⊢ e_some : R
---------------------------------------------------------
Γ ⊢ match_option(e, e_none, |x| e_some) : R

Γ ⊢ xs : List<A>
-----------------------------------------
Γ ⊢ uncons(xs) : Option<Pair<A, List<A>>>
```

新しい診断コード（v1 §10.4 の typecheck 系列に追加）：

| コード | 条件 | expected / actual |
|---|---|---|
| `E-TYPE-MATCH-SCRUTINEE` | `e` が Option でない | `Option` / `e` の型 |
| `E-TYPE-MATCH-BRANCH` | `e_some` の型が `e_none` の型と異なる | `e_none` の型 / `e_some` の型 |

`uncons` の引数がリストでないときは、`reverse`・`length` と同じ `E-TYPE-EXPECTED-LIST` を使う。
型検査の論理仕事量（v1 §18.1a）は `fold` と同じく、scrutinee の head 比較一回と、分岐の型の Equal 一回を数える。
`uncons` の結果型の構築は、Pair と Option の二回の Build として数え、意味型の深さ上限の対象にする。

## 6. 評価（v1 §7 の追加）

- `match_option(e, e_none, |x| e_some)`：`e` を評価する。`none` なら `e_none` だけを評価し、その値が結果になる。
  `some(v)` なら環境に `x := v` を加えて `e_some` だけを評価する。選ばれなかった分岐は評価しない（`if` と同じ選択的評価）。
- `uncons(xs)`：`xs` が空なら `none`、そうでなければ `some(pair(先頭, 残り))`。残りのリストは元の cons セルを共有する。

停止性は保たれる。どちらも再帰を導入せず、`match_option` の評価は部分式の評価高々二回、`uncons` は O(1) である。

## 7. 資源（v1 §8.4、§18.1b、§18.3 の追加）

- 参照イベント：`match_option` は式 node の評価開始（1 step）だけを数える。binder の設定は追加 step なし（`let` と同じ）。
  `uncons` は通常組込みの適用開始（1 step）を数え、非空のときは pair node と some node を一つずつ確保する（各 1 step、AllocatedNodeCount +2）。
  空リストのときの none は共有 singleton で割当 0。
- 静的 Admission：`match_option` の node は `let` と同じく let 深さを一つ増やし、その三つの部分式はすべて増えた深さで数える。

## 8. 証明義務（v1 §11.2 の更新）

verus/ の spec 層（`spec.rs` の `Builtin::Uncons`、`Expr::Match`、`ty_expr`、`apply`、`eval`；`syntax.rs` の予約語・EBNF・正準整形・構文解析）
を本書どおりに拡張し、v1 §11.2 の義務 1〜10 を v1.1 の言語について示し直す。

| 義務 | v1.1 で追加する場合 |
|---|---|
| 1〜3 字句・構文・整形・名前解決 | `match_option` の構文と binder の scope、`uncons` の予約語化 |
| 4〜5 型検査器の健全性 | `ty_of` の `Match` と `builtin_ty` の `Uncons` |
| 6〜7 全域性・型安全性・決定性 | `total`、`mono`、`apply_sound` の新しい場合 |
| 8 評価器の適合 | `bs_match`、`fl_match` と exec 評価器の `Match`・`Uncons` |

上の場合をすべて加え、`cargo verus focus` は 529 verified, 0 errors（v1 では 519）。義務 9〜10 は新しい場合を持たない
（値 JSON と入力 JSON は変わらない）。診断側（crates/tlvm）は v1 と同じく未検証で、受理・拒否を検証済み部品と突き合わせる。

## 9. LLM 評価

v1 と同じ 60 問を、v1.1 の Skill（eval/SKILL.md）で解かせて比べた（2026-10-07、各 1 回、修復 3 回まで）。
予備実験であり §12.5 の事前登録実験ではない。

| モデル / effort | 版 | Success@1 | うち難問 17 問 | Success@3 | 出力トークン |
|---|---|---|---|---|---|
| Haiku 4.5 / low | v1 | 55/60 | 14/17 | 60/60 | 187,393 |
| Haiku 4.5 / low | v1.1 | 56/60 | 16/17 | 60/60 | 161,852 |
| Opus 5.5 / high | v1 | 60/60 | 17/17 | 60/60 | 21,401 |
| Opus 5.5 / high | v1.1 | 60/60 | 17/17 | 60/60 | 16,681 |

- 出力トークンは Haiku で 14%、Opus で 22% 減った。正答率の差は 1 回の試行では誤差の範囲である。
- 解答の約 4 割（Haiku 25 問、Opus 22 問）が `match_option` か `uncons` を使った。
- v1.1 での Haiku の初回失敗 4 件は、どれも新しい形の意味ではなく表記の誤り（`none<Int>()` の余分な `()`、予約語 `entry` を変数名に使用、括弧の数）。
- 17-zip_sum では Skill の例がそのまま解になるため、この 1 問は比較から割り引いて読む。

括弧の統一（§1a）とレコード型（§1b）を加えた後の同じ 60 問（同日、各 1 回）：

| モデル / effort | Skill | Success@1 | Success@3 | 出力トークン |
|---|---|---|---|---|
| Haiku 4.5 / low | 山括弧 | 57/60 | 60/60 | 149,222 |
| Haiku 4.5 / low | 山括弧 + レコード | 57/60 | 60/60 | 158,690 |
| Opus 5.5 / high | 山括弧 | 60/60 | 60/60 | 16,527 |
| Opus 5.5 / high | 山括弧 + レコード | 60/60 | 60/60 | 16,993 |

- 山括弧にした後、初回の解答に `[` は現れなかった。Haiku の残りの初回失敗は括弧の数の誤りと予約語 `entry` の使用。
- レコード型は Haiku が一度も使わず、Opus が 5 問で使った。この 60 問は状態が小さく、レコードの効果は測れていない
  （正答率・トークンとも誤差の範囲）。効果を見るには、状態の多い課題を足す必要がある。

状態の多い 24 問（eval/tasks の 61〜84、category: stateful）を加えて、LPTL と Python を同じ条件で比べた（同日、各 1 回、修復 3 回まで）：

| モデル / effort | 言語 | Success@1 | Success@3 | 初回のコンパイル失敗 | 出力トークン |
|---|---|---|---|---|---|
| Haiku 4.5 / low | LPTL | 19/24 | 21/24 | 3 | 215,087 |
| Haiku 4.5 / low | Python | 24/24 | 24/24 | 0 | 68,344 |
| Opus 5.5 / high | LPTL | 24/24 | 24/24 | 0 | 21,424 |
| Opus 5.5 / high | Python | 24/24 | 24/24 | 0 | 4,214 |

- Opus はこの 24 問でも両言語とも全問正解で、差は出力トークン（LPTL が約 5 倍）にだけ現れた。
- Haiku の LPTL の初回失敗 5 件の内訳：
  - 予約語を名前に使った 2 件（レコードのフィールド `length`、ラムダの引数 `pair`）。どちらも修復ヒントで次の回に直った。
  - 深い入れ子で閉じ括弧が 1 つ多かった 1 件（83-bowling_score）。診断に修復ヒントがなく、2 回目も同じ解答を返し、3 回目は別の誤り（シャドー）で終わった。
  - 論理の誤り 2 件。81-interval_scheduling は「まだ何も選んでいない」を番兵 `-1` で表したが、入力に負の座標があった。Option で表せば避けられた誤りである。
- レコード型は Haiku が 7 問、Opus が 16 問で使った。60 問のとき（Haiku 0 問、Opus 5 問）より大きく増えた。Haiku がレコードを使った解答は、最終的にすべて正解した。
- 改善の候補：
  - 予約語を減らす。組み込み関数名を文脈キーワードにする。
  - 括弧の過不足に、対応する開き括弧の位置を示す修復ヒントを付ける。
