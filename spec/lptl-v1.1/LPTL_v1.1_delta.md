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
- v1.1 での Haiku の初回失敗 4 件は、どれも新しい形の意味ではなく表記の誤り（`none[Int]()` の余分な `()`、予約語 `entry` を変数名に使用、括弧の数）。
- 17-zip_sum では Skill の例がそのまま解になるため、この 1 問は比較から割り引いて読む。
