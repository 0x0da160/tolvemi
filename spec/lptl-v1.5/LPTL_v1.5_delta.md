# LPTL v1.5 差分仕様：関数を渡す組み込み

本書は [v1.4 差分仕様](../lptl-v1.4/LPTL_v1.4_delta.md) に対する差分である。汎用言語にするロードマップの 4 段目で、
リストの各要素に式を当てる書き方を `fold` より短く書けるようにする。

状態：草案。処理系は本書どおりに実装済み。

## 1. 追加するもの

```text
map(xs, |x| e)       List<A> -> List<B>     各要素に e を当てた列（順序を保つ）
filter(xs, |x| p)    List<A> -> List<A>     p が true の要素だけ（順序を保つ）
any(xs, |x| p)       List<A> -> Bool        p が true の要素がある
all(xs, |x| p)       List<A> -> Bool        すべての要素で p が true（空なら true）
find(xs, |x| p)      List<A> -> Option<A>   p が true の最初の要素
sort_by(xs, |x| k)   List<A> -> List<A>     k（Int）の昇順。k が等しい要素は元の順（安定）
```

- `|x| e` は `fold` と同じく、その位置にだけ書ける局所の binder で、第一級の関数ではない。x は e の中でだけ見え、
  外側の可視変数をシャドーできない。e は外側の変数を参照できる。
- 型：xs は `List<A>`（`String` も可）、x : A。`filter`・`any`・`all`・`find` の本体は `Bool`、`sort_by` の本体は `Int`。
- 評価：要素の順に本体を評価する。`any` は true が出た後、`all` は false が出た後、`find` は見つかった後の要素で
  本体を評価しない。`sort_by` は比較のたびに鍵を計算し直す（要素数 n に対して O(n²) の評価）。
- 6 語は文脈キーワード（v1.1 §2a）で、変数名などに使える。直後が `(` のときだけ組み込み。

## 2. 検証との関係

6 つの形は、型検査の後に `fold`・`reverse`・`cons`・`if`・`match_option` の組み合わせへ書き換える（検証されていない接着部分
`crates/tlvm/src/hof.rs`）。検証済み部品は書き換え後のプログラムを検査・実行するので、停止性・型安全性・決定性
（v1 §11.2）は書き換え後のプログラムについて成り立つ（レコード、直和型と同じ扱い）。

```text
map(xs, |x| e)     => reverse(fold(xs, list<B>(), |acc, x| cons(e, acc)))
filter(xs, |x| p)  => reverse(fold(xs, list<A>(), |acc, x| if(p, cons(x, acc), acc)))
any(xs, |x| p)     => fold(xs, false, |acc, x| if(acc, true, p))
all(xs, |x| p)     => fold(xs, true, |acc, x| if(acc, p, false))
find(xs, |x| p)    => fold(xs, none<A>(), |acc, x| match_option(acc, if(p, some(x), none<A>()), |y| some(y)))
sort_by            => fold による安定な挿入整列
```

acc・y などの導入する名前は、プログラム中のどの名前とも重ならないものを選ぶ。

## 3. 診断

| コード | phase | 意味 |
|---|---|---|
| `E-TYPE-HOF-LIST` | typecheck | 第 1 引数がリストでない |
| `E-TYPE-HOF-BODY` | typecheck | 本体の型が違う（`filter` などで Bool でない、`sort_by` で Int でない） |
| `E-PARSE-EXPECTED-LAMBDA` | parse | 第 2 引数が `\|x\| e` の形でない（修復ヒント付き） |

## 4. LLM での確認

この機能を使う少数の問題を Haiku（effort low）で各 1 回解かせる（結果は §5 に書く）。
