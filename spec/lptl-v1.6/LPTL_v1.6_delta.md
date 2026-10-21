# LPTL v1.6 差分仕様：上限つき反復 `loop`

本書は [v1.5 差分仕様](../lptl-v1.5/LPTL_v1.5_delta.md) に対する差分である。汎用言語にするロードマップの 5 段目の前半で、
「条件を満たすまで繰り返す」処理を、リストを用意せずに書けるようにする。停止性は既定で保証したまま（上限が必須）。
上限なしの再帰（印をつけた関数）は後半で扱う。

状態：草案。処理系は本書どおりに実装済み。

## 1. 追加するもの

```text
loop(init, max, |s| e)    S, Int -> Option<S>
```

- `init : S` が最初の状態。`e : Option<S>` は 1 歩の処理で、`some(s2)` なら状態を s2 にして続け、`none<S>()` なら止まる。
- 結果：止まったときはその時点の状態 s を `some(s)` で返す。本体を `max` 回評価しても止まらなければ `none<S>()`
  （上限に達したことを黙って捨てない）。`max <= 0` なら本体を評価せず `none<S>()`。
- `|s| e` は `map` などと同じ局所の binder（第一級の関数ではない）。s は外側の名前をシャドーできない。
- `loop` は文脈キーワード（v1.1 §2a）。直後が `(` のときだけ組み込み。関数名には使えない。
- 例：`loop(1, 64, |n| if(lt(n, 1000), some(mul(n, 2)), none<Int>()))` は `some(1024)`。

## 2. 検証との関係

型検査の後、接着部分 `crates/tlvm/src/hof.rs` で `fold` に書き換える（v1.5 と同じ扱い。検証済みの中核は変えない）。
状態は `pair(c, Result<S, S>)` で持つ。c は本体を評価した回数（止まったときは max にする）、ok = 続行中、err = 止まった。
1 段で `range(0, max)` を辿ると、早く止まっても手間が max に比例する（v1.8 で修正。§2a）ので、長さ 16 のリストを辿る
fold を 16 段入れ子にする（16^16 = 2^64 歩まで受け持つ）。

```text
loop(init, max, |s| e)
  => let s0 = pair(0, ok<S, S>(init)) in let m = max in
     let rg = range(0, 16) in let one = range(0, 1) in let nil = list<Int>() in
     let r = fold(if(lt(16^15, m), rg, one), s0, |a1, i1|
         fold(if(lt(fst(a1), m), if(lt(16^14, sub(m, fst(a1))), rg, one), nil), a1, |a2, i2|
           ...                                       -- 段 j（2〜15）の 1 要素は 16^(16-j) 歩を受け持つ
             let n = min(16, sub(m, fst(a15))) in   -- 段 16：残りが 16 未満なら残りの歩数だけ
             let res = fold(range(0, n), snd(a15), |acc, i|
               match_result(acc, |s| match_option(e, err<S, S>(s), |s2| ok<S, S>(s2)), |d| err<S, S>(d))) in
             pair(match_result(res, |x| add(fst(a15), n), |x| m), res)
           ...) in
     match_result(snd(r), |v| none<S>(), |d| some(d))
```

（`16^15` などは実際には整数リテラル。）各段は、残りの歩 `m - c` がその段の 1 要素の受け持ちより多ければ 16 要素の
`rg`、そうでなければ 1 要素の `one` を辿り、`c >= m`（止まったか m 回評価した）になった後は空の `nil` を辿る。

- 本体の評価はちょうど `min(m, 止まるまでの回数)` 回（§1 のとおり）。本体はソースに一度だけ現れるので、`loop` を
  入れ子にしても書き換え後のソースは入れ子の深さに比例する大きさ。
- 手間は、実際に評価した回数に比例する歩と、定数の上乗せ（止まった後に各段で残る高々 15 要素の比較。max が 16^k
  以下なら高々 k 段）。参照 profile での実測（本体が小さい場合）：max = 1 で約 460 step、max = 10^12 で 40 歩で止まると
  約 3400 step。max 回回り切るときは 1 歩あたり約 27 step（1 段の fold では約 24 step）。
- 受け持てるのは 16^16 = 2^64 歩までで、max がそれより大きくても 2^64 回で打ち切って `none` になる。どの実行上限
  （step 数。`tlvm exec` でも 10^9）も 2^64 より小さいので、この違いは観測できない（その前に資源上限で止まる）。
- acc・i・s2・d・r・m・a1 などは、プログラム中のどの名前とも重ならない新しい名前を使う。止まった後の歩では本体を
  評価しない。
- `loop` は `fold` と同じく、診断用 parser では fold の入れ子の深さ 1 に数える。書き換え後は 1 つの `loop` が式の深さを約 26 段使うので、式の深さの上限 256（`E-LIMIT-STATIC-EXPR-DEPTH`）により、`loop` を 10 段直に入れ子にすると拒否する（9 段までは受理する）。位置ごとの数は `knowledge/overview/status-and-gates.md` の DECISION-39 の段落にある。

### 2a. v1.8 での修正（問題 95）

当初は `fold(range(0, max), ...)` の 1 段に書き換えていた。止まった後の歩で本体は評価しないが、`range(0, max)` を作って
全要素を辿るため、手間は max に比例した。問題 95-base_digits の Haiku の回答は `loop(pair(n, list<Int>()), add(n, 1), ...)`
（n は約 10^12、実際の歩は約 40）で、隠しテスト 30 件中 23 件が資源上限で失敗した。上の段つきの書き換えで 30 件とも通る。

## 3. 診断

| コード | phase | 意味 |
|---|---|---|
| `E-TYPE-LOOP-MAX` | typecheck | 第 2 引数が Int でない |
| `E-TYPE-LOOP-BODY` | typecheck | 本体が `Option<S>`（S は init の型）でない |
| `E-PARSE-EXPECTED-LAMBDA` | parse | 第 3 引数が `\|s\| e` の形でない（v1.5 と共通） |

## 4. LLM での確認

この機能を使う問題 1 つを Haiku（effort low）で 1 回解かせる（結果は §5 に書く）。

## 5. 結果

- 実行 `20261013T030823Z-claude-cli`（Haiku・effort low・1 回）：93-collatz_steps は 1 ラウンド目で正解（1/1）。回答は `loop` を使った。
- 問題 93 は「100 歩で 1 に届かなければ -1」（1000 歩だと -1 の場合が隠しテストに現れないため）。
- 検証済みの中核（`verus/`）は変更なし（622 件のまま）。`cargo test --release --locked` は 104 件すべて成功。
