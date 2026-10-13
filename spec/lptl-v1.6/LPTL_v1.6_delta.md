# LPTL v1.6 差分仕様：上限つき反復 `loop`

本書は [v1.5 差分仕様](../lptl-v1.5/LPTL_v1.5_delta.md) に対する差分である。汎用言語にするロードマップの 5 段目の前半で、
「条件を満たすまで繰り返す」処理を、リストを用意せずに書けるようにする。停止性は既定で保証したまま（上限が必須）。
上限なしの再帰（印をつけた関数）は後半で扱う。

状態：草案。

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
状態は `Result<S, S>` で持つ（ok = 続行中、err = 止まった）。

```text
loop(init, max, |s| e)
  => match_result(
       fold(range(0, max), ok<S, S>(init), |acc, i|
         match_result(acc, |s| match_option(e, err<S, S>(s), |s2| ok<S, S>(s2)), |d| err<S, S>(d))),
       |r| none<S>(), |d| some(d))
```

acc・i・s2・d・r は、プログラム中のどの名前とも重ならない新しい名前を使う。止まった後の歩では本体を評価しない
（`range(0, max)` の要素を辿る手間だけかかる）。`loop` は `fold` と同じく fold の入れ子の深さに数える。

## 3. 診断

| コード | phase | 意味 |
|---|---|---|
| `E-TYPE-LOOP-MAX` | typecheck | 第 2 引数が Int でない |
| `E-TYPE-LOOP-BODY` | typecheck | 本体が `Option<S>`（S は init の型）でない |
| `E-PARSE-EXPECTED-LAMBDA` | parse | 第 3 引数が `\|s\| e` の形でない（v1.5 と共通） |

## 4. LLM での確認

この機能を使う問題 1 つを Haiku（effort low）で 1 回解かせる（結果は §5 に書く）。
