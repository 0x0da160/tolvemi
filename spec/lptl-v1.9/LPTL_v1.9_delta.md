# LPTL v1.9 差分仕様：辞書 `Dict<K, V>`

本書は [v1.8 差分仕様](../lptl-v1.8/LPTL_v1.8_delta.md) に対する差分である。汎用言語にするロードマップの 6 段目の続きで、
鍵から値を引く表（数え上げ、グループ分け、在庫の更新など）を、`(鍵, 値)` の pair のリストを手で探し直さずに書けるようにする。

状態：草案。処理系は本書どおりに実装済み。

## 1. 追加するもの

```text
Dict<K, V>                                型：鍵 K から値 V への辞書（K は任意の型）

dict<K, V>()              -> Dict<K, V>       空の辞書（型引数は必ず書く。list<T>() と同じ）
dict_get(d, k)            -> Option<V>        k の値。なければ none
dict_put(d, k, v)         -> Dict<K, V>       k があればその位置で値を v に置き換え、なければ末尾に足す
dict_remove(d, k)         -> Dict<K, V>       k を除く（なければ d のまま）
dict_has(d, k)            -> Bool             k があるか
dict_size(d)              -> Int              鍵の数
dict_keys(d)              -> List<K>          鍵（挿入順）
dict_values(d)            -> List<V>          値（鍵の挿入順）
dict_entries(d)           -> List<Pair<K, V>> (鍵, 値) の pair（挿入順）
dict_from(xs)             -> Dict<K, V>       xs : List<Pair<K, V>> を前から順に dict_put した辞書
```

- 辞書は**挿入順**を保つ（Python の dict と同じ）。鍵が初めて入った位置に留まり、`dict_put` で値を変えても動かない。
  `dict_remove` した鍵を後で入れ直すと末尾に付く。`dict_from` は同じ鍵が重なれば後の値で置き換え、位置は最初のもの。
- 鍵は `eq` と同じ構造的等価性で比べる。鍵の型に制限はない（`Int`、`String`、`Pair`、レコード、`Dict` も可）。
- `Dict<K, V>` は `List<Pair<K, V>>` とは別の型。相互の変換は `dict_from` と `dict_entries` で明示する。
  `fold`・`map` などは辞書を直接は取らない（`dict_entries(d)` などのリストを渡す）。
- `eq` は辞書にも使え、`dict_entries` の列として比べる。つまり**挿入順も比べる**（同じ鍵と値でも入れた順が違えば false）。
  順を無視して比べるには、鍵を整列してから比べるなどを書く。
- 名前：`dict` と `dict_get` などの 10 語は文脈キーワード（v1.1 §2a）。直後が `(`（`dict` は `<`）のときだけ組み込みで、
  変数・引数・束縛・field の名前には使える。関数名と entry の名前には使えない。`Dict` は予約語ではなく、型の位置で
  直後が `<` のときだけ辞書の型（型引数のない `Dict` はレコード型の名前として読む）。
- 例：語を数える。

```text
fn count(ws: List<String>) -> Dict<String, Int> =
  fold(ws, dict<String, Int>(), |d, w| dict_put(d, w, add(match_option(dict_get(d, w), 0, |c| c), 1)))
```

### 1a. 入出力

entry の入力型・出力型に `Dict<K, V>` を使える（入れ子も可）。

- plain JSON：`[key, value]` の配列の配列（挿入順）。例：`[["apple", 3], ["pear", 1]]`。鍵が `String` でも object にはしない
  （鍵の型によらず一つの形にする。object の key の順序に頼らない）。
- 値 JSON：`List<Pair<K, V>>` と同じ（`{"tag":"list","items":[{"tag":"pair","left":...,"right":...}, ...]}`）。
- 入力に同じ鍵が二度あれば `E-INPUT-DICT-DUPLICATE-KEY` で拒否する（どちらの JSON でも。正準の値 JSON が等しい鍵を同じとみなす）。
- `tlvm exec` の入力型には使えない（v1.3 の 3 形のまま）。プログラムの中で使うのは自由。

## 2. 検証との関係

検証済みの中核は変えない。型検査の後、接着部分（`crates/tlvm/src/dict.rs`、走査は `hof.rs` と共有）で各操作を
`fold` などに書き換え、型の `Dict<K, V>` を `List<Pair<K, V>>` に置き換えてから検証済み部品に渡す（v1.5 の `map` などと
同じ扱い）。書き換え後の辞書は、挿入順に並び鍵が相異なる `(鍵, 値)` の列である。

```text
dict<K, V>()        => list<Pair<K, V>>()
dict_size(d)        => length(d)
dict_entries(d)     => d
dict_keys(d)        => reverse(fold(d, list<K>(), |acc, e| cons(fst(e), acc)))
dict_values(d)      => reverse(fold(d, list<V>(), |acc, e| cons(snd(e), acc)))
dict_get(d, k)      => let dd = d in let kk = k in fold(dd, none<V>(), |acc, e| if(eq(fst(e), kk), some(snd(e)), acc))
dict_has(d, k)      => let dd = d in let kk = k in fold(dd, false, |acc, e| if(acc, true, eq(fst(e), kk)))
dict_remove(d, k)   => let dd = d in let kk = k in
                         reverse(fold(dd, list<Pair<K, V>>(), |acc, e| if(eq(fst(e), kk), acc, cons(e, acc))))
dict_put(d, k, v)   => let dd = d in let kk = k in let vv = v in PUT(dd, kk, vv)
dict_from(xs)       => fold(xs, list<Pair<K, V>>(), |acc, p| let kk = fst(p) in let vv = snd(p) in PUT(acc, kk, vv))

PUT(d, kk, vv)      => let r = fold(d, pair(list<Pair<K, V>>(), false), |acc, e|
                         if(eq(fst(e), kk), pair(cons(pair(kk, vv), fst(acc)), true), pair(cons(e, fst(acc)), snd(acc)))) in
                       reverse(if(snd(r), fst(r), cons(pair(kk, vv), fst(r))))
```

- 引数は左から順に一度だけ評価する。dd・kk・acc・e などの導入する名前は、プログラム中のどの名前とも重ならないもの
  （v1.5 と同じ `hof1` などの列）。
- 手間：どの操作も辞書の大きさ n に対して O(n) の歩（ハッシュ表ではない）。`dict_from(xs)` と、n 件を 1 件ずつ
  `dict_put` する fold は O(n²)。数百件までは既定の資源上限に十分収まる（例：鍵 150 個に 400 件を入れて約 110 万歩）。
- 停止性・型安全性・決定性（v1 §11.2）は書き換え後のプログラムについて成り立つ。「鍵が相異なる」ことは検証済み部品の
  型には現れない性質で、各操作の書き換えが保ち、入力では復号の検査（§1a。接着部分）で保つ。
- `rec fn`・`loop`・`map` など・レコード・直和型と組み合わせられる（辞書をレコードの field、直和型の中身、`loop` の状態、
  辞書の値や鍵にしてよい）。
- AST transport（この処理系の拡張）：型は `{"tag":"dict","key":T,"value":T}`、空の辞書は
  `{"tag":"dict","key_type":T,"value_type":T}`、操作は `call`（callee が `dict_get` など）。

## 3. 診断

| コード | phase | 意味 |
|---|---|---|
| `E-TYPE-DICT-ARG` | typecheck | `dict_get` などの第 1 引数が辞書でない（`List<Pair<K, V>>` なら修復ヒントで `dict_from` を示す） |
| `E-TYPE-DICT-FROM` | typecheck | `dict_from` の引数が `List<Pair<K, V>>` でない（既に辞書なら、そのまま使うよう示す） |
| `E-TYPE-ARG` | typecheck | 鍵・値の型が辞書の K・V と違う（既存のコード） |
| `E-INPUT-DICT-DUPLICATE-KEY` | input-decode | 入力の辞書に同じ鍵が二度ある |

- 辞書を `fold`・`map`・`length` などに渡すと既存の `E-TYPE-FOLD-LIST`・`E-TYPE-HOF-LIST`・`E-TYPE-EXPECTED-LIST` になり、
  修復ヒントで `dict_entries(d)`・`dict_keys(d)`・`dict_values(d)` を示す。`Dict` と `List<Pair<K, V>>` を取り違えた
  `E-TYPE-ARG`・`E-TYPE-RETURN` などにも `dict_from`／`dict_entries` を添える。
- `dict()`（型引数がない）・`dict<K, V>`（`()` がない）は `E-PARSE-EXPECTED-TOKEN`（修復ヒントで `dict<K, V>()` を示す）。

## 4. LLM での確認

この機能を使う問題 1 つ（96-inventory：在庫の更新。消えた品目を入れ直すと末尾に付く）を Haiku（effort low）で 1 回
解かせる（結果は §5 に書く）。

## 5. 結果

- 検証済みの中核（`verus/`）は変更なし。`cargo test --release --locked` は 144 件すべて成功。
- 実行 `20261013T061404Z-claude-cli`（Haiku・effort low・1 回）：96-inventory は 1 ラウンド目で正解（1/1）。回答は `dict_get`・`dict_put`・`dict_remove`・`dict_entries` を使った。
