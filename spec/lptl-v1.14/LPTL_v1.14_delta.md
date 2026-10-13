# LPTL v1.14 差分仕様：再帰する直和型

本書は [v1.13 差分仕様](../lptl-v1.13/LPTL_v1.13_delta.md) に対する差分である。自分自身を項に含む直和型
（`type Tree = Leaf | Node(Tree, Int, Tree)`）を書けるようにする。

状態：草案。処理系は本書どおりに実装済み。LLM での確認は §10。

**検証済みの中核（`verus/`）は変えない。** 型検査の前に、再帰する型を整数の列の型 `List<Int>` に書き換える（接着部分。
`crates/tlvm/src/recursive.rs`）。書き換えた後のプログラムは、今までどおり検証済みの部品が検査し、実行する。

**この版に含めないもの**：総称（型引数つき）の再帰する型、項に `String`・`List`・レコード・再帰しない直和型を置くこと、
再帰する型どうしを型検査で区別すること、木の形の JSON による入出力（§5）。

## 1. 追加するもの

- 直和型の宣言 `type Name = A | B(T, ...) | ...` のうち、宣言の型の名前をたどって自分に戻るもの（再帰する型）。
  相互に参照する型（`type A = X(B) | Ea` と `type B = Y(A, Int) | Eb`）も、循環に入るものはすべて再帰する型になる。
- 項の型の制限（§2）。
- 構築・`match`・型の名前の書き換え（§3）。

## 2. 型の制限

- 再帰する型の項の型は、`Int`、`Bool`、再帰する型そのもの（引数なし）のどれかでなければならない。
  それ以外（`String`、`List<...>`、`Option`、レコード、再帰しない直和型など）は `E-REC-FIELD-TYPE`。
- 再帰する型に型引数を付けた宣言（`type Tree<T> = ...`）は `E-REC-TYPE-PARAM`。使うときに型引数を書いた
  `Tree<Int>` は `E-TYPE-GENERIC-ARITY`。
- 再帰しない直和型と型の規則は v1.4 のまま（使う前に宣言する）。再帰しない型が再帰する型を項に含むのは構わない
  （`type Wrap = W(Tree) | N`）。
- 名前の規則（構築子の名前の一意性、関数・型との重なり、束縛名との重なり）は v1.4 と同じ診断を出す。

## 3. 値の符号化と書き換え

値は `List<Int>` である。構築子 `C` の番号を `k`（宣言の順、0 から）、項を `f1`、…、`fn` とすると、

```
C(f1, ..., fn) = [k] ++ block(f1) ++ ... ++ block(fn)
block(Int の値 x)       = [1, x]
block(Bool の値 b)      = [1, if b then 1 else 0]
block(再帰する型の値 v)  = [length(v)] ++ v
```

引数のない構築子は `[k]`。例：`Leaf` は `[0]`、`Node(Leaf, 3, Leaf)` は `[1, 1, 0, 1, 3, 1, 0]`、
`Node(Leaf, 3, Node(Leaf, 4, Leaf))` は `[1, 1, 0, 1, 3, 7, 1, 1, 0, 1, 4, 1, 0]`。

項の長さを前に置くので、次の項の位置を求めるのに子の中身を再帰で読まなくてよい。書き換えは次のとおり。

- 構築 `C(a1, ..., an)` は、関数 `c_new(a1, ..., an) -> List<Int>` の呼び出しになる（関数名は構築子の名前の小文字と
  `_new`。名前が重なれば番号を付ける）。引数のない構築子は `[k]` の列の定数になる。
- `match` は、先頭の番号 `rec_at(s, 0)` と比べる `if` の連鎖になる。最後の枝（`_` があれば `_` の枝）が残りの場合を
  受け持つ。枝の束縛は、項を先頭から順に取り出す `let` になる（`rec_at`、`rec_take`、`rec_drop` で長さと中身を読む）。
- 補助関数は LPTL の関数として書き、型検査を通す。`rec_drop(xs, n)` は先頭 `n` 個を除いた残り、`rec_take(xs, n)` は
  先頭 `n` 個、`rec_at(xs, i)` は `i` 番目（0 から。範囲外は 0）。どれも `fold` と組み込みの関数だけで書く。
- 構築の関数と補助関数には `W-UNUSED-FUNCTION` を出さない（使われなくても警告しない）。

`match` の規則は v1.4 と同じである。全部の構築子を一度ずつ書くか、最後に `_` を書く（網羅性）。同じ構築子の枝の
重複、`_` の後の枝、全部の場合を書いた後の `_` は誤り。枝の束縛の数は構築子の項の数と合わせる。

## 4. 型

- 検査器の中では、再帰する型は `List<Int>` である。型エラーの文面は `List<Int>` と出る（既知の制限）。
- 異なる再帰する型どうし、または木でない `List<Int>` を、型検査は区別しない（既知の制限。例：`Tree` の引数に
  `List<Int>` の値を渡しても検査で拒否されない）。符号化が違う値を取り違えても、実行は止まらず、結果が意味を失う。
- `eq(a, b)` は値の列を構造で比べる。符号化は一つの値に一つなので、木の等しさとして正しい。
- `Dict<K, V>`、`List<T>`、`Option<T>`、レコードの項などに再帰する型を使うのは通常どおりである（型の名前だけが
  `List<Int>` に変わる）。

## 5. 入出力と実行

- `run`（`--plain` を含む）：再帰する型の入力と出力は、その値の整数の列（plain JSON の整数の配列）。例：`Leaf` は `[0]`、
  `Node(Leaf, 3, Leaf)` は `[1,1,0,1,3,1,0]`。木の形の JSON（`{"Node": [...]}`）は未対応（次の課題）。
- `tlvm exec`：entry の入力が再帰する型なら `UnsupportedEntry`（終了コード 64）。入力の型 `List<Int>` と同じ扱い。
  出力は `run` と同じく、整数の列を plain JSON で一行に書く。
- 資源の上限は v1.13 のまま（値の節点数の上限は `run --plain` の入力の上限）。

## 6. 停止

- 再帰する型を上から下へたどる関数は、再帰するので `rec fn` にする（v1.7 と同じ規則）。`rec fn` のあるプログラムは停止を
  保証しない（`"terminates":false`）。`rec fn` のない再帰は `E-CYCLE-CALL`。
- 補助関数と構築の関数は再帰しないので、停止は常に保証される。

## 7. 診断

新しく加えた診断：

| コード | 段階 | 意味 |
|---|---|---|
| `E-REC-FIELD-TYPE` | name | 再帰する型の項が `Int`、`Bool`、再帰する型そのもの以外（§2） |
| `E-REC-TYPE-PARAM` | name | 再帰する型に型引数を付けた宣言（§2） |

既存の診断を再利用する：`E-RECORD-DUPLICATE-TYPE`、`E-SUM-DUPLICATE-CTOR`、`E-SUM-NAME-CONFLICT`（束縛名を含む）、
`E-SUM-CTOR-ARITY`、`E-SUM-UNKNOWN-CTOR`、`E-MATCH-MISSING`、`E-MATCH-DUPLICATE`、`E-MATCH-UNREACHABLE`、
`E-MATCH-MIXED`、`E-TYPE-GENERIC-ARITY`。`E-RECORD-UNKNOWN-TYPE` は、循環しない前方参照に限って従来どおり出る
（循環する型は受理する）。

## 8. 検証との関係

- 検証済みの部品（`verus/`）は変えない。Verus の結果は v1.13 と同じ（626 verified、0 errors）。
- 書き換えは `trust-boundary.toml` の `glue` に載せる（`crates/tlvm/src/recursive.rs`）。書き換えた後の整形ソースを検証済み部品が
  検査・実行し、受理の判定は今までどおり突き合わせる（`cross_check`）。
- 符号化の誤り（長さの取り違えなど）は、検証済み部品の受理では見つからない。`crates/tlvm/tests/recursive.rs` の実行の検査で確かめる。

## 9. 次の課題（候補）

- 木の形の JSON による入出力（`{"Node": [...]}`）。
- 項に `String`、`List`、レコード、再帰しない直和型を置くこと（符号化の拡張）。
- 総称の再帰する型（`type Tree<T> = ...`）。
- 再帰する型どうしを型検査で区別すること（名義の型）。値に型の番号を持たせるか、検査器に名前を残すかの選択になる。

## 10. LLM での確認

評価タスク `99-bst_height`（整数の列を二分探索木に挿入し、その高さを返す）を一つ、評価用の LLM で一回だけ確認した（`--arms lptl`、
`--rounds 1`、`--repeats 1`。修復なし）。`eval/SKILL.md` に「Recursive sum types」の節を加え、`eval/manifest.json` を書き直した。
結果は §11。

## 11. 結果

- `crates/tlvm/src/recursive.rs`（新規）：再帰する型の検出、項の符号化、構築と `match` の書き換え、補助関数。
- `crates/tlvm/src/api.rs`：`needs_expansion` に再帰する型を加え、`expand` で `sums::expand` より前に書き換える。
- `crates/tlvm/src/sums.rs`：`pattern_text` を crate 内に公開した（書き換えと同じ診断の表示に使う）。
- `crates/tlvm/src/diagnostics.rs`：`E-REC-FIELD-TYPE` と `E-REC-TYPE-PARAM` の説明文を加えた。
- `crates/tlvm/tests/recursive.rs`（新規、10 件）：符号化と実行、Bool の項、等しさ、ワイルドカード、入れ子の `match`、
  レコードと辞書と総称の関数の中の再帰する型、相互再帰と `terminates`、警告、項の型の拒否、総称の拒否、名前と枝の診断、
  型エラーの文面（`List<Int>`）、`tlvm exec` の拒否と `tlvm fmt` の出力。
- `crates/tlvm/tests/sums.rs`：「`type L = Nil | Cons(Int, L)` は再帰する型の前方参照として拒否される」という v1.4 の検査を、
  受理する検査に替えた（v1.14 で再帰する型を受理するため。前方参照の拒否の検査は残した）。
- `eval/tasks/99-bst_height/`（新規）と `eval/SKILL.md` の節、`eval/manifest.json` を更新した。
- `cargo test --release --locked --no-fail-fast` は 234 件すべて成功（v1.13 の 224 件に `recursive.rs` の 10 件を加えた）。
  `python3 eval/check.py` は成功（99 件、SKILL.md の 17 ブロック）。`python3 -m unittest discover -s eval -p 'test_*.py'` は 12 件すべて成功。
  `examples/*.tlvm` は `tlvm test --human` で 3 件すべて成功。
- 評価用の LLM での確認（§10）：`99-bst_height` を一回だけ実行した（`--arms lptl`、`--rounds 1`、`--repeats 1`、effort は low、修復なし）。
  コンパイル、シグネチャ、公開の例、隠し 30 件のすべてに合格し、出力トークンは 1040。95% 信頼区間は 21%〜100% なので、
  この一回から言えるのは「LLM が木の挿入と高さを書けた」ことまでで、精度は判定できない。
