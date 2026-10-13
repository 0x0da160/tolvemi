# LPTL v1.13 差分仕様：`tlvm exec` の辞書の入力

本書は [v1.12 差分仕様](../lptl-v1.12/LPTL_v1.12_delta.md) に対する差分である。プログラムをコマンドとして動かす `tlvm exec` で、
標準入力を「行ごとの鍵と値」の表として受け取れるようにする。一行に鍵と値を TAB で並べた表（`awk` や `cut` で作れる）を、そのまま辞書に読める。

状態：草案。処理系は本書どおりに実装済み。LLM での確認は対象外（§4）。

**言語は変えない。** 構文・型規則・意味論・診断のコード・資源上限は v1.12 のままである。加えるのは、`tlvm exec` の entry の入力型に
`Dict<String, String>` と `Dict<String, Int>` を受け付けることと、その入力を標準入力の行から作る規則だけである。

**この版に含めないもの**：鍵が `String` 以外の辞書の入力（`UnsupportedEntry` のまま）、TAB や改行を値に含める方法（引用符や
エスケープの方言）、CSV や JSON Lines などほかの表の形式、入力の上限の変更（§2c）。

## 1. 入力の形

### 1a. entry の入力型

| entry の入力型 | 渡すもの |
|---|---|
| `String` | 標準入力の全文 |
| `List<String>` | コマンドライン引数 |
| `Pair<List<String>, String>` | 引数と標準入力の全文 |
| `Dict<String, String>`（v1.13） | 標準入力の行から作った辞書。値は文字列 |
| `Dict<String, Int>`（v1.13） | 標準入力の行から作った辞書。値は整数 |

- 上の表にない型は `UnsupportedEntry`（終了コード 64）。説明文は受け付ける形の一覧を示す。鍵が `String` でない辞書
  （`Dict<Int, String>` など）はここに入る。
- 辞書の入力のとき、引数は読まない（String の入力と同じく、引数は無視する）。

### 1b. 行の読み方

標準入力は UTF-8 として検査する（v1.3 と同じ。UTF-8 でなければ `InputBoundaryFailure`、理由は `InvalidUtf8`）。そのあと次の規則で行に分ける。

- 改行 `\n` で区切る。行末の CR `\r` は一つだけ取る（CRLF の入力を読める。行の途中の CR は残す）。
- 長さ 0 の行は読まない。末尾の改行は行を増やさない（`a\t1`、`a\t1\n`、`a\t1\n\n` は同じ辞書になる）。
- 行の最初の TAB より前を鍵、後を値とする。TAB は鍵と値を分けるために一つだけ置く。
  - 鍵は空でない。空白は鍵の一部で、前後を取らない（`hello world` と `hello world ` は別の鍵）。
  - 値は TAB を含まない。空の値は `Dict<String, String>` では空の文字列 `""` になる。
  - `Dict<String, Int>` の値は正規の十進表記に限る（`-` の後に数字、先頭に 0 を置かない。`-0` と `+` は不可）。桁数の上限は
    Int と同じ 4096 桁。
- 同じ鍵が二度あれば拒否する（§1c）。挿入順は行の順である。
- 行番号は改行で数え、読まない空の行も数える（`cat -n` と同じ）。
- 先頭の BOM（U+FEFF）は取らない。最初の鍵の一部になる。

### 1c. 誤りの出し方

- 行の形の誤り（TAB がない、鍵が空、値に TAB がある、Int の表記が正規でない）は、`InputBoundaryFailure` の envelope を標準エラーに
  出し、理由に行番号を入れる。終了コード 1。

  ```text
  {"result":"InputBoundaryFailure","reason":"行 2: 鍵と値を分ける TAB がありません"}
  ```

- 辞書の復号が拒否したもの（鍵の重複、入力の資源上限）は、`run --plain` と同じ診断（一行一 JSON）を標準エラーに出す。終了コード 1。
  診断の span は、その項のもとの標準入力の行の範囲（bytes）を指す。

## 2. 変換と検証

### 2a. 普通の JSON への変換

読んだ行は、普通の JSON の配列 `[["鍵","値"], ...]` にする（鍵と値は JSON の文字列。escape は `"`・`\` と制御文字だけ）。
これを、`run --plain` で辞書を読むのと同じ `api::decode_plain_input` で読む。したがって、同じ辞書を `tlvm run --plain` に渡すと、
`tlvm exec` と同じ結果（同じ出力、同じ診断コード）になる（`crates/tlvm/tests/exec_dict.rs` の
`exec_and_run_agree_on_the_same_dict` などで確かめる）。

### 2b. 検証済みの部品

復号した辞書は `run_input_json` と同じく、検証済みの復号器（`decode_input_e`）で値にし、検証済みの評価器（`run_checked`）で実行する。
出力は v1.3・v1.4 と同じ。

### 2c. 入力の上限

辞書の入力の上限は `run --plain` と同じ（`InputProfile::default()`）。生成する JSON は 4 MiB まで、値の node 数は 262,144 まで。
一つの node は JSON の 3 bytes を超えないので、実際には node 数の上限が先に効く。鍵と値の文字は一文字が一つの node で、
項あたりの node 数は、鍵が n 文字で値が Int なら n + 3、値が String で m 文字なら n + m + 3 になる。
目安として、鍵が 6 文字・値が Int の辞書は約 2 万 9 千項まで、鍵が 12 文字なら約 1 万 7 千項まで。超えた項の行を指して拒否する。
`exec` だけ上限を上げると、同じ辞書に対する `run --plain` と結果が変わるので、この版では上げない。

### 2d. 検証との関係

- 行の読み方、普通の JSON への変換、診断の span をもとの行に直す写像は検証されていない（接着部分。`trust-boundary.toml` の glue）。
- 変換の誤りは、意図と違う辞書を実行することになり保証の外である。実行されるのは変換で作った辞書の値そのもので、その辞書に対する
  停止性・型安全性・決定性は検証済みの部品が保証する。
- 鍵の相異なりは、検証済みの復号器が受理する（`List<Pair<K, V>>` として読むため）。重複の拒否は接着部分（`values.rs`・`plain.rs`）の検査である。

## 3. 出力

v1.3・v1.4 のまま。出力が `String` ならそのまま標準出力へ。`Result<String, String>` なら `ok(s)` は標準出力へ、`err(s)` は
標準エラーへ（終了コード 1）。それ以外は plain JSON を一行で出す。

## 4. LLM での確認

対象外。LLM の実行はしていない。`eval/SKILL.md` の「Programs as commands」の節だけを、この版の入力の形に合わせて書き直した
（そのため `eval/manifest.json` の SKILL.md の SHA-256 が変わる）。評価セットの問題は変えていない。

## 5. 結果

- `crates/tlvm/src/lines.rs`（新規）：標準入力の行を普通の JSON の配列にし、診断の span をもとの行に直す。
- `crates/tlvm/src/runtime.rs`：入力の形 `Lines` を加え、行の誤りと復号の拒否を `ExecResult::InputBoundaryFailure`・
  `InputInvalid` で返す。受け付ける形の一覧 `ENTRY_SHAPES` を UnsupportedEntry の説明と共有する。`main.rs` は二つの結果を
  `run` と同じ envelope と診断の形で出す。
- `crates/tlvm/src/evaluator.rs`：`input_bits_over` を crate 内に公開し、辞書の入力にも `run` と同じ整数の bit 長の検査をかける。
- `crates/tlvm/tests/exec_dict.rs` を加えた（15 件）。`tests/dict.rs` の `exec_with_dict_inside` は、`Dict<String, Int>` が受理される
  ようになったので、拒否の検査を鍵が `Int` の `Dict<Int, String>` に替えた。
- crate の依存・`Cargo.lock` は変えていない。
- `cargo test --release --locked` は 224 件すべて成功（導入前は 209 件。`exec_dict.rs` の 15 件を加えた）。`python3 eval/check.py` は成功し、`eval/manifest.json` は SKILL.md の変更に合わせて書き直した。`python3 -m unittest discover -s eval -p 'test_*.py'` は 12 件すべて成功（偽の `claude` を使う試験を含む）。`examples/*.tlvm` の `tlvm test` は 3 件すべて成功。
