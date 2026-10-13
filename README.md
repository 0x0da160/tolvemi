# Tolvemi

Tolvemi（トルベミ、省略表記：tlvm）は、有限データ上の純粋・全域・決定的計算のための DSL の設計プロジェクトです。設計書上の名称は LPTL（LLM-Pure Total Language）です。

## 構成

| パス | 内容 |
|---|---|
| [`spec/lptl-v1/`](spec/lptl-v1/) | LPTL 設計方針 v1 と検証バンドル（一次資料。manifest の SHA-256 と一致） |
| [`spec/lptl-v1.1/`](spec/lptl-v1.1/) | v1.1 の差分仕様（`match_option` と `uncons` の追加。草案）。v1.2〜v1.11 も同じく `spec/lptl-v1.N/` |
| [`spec/Tolvemi_name_explanation_clean.md`](spec/Tolvemi_name_explanation_clean.md) | 名称・表記・設計思想 |
| [`knowledge/`](knowledge/) | 上記を [Open Knowledge Format v0.2](https://github.com/GoogleCloudPlatform/open-knowledge-format/blob/main/SPEC.md) でまとめたナレッジバンドル（入口は [`knowledge/index.md`](knowledge/index.md)） |
| [`crates/tlvm/`](crates/tlvm/) | Rust の処理系（`tlvm check／run／fmt／ast`）と回帰テスト。判定と実行は verus/ の検証済み部品が行う。説明は [`docs/implementation.md`](docs/implementation.md) |
| [`crates/tlvm-py/`](crates/tlvm-py/) | Python binding（PyO3 の拡張モジュール `tlvm`）。Rust の組み込み API `tlvm::embed` を包む。build は [`crates/tlvm-py/README.md`](crates/tlvm-py/README.md) |
| [`verus/`](verus/) | Verus の spec 層・proof 層と、検証済みの lexer・parser・formatter・名前解決・型検査器・入力 JSON の復号器・評価器・出力 encoder |
| [`trust-boundary.toml`](trust-boundary.toml) | 信頼境界と未証明義務の一覧（設計書 §11.3） |
| [`examples/`](examples/) | 設計書 §13 の例とテストケース |
| [`eval/`](eval/) | LLM 予備実験の評価セット（SKILL.md、97 問のタスク、ハーネス）。説明は [`eval/README.md`](eval/README.md) |

設計は凍結候補です（G0 未達、G1–G4 未判定）。Rust の処理系があり、字句・構文・整形・名前解決・型検査・入力 JSON の復号・評価・出力 encode は Verus で spec への適合を証明した部品が行います。spec 層の人手レビュー、診断、資源上限、接着部分は未検証で、BigInt は信頼仮定です。処理系は [v1.1 の差分仕様](spec/lptl-v1.1/LPTL_v1.1_delta.md)（`match_option`、`uncons`、レコード型、追加の組み込み関数など）と [v1.2 の差分仕様](spec/lptl-v1.2/LPTL_v1.2_delta.md)（文字 `Char` と文字列 `String`、文字・文字列リテラル、`code`・`char`・`to_string`・`parse_int`）を実装しています。[v1.3](spec/lptl-v1.3/LPTL_v1.3_delta.md) の `tlvm exec FILE ARGS...` で、プログラムを標準入力・引数から標準出力へのコマンドとして動かせます。[v1.4 の差分仕様](spec/lptl-v1.4/LPTL_v1.4_delta.md)（草案）で、失敗を値として返す `Result<T, E>`（`ok`、`err`、`match_result`）と、ユーザー定義の直和型（`type Shape = Circle(Int) | Rect(Int, Int) | Empty`）、それを分解する `match` を加えました。出力型が `Result<String, String>` のプログラムは、`exec` で `err` のとき標準エラーに書いて終了コード 1 で終わります。[v1.5 の差分仕様](spec/lptl-v1.5/LPTL_v1.5_delta.md)（草案）で、リストと一引数のラムダを取る `map(xs, |x| e)`、`filter`、`any`、`all`、`find`、`sort_by` を加えました（型検査の後に `fold` などへ書き換えてから検証済み部品に渡します）。[v1.6 の差分仕様](spec/lptl-v1.6/LPTL_v1.6_delta.md)（草案）で、上限つき反復 `loop(init, max, |s| e)` を加えました（同じく `fold` に書き換えます）。[v1.7 の差分仕様](spec/lptl-v1.7/LPTL_v1.7_delta.md)（草案）で、印をつけた関数だけ上限なしの再帰を許す `rec fn` を加えました。`rec fn` のないプログラムは従来どおり停止を証明済みで、あるプログラムは停止を保証しません（`tlvm check` が `"terminates":false` と報告し、止まらない再帰は資源上限で打ち切ります。返した値の型と一意性は証明済み）。[v1.8 の差分仕様](spec/lptl-v1.8/LPTL_v1.8_delta.md)（草案）で、整数の割り算 `div(a, b)`（`mod` と組になる床除算の商。`b <= 0` なら `none`）を検証済みの中核に加えました。[v1.9 の差分仕様](spec/lptl-v1.9/LPTL_v1.9_delta.md)（草案）で、挿入順を保つ辞書 `Dict<K, V>`（`dict<K, V>()`、`dict_get`、`dict_put`、`dict_remove`、`dict_has`、`dict_size`、`dict_keys`、`dict_values`、`dict_entries`、`dict_from`）を加えました（型検査の後に `fold` などと `List<Pair<K, V>>` へ書き換えます。入出力では `[key, value]` の配列の配列）。[v1.10 の差分仕様](spec/lptl-v1.10/LPTL_v1.10_delta.md)（草案）で、ユーザー定義の型引数（`fn first<T>(xs: List<T>) -> Option<T>`、`type Box<T> = { value: T }`、`type Tree<T> = Leaf | Node(T, Int)`）を加えました（呼び出しの型引数は引数の型から推論し、型検査の後に使われた型ごとに複製して単相化してから検証済み部品に渡します）。[v1.11 の差分仕様](spec/lptl-v1.11/LPTL_v1.11_delta.md)（草案）で、ほかの source ファイルの定義を使う `import "lib/util.tlvm"`（ファイルの先頭に書き、名前空間は一つ）を加えました（CLI がファイルをたどって一つのプログラムにまとめてから検査します。例は [`examples/stats.tlvm`](examples/stats.tlvm)）。LLM 予備実験の評価セットとハーネスは `eval/` にあり、Claude のサブスクリプションだけで実行できます（`--backend claude-cli`）。

```sh
cargo run --release -- run examples/sum_even.tlvm '{"tag":"list","items":[{"tag":"int","value":"2"},{"tag":"int","value":"3"}]}'
cargo run --release -- run examples/sum_even.tlvm '[2, 3, 4]' --plain   # 普通の JSON で入出力
cargo run --release -- test examples/sum_even.tlvm                      # examples/sum_even.tests.json を照合
cargo test --release
(cd verus && cargo verus focus -- --triggers-mode silent)
```
