# Tolvemi

Tolvemi（トルベミ、省略表記：tlvm）は、有限データ上の純粋・全域・決定的計算のための DSL の設計プロジェクトです。設計書上の名称は LPTL（LLM-Pure Total Language）です。

## 構成

| パス | 内容 |
|---|---|
| [`spec/lptl-v1/`](spec/lptl-v1/) | LPTL 設計方針 v1 と検証バンドル（一次資料。manifest の SHA-256 と一致） |
| [`spec/lptl-v1.1/`](spec/lptl-v1.1/) | v1.1 の差分仕様（`match_option` と `uncons` の追加。草案） |
| [`spec/Tolvemi_name_explanation_clean.md`](spec/Tolvemi_name_explanation_clean.md) | 名称・表記・設計思想 |
| [`knowledge/`](knowledge/) | 上記を [Open Knowledge Format v0.2](https://github.com/GoogleCloudPlatform/open-knowledge-format/blob/main/SPEC.md) でまとめたナレッジバンドル（入口は [`knowledge/index.md`](knowledge/index.md)） |
| [`crates/tlvm/`](crates/tlvm/) | Rust の処理系（`tlvm check／run／fmt／ast`）と回帰テスト。判定と実行は verus/ の検証済み部品が行う。説明は [`docs/implementation.md`](docs/implementation.md) |
| [`crates/tlvm-py/`](crates/tlvm-py/) | Python binding（PyO3 の拡張モジュール `tlvm`）。Rust の組み込み API `tlvm::embed` を包む。build は [`crates/tlvm-py/README.md`](crates/tlvm-py/README.md) |
| [`verus/`](verus/) | Verus の spec 層・proof 層と、検証済みの lexer・parser・formatter・名前解決・型検査器・入力 JSON の復号器・評価器・出力 encoder |
| [`trust-boundary.toml`](trust-boundary.toml) | 信頼境界と未証明義務の一覧（設計書 §11.3） |
| [`examples/`](examples/) | 設計書 §13 の例とテストケース |
| [`eval/`](eval/) | LLM 予備実験の評価セット（SKILL.md、60 問のタスク、ハーネス）。説明は [`eval/README.md`](eval/README.md) |

設計は凍結候補です（G0 未達、G1–G4 未判定）。Rust の処理系があり、字句・構文・整形・名前解決・型検査・入力 JSON の復号・評価・出力 encode は Verus で spec への適合を証明した部品が行います。spec 層の人手レビュー、診断、資源上限、接着部分は未検証で、BigInt は信頼仮定です。処理系は [v1.1 の差分仕様](spec/lptl-v1.1/LPTL_v1.1_delta.md)（`match_option` と `uncons`）を実装しています。LLM 予備実験の評価セットとハーネスは `eval/` にあり、Claude のサブスクリプションだけで実行できます（`--backend claude-cli`）。

```sh
cargo run --release -- run examples/sum_even.tlvm '{"tag":"list","items":[{"tag":"int","value":"2"},{"tag":"int","value":"3"}]}'
cargo run --release -- run examples/sum_even.tlvm '[2, 3, 4]' --plain   # 普通の JSON で入出力
cargo run --release -- test examples/sum_even.tlvm                      # examples/sum_even.tests.json を照合
cargo test --release
(cd verus && cargo verus focus -- --triggers-mode silent)
```
