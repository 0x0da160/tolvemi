# Tolvemi

Tolvemi（トルベミ、省略表記：tlvm）は、有限データ上の純粋・全域・決定的計算のための DSL の設計プロジェクトです。設計書上の名称は LPTL（LLM-Pure Total Language）です。

## 構成

| パス | 内容 |
|---|---|
| [`spec/lptl-v1/`](spec/lptl-v1/) | LPTL 設計方針 v1 と検証バンドル（一次資料。manifest の SHA-256 と一致） |
| [`spec/Tolvemi_name_explanation_clean.md`](spec/Tolvemi_name_explanation_clean.md) | 名称・表記・設計思想 |
| [`knowledge/`](knowledge/) | 上記を [Open Knowledge Format v0.2](https://github.com/GoogleCloudPlatform/open-knowledge-format/blob/main/SPEC.md) でまとめたナレッジバンドル（入口は [`knowledge/index.md`](knowledge/index.md)） |
| [`tolvemi/`](tolvemi/) | Python 試作処理系（`tlvm check／run／fmt／ast`）。説明は [`docs/implementation.md`](docs/implementation.md) |
| [`tests/`](tests/)、[`examples/`](examples/) | 設計書 §20.1 の回帰テストと §13 の例 |

設計は凍結候補です（G0 未達、G1–G4 未判定）。Python の試作処理系はありますが、Rust/Verus の規範実装・機械証明・LLM 実験はまだありません。

```sh
python3 -m tolvemi run examples/sum_even.tlvm '{"tag":"list","items":[{"tag":"int","value":"2"},{"tag":"int","value":"3"}]}'
python3 -m unittest discover -s tests -t .
```
