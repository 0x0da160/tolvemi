# Directory Update Log

## 2026-10-13
* **v1.7**: 印をつけた関数の再帰 `rec fn`（[v1.7 差分仕様](../spec/lptl-v1.7/LPTL_v1.7_delta.md)）を、字句・文法・型規則・呼出しグラフ・名前・動的意味論・停止性・例の各ページと診断コード表、AST codec の表に追記した。
* **v1.6**: 上限つき反復 `loop(init, max, |s| e)`（[v1.6 差分仕様](../spec/lptl-v1.6/LPTL_v1.6_delta.md)）を、組込み・字句・文法・型規則・名前・動的意味論・正準フォーマット・例の各ページと診断コード表、AST codec の表に追記した。
* **v1.5**: `map`・`filter`・`any`・`all`・`find`・`sort_by`（[v1.5 差分仕様](../spec/lptl-v1.5/LPTL_v1.5_delta.md)）を、組込み・字句・文法・型規則・名前・動的意味論・正準フォーマット・例の各ページと診断コード表、AST codec の表に追記した。
* **v1.4**: `Result`、`ok`／`err`、`match_result`、ユーザー定義の直和型と `match`（[v1.4 差分仕様](../spec/lptl-v1.4/LPTL_v1.4_delta.md)）を、型と値・字句・文法・型規則・名前・動的意味論・正準フォーマットの各ページと診断コード表に追記した。

## 2026-10-06
* **Initialization**: LPTL 設計方針 v1（文書日付 2026-10-01）と検証バンドル、Tolvemi 名称資料から、OKF v0.2 バンドルを作成した。全 concept は `status: draft`（人手レビュー前）。
* **Verification**: 限定検査 `v1_limited_checks.py` を Python 3.13.16 / jsonschema 4.26.0 で再実行し、92件中92件通過を確認した。結果は [限定検査の合格数](conformance/limited-checks.md) に記録。
