# Directory Update Log

## 2026-10-13
* **v1.14**: 自分自身を項に含む直和型（再帰する型、`type Tree = Leaf | Node(Tree, Int, Tree)`）を加えた（[v1.14 差分仕様](../spec/lptl-v1.14/LPTL_v1.14_delta.md)）。検査の前に `List<Int>` の整数の列へ書き換える接着部分（`crates/tlvm/src/recursive.rs`）で、検証済みの中核は変えない。項は Int・Bool・再帰する型だけ、型引数は未対応。型の名前は型エラーに `List<Int>` と出る（既知の制限）。値の入出力は整数の列。評価タスク `99-bst_height` を評価用の LLM で一回確認した（結果は仕様 §11）。
* **v1.13**: `tlvm exec` の entry の入力に `Dict<String, String>`・`Dict<String, Int>` を加えた。標準入力の行（`鍵<TAB>値`）を普通の JSON の配列にして `run --plain` と同じ経路で読む（[v1.13 差分仕様](../spec/lptl-v1.13/LPTL_v1.13_delta.md)。言語は変えない）。型と値のページ・診断コード表に追記した。
* **v1.12**: 対話的な道具 `tlvm repl` と `tlvm lsp`（[v1.12 差分仕様](../spec/lptl-v1.12/LPTL_v1.12_delta.md)。言語は変えない）を、API とコーデックに [対話的な道具](api/tooling.md) のページとして加えた。
* **v1.11**: ほかの source ファイルの `import`（[v1.11 差分仕様](../spec/lptl-v1.11/LPTL_v1.11_delta.md)）を、字句・文法・名前・entry と到達可能性・正準フォーマット・例の各ページと診断コード表、診断 schema（省略できる `file`）、診断の段階（`import`）、静的プロファイル（ファイル数）に追記した。
* **v1.10**: ユーザー定義の型引数（総称の関数・レコード型・直和型と単相化。[v1.10 差分仕様](../spec/lptl-v1.10/LPTL_v1.10_delta.md)）を、型と値・字句・文法・型規則・名前・動的意味論・正準フォーマット・例の各ページと診断コード表、AST codec の表に追記した。
* **v1.9**: 辞書 `Dict<K, V>` と `dict<K, V>()`・`dict_get` などの操作（[v1.9 差分仕様](../spec/lptl-v1.9/LPTL_v1.9_delta.md)）を、型と値・組込み・字句・文法・型規則・名前・動的意味論・正準フォーマット・例の各ページと診断コード表、AST codec の表に追記した。
* **v1.8（loop の手間）**: `loop` の書き換えを `range(0, 16)` を辿る fold の 16 段の入れ子に改め、手間が max でなく実際の歩数に比例するようにした（問題 95 で発見）。動的意味論のページに追記した。
* **v1.8**: 整数の割り算 `div(a, b)`（[v1.8 差分仕様](../spec/lptl-v1.8/LPTL_v1.8_delta.md)）を、組込み・字句の各ページと診断コード表、範囲（非目標）のページに追記した。
* **v1.7**: 印をつけた関数の再帰 `rec fn`（[v1.7 差分仕様](../spec/lptl-v1.7/LPTL_v1.7_delta.md)）を、字句・文法・型規則・呼出しグラフ・名前・動的意味論・停止性・例の各ページと診断コード表、AST codec の表に追記した。
* **v1.6**: 上限つき反復 `loop(init, max, |s| e)`（[v1.6 差分仕様](../spec/lptl-v1.6/LPTL_v1.6_delta.md)）を、組込み・字句・文法・型規則・名前・動的意味論・正準フォーマット・例の各ページと診断コード表、AST codec の表に追記した。
* **v1.5**: `map`・`filter`・`any`・`all`・`find`・`sort_by`（[v1.5 差分仕様](../spec/lptl-v1.5/LPTL_v1.5_delta.md)）を、組込み・字句・文法・型規則・名前・動的意味論・正準フォーマット・例の各ページと診断コード表、AST codec の表に追記した。
* **v1.4**: `Result`、`ok`／`err`、`match_result`、ユーザー定義の直和型と `match`（[v1.4 差分仕様](../spec/lptl-v1.4/LPTL_v1.4_delta.md)）を、型と値・字句・文法・型規則・名前・動的意味論・正準フォーマットの各ページと診断コード表に追記した。

## 2026-10-06
* **Initialization**: LPTL 設計方針 v1（文書日付 2026-10-01）と検証バンドル、Tolvemi 名称資料から、OKF v0.2 バンドルを作成した。全 concept は `status: draft`（人手レビュー前）。
* **Verification**: 限定検査 `v1_limited_checks.py` を Python 3.13.16 / jsonschema 4.26.0 で再実行し、92件中92件通過を確認した。結果は [限定検査の合格数](conformance/limited-checks.md) に記録。
