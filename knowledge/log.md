# Directory Update Log

## 2026-10-21
* **決定（DECISION-39、2026-10-21）**：loop の深さの境界は、オーナーが「nil を束縛して深さを揃える」を選んだ。loop の書換えで空のリストを `let nil = list<Int>()` で束縛し、段の fold の結果も `let r` で束縛して、段 1 の fold を評価の順を変える前と同じ深さに置いた（`crates/tlvm/src/hof.rs` の `loop_`）。init は max より先のまま（init を含む初期状態 `pair(0, ok(init))` を一番外側で束縛する。DECISION-36）。十段の入れ子の書換え後の深さは、本体の位置 262（前と同じ）、max の位置 265（前は 264）、init の位置 266（前は 272）。Steps は loop の評価 1 回あたり 4 多く、値と割当の数は同じ。テスト `loop_nesting_limit_in_the_max_and_init_positions` を加え、`doubling_lowered` と `reference_events_of_loop_are_fixed`（86 → 90 step）を直した。[状態とゲート](overview/status-and-gates.md) と v1.6 差分仕様 §2 の書換えの形も直した。
* **決定（DECISION-40、2026-10-21）**：入力の辞書の重複鍵の検査の計算量は、オーナーが「整列の検査を証明する」を選んだ（推奨の「上限のまま、注意に書く」は採らない）。作業者の見積もりでは、既定の値ノード上限のもとで辞書の件数は最大約 15k〜29k、最悪の CLI 実行は約 4 秒で、そのうち鍵の検査が約 6 割を占めていた。鍵の相異なりの検査 `distinct_e`（`verus/src/input_exec.rs`）を、鍵の併合整列（`verus/src/keysort.rs` の `sort_keys_e`）と隣り合う二つの比較に変えた。比較は O(n log n) 回になり、件数で区切る必要はなくなった（資源の上限は既定のまま）。整列した並べ替えでの判定の正しさは `keysort::sorted_perm_distinct` が示し、`distinct_e` の事後条件は `r == distinct(vks(ks@))`。信頼の境界は `trust-boundary.toml` の `9.input-dict` と `[exec] verified` に書いた。計測（release、`exec`、20000 件、同じ機械で各 2 回）：f1a006d の形 2.39〜2.56 s、今の形 0.98〜1.04 s、出力は両方 59997。Verus は 1389 件・error 0（前は 1371 件）。`tlvm` のテストは debug で 374 件、release で 377 件が通り、失敗は 0 だった。

## 2026-10-20
* **決定（DECISION-35、2026-10-20）**：過去の commit の trailer は「そのまま」（オーナーの選択）。履歴は書き換えない。今後の commit の trailer にはモデル名を入れない。モデル名を含む trailer 75 件のうち 67 件が main の履歴にあり、全部を書き換えると main との共通の祖先が失われるため。
* **決定（DECISION-36、2026-10-20）**：loop の上限と評価の順は「上限は外、評価は左から」（オーナーの選択、推奨）。2^64 回の打ち切りは資源の議論として凍結の外（資源の側は DECISION-31）。評価は init、次に max。両方が資源の上限で失敗するなら、報告されるのは init のエラー（`crates/tlvm/src/hof.rs` の `loop_`、テスト `init_is_evaluated_before_max`）。動的意味論のページの評価の順も直した。式の深さは、loop の本体では変わらず、max の位置では一段深く、init の位置では浅くなる。spec の 514 行は旧順のまま（文面はオーナーの判断）。
* **DECISION-37（入力の辞書の重複鍵、2026-10-20）**：オーナーが「証明する」を選んだ（推奨どおり）。入力の辞書の重複鍵の検査は、検証済みの入力の復号器で証明する。拒否も凍結の主張に含める（値と誤り）。
* **DECISION-38（hof・dict・loop の書換えの型、2026-10-20）**：オーナーが「一致だけ証明」を選んだ。書換えに使う型（`HofTypes`、`crates/tlvm/src/checker.rs`）は信頼の境界に残す。検証済みの型付け規則との一致は SH1 で証明する。checker 自体は検証しない。
* **決定の反映（2026-10-20）**：OD-9（書換えの数は凍結の外）、式の末尾のコンマ（構文で拒否）、G3（ゲートを主張に入れる）、宣言の数の上限（平らな宣言は 126 個まで。v1.15 §3）を反映した。499d5e4 の作成者行を直し、force-with-lease で push した（c033997 に載せ直し。内容は変えていない）。
* **段階 2 の結果（S5c）**：記録と名前だけのプログラムは、検証済みの経路（`verified_from_source`、[api.rs](../crates/tlvm/src/api.rs)）で受理を判定し、印なしの写しを実行する（S5b、`71d11e0`）。S5c では、[信頼の境界](../trust-boundary.toml) の記述を実装に合わせて直し、`[proved]` に S3d（印つきの名前）、S4a と S4b（記録の意味）を加えた。凍結の主張は `2.stage2-route` の八項目に限る。G2（宣言の順序）は、オーナーが「許す」を選び（803db9c）、[DECISION-29](overview/status-and-gates.md) に記録した。
* **経路の範囲**：`route_scope`（`api.rs:750–756`）は、総称、直和型、再帰する型、`Dict`、hof、`loop` を外す。`fold` は範囲に入る（核の形、設計書 454 行）。末尾のコンマの記録（`P { a: x, }`）は、信頼側の構文器が拒否する（`parser.rs:937`。2026-10-20 のオーナーの決定。検証済みの文法と同じ）。
* **経路に残る信頼**：別の宣言の字段への参照の診断（`E-TYPE-FIELD-ACCESS`、`checker.rs:1008–1047`）と、名義の型への `fst`・`snd` の拒否（`checker.rs:1602–1608`）はゲートが行う。受理の側は、印つきの写しの型検査が見る（別の宣言の字段は受理しない）。この二つは凍結の主張に含める（G3。2026-10-20 にオーナーが「入れる」を選んだ）。名前の診断の符号と位置は信頼（`records.rs:606–610`、`sums.rs:176–232`）。手で組んだ印の形は v1.15 差分仕様 §5 のとおり閉じていない。印の消去（S4c）は未証明。
* **突き合わせの範囲**：検証済みとの突き合わせは、受理と拒否の別だけを比べる。符号・位置・理由は比べない（`api.rs:440`、`535–536`）。型の拒否は調べない（片方向）。展開段階では、名前の 8 符号（`api.rs:729`）の拒否だけを、検証済みの解決器が受理するかで調べる。`E-SUM-NAME-CONFLICT` と `E-SUM-DUPLICATE-CTOR` は突き合わせず、信頼のままにした（`api.rs:723`）。
* **変異の掃引（V7）**：記録のプログラム 77 件（経路の 53 件と V7 の 24 件。末尾のコンマの記録 `record_names.rs:383` は除く）に、七種の変異を掛けた。本番の CLI での全件は 540 件で、検証済みの食い違い 0、クラッシュ 0。テストは偶数番目の 284 件を流す。末尾のコンマの記録は、この掃引に入れない。
* **宣言の数と書換えの大きさ（V12）**：HEAD（`9a96889` から作った参照の CLI）と判定が一致した。200 個の平らな宣言は `R126` で型の深さの上限に掛かる（期待 128、実際 129）。書換えの大きさの上限（4 MiB）は、60 段の鎖と 200 個の関数で掛かる（5,663,489 bytes）。
* **深さの結果（release）**：`cargo build --release -p tlvm` は成功した。ネストした加算は 255 段まで受理し、256 段で `E-LIMIT-STATIC-EXPR-DEPTH` になる。記録の入れ子は 63 段まで受理し、64 段で拒否する（書換え後の深さ 257）。50 段から 5000 段まで、どれも溢れなかった。debug ビルドは 100 段で主スレッドが溢れる（HEAD も同じ）。上限（`profiles.rs:33`、256）とスタックの大きさは変えていない。
* **テスト**：`cargo test -p tlvm --no-fail-fast` は終了 0、passed 372、failed 0、ignored 3、コンパイラの警告 0 だった（前回は 370）。増えた 2 件は `v7_record_mutations_get_no_verified_mismatch` と `v12_declaration_count_and_rewritten_size_decisions_match_head`。
* **報告の扱い（2026-10-20）**：`[verus]` の `command` 欄は、結果の欄と同じ full crate の verify に直した（S5c、c033997）。設計書 125 行の最初の文は、オーナーが「文面を直す」を選んだ。設計書はオーナーが編集する。

## 2026-10-15
* **計数の決定（DECISION-25〜27）**：min と max の結果は、選んだ引数の値でも整数の割当を一つ数えるように `verus/src/eval.rs` を直した（Verus 667 件・error 0）。既に束縛された型変数への bind は Compare と Equal の両方を数える（§4.6。実装は既にこの形）。ok と err の構築は一つのステップと一つの割当（§8.4、§18.3 に追記）。固定は `counting.rs` と `counting_nodes.rs`。ワークスペースのテストは 328 件、失敗 0。
* **§11.2a の形 C（DECISION-28）**：規模を v1.1 で測ってから形を決める。測定の結果が出るまで、形は未決。
* **`..base`（DECISION-21）**：全部の field を書いた `..base` を `E-RECORD-BASE-REDUNDANT` で拒否するようにした。`records.rs` が base を検査せずに捨てていた不具合の修正。診断の registry は 138 コード。テストは `records.rs` と `diagnostic_registry.rs`（[既知の注意点](overview/known-caveats.md)）。
* **決定（2026-10-15）**：秘密 seed は使わず、新しい最終課題を作る（DECISION-22）。§11.2a は書換えの実装を Verus で証明し、v1.1 から v1.16 まで全版を今回の作業に入れる（DECISION-23、24）。
* **既知の注意点**：凍結前の確認で分かった、仕様どおりだが驚きやすい振る舞い、範囲外・未対応・未検査の部分、未決の事項をまとめた（[既知の注意点](overview/known-caveats.md)）。索引にも載せた。
* **診断コード**：発生箇所があるのに一覧になかった 57 件を、ソースと照合して加えた（[診断コード](diagnostics/diagnostic-codes.md)）。メッセージの雛形と修復規則は未固定。
* **診断の registry**：ソースで発生する 137 コードについて、severity、phase、message template、repair 規則、発生箇所を版 1 の registry に固定した（[registry-v1.json](diagnostics/registry-v1.json)）。ソースと fixture に照合するテストを付けた（`crates/tlvm/tests/diagnostic_registry.rs`）。spec の成果物と manifest への登録は未了。
* **Verus（レコードの試作）**：v1.1 のレコード展開が意味を保つことを、仕様上のモデルで証明した（[records_proof.rs](../verus/src/records_proof.rs)、`5566e09`）。検証は 667 件・error 0（コンテナの 0.2026.10.07 build）。`records.rs` 自体は未検証。試作の中で、全部の field を書いた `..base` が検査されない不具合を見つけ、扱いをオーナーに確認している（[既知の注意点](overview/known-caveats.md)）。
* **型引数の確認**：型引数を書かせる課題（98-adjacent_pairs）を、サブスクリプションでログインした `claude` CLI から現在の SKILL.md で一回実行し、正解した（隠しテスト 30/30）。API キーは使っていない（[v1.10 差分仕様](../spec/lptl-v1.10/LPTL_v1.10_delta.md) §5）。
* **整形**：`tlvm fmt` と LSP の整形は、`tlvm check` と同じ検査に誤りがあれば整形しない（[正準フォーマット](language/canonical-formatting.md)、[対話的な道具](api/tooling.md)。仕様は [v1.12 差分仕様](../spec/lptl-v1.12/LPTL_v1.12_delta.md) §2b）。
* **Verus**：`cargo fmt`（`56c5ce5`）で並びが変わった `lib.rs` と `pipeline.rs` のあと、`push_inj` と `ft_app` が rlimit を超えていた（625 件・error 2）。両関数に `#[verifier::rlimit(50)]` を付け、627 件・error 0 に戻した（`5ff847f`。[必須回帰テスト](conformance/regression-tests.md) の 2026-10-15 の記録）。

## 2026-10-13
* **v1.16**: パッケージ（ローカルの依存）を加えた。import の文字列の `@名前/パス` は、根のファイルのディレクトリ（またはその下のパッケージ）の `tlvm.json` が宣言した依存のディレクトリの中のファイルを読む（[v1.16 差分仕様](../spec/lptl-v1.16/LPTL_v1.16_delta.md)）。依存はローカルのディレクトリだけで、取得・版の範囲・解決・ロックファイルは含めない（v1.0.0 の前に決めた最小の形）。検証済みの核は変えず、解決は接着部分（`crates/tlvm/src/packages.rs`、`imports.rs`）で行う。`tlvm.json` を使わないプログラムは従来どおり動く。
* **v1.15**: 宣言した型（レコード型・直和型・再帰する直和型）を名義で区別した（[v1.15 差分仕様](../spec/lptl-v1.15/LPTL_v1.15_delta.md)）。展開後の構造が同じでも宣言が違えば別の型で、混ぜると型検査で拒否され、文面は型の名前で出る。検証済みの核は変えず、検査用の写しに宣言ごとの印を付ける接着部分（`crates/tlvm/src/nominal.rs`）で行った。レコードと直和型に `fst`・`snd` は使えなくなった（破壊的変更）。
* **v1.14**: 自分自身を項に含む直和型（再帰する型、`type Tree = Leaf | Node(Tree, Int, Tree)`）を加えた（[v1.14 差分仕様](../spec/lptl-v1.14/LPTL_v1.14_delta.md)）。検査の前に `List<Int>` の整数の列へ書き換える接着部分（`crates/tlvm/src/recursive.rs`）で、検証済みの中核は変えない。項は Int・Bool・再帰する型だけ、型引数は未対応。異なる再帰する型どうしは型検査で区別する（型ごとの印。混ぜると拒否される）。型エラーの文面は型の名前で出る。値の入出力は整数の列。評価タスク `99-bst_height` を評価用の LLM で一回確認した（結果は仕様 §11）。
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
