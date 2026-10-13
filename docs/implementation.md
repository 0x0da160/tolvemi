# Tolvemi 処理系（Rust／Verus）について

LPTL 設計方針 v1（[`spec/lptl-v1/LPTL_design_v1.md`](../spec/lptl-v1/LPTL_design_v1.md)）§11 の層分離に沿って、
処理系を Rust で、数学的仕様と証明と検証済みの実行部品を Verus で書いています。
言語は v1 に [v1.1 の差分](../spec/lptl-v1.1/LPTL_v1.1_delta.md)（`match_option` と `uncons`、組み込み関数 `min`・`max`・`range`・`contains`・`sort`、値の型引数の山括弧、レコード型）と [v1.2 の差分](../spec/lptl-v1.2/LPTL_v1.2_delta.md)（文字と文字列、そのリテラル、組み込み関数 `code`・`char`・`to_string`・`parse_int`）を加えたものです。spec 層と証明は、レコード型を除く v1.2 の言語に対するものです。レコード型は `records.rs` が pair の入れ子に展開し、検証済み部品は書き換え後のプログラムを検査・実行します。
[v1.4 の差分](../spec/lptl-v1.4/LPTL_v1.4_delta.md) の `Result<T, E>`、`ok`／`err`、`match_result` は検証済み部品が直接扱います。
ユーザー定義の直和型と `match` は `sums.rs` が `ok`／`err` の入れ子と `match_result`／`match_option`、`fst`／`snd` の
`let` に書き換え（網羅性などの診断もここで出す）、検証済み部品は書き換え後のプログラムを検査・実行します。組み込み関数名を使った変数名（文脈キーワード）は検証済みの構文規則が直接受け付けます。
[v1.5 の差分](../spec/lptl-v1.5/LPTL_v1.5_delta.md) の `map`・`filter`・`any`・`all`・`find`・`sort_by` は、診断用の検査器が
型を検査した後に `hof.rs` が `fold`・`reverse`・`cons`・`if`・`match_option`・`let` の組み合わせへ書き換え（`sort_by` は
fold による安定な挿入整列）、検証済み部品は書き換え後のプログラムを検査・実行します。
[v1.6 の差分](../spec/lptl-v1.6/LPTL_v1.6_delta.md) の `loop(init, max, |s| e)` も同じく `hof.rs` が、状態を
`pair(評価した回数, Result<S, S>)`（ok = 続行中、err = 止まった）で持つ、`range(0, 16)` を辿る `fold` の 16 段の入れ子と
`match_result`・`match_option` に書き換えます（手間は実際の歩数に比例。v1.8 で `range(0, max)` 1 段から改めた）。
[v1.8 の差分](../spec/lptl-v1.8/LPTL_v1.8_delta.md) の整数の割り算 `div(a, b)` は `mod` と同じ経路で検証済み部品が直接扱います
（spec の `Builtin::Div`、`apply_sound` の場合、キーワード表、exec は信頼する多倍長整数の `div_pos`）。
[v1.9 の差分](../spec/lptl-v1.9/LPTL_v1.9_delta.md) の辞書 `Dict<K, V>` は、診断用の検査器が `List<Pair<K, V>>` とは別の型として
検査した後、`dict.rs`（走査は `hof.rs` と共有）が各操作を `fold`・`eq`・`reverse`・`cons`・`let` などに書き換え、型の
`Dict<K, V>` を `List<Pair<K, V>>` に置き換えます（挿入順で鍵が相異なる列。どの操作も O(n)）。検証済み部品は書き換え後の
プログラムを検査・実行します。入力の辞書の鍵の重複は接着部分（`values.rs`・`plain.rs`）が拒否します。
[v1.10 の差分](../spec/lptl-v1.10/LPTL_v1.10_delta.md) の型引数（総称の関数・レコード型・直和型）は、`generics.rs` が
名前解決（型の位置の型引数の名前を型引数の node にする）の後、`sums.rs`・`records.rs` が総称の型の使用を型引数を置き換えた
構造に展開し（型引数を推論する構築 `Node(x, 1)` は展開で作る総称の関数の呼び出しにする）、診断用の検査器が総称の関数の本体を
型引数を不透明な型として一度だけ検査して、呼び出しごとに一階の照合で型引数を決めます。続いて `generics.rs` が多相再帰を
拒否し、使われた（関数、型引数の組）ごとに複製して単相化し（名前は `first_g1` などの重ならない名前、`rec` の印は複製に移る、
使われない総称の関数はコードにならない。複製 256 個・型引数の大きさ 256 node まで）、単相のプログラムをもう一度検査します。
以降は今までどおりで、検証済み部品は単相化・書き換え後のプログラムを検査・実行します。`tlvm check` の型の表示は展開後の型から
`Opt<String>` のように型引数を復元します。
[v1.11 の差分](../spec/lptl-v1.11/LPTL_v1.11_delta.md) の `import "path.tlvm"` は、`imports.rs` が根のファイルから import を
深さ優先でたどって各ファイルを一度ずつ読み（パスは import を書いたファイルのディレクトリから解決し、根のファイルのディレクトリ
より上は拒否。循環・欠落・ファイル間の名前の衝突・ファイル数 64 と bytes の合計 1 MiB の上限を検査）、import されたものが先・
根が最後の順に一つの source へつなぎます（import の行と根以外の `entry` は同じ長さの空白にして位置を保つ）。つないだ source を
今までの `compile` に渡すので、総称・直和型・レコード・map など・辞書の処理も検証済み部品の検査も、まとめた一つのプログラムに
対して行われます。診断の span はファイルの中の位置に戻し、複数ファイルのプログラムの診断には `file` を付けます（一行 JSON の
最後の key。import のないプログラムでは付けません）。import を解決するのは CLI（ファイル）と `api::compile_files`（名前と source の
対応表。embed・Python にもある）だけで、source の文字列だけの API は `E-IMPORT-UNSUPPORTED` で拒否します。

| 設計書の層 | 場所 | 内容 |
|---|---|---|
| `spec/` | [`verus/src/`](../verus/src) の `spec.rs`、`bigstep.rs`、`syntax.rs`、`resolve.rs`（spec 部分）、`input.rs`、`json.rs`（`enc`） | 表面構文（字句・EBNF・正準整形）、名前解決、型、値、型付け、燃料付き評価、入力 JSON の文法と値 JSON の復号、出力の正準 JSON |
| `proof/` | `proof.rs`、`syntax_proof.rs`、`parse_proof.rs`、`input_proof.rs`、`bigstep.rs` | 下の「証明したこと」 |
| `exec/`（検証済み） | `surface.rs`、`resolve.rs`、`check.rs`、`eval.rs`、`input_exec.rs`、`json.rs`、`pipeline.rs`、`ir.rs`、`value.rs` | lexer、parser、formatter、名前解決、型検査、評価器、入力 JSON の parser と復号器、出力 encoder。spec との一致を証明 |
| `exec/`（未検証） | [`crates/tlvm`](../crates/tlvm) | 診断を出す lexer・parser・検査器・入力復号器、資源上限、AST transport、CLI、検証済み部品への接着。回帰テストと差分テストで確認 |

信頼している部品と未証明の義務は [`trust-boundary.toml`](../trust-boundary.toml) にまとめています。
この版は V1-A（外部 BigInt を信頼仮定とする版）です。spec 層の人手レビューが済んでおらず、診断、資源上限、
接着部分が未検証で、BigInt を信頼しているので、処理系全体を「完全に形式検証済み」とは呼びません。

## 実行の流れ

受理・拒否の判定と実行に使う値は、すべて検証済み部品が決めます。crates/tlvm の診断付きの部品は、
同じ判定に診断（コード・span・段階順）を付けるために動き、検証済み部品と判定が食い違えば
`E-INTERNAL-VERIFIED-MISMATCH` で拒否します（資源上限による打ち切りは突き合わせない）。

1. **compile**（`api::compile`）：検証済みの `compile_source`（`verus/src/pipeline.rs`）が source を字句解析・構文解析・
   名前解決して中間表現 `EProg` を作り、`check_prog` で整形式条件 `wf` を検査する。呼出しランク列は未検証の
   Tarjan 実装が作るが、`check_prog` が検査するので信頼不要。v1.7 の `rec fn` の印も未検証の接着部分が作って
   別に渡す（検証済み parser は `rec` を知らないので、source の印は同じ長さの空白に置き換え、書き換え後・AST の
   プログラムは印を外して整形してから渡す。印の列は関数の宣言順）。ランクは印のある関数へ入る辺を除いたグラフで作る。
   印を落とせば `check_prog` が循環として拒否し、余計に付ければ停止の保証の報告（`tlvm check` の `terminates`）を
   誤るだけで、型と一意性の保証は残る。
2. **decode**（`values::decode_input`）：診断付きの strict JSON parser と値復号器が入力を読み、検証済みの
   `decode_input_e`（`verus/src/input_exec.rs`）の結果と突き合わせる。
3. **run**（`evaluator::run`）：検証済みの `run_input_json` が、`check_prog` で `wf` を確かめ、入力 JSON の文字列を
   検証済みの復号器で読み直し、検証済み評価器で実行し、結果を検証済み encoder で正準 JSON にする。
4. **fmt**：検証済みの `canonical_source` が整形する（v1.7：印 `rec` を外したもので照合し、印を付けて出す）。

次が証明されています（`assume`・`admit` は使わず、`external_body` は `bigint.rs` の多倍長整数演算だけ）。

- `compile_source` が受理すれば、source は spec の構文 `parse` と名前解決 `resolve` を通り、その結果が `EProg` で、`wf` を満たす。
  構文で拒否するのは spec の `parse` が None のときだけ。
- `canonical_source` の出力は、parse すると同じ AST に戻り、字句解析すると元の source と同じ token 列になる。
- `run_input_json` が入力を拒否するのは spec の `input_val` が None のときだけ。実行したなら入力は `input_val` の
  唯一の値 v で、v は entry の入力型を持つ。
- 実行が値を返したなら、それは spec の評価 `eval_entry` が v に対して返す唯一の値 w で、出力型を持ち、出力は
  w の正準 JSON `enc(w)`（型の保証は定理 `sound` による）。`rec` の印のある関数がなければ（`no_rec`）、
  実行が Fault（spec の行き詰まり）で終わることはない（停止性 `entry_total` による）。資源上限による打ち切りは
  spec と無関係に起こりうる。

## exec 層（crates/tlvm）

| モジュール | 設計書 | 内容 |
|---|---|---|
| `lexer.rs` | §4.2、§18.1 | 診断付きの字句解析。ASCII 字句、符号付き INT、数値境界、lexical-limits |
| `parser.rs` | §4.1、§10.3、§18.1b | 診断付きの再帰下降 parser、parse Admission と structural guard、8回までの同期 recovery |
| `checker.rs` | §5、§6、§10.2、§18.1a | 診断付きの name → call-graph（DAG・rank。v1.7：`rec fn` へ入る辺を除いて検査し、循環には `rec` を勧める修復ヒント）→ typecheck（ErrorType 回復、SemanticWork 計数）→ entry → warnings |
| `formatter.rs` | §4.3、§19.4 | AST 入力用の整形と `ast_codec_v1` encoder |
| `strict_json.rs` | §9.3a | 診断付きの strict JSON parser（文法／深さ → string scalar → 重複キーの段階順） |
| `ast_codec.rs` | §19.2–19.3 | AST transport 検査と Admission 付き AST 構築 |
| `values.rs` | §9 | 診断付きの値 JSON の復号（InputAdmission を含む）と、検証済み復号器との突き合わせ |
| `evaluator.rs` | §7、§9 | 検証済み部品の結果を envelope に写す接着 |
| `api.rs` | §9.1 | `compile`／`compile_ast`／`decode_input`／`run`（v1.11：`compile_path`・`compile_files`）、検証済み部品との突き合わせ（v1.7：印 `rec` を外したテキストと印の列を渡す） |
| `plain.rs` | — | 普通の JSON と値 JSON の相互変換（設計書の外側の便宜。下の節） |
| `records.rs` | v1.1 差分 §1b | レコード型の展開（pair の入れ子と fst／snd への書き換え。未検証の接着部分） |
| `sums.rs` | v1.4 差分 §3 | 直和型と `match` の展開（ok／err の入れ子、match_result／match_option と fst／snd の let への書き換え、網羅性の検査。未検証の接着部分） |
| `recursive.rs` | v1.14 差分 §3 | 再帰する直和型の書き換え（項を長さの前置きつきの `List<Int>` に符号化し、構築を `*_new` の呼び出し、`match` を番号による `if` の連鎖、項の取り出しを `rec_at`・`rec_take`・`rec_drop` に書き換える。型の区別のため、型ごとの印を付けた写しも作る（受理の判定は両方の写しを検証済みの部品が行う）。`sums::expand` より前に行う。未検証の接着部分） |
| `hof.rs` | v1.5 差分 §2、v1.6 差分 §2 | `map`・`filter`・`any`・`all`・`find`・`sort_by`・`loop` の書き換え（型検査が残した要素と本体の型を使い、fold などにする。導入する名前はプログラム中の名前と重ならない。未検証の接着部分） |
| `dict.rs` | v1.9 差分 §2 | 辞書の操作の書き換え（`hof.rs` の走査から呼ばれ、型検査が残した鍵と値の型を使う）と、型の `Dict<K, V>` を `List<Pair<K, V>>` にする `erase`。未検証の接着部分 |
| `generics.rs` | v1.10 差分 §2 | 型引数の解決、多相再帰の検査、単相化（呼び出しごとの型引数は型検査器が記録する）と単相のプログラムの再検査。総称の型の展開は `records.rs`・`sums.rs`。未検証の接着部分 |
| `imports.rs` | v1.11 差分 §2 | `import` の解決（パスの正規化、`FsLoader`／`MapLoader`、循環・欠落・衝突・上限の検査）、ファイルをつないだ source の作成、診断の span をファイルに戻す写像。未検証の接着部分 |
| `runtime.rs` | v1.3 差分、v1.4 差分 §4、v1.13 差分 §1 | `tlvm exec`（入力の形の選択、出力型 `Result<String, String>` の標準出力・標準エラーと終了コードへの写像。v1.13：辞書の入力は `lines.rs` が作った普通の JSON を `api::decode_plain_input` で読み、`decode_input_e` で値にして `run_checked` に渡す） |
| `lines.rs` | v1.13 差分 §1b、§2a | `tlvm exec` の辞書の入力。標準入力の行（改行、行末の CR、長さ 0 の行、最初の TAB）を鍵と値にして普通の JSON の配列にし、行の形（鍵が空、値の TAB、Int の正規の表記）を検査する。診断の span をもとの行に直す。未検証の接着部分 |
| `softnames.rs` | v1.1 差分 §2a | `tlvm ast` の出力で文脈キーワードの変数名を付け替える（α 変換。検査・実行には使わない） |
| `embed.rs` | — | ホストに組み込むための小さな API（下の「組み込み」の節） |
| `repl.rs` | v1.12 差分 §1 | `tlvm repl`。セッションの宣言と式から一つのプログラムを組み立て、`imports::compile_root` と `api::run` で検査・実行する（戻り型は `E-TYPE-RETURN` の actual で決める）。未検証の front-end |
| `lsp.rs` | v1.12 差分 §2 | `tlvm lsp`。JSON-RPC の区切り（`Content-Length`）、`strict_json` での読み取り、診断の span から LSP の range（UTF-16 の列）への写像、開いている文書を先に読む import の loader、`tlvm fmt` と同じ整形。未検証の front-end |
| `main.rs` | — | `tlvm check|run|fmt|ast|test|exec`（v1.12：`repl`・`lsp`）、`--plain`、`--human`（v1.11：source のファイルは `compile_path` で import ごと検査、`ast` はまとめたプログラム） |

```sh
cargo build --release
cargo run --release -- check examples/sum_even.tlvm
cargo run --release -- run examples/sum_even.tlvm '{"tag":"list","items":[{"tag":"int","value":"2"},{"tag":"int","value":"3"}]}' --stats
cargo run --release -- fmt examples/positive_values.tlvm
cargo run --release -- run examples/identity.json '{"tag":"int","value":"-42"}'
cargo test --release
```

診断は一行一 JSON object で stderr、結果は stdout に出ます。verus/ は通常の cargo build では ghost コードを
消して普通の Rust としてコンパイルされるので、build と test に Verus は要りません。

検証済み部品に切り替える前の処理系（origin/main の版）と、ランダムに生成した型付きプログラム 400 件、
字句・名前を壊したプログラム 2900 件、入力 JSON 4000 件（空白・escape・キー順・重複キー・surrogate・
構文の破壊を含む）で、出力・診断・終了コードが一致することを確かめました。

## Verus の部分（verus/）

| ファイル | 内容 |
|---|---|
| `spec.rs` | 型、値、名前解決済み AST、型付け `ty_expr`、整形式 `wf`、燃料付き評価 `eval` |
| `proof.rs` | 停止性・型安全性 `total`／`entry_total`（`no_rec` が前提）、型保存 `sound`／`entry_sound`（`rec` があっても成り立つ）、燃料単調性 `mono`、決定性 `entry_deterministic`、組込みの健全性 `apply_sound` |
| `bigstep.rs` | 燃料付き評価から導いた大ステップ規則と、行き詰まりの伝播（`fails`） |
| `syntax.rs` | 表面構文の spec：字句 `lex`、構文 `parse`（EBNF）、token 列への印字 `tds`、正準整形 `fds` |
| `syntax_proof.rs` | 正準整形の字句解析 `lex(fds(p)) == Some(tds(p))` |
| `parse_proof.rs` | parser の健全性 `parse_sound`・完全性 `parse_complete`・token 列の一意性、formatter の AST 保存性 `format_preserves`・冪等性 `format_idempotent` |
| `surface.rs` | lexer `lex_e`、parser `parse_e`、formatter `format_e`。spec と一致 |
| `resolve.rs` | 名前解決の spec `resolve`（関数名の一意性、変数の scope、shadowing と binder 重複の拒否、entry 検査）と実行コード `resolve_e` |
| `input.rs` | 入力 JSON の spec：strict JSON の文法 `jparse`、値 JSON の復号 `jd`、`input_val` |
| `input_proof.rs` | 型整合性 `input_typed`、重複キー拒否 `input_nodup`、往復性 `input_roundtrip` |
| `input_exec.rs` | strict JSON parser `jparse_e` と復号器 `decode_input_e`。spec と一致 |
| `bigint.rs` | 信頼する多倍長整数（num-bigint を `external_body` で包む。V1-A の信頼仮定） |
| `ir.rs` | exec の中間表現 `EProg` と spec への写像 |
| `value.rs` | exec の値（共有 cons セル）と spec の値への写像、環境 |
| `check.rs` | 型検査器 `ty_of`、整形式検査 `check_prog`（ランク証明書の検査を含む）、値の型検査 `has_type` |
| `eval.rs` | 評価器。返した値は spec でも同じ値に評価され（`evals_to`）、Fault は spec の行き詰まり（`fails`）に限る |
| `json.rs` | 出力の正準 JSON：encoder の正しさ、往復性 `roundtrip`、型整合性 `dec_typed` |
| `pipeline.rs` | 入口 `compile_source`、`canonical_source`、`run_checked`、`run_checked_json`、`run_input_json` と中心定理 |

### 証明したこと（§11.2）

| 義務 | 定理 |
|---|---|
| 1 parser | `parse_sound`（受理した source の token 列は返した AST の印字 `tds(p)` に等しく、AST は深さ上限と名前規則を満たす）、`parse_complete`（source の token 列が深さ上限内の AST の印字なら、parser はその AST を返す）、`toks_unique`（EBNF の非曖昧性）、`surface::lex_e`／`parse_e` は spec と一致 |
| 2 formatter | `format_preserves`（`parse(fds(p)) == Some(p)`）、`format_idempotent`（再 parse・再整形・token 列が一致）、`surface::format_e` は spec と一致 |
| 3 名前解決 | `resolve` は関数名の一意性・entry の存在と一引数・変数の scope を検査し、`rx_scoped` で解決後の変数は scope 内。`resolve_e` は spec と一致 |
| 4 型検査 | `check::ty_of` は `ty_expr` と一致、`apply_sound` |
| 5 DAG | `check_prog` が真なら `wf`（呼出し先のランクが真に小さいか、呼出し先に `rec` の印がある） |
| 6 | `total`、`entry_total`（`no_rec` のとき）、`sound`、`entry_sound`、`entry_deterministic`、`run_checked` |
| 7 | `mono` |
| 8 評価器 | 返した値は spec の値（`evals_to`）。Fault を返すのは spec が行き詰まるときだけで、整形式で `rec` の印のないプログラムに型の合う入力を与えれば起きない（`run_checked` の ensures） |
| 9 JSON | 出力：`encode` は `enc` どおり、`roundtrip`、`dec_typed`。入力：`input_typed`、`input_nodup`、`input_roundtrip`、`decode_input_e` は spec と一致 |
| 10 失敗の分離 | `compile_source` は構文・名前・型の拒否を分け、構文で拒否するのは spec の parse が失敗するときだけ。`run_input_json` は復号の拒否（spec の `input_val` が None のときだけ）と実行を分け、`no_rec` なら実行は Fault で終わらない |

### 検証の再現

Verus 0.2026.10.06（Rust 1.98.1 ツールチェイン）と Z3 4.16.0 で確認しました。

```sh
# Verus を source から build（https://github.com/verus-lang/verus の BUILD.md に従う）
git clone https://github.com/verus-lang/verus.git && cd verus/source
./tools/get-z3.sh             # または z3 4.16.0 を用意して VERUS_Z3_PATH を設定
source ../tools/activate && vargo build --release
# 検証（このリポジトリの verus/ で。cargo-verus は Verus の build に含まれる）
cd path/to/tolvemi/verus && cargo verus focus -- --triggers-mode silent
# => verification results:: 626 verified, 0 errors
```

### まだ証明していないこと

- spec 層が設計書を正しく写しているかの人手レビュー（字句・EBNF・名前規則・値 JSON・strict JSON の文法を含む）。
- 診断（コード、span、段階順、recovery）。診断付きの部品は検証済み部品と受理・拒否を突き合わせるだけです。
- 資源上限（StaticProfile、InputAdmission の値の深さ・node 数・桁数、出力 bytes）の判定。評価器の step・割当・
  bit 長の上限は検証済み評価器の中で数えますが、上限で打ち切ることの正しさは spec に含みません。
- 完全性の向き：整形式のプログラムを `check_prog` が必ず受理すること、DAG なら Tarjan 実装が正しいランクを作ること。
- 接着部分：UTF-8 から文字列への変換、型の変換、`compile_ast` の AST 整形（tlvm の `format_program`）、envelope への写像、
  v1.7 の印 `rec` の除去と印の列（印の正しさは安全側：落とせば拒否、余計に付ければ停止を主張しなくなるだけ）。
  v1.11 の import のファイルのつなぎ方（検証済み部品はつないだ一つのプログラムを検査・実行する）と診断の span の写像。
- V1-B／V1-C（BigInt と算術の検証）。

## 設計書が決めていないため暫定で選んだこと

正式な diagnostic registry（G0 の未達項目）がまだないため、設計書本文に無い具体コードは次の暫定名にしました。
registry が決まったら差し替える前提です。

| 暫定コード | 用途 |
|---|---|
| `E-LEX-UNEXPECTED-CHARACTER` | トークンを開始できない ASCII 文字（単独の `-`、`/`、`@` など） |
| `E-LEX-INVALID-INTEGER` | `-0`、`+1`、先頭ゼロ |
| `E-PARSE-EXPECTED-TOKEN` | 区切り記号の欠落（専用構文の位置不足を含む） |
| `E-PARSE-EXPECTED-EXPR` | 式位置に式を開始できない token |
| `E-NAME-UNBOUND-VARIABLE`、`-DUPLICATE-FUNCTION`、`-DUPLICATE-PARAM`、`-DUPLICATE-BINDER`、`-SHADOW` | 名前規則違反 |
| `E-TYPE-ARG`、`-EQ-OPERANDS`、`-SND-ARG`、`-EXPECTED-LIST`、`-LIST-ITEM`、`-IF-CONDITION`、`-FOLD-LIST`、`-FOLD-BODY`、`-RETURN` | 型規則違反 |

その他の暫定判断：

- 整数直後の `-` と `.` も数値境界違反にしています（`1-2` を字句不正にするため）。
- `E-DIAG-LIMIT`／`W-DIAG-LIMIT` の phase は `diagnostic-limit`、span はゼロ幅 0 としています。
- `E-LIMIT-STATIC-SOURCE-BYTES` と入力・AST の bytes 上限診断の span はゼロ幅 0 です。
- 型エラーの主 span は違反した部分式（if 分岐不一致は else 枝、arity は call 全体）です。
- repair は source API の診断にだけ、次の機械的に決まる場合に付けます（AST API では §10.1 に従い常に `null`）。
  修復の正しさ・唯一性は保証しません。欠けた区切り記号（`E-PARSE-EXPECTED-TOKEN`）のように挿入位置や内容が
  一意に決まらないものには付けません。

  | コード | kind | constraint |
  |---|---|---|
  | `E-TYPE-RETURN`、`-ARG`、`-LIST-ITEM`、`-IF-CONDITION`、`-IF-BRANCH`、`-FOLD-BODY`、`-EQ-OPERANDS` | `replace_expression` | `expression of type T`（T は expected） |
  | `E-TYPE-FOLD-LIST`、`-EXPECTED-LIST`／`-FST-ARG`、`-SND-ARG` | `replace_expression` | `expression of type List<...>`／`Pair<..., ...>` |
  | `E-ARITY-USER`、`-BUILTIN` | `replace_expression` | `call with N arguments` |
  | `E-NAME-UNBOUND-VARIABLE` | `replace_identifier` | `variable in scope: …`（近い名前を先に最大 8 件。scope が空なら repair なし） |
  | `E-NAME-UNKNOWN-FUNCTION`、`E-ENTRY-UNKNOWN` | `replace_identifier` | 編集距離の近い関数名・組込み名（最大 3 件）、無ければ一般的な制約 |
  | `E-NAME-SHADOW`、`-DUPLICATE-BINDER`、`-DUPLICATE-PARAM`、`-DUPLICATE-FUNCTION` | `replace_identifier` | 未使用の名前 |
  | `E-ENTRY-MISSING` | `insert_text`（EOF のゼロ幅） | entry 宣言 |
  | `E-LEX-INVALID-INTEGER` | `replace_expression` | 正規形の整数リテラル |
  | `E-PARSE-EXPECTED-IDENT`（予約語が来たときだけ） | `replace_identifier` | その語が予約語であることと、`語_` のような別名 |
  | `E-PARSE-EXPECTED-TOKEN`（`)` の所に `,`、宣言の先頭、EOF） | `insert_text` | 閉じようとしている `名前(` の行と桁、`)` が一つ足りないこと |
  | `E-PARSE-EXPECTED-TOKEN`（`,` の所に `)`） | `delete_span` | その `)` が閉じる `名前(` の行と桁、引数が足りないうちに閉じていること |
  | `E-PARSE-EXPECTED-TYPE` | `replace_type` | 型の文法 |
  | `E-CYCLE-CALL`（v1.7） | `insert_text`（循環にある最初の関数の宣言の先頭） | 循環にある関数すべてに `rec ` を付けること（停止は保証されなくなる。歩数に上限があるなら fold・loop を勧める） |
  | `E-PARSE-REC-ENTRY`（v1.7） | `delete_span`（`rec`） | `rec` を消す。entry の関数が再帰するならその宣言を `rec fn` にする |
  | `E-LEX-UNEXPECTED-CHARACTER`（`/` のとき。v1.8） | `replace_expression` | 演算子は無く、整数の割り算は `div(a, b)`（`Option<Int>`、`b <= 0` なら none）、行コメントは `//` |
  | `E-TYPE-DICT-ARG`、`E-TYPE-DICT-FROM`（v1.9） | `replace_expression` | 辞書（`List<Pair<K, V>>` なら `dict_from(xs)`）／pair のリスト（既に辞書ならそのまま） |
  | `E-TYPE-FOLD-LIST`・`E-TYPE-HOF-LIST`・`E-TYPE-EXPECTED-LIST`（実際が辞書のとき。v1.9） | `replace_expression` | `dict_entries(d)`・`dict_keys(d)`・`dict_values(d)` |
  | `E-TYPE-GENERIC-INFER`（v1.10） | `insert_text`（呼び出し先の名前の直後） | `<Int, U>` のような明示の型引数（推論できた分は具体的な型で埋める）。中身のない構築子なら `Leaf<Int>()` |
  | `E-TYPE-GENERIC-UNKNOWN-PARAM`（v1.10） | `insert_text`（宣言の型引数の末尾か名前の直後） | `<T>`・`<T, U>` の宣言 |
  | `E-TYPE-GENERIC-ARITY`、`-MISMATCH`、`-INFINITE`（v1.10） | `replace_type`／`replace_expression` | 宣言どおりの数の型引数／先の引数で決まった型に合わせる／型引数を大きくしない再帰 |
  | `E-TYPE-GENERIC-DUPLICATE-PARAM`、`-PARAM-CONFLICT`、`-UNUSED-PARAM`（v1.10） | `replace_identifier`／`delete_span` | 別の名前／使わない型引数を消すか field で使う |
  | `E-ENTRY-GENERIC`（v1.10） | `insert_text` | 具体的な型の包み関数を entry にする |
  | `E-TYPE-*`（実際の型が型引数のとき。v1.10） | `replace_expression` | その型の操作は呼び出し側で行うか、具体的な型の引数を取る |
  | `E-IMPORT-AFTER-DECL`、`E-IMPORT-UNSUPPORTED`、`E-IMPORT-CYCLE`（v1.11） | `delete_span` | import の行をファイルの先頭へ移す／ファイルから検査するか対応表の API を使う／循環する import を消して共有の定義を第三のファイルへ |
  | `E-IMPORT-PATH`、`E-IMPORT-NOT-FOUND`（v1.11） | `replace_expression`（パスの文字列） | `.tlvm` で終わる相対パス／存在するファイルのパス |
  | `E-IMPORT-CONFLICT`（v1.11） | `replace_identifier` | ほかのファイルが定義していない名前（名前空間は一つ） |
- message は暫定の日本語テンプレートです。
- `E-CYCLE-CALL` の関数名関連情報は schema に関連情報キーが無いため `actual` と message に辞書順で入れています。
- host-policy は `tlvm-rust-host-v0`（評価の入れ子深さ上限 400000、評価スレッドのスタック 1 GiB）で、超過は `HostAborted` です。
  v1.7 の `rec fn` の止まらない再帰は、この深さ上限（`HostAborted` `eval-depth`）か step・割当の上限
  （`ResourceExhausted`）で終わります（スタックあふれにはならない）。
- `tlvm check` の結果 JSON に `terminates`（v1.7）を足しました。`rec fn` がなければ true、あれば false です
  （`--human` なら stderr に注記）。embed API の `Program::terminates()`、Python の `Program.terminates` も同じです。

## 設計書の外側の便宜（plain JSON、--human、tlvm test）

設計書の入出力（§9.2 の値 JSON）と診断 JSON（§10.1）はそのままにして、使いやすくするための層を足しています。
どれも検証されていない接着部分です（`trust-boundary.toml` の `glue`）。

- **普通の JSON での入出力**（`plain.rs`、`run --plain`、`api::decode_plain_input`）：entry の入力型で普通の JSON を読み、
  値 JSON に変換してから従来どおり診断付きの復号器と検証済みの復号器で読みます。出力は検証済み encoder の値 JSON を
  出力型で普通の JSON に戻します。対応は型ごとに一対一です。

  | 型 | plain JSON |
  |---|---|
  | `Int` | 整数の number（`-42`）。桁の多い整数のため正規形の十進文字列（`"-42"`）も受理。出力は \|n\| ≤ 2^53 − 1 なら number、それを超えると十進文字列（JavaScript の number で精度が落ちないように） |
  | `Bool`／`Unit` | `true`・`false`／`null` |
  | `List<T>`／`Pair<A, B>` | 配列／二要素の配列 |
  | `Option<T>` | `none` は `null`、`some(v)` は v。T が `Unit` か `Option` のときだけ `{"some": v}` |
  | レコード型 | field 名を key にした object |
  | `Result<T, E>`（v1.4） | `{"ok": v}`、`{"err": e}` |
  | 直和型（v1.4） | variant 名を key にし、中身を配列にした object（`{"Rect": [2, 3]}`、`{"Empty": []}`） |
  | `Dict<K, V>`（v1.9） | `[key, value]` の配列の配列（挿入順。`[["a", 1], ["b", 2]]`）。鍵が重なる入力は `E-INPUT-DICT-DUPLICATE-KEY`（値 JSON でも同じ） |
  | 総称の型（v1.10） | 型引数を入れて展開した構造と同じ（`Box<Int>` はレコード型の object、`Opt<String>` は直和型の object） |

  入力の上限（bytes、JSON の深さ、値の深さ・node 数・整数の桁数）は plain JSON の上で数え、診断の span も
  plain JSON の bytes 上の位置です。
- **`--human`**：診断を `file:行:列: error[CODE]: message (expected …, found …)` の形で、該当行・下線・修復ヒントを
  添えて出します（v1.11：import したファイルの診断はそのファイルの名前と行）。既定の出力は §10.1 の一行 JSON のままです（schema は未知キーを禁じるので、行・列は JSON に足しません）。
- **`tlvm test FILE [CASES]`**：`CASES`（既定は `FILE` の拡張子を `.tests.json` にしたもの）の
  `[{"name": …, "input": …, "expected": …}]` を順に実行し、出力の正準 JSON を期待値と比べます。
  input と expected は plain JSON（`--canonical` なら値 JSON）。一件ごとに一行 JSON、最後に件数を出し、
  全件 pass なら終了コード 0、それ以外は 1 です。

```sh
cargo run --release -- run examples/positive_values.tlvm '[3, -1, 2]' --plain     # => [3,2]
cargo run --release -- check examples/sum_even.tlvm --human
cargo run --release -- test examples/sum_even.tlvm                                # examples/sum_even.tests.json
```

## 対話的な道具（v1.12：tlvm repl、tlvm lsp）

言語は変えず、今までの検査・実行の経路の前に置く front-end です（検証されていない接着部分。`trust-boundary.toml` の `glue`）。
仕様は [v1.12 差分仕様](../spec/lptl-v1.12/LPTL_v1.12_delta.md) にあります。

- **`tlvm repl [FILE]`**（`repl.rs`）：セッションは import の行と宣言の source の列です。宣言の入力は単独で parse して宣言ごとに
  切り分け（同じ名前の古い宣言は置き換え）、`fn __repl_main(__repl_unit: Unit) -> Unit = unit` と `entry __repl_main` を付けた
  プログラムを `imports::compile_root`（import はカレントディレクトリから `FsLoader` で読む）で検査し、受理なら加えます。
  式は `entry __repl_main` と `fn __repl_main(__repl_unit: Unit) -> T =` の後ろ（source の最後）に置き、まず `T = Unit` で
  検査して、本体の `E-TYPE-RETURN` の actual を `T` にして検査し直します（本体がレコードの構築なら先にその型の名前）。
  実行は `tlvm run` と同じ既定の資源プロファイルで、値は `encode_plain` で出します。診断は、つないだ source のどの部分
  （今の入力、`:load` したファイル、セッションの宣言）から来たかを覚えておき、その部分の source の行・列で `render_human` します。
  出力はすべて標準出力で、prompt は標準入力が端末のとき（`std::io::IsTerminal`）だけ出します。
- **`tlvm lsp`**（`lsp.rs`）：依存を増やさないよう、JSON は `strict_json::parse` で読み、応答は `diagnostics::json_string` で
  手で組み立てます。request の `id` は受け取った bytes をそのまま返します。文書は全文同期で保持し、開く・変えるたびに
  その文書と、ほかの開いている文書の診断を出し直します。`file://` の文書は `imports::compile_root` に、開いている文書の
  中身を先に返す loader（中で `FsLoader` に委ねる）を渡して検査します。span の写像は、byte 位置の前の `\n` の数を行に、
  行頭からの文字の `len_utf16` の和を列にします。整形は `tlvm fmt` の source の経路と同じ判定（`needs_glue`・import の有無と、
  検証済み formatter との照合）です。

```sh
printf 'fn sq(x: Int) -> Int = mul(x, x)\nsq(12)\n' | cargo run --release -- repl    # defined sq / 144 : Int
cargo test --release --test repl --test lsp
```

## 組み込み（Rust の embed API、Python binding）

ホストのプログラムから LPTL を呼ぶための小さな API です。中身は `api` の compile → `decode_plain_input` → run →
`encode_plain` を既定の資源プロファイル（CLI と同じ reference-1）でつないだもので、判定と実行は CLI と同じく
検証済み部品が行います。API 自体は検証されていない接着部分です。

- **Rust**（`tlvm::embed`）：`Program::compile(source)` は受理なら `Program`、拒否なら error の診断（`Vec<Diagnostic>`）を返します。
  `input_type()`／`output_type()` は `List<Int>` の形の型、`run_json(input)` は plain JSON の入力で実行して plain JSON
  （最小空白）の出力を返します。失敗は `RunError`（`Input(診断)`、`ResourceExhausted { kind, observed, limit }`、
  `HostAborted`、`Internal`）です。診断は `diagnostic_json` で CLI と同じ一行 JSON（§10.1）になります。
  v1.11：`Program::compile_files(root, &files)` は名前と source の対応表（`BTreeMap<String, String>`）から import ごと検査します。
  上限を変えるときは `run_json_with(input, &Limits)` を使います。plain JSON の出力では 2^53 を超える整数が十進文字列になります。桁数によらず number で欲しいホスト（Python など）は `run_json_exact(input)` を使います。
- **Python**（[`crates/tlvm-py`](../crates/tlvm-py)）：PyO3 の拡張モジュール `tlvm` です。`tlvm.compile(src)` が
  `Program` を返し（v1.11：`tlvm.compile_files(root, {path: source})` は import ごと検査）、`p.run(value)` は Python の値を `json.dumps` で plain JSON にして実行し、結果を `json.loads` で
  Python の値に戻します（整数は桁数によらず int のまま往復し、`Pair` は list で返ります）。失敗は `tlvm.CompileError`・
  `tlvm.InputError`（属性 `diagnostics` は診断 JSON を dict にした list）、`tlvm.ResourceExhausted`（`kind`、
  `observed`、`limit`）、`tlvm.HostAborted`、`tlvm.InternalError` で、どれも `tlvm.TlvmError` の派生です。
  PyO3 の依存をルートに持ち込まないよう、この crate はルートの workspace から外し、独自の `Cargo.lock` を持ちます。
  build の手順は [`crates/tlvm-py/README.md`](../crates/tlvm-py/README.md) にあります。

```rust
let p = tlvm::embed::Program::compile("fn solve(xs: List<Int>) -> Int = fold(xs, 0, |acc, x| add(acc, x))\nentry solve\n")?;
assert_eq!(p.run_json("[1, 2, 3]")?, "6");
```

## 未実装

- BLAKE3 を使う成果物 hash／structural_hash。`spec_version` は未確定なので、仕様結合 hash と再現 hash はどのみち発行しません。
- 上記の未証明の項目、Skill、LLM 評価。
- パッケージ管理と性能の改善（v1.12 でも扱わない）。LSP の hover・補完・定義への移動、REPL の行編集と履歴。
