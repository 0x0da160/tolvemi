# Tolvemi 処理系（Rust／Verus）について

LPTL 設計方針 v1（[`spec/lptl-v1/LPTL_design_v1.md`](../spec/lptl-v1/LPTL_design_v1.md)）§11 の層分離に沿って、
処理系を Rust で、数学的仕様と証明と検証済みの実行部品を Verus で書いています。
言語は v1 に [v1.1 の差分](../spec/lptl-v1.1/LPTL_v1.1_delta.md)（`match_option` と `uncons`）を加えたもので、spec 層と証明も v1.1 の言語に対するものです。

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
   Tarjan 実装が作るが、`check_prog` が検査するので信頼不要。
2. **decode**（`values::decode_input`）：診断付きの strict JSON parser と値復号器が入力を読み、検証済みの
   `decode_input_e`（`verus/src/input_exec.rs`）の結果と突き合わせる。
3. **run**（`evaluator::run`）：検証済みの `run_input_json` が、`check_prog` で `wf` を確かめ、入力 JSON の文字列を
   検証済みの復号器で読み直し、検証済み評価器で実行し、結果を検証済み encoder で正準 JSON にする。
4. **fmt**：検証済みの `canonical_source` が整形する。

次が証明されています（`assume`・`admit` は使わず、`external_body` は `bigint.rs` の多倍長整数演算だけ）。

- `compile_source` が受理すれば、source は spec の構文 `parse` と名前解決 `resolve` を通り、その結果が `EProg` で、`wf` を満たす。
  構文で拒否するのは spec の `parse` が None のときだけ。
- `canonical_source` の出力は、parse すると同じ AST に戻り、字句解析すると元の source と同じ token 列になる。
- `run_input_json` が入力を拒否するのは spec の `input_val` が None のときだけ。実行したなら入力は `input_val` の
  唯一の値 v で、v は entry の入力型を持つ。
- 実行が値を返したなら、それは spec の評価 `eval_entry` が v に対して返す唯一の値 w で、出力型を持ち、出力は
  w の正準 JSON `enc(w)`。実行が Fault（spec の行き詰まり）で終わることはない。資源上限による打ち切りは
  spec と無関係に起こりうる。

## exec 層（crates/tlvm）

| モジュール | 設計書 | 内容 |
|---|---|---|
| `lexer.rs` | §4.2、§18.1 | 診断付きの字句解析。ASCII 字句、符号付き INT、数値境界、lexical-limits |
| `parser.rs` | §4.1、§10.3、§18.1b | 診断付きの再帰下降 parser、parse Admission と structural guard、8回までの同期 recovery |
| `checker.rs` | §5、§6、§10.2、§18.1a | 診断付きの name → call-graph（DAG・rank）→ typecheck（ErrorType 回復、SemanticWork 計数）→ entry → warnings |
| `formatter.rs` | §4.3、§19.4 | AST 入力用の整形と `ast_codec_v1` encoder |
| `strict_json.rs` | §9.3a | 診断付きの strict JSON parser（文法／深さ → string scalar → 重複キーの段階順） |
| `ast_codec.rs` | §19.2–19.3 | AST transport 検査と Admission 付き AST 構築 |
| `values.rs` | §9 | 診断付きの値 JSON の復号（InputAdmission を含む）と、検証済み復号器との突き合わせ |
| `evaluator.rs` | §7、§9 | 検証済み部品の結果を envelope に写す接着 |
| `api.rs` | §9.1 | `compile`／`compile_ast`／`decode_input`／`run`、検証済み部品との突き合わせ |
| `plain.rs` | — | 普通の JSON と値 JSON の相互変換（設計書の外側の便宜。下の節） |
| `main.rs` | — | `tlvm check|run|fmt|ast|test`、`--plain`、`--human` |

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
| `proof.rs` | 停止性・型安全性 `total`／`entry_total`、燃料単調性 `mono`、決定性 `entry_deterministic`、組込みの健全性 `apply_sound` |
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
| 5 DAG | `check_prog` が真なら `wf`（呼出し先のランクが真に小さい） |
| 6 | `total`、`entry_total`、`entry_deterministic`、`run_checked` |
| 7 | `mono` |
| 8 評価器 | 返した値は spec の値（`evals_to`）。Fault を返すのは spec が行き詰まるときだけで、整形式のプログラムに型の合う入力を与えれば起きない（`run_checked` の ensures） |
| 9 JSON | 出力：`encode` は `enc` どおり、`roundtrip`、`dec_typed`。入力：`input_typed`、`input_nodup`、`input_roundtrip`、`decode_input_e` は spec と一致 |
| 10 失敗の分離 | `compile_source` は構文・名前・型の拒否を分け、構文で拒否するのは spec の parse が失敗するときだけ。`run_input_json` は復号の拒否（spec の `input_val` が None のときだけ）と実行を分け、実行は Fault で終わらない |

### 検証の再現

Verus 0.2026.10.06（Rust 1.98.1 ツールチェイン）と Z3 4.16.0 で確認しました。

```sh
# Verus を source から build（https://github.com/verus-lang/verus の BUILD.md に従う）
git clone https://github.com/verus-lang/verus.git && cd verus/source
./tools/get-z3.sh             # または z3 4.16.0 を用意して VERUS_Z3_PATH を設定
source ../tools/activate && vargo build --release
# 検証（このリポジトリの verus/ で。cargo-verus は Verus の build に含まれる）
cd path/to/tolvemi/verus && cargo verus focus -- --triggers-mode silent
# => verification results:: 529 verified, 0 errors
```

### まだ証明していないこと

- spec 層が設計書を正しく写しているかの人手レビュー（字句・EBNF・名前規則・値 JSON・strict JSON の文法を含む）。
- 診断（コード、span、段階順、recovery）。診断付きの部品は検証済み部品と受理・拒否を突き合わせるだけです。
- 資源上限（StaticProfile、InputAdmission の値の深さ・node 数・桁数、出力 bytes）の判定。評価器の step・割当・
  bit 長の上限は検証済み評価器の中で数えますが、上限で打ち切ることの正しさは spec に含みません。
- 完全性の向き：整形式のプログラムを `check_prog` が必ず受理すること、DAG なら Tarjan 実装が正しいランクを作ること。
- 接着部分：UTF-8 から文字列への変換、型の変換、`compile_ast` の AST 整形（tlvm の `format_program`）、envelope への写像。
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
  | `E-PARSE-EXPECTED-TYPE` | `replace_type` | 型の文法 |
- message は暫定の日本語テンプレートです。
- `E-CYCLE-CALL` の関数名関連情報は schema に関連情報キーが無いため `actual` と message に辞書順で入れています。
- host-policy は `tlvm-rust-host-v0`（評価の入れ子深さ上限 400000、評価スレッドのスタック 1 GiB）で、超過は `HostAborted` です。

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

  入力の上限（bytes、JSON の深さ、値の深さ・node 数・整数の桁数）は plain JSON の上で数え、診断の span も
  plain JSON の bytes 上の位置です。
- **`--human`**：診断を `file:行:列: error[CODE]: message (expected …, found …)` の形で、該当行・下線・修復ヒントを
  添えて出します。既定の出力は §10.1 の一行 JSON のままです（schema は未知キーを禁じるので、行・列は JSON に足しません）。
- **`tlvm test FILE [CASES]`**：`CASES`（既定は `FILE` の拡張子を `.tests.json` にしたもの）の
  `[{"name": …, "input": …, "expected": …}]` を順に実行し、出力の正準 JSON を期待値と比べます。
  input と expected は plain JSON（`--canonical` なら値 JSON）。一件ごとに一行 JSON、最後に件数を出し、
  全件 pass なら終了コード 0、それ以外は 1 です。

```sh
cargo run --release -- run examples/positive_values.tlvm '[3, -1, 2]' --plain     # => [3,2]
cargo run --release -- check examples/sum_even.tlvm --human
cargo run --release -- test examples/sum_even.tlvm                                # examples/sum_even.tests.json
```

## 未実装

- BLAKE3 を使う成果物 hash／structural_hash。`spec_version` は未確定なので、仕様結合 hash と再現 hash はどのみち発行しません。
- 上記の未証明の項目、Skill、LLM 評価。
