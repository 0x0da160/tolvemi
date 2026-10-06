# Tolvemi 処理系（Rust／Verus）について

LPTL 設計方針 v1（[`spec/lptl-v1/LPTL_design_v1.md`](../spec/lptl-v1/LPTL_design_v1.md)）§11 の層分離に沿って、
処理系を Rust で、数学的仕様と証明と検証済みの実行部品を Verus で書いています。

| 設計書の層 | 場所 | 検証 |
|---|---|---|
| `spec/` | [`verus/src/spec.rs`](../verus/src/spec.rs)、[`bigstep.rs`](../verus/src/bigstep.rs) | 型、値、名前解決済み AST、型付け、呼出しランク、燃料付き評価と、そこから導いた大ステップ規則 |
| `proof/` | [`verus/src/proof.rs`](../verus/src/proof.rs) | 停止性、型安全性、決定性、燃料単調性 |
| `exec/`（検証済み） | [`verus/src/`](../verus/src) の `ir.rs`、`value.rs`、`check.rs`、`eval.rs`、`json.rs`、`pipeline.rs` | 型検査器、ランク検査、入力値の型検査、評価器、出力 JSON encoder。spec への適合を証明 |
| `exec/`（未検証） | [`crates/tlvm`](../crates/tlvm) | 字句、構文、診断付きの検査、入力 JSON の復号、CLI。回帰テストで確認 |

信頼している部品と未証明の義務は [`trust-boundary.toml`](../trust-boundary.toml) にまとめています。
この版は V1-A（外部 BigInt を信頼仮定とする版）です。parser、formatter、入力 JSON の復号などは
未検証なので、処理系全体を「完全に形式検証済み」とは呼びません。

## 実行の流れ

`tlvm run` は次の順に進みます。

1. 未検証の lexer・parser・検査器が source を受理し、診断を出す（crates/tlvm）。
2. 未検証の接着部分（`crates/tlvm/src/evaluator.rs`）が、型検査済みの AST を名前解決済みの中間表現
   `EProg` に下ろし、未検証の Tarjan 実装が作ったランク列を添える。入力値も検証済み部品の表現に移す。
3. 検証済みの `run_checked_json`（`verus/src/pipeline.rs`）が、
   - `check_prog` でプログラムが spec の整形式条件 `wf` を満たすことを確かめ（ランク列はここで検査されるので信頼不要）、
   - `has_type` で入力値が entry の入力型を持つことを確かめ、
   - 検証済み評価器で実行し、
   - 結果を検証済み encoder で正準 JSON にする。

`run_checked_json` が出力 o を返したなら、次が証明されています。

- プログラムは `wf` を満たす。
- ある値 w があり、w は spec の評価 `eval_entry` が返す唯一の結果で、entry の出力型を持つ。
- o は w の正準 JSON `enc(w)` で、出力型に沿って復号すると w に戻る。

評価器は step 上限で必ず停止すること（exec 関数の停止性）も Verus が検査しています。資源上限による
打ち切りは spec と無関係に起こりえます。step・AllocatedNodes・整数 bit 長の数え方は旧実装と同じで、
ランダムに生成した 2500 個の型付きプログラムで出力と計数が一致することを確かめました。

## exec 層（crates/tlvm）

| モジュール | 設計書 | 内容 |
|---|---|---|
| `lexer.rs` | §4.2、§18.1 | ASCII 字句、符号付き INT、数値境界、lexical-limits |
| `parser.rs` | §4.1、§10.3、§18.1b | 再帰下降 parser、parse Admission と structural guard、8回までの同期 recovery |
| `checker.rs` | §5、§6、§10.2、§18.1a | name → call-graph（DAG・rank）→ typecheck（ErrorType 回復、SemanticWork 計数）→ entry → warnings |
| `formatter.rs` | §4.3、§19.4 | 正準フォーマッタ、`ast_codec_v1` encoder |
| `strict_json.rs` | §9.3a | 文法／深さ → string scalar → 重複キーの段階順を守る strict JSON parser |
| `ast_codec.rs` | §19.2–19.3 | AST transport 検査と Admission 付き AST 構築 |
| `values.rs` | §9 | 値 JSON の復号（InputAdmission を含む decode 順序） |
| `evaluator.rs` | §7、§9 | 検証済み部品への接着（中間表現への変換、結果 envelope への写像） |
| `api.rs` | §9.1 | `compile`／`compile_ast`／`decode_input`／`run` と結果 envelope |
| `main.rs` | — | `tlvm check|run|fmt|ast` |

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

## Verus の部分（verus/）

| ファイル | 内容 |
|---|---|
| `spec.rs` | 型、値、名前解決済み AST、型付け `ty_expr`、整形式 `wf`、燃料付き評価 `eval` |
| `proof.rs` | 停止性・型安全性 `total`／`entry_total`、燃料単調性 `mono`、決定性 `entry_deterministic`、組込みの健全性 `apply_sound` |
| `bigstep.rs` | 燃料付き評価から導いた大ステップ規則（exec 評価器の証明に使う） |
| `bigint.rs` | 信頼する多倍長整数（num-bigint を `external_body` で包む。V1-A の信頼仮定） |
| `ir.rs` | exec の中間表現 `EProg` と spec への写像 |
| `value.rs` | exec の値（共有 cons セル）と spec の値への写像、環境 |
| `check.rs` | 型検査器 `ty_of`、整形式検査 `check_prog`（ランク証明書の検査を含む）、値の型検査 `has_type` |
| `eval.rs` | 評価器。返した値は spec でも同じ値に評価される（`evals_to`） |
| `json.rs` | 出力の正準 JSON：encoder の正しさ、往復性 `roundtrip`、型整合性 `dec_typed` |
| `pipeline.rs` | 中心定理つきの入口 `run_checked`／`run_checked_json` |

`assume` と `admit` は使っていません。`external_body` は `bigint.rs` の多倍長整数演算だけです。

### 検証の再現

Verus 0.2026.10.06（Rust 1.98.1 ツールチェイン）と Z3 4.16.0 で確認しました。

```sh
# Verus を source から build（https://github.com/verus-lang/verus の BUILD.md に従う）
git clone https://github.com/verus-lang/verus.git && cd verus/source
./tools/get-z3.sh             # または z3 4.16.0 を用意して VERUS_Z3_PATH を設定
source ../tools/activate && vargo build --release
# 検証（このリポジトリの verus/ で。cargo-verus は Verus の build に含まれる）
cd path/to/tolvemi/verus && cargo verus focus
# => verification results:: 137 verified, 0 errors
```

### まだ証明していないこと

- §11.2 の 1〜3：parser、formatter、名前解決（表面 AST から中間表現への変換）。
- §11.2 の 9 のうち入力側：strict JSON parser、重複キー拒否、入力値の復号。復号した値の型だけは検証済みの `has_type` で確かめています。
- 診断を出す検査器（crates/tlvm/src/checker.rs）そのもの。受理したプログラムは検証済みの `check_prog` で必ず検査し直すので、誤って受理しても実行されませんが、誤って拒否することは防げません。
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
- repair は推測で出さない規則に従い、全て `null` です。
- message は暫定の日本語テンプレートです。
- `E-CYCLE-CALL` の関数名関連情報は schema に関連情報キーが無いため `actual` と message に辞書順で入れています。
- host-policy は `tlvm-rust-host-v0`（評価の入れ子深さ上限 400000、評価スレッドのスタック 1 GiB）で、超過は `HostAborted` です。

## 未実装

- BLAKE3 を使う成果物 hash／structural_hash。`spec_version` は未確定なので、仕様結合 hash と再現 hash はどのみち発行しません。
- 上記の未証明義務、Skill、LLM 評価。
