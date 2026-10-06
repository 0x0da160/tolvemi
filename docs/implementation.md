# Tolvemi 処理系（Rust／Verus）について

LPTL 設計方針 v1（[`spec/lptl-v1/LPTL_design_v1.md`](../spec/lptl-v1/LPTL_design_v1.md)）§11 の層分離に沿って、
実行可能な処理系を Rust で、数学的仕様と証明を Verus で書いています。

| 設計書の層 | 場所 | 検証 |
|---|---|---|
| `exec/` | [`crates/tlvm`](../crates/tlvm) | 通常の Rust。Verus の検証対象外で、回帰テストで確認 |
| `spec/` | [`verus/src/spec.rs`](../verus/src/spec.rs) | 型、値、名前解決済み AST、型付け、呼出しランク、燃料付き評価 |
| `proof/` | [`verus/src/proof.rs`](../verus/src/proof.rs) | 停止性、型安全性、決定性、燃料単調性 |

信頼している部品と未証明の義務は [`trust-boundary.toml`](../trust-boundary.toml) にまとめています。
この版は V1-A（外部 BigInt を信頼仮定とする版）で、exec 層と spec 層の精緻化は未証明です。
したがって処理系全体を「完全に形式検証済み」とは呼びません。

## exec 層（crates/tlvm）

| モジュール | 設計書 | 内容 |
|---|---|---|
| `lexer.rs` | §4.2、§18.1 | ASCII 字句、符号付き INT、数値境界、lexical-limits |
| `parser.rs` | §4.1、§10.3、§18.1b | 再帰下降 parser、parse Admission と structural guard、8回までの同期 recovery |
| `checker.rs` | §5、§6、§10.2、§18.1a | name → call-graph（DAG・rank）→ typecheck（ErrorType 回復、SemanticWork 計数）→ entry → warnings |
| `formatter.rs` | §4.3、§19.4 | 正準フォーマッタ、`ast_codec_v1` encoder |
| `strict_json.rs` | §9.3a | 文法／深さ → string scalar → 重複キーの段階順を守る strict JSON parser |
| `ast_codec.rs` | §19.2–19.3 | AST transport 検査と Admission 付き AST 構築 |
| `values.rs` | §9 | 値 JSON codec（InputAdmission を含む decode 順序）。深い値も反復で解放・encode |
| `evaluator.rs` | §7、§8.4、§18.3 | 参照 step・AllocatedNodeCount・整数 bit 長を計数する評価器（BigInt は num-bigint） |
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

診断は一行一 JSON object で stderr、結果は stdout に出ます。

## spec 層と proof 層（verus/）

`spec.rs` は名前解決後のプログラムを対象にします。変数と binder は `nat`、関数は `Prog::funcs` の添字で、
呼出しグラフが DAG であることは「呼出し先のランクは呼出し元より真に小さい」という型付け条件で表します。
評価 `eval` は燃料付きで、燃料切れ（`OutOfFuel`）と型の行き詰まり（`Stuck`）を区別します。

`proof.rs` で証明している主な定理：

- `entry_total`：整形式（`wf`）プログラムの entry に入力型の値を与えると、ある燃料で必ず `Done(w)` になり、`w` は出力型を持つ（停止性と型安全性）。
- `total`：型の付いた式は、型環境に適合する実行時環境で必ず値に評価される（ランク、式の辞書式帰納法）。
- `mono`：燃料を増やしても `OutOfFuel` 以外の結果は変わらない（§11.2 の 7）。
- `eval_deterministic`／`entry_deterministic`：結果は燃料に依らず一意。
- `apply_sound`：組込みの型規則と意味が整合する。`mod_bounds`：正の除数で `0 <= x mod y < y`。
- `example_wf`：`wf` が空虚でない具体例。

`assume`、`external_body`、`admit` は使っていません。

### 検証の再現

Verus 0.2026.10.06（Rust 1.98.1 ツールチェイン）と Z3 4.16.0 で確認しました。

```sh
# Verus を source から build（https://github.com/verus-lang/verus の BUILD.md に従う）
git clone https://github.com/verus-lang/verus.git && cd verus/source
./tools/get-z3.sh             # または z3 4.16.0 を用意して VERUS_Z3_PATH を設定
source ../tools/activate && vargo build --release
# 検証（このリポジトリの root から）
path/to/verus --crate-type=lib verus/src/lib.rs
# => verification results:: 25 verified, 0 errors
```

### まだ証明していないこと

§11.2 の 1〜5 と 8〜10（parser、formatter、resolver、exec 型検査器と DAG 検査器の正しさ、
exec 評価器の spec 評価への適合、JSON codec、結果 envelope の分離）は未証明です。
spec 層は資源上限（steps、AllocatedNodes、IntegerBits）を持たず、燃料は停止性のための抽象です。
V1-B／V1-C（BigInt と算術の検証）にも未着手です。

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
