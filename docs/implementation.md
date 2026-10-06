# Tolvemi Python 参照処理系（試作）について

`tolvemi/` は LPTL 設計方針 v1（[`spec/lptl-v1/LPTL_design_v1.md`](../spec/lptl-v1/LPTL_design_v1.md)）の
Python 試作処理系です。標準ライブラリだけで動きます（Python 3.11 以上）。
Rust/Verus の `spec` 層ではなく、G0〜G2 のどのゲートも満たしたとは主張しません。

## 構成

| モジュール | 設計書 | 内容 |
|---|---|---|
| `lexer.py` | §4.2、§18.1 | ASCII 字句、符号付き INT、数値境界、lexical-limits |
| `parser.py` | §4.1、§10.3、§18.1b | 再帰下降 parser、parse Admission と structural guard、8回までの同期 recovery |
| `checker.py` | §5、§6、§10.2、§18.1a | name → call-graph（DAG・rank）→ typecheck（ErrorType 回復、SemanticWork 計数）→ entry → warnings |
| `formatter.py` | §4.3、§19.4 | 正準フォーマッタ、`ast_codec_v1` encoder |
| `strict_json.py` | §9.3a | 文法／深さ → string scalar → 重複キーの段階順を守る strict JSON parser |
| `ast_codec.py` | §19.2–19.3 | AST transport 検査と Admission 付き AST 構築 |
| `values.py` | §9 | 値 JSON codec（InputAdmission を含む decode 順序） |
| `evaluator.py` | §7、§8.4、§18.3 | 参照 step・AllocatedNodeCount・整数 bit 長を計数する評価器 |
| `api.py` | §9.1 | `compile`／`compile_ast`／`decode_input`／`run` と結果 envelope |
| `cli.py` | — | `tlvm check|run|fmt|ast` |

## 使い方

```sh
python3 -m tolvemi check examples/sum_even.tlvm
python3 -m tolvemi run examples/sum_even.tlvm '{"tag":"list","items":[{"tag":"int","value":"2"},{"tag":"int","value":"3"}]}' --stats
python3 -m tolvemi fmt examples/positive_values.tlvm
python3 -m tolvemi ast examples/sum_even.tlvm
python3 -m tolvemi run examples/identity.json '{"tag":"int","value":"-42"}'
python3 -m unittest discover -s tests -t .
```

`pip install -e .` で `tlvm` コマンドとしても使えます。診断は一行一 JSON object で stderr、結果は stdout に出ます。

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
- host-policy は Python 実装用の `tolvemi-python-host-v0`（評価の入れ子深さ上限）で、超過は `HostAborted` です。

## 未実装

- BLAKE3 を使う成果物 hash／structural_hash（標準ライブラリに BLAKE3 が無いため）。`spec_version` は未確定なので、仕様結合 hash と再現 hash はどのみち発行しません。
- Verus による証明、Skill、LLM 評価。
