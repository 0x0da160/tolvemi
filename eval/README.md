# LLM 予備実験（フェーズ 2）

LPTL v1 を LLM が実際に書けるか、どこで失敗するかを測るための評価セットとハーネスです。
設計書 §12 の Surface モードと Repair モードの最小版で、**事前登録した正式実験（§12.5、G4）ではありません**。
ここでの結果から「LPTL は LLM に有利」とは主張せず、診断・Skill・言語拡張（`match_option` など）の優先順位を
決める材料にします。

## 中身

| パス | 内容 |
|---|---|
| [`SKILL.md`](SKILL.md) | モデルに渡す LPTL の説明（§12.2 の Skill）。最小文法、型、組込み、禁止事項、定石、主要診断、出力形式。コード例は全て `tlvm check` を通る |
| [`tasks/`](tasks/) | 43 問。各ディレクトリに `task.json`（問題文・型・公開例 3 件）、`hidden.json`（隠しテスト 30 件）、`reference.tlvm`、`reference.py` |
| [`out_of_scope.json`](out_of_scope.json) | v1 で書けないため対象から外した 5 問と理由（Option の中身の取り出し、除算、整数からの反復） |
| [`manifest.json`](manifest.json) | SKILL.md と全タスクのファイルの SHA-256。実行結果の `config.json` に記録する |
| [`harness.py`](harness.py) | 実験の実行と集計 |
| [`check.py`](check.py) | 参照解が全テストを通ること、SKILL.md の例がコンパイルできること、manifest が最新であることを検査（CI で実行） |
| [`gen_tests.py`](gen_tests.py) | 参照解（Python）から公開例の期待値と隠しテストを生成（種はタスク ID から固定） |

タスクの分類は aggregate（集計）、filter、map、scan（前の要素に依存）、search、reorder（並べ替え）、index（位置）、
nested（入れ子のリスト）、option です。入力は一つの値で、複数の入力は `Pair` にまとめています。
隠しテストの期待値は Python の参照解で求め、LPTL の参照解が同じ答えを返すことを `check.py` で確かめています。

## arm

| arm | system | 修復時に返すもの |
|---|---|---|
| `lptl` | SKILL.md | tlvm の診断（`--human`：行・列、expected／found、repair）か、失敗した公開例 |
| `lptl-nodiag` | SKILL.md | 「拒否された」という一文だけか、失敗した公開例（診断の効果を見る対照） |
| `python` | Python の説明 | 例外のトレースバックか、失敗した公開例（同じタスク・同じテスト） |

1 回目が Surface モード、2 回目以降が Repair モードです。公開例が全て通るか `--rounds` 回に達したら終わり、
各回の候補を隠しテストでも採点します。報告するのは Success@1（初回の候補が隠しテストを全て通した割合）と
Success@R（最終回）、その 95% 信頼区間（Wilson）、初回のコンパイル失敗数、失敗した回の診断コードの分布、トークン数です。

## 実行

```sh
cargo build --release

# API を使わずに経路を確かめる（参照解をそのまま返す）
python3 eval/harness.py --backend oracle

# サブスクリプションで実行（ログイン済みの Claude Code の claude -p を使う。API キー不要）
python3 eval/harness.py --backend claude-cli --model claude-opus-5-5 --effort high --arms lptl,python

# Claude API で実行（pip install 'anthropic>=1.11' と ANTHROPIC_API_KEY などの認証が必要）
python3 eval/harness.py --model claude-opus-5-5 --effort high --arms lptl,lptl-nodiag,python --rounds 3 --repeats 1
```

結果は `eval/runs/<run-id>/` に `config.json`、`episodes.jsonl`（全回の候補コードと採点）、`summary.json`、
`summary.md` として出ます（`eval/runs/` は git の管理外）。43 問 × 3 arm × 最大 3 回で、API 呼び出しは最大 387 回です。

`claude-cli` はツールを無効にし、設定・MCP・CLAUDE.md を読まずに空の一時ディレクトリで動かすので、
モデルは参照解や隠しテストを見られません。CLI は 1 回の呼び出しが 1 往復なので、修復の回ではそれまでの会話を
1 つのプロンプトに書き起こして渡します（思考は引き継がれません）。Claude Code が system prompt に短い定型文を
足すため、API で回した結果とは条件が少し違います。比べるときは同じ backend どうしで比べてください。

`anthropic` backend では、既定で、安全分類器が回答を断ったときに推奨モデルで続ける server-side fallback を有効にしています。
別のモデルが答えた回は episode の `fallback` に記録され、`summary.md` に件数が出ます。比較を厳密にするなら
`--no-fallback` を付けてください。

## 解釈の注意

- SKILL.md の例のうち設計書 §13 の 2 例は、`count_even`（偶数の個数）と `filter_greater`（閾値より大きい要素）に近い
  解法を含みます。§12.2 は最終評価の解法・近傍例を Skill に含めないことを求めているので、正式実験ではタスクを分け直します。
- Python 対照群は「同じ問題を Python で解かせた」だけで、言語・tooling・事前知識の総合差です（§12.4 の通り、
  Python の物理時間と LPTL の参照 step は比べません）。
- 繰り返し数・最終評価の規模・採否の閾値は決めていません（§12.5）。
