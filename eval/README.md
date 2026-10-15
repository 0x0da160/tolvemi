# LLM 予備実験（フェーズ 2）

LPTL v1 を LLM が実際に書けるか、どこで失敗するかを測るための評価セットとハーネスです。
設計書 §12 の Surface モードと Repair モードを実装し、評価の事前登録（evaluation-protocol-v1 草案）のうち
オーナーの決定に依らない規則（最終候補の選び方、分母と失敗の分類、予算 B、統計、秘密の種）を `--protocol` の実行で使います。
**草案はまだ登録していないので、ここでの実行はどれも事前登録した正式実験（§12.5、G4）ではありません**。
ここでの結果から「LPTL は LLM に有利」とは主張せず、診断・Skill・言語拡張（`match_option` など）の優先順位を
決める材料にします。

## 中身

| パス | 内容 |
|---|---|
| [`SKILL.md`](SKILL.md) | モデルに渡す LPTL の説明（§12.2 の Skill）。最小文法、型、組込み、禁止事項、定石、主要診断、出力形式。コード例は全て `tlvm check` を通る |
| [`SKILL-nolet.md`](SKILL-nolet.md) | `lptl-nolet` の Skill。SKILL.md から `let` を除き、`let` を使う例を補助関数で書き直したもの（例は全て `tlvm check` を通り、`let` を含まない） |
| [`ast_output.md`](ast_output.md) | `ast` と `ast-schema` の出力形式の節。SKILL.md の出力形式の節と置き換え、`ast_codec_v1` の schema（`spec/lptl-v1/ast_codec_v1.schema.json`）を埋め込む |
| [`tasks/`](tasks/) | 60 問（うち 44〜60 は `category: hard`：2 つのリストの同時走査、整列、区間の併合など）。各ディレクトリに `task.json`（問題文・型・公開例 3 件）、`hidden.json`（隠しテスト 30 件）、`reference.tlvm`、`reference.py` |
| [`out_of_scope.json`](out_of_scope.json) | v1 で書けないため対象から外した 5 問と理由（Option の中身の取り出し、除算、整数からの反復） |
| [`manifest.json`](manifest.json) | SKILL.md、arm のプロンプトの部品（SKILL-nolet.md、ast_output.md）と全タスクのファイルの SHA-256。実行結果の `config.json` に記録する |
| [`harness.py`](harness.py) | 実験の実行と集計 |
| [`protocol.py`](protocol.py) | 草案の規則：必須の設定、予算 B、最終候補の選び方、失敗の分類と試験基盤の事故の判定表 |
| [`stats.py`](stats.py) | 草案 §4 の統計：Wilson 区間、課題単位の対応ブートストラップ、Holm 法 |
| [`primary_comparisons.json`](primary_comparisons.json) | 主要比較の一覧（登録の時にオーナーが列挙する。空のあいだは主要比較を主張しない） |
| [`check.py`](check.py) | 参照解が全テストを通ること、Skill と出力形式の例がコンパイルできること、manifest が最新であることを検査（CI で実行） |
| [`gen_tests.py`](gen_tests.py) | 参照解（Python）から公開例の期待値と隠しテストを生成（種はタスク ID から固定） |

タスクの分類は aggregate（集計）、filter、map、scan（前の要素に依存）、search、reorder（並べ替え）、index（位置）、
nested（入れ子のリスト）、option です。入力は一つの値で、複数の入力は `Pair` にまとめています。
v1.4 の `sum`（89-shapes_area、90-parse_config）は、直和型と `match`、`Result` を使うのが自然な問題です。
v1.5 の `hof`（91-top_scores、92-word_stats）は、`map`・`filter`・`any`・`all`・`find`・`sort_by` を使うのが自然な問題です。
v1.6 の `loop`（93-collatz_steps）は、上限つき反復 `loop` を使うのが自然な問題です。
v1.7 の `rec`（94-prefix_eval）は、`rec fn` の再帰（値と残りの token を返す再帰下降）を使うのが自然な問題です。
v1.8 の `div`（95-base_digits）は、整数の割り算 `div` を使うのが自然な問題です（`mod` と組にして桁を取り出す）。
v1.9 の `dict`（96-inventory）は、辞書 `Dict<K, V>` を使うのが自然な問題です（在庫の更新。入出力は組み込みの型で、辞書はプログラムの中で使う）。
v1.10 の `generic`（97-batches）は、型引数を取る補助関数（`chunk<T>`・`zip<A, B>`）を二つの要素の型で使うのが自然な問題です（名前と金額を同じ大きさの組に分け、両方を組み合わせて出力する）。
ユーザー定義の型は型の文字列だけでは宣言が分からないので、入出力の型は組み込みの型（`Result<T, E>` を含む）に限り、
直和型はプログラムの中で宣言して使います。plain JSON とハーネスの Python 側では `Result` を `{"ok": v}`／`{"err": e}` で表します。
隠しテストの期待値は Python の参照解で求め、LPTL の参照解が同じ答えを返すことを `check.py` で確かめています。

## arm

| arm | system | 修復時に返すもの（草案 §2a） |
|---|---|---|
| `lptl` | SKILL.md | tlvm の診断（`--human`：行・列、expected／found、repair）か、失敗した公開例 |
| `lptl-nodiag` | SKILL.md | 「拒否された」という一文だけか、失敗した公開例（診断の効果を見る対照） |
| `lptl-msg` | SKILL.md | 診断の message だけ（span、コード、修復ヒントなし）か、失敗した公開例 |
| `lptl-code` | SKILL.md | 診断のコードだけ（例：`E-TYPE-RETURN`）か、失敗した公開例 |
| `lptl-span` | SKILL.md | span（`行:列-行:列`）と expected、found だけか、失敗した公開例 |
| `lptl-noskill` | 言語名と出力形式だけ（SKILL.md を置かない） | `lptl` と同じ。課題文と公開例も同じ |
| `lptl-nolet` | SKILL-nolet.md | `lptl` と同じ。`let` を含むプログラムは tlvm に渡さず診断 `NoLet`（parse の拒否）で返す |
| `python` | Python の説明 | 例外のトレースバックか、失敗した公開例（同じタスク・同じテスト） |
| `ast` | SKILL.md の本文と ast_output.md（schema を含む） | `json` のコードブロックの AST を `compile_ast`（`tlvm check solution.json`）で検査し、`lptl` と同じ形の診断を返す |
| `ast-schema` | `ast` と同じ | `ast` と同じ。CLI の `--json-schema` で ast_codec_v1 の schema を渡し、構造化出力を AST として読む（claude-cli だけ） |
| `render` | SKILL.md（入力は正解 AST の JSON） | 修復はしない（一回だけ書かせる）。採点は、書かれた program の `tlvm ast` が正解 AST と一致するか |
| `gen-render` | SKILL.md（連結） | 連結 arm。`lptl` で一回生成し、その AST（`tlvm ast`）を `render` へ渡す。採点は render の出力が生成 AST と一致するか。`render` の行とは別に報告する |

公開例の失敗は、どの arm にも同じ形で返します。隠しテストの結果は修復に返しません。
草案 §2 の `python-restricted`（§2b の制限の定義が要る）、`lptl-nolist-builtins`（除く組込みと共通課題の作り直しが要る）、
別表記の arm（表記の定義と正準形への変換が要る）は、オーナーの決定がないので実装していません（指定すると理由を出して止まる）。
`lptl-nolet` と比べる共通課題は、参照解が `let` を使わない課題です（`check.py` が数を表示する。現在 99 題中 44 題）。
AST の transport には型宣言（レコード・直和型）、`match`、`import` がないので、`ast` の arm ではそれらを使わずに書くことになります。

1 回目が Surface モード、2 回目以降が Repair モードです。

### 最終候補と分母（草案 §3）

- 各回の候補を、受理の検査（`compile`、AST の arm は `compile_ast`、Python は読み込みと `solve` の有無）と公開例で検査する。
  公開例が全て通るか、回数の上限（予備実験は `--rounds`、protocol の実行は予算 B）で終わる
- 最終候補は、予算内に検証され受理された**最後の**候補を一件だけ選ぶ（`success_selected`）。受理された候補がなければ失敗。
  隠しテストは受理された候補ごとに走らせて記録するが（`rounds[].hidden_pass`）、選択には使わない。
  以前の `success_final`（最終回の候補の隠しテスト）は `hidden_last_round` に名前を変えて二次指標にした
- 各 episode の `outcome` は success か、失敗の分類（`generation_failure`、`rejected`（`outcome_detail` に parse・name・type・entry）、
  `invalid_input`、`resource_exceeded`、`no_candidate`、`budget_exceeded`、`wrong_answer`、`host_aborted`）か、試験基盤の事故
  （`infra_fault`）。どれも分母から落とさない。試験基盤の事故は `protocol.INFRA_TABLE` の固定の表で判定し（tlvm の InternalFault・
  異常終了、CLI の時間切れ・`is_error`、API の通信と HTTP エラーなど）、件数と episode ID を `summary` に出す。
  episode をそこで止め、どの arm も再試行しない（protocol の実行では CLI の時間切れも呼び直さない）

### 予算 B（草案 §5）

B は四成分（累積の論理入力 tokens、出力 tokens、モデル要求回数、可視検証の呼び出し回数）の上限で、全成分が上限以内（ちょうど上限は可）
のときだけ予算内です。論理入力 tokens はキャッシュの読み・書きを含み、内訳は `budget.input_breakdown` に別に記録します。
要求の前に、要求回数と入力 tokens の見積り（初回は文の bytes ÷ 2.0、二回目からは直前の要求の実測と増えた文の bytes ÷ 2.0）を検査し、超えるなら要求を出さずに既存の
候補で終えます。CLI の中の再試行（構造化出力の検証など）は `num_turns` で要求回数に数えます。出力 tokens は CLI では事前に抑えられないので、
実測の累積が上限を超えた episode は、それより前に正しい候補があっても `budget_exceeded` です（API の backend では残りを `max_tokens` にする）。
可視検証は、候補ごとに受理の検査 1 回と、受理されたら公開例ごとに入力の読み込みと実行の 2 回を数えます（設計書 §12.5）。
公開例を走らせる余地がなければ受理の検査だけをし、受理されたらそこで終えます。隠しテストは B の外です。

### 統計（草案 §4）

`summary.json` の主指標は arm ごとの `success_selected` とその Wilson 区間、課題単位の対応ブートストラップ（10,000 回、95% の
パーセンタイル区間。全 arm に同じ再標本の課題番号を使い、乱数の種は課題 ID の集合から決める）です。主要比較は
`primary_comparisons.json` に列挙したものだけを、ブートストラップの p 値（区間の反転）と Holm 法で扱います。Holm の族は一覧の
全比較で、実行で計算できなかった比較は p = 1.0 として族に残します（そのときは主要比較を主張しません）。一覧が空なら主要比較を
主張しません。二次指標（Success@1、`hidden_last_round`、修復成功、受理率、費用、失敗の分類の内訳）は `secondary` に別名で出します。

## 実行

```sh
cargo build --release

# API を使わずに経路を確かめる（参照解をそのまま返す）
python3 eval/harness.py --backend oracle --model oracle

# サブスクリプションで実行（ログイン済みの Claude Code の claude -p を使う。API キー不要）
python3 eval/harness.py --backend claude-cli --model <モデル ID> --effort high --arms lptl,python

# Claude API で実行（pip install 'anthropic>=1.11' と ANTHROPIC_API_KEY などの認証が必要）
python3 eval/harness.py --model <モデル ID> --effort high --arms lptl,lptl-nodiag,python --rounds 3 --repeats 1
```

`--model` は必須で、既定値はありません（モデルの版の識別子をリポジトリに書かないため）。oracle は値を使いません。

結果は `eval/runs/<run-id>/` に `config.json`、`episodes.jsonl`（全回の候補コードと採点）、`summary.json`、
`summary.md` として出ます（`eval/runs/` は git の管理外）。99 問 × 3 arm × 最大 3 回で、呼び出しは最大 891 回です。`--category hard` で難しい問題だけに絞れます。
`summary.md` と `summary.json` にはモデルの版の識別子を書きません（`config.json` と `episodes.jsonl` にだけ記録します）。

### protocol の実行

`--protocol CONFIG.json` を付けると、事前登録の設定を読んで実行します。設定にはオーナーが決める五つの項目が**すべて必要**で、
既定値はありません。一つでも欠けるか不正なら、何も実行せずに止まります（fail closed）。

```json
{
  "hidden_set_location": "<秘密の最終評価の課題を置くディレクトリ>",
  "repeats": "<反復数 K（1 以上の整数）>",
  "budget": {
    "input_tokens": "<整数>", "output_tokens": "<整数>", "requests": "<整数>", "verification_calls": "<整数>"
  },
  "cli_limits": "<cli-defaults（claude -p の既定値のまま、限界として公開）か api-fixed（API backend で固定）>",
  "publication_scope": "<summary-only か summary-and-raw>"
}
```

protocol の実行では、`--model` に加えて `--effort` も明示します（値は `config.json` にだけ記録）。`--repeats` と `--rounds` は使えません
（K は設定から、回数は B から決まる）。`cli_limits` が `cli-defaults` なら `--backend claude-cli`、`api-fixed` なら `--backend anthropic` です
（`oracle` はどちらでも空回しに使える）。server-side fallback は使いません。実行のディレクトリには、公開してよいファイルの一覧
`publish.json`（`publication_scope` による）も出ます。秘密の課題集合の実行では、生データ（`config.json`、`episodes.jsonl`）は
秘密の課題を明かすので、範囲によらず一覧に入れません。`config.json` には処理系の commit と、未コミットの変更の有無（`git.dirty`）を記録します。

```sh
python3 eval/harness.py --protocol CONFIG.json --backend claude-cli --model MODEL --effort EFFORT --arms lptl,python
LPTL_EVAL_HIDDEN_SEED=... python3 eval/harness.py --protocol CONFIG.json --task-set secret ...
```

隠しテストの種は二つです。公開再現の課題集合（`eval/tasks`）はタスク ID の SHA-256 から決まり、誰でも `gen_tests.py` で
同じ `hidden.json` を作り直せます。秘密の最終評価の課題集合（`--task-set secret`、設定の `hidden_set_location`）は、環境変数
`LPTL_EVAL_HIDDEN_SEED` の秘密の値とタスク ID の HMAC-SHA256 から隠しテストをその場で作り、ファイルには書きません。
環境変数がなければ読みません。種の値はリポジトリにも実行の記録にも書きません。

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
- 繰り返し数・予算・最終評価の規模・採否の閾値は決めていません（§12.5。草案 §9 でオーナーが決める）。
- `ast-schema` の `--json-schema` は、CLI が StructuredOutput というツールの入力を schema で検証し、合わなければモデルに出し直させる
  仕組みです。ast_codec_v1 は再帰する schema なので、生成の段階での制約（constrained decoding）ではありません（この環境の CLI の
  実装で確認。モデルは呼んでいないので、`--tools ""` と併せたときに動くかは、登録の前に一度だけ確かめる）。
- `lptl-msg` が返す message は tlvm の診断文そのもの（日本語）です。
