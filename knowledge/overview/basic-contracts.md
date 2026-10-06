---
type: Design Contract
title: v1 の基本契約
description: 設計書 §1 が定める10項目の基本契約と、§16 の契約索引による主節への対応。
tags: [lptl, contracts, index]
status: draft
generated: { by: claude-code/2026-10-06, at: 2026-10-06T16:00:00Z }
sources:
  - id: lptl-design
    resource: ../../spec/lptl-v1/LPTL_design_v1.md
    title: LLM向け純粋・全域言語：設計方針 v1（§1、§16）
    last_modified: 2026-10-01T00:00:00Z
---

# 10項目の基本契約

1. entry は parse 成功後に構文個数を収集する。未知 entry は name phase、欠落・重複・引数数は entry phase とし、name 失敗時は entry phase を実行しない。→ [entry と到達可能性](/language/entry-and-reachability.md)
2. トップレベル本体の終端は、完成した一つの expr の直後の `fn`、`entry`、EOF に限定する。改行なしの宣言列も受理する。→ [文法](/language/grammar.md)
3. DAG 検査は `call-graph` phase で行い、静的資源検査から分離する。→ [呼出しグラフ](/language/call-graph.md)
4. 静的上限は取得できる最初の時点で検査する。上限超過は後続を停止し、未実行の検査を成功とは扱わない。→ [診断パイプライン](/diagnostics/pipeline.md)
5. arity は typecheck phase で検査し、全ての実引数式を検査するが、arity 不一致の呼出しでは期待引数との型比較を抑制する。→ [型規則](/language/typing.md)
6. `none[Foo]` は閉じた型文法への不適合として `E-PARSE-EXPECTED-TYPE` とする。
7. bytes API、値 codec、AST 専用 codec、repair schema、recovery 終了規則、資源計数を契約として定義する。
8. `Pair<A, B>` の二成分は独立した型である。→ [値 JSON codec](/api/value-json-codec.md)
9. `fold` 内の呼出しも呼出しグラフに含め、関数 rank と反復長の帰納を接続する。→ [停止性の証明構造](/guarantees/termination-proof.md)
10. `match_option`、`option_fold`、`uncons` は本コアに含めない。→ [将来拡張](/future/option-elimination.md)[^lptl-design]

# 契約索引

| 項目 | v1 の契約 | 設計書の主節 |
|---|---|---|
| entry 欠落・未知・重複 | 個数収集と診断を分離、name 失敗時は entry 停止 | 5.2、10.2 |
| 宣言境界 | 完成 expr の直後の fn／entry／EOF。改行不要 | 4.1 |
| static と DAG の検査分離 | call-graph と各 limits phase に分離 | 10.2 |
| 上限超過後の継続 | 最初の cutoff で後続を全停止、既存診断は保持 | 10.2 |
| 通常 call の arity | typecheck、実引数を検査、引数型との比較は抑制 | 6.1 |
| none[Foo] | E-PARSE-EXPECTED-TYPE | 6.1 |
| API の bytes 境界 | source_bytes／json_bytes／ast_json_bytes | 9.1 |
| AST mode | schema、キー、名前、span、共通検査を固定 | 19 |
| fold 停止証明 | 本体 call を DAG に含め rank 帰納と接続 | 8.2 |
| Pair 表記 | 二つの独立した型パラメータ | 3.1 |
| JSON 正準性 | 実 JSON 例、引用キー順、全体 first-error | 9.2–9.4 |
| repair | 完全な列挙・必須キー、非保証 hint | 10.1 |
| recovery | 8回後の追加 error で専用コード、停止 | 10.3 |
| concat／none 計数 | 一時参照スタック、m セル、none singleton | 8.4、18 |
| 実装・証明の状態 | 完了とは主張せず、出荷ゲートで確認 | 11、15、20 |
| Option 拡張 | 本コア対象外。将来の独立拡張として審査 | 14 |

[^lptl-design]: LLM向け純粋・全域言語：設計方針 v1
