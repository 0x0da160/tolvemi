---
type: Test Suite
title: 必須回帰テスト
description: LPTL v1 設計書 §20.1 の 69 行を既存テストと補助モデルへ対応付けた表。対応・部分・未対応・モデルのみの別と、残りの扱いを示す（2026-10-14 時点）。
tags: [lptl, conformance, tests, traceability]
status: draft
generated: { by: claude-code/2026-10-14, at: 2026-10-14T00:00:00Z }
sources:
  - id: lptl-design
    resource: ../../spec/lptl-v1/LPTL_design_v1.md
    title: LLM向け純粋・全域言語：設計方針 v1（§20.1）
    last_modified: 2026-10-01T00:00:00Z
---

# 位置付け

- 行番号は設計書 §20.1 の表の出現順（1〜69）。
- 「テスト」は `crates/tlvm/tests/` の Rust テスト（関数名で示す。`regression.rs` の関数を指す場合は省略）。「モデル」は `spec/lptl-v1/v1_check_inputs.json` の case（`v1-C0xx` の下 3 桁で示す）。モデルは仕様の補助モデルの検査であり、処理系の検査ではない（[限定検査](limited-checks.md)）。
- 2026-10-14 時点の内訳：対応 49、部分 9、未対応 3、モデルのみ 8（合計 69）。
- 部分・未対応・モデルのみの行は G0 の未達項目である（[出荷ゲート](../overview/status-and-gates.md)）。[^lptl-design]

# 対応表

| 行 | 要件（要約） | 状態 | 根拠 | 残り |
|---|---|---|---|---|
| 1 | entry がない → E-ENTRY-MISSING | 対応 | `entry_rules` | - |
| 2 | entry 名が未定義 → E-ENTRY-UNKNOWN（DUPLICATE なし） | 対応 | `entry_rules` | - |
| 3 | entry が二重 → E-ENTRY-DUPLICATE 一件 | 対応 | `entry_rules` | - |
| 4 | entry の引数個数違い → E-ENTRY-ARITY | 対応 | `entry_rules` | - |
| 5 | 未使用 fn → Accepted と W-UNUSED-FUNCTION | 対応 | `unused_function_warning` | - |
| 6 | 余分な token → E-PARSE-UNEXPECTED-TOKEN | 対応 | `parse_errors` | - |
| 7 | `none[…]` → E-PARSE-EXPECTED-TOKEN | 対応 | `option_elim.rs` | - |
| 8 | `f(1,true)`（既知の `f(Int)`）→ E-ARITY-USER のみ | 対応 | `types_arity_dag` | - |
| 9 | `add(1,true,0)` → E-ARITY-BUILTIN のみ | 対応 | `types_arity_dag`；モデル C041 | - |
| 10 | `f(1,fst(unit))` で E-ARITY-USER と E-TYPE-FST-ARG が独立 | 対応 | `types_arity_dag` | - |
| 11 | fold 内で現在の関数を呼ぶ → E-CYCLE-CALL | 対応 | `types_arity_dag` | - |
| 12 | token 上限 L と L+1 の境界 | 対応 | `lexical_limits` | - |
| 13 | typecheck 中の semantic cutoff → entry と warnings を実行しない | 対応 | `semantic_limits` | - |
| 14 | recovery 8 回の後の error → E-PARSE-RECOVERY-LIMIT で停止 | 対応 | `recovery`；モデル C049 | - |
| 15 | AST object の重複 key → E-AST-DUPLICATE-KEY | 対応 | `ast_transport` | - |
| 16 | AST に `inferred_type` → E-AST-UNKNOWN-FIELD | 対応 | `ast_transport` | - |
| 17 | AST の `var.name="if"` → E-AST-IDENTIFIER | 対応 | `ast_transport` | - |
| 18 | 識別子末尾の LF・CR・CRLF・tab | 対応 | `ast_transport`（var）；`rows_20_1_boundaries`（fn・entry・param・let・fold・callee）；モデル C002, C006–C008 | - |
| 19 | 識別子の前後空白・非 ASCII・U+2028/2029 | 対応 | `ast_transport`（var）；モデル C009–C013（fn） | U+2029 と fn 名の実装テストなし |
| 20 | int の value 末尾の制御文字・空白・U+2028/2029 | 対応 | `rows_20_1_boundaries`；モデル C003, C017–C023 | - |
| 21 | int の `"-0"`・`"01"`・`"+1"` → E-AST-INTEGER、JSON number → E-AST-FIELD-TYPE | 対応 | `ast_transport`；モデル C024–C027 | - |
| 22 | 識別子 `"x"` は受理、`"x\n"` は拒否 | 対応 | `ast_transport` | - |
| 23 | `declarations: []` → E-ENTRY-MISSING | 対応 | `ast_transport` | - |
| 24 | AST fold の acc と item が同名 → binder 重複 | 対応 | `rows_20_1_boundaries` | - |
| 25 | AST callee `uncons` の組込み解決と個数検査（v1.1） | 対応 | `ast_transport`、`rows_20_1_boundaries`；`option_elim.rs` | - |
| 26 | AST call の余分な実引数 → transport は通り E-ARITY-USER | 対応 | `rows_20_1_boundaries`；`types_arity_dag`（source） | - |
| 27 | AST some に value がない → E-AST-MISSING-FIELD | 対応 | `ast_transport` | - |
| 28 | input int の value が JSON number → E-INPUT-*、Int として受理しない | 対応 | `input_decode`；モデル C063 | - |
| 29 | decode 後の同じ key（escape 違い）→ duplicate 拒否 | 部分 | `rows_20_1_boundaries`（AST のみ）；モデル C057, C073, C080 | input 側の実装テストなし |
| 30 | concat 長さ m,n → 結果 m+n、追加 cons は m | 対応 | `builtins_and_sharing`（割当数） | 共有は割当数からの推定 |
| 31 | none の反復評価 → none 由来の割当 0 | 部分 | `builtins_and_sharing`（none リテラル 2 個）；`counting.rs` の `none_repeated_in_a_fold_allocates_nothing`（fold の反復で割当 0） | loop 内の反復を未検査 |
| 32 | let の値を pair の両側で参照 → 束縛 1 回、pair 1 ノード | 対応 | `builtins_and_sharing`（割当数） | 束縛 1 回は割当数からの推定 |
| 33 | bytes 上限超過かつ不正 UTF-8 → bytes 優先 | 部分 | `lexical_limits`、`ast_transport`（AST）；`tooling.rs`（input は有効 UTF-8 のみ） | input 側の不正 UTF-8 なし |
| 34 | error 候補 33 件 → 通常 31 件＋E-DIAG-LIMIT | 部分 | `rows_20_1_boundaries`（33 件）、`error_limit`（40 件） | 一件 cutoff の特別選択を未検査 |
| 35 | host の参照スロット・frame 上限 → HostAborted | 対応 | `host_ref_slots`；`rec.rs`（eval-depth） | stack_bytes 超過は未検査 |
| 36 | Steps・AllocatedNodes・IntegerBits・OutputBytes 超過 → ResourceExhausted | 対応 | `resource_exhausted` | - |
| 37 | 型共有・interning・比較 cache の有無 → 同じ trace と仕事量 | 部分 | `sharing_replays_cached_comparisons`、`sharing_keeps_trace_work_and_cutoff`（`tests/sharing.rs`） | interning は実装していない。Ty の Arc 共有は従来のまま |
| 38 | add 例、SemanticWork 9 と 8 | 対応 | `semantic_work_trace_fixtures`、`semantic_limits`；モデル C036, C042, C043 | - |
| 39 | 型深さと SemanticWork の同時超過 → SEMANTIC-TYPE-DEPTH 優先 | 対応 | `semantic_limits` | 同時超過の例は一件のみ |
| 40 | 合法な param `{"tag":"int"}` は tag 検査なしで受理 | 対応 | `ast_transport` | - |
| 41 | 合法な param に tag を追加 → E-AST-UNKNOWN-FIELD | 対応 | `ast_transport`；モデル C030–C031 | - |
| 42 | fn 名 `"if"` と数値 body → E-AST-FIELD-TYPE（名前の内容は後） | 対応 | `ast_transport`；モデル C032 | - |
| 43 | AST の必須キー複数欠落・余分キー複数の選択順 | 対応 | `rows_20_1_boundaries` | - |
| 44 | add(1,true,0)、SemanticWork 0 と 1 の cutoff 位置 | 対応 | `semantic_limits`；モデル C040, C041 | - |
| 45 | some の子 unit が budget 超過 → AST-NODES が閉じ括弧欠落より先 | 対応 | `structural_limits`；モデル C044, C045 | - |
| 46 | expr 位置の fn の parse error 後の同期（一回） | 対応 | `recovery`；モデル C046, C047 | - |
| 47 | 未消費 token が EOF → 停止、RECOVERY-LIMIT を加算しない | 対応 | `parse_errors`；モデル C048 | - |
| 48 | 同期で飛ばす token の node 開始 keyword → Admission 抑止、budget 非リセット | 対応 | `recovery_admission`（診断の node_index で Admission の位置を読む） | - |
| 49 | 524,276 字名の formatter 境界、再投入拒否 | 対応 | `formatter_boundary_fixture`；モデル C051 | - |
| 50 | Int `10^4096`：抽象往復は成立、標準 input は桁上限で拒否 | 対応 | `input_decode`；モデル C052 | 抽象往復は証明対象 |
| 51 | 3 失敗後 1 成功の episode、S=1、分母に 4 試行を加えない | モデルのみ | モデル C053；`eval/test_harness.py`（1 失敗後の成功） | 実装テストなし |
| 52 | 最終候補の隠しテスト不合格 → episode 失敗、選び直さない | モデルのみ | モデル C054 | 実装テストなし |
| 53 | 予算 B の一成分ちょうど上限・次操作禁止 → 既存の Accepted 候補を選択 | モデルのみ | モデル C082–C085 | 実装テストなし |
| 54 | Render 正解 AST とモデル AST → 主 Render と連結 arm を別報告 | 対応 | `eval/test_harness.py` の `test_render_scores_the_ast`、`test_gen_render_reports_generation_and_render_apart`（別行の報告） | 実測は G4 で行う。ここではオラクルと偽のモデルで経路だけを確かめた |
| 55 | input Pair の左に余分な key → E-INPUT-UNKNOWN-FIELD（子の Admission 前） | 対応 | `input_decode`；モデル C058 | - |
| 56 | input Pair の深さ上限 1、子 Unit → E-LIMIT-INPUT-VALUE-DEPTH | 対応 | `input_decode`；モデル C059 | - |
| 57 | 値の深さと node 数の同時超過 → VALUE-DEPTH 優先 | モデルのみ | モデル C060 | 既定の上限では同時超過にならない |
| 58 | Int 正規形違反と node 超過 → VALUE-NODES が先 | 対応 | `input_decode`；モデル C061 | - |
| 59 | Int 正規形違反と桁上限超過 → E-INPUT-INTEGER が先 | 対応 | `input_decode`；モデル C062 | - |
| 60 | Int の value が number、node 上限 0 → E-INPUT-FIELD-TYPE が先 | 対応 | `input_decode`；モデル C063 | - |
| 61 | 不対 surrogate と重複・unknown key → STRING-SCALAR が先 | 部分 | `rows_20_1_boundaries`（AST）、`strings.rs`；モデル C071–C077, C081 | span 未検査。input の組合せはモデルのみ |
| 62 | 正しい surrogate escape の対 → scalar 検査を通る | 部分 | `rows_20_1_boundaries`（AST）、`strings.rs`；モデル C074, C078 | input 側はモデルのみ |
| 63 | input の重複 key と root tag 違反 → E-INPUT-DUPLICATE-KEY が先 | 対応 | `input_decode`；モデル C073 | - |
| 64 | Accepted あり、予算ちょうど上限・次操作禁止 → S=1 | モデルのみ | モデル C082–C084 | 実装テストなし |
| 65 | 予算内で停止、Accepted なし → no_accepted_candidate、S=0 | モデルのみ | モデル C085 | 実装テストなし |
| 66 | 実測 usage が一成分でも超過 → budget_exceeded、S=0 | モデルのみ | モデル C086, C056 | 実装テストなし |
| 67 | 予算 vector の欠落成分・長さ不一致 → 計測不正 | 部分 | モデル C087（長さ 3）、C088（負値） | 計測不正の分岐（`v1_limited_checks.py` の `budget_end_model`）の case がない |
| 68 | 同じ AST、異なる spec_version → preimage が異なる | 部分 | モデル C089, C090 | crate に hash の実装がない |
| 69 | spec_version 未確定 → 正式 hash を発行しない | モデルのみ | モデル C091, C092 | crate に hash の実装がない |

# 残りの扱い（判断が要る行）

判断カード（§20.1 の 35・37・54）の回答は「三行とも実装」である（2026-10-14）。それぞれ次のとおり実装した。残りは下の三点だけである。

- 行 35：`HostPolicy.max_ref_slots` と、検証済み評価器の `Limits.max_slots`・`Stop::HostSlots` を実装した。環境の束縛を積む直前に検査し、超過は `HostAborted("ref-slots")` とする。ResourceExhausted へは統合しない。stack_bytes の超過は未検査のまま残る。
- 行 37：型比較の cache（`TypeSharing::On`）を実装した。cache は両型の Arc の address を鍵にし、再照合では覚えた論理イベント列を再生するので、trace・仕事量・cutoff は Off と同じになる。interning（構造による正準化）は実装していない。
- 行 54：`eval/harness.py` に `render`（正解 AST を示して書かせ、`tlvm ast` の一致で採点する）と `gen-render`（連結 arm、`render` とは別行に報告する）を追加した。実測は G4 で行い、ここでは実行していない。

# 更新の記録

- 2026-10-14（§18.1c の未了の項目）：`counting.rs` に `none_repeated_in_a_fold_allocates_nothing`（行 31 の fold の反復）、`reference_events_of_a_recursive_program_are_fixed`（再帰する型の代表の Steps と AllocatedNodes）、`tagged_copy_is_reported_only_when_rejected`（規則 T と、印つきと印なしの trace の差）を追加した。`recursive.rs` に `recursive_helper_shapes_match_the_deltas`（補助関数の全文の fixture）、`sums.rs` に `wildcard_only_match_is_accepted_on_sums_and_options`（`_` だけの `match`）、`rewritten.rs` に `rewritten_expression_depth_is_checked_after_lowering`（書換え後の式深さ）を追加した。行 31 は fold の反復まで覆ったが、loop の反復が未検査なので部分のままである。§20.1 の件数（対応 52、部分 9、未対応 0、モデルのみ 8）は変わらない。

- 2026-10-14：`crates/tlvm/tests/regression.rs` に `rows_20_1_boundaries` を追加した。行 18・20・24・25・26・29（AST 側）・34（33 件）・43・61・62（AST 側）の実装テストになった。`ast_transport`、`names`、`types_arity_dag` などの既存テストは変更していない。

- 2026-10-14：行 35・37・48・54 を実装し、tlvm の全テスト（271 件、失敗 0）と Verus（627 verified、error 0）を通した。

[^lptl-design]: LLM向け純粋・全域言語：設計方針 v1
