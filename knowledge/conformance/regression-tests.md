---
type: Test Suite
title: 必須回帰テスト
description: LPTL v1 設計書 §20.1 が定める必須回帰テストを領域別に整理した表。処理系実装はまだなく、これらは G0 以降で照合する期待結果である。
tags: [lptl, conformance, tests, fixtures]
status: draft
generated: { by: claude-code/2026-10-06, at: 2026-10-06T16:00:00Z }
sources:
  - id: lptl-design
    resource: ../../spec/lptl-v1/LPTL_design_v1.md
    title: LLM向け純粋・全域言語：設計方針 v1（§20.1）
    last_modified: 2026-10-01T00:00:00Z
---

# 位置付け

処理系が存在しないため、下表は実行結果ではなく期待される主結果である。一部は [限定検査](/conformance/limited-checks.md) の補助モデルで照合済み。全件は設計書 §20.1 を参照。[^lptl-design]

# Examples

## entry・宣言境界・parse

| 入力／条件 | 期待される主結果 |
|---|---|
| `fn f(x: Int) -> Int = x` | `E-ENTRY-MISSING` |
| `fn f(x: Int) -> Int = x entry missing entry f` | `E-ENTRY-UNKNOWN`。DUPLICATE なし |
| `fn f(x: Int) -> Int = x entry f entry f` | `E-ENTRY-DUPLICATE` 一件 |
| `fn f() -> Int = 0 entry f` | `E-ENTRY-ARITY` |
| `fn f(x: Int) -> Int = x fn g(y: Int) -> Int = y entry f` | Accepted と g の `W-UNUSED-FUNCTION` |
| `fn f(x: Int) -> Int = x 1 entry f` | `E-PARSE-UNEXPECTED-TOKEN` |
| `fn f(x: Int) -> Option<Int> = none[Foo] entry f` | `E-PARSE-EXPECTED-TYPE` |
| recovery 8回後に更に error | 通常 error と `E-PARSE-RECOVERY-LIMIT`、停止 |
| expr 位置の fn へ parse error 後に同期 | 前の宣言開始より先なら fn を保持して新宣言試行。同期は一回 |
| parse error 時の未消費 token が EOF | 停止。同期回数／RECOVERY-LIMIT を加算しない |

## 型・arity・DAG

| 入力／条件 | 期待される主結果 |
|---|---|
| 既知の `f(Int)` を `f(1,true)` と呼出し | `E-ARITY-USER`。true を Int と比較しない |
| `add(1,true,0)` | `E-ARITY-BUILTIN`。引数型比較を抑制 |
| `f(1,fst(unit))`、f は一引数 | `E-ARITY-USER` と独立した `E-TYPE-FST-ARG` |
| fold 内から現在関数を呼ぶ | `E-CYCLE-CALL` |
| 型共有・interning・比較 cache の有無 | 同じ論理型検査 trace・仕事量・cutoff |

## 上限・cutoff

| 入力／条件 | 期待される主結果 |
|---|---|
| token limit=L、ちょうど L／L+1 | 前者は次 phase、後者は TOKENS cutoff |
| typecheck 中の semantic cutoff | entry／warnings を実行しない |
| add 例、SemanticWork 上限 9／8 | 前者は完了、後者は SEMANTIC-WORK cutoff |
| 型構成イベントで型深さと SemanticWork が同時超過 | SEMANTIC-TYPE-DEPTH を優先 |
| `add(1,true,0)`、SemanticWork 上限 0／1 | 0 は call VisitExpr 前 cutoff のみ。1 は `E-ARITY-BUILTIN` を保持し最初の子 VisitExpr 前 cutoff |
| Admission 済み some の子 unit が budget 超過の不完全構文 | 閉じ括弧欠落より先に AST-NODES cutoff |
| source／AST／input の bytes 上限超過かつ不正 UTF-8 | bytes 上限を優先、UTF-8 未検査 |
| error 候補33件 | 通常31件＋`E-DIAG-LIMIT` |
| 524,276 文字名の formatter 境界 fixture | 元 1,048,576 bytes、format 後 1,048,582 bytes。再投入は拒否 |

## AST transport

| 入力／条件 | 期待される主結果 |
|---|---|
| AST object 重複 key | map 化前に `E-AST-DUPLICATE-KEY` |
| AST に `inferred_type` field | `E-AST-UNKNOWN-FIELD` |
| `var.name="if"` | `E-AST-IDENTIFIER` |
| 識別子の末尾 LF・CR・CRLF・tab、前後空白、非 ASCII、U+2028/2029 | schema 拒否、`E-AST-IDENTIFIER` |
| 整数 `"-0"`／`"01"`／`"+1"`／JSON number | 前三者は `E-AST-INTEGER`、number は `E-AST-FIELD-TYPE` |
| 識別子 `"x"`／`"x\n"` | 前者は `x` として受理、後者は `E-AST-IDENTIFIER` |
| `declarations: []` | schema 適合、共通検査で `E-ENTRY-MISSING` |
| `callee="uncons"`、同名 fn なし／あり | `E-NAME-UNKNOWN-FUNCTION`／通常ユーザー call |
| some node に value なし | `E-AST-MISSING-FIELD` |
| 合法 param へ tag 追加 | `E-AST-UNKNOWN-FIELD` |
| fn の name が if、body が JSON number | 浅い型検査が先なので `E-AST-FIELD-TYPE` |

## 入力・実行・資源

| 入力／条件 | 期待される主結果 |
|---|---|
| input int の value が JSON number | `E-INPUT-*`、Int として受理しない |
| decode 後の同じ key を escape 違いで重複 | duplicate key として拒否 |
| concat 長さ m,n | 結果 m+n、追加 cons は m、要素と ys を共有 |
| none を反復評価 | none 由来の新規割当0 |
| let の同じ値を pair の両側で参照 | 束縛式一回、pair 一ノード |
| host-policy の参照スロット／frame 上限超過 | HostAborted |
| Steps／AllocatedNodes／IntegerBits／OutputBytes 上限超過 | ResourceExhausted |
| Int `10^4096` の codec 往復 | 抽象往復は成立、標準 input は桁数上限で拒否 |

## 評価・hash

| 入力／条件 | 期待される主結果 |
|---|---|
| 3失敗候補後に1成功候補 | episode の S=1、分母へ4試行を加えない |
| 最終候補選択後の隠しテスト不合格 | episode 失敗。選び直さない |
| 予算一成分ちょうど上限／次操作が guard で禁止 | budget 内で終了 |
| 実測 usage が一成分でも超過 | budget_exceeded、S=0 |
| 同 AST／codec、異なる spec_version | structural_hash 同じ、spec_bound_syntax_hash の preimage は異なる |
| spec_version 未確定 | 正式 hash を発行しない |

[^lptl-design]: LLM向け純粋・全域言語：設計方針 v1
