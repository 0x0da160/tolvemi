---
type: Resource Profile
title: execution profile
description: 参照評価器の cost trace として7種の step イベントを定め、execution-v1-reference-1 の上限（10,000,000 step、1,000,000 AllocatedNodes、65,536 bit、16 MiB 出力）と ResourceExhausted の observed 報告規則を定める。
tags: [lptl, resources, execution, steps]
status: draft
generated: { by: claude-code/2026-10-06, at: 2026-10-06T16:00:00Z }
sources:
  - id: lptl-design
    resource: ../../spec/lptl-v1/LPTL_design_v1.md
    title: LLM向け純粋・全域言語：設計方針 v1（§18.3、§18.4）
    last_modified: 2026-10-01T00:00:00Z
---

# 参照 step イベント

数学的評価とは別に、reference evaluator の cost trace を spec に定義する。Rust 命令数や BigInt 内部命令数は step にしない。以下の各イベントを1 step とする。[^lptl-design]

1. 式 node の評価開始（各 fold 反復の body 開始も含む）
2. entry またはユーザー関数本体への入場（引数束縛自体は追加なし）
3. 通常組込みの適用開始（構成子は式 node と割当イベントで計測）
4. fold／length／reverse／concat の spine cursor による一つの cons または末尾 nil の読取り
5. list 構築／concat での一時要素参照の push と pop（一要素につき各一回）
6. 構造的 eq での一対の値根、または一対の list spine セル／nil の比較
7. [資源モデル](/resources/resource-model.md) の新規整数／cons／pair／some node の一つの確保

複数イベントは手続き順に発生させる。concat は引数評価 → dispatch → xs の各セル読取りと push → nil 読取り → 各 pop とセル確保。reverse は各セル読取りと確保、最後に nil 読取り。fold はセル読取り → binder 設定 → body 評価の繰返し、最後に nil 読取り。

eq は共有 pointer 一致による短絡・memoization を行わない。根 tag が異なれば即不一致、pair は left→right、some は payload、list は head 値 → tail spine。実行時の型比較は不要。

# Schema

| execution-v1-reference-1 | 上限 |
|---|---:|
| 参照 step | 10,000,000 |
| run 中の AllocatedNodeCount | 1,000,000 |
| 整数 bit 長 | 65,536 |
| 正準出力 bytes | 16,777,216 |

ResourceKind は `Steps`、`AllocatedNodes`、`IntegerBits`、`OutputBytes`。

# 判定と報告

- step を加算する前に上限を検査し、許されないイベントを実行しない。
- 割当イベントでは step 上限 → 整数 bit 上限 → AllocatedNodeCount の順に判定する。
- 結果整数の bits は exact な数学的結果に基づく。BigInt 計算途中のメモリ不足は bit 超過に置き換えず HostAborted／InternalFault。
- カウンタは wrap しない。observed は当該イベントの正確な値を報告する：steps／allocated は通常 limit+1、bit は結果の exact bit 数、出力 bytes は最初の超過 byte で limit+1。
- run 開始時に入力の全整数 bit 長を前順で検査し、超過なら step=0・割当=0 のまま IntegerBits を返す。
- frame／参照スタック／ヒープ bytes／時間は host-policy に明記し、違反は HostAborted。参照 step との一致や機種間再現性は保証しない。

# 凍結条件

reference-1 の凍結には、全イベントが spec の trace 関係に写像されること、fixture の step／allocation 値が一致すること、cutoff の precedence が一致することを要する。本書だけで物理的安全や実装資源モデルの検証完了を主張しない。

[^lptl-design]: LLM向け純粋・全域言語：設計方針 v1
