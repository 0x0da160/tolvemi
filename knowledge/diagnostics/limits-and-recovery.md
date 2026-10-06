---
type: Pipeline Specification
title: 診断件数と recovery
description: error と warning はそれぞれ最大32件で、phase 順と span・code による安定整列で一意に並べ、parser recovery は最大8回の同期化で打ち切る。
tags: [lptl, diagnostics, parser, recovery]
status: draft
generated: { by: claude-code/2026-10-06, at: 2026-10-06T16:00:00Z }
sources:
  - id: lptl-design
    resource: ../../spec/lptl-v1/LPTL_design_v1.md
    title: LLM向け純粋・全域言語：設計方針 v1（§10.3）
    last_modified: 2026-10-01T00:00:00Z
---

# 件数上限

- error、warning はそれぞれ合計最大32件。候補が32件以下なら全件、33件以上なら先頭31件と最後の `E-DIAG-LIMIT`／`W-DIAG-LIMIT` 一件。[^lptl-design]
- resource cutoff が32件制限で隠れる場合は、先頭30件、cutoff 一件、`E-DIAG-LIMIT` 一件。cutoff を省略しない。

# 整列

- phase 順は [パイプライン](pipeline.md) の順。
- parse phase は観測順（最初の error を先頭に保つ）で、recovery-limit を最後に置く。
- それ以外の phase 内は 主 span.start → span.end → code の ASCII 辞書順 → 論理 node index で安定整列。完成 AST では前順 index、構築 guard では Admission index。
- 同一 node・同一 code の候補は一件に統合。
- 同一入力・仕様版・profile に対し、内容・位置・順序・件数は一意。

# parser recovery

- lex は最初の error で停止し、recovery しない。
- parser recovery は最大8回の同期化操作。9回目が必要な error を観測したら、その通常 parse error と `E-PARSE-RECOVERY-LIMIT` を生成して停止する。8回目の後に EOF まで正常なら追加診断なし。
- resource guard は recovery より優先して停止する。回復 AST を name／typecheck へ渡さない。

固定手順（s = 宣言試行の開始 index、p = 失敗時の未消費 token index）：

1. 通常 parse error を生成する。
2. p が EOF なら同期操作を追加せず停止。
3. 同期回数が既に8なら `E-PARSE-RECOVERY-LIMIT` を生成して停止。
4. それ以外は `max(p, s+1)` 以降の最初の `fn`／`entry`／EOF の index q を求め、同期回数を一つ増やす。
5. q が `fn`／`entry` ならその token を消費せず、q から新しい宣言試行を開始。q が EOF なら停止。

- 進行条件は q > s。構造内部の予約語も同じ同期集合に含める。
- 探索で飛ばす token には Admission を発行せず、合成・修復 node を生成しない。既に発行した Admission 分の budget はリセットしない（[parse Admission](../resources/parse-admission.md)）。

[^lptl-design]: LLM向け純粋・全域言語：設計方針 v1
