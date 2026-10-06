---
type: Verification Plan
title: Verus の層分離・証明義務・信頼境界
description: Rust/Verus 実装を spec・proof・exec の三層に分け、10項目と追加の証明義務を課し、TCB を trust-boundary.toml に記録して BigInt 検証を V1-A〜V1-C の段階で進める計画。
tags: [lptl, verus, rust, proof, tcb]
status: draft
generated: { by: claude-code/2026-10-06, at: 2026-10-06T16:00:00Z }
sources:
  - id: lptl-design
    resource: ../../spec/lptl-v1/LPTL_design_v1.md
    title: LLM向け純粋・全域言語：設計方針 v1（§11、§20.2）
    last_modified: 2026-10-01T00:00:00Z
---

# 層分離

```text
spec/   Ty, Value, AST, scope, typing, call graph, mathematical evaluation, codec relation
proof/  termination, determinism, type soundness, refinement proofs
exec/   lexer, parser, formatter, resolver, type checker, DAG checker, evaluator, JSON codec, CLI
```

実装時の唯一の規範的意味論は `spec` 層である。[^lptl-design]

# 証明義務

1. parser 健全性、および資源上限内の EBNF 適合 source に対する完全性
2. formatter の AST 保存性と冪等性
3. 名前解決の一意性、entry 検査、scope 整合性
4. 型検査と組込み型規則の健全性
5. DAG 検査・ランク構成の健全性
6. 型安全性、停止性、決定性、中心定理
7. `eval_fuel` の燃料単調性
8. 実行可能評価器の数学的評価への適合
9. strict JSON parser・codec の型整合性、往復性、重複キー拒否
10. Compile / Decode / Run の失敗結果分離

追加（§20.2）：AST strict parser の重複拒否、schema/EBNF の表現対応、AST round-trip、元 byte span 保存、limits guard の健全性、診断順の決定性、参照イベント trace への適合、出力 guard の健全性。

# 信頼境界

`trust-boundary.toml` に、仕様レビュー、`assume`、`external_body`、`unsafe`、未検証ライブラリ、Verus、SMT、Rust コンパイラ、標準ライブラリ、OS、CPU、アロケータ、BigInt を記録する。

| 検証段階 | 内容 |
|---|---|
| **V1-A** | 外部 BigInt を信頼仮定とする検証版 |
| **V1-B** | BigInt の表現、比較、加減を検証 |
| **V1-C** | 乗算と `mod` を検証し、算術中核を TCB から除去 |

未証明中核を「完全に形式検証済み」と呼ばない。現時点では実装・証明とも存在しない（[設計状態](/overview/status-and-gates.md)）。

[^lptl-design]: LLM向け純粋・全域言語：設計方針 v1
