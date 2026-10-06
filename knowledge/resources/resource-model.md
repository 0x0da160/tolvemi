---
type: Resource Model
title: 資源モデル
description: 資源上限は言語意味論と別の版付き profile であり、SemanticTreeNodes・ReachableHeapNodes・AllocatedNodeCount を区別し、参照コストモデルでは AllocatedNodeCount・整数ビット長・評価遷移数を規範的に数える。
tags: [lptl, resources, cost-model, sharing]
status: draft
generated: { by: claude-code/2026-10-06, at: 2026-10-06T16:00:00Z }
sources:
  - id: lptl-design
    resource: ../../spec/lptl-v1/LPTL_design_v1.md
    title: LLM向け純粋・全域言語：設計方針 v1（§8.3–§8.5、§18.1）
    last_modified: 2026-10-01T00:00:00Z
---

# 三つの量の区別

| 量 | 定義 | 性質 |
|---|---|---|
| SemanticTreeNodes(v) | 値を共有なしの有限木として展開したノード数 | 意味論的量。実装の共有に依存しない |
| ReachableHeapNodes(h) | 実装ヒープ上で根から到達可能な固有ノード数 | 実装量 |
| AllocatedNodeCount | 実行開始後に確保したノードの累積数 | v1 標準 profile で規範的に計測 |

v1 の標準資源プロファイルは再現性のため **AllocatedNodeCount**、整数ビット長、評価遷移数（step）を規範的に計測する。`let x = huge in pair(x,x)` は huge を一度評価・一度割当て、共有参照を二つ持つ pair を一つ追加する。[^lptl-design]

# 参照コストモデル（resource-profile-v1-reference-1）

- リストは不変 cons-cell DAG。空リスト、bool、unit、none は共有 singleton で割当0。none の型はコンパイラ側の型情報で区別する。
- `cons` は一セル、`pair` は一ノード、`some` は一ノード。既存 payload は共有する。
- `list[T](e1,...,en)` は引数を左から右に評価後、要素参照を一時スタックに置き、末尾から n セルを構築する（要素はコピーしない）。
- `concat(xs,ys)` は xs の spine を走査して要素参照をスタックへ置き、ys を末尾として長さ m の新規セルを作る。ys と要素を共有する。結果 m+n、追加 cons は m。
- `reverse(xs)` は n セルを作る。`length` はキャッシュせず spine を走査する。
- 整数リテラルの評価、入力整数のデコード、整数を返す算術・length は一回ごとに一整数ノードを生成する（小整数の interning なし）。変数参照、fst、snd、引数渡しは新規割当しない。
- 実行割当カウンタは decode と compile を含めず、run 開始時に0。
- 一時参照スタック、環境、実行 frame は AllocatedNodeCount に含めない。それらの物理上限は host-policy で扱い、超過は HostAborted。
- 最大整数ビット長は `bits(0)=0`、それ以外は `floor(log2(abs(n)))+1`。入力を含む全整数値を検査する。

最適化版は参照カウンタを忠実に再現する shadow accounting を持つ場合だけ同じ reference profile を名乗れる。

# 公開する資源項目

ソースバイト数、トークン数、AST ノード数、関数数、型深さ、式深さ、let 深さ、fold ネスト深さ、整数リテラル桁数、入力 JSON バイト数、入力値深さ・ノード数、評価遷移数、AllocatedNodeCount、最大整数ビット長、ヒープバイト、壁時計時間。結果型への振り分けは [API 分離](/api/api-separation.md)。

# 数値の位置付け

各 profile の数値は**標準 profile の設計値であり、性能測定から導いた値ではない**。実装・proof と照合するまで profile も凍結候補。境界値は「観測値 <= limit なら通過」、初めて超過するイベントで停止する。数値上限が等しくても診断順・cutoff の契約同一性は保証しない。

[^lptl-design]: LLM向け純粋・全域言語：設計方針 v1
