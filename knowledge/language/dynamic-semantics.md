---
type: Language Specification
title: 動的意味論
description: LPTL の評価は純粋・決定的・左から右の call-by-value で、if は選択枝だけ、let は束縛式を一度だけ、fold はリスト・初期値・各反復本体の順に評価する。
tags: [lptl, semantics, evaluation]
status: draft
generated: { by: claude-code/2026-10-06, at: 2026-10-06T16:00:00Z }
sources:
  - id: lptl-design
    resource: ../../spec/lptl-v1/LPTL_design_v1.md
    title: LLM向け純粋・全域言語：設計方針 v1（§7）
    last_modified: 2026-10-01T00:00:00Z
---

# 評価順序

評価は純粋・決定的・左から右の call-by-value である。[^lptl-design]

- **strict call**（組込み・ユーザー関数）：全引数を左から右へ評価後に組込みまたは関数本体を評価する。
- **`if`**：条件を評価し、選択された枝のみを評価する。
- **`let`**：束縛式を一度評価してから本体を評価する。
- **`fold`**：リスト式、初期値、各反復本体の順に評価する。

# let

`let x = e1 in e2` は `e1` をちょうど一度評価して値 `v` を得た後、`x=v` を環境に追加して `e2` を評価する。非再帰・不変・局所であり、代入、共有可変セル、関数再帰を導入しない。

# if と fold

```text
if(true, t, f)  -> t
if(false, t, f) -> f

fold(list[T](), init, body) = init
fold(list[T](x1, ..., xn), init, body)
  = body(...body(body(init, x1), x2)..., xn)
```

各 fold ステップでは現在累積値を `acc`、現在要素を `item` として `body` を評価する。fold は左畳み込みで、入力リストは反復中に変更されない。

組込みの意味は [組込み関数](builtins.md)、停止性は [停止性の証明構造](../guarantees/termination-proof.md)、参照コストは [execution profile](../resources/execution-profile.md) を参照。


# v1.4 の追加：match_result と match

`match_result(m, |x| a, |y| b)` は m を評価し、`ok(v)` なら x=v で a だけを、`err(w)` なら y=w で b だけを評価する。
直和型の構築は `ok`／`err` の入れ子の値を作り、`match` は書き換え後の `match_result`／`match_option` の入れ子として
評価される（対象は一度だけ評価し、選ばれた枝だけを評価する）。詳細は [v1.4 差分仕様](../../spec/lptl-v1.4/LPTL_v1.4_delta.md)。


# v1.5 の追加：map など

リスト、続いて要素の順に本体を評価する。`any` は true が出た後、`all` は false が出た後、`find` は見つかった後の
要素で本体を評価しない（書き換え後の `if`・`match_option` が選ばれた枝だけを評価する）。`sort_by` は安定な挿入整列で、
比較のたびに鍵を計算し直す（要素数 n に対して O(n²) の評価）。評価は書き換え後のプログラムについて行う。詳細は
[v1.5 差分仕様](../../spec/lptl-v1.5/LPTL_v1.5_delta.md)。

# v1.6 の追加：loop

max、init の順に評価し、続いて状態 s に対して本体を評価する。本体が `none` を返した歩で止まり、それ以降の歩では本体を
評価しない。本体を max 回評価しても止まらなければ `none<S>()`、`max <= 0` なら本体を一度も評価しない。
手間は実際に本体を評価した回数に比例する分と小さな定数で、max の大きさには（ほぼ）よらない：書き換え後は長さ 16 の
リストを辿る `fold` を 16 段入れ子にし、止まった後は各段の残りの要素を比較 1 回ずつで辿る（v1.8 で修正。以前は
`range(0, max)` を辿るので max に比例した）。受け持てるのは 2^64 歩までだが、どの実行上限もそれより小さい。評価は書き換え後のプログラムについて行う。詳細は [v1.6 差分仕様](../../spec/lptl-v1.6/LPTL_v1.6_delta.md)。

# v1.7 の追加：rec fn

呼出しの評価規則は変わらない（引数を左から右に評価してから本体を評価する）。`rec fn` を含むプログラムでは評価が止まら
ないことがあり、その場合は資源上限で打ち切る：step 数・割当 node 数の上限なら `ResourceExhausted`、評価の入れ子の深さが
host-policy の上限（400000）を超えれば `HostAborted`（`eval-depth`）。環境の束縛の同時数が参照スロットの上限（4000000）を超えれば、束縛を積まずに `HostAborted`（`ref-slots`）。どちらもスタックあふれにはならない。値を返した
なら、その値は宣言した型を持ち、spec の評価の唯一の結果である（定理 `sound`）。詳細は [v1.7 差分仕様](../../spec/lptl-v1.7/LPTL_v1.7_delta.md)。

# v1.9 の追加：辞書

引数は左から右に評価する（書き換え後は `let` で一度だけ束縛する）。辞書は挿入順の `(鍵, 値)` の列として評価され、
`dict_get`・`dict_has`・`dict_remove`・`dict_put` は列を一度辿る（O(n)）。`dict_put` は既にある鍵の値をその位置で置き換え、
なければ末尾に足す。`dict_from` は前から順に `dict_put` する（O(n²)）。評価は書き換え後のプログラムについて行う。
詳細は [v1.9 差分仕様](../../spec/lptl-v1.9/LPTL_v1.9_delta.md)。

# v1.10 の追加：型引数

型引数は実行に影響しない。評価は単相化（使われた型引数の組ごとに総称の関数を複製し、型引数を具体的な型に置き換えた）
後のプログラムについて行い、意味は複製元の関数の本体と同じ。使われない総称の関数はコードにならない。
詳細は [v1.10 差分仕様](../../spec/lptl-v1.10/LPTL_v1.10_delta.md)。

[^lptl-design]: LLM向け純粋・全域言語：設計方針 v1
