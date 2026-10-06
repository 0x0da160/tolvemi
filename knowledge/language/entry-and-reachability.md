---
type: Language Specification
title: entry と到達可能性
description: entry 宣言は構文個数を収集し、未知は name phase、欠落・重複・arity は entry phase で診断する。有効な entry から到達しない関数に W-UNUSED-FUNCTION を出す。
tags: [lptl, entry, reachability, diagnostics]
status: draft
generated: { by: claude-code/2026-10-06, at: 2026-10-06T16:00:00Z }
sources:
  - id: lptl-design
    resource: ../../spec/lptl-v1/LPTL_design_v1.md
    title: LLM向け純粋・全域言語：設計方針 v1（§5.2、§5.3、§10.2、§20.1）
    last_modified: 2026-10-01T00:00:00Z
---

# entry 検査の分割

parse 成功後、entry 宣言を入力順に収集し構文個数 N を保存する（収集は診断の発行ではない）。[^lptl-design]

| 状況 | name phase | entry phase |
|---|---|---|
| N=0、その他の name error なし | entry 由来の error なし | `E-ENTRY-MISSING` |
| N=1、名が未知 | `E-ENTRY-UNKNOWN` | 実行しない |
| N>=2、一つ以上が未知 | 未知の宣言ごとに `E-ENTRY-UNKNOWN` | 実行しない。重複を併記しない |
| N>=2、全名が既知、その他の name error なし | 成功 | `E-ENTRY-DUPLICATE` 一件。arity は検査しない |
| N=1、名が既知、その他の name error なし | 成功 | 引数が一つでなければ `E-ENTRY-ARITY` |
| 任意の N、その他の name error あり | 通常の name 診断 | 実行しない |

- resource cutoff により entry phase に到達しない場合も、欠落・重複・arity を発行しない。
- 主 span：重複は二番目の entry 宣言全体、欠落は EOF のゼロ幅、未知は entry の関数名、arity は唯一の entry の関数名。
- entry の戻り型に追加制約はない。入力型・出力型は任意の LPTL 型（ただし引数は一つ）。

# 到達可能性

entry が name phase と entry phase の双方で有効なとき、entry 関数からユーザー関数呼出しをたどって到達可能な関数を **live** と呼ぶ。

- 全トップレベル関数は名前解決・DAG 検査・型検査の対象（live でなくても検査する）。
- live でない関数ごとに、関数名 span を主 span とする `W-UNUSED-FUNCTION` を一件発行する。
- entry が無効、name 失敗、または resource cutoff があれば到達性を定義せず warning を出さない。call-graph／typecheck error があっても構文上の到達性 warning は計算する。

# Examples

| 入力 | 主結果 |
|---|---|
| `fn f(x: Int) -> Int = x` | entry phase の `E-ENTRY-MISSING` |
| `fn f(x: Int) -> Int = x entry missing entry f` | name の `E-ENTRY-UNKNOWN`。DUPLICATE なし |
| `fn f(x: Int) -> Int = x entry f entry f` | `E-ENTRY-DUPLICATE` 一件 |
| `fn f() -> Int = 0 entry f` | `E-ENTRY-ARITY` |
| `fn f(x: Int) -> Int = x fn g(y: Int) -> Int = y entry f` | Accepted と g の `W-UNUSED-FUNCTION` |

[^lptl-design]: LLM向け純粋・全域言語：設計方針 v1
