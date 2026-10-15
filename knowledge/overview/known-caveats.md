---
type: Reference
title: 既知の注意点
description: 凍結前の確認で分かった、仕様どおりだが驚きやすい振る舞い、範囲外・未対応・未検査の部分、運用上の注意、未決の事項。各項目の根拠を示す。
tags: [lptl, caveats, known-issues]
status: draft
generated: { by: claude-code/2026-10-14 }
sources:
  - id: lptl-design
    resource: ../../spec/lptl-v1/LPTL_design_v1.md
    title: LLM向け純粋・全域言語：設計方針 v1（15、119、541、548、925 行、§18.1、§18.3）
  - id: v1-16-delta
    resource: ../../spec/lptl-v1.16/LPTL_v1.16_delta.md
    title: LPTL v1.16 差分仕様：パッケージ（ローカルの依存）
  - id: regression-tests
    resource: ../conformance/regression-tests.md
    title: 必須回帰テスト
---

# 既知の注意点

この節は、凍結前の確認で分かった注意点を一か所にまとめる。確認日は 2026-10-14。各項目は、設計書の行、ソースやテストの場所、または実行結果で根拠を示す。仕様どおりの振る舞いは「仕様どおり」と書き、範囲外・未対応・未検査のものは、その旨を書く。

## 仕様どおりだが驚きやすい振る舞い

- **Dict の等値は挿入順を含めて比べる。** 同じ鍵と値でも、入れた順が違えば `eq` は `false` を返す。設計書の `eq` の規則（548 行）による。確認：`dict_put` の順を変えた二つの辞書を `eq` で比べると `false`、同じ順なら `true`。
- **`div(a, b)` は除数が 0 以下なら `none` を返す。** 設計書の定義（541 行）による。確認：`div(x, 0)` と `div(x, -2)` の plain 出力は `null`（`none`）。
- **`rec` の印を付けた関数を含むプログラムは、停止を保証しない。** 印のないプログラムは必ず停止する（設計書 15 行）。
- **`tlvm fmt` は型の誤りがあっても整形する。** 止まるのは構文エラーのときだけ（終了コード 1）。確認：`fn f(x: Int) -> Bool = x` は整形され、終了コードは 0。設計書はこの扱いを書いていない（下の「未決」を見る）。

## 範囲外・未対応・未検査

- **`tlvm exec` の entry の入力型は五つの形だけ。** `String`、`List<String>`、`Pair<List<String>, String>`、`Dict<String, String>`、`Dict<String, Int>`。ほかの型の entry は `UnsupportedEntry` になり、JSON の envelope と終了コード 64 を返す（`main.rs` の `exec_cmd`、`runtime.rs` の `ENTRY_SHAPES`。確認：`Int` の entry で終了コード 64）。
- **`exec` で Dict を受けるのは、標準入力の行（`key<TAB>value`）から作る形だけ**（v1.13。`runtime.rs`）。
- **パッケージは、ローカルのディレクトリの依存だけ。** レジストリからの取得、版の範囲指定と解決、ロックファイルは含まない（[v1.16 差分仕様](../../spec/lptl-v1.16/LPTL_v1.16_delta.md) の §0。草案で、`crates/tlvm/src/packages.rs` に実装）。取得と版の解決は、v1.0.0 の後に扱う。
- **import は根のディレクトリの内側のファイルだけ。** `..` で根のディレクトリより上へは出られない（v1.16 差分仕様の §0、v1.11 の規則）。
- **多倍長整数の `div_pos` は信頼仮定。** 検証済みの核の外にあり、設計書 925 行が明記している。
- **整数の bit 数は、成功時の結果に含まない。** bit の上限を超えたときは `ResourceExhausted`（`IntegerBits`）になり、そのとき超えた bit 数を報告する（設計書 §18.3）。
- **書換え後の式の深さは、上限 256 で検査する。** `loop` を 20 段入れ子にすると、書換え後の深さは 260 になり、`E-LIMIT-STATIC-EXPR-DEPTH` で拒否される（設計書 §18.1、`crates/tlvm/tests/rewritten.rs`）。
- **`stack_bytes` の超過は未検査。** [必須回帰テスト](../conformance/regression-tests.md) の行 35 では、ref-slot の上限は検査するが、stack_bytes の超過は検査していない。

## 運用上の注意

- **debug ビルドでは深い再帰の三つのテストを ignore する。** `crates/tlvm/tests/rec.rs` の 202、236、246 行。debug では評価スレッド（1 GiB）が深さの上限より先に溢れるため、release の CI で実行する。
- **テストのスレッドのスタックは 16 MiB。** `.cargo/config.toml` の `RUST_MIN_STACK` で設定している（深い入力の構文解析を `tests/hof.rs` で確かめるため）。

## 未了の検証

- **型引数を実際に書かせる Haiku の確認は未実施。** 凍結の前に課題を 1 題加えて 1 回確認する予定。

## 未決（判断が要る）

- **パッケージの範囲**：v1.0.0 は、ローカルの依存だけと書くか。
- **速度**：性能の目標を置くか。今は計測の基準値があるだけで、目標はない。
- **Dict の入力**：exec で受ける Dict を、現在の二つの形のまま仕様に書くか。設計書は鍵の型を制限していない（119 行）。
- **整形**：型の誤りがあるプログラムの整形を、現行のまま仕様に書くか。
- **cargo fmt**：凍結の前にリポジトリ全体へかけるか。`cargo fmt --check` は 1084 か所の差分を出す。CI は fmt を実行していない。
