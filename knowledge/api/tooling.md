---
type: Tool Contract
title: 対話的な道具（REPL と Language Server）
description: v1.12 の tlvm repl（宣言を足しながら式を評価する REPL）と tlvm lsp（診断と整形を出す最小の Language Server）の入出力の契約。どちらも今までの検査・実行の経路の前に置く未検証の front-end で、言語は変えない。
tags: [lptl, tooling, repl, lsp, cli]
status: draft
generated: { by: claude-code/2026-10-13, at: 2026-10-13T00:00:00Z }
sources:
  - id: lptl-v1-12
    resource: ../../spec/lptl-v1.12/LPTL_v1.12_delta.md
    title: LPTL v1.12 差分仕様：対話的な道具（REPL と Language Server）
    last_modified: 2026-10-13T00:00:00Z
---

# 位置づけ

- 言語（構文・型規則・意味論・診断のコード・資源上限）は v1.11 のまま。加えるのは CLI の `tlvm repl [FILE]` と `tlvm lsp` だけ。[^lptl-v1-12]
- どちらも source を組み立てて今までの API（`imports::compile_root`、`api::compile`、`api::run`）に渡し、結果を表示に写す。
  判定と実行は今までどおり検証済み部品が行い、組み立てと写像は検証されていない（[信頼境界](../guarantees/verus-and-trust-boundary.md)）。
- パッケージ管理と性能の改善は v1.12 に含めない。LLM での確認は対象外（評価セットは変えない）。

# tlvm repl

| 入力 | 振る舞い |
|---|---|
| `fn`・`rec fn`・`type`・`import "p.tlvm"` で始まる | セッションに加えたプログラムを検査し、受理なら加える（`defined NAME`、`imported "p"`）。拒否ならセッションは元のまま。同じ名前は置き換え（`redefined NAME`） |
| `entry ...` | 誤り（REPL に entry はない） |
| それ以外 | 式として評価し `値 : 型`（値は plain JSON） |
| `:type EXPR`・`:list`・`:reset`・`:load FILE`・`:help`・`:quit` | 型だけ、宣言の一覧、全消去、ファイルの宣言を加える（entry は無視）、説明、終了 |

- 式 `e` は `entry __repl_main` と `fn __repl_main(__repl_unit: Unit) -> T =` の後ろに `e` を置いたプログラムにする。`T` は `Unit` で
  検査したときの本体の `E-TYPE-RETURN` の actual（レコードの構築ならその型の名前を先に試す）。
- import はカレントディレクトリから解決する。資源プロファイルは `tlvm run` と同じで、資源上限で止まっても
  （`error: ResourceExhausted ...`）セッションは残る。
- 括弧が閉じていない・行末が `=`・`->`・`,`・`|`・` in`・` =>` の入力は次の行に続く。
- 出力はすべて標準出力（診断は `--human` の形で、今の入力は `<input>` の行・列）。prompt `> ` は標準入力が端末のときだけ。
- 引数の FILE が拒否されれば終了コード 1、それ以外は 0。

# tlvm lsp

- 標準入出力の JSON-RPC 2.0（`Content-Length` の header）。`initialize`・`initialized`・`shutdown`・`exit`、
  `textDocument/didOpen`・`didChange`（全文の同期）・`didClose`、`textDocument/formatting` を扱う。
- `exit` の終了コードは `shutdown` の後なら 0、前なら 1。`initialize` の前の request は `-32002`、知らない request は `-32601`。
- 診断（`publishDiagnostics`）：range は span の bytes を行と **UTF-16 の code unit** の列にしたもの。severity は error 1・
  warning 2、`code` は診断のコード、`source` は `tlvm`、message に expected／actual と修復ヒント（`repair (KIND): ...`）を添える。
  受理された文書には空の配列。
- `file://` の文書の import は、開いている文書を先に、なければディスクを読む。import したファイルの誤りは根の最初の import の
  行に `path:行:列:` を付けて出す。ほかの URI では import は `E-IMPORT-UNSUPPORTED`。
- 整形は `tlvm fmt` と同じ正準の整形を、文書全体を置き換える一つの edit で返す。既に正準なら `[]`、構文の誤りがあれば `null`。
- editor では、拡張子 `.tlvm` の言語の server のコマンドを `tlvm lsp` にする（`--stdio` は受け付けて無視する）。

[^lptl-v1-12]: [LPTL v1.12 差分仕様](../../spec/lptl-v1.12/LPTL_v1.12_delta.md)
