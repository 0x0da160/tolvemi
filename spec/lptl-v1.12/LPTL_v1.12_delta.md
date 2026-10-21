# LPTL v1.12 差分仕様：対話的な道具（REPL と Language Server）

本書は [v1.11 差分仕様](../lptl-v1.11/LPTL_v1.11_delta.md) に対する差分である。汎用言語にするロードマップの 9 段目で、
書いたプログラムを試し、editor の中で誤りを見られるようにする（ファイルを書いては `tlvm check`・`tlvm run` を打ち直さずに済む）。

状態：草案。処理系は本書どおりに実装済み。

**言語は変えない。** 構文・型規則・意味論・診断のコード・資源上限は v1.11 のままで、加えるのは CLI の二つの subcommand
（`tlvm repl`、`tlvm lsp`）だけである。どちらも今までの検査・実行の経路（`api::compile`・`imports::compile_root`・
`api::run`）の前に置く、検証されていない front-end である（§3）。

**この版に含めないもの**：パッケージ管理（依存の取得・版の解決・標準ライブラリの探索パス）と、性能の改善（評価器の速度、
書き換え後のプログラムの大きさ、検査の手間）は扱わない。ロードマップの後の段で扱う。

## 1. `tlvm repl [FILE]`

標準入力から一行ずつ読む対話的な評価環境。セッションは宣言（`fn`・`rec fn`・`type`）と `import` の列を持つ。

```text
$ tlvm repl
> fn double(x: Int) -> Int = mul(x, 2)
defined double
> double(21)
42 : Int
> type P = { x: Int, y: Int }
defined P
> P { x: 1, y: 2 }
{"x":1,"y":2} : P
> :type pair("a", 'b')
Pair<String, Char>
```

### 1a. 入力

- **宣言**：入力が `fn`・`rec fn`・`type`・`import "..."` で始まれば宣言として読む（先頭のコメントは飛ばす）。一つの入力に
  いくつ書いてもよい。セッションの宣言に加えたプログラムを今までどおり検査し、受理されたときだけ加えて `defined NAME`
  （`import` は `imported "path"`）を出す。拒否なら診断を出し、セッションは元のまま残す。
- **再定義**：セッションにある名前（関数・型・構築子）を宣言し直すと、古い宣言を置き換える（`redefined NAME`）。置き換えた
  プログラムが拒否されれば（ほかの宣言が古い型に依っていたなど）元のまま残す。
- **`entry`**：REPL には entry がない。入力の `entry` は誤り（`error: the REPL has no entry; ...`）。
- **`import "path.tlvm"`**：カレントディレクトリから解決する（v1.11 の規則で、根のファイルのディレクトリをカレントディレクトリと
  読み替える。`..` で上には出られない）。import の行はセッションの先頭に置かれる。同じパスは一度だけ。
- **式**：それ以外の入力は式として読み、`値 : 型` を出す。値は plain JSON（`tlvm run --plain` の出力と同じ対応）、型は
  `tlvm check` の `output_type` と同じ綴り。
- **続きの行**：丸・角・波括弧が閉じていない（文字・文字列リテラルとコメントの中は数えない）か、行末が `=`・`->`・`,`・`|`・
  ` in`・` =>` なら次の行を続けて読む。閉じないまま入力が終われば、そこまでを検査して診断を出す。
- **コマンド**（`:` で始まる行）：

| コマンド | 意味 |
|---|---|
| `:type EXPR`（`:t`） | 式の型だけを出す（評価しない） |
| `:list`（`:l`） | セッションの宣言（import が先、宣言は加えた順）の source |
| `:reset`（`:r`） | 宣言をすべて捨てる |
| `:load FILE` | FILE の宣言と import を加える（FILE の `entry` は無視する。FILE の import のパスはカレントディレクトリからのパスに直す）。受理なら `loaded N declaration(s) from FILE` |
| `:help`（`:h`、`:?`） | 説明 |
| `:quit`（`:q`） | 終わる。入力の終わり（EOF）でも終わる |

- 引数の `FILE` は始めに `:load FILE` する。拒否なら診断を出して終了コード 1 で終わる。それ以外の終了コードは 0。

### 1b. 式の検査と実行

式 `e` は次のプログラムにして検査・実行する（`__repl_main`・`__repl_unit` は利用者の名前と重ならない名前）。

```text
import ...                                   セッションの import
<セッションの宣言>
entry __repl_main
fn __repl_main(__repl_unit: Unit) -> T =
e
```

- 戻り型 `T` は次の順に決める：`Unit` で検査して受理なら `Unit`。拒否で、誤りが本体の `E-TYPE-RETURN` だけなら、その actual
  （本体の型）を `T` にして検査し直す。本体がレコードの構築 `P { ... }` なら先に `T = P` を試す（レコードの構築の型は
  構造の型 `Pair<...>` と表示されるため。値を field 名つきで出せる）。ほかの誤りがあれば、その診断を出す（作った
  `E-TYPE-RETURN` は出さない）。
- 入力は `unit`。静的プロファイル・実行プロファイル・ホストの方針は `tlvm run` と同じ既定（reference-1）。資源上限で
  止まれば `error: ResourceExhausted KIND (observed N, limit M)`（`HostAborted`・`InternalFault` も同じ形）を出し、
  セッションは残る。
- `rec fn` のある式は止まらないことがある（資源上限で打ち切る。v1.7 と同じ）。

### 1c. 出力

- 結果・診断・コマンドの応答はすべて**標準出力**に、入力の順に出す（標準エラーには出さない）。診断は `--human` と同じ形
  （`<input>:行:列: error[CODE]: message (expected …, found …)`、該当行、下線、修復ヒント）。
- 位置は、今の入力の中の誤りは `<input>` の行・列、`:load` したファイルの宣言の誤りはそのファイルの行・列、セッションに
  既にある宣言の誤りは `<session>`（その宣言の中の行・列）、import したファイルの誤りはそのファイルで示す。
- **prompt**：標準入力が端末のときだけ `> `（続きの行は `. `）を標準出力に出す。端末でなければ出さないので、パイプで流した
  入力の出力は結果と診断だけになる（テストはこの形で行う）。

## 2. `tlvm lsp`

標準入出力で話す最小の Language Server（LSP 3.17 の一部）。message は JSON-RPC 2.0 で、`Content-Length: N\r\n\r\n` の header
で区切る。editor が付ける `--stdio` は受け付けて無視する。

| method | 種類 | 振る舞い |
|---|---|---|
| `initialize` | request | capabilities `{"textDocumentSync": {"openClose": true, "change": 1}, "documentFormattingProvider": true}` と `serverInfo`（`tlvm`）を返す |
| `initialized` | 通知 | 何もしない |
| `textDocument/didOpen`・`didChange` | 通知 | 文書を全文で保持し（`change: 1` は全文の同期。最後の変更の `text` が新しい全文）、`textDocument/publishDiagnostics` を出す。その文書の後に、ほかの開いている文書の診断も出し直す（import で依存しうるため） |
| `textDocument/didClose` | 通知 | 文書を捨て、その URI に空の診断を出す |
| `textDocument/formatting` | request | §2b |
| `shutdown` | request | `null` を返す。以後の request は `-32600` |
| `exit` | 通知 | 終わる。`shutdown` の後なら終了コード 0、前なら 1。入力の終わり（EOF）も同じ |

- `initialize` の前の request は `-32002`、知らない request（`textDocument/hover` など）は `-32601`、JSON として読めない
  message は `id: null` の `-32700`。知らない通知は無視する。header が壊れていれば終わる。
- JSON の読み取りは処理系の strict JSON parser（`strict_json.rs`）、書き出しは手で組み立てる（crate の依存は増やさない）。

### 2a. 診断

- 文書を今までの経路で検査する。URI が `file://` なら、そのパスを根のファイルとして import ごと検査し（v1.11 §1b の CLI と
  同じ規則）、import したファイルは**開いている文書の中身を先に**、なければディスクのファイルを読む。それ以外の URI
  （`untitled:` など）は `api::compile` で検査し、import は今までどおり `E-IMPORT-UNSUPPORTED`。
- 一つの tlvm の診断を一つの LSP の Diagnostic にする：
  - `range`：span（UTF-8 の bytes の半開区間）を、行（`\n` で数える。0 始まり）と、行頭からの **UTF-16 の code unit** の数
    （0 始まり）にする。非 ASCII の文字列リテラル（`"日本語"` は 3 単位、`😀` は 2 単位）の後ろの誤りも正しい列になる。
  - `severity`：error は 1、warning（`W-UNUSED-FUNCTION` など）は 2。`code` は診断のコード、`source` は `tlvm`。
  - `message`：診断の message に ` (expected …, found …)` と、修復ヒントがあれば改行の後に `repair (KIND): constraint` を添える。
- import したファイルの中の誤り（`file` が根でない診断）は、根の文書の最初の import の行の range に、`path:行:列: ` を前に
  付けた message で出す（ほかのファイルの URI には出さない）。
- 受理された文書には空の `diagnostics` を出す（前の誤りを消す）。`didOpen`・`didChange` の `version` があれば添える。

### 2b. 整形

- `tlvm fmt` と同じ正準の整形（検証済み formatter の出力を診断用 formatter と照合する。レコード・直和型・map など・辞書・
  総称・import を含むものは診断用 formatter の出力）。
- 結果は、文書全体（`0:0` から文書の終わりまで）を置き換える一つの `TextEdit` の配列。既に正準なら空の配列。
- **検査に誤りがある**文書（構文・名前・型・静的な上限・import のいずれか）と、開いていない文書には `null` を返す（edit しない）。
  整形するのは `tlvm check` と同じ検査を通った文書だけで、警告だけの文書は整形する。`tlvm fmt` も同じ規則で、誤りがあれば
  何も出さず、診断を出して終了コード 1 で終わる。

### 2c. editor への組み込み

LSP の client を持つ editor なら、言語 `tlvm`（拡張子 `.tlvm`）の server のコマンドを `tlvm lsp` にするだけでよい。
hover・補完・定義への移動などはこの版では扱わない。

## 3. 検証との関係

検証済みの中核（`verus/`）は変えない。REPL と Language Server は、source を組み立てて今までの API に渡し、その結果を表示に
写すだけの、検証されていない front-end である（`trust-boundary.toml` の `glue`）。

- REPL の式の判定と値は、組み立てた一つのプログラム（§1b）を今までの経路で検査・実行したものそのもので、停止性・型安全性・
  決定性（v1 §11.2）はそのプログラムについて成り立つ。組み立て方の誤り（宣言の取り違え・別の戻り型）は、意図と違う
  プログラムを検査・実行することになり保証の外。
- 戻り型の推論（§1b）は診断の actual の文字列を型として読み直すもので、読み直した型での検査が受理されたものだけを使う
  （誤れば拒否になるだけ）。
- Language Server の診断の位置（UTF-16 への写像）と整形の edit、import したファイルの診断の置き場所も検証されていない。

## 4. LLM での確認

対象外。言語を変えないので評価セットに問題を加えず、実行もしない（`eval/SKILL.md` は変えない）。

## 5. 結果

- `crates/tlvm/src/repl.rs`（REPL）、`crates/tlvm/src/lsp.rs`（Language Server）を加え、`main.rs` に `repl`・`lsp` を足した。
  crate の依存・`Cargo.lock` は変えていない。
- `cargo test --release --locked` は 208 件すべて成功（`crates/tlvm/tests/repl.rs` の 10 件と `crates/tlvm/tests/lsp.rs` の
  10 件を含む。どちらも build した binary に標準入力を流す）。
- 加えなかったもの：パッケージ管理、性能の改善、REPL の行編集と履歴（端末の機能は使わない。`rlwrap tlvm repl` などで補える）、
  REPL の `let` によるセッションの変数、LSP の hover・補完・定義への移動・増分の同期・設定。
