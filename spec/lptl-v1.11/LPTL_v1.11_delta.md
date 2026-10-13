# LPTL v1.11 差分仕様：ほかの source ファイルの import

本書は [v1.10 差分仕様](../lptl-v1.10/LPTL_v1.10_delta.md) に対する差分である。汎用言語にするロードマップの 8 段目で、
補助関数や型を別のファイルに置き、複数のプログラムから使えるようにする（一つのファイルに全部を書き写さずに済む）。

状態：草案。処理系は本書どおりに実装済み。

## 1. 追加するもの

```text
import "lib/util.tlvm"                         ほかの source ファイルの定義を使う（ファイルの先頭、宣言より前）
```

- `import` の行はファイルの先頭に、どの宣言（`fn`・`rec fn`・`type`・`entry`）よりも前に書く。いくつ書いてもよい。宣言の後の
  `import` は `E-IMPORT-AFTER-DECL`（phase parse。修復ヒントでファイルの先頭へ移すよう示す）。コメントは前に書いてよい。
- `import` は予約語ではない。トップレベルの宣言の位置で直後が文字列リテラルのときだけ import として読む（今まではこの位置の
  `import` は常に構文誤りだった）。変数名・関数名などの `import` は今までどおり使える。
- パスは文字列リテラル（エスケープは文字列と同じ）で、**import を書いたファイルのディレクトリ**から解決する。区切りは `/`。
  次は `E-IMPORT-PATH`：空、`/` で始まる（絶対パス）、`\`・`:`・制御文字を含む、`.tlvm` で終わらない、空の要素（`a//b.tlvm`、
  末尾の `/`）、名前が `.tlvm` だけ、`..` で**根のファイル**（検査・実行を指示したファイル）のディレクトリより上に出る。
  途中の `.` と `..` は正規化する（`lib/../util.tlvm` は `util.tlvm`）。
- 例：

```text
// lib/stats.tlvm（ライブラリ：entry を持たない）
type Summary = { count: Int, total: Int }
fn summarize(xs: List<Int>) -> Summary = Summary { count: length(xs), total: fold(xs, 0, |acc, x| add(acc, x)) }

// main.tlvm
import "lib/stats.tlvm"
fn solve(xs: List<Int>) -> Int = summarize(xs).total
entry solve
```

### 1a. 意味

- 名前空間は一つ（平坦）。import したファイルの（そのファイルがさらに import したものも含む）`fn`・`rec fn`・総称の関数・
  `type`（レコード型・直和型と構築子）はすべて、import したファイルから見える。名前を限定する構文（`util.f`）や、一部だけを
  import する構文、名前を隠す構文はない。import していないファイルの定義も、同じプログラムのどこかで import されていれば見える
  （まとめた一つのプログラムを検査するため。§2）。
- 同じファイルは何度 import されても（菱形の import、同じ行の重複を含む）一度だけ読む。ファイルの同一性は正規化した相対パスで
  決める。
- import が循環すれば `E-IMPORT-CYCLE`（actual に `a.tlvm -> b.tlvm -> a.tlvm` の形で循環を示す。自分自身の import も循環）。
  ファイルが無ければ `E-IMPORT-NOT-FOUND`。二つのファイルが同じ名前（関数・型・構築子の名前。名前空間は一つ）を定義すれば
  `E-IMPORT-CONFLICT`（actual に `sq: defined in a.tlvm and in b.tlvm` の形で両方のファイルを示す。一つのファイルの中の重複は
  今までどおり `E-NAME-DUPLICATE-FUNCTION` など）。
- `entry` は根のファイルのものだけが数える。import したファイルの `entry` の行は無視する（ライブラリに試し用の entry を
  書いておける）。根に `entry` がなければ今までどおり `E-ENTRY-MISSING`。
- **ライブラリ単独の検査**：entry のないファイルを `tlvm check` すると今までどおり `E-ENTRY-MISSING` になる。ライブラリは、
  それを import して entry を持つファイルから検査する（entry のない検査の形は加えない。§5）。
- 型は今までどおり使うより前に宣言する。まとめる順（§2）では import されたファイルが import したファイルより前に来るので、
  import したファイルの型を使える。import していない兄弟のファイルの型を使うと、順によっては `E-RECORD-UNKNOWN-TYPE` になる。
- `W-UNUSED-FUNCTION` は根のファイルの関数にだけ出す（ライブラリの関数が使われないのは普通のこと）。

### 1b. 使える場所

- import を解決するのは、ファイルから検査する入口だけ：CLI の `tlvm check`・`run`・`test`・`exec`・`ast`（source のファイル。
  `--ast`・`.json`・標準入力 `-` は対象外）と、名前と source の対応表を渡す API（Rust の `api::compile_files`・
  `embed::Program::compile_files`、Python の `tlvm.compile_files(root, {path: source})`）。対応表の API はファイルシステムに
  触れず、key（`/` 区切り、`.`・`..` を含まない）を根の key のディレクトリからの相対パスで引く。
- source の文字列だけを受け取る API（`api::compile`、`embed::Program::compile`、`tlvm.compile`）は、import を含むプログラムを
  `E-IMPORT-UNSUPPORTED`（phase import。修復ヒントでファイルからの検査か対応表の API を示す）で拒否する。AST transport に import
  の node はない。
- `tlvm fmt` は与えたファイルだけを整形し、import の行を残す（`import "path"` を一行ずつ、宣言より前に）。import の行を含む
  ファイルは検証済み formatter の対象外で、診断用 formatter の出力を出す。
- `tlvm ast` は import をまとめたプログラム（§2 の順。entry は根のもの）を出す。これは `--ast` でそのまま検査・実行できる。
- CLI の FsLoader は、根のファイルのディレクトリの外を指す symlink も読まない（`E-IMPORT-NOT-FOUND`、actual に理由）。

## 2. 検証との関係

検証済みの中核は変えない。接着部分（`crates/tlvm/src/imports.rs`。構文は `parser.rs`）が、import を一つのプログラムに
まとめてから今までの経路に渡す。

1. 根のファイルを構文解析する。import が無ければ（または根が構文として読めなければ）今までどおり根だけを検査する。
2. 深さ優先で import をたどる。各 import のパスを正規化し（§1 の誤りは `E-IMPORT-PATH`）、探索中のファイルに戻れば
   `E-IMPORT-CYCLE`、読んだファイルなら飛ばし、無ければ `E-IMPORT-NOT-FOUND`。読んだファイルは単独で構文解析し、構文の誤りは
   単一ファイルと同じ診断（修復ヒント、検証済み parser との照合を含む）をそのファイルに付けて出す。
3. 上限：読むファイルは根を含めて 64 個まで（`E-LIMIT-STATIC-IMPORT-FILES`、静的プロファイルの `import_files`）、bytes は
   全ファイルの合計を静的プロファイルの `source_bytes`（1 MiB）で抑える（`E-LIMIT-STATIC-SOURCE-BYTES`）。token 数・関数の数・
   AST node 数などの上限は、まとめたプログラム全体にかかる。
4. 名前の衝突（`E-IMPORT-CONFLICT`）を検査する。
5. 深さ優先の帰りがけ順（import されたものが先、根が最後）に、各ファイルの中身を改行で区切ってつなぐ。各ファイルの import の行と、
   根以外のファイルの `entry` 宣言は、同じ長さの空白に置き換える（位置を保つ）。
6. つないだ source を今までの経路（型引数の解決・単相化、直和型・レコードの展開、map など・辞書の書き換え、検証済み部品による
   検査）に渡す。生成する名前（`first_g1`、`node_new` など）はまとめたプログラム全体で重ならない。
7. 診断の span（修復ヒントの target_span も）を、つないだ source 上の位置からファイルの中の位置に戻し、`file` を付ける。

- 停止性・型安全性・決定性（v1 §11.2）は、まとめた一つのプログラムについて成り立つ。検証済み部品が検査・実行するのはまとめた
  プログラムそのものなので、つなぎ方の誤り（読み落とし・別の順）は、意図と違うプログラムを検査することになり保証の外。
- 診断の `file`：§2 の 2 以降で複数のファイルを扱ったプログラムの診断には、全部に `file`（CLI では根のファイルのパスに
  ディレクトリをつないだもの、対応表の API では key）を付ける。一行 JSON では最後の key（`..., "repair": ..., "file": "lib/a.tlvm"}`）。
  import のないプログラムの診断には付けない（JSON は今までと byte 単位で同じ）。`--human` は `file:行:列` をそのファイルで示す。
- 診断の phase に `import`（parse と structural-limits の間）を加える。

## 3. 診断

| コード | phase | 意味 |
|---|---|---|
| `E-IMPORT-AFTER-DECL` | parse | 宣言の後の import。修復ヒント（delete_span）でファイルの先頭へ移すよう示す |
| `E-IMPORT-PATH` | import | §1 のパスの形の誤り（actual にパスと理由）。修復ヒントで相対パスの形を示す |
| `E-IMPORT-NOT-FOUND` | import | ファイルが無い（actual に解決したパスと理由。CLI では外を指す symlink・普通のファイルでないものも） |
| `E-IMPORT-CYCLE` | import | import の循環（actual に循環。span は循環を閉じる import の行） |
| `E-IMPORT-CONFLICT` | import | 二つのファイルが同じ名前を定義（actual に名前と両方のファイル。span は後にまとめるファイルの名前） |
| `E-IMPORT-UNSUPPORTED` | import | source の文字列だけの API に import（§1b） |
| `E-LIMIT-STATIC-IMPORT-FILES` | import | 読むファイルの数の上限（expected に上限、actual に数） |

- 全部の import の誤り（パス・欠落・循環）と、読んだファイルの構文の誤りをまとめて報告する。どれかがあれば、衝突の検査と
  まとめたプログラムの検査はしない。上限を超えたらそこで止める。

## 4. LLM での確認

評価の仕掛け（`eval/`）は一つの問題に一つの source ファイルを書かせる形なので、この機能は LLM では確認しない（評価セットに
問題を加えず、実行もしない）。`eval/SKILL.md` には短い説明だけを加えた。

## 5. 結果

- 検証済みの中核（`verus/`）は変更なし。`cargo test --release --locked` は 188 件すべて成功（`crates/tlvm/tests/import.rs` の
  21 件、`embed::Program::compile_files` の doctest を含む）。Python binding の test は 14 件成功（`tlvm.compile_files` を含む）。
- 例 `examples/stats.tlvm`（`examples/lib/stats.tlvm` を import する）を加えた。CI の `examples/*.tlvm` の繰り返しには
  サブディレクトリのライブラリは入らない。
- 加えなかったもの：名前を限定する import・一部だけの import、entry のないライブラリの検査の形、AST transport の import、
  標準ライブラリの探索パス。
