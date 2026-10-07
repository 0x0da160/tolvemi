# tlvm-py（Python binding）

Tolvemi の処理系を Python から呼ぶための PyO3 の拡張モジュール `tlvm` です。Rust の組み込み API
（`crates/tlvm` の `embed`）を薄く包んでいます。判定と実行は CLI と同じく検証済み部品が行い、資源上限は
CLI と同じ既定値（reference-1）です。説明は [`docs/implementation.md`](../../docs/implementation.md) の「組み込み」の節にあります。

この crate はルートの workspace から外してあり、独自の `Cargo.lock` を持ちます。

## build

maturin は使わず、cargo で build した共有ライブラリを `tlvm.abi3.so` という名前で置きます（abi3 なので Python 3.8 以降で使えます）。

```sh
crates/tlvm-py/build.sh                                   # crates/tlvm-py/tlvm.abi3.so ができる
python3 -m unittest discover -s crates/tlvm-py -p 'test_*.py'
```

`tlvm.abi3.so` を置いたディレクトリを `sys.path`（または `PYTHONPATH`）に入れれば `import tlvm` できます。
macOS では `build.sh` が `libtlvm.dylib` を同じ名前で置きます。

## 使い方

```python
import tlvm

p = tlvm.compile("fn solve(xs: List<Int>) -> Int = fold(xs, 0, |acc, x| add(acc, x))\nentry solve\n")
p.input_type          # 'List<Int>'
p.output_type         # 'Int'
p.run([1, 2, 3])      # 6
p.run([2**80, 1])     # 1208925819614629174706177（整数は桁数によらず int のまま）
p.run_json("[1, 2]")  # '3'（plain JSON の文字列で受け渡す版）

try:
    tlvm.compile("fn solve(xs: List<Int>) -> Int = add(xs, 1)\nentry solve\n")
except tlvm.CompileError as e:
    for d in e.diagnostics:   # 診断の一行 JSON（設計書 §10.1）を dict にしたもの
        print(d["code"], d["span"])
```

値は plain JSON（`tlvm run --plain` と同じ対応）を経由して受け渡します。`run` は Python の値を `json.dumps` で
文字列にし、結果を `json.loads` で戻します。

| 型 | Python の値 |
|---|---|
| `Int` | int（入力では正規形の十進文字列も可） |
| `Bool`／`Unit` | bool／None |
| `List<T>` | list（入力では tuple も可） |
| `Pair<A, B>` | 二要素の list（入力では tuple も可） |
| `Option<T>` | `none` は None、`some(v)` は v。T が `Unit` か `Option` のときだけ `{"some": v}` |

## 例外

すべて `tlvm.TlvmError` の派生です。

| 例外 | いつ | 属性 |
|---|---|---|
| `tlvm.CompileError` | source が検査で拒否された | `diagnostics` |
| `tlvm.InputError` | 入力を入力型の値として読めない | `diagnostics`（span は入力 JSON 上の位置） |
| `tlvm.ResourceExhausted` | 実行の資源上限を超えた | `kind`（`Steps` など）、`observed`、`limit` |
| `tlvm.HostAborted` | ホスト側の物理上限（評価の深さ）で中断した | `reason` |
| `tlvm.InternalError` | 処理系の内部の失敗 | `reason` |

実行中は GIL を手放すので、別スレッドから並行に呼べます。
