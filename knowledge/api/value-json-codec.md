---
type: Data Format
title: 値 JSON codec
description: LPTL の入出力値は tag 付き JSON で、Int は正規十進文字列（JSON number 不使用）、デコーダは member 順非依存、エンコーダは一意の正準 JSON を出す。
tags: [lptl, json, codec, io]
status: draft
generated: { by: claude-code/2026-10-06, at: 2026-10-06T16:00:00Z }
sources:
  - id: lptl-design
    resource: ../../spec/lptl-v1/LPTL_design_v1.md
    title: LLM向け純粋・全域言語：設計方針 v1（§9.2、§9.3、§9.5）
    last_modified: 2026-10-01T00:00:00Z
---

# Schema

| 型 | 正準 JSON | キー順 |
|---|---|---|
| Int | `{"tag":"int","value":"-42"}` | tag, value |
| Bool | `{"tag":"bool","value":true}` | tag, value |
| Unit | `{"tag":"unit"}` | tag |
| List | `{"tag":"list","items":[{"tag":"int","value":"1"}]}` | tag, items |
| Option some | `{"tag":"some","value":{"tag":"int","value":"1"}}` | tag, value |
| Option none | `{"tag":"none"}` | tag |
| Pair | `{"tag":"pair","left":{"tag":"int","value":"1"},"right":{"tag":"bool","value":true}}` | tag, left, right |

[^lptl-design]

# デコード（受理）

- object member の順序に依存しない。有効なキー集合で各キーが一度だけ現れ、値が期待型に適合すれば任意の順を受理する。
- 余分なキー、欠落キー、重複キーを拒否。重複キーは map に落とす前に token stream で検出する。
- JSON number、JSON null、予期しない位置の配列・object、型不一致を拒否。Int の値は `INT` の正規形の文字列のみ。
- 検査順と診断選択は [strict JSON と decode 順序](strict-json.md) に従う。

# エンコード（正準出力）

UTF-8、最小空白、上表のキー順、期待型に対応する正確な tag 文字列、整数は INT の正規形。

# 往復性

`decode_T`／`encode_T` は profile による失敗を含めない抽象的な関係で、任意の有限有効値 `v:T` について次を証明対象とする。

```text
decode_T(encode_T(v)) = Decoded(v)
```

有限 API `decode_input` での成功は、encode 結果の bytes・JSON 深さ・値深さ・SemanticTreeNodes・整数桁数が input profile 内であり、ホスト資源がある場合だけ。出力 profile と入力 profile は別契約なので、`Completed` の出力を標準 input profile へ必ず再投入できるとは約束しない。例：`10^4096` は 4,097 桁・13,607 bits の有限 Int だが、標準 input の 4,096 桁上限を超える（抽象往復の反例ではない）。

[^lptl-design]: LLM向け純粋・全域言語：設計方針 v1
