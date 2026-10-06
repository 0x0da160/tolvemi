---
type: API Contract
title: API 分離
description: LPTL のホスト API は compile・compile_ast・decode_input・run に分かれ、境界失敗・静的拒否・入力不正・資源超過・ホスト中断・内部障害を別の結果型で返す。
tags: [lptl, api, results]
status: draft
generated: { by: claude-code/2026-10-06, at: 2026-10-06T16:00:00Z }
sources:
  - id: lptl-design
    resource: ../../spec/lptl-v1/LPTL_design_v1.md
    title: LLM向け純粋・全域言語：設計方針 v1（§8.5、§9.1）
    last_modified: 2026-10-01T00:00:00Z
---

# Schema

```text
compile(source_bytes, static_profile)
  -> SourceBoundaryFailure(InvalidSourceEncoding)
   | CompileResult

compile_ast(ast_json_bytes, static_profile, ast_transport_profile)
  -> AstBoundaryFailure(InvalidUtf8)
   | AstInvalid(AstDiagnostics)
   | CompileResult

CompileResult =
    Accepted(TypedProgram, CompileWarnings)
  | Rejected(CompileErrors, CompileWarnings)

decode_input(T_in, json_bytes, input_profile)
  -> InputBoundaryFailure(InvalidUtf8)
   | DecodeResult

DecodeResult = Decoded(TypedValue(T_in)) | Invalid(DecodeDiagnostics)

run(typed_program, decoded_input, execution_profile, host_policy)
  -> RunResult

RunResult =
    Completed(EncodedValue)
  | ResourceExhausted(ResourceKind, Observed, Limit)
  | HostAborted(VersionedHostReason)
  | InternalFault(VersionedFaultCode)
```

[^lptl-design]

# 規則

- Compile、Decode、Run は別 API・別結果型。AstDiagnostics は AST transport の失敗であり、name/typecheck の静的拒否と分離する。
- source／AST／input は **サイズ上限 → UTF-8 → 構文** の順に検査する。サイズ超過時は UTF-8 を走査しない。
- プロファイルは版付きの検証済み設定値。設定の欠落・負上限・未知版はホスト API の設定エラーであり、プログラム診断ではない。
- TypedProgram は仕様版・型・AST を含む不透明値。run は entry 入力型と一致する TypedValue だけを受け取る。型・仕様版の不一致はホスト側 API misuse で、LPTL の動的型エラーではない。
- `Completed` は出力 codec まで完了した結果。出力 byte 上限超過は `ResourceExhausted(OutputBytes, ...)`。
- RunResult と UTF-8 boundary failure はプログラム診断列ではなく結果 envelope として伝え、E-LEX や E-TYPE へ変換しない。

# 上限超過の振り分け

| 超過した上限 | 結果 |
|---|---|
| 静的上限（ソース、AST、型深さ等） | `CompileResult::Rejected(E-LIMIT-STATIC-*)` |
| 入力上限 | `DecodeResult::Invalid(E-LIMIT-INPUT-*)` |
| AST transport のサイズ | `AstInvalid(E-AST-LIMIT-BYTES)` |
| execution profile（Steps、AllocatedNodes、IntegerBits、OutputBytes） | `RunResult::ResourceExhausted` |
| host-policy（時間、物理ヒープ、frame、参照スロット） | `RunResult::HostAborted` |

評価中に起きたという理由だけで ResourceExhausted へ統合しない。OS kill などで結果を返せない場合もある。各 profile の数値は [資源](../resources/) を参照。

[^lptl-design]: LLM向け純粋・全域言語：設計方針 v1
