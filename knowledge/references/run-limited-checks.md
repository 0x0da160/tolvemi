---
type: Run Instructions
title: 限定検査の実行手順
description: 限定検査を一時ディレクトリで実行して receipt を作り、attester で検証する手順。
tags: [lptl, verification, executor]
status: draft
generated: { by: claude-code/2026-10-06, at: 2026-10-06T16:00:00Z }
---

# Steps

[限定検査の合格数](../conformance/limited-checks.md) の executor。前提は Python 3.12 以上と `jsonschema` パッケージ。

`v1_limited_checks.py` は自分と同じディレクトリの `v1_checks.csv` を上書きするため、executor はリポジトリの `spec/lptl-v1/` を直接は実行せず、一時ディレクトリへ計算と入力をコピーして実行する。

リポジトリのルートで次を実行する。

```sh
python3 -I knowledge/references/executors/run_limited_checks.py spec/lptl-v1 > /tmp/lptl-receipt.json
python3 -I knowledge/references/attesters/limited_checks_attester.py spec/lptl-v1/v1_artifact_manifest.json /tmp/lptl-receipt.json
```

attester は receipt の計算・入力の SHA-256 が manifest と一致すること、92件の一意な case が揃っていること、合格数が case ごとの結果と一致することを確かめ、`{"verdict":"pass",...}` を出して終了コード0で終わる。表示する合格数は receipt の `summary.passed` を使い、エージェントの文章から取らない。
