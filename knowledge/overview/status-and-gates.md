---
type: Project Status
title: 設計状態と出荷ゲート
description: LPTL v1 は凍結候補の設計文書であり実装・証明・出荷ではない。G0 は未達、G1–G4 は未判定で、spec_version は未確定（null）。
tags: [lptl, status, gates, release]
status: draft
generated: { by: claude-code/2026-10-06, at: 2026-10-06T16:00:00Z }
sources:
  - id: lptl-design
    resource: ../../spec/lptl-v1/LPTL_design_v1.md
    title: LLM向け純粋・全域言語：設計方針 v1（冒頭、§15、§17、§20.3、§20.5）
    last_modified: 2026-10-01T00:00:00Z
  - id: manifest
    resource: ../../spec/lptl-v1/v1_artifact_manifest.json
    title: v1 artifact manifest
---

# 現在の状態

- **凍結候補。** 実装完了・証明完了・出荷を意味しない。文書日付 2026-10-01、文書版 `v1`。[^lptl-design]
- **規範性。** 実装時の唯一の規範的意味論は Rust/Verus プロジェクトの `spec` 層。本書はその契約案・公開投影であり、既存 `spec` と照合済みとは主張しない。
- **`spec_version` は未確定（null）。** 文書版 v1 や codec ID で代用しない。そのため仕様結合 hash・再現 hash の正式値は発行しない（[ハッシュと同一性](../api/hashes-and-identity.md)）。
- 成果物は設計文書、AST schema、manifest、限定検査の入力・結果・補助モデル、突き合わせ資料。Rust/Verus 実装、機械証明、LPTL 実装の実測、LLM 実験を含まない。

manifest 上のゲート状態：[^manifest]

| ゲート | 状態 |
|---|---|
| G0 | `not_met` |
| G1–G4 | `not_assessed` |

# 出荷ゲート

| ゲート | 内容 | 判定時期 |
|---|---|---|
| **G0 仕様凍結** | v1 `spec`、EBNF、型、評価、API、codec、診断、resource profile interface を固定。後続の Option 消去候補と混在させない。文書・Skill・例・テストを規範仕様に追跡可能にする | 対応 spec、実 schema、完全な diagnostic registry、Admission・型検査・実行 profile の trace fixture を固定し適合照合した後 |
| **G1 数学的コア** | `let`、`fold`、リスト構築操作、DAG 呼出しを含む型安全性・停止性・決定性・中心定理を機械検証 | 実装／証明後 |
| **G2 処理系適合** | resolver、type checker、DAG checker、evaluator、formatter、parser、strict JSON codec の適合を証明または台帳化 | 実装／証明後 |
| **G3 境界監査** | TCB、`assume`、`external_body`、`unsafe`、BigInt、SMT、Rust、OS 等を版付き台帳で公開 | 境界監査後 |
| **G4 LLM 実験** | §12.3–12.5 に従う介入を事前登録し、秘密 seed 最終評価・全 episode の分母・失敗分類・無条件費用・資源超過・対応比較と信頼区間を公開。正の優位性は必須にしない | 事前登録実験後 |

G0 の未達項目は、対応 spec、Admission・実行・型検査の参照 trace fixture、strict parser／encoder／共通検査器との適合照合。診断の版付き registry は [registry-v1.json](../diagnostics/registry-v1.json) として 2026-10-15 に作成し、ソースと fixture に照合するテストを付けた（spec の成果物と manifest への登録は未了）。限定 schema 検査や補助モデルの通過（[限定検査](../conformance/limited-checks.md)）をゲートへ代用しない。

# v1.0.0 の凍結に関する決定

回答済みの決定は DECISION 行で記録します。未回答の項目は「未決定」と書きます（2026-10-13 時点）。

- DECISION-1（範囲）：設計書の核を v1 とする（route A）。レコード、直和、match、型引数、再帰、Char・String・Result、div、dict、Option 消去は v1 の外。【DECISION-4 により置き換え】
- DECISION-2（拡張の扱い）：検証済みの仕様（verus/）は据え置き、v1 の判定が拡張を拒否する。【DECISION-4 により置き換え】G0 の「後続の Option 消去候補と混在させない」は option_fold を指し、DECISION-4 のあとも有効。
- DECISION-3（凍結の条件）：Verus で証明が要る G0 の項目を満たしてから凍結する。G1〜G4 を凍結の条件に含めるかは、DECISION-7 で決めた。
- DECISION-4（範囲）：実装済みの機能（v1.1〜v1.16）をすべて v1 に含める。非目標は実装と照合して改めた（設計書 2.2 節、2.3 節）。option_fold は実装がないため v1 の外。DECISION-1 と DECISION-2 を置き換える。
- DECISION-5（字句表、D2）：字句表は実装の 68 語とする。予約語 19、文脈キーワード 49。
- DECISION-6（凍結の時期、D6）：未証明の書換えを残して凍結しない。証明を終えてから凍結する（DECISION-3 を支持）。
- DECISION-7（凍結条件、G1〜G4）：凍結条件は G0〜G4 のすべてとする。G4 は事前登録した実験の実施と公開を条件とし、正の優位性は条件としない（設計書 §15）。
- DECISION-8（推奨の採用、D3・D5・D7〜D12、2026-10-13）：オーナーがスレッドで「はい」と答え、次の推奨どおりに決めた。
  - D3 括弧は山括弧。実装は `list<Int>` と `none<Int>()` を受理し、`list[Int]` は E-PARSE-EXPECTED-TOKEN で拒否する。
  - D5 作業量・Admission・実行の trace は適合試験の glue であり、規範仕様の一部ではない。G0 では参照 fixture として固定する。
  - D7 v1 の判定は実装済みの拡張タグ（v1.1〜v1.16）を受理する。「厳格に拒否」から変更（DECISION-4 による）。
  - D8 実行の trace は設計書の規定どおり（execution-v1-reference-1 と論理 trace）。
  - D9 補助モデルの行は G0 の必須に含めない。限定検査や補助モデルの通過は G0 の代用にしない。
  - D10 `SKILL.md` は「仕様と照合する」と書き直す（設計書 §12.2、[LLM 統合と Skill](../llm-evaluation/integration-and-skill.md)）。
  - D11 spec_version は凍結時に決める（候補は lptl-v1.0.0）。それまで null のまま。
  - D12 型検査の仕事量 cutoff（typecheck-cost-v1）と AST の重複 key（§9.3a、§19.3）は実装のある規則なので v1 の対象とする。設計書の本文はこの扱いになっている（DECISION-4 による）。
- DECISION-9（call の型引数、2026-10-13）：オーナーが「call に type_args を足す」を選んだ。`call` は `type_args` を必ず持ち、型引数を明示しない call では空配列を書く（v1.10 で省略可能だった扱いを改める）。構築子（`Leaf<Int>()`）は展開後の形で書くので、型引数は AST に現れない。
- DECISION-10（名前規則、2026-10-14）：オーナーが「68語すべて除く」を選んだ（推奨の 19 語案は採らない）。AST の変数・引数・束縛・関数名・entry 名・組込みでない callee・型引数の名前は、字句表の 68 語をすべて除く。Surface は文脈キーワードを変数・引数・束縛に使えるままで、AST だけが狭い（§4.2、§19.2）。codec、テスト（`hof.rs`、`loop.rs`、`regression.rs`）、schema をこの規則へ戻した。

DECISION-10 は確定した（オーナーの選択、2026-10-14）。`tlvm ast` と `encode_ast` は、字句表の語を変数名に使ったプログラムを付け替えずに `E-AST-IDENTIFIER` で拒否する（オーナーの選択、2026-10-14）。先に選んだ「encode で拒否する」は、出力が受理されるという誤った前提に基づいていたため、決め直しを求めた。拒否の結果、そうしたプログラムは `tlvm ast` で出せず、名前を変える必要がある（[字句の仕様](../language/lexical-syntax.md)）。

DECISION-11（§20.1 の 35・37・54、2026-10-14）：オーナーが「三行とも実装」を選んだ（推奨の「三行とも v1 から外す」は採らない）。行 35 は `HostPolicy.max_ref_slots`（既定 4,000,000）と検証済み評価器の `Limits.max_slots`・`Stop::HostSlots` で実装し、超過は `HostAborted("ref-slots")` とする。host-policy の識別子は `tlvm-rust-host-v1` に改めた。行 37 は型比較の cache（`TypeSharing::On`）で実装し、論理 trace・仕事量・cutoff は Off と同じになる。interning は未実装である。行 54 は `eval/harness.py` の `render` と連結 arm `gen-render` で実装した。実測（G4）は行っていない。残りは [対応表](../conformance/regression-tests.md) の「残りの扱い」に記す。

DECISION-11 の追記（2026-10-15）：行 37 の interning を `TypeSharing::Interned` として実装した（[intern.rs](../../crates/tlvm/src/intern.rs)）。既定は Off のまま。行 37 は対応になった。上の決定の本文は書き換えていない。

DECISION-12（§18.1c の計数の木、2026-10-14）：オーナーが「入力の木で数える」を選んだ（推奨の A。書換え後の木で数える案は採らない）。型検査の論理仕事量は、型検査器が読む木（書換えの前）で数える。実行の参照イベントは書換え後の木で数える。書換え後の大きさの上限は、次の決定として出した（設計書 §11.4）。

DECISION-13（書換え後の大きさの上限、2026-10-14）：オーナーが「上限を新設する（推奨）」を選んだ。書換え後のプログラムの bytes に上限 4,194,304 を置き、型検査を通ったプログラムについて、検証済み部品へ渡す文字列で検査する（`E-LIMIT-STATIC-REWRITTEN-BYTES`）。値は計測で決めた。2.2 MB の書換えは約 2.7 秒で受理され、4.4 MB は上限で拒否された（約 7 秒）。原文の上限（1 MiB）の 4 倍で、入力 profile の 4 MiB とも揃う。profile の識別子 `static-v1-reference-1` は変えていない（凍結前の候補。凍結時に識別子を決める）。拒否までの時間は、同日に書換えを要しないものの複製をやめて抑えた（設計書 O-7）。参照実装（release）では約 9 MB の拒否は約 1 秒（以前は約 11〜16 秒）。

DECISION-14（§18.1c の未了の項目、2026-10-14）：次の二点は、推奨の案をオーナーが選んで確定した（2026-10-14）。(1) 書換え後の式深さを、§18.1 の式深さの上限（256）で検査する。その拒否（`E-LIMIT-STATIC-EXPR-DEPTH`）を §18.1 に書いた。上限は増やさない。(2) 成功した run の結果に整数の bit 数を含めない。上限の検査は評価器の割当ごとに行う（既存の動作）。取り出しを足す案は、検証済みの評価器と Verus の再検証が要るため採らない。

DECISION-15（印つきの構築の形、2026-10-14）：オーナーが、実装の形に合わせることを選んだ（推奨）。再帰する直和型の構築は、印を式の中に直接書く（`<名前>_wrap` は作らない）。v1.15 差分 §3 の文言を、この形に合わせて直した。計数の fixture（代表 program の 472 と 356）は変えない。

DECISION-16（v1.0.0 のパッケージの範囲、2026-10-15）：オーナーが「対象外と明記（推奨）」を選んだ。v1.0.0 のパッケージは、ローカルのディレクトリの依存だけとする。レジストリからの取得、版の範囲指定と解決、ロックファイルは対象外と仕様に書いた（[v1.16 差分仕様](../../spec/lptl-v1.16/LPTL_v1.16_delta.md) §0）。取得と版の解決は、後の別の版で扱う。

DECISION-17（速度の目標、2026-10-15）：オーナーが「基準値だけ残す（推奨）」を選んだ。v1.0.0 の条件に性能の目標は置かない。計測の基準値（共有のロードマップ §7）だけを残す。目標の値は、利用者が決めてから別に書く。

DECISION-18（exec の Dict の形、2026-10-15）：オーナーが「二つの形を書く（推奨）」を選んだ。`tlvm exec` の entry の Dict は `Dict<String, String>` と `Dict<String, Int>` だけで、標準入力の行から作る。この二つは [v1.13 差分仕様](../../spec/lptl-v1.13/LPTL_v1.13_delta.md)（冒頭の「この版に含めないもの」と §1a）に書いてあり、実装は変えない。ほかの鍵・値の型の Dict は `UnsupportedEntry`（終了コード 64）になる。

DECISION-19（型の誤りがあるプログラムの整形、2026-10-15）：オーナーが「型検査を通してから整形」を選んだ。`tlvm fmt` と LSP の整形は、`tlvm check` と同じ検査（構文・名前・型・静的な上限・import）を通ったプログラムだけを整形する。誤りがあれば整形せず、`tlvm fmt` は診断を出して終了コード 1、LSP は `null` を返す。警告だけの文書は整形する。仕様（[v1.12 差分仕様](../../spec/lptl-v1.12/LPTL_v1.12_delta.md) §2b）と実装（`main.rs`、`lsp.rs`）を変えた。

DECISION-20（cargo fmt、2026-10-15）：オーナーが「別コミットで適用（推奨）」を選んだ。リポジトリ全体へ `cargo fmt` をかけた。動作を変えない別コミット（`56c5ce5`）で、`cargo fmt --check` は通る。CI の段に fmt は加えていない。

Verus は本コンテナでソースからビルド済み（0.2026.10.07.89f8d65、Z3 4.16.0）。リポジトリの証明（`tlvm-verified`）は実行で 667 件が検証され、error は 0 件（v1.1 レコードの試作 `5566e09` の後、2026-10-15）。この確認は上の 0.2026.10.07 で行い、`docs/implementation.md` の pin（0.2026.10.06）では再確認していない。2026-10-14 には 627 件・error 0 だったが、`cargo fmt`（`56c5ce5`）で並びが変わった `lib.rs` と `pipeline.rs` のあと、`push_inj`（`surface.rs`）と `ft_app`（`syntax_proof.rs`）が rlimit を超え、625 件・error 2 になった（HEAD で確認）。並びを戻すと 627・0、両関数に `#[verifier::rlimit(50)]` を付けると 627・0 になり、後者を採った。証明と仕様は変えていない。§11.2a の版ごとの証明は未着手。

# 設計本文に残っている作業（G0）

設計書の憲章、非目標、§2.3、§3（型・値）、§4（文法・字句・正準形）、§5.1、§5.4、§6（型規則）、§7（評価と組込み）、§8.1、§8.2、§9（JSON と plain JSON）、§11.2a、§13.3、§14.1、§17、§19.2 の node 表、§19.6 の `uncons` は v1.1〜v1.16 を含む形に改めた。本文の残りは次のとおり。畳み込みが済むまで、本文と版の差分の間に食い違いがある。

- §18.1c：v1.1〜v1.16 の追加分の計数。型検査の計数は入力の木（書換えの前）で数える（DECISION-12）。規則 G（総称の単相化）と規則 L（`loop` の結果型）を実装し、代表 program の値を [counting.rs](../../crates/tlvm/tests/counting.rs) で固定した（2026-10-14）。固定した：実行の参照イベントの代表値（P1〜P3 と再帰する型の代表）、再帰する直和型の補助関数の形、印つきと印なしの trace（一致せず、報告は規則 T）、書換えの深さの拒否（§18.1）。未了：節点ごとの規則の全体、代表以外の Steps と AllocatedNodes。書換えの深さと整数の bit 数は DECISION-14 で、印つきの構築の形は DECISION-15 で確定した。書換え後の大きさには上限 `E-LIMIT-STATIC-REWRITTEN-BYTES`（4 MiB、DECISION-13）を置いた。書換えの時間は、同日に書換えを要しないものの複製をやめて抑えた（O-7）。G0 の未達項目のまま。設計の経緯は [計数設計](../../docs/typecheck-counting-design.md)。
- §19.2 と `ast_codec_v1.schema.json`：全 node（v1.1〜v1.16）、fn の `rec` と `type_params`、識別子の除外語（名前はすべて字句表の 68 語）を反映した（2026-10-14）。文字列の制御文字、char の範囲、整数桁上限は codec が検査する。
- §20.1：v1.x の回帰行を既存テストへ対応付けた（[対応表](../conformance/regression-tests.md)、69 行。2026-10-15 時点で対応 53、部分 8、未対応 0、モデルのみ 8。2026-10-14 は対応 52、部分 9）。境界の追加は `rows_20_1_boundaries`（2026-10-14）。行 35・48・54 は 2026-10-14 に実装した。行 37 は型比較の cache（`TypeSharing::On`、2026-10-14）と interning（`TypeSharing::Interned`、2026-10-15）で実装し、対応にした。部分 8 行の残りは対応表の「残りの扱い」に記す。§20.4：schema と成果物の bytes・SHA-256 を 2026-10-14 に再記録した。§18.1c の改訂と書換えの時間の記述の改訂で、設計本文の bytes・SHA-256 を再記録した（現在の値は後の再記録）（manifest と検証バンドルの表）。どちらも G0 の未達項目。
- 証明：§11.2a の接着部分の書換えのうち、v1.1 のレコード展開だけは仕様上のモデルで証明した（`verus/src/records_proof.rs`、`5566e09`）。モデルは `records.rs` 自体を検証しない。全部の field を書いた `..base` の扱いは未決（[既知の注意点](known-caveats.md)）。ほかの版の書換えは未証明で、§11.2a の残りは未了。

# 設計状態として明示している境界

- Option の表現力上の境界を隠さない。v1 は `match_option` で payload を枝の中へ束縛できる（v1.1）。`option_fold` は含まない（[Option の境界](../language/option-boundary.md)。このページは本文の取り込みと合わせて更新する）。
- LLM に対する優位性は未測定である。
- 文書で手順を選択したことを、実装の決定性や実験の識別可能性が確認済みという意味にしない。
- 本書は目的・原理から一意に決まらない数値（最終評価の B、反復数、最低効果量、採否閾値）を設定しない。

[^lptl-design]: LLM向け純粋・全域言語：設計方針 v1
[^manifest]: v1 artifact manifest
