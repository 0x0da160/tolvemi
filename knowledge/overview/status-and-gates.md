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

G0 の未達項目は、対応 spec、完全な diagnostic registry、Admission・実行・型検査の参照 trace fixture、strict parser／encoder／共通検査器との適合照合。限定 schema 検査や補助モデルの通過（[限定検査](../conformance/limited-checks.md)）をゲートへ代用しない。

# v1.0.0 の凍結に関する決定

回答済みの決定は DECISION 行で記録します。未回答の項目は「未決定」と書きます（2026-10-13 時点）。

- DECISION-1（範囲）：設計書の核を v1 とする（route A）。レコード、直和、match、型引数、再帰、Char・String・Result、div、dict、Option 消去は v1 の外。【DECISION-4 により置き換え】
- DECISION-2（拡張の扱い）：検証済みの仕様（verus/）は据え置き、v1 の判定が拡張を拒否する。【DECISION-4 により置き換え】G0 の「後続の Option 消去候補と混在させない」は option_fold を指し、DECISION-4 のあとも有効。
- DECISION-3（凍結の条件）：Verus で証明が要る G0 の項目を満たしてから凍結する。G1〜G4 を凍結の条件に含めるかは、DECISION-7 で決めた。
- DECISION-4（範囲）：実装済みの機能（v1.1〜v1.16）をすべて v1 に含める。非目標は実装と照合して改めた（設計書 2.2 節、2.3 節）。option_fold は実装がないため v1 の外。DECISION-1 と DECISION-2 を置き換える。
- DECISION-5（字句表、D2）：字句表は実装の 68 語とする。予約語 19、文脈キーワード 49。
- DECISION-6（凍結の時期、D6）：未証明の書換えを残して凍結しない。証明を終えてから凍結する（DECISION-3 を支持）。
- DECISION-7（凍結条件、G1〜G4）：凍結条件は G0〜G4 のすべてとする。G4 は事前登録した実験の実施と公開を条件とし、正の優位性は条件としない（設計書 §15）。

未決定（推奨つき。D2、D4、D6 は DECISION-5、4、6 で決定済み）：
- D2 は DECISION-5 で決定。字句表は実装の 68 語（`crates/tlvm/src/syntax.rs` の KEYWORDS）。うち 19 語は予約語、49 語は文脈キーワード（`SOFT_KEYWORDS`）。設計書 §4.2 に書いた。
- D3 括弧は山括弧。実装は `list<Int>` と `none<Int>()` を受理し、`list[Int]` は E-PARSE-EXPECTED-TOKEN で拒否する。
- D4 は DECISION-4 で決定：Char・String・Result・div を v1 に含める。
- D5 作業量・Admission・実行の trace は適合試験の glue。
- D6 は DECISION-6 で決定。証明まで凍結しない（DECISION-3 を支持）。
- D7 v1 の判定は実装済みの拡張タグを受理する。「厳格に拒否」から変更（DECISION-4 による）。
- D8 実行の trace は設計書どおり。
- D9 補助の行は G0 の必須から外す。
- D10 SKILL.md は「仕様と照合する」と書き直す。
- D11 spec_version は凍結時に決める（候補は lptl-v1.0.0）。
- D12 設計書の 1330・1332 行（型検査の cutoff、AST の重複 key）は実装のある規則なので v1 の対象とする。「対象外」から変更（DECISION-4 による）。

このコンテナでは github.com への接続が 403 で拒否されるため、Verus（GitHub のリリース）を取得できません。証明は、github.com の許可のあとに進めます。

# 設計本文に残っている作業（G0）

設計書の憲章、非目標、§2.3、§11.2a、§13.3、§14.1 は v1.1〜v1.16 を含む形に改めた。本文の残りは次のとおり。畳み込みが済むまで、本文と版の差分の間に食い違いがある。

- §3.1、§3.2：型（`Char`、`String`、`Result`、`Dict`、レコード、直和、名義、型引数）と値。値の角括弧は山括弧へ（v1.1 §1a）。
- §4.1：EBNF の生成規則。字句表（§4.2）は DECISION-5 どおりに書いた。
- §5.4：呼出しグラフから `rec` 関数への辺を除く（v1.7）。
- §6、§7：型規則と組込みの意味。v1.1〜v1.10 の組込みと書換え、`rec` の評価。
- §9、§19、§20.1：正準 JSON、AST codec（新しい tag）、`uncons` の callee 規則（v1.1 で廃止）、`none[Foo]` の期待コード（v1.1 で E-PARSE-EXPECTED-TOKEN）。
- §18：資源の計数。新しい組込みと書換えの計数。
- §20.4：schema を変えたあとの bytes と SHA-256 の再記録。
- 証明：§11.2a の義務。Verus を実行できる環境で版ごとに作る。

# 設計状態として明示している境界

- Option の表現力上の境界を隠さない。v1 は `match_option` で payload を枝の中へ束縛できる（v1.1）。`option_fold` は含まない（[Option の境界](../language/option-boundary.md)。このページは本文の取り込みと合わせて更新する）。
- LLM に対する優位性は未測定である。
- 文書で手順を選択したことを、実装の決定性や実験の識別可能性が確認済みという意味にしない。
- 本書は目的・原理から一意に決まらない数値（最終評価の B、反復数、最低効果量、採否閾値）を設定しない。

[^lptl-design]: LLM向け純粋・全域言語：設計方針 v1
[^manifest]: v1 artifact manifest
