---
okf_version: "0.2"
---

# LPTL / Tolvemi ナレッジバンドル

LLM向け純粋・全域言語 LPTL（LLM-Pure Total Language）設計方針 v1 と、その公開名称 Tolvemi（トルベミ、省略表記：tlvm）の知識を Open Knowledge Format v0.2 でまとめたバンドル。一次資料は [`/spec`](../spec/) にある設計書・検証資料で、本バンドルの各 concept は `sources` でそこへ遡れる。

* [概要](overview/) - 憲章、名称、範囲、基本契約、設計状態と出荷ゲート
* [言語](language/) - 型と値、字句、文法、名前、entry、呼出しグラフ、型規則、組込み、動的意味論、例
* [保証](guarantees/) - 停止性の証明構造、Verus の層分離・証明義務・信頼境界
* [API とコーデック](api/) - compile/decode/run の分離、値 JSON、strict JSON、AST codec、ハッシュ
* [診断](diagnostics/) - 診断 schema、パイプライン、件数と recovery、コード一覧
* [資源](resources/) - 資源モデル、static/parse/typecheck/input/execution の各 profile
* [LLM 統合と評価](llm-evaluation/) - 運用原則と Skill、評価モード、事前登録と指標
* [将来拡張](future/) - Option 消去と安全リスト分解
* [適合と検証](conformance/) - 必須回帰テスト、検証バンドル、限定検査
* [参照](references/) - 識別子レジストリ、限定検査の実行手順と attester
