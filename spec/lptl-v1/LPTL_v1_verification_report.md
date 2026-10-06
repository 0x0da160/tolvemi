# LPTL v1 統一版：突き合わせ確認報告

確認日：2026-10-01。

## 1. 変更範囲と判定

文書版だけでなく、codec、schemaのID・title・codec固定値、10設計契約ID、研究arm、検証段階、ハッシュdomain、検査資料・参照ファイル名をv1の名前空間へ統一した。改訂履歴を含まない現行設計本文として作成した。

意図的に変更したのは識別子、codecが受理する固定文字列、hash preimage、それらに依存するschema／入力fixture／期待値／参照／実体hashである。計算意味論、言語文法、型規則、評価順、資源数値上限、診断コード、検査順、評価集計条件は保持した。名前空間変更を無変更やbyte互換とは扱わない。

確認範囲で、指定外の計算規則の変更・必要情報の欠落・新たな論理矛盾は検出しなかった。文書の意味保存の機械証明、原文の無欠陥保証、処理系適合証明ではない。

比較基準となる添付本文のSHA-256：`6e2565cf4e7f495f81416b85c8ba1328250cf926ea981118982a2ca79f040b9c`。原本・添付資料は上書きしていない。過去に記録された実体hashを新成果物のhashとして流用していない。

## 2. v1識別子

| 対象 | 統一後の識別子 |
|---|---|
| 文書・言語ラベル | `v1` |
| AST codec | `ast_codec_v1` |
| AST schema | `ast_codec_v1.schema.json` |
| Schema ID | `urn:lptl:ast-codec:v1` |
| Schema title | `LPTL ast_codec_v1` |
| Static profile | `static-v1-reference-1` |
| Parse Admission | `parse-admission-v1` |
| Typecheck cost | `typecheck-cost-v1` |
| Input profile | `input-v1-reference-1` |
| Input Admission | `input-admission-v1` |
| Diagnostic pipeline | `diagnostic-pipeline-v1` |
| Evaluation protocol | `evaluation-protocol-v1` |
| Reference cost model | `resource-profile-v1-reference-1` |
| AST transport profile | `ast-transport-v1-reference-1` |
| Execution profile | `execution-v1-reference-1` |
| 研究arm | `v1-no-let`、`v1-no-cons-concat-reverse` |
| 検証段階 | `V1-A`、`V1-B`、`V1-C` |

ハッシュdomainは次の4固定値とする。表中の `\0` は実際のhash入力でNUL byteを表し、文字 `\` と `0` の2byteではない。

| 用途 | Domain |
|---|---|
| 言語成果物 | `LPTL-artifact-v1\0` |
| AST構文 | `LPTL-AST-v1\0` |
| 規範仕様結合 | `LPTL-spec-bound-syntax-v1\0` |
| 再現record | `LPTL-reproducibility-v1\0` |

`spec_version` は引き続きnullである。設計書やcodecをv1と名付けたことは、規範specが確定・実装されたことを意味しない。仮のv1を正式spec_versionとして発行せず、仕様結合hash・再現hashも正式値を発行しない。検査に用いる `spec-test-a`／`spec-test-b` は版分離を試す架空fixture IDであり、規範仕様の公表版ではない。

JSON Schema Draft 2020-12、Python、jsonschemaの実際のバージョンは外部規格・依存ソフトウェアの識別であるため、v1へ偽装しない。

## 3. 突き合わせ結果

構造・名前空間・契約照合は34項目中34項目通過。

| 確認対象 | 結果 |
|---|---|
| 第0–20節 | 21主要節を保持 |
| コードブロック | 全34ブロック。codec／domainのv1置換以外は内容・順序一致 |
| 診断コード | 52種類、追加・欠落なし |
| 重要な表 | 12対象節で、ID置換以外の数値・型・keys・期待結果が完全一致 |
| Schema構造 | 変更はID・title・codec constの3箇所だけ。tag・keys・pattern・予約語・型条件は保持 |
| AST identity例 | v1 schemaへ適合。旧名前空間のcodecはv1 schemaが拒否 |
| 節参照 | 削除履歴小節への参照なし。現在の節へ解決 |
| ファイル・本文参照 | schema filename、codec、契約、domainを一致させ、実体hashを再計算 |

限定fixtureは、比較基準の92件を再実行して92件通過した後、v1化した同じ92件を再実行して92件通過した。33件の入力中のcodec文字列を変更し、仕様結合preimageの期待値1件を更新した。期待値は元の期待preimage bytesへ指定のcodec置換を施して作成し、更新したモデルの実出力をそのまま期待値にコピーしたものではない。その他の期待値は不変で、観測値もcodec表現差を除けば一致した。

検査IDは `v1-C001`–`v1-C092` に統一した。末尾LFに関する2件は別patternを使う対照schemaの挙動確認であり、v1受理schemaが末尾LFを許すことを意味しない。添付の検査順は保存し、対応表には元のfixture順番号を記録した。

実行環境：Python 3.12.8、jsonschema 4.23.0、Draft202012Validator。schemaメタ検査も通過。92種類のfixtureの比較実行であり、184種類の独立検査とは数えない。

論理整合性は次の相互依存を読み合わせた。各項目で、指定外の変更や新たな矛盾は検出しなかった。

| 対象 | 参照節 | 確認内容 |
|---|---|---|
| 型・評価・停止性 | 3、5.4、6–8 | 型・組込み・評価順・DAG／foldの停止性構造を保持。 |
| entry・arity・cutoff | 5.2、6.1、10、18.1a–18.1b | name失敗／semantic cutoff後の停止、arity候補生成の時点、Admission順を保持。 |
| JSON・入力・AST | 9、19 | 浅い型→Admission→内容、scalar→重複→内容、param例外、元byte span契約を保持。codec識別だけ意図的に変更。 |
| 資源・共有・ホスト境界 | 8.3–8.5、18 | 全数値上限と論理計数を保持。host-policyと参照profileを区別。 |
| 評価計画 | 12、15 | episode分母、予算vector、停止と実測超過、既存Accepted候補、隠しテスト一件選択を保持。arm名だけv1へ統一。 |
| hash・spec・出荷状態 | 4.3、17、19.4、20 | v1 domain／codecに統一。spec_versionは未確定、正式仕様結合hashは未発行。G0未達、G1–G4未判定を保持。 |

## 4. 互換性と実体hash

旧名前空間とのcodec互換は維持しない。v1 schema／補助decoderは `ast_codec_v1` を要求し、旧codecをaliasとして受理しない。契約IDを利用する設定・registry・再現record・実装・実験記録も、v1の識別子へ揃える必要がある。本成果物に実装されていないregistryや処理系まで自動更新・適合確認したとは主張しない。

ASTの正準JSONにはcodecが含まれ、構文hashのdomainも変更したため、同じ計算を表すASTであっても旧hashをv1のhashとして流用しない。成果物hashのdomain変更と、仕様結合hashに含まれるcodec変更も反映した。仕様結合／再現domainはv1の固定値へ統一し、未確定spec時の未発行条件を保持した。

新しいschemaは10,590 bytes、SHA-256は `eefa368250b12a11afc842c6f92dc03348a18a9e946a4626b23794a17341e593`。schemaをbyte同一と称さない。文書中のschema実体表もこの値へ更新した。他の配布ファイルのbytes／SHA-256は同梱manifestへ記録した。文書・manifest・ZIPは自己hashを内部へ埋め込まない。

## 5. 配布資料と検証限界

配布資料は、v1設計本文、本確認報告、v1 AST schema、検証資料ZIPである。ZIPには本文・報告・schema、限定検査コード、入力・期待値、観測CSV、fixture対応表、構造照合JSON、編集範囲一覧、manifestを含む。配布ファイル名とテキスト内容について、旧成果物の版ラベル・改訂suffixの残存を検査した。

限定検査の再実行は、ZIPを同じディレクトリへ展開して `python v1_limited_checks.py` とする。Python 3.12、jsonschema 4.23.0を使用する。結果CSVは再生成されるため、環境が異なる場合や実体bytesが変わった場合は新しい実行として記録する。

未検証なのはRust/Verus specとの照合、LPTL処理系、strict JSON token parser、全型input decoder／encoder、元byte span、message／repair、transport guards、host behavior、追加予算成分・provider usage集計、reproducibility recordの実装適合、機械証明、LLM実験である。BLAKE3 digestは計算・検証していない。固定文字列・codec・hash preimageの変更と、ファイル実体のSHA-256再計算を確認した。

凍結候補、G0未達、G1–G4未判定という状態は保持する。有限fixture通過を無欠陥・実装適合・形式証明・出荷の宣言へ代用しない。
