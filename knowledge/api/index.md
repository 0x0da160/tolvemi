# API とコーデック

* [API 分離](api-separation.md) - compile / compile_ast / decode_input / run の別 API・別結果型
* [値 JSON codec](value-json-codec.md) - Int を十進文字列で表す tag 付き正準 JSON と往復性
* [strict JSON と decode 順序](strict-json.md) - input と AST 共通の段階順、scalar・重複キー、値位置ごとの検査順
* [AST codec](ast-codec.md) - ast_codec_v1 の node schema、transport 拒否、Surface との公平性
* [ハッシュと同一性](hashes-and-identity.md) - 成果物 hash、structural_hash、仕様結合 hash、再現 record
