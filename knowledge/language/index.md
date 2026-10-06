# 言語

* [型と値](types-and-values.md) - Int/Bool/Unit/List/Option/Pair の6型と、有限木としての値
* [Option の境界](option-boundary.md) - v1 の Option は生成・伝達・比較のみで、一般 payload の取り出しはできない
* [字句規則](lexical-syntax.md) - ASCII のみ、符号付き INT 単一トークン、行コメント、予約語
* [文法と宣言終端](grammar.md) - EBNF、特殊形式と strict call、改行なし宣言列
* [正準フォーマット](canonical-formatting.md) - バージョン付き formatter の出力規則
* [名前解決とスコープ](names-and-scoping.md) - トップレベル一意性、非再帰 let、シャドー禁止、前方参照
* [entry と到達可能性](entry-and-reachability.md) - entry 検査の name/entry phase 分割と W-UNUSED-FUNCTION
* [呼出しグラフと DAG](call-graph.md) - 自己辺を含む全循環の拒否と rank 構成
* [型規則](typing.md) - 単相の注釈、if/let/fold 規則、arity 検査と ErrorType 回復
* [組込み関数](builtins.md) - 14個の組込みの型規則スキームと意味
* [動的意味論](dynamic-semantics.md) - 左から右の call-by-value、let・if・fold の評価
* [プログラム例](examples.md) - 偶数の合計、正の値の抽出、v1 で書けない例
