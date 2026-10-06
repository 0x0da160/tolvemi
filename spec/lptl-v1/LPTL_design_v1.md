# LLM向け純粋・全域言語：設計方針 v1

> 状態：凍結候補。実装完了・証明完了・出荷を意味しない。  
> 文書日付：2026-10-01。文書版：`v1`。  
> 規範性：実装時の唯一の規範的意味論は Rust/Verus プロジェクトの `spec` 層とする。本書は、その実装に向けた契約案・公開投影の設計書であり、既存 `spec` と照合済みとは主張しない。対応する `spec`、codec、profile、診断の版と適合テストが揃うまで凍結・出荷を宣言しない。

本成果物の文書版、codec、schema、設計契約、研究arm、検証段階、ハッシュdomainの版ラベルはv1とする。各識別子は用途ごとに独立した固定文字列であり、正確な綴りは各該当節に定義する。規範仕様の `spec_version` は未確定（null）であり、文書版v1やcodec IDで代用しない。v1の名前空間を使用し、別の名前空間のcodecや契約IDを同一識別子として受理・解釈しない。ハッシュdomainとcodec bytesに依存するhash値について、別の名前空間との互換性を保証しない。JSON Schemaの標準版や検査依存ソフトウェアの実際の版は、成果物の版ラベルと区別する。

---

## 0. 憲章

**LPTL（LLM-Pure Total Language）** は、有限データ上の純粋な計算のための、静的型付き・決定的・全域な DSL である。

整形式かつ受理済みの LPTL プログラム `P` の entry 関数を、有効な有限入力 `i` に適用すると、数学的意味論において必ず停止し、宣言戻り型に属する一意の有限値 `v` を返す。

```text
well_formed(P) ∧ i ∈ Value(T_in)
  ⇒ ∃! v ∈ Value(T_out). P(i) ⇓ v
```

数学的命題の前提は、固定された数学的仕様、整形式プログラム、型に属する有限入力であり、物理ホストや処理系の存在ではない。well_formedには名前・scope・型・DAG・唯一のarity=1 entryの成立を含む。受理済みならwell_formedを満たすことを処理系適合の証明対象とし、well_formedでも有限profileにより静的拒否され得る。実装上の成功については、検証済み実装範囲、明示的な信頼境界、当該runに十分な参照予算とホスト資源、出力codec完了が別に必要である。ソース不正、静的拒否、入力デコード失敗、資源超過、タイムアウト、処理系障害は、言語意味論上の値・例外・非停止とは別のホスト結果である。

LPTL は一般目的言語ではない。第一の用途は、LLM を含む外部提案器が生成した有限・純粋・決定的ロジックを、型・停止性・決定性・資源契約の下で受理・実行する高保証計算カーネルである。第二の用途は、LLM の生成・修復に対する構文、意味論、診断、Skill、表記の寄与を分解して測定する研究基盤である。

「LLM に最適」「LLM の意味的成功率を改善する」「実運用で優位」といった経験的主張は、形式保証から導かれない。仕様、Skill、評価器、予算、対照、最終タスクを固定した比較実験でのみ判断する。

---

## 1. 基本契約

本コアは機能範囲を限定し、次の契約を採用する。詳細な条件・順序・例外は各該当節に定義する。

1. entry は parse 成功後に構文個数を収集する。未知 entry は name phase、欠落・重複・引数数は entry phase とし、name 失敗時は entry phase を実行しない。
2. トップレベル本体の終端は、完成した一つの expr の直後の `fn`、`entry`、EOF に限定する。改行なしの宣言列も受理する。
3. DAG 検査は `call-graph` phase で行い、静的資源検査から分離する。
4. 静的上限は取得できる最初の時点で検査する。上限超過は後続を停止し、未実行の検査を成功とは扱わない。
5. arity は typecheck phase で検査し、全ての実引数式を検査するが、arity 不一致の呼出しでは期待引数との型比較を抑制する。
6. `none[Foo]` は閉じた型文法への不適合として `E-PARSE-EXPECTED-TYPE` とする。
7. bytes API、値 codec、AST 専用 codec、repair schema、recovery 終了規則、資源計数を契約として定義する。
8. `Pair<A, B>` の二成分は独立した型である。正準 JSON の例とキー順は第9節に定義する。
9. `fold` 内の呼出しも呼出しグラフに含め、関数 rank と反復長の帰納を接続する。
10. `match_option`、`option_fold`、`uncons` は本コアに含めない。将来の独立拡張版で一体的に審査する。

---

## 2. 対象範囲

### 2.1 設計目標

1. **全域性**：受理プログラムは有効な有限入力で停止する。
2. **型安全性**：評価結果は宣言型の有限値であり、動的型エラーを生じない。
3. **決定性**：同一のプログラム、入力、仕様版に対する結果は一意である。
4. **構文的正準性**：曖昧な表面構文を避け、AST を一意に復元しやすくする。
5. **局所修復可能性**：失敗を安定コード、位置、期待制約、決定論的順序で返す。
6. **実装適合性**：仕様、コンパイラ、codec、実行器、資源結果を分離して検証する。
7. **実験分解性**：言語制限、表記、制約付き生成、診断、Skillの介入を明示し、識別可能な効果だけを評価・主張する。モード名や受理規則の共通化だけで独立効果が識別されたとは扱わない。

### 2.2 非目標

初期コアは以下を含まない。

- 一般再帰、相互再帰、自己参照 `let`
- 第一級関数、自由ラムダ、クロージャ
- 可変状態、参照、例外、外部 I/O、並行性
- 文字列、浮動小数点、日時、正規表現
- ユーザー定義 ADT、レコード、パターンマッチ
- ユーザー定義型変数、型スキーム、let 多相性、ランク多相性、型クラス
- サブタイピング、暗黙変換、オーバーロード、デフォルト引数、可変長引数
- 演算子構文、演算子優先順位、マクロ、ホスト言語エスケープ
- 部分関数的な `head`、`tail`、添字アクセス、除算
- `uncons`、`match_option`、`option_fold`（将来の独立拡張候補）
- JSON number による `Int` の入出力

`List<T>`、`Option<T>`、`Pair<A,B>` はパラメータ化された型構成子である。これはユーザーが型変数を抽象化・量化する多相型機構を意味しない。

---

## 3. 型と値

### 3.1 型

```text
T, A, B ::= Int | Bool | Unit
    | List<T>
    | Option<T>
    | Pair<A, B>
```

- `Int` は数学的任意精度整数。
- `Bool` は `true` と `false`。
- `Unit` の唯一の値は `unit`。
- `List<T>` は有限個の `T` 値からなる順序付き同種リスト。
- `Option<T>` は `none` または `some(v)`。
- `Pair<A,B>` は `pair(v,w)`。

型等価性は構文的等価性である。v1 の全型は構造的等値可能である。ただし、将来導入される型が自動的に等値可能になることはない。等値可能性は型ごとに明示する。

### 3.2 値

```text
v ::= 整数 | true | false | unit
    | list[T](v, ...)
    | some(v) | none[T]
    | pair(v, v)
```

値は有限木としての数学的値である。実装は共有を持つ不変 DAG 表現を使用してよいが、観測可能な意味は有限木の展開として定義する。循環値、参照値、関数値、未初期化値は存在しない。

### 3.3 Option の境界

v1 の `Option<T>` は、部分性を言語エラーではなく値へ写すための構成子である。

- `some(e)`、`none[T]`、`mod` により生成できる。
- `let`、`pair`、`list` 等で保存・伝達できる。
- `eq` により、`none[T]` または有限個の既知 payload を持つ `some(c)` と比較できる。
- **一般 payload を束縛して取り出す消去構文はない。**

従って v1 は、任意の `some(x)` から未知の `x` を抽出する処理、`uncons` の結果から先頭要素を取得する処理、動的除数の `mod` 結果を一般の整数計算へ渡す処理を対象にしない。この能力は `match_option` 等を含む後続版でのみ導入する。

---

## 4. 表面文法

compile API は任意の `source_bytes` を受け取る。source bytes 上限を先に検査し、上限内の不正 UTF-8 は `SourceBoundaryFailure(InvalidSourceEncoding)` とする。UTF-8 検査に成功した列だけを lexer に渡す。上限超過は `CompileResult::Rejected(E-LIMIT-STATIC-SOURCE-BYTES)` であり、UTF-8 の妥当性は検査しない。

コメントを除く受理文字は ASCII のみである。Unicode 識別子、文字列リテラル、Unicode 正規化、エスケープ構文は対象外である。

### 4.1 EBNF

```ebnf
program      ::= { top_decl } EOF
top_decl     ::= function_def | entry_def

function_def ::= "fn" IDENT "(" [ params ] ")" "->" type "=" expr
entry_def    ::= "entry" IDENT

params       ::= param { "," param }
param        ::= IDENT ":" type

type         ::= "Int" | "Bool" | "Unit"
               | "List" "<" type ">"
               | "Option" "<" type ">"
               | "Pair" "<" type "," type ">"

expr         ::= INT | "true" | "false" | "unit" | IDENT
               | "list" "[" type "]" "(" [ arguments ] ")"
               | "some" "(" expr ")"
               | "none" "[" type "]"
               | "pair" "(" expr "," expr ")"
               | builtin "(" [ arguments ] ")"
               | "let" IDENT "=" expr "in" expr
               | "if" "(" expr "," expr "," expr ")"
               | "fold" "(" expr "," expr "," lambda ")"
               | IDENT "(" [ arguments ] ")"

builtin      ::= "add" | "sub" | "mul" | "neg"
               | "lt" | "le" | "eq" | "mod"
               | "fst" | "snd"
               | "cons" | "concat" | "reverse" | "length"

lambda       ::= "|" IDENT "," IDENT "|" expr
arguments    ::= expr { "," expr }
```

`if`、`fold`、`let` は特殊形式であり、`builtin` とユーザー関数呼出しは strict call である。改行は空白であり、宣言終端ではない。

`fn` と `entry` は `expr` を開始できない予約トークンである。function_def は完全な一つの expr を読み、その式の全ての開いた構文構造を閉じた後、次トークンが `fn`、`entry`、EOF のいずれかなら終了する。その他が続けば `E-PARSE-UNEXPECTED-TOKEN`。未完の式の途中の `fn`／`entry` は正常終端ではなく parse error とする。entry_def も IDENT の直後に同じ終端集合を要求する。

従って以下は改行なしで受理する。formatter は宣言ごとに改行する。

```text
fn f(x: Int) -> Int = x fn g(y: Int) -> Int = y entry f
```

`some`、`pair`、`list`、`none`、`if`、`fold` は専用構文である。その固定位置の欠落・過剰要素は parse error であり、通常の組込み call の arity error と混同しない。

### 4.2 字句

```text
IDENT ::= [A-Za-z_][A-Za-z0-9_]*
INT   ::= 0 | -?[1-9][0-9]*
```

- `INT` は先行する `-` を含む**単一の字句トークン**である。
- `-` は `INT` の符号以外の独立トークンではない。従って `1-2`、`- 2`、`--2` は字句不正である。
- `sub(1,-2)` と `f(-2)` は `-2` を `INT` として受理する。
- 字句解析は最大一致を使う。ただし整数直後に `IDENT` 開始文字が連続する列、例えば `12x` は `INT(12), IDENT(x)` へ分割せず、`E-LEX-INVALID-NUMERIC-BOUNDARY` とする。
- `-0`、`+1`、先頭ゼロ付き非零整数、指数表記、桁区切り、16進表記を拒否する。
- 空白は ASCII space、tab、CR、LF のみ。
- コメントは `//` から次の CR、LF、EOF の直前までの行コメントのみ。コメント内は有効 UTF-8 を許す。ブロックコメントはない。
- 非コメント部の非 ASCII は `E-LEX-NON-ASCII`。UTF-8 BOM は空白でもコメントでもなく拒否する。
- EOF とコメント・空白はトークン数に含めない。全ての予約語、識別子、整数、句読点をそれぞれ一トークンとする。
- 予約語は EBNF 中の全固定語である。lexer は予約語を `IDENT` として返さない。
- 予約語を関数名、変数名、型名に置いた場合、parser は `E-PARSE-EXPECTED-IDENT` として拒否する。

### 4.3 正準ソースとハッシュ

フォーマッタはバージョン付き公開成果物である。

- `,` の直後に ASCII space を一つ置く。
- `Pair<A, B>` のカンマ後に ASCII space を一つ置く。
- 整数は `INT` の正規形で出力する。
- コメントは正準出力から除去する。
- フォーマッタは名前・型に依存する書換えを行わず、AST の意味を保存する。
- 宣言順序・名前・型注釈を保持し、各宣言を一行に出力する。関数は `fn NAME(PARAMS) -> TYPE = EXPR`、entry は `entry NAME` とする。
- 引数は `NAME: TYPE`、let は `let NAME = EXPR in EXPR`、fold lambda は `|ACC, ITEM| EXPR`。call は `NAME(ARGS)`、型引数のある構成子は `list[TYPE](ARGS)`／`none[TYPE]` とする。
- 句読点周辺は上記の空白以外を挿入せず、宣言間は LF 一つ、末尾も LF 一つ。インデント・空行・CR は出力しない。

`canonical_source(P)` は、受理済み AST を formatter が UTF-8 で出力した値である。実験・配布・改竄検知の基本ハッシュは次である。

```text
BLAKE3(
  "LPTL-artifact-v1\0" ||
  spec_version || "\0" ||
  canonical_source(P) || "\0" ||
  resource_profile_id || "\0" ||
  skill_hash
)
```

個別プログラムのcodecレベルの構文的同一性には、第19.4節のstructural_hashを用いる。規範仕様版に結び付ける場合は同節のspec_bound_syntax_hashを用いる。structural_hash単独はspec_version、診断、静的検査、実行profileの互換性を表さない。これは意味等価性の完全判定ではない。alpha-renaming、宣言の並べ替え、等価な計算の書換えを同一視しない。コメント、入力時の空白、JSON object の入力順序は構文ハッシュに影響しない。構文ハッシュと実験・配布用の成果物ハッシュを区別する。

---

## 5. 名前、entry、到達性

### 5.1 名前解決

- トップレベル関数名は一意。
- 同一関数の引数名は一意。
- `let x = e1 in e2` の `x` は `e2` だけで束縛され、`e1` には可視でない。
- `fold(xs, init, |acc, item| body)` の binder は `body` だけで可視。
- `fold` の二 binder は相異なる。
- `let` binder と `fold` binder は、外側の可視変数をシャドーできない。
- 外側の関数引数、外側 `let`、外側 `fold` binder は参照できる。
- 全トップレベル関数は全プログラムで可視であり、前方参照を許可する。
- ユーザー関数のオーバーロード、局所関数、名前空間、メソッド記法はない。

### 5.2 entry 検査の分割

parse 成功後、entry 宣言を入力順に収集し構文個数 N を保存する。構文個数の収集は診断の発行ではない。

| 状況 | name phase | entry phase |
|---|---|---|
| N=0、その他の name error なし | entry 由来の error なし | `E-ENTRY-MISSING` |
| N=1、名が未知 | `E-ENTRY-UNKNOWN` | 実行しない |
| N>=2、一つ以上が未知 | 未知の宣言ごとに `E-ENTRY-UNKNOWN` | 実行しない。重複を併記しない |
| N>=2、全名が既知、その他の name error なし | 成功 | `E-ENTRY-DUPLICATE` 一件。arity は検査しない |
| N=1、名が既知、その他の name error なし | 成功 | 引数が一つでなければ `E-ENTRY-ARITY` |
| 任意の N、その他の name error あり | 通常の name 診断 | 実行しない |

N=0 で「name 成功」となるのは、他の名前解決違反がない場合だけである。resource cutoff により entry phase に到達しない場合も、欠落・重複・arity を発行しない。

重複診断の主 span は二番目の entry 宣言全体、欠落は EOF のゼロ幅 span、未知は entry の関数名、arity は唯一の entry の関数名とする。

entry の戻り型に追加制約はない。入力型・出力型は任意の LPTL 型である。

---

### 5.3 到達可能性

entry が name phase と entry phase の双方で有効なとき、entry 関数からユーザー関数呼出しをたどって到達可能な関数を **live** と呼ぶ。

- すべてのトップレベル関数は名前解決、DAG 検査、型検査の対象である。
- 各 live でないトップレベル関数ごとに、関数名 span を主 span とする `W-UNUSED-FUNCTION` を一件発行する。
- entry が無効なら到達性は定義せず、`W-UNUSED-FUNCTION` を発行しない。
- warning の上限は第10節に従う。

### 5.4 呼出しグラフ

ユーザー関数集合を `F` とし、`f` 本体が `g(...)` を含むとき辺 `f -> g` を置く。自己辺を含む全循環を拒否する。

```text
受理条件：call_graph(P) は DAG である。
```

DAG なら実装はトポロジカルランク `rank : F -> Nat` を構築し、

```text
f -> g ならば rank(g) < rank(f)
```

を満たす。循環時は `E-CYCLE-CALL` を返す。`E-CYCLE-*` は診断分類プレフィックスであり、具体コードは `E-CYCLE-CALL` である。辺は非選択枝、未到達関数、fold 本体を含む全ての構文上のユーザー call から収集する。

循環診断は循環を持つ強連結成分ごとに一件。成分内の辺の call-name span が最小のものを主 span とし、関数名の関連情報は ASCII 辞書順にする。rank は、呼出し先のない関数を0、その他を `1 + max(rank(callee))` とする。循環がある場合 rank を生成せず、実行可能プログラムを受理しない。

---

## 6. 型規則

### 6.1 注釈と単相型

- トップレベル関数の各引数型と戻り型は必須。
- `fold` binder の型は、リスト型と初期値型から一意に決まるため表記しない。
- `let` binder の型は束縛式の型から一意に決まる。let-generalization は行わない。
- リストは空・非空を問わず `list[T](...)` と書く。
- `some(e)` の型は `Option<T>`（`e:T`）で一意。
- `none[T]` の `T` は閉じた `type` 非終端記号で parse する。`none[Foo]` は `E-PARSE-EXPECTED-TYPE`。未定義のユーザー型を typecheck に渡さない。
- 関数・通常組込みの arity は typecheck で検査する。未知 call は name error だけで後続を停止する。
- 通常callのVisitExprが仕事量guardを通過した直後、子の検査前にarityを判定し、不一致なら対応するarity診断候補を一件生成する。判定と候補生成はSemanticWorkへ加算しない。arity不一致でも実引数式を全て左から右に型検査する。ただし資源cutoffで中断した後は継続しない。当該callの期待引数型との比較と結果BuildTypeは全て抑制し、通常完走時の結果をErrorTypeとする。欠落引数への二次エラーは生成しない。
- 組込み型の推論は実引数型だけから行う。`fold` の acc 型は init、item 型は xs に依存する。依存元が ErrorType なら該当 binder も ErrorType とし、依存した診断は抑制する。

### 6.2 型スキーム表記

次表中の `A`、`B` は仕様記述のメタ変数である。これはユーザーが書ける型変数でも、言語の let 多相性でもない。組込み適用の各箇所で、引数型から一意に具体型へインスタンス化される固定の組込み型規則である。

| 名前 | 型規則スキーム | 意味 |
|---|---|---|
| `add` | `Int × Int -> Int` | 加算 |
| `sub` | `Int × Int -> Int` | 減算 |
| `mul` | `Int × Int -> Int` | 乗算 |
| `neg` | `Int -> Int` | 加法逆元 |
| `lt` | `Int × Int -> Bool` | 狭義順序 |
| `le` | `Int × Int -> Bool` | 非狭義順序 |
| `eq` | `A × A -> Bool` | 構造的等値 |
| `fst` | `Pair<A,B> -> A` | 第1成分 |
| `snd` | `Pair<A,B> -> B` | 第2成分 |
| `mod` | `Int × Int -> Option<Int>` | 正の除数に対する非負剰余 |
| `cons` | `A × List<A> -> List<A>` | 先頭追加 |
| `concat` | `List<A> × List<A> -> List<A>` | 連結 |
| `reverse` | `List<A> -> List<A>` | 逆順 |
| `length` | `List<A> -> Int` | 有限長 |

### 6.3 主要規則

```text
if(c, t, f) : T
  iff c : Bool, t : T, f : T

let x = e1 in e2 : B
  iff e1 : A かつ Γ,x:A ⊢ e2 : B

fold(xs, init, |acc, item| body) : A
  iff xs : List<X>, init : A,
      Γ,acc:A,item:X ⊢ body : A
```

`if`、`fold`、`let` は AST 上でも別コンストラクタである。その他の組込みとユーザー関数呼出しは、引数を左から右へ評価する strict call である。

異型 `eq(1,true)`、異型 `concat(list[Int](), list[Bool]())` 等は静的拒否であり、実行時に `false` や空リストにはならない。

---

## 7. 動的意味論

### 7.1 評価順序

評価は純粋・決定的・左から右の call-by-value である。

- strict call では、全引数を左から右へ評価後に組込みまたは関数本体を評価する。
- `if` は条件を評価し、選択された枝のみを評価する。
- `let` は束縛式を一度評価してから本体を評価する。
- `fold` はリスト式、初期値、各反復本体の順に評価する。

### 7.2 `let`

```text
let x = e1 in e2
```

は `e1` をちょうど一度評価して値 `v` を得た後、`x=v` を環境に追加して `e2` を評価する。`x` は `e1` 内では可視でない。`let` は非再帰・不変・局所であり、代入、共有可変セル、関数再帰を導入しない。

### 7.3 `if` と `fold`

```text
if(true, t, f)  -> t
if(false, t, f) -> f

fold(list[T](), init, body) = init
fold(list[T](x1, ..., xn), init, body)
  = body(...body(body(init, x1), x2)..., xn)
```

各 fold ステップでは現在累積値を `acc`、現在要素を `item` として `body` を評価する。

### 7.4 組込み

```text
add(a,b) = a+b
sub(a,b) = a-b
mul(a,b) = a*b
neg(a) = -a
lt(a,b) = (a < b)
le(a,b) = (a <= b)
fst(pair(v,w)) = v
snd(pair(v,w)) = w

cons(x, list[T](x1, ..., xn)) = list[T](x, x1, ..., xn)
concat(list[T](x1, ..., xm), list[T](y1, ..., yn))
  = list[T](x1, ..., xm, y1, ..., yn)
reverse(list[T](x1, ..., xn)) = list[T](xn, ..., x1)
length(list[T](x1, ..., xn)) = n
```

`eq` は同型値に対する構造的等値である。リスト・ペア・Option の比較は左から右、浅い構造から深い構造の順に行い、最初の不一致で `false` を返す。等しい場合だけ全構造を走査する。

```text
b > 0 なら mod(a,b) = some(r)
  ただし a = b*q + r、0 <= r < b を満たす一意の r
b <= 0 なら mod(a,b) = none[Int]
```

`mod(-3,2)=some(1)`、`mod(1,0)=none[Int]`。

---

## 8. 停止性、決定性、資源

### 8.1 中心定理

entry 型が `T_in -> T_out` の整形式プログラム `P` と有効入力 `i:T_in` に対し、一意の `v:T_out` が存在して `P(i) ⇓ v` を示す。

### 8.2 停止性の証明構造

停止性を、曖昧な単一の「残余式仕事量」測度に依存させない。次の入れ子の帰納で証明する。

1. **関数ランク帰納**：DAG のランク `rank(f)` について帰納する。関数 `f` からのユーザー関数呼出しは必ずより小さいランクへ進む。
2. **式構造帰納**：固定した関数本体・環境における各式について構造帰納する。`let` は束縛式と本体の有限構文へ、strict call は有限個の引数と呼出し先へ還元される。
3. **リスト長帰納**：`fold` は入力リスト長について帰納する。各反復後、未処理要素数は一つ減る。
4. **組込み全域性**：算術、構造演算、構造的等値は数学的整数・有限木に対して全域である。

fold 本体内の call も現在関数からの辺であるため、呼出し先は厳密に低い rank を持つ。現在関数の直接・間接呼出しは DAG 条件が拒否する。低 rank 関数の停止性を仮定した式構造帰納の中で、fold ケースをリスト長帰納で示す。各反復本体は構造上の真部分式として停止し、リスト長帰納はその停止済み評価を有限回列化する。累積値が増大しても反復対象の入力リストは変更しない。

実装適合には燃料付き評価 `eval_fuel(P,input,n)` を定義し、停止性から

```text
∃n,v. eval_fuel(P,input,n) = Done(v)
```

を、さらに燃料単調性を示す。

```text
eval_fuel(P,input,n)=Done(v) ∧ m>=n
  ⇒ eval_fuel(P,input,m)=Done(v)
```

### 8.3 意味論的値サイズと実装資源

数学的値は有限木である。一方、実装は不変値を共有 DAG として保持できる。資源契約では次を明確に分ける。

- **SemanticTreeNodes(v)**：値 `v` を共有なしの有限木として展開したノード数。意味論的量であり、実装上の共有に依存しない。
- **ReachableHeapNodes(h)**：実装ヒープ上で根から到達可能な固有ノード数。
- **AllocatedNodeCount**：実行開始後に確保したノードの累積数。

v1 の標準資源プロファイルは、再現性のため **AllocatedNodeCount** と整数ビット長、評価遷移数を規範的に計測する。`let x = huge in pair(x,x)` は `huge` を一度評価・一度割当てるが、共有参照を二つ持つ `pair` を追加する。意味論上の木展開量と物理割当量を同一視しない。

### 8.4 参照コストモデル

`resource-profile-v1-reference-1` は第18節の参照機械と以下の割当規則を使う。

- リストは不変 cons-cell DAG。空リスト、bool、unit、none は共有 singleton であり、割当数0。none は型を保持するコンパイラ側の型情報で区別し、実行値ごとに型ノードを割り当てない。
- `cons` は一セル、`pair` は一ノード、`some` は一ノード。既存 payload は共有する。
- `list[T](e1,...,en)` は引数を左から右に評価後、要素参照を一時スタックに置き、末尾から n セルを構築する。要素のコピーはしない。
- `concat(xs,ys)` は xs の spine を先頭から走査し、要素参照を一時スタックへ置く。ys を初期末尾としてスタックを逆順に取り出し、xs の長さ m の新規セルを作る。ys と要素を共有し、LPTL の中間 cons spine を作らない。
- `reverse(xs)` は先頭から走査し、空リストを初期末尾として n セルを作る。`length` はキャッシュせず spine を走査する。
- 整数リテラルの評価、入力整数のデコード、および整数を返す算術・length は、一回ごとに一整数ノードを生成する。小整数の interning は参照モデルにない。変数参照、fst、snd、引数渡しは新規割当しない。
- 実行割当カウンタは decode と compile を含めず、run 開始時に0。入力値のノード数は input profile で別計測する。
- `eq` は第7.4節の短絡順で走査する。参照イベントと共有 pointer 一致による短絡・memoization の禁止は第18.3節に従う。
- 一時参照スタック、環境、実行 frame は AllocatedNodeCount に含めない。それらの物理資源上限（参照スロット数を含む）は host-policy で扱い、超過は HostAborted とする。reference execution profile の ResourceKind に参照スロットを含めない。
- 最大整数ビット長は `bits(0)=0`、それ以外は `floor(log2(abs(n)))+1`。入力を含む全整数値と生成結果を検査する。BigInt ライブラリの内部一時 limb はホストヒープ制限で扱う。

最適化版は参照カウンタを忠実に再現する shadow accounting を持つ場合のみ同じ reference profile を名乗れる。物理ヒープ・時間は別の host policy であり、この profile のカウンタと同一ではない。

---

### 8.5 実行資源プロファイル

資源上限は言語意味論とは別の、版付きプロファイルである。少なくとも以下を個別に公開する。

- ソースバイト数、トークン数、AST ノード数、関数数
- 型深さ、式深さ、let 深さ、fold ネスト深さ
- 整数リテラル桁数、入力 JSON バイト数、入力値深さ・ノード数
- 評価遷移数、AllocatedNodeCount、最大整数ビット長
- ヒープバイト、壁時計時間

静的上限（ソース、AST、型深さ等）の超過は `CompileResult::Rejected(E-LIMIT-STATIC-*)`、入力上限の超過は `DecodeResult::Invalid(E-LIMIT-INPUT-*)` とする。run の決定論的な execution profile 上限（Steps、AllocatedNodes、IntegerBits、OutputBytes）の超過は `RunResult::ResourceExhausted`。時間、物理ヒープ、frame、参照スロットなど host-policy 上限の超過は `RunResult::HostAborted` とする。これらは検査責務・結果型を分け、評価中に起きたという理由だけで ResourceExhausted へ統合しない。OS kill などで結果を返せない場合は第18.3節の境界に従う。

---

## 9. API と canonical JSON

### 9.1 API 分離

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

プロファイルは版付きの検証済み設定値を API に渡す。設定そのものの欠落・負上限・未知版はホスト API の設定エラーであり、プログラム診断ではない。

TypedProgram は仕様版・型・AST を含む不透明値。run は entry 入力型と一致する TypedValue だけを受け取る。型や仕様版の不一致はホスト側 API misuse であり、LPTL の動的型エラーではない。

source／AST／input はサイズ上限、UTF-8、構文の順に検査する。サイズ超過時は UTF-8 を走査しない。入力境界のサイズ違反は `DecodeResult::Invalid(E-LIMIT-INPUT-JSON-BYTES)`、AST transport のサイズ違反は `AstInvalid(E-AST-LIMIT-BYTES)`。

Completed は出力 codec まで完了した結果。出力 byte 上限は execution profile で検査し、超過は `ResourceExhausted(OutputBytes, ...)`。出力の共有木展開を無制限に行わない。壁時計期限・OS ヒープ制限は `HostAborted` とし、決定論的参照資源超過から分離する。

Compile、Decode、Run は別 API・別結果型である。AstDiagnostics は AST transport の失敗であり、name/typecheck の静的拒否とは分離する。

---

### 9.2 JSON 値形式

LPTL Int は正規十進文字列。JSON number は使用しない。以下は省略記号を含まない正準 JSON の例である。

```json
{"tag":"int","value":"-42"}
{"tag":"bool","value":true}
{"tag":"unit"}
{"tag":"list","items":[{"tag":"int","value":"1"}]}
{"tag":"some","value":{"tag":"int","value":"1"}}
{"tag":"none"}
{"tag":"pair","left":{"tag":"int","value":"1"},"right":{"tag":"bool","value":true}}
```

---

### 9.3 受理規則と正準出力

デコーダは、**object member の順序には依存しない**。有効なキー集合を持つ object で、各キーが一度だけ現れ、値が期待型に適合すれば、任意の member 順を受理する。

エンコーダは一意の正準 JSON を出力する。

- UTF-8、最小空白。
- キー順は `"tag", "value"`、`"tag", "left", "right"`、`"tag", "items"`、または `"tag"`。
- `tag` は期待型に対応する正確な文字列。
- 余分なキー、欠落キー、重複キーを拒否。
- 整数字列は `INT` の正規形。
- JSON number、JSON null、配列・object の予期しない位置、型不一致を拒否。

重複キーは、通常の map に落とす前に token stream で検出し、必ず拒否する。

### 9.3a 共通strict JSON文字列契約

本節はinputとAST transportの両方へ適用する。JSON bytes→UTF-8→JSON文法／構造深さ→string scalar妥当性→重複キー→object／値内容検査の順とする。JSON文法／構造深さの段階は元bytes上の最初の観測違反で停止する。この段階が全体で成功した場合だけscalar段階へ進み、scalar段階が全体で成功した場合だけ重複段階へ進む。streamingで検出候補を収集してよいが、この段階順を変えて返さない。文字列の走査・保管はtransport bytes／深さとホスト資源の境界内で行う。

全てのJSON string（key、tag、payload、未知field内を含む）をescape decode後のUnicode scalar sequenceとして扱う。正しいhigh＋low surrogate escape対は対応scalarへ復号する。単独high、単独low、不正な対を拒否する。scalar違反が複数なら元bytes上で最初の不正string tokenを選び、主spanは引用符を含む当該token全体とする。UTF-8不正は別の境界失敗であり、ASCII bytesのsurrogate escape違反と混同しない。

キーはdecode後のscalar列の完全一致で比較し、Unicode正規化・case変換・trimをしない。例えば"name"と"\u006eame"は重複。全objectの重複候補は二番目のkey tokenの元byte開始位置で選び、最初の一件を返す。scalar違反は重複違反より先で、重複違反はroot／子objectの内容違反より先とする。unknown keyの辞書順はscalar整数値列の辞書順であり、prefixが同じなら短い列を先とする。

inputのscalar違反はE-INPUT-STRING-SCALAR、重複はE-INPUT-DUPLICATE-KEY、文法違反はE-INPUT-JSON-SYNTAXとし、phaseはinput-parse。inputのbytes上限はinput-boundary、JSON深さ上限はinput-parse、以下のobject／値Admission／内容違反はinput-decodeとする。ASTのscalar違反はE-AST-STRING-SCALAR、重複はE-AST-DUPLICATE-KEY、文法違反はE-AST-JSON-SYNTAXでphaseはast-parse。全コードのmessage、expected／actual、その他のspan規則はG0のdiagnostic registryで照合する。


### 9.4 Decode エラー優先順位

第9.3a節の全体transport段階を通過してから、期待型を伴うroot値デコードを開始する。全体で最初の一件のみ返す。各値位置では次を順に行う。

1. objectであることを確認する。
2. tagキーの存在、string型、期待型に対応するtagを確認する。
3. 必須キー、次に余分キーを検査する。
4. 全直接fieldの浅いJSON型を第9.3節の正準key順で検査する。子object内部・array要素はまだ検査しない。
5. InputAdmission候補の値深さと累積SemanticTreeNodes次値をguardする。深さ超過をnode数超過より優先し、成功時だけ一値nodeのAdmissionを発行する。
6. 当該値の内容を検査する。Intでは正規形→桁数guard→整数変換。pairはleft→right、listはitems入力順、someはvalueへ再帰する。他の値は追加内容検査なし。

InputAdmissionは入力codecの論理イベントであり、物理allocation・cons spine数とは別である。rootの候補深さは1、子値は親+1、累積node数は0から開始する。header、キー集合、浅いJSON型の段階に失敗した値位置にはAdmissionを発行しない。内容違反では既に発行したAdmissionを取り消さない。超過イベントは発行せず、後続の内容検査・再帰・物理TypedValue構築を停止する。事前のJSON token／span表現は値Admissionではなくtransportの境界で管理する。

従って同じ値位置ではobject／tag／キー／浅い型違反が値guardより先、値guardが整数正規形・桁数・子の内容違反より先となる。親の内容再帰は親Admission後に開始するが、各子では再びheaderから検査する。子のキー違反があれば、子の値深さ超過よりキー違反を選ぶ。正常な値位置で深さとnode数が同時超過なら深さを選ぶ。整数正規形と桁数の競合では正規形を選ぶ。

欠落キーは正準key順、余分キーは第9.3a節のscalar辞書順で最初を選ぶ。member入力順をobject主診断選択へ混ぜない。objectでない値または浅いJSON型違反はE-INPUT-FIELD-TYPE、tag欠落はE-INPUT-MISSING-FIELD、tag型／不一致はE-INPUT-TAG、その他の欠落はE-INPUT-MISSING-FIELD、余分キーはE-INPUT-UNKNOWN-FIELD、整数正規形はE-INPUT-INTEGER。これらはphase=input-decode。unknownは選択key token、missingはobject閉じ括弧直前のゼロ幅、tagは対応string／JSON値token、field型は該当field値（root非objectはroot値全体）、整数違反はvalue string tokenを主spanとする。値深さ／node数cutoffは当該値object全体、整数桁cutoffはvalue string token。全spanは元JSON bytes上で保持する。

InputAdmissionの識別子は `input-admission-v1`、有限input profileは `input-v1-reference-1` とする。上限値だけでは契約を同定せず、競合順・scalar契約を含む識別子で診断・cutoff契約を区別する。

### 9.5 codec 契約

decode_Tとencode_Tは、profileによる失敗を含めない抽象的な値codec関係／関数である。任意の有限有効値v:Tについて次を証明対象とする。

```text
decode_T(encode_T(v)) = Decoded(v)
```

受理可能な任意JSON jについて、Decoded(v)=decode_T(j)ならencode_T(v)は正準JSONとなる。成功結果のpayloadを取り出さずに結果envelopeをencoderへ渡す式ではない。

decode_input(T,j,input_profile)は有限予算付きの別APIである。抽象等式から任意profileでの成功を導かない。encode_T(v)のJSON bytes・JSON深さ・値深さ・SemanticTreeNodes・整数桁数が再入力profile内であり、strict parser／decoderが適合し、必要なホスト資源がある場合だけ、有限APIでDecoded(v)となる。runのCompletedにはさらにexecution profileとhost-policy、出力codecの完了が必要である。

出力profileと入力profileは別契約なので、Completedの出力を標準input profileへ必ず再投入できるとは約束しない。例えば10^4096は有限Intで4,097桁・13,607 bitsだが、標準inputの4,096桁上限を超える。これは抽象codec往復の反例ではない。

---

## 10. 診断契約

### 10.1 共通 schema

各診断は JSON object 一つを一行で出す。必須キーと正準出力順は `severity`、`phase`、`code`、`span`、`expected`、`actual`、`message`、`repair`。未知キーは禁止する。

- severity は `error` または `warning`。
- phase と code は版付き台帳の列挙。code prefix は対象領域であり phase と一対一対応しない。`E-ENTRY-UNKNOWN` の phase は `name`。
- span は `{"start":非負整数,"end":非負整数}`、start<=end。UTF-8 bytes の半開区間。source API は source bytes、AST API は元 JSON bytes、input API は元入力 JSON bytes を対象とする。offset は文字数ではない。
- expected、actual は正準型・制約の string または null。message は版固定のテンプレートから生成する。
- repair は null、または次の完全な schema に適合する object。hint は修復の正しさ・唯一性を保証しない。

```text
repair = {
  "kind": "replace_expression" | "replace_identifier" |
          "replace_type" | "insert_text" | "delete_span",
  "target_span": {"start": Nat, "end": Nat},
  "constraint": String
}
```

repair の3キーは全て必須、余分なキーは禁止。insert_text はゼロ幅 span、それ以外も対象 byte stream 内の範囲を要求する。AST API は実装が安全な JSON 部分木置換を指定できない場合 repair=null とする。未実装の repair を推測して出さない。

型表示は `Int`、`Bool`、`Unit`、`List<Int>`、`Option<List<Int>>`、`Pair<Int, List<Option<Bool>>>` の形式を使う。

```json
{"severity":"error","phase":"typecheck","code":"E-TYPE-IF-BRANCH","span":{"start":84,"end":101},"expected":"Int","actual":"Option<Int>","message":"if の両分岐は同じ型でなければなりません","repair":{"kind":"replace_expression","target_span":{"start":84,"end":101},"constraint":"expression of type Int"}}
```

RunResult と UTF-8 boundary failure はプログラム診断列ではなく、結果 envelope として伝える。境界結果を E-LEX や E-TYPE へ変換しない。

---

### 10.2 診断パイプライン

```text
source-boundary → lex → lexical-limits → parse → structural-limits
  → name → call-graph → typecheck → semantic-limits → entry → warnings
```

lexical-limits は lex と、structural-limits の安全 guard は parse と、semantic-limits は typecheck とそれぞれ一体で実行する。矢印は検査責務の順序であり、巨大な中間物を全部生成してから上限を測る意味ではない。

| 段階 | 検査 | 失敗後の規則 |
|---|---|---|
| source-boundary | source bytes 上限、続いて UTF-8 | bytes 超過は静的拒否、UTF-8 不正は境界失敗。以後停止 |
| lex | ASCII、トークン形式 | 最初の字句 error で停止。parse しない |
| lexical-limits | 次の token と整数桁数 | 上限を超える token 確定時に cutoff。parse しない |
| parse | EBNF、宣言終端 | parse error のみなら bounded recovery。name 以後なし |
| structural-limits | 関数数、AST node数、型・式・let・fold深さ | guard 超過時点で parse／recovery を打切り、以後停止 |
| name | 全宣言・全式の名前と entry 参照 | error があれば call-graph 以後停止 |
| call-graph | 全関数の DAG | cycle error があっても typecheck と entry を実行 |
| typecheck | arity と型制約 | 通常の型 error なら entry まで継続 |
| semantic-limits | 推論型深さ・検査仕事量 | 超過時に typecheck を中断し、entry と warnings も停止 |
| entry | 構文個数と唯一の関数の arity | 不正なら到達性 warning なし |
| warnings | 唯一の有効 entry からの到達性 | 下記条件で W-UNUSED-FUNCTION |

structural guardは第18.1b節の論理的Admissionイベントの直前に検査する。物理ASTオブジェクトの作成順・作成数を規範的計数にしない。超過イベントは発行せず、安全上限を超えた木を割り当てない。parse成功時に完成ASTとの計数整合を検査する。未完成・回復で破棄された構文も、既に発行したAdmission分だけparse安全budgetを消費し、リセットしない。AST transportからの構築も同節の規範前順traceで計数する。

競合時は source size→UTF-8→入力順の lex／parse の観測順。既に生成した通常診断は保持する。cutoff は一件だけ発行し、未実施の後続診断は追加しない。同時に複数の structural 上限を超えるイベントでは関数数、AST数、型深さ、式深さ、let深さ、fold深さの順で一つだけ選ぶ。

warnings は name 成功、唯一の arity=1 entry 有効、resource cutoff なしの場合に実行する。call-graph／typecheck error があっても構文上の到達性 warning を計算する。Accepted は全必須 phase が完了し error が0件の場合だけ。

E-CYCLE-CALL の phase は `call-graph`、通常 arity は `typecheck`、静的上限の phase は対応する `source-boundary`、`lexical-limits`、`structural-limits`、`semantic-limits` とする。

---

### 10.3 診断件数と recovery

- error、warning はそれぞれ合計最大32件。通常候補が32件以下なら全件、33件以上なら先頭31件と最後の `E-DIAG-LIMIT`／`W-DIAG-LIMIT` 一件を出す。
- phase順は第10.2節の順。parse phaseは、最初のerrorを先頭に保つため診断観測順とし、recovery-limitを最後に置く。それ以外のphase内は主span.start、span.end、codeのASCII辞書順、論理node indexの順で安定整列する。完成ASTでは前順index、構築guardではAdmission indexを用いる。同一node・同一codeの候補は一件に統合する。ASTを持たないparse診断は同一観測位置・同一codeの候補だけを統合する。
- resource cutoff が32件制限で隠れる場合、先頭30件、cutoff 一件、E-DIAG-LIMIT 一件とする。cutoff を省略して通常 error だけを返さない。
- parser recovery は最大8回の同期化操作。9回目が必要な error を観測したとき、その通常 parse error と `E-PARSE-RECOVERY-LIMIT` を生成して停止する。上限到達のみでは止めず、8回目の後に EOF まで正常なら追加診断なし。
- recoveryは次の固定手順に従う。各トップレベル宣言試行または不正トップレベルtokenの処理開始indexをs、失敗時の未消費token indexをpとする。通常parse errorを生成した後、pがEOFなら同期操作を追加せず停止する。EOF以外で同期回数が既に8ならE-PARSE-RECOVERY-LIMITを生成して停止する。それ以外はmax(p,s+1)以降の最初のfn／entry／EOFのindex qを求め、同期回数を一つ増やす。qがfn／entryならそのtokenを消費せず、qから新しい宣言試行を開始する。qがEOFなら停止する。q>sを各試行間の進行条件とし、q=pでも前の試行開始sより先なら許す。探索で飛ばすtokenにはAdmissionを発行せず、合成・修復nodeを生成しない。構造内部の予約語も同じ同期集合に含める。回復ASTをname／typecheckへ渡さない。
- 最初の parse error はその phase の先頭。recovery-limit は最後。resource guard は recovery より優先して停止する。
- lex は最初の error で停止し、recovery しない。
- W-UNUSED-FUNCTION は未到達関数ごとに一件、関数名 span を主 span とする。

name はトップレベル、各関数の引数と式を入力・前順で走査する。重複名の後続定義は診断し、曖昧名の使用に派生 unknown を出さない。shadow binder は診断した上でその局所範囲に導入し、未束縛由来の派生診断を避ける。name error がある木は受理しない。

型検査は全関数を宣言順、部分式を左から右に走査し、独立した兄弟を常に検査する。ErrorType 由来の親診断だけを抑制する。「継続してよい」という実装選択にしない。同一入力・仕様版・profile に対し内容、位置、順序、件数は一意とする。

---

### 10.4 コード系列

- `E-LEX-*`：字句不正、数値境界、整数正規形
- `E-PARSE-*`：構文不正、予約語位置、区切り不整合
- `E-NAME-*`：未束縛変数、未知関数、重複束縛、シャドー
- `E-ARITY-*`：ユーザー関数・組込みの引数数不一致
- `E-TYPE-*`：型不一致、`if`、`let`、`fold`、組込み規則違反
- `E-CYCLE-CALL`：ユーザー関数呼出し循環
- `E-ENTRY-*`：entry の未知名、欠落、重複、引数数不正
- `E-LIMIT-STATIC-*`：コンパイル静的上限超過
- `E-INPUT-*`：JSON 構文、重複キー、tag、キー集合、型、整数正規形
- `E-LIMIT-INPUT-*`：入力境界上限超過
- `W-UNUSED-FUNCTION`：未到達トップレベル関数

`E-CYCLE-*` は分類名であり、v1 における公開具体コードは `E-CYCLE-CALL` 一つである。

### 10.5 型エラー回復

型検査はエラー型を内部的に用いて、独立した兄弟部分式の診断を継続する。ただし、ある部分式が型エラーで ErrorType になった結果生じる親の二次エラーは抑制する。

例：`fst(fst(u))` で `u:Option<Pair<Int,List<Int>>>` の場合、内側 `fst(u)` に `E-TYPE-FST-ARG` を一件報告し、外側 `fst` について ErrorType 由来の二次エラーを報告しない。

---

## 11. Verus 仕様、証明、信頼境界

### 11.1 層分離

```text
spec/   Ty, Value, AST, scope, typing, call graph, mathematical evaluation, codec relation
proof/  termination, determinism, type soundness, refinement proofs
exec/   lexer, parser, formatter, resolver, type checker, DAG checker, evaluator, JSON codec, CLI
```

### 11.2 証明義務

1. parser 健全性、および資源上限内の EBNF 適合 source に対する完全性
2. formatter の AST 保存性と冪等性
3. 名前解決の一意性、entry 検査、scope 整合性
4. 型検査と組込み型規則の健全性
5. DAG 検査・ランク構成の健全性
6. 型安全性、停止性、決定性、中心定理
7. `eval_fuel` の燃料単調性
8. 実行可能評価器の数学的評価への適合
9. strict JSON parser・codec の型整合性、往復性、重複キー拒否
10. Compile / Decode / Run の失敗結果分離

### 11.3 信頼境界

`trust-boundary.toml` には、仕様レビュー、`assume`、`external_body`、`unsafe`、未検証ライブラリ、Verus、SMT、Rust コンパイラ、標準ライブラリ、OS、CPU、アロケータ、BigInt を記録する。

- **V1-A**：外部 BigInt を信頼仮定とする検証版。
- **V1-B**：BigInt の表現、比較、加減を検証。
- **V1-C**：乗算と `mod` を検証し、算術中核を TCB から除去。

未証明中核を「完全に形式検証済み」と呼ばない。

---

## 12. LLM 統合と評価

### 12.1 運用原則

LLM は候補生成・修復器であって、信頼実行主体ではない。受理判断はコンパイラ、codec、評価器、資源プロファイル、隠しテスト、性質検査に属する。

### 12.2 Skill

`SKILL.md` は仕様から生成・照合し、ハッシュとトークン数を固定する。v1 Skill は、`Option` に一般 payload 消去がないことを明記し、`uncons` や `match_option` を使わせない。

含めるのは最小文法、型、組込み規則、`let`・`fold`・`Pair`・`cons`／`reverse` の例、禁止事項、出力形式、主要診断コードである。最終評価の解法・近傍例・手書き例外規則は含めない。

### 12.3 評価モード

モードは出力・入力条件の名称であり、それだけで因果要因を分離した証拠ではない。

| モード | 入出力 | 評価する対象と限界 |
|---|---|---|
| Surface | LLMがLPTL sourceを出力 | 要求理解から表面構文・型・意味構成までの総合成功 |
| AST | LLMがJSON ASTを出力 | 要求理解とAST生成の総合成功。制約付き／制約なしを別armとして記録 |
| Render | 正解の未型検査ASTを入力しLLMがsourceを出力 | 与えた構文構造の保持と表記生成。課題の解法生成能力を測らない |
| Repair | 可視診断に基づく局所差分または再生成 | 固定した初期候補・診断条件からの修復効果 |
| Spec | 要求から形式仕様と実装を出力 | 要求理解・仕様化の別評価。主たるsource／AST生成のSuccess@Bへ混ぜない |

Renderの主評価ではAST内の型注釈・binder・宣言順等を保持し、abstract parse結果が入力ASTと一致するかを検査する。有限検査器で測定するfixtureには、静的に有効でSurfaceの登録profile内に正しい出力が存在することを事前確認する。Renderはepisode単位の構文AST一致率を別に報告し、主要生成・修復の意味的Success@BやSpecの指標へ合算しない。モデル生成ASTからのRenderは生成＋renderの連結armとして別報告する。deterministic formatterは対照／検査器であってLLM Renderの成績に混ぜない。

### 12.4 必須比較と識別対象

全armで、仕様・モデル版・温度・seed割付・候補選択・可視ツール・input／execution条件を事前登録する。同じモデル内で対応するtask／replicate seedの割付を行う。表記ごとのprompt長と出力長は記録し、実際に異なる量を同一と称さない。

| 比較 | 主な介入 | 報告できる効果・共通化する条件 |
|---|---|---|
| v1／v1-no-let | letの有無 | letによる表記・共有評価・資源差を含む総合効果。純粋な表記効果とは呼ばない。no-letでも表現可能な共通課題で比較 |
| Surface／AST、双方制約なし | 表記・prompt・長さ | その生成条件における表記パッケージの差。共通静的意味規則、ツール、予算を固定 |
| AST制約なし／AST制約付き | schema制約生成 | 同じ表記下での制約付き生成の総合効果。使用schema、生成器の実装・対応範囲・費用を記録 |
| Surface／制約付きAST | 表記と制約生成の同時介入 | 運用パッケージの総合差だけを主張し、純粋な構文効果としない |
| Render | 正解ASTが既知 | 構文保持・表記生成。未知解法生成の優位性を推論しない |
| 同意味論・別表記 | 表記を変更 | 注釈・意味構成子・生成制約条件を固定した範囲の表記効果 |
| 診断なし／文章のみ／コードのみ／span＋制約 | 可視診断 | 同じ失敗候補からの修復効果。主実験は固定初期候補を対応割付。自然生成の失敗候補だけを用いる条件付き結果は別報告 |
| Skillあり／なし | Skillの提示 | Skill内容と増分context費用を含む総合効果。トークン長一致だけで情報内容が統制されたとはしない |
| 通常Python／制限Python／LPTL | 言語・制限・tooling | 同一問題の総合差。Pythonの物理時間やメモリをLPTLの参照Steps／AllocatedNodesと同一視しない |
| リスト構築組込みあり／なし | cons、concat、reverseを一体的に除く | 型、list専用構文、fold、length、他の機能は保持。別研究arm v1-no-cons-concat-reverseとして識別。共通表現可能課題で総合効果を比較 |

上表のアブレーションは研究armの契約であり、出荷するv1言語コアを変更しない。armごとのspec・Skill・資源設定・除去集合・適合検査は実験前に固定し、未提示armを実装済みと扱わない。

比較する課題は各armで解けることを、モデルの最終結果と独立した参照解・表現可能性の根拠で事前確認する。参照解をモデルへ渡さない。表現できない課題は主要Success@Bの共通集合から事前に分離し、能力境界の結果として件数・理由を公開する。失敗結果を見て後から除外しない。

v1はOption一般payload消去を対象外とする。その消去が必要な課題はv1最終タスクに含めず、将来拡張版の実験へ分離する。参照／物理資源条件、表記固有transport、最終タスクの範囲を明示し、形式保証からLLM優位性を導かない。

### 12.5 事前登録と指標

`evaluation-protocol-v1` は実験計画の契約識別子であり、実行済み実験を意味しない。仕様、Skill、処理系、全profile、モデル版、温度、最大出力、反復数K、task集合、候補選択、可視ツール、生成器、seed、隠し検査、閾値、除外基準、失敗集計を秘密seed最終評価前に固定する。

主要生成・修復評価の一試行は一つの(task_id, replicate_id, arm_id)に対応するepisodeとする。初回生成とその後の全修復・候補生成を同じepisodeへ含める。各taskに同じKを割り付け、成功した課題だけ反復を増減しない。候補一件を新たな試行と数えない。Repairを固定失敗候補から開始する場合、その候補をepisodeの所与入力とし、生成に要した費用を含めない修復単独指標と、生成を含む連結指標を分ける。

予算Bは単一の不明な量ではなく、(累積モデル入力tokens、累積モデル出力tokens、モデル要求回数、可視検証API呼出し回数)の上限vectorとする。compile／compile_ast／decode_input／runの可視呼出しはそれぞれ一回と数え、CLI内でまとめた場合も内部呼出し数を記録する。各上限は全episodeで同じarm比較条件として固定し、全成分が上限以内のときだけ予算内とする。tokensは版付き計数器またはprovider usageの事前登録した規則で数え、Skill・診断・明示schema・修復履歴を含む実際のモデルcontextを各要求で課金する。cacheによる料金割引と論理tokensを混同しない。provider内部の非公開制約処理費用は推測せず、既知費用・不明費用・壁時計・料金を別途公開する。

要求・検証回数と要求時context入力tokensは実施前にguardする。出力は残余token予算に合わせて制限し、途中で上限超過した場合はepisodeをbudget失敗とする。ちょうど上限は許す。次の操作に予算がなければ発行せず、予算内の既存候補を使って通常終了する。guardが追加操作を禁止したこと、または一成分が上限へ到達したことだけでepisodeをbudget失敗にしない。追加の有料・外部ツールを使う場合は共通の上限と計数規則を事前登録に追加し、無予算のtoolへ探索費用を移さない。BはLPTLのinput／execution profileと別の探索予算である。

終了理由とbudget違反を分離する。normal_stop／budget_reached／operation_guardedは実測累積usageが全成分以内ならbudget内であり、既存候補を選択できる。実測累積usageが一成分でも上限を超えたbudget_exceededだけをbudget失敗とする。予算内終了時にAccepted候補がなければno_accepted_candidate失敗。model出力が途中で切れた場合はその不完全候補をAcceptedとして扱わないが、実測usageが上限内なら既存のAccepted候補は失格にしない。登録Bは定めた全成分を持つ非負整数vectorであり、欠落成分・長さ不一致をzip等で無視しない。追加成分を登録した場合も全成分を検査する。

候補が既に予算内にAcceptedとして検証済みなら、選択時の重複compileは必須にしない。最後のAccepted候補は修復前の不変bytesと検証記録で同定し、未検証の編集をその候補へ混ぜない。再検証を行う場合はBに計上し、予算がなければ実施しない。隠し採点前に候補選択を固定する。


最終候補は隠しテストを一切参照せず一件だけ選ぶ。主評価では予算内に検証された候補のうち、最後にcompile／compile_astでAcceptedとなった候補を選ぶ。Accepted候補がなければ失敗。全候補を隠しテストで評価してから最良を選ぶことは禁止する。最終候補の受理確認までBへ含め、固定した隠しテスト・性質検査による最終採点はB外の共通評価費用として記録する。採点結果をepisodeの修復へ返さない。候補は課題の同一interfaceに適合し、公開・秘密入力で同じprofileを使う。

```text
S(task, replicate, arm; B) = 1
  iff budget内に選択した最終候補がAcceptedであり、
      固定した全隠しテスト・性質検査・参照資源条件に通過する
それ以外は0

Success@B(arm) = (1 / task数) * Σ_task ((1 / K) * Σ_replicate S)
```

Kが共通なら全episodeの成功数／全episode数と一致する。生成失敗、parse/name/type/entry拒否、入力不正、参照資源超過、候補なし、budget超過、誤答、候補実行によるHostAbortedを分母から落とさない。受理率は別指標であり、意味的タスク成功の代替としない。評価器のInternalFaultや共通サービス障害等の試験基盤事故は、結果と独立に事前登録した判定規則で区別し、件数、影響したepisode、再実行・欠測処理を公開する。モデル成績に有利な一方のarmだけを再試行しない。

二次指標は初回phase通過率、固定失敗候補からの修復成功、候補単位の受理率、条件付き・無条件費用、検証回数、診断別修復率、深さ別成功、資源超過率を別名で報告する。失敗したepisodeにも実費を計上する。複数違反は診断全件と終端理由を記録し、episodeを重複して分母へ加えない。task単位ブートストラップを用い、対応比較では同じ再標本taskを全armに適用する。信頼水準、再標本回数、差の推定量、多重比較扱いは事前登録する。

公開再現課題と秘密seed最終課題を分離し、表層・意味・構造近傍による汚染検査を記録する。秘密seedのみで汚染不在を証明したとはしない。G4完了は事前登録に沿う実験と結果公開であり、正の優位性を必須にしない。優位性の主張には、事前登録した対照・最低効果量・不確実性・無条件費用の条件を別に満たす必要がある。結論は固定task分布、モデル、予算、tools、profileの範囲へ限定する。

### 12.6 高保証カーネルの費用と採用判断

第一用途の受理・実行契約を、第二用途の成功率のために緩めない。初期の代表workloadは現行の純粋有限コアで表せる集計、条件付きリスト抽出、有限構造の変換・等値・Option状態伝達とし、Option一般payload消去、I/O、一般再帰を必要とする用途へ成功保証を拡張しない。

G0でfixture対象の型、入力長・深さ・整数規模、期待出力規模を記録する。G2／profile凍結では正準化、診断、論理trace／shadow accounting、共有出力展開を含む費用を測定し、論理カウンタと物理時間・ヒープ・frameを別報告する。標準profile数値は測定値ではない。どの規模・host-policyで実用採用するかの閾値は対象環境と実測に基づき別に判断し、恣意的な性能目標を設定しない。

---

## 13. 例

### 13.1 偶数の合計

```text
fn sum_even(xs: List<Int>) -> Int =
  fold(xs, 0, |acc, x|
    let r = mod(x, 2) in
    if(eq(r, some(0)), add(acc, x), acc))
entry sum_even
```

正の定数除数 `2` に対して、`mod` は常に `some(r)` を返す。`r` を未知 payload として取り出してはいないため、v1 で表現できる。

### 13.2 正の値だけを順序保存で抽出

```text
fn positive_values(xs: List<Int>) -> List<Int> =
  let reversed = fold(xs, list[Int](), |acc, x|
    if(lt(0, x), cons(x, acc), acc)) in
  reverse(reversed)
entry positive_values
```

`fold` と `cons` により逆順で構築し、`reverse` により入力順へ戻す。全操作は有限リストに対し全域である。

### 13.3 v1 で表せない Option payload 消去

以下は v1 では書けない要求である。

```text
// mod(a,b) が some(r) のとき r+1、none のとき 0
```

理由は `Option<Int>` の一般 payload `r` を束縛する `match_option` がないためである。これは 将来の独立した Option 消去拡張で初めて対象とする。

---

## 14. 将来拡張

### 14.1 独立拡張候補：Option 消去と安全リスト分解

次の機能は一体としてのみ検討する。

```text
match_option(e, on_none, |x| on_some)
uncons(xs) : Option<Pair<T, List<T>>>
```

`match_option` は自由な第一級関数ではなく、`fold` と同様の局所 binder 特殊形式である。導入時には、型規則、選択的評価順序、停止性、診断、codec、LLM 評価、Skill、証明義務を追加する。

### 14.2 追加判断の条件

機能追加は、次を満たす別バージョンとしてのみ許される。

1. 規範 `spec` の文法、型、評価、資源、診断を更新する。
2. 全域性、型安全性、決定性、実装適合の証明を更新する。
3. TCB と資源プロファイルへの影響を公開する。
4. 既存コアと混同しないタスク分布・消去実験で LLM 効果を測定する。

---

## 15. 出荷ゲート

### G0：仕様凍結

- v1 `spec`、EBNF、型、評価、API、codec、診断、resource profile interface を固定。
- v1 と後続の Option 消去候補を混在させない。
- 文書、Skill、例、テストを規範仕様に追跡可能にする。

### G1：数学的コア

- `let`、`fold`、リスト構築操作、DAG 呼出しを含む型安全性、停止性、決定性、中心定理を機械検証する。

### G2：処理系適合

- resolver、type checker、DAG checker、evaluator、formatter、parser、strict JSON codec の適合を証明または台帳化する。

### G3：境界監査

- TCB、`assume`、`external_body`、`unsafe`、BigInt、SMT、Rust、OS 等を版付き台帳で公開する。

### G4：LLM 実験

- 第12.3–12.5節に従い、v1／v1-no-let、制約なしSurface／AST、ASTの制約生成消去、Render／Repair、診断消去、別表記、Skill、制限Python、リスト構築組込み消去の介入と識別対象を事前登録する。
- 秘密seed最終評価、全episodeの分母、失敗分類、無条件費用、資源超過、対応比較と信頼区間を公開する。実験実施・公開と正の優位性の成立を分離して判定する。

---

## 16. 契約索引

| 項目 | v1 の契約 | 主節 |
|---|---|---|
| entry 欠落・未知・重複 | 個数収集と診断を分離、name 失敗時は entry 停止 | 5.2、10.2 |
| 宣言境界 | 完成 expr の直後の fn／entry／EOF。改行不要 | 4.1 |
| static と DAG の検査分離 | call-graph と各 limits phase に分離 | 10.2 |
| 上限超過後の継続 | 最初の cutoff で後続を全停止、既存診断は保持 | 10.2 |
| 通常 call の arity | typecheck、実引数を検査、引数型との比較は抑制 | 6.1 |
| none[Foo] | E-PARSE-EXPECTED-TYPE | 6.1 |
| API の bytes 境界 | source_bytes／json_bytes／ast_json_bytes | 9.1 |
| AST mode | schema、キー、名前、span、共通検査を固定 | 19 |
| fold 停止証明 | 本体 call を DAG に含め rank 帰納と接続 | 8.2 |
| Pair 表記 | 二つの独立した型パラメータ | 3.1 |
| JSON 正準性 | 実 JSON 例、引用キー順、全体 first-error | 9.2–9.4 |
| repair | 完全な列挙・必須キー、非保証 hint | 10.1 |
| recovery | 8回後の追加 error で専用コード、停止 | 10.3 |
| concat／none 計数 | 一時参照スタック、mセル、none singleton | 8.4、18 |
| 実装・証明の状態 | 完了とは主張せず、出荷ゲートで確認 | 11、15、20 |
| Option 拡張 | 本コア対象外。将来の独立拡張として審査 | 14 |

---

## 17. 設計状態

本書は、非再帰letと有限リスト構築、診断phase、AST transport、資源cutoff、入力値Admission、scalar検査、予算終了、hash用途の契約を定義する設計案である。固定した記述と、将来spec・registry・実装・証明・実験で照合する条件を区別する。

本版では、Option payload 消去がないという表現力上の境界を隠さない。この制限を明示することで、実装、Verus 証明、Skill、ベンチマーク、LLM の期待能力が同じ言語を対象にする。`match_option` と `uncons` は有用だが、後続の独立拡張版で一体的に審査する。

LLMに対する優位性は未測定である。v1は、その検証に向けて構文、診断、資源、codec、実験条件を明示し、規範specへの追跡・適合確認を要求する高保証DSLの候補である。文書で手順を選択したことを、実装の決定性や実験の識別可能性が確認済みという意味にしない。


---

## 18. 資源プロファイル契約

### 18.1 版と検査点

以下の数値は標準profileの設計値であり、性能測定から導いた値ではない。実装・proofと照合するまでprofileも凍結候補とする。境界値は観測値<=limitなら通過し、初めて超過するイベントで停止する。static profile識別子は `static-v1-reference-1`、parse構築試行は `parse-admission-v1`、型検査計数・診断時点は `typecheck-cost-v1`、診断pipelineは `diagnostic-pipeline-v1` とする。finite input profileは `input-v1-reference-1`、InputAdmissionは `input-admission-v1` とする。参照コストモデルは `resource-profile-v1-reference-1`、AST transportは `ast-transport-v1-reference-1`、executionは `execution-v1-reference-1` を用いる。表のreference-1は数値設定の略記であって版識別子の代用ではない。数値上限が等しくても、診断順・cutoffの契約同一性を保証しない。これらは実装済みspec_versionや凍結済みprofileではない。

| static 項目 | reference-1 上限 | コード末尾 | 検査点 |
|---|---:|---|---|
| source bytes | 1,048,576 | SOURCE-BYTES | source-boundary |
| token数、EOF除外 | 131,072 | TOKENS | lexical-limits |
| 整数リテラル桁数、符号除外 | 4,096 | INTEGER-DIGITS | lexical-limits |
| 関数数 | 1,024 | FUNCTIONS | structural-limits |
| AST node数 | 131,072 | AST-NODES | structural-limits |
| 型構文深さ | 64 | TYPE-DEPTH | structural-limits |
| 式深さ | 256 | EXPR-DEPTH | structural-limits |
| let ネスト深さ | 128 | LET-DEPTH | structural-limits |
| fold ネスト深さ | 32 | FOLD-DEPTH | structural-limits |
| 推論された型深さ | 128 | SEMANTIC-TYPE-DEPTH | semantic-limits |
| 型検査イベント数 | 2,000,000 | SEMANTIC-WORK | semantic-limits |

全コードは `E-LIMIT-STATIC-` に末尾を連結する。AST node は program、各 fn／entry、param、各型構成子、各式をそれぞれ一つと数える。lambda は fold node の binder fields であり独立 node ではない。名前 string、整数 string、配列、span は node に含めない。

型・式深さは根を1とし、同種の子 node へ一段進むごとに1増加。関数本体の式深さは1から開始する。let／fold深さは一つの式経路上の該当 node 数であり、兄弟の合計ではない。明示された型の出現は全て別 node と数え、interning により静的計数を減らさない。

型検査仕事量は第18.1a節の論理イベント列で計測する。実装ヒープ上の型オブジェクトの生成数・共有数・interning・cache hit数を計測するものではない。型比較は外側から、Pair は第一成分から行い、不一致で止める。ErrorType は有限の特殊内部値で深さ0、ユーザー AST と値には存在しない。深さと仕事量は typecheck 中に検査し、深さ超過を優先する。

整数列を認識するとき、字句の正規形・数値境界違反と桁上限が同じ token で競合する場合、先に正規形・境界を判定する。ただし巨大な列を BigInt に変換しない。token count は正常 token 確定後に検査し、同じ token の桁超過を token count より先に返す。


### 18.1a 型検査の論理仕事量

`typecheck-cost-v1` は凍結候補profileの計数・診断時点契約識別子であり、言語機能や実装済みspecの追加を意味しない。arity診断のcutoff前保持もこの契約に含む。SemanticWork は次の論理イベント数の合計である。

| イベント | 1イベントの意味 |
|---|---|
| VisitExpr | 共通ASTの一つの式nodeの型検査開始 |
| BuildType | 以下の規則で結果型の外側構成子一つを論理的に構成 |
| CompareType | 型等価性検査の一つの構成子対の検査、または期待する外側tagとの検査 |

実際の型メモリ確保・deep copy・型hash計算はイベントにしない。型共有・interning・cacheは許すが、参照イベント列は短縮しない。最適化版は同じ列・cutoffを再現するshadow accountingを持つ場合だけ、この計数契約の互換を名乗れる。

**式のvisit順。** 関数を宣言順に検査し、各関数本体を一回だけ検査する。callのcallee本体をその場で再検査しない。各式はVisitExprを発行してから子を左から右に検査する。callではVisitExpr通過直後にarityを判定して診断候補を発行し、その後、全実引数を左から右に検査する。arityが正常な場合だけ、最後に引数型制約を左から右に比較する。arity判定は独立した論理イベントではなくSemanticWorkを消費しない。call自身のVisitExprがcutoffした場合はarity判定も未実施とする。listも全要素を先に検査し、その後に要素型を入力順に比較する。letはvalue、body。ifはcondition、then、elseを先に検査し、その後condition対Bool、then対elseの順に比較する。foldはlist、initを検査し、listの外側tagを確認してbinder型を決め、bodyを検査してからbody対initの型比較を行う。非選択枝・未到達関数も静的に検査する。

**BuildTypeの発行規則。** 子と当該式の型制約が正常な場合のみ、次のイベントを発行する。注釈型のparse、型参照の取得、scopeへの型参照束縛はBuildTypeではない。

| 式／正常call | 論理的BuildType |
|---|---|
| 整数、bool、unit literal | Int、Bool、Unitの一つ：1イベント |
| list、none | List<T>、Option<T>の外側一つ：1イベント |
| some、pair | Option<A>、Pair<A,B>の外側一つ：1イベント |
| add、sub、mul、neg、length | 結果Int：1イベント |
| lt、le、eq | 結果Bool：1イベント |
| mod | 内側Int、外側Option<Int>の順：2イベント |
| var、let、if、fold | 既存の型を参照：0イベント |
| ユーザーcall | 宣言戻り型を参照：0イベント |
| fst、snd | 引数Pairの対応成分型を参照：0イベント |
| cons、concat、reverse | 検査済みのリスト引数型を参照：0イベント |
| ErrorType結果 | 0イベント |

これは数学的に同じIntが既に存在していても発行する論理イベントである。子型を外側構成子へ接続する際、子の構成子を再生成したとは数えない。modの型構成は実行時の整数・some割当とは別であり、評価時の除数に依存しない。

**CompareTypeの発行規則。** 完全型同士の比較では根の構成子対に一イベントを発行する。tagが違えばそこで停止。tagが同じList／Optionはelementへ、Pairはleft→rightへ進み、最初の不一致で当該比較を止める。Int／Bool／Unitは根だけで終了する。同じpointer・同じintern IDでもこの論理走査を省略しない。独立した次の引数・要素の比較は継続する。

外側tagの制約検査は根だけの一イベントとし、子型を比較しない。これをHead(T,Tag)と表す。完全型の比較をEqual(A,B)と表す。型メタ変数を取得するだけではイベントを発行しない。

| 通常builtin | 引数制約の比較順 |
|---|---|
| add、sub、mul、lt、le、mod | Equal(arg1,Int)→Equal(arg2,Int) |
| neg | Equal(arg1,Int) |
| eq | Equal(arg1,arg2) |
| fst、snd | Head(arg1,Pair) |
| cons | Head(arg2,List)、成功時にEqual(arg1,arg2.element) |
| concat | Head(arg1,List)→Head(arg2,List)、両方成功時にEqual(arg1.element,arg2.element) |
| reverse、length | Head(arg1,List) |

ユーザーcallでは各実引数を対応する宣言引数型とEqualで比較する。arity不一致のcallは全実引数のVisitExprを継続するが、当該callの引数比較と結果BuildTypeは全て0とし、結果ErrorType。専用構文の位置不足はparse／AST schemaで拒否され、typecheckへ渡らない。

listでは各要素とelement_typeをEqualで比較する。noneは型注釈以外の比較なし。some／pairは子から型を構成し比較なし。letはvalue型をbinderへ参照束縛しbodyを検査する。ifは前述の順、foldはHead(xs,List)とbody対initのEqualを行う。最後に各関数本体型を宣言戻り型とEqualで比較する。引数・戻り型の注釈自体はstructural-limitsで既に検査されている。

ErrorTypeとのEqual／Headは0イベントで二次診断を出さない。必要な子のErrorType、当該式の型制約違反、arity違反を持つ式はErrorTypeを返す。letはvalueかbody、ifはいずれかの子または自分の制約、foldはいずれかの子または自分の制約が不正ならErrorType。独立した正常兄弟のVisitExpr・BuildType・比較は継続する。foldのxsが正常型だがListでない場合はHead違反を出しitemをErrorTypeとする。initがErrorTypeならaccもErrorTypeとする。

**上限と優先順位。** SemanticWorkはtypecheck開始時0。各論理イベントの直前に次の値を検査し、超過イベントを発行せず `E-LIMIT-STATIC-SEMANTIC-WORK` で停止する。BuildTypeでは先に生成予定の論理型深さを検査し、その後SemanticWorkを検査する。同時超過は型深さを優先する。型深さは構造上の量であり、それを取得する実装のcache／走査回数はSemanticWorkへ追加しない。cutoff後はentry／warningsを実行しない。

次は上記規則から導くtrace fixtureの期待値であり、処理系を実行した測定値ではない。各programには一関数と対応entryを置く。

| 関数 | VisitExpr | BuildType | CompareType | 合計 |
|---|---:|---:|---:|---:|
| `fn f(x: Int) -> Int = x` | 1 | 0 | 1 | 2 |
| `fn f(x: Unit) -> Int = 0` | 1 | 1 | 1 | 3 |
| `fn f(x: Unit) -> Int = add(1, 2)` | 3 | 3 | 3 | 9 |
| `fn f(x: Unit) -> Option<Int> = some(0)` | 2 | 2 | 2 | 6 |
| `fn f(x: Unit) -> List<Int> = list[Int](1, 2)` | 3 | 3 | 4 | 10 |
| `fn f(x: Unit) -> Option<Int> = none[Int]` | 1 | 1 | 2 | 4 |

G0では、この論理traceをspecと参照型検査器へ写し、通常型違反、ErrorType回復、深さ／仕事量cutoffを含むfixtureで照合する。本書の規則記述を、参照検査器の実装・証明・適合確認の完了と読み替えない。

### 18.1b parse構築試行と共通AST Admission

`parse-admission-v1` は論理的な安全計数契約である。AST node数は物理確保数ではなく、次の規範的Admissionの累積数とする。Admissionは前順に一nodeずつ発行し、イベント直前に全ての該当する次値を同時に検査する。超過時は第10.2節の優先順位で一件だけcutoffし、当該イベントとその後のイベントを発行しない。正常な入力では完成ASTの第18.1節のnode数に一致する。

| 構文上の対象 | SurfaceでのAdmission時点 | 同時に検査する量 |
|---|---|---|
| program | lexとlexical-limits完了後、最初の宣言試行より前。空programにも一回 | AST数 |
| fn／entry | トップレベルで対応keywordを認識した時、子を読む前 | AST数、fnの場合は関数数 |
| param | params位置で合法IDENTを認識した時、コロン・型を読む前 | AST数 |
| 型構成子 | type位置でInt／Bool／Unit／List／Option／Pairを認識した時、区切りと子型を読む前 | AST数、現在の型構文深さ |
| 各式構成子 | expr位置で合法な先頭を認識し構成子を決めた時、子を読む前 | AST数、式深さ、let／foldの場合は該当ネスト深さ |

IDENT式は一token先読みで次が左括弧ならcall、そうでなければvarとし、一度だけAdmissionする。専用構文はそのkeywordで構成子を決める。INT・true・false・unitも一回。type位置のFoo、expr位置のfn等、合法な先頭を認識できない位置ではAdmissionを発行せずparse errorとする。先頭は合法だが後続の閉じ括弧・型・binder等が不正な場合も、既に発行した親Admissionを取り消さない。fold lambda、名前、文字列、配列、括弧には追加Admissionを発行しない。

深さは第18.1節の定義に従い、関数本体式と各明示型の根で1に開始する。子への論理的進入・退出に従って現在深さを更新し、失敗した宣言の回復時は深さcontextをトップレベルに戻す。累積AST数と関数数は戻さない。先読み、再検査、物理nodeの作成・破棄・共有・cacheは計数しない。grammar alternativeの投機や回復用nodeを規範traceへ混ぜない。同期で飛ばしたtokenは新しい宣言試行が始まるまで計数しない。

Admission indexは成功イベントごとに一つ増える論理indexとする。失敗した構文にも直近のAdmissionまたは診断観測indexを保持し、完成ASTが存在しないparse診断を架空のAST nodeに結び付けない。SurfaceのAdmission cutoff主spanは対象先頭token、programはsource開始のゼロ幅位置とする。元UTF-8 bytesを使用する。

AST APIでは第19.3節のtransport検査を全て通過した後、物理AST全体を作成する前に、program→declarations入力順の前順Admissionを発行する。子の順はfnでparams→return_type→body、paramでtype、型はelementまたはleft→right、式は第19.2節の子field順・配列入力順とする。paramにはtagはないが一nodeとして計上する。AST cutoff主spanは対象object全体。SurfaceとASTの正常入力は同じ構文ASTについて同じAdmission列・node数・深さを持つ。Surfaceの不正構文にだけ存在する失敗試行をAST APIへ合成しない。

G0では完成ASTとの一致、不完全構文、破棄された親、同期で飛ばすtoken、guard同時超過をfixture化する。この論理契約の記述はparser実装・証明完了の証跡ではない。

### 18.2 入力と AST transport

| profile | 項目 | 上限 |
|---|---|---:|
| input-v1-reference-1 | JSON bytes | 4,194,304 |
| input-v1-reference-1 | JSON 構造深さ | 512 |
| input-v1-reference-1 | 値深さ | 128 |
| input-v1-reference-1 | SemanticTreeNodes | 262,144 |
| input-v1-reference-1 | Int 桁数 | 4,096 |
| ast-transport-v1-reference-1 | JSON bytes | 16,777,216 |
| ast-transport-v1-reference-1 | JSON 構造深さ | 1,024 |

JSON 構造深さは object／array の開き括弧について、根の container を1として測る。semantic value 深さは各値の根を1とする。SemanticTreeNodes は int、bool、unit、none、some、pair、list をそれぞれ一つとし、list の要素値を加算する。cons spine の物理 node 数ではない。

input profile（input-v1-reference-1）のコードは `E-LIMIT-INPUT-JSON-DEPTH`、`E-LIMIT-INPUT-VALUE-DEPTH`、`E-LIMIT-INPUT-VALUE-NODES`、`E-LIMIT-INPUT-INTEGER-DIGITS`。値node・深さのguardは第9.4節のInputAdmission直前、object header・キー集合・全直接fieldの浅い型検査後かつ内容再帰前に行う。同時超過は値深さを優先する。整数桁数guardは同じ値のAdmissionと正規形検査後に行う。

AST transport 上限は表記に固有であり source bytes と同じ数値にはしない。共通 AST node／型／式上限は Surface と同一。AST と Surface の transport byte 数は別々に記録し、表記の長さが同じだったと見なさない。

### 18.3 実行の参照イベント

数学的評価とは別に、reference evaluator の cost trace を spec に定義する。実装の Rust 命令数・BigInt 内部命令数は参照イベントにしない。以下の各イベントを1 step とする。

1. 式 node の評価開始。各 fold 反復の body 開始も一回ずつ含む。
2. entry またはユーザー関数本体への入場。環境への引数参照の束縛自体は追加 step なし。
3. 通常組込みの適用開始。構成子は式 node と割当イベントで計測し、builtin-dispatch を重複させない。
4. fold／length／reverse／concat の spine cursor による一つの cons または末尾 nil の読取り。
5. list 構築／concat での一時要素参照の push と pop。一要素につき各一回。
6. 構造的 eq での一対の値根、または一対の list spine セル／nil の比較。一対の list 値根を比較した後、spine の対を走査する。
7. 第8.4節の新規整数／cons／pair／some node の一つの確保。

複数イベントを伴う処理は上記の手続き順に発生させる。例として concat は引数評価、dispatch、xs の各セル読取りと push、nil読取り、各 pop とセル確保の順。reverse は各セル読取りと確保、最後にnil読取り。fold はセル読取り、binder 設定、body 評価を繰り返し最後にnil読取り。

eq は共有 pointer 一致による短絡・memoization を行わない。根 tag が異なると即座に不一致。pair は left→right、some は payload、list は head 値→tail spine、Int は数学的整数比較、bool は値比較、unit／none は同じ tag なら等しい。型は静的に同一なので実行時の型比較は不要。

step を加算する前に上限を検査し、許されないイベントを実行しない。割当イベントでは step 上限、整数 bit 上限、AllocatedNodeCount の順に判定する。結果整数の bits は exact な数学的結果に基づく。ホスト BigInt 計算途中のメモリ不足は参照 bit 超過に置き換えず HostAborted／InternalFault の適切な結果にする。

| execution-v1-reference-1 | 上限 |
|---|---:|
| 参照 step | 10,000,000 |
| run 中の AllocatedNodeCount | 1,000,000 |
| 整数 bit 長 | 65,536 |
| 正準出力 bytes | 16,777,216 |

ResourceKind は `Steps`、`AllocatedNodes`、`IntegerBits`、`OutputBytes` とする。カウンタは幅が不足して wrap しない。閾値超過が分かる場合は飽和値 limit+1 を報告してよいのではなく、当該イベントの正確な observed を報告する。steps／allocated は通常 limit+1、bit は結果の exact bit 数、出力 bytes は出力ストリームの最初の超過 byte で limit+1。

run 開始時に入力の全整数 bit 長を値の左から右前順で検査し、超過なら step=0、割当=0 のまま IntegerBits を返す。入力 validation と実行の bit 上限は別契約である。

ホストの frame／参照スタック／ヒープ bytes／時間は `host-policy` に明記する。これらの違反は HostAborted であり、参照 step との一致・機種間再現性を保証しない。外部中断と実装バグは区別する。OS kill の場合に必ず構造化結果が返るとは約束しない。

### 18.4 資源ゲート

reference-1 の凍結には、全イベントが spec の trace 関係に写像されること、fixture の step／allocation 値が一致すること、cutoff の precedence が一致することを要する。本書だけで物理的安全や実装資源モデルの検証完了を主張しない。

---

## 19. AST codec

### 19.1 独立した transport

`ast_codec_v1` はプログラム AST 専用であり、第9節の入力値 codec と混用しない。

```json
{"codec":"ast_codec_v1","declarations":[{"tag":"fn","name":"identity","params":[{"name":"x","type":{"tag":"int"}}],"return_type":{"tag":"int"},"body":{"tag":"var","name":"x"}},{"tag":"entry","name":"identity"}]}
```

AST は未型検査の表面 AST。明示注釈を source と同じ位置にだけ持ち、内部型、推論結果、rank、symbol ID、source span、実行値、暗黙の default を入力できない。型・name・DAG の検査を省略しない。

### 19.2 完全な node schema

表の keys は許可集合・全て必須・正準出力順を同時に示す。どの object も余分なキーを拒否する。各配列は順序を保存し、空配列の受理は static 検査と分離する。

| node | keys／fields |
|---|---|
| program | `codec`, `declarations`。codec は固定 string、declarations は fn／entry 配列 |
| fn | `tag`, `name`, `params`, `return_type`, `body` |
| entry | `tag`, `name` |
| param | `name`, `type` |
| type int／bool／unit | `tag` |
| type list／option | `tag`, `element`（type） |
| type pair | `tag`, `left`, `right`（type） |
| expr int | `tag`, `value`（正規十進 string） |
| expr bool | `tag`, `value`（JSON boolean） |
| expr unit | `tag` |
| expr var | `tag`, `name` |
| expr list | `tag`, `element_type`, `items`（expr 配列） |
| expr some | `tag`, `value`（expr） |
| expr none | `tag`, `element_type` |
| expr pair | `tag`, `left`, `right`（expr） |
| expr call | `tag`, `callee`, `args`（expr 配列） |
| expr let | `tag`, `name`, `value`, `body`（expr） |
| expr if | `tag`, `condition`, `then`, `else`（expr） |
| expr fold | `tag`, `list`, `init`, `acc`, `item`, `body` |

callee は通常 builtin 名または合法ユーザー関数名。some／pair／if 等の専用構文を call node で代用しない。let と fold binder は name と同じ IDENT 規則・予約語除外を適用する。fold の二 binder の相異性と shadow は共通 name phase で検査する。

`ast_codec_v1.schema.json` は node の構造と文字列条件を検査する機械可読表現であり、JSON Schema Draft 2020-12 を用いる。各型・式nodeのtag集合、必須キー、余分キー禁止は本節の表に対応する。同梱schemaの識別子・整数patternは第19.6節の全体一致形であり、その実ファイルを照合対象とする。文書の記述だけで別のschemaファイルの適合を認定しない。

重複キー、バイト数、JSON深さ、UTF-8、不対surrogate、整数桁上限、元byte span、正準キー順、共通静的検査は JSON Schema 単体では保証されず、strict parser、コンパイラ、encoderが別途実施する。schema validator のエラー出力順を第19.3節の規範的診断順に代用しない。

### 19.3 transport 拒否

1. JSON bytes上限、UTF-8を順に検査する。
2. JSON token streamを解析する。JSON構造深さは開始括弧でguard。文法error／深さ超過は最初に観測したものを返す。
3. 第9.3a節の共通strict JSON文字列契約を適用する。JSON stringはdecoded scalar sequenceとして扱う。不対surrogateを拒否する。escape入力は受理できるが、decode後の名前条件を緩めない。
4. map化前に重複キーを検出する。キーをdecodeして比較し、"name"と"\u006eame"も重複とする。同一段階で複数のscalar違反または重複がある場合は元byte位置が最初の違反を返す。scalar違反と重複の段階順は第9.3a節と上記の順とする。scalar違反spanは不正string token全体。
5. rootをprogramとして、以下のobject検査手順に従って検査する。
6. declarationsと各配列は入力順、各nodeの子fieldは第19.2節のkey順に再帰検査する。全体で最初の一件だけを返す。
7. transport成功後、第18.1b節の共通Admission guardを適用しながら表面ASTと元JSON byte span mapを構築する。構築後はstructural-limitsの最終整合検査→name→call-graph→typecheck→semantic-limits→entry→warningsを実行する。

各objectの検査は次の全段階を順に完了する。あるfieldの内容を調べる前に、そのobjectの全直接fieldの浅いJSON型を検査する。浅い型検査でarrayと分かっても、その要素や子object内部はまだ検査しない。

| object種別 | header検査 |
|---|---|
| program | objectであること→codec存在→codecのstring型→固定値 |
| param | objectであることだけ。tagの存在・型・列挙を検査しない |
| fn／entry／型／式 | objectであること→tag存在→tagのstring型→当該位置で許されるtag列挙 |

header完了後、必須キー→余分キー→全直接fieldの浅いJSON型→field内容の順とする。必須キーが複数欠落した場合は第19.2節のkey順で最初を選ぶ。余分キーが複数ある場合はdecode後のUnicode scalar列の辞書順で最小を選ぶ。Unicode正規化やtrimは行わない。浅い型違反が複数ある場合も表のkey順で最初を選ぶ。これらの選択をJSON member入力順やvalidatorのエラー列挙順に依存させない。

field内容の検査は表のkey順で行う。name／binder／合法calleeの文字列条件、整数正規形・桁上限、子型・子式・param・宣言、配列要素をこの段階で検査する。通常builtin calleeと合法ユーザーcallee以外はE-AST-IDENTIFIER。整数では正規形を先に、正常な場合だけ桁上限を検査する。headerのcodec違反はE-AST-CODEC、tag欠落はE-AST-MISSING-FIELD、tag型・列挙違反はE-AST-TAG。objectでないnodeやその他の浅いJSON型違反はE-AST-FIELD-TYPE。paramにtagを追加した場合はE-AST-UNKNOWN-FIELDであり、tag付きparamを別構成子として受理しない。

duplicateの主spanは二番目のkey token。missing keyは当該objectの閉じ括弧のゼロ幅位置。unknown fieldは選択されたkey token。nodeの共通診断spanはそのobject全体、nameは対応string token（引用符を含む）。UTF-8 offsetは元JSON上で保持し、再符号化後のoffsetを使わない。

ASTはSurfaceのlex／parseを通らないが、整数桁条件・予約語・専用構文の制約をtransportで等しく検査する。通常callのarityはschemaで固定せずtypecheckへ渡す。専用some／pair／if／foldの必須fieldsはschemaで固定する。

AST transportコードはE-AST-JSON-SYNTAX、E-AST-STRING-SCALAR、E-AST-DUPLICATE-KEY、E-AST-CODEC、E-AST-TAG、E-AST-MISSING-FIELD、E-AST-UNKNOWN-FIELD、E-AST-FIELD-TYPE、E-AST-IDENTIFIER、E-AST-INTEGER、E-AST-LIMIT-BYTES、E-AST-LIMIT-JSON-DEPTH、E-AST-LIMIT-INTEGER-DIGITS。phaseはast-boundary、ast-parse、ast-schemaの対応責務とする。schema enumにない型tagはtransport errorであり、sourceのnone[Foo]と同じコードになるとは主張しない。

### 19.4 正準化と同一性

encoder は UTF-8、最小空白、表の key 順、宣言／param／items／args の順序保持、非不要 escape、末尾改行なしで出力する。name と値 string は受理上 ASCII なので正準出力で Unicode escape を使わない。

```text
decode_ast(encode_ast(A)) = A
parse(format(A)) = A
encode_ast(parse(format(A))) = encode_ast(A)
```

この等式のdecode_ast、parse、encode_ast、formatは、有限profileによる失敗を含めない抽象的な構文codec関係／関数である。source span、JSON span、コメント、元の空白を除いた構文ASTについて主張する。decode_astの定義域は有限のschema適合ASTであり、parse／formatはさらにSurfaceで表現可能な範囲に限る。静的拒否ASTへ意味論的評価を定義するものではない。

compile、compile_astは静的検査を含む有限APIであり、上記の構文往復とは異なる。有限parser／AST decoderの成功には出力列のtransport予算、共通Admission予算、整数桁等の全該当上限と必要なホスト資源が必要である。compileのAcceptedにはさらにname、DAG、typecheck、entry等の成立が必要。同一profileで受理したsourceのformatter出力が同一profileで再受理される保証は置かない。コメント除去で短くなる場合も、空白・末尾LFの付加で長くなる場合もある。

境界fixture：関数名Nを524,276文字のASCII f列とすると、`fn N(x:Int)->Int=x entry N`の展開後sourceは1,048,576 bytes、指定format出力は1,048,582 bytes。前者のbytes guardは通過し、後者を標準source profileへ再投入するとSOURCE-BYTESで拒否する。これは抽象parse(format(A))=Aを否定しない。

```text
structural_hash(A) = BLAKE3(
  "LPTL-AST-v1\0" || encode_ast(A)
)
```

structural_hashは `ast_codec_v1` レベルの構文同一性を表す。固定domain文字列 `LPTL-AST-v1\0` はcodec／構文の版を識別し、独立した規範spec_versionではない。同じschema／codecを用いる仕様・診断の差をstructural_hashで区別しない。domain文字列は提示したv1の固定値を用いる。

規範仕様に結び付ける識別子は別に次を定義する。

```text
spec_bound_syntax_hash(spec_version,A) = BLAKE3(
  "LPTL-spec-bound-syntax-v1\0" ||
  canonical_json([spec_version, "ast_codec_v1", structural_hash(A).lower_hex])
)
```

canonical_jsonはUTF-8、空白・末尾改行なし、JSON配列の提示順とし、ASCIIのstring内容は不要escapeなしで出力する。版IDは登録済みの非空ASCII文字列とする。spec_version未確定（本成果物ではnull）の場合はこのhashを発行しない。null、仮の文書版、言語ラベルや文書版v1で代用しない。

診断・cutoff・運用結果の再現にはreproducibility recordを別に固定する。必須fields／正準key順はspec_version、codec_id、structural_hash、static_profile_id、parse_admission_id、typecheck_cost_id、input_profile_id、input_admission_id、ast_transport_profile_id、execution_profile_id、diagnostic_pipeline_id、host_policy_hash、skill_hash。各値は登録済みIDまたは指定hash算法のlowercase hex stringで、host_policy_hash／skill_hashは対応する公開bytesのSHA-256とする。structural_hashは上記BLAKE3のlowercase hex。このrecordのcanonical JSON bytesをdomain "LPTL-reproducibility-v1\0"の後に連結したBLAKE3をreproducibility_hashとする。spec_versionが未確定なら正式record／hashを発行しない。実験再現にはさらにモデル、task、予算B、seed等の第12節の記録が必要である。record一致は同じ入力や物理hostを意味せず、host結果の機種間一致も保証しない。

これは構文の hash であり、同じ入出力関数を表す別プログラムの意味等価性を判定しない。JSON member 入力順・escape・空白の差は正準化で消えるが、宣言順・binder 名は消えない。

### 19.5 実験上の公平性

Surface と AST は同じ型注釈、名前規則、DAG、組込み、entry、静的 AST／semantic 上限、input／execution profile を使用する。JSON transport 上限と source bytes／token 上限は表記固有として公開する。

AST側に型推論の追加、欠落注釈の補完、未知 field の無視、binder自動改名、循環の除去を行わない。診断の phase と byte span は表記に依存するため、バイト列一致ではなくコード分類・課題成功・共通資源量とtransport費用を区別して比較する。

### 19.6 文字列制約とschema適合性

識別子と整数は、JSON stringをdecodeした後の文字列全体について、第4.2節のIDENT・INT条件に一致しなければならない。前後の空白、LF、CR、CRLF、tab、Unicodeの行区切り、その他の余分な文字を許可しない。JSON escape自体は第19.3節に従って受理できるが、decode後の条件を緩めない。例えば `"\u0078"` は識別子 `x` として受理できるが、`"x\n"` は拒否する。

回帰用対照fixtureのアンカー候補 `^[A-Za-z_][A-Za-z0-9_]*$` と `^(0|-?[1-9][0-9]*)$` は、利用する正規表現処理系によっては末尾LF直前への一致を許す。二つのpatternだけをこの候補へ置き換える補助fixtureはアンカーの挙動を検査する対照であり、本コアの受理schemaではない。同梱schemaは末尾LF付き識別子・整数を拒否する。対照fixtureの受理挙動を本コアの受理契約に含めない。

同梱schemaの `$defs.identifier.pattern` は次のJSON表記と一致する。以下はtype・patternの抜粋であり、予約語を除外する `not.enum` は維持する。

```json
{
  "type": "string",
  "pattern": "^[A-Za-z_][A-Za-z0-9_]*(?![\\s\\S])"
}
```

同梱schemaの `$defs.expr.oneOf` 内の `tag=int` nodeについて、`properties.value` は次のJSON表記と一致する。

```json
{
  "type": "string",
  "pattern": "^(0|-?[1-9][0-9]*)(?![\\s\\S])"
}
```

上記の否定先読みは、文字列の残りにいかなる文字も存在しないことを要求する。対応しない正規表現処理系へ別のパターンを移植する場合も、文字列全体一致と予約語除外について同じ受理集合を保ち、回帰テストで照合する。strict parser側でも全体一致を検査し、schema validatorの部分一致や文字列のtrimに依存しない。識別子違反は `E-AST-IDENTIFIER`、整数正規形違反は `E-AST-INTEGER` とする。

schema適合と静的受理は別である。次の入力は構造検査を通過し得るが、共通検査を省略してはならない。

| schema適合する構造 | 共通検査での扱い |
|---|---|
| `declarations: []` | name成功かつcutoffなしならentryで `E-ENTRY-MISSING` |
| 通常callの実引数不足・過剰 | 解決済みcallならtypecheckで `E-ARITY-*` |
| 未定義の合法callee名 | nameで `E-NAME-UNKNOWN-FUNCTION` |
| foldの `acc` と `item` が同名 | nameでbinder重複を拒否 |
| `callee: "uncons"` | 合法なユーザー関数名として解決。組込みとしては扱わない |

`uncons` は第4.2節の予約語集合に含めない。従って同名の合法ユーザー関数を定義・呼び出すことは可能だが、Option payload消去や組込みの安全リスト分解を提供するものではない。将来の独立拡張で組込みとして導入する場合は、予約語・名前互換性への影響も審査する。

G0では、実schema、strict parser、文書の文字列条件が同じ受理集合を持つことを照合する。schemaファイルのハッシュとvalidatorの実装・版・設定を記録する。実体が提示されていないファイルのハッシュは unavailable とし、回帰用の再構成物のハッシュで埋めない。同梱schemaの内容識別と限定検査の範囲は第20.4–20.5節に定義する。

---

## 20. 適合テストと凍結条件

### 20.1 必須回帰テスト

| 入力／条件 | 期待される主結果 |
|---|---|
| `fn f(x: Int) -> Int = x` | entry phase の E-ENTRY-MISSING |
| `fn f(x: Int) -> Int = x entry missing entry f` | name の E-ENTRY-UNKNOWN。DUPLICATEなし |
| `fn f(x: Int) -> Int = x entry f entry f` | entry の E-ENTRY-DUPLICATE 一件 |
| `fn f() -> Int = 0 entry f` | E-ENTRY-ARITY |
| `fn f(x: Int) -> Int = x fn g(y: Int) -> Int = y entry f` | Accepted と g の W-UNUSED-FUNCTION |
| `fn f(x: Int) -> Int = x 1 entry f` | E-PARSE-UNEXPECTED-TOKEN |
| `fn f(x: Int) -> Option<Int> = none[Foo] entry f` | E-PARSE-EXPECTED-TYPE |
| 既知の `f(Int)` を `f(1,true)` と呼出し | E-ARITY-USER。true を Int と比較しない |
| `add(1,true,0)` | E-ARITY-BUILTIN。引数型比較を抑制 |
| `f(1,fst(unit))`、f は一引数 | E-ARITY-USER と独立した E-TYPE-FST-ARG |
| fold 内から現在関数を呼ぶ | E-CYCLE-CALL |
| token limit=L、ちょうどL／L+1 | 前者は次phase、後者は TOKENS cutoff |
| typecheck 中の semantic cutoff | entry／warnings を実行しない |
| recovery 8回後に更にerror | 通常errorと E-PARSE-RECOVERY-LIMIT、停止 |
| AST object 重複 key | map化前に E-AST-DUPLICATE-KEY |
| AST に `inferred_type` field | E-AST-UNKNOWN-FIELD |
| AST `var.name="if"` | E-AST-IDENTIFIER |
| ASTのfn／entry／param／var／let／fold binder／ユーザーcallee名の末尾にLF・CR・CRLF・tab | schema拒否、transportで E-AST-IDENTIFIER |
| AST識別子に前後空白・非ASCII・U+2028・U+2029 | schema拒否、transportで E-AST-IDENTIFIER |
| AST `expr int.value` の末尾にLF・CR・CRLF・tab、または前後空白・U+2028・U+2029 | schema拒否、transportで E-AST-INTEGER |
| AST整数 `"-0"`／`"01"`／`"+1"`／JSON number | 前三者は E-AST-INTEGER、JSON numberは E-AST-FIELD-TYPE |
| AST識別子 `"\u0078"`／`"x\n"` | 前者はdecode後 `x` として受理、後者は E-AST-IDENTIFIER |
| AST `declarations: []` | schema適合。共通検査で E-ENTRY-MISSING |
| AST foldのaccとitemが同名 | schema適合。共通nameでbinder重複を拒否 |
| AST `callee="uncons"`、同名fn定義なし／あり | 前者は E-NAME-UNKNOWN-FUNCTION、後者は通常ユーザーcallとして共通検査 |
| AST call に余分な通常実引数 | transport成功、typecheckで E-ARITY-* |
| AST some node に valueなし | E-AST-MISSING-FIELD |
| input int の value が JSON number | E-INPUT-*、Intとして受理しない |
| decode後の同じ key をescape違いで重複 | duplicate keyとして拒否 |
| concat 長さm,n | 結果m+n、追加consはm、要素とysを共有 |
| none を反復評価 | none由来の新規割当0 |
| let の同じ値を pair の両側で参照 | 束縛式一回、pair一ノード |
| source／AST／input のbytes上限超過かつ不正UTF-8 | bytes上限を優先、UTF-8未検査 |
| error候補33件 | 通常31件＋E-DIAG-LIMIT、一件cutoffがある場合は規定の特別選択 |
| host-policyの参照スロット／frame上限超過 | HostAborted。ResourceKindへ変換しない |
| execution profileのSteps／AllocatedNodes／IntegerBits／OutputBytes上限超過 | ResourceExhausted |
| 型共有・interning・比較cacheの有無 | 同じ論理型検査trace・仕事量・cutoff |
| 上表18.1aのadd例、SemanticWork上限9／8 | 前者は型検査完了、後者はSEMANTIC-WORK cutoff、entry／warnings停止 |
| 型構成イベントで型深さとSemanticWorkが同時超過 | SEMANTIC-TYPE-DEPTHを優先 |
| ASTの合法param `{"name":"x","type":{"tag":"int"}}` | tag検査なしでtransport成功 |
| 合法paramへtag fieldを追加 | E-AST-UNKNOWN-FIELD。tag付きparamを受理しない |
| fnのnameが予約語if、bodyがJSON number | 全直接fieldの浅い型検査が先なのでE-AST-FIELD-TYPE。name内容検査は未実施 |
| ASTで必須キー複数欠落／余分キー複数 | 欠落は表key順、余分はdecoded scalar辞書順で最初を選ぶ |
| `add(1,true,0)`、SemanticWork上限0／1 | 0はcall VisitExpr前cutoffのみ。1はE-ARITY-BUILTINを保持し最初の子VisitExpr前cutoff |
| Admission済みsomeの子unitがbudgetを超える不完全構文 | 閉じ括弧欠落より先にAST-NODES cutoff。親を完成時だけ計数しない |
| expr位置のfnへparse error後に同期 | 前の宣言開始より先ならfnを保持して新宣言試行。同期は一回 |
| parse error時の未消費tokenがEOF | 通常parse error後に停止。不要な同期回数／RECOVERY-LIMITを加算しない |
| 同期で飛ばすtokenにnode開始keywordがある | 新宣言試行までAdmissionなし。budgetをリセットしない |
| 524,276文字名のformatter境界fixture | 元source1,048,576 bytes、format後1,048,582 bytes。同一source profile再投入は拒否 |
| Int `10^4096` のcodec往復 | 抽象往復成立を証明対象。標準inputは桁数上限で拒否 |
| 3失敗候補後に1成功候補を選択したepisode | episode単位のSは1。候補受理率等とは分け、分母へ4試行を加えない |
| 最終候補選択後の隠しテスト不合格 | episode失敗。別候補へ隠し結果を見て選び直さない |
| 予算Bの一成分ちょうど上限／次操作がguardで禁止 | 両者とも実測usageが上限内ならbudget内で終了。既存Accepted候補を選択し、なければ候補なし失敗 |
| Renderに正解AST／モデル生成AST | 主Renderと連結armを別報告し、解法生成の効果へ混ぜない |
| input Pair<Unit,Unit>、深さ上限1、leftに余分キー | 子のキー検査が子Admissionより先なのでE-INPUT-UNKNOWN-FIELD |
| input Pair<Unit,Unit>、深さ上限1、子は正常Unit | 子InputAdmissionでE-LIMIT-INPUT-VALUE-DEPTH |
| 正常Unit値位置で値深さ／node数同時超過 | VALUE-DEPTHを優先し超過Admissionを発行しない |
| input Int正規形違反とnode数超過 | 浅い型通過後、AdmissionのVALUE-NODESが先。正規形は未検査 |
| input Int正規形違反と桁上限超過 | Admission通過後、E-INPUT-INTEGERが先 |
| input Int.valueがnumber、node数上限0 | 浅い型違反E-INPUT-FIELD-TYPEが先。Admissionなし |
| input／ASTの不対surrogateと重複・unknown key | JSON文法段階成功後、STRING-SCALARが先。不正string tokenをspanにする |
| input／ASTの正しいsurrogate escape対 | scalar検査通過。内容は通常のtag／キー規則で判定 |
| inputの重複keyとroot tag違反 | 全体重複段階が先でE-INPUT-DUPLICATE-KEY |
| 正常Accepted候補あり、予算ちょうど上限／次操作禁止 | 隠し採点通過ならS=1。追加compileなしで既存検証記録を使用 |
| 予算内で停止、Accepted候補なし | no_accepted_candidate、S=0 |
| 実測usageが一成分でも超過 | budget_exceeded、S=0。既存正解候補も成功にしない |
| 予算vectorの欠落成分・長さ不一致 | 無視せず設定／計測不正として扱う。budget内としない |
| 同AST／codec、異なるspec_version | structural_hashは同じ、spec_bound_syntax_hashのpreimageは異なる |
| spec_version未確定 | 仕様結合／再現用の正式hashを発行しない |


E-ARITY-USER と E-ARITY-BUILTIN は正式な具体コードとする。その他の型／name／lex／parse の具体コード、message template、全 repair 生成規則は版付き diagnostic registry に列挙して G0 で照合する。上表の E-INPUT-* は分類名であり一つの送信コードではない。

### 20.2 追加の証明義務

第11節に加え、AST strict parser の重複拒否、schema/EBNF の表現対応、AST round-trip、元 byte span 保存、limits guard の健全性、診断順の決定性、参照イベント trace への適合、出力 guard の健全性を要する。

実験のコア対照はv1／`v1-no-let` とする。異なる仕様・診断・profileの契約を比較する場合は、それぞれの差を介入要因として明示し、診断・profile差だけの比較を言語意味論の改善実験と呼ばない。Option消去課題は本コアの最終タスクに含めない。

### 20.3 出荷状態

本成果物は設計文書、AST schema、manifest、限定検査の入力・結果・補助モデル、突き合わせ確認資料である。Rust/Verus実装、機械証明、LPTL実装の実測、LLM実験、GitHub commitを含まない。G0は対応spec、実schema、完全なdiagnostic registry、Admission・型検査・実行profile trace fixtureを固定し適合照合した後、G1–G3は実装／証明／境界監査後、G4は第12節の事前登録実験後に判定する。限定schema検査や補助モデルの通過をこれらのゲートへ代用しない。

設計文書の作成をもって、全域性の機械検証、LLM優位性、ホスト資源安全性の達成と読み替えない。

### 20.4 成果物の同一性

文書、schema、検査入力、検査コード、検査結果は別々のファイル実体として、manifestにbytesとSHA-256を記録する。ファイル実体のSHA-256は、BLAKE3の言語成果物hashや規範spec_versionの代用ではない。文書自身へ自己hashを埋め込まない。manifestも自己hashを埋め込まない。

同梱AST schemaは次の実体である。ファイル名だけで内容同一性を認定せず、bytesとhashを照合する。

| 実体 | bytes | SHA-256 |
|---|---:|---|
| `ast_codec_v1.schema.json` | 10,590 | `eefa368250b12a11afc842c6f92dc03348a18a9e946a4626b23794a17341e593` |

検査用の対照schemaは実体schemaの代用品ではない。未提示ファイルの実体・hashは推測せず、unavailableとする。

### 20.5 検証範囲と未達条件

同梱の限定検査は92件の入力・期待値を持ち、schema回帰、AST header／field順、型検査trace、AST Admission、recovery、入力値Admission、JSON scalar／重複段階、探索予算、hash preimage等の狭い補助モデルを対象とする。実行結果、実行環境、具体入力、期待値、観測値は確認資料・CSV・manifestへ記録する。検査件数を別の実行件数へ合算しない。

これらの検査はstrict JSON parser、LPTL compiler／input decoder／encoder、Rust/Verus spec、機械証明、LLM実験の適合確認ではない。入力の補助モデルはPython JSON読込みでdecoded key列を保持するが、全JSON文法・number方言、元byte span、message／repair、JSON transport bytes／深さguard、ホスト障害を検証しない。予算終了の補助モデルは既定4成分と検証済み候補記録を所与とし、追加登録成分、provider usage集計器、実際の生成・検証API呼出しを実装したものではない。

hashの補助検査は仕様結合preimageのdomain NUL、JSON表現、仕様版差、null／空版の拒否に限定する。BLAKE3 digestを計算・検証せず、衝突不在を証明しない。reproducibility recordの実装適合も未検査である。

G0は未達、G1–G4は未判定とする。G0の未達項目は、対応spec、完全なdiagnostic registry、Admission・実行・型検査の参照trace fixture、strict parser／encoder／共通検査器との適合照合である。最終評価のB、反復数、モデル、最低効果量、費用・運用採否閾値は事前登録と実測・対象環境に基づいて判断する。本書は目的・原理から一意に決まらない数値を設定しない。有限検査通過を出荷・無欠陥・証明完了の宣言に代用しない。
