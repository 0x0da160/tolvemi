---
type: Language Specification
title: 型規則
description: トップレベル関数は引数型と戻り型の注釈が必須の単相型で、if・let・fold の型規則、typecheck phase での arity 検査、ErrorType による二次エラー抑制を定める。
tags: [lptl, typing, type-system, arity]
status: draft
generated: { by: claude-code/2026-10-06, at: 2026-10-06T16:00:00Z }
sources:
  - id: lptl-design
    resource: ../../spec/lptl-v1/LPTL_design_v1.md
    title: LLM向け純粋・全域言語：設計方針 v1（§6、§10.5、§18.1a）
    last_modified: 2026-10-01T00:00:00Z
---

# 注釈と単相型

- トップレベル関数の各引数型と戻り型は**必須**。[^lptl-design]
- `fold` binder の型はリスト型と初期値型から一意に決まるため表記しない。
- `let` binder の型は束縛式の型から一意に決まる。let-generalization は行わない。
- リストは空・非空を問わず `list[T](...)` と書く。`some(e)` の型は `Option<T>`（`e:T`）。
- `none[T]` の `T` は閉じた型文法で parse し、未定義型は typecheck に渡らない。

# 主要規則

```text
if(c, t, f) : T
  iff c : Bool, t : T, f : T

let x = e1 in e2 : B
  iff e1 : A かつ Γ,x:A ⊢ e2 : B

fold(xs, init, |acc, item| body) : A
  iff xs : List<X>, init : A,
      Γ,acc:A,item:X ⊢ body : A
```

- 組込みの型は [組込み関数](builtins.md) の型規則スキームに従い、実引数型だけから推論する。
- 異型 `eq(1,true)`、異型 `concat(list[Int](), list[Bool]())` 等は**静的拒否**であり、実行時に `false` や空リストにはならない。
- 最後に各関数本体型を宣言戻り型と比較する。

# arity 検査

- 関数・通常組込みの arity は **typecheck phase** で検査する（専用構文の位置不足は parse で拒否済み）。
- 通常 call の VisitExpr 直後、子の検査前に arity を判定し、不一致なら診断候補を一件生成する。
- arity 不一致でも実引数式を全て左から右に型検査する。ただし当該 call の期待引数型との比較と結果型構成は抑制し、結果は ErrorType。欠落引数への二次エラーは生成しない。
- 具体コード：`E-ARITY-USER`、`E-ARITY-BUILTIN`。

| 入力 | 主結果 |
|---|---|
| 既知の `f(Int)` を `f(1,true)` と呼出し | `E-ARITY-USER`。true を Int と比較しない |
| `add(1,true,0)` | `E-ARITY-BUILTIN`。引数型比較を抑制 |
| `f(1,fst(unit))`、f は一引数 | `E-ARITY-USER` と独立した `E-TYPE-FST-ARG` |

# 型エラー回復（ErrorType）

型検査はエラー型を内部的に用いて、独立した兄弟部分式の診断を継続する。ErrorType 由来の親の二次エラーだけを抑制する。これは「継続してよい」という実装選択ではなく規範であり、同一入力・仕様版・profile に対し診断の内容・位置・順序・件数は一意。

例：`u:Option<Pair<Int,List<Int>>>` のとき `fst(fst(u))` は内側 `fst(u)` に `E-TYPE-FST-ARG` を一件だけ報告する。

- 依存元が ErrorType なら fold の該当 binder も ErrorType とし、依存した診断を抑制する。
- 型検査は全関数を宣言順、部分式を左から右に走査し、非選択枝・未到達関数も検査する。
- 型検査の論理仕事量の計数は [static profile](../resources/static-profile.md) を参照。


# v1.4 の追加：Result と match

```text
ok<T, E>(x) : Result<T, E>    iff x : T
err<T, E>(x) : Result<T, E>   iff x : E
match_result(m, |x| a, |y| b) : A
  iff m : Result<T, E>, Γ,x:T ⊢ a : A, Γ,y:E ⊢ b : A
```

`match e { P => e, ... }` は、pattern が直和型の構築子なら e がその型（同じ宣言の型。v1.15 から名義の型）、`ok`／`err` なら
`Result`、`some`／`none` なら `Option` でなければならず（違えば `E-TYPE-MATCH-SCRUTINEE`）、各枝の束縛は中身の型を持ち、
枝の型はすべて等しい（`E-TYPE-MATCH-BRANCH`）。`_` だけの `match` は対象が直和型・`Result`・`Option` のどれかであること
を求める。詳細は [v1.4 差分仕様](../../spec/lptl-v1.4/LPTL_v1.4_delta.md)。


# v1.5 の追加：map など

```text
map(xs, |x| e)     : List<B>     iff xs : List<A>, Γ,x:A ⊢ e : B
filter(xs, |x| p)  : List<A>     iff xs : List<A>, Γ,x:A ⊢ p : Bool
any / all(xs, |x| p) : Bool      iff xs : List<A>, Γ,x:A ⊢ p : Bool
find(xs, |x| p)    : Option<A>   iff xs : List<A>, Γ,x:A ⊢ p : Bool
sort_by(xs, |x| k) : List<A>     iff xs : List<A>, Γ,x:A ⊢ k : Int
```

xs がリストでなければ `E-TYPE-HOF-LIST`、本体の型が違えば `E-TYPE-HOF-BODY`（`map` の本体は任意の型）。xs が
ErrorType なら x も ErrorType とし、依存した診断を抑制する（`fold` と同じ）。詳細は
[v1.5 差分仕様](../../spec/lptl-v1.5/LPTL_v1.5_delta.md)。

# v1.6 の追加：loop

```text
loop(init, max, |s| e) : Option<S>   iff Γ ⊢ init : S, Γ ⊢ max : Int, Γ,s:S ⊢ e : Option<S>
```

max が Int でなければ `E-TYPE-LOOP-MAX`、e が `Option<S>` でなければ `E-TYPE-LOOP-BODY`（expected に `Option<S>`、
found に e の型）。init が ErrorType なら本体の型の診断は出さない。詳細は [v1.6 差分仕様](../../spec/lptl-v1.6/LPTL_v1.6_delta.md)。

# v1.7 の追加：rec fn と呼出しグラフ

型規則は変わらない（`rec fn` の本体と呼出しは普通の関数と同じ規則で検査する）。呼出しグラフの条件だけが緩む：
`rec` の印のある関数へ入る辺を除いたグラフが DAG であればよい（[呼出しグラフと DAG](call-graph.md)）。
検証済みの型付け条件は「`rank[g] < r` または `rec[g]`」。詳細は [v1.7 差分仕様](../../spec/lptl-v1.7/LPTL_v1.7_delta.md)。

# v1.9 の追加：辞書

```text
dict<K, V>()        : Dict<K, V>
dict_get(d, k)      : Option<V>          iff d : Dict<K, V>, k : K
dict_put(d, k, v)   : Dict<K, V>         iff d : Dict<K, V>, k : K, v : V
dict_remove(d, k)   : Dict<K, V>         iff d : Dict<K, V>, k : K
dict_has(d, k)      : Bool               iff d : Dict<K, V>, k : K
dict_size(d)        : Int                iff d : Dict<K, V>
dict_keys(d)        : List<K>            iff d : Dict<K, V>      （dict_values は List<V>）
dict_entries(d)     : List<Pair<K, V>>   iff d : Dict<K, V>
dict_from(xs)       : Dict<K, V>         iff xs : List<Pair<K, V>>
```

`Dict<K, V>` と `List<Pair<K, V>>` は別の型（等価性は tag で決まる）。第 1 引数が辞書でなければ `E-TYPE-DICT-ARG`、
`dict_from` の引数が pair のリストでなければ `E-TYPE-DICT-FROM`、鍵・値の型が違えば `E-TYPE-ARG`。辞書を `fold`・`map`
などに渡すと既存の `E-TYPE-FOLD-LIST`・`E-TYPE-HOF-LIST`（修復ヒントで `dict_entries` などを示す）。詳細は [v1.9 差分仕様](../../spec/lptl-v1.9/LPTL_v1.9_delta.md)。

# v1.10 の追加：型引数

総称の関数の本体は一度だけ、型引数を不透明な型として検査する（`T` の値に使えるのは `eq`、組み・リスト・Option・辞書・
レコード・直和型への出し入れ、`fold`・`map` などと `loop`、関数への受け渡し。`add`・`lt`・`sort`・`to_string` などは
`E-TYPE-ARG`、修復ヒントで呼び出し側で行うよう示す）。呼び出し `f(e1, ..., en)` の型引数は、明示（`f<Int>(...)`）がなければ
引数の型との一階の照合で左から決める。

```text
f<T1..Tm>(x1: S1, ..., xn: Sn) -> R
f(e1, ..., en) : R[T := U]   iff ei : Si[T := U]（U は照合で一意に決まる）
```

同じ型引数に違う型が当たれば `E-TYPE-GENERIC-MISMATCH`、束縛されない型引数が残れば `E-TYPE-GENERIC-INFER`、明示した
型引数の数が違えば `E-TYPE-GENERIC-ARITY`。呼び出しの外の文脈からは推論しない。中身のない構築子は `Leaf<Int>()` と書く。
型検査の後、使われた（関数、型引数の組）ごとに複製して単相化し（`crates/tlvm/src/generics.rs`）、単相のプログラムを
もう一度検査してから検証済み部品に渡す。呼ぶたびに型引数が大きくなる再帰（多相再帰）は `E-TYPE-GENERIC-INFINITE`、
複製の数・型引数の大きさの上限は `E-LIMIT-STATIC-GENERIC-INSTANCES`。entry の関数は総称にできない（`E-ENTRY-GENERIC`）。
詳細は [v1.10 差分仕様](../../spec/lptl-v1.10/LPTL_v1.10_delta.md)。

[^lptl-design]: LLM向け純粋・全域言語：設計方針 v1
