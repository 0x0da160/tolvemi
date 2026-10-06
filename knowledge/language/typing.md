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

- 組込みの型は [組込み関数](/language/builtins.md) の型規則スキームに従い、実引数型だけから推論する。
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
- 型検査の論理仕事量の計数は [static profile](/resources/static-profile.md) を参照。

[^lptl-design]: LLM向け純粋・全域言語：設計方針 v1
