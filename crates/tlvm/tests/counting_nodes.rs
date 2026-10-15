//! §18.1c の節点ごとの規則（`docs/typecheck-counting-design.md` §4.1〜§4.6）の固定値。
//!
//! 期待値は §18.1a の定義と設計書 §4 の表から手で求めたものであり、処理系の出力を写したものではない。
//! 各 program は関数 `f`（と、呼ばれる関数・型の宣言）に `entry f` を足したもの。注釈は事象の組ごとに一行で、
//! V は VisitExpr、B は BuildType、C は CompareType の数。Equal は構成子の対ごとに 1（最初の不一致で止まる）、
//! Head は 1。「戻り」は本体の型と宣言の戻り型の Equal。§18.1c の代表 program の表と §18.1a の表にある節点は
//! `counting.rs`・`regression.rs` で固定済みなので、ここには置かない。

use tlvm::api::{compile, SourceCompile};
use tlvm::profiles::StaticProfile;

/// 一件：program（`entry f` はここで足す）、(V, B, C)、総計。
type Case = (&'static str, (u64, u64, u64), u64);

/// 受理したか、報告された仕事量の (V, B, C) と総計、診断の code（`src` は entry を含む全文）。
fn reported_program(src: &str) -> (bool, (u64, u64, u64), u64, Vec<&'static str>) {
    let r = match compile(src.as_bytes(), &StaticProfile::default()) {
        SourceCompile::Result(r) => r,
        SourceCompile::SourceBoundaryFailure => panic!("結果が出ない: {src}"),
    };
    let w = r
        .work()
        .unwrap_or_else(|| panic!("仕事量が報告されない: {src}"));
    let codes = r.errors().iter().map(|d| d.code).collect();
    (
        r.program().is_some(),
        (w.visit, w.build, w.compare),
        w.total(),
        codes,
    )
}

/// `reported_program` に `entry f` を足したもの。
fn reported(src: &str) -> (bool, (u64, u64, u64), u64, Vec<&'static str>) {
    reported_program(&format!("{src}\nentry f\n"))
}

/// 全件が受理され、報告の総計と内訳が手で求めた値と一致すること（食い違いはまとめて示す）。
fn accepted_with(cases: &[Case]) {
    let mut wrong = vec![];
    for &(src, vbc, total) in cases {
        assert_eq!(vbc.0 + vbc.1 + vbc.2, total, "期待値の内訳と総計: {src}");
        let got = reported(src);
        if got != (true, vbc, total, vec![]) {
            wrong.push(format!("{src}\n  期待 {vbc:?} {total}、報告 {got:?}"));
        }
    }
    assert!(wrong.is_empty(), "{}", wrong.join("\n"));
}

#[test]
fn literals_and_text_builtins() {
    // §4.1：リテラルと v1.2 の文字・文字列の組込み
    accepted_with(&[
        // V 1：true ／ B 1：Bool ／ C 1：戻り Equal(Bool, Bool)
        ("fn f(x: Int) -> Bool = true", (1, 1, 1), 3),
        // V 1：unit ／ B 1：Unit ／ C 1：戻り
        ("fn f(x: Int) -> Unit = unit", (1, 1, 1), 3),
        // V 1：'a' ／ B 1：Char ／ C 1：戻り Equal(Char, Char)
        ("fn f(x: Int) -> Char = 'a'", (1, 1, 1), 3),
        // V 2：code、c ／ B 1：Int ／ C 2：Equal(c, Char)、戻り
        ("fn f(c: Char) -> Int = code(c)", (2, 1, 2), 5),
        // V 2：char、n ／ B 2：Char、Option<Char> ／ C 3：Equal(n, Int)、戻り Equal(Option<Char>, …) 2
        ("fn f(n: Int) -> Option<Char> = char(n)", (2, 2, 3), 7),
        // V 2：to_string、n ／ B 2：Char、List<Char> ／ C 3：Equal(n, Int)、戻り Equal(String, String) 2
        ("fn f(n: Int) -> String = to_string(n)", (2, 2, 3), 7),
        // V 2：parse_int、s ／ B 2：Int、Option<Int> ／ C 4：Equal(s, List<Char>) 2、戻り 2
        (
            "fn f(s: String) -> Option<Int> = parse_int(s)",
            (2, 2, 4),
            8,
        ),
    ]);
}

#[test]
fn arithmetic_and_comparison_builtins() {
    // §4.1：整数の組込みと比較（add と div は §18.1a・§18.1c の表で固定済み）
    accepted_with(&[
        // V 3：sub、x、1 ／ B 2：1 の Int、結果 Int ／ C 3：Equal(x, Int)、Equal(1, Int)、戻り
        ("fn f(x: Int) -> Int = sub(x, 1)", (3, 2, 3), 8),
        // V 3：mul、x、x ／ B 1：結果 Int ／ C 3：Equal(x, Int) 2 回、戻り
        ("fn f(x: Int) -> Int = mul(x, x)", (3, 1, 3), 7),
        // V 3：min、x、1 ／ B 2：1 の Int、結果 Int ／ C 3：Equal 2 回、戻り
        ("fn f(x: Int) -> Int = min(x, 1)", (3, 2, 3), 8),
        // V 3：max、x、1 ／ B 2：1 の Int、結果 Int ／ C 3：Equal 2 回、戻り
        ("fn f(x: Int) -> Int = max(x, 1)", (3, 2, 3), 8),
        // V 2：neg、x ／ B 1：結果 Int ／ C 2：Equal(x, Int)、戻り
        ("fn f(x: Int) -> Int = neg(x)", (2, 1, 2), 5),
        // V 3：lt、x、1 ／ B 2：1 の Int、結果 Bool ／ C 3：Equal 2 回、戻り Equal(Bool, Bool)
        ("fn f(x: Int) -> Bool = lt(x, 1)", (3, 2, 3), 8),
        // V 3：le、x、x ／ B 1：結果 Bool ／ C 3：Equal 2 回、戻り
        ("fn f(x: Int) -> Bool = le(x, x)", (3, 1, 3), 7),
        // V 3：eq、x、x ／ B 1：結果 Bool ／ C 3：Equal(List<Int>, List<Int>) 2、戻り
        ("fn f(x: List<Int>) -> Bool = eq(x, x)", (3, 1, 3), 7),
        // V 3：mod、x、2 ／ B 3：2 の Int、内側 Int、外側 Option<Int>
        // C 4：Equal 2 回、戻り Equal(Option<Int>, Option<Int>) 2
        ("fn f(x: Int) -> Option<Int> = mod(x, 2)", (3, 3, 4), 10),
    ]);
}

#[test]
fn list_and_pair_builtins() {
    // §4.1：リストと pair の組込み（list、some、none、uncons、contains、sort、range は固定済み）
    accepted_with(&[
        // V 2：length、x ／ B 1：Int ／ C 2：Head(x, List)、戻り
        ("fn f(x: List<Int>) -> Int = length(x)", (2, 1, 2), 5),
        // V 2：reverse、x ／ B 0 ／ C 3：Head(x, List)、戻り Equal(List<Int>, List<Int>) 2
        ("fn f(x: List<Int>) -> List<Int> = reverse(x)", (2, 0, 3), 5),
        // V 3：cons、1、x ／ B 1：1 の Int ／ C 4：Head(x, List)、Equal(1, 要素 Int)、戻り 2
        ("fn f(x: List<Int>) -> List<Int> = cons(1, x)", (3, 1, 4), 8),
        // V 3：concat、x、x ／ B 0 ／ C 5：Head(a, List)、Head(b, List)、Equal(要素, 要素)、戻り 2
        (
            "fn f(x: List<Int>) -> List<Int> = concat(x, x)",
            (3, 0, 5),
            8,
        ),
        // V 2：fst、p ／ B 0 ／ C 2：Head(p, Pair)、戻り Equal(Int, Int)
        ("fn f(p: Pair<Int, Bool>) -> Int = fst(p)", (2, 0, 2), 4),
        // V 2：snd、p ／ B 0 ／ C 2：Head(p, Pair)、戻り Equal(Bool, Bool)
        ("fn f(p: Pair<Int, Bool>) -> Bool = snd(p)", (2, 0, 2), 4),
        // V 3：pair、x、true ／ B 2：Bool、Pair ／ C 3：戻り Equal(Pair<Int, Bool>, Pair<Int, Bool>)
        (
            "fn f(x: Int) -> Pair<Int, Bool> = pair(x, true)",
            (3, 2, 3),
            8,
        ),
    ]);
}

#[test]
fn dict_builtins() {
    // §4.1：v1.9 の辞書（書換え前の呼出しを数える。規則 R）。dict_get と dict_put は §18.1c の表で固定済み
    accepted_with(&[
        // V 1：dict ／ B 1：Dict<Int, Bool> ／ C 3：戻り Equal(Dict<Int, Bool>, Dict<Int, Bool>)
        (
            "fn f(x: Int) -> Dict<Int, Bool> = dict<Int, Bool>()",
            (1, 1, 3),
            5,
        ),
        // V 3：dict_size、dict_from、x ／ B 2：Dict<Int, Bool>、Int
        // C 4：Head(x, List)、Head(要素, Pair)、Head(d, Dict)、戻り
        (
            "fn f(x: List<Pair<Int, Bool>>) -> Int = dict_size(dict_from(x))",
            (3, 2, 4),
            9,
        ),
        // V 3：dict_has、dict、x ／ B 2：Dict<Int, Bool>、Bool ／ C 3：Head(d, Dict)、Equal(x, Int)、戻り
        (
            "fn f(x: Int) -> Bool = dict_has(dict<Int, Bool>(), x)",
            (3, 2, 3),
            8,
        ),
        // V 4：dict_size、dict_remove、dict、x ／ B 2：Dict<Int, Bool>、Int
        // C 4：Head(d, Dict)、Equal(x, Int)（dict_remove）、Head(d, Dict)（dict_size）、戻り
        (
            "fn f(x: Int) -> Int = dict_size(dict_remove(dict<Int, Bool>(), x))",
            (4, 2, 4),
            10,
        ),
        // V 2：dict_keys、dict ／ B 2：Dict<Int, Bool>、List<Int> ／ C 3：Head(d, Dict)、戻り 2
        (
            "fn f(x: Int) -> List<Int> = dict_keys(dict<Int, Bool>())",
            (2, 2, 3),
            7,
        ),
        // V 2：dict_values、dict ／ B 2：Dict<Int, Bool>、List<Bool> ／ C 3：Head(d, Dict)、戻り 2
        (
            "fn f(x: Int) -> List<Bool> = dict_values(dict<Int, Bool>())",
            (2, 2, 3),
            7,
        ),
        // V 2：dict_entries、dict ／ B 3：Dict<Int, Bool>、Pair<Int, Bool>、List<Pair<Int, Bool>>
        // C 5：Head(d, Dict)、戻り Equal(List<Pair<Int, Bool>>, …) 4
        (
            "fn f(x: Int) -> List<Pair<Int, Bool>> = dict_entries(dict<Int, Bool>())",
            (2, 3, 5),
            10,
        ),
    ]);
}

#[test]
fn result_and_sum_nodes() {
    // §4.2：Result の構築（Inj）、match_result、直和型の構築と match（受理のときは印なしの写しの数。規則 T）
    accepted_with(&[
        // V 2：ok、x ／ B 1：Result<Int, Bool> ／ C 4：Equal(x, Int)、戻り Equal(Result<Int, Bool>, …) 3
        (
            "fn f(x: Int) -> Result<Int, Bool> = ok<Int, Bool>(x)",
            (2, 1, 4),
            7,
        ),
        // V 2：err、true ／ B 2：Bool、Result<Int, Bool> ／ C 4：Equal(true, Bool)、戻り 3
        (
            "fn f(x: Int) -> Result<Int, Bool> = err<Int, Bool>(true)",
            (2, 2, 4),
            8,
        ),
        // V 4：match_result、r、v、0 ／ B 1：0 の Int ／ C 3：Head(r, Result)、Equal(err 枝, ok 枝)、戻り
        (
            "fn f(r: Result<Int, Bool>) -> Int = match_result(r, |v| v, |e| 0)",
            (4, 1, 3),
            8,
        ),
        // 変種 2 の構築は err(ok(true)) の二段（T = Result<Int, Result<Bool, Int>>）
        // V 3：err、ok、true ／ B 3：Bool、Result<Bool, Int>、Result<Int, Result<Bool, Int>>
        // C 9：Equal(true, Bool) 1、Equal(Result<Bool, Int>, …) 3、戻り Equal(T, T) 5
        (
            "type T = A(Int) | B(Bool) | C(Int)\nfn f(x: Int) -> T = B(true)",
            (3, 3, 9),
            15,
        ),
        // 直和型の match（S = Result<Int, Bool>）。V 4：match、s、r、0 ／ B 1：0 の Int
        // C 5：Equal(s の型, S) 3、Equal(二つ目の枝, 最初の枝) 1、戻り 1
        (
            "type S = Circle(Int) | Sq(Bool)\nfn f(s: S) -> Int = match s { Circle(r) => r, Sq(b) => 0 }",
            (4, 1, 5),
            10,
        ),
        // 変種 3 の match。V 5：match、t、a、0、c ／ B 1：0 の Int
        // C 8：Equal(t の型, T) 5、Equal(二つ目, 最初) 1、Equal(三つ目, 最初) 1、戻り 1
        (
            "type T = A(Int) | B(Bool) | C(Int)\nfn f(t: T) -> Int = match t { A(a) => a, B(b) => 0, C(c) => c }",
            (5, 1, 8),
            14,
        ),
        // Result 族の match。V 4：match、r、v、0 ／ B 1 ／ C 3：Head(r, Result)、Equal(二つ目, 最初)、戻り
        (
            "fn f(r: Result<Int, Bool>) -> Int = match r { ok(v) => v, err(e) => 0 }",
            (4, 1, 3),
            8,
        ),
        // Option 族の match。V 4：match、o、v、0 ／ B 1 ／ C 3：Head(o, Option)、Equal(二つ目, 最初)、戻り
        (
            "fn f(o: Option<Int>) -> Int = match o { some(v) => v, none => 0 }",
            (4, 1, 3),
            8,
        ),
        // 族が決まらない match（`_` だけ）。V 3：match、x、0 ／ B 1：0 の Int ／ C 2：族の確認 1、戻り
        (
            "type S = A | B\nfn f(x: S) -> Int = match x { _ => 0 }",
            (3, 1, 2),
            6,
        ),
        // 同じく Option の値。V 3 ／ B 1 ／ C 2
        (
            "fn f(x: Option<Int>) -> Int = match x { _ => 0 }",
            (3, 1, 2),
            6,
        ),
    ]);
}

/// 宣言が再帰する型の代表 program（`counting.rs` の TREE_SIZE と同じ）。
const TREE_SIZE: &str = "type Tree = Leaf | Node(Tree, Int, Tree)\nrec fn size(t: Tree) -> Int = match t { Leaf => 0, Node(l, v, r) => add(size(l), add(v, size(r))) }\nfn solve(n: Int) -> Int = size(Node(Leaf, n, Leaf))\nentry solve\n";

#[test]
fn records_and_recursive_sums() {
    // §4.3：レコードの参照と構築、再帰する直和型（展開の形は recursive.rs の
    // recursive_helper_shapes_match_the_deltas で固定した全文）
    accepted_with(&[
        // P = Pair<Int, Bool>。V 2：Field、p ／ B 0 ／ C 4：Equal(p の型, P) 3、戻り 1
        (
            "type P = { x: Int, y: Bool }\nfn f(p: P) -> Int = p.x",
            (2, 0, 4),
            6,
        ),
        // Q = Pair<Int, Pair<Bool, Int>>。V 2：Field、q ／ B 0 ／ C 6：Equal(q の型, Q) 5、戻り 1
        (
            "type Q = { a: Int, b: Bool, c: Int }\nfn f(q: Q) -> Int = q.c",
            (2, 0, 6),
            8,
        ),
        // 3 項のレコードは pair 二つ：pair(x, pair(true, 1))。V 5：pair、x、pair、true、1
        // B 4：Bool、Int、内側の Pair、外側の Pair ／ C 5：戻り Equal(Q, Q) 5
        (
            "type Q = { a: Int, b: Bool, c: Int }\nfn f(x: Int) -> Q = Q { a: x, b: true, c: 1 }",
            (5, 4, 5),
            14,
        ),
        // 再帰する型を宣言しただけでも、構成子の関数と補助関数を宣言として各一度数える（関数ごと）：
        // f：V 1、C 1（戻り）＝ 2
        // end_new = list<Int>(0)：V 2、B 2、C 3（Equal(0, Int)、戻り 2）＝ 7
        // link_new = concat(list<Int>(1), concat(list<Int>(length(a)), a))：V 8、B 4（Int と List が二組）、
        //   C 11（list の Equal 2、length の Head 1、concat 3 ×2、戻り 2）＝ 23
        // rec_drop：V 26、B 8、C 25 ＝ 59（fold の本体 V 19、B 5、C 16、本体と init の Equal 4）
        // rec_take：V 22、B 7、C 23 ＝ 52（fold の本体 V 15、B 4、C 14、本体と init の Equal 4）
        // rec_at：V 8、B 2、C 9（呼出しの引数の Equal 3 ×2、Head 1、本体と init 1、戻り 1）＝ 19
        // 計 V 67、B 23、C 72
        (
            "type Chain = End | Link(Chain)\nfn f(x: Int) -> Int = x",
            (67, 23, 72),
            162,
        ),
    ]);
    // TREE_SIZE（`counting.rs` では処理系の出力として 356 を固定した）を規則から手で数える。関数ごと：
    // size：let scrut と t と let tag（V 3）、rec_at(scrut, 0)（V 3、B 1、C 3）、
    //   if(eq(tag, 0), 0, …)（V 5、B 3、C 3：Equal(tag, Int)、Equal(Bool)、Equal(then, else)）、
    //   else 側の let 12 個（V 12）、束縛の値（V 42、B 12、C 43：rec_drop(·, 1) 1 個 3/1/3、rec_at 4 個 3/1/3、
    //   rec_take(rec_drop(·, 1), ·) 3 個 5/1/6、rec_drop(·, add(1, ·)) 2 個 5/2/5、変数 2 個 1/0/0）、
    //   add(size(l), add(v, size(r)))（V 7、B 2、C 8）、戻り（C 1）。計 V 72、B 18、C 58 ＝ 148
    // solve：size(node_new(list<Int>(0), n, list<Int>(0)))：V 7、B 4、C 10
    //   （list の Equal 2、node_new の引数 5、size の引数 2、戻り 1）＝ 21
    // leaf_new ＝ 7（end_new と同じ形）
    // node_new：concat 5 段：V 18、B 8、C 24（list の Equal と length の Head 7、concat 3 ×5、戻り 2）＝ 50
    // rec_drop 59、rec_take 52、rec_at 19（上と同じ）
    // 計 V 155、B 49、C 152
    assert_eq!(
        reported_program(TREE_SIZE),
        (true, (155, 49, 152), 356, vec![])
    );
}

#[test]
fn function_taking_builtins() {
    // §4.4：関数を取る組込み（書換え前の節点を数える。規則 R）。map は §18.1c の表で固定済み
    accepted_with(&[
        // V 5：filter、x、lt、y、2 ／ B 2：2 の Int、lt の Bool
        // C 6：Head(x, List)、lt の Equal 2、Equal(p, Bool)、戻り Equal(List<Int>, List<Int>) 2
        (
            "fn f(x: List<Int>) -> List<Int> = filter(x, |y| lt(y, 2))",
            (5, 2, 6),
            13,
        ),
        // V 5：any、x、lt、y、2 ／ B 3：Int、Bool、結果 Bool ／ C 5：Head、Equal 2、Equal(p, Bool)、戻り
        (
            "fn f(x: List<Int>) -> Bool = any(x, |y| lt(y, 2))",
            (5, 3, 5),
            13,
        ),
        // V 5：all、x、lt、y、2 ／ B 3：Int、Bool、結果 Bool ／ C 5：Head、Equal 2、Equal(p, Bool)、戻り
        (
            "fn f(x: List<Int>) -> Bool = all(x, |y| lt(y, 2))",
            (5, 3, 5),
            13,
        ),
        // V 5：find、x、lt、y、2 ／ B 3：Int、Bool、結果 Option<Int>
        // C 6：Head、Equal 2、Equal(p, Bool)、戻り Equal(Option<Int>, Option<Int>) 2
        (
            "fn f(x: List<Int>) -> Option<Int> = find(x, |y| lt(y, 2))",
            (5, 3, 6),
            14,
        ),
        // 鍵の binder の型は要素の型（Bool）。V 6：sort_by、x、if、y、1、0 ／ B 2：1 と 0 の Int
        // C 6：Head(x, List)、if の Equal(y, Bool) と Equal(1, 0)、Equal(k, Int)、戻り Equal(List<Bool>, …) 2
        (
            "fn f(x: List<Bool>) -> List<Bool> = sort_by(x, |y| if(y, 1, 0))",
            (6, 2, 6),
            14,
        ),
    ]);
}

#[test]
fn calls() {
    // §4.6：呼出し。総称の関数は規則 G（第一パスは全関数を宣言の形で、第二パスは複製の本体だけ）
    accepted_with(&[
        // 非総称の呼出し。g：V 1、C 1（戻り）
        // f：V 3：g、x、true ／ B 1：Bool ／ C 3：Equal(x, Int)、Equal(true, Bool)、戻り（戻り型は参照で B 0）
        (
            "fn g(a: Int, b: Bool) -> Int = a\nfn f(x: Int) -> Int = g(x, true)",
            (4, 1, 4),
            9,
        ),
        // 型引数二つと構成子の bind。第一パス first：V 2：fst、p ／ C 2：Head(p, Pair)、戻り Equal(A, A)
        // 第一パス f：V 4：first、pair、x、true ／ B 5：Bool、Pair、型引数 A と B、戻り型
        //   C 4：bind(Pair<A, B>, Pair<Int, Bool>) の構成子 1・A 1・B 1、戻り Equal(Int, Int)
        // 複製 first<Int, Bool>：V 2、C 2（Head、戻り）
        (
            "fn first<A, B>(p: Pair<A, B>) -> A = fst(p)\nfn f(x: Int) -> Int = first(pair(x, true))",
            (8, 5, 8),
            21,
        ),
        // 既に束縛のある型引数の bind（同じ型引数が二度現れる呼出し、型引数を明示した呼出し）は、§4.6 の文言の読みが
        // 二通りあるので、ここでは固定していない。
        // 引数に現れない型引数を明示する。第一パス mk：V 1：list ／ B 1：List<T> ／ C 2：戻り
        // 第一パス f：V 2：mk、x ／ B 2：型引数 T、戻り型 ／ C 3：bind(Int, Int) は Equal 1、戻り 2
        // 複製 mk<Int>：V 1、B 1、C 2
        (
            "fn mk<T>(x: Int) -> List<T> = list<T>()\nfn f(x: Int) -> List<Int> = mk<Int>(x)",
            (4, 4, 7),
            15,
        ),
    ]);
}

#[test]
fn rejected_calls_count_no_comparison_or_result_type() {
    // §4.6：個数が違う呼出しは、引数の検査を続け、比較せず拒否する（結果は ErrorType）。
    // g：V 1、C 1 ／ f：V 3：g、x、true ／ B 1：Bool ／ C 0（引数の比較なし、戻りは ErrorType との比較で 0）
    assert_eq!(
        reported("fn g(a: Int) -> Int = a\nfn f(x: Int) -> Int = g(x, true)"),
        (false, (4, 1, 1), 6, vec!["E-ARITY-USER"])
    );
    // 推論できない型引数があれば 0 で拒否する（bind は済ませる）。第二パスはない。
    // 第一パス mk：V 1、B 1、C 2 ／ f：V 2：mk、x ／ B 0 ／ C 1：bind(Int, Int) は Equal 1（戻りは ErrorType で 0）
    assert_eq!(
        reported("fn mk<T>(x: Int) -> List<T> = list<T>()\nfn f(x: Int) -> List<Int> = mk(x)"),
        (false, (3, 1, 3), 7, vec!["E-TYPE-GENERIC-INFER"])
    );
}
