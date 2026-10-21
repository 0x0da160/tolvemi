//! SH1：checker の `HofTypes`（node ごとの型の対）を、verus/src/hof_types.rs の写し（`hof_entry`・`form_ty`）を
//! data に書いた表と比べる。試験であって証明ではない。写しと検証済みの型付け規則との一致は
//! verus/src/hof_agree.rs・loop_types.rs・dict_types.rs、全域性は verus/src/hof_total.rs で示す。
//!
//! - 表の項目：形ごとに、被演算子の型から checker が表に入れる項目と形の型が写しと同じ（型を三通りに置いて）。
//! - 項目のない形：checker が形に ErrorType を返すとき、表に項目はない。
//! - 全域性（プログラムごと）：受理したプログラムの hof・loop・辞書の操作のどの形にも項目があり、形の node index は
//!   互いに異なり、表にほかの項目はなく、書換えの後に形は残らない。
//! - 書換えの写し：hof.rs と dict.rs の書換えの出力が、verus/src/hof_agree.rs の `hof_rw` と
//!   verus/src/dict_types.rs の `dict_rw` を文字列に写したものと一字ずつ同じ（loop の書換えは tests/loop.rs の
//!   `doubling_lowered` が同じことを確かめる）。

use std::collections::HashSet;
use tlvm::api::*;
use tlvm::checker::CheckOutcome;
use tlvm::formatter::format_program;
use tlvm::profiles::*;
use tlvm::syntax::{Expr, ExprKind, Program, DICT_OPS};

/// 型検査（`compile` と同じく、総称の関数は単相化して検査し直す）。返すのは（検査の結果、書換えに使うプログラム）。
fn checked(src: &str) -> (CheckOutcome, Program) {
    let profile = StaticProfile::default();
    let p = match parse_source(src.as_bytes(), &profile) {
        Parsed::Program(p) => p,
        _ => panic!("parse: {src}"),
    };
    let px = expand(&p).unwrap();
    tlvm::generics::check(&px, src.len(), &profile)
}

/// 検証済み部品へ渡す、書き換え後のソース。
fn lowered(src: &str) -> String {
    let (o, p) = checked(src);
    assert!(o.typed.is_some(), "{src}: {:?}", o.diagnostics);
    format_program(&tlvm::dict::erase(&lower(&tlvm::hof::lower(&p, &o.hof))))
}

fn body<'a>(p: &'a Program, name: &str) -> &'a Expr {
    &p.functions().find(|f| f.name == name).unwrap().body
}

/// node e の表の項目（型の表示）。
fn entry(o: &CheckOutcome, e: &Expr) -> Option<(String, String)> {
    o.hof
        .get(&e.meta.index)
        .map(|(a, b)| (a.to_string(), b.to_string()))
}

/// 型の文字列の中の型の名前（識別子として現れるものだけ）を置き換える。
fn inst(t: &str, sub: &[(&str, &str)]) -> String {
    fn flush(word: &mut String, out: &mut String, sub: &[(&str, &str)]) {
        let w = std::mem::take(word);
        match sub.iter().find(|(v, _)| *v == w) {
            Some((_, t)) => out.push_str(t),
            None => out.push_str(&w),
        }
    }
    let mut out = String::new();
    let mut word = String::new();
    for c in t.chars() {
        if c.is_ascii_alphanumeric() || c == '_' {
            word.push(c);
        } else {
            flush(&mut word, &mut out, sub);
            out.push(c);
        }
    }
    flush(&mut word, &mut out, sub);
    out
}

const HOF_NAMES: [&str; 6] = ["map", "filter", "any", "all", "find", "sort_by"];

/// 形 `form` を本体に持つ関数 f（被演算子は引数 p0, p1, ...。hof と loop の本体は最後の引数）と、入口の main。
fn program(form: &str, ts: &[String], result: &str) -> String {
    let params: Vec<String> = ts
        .iter()
        .enumerate()
        .map(|(i, t)| format!("p{i}: {t}"))
        .collect();
    let args: Vec<String> = (0..ts.len()).map(|i| format!("p{i}")).collect();
    let body = if form == "loop" {
        "loop(p0, p1, |s| p2)".to_string()
    } else if HOF_NAMES.contains(&form) {
        format!("{form}(p0, |x| p1)")
    } else {
        format!("{form}({})", args.join(", "))
    };
    format!(
        "fn f({}) -> {result} = {body}\nfn main(u: Unit) -> Unit = u\nentry main\n",
        params.join(", ")
    )
}

/// verus/src/hof_types.rs の写しを data にしたもの：（形、被演算子の型、`hof_entry` の項目、`form_ty` の型）。
/// 型の名前 A・B（hof の列の要素と本体）、S（loop の状態）、K・V（辞書の鍵と値）は `SUBS` で具体的な型に置く。
const TABLE: [(&str, &[&str], (&str, &str), &str); 16] = [
    ("map", &["List<A>", "B"], ("A", "B"), "List<B>"),
    ("filter", &["List<A>", "Bool"], ("A", "Bool"), "List<A>"),
    ("any", &["List<A>", "Bool"], ("A", "Bool"), "Bool"),
    ("all", &["List<A>", "Bool"], ("A", "Bool"), "Bool"),
    ("find", &["List<A>", "Bool"], ("A", "Bool"), "Option<A>"),
    ("sort_by", &["List<A>", "Int"], ("A", "Int"), "List<A>"),
    ("loop", &["S", "Int", "Option<S>"], ("S", "Option<S>"), "Option<S>"),
    ("dict_get", &["Dict<K, V>", "K"], ("K", "V"), "Option<V>"),
    ("dict_put", &["Dict<K, V>", "K", "V"], ("K", "V"), "Dict<K, V>"),
    ("dict_remove", &["Dict<K, V>", "K"], ("K", "V"), "Dict<K, V>"),
    ("dict_has", &["Dict<K, V>", "K"], ("K", "V"), "Bool"),
    ("dict_size", &["Dict<K, V>"], ("K", "V"), "Int"),
    ("dict_keys", &["Dict<K, V>"], ("K", "V"), "List<K>"),
    ("dict_values", &["Dict<K, V>"], ("K", "V"), "List<V>"),
    ("dict_entries", &["Dict<K, V>"], ("K", "V"), "List<Pair<K, V>>"),
    ("dict_from", &["List<Pair<K, V>>"], ("K", "V"), "Dict<K, V>"),
];

const SUBS: [[(&str, &str); 5]; 3] = [
    [
        ("A", "Int"),
        ("B", "Bool"),
        ("S", "Int"),
        ("K", "Int"),
        ("V", "Bool"),
    ],
    [
        ("A", "Pair<Bool, Int>"),
        ("B", "List<Option<Int>>"),
        ("S", "Pair<Int, List<Bool>>"),
        ("K", "Pair<Int, Bool>"),
        ("V", "List<Int>"),
    ],
    [
        ("A", "Option<Bool>"),
        ("B", "Dict<Int, Bool>"),
        ("S", "Dict<Int, Int>"),
        ("K", "Dict<Int, Int>"),
        ("V", "Option<Pair<Int, Int>>"),
    ],
];

#[test]
fn entries_match_the_transcription() {
    // 表は九つの辞書の操作と六つの hof と loop を一度ずつ含む
    let forms: HashSet<&str> = TABLE.iter().map(|r| r.0).collect();
    assert_eq!(forms.len(), TABLE.len());
    assert!(DICT_OPS.iter().all(|op| forms.contains(op)));
    assert!(HOF_NAMES.iter().all(|op| forms.contains(op)));
    for sub in &SUBS {
        for (form, ts, (a, b), result) in TABLE {
            let ts: Vec<String> = ts.iter().map(|t| inst(t, sub)).collect();
            let result = inst(result, sub);
            let src = program(form, &ts, &result);
            let (o, p) = checked(&src);
            // 受理した（形の型は f の返り値の型 = `form_ty`）
            assert!(o.typed.is_some(), "{src}: {:?}", o.diagnostics);
            assert_eq!(
                entry(&o, body(&p, "f")),
                Some((inst(a, sub), inst(b, sub))),
                "{src}"
            );
            assert_eq!(o.hof.len(), 1, "{src}");
        }
    }
}

/// checker が形に ErrorType を返す例（`form_ty` が None）：（形、被演算子の型、f の返り値の型）。
const REJECTED: [(&str, &[&str], &str); 21] = [
    // 列が List でない
    ("map", &["Int", "Bool"], "List<Bool>"),
    // 本体の型が違う（filter・any・all・find は Bool、sort_by は Int）
    ("filter", &["List<Int>", "Int"], "List<Int>"),
    ("any", &["List<Int>", "Int"], "Bool"),
    ("all", &["List<Int>", "Unit"], "Bool"),
    ("find", &["List<Int>", "Option<Bool>"], "Option<Int>"),
    ("sort_by", &["List<Int>", "Bool"], "List<Int>"),
    // max が Int でない、本体が Option<S> でない
    ("loop", &["Int", "Bool", "Option<Int>"], "Option<Int>"),
    ("loop", &["Int", "Int", "Option<Bool>"], "Option<Int>"),
    ("loop", &["Int", "Int", "Int"], "Option<Int>"),
    // 鍵・値の型が違う
    ("dict_get", &["Dict<Int, Bool>", "Bool"], "Option<Bool>"),
    ("dict_put", &["Dict<Int, Bool>", "Int", "Int"], "Dict<Int, Bool>"),
    ("dict_remove", &["Dict<Int, Bool>", "Bool"], "Dict<Int, Bool>"),
    // 第 1 引数が辞書でない（dict_from は List<Pair<K, V>> でない）
    ("dict_get", &["List<Pair<Int, Bool>>", "Int"], "Option<Bool>"),
    ("dict_has", &["Int", "Int"], "Bool"),
    ("dict_size", &["List<Pair<Int, Int>>"], "Int"),
    ("dict_keys", &["Int"], "List<Int>"),
    ("dict_values", &["Option<Int>"], "List<Int>"),
    ("dict_entries", &["List<Int>"], "List<Pair<Int, Int>>"),
    ("dict_from", &["List<Int>"], "Dict<Int, Int>"),
    ("dict_from", &["Dict<Int, Int>"], "Dict<Int, Int>"),
    // 引数の数が違う（E-ARITY-BUILTIN）
    ("dict_put", &["Dict<Int, Bool>", "Int"], "Dict<Int, Bool>"),
];

#[test]
fn rejected_forms_have_no_entry() {
    let mut srcs: Vec<String> = REJECTED
        .iter()
        .map(|(form, ts, result)| {
            let ts: Vec<String> = ts.iter().map(|t| t.to_string()).collect();
            program(form, &ts, result)
        })
        .collect();
    // 被演算子の型が ErrorType（add の引数の型の誤り）でも、形に項目はない
    for body in [
        "map(range(0, add(p0, true)), |x| p1)",
        "map(range(0, p0), |x| add(x, p1))",
        "loop(add(p0, p1), 3, |s| some(s))",
        "loop(p0, add(p0, p1), |s| some(s))",
        "dict_get(dict<Int, Bool>(), add(p0, p1))",
        "dict_from(map(range(0, add(p0, p1)), |x| pair(x, x)))",
    ] {
        srcs.push(format!(
            "fn f(p0: Int, p1: Bool) -> Option<Int> = {body}\nfn main(u: Unit) -> Unit = u\nentry main\n"
        ));
    }
    for src in &srcs {
        let (o, p) = checked(src);
        assert!(o.typed.is_none(), "{src}");
        assert!(!o.diagnostics.is_empty(), "{src}");
        assert_eq!(entry(&o, body(&p, "f")), None, "{src}");
    }
}

/// e の中の、書換えが表を引く形（hof、loop、辞書の操作の呼出し）。
fn forms<'a>(e: &'a Expr, out: &mut Vec<&'a Expr>) {
    match &e.kind {
        ExprKind::Hof { .. } | ExprKind::Loop { .. } => out.push(e),
        ExprKind::Call {
            callee,
            builtin: true,
            ..
        } if DICT_OPS.contains(&callee.as_str()) => out.push(e),
        _ => {}
    }
    for c in e.children() {
        forms(c, out);
    }
}

fn all_forms(p: &Program) -> Vec<&Expr> {
    let mut out = vec![];
    for f in p.functions() {
        forms(&f.body, &mut out);
    }
    out
}

/// hof・loop・辞書の操作を入れ子にし、総称の関数（二つの型で単相化する）・レコード・直和型の中でも使う。
const MIXED: &str = "type Inv = { items: Dict<Int, Int>, ops: Int }
type Op = Add(Int, Int) | Drop(Int)
fn first<T>(xs: List<T>, keep: Bool) -> Option<T> = find(xs, |x| keep)
fn count<K>(ws: List<K>) -> Dict<K, Int> =
  fold(ws, dict<K, Int>(), |d, w| dict_put(d, w, add(match_option(dict_get(d, w), 0, |c| c), 1)))
fn apply(inv: Inv, op: Op) -> Inv = match op {
  Add(k, n) => Inv { items: dict_put(inv.items, k, add(match_option(dict_get(inv.items, k), 0, |c| c), n)), ops: add(inv.ops, 1) },
  Drop(k) => Inv { items: dict_remove(inv.items, k), ..inv }
}
fn solve(xs: List<Int>) -> Pair<Option<Int>, Pair<Option<Bool>, Pair<List<Int>, Pair<Bool, Pair<Option<Int>, Pair<Inv, List<Pair<Int, Int>>>>>>>> =
  let d = count(xs) in
  let e = dict_from(map(dict_entries(d), |p| pair(snd(p), fst(p)))) in
  let inv = fold(xs, Inv { items: dict<Int, Int>(), ops: 0 }, |s, x| apply(s, if(lt(x, 0), Drop(x), Add(x, x)))) in
  pair(first(sort_by(filter(dict_keys(d), |k| dict_has(d, k)), |k| neg(k)), true),
  pair(first(map(xs, |x| lt(0, x)), any(xs, |y| all(xs, |z| eq(y, z)))),
  pair(dict_values(dict_remove(e, 1)),
  pair(eq(dict_size(d), dict_size(count(map(xs, |x| lt(0, x))))),
  pair(loop(0, 10, |s| if(lt(s, dict_size(e)), some(add(s, 1)), none<Int>())),
  pair(inv, match_option(loop(dict<Int, Int>(), 5, |m| if(lt(dict_size(m), 3), some(dict_put(m, dict_size(m), 0)), none<Dict<Int, Int>>())), list<Pair<Int, Int>>(), |r| dict_entries(r))))))))
entry solve
";

#[test]
fn every_form_in_an_accepted_program_has_an_entry() {
    let (o, p) = checked(MIXED);
    assert!(o.typed.is_some(), "{:?}", o.diagnostics);
    let fs = all_forms(&p);
    assert!(fs.len() >= 25, "{}", fs.len());
    for e in &fs {
        assert!(entry(&o, e).is_some(), "{:?}", e.kind);
    }
    // 形の node index は互いに異なり、表にはほかの項目がない
    let idx: HashSet<usize> = fs.iter().map(|e| e.meta.index).collect();
    assert_eq!(idx.len(), fs.len());
    assert_eq!(o.hof.len(), fs.len());
    // 書換えの後に、表を引く形は残らない（項目が無くてそのまま残った形はない）
    let low = tlvm::hof::lower(&p, &o.hof);
    assert!(all_forms(&low).is_empty());
    // 書き換え後のソースは検証済み部品の型検査を通る（項目の型を注釈に入れた書換えが型を持つ）
    let src = MIXED;
    match compile(src.as_bytes(), &StaticProfile::default()) {
        SourceCompile::Result(CompileResult::Accepted { .. }) => {}
        SourceCompile::Result(r) => panic!("rejected: {:?}", r.errors()),
        _ => panic!("boundary"),
    }
}

/// verus/src/hof_agree.rs の `hof_rw`（形は fold_meaning.rs と sortmeaning.rs）を文字列に写したもの。xs は列の式、
/// x は束縛、c は本体の式、t は注釈の型（`hof_note`）、導入する名前 ns[i] は hof{i + 1}（`fresh` の順）。
fn hof_rw(op: &str, xs: &str, x: &str, c: &str, t: &str) -> String {
    match op {
        "map" => format!("reverse(fold({xs}, list<{t}>(), |hof1, {x}| cons({c}, hof1)))"),
        "filter" => {
            format!("reverse(fold({xs}, list<{t}>(), |hof1, {x}| if({c}, cons({x}, hof1), hof1)))")
        }
        "any" => format!("fold({xs}, false, |hof1, {x}| if(hof1, true, {c}))"),
        "all" => format!("fold({xs}, true, |hof1, {x}| if(hof1, {c}, false))"),
        "find" => format!(
            "fold({xs}, none<{t}>(), |hof1, {x}| match_option(hof1, if({c}, some({x}), none<{t}>()), |hof2| some(hof2)))"
        ),
        _ => {
            // sort_collect の acc・e・st・y・ky・ke・rb が hof1〜hof7
            let out = "fst(snd(hof3))";
            let placed = format!("pair(fst(hof3), pair(cons(hof4, {out}), true))");
            let before = format!("pair(fst(hof3), pair(cons(hof4, cons(hof2, {out})), true))");
            let after = format!("pair(fst(hof3), pair(cons(hof4, {out}), false))");
            let compare = format!(
                "match_option(fst(hof3), pair(some(hof5), snd(hof3)), |hof6| if(lt(hof6, hof5), {before}, {after}))"
            );
            let inner = format!(
                "if(snd(snd(hof3)), {placed}, let hof5 = let {x} = hof4 in {c} in {compare})"
            );
            let scan = format!(
                "fold(cons(hof2, hof1), pair(none<Int>(), pair(list<{t}>(), false)), |hof3, hof4| {inner})"
            );
            format!(
                "fold({xs}, list<{t}>(), |hof1, hof2| let hof7 = {scan} in reverse(if(snd(snd(hof7)), fst(snd(hof7)), cons(hof2, fst(snd(hof7))))))"
            )
        }
    }
}

#[test]
fn hof_lowering_matches_the_transcription() {
    let sub = [("A", "Int"), ("B", "Bool")];
    for (op, ts, (a, b), result) in TABLE.iter().filter(|r| HOF_NAMES.contains(&r.0)) {
        let ts: Vec<String> = ts.iter().map(|t| inst(t, &sub)).collect();
        let result = inst(result, &sub);
        let src = program(op, &ts, &result);
        // 注釈の型（`hof_note`）：map は本体の型、ほかは列の要素の型
        let t = if *op == "map" {
            inst(b, &sub)
        } else {
            inst(a, &sub)
        };
        let params: Vec<String> = ts
            .iter()
            .enumerate()
            .map(|(i, t)| format!("p{i}: {t}"))
            .collect();
        assert_eq!(
            lowered(&src),
            format!(
                "fn f({}) -> {result} = {}\nfn main(u: Unit) -> Unit = u\nentry main\n",
                params.join(", "),
                hof_rw(op, "p0", "x", "p1", &t)
            ),
            "{src}"
        );
    }
}

/// verus/src/dict_types.rs の `dict_rw`（と `put_rw`・`scan_rw`）を文字列に写したもの。args は引数の式、k・v は
/// 注釈の鍵と値の型、導入する名前 ns[i] は hof{i + 1}（`fresh` の順）。
fn dict_rw(op: &str, args: &[&str], k: &str, v: &str) -> String {
    let n = |i: usize| format!("hof{}", i + 1);
    let en = format!("Pair<{k}, {v}>");
    let put = |d: &str, kk: &str, vv: &str, r: &str, acc: &str, e: &str| {
        let new = format!("pair({kk}, {vv})");
        format!(
            "let {r} = fold({d}, pair(list<{en}>(), false), |{acc}, {e}| if(eq(fst({e}), {kk}), pair(cons({new}, fst({acc})), true), pair(cons({e}, fst({acc})), snd({acc})))) in reverse(if(snd({r}), fst({r}), cons({new}, fst({r}))))"
        )
    };
    let (dd, kk) = (n(0), n(1));
    let same = |e: &str| format!("eq(fst({e}), {kk})");
    match op {
        "dict_size" => format!("length({})", args[0]),
        "dict_entries" => args[0].to_string(),
        "dict_keys" | "dict_values" => {
            let (proj, t) = if op == "dict_keys" {
                ("fst", k)
            } else {
                ("snd", v)
            };
            format!(
                "reverse(fold({}, list<{t}>(), |{}, {}| cons({proj}({}), {})))",
                args[0],
                n(0),
                n(1),
                n(1),
                n(0)
            )
        }
        "dict_from" => format!(
            "fold({}, list<{en}>(), |{}, {}| let {} = fst({}) in let {} = snd({}) in {})",
            args[0],
            n(0),
            n(1),
            n(2),
            n(1),
            n(3),
            n(1),
            put(&n(0), &n(2), &n(3), &n(4), &n(5), &n(6))
        ),
        "dict_put" => format!(
            "let {dd} = {} in let {kk} = {} in let {} = {} in {}",
            args[0],
            args[1],
            n(2),
            args[2],
            put(&dd, &kk, &n(2), &n(3), &n(4), &n(5))
        ),
        _ => {
            let (acc, e) = (n(2), n(3));
            let scan = match op {
                "dict_get" => format!(
                    "fold({dd}, none<{v}>(), |{acc}, {e}| if({}, some(snd({e})), {acc}))",
                    same(&e)
                ),
                "dict_has" => format!(
                    "fold({dd}, false, |{acc}, {e}| if({acc}, true, {}))",
                    same(&e)
                ),
                _ => format!(
                    "reverse(fold({dd}, list<{en}>(), |{acc}, {e}| if({}, {acc}, cons({e}, {acc}))))",
                    same(&e)
                ),
            };
            format!("let {dd} = {} in let {kk} = {} in {scan}", args[0], args[1])
        }
    }
}

#[test]
fn dict_lowering_matches_the_transcription() {
    let (k, v) = ("Int", "Bool");
    for (op, ts, _, result) in TABLE.iter().filter(|r| r.0.starts_with("dict_")) {
        let sub = [("K", k), ("V", v)];
        let ts: Vec<String> = ts.iter().map(|t| inst(t, &sub)).collect();
        let result = inst(result, &sub);
        let src = program(op, &ts, &result);
        let args: Vec<String> = (0..ts.len()).map(|i| format!("p{i}")).collect();
        let args: Vec<&str> = args.iter().map(|a| a.as_str()).collect();
        // 型の Dict<K, V> は List<Pair<K, V>> に消去する
        let erase = |t: &str| t.replace("Dict<Int, Bool>", "List<Pair<Int, Bool>>");
        let params: Vec<String> = ts
            .iter()
            .enumerate()
            .map(|(i, t)| format!("p{i}: {}", erase(t)))
            .collect();
        assert_eq!(
            lowered(&src),
            format!(
                "fn f({}) -> {} = {}\nfn main(u: Unit) -> Unit = u\nentry main\n",
                params.join(", "),
                erase(&result),
                dict_rw(op, &args, k, v)
            ),
            "{src}"
        );
    }
}
