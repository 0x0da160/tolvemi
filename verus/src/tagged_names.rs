//! 印つきの名前表の性質（段階 2 の S3d）。仕様の関数（to_ty・rec_from・tb_push・decl_table・ty_expr）について、
//! 次を証明する。いずれも仕様の上の性質で、テストではない（表が nominal.rs の表と同じかどうかは、テスト V3 と S3c で確かめる）。
//! T1 項目：記録の宣言の項目（位置 k）は、名前 r と、その前の表から作った印つきの字段の構造 Body_k を持つ。名義の印つきの
//!    写しは Pair<tag(k), Body_k>（Body_k が定まるとき）。証明は宣言の数の帰納（位置 k の項目は、後の表で動かない）。
//! T2 印の頭：番号が違えば、Pair<tag(j), _> と Pair<tag(k), _> は違う（tag_ty_inj）。
//! T3 名義の単射性（経路の形 apart）：二つの型が、一か所の名義（番号が違う）でだけ違い、どちらも写せるなら、印つきの写しは違う。
//! T4 核の結論：T3 の二つの型の一方を引数の型、他方を仮引数の型とする呼出しは、型の規則（ty_expr の Call の腕）で拒否される。
//! 証明していないこと：表が nominal.rs の表と同じであること（パリティ）。resolve.rs は変えていない（印なしの経路も同じ）。

use vstd::prelude::*;
use crate::ir::*;
use crate::resolve::*;
use crate::spec::*;
use crate::surface::*;
use crate::syntax::*;

verus! {

// ------------------------------------------------------------------ 表の補題

/// idx の答えは表の内側（長さより小さい）。
proof fn idx_lt(s: Seq<Seq<char>>, x: Seq<char>, i: nat)
    requires
        idx(s, x, i) is Some,
    ensures
        idx(s, x, i)->Some_0 < s.len(),
    decreases s.len() - i,
{
    reveal_with_fuel(idx, 2);
    if i >= s.len() {
    } else if s[i as int] == x {
    } else {
        idx_lt(s, x, i + 1);
    }
}

/// 位置 k に x があり、i から k の前までに x がなければ、idx は k を返す（名前の最初の位置）。
proof fn idx_first(s: Seq<Seq<char>>, x: Seq<char>, i: nat, k: nat)
    requires
        i <= k < s.len(),
        s[k as int] == x,
        forall|j: int| i <= j < k ==> s[j] != x,
    ensures
        idx(s, x, i) == Some(k),
    decreases k - i,
{
    reveal_with_fuel(idx, 2);
    if i == k {
    } else {
        idx_first(s, x, i + 1, k);
    }
}

/// idx が None なら、i より後の位置に x はない。
proof fn idx_none(s: Seq<Seq<char>>, x: Seq<char>, i: nat)
    requires
        idx(s, x, i) is None,
    ensures
        forall|j: int| i <= j < s.len() ==> s[j] != x,
    decreases s.len() - i,
{
    reveal_with_fuel(idx, 2);
    if i >= s.len() {
    } else if s[i as int] == x {
    } else {
        idx_none(s, x, i + 1);
    }
}

/// 表の一歩：宣言 n-1 を足した表が decl_table(p, n) になり、その前の表は Some。
proof fn table_step(p: Seq<Sd>, n: nat)
    requires
        0 < n <= p.len(),
        decl_table(p, n) is Some,
    ensures
        decl_table(p, (n - 1) as nat) is Some,
        decl_table(p, n) == tb_push(decl_table(p, (n - 1) as nat)->Some_0, p[(n - 1) as int]),
{
    reveal_with_fuel(decl_table, 2);
}

/// 足すとき、前の項目は変わらない（位置 j < 前の長さ）。
proof fn push_prefix(tb: Seq<(Seq<char>, Option<Ty>, Seq<Seq<char>>, Option<Ty>)>, d: Sd)
    requires
        tb_push(tb, d) is Some,
    ensures
        tb_push(tb, d)->Some_0.len() >= tb.len(),
        forall|j: int| 0 <= j < tb.len() ==> tb_push(tb, d)->Some_0[j] == tb[j],
{
    reveal(tb_push);
}

// ------------------------------------------------------------------ T1：項目

/// T1：宣言 i が記録（RecTy(r, fs, tc)）なら、その項目は位置 k（宣言の直前の表の長さ）に入り、名前は r、
/// 印つきの展開は Body_k = rec_from(fs, 0, 直前の表, true)（直前の表だけを引く）。位置 k より前の項目の名前は r でない。
proof fn entry_body(p: Seq<Sd>, i: nat, n: nat, r: Seq<char>, fs: Seq<(Seq<char>, SType)>, tc: bool)
    requires
        i < n,
        n <= p.len(),
        p[i as int] == (Sd::RecTy(r, fs, tc)),
        decl_table(p, n) is Some,
    ensures
        decl_table(p, i) is Some,
        decl_table(p, i)->Some_0.len() < decl_table(p, n)->Some_0.len(),
        decl_table(p, n)->Some_0[decl_table(p, i)->Some_0.len() as int].0 == r,
        decl_table(p, n)->Some_0[decl_table(p, i)->Some_0.len() as int].3
            == rec_from(fs, 0, decl_table(p, i)->Some_0, true),
        forall|j: int| 0 <= j < decl_table(p, i)->Some_0.len() ==> decl_table(p, n)->Some_0[j].0 != r,
    decreases n - i,
{
    reveal_with_fuel(decl_table, 2);
    reveal(tb_push);
    if n == i + 1 {
        table_step(p, n);
        assert((n - 1) as nat == i);
        let t = decl_table(p, i)->Some_0;
        // 宣言 i を足したときの表：前の表に r がなく、位置 t.len() に r の項目が入る。
        assert(tb_push(t, p[i as int]) is Some);
        assert(idx(tnames(t), r, 0) is None);
        idx_none(tnames(t), r, 0);
        assert(forall|j: int| 0 <= j < t.len() ==> t[j].0 != r) by {
            assert forall|j: int| 0 <= j < t.len() implies t[j].0 != r by {
                assert(tnames(t)[j] == t[j].0);
            }
        }
        push_prefix(t, p[i as int]);
    } else {
        table_step(p, n);
        entry_body(p, i, (n - 1) as nat, r, fs, tc);
        push_prefix(decl_table(p, (n - 1) as nat)->Some_0, p[(n - 1) as int]);
    }
}

/// T1 の名義：位置 k の名前 r の最初の位置は k（前の項目に r がない）。そこで名義の印つきの写しは
/// Pair<tag(k), Body_k>（Body_k が定まるとき）、定まらないときは None。
pub proof fn named_entry(p: Seq<Sd>, i: nat, n: nat, r: Seq<char>, fs: Seq<(Seq<char>, SType)>, tc: bool)
    requires
        i < n,
        n <= p.len(),
        p[i as int] == (Sd::RecTy(r, fs, tc)),
        decl_table(p, n) is Some,
    ensures
        idx(tnames(decl_table(p, n)->Some_0), r, 0) == Some(decl_table(p, i)->Some_0.len()),
        rec_from(fs, 0, decl_table(p, i)->Some_0, true) is Some ==> to_ty(SType::Named(r), decl_table(p, n)->Some_0, true)
            == Some(Ty::Pair(
                Box::new(tag_ty(decl_table(p, i)->Some_0.len())),
                Box::new(rec_from(fs, 0, decl_table(p, i)->Some_0, true)->Some_0),
            )),
        rec_from(fs, 0, decl_table(p, i)->Some_0, true) is None ==> to_ty(SType::Named(r), decl_table(p, n)->Some_0, true)
            is None,
{
    entry_body(p, i, n, r, fs, tc);
    let tb = decl_table(p, n)->Some_0;
    let k = decl_table(p, i)->Some_0.len();
    assert(forall|j: int| 0 <= j < k ==> tnames(tb)[j] != r) by {
        assert forall|j: int| 0 <= j < k implies tnames(tb)[j] != r by {
            assert(tnames(tb)[j] == tb[j].0);
        }
    }
    assert(tnames(tb)[k as int] == r);
    idx_first(tnames(tb), r, 0, k);
    reveal_with_fuel(to_ty, 2);
    if rec_from(fs, 0, decl_table(p, i)->Some_0, true) is Some {
        named_tagged(tb, r, k);
    }
}

// ------------------------------------------------------------------ T2：印の頭

/// T2：番号が違えば、Pair<tag(j), _> と Pair<tag(k), _> は違う（tag_ty_inj）。
pub proof fn tag_heads_differ(j: nat, k: nat, s: Ty, t: Ty)
    requires
        j != k,
    ensures
        Ty::Pair(Box::new(tag_ty(j)), Box::new(s)) != Ty::Pair(Box::new(tag_ty(k)), Box::new(t)),
{
    if Ty::Pair(Box::new(tag_ty(j)), Box::new(s)) == Ty::Pair(Box::new(tag_ty(k)), Box::new(t)) {
        assert(tag_ty(j) == tag_ty(k));
        tag_ty_inj(j, k);
    }
}

// ------------------------------------------------------------------ T3：名義の単射性

/// 経路の形：a と b は、ちょうど一か所（経路）でだけ違う。そこでは両方が名義の頭で、表の番号が違う（j ≠ k）。
/// Pair・Result・Dict では片方の字段が違い、もう片方は同じ。List・Option では中身が違う。
pub open spec fn apart(a: SType, b: SType, tb: Seq<(Seq<char>, Option<Ty>, Seq<Seq<char>>, Option<Ty>)>) -> bool
    decreases a,
{
    match (a, b) {
        (SType::Named(x), SType::Named(y)) => match (idx(tnames(tb), x, 0), idx(tnames(tb), y, 0)) {
            (Some(j), Some(k)) => j != k,
            _ => false,
        },
        (SType::List(a1), SType::List(b1)) => apart(*a1, *b1, tb),
        (SType::Option(a1), SType::Option(b1)) => apart(*a1, *b1, tb),
        (SType::Pair(a1, a2), SType::Pair(b1, b2)) => (apart(*a1, *b1, tb) && *a2 == *b2) || (*a1 == *b1 && apart(*a2, *b2, tb)),
        (SType::Result(a1, a2), SType::Result(b1, b2)) => (apart(*a1, *b1, tb) && *a2 == *b2) || (*a1 == *b1 && apart(*a2, *b2, tb)),
        (SType::Dict(a1, a2), SType::Dict(b1, b2)) => (apart(*a1, *b1, tb) && *a2 == *b2) || (*a1 == *b1 && apart(*a2, *b2, tb)),
        _ => false,
    }
}

/// T3：経路の形で違う二つの型は、両方が写せるなら、印つきの写しは違う（経路の帰納）。
pub proof fn apart_differ(a: SType, b: SType, tb: Seq<(Seq<char>, Option<Ty>, Seq<Seq<char>>, Option<Ty>)>)
    requires
        apart(a, b, tb),
        to_ty(a, tb, true) is Some,
        to_ty(b, tb, true) is Some,
    ensures
        to_ty(a, tb, true) != to_ty(b, tb, true),
    decreases a,
{
    reveal_with_fuel(apart, 2);
    reveal_with_fuel(to_ty, 2);
    match a {
        SType::Named(x) => match b {
            SType::Named(y) => {
                assert(idx(tnames(tb), x, 0) is Some);
                assert(idx(tnames(tb), y, 0) is Some);
                idx_lt(tnames(tb), x, 0);
                idx_lt(tnames(tb), y, 0);
                let j = idx(tnames(tb), x, 0)->Some_0;
                let k = idx(tnames(tb), y, 0)->Some_0;
                assert(idx(tnames(tb), x, 0) == Some(j));
                assert(idx(tnames(tb), y, 0) == Some(k));
                assert(j < tb.len());
                assert(k < tb.len());
                assert(tb[j as int].3 is Some);
                assert(tb[k as int].3 is Some);
                named_tagged(tb, x, j);
                named_tagged(tb, y, k);
                tag_heads_differ(j, k, tb[j as int].3->Some_0, tb[k as int].3->Some_0);
            },
            _ => {},
        },
        SType::List(a1) => match b {
            SType::List(b1) => {
                apart_differ(*a1, *b1, tb);
            },
            _ => {},
        },
        SType::Option(a1) => match b {
            SType::Option(b1) => {
                apart_differ(*a1, *b1, tb);
            },
            _ => {},
        },
        SType::Pair(a1, a2) => match b {
            SType::Pair(b1, b2) => {
                if apart(*a1, *b1, tb) && *a2 == *b2 {
                    apart_differ(*a1, *b1, tb);
                } else {
                    apart_differ(*a2, *b2, tb);
                }
            },
            _ => {},
        },
        SType::Result(a1, a2) => match b {
            SType::Result(b1, b2) => {
                if apart(*a1, *b1, tb) && *a2 == *b2 {
                    apart_differ(*a1, *b1, tb);
                } else {
                    apart_differ(*a2, *b2, tb);
                }
            },
            _ => {},
        },
        SType::Dict(a1, a2) => match b {
            SType::Dict(b1, b2) => {
                if apart(*a1, *b1, tb) && *a2 == *b2 {
                    apart_differ(*a1, *b1, tb);
                } else {
                    apart_differ(*a2, *b2, tb);
                }
            },
            _ => {},
        },
        _ => {},
    }
}

// ------------------------------------------------------------------ T4：核の結論

/// T4：引数の型が b 側（呼出しの引数の型の一つは a の写し）、仮引数の型が b の写しで、a と b が一か所の名義で違えば、
/// 型の規則は呼出しを拒否する（ty_expr の Call の腕は、全部の位置で型が等しいことを要る）。
pub proof fn call_rejects(p: Prog, r: nat, ctx: Map<nat, Ty>, g: nat, es: Seq<Expr>, ts: Seq<Ty>, k: nat, a: SType, b: SType,
    tb: Seq<(Seq<char>, Option<Ty>, Seq<Seq<char>>, Option<Ty>)>)
    requires
        ty_args(p, r, ctx, es, 0) == Some(ts),
        g < p.funcs.len(),
        ts.len() == p.funcs[g as int].params.len(),
        k < ts.len(),
        to_ty(a, tb, true) == Some(ts[k as int]),
        to_ty(b, tb, true) == Some(p.funcs[g as int].params[k as int].1),
        apart(a, b, tb),
    ensures
        ty_expr(p, r, ctx, Expr::Call(g, es)) is None,
{
    reveal_with_fuel(ty_expr, 2);
    apart_differ(a, b, tb);
    assert(ts[k as int] != p.funcs[g as int].params[k as int].1);
    assert(!(forall|m: int| 0 <= m < ts.len() ==> #[trigger] ts[m] == p.funcs[g as int].params[m].1)) by {
        if forall|m: int| 0 <= m < ts.len() ==> #[trigger] ts[m] == p.funcs[g as int].params[m].1 {
            assert(ts[k as int] == p.funcs[g as int].params[k as int].1);
        }
    }
}

// ------------------------------------------------------------------ 前提が成り立つ例

/// 二つの項目（A と B）を持つ表。
pub open spec fn tb_example() -> Seq<(Seq<char>, Option<Ty>, Seq<Seq<char>>, Option<Ty>)> {
    seq![
        (seq!['A'], Some(Ty::Int), Seq::empty(), Some(Ty::Int)),
        (seq!['B'], Some(Ty::Bool), Seq::empty(), Some(Ty::Bool)),
    ]
}

/// 前提の確認：例の表では、A と B は一か所の名義で違い（apart）、どちらも写せる。
/// したがって T3 の前提は空でない（T3 が空虚に成り立つのではない）。
proof fn apart_example()
    ensures
        apart(SType::Named(seq!['A']), SType::Named(seq!['B']), tb_example()),
        to_ty(SType::Named(seq!['A']), tb_example(), true) is Some,
        to_ty(SType::Named(seq!['B']), tb_example(), true) is Some,
{
    reveal_with_fuel(idx, 2);
    reveal_with_fuel(apart, 2);
    reveal_with_fuel(to_ty, 2);
    assert(tnames(tb_example())[0] == seq!['A']);
    assert(tnames(tb_example())[1] == seq!['B']);
    assert(seq!['A'][0] == 'A');
    assert(seq!['B'][0] == 'B');
    assert(seq!['A'] != seq!['B']) by {
        if seq!['A'] == seq!['B'] {
            assert(seq!['A'][0] == seq!['B'][0]);
        }
    }
    assert(idx(tnames(tb_example()), seq!['A'], 0) == Some(0nat));
    assert(idx(tnames(tb_example()), seq!['B'], 1) == Some(1nat));
    assert(idx(tnames(tb_example()), seq!['B'], 0) == Some(1nat));
}

} // verus!
