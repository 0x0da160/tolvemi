//! hof を検証済みの名前解決に入れる（段階 1b、DECISION-43。オーナーの選択「hof を resolve に入れる」）。
//!
//! 源の表面の式 `Sx` を、束縛の番号を振った源の式 `XExpr`（hof の形を含む）に解決する `hx`。束縛の番号は
//! 計数器 c から、割り当てた順に一つずつ取る。よって、一つの解決の中で束縛の番号は重ならず、連続した範囲
//! c, c+1, … になる（`hx_consec`）。hof の要素の型と本体の型は、表（信頼する checker の HofTypes の写し、
//! DECISION-38）から取り、表は束縛の番号で引く（hofrw.rs の rw_tb）。
//! 番号を取るたびに、次の計数器が usize に収まるかを確かめ（room）、収まらなければ None（拒否）。
//!
//! 名前解決の rx（resolve.rs）との違い：rx は束縛の番号に並びの位置（深さ）を使うので、兄弟の hof の束縛は
//! 同じ番号になりうる。hx は計数器を使うので、番号は一意になり、表を番号で引ける。
//!
//! この段階の範囲：記録（Fld、Rec）、直和型の match（SumMatch）、dict、loop は None（経路の外）。宣言された型は
//! 含まない（型の表は空として、基本の型だけを to_ty で写す）。関数の宣言と entry は次の段階で扱う。
//!
//! 示すこと：成功したときの束縛の番号の列 bnums は、c から連続した範囲に等しく、次の計数器は c + 束縛の数
//! （hx_consec）。よって、束縛の番号はすべて相異なる。
//! 扱わないこと：表と hof の番号の対応（表の並びの順、Rust 側の接着）、関数・entry の解決、exec の版、
//! 源の意味（xeval）との一致。

use crate::resolve::*;
use crate::spec::*;
use crate::syntax::*;
use crate::xsem::*;
use vstd::prelude::*;

verus! {

/// 束縛の並び：（名前、番号）の列。外側から順。並びの中で名前は重複しない（入れ子の同名は拒否する）。
pub open spec fn hlook(sc: Seq<(Seq<char>, nat)>, x: Seq<char>, i: nat) -> Option<nat>
    decreases sc.len() - i,
{
    if i >= sc.len() {
        None
    } else if sc[i as int].0 == x {
        Some(sc[i as int].1)
    } else {
        hlook(sc, x, i + 1)
    }
}

/// 文字列の綴りを文字の式の列にする。
pub open spec fn str_xs(w: Seq<char>) -> Seq<XExpr> {
    Seq::new(w.len(), |i: int| XExpr::Char(w[i] as u32 as int))
}

/// hof の語に応じた源の式。
pub open spec fn hof_x(h: Hf, xs: XExpr, x: nat, body: XExpr) -> XExpr {
    match h {
        Hf::Map => XExpr::Map(Box::new(xs), x, Box::new(body)),
        Hf::Filter => XExpr::Filter(Box::new(xs), x, Box::new(body)),
        Hf::Any => XExpr::Any(Box::new(xs), x, Box::new(body)),
        Hf::All => XExpr::All(Box::new(xs), x, Box::new(body)),
        Hf::Find => XExpr::Find(Box::new(xs), x, Box::new(body)),
        Hf::SortBy => XExpr::SortBy(Box::new(xs), x, Box::new(body)),
    }
}

/// 番号を k 個取る余地があるか（番号は usize に収まる）。収まらなければ解決は拒否する。
pub open spec fn room(c: nat, k: nat) -> bool {
    c + k <= usize::MAX as nat
}

/// 源の式の解決。c は次の束縛の番号、sc は可視の束縛、fs は関数名の列。結果は（式、次の番号）。
/// 束縛の番号は、割り当てる順に c から取る（先に式の中の束縛、次に自分の束縛、次に本体の束縛）。
pub open spec fn hx(fs: Seq<Seq<char>>, c: nat, sc: Seq<(Seq<char>, nat)>, e: Sx) -> Option<(XExpr, nat)>
    decreases e, 0nat,
{
    match e {
        Sx::Int(n) => Some((XExpr::Int(n), c)),
        Sx::Chr(ch) => Some((XExpr::Char(ch as u32 as int), c)),
        Sx::Str(w) => Some((XExpr::List(Ty::Char, str_xs(w)), c)),
        Sx::Bool(b) => Some((XExpr::Bool(b), c)),
        Sx::Unit => Some((XExpr::Unit, c)),
        Sx::Var(x) => if x.len() == 0 {
            None
        } else {
            match hlook(sc, x, 0) {
                Some(k) => Some((XExpr::Var(k), c)),
                None => None,
            }
        },
        Sx::List(t, es) => match (to_ty(t, Seq::empty(), false), hxs(fs, c, sc, es, 0)) {
            (Some(u), Some((xs, c1))) => Some((XExpr::List(u, xs), c1)),
            _ => None,
        },
        Sx::Some(a) => match hx(fs, c, sc, *a) {
            Some((x, c1)) => Some((XExpr::Some(Box::new(x)), c1)),
            None => None,
        },
        Sx::None(t) => match to_ty(t, Seq::empty(), false) {
            Some(u) => Some((XExpr::None(u), c)),
            None => None,
        },
        Sx::Pair(a, b) => match hx(fs, c, sc, *a) {
            Some((x, c1)) => match hx(fs, c1, sc, *b) {
                Some((y, c2)) => Some((XExpr::Pair(Box::new(x), Box::new(y)), c2)),
                None => None,
            },
            None => None,
        },
        Sx::Builtin(b, es) => match hxs(fs, c, sc, es, 0) {
            Some((xs, c1)) => Some((XExpr::Builtin(b, xs), c1)),
            None => None,
        },
        Sx::Call(f, es) => match idx(fs, f, 0) {
            Some(g) => match hxs(fs, c, sc, es, 0) {
                Some((xs, c1)) => Some((XExpr::Call(g, xs), c1)),
                None => None,
            },
            None => None,
        },
        Sx::Let(x, a, b) => if hlook(sc, x, 0) is Some {
            None
        } else {
            match hx(fs, c, sc, *a) {
                Some((ra, c1)) => if !room(c1, 1) {
                    None
                } else {
                    match hx(fs, c1 + 1, sc.push((x, c1)), *b) {
                        Some((rb, c2)) => Some((XExpr::Let(c1, Box::new(ra), Box::new(rb)), c2)),
                        None => None,
                    }
                },
                None => None,
            }
        },
        Sx::If(cnd, a, b) => match hx(fs, c, sc, *cnd) {
            Some((x, c1)) => match hx(fs, c1, sc, *a) {
                Some((y, c2)) => match hx(fs, c2, sc, *b) {
                    Some((z, c3)) => Some((XExpr::If(Box::new(x), Box::new(y), Box::new(z)), c3)),
                    None => None,
                },
                None => None,
            },
            None => None,
        },
        Sx::Fold(l, i, a, x, b) => if a == x || hlook(sc, a, 0) is Some || hlook(sc, x, 0) is Some {
            None
        } else {
            match hx(fs, c, sc, *l) {
                Some((rl, c1)) => match hx(fs, c1, sc, *i) {
                    Some((ri, c2)) => if !room(c2, 2) {
                        None
                    } else {
                        match hx(fs, c2 + 2, sc.push((a, c2)).push((x, c2 + 1)), *b) {
                            Some((rb, c3)) => Some((XExpr::Fold(Box::new(rl), Box::new(ri), c2, c2 + 1, Box::new(rb)), c3)),
                            None => None,
                        }
                    },
                    None => None,
                },
                None => None,
            }
        },
        Sx::Match(m, n, x, b) => if hlook(sc, x, 0) is Some {
            None
        } else {
            match hx(fs, c, sc, *m) {
                Some((rm, c1)) => match hx(fs, c1, sc, *n) {
                    Some((rn, c2)) => if !room(c2, 1) {
                        None
                    } else {
                        match hx(fs, c2 + 1, sc.push((x, c2)), *b) {
                            Some((rb, c3)) => Some((XExpr::Match(Box::new(rm), Box::new(rn), c2, Box::new(rb)), c3)),
                            None => None,
                        }
                    },
                    None => None,
                },
                None => None,
            }
        },
        Sx::Inj(ok, t, u, a) => match (to_ty(t, Seq::empty(), false), to_ty(u, Seq::empty(), false), hx(fs, c, sc, *a)) {
            (Some(t1), Some(u1), Some((x, c1))) => Some((XExpr::Inj(ok, t1, u1, Box::new(x)), c1)),
            _ => None,
        },
        Sx::MatchR(m, x, a, y, b) => if hlook(sc, x, 0) is Some || hlook(sc, y, 0) is Some {
            None
        } else {
            match hx(fs, c, sc, *m) {
                Some((rm, c1)) => if !room(c1, 1) {
                    None
                } else {
                    match hx(fs, c1 + 1, sc.push((x, c1)), *a) {
                        Some((ra, c2)) => if !room(c2, 1) {
                            None
                        } else {
                            match hx(fs, c2 + 1, sc.push((y, c2)), *b) {
                                Some((rb, c3)) => Some((XExpr::MatchR(Box::new(rm), c1, Box::new(ra), c2, Box::new(rb)), c3)),
                                None => None,
                            }
                        },
                        None => None,
                    }
                },
                None => None,
            }
        },
        // hof：列を先に解決し、次に自分の束縛の番号を取り、本体を解決する（割り当ての順）。
        Sx::Hof(h, l, x, b) => if hlook(sc, x, 0) is Some {
            None
        } else {
            match hx(fs, c, sc, *l) {
                Some((rl, c1)) => if !room(c1, 1) {
                    None
                } else {
                    match hx(fs, c1 + 1, sc.push((x, c1)), *b) {
                        Some((rb, c2)) => Some((hof_x(h, rl, c1, rb), c2)),
                        None => None,
                    }
                },
                None => None,
            }
        },
        // この段階の範囲外：記録、直和型の match、loop、dict。
        Sx::Fld(..) => None,
        Sx::Rec(..) => None,
        Sx::SumMatch(..) => None,
        Sx::Loop(..) => None,
        Sx::DictNew(..) | Sx::DictOp(..) => None,
    }
}

/// 式の列の解決（i から先）。計数器は左から順に進む。
pub open spec fn hxs(fs: Seq<Seq<char>>, c: nat, sc: Seq<(Seq<char>, nat)>, es: Seq<Sx>, i: nat) -> Option<(Seq<XExpr>, nat)>
    decreases es, es.len() - i,
{
    if i >= es.len() {
        Some((Seq::empty(), c))
    } else {
        match hx(fs, c, sc, es[i as int]) {
            Some((x, c1)) => match hxs(fs, c1, sc, es, i + 1) {
                Some((xs, c2)) => Some((seq![x] + xs, c2)),
                None => None,
            },
            None => None,
        }
    }
}

// ------------------------------------------------------------------ 束縛の番号の列

/// 式の束縛の番号を、割り当てた順に並べる（hx の割り当ての順と同じ）。
pub open spec fn bnums(e: XExpr) -> Seq<nat>
    decreases e, 0nat,
{
    match e {
        XExpr::Int(_) => Seq::empty(),
        XExpr::Bool(_) => Seq::empty(),
        XExpr::Unit => Seq::empty(),
        XExpr::Char(_) => Seq::empty(),
        XExpr::Var(_) => Seq::empty(),
        XExpr::None(_) => Seq::empty(),
        XExpr::List(_, es) => bnums_seq(es, 0),
        XExpr::Some(a) => bnums(*a),
        XExpr::Pair(a, b) => bnums(*a) + bnums(*b),
        XExpr::Builtin(_, es) => bnums_seq(es, 0),
        XExpr::Call(_, es) => bnums_seq(es, 0),
        XExpr::Let(n, a, b) => (bnums(*a) + seq![n]) + bnums(*b),
        XExpr::If(c, a, b) => (bnums(*c) + bnums(*a)) + bnums(*b),
        XExpr::Fold(l, i, a, x, b) => ((bnums(*l) + bnums(*i)) + seq![a, x]) + bnums(*b),
        XExpr::Match(m, nb, x, sm) => ((bnums(*m) + bnums(*nb)) + seq![x]) + bnums(*sm),
        XExpr::Inj(_, _, _, a) => bnums(*a),
        XExpr::MatchR(m, x, a, y, b) => (((bnums(*m) + seq![x]) + bnums(*a)) + seq![y]) + bnums(*b),
        XExpr::Map(xs, x, c) => (bnums(*xs) + seq![x]) + bnums(*c),
        XExpr::Filter(xs, x, c) => (bnums(*xs) + seq![x]) + bnums(*c),
        XExpr::Any(xs, x, c) => (bnums(*xs) + seq![x]) + bnums(*c),
        XExpr::All(xs, x, c) => (bnums(*xs) + seq![x]) + bnums(*c),
        XExpr::Find(xs, x, c) => (bnums(*xs) + seq![x]) + bnums(*c),
        XExpr::SortBy(xs, x, c) => (bnums(*xs) + seq![x]) + bnums(*c),
    }
}

/// 式の列の束縛の番号（i から先、割り当ての順）。
pub open spec fn bnums_seq(es: Seq<XExpr>, i: nat) -> Seq<nat>
    decreases es, es.len() - i,
{
    if i >= es.len() {
        Seq::empty()
    } else {
        bnums(es[i as int]) + bnums_seq(es, i + 1)
    }
}

/// c から始まる n 個の連続した番号。
pub open spec fn consec(c: nat, n: nat) -> Seq<nat> {
    Seq::new(n, |i: int| (c + i) as nat)
}

// ------------------------------------------------------------------ 連続性の補題

/// 連続した範囲の後ろに、続きの連続した範囲をつなぐと、一つの連続した範囲になる。
pub proof fn consec_join(c: nat, p: Seq<nat>, q: Seq<nat>)
    requires
        p =~= consec(c, p.len()),
        q =~= consec(c + p.len(), q.len()),
    ensures
        (p + q) =~= consec(c, p.len() + q.len()),
{
    let s = p + q;
    let t = consec(c, p.len() + q.len());
    assert(s.len() == t.len());
    assert forall|i: int| 0 <= i < s.len() implies s[i] == t[i] by {
        if i < p.len() {
            assert(s[i] == p[i]);
            assert(p[i] == consec(c, p.len())[i]);
        } else {
            assert(s[i] == q[i - p.len()]);
            assert(q[i - p.len()] == consec(c + p.len(), q.len())[i - p.len()]);
        }
    }
    assert(s =~= t);
}

/// 長さ 0 の連続した範囲は空の列。
pub proof fn consec_zero(c: nat)
    ensures
        consec(c, 0) =~= Seq::<nat>::empty(),
{
    assert(consec(c, 0).len() == 0);
}

/// 一つの番号は、長さ 1 の連続した範囲。
pub proof fn consec_one(c: nat)
    ensures
        seq![c] =~= consec(c, 1),
{
    assert(consec(c, 1)[0] == c);
}

/// 二つの番号 c, c+1 は、長さ 2 の連続した範囲。
pub proof fn consec_two(c: nat)
    ensures
        seq![c, c + 1] =~= consec(c, 2),
{
    assert(consec(c, 2)[0] == c);
    assert(consec(c, 2)[1] == c + 1);
}

/// 先頭に一つ足した列の番号は、元の列の番号を一つずらしたもの。
pub proof fn bnums_seq_shift(x: XExpr, xs: Seq<XExpr>, j: nat)
    ensures
        bnums_seq(seq![x] + xs, j + 1) =~= bnums_seq(xs, j),
    decreases xs.len() - j,
{
    reveal_with_fuel(bnums_seq, 2);
    let s = seq![x] + xs;
    assert(s.len() == 1 + xs.len());
    if j >= xs.len() {
    } else {
        assert(s[(j + 1) as int] == xs[j as int]);
        bnums_seq_shift(x, xs, j + 1);
    }
}

/// 先頭に一つ足した列の番号は、その式の番号と残りの列の番号の並び。
pub proof fn bnums_seq_cons(x: XExpr, xs: Seq<XExpr>)
    ensures
        bnums_seq(seq![x] + xs, 0) =~= bnums(x) + bnums_seq(xs, 0),
{
    reveal_with_fuel(bnums_seq, 2);
    let s = seq![x] + xs;
    assert(s.len() == 1 + xs.len());
    assert(s[0] == x);
    bnums_seq_shift(x, xs, 0);
}

/// 文字の列の式には、束縛の番号がない。
pub proof fn bnums_seq_chars(s: Seq<XExpr>, i: nat)
    requires
        forall|k: int| 0 <= k < s.len() ==> s[k] is Char,
    ensures
        bnums_seq(s, i) =~= Seq::empty(),
    decreases s.len() - i,
{
    reveal_with_fuel(bnums_seq, 2);
    reveal_with_fuel(bnums, 2);
    if i < s.len() {
        assert(s[i as int] is Char);
        bnums_seq_chars(s, i + 1);
    }
}

/// hof の語によらず、式の束縛の番号は、列・束縛・本体の順。
pub proof fn hof_x_bnums(h: Hf, xs: XExpr, x: nat, body: XExpr)
    ensures
        bnums(hof_x(h, xs, x, body)) =~= (bnums(xs) + seq![x]) + bnums(body),
{
    reveal_with_fuel(bnums, 2);
    match h {
        Hf::Map => {},
        Hf::Filter => {},
        Hf::Any => {},
        Hf::All => {},
        Hf::Find => {},
        Hf::SortBy => {},
    }
}

// ------------------------------------------------------------------ hx の性質（枝ごとの補題）

/// 一つの式の番号の並びは、子の並びをつなげたもの（子は続けて番号を取る）。ここでは子を二つ（対）として扱う。
pub proof fn pair_consec(c: nat, x: XExpr, c1: nat, y: XExpr, c2: nat)
    requires
        c1 == c + bnums(x).len(),
        bnums(x) =~= consec(c, bnums(x).len()),
        c2 == c1 + bnums(y).len(),
        bnums(y) =~= consec(c1, bnums(y).len()),
    ensures
        c2 == c + bnums(XExpr::Pair(Box::new(x), Box::new(y))).len(),
        bnums(XExpr::Pair(Box::new(x), Box::new(y))) =~= consec(c, bnums(XExpr::Pair(Box::new(x), Box::new(y))).len()),
{
    reveal_with_fuel(bnums, 2);
    consec_join(c, bnums(x), bnums(y));
}

/// 条件式の後に二つの枝。
pub proof fn if_consec(c: nat, x: XExpr, c1: nat, y: XExpr, c2: nat, z: XExpr, c3: nat)
    requires
        c1 == c + bnums(x).len(),
        bnums(x) =~= consec(c, bnums(x).len()),
        c2 == c1 + bnums(y).len(),
        bnums(y) =~= consec(c1, bnums(y).len()),
        c3 == c2 + bnums(z).len(),
        bnums(z) =~= consec(c2, bnums(z).len()),
    ensures
        c3 == c + bnums(XExpr::If(Box::new(x), Box::new(y), Box::new(z))).len(),
        bnums(XExpr::If(Box::new(x), Box::new(y), Box::new(z))) =~= consec(c, bnums(XExpr::If(Box::new(x), Box::new(y), Box::new(z))).len()),
{
    reveal_with_fuel(bnums, 2);
    consec_join(c, bnums(x), bnums(y));
    consec_join(c, bnums(x) + bnums(y), bnums(z));
}

/// let の束縛は、式 a の後、本体 b の前の番号 c1。
pub proof fn let_consec(c: nat, a: XExpr, c1: nat, b: XExpr, c2: nat)
    requires
        c1 == c + bnums(a).len(),
        bnums(a) =~= consec(c, bnums(a).len()),
        c2 == c1 + 1 + bnums(b).len(),
        bnums(b) =~= consec(c1 + 1, bnums(b).len()),
    ensures
        c2 == c + bnums(XExpr::Let(c1, Box::new(a), Box::new(b))).len(),
        bnums(XExpr::Let(c1, Box::new(a), Box::new(b))) =~= consec(c, bnums(XExpr::Let(c1, Box::new(a), Box::new(b))).len()),
{
    reveal_with_fuel(bnums, 2);
    consec_one(c1);
    consec_join(c, bnums(a), seq![c1]);
    consec_join(c, bnums(a) + seq![c1], bnums(b));
}

/// fold：列 l、初期値 i の後に、acc（c2）と item（c2 + 1）、本体 b は c2 + 2 から。
pub proof fn fold_consec(c: nat, l: XExpr, c1: nat, i: XExpr, c2: nat, b: XExpr, c3: nat)
    requires
        c1 == c + bnums(l).len(),
        bnums(l) =~= consec(c, bnums(l).len()),
        c2 == c1 + bnums(i).len(),
        bnums(i) =~= consec(c1, bnums(i).len()),
        c3 == c2 + 2 + bnums(b).len(),
        bnums(b) =~= consec(c2 + 2, bnums(b).len()),
    ensures
        c3 == c + bnums(XExpr::Fold(Box::new(l), Box::new(i), c2, c2 + 1, Box::new(b))).len(),
        bnums(XExpr::Fold(Box::new(l), Box::new(i), c2, c2 + 1, Box::new(b))) =~= consec(c, bnums(XExpr::Fold(Box::new(l), Box::new(i), c2, c2 + 1, Box::new(b))).len()),
{
    reveal_with_fuel(bnums, 2);
    consec_join(c, bnums(l), bnums(i));
    consec_two(c2);
    consec_join(c, bnums(l) + bnums(i), seq![c2, c2 + 1]);
    consec_join(c, (bnums(l) + bnums(i)) + seq![c2, c2 + 1], bnums(b));
}

/// match_option：m、none の枝 n の後に、some の束縛 c2、本体 b は c2 + 1 から。
pub proof fn match_consec(c: nat, m: XExpr, c1: nat, n: XExpr, c2: nat, b: XExpr, c3: nat)
    requires
        c1 == c + bnums(m).len(),
        bnums(m) =~= consec(c, bnums(m).len()),
        c2 == c1 + bnums(n).len(),
        bnums(n) =~= consec(c1, bnums(n).len()),
        c3 == c2 + 1 + bnums(b).len(),
        bnums(b) =~= consec(c2 + 1, bnums(b).len()),
    ensures
        c3 == c + bnums(XExpr::Match(Box::new(m), Box::new(n), c2, Box::new(b))).len(),
        bnums(XExpr::Match(Box::new(m), Box::new(n), c2, Box::new(b))) =~= consec(c, bnums(XExpr::Match(Box::new(m), Box::new(n), c2, Box::new(b))).len()),
{
    reveal_with_fuel(bnums, 2);
    consec_one(c2);
    consec_join(c, bnums(m), bnums(n));
    consec_join(c, bnums(m) + bnums(n), seq![c2]);
    consec_join(c, (bnums(m) + bnums(n)) + seq![c2], bnums(b));
}

/// match_result：m の後に、ok の束縛 c1、その本体 a、err の束縛 c2、その本体 b。
pub proof fn matchr_consec(c: nat, m: XExpr, c1: nat, a: XExpr, c2: nat, b: XExpr, c3: nat)
    requires
        c1 == c + bnums(m).len(),
        bnums(m) =~= consec(c, bnums(m).len()),
        c2 == c1 + 1 + bnums(a).len(),
        bnums(a) =~= consec(c1 + 1, bnums(a).len()),
        c3 == c2 + 1 + bnums(b).len(),
        bnums(b) =~= consec(c2 + 1, bnums(b).len()),
    ensures
        c3 == c + bnums(XExpr::MatchR(Box::new(m), c1, Box::new(a), c2, Box::new(b))).len(),
        bnums(XExpr::MatchR(Box::new(m), c1, Box::new(a), c2, Box::new(b))) =~= consec(c, bnums(XExpr::MatchR(Box::new(m), c1, Box::new(a), c2, Box::new(b))).len()),
{
    reveal_with_fuel(bnums, 2);
    consec_one(c1);
    consec_one(c2);
    consec_join(c, bnums(m), seq![c1]);
    consec_join(c, bnums(m) + seq![c1], bnums(a));
    consec_join(c, (bnums(m) + seq![c1]) + bnums(a), seq![c2]);
    consec_join(c, ((bnums(m) + seq![c1]) + bnums(a)) + seq![c2], bnums(b));
}

/// hof：列 xs の後に、束縛の番号 c1、本体 body は c1 + 1 から。
pub proof fn hof_consec(c: nat, h: Hf, xs: XExpr, c1: nat, body: XExpr, c2: nat)
    requires
        c1 == c + bnums(xs).len(),
        bnums(xs) =~= consec(c, bnums(xs).len()),
        c2 == c1 + 1 + bnums(body).len(),
        bnums(body) =~= consec(c1 + 1, bnums(body).len()),
    ensures
        c2 == c + bnums(hof_x(h, xs, c1, body)).len(),
        bnums(hof_x(h, xs, c1, body)) =~= consec(c, bnums(hof_x(h, xs, c1, body)).len()),
{
    hof_x_bnums(h, xs, c1, body);
    consec_one(c1);
    consec_join(c, bnums(xs), seq![c1]);
    consec_join(c, bnums(xs) + seq![c1], bnums(body));
}

// ------------------------------------------------------------------ hx の性質

/// 成功した解決の束縛の番号は、c から連続する。次の計数器は c に束縛の数を足したもの。
/// よって、一つの解決の中の束縛の番号は相異なる。
pub proof fn hx_consec(fs: Seq<Seq<char>>, c: nat, sc: Seq<(Seq<char>, nat)>, e: Sx)
    ensures
        match hx(fs, c, sc, e) {
            Some((xe, c2)) => c2 == c + bnums(xe).len() && bnums(xe) =~= consec(c, bnums(xe).len()),
            None => true,
        },
    decreases e, 0nat,
{
    reveal_with_fuel(hx, 2);
    reveal_with_fuel(bnums, 2);
    consec_zero(c);
    match e {
        Sx::Int(_) => {},
        Sx::Chr(_) => {},
        Sx::Str(w) => {
            let s = str_xs(w);
            assert forall|k: int| 0 <= k < s.len() implies s[k] is Char by {}
            bnums_seq_chars(s, 0);
        },
        Sx::Bool(_) => {},
        Sx::Unit => {},
        Sx::Var(_) => {},
        Sx::None(_) => {},
        Sx::List(_, es) => {
            hxs_consec(fs, c, sc, es, 0);
        },
        Sx::Builtin(_, es) => {
            hxs_consec(fs, c, sc, es, 0);
        },
        Sx::Call(_, es) => {
            hxs_consec(fs, c, sc, es, 0);
        },
        Sx::Some(a) => {
            hx_consec(fs, c, sc, *a);
        },
        Sx::Inj(_, _, _, a) => {
            hx_consec(fs, c, sc, *a);
        },
        Sx::Pair(a, b) => {
            hx_consec(fs, c, sc, *a);
            match hx(fs, c, sc, *a) {
                Some((x, c1)) => {
                    hx_consec(fs, c1, sc, *b);
                    match hx(fs, c1, sc, *b) {
                        Some((y, c2)) => {
                            pair_consec(c, x, c1, y, c2);
                        },
                        None => {},
                    }
                },
                None => {},
            }
        },
        Sx::If(cnd, a, b) => {
            hx_consec(fs, c, sc, *cnd);
            match hx(fs, c, sc, *cnd) {
                Some((x, c1)) => {
                    hx_consec(fs, c1, sc, *a);
                    match hx(fs, c1, sc, *a) {
                        Some((y, c2)) => {
                            hx_consec(fs, c2, sc, *b);
                            match hx(fs, c2, sc, *b) {
                                Some((z, c3)) => {
                                    if_consec(c, x, c1, y, c2, z, c3);
                                },
                                None => {},
                            }
                        },
                        None => {},
                    }
                },
                None => {},
            }
        },
        Sx::Let(x, a, b) => match hlook(sc, x, 0) {
            Some(_) => {},
            None => {
                hx_consec(fs, c, sc, *a);
                match hx(fs, c, sc, *a) {
                    Some((ra, c1)) => {
                        hx_consec(fs, c1 + 1, sc.push((x, c1)), *b);
                        match hx(fs, c1 + 1, sc.push((x, c1)), *b) {
                            Some((rb, c2)) => {
                                let_consec(c, ra, c1, rb, c2);
                            },
                            None => {},
                        }
                    },
                    None => {},
                }
            },
        },
        Sx::Fold(l, i, a, x, b) => match (a == x, hlook(sc, a, 0), hlook(sc, x, 0)) {
            (false, None, None) => {
                hx_consec(fs, c, sc, *l);
                match hx(fs, c, sc, *l) {
                    Some((rl, c1)) => {
                        hx_consec(fs, c1, sc, *i);
                        match hx(fs, c1, sc, *i) {
                            Some((ri, c2)) => {
                                hx_consec(fs, c2 + 2, sc.push((a, c2)).push((x, c2 + 1)), *b);
                                match hx(fs, c2 + 2, sc.push((a, c2)).push((x, c2 + 1)), *b) {
                                    Some((rb, c3)) => {
                                        fold_consec(c, rl, c1, ri, c2, rb, c3);
                                    },
                                    None => {},
                                }
                            },
                            None => {},
                        }
                    },
                    None => {},
                }
            },
            _ => {},
        },
        Sx::Match(m, n, x, b) => match hlook(sc, x, 0) {
            Some(_) => {},
            None => {
                hx_consec(fs, c, sc, *m);
                match hx(fs, c, sc, *m) {
                    Some((rm, c1)) => {
                        hx_consec(fs, c1, sc, *n);
                        match hx(fs, c1, sc, *n) {
                            Some((rn, c2)) => {
                                hx_consec(fs, c2 + 1, sc.push((x, c2)), *b);
                                match hx(fs, c2 + 1, sc.push((x, c2)), *b) {
                                    Some((rb, c3)) => {
                                        match_consec(c, rm, c1, rn, c2, rb, c3);
                                    },
                                    None => {},
                                }
                            },
                            None => {},
                        }
                    },
                    None => {},
                }
            },
        },
        Sx::MatchR(m, x, a, y, b) => match (hlook(sc, x, 0), hlook(sc, y, 0)) {
            (None, None) => {
                hx_consec(fs, c, sc, *m);
                match hx(fs, c, sc, *m) {
                    Some((rm, c1)) => {
                        hx_consec(fs, c1 + 1, sc.push((x, c1)), *a);
                        match hx(fs, c1 + 1, sc.push((x, c1)), *a) {
                            Some((ra, c2)) => {
                                hx_consec(fs, c2 + 1, sc.push((y, c2)), *b);
                                match hx(fs, c2 + 1, sc.push((y, c2)), *b) {
                                    Some((rb, c3)) => {
                                        matchr_consec(c, rm, c1, ra, c2, rb, c3);
                                    },
                                    None => {},
                                }
                            },
                            None => {},
                        }
                    },
                    None => {},
                }
            },
            _ => {},
        },
        Sx::Hof(h, l, x, b) => match hlook(sc, x, 0) {
            Some(_) => {},
            None => {
                hx_consec(fs, c, sc, *l);
                match hx(fs, c, sc, *l) {
                    Some((rl, c1)) => {
                        hx_consec(fs, c1 + 1, sc.push((x, c1)), *b);
                        match hx(fs, c1 + 1, sc.push((x, c1)), *b) {
                            Some((rb, c2)) => {
                                hof_consec(c, h, rl, c1, rb, c2);
                            },
                            None => {},
                        }
                    },
                    None => {},
                }
            },
        },
        Sx::Fld(..) => {},
        Sx::Rec(..) => {},
        Sx::SumMatch(..) => {},
        Sx::Loop(..) => {},
        Sx::DictNew(..) => {},
        Sx::DictOp(..) => {},
    }
}

/// 式の列の版。先頭の式の番号の後ろに、残りの列の番号が続く。
pub proof fn hxs_consec(fs: Seq<Seq<char>>, c: nat, sc: Seq<(Seq<char>, nat)>, es: Seq<Sx>, i: nat)
    ensures
        match hxs(fs, c, sc, es, i) {
            Some((xs, c2)) => c2 == c + bnums_seq(xs, 0).len() && bnums_seq(xs, 0) =~= consec(c, bnums_seq(xs, 0).len()),
            None => true,
        },
    decreases es, es.len() - i,
{
    reveal_with_fuel(hxs, 2);
    reveal_with_fuel(bnums_seq, 2);
    consec_zero(c);
    if i >= es.len() {
        assert(bnums_seq(Seq::<XExpr>::empty(), 0) =~= Seq::<nat>::empty());
    } else {
        hx_consec(fs, c, sc, es[i as int]);
        match hx(fs, c, sc, es[i as int]) {
            Some((x, c1)) => {
                hxs_consec(fs, c1, sc, es, i + 1);
                match hxs(fs, c1, sc, es, i + 1) {
                    Some((xs, c2)) => {
                        bnums_seq_cons(x, xs);
                        consec_join(c, bnums(x), bnums_seq(xs, 0));
                    },
                    None => {},
                }
            },
            None => {},
        }
    }
}

} // verus!
