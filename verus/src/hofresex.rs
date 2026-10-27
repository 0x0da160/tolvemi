//! hx の exec 版（段階 1b、DECISION-43）：hofres.rs の hx を、表面の exec の式 SExpr の上で計算する。
//!
//! `hx_e` は、束縛の並び（名前と番号の組の Vec）と計数器（usize）を受け取り、源の exec の式 `EX` と次の計数器を返す。
//! 結果の写し（view_ex）と次の計数器は、spec の `hx` の結果に等しい（`hx_e` の ensures）。束縛の番号は、hx と同じく
//! 割り当ての順に計数器から取る。番号を取る前に、次の計数器が usize に収まるかを比べて確かめ、収まらなければ None を返す
//! （spec の room に対応）。加算は比べた後に行うので、桁あふれは起きない。
//!
//! 扱わないこと：program 全体（関数、entry）の解決、表（checker の HofTypes）の出どころ、Rust の AST との変換、
//! 成功した解決の番号が usize に収まることの証明（room の十分性）。

use crate::bigint::*;
use crate::hofex::*;
use crate::hofres::*;
use crate::resolve::*;
use crate::spec::*;
use crate::surface::{clone_chars, eq_chars, vty, vx, vxs, SExpr, STy};
use crate::syntax::*;
use crate::xsem::*;
use vstd::prelude::*;

verus! {

/// 束縛の並びの写し（名前は字句の列、番号は nat）。
pub open spec fn vhs(sc: Seq<(Vec<char>, usize)>) -> Seq<(Seq<char>, nat)> {
    Seq::new(sc.len(), |i: int| (sc[i].0@, sc[i].1 as nat))
}

proof fn vhs_push(a: Seq<(Vec<char>, usize)>, p: (Vec<char>, usize))
    ensures
        vhs(a.push(p)) == vhs(a).push((p.0@, p.1 as nat)),
{
    assert(vhs(a.push(p)) =~= vhs(a).push((p.0@, p.1 as nat)));
}

/// hx の列の版の連接（hxs の先頭の結果を、残りの結果の前につなぐ）。
pub open spec fn catox(u: Seq<XExpr>, o: Option<(Seq<XExpr>, nat)>) -> Option<(Seq<XExpr>, nat)> {
    match o {
        Some((w, c2)) => Some((u + w, c2)),
        None => None,
    }
}

proof fn view_exs_push(a: Vec<EX>, b: Vec<EX>, e: EX)
    requires
        b@ == a@.push(e),
    ensures
        view_exs(b) == view_exs(a) + seq![view_ex(e)],
{
    assert(view_exs(b) =~= view_exs(a) + seq![view_ex(e)]);
}

/// 名前 x の番号（hlook の exec 版）。
fn hlook_e(sc: &Vec<(Vec<char>, usize)>, x: &Vec<char>) -> (r: Option<usize>)
    ensures
        match r {
            Some(k) => hlook(vhs(sc@), x@, 0) == Some(k as nat),
            None => hlook(vhs(sc@), x@, 0) is None,
        },
{
    let ghost v = vhs(sc@);
    let mut i: usize = 0;
    while i < sc.len()
        invariant
            v == vhs(sc@),
            i <= sc@.len(),
            hlook(v, x@, 0) == hlook(v, x@, i as nat),
        decreases sc@.len() - i,
    {
        proof {
            assert(v[i as int] == (sc@[i as int].0@, sc@[i as int].1 as nat));
        }
        if eq_chars(&sc[i].0, x) {
            proof {
                reveal_with_fuel(hlook, 2);
            }
            return Some(sc[i].1);
        }
        proof {
            reveal_with_fuel(hlook, 2);
        }
        i += 1;
    }
    None
}

/// 表面の型から、空の表による核の型へ（to_ty の空の表の版）。
pub fn to_ty0_e(t: &STy) -> (r: Option<Ty>)
    ensures
        match r {
            Some(u) => to_ty(vty(*t), Seq::empty(), false) == Some(u),
            None => to_ty(vty(*t), Seq::empty(), false) is None,
        },
{
    let tb: Vec<(Vec<char>, Option<Ty>, Vec<Vec<char>>, Option<Ty>)> = Vec::new();
    proof {
        assert(vtb(tb@) =~= Seq::<(Seq<char>, Option<Ty>, Seq<Seq<char>>, Option<Ty>)>::empty());
    }
    to_ty_e(t, &tb, false)
}

/// hof の語に応じた源の exec の式（hof_x の exec 版）。
fn hof_ex(h: Hf, xs: EX, x: usize, body: EX) -> (r: EX)
    ensures
        view_ex(r) == hof_x(h, view_ex(xs), x as nat, view_ex(body)),
{
    match h {
        Hf::Map => EX::Map(Box::new(xs), x, Box::new(body)),
        Hf::Filter => EX::Filter(Box::new(xs), x, Box::new(body)),
        Hf::Any => EX::Any(Box::new(xs), x, Box::new(body)),
        Hf::All => EX::All(Box::new(xs), x, Box::new(body)),
        Hf::Find => EX::Find(Box::new(xs), x, Box::new(body)),
        Hf::SortBy => EX::SortBy(Box::new(xs), x, Box::new(body)),
    }
}

/// 文字列の綴りの式の列（str_xs の exec 版）。
fn str_ex(w: &Vec<char>) -> (r: Vec<EX>)
    ensures
        view_exs(r) =~= str_xs(w@),
{
    let mut xs: Vec<EX> = Vec::new();
    let mut i: usize = 0;
    while i < w.len()
        invariant
            i <= w.len(),
            xs@.len() == i,
            forall|j: int| 0 <= j < i ==> view_ex(#[trigger] xs@[j]) == XExpr::Char(w@[j] as u32 as int),
        decreases w.len() - i,
    {
        xs.push(EX::Char(w[i] as u32));
        i += 1;
    }
    proof {
        assert(view_exs(xs) =~= str_xs(w@));
    }
    xs
}

/// 源の式の解決（hx の exec 版）。計数器 c は次の束縛の番号、sc は可視の束縛（名前と番号）、fs は関数名の列。
pub fn hx_e(fs: &Vec<Vec<char>>, c: usize, sc: &mut Vec<(Vec<char>, usize)>, e: &SExpr) -> (r: Option<(EX, usize)>)
    ensures
        final(sc)@ == old(sc)@,
        match r {
            Some((x, c2)) => hx(vnames(fs@), c as nat, vhs(old(sc)@), vx(*e)) == Some((view_ex(x), c2 as nat)),
            None => hx(vnames(fs@), c as nat, vhs(old(sc)@), vx(*e)) is None,
        },
    decreases e, 1nat,
{
    proof {
        reveal_with_fuel(hx, 2);
    }
    match e {
        SExpr::Int(n) => Some((EX::Int(n.copy()), c)),
        SExpr::Chr(ch) => Some((EX::Char(*ch as u32), c)),
        SExpr::Str(w) => Some((EX::List(Ty::Char, str_ex(w)), c)),
        SExpr::Bool(b) => Some((EX::Bool(*b), c)),
        SExpr::Unit => Some((EX::Unit, c)),
        SExpr::Var(x) => if x.len() == 0 {
            None
        } else {
            match hlook_e(sc, x) {
                Some(k) => Some((EX::Var(k), c)),
                None => None,
            }
        },
        SExpr::List(t, es) => match (to_ty0_e(t), hxs_e(fs, c, sc, es)) {
            (Some(u), Some((xs, c1))) => Some((EX::List(u, xs), c1)),
            _ => None,
        },
        SExpr::Some(a) => match hx_e(fs, c, sc, a) {
            Some((x, c1)) => Some((EX::Some(Box::new(x)), c1)),
            None => None,
        },
        SExpr::None(t) => match to_ty0_e(t) {
            Some(u) => Some((EX::None(u), c)),
            None => None,
        },
        SExpr::Pair(a, b) => match hx_e(fs, c, sc, a) {
            Some((x, c1)) => match hx_e(fs, c1, sc, b) {
                Some((y, c2)) => Some((EX::Pair(Box::new(x), Box::new(y)), c2)),
                None => None,
            },
            None => None,
        },
        SExpr::Builtin(b, es) => match hxs_e(fs, c, sc, es) {
            Some((xs, c1)) => Some((EX::Builtin(*b, xs), c1)),
            None => None,
        },
        SExpr::Call(g, es) => match idx_e(fs, g) {
            Some(gi) => match hxs_e(fs, c, sc, es) {
                Some((xs, c1)) => Some((EX::Call(gi, xs), c1)),
                None => None,
            },
            None => None,
        },
        SExpr::Let(..) => hx_let_e(fs, c, sc, e),
        SExpr::If(cnd, a, b) => match hx_e(fs, c, sc, cnd) {
            Some((x, c1)) => match hx_e(fs, c1, sc, a) {
                Some((y, c2)) => match hx_e(fs, c2, sc, b) {
                    Some((z, c3)) => Some((EX::If(Box::new(x), Box::new(y), Box::new(z)), c3)),
                    None => None,
                },
                None => None,
            },
            None => None,
        },
        SExpr::Fold(..) => hx_fold_e(fs, c, sc, e),
        SExpr::Match(..) => hx_match_e(fs, c, sc, e),
        SExpr::Inj(ok, t, u, a) => match (to_ty0_e(t), to_ty0_e(u), hx_e(fs, c, sc, a)) {
            (Some(t1), Some(u1), Some((x, c1))) => Some((EX::Inj(*ok, t1, u1, Box::new(x)), c1)),
            _ => None,
        },
        SExpr::MatchR(..) => hx_matchr_e(fs, c, sc, e),
        SExpr::Hof(..) => hx_hof_e(fs, c, sc, e),
        // この段階の範囲外：記録、直和型の match、loop、dict。
        SExpr::Fld(..) => None,
        SExpr::Rec(..) => None,
        SExpr::SumMatch(..) => None,
        SExpr::Loop(..) => None,
        SExpr::DictNew(..) => None,
        SExpr::DictOp(..) => None,
    }
}

fn hx_let_e(fs: &Vec<Vec<char>>, c: usize, sc: &mut Vec<(Vec<char>, usize)>, e: &SExpr) -> (r: Option<(EX, usize)>)
    requires
        e is Let,
    ensures
        final(sc)@ == old(sc)@,
        match r {
            Some((x, c2)) => hx(vnames(fs@), c as nat, vhs(old(sc)@), vx(*e)) == Some((view_ex(x), c2 as nat)),
            None => hx(vnames(fs@), c as nat, vhs(old(sc)@), vx(*e)) is None,
        },
    decreases e, 0nat,
{
    let ghost s0 = sc@;
    proof {
        reveal_with_fuel(hx, 2);
    }
    if let SExpr::Let(x, a, b) = e {
        if hlook_e(sc, x).is_some() {
            return None;
        }
        match hx_e(fs, c, sc, a) {
            Some((ra, c1)) => {
                if c1 >= usize::MAX {
                    return None;
                }
                sc.push((clone_chars(x), c1));
                let k = sc.len() - 1;
                proof {
                    vhs_push(s0, sc@[k as int]);
                }
                let rb = hx_e(fs, c1 + 1, sc, b);
                sc.pop();
                proof {
                    assert(sc@ =~= s0);
                }
                match rb {
                    Some((rb, c2)) => Some((EX::Let(c1, Box::new(ra), Box::new(rb)), c2)),
                    None => None,
                }
            },
            None => None,
        }
    } else {
        None
    }
}

fn hx_fold_e(fs: &Vec<Vec<char>>, c: usize, sc: &mut Vec<(Vec<char>, usize)>, e: &SExpr) -> (r: Option<(EX, usize)>)
    requires
        e is Fold,
    ensures
        final(sc)@ == old(sc)@,
        match r {
            Some((x, c2)) => hx(vnames(fs@), c as nat, vhs(old(sc)@), vx(*e)) == Some((view_ex(x), c2 as nat)),
            None => hx(vnames(fs@), c as nat, vhs(old(sc)@), vx(*e)) is None,
        },
    decreases e, 0nat,
{
    let ghost s0 = sc@;
    proof {
        reveal_with_fuel(hx, 2);
    }
    if let SExpr::Fold(l, i, a, x, b) = e {
        if eq_chars(a, x) || hlook_e(sc, a).is_some() || hlook_e(sc, x).is_some() {
            return None;
        }
        match hx_e(fs, c, sc, l) {
            Some((rl, c1)) => match hx_e(fs, c1, sc, i) {
                Some((ri, c2)) => {
                    if c2 > usize::MAX - 2 {
                        return None;
                    }
                    sc.push((clone_chars(a), c2));
                    let ghost s1 = sc@;
                    sc.push((clone_chars(x), c2 + 1));
                    let k1 = sc.len() - 1;
                    let k = k1 - 1;
                    proof {
                        vhs_push(s0, s1[k as int]);
                        vhs_push(s1, sc@[k1 as int]);
                    }
                    let rb = hx_e(fs, c2 + 2, sc, b);
                    sc.pop();
                    sc.pop();
                    proof {
                        assert(sc@ =~= s0);
                    }
                    match rb {
                        Some((rb, c3)) => Some((EX::Fold(Box::new(rl), Box::new(ri), c2, c2 + 1, Box::new(rb)), c3)),
                        None => None,
                    }
                },
                None => None,
            },
            None => None,
        }
    } else {
        None
    }
}

fn hx_match_e(fs: &Vec<Vec<char>>, c: usize, sc: &mut Vec<(Vec<char>, usize)>, e: &SExpr) -> (r: Option<(EX, usize)>)
    requires
        e is Match,
    ensures
        final(sc)@ == old(sc)@,
        match r {
            Some((x, c2)) => hx(vnames(fs@), c as nat, vhs(old(sc)@), vx(*e)) == Some((view_ex(x), c2 as nat)),
            None => hx(vnames(fs@), c as nat, vhs(old(sc)@), vx(*e)) is None,
        },
    decreases e, 0nat,
{
    let ghost s0 = sc@;
    proof {
        reveal_with_fuel(hx, 2);
    }
    if let SExpr::Match(m, n, x, b) = e {
        if hlook_e(sc, x).is_some() {
            return None;
        }
        match hx_e(fs, c, sc, m) {
            Some((rm, c1)) => match hx_e(fs, c1, sc, n) {
                Some((rn, c2)) => {
                    if c2 >= usize::MAX {
                        return None;
                    }
                    sc.push((clone_chars(x), c2));
                    let k = sc.len() - 1;
                    proof {
                        vhs_push(s0, sc@[k as int]);
                    }
                    let rb = hx_e(fs, c2 + 1, sc, b);
                    sc.pop();
                    proof {
                        assert(sc@ =~= s0);
                    }
                    match rb {
                        Some((rb, c3)) => Some((EX::Match(Box::new(rm), Box::new(rn), c2, Box::new(rb)), c3)),
                        None => None,
                    }
                },
                None => None,
            },
            None => None,
        }
    } else {
        None
    }
}

fn hx_matchr_e(fs: &Vec<Vec<char>>, c: usize, sc: &mut Vec<(Vec<char>, usize)>, e: &SExpr) -> (r: Option<(EX, usize)>)
    requires
        e is MatchR,
    ensures
        final(sc)@ == old(sc)@,
        match r {
            Some((x, c2)) => hx(vnames(fs@), c as nat, vhs(old(sc)@), vx(*e)) == Some((view_ex(x), c2 as nat)),
            None => hx(vnames(fs@), c as nat, vhs(old(sc)@), vx(*e)) is None,
        },
    decreases e, 0nat,
{
    let ghost s0 = sc@;
    proof {
        reveal_with_fuel(hx, 2);
    }
    if let SExpr::MatchR(m, x, a, y, b) = e {
        if hlook_e(sc, x).is_some() || hlook_e(sc, y).is_some() {
            return None;
        }
        match hx_e(fs, c, sc, m) {
            Some((rm, c1)) => {
                if c1 >= usize::MAX {
                    return None;
                }
                sc.push((clone_chars(x), c1));
                let k = sc.len() - 1;
                proof {
                    vhs_push(s0, sc@[k as int]);
                }
                let ra = hx_e(fs, c1 + 1, sc, a);
                sc.pop();
                proof {
                    assert(sc@ =~= s0);
                }
                match ra {
                    Some((ra, c2)) => {
                        if c2 >= usize::MAX {
                            return None;
                        }
                        sc.push((clone_chars(y), c2));
                        let k2 = sc.len() - 1;
                        proof {
                            vhs_push(s0, sc@[k2 as int]);
                        }
                        let rb = hx_e(fs, c2 + 1, sc, b);
                        sc.pop();
                        proof {
                            assert(sc@ =~= s0);
                        }
                        match rb {
                            Some((rb, c3)) => Some((EX::MatchR(Box::new(rm), c1, Box::new(ra), c2, Box::new(rb)), c3)),
                            None => None,
                        }
                    },
                    None => None,
                }
            },
            None => None,
        }
    } else {
        None
    }
}

fn hx_hof_e(fs: &Vec<Vec<char>>, c: usize, sc: &mut Vec<(Vec<char>, usize)>, e: &SExpr) -> (r: Option<(EX, usize)>)
    requires
        e is Hof,
    ensures
        final(sc)@ == old(sc)@,
        match r {
            Some((x, c2)) => hx(vnames(fs@), c as nat, vhs(old(sc)@), vx(*e)) == Some((view_ex(x), c2 as nat)),
            None => hx(vnames(fs@), c as nat, vhs(old(sc)@), vx(*e)) is None,
        },
    decreases e, 0nat,
{
    let ghost s0 = sc@;
    proof {
        reveal_with_fuel(hx, 2);
    }
    if let SExpr::Hof(h, l, x, b) = e {
        if hlook_e(sc, x).is_some() {
            return None;
        }
        match hx_e(fs, c, sc, l) {
            Some((rl, c1)) => {
                if c1 >= usize::MAX {
                    return None;
                }
                sc.push((clone_chars(x), c1));
                let k = sc.len() - 1;
                proof {
                    vhs_push(s0, sc@[k as int]);
                }
                let rb = hx_e(fs, c1 + 1, sc, b);
                sc.pop();
                proof {
                    assert(sc@ =~= s0);
                }
                match rb {
                    Some((rb, c2)) => Some((hof_ex(*h, rl, c1, rb), c2)),
                    None => None,
                }
            },
            None => None,
        }
    } else {
        None
    }
}

/// 式の列の解決（hxs の exec 版）。計数器は左から順に進む。
pub fn hxs_e(fs: &Vec<Vec<char>>, c: usize, sc: &mut Vec<(Vec<char>, usize)>, es: &Vec<SExpr>) -> (r: Option<(Vec<EX>, usize)>)
    ensures
        final(sc)@ == old(sc)@,
        match r {
            Some((xs, c2)) => hxs(vnames(fs@), c as nat, vhs(old(sc)@), vxs(*es), 0) == Some((view_exs(xs), c2 as nat)),
            None => hxs(vnames(fs@), c as nat, vhs(old(sc)@), vxs(*es), 0) is None,
        },
    decreases es, 0nat,
{
    let ghost f = vnames(fs@);
    let ghost s0 = sc@;
    let ghost v = vxs(*es);
    let mut out: Vec<EX> = Vec::new();
    let mut i: usize = 0;
    let mut cur: usize = c;
    proof {
        reveal_with_fuel(hxs, 2);
        assert(view_exs(out) =~= Seq::<XExpr>::empty());
        if let Some((w, c2)) = hxs(f, c as nat, vhs(s0), v, 0) {
            assert(Seq::<XExpr>::empty() + w =~= w);
        }
    }
    while i < es.len()
        invariant
            f == vnames(fs@),
            sc@ == s0,
            s0 == old(sc)@,
            v == vxs(*es),
            i <= es@.len(),
            hxs(f, c as nat, vhs(s0), v, 0) == catox(view_exs(out), hxs(f, cur as nat, vhs(s0), v, i as nat)),
        decreases es@.len() - i,
    {
        proof {
            vstd::std_specs::vec::axiom_vec_index_decreases(*es, i as int);
            assert(v[i as int] == vx(es@[i as int]));
        }
        let ghost o0 = out;
        let ghost cur0 = cur;
        match hx_e(fs, cur, sc, &es[i]) {
            Some((x, c1)) => {
                let ghost xv = view_ex(x);
                out.push(x);
                proof {
                    view_exs_push(o0, out, x);
                    reveal_with_fuel(hxs, 2);
                    match hxs(f, c1 as nat, vhs(s0), v, (i + 1) as nat) {
                        Some((ws, c2)) => {
                            assert(hxs(f, cur0 as nat, vhs(s0), v, i as nat) == Some((seq![xv] + ws, c2)));
                            assert(view_exs(out) + ws =~= view_exs(o0) + (seq![xv] + ws));
                        },
                        None => {},
                    }
                }
                cur = c1;
                i += 1;
            },
            None => {
                proof {
                    reveal_with_fuel(hxs, 2);
                }
                return None;
            },
        }
    }
    proof {
        reveal_with_fuel(hxs, 2);
        assert(view_exs(out) + Seq::<XExpr>::empty() =~= view_exs(out));
    }
    Some((out, cur))
}

} // verus!
