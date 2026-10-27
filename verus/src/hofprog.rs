//! 関数と entry の名前解決（hof を含むプログラムの版、段階 1b、DECISION-43）。
//!
//! resolve.rs の resolve_t の写しである。違いは二つ。関数の本体は hx（hofres.rs）で解決し、束縛の番号は
//! プログラム全体で一つの計数器から取る（関数の引数が先に番号を取り、本体の束縛が続く。関数の順に計数器を受け継ぐ）。
//! 番号が一つのプログラムの中で重ならないので、表を番号で引ける。型の宣言（記録、直和型）を含むプログラムは None
//! （この段階の範囲外。型の表は空として、基本の型だけを写す）。
//!
//! 示すこと：exec の hresolve_e は spec の hresolve と一致する（ensures）。
//! 扱わないこと：表（hof の要素の型と本体の型）、源の意味（xeval）との一致、経路への接続。

use crate::hofex::*;
use crate::hofres::*;
use crate::hofresex::*;
use crate::resolve::*;
use crate::spec::*;
use crate::surface::{clone_chars, vd, vds, vps, SDecl};
use crate::syntax::*;
use crate::xsem::*;
use vstd::prelude::*;

verus! {

// ------------------------------------------------------------------ spec

/// 引数の並び。k 番目の引数は番号 c + k を取る（引数は関数の先頭で、計数器から順に番号を取る）。
pub open spec fn hparams(ps: Seq<(Seq<char>, SType)>, c: nat) -> Seq<(Seq<char>, nat)> {
    Seq::new(ps.len(), |k: int| (ps[k].0, c + k as nat))
}

/// 引数の型の並び（核の型。型の表は空で、基本の型だけを写す）。
pub open spec fn hrparams(ps: Seq<(Seq<char>, SType)>, c: nat) -> Seq<(nat, Ty)> {
    Seq::new(ps.len(), |k: int| (c + k as nat, ty_or_unit(ps[k].1, Seq::empty(), false)))
}

/// 関数の宣言の番号づけ。計数器 c から引数の番号を取り、本体を hx で解決する。結果は（源の関数、次の計数器）。
pub open spec fn hfunc(fs: Seq<Seq<char>>, c: nat, d: Sd) -> Option<(XFunc, nat)> {
    match d {
        Sd::Fn(_, ps, r, b) => if !room(c, ps.len()) || !distinct(pnames(ps)) || !params_ok(ps, Seq::empty(), false)
            || to_ty(r, Seq::empty(), false) is None {
            None
        } else {
            match hx(fs, c + ps.len(), hparams(ps, c), b) {
                Some((body, c2)) => Some((XFunc { params: hrparams(ps, c), ret: ty_or_unit(r, Seq::empty(), false), body }, c2)),
                None => None,
            }
        },
        Sd::Entry(_) => None,
        Sd::RecTy(_, _, _) => None,
        Sd::Sum(_, _) => None,
    }
}

/// ds[i..] の各関数の番号づけ。計数器は左から順に進む。
pub open spec fn hfuncs(fs: Seq<Seq<char>>, ds: Seq<Sd>, i: nat, c: nat) -> Option<(Seq<XFunc>, nat)>
    decreases ds.len() - i,
{
    if i >= ds.len() {
        Some((Seq::empty(), c))
    } else {
        match hfunc(fs, c, ds[i as int]) {
            Some((f, c1)) => match hfuncs(fs, ds, i + 1, c1) {
                Some((fs2, c2)) => Some((seq![f] + fs2, c2)),
                None => None,
            },
            None => None,
        }
    }
}

/// 宣言は関数か entry だけ（型の宣言を含まない）。
pub open spec fn hdecls_ok(p: Seq<Sd>) -> bool {
    forall|i: int| 0 <= i < p.len() ==> (p[i] is Fn || p[i] is Entry)
}

/// プログラムの名前解決。結果は（関数の列、entry の添字、使い終わった計数器）。
pub open spec fn hresolve(p: Seq<Sd>) -> Option<(Seq<XFunc>, nat, nat)> {
    let ds = fns_upto(p, p.len());
    let fs = names_of(ds);
    let es = ents_upto(p, p.len());
    if !hdecls_ok(p) || !distinct(fs) || es.len() != 1 {
        None
    } else {
        match (hfuncs(fs, ds, 0, 0), idx(fs, es[0], 0)) {
            (Some((funcs, c)), Some(g)) => if g < funcs.len() && funcs[g as int].params.len() == 1 {
                Some((funcs, g, c))
            } else {
                None
            },
            _ => None,
        }
    }
}

// ------------------------------------------------------------------ exec

/// 関数の exec の版（XFunc の写し）：引数の（番号、型）の列、結果の型、本体の源の exec の式。
pub struct EXFunc {
    pub params: Vec<(usize, Ty)>,
    pub ret: Ty,
    pub body: EX,
}

pub open spec fn view_xfunc(f: EXFunc) -> XFunc {
    XFunc {
        params: Seq::new(f.params@.len(), |k: int| (f.params@[k].0 as nat, f.params@[k].1)),
        ret: f.ret,
        body: view_ex(f.body),
    }
}

pub open spec fn view_xfuncs(fs: Seq<EXFunc>) -> Seq<XFunc> {
    Seq::new(fs.len(), |i: int| view_xfunc(fs[i]))
}

/// 関数の列の連接（hfuncs の結果の先頭を、残りの結果の前につなぐ）。
pub open spec fn cat_xfuncs(u: Seq<XFunc>, o: Option<(Seq<XFunc>, nat)>) -> Option<(Seq<XFunc>, nat)> {
    match o {
        Some((w, c2)) => Some((u + w, c2)),
        None => None,
    }
}

/// 関数の宣言の番号づけ（hfunc の exec 版）。
fn hfunc_e(fs: &Vec<Vec<char>>, c: usize, d: &SDecl) -> (r: Option<(EXFunc, usize)>)
    ensures
        match r {
            Some((f, c2)) => hfunc(vnames(fs@), c as nat, vd(*d)) == Some((view_xfunc(f), c2 as nat)),
            None => hfunc(vnames(fs@), c as nat, vd(*d)) is None,
        },
{
    match d {
        SDecl::Fn(_, ps, ret, body) => {
            let n = ps.len();
            if c > usize::MAX - n {
                return None;
            }
            let ghost pv = vps(ps@);
            let rt = match to_ty0_e(ret) {
                Some(u) => u,
                None => return None,
            };
            let mut names: Vec<Vec<char>> = Vec::new();
            let mut sc: Vec<(Vec<char>, usize)> = Vec::new();
            let mut params: Vec<(usize, Ty)> = Vec::new();
            let mut k: usize = 0;
            let mut ok: bool = true;
            while k < n && ok
                invariant
                    pv == vps(ps@),
                    n == ps@.len(),
                    k <= n,
                    c as int + n as int <= usize::MAX as int,
                    names@.len() == k,
                    forall|j: int| 0 <= j < k ==> names@[j]@ == pv[j].0,
                    sc@.len() == k,
                    forall|j: int| 0 <= j < k ==> (sc@[j].0@, sc@[j].1 as nat) == hparams(pv, c as nat)[j],
                    params@.len() == k,
                    forall|j: int| 0 <= j < k ==> (params@[j].0 as nat, params@[j].1) == hrparams(pv, c as nat)[j],
                    forall|j: int| 0 <= j < k ==> to_ty(#[trigger] pv[j].1, Seq::empty(), false) is Some,
                    !ok ==> k < n && to_ty(pv[k as int].1, Seq::empty(), false) is None,
                decreases if ok { n - k } else { 0 },
            {
                let (x, t) = &ps[k];
                match to_ty0_e(t) {
                    Some(u) => {
                        names.push(clone_chars(x));
                        sc.push((clone_chars(x), c + k));
                        params.push((c + k, u));
                        k += 1;
                    },
                    None => {
                        ok = false;
                    },
                }
            }
            if !ok {
                proof {
                    assert(to_ty(vps(ps@)[k as int].1, Seq::empty(), false) is None);
                    assert(!params_ok(vps(ps@), Seq::empty(), false));
                    assert(hfunc(vnames(fs@), c as nat, vd(*d)) is None);
                }
                return None;
            }
            if !distinct_e(&names) {
                proof {
                    assert(vnames(names@) =~= pnames(pv));
                    assert(!distinct(pnames(pv)));
                    assert(hfunc(vnames(fs@), c as nat, vd(*d)) is None);
                }
                return None;
            }
            proof {
                assert(vnames(names@) =~= pnames(pv));
                assert(vhs(sc@) =~= hparams(pv, c as nat));
                assert(params_ok(pv, Seq::empty(), false));
                assert(Seq::new(params@.len(), |j: int| (params@[j].0 as nat, params@[j].1)) =~= hrparams(pv, c as nat));
            }
            match hx_e(fs, c + n, &mut sc, body) {
                Some((x, c2)) => Some((EXFunc { params, ret: rt, body: x }, c2)),
                None => None,
            }
        },
        SDecl::Entry(_) => None,
        SDecl::RecTy(_, _, _) => None,
        SDecl::Sum(_, _) => None,
    }
}

/// プログラムの名前解決（hresolve の exec 版）。関数の列、entry の添字、使い終わった計数器を返す。
pub fn hresolve_e(p: &Vec<SDecl>) -> (r: Option<(Vec<EXFunc>, usize, usize)>)
    ensures
        match r {
            Some((fs, g, c)) => hresolve(vds(p@)) == Some((view_xfuncs(fs@), g as nat, c as nat)) && g < fs@.len(),
            None => hresolve(vds(p@)) is None,
        },
{
    let ghost v = vds(p@);
    let mut names: Vec<Vec<char>> = Vec::new();
    let mut fidx: Vec<usize> = Vec::new();
    let mut ents: Vec<usize> = Vec::new();
    let mut i: usize = 0;
    proof {
        assert(vnames(names@) =~= names_of(fns_upto(v, 0)));
    }
    while i < p.len()
        invariant
            v == vds(p@),
            i <= p@.len(),
            vnames(names@) == names_of(fns_upto(v, i as nat)),
            fns_upto(v, i as nat) == Seq::new(fidx@.len(), |m: int| v[fidx@[m] as int]),
            forall|k: int| 0 <= k < fidx@.len() ==> #[trigger] fidx@[k] < p@.len(),
            ents_upto(v, i as nat) == Seq::new(ents@.len(), |m: int| v[ents@[m] as int]->Entry_0),
            forall|k: int| 0 <= k < ents@.len() ==> #[trigger] ents@[k] < p@.len() && v[ents@[k] as int] is Entry,
            forall|j: int| 0 <= j < i ==> (v[j] is Fn || v[j] is Entry),
        decreases p@.len() - i,
    {
        proof {
            assert(v[i as int] == vd(p@[i as int]));
        }
        let ghost n0 = names@;
        let ghost f0 = fns_upto(v, i as nat);
        let ghost e0 = ents_upto(v, i as nat);
        match &p[i] {
            SDecl::Fn(f, _, _, _) => {
                names.push(clone_chars(f));
                fidx.push(i);
                proof {
                    assert(v[i as int] is Fn);
                    assert(fns_upto(v, (i + 1) as nat) == f0.push(v[i as int]));
                    assert(ents_upto(v, (i + 1) as nat) == e0);
                    vnames_push(n0, names@[n0.len() as int]);
                    assert(names_of(f0.push(v[i as int])) =~= names_of(f0).push(fname(v[i as int])));
                    assert(f0.push(v[i as int]) =~= Seq::new(fidx@.len(), |m: int| v[fidx@[m] as int]));
                }
            },
            SDecl::Entry(_) => {
                ents.push(i);
                proof {
                    assert(v[i as int] is Entry);
                    assert(fns_upto(v, (i + 1) as nat) == f0);
                    assert(ents_upto(v, (i + 1) as nat) == e0.push(v[i as int]->Entry_0));
                    assert(e0.push(v[i as int]->Entry_0) =~= Seq::new(ents@.len(), |m: int| v[ents@[m] as int]->Entry_0));
                }
            },
            // 型の宣言（記録・直和型）は、この段階の範囲外（hdecls_ok が偽になる）。
            SDecl::RecTy(_, _, _) | SDecl::Sum(_, _) => {
                proof {
                    assert(!(v[i as int] is Fn || v[i as int] is Entry));
                    assert(!hdecls_ok(v));
                    assert(hresolve(v) is None);
                }
                return None;
            },
        }
        i += 1;
    }
    let ghost ds = fns_upto(v, v.len());
    let ghost fsv = names_of(ds);
    if !distinct_e(&names) || ents.len() != 1 {
        return None;
    }
    let mut out: Vec<EXFunc> = Vec::new();
    let mut cur: usize = 0;
    let mut k: usize = 0;
    proof {
        reveal_with_fuel(hfuncs, 2);
        assert(view_xfuncs(out@) =~= Seq::<XFunc>::empty());
        if let Some((w, c2)) = hfuncs(fsv, ds, 0, 0) {
            assert(Seq::<XFunc>::empty() + w =~= w);
        }
    }
    while k < fidx.len()
        invariant
            v == vds(p@),
            ds == fns_upto(v, v.len()),
            fsv == names_of(ds),
            vnames(names@) == fsv,
            ds == Seq::new(fidx@.len(), |m: int| v[fidx@[m] as int]),
            forall|m: int| 0 <= m < fidx@.len() ==> #[trigger] fidx@[m] < p@.len(),
            k <= fidx@.len(),
            out@.len() == k,
            cur as nat <= usize::MAX as nat,
            hfuncs(fsv, ds, 0, 0) == cat_xfuncs(view_xfuncs(out@), hfuncs(fsv, ds, k as nat, cur as nat)),
        decreases fidx@.len() - k,
    {
        let j = fidx[k];
        proof {
            assert(ds[k as int] == v[j as int]);
            assert(v[j as int] == vd(p@[j as int]));
        }
        let ghost o0 = out@;
        match hfunc_e(&names, cur, &p[j]) {
            Some((f, c1)) => {
                let ghost xv = view_xfunc(f);
                out.push(f);
                proof {
                    reveal_with_fuel(hfuncs, 2);
                    assert(view_xfuncs(out@) =~= view_xfuncs(o0).push(xv));
                    match hfuncs(fsv, ds, (k + 1) as nat, c1 as nat) {
                        Some((ws, c2)) => {
                            assert(hfuncs(fsv, ds, k as nat, cur as nat) == Some((seq![xv] + ws, c2)));
                            assert(view_xfuncs(out@) + ws =~= view_xfuncs(o0) + (seq![xv] + ws));
                        },
                        None => {},
                    }
                }
                cur = c1;
                k += 1;
            },
            None => {
                proof {
                    reveal_with_fuel(hfuncs, 2);
                }
                return None;
            },
        }
    }
    let e = ents[0];
    proof {
        assert(ents_upto(v, v.len())[0] == v[e as int]->Entry_0);
        assert(v[e as int] == vd(p@[e as int]));
    }
    let g = match &p[e] {
        SDecl::Entry(x) => match idx_e(&names, x) {
            Some(g) => g,
            None => return None,
        },
        _ => return None,
    };
    proof {
        idx_props(fsv, ents_upto(v, v.len())[0], 0);
        reveal_with_fuel(hfuncs, 2);
        assert(hfuncs(fsv, ds, k as nat, cur as nat) == Some((Seq::<XFunc>::empty(), cur as nat)));
        assert(view_xfuncs(out@) + Seq::<XFunc>::empty() =~= view_xfuncs(out@));
    }
    if g >= out.len() || out[g].params.len() != 1 {
        return None;
    }
    Some((out, g, cur))
}

} // verus!
