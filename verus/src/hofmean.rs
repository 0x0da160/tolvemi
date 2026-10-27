//! hof を含むプログラムの、核の意味と源の意味の一致（段階 2、DECISION-43）。
//!
//! hofroute.rs の hof_compile が受理した核のプログラム p は、解決した関数の列 fs を表 tb で写したもの（hrw_funcs）で、
//! 整形式（wf）である。ここでは、p の意味が fs の源の意味（xeval）に等しいことを示す。書換えの仮定（homomorphic と
//! hof_shapes）は、写し rw_tb について hofrw.rs が示している。署名の消去（erase_sig）は、署名に Dict が無いことから
//! 恒等になる。
//!
//! 示すこと：入力の値が入口の引数の型を持つなら、源は行き詰まらず Done を返す（xeval）。どの燃料の核の結果も、
//! OutOfFuel でなければ源の結果に等しく、ある燃料では源の結果を返す。
//! 仮定：（一）入力の値が入口の引数の型を持つ（Rust が入力を読む。sh6_typed_same の仮定）、（二）署名に Dict が無い
//! （Rust の経路の範囲が確かめる。dict::has_dict は型も見る）、（三）燃料 fuel の源の結果が OutOfFuel でない。
//! 扱わないこと：名前の解決（hresolve）が源の文字列の意味を保つこと、核の意味と Rust の実行器の一致、入力の読み込み。

use crate::hofroute::*;
use crate::hofrw::*;
use crate::sh6_obligations::*;
use crate::sh6_safe::*;
use crate::simulation::*;
use crate::spec::*;
use crate::xsem::*;
use vstd::prelude::*;

verus! {

/// 型に Dict が無い（erase_ty は、この型では恒等になる）。
pub open spec fn nodict(t: Ty) -> bool
    decreases t,
{
    match t {
        Ty::List(a) => nodict(*a),
        Ty::Option(a) => nodict(*a),
        Ty::Pair(a, b) => nodict(*a) && nodict(*b),
        Ty::Result(a, b) => nodict(*a) && nodict(*b),
        Ty::Dict(_, _) => false,
        _ => true,
    }
}

/// 関数の署名（引数の型と結果の型）に Dict が無い。
pub open spec fn nodict_sig(f: XFunc) -> bool {
    &&& forall|k: int| 0 <= k < f.params.len() ==> nodict(#[trigger] f.params[k].1)
    &&& nodict(f.ret)
}

/// Dict の無い型は、erase_ty で変わらない。
pub proof fn erase_nodict(t: Ty)
    requires
        nodict(t),
    ensures
        erase_ty(t) == t,
    decreases t,
{
    match t {
        Ty::List(a) => erase_nodict(*a),
        Ty::Option(a) => erase_nodict(*a),
        Ty::Pair(a, b) => {
            erase_nodict(*a);
            erase_nodict(*b);
        },
        Ty::Result(a, b) => {
            erase_nodict(*a);
            erase_nodict(*b);
        },
        _ => {},
    }
}

/// 表で写した関数は、消去した署名を持つ（Dict が無い署名は、消去しても変わらない）。
pub proof fn erase_sig_of_hrw(f: XFunc, tb: Seq<(nat, Ty, Ty)>)
    requires
        nodict_sig(f),
    ensures
        erase_sig(f, hrw_func(f, tb)),
{
    assert forall|k: int| 0 <= k < f.params.len() implies #[trigger] hrw_func(f, tb).params[k].1 == erase_ty(
        f.params[k].1,
    ) by {
        erase_nodict(f.params[k].1);
    }
    erase_nodict(f.ret);
}

/// 核のプログラム p（解決した関数の列 fs を表 tb で写したもの）の意味は、源の意味（xeval）に等しい。
pub proof fn hof_route_meaning(fs: Seq<XFunc>, rank: Seq<nat>, rec: Seq<bool>, tb: Seq<(nat, Ty, Ty)>, p: Prog, v: Val, n: nat)
    requires
        forall|i: int| 0 <= i < fs.len() ==> nodict_sig(#[trigger] fs[i]),
        p.funcs == hrw_funcs(fs, tb),
        p.rank == rank,
        p.rec == rec,
        p.entry < fs.len(),
        wf(p),
        val_type(v, p.funcs[p.entry as int].params[0].1),
        !(xeval_entry(XProg { funcs: fs, rank, rec, entry: p.entry }, n, v) is OutOfFuel),
    ensures
        xeval_entry(XProg { funcs: fs, rank, rec, entry: p.entry }, n, v) is Done,
        exists|m: nat| #[trigger] eval_entry(p, m, v) == xeval_entry(XProg { funcs: fs, rank, rec, entry: p.entry }, n, v),
        forall|m: nat| !(#[trigger] eval_entry(p, m, v) is OutOfFuel) ==> eval_entry(p, m, v) == xeval_entry(
            XProg { funcs: fs, rank, rec, entry: p.entry },
            n,
            v,
        ),
{
    let xp = XProg { funcs: fs, rank, rec, entry: p.entry };
    let rw: spec_fn(XExpr) -> Expr = |e: XExpr| rw_tb(tb, e);
    assert forall|e: XExpr| #[trigger] rw(e) == rw_tb(tb, e) by {}
    tb_homomorphic(tb, rw);
    tb_hof_shapes(tb, rw);
    assert forall|i: int| 0 <= i < fs.len() implies erase_sig(#[trigger] xp.funcs[i], p.funcs[i]) by {
        assert(p.funcs[i] == hrw_func(fs[i], tb));
        erase_sig_of_hrw(fs[i], tb);
    }
    assert forall|i: int| 0 <= i < fs.len() implies #[trigger] p.funcs[i].body == rw(xp.funcs[i].body) by {
        assert(p.funcs[i] == hrw_func(fs[i], tb));
    }
    assert(sim_prog(xp, p, rw));
    sh6_typed_same(xp, p, rw, n, v);
}

} // verus!
