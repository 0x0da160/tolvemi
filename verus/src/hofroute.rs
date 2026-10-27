//! hof を含むプログラムの、検証済みの経路（段階 2、DECISION-43）。
//!
//! 源の文字列を検証済みの構文器で読み、hof を含む名前解決（hofprog.rs の hresolve_e）で関数の列にし、表 tb で
//! 各本体を書き換え（hofex.rs の rw_ex）、核のプログラムを検証済みの型検査器に通す。二段に分ける。hof_resolve_source
//! が返す関数の列（源の exec の式）から、Rust の接着が表を作る。その後に hof_compile が書き換えと型検査をする。
//!
//! 示すこと：hof_resolve_source の結果は、源の文字列の名前解決（hresolve）に等しい。hof_compile が受理したなら、
//! 核の関数の列は、解決した関数の列を表 tb で写したもの（hrw_funcs）に等しく、整形式である。
//! 扱わないこと：表の中身（HofTypes の型）と、表の束縛番号が解決の番号と一致すること（Rust の接着が検査する）、
//! 源の意味（xeval）と核の意味の一致（段階 2 の未証明）。

use crate::check::*;
use crate::hofex::*;
use crate::hofprog::*;
use crate::hofrw::*;
use crate::ir::*;
use crate::spec::*;
use crate::syntax::*;
use crate::surface::parse_e;
use crate::xsem::*;
use vstd::prelude::*;

verus! {

// ------------------------------------------------------------------ spec

/// 解決した関数の一つを、表 tb で核の関数に写す。引数と結果の型は変えない。
pub open spec fn hrw_func(f: XFunc, tb: Seq<(nat, Ty, Ty)>) -> Func {
    Func { params: f.params, ret: f.ret, body: rw_tb(tb, f.body) }
}

pub open spec fn hrw_funcs(fs: Seq<XFunc>, tb: Seq<(nat, Ty, Ty)>) -> Seq<Func> {
    Seq::new(fs.len(), |i: int| hrw_func(fs[i], tb))
}

// ------------------------------------------------------------------ exec

/// 核の経路の結果（書換えの桁あふれ、型検査の拒否、受理）。
pub enum HofCompiled {
    /// 書換えが名前の加算の桁あふれで拒否した（呼出し側は資源の上限による拒否として扱う）
    RewriteRejected,
    /// 検証済み型検査器がプログラムを受理しなかった
    NotWellFormed,
    Accepted(EProg),
}

/// 源の文字列の名前解決（段階 1b の hresolve）。結果は（関数の列、entry の添字、使い終わった計数器）。
pub fn hof_resolve_source(src: &Vec<char>, d: usize, td: usize) -> (r: Option<(Vec<EXFunc>, usize, usize)>)
    requires
        src@.len() < 0x1000_0000,
    ensures
        match r {
            Some((fs, g, c)) => parse(src@, d as nat, td as nat) is Some
                && hresolve(parse(src@, d as nat, td as nat)->Some_0) == Some((view_xfuncs(fs@), g as nat, c as nat))
                && g < fs@.len(),
            None => parse(src@, d as nat, td as nat) is None
                || hresolve(parse(src@, d as nat, td as nat)->Some_0) is None,
        },
{
    match parse_e(src, d, td) {
        Some(sp) => hresolve_e(&sp),
        None => None,
    }
}

/// 引数の並び（型は ty_clone で写す）。
fn params_clone(ps: &Vec<(usize, Ty)>) -> (r: Vec<(usize, Ty)>)
    ensures
        r@.len() == ps@.len(),
        forall|i: int| 0 <= i < ps@.len() ==> r@[i] == ps@[i],
{
    let mut r: Vec<(usize, Ty)> = Vec::new();
    let mut i: usize = 0;
    while i < ps.len()
        invariant
            i <= ps@.len(),
            r@.len() == i,
            forall|j: int| 0 <= j < i ==> r@[j] == ps@[j],
        decreases ps.len() - i,
    {
        r.push((ps[i].0, ty_clone(&ps[i].1)));
        i += 1;
    }
    r
}

/// 解決した関数の列を表 tb で書き換え、核のプログラムを作って型検査する。entry は g（検査で範囲を確かめる）。
/// rank と rec は呼出し側（Rust の接着）が関数の順に作る。受理したなら、核の関数は hrw_funcs の写し。
pub fn hof_compile(fs: &Vec<EXFunc>, g: usize, tb: &Vec<(usize, Ty, Ty)>, rank: Vec<usize>, rec: Vec<bool>) -> (r: HofCompiled)
    ensures
        r matches HofCompiled::Accepted(p) ==> view_prog(p).funcs == hrw_funcs(view_xfuncs(fs@), view_tb(*tb))
            && view_prog(p).entry == g as nat
            && wf(view_prog(p))
            && view_prog(p).rec == rec@,
{
    let mut out: Vec<EFunc> = Vec::new();
    let mut k: usize = 0;
    while k < fs.len()
        invariant
            k <= fs@.len(),
            out@.len() == k,
            forall|i: int| 0 <= i < k ==> view_func(#[trigger] out@[i]) == hrw_func(view_xfunc(fs@[i]), view_tb(*tb)),
        decreases fs.len() - k,
    {
        let f = &fs[k];
        let body = match rw_ex(tb, &f.body) {
            Some(b) => b,
            None => return HofCompiled::RewriteRejected,
        };
        out.push(EFunc { params: params_clone(&f.params), ret: ty_clone(&f.ret), body });
        proof {
            assert(view_params(out@[k as int].params@) =~= view_xfunc(fs@[k as int]).params);
            assert(view_expr(out@[k as int].body) == rw_tb(view_tb(*tb), view_ex(fs@[k as int].body)));
        }
        k += 1;
    }
    let p = EProg { funcs: out, rank, rec, entry: g };
    proof {
        assert(view_prog(p).funcs =~= hrw_funcs(view_xfuncs(fs@), view_tb(*tb)));
    }
    if !check_prog(&p) {
        return HofCompiled::NotWellFormed;
    }
    HofCompiled::Accepted(p)
}

} // verus!
