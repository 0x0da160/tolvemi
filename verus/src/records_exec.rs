//! v1.1 のレコードの展開の exec 実装の最初の一片（設計書 §11.2a、DECISION-23「書換えを Verus で書く」の試作）。
//!
//! `records_proof.rs` の spec モデルを、名前解決済みの exec AST（`ir::EExpr`）の上で計算する。各関数の ensures は、
//! 結果の `view_expr` がモデルの spec 関数（`rty`、`rbuild`、`snds`、`rfield`、`nmissing`、`fill`、`rupdate`）の値に
//! 等しいことである。
//! - `rty_e`：レコード型の展開（records.rs の `record_type`。レコード名の label は扱わない）。
//! - `rbuild_e`：構築の pair の入れ子。`snds_e`、`rfield_e`：参照 `e.fi` の `fst`／`snd` の並び（`lower_expr`、印なし）。
//! - `nmissing_e`、`rupdate_e`：更新 `R { ..., ..base }` の展開（base を置くか、let で一度だけ束縛する）。
//! - `record_e`：records.rs の `record` の核（field を宣言順に置いた後）。base がなく書いていない field があれば
//!   `Missing`（E-RECORD-MISSING-FIELD）、base があり書いていない field がなければ `BaseRedundant`
//!   （E-RECORD-BASE-REDUNDANT）を返す。spec は `rrecord`。
//! - `rrecord_meaning`：受理した展開に `records_proof.rs` の型と意味の補題を当てはめる。base のある構築は書いていない
//!   field を持つ（拒否の規則）ので、`rupdate_meaning` の前提「書いていない field があるか、base が値を持つ」は
//!   いつも満たされる。
//!
//! 扱わないこと（接着部分のまま。records.rs はこの module を呼ばない）：field 名から位置への配置と重複・未知の field の
//! 診断、型名の展開、新しい変数 x の選択（x が書いた式に現れないこと）、式の木全体の走査、名前付きの表面 AST
//! （`SExpr`）での同じ書換えと名前解決（`rx`）との可換性、v1.10 の総称のレコード、v1.15 の名義の印。

use crate::bigstep::*;
use crate::ir::*;
use crate::proof::*;
use crate::records_proof::*;
use crate::spec::*;
use vstd::prelude::*;

verus! {

// ------------------------------------------------------------------ 写像と spec

/// 宣言順の一つの field（exec）の写像：書いた式（`Some`）か、書いていない（`None`）。base にも使う。
pub open spec fn view_slot(o: Option<EExpr>) -> Option<Expr> {
    match o {
        Some(e) => Some(view_expr(e)),
        None => None,
    }
}

/// 宣言順の field の列（exec）の写像。
pub open spec fn view_upd(u: Seq<Option<EExpr>>) -> Seq<Option<Expr>> {
    Seq::new(u.len(), |k: int| view_slot(u[k]))
}

/// すべての field を書いた構築の、field の式の列（宣言順）。
pub open spec fn written(upd: Seq<Option<Expr>>) -> Seq<Expr> {
    Seq::new(upd.len(), |k: int| upd[k]->Some_0)
}

/// 構築を拒否する理由。
pub enum RecErr {
    /// base がなく、書いていない field がある（E-RECORD-MISSING-FIELD）
    Missing,
    /// base があり、書いていない field がない（E-RECORD-BASE-REDUNDANT）
    BaseRedundant,
}

/// records.rs の `record` の核（field を宣言順に置いた後）：拒否の理由か、展開した式。
pub open spec fn rrecord(upd: Seq<Option<Expr>>, base: Option<Expr>, x: nat) -> Result<Expr, RecErr> {
    match base {
        None => if nmissing(upd) > 0 {
            Err(RecErr::Missing)
        } else {
            Ok(rbuild(written(upd)))
        },
        Some(b) => if nmissing(upd) == 0 {
            Err(RecErr::BaseRedundant)
        } else {
            Ok(rupdate(upd, b, x))
        },
    }
}

/// 書いていない field がなければ、すべての field を書いている。
proof fn nmissing_zero(upd: Seq<Option<Expr>>)
    requires
        nmissing(upd) == 0,
    ensures
        forall|k: int| 0 <= k < upd.len() ==> (#[trigger] upd[k]) is Some,
    decreases upd.len(),
{
    if upd.len() > 0 {
        nmissing_zero(upd.drop_last());
        assert forall|k: int| 0 <= k < upd.len() implies (#[trigger] upd[k]) is Some by {
            if k < upd.len() - 1 {
                assert(upd.drop_last()[k] == upd[k]);
            }
        }
    }
}

/// 書いていない field がなければ、b が何であれ `fill` は書いた式の列。
proof fn fill_written(upd: Seq<Option<Expr>>, b: Expr)
    requires
        nmissing(upd) == 0,
    ensures
        fill(upd, b) == written(upd),
{
    nmissing_zero(upd);
    assert(fill(upd, b) =~= written(upd));
}

// ------------------------------------------------------------------ 型

/// レコード型の展開：field の型を右に入れ子にした pair（records.rs の `record_type`）。
pub fn rty_e(ts: Vec<Ty>) -> (r: Ty)
    requires
        ts.len() >= 1,
    ensures
        r == rty(ts@),
{
    let ghost g = ts@;
    let mut ts = ts;
    let mut out = ts.pop().unwrap();
    proof {
        assert(ts@ =~= g.subrange(0, g.len() - 1));
    }
    while ts.len() > 0
        invariant
            1 <= g.len(),
            ts.len() < g.len(),
            ts@ == g.subrange(0, ts.len() as int),
            out == rty(g.subrange(ts.len() as int, g.len() as int)),
        decreases ts.len(),
    {
        let ghost k: int = ts.len() - 1;
        let t = ts.pop().unwrap();
        proof {
            let s = g.subrange(k, g.len() as int);
            assert(s.drop_first() =~= g.subrange(k + 1, g.len() as int));
            assert(s[0] == g[k]);
            assert(ts@ =~= g.subrange(0, k));
        }
        out = Ty::Pair(Box::new(t), Box::new(out));
    }
    proof {
        assert(g.subrange(0, g.len() as int) =~= g);
    }
    out
}

// ------------------------------------------------------------------ 構築と参照

/// 構築の展開：式の列の pair の入れ子（records.rs の `record` の最後の組み立て）。
pub fn rbuild_e(es: Vec<EExpr>) -> (r: EExpr)
    requires
        es.len() >= 1,
    ensures
        view_expr(r) == rbuild(view_exprs(es)),
{
    let ghost orig = es@;
    let ghost g = view_exprs(es);
    proof {
        assert forall|i: int| 0 <= i < g.len() implies #[trigger] g[i] == view_expr(orig[i]) by {}
    }
    let mut es = es;
    let mut out = es.pop().unwrap();
    proof {
        assert(es@ =~= orig.subrange(0, orig.len() - 1));
    }
    while es.len() > 0
        invariant
            g.len() == orig.len(),
            1 <= g.len(),
            es.len() < g.len(),
            es@ == orig.subrange(0, es.len() as int),
            forall|i: int| 0 <= i < g.len() ==> #[trigger] g[i] == view_expr(orig[i]),
            view_expr(out) == rbuild(g.subrange(es.len() as int, g.len() as int)),
        decreases es.len(),
    {
        let ghost k: int = es.len() - 1;
        let v = es.pop().unwrap();
        proof {
            let s = g.subrange(k, g.len() as int);
            assert(s.drop_first() =~= g.subrange(k + 1, g.len() as int));
            assert(s[0] == g[k]);
            assert(es@ =~= orig.subrange(0, k));
        }
        out = EExpr::Pair(Box::new(v), Box::new(out));
    }
    proof {
        assert(g.subrange(0, g.len() as int) =~= g);
    }
    out
}

/// e に `snd` を i 回適用した式。
pub fn snds_e(e: EExpr, i: usize) -> (r: EExpr)
    ensures
        view_expr(r) == snds(view_expr(e), i as nat),
{
    let ghost e0 = view_expr(e);
    let mut x = e;
    let mut j: usize = 0;
    while j < i
        invariant
            j <= i,
            snds(view_expr(x), (i - j) as nat) == snds(e0, i as nat),
        decreases i - j,
    {
        let ghost xv = view_expr(x);
        let mut args: Vec<EExpr> = Vec::new();
        args.push(x);
        proof {
            assert(view_exprs(args) =~= seq![xv]);
        }
        x = EExpr::Builtin(Builtin::Snd, args);
        j = j + 1;
    }
    x
}

/// 参照 `e.fi`（n 個の field の i 番目）の展開（records.rs の `lower_expr`、印なし）。
pub fn rfield_e(e: EExpr, i: usize, n: usize) -> (r: EExpr)
    requires
        i < n,
    ensures
        view_expr(r) == rfield(view_expr(e), i as nat, n as nat),
{
    let x = snds_e(e, i);
    if i + 1 < n {
        let ghost xv = view_expr(x);
        let mut args: Vec<EExpr> = Vec::new();
        args.push(x);
        proof {
            assert(view_exprs(args) =~= seq![xv]);
        }
        EExpr::Builtin(Builtin::Fst, args)
    } else {
        x
    }
}

// ------------------------------------------------------------------ 更新

/// 書いていない field の数。
pub fn nmissing_e(upd: &Vec<Option<EExpr>>) -> (m: usize)
    ensures
        m as nat == nmissing(view_upd(upd@)),
{
    let ghost u = view_upd(upd@);
    let mut m: usize = 0;
    let mut i: usize = 0;
    while i < upd.len()
        invariant
            i <= upd.len(),
            u == view_upd(upd@),
            m <= i,
            m as nat == nmissing(u.subrange(0, i as int)),
        decreases upd.len() - i,
    {
        proof {
            let s = u.subrange(0, i as int + 1);
            assert(s.drop_last() =~= u.subrange(0, i as int));
            assert(s.last() == u[i as int]);
        }
        match &upd[i] {
            None => {
                m = m + 1;
            },
            Some(_) => {},
        }
        i = i + 1;
    }
    proof {
        assert(u.subrange(0, u.len() as int) =~= u);
    }
    m
}

/// `rbuild(fill(upd, b))` を右から組み立てる。書いていない field の式は b の参照で、b は変数 y（`var` が `Some(y)`。
/// 参照ごとに `Var(y)` を作る）か、一度だけ使う式 `once`（書いていない field が一つ以下のとき）。
fn fill_build_e(upd: Vec<Option<EExpr>>, var: Option<usize>, once: Option<EExpr>, Ghost(b): Ghost<Expr>) -> (r: EExpr)
    requires
        upd.len() >= 1,
        var matches Some(y) ==> b == Expr::Var(y as nat),
        var is None ==> nmissing(view_upd(upd@)) <= 1,
        var is None && nmissing(view_upd(upd@)) == 1 ==> (once matches Some(e) && view_expr(e) == b),
    ensures
        view_expr(r) == rbuild(fill(view_upd(upd@), b)),
{
    let ghost orig = upd@;
    let ghost u = view_upd(upd@);
    let ghost f = fill(u, b);
    let n = upd.len();
    let mut upd = upd;
    let mut once = once;
    let ghost mut used: nat = 0;
    let mut out: Option<EExpr> = None;
    proof {
        assert(u.subrange(0, n as int) =~= u);
    }
    while upd.len() > 0
        invariant
            n == orig.len(),
            n >= 1,
            u == view_upd(orig),
            f == fill(u, b),
            upd.len() <= n,
            upd@ == orig.subrange(0, upd.len() as int),
            nmissing(u) == nmissing(u.subrange(0, upd.len() as int)) + used,
            var matches Some(y) ==> b == Expr::Var(y as nat),
            var is None ==> nmissing(u) <= 1,
            var is None && used == 0 && nmissing(u) == 1 ==> (once matches Some(e) && view_expr(e) == b),
            out is None <==> upd.len() == n,
            out matches Some(o) ==> view_expr(o) == rbuild(f.subrange(upd.len() as int, n as int)),
        decreases upd.len(),
    {
        let k = upd.len() - 1;
        let s = upd.pop().unwrap();
        proof {
            assert(upd@ =~= orig.subrange(0, k as int));
            assert(s == orig[k as int]);
            assert(u[k as int] == view_slot(s));
            let p = u.subrange(0, k as int + 1);
            assert(p.drop_last() =~= u.subrange(0, k as int));
            assert(p.last() == u[k as int]);
        }
        let v = match s {
            Some(e) => e,
            None => {
                let base = match var {
                    Some(y) => EExpr::Var(y),
                    None => once.take().unwrap(),
                };
                proof {
                    used = used + 1;
                }
                rfield_e(base, k, n)
            },
        };
        proof {
            assert(view_expr(v) == f[k as int]);
        }
        out = Some(
            match out {
                None => v,
                Some(o) => {
                    proof {
                        let t = f.subrange(k as int, n as int);
                        assert(t.drop_first() =~= f.subrange(k as int + 1, n as int));
                        assert(t[0] == f[k as int]);
                    }
                    EExpr::Pair(Box::new(v), Box::new(o))
                },
            },
        );
    }
    proof {
        assert(f.subrange(0, n as int) =~= f);
    }
    out.unwrap()
}

/// 更新 `R { ..., ..base }` の展開（records.rs の `record`）。base が変数か、書いていない field が一つ以下なら
/// base をその場に置き、そうでなければ x に let で一度だけ束縛する。
pub fn rupdate_e(upd: Vec<Option<EExpr>>, base: EExpr, x: usize) -> (r: EExpr)
    requires
        upd.len() >= 1,
    ensures
        view_expr(r) == rupdate(view_upd(upd@), view_expr(base), x as nat),
{
    let ghost bv = view_expr(base);
    let m = nmissing_e(&upd);
    match base {
        EExpr::Var(y) => fill_build_e(upd, Some(y), None, Ghost(bv)),
        base => {
            proof {
                assert(!(bv is Var));
            }
            if m <= 1 {
                fill_build_e(upd, None, Some(base), Ghost(bv))
            } else {
                let body = fill_build_e(upd, Some(x), None, Ghost(Expr::Var(x as nat)));
                EExpr::Let(x, Box::new(base), Box::new(body))
            }
        },
    }
}

/// records.rs の `record` の核：field を宣言順に置いた後の、構築・更新の拒否と展開。
pub fn record_e(upd: Vec<Option<EExpr>>, base: Option<EExpr>, x: usize) -> (r: Result<EExpr, RecErr>)
    requires
        upd.len() >= 1,
    ensures
        r matches Ok(e) ==> rrecord(view_upd(upd@), view_slot(base), x as nat) == Ok::<Expr, RecErr>(view_expr(e)),
        r matches Err(k) ==> rrecord(view_upd(upd@), view_slot(base), x as nat) == Err::<Expr, RecErr>(k),
{
    let ghost u = view_upd(upd@);
    let m = nmissing_e(&upd);
    match base {
        None => {
            if m > 0 {
                Err(RecErr::Missing)
            } else {
                proof {
                    fill_written(u, Expr::Unit);
                }
                Ok(fill_build_e(upd, None, None, Ghost(Expr::Unit)))
            }
        },
        Some(b) => {
            if m == 0 {
                Err(RecErr::BaseRedundant)
            } else {
                Ok(rupdate_e(upd, b, x))
            }
        },
    }
}

// ------------------------------------------------------------------ 受理した展開の型と意味

/// 受理した構築・更新の展開は展開後のレコード型を持ち、その値はレコードの意味の値と一致する（`rbuild_type`、
/// `rbuild_meaning`、`rupdate_type`、`rupdate_meaning` を `rrecord` の結果に当てはめる）。base のある構築は
/// 書いていない field を持つので、`rupdate_meaning` の前提「書いていない field があるか、base が値を持つ」は要らない。
pub proof fn rrecord_meaning(
    p: Prog,
    r: nat,
    ctx: Map<nat, Ty>,
    env: Map<nat, Val>,
    upd: Seq<Option<Expr>>,
    base: Option<Expr>,
    x: nat,
    ts: Seq<Ty>,
    out: Expr,
    w: Val,
)
    requires
        wf(p),
        env_ok(env, ctx),
        rrecord(upd, base, x) == Ok::<Expr, RecErr>(out),
        upd.len() == ts.len(),
        ts.len() >= 1,
        forall|k: int|
            0 <= k < upd.len() && (#[trigger] upd[k]) is Some ==> absent(x, upd[k]->Some_0) && ty_expr(
                p,
                r,
                ctx,
                upd[k]->Some_0,
            ) == Some(ts[k]),
        base matches Some(b) ==> ty_expr(p, r, ctx, b) == Some(rty(ts)),
    ensures
        ty_expr(p, r, ctx, out) == Some(rty(ts)),
        base is None ==> (evals_to(p, env, out, w) <==> exists|vs: Seq<Val>|
            #[trigger] fields_to(p, env, written(upd), vs) && w == rval(vs)),
        base matches Some(b) ==> (evals_to(p, env, out, w) <==> exists|vb: Val, vs: Seq<Val>|
            evals_to(p, env, b, vb) && #[trigger] update_to(p, env, upd, vb, vs) && w == rval(vs)),
{
    match base {
        None => {
            nmissing_zero(upd);
            let es = written(upd);
            assert forall|k: int| 0 <= k < es.len() implies ty_expr(p, r, ctx, #[trigger] es[k]) == Some(ts[k]) by {
                assert(upd[k] is Some);
            }
            rbuild_type(p, r, ctx, es, ts);
            rbuild_meaning(p, env, es, w);
        },
        Some(b) => {
            rupdate_type(p, r, ctx, upd, b, x, ts);
            rupdate_meaning(p, r, ctx, env, upd, b, x, ts, w);
        },
    }
}

} // verus!
