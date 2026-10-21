//! v1.1 のレコードの展開の spec モデルと、展開が意味を保つことの証明（設計書 §11.2a の版ごとの証明の試行。
//! §11.2 の義務 6〜8 に沿う）。
//!
//! モデル（`crates/tlvm/src/records.rs` の印なしの写し。v1.15 の名義の印は扱わない）：
//! - 型 `{ f1: T1, ..., fn: Tn }` は `rty(ts)` ＝ `Pair<T1, Pair<T2, ... Tn>>`（n = 1 なら T1）。値は `rval(vs)`。
//! - 構築 `R { ... }` は `rbuild(es)`：各 field に書いた式を宣言順に並べた列 es の pair の入れ子。
//! - 参照 `e.fi` は `rfield(e, i, n)` ＝ `fst(snd^i(e))`（最後の field は `snd^i(e)`）。
//! - 更新 `R { ..., ..base }` は `rupdate(upd, base, x)`：書いていない field を base の参照で埋める。base が変数か、
//!   書いていない field が一つ以下なら base をその場に置き、そうでなければ新しい変数 x に let で一度だけ束縛する。
//!
//! レコードの意味は field の値の列で与える。構築の値は各 field の式の値の列、`e.fi` の値は e の値を n 個の field の
//! 列として見た `rview(v, n)` の i 番目、更新の値は、書いた field を書いた式の値に、残りを base の値の field にした列。
//! 意味は燃料に依らない `evals_to`（`bigstep`）で述べる。
//!
//! 証明したこと（`assume`・`admit`・`external_body` なし）：
//! - 値と型（義務 6）：展開後の型の値は、field ごとに型の付いた値の列と一対一に対応する（`rval_type`、`rview_ok`、
//!   `rview_rval`）。型の付いた構築・参照・更新は、展開後も同じ型を持つ（`rbuild_type`、`rfield_type`、`rupdate_type`）。
//! - 意味の保存（義務 6〜8、両方向）：展開後の式が値 w を持つことと、レコードの意味で w を持つことは同値（`rbuild_meaning`、
//!   `rfield_meaning`、`rupdate_meaning`、構築した値の参照 `rget_build`）。値を持たないこと（行き詰まり・停止しない
//!   こと）も一致し、field を宣言順に並べ替えても意味は変わらない。展開後の式は核の式なので、燃料単調性と決定性
//!   （`mono`、`eval_deterministic`）と exec 評価器の適合（`bigstep` の規則）はそのまま当てはまる。
//! - 束縛の新しさ：let で入れる x が式に現れなければ、x の束縛は評価も型も変えない（`eval_absent`、`ty_absent`）。
//! - モデルの形：3 個の field の型・参照・更新が records.rs の出力と同じ形になる（`example_shapes`。すべての field を
//!   書いた更新では base が消える）。
//!
//! 証明していないこと：
//! - records.rs（exec）がこのモデルのとおりに書き換えること。展開は検証されていない接着部分のまま。
//! - プログラム全体の定理（レコードの構文を持つ AST とその意味を定義し、上の補題を展開に沿った帰納法で組み合わせる）。
//! - 名前解決後の番号で x が書いた式に現れないこと（records.rs はプログラム中のどの名前とも違う名前を選ぶ）。
//! - すべての field を書いた更新：records.rs は base を捨てる（評価も名前解決も型検査もしない）。`rupdate_meaning` は
//!   この場合だけ base が値を持つことを前提にする。
//! - v1.10 の総称のレコード、v1.15 の名義の印、plain JSON の入出力。

use crate::bigstep::*;
use crate::proof::*;
use crate::spec::*;
use vstd::prelude::*;

verus! {

// ------------------------------------------------------------------ 展開（spec モデル）

/// レコード型の展開：field の型の列 ts（宣言順、空でない）を右に入れ子にした pair。records.rs の `record_type`。
pub open spec fn rty(ts: Seq<Ty>) -> Ty
    decreases ts.len(),
{
    if ts.len() <= 1 {
        ts[0]
    } else {
        Ty::Pair(Box::new(ts[0]), Box::new(rty(ts.drop_first())))
    }
}

/// レコードの値（field の値の列）の展開。
pub open spec fn rval(vs: Seq<Val>) -> Val
    decreases vs.len(),
{
    if vs.len() <= 1 {
        vs[0]
    } else {
        Val::Pair(Box::new(vs[0]), Box::new(rval(vs.drop_first())))
    }
}

/// 値 v を n 個の field の値の列として見る（`rval` の逆）。
pub open spec fn rview(v: Val, n: nat) -> Seq<Val>
    decreases n,
{
    if n <= 1 {
        seq![v]
    } else {
        seq![*v->Pair_0] + rview(*v->Pair_1, (n - 1) as nat)
    }
}

/// 構築 `R { ... }` の展開：field の式を宣言順に並べた列 es の pair の入れ子。records.rs の `record`。
pub open spec fn rbuild(es: Seq<Expr>) -> Expr
    decreases es.len(),
{
    if es.len() <= 1 {
        es[0]
    } else {
        Expr::Pair(Box::new(es[0]), Box::new(rbuild(es.drop_first())))
    }
}

/// e に `snd` を i 回適用した式。
pub open spec fn snds(e: Expr, i: nat) -> Expr
    decreases i,
{
    if i == 0 {
        e
    } else {
        snds(Expr::Builtin(Builtin::Snd, seq![e]), (i - 1) as nat)
    }
}

/// 参照 `e.f`（f は n 個の field の i 番目）の展開。records.rs の `lower_expr`（印なし）。
pub open spec fn rfield(e: Expr, i: nat, n: nat) -> Expr {
    if i + 1 < n {
        Expr::Builtin(Builtin::Fst, seq![snds(e, i)])
    } else {
        snds(e, i)
    }
}

/// 更新の field の式：書いた field（`Some`）はその式、書いていない field は b の参照。
pub open spec fn fill(upd: Seq<Option<Expr>>, b: Expr) -> Seq<Expr> {
    Seq::new(
        upd.len(),
        |k: int|
            match upd[k] {
                Some(e) => e,
                None => rfield(b, k as nat, upd.len()),
            },
    )
}

/// 書いていない field の数。
pub open spec fn nmissing(upd: Seq<Option<Expr>>) -> nat
    decreases upd.len(),
{
    if upd.len() == 0 {
        0
    } else {
        let m = nmissing(upd.drop_last());
        if upd.last() is None {
            m + 1
        } else {
            m
        }
    }
}

/// 更新 `R { ..., ..base }` の展開。base が変数か、書いていない field が一つ以下なら base をその場に置き、
/// そうでなければ新しい変数 x に let で一度だけ束縛する（records.rs の `record`）。
pub open spec fn rupdate(upd: Seq<Option<Expr>>, base: Expr, x: nat) -> Expr {
    if base is Var || nmissing(upd) <= 1 {
        rbuild(fill(upd, base))
    } else {
        Expr::Let(x, Box::new(base), Box::new(rbuild(fill(upd, Expr::Var(x)))))
    }
}

// ------------------------------------------------------------------ レコードの意味

/// 構築の意味：各 field の式 es[k] が値 vs[k] を持つ（構築の値は列 vs）。評価の順は問わない。
pub open spec fn fields_to(p: Prog, env: Map<nat, Val>, es: Seq<Expr>, vs: Seq<Val>) -> bool {
    &&& vs.len() == es.len()
    &&& forall|k: int| 0 <= k < es.len() ==> evals_to(p, env, #[trigger] es[k], vs[k])
}

/// 更新の一つの field の値：書いた式の値（`Some`）か、base の値の同じ field（`None`）。
pub open spec fn slot_to(p: Prog, env: Map<nat, Val>, o: Option<Expr>, old: Val, v: Val) -> bool {
    match o {
        Some(e) => evals_to(p, env, e, v),
        None => v == old,
    }
}

/// 更新の意味：base の値 vb の field を、書いた field だけ書いた式の値に置き換えた列 vs。
pub open spec fn update_to(p: Prog, env: Map<nat, Val>, upd: Seq<Option<Expr>>, vb: Val, vs: Seq<Val>) -> bool {
    &&& vs.len() == upd.len()
    &&& forall|k: int| 0 <= k < upd.len() ==> slot_to(p, env, #[trigger] upd[k], rview(vb, upd.len())[k], vs[k])
}

/// 変数 x が式 e に現れない（参照にも束縛にも）。
pub open spec fn absent(x: nat, e: Expr) -> bool
    decreases e, 0nat,
{
    match e {
        Expr::Var(y) => y != x,
        Expr::List(_, es) => absent_args(x, es, 0),
        Expr::Some(a) => absent(x, *a),
        Expr::Pair(a, b) => absent(x, *a) && absent(x, *b),
        Expr::Builtin(_, es) => absent_args(x, es, 0),
        Expr::Call(_, es) => absent_args(x, es, 0),
        Expr::Let(y, a, b) => y != x && absent(x, *a) && absent(x, *b),
        Expr::If(c, a, b) => absent(x, *c) && absent(x, *a) && absent(x, *b),
        Expr::Fold(xs, init, acc, item, body) => acc != x && item != x && absent(x, *xs) && absent(x, *init)
            && absent(x, *body),
        Expr::Match(m, nb, y, sm) => y != x && absent(x, *m) && absent(x, *nb) && absent(x, *sm),
        Expr::Inj(_, _, _, a) => absent(x, *a),
        Expr::MatchR(m, y, a, z, b) => y != x && z != x && absent(x, *m) && absent(x, *a) && absent(x, *b),
        _ => true,
    }
}

pub open spec fn absent_args(x: nat, es: Seq<Expr>, i: nat) -> bool
    decreases es, es.len() - i,
{
    if i >= es.len() {
        true
    } else {
        absent(x, es[i as int]) && absent_args(x, es, i + 1)
    }
}

// ------------------------------------------------------------------ 補助：fst・snd・pair・let

/// fst／snd の型：e が pair の型 t を持てば、その成分の型。
proof fn un_type(p: Prog, r: nat, ctx: Map<nat, Ty>, e: Expr, t: Ty)
    requires
        ty_expr(p, r, ctx, e) == Some(t),
        t is Pair,
    ensures
        ty_expr(p, r, ctx, Expr::Builtin(Builtin::Fst, seq![e])) == Some(*t->Pair_0),
        ty_expr(p, r, ctx, Expr::Builtin(Builtin::Snd, seq![e])) == Some(*t->Pair_1),
{
    let es = seq![e];
    assert(es[0] == e);
    assert(ty_args(p, r, ctx, es, 1) == Some(Seq::<Ty>::empty()));
    assert(seq![t] + Seq::<Ty>::empty() =~= seq![t]);
    assert(ty_args(p, r, ctx, es, 0) == Some(seq![t]));
}

/// fst／snd の評価：e が pair の値 v を持てば、その成分を持つ。
proof fn un_eval(p: Prog, env: Map<nat, Val>, e: Expr, v: Val)
    requires
        evals_to(p, env, e, v),
        v is Pair,
    ensures
        evals_to(p, env, Expr::Builtin(Builtin::Fst, seq![e]), *v->Pair_0),
        evals_to(p, env, Expr::Builtin(Builtin::Snd, seq![e]), *v->Pair_1),
{
    let n = choose|n: nat| #[trigger] eval(p, n, env, e) == Res::Done(v);
    assert(n > 0);
    let es = seq![e];
    assert(es[0] == e);
    assert(eval_args(p, n, env, es, 1) == ResSeq::Done(Seq::<Val>::empty()));
    assert(seq![v] + Seq::<Val>::empty() =~= seq![v]);
    assert(eval_args(p, n + 1, env, es, 0) == ResSeq::Done(seq![v]));
    assert(eval(p, n + 2, env, Expr::Builtin(Builtin::Fst, es)) == Res::Done(*v->Pair_0));
    assert(eval(p, n + 2, env, Expr::Builtin(Builtin::Snd, es)) == Res::Done(*v->Pair_1));
}

/// fst／snd の評価の逆：結果が値 w なら、e は pair の値 v を持ち、w はその成分。
proof fn un_inv(p: Prog, env: Map<nat, Val>, b: Builtin, e: Expr, w: Val) -> (v: Val)
    requires
        b == Builtin::Fst || b == Builtin::Snd,
        evals_to(p, env, Expr::Builtin(b, seq![e]), w),
    ensures
        evals_to(p, env, e, v),
        v is Pair,
        w == if b == Builtin::Fst {
            *v->Pair_0
        } else {
            *v->Pair_1
        },
{
    let es = seq![e];
    let n = choose|n: nat| #[trigger] eval(p, n, env, Expr::Builtin(b, es)) == Res::Done(w);
    assert(n > 0);
    let f = (n - 1) as nat;
    assert(eval_args(p, f, env, es, 0) is Done);
    let vs = eval_args(p, f, env, es, 0)->Done_0;
    assert(f > 0);
    let g = (f - 1) as nat;
    assert(es[0] == e);
    assert(eval(p, g, env, e) is Done);
    let v = eval(p, g, env, e)->Done_0;
    assert(eval_args(p, g, env, es, 1) is Done);
    assert(g > 0);
    assert(eval_args(p, g, env, es, 1) == ResSeq::Done(Seq::<Val>::empty()));
    assert(vs =~= seq![v]);
    assert(apply(b, seq![v]) == Res::Done(w));
    assert(eval(p, g, env, e) == Res::Done(v));
    v
}

/// pair の評価の逆。
proof fn pair_inv(p: Prog, env: Map<nat, Val>, a: Expr, b: Expr, w: Val) -> (r: (Val, Val))
    requires
        evals_to(p, env, Expr::Pair(Box::new(a), Box::new(b)), w),
    ensures
        evals_to(p, env, a, r.0),
        evals_to(p, env, b, r.1),
        w == Val::Pair(Box::new(r.0), Box::new(r.1)),
{
    let n = choose|n: nat| #[trigger] eval(p, n, env, Expr::Pair(Box::new(a), Box::new(b))) == Res::Done(w);
    let f = (n - 1) as nat;
    let va = eval(p, f, env, a)->Done_0;
    let vb = eval(p, f, env, b)->Done_0;
    assert(eval(p, f, env, a) == Res::Done(va));
    assert(eval(p, f, env, b) == Res::Done(vb));
    (va, vb)
}

/// let の評価の逆。
proof fn let_inv(p: Prog, env: Map<nat, Val>, x: nat, a: Expr, b: Expr, w: Val) -> (va: Val)
    requires
        evals_to(p, env, Expr::Let(x, Box::new(a), Box::new(b)), w),
    ensures
        evals_to(p, env, a, va),
        evals_to(p, env.insert(x, va), b, w),
{
    let n = choose|n: nat| #[trigger] eval(p, n, env, Expr::Let(x, Box::new(a), Box::new(b))) == Res::Done(w);
    let f = (n - 1) as nat;
    let va = eval(p, f, env, a)->Done_0;
    assert(eval(p, f, env, a) == Res::Done(va));
    assert(eval(p, f, env.insert(x, va), b) == Res::Done(w));
    va
}

/// 値は一意（決定性）。
proof fn evals_unique(p: Prog, env: Map<nat, Val>, e: Expr, v: Val, w: Val)
    requires
        evals_to(p, env, e, v),
        evals_to(p, env, e, w),
    ensures
        v == w,
{
    let n = choose|n: nat| #[trigger] eval(p, n, env, e) == Res::Done(w);
    same(p, n, env, e, v);
}

/// 変数 x の値は、x を束縛した環境で一意に決まる。
proof fn var_to(p: Prog, env: Map<nat, Val>, x: nat, v: Val)
    ensures
        evals_to(p, env.insert(x, v), Expr::Var(x), v),
{
    assert(eval(p, 1, env.insert(x, v), Expr::Var(x)) == Res::Done(v));
}

/// 書いていない field が一つでもあれば、その位置がある。
proof fn nmissing_pos(upd: Seq<Option<Expr>>) -> (k: int)
    requires
        nmissing(upd) > 0,
    ensures
        0 <= k < upd.len(),
        upd[k] is None,
    decreases upd.len(),
{
    if upd.last() is None {
        upd.len() - 1
    } else {
        let k = nmissing_pos(upd.drop_last());
        assert(upd.drop_last()[k] == upd[k]);
        k
    }
}

/// `rview` の長さ。
proof fn rview_len(v: Val, n: nat)
    requires
        n >= 1,
    ensures
        rview(v, n).len() == n,
    decreases n,
{
    if n >= 2 {
        rview_len(*v->Pair_1, (n - 1) as nat);
    }
}

// ------------------------------------------------------------------ 値と型

/// field の値の列の展開が展開後の型を持つことと、各 field の値が field の型を持つことは同値。
pub proof fn rval_type(vs: Seq<Val>, ts: Seq<Ty>)
    requires
        vs.len() == ts.len(),
        vs.len() >= 1,
    ensures
        val_type(rval(vs), rty(ts)) <==> forall|k: int| 0 <= k < vs.len() ==> #[trigger] val_type(vs[k], ts[k]),
    decreases vs.len(),
{
    if vs.len() >= 2 {
        let us = vs.drop_first();
        let ss = ts.drop_first();
        rval_type(us, ss);
        assert(rval(vs) == Val::Pair(Box::new(vs[0]), Box::new(rval(us))));
        assert(rty(ts) == Ty::Pair(Box::new(ts[0]), Box::new(rty(ss))));
        if forall|k: int| 0 <= k < vs.len() ==> #[trigger] val_type(vs[k], ts[k]) {
            assert forall|k: int| 0 <= k < us.len() implies #[trigger] val_type(us[k], ss[k]) by {
                assert(us[k] == vs[k + 1] && ss[k] == ts[k + 1]);
                assert(val_type(vs[k + 1], ts[k + 1]));
            }
            assert(val_type(vs[0], ts[0]));
        }
        if val_type(rval(vs), rty(ts)) {
            assert forall|k: int| 0 <= k < vs.len() implies #[trigger] val_type(vs[k], ts[k]) by {
                if k > 0 {
                    assert(us[k - 1] == vs[k] && ss[k - 1] == ts[k]);
                    assert(val_type(us[k - 1], ss[k - 1]));
                }
            }
        }
    } else {
        assert(rval(vs) == vs[0] && rty(ts) == ts[0]);
        if val_type(rval(vs), rty(ts)) {
            assert forall|k: int| 0 <= k < vs.len() implies #[trigger] val_type(vs[k], ts[k]) by {
                assert(k == 0);
            }
        }
    }
}

/// 展開後の型の値 v は、field ごとに型の付いた値の列 `rview(v, n)` の展開である。
pub proof fn rview_ok(v: Val, ts: Seq<Ty>)
    requires
        ts.len() >= 1,
        val_type(v, rty(ts)),
    ensures
        rview(v, ts.len()).len() == ts.len(),
        rval(rview(v, ts.len())) == v,
        forall|k: int| 0 <= k < ts.len() ==> #[trigger] val_type(rview(v, ts.len())[k], ts[k]),
    decreases ts.len(),
{
    let n = ts.len();
    if n >= 2 {
        let ss = ts.drop_first();
        assert(rty(ts) == Ty::Pair(Box::new(ts[0]), Box::new(rty(ss))));
        assert(v is Pair);
        let a = *v->Pair_0;
        let b = *v->Pair_1;
        rview_ok(b, ss);
        let s = rview(b, ss.len());
        let u = rview(v, n);
        assert(u == seq![a] + s);
        assert(u.drop_first() =~= s);
        assert(rval(u) == Val::Pair(Box::new(a), Box::new(rval(s))));
        assert forall|k: int| 0 <= k < n implies #[trigger] val_type(rview(v, n)[k], ts[k]) by {
            if k > 0 {
                assert(u[k] == s[k - 1] && ts[k] == ss[k - 1]);
                assert(val_type(s[k - 1], ss[k - 1]));
            }
        }
    } else {
        assert forall|k: int| 0 <= k < n implies #[trigger] val_type(rview(v, n)[k], ts[k]) by {
            assert(k == 0);
        }
    }
}

/// `rview` は `rval` の逆：field の値の列を展開して見直すと元の列に戻る。
pub proof fn rview_rval(vs: Seq<Val>)
    requires
        vs.len() >= 1,
    ensures
        rview(rval(vs), vs.len()) == vs,
    decreases vs.len(),
{
    if vs.len() >= 2 {
        let us = vs.drop_first();
        rview_rval(us);
        assert(rval(vs) == Val::Pair(Box::new(vs[0]), Box::new(rval(us))));
        assert(rview(rval(vs), vs.len()) == seq![vs[0]] + rview(rval(us), us.len()));
        assert(seq![vs[0]] + us =~= vs);
    } else {
        assert(seq![vs[0]] =~= vs);
    }
}

// ------------------------------------------------------------------ 参照 `e.f`

/// 参照の型：e が展開後のレコード型を持てば、`rfield(e, i, n)` は i 番目の field の型を持つ。
pub proof fn rfield_type(p: Prog, r: nat, ctx: Map<nat, Ty>, e: Expr, ts: Seq<Ty>, i: nat)
    requires
        i < ts.len(),
        ty_expr(p, r, ctx, e) == Some(rty(ts)),
    ensures
        ty_expr(p, r, ctx, rfield(e, i, ts.len())) == Some(ts[i as int]),
    decreases i,
{
    assert(snds(e, 0) == e);
    if ts.len() >= 2 {
        let ss = ts.drop_first();
        assert(rty(ts) == Ty::Pair(Box::new(ts[0]), Box::new(rty(ss))));
        un_type(p, r, ctx, e, rty(ts));
        if i > 0 {
            let e1 = Expr::Builtin(Builtin::Snd, seq![e]);
            rfield_type(p, r, ctx, e1, ss, (i - 1) as nat);
            assert(rfield(e, i, ts.len()) == rfield(e1, (i - 1) as nat, ss.len()));
            assert(ts[i as int] == ss[i - 1]);
        }
    }
}

/// 参照の評価：e が展開後の型の値 v を持てば、`rfield(e, i, n)` は v の i 番目の field を持つ。
pub proof fn rfield_fwd(p: Prog, env: Map<nat, Val>, e: Expr, v: Val, ts: Seq<Ty>, i: nat)
    requires
        i < ts.len(),
        evals_to(p, env, e, v),
        val_type(v, rty(ts)),
    ensures
        evals_to(p, env, rfield(e, i, ts.len()), rview(v, ts.len())[i as int]),
    decreases i,
{
    let n = ts.len();
    assert(snds(e, 0) == e);
    if n >= 2 {
        let ss = ts.drop_first();
        assert(rty(ts) == Ty::Pair(Box::new(ts[0]), Box::new(rty(ss))));
        assert(v is Pair);
        un_eval(p, env, e, v);
        if i > 0 {
            let e1 = Expr::Builtin(Builtin::Snd, seq![e]);
            rfield_fwd(p, env, e1, *v->Pair_1, ss, (i - 1) as nat);
            assert(rfield(e, i, n) == rfield(e1, (i - 1) as nat, ss.len()));
            rview_len(*v->Pair_1, ss.len());
            assert(rview(v, n)[i as int] == rview(*v->Pair_1, ss.len())[i - 1]);
        }
    }
}

/// 参照の評価の逆：`rfield(e, i, n)` が値 w を持てば、e は値 v を持ち、w は v の i 番目の field。
pub proof fn rfield_inv(p: Prog, env: Map<nat, Val>, e: Expr, i: nat, n: nat, w: Val) -> (v: Val)
    requires
        i < n,
        evals_to(p, env, rfield(e, i, n), w),
    ensures
        evals_to(p, env, e, v),
        w == rview(v, n)[i as int],
    decreases i,
{
    assert(snds(e, 0) == e);
    if i == 0 {
        if n >= 2 {
            un_inv(p, env, Builtin::Fst, e, w)
        } else {
            w
        }
    } else {
        let e1 = Expr::Builtin(Builtin::Snd, seq![e]);
        assert(rfield(e, i, n) == rfield(e1, (i - 1) as nat, (n - 1) as nat));
        let v1 = rfield_inv(p, env, e1, (i - 1) as nat, (n - 1) as nat, w);
        let v = un_inv(p, env, Builtin::Snd, e, v1);
        rview_len(v1, (n - 1) as nat);
        assert(rview(v, n)[i as int] == rview(v1, (n - 1) as nat)[i - 1]);
        v
    }
}

// ------------------------------------------------------------------ 構築 `R { ... }`

/// 構築の型：各 field の式が field の型を持てば、展開は展開後のレコード型を持つ。
pub proof fn rbuild_type(p: Prog, r: nat, ctx: Map<nat, Ty>, es: Seq<Expr>, ts: Seq<Ty>)
    requires
        es.len() == ts.len(),
        es.len() >= 1,
        forall|k: int| 0 <= k < es.len() ==> ty_expr(p, r, ctx, #[trigger] es[k]) == Some(ts[k]),
    ensures
        ty_expr(p, r, ctx, rbuild(es)) == Some(rty(ts)),
    decreases es.len(),
{
    assert(ty_expr(p, r, ctx, es[0]) == Some(ts[0]));
    if es.len() >= 2 {
        let fs = es.drop_first();
        let ss = ts.drop_first();
        assert forall|k: int| 0 <= k < fs.len() implies ty_expr(p, r, ctx, #[trigger] fs[k]) == Some(ss[k]) by {
            assert(fs[k] == es[k + 1] && ss[k] == ts[k + 1]);
            assert(ty_expr(p, r, ctx, es[k + 1]) == Some(ts[k + 1]));
        }
        rbuild_type(p, r, ctx, fs, ss);
        assert(rbuild(es) == Expr::Pair(Box::new(es[0]), Box::new(rbuild(fs))));
        assert(rty(ts) == Ty::Pair(Box::new(ts[0]), Box::new(rty(ss))));
    }
}

/// 構築の評価：各 field の式が値を持てば、展開はその値の列の展開を持つ。
pub proof fn rbuild_fwd(p: Prog, env: Map<nat, Val>, es: Seq<Expr>, vs: Seq<Val>)
    requires
        es.len() >= 1,
        fields_to(p, env, es, vs),
    ensures
        evals_to(p, env, rbuild(es), rval(vs)),
    decreases es.len(),
{
    assert(evals_to(p, env, es[0], vs[0]));
    if es.len() >= 2 {
        let fs = es.drop_first();
        let us = vs.drop_first();
        assert forall|k: int| 0 <= k < fs.len() implies evals_to(p, env, #[trigger] fs[k], us[k]) by {
            assert(fs[k] == es[k + 1] && us[k] == vs[k + 1]);
            assert(evals_to(p, env, es[k + 1], vs[k + 1]));
        }
        rbuild_fwd(p, env, fs, us);
        bs_pair(p, env, es[0], rbuild(fs), vs[0], rval(us));
        assert(rbuild(es) == Expr::Pair(Box::new(es[0]), Box::new(rbuild(fs))));
        assert(rval(vs) == Val::Pair(Box::new(vs[0]), Box::new(rval(us))));
    }
}

/// 構築の評価の逆：展開が値 w を持てば、各 field の式は値を持ち、w はその値の列の展開。
pub proof fn rbuild_inv(p: Prog, env: Map<nat, Val>, es: Seq<Expr>, w: Val) -> (vs: Seq<Val>)
    requires
        es.len() >= 1,
        evals_to(p, env, rbuild(es), w),
    ensures
        fields_to(p, env, es, vs),
        w == rval(vs),
    decreases es.len(),
{
    if es.len() == 1 {
        let vs = seq![w];
        assert forall|k: int| 0 <= k < es.len() implies evals_to(p, env, #[trigger] es[k], vs[k]) by {
            assert(k == 0);
        }
        vs
    } else {
        let fs = es.drop_first();
        assert(rbuild(es) == Expr::Pair(Box::new(es[0]), Box::new(rbuild(fs))));
        let (va, vb) = pair_inv(p, env, es[0], rbuild(fs), w);
        let us = rbuild_inv(p, env, fs, vb);
        let vs = seq![va] + us;
        assert forall|k: int| 0 <= k < es.len() implies evals_to(p, env, #[trigger] es[k], vs[k]) by {
            if k > 0 {
                assert(es[k] == fs[k - 1] && vs[k] == us[k - 1]);
                assert(evals_to(p, env, fs[k - 1], us[k - 1]));
            }
        }
        assert(vs.drop_first() =~= us);
        vs
    }
}

// ------------------------------------------------------------------ 意味の保存：構築と参照

/// 構築の意味の保存：展開が値 w を持つことと、各 field の式が値の列 vs を持ち w が vs の展開であることは同値。
pub proof fn rbuild_meaning(p: Prog, env: Map<nat, Val>, es: Seq<Expr>, w: Val)
    requires
        es.len() >= 1,
    ensures
        evals_to(p, env, rbuild(es), w) <==> exists|vs: Seq<Val>| #[trigger] fields_to(p, env, es, vs) && w == rval(vs),
{
    if evals_to(p, env, rbuild(es), w) {
        let vs = rbuild_inv(p, env, es, w);
    }
    if exists|vs: Seq<Val>| #[trigger] fields_to(p, env, es, vs) && w == rval(vs) {
        let vs = choose|vs: Seq<Val>| #[trigger] fields_to(p, env, es, vs) && w == rval(vs);
        rbuild_fwd(p, env, es, vs);
    }
}

/// 参照の意味の保存：e が展開後のレコード型を持つとき、`rfield(e, i, n)` は i 番目の field の型を持つ。
/// 値 w を持つことと、e が値 v を持ち w が v の i 番目の field であることは同値。
pub proof fn rfield_meaning(
    p: Prog,
    r: nat,
    ctx: Map<nat, Ty>,
    env: Map<nat, Val>,
    e: Expr,
    ts: Seq<Ty>,
    i: nat,
    w: Val,
)
    requires
        wf(p),
        env_ok(env, ctx),
        ty_expr(p, r, ctx, e) == Some(rty(ts)),
        i < ts.len(),
    ensures
        ty_expr(p, r, ctx, rfield(e, i, ts.len())) == Some(ts[i as int]),
        evals_to(p, env, rfield(e, i, ts.len()), w) <==> exists|v: Val|
            #[trigger] evals_to(p, env, e, v) && w == rview(v, ts.len())[i as int],
{
    rfield_type(p, r, ctx, e, ts, i);
    if evals_to(p, env, rfield(e, i, ts.len()), w) {
        let v = rfield_inv(p, env, e, i, ts.len(), w);
    }
    if exists|v: Val| #[trigger] evals_to(p, env, e, v) && w == rview(v, ts.len())[i as int] {
        let v = choose|v: Val| #[trigger] evals_to(p, env, e, v) && w == rview(v, ts.len())[i as int];
        let n = choose|n: nat| #[trigger] eval(p, n, env, e) == Res::Done(v);
        sound(p, n, r, ctx, env, e, v);
        rfield_fwd(p, env, e, v, ts, i);
    }
}

/// 構築した値の参照（射影の法則）：`R { ... }.fi` の展開が値 w を持つことと、各 field の式が値の列 vs を持ち
/// w == vs[i] であることは同値。
pub proof fn rget_build(
    p: Prog,
    r: nat,
    ctx: Map<nat, Ty>,
    env: Map<nat, Val>,
    es: Seq<Expr>,
    ts: Seq<Ty>,
    i: nat,
    w: Val,
)
    requires
        wf(p),
        env_ok(env, ctx),
        es.len() == ts.len(),
        i < ts.len(),
        forall|k: int| 0 <= k < es.len() ==> ty_expr(p, r, ctx, #[trigger] es[k]) == Some(ts[k]),
    ensures
        evals_to(p, env, rfield(rbuild(es), i, ts.len()), w) <==> exists|vs: Seq<Val>|
            #[trigger] fields_to(p, env, es, vs) && w == vs[i as int],
{
    rbuild_type(p, r, ctx, es, ts);
    rfield_meaning(p, r, ctx, env, rbuild(es), ts, i, w);
    if evals_to(p, env, rfield(rbuild(es), i, ts.len()), w) {
        let v = choose|v: Val| #[trigger] evals_to(p, env, rbuild(es), v) && w == rview(v, ts.len())[i as int];
        let vs = rbuild_inv(p, env, es, v);
        rview_rval(vs);
    }
    if exists|vs: Seq<Val>| #[trigger] fields_to(p, env, es, vs) && w == vs[i as int] {
        let vs = choose|vs: Seq<Val>| #[trigger] fields_to(p, env, es, vs) && w == vs[i as int];
        rbuild_fwd(p, env, es, vs);
        rview_rval(vs);
        assert(evals_to(p, env, rbuild(es), rval(vs)) && w == rview(rval(vs), ts.len())[i as int]);
    }
}

// ------------------------------------------------------------------ 束縛の新しさ

/// x が e に現れなければ、x の束縛を加えても評価は変わらない。
pub proof fn eval_absent(p: Prog, n: nat, env: Map<nat, Val>, e: Expr, x: nat, v: Val)
    requires
        absent(x, e),
    ensures
        eval(p, n, env.insert(x, v), e) == eval(p, n, env, e),
    decreases n,
{
    if n > 0 {
        let f = (n - 1) as nat;
        let env1 = env.insert(x, v);
        match e {
            Expr::Var(y) => {
                assert(env1.contains_key(y) == env.contains_key(y));
                if env.contains_key(y) {
                    assert(env1[y] == env[y]);
                }
            },
            Expr::List(_, es) => eval_args_absent(p, f, env, es, 0, x, v),
            Expr::Some(a) => eval_absent(p, f, env, *a, x, v),
            Expr::Pair(a, b) => {
                eval_absent(p, f, env, *a, x, v);
                eval_absent(p, f, env, *b, x, v);
            },
            Expr::Builtin(_, es) => eval_args_absent(p, f, env, es, 0, x, v),
            Expr::Call(_, es) => eval_args_absent(p, f, env, es, 0, x, v),
            Expr::Let(y, a, b) => {
                eval_absent(p, f, env, *a, x, v);
                match eval(p, f, env, *a) {
                    Res::Done(va) => {
                        assert(env1.insert(y, va) =~= env.insert(y, va).insert(x, v));
                        eval_absent(p, f, env.insert(y, va), *b, x, v);
                    },
                    _ => {},
                }
            },
            Expr::If(c, a, b) => {
                eval_absent(p, f, env, *c, x, v);
                eval_absent(p, f, env, *a, x, v);
                eval_absent(p, f, env, *b, x, v);
            },
            Expr::Fold(xs, init, acc, item, body) => {
                eval_absent(p, f, env, *xs, x, v);
                eval_absent(p, f, env, *init, x, v);
                match (eval(p, f, env, *xs), eval(p, f, env, *init)) {
                    (Res::Done(Val::List(s)), Res::Done(v0)) => eval_fold_absent(
                        p,
                        f,
                        env,
                        acc,
                        item,
                        *body,
                        s,
                        0,
                        v0,
                        x,
                        v,
                    ),
                    _ => {},
                }
            },
            Expr::Match(m, nb, y, sm) => {
                eval_absent(p, f, env, *m, x, v);
                eval_absent(p, f, env, *nb, x, v);
                match eval(p, f, env, *m) {
                    Res::Done(Val::Some(w)) => {
                        assert(env1.insert(y, *w) =~= env.insert(y, *w).insert(x, v));
                        eval_absent(p, f, env.insert(y, *w), *sm, x, v);
                    },
                    _ => {},
                }
            },
            Expr::Inj(_, _, _, a) => eval_absent(p, f, env, *a, x, v),
            Expr::MatchR(m, y, a, z, b) => {
                eval_absent(p, f, env, *m, x, v);
                match eval(p, f, env, *m) {
                    Res::Done(Val::Ok(w)) => {
                        assert(env1.insert(y, *w) =~= env.insert(y, *w).insert(x, v));
                        eval_absent(p, f, env.insert(y, *w), *a, x, v);
                    },
                    Res::Done(Val::Err(w)) => {
                        assert(env1.insert(z, *w) =~= env.insert(z, *w).insert(x, v));
                        eval_absent(p, f, env.insert(z, *w), *b, x, v);
                    },
                    _ => {},
                }
            },
            _ => {},
        }
    }
}

pub proof fn eval_args_absent(p: Prog, n: nat, env: Map<nat, Val>, es: Seq<Expr>, i: nat, x: nat, v: Val)
    requires
        absent_args(x, es, i),
    ensures
        eval_args(p, n, env.insert(x, v), es, i) == eval_args(p, n, env, es, i),
    decreases n,
{
    if n > 0 && i < es.len() {
        let f = (n - 1) as nat;
        eval_absent(p, f, env, es[i as int], x, v);
        eval_args_absent(p, f, env, es, i + 1, x, v);
    }
}

pub proof fn eval_fold_absent(
    p: Prog,
    n: nat,
    env: Map<nat, Val>,
    acc: nat,
    item: nat,
    body: Expr,
    items: Seq<Val>,
    j: nat,
    a: Val,
    x: nat,
    v: Val,
)
    requires
        absent(x, body),
        acc != x,
        item != x,
    ensures
        eval_fold(p, n, env.insert(x, v), acc, item, body, items, j, a) == eval_fold(
            p,
            n,
            env,
            acc,
            item,
            body,
            items,
            j,
            a,
        ),
    decreases n,
{
    if n > 0 && j < items.len() {
        let f = (n - 1) as nat;
        let env2 = env.insert(acc, a).insert(item, items[j as int]);
        assert(env.insert(x, v).insert(acc, a).insert(item, items[j as int]) =~= env2.insert(x, v));
        eval_absent(p, f, env2, body, x, v);
        match eval(p, f, env2, body) {
            Res::Done(w) => eval_fold_absent(p, f, env, acc, item, body, items, j + 1, w, x, v),
            _ => {},
        }
    }
}

/// x が e に現れなければ、型の文脈に x を加えても型は変わらない。
pub proof fn ty_absent(p: Prog, r: nat, ctx: Map<nat, Ty>, e: Expr, x: nat, t: Ty)
    requires
        absent(x, e),
    ensures
        ty_expr(p, r, ctx.insert(x, t), e) == ty_expr(p, r, ctx, e),
    decreases e, 0nat,
{
    let c1 = ctx.insert(x, t);
    match e {
        Expr::Var(y) => {
            assert(c1.contains_key(y) == ctx.contains_key(y));
            if ctx.contains_key(y) {
                assert(c1[y] == ctx[y]);
            }
        },
        Expr::List(_, es) => ty_args_absent(p, r, ctx, es, 0, x, t),
        Expr::Some(a) => ty_absent(p, r, ctx, *a, x, t),
        Expr::Pair(a, b) => {
            ty_absent(p, r, ctx, *a, x, t);
            ty_absent(p, r, ctx, *b, x, t);
        },
        Expr::Builtin(_, es) => ty_args_absent(p, r, ctx, es, 0, x, t),
        Expr::Call(_, es) => ty_args_absent(p, r, ctx, es, 0, x, t),
        Expr::Let(y, a, b) => {
            ty_absent(p, r, ctx, *a, x, t);
            match ty_expr(p, r, ctx, *a) {
                Some(ta) => {
                    assert(c1.insert(y, ta) =~= ctx.insert(y, ta).insert(x, t));
                    ty_absent(p, r, ctx.insert(y, ta), *b, x, t);
                },
                None => {},
            }
        },
        Expr::If(c, a, b) => {
            ty_absent(p, r, ctx, *c, x, t);
            ty_absent(p, r, ctx, *a, x, t);
            ty_absent(p, r, ctx, *b, x, t);
        },
        Expr::Fold(xs, init, acc, item, body) => {
            ty_absent(p, r, ctx, *xs, x, t);
            ty_absent(p, r, ctx, *init, x, t);
            match (ty_expr(p, r, ctx, *xs), ty_expr(p, r, ctx, *init)) {
                (Some(tx), Some(ta)) => {
                    if tx is List {
                        let c2 = ctx.insert(acc, ta).insert(item, *tx->List_0);
                        assert(c1.insert(acc, ta).insert(item, *tx->List_0) =~= c2.insert(x, t));
                        ty_absent(p, r, c2, *body, x, t);
                    }
                },
                _ => {},
            }
        },
        Expr::Match(m, nb, y, sm) => {
            ty_absent(p, r, ctx, *m, x, t);
            ty_absent(p, r, ctx, *nb, x, t);
            match ty_expr(p, r, ctx, *m) {
                Some(tm) => {
                    if tm is Option {
                        let te = *tm->Option_0;
                        assert(c1.insert(y, te) =~= ctx.insert(y, te).insert(x, t));
                        ty_absent(p, r, ctx.insert(y, te), *sm, x, t);
                    }
                },
                None => {},
            }
        },
        Expr::Inj(_, _, _, a) => ty_absent(p, r, ctx, *a, x, t),
        Expr::MatchR(m, y, a, z, b) => {
            ty_absent(p, r, ctx, *m, x, t);
            match ty_expr(p, r, ctx, *m) {
                Some(tm) => {
                    if tm is Result {
                        let tl = *tm->Result_0;
                        let tr = *tm->Result_1;
                        assert(c1.insert(y, tl) =~= ctx.insert(y, tl).insert(x, t));
                        assert(c1.insert(z, tr) =~= ctx.insert(z, tr).insert(x, t));
                        ty_absent(p, r, ctx.insert(y, tl), *a, x, t);
                        ty_absent(p, r, ctx.insert(z, tr), *b, x, t);
                    }
                },
                None => {},
            }
        },
        _ => {},
    }
}

pub proof fn ty_args_absent(p: Prog, r: nat, ctx: Map<nat, Ty>, es: Seq<Expr>, i: nat, x: nat, t: Ty)
    requires
        absent_args(x, es, i),
    ensures
        ty_args(p, r, ctx.insert(x, t), es, i) == ty_args(p, r, ctx, es, i),
    decreases es, es.len() - i,
{
    if i < es.len() {
        ty_absent(p, r, ctx, es[i as int], x, t);
        ty_args_absent(p, r, ctx, es, i + 1, x, t);
    }
}

/// `eval_absent` の燃料に依らない形。
proof fn evals_absent(p: Prog, env: Map<nat, Val>, e: Expr, x: nat, v: Val, w: Val)
    requires
        absent(x, e),
    ensures
        evals_to(p, env.insert(x, v), e, w) <==> evals_to(p, env, e, w),
{
    if evals_to(p, env.insert(x, v), e, w) {
        let n = choose|n: nat| #[trigger] eval(p, n, env.insert(x, v), e) == Res::Done(w);
        eval_absent(p, n, env, e, x, v);
        assert(eval(p, n, env, e) == Res::Done(w));
    }
    if evals_to(p, env, e, w) {
        let n = choose|n: nat| #[trigger] eval(p, n, env, e) == Res::Done(w);
        eval_absent(p, n, env, e, x, v);
        assert(eval(p, n, env.insert(x, v), e) == Res::Done(w));
    }
}

// ------------------------------------------------------------------ 更新 `R { ..., ..base }`

/// 更新の型：base が展開後のレコード型を持ち、書いた field の式が field の型を持ち、x が書いた式に現れなければ、
/// 展開は展開後のレコード型を持つ。
pub proof fn rupdate_type(
    p: Prog,
    r: nat,
    ctx: Map<nat, Ty>,
    upd: Seq<Option<Expr>>,
    base: Expr,
    x: nat,
    ts: Seq<Ty>,
)
    requires
        ty_expr(p, r, ctx, base) == Some(rty(ts)),
        upd.len() == ts.len(),
        ts.len() >= 1,
        forall|k: int|
            0 <= k < upd.len() && (#[trigger] upd[k]) is Some ==> absent(x, upd[k]->Some_0) && ty_expr(
                p,
                r,
                ctx,
                upd[k]->Some_0,
            ) == Some(ts[k]),
    ensures
        ty_expr(p, r, ctx, rupdate(upd, base, x)) == Some(rty(ts)),
{
    if base is Var || nmissing(upd) <= 1 {
        let fs = fill(upd, base);
        assert forall|k: int| 0 <= k < fs.len() implies ty_expr(p, r, ctx, #[trigger] fs[k]) == Some(ts[k]) by {
            if upd[k] is None {
                rfield_type(p, r, ctx, base, ts, k as nat);
            }
        }
        rbuild_type(p, r, ctx, fs, ts);
    } else {
        let xv = Expr::Var(x);
        let c1 = ctx.insert(x, rty(ts));
        let fs = fill(upd, xv);
        assert(ty_expr(p, r, c1, xv) == Some(rty(ts)));
        assert forall|k: int| 0 <= k < fs.len() implies ty_expr(p, r, c1, #[trigger] fs[k]) == Some(ts[k]) by {
            match upd[k] {
                Some(e) => ty_absent(p, r, ctx, e, x, rty(ts)),
                None => rfield_type(p, r, c1, xv, ts, k as nat),
            }
        }
        rbuild_type(p, r, c1, fs, ts);
    }
}

/// 更新の評価：base が型の付いた値 vb を持ち、列 vs が更新の意味なら、展開は vs の展開を持つ。
proof fn rupdate_fwd(
    p: Prog,
    env: Map<nat, Val>,
    upd: Seq<Option<Expr>>,
    base: Expr,
    x: nat,
    ts: Seq<Ty>,
    vb: Val,
    vs: Seq<Val>,
)
    requires
        upd.len() == ts.len(),
        ts.len() >= 1,
        forall|k: int| 0 <= k < upd.len() && (#[trigger] upd[k]) is Some ==> absent(x, upd[k]->Some_0),
        evals_to(p, env, base, vb),
        val_type(vb, rty(ts)),
        update_to(p, env, upd, vb, vs),
    ensures
        evals_to(p, env, rupdate(upd, base, x), rval(vs)),
{
    let n = upd.len();
    if base is Var || nmissing(upd) <= 1 {
        let fs = fill(upd, base);
        assert forall|k: int| 0 <= k < fs.len() implies evals_to(p, env, #[trigger] fs[k], vs[k]) by {
            assert(slot_to(p, env, upd[k], rview(vb, n)[k], vs[k]));
            if upd[k] is None {
                rfield_fwd(p, env, base, vb, ts, k as nat);
            }
        }
        rbuild_fwd(p, env, fs, vs);
    } else {
        let xv = Expr::Var(x);
        let env1 = env.insert(x, vb);
        let fs = fill(upd, xv);
        var_to(p, env, x, vb);
        assert forall|k: int| 0 <= k < fs.len() implies evals_to(p, env1, #[trigger] fs[k], vs[k]) by {
            assert(slot_to(p, env, upd[k], rview(vb, n)[k], vs[k]));
            match upd[k] {
                Some(e) => evals_absent(p, env, e, x, vb, vs[k]),
                None => rfield_fwd(p, env1, xv, vb, ts, k as nat),
            }
        }
        rbuild_fwd(p, env1, fs, vs);
        bs_let(p, env, x, base, rbuild(fs), vb, rval(vs));
    }
}

/// 更新の評価の逆：展開が値 w を持てば、base は値 vb を持ち、w は更新の意味の列 vs の展開。
proof fn rupdate_inv(
    p: Prog,
    env: Map<nat, Val>,
    upd: Seq<Option<Expr>>,
    base: Expr,
    x: nat,
    w: Val,
) -> (r: (Val, Seq<Val>))
    requires
        upd.len() >= 1,
        forall|k: int| 0 <= k < upd.len() && (#[trigger] upd[k]) is Some ==> absent(x, upd[k]->Some_0),
        nmissing(upd) > 0 || exists|vb: Val| #[trigger] evals_to(p, env, base, vb),
        evals_to(p, env, rupdate(upd, base, x), w),
    ensures
        evals_to(p, env, base, r.0),
        update_to(p, env, upd, r.0, r.1),
        w == rval(r.1),
{
    let n = upd.len();
    if base is Var || nmissing(upd) <= 1 {
        let fs = fill(upd, base);
        let vs = rbuild_inv(p, env, fs, w);
        let vb = if nmissing(upd) > 0 {
            let k0 = nmissing_pos(upd);
            assert(evals_to(p, env, fs[k0], vs[k0]));
            rfield_inv(p, env, base, k0 as nat, n, vs[k0])
        } else {
            choose|vb: Val| #[trigger] evals_to(p, env, base, vb)
        };
        assert(evals_to(p, env, base, vb));
        assert forall|k: int| 0 <= k < n implies slot_to(p, env, #[trigger] upd[k], rview(vb, n)[k], vs[k]) by {
            assert(evals_to(p, env, fs[k], vs[k]));
            if upd[k] is None {
                let vk = rfield_inv(p, env, base, k as nat, n, vs[k]);
                evals_unique(p, env, base, vk, vb);
            }
        }
        (vb, vs)
    } else {
        let xv = Expr::Var(x);
        let fs = fill(upd, xv);
        let vb = let_inv(p, env, x, base, rbuild(fs), w);
        let env1 = env.insert(x, vb);
        let vs = rbuild_inv(p, env1, fs, w);
        var_to(p, env, x, vb);
        assert forall|k: int| 0 <= k < n implies slot_to(p, env, #[trigger] upd[k], rview(vb, n)[k], vs[k]) by {
            assert(evals_to(p, env1, fs[k], vs[k]));
            match upd[k] {
                Some(e) => evals_absent(p, env, e, x, vb, vs[k]),
                None => {
                    let vk = rfield_inv(p, env1, xv, k as nat, n, vs[k]);
                    evals_unique(p, env1, xv, vk, vb);
                },
            }
        }
        (vb, vs)
    }
}

/// 更新の意味の保存：base が展開後のレコード型を持ち、x が書いた式に現れないとき、展開が値 w を持つことと、
/// base が値 vb を持ち、書いた field を書いた式の値に、残りを vb の field にした列の展開が w であることは同値。
/// すべての field を書いたときは展開が base を捨てるので、その場合だけ base が値を持つことを前提にする。
pub proof fn rupdate_meaning(
    p: Prog,
    r: nat,
    ctx: Map<nat, Ty>,
    env: Map<nat, Val>,
    upd: Seq<Option<Expr>>,
    base: Expr,
    x: nat,
    ts: Seq<Ty>,
    w: Val,
)
    requires
        wf(p),
        env_ok(env, ctx),
        ty_expr(p, r, ctx, base) == Some(rty(ts)),
        upd.len() == ts.len(),
        ts.len() >= 1,
        forall|k: int| 0 <= k < upd.len() && (#[trigger] upd[k]) is Some ==> absent(x, upd[k]->Some_0),
        nmissing(upd) > 0 || exists|vb: Val| #[trigger] evals_to(p, env, base, vb),
    ensures
        evals_to(p, env, rupdate(upd, base, x), w) <==> exists|vb: Val, vs: Seq<Val>|
            evals_to(p, env, base, vb) && #[trigger] update_to(p, env, upd, vb, vs) && w == rval(vs),
{
    if evals_to(p, env, rupdate(upd, base, x), w) {
        let (vb, vs) = rupdate_inv(p, env, upd, base, x, w);
    }
    if exists|vb: Val, vs: Seq<Val>| evals_to(p, env, base, vb) && #[trigger] update_to(p, env, upd, vb, vs) && w == rval(vs) {
        let (vb, vs) = choose|vb: Val, vs: Seq<Val>|
            evals_to(p, env, base, vb) && #[trigger] update_to(p, env, upd, vb, vs) && w == rval(vs);
        let m = choose|m: nat| #[trigger] eval(p, m, env, base) == Res::Done(vb);
        sound(p, m, r, ctx, env, base, vb);
        rupdate_fwd(p, env, upd, base, x, ts, vb, vs);
    }
}

// ------------------------------------------------------------------ モデルの確認

/// 3 個の field での形（records.rs の出力と同じ）：型、参照、二つを書かない更新（let）、すべてを書いた更新
/// （base が消える）。
pub proof fn example_shapes(a: Expr, b: Expr, c: Expr, base: Expr, x: nat)
    requires
        !(base is Var),
    ensures
        rty(seq![Ty::Int, Ty::Bool, Ty::Unit]) == Ty::Pair(
            Box::new(Ty::Int),
            Box::new(Ty::Pair(Box::new(Ty::Bool), Box::new(Ty::Unit))),
        ),
        rfield(a, 1, 3) == Expr::Builtin(Builtin::Fst, seq![Expr::Builtin(Builtin::Snd, seq![a])]),
        rfield(a, 2, 3) == Expr::Builtin(Builtin::Snd, seq![Expr::Builtin(Builtin::Snd, seq![a])]),
        rupdate(seq![Some(a), None, None], base, x) == Expr::Let(
            x,
            Box::new(base),
            Box::new(rbuild(seq![a, rfield(Expr::Var(x), 1, 3), rfield(Expr::Var(x), 2, 3)])),
        ),
        rupdate(seq![Some(a), Some(b), Some(c)], base, x) == rbuild(seq![a, b, c]),
{
    let ts = seq![Ty::Int, Ty::Bool, Ty::Unit];
    assert(ts.drop_first() =~= seq![Ty::Bool, Ty::Unit]);
    assert(ts.drop_first().drop_first() =~= seq![Ty::Unit]);
    reveal_with_fuel(rty, 3);
    reveal_with_fuel(snds, 3);
    reveal_with_fuel(nmissing, 4);
    let u1 = seq![Some(a), None, None];
    assert(u1.drop_last() =~= seq![Some(a), None]);
    assert(u1.drop_last().drop_last() =~= seq![Some(a)]);
    assert(u1.drop_last().drop_last().drop_last() =~= Seq::<Option<Expr>>::empty());
    assert(nmissing(u1) == 2);
    assert(fill(u1, Expr::Var(x)) =~= seq![a, rfield(Expr::Var(x), 1, 3), rfield(Expr::Var(x), 2, 3)]);
    let u2 = seq![Some(a), Some(b), Some(c)];
    assert(u2.drop_last() =~= seq![Some(a), Some(b)]);
    assert(u2.drop_last().drop_last() =~= seq![Some(a)]);
    assert(u2.drop_last().drop_last().drop_last() =~= Seq::<Option<Expr>>::empty());
    assert(nmissing(u2) == 0);
    assert(fill(u2, base) =~= seq![a, b, c]);
}

} // verus!
