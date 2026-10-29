//! v1.1 のレコードの書換えの計画（DECISION-43）。records.rs の意味を決める三つの判断を、検証済みの exec に替える。
//!
//! records.rs の木の走査、型の展開、名前から整数への対応づけ（intern）、pair の組み立ては接着のまま（検証していない）。
//! ここで決めるのは records.rs が使う次の三つ：
//! - `place_e`：字段の名前の位置。spec は records_meaning の `pos`（名前の列での最初の位置）。`pos_at` と `pos_none` で一致を示す。
//! - `field_steps_e`：字段の参照 `e.f` の fst／snd の並び（先頭から e に適用する）。`apply_steps` で適用すると
//!   `tfield` になり、`tfield` は records_proof の `rfield`（印つきなら先頭に snd）。値の意味は `rfield_eval`。
//! - `record_mode_e`：構築の拒否（base がなく書いていない字段がある、base があるのに書いていない字段がない）と、
//!   base を let で一度だけ束縛するか。spec は records_proof の `rrecord` の拒否の場合分けと、`rupdate` の束縛の規則（`base is Var || nmissing <= 1` なら展開、それ以外は let）。`mode_none_rrecord` と `mode_some_rrecord` が両者の一致を示す。

use crate::ir::*;
use crate::records_exec::*;
use crate::records_proof::*;
use crate::spec::*;
use vstd::prelude::*;

verus! {

// ------------------------------------------------------------------ 字段の位置

/// 名前の番号の列を、`pos` が読む形（nat の列）にする。
pub open spec fn view_names(decl: Seq<usize>) -> Seq<nat> {
    Seq::new(decl.len(), |k: int| decl[k] as nat)
}

/// 宣言の名前の列に字段 f がなければ、`pos` は None。
proof fn pos_none(decl: Seq<nat>, f: nat)
    requires
        forall|j: int| 0 <= j < decl.len() ==> decl[j] != f,
    ensures
        crate::records_meaning::pos(decl, f) is None,
    decreases decl.len(),
{
    if decl.len() > 0 {
        assert(decl.drop_first().len() == decl.len() - 1);
        assert forall|j: int| 0 <= j < decl.drop_first().len() implies decl.drop_first()[j] != f by {
            assert(decl.drop_first()[j] == decl[j + 1]);
        }
        pos_none(decl.drop_first(), f);
    }
}

/// 宣言の名前の列で、字段 k が f で、それより前に f がなければ、`pos` は k。
proof fn pos_at(decl: Seq<nat>, f: nat, k: nat)
    requires
        k < decl.len(),
        decl[k as int] == f,
        forall|j: int| 0 <= j < k ==> decl[j] != f,
    ensures
        crate::records_meaning::pos(decl, f) == Some(k),
    decreases k,
{
    if k > 0 {
        assert(decl[0] != f);
        assert(decl.drop_first().len() == decl.len() - 1);
        assert(decl.drop_first()[(k - 1) as int] == decl[k as int]);
        assert forall|j: int| 0 <= j < k - 1 implies decl.drop_first()[j] != f by {
            assert(decl.drop_first()[j] == decl[j + 1]);
        }
        pos_at(decl.drop_first(), f, (k - 1) as nat);
    }
}

/// 字段 f の位置（宣言の名前の列での最初の位置）。`pos` と同じ答えを返す。
pub fn place_e(decl: &Vec<usize>, f: usize) -> (r: Option<usize>)
    ensures
        r matches Some(k) ==> crate::records_meaning::pos(view_names(decl@), f as nat) == Some(k as nat),
        r is None ==> crate::records_meaning::pos(view_names(decl@), f as nat) is None,
{
    let mut i: usize = 0;
    while i < decl.len()
        invariant
            i <= decl.len(),
            forall|j: int| 0 <= j < i ==> view_names(decl@)[j] != f as nat,
        decreases decl.len() - i,
    {
        if decl[i] == f {
            proof {
                assert(view_names(decl@)[i as int] == f as nat);
                pos_at(view_names(decl@), f as nat, i as nat);
            }
            return Some(i);
        }
        i = i + 1;
    }
    proof {
        assert forall|j: int| 0 <= j < view_names(decl@).len() implies view_names(decl@)[j] != f as nat by {
            assert(view_names(decl@)[j] == decl@[j] as nat);
        }
        pos_none(view_names(decl@), f as nat);
    }
    None
}

// ------------------------------------------------------------------ 字段の参照の計画

/// 一手：true は snd、false は fst。`apply_steps` の先頭から適用する。
pub open spec fn step_e(e: Expr, b: bool) -> Expr {
    if b {
        Expr::Builtin(Builtin::Snd, seq![e])
    } else {
        Expr::Builtin(Builtin::Fst, seq![e])
    }
}

/// steps を先頭から e に適用する。
pub open spec fn apply_steps(e: Expr, steps: Seq<bool>) -> Expr
    decreases steps.len(),
{
    if steps.len() == 0 {
        e
    } else {
        apply_steps(step_e(e, steps[0]), steps.drop_first())
    }
}

/// 字段の参照の計画：印つきなら先頭に snd、次に i 回の snd、最後に（i + 1 < n なら）fst。records.rs の `lower_expr` の並び。
pub open spec fn field_steps(tagged: bool, i: nat, n: nat) -> Seq<bool> {
    (if tagged { seq![true] } else { Seq::<bool>::empty() }) + Seq::new(i, |k: int| true) + (if i + 1 < n {
        seq![false]
    } else {
        Seq::<bool>::empty()
    })
}

/// 計画の結果：印つきなら先に snd を当ててから、字段の参照 rfield を当てる。
pub open spec fn tfield(e: Expr, tagged: bool, i: nat, n: nat) -> Expr {
    rfield(
        if tagged {
            Expr::Builtin(Builtin::Snd, seq![e])
        } else {
            e
        },
        i,
        n,
    )
}

/// snd を k 回当てる計画は、records_proof の `snds` と同じ。
proof fn steps_snds(e: Expr, k: nat)
    ensures
        apply_steps(e, Seq::new(k, |j: int| true)) == snds(e, k),
    decreases k,
{
    reveal_with_fuel(apply_steps, 1);
    if k > 0 {
        let s = Seq::new(k, |j: int| true);
        assert(s.len() == k);
        assert(s[0] == true);
        assert(s.drop_first() =~= Seq::new((k - 1) as nat, |j: int| true));
        steps_snds(step_e(e, true), (k - 1) as nat);
    }
}

/// 計画の連結：s1 を当ててから s2 を当てるのは、s1 + s2 を当てるのと同じ。
proof fn apply_concat(e: Expr, s1: Seq<bool>, s2: Seq<bool>)
    ensures
        apply_steps(e, s1 + s2) == apply_steps(apply_steps(e, s1), s2),
    decreases s1.len(),
{
    if s1.len() > 0 {
        assert((s1 + s2)[0] == s1[0]);
        assert((s1 + s2).drop_first() =~= s1.drop_first() + s2);
        apply_concat(step_e(e, s1[0]), s1.drop_first(), s2);
    }
}

/// 字段の参照の計画を当てると、tfield になる。
pub proof fn field_steps_apply(e: Expr, tagged: bool, i: nat, n: nat)
    ensures
        apply_steps(e, field_steps(tagged, i, n)) == tfield(e, tagged, i, n),
{
    reveal_with_fuel(apply_steps, 3);
    let t = if tagged { seq![true] } else { Seq::<bool>::empty() };
    let s = Seq::new(i, |k: int| true);
    let f = if i + 1 < n { seq![false] } else { Seq::<bool>::empty() };
    assert(field_steps(tagged, i, n) =~= t + s + f);
    apply_concat(e, t + s, f);
    apply_concat(e, t, s);
    if tagged {
        assert(t =~= seq![true]);
        assert(t.drop_first() =~= Seq::<bool>::empty());
        assert(apply_steps(e, t) == step_e(e, true));
    } else {
        assert(t =~= Seq::<bool>::empty());
        assert(apply_steps(e, t) == e);
    }
    let x = apply_steps(e, t);
    steps_snds(x, i);
    assert(apply_steps(e, t + s) == snds(x, i));
    if i + 1 < n {
        assert(f =~= seq![false]);
        assert(f.drop_first() =~= Seq::<bool>::empty());
        assert(apply_steps(snds(x, i), f) == step_e(snds(x, i), false));
    } else {
        assert(f =~= Seq::<bool>::empty());
        assert(apply_steps(snds(x, i), f) == snds(x, i));
    }
}

/// 字段の参照の計画（records.rs の `lower_expr` の fst／snd の並び）を exec で作る。
pub fn field_steps_e(tagged: bool, i: usize, n: usize) -> (r: Vec<bool>)
    requires
        i < n,
    ensures
        r@ == field_steps(tagged, i as nat, n as nat),
{
    let ghost t: Seq<bool> = if tagged { seq![true] } else { Seq::<bool>::empty() };
    let mut r: Vec<bool> = Vec::new();
    if tagged {
        r.push(true);
        proof {
            assert(r@ =~= seq![true]);
        }
    } else {
        proof {
            assert(r@ =~= Seq::<bool>::empty());
        }
    }
    proof {
        assert(r@ =~= t);
    }
    let mut k: usize = 0;
    while k < i
        invariant
            k <= i,
            i < n,
            r@ =~= t + Seq::new(k as nat, |j: int| true),
        decreases i - k,
    {
        proof {
            assert(Seq::new((k + 1) as nat, |j: int| true) =~= Seq::new(k as nat, |j: int| true).push(true));
            assert((t + Seq::new(k as nat, |j: int| true)).push(true) =~= t + Seq::new((k + 1) as nat, |j: int| true));
        }
        r.push(true);
        k = k + 1;
    }
    proof {
        assert(k == i);
        assert(Seq::new(i as nat, |j: int| true) =~= Seq::new(k as nat, |j: int| true));
    }
    if i + 1 < n {
        r.push(false);
        proof {
            assert(r@ =~= (t + Seq::new(i as nat, |j: int| true)).push(false));
            assert((t + Seq::new(i as nat, |j: int| true)).push(false) =~= t + Seq::new(i as nat, |j: int| true) + seq![false]);
        }
    } else {
        proof {
            assert(r@ =~= t + Seq::new(i as nat, |j: int| true) + Seq::<bool>::empty());
        }
    }
    proof {
        assert(field_steps(tagged, i as nat, n as nat) =~= r@);
    }
    r
}

// ------------------------------------------------------------------ 構築の計画

/// 構築の計画。
#[derive(PartialEq, Eq)]
pub enum RecMode {
    /// base がなく、書いていない字段がある（E-RECORD-MISSING-FIELD）
    Missing,
    /// base があり、書いていない字段がない（E-RECORD-BASE-REDUNDANT）
    BaseRedundant,
    /// base がなく、字段がすべて書いてある：pair の入れ子をそのまま作る
    Plain,
    /// base があり、書いていない字段が一つ以下か、base が変数：base を各参照に写す
    Inline,
    /// base があり、書いていない字段が二つ以上で、base が変数でない：base を let で一度だけ束縛する
    Bind,
}

/// 書いていない字段の数（given の false の数）。
pub open spec fn nmiss(given: Seq<bool>) -> nat
    decreases given.len(),
{
    if given.len() == 0 {
        0
    } else {
        nmiss(given.drop_last()) + if given.last() {
            0nat
        } else {
            1nat
        }
    }
}

/// 構築の計画の spec：書いていない字段の数 m と、base の有無、base が変数か。
pub open spec fn mode_spec(m: nat, has_base: bool, base_var: bool) -> RecMode {
    if !has_base {
        if m > 0 {
            RecMode::Missing
        } else {
            RecMode::Plain
        }
    } else if m == 0 {
        RecMode::BaseRedundant
    } else if base_var || m <= 1 {
        RecMode::Inline
    } else {
        RecMode::Bind
    }
}

/// 書いていない字段の数を数える（nmiss の実行）。
fn count_missing(given: &Vec<bool>) -> (m: usize)
    ensures
        m as nat == nmiss(given@),
{
    let ghost g = given@;
    let mut m: usize = 0;
    let mut i: usize = 0;
    while i < given.len()
        invariant
            i <= given.len(),
            g == given@,
            m <= i,
            m as nat == nmiss(g.subrange(0, i as int)),
        decreases given.len() - i,
    {
        proof {
            let s = g.subrange(0, i as int + 1);
            assert(s.drop_last() =~= g.subrange(0, i as int));
            assert(s.last() == g[i as int]);
        }
        if !given[i] {
            m = m + 1;
        }
        i = i + 1;
    }
    proof {
        assert(g.subrange(0, g.len() as int) =~= g);
    }
    m
}

/// 構築の計画を決める。拒否と、base を束縛するかどうかを返す（mode_spec）。
pub fn record_mode_e(given: &Vec<bool>, has_base: bool, base_var: bool) -> (r: RecMode)
    ensures
        r == mode_spec(nmiss(given@), has_base, base_var),
{
    let m = count_missing(given);
    if !has_base {
        if m > 0 {
            RecMode::Missing
        } else {
            RecMode::Plain
        }
    } else if m == 0 {
        RecMode::BaseRedundant
    } else if base_var || m <= 1 {
        RecMode::Inline
    } else {
        RecMode::Bind
    }
}

// ------------------------------------------------------------------ 計画と rrecord の一致

/// 書いた字段の有無（upd の Some の列）。
pub open spec fn flags_of(upd: Seq<Option<Expr>>) -> Seq<bool> {
    Seq::new(upd.len(), |k: int| upd[k] is Some)
}

/// 有無の列で数えた書いていない字段の数は、nmissing と同じ。
proof fn nmiss_flags(upd: Seq<Option<Expr>>)
    ensures
        nmiss(flags_of(upd)) == nmissing(upd),
    decreases upd.len(),
{
    if upd.len() > 0 {
        let f = flags_of(upd);
        assert(f.len() == upd.len());
        assert(f.drop_last() =~= flags_of(upd.drop_last()));
        assert(f.last() == (upd.last() is Some));
        nmiss_flags(upd.drop_last());
    }
}

/// base がない構築：計画の拒否は rrecord の拒否（Missing）と同じ場合で、それ以外は Plain。
pub proof fn mode_none_rrecord(upd: Seq<Option<Expr>>, x: nat)
    ensures
        nmissing(upd) > 0 ==> mode_spec(nmiss(flags_of(upd)), false, false) == RecMode::Missing && rrecord(
            upd,
            None,
            x,
        ) is Err,
        nmissing(upd) == 0 ==> mode_spec(nmiss(flags_of(upd)), false, false) == RecMode::Plain && rrecord(
            upd,
            None,
            x,
        ) is Ok,
{
    nmiss_flags(upd);
}

/// base がある構築：計画の拒否（BaseRedundant）は rrecord の拒否と同じ場合。受理のときは、base を let で束縛する
/// 計画（Bind）は rupdate が let を作る場合と同じ（base が変数でなく、書いていない字段が二つ以上）。
pub proof fn mode_some_rrecord(upd: Seq<Option<Expr>>, b: Expr, x: nat)
    ensures
        nmissing(upd) == 0 ==> mode_spec(nmiss(flags_of(upd)), true, b is Var) == RecMode::BaseRedundant && rrecord(
            upd,
            Some(b),
            x,
        ) is Err,
        nmissing(upd) > 0 ==> mode_spec(nmiss(flags_of(upd)), true, b is Var) != RecMode::BaseRedundant && rrecord(
            upd,
            Some(b),
            x,
        ) is Ok,
        mode_spec(nmiss(flags_of(upd)), true, b is Var) == RecMode::Bind ==> rupdate(upd, b, x) is Let,
{
    nmiss_flags(upd);
}

} // verus!
