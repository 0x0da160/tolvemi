//! 入力 JSON の spec の性質（§11.2 の 9）：型整合性、重複キー拒否、正準形の往復性。

use crate::bigint::*;
use crate::input::*;
use crate::json::*;
use crate::proof::*;
use crate::spec::*;
use vstd::prelude::*;

verus! {

// ------------------------------------------------------------------ キー

pub proof fn keys()
    ensures
        k_tag().len() == 3,
        k_value().len() == 5,
        k_left().len() == 4,
        k_right().len() == 5,
        k_items().len() == 5,
        k_value() != k_items(),
        t_some() != t_none(),
{
    assert(k_value()[0] == ('v' as u32));
    assert(k_items()[0] == ('i' as u32));
    assert(t_some()[0] == ('s' as u32));
    assert(t_none()[0] == ('n' as u32));
}

pub proof fn kpos_props(ks: Seq<Seq<u32>>, k: Seq<u32>, i: nat)
    ensures
        kpos(ks, k, i) <= ks.len() || kpos(ks, k, i) == ks.len(),
        i <= ks.len() ==> i <= kpos(ks, k, i),
        kpos(ks, k, i) < ks.len() ==> ks[kpos(ks, k, i) as int] == k,
    decreases ks.len() - i,
{
    if i < ks.len() && ks[i as int] != k {
        kpos_props(ks, k, i + 1);
    }
}

// ------------------------------------------------------------------ 型整合性と重複キー拒否

proof fn nodups_from_each(xs: Seq<J>, i: nat)
    requires
        forall|m: int| i <= m < xs.len() ==> nodup(#[trigger] xs[m]),
    ensures
        nodups(xs, i),
    decreases xs.len() - i,
{
    if i < xs.len() {
        nodups_from_each(xs, i + 1);
    }
}

pub proof fn jd_props(j: J, t: Ty)
    ensures
        jd(j, t) is Some ==> val_type(jd(j, t)->Some_0, t) && nodup(j),
    decreases j, 0nat,
{
    if let J::Obj(ks, vs) = j {
        if jd(j, t) is Some {
            let it = kpos(ks, k_tag(), 0);
            let iv = kpos(ks, k_value(), 0);
            let il = kpos(ks, k_left(), 0);
            let ir = kpos(ks, k_right(), 0);
            let ii = kpos(ks, k_items(), 0);
            kpos_props(ks, k_tag(), 0);
            kpos_props(ks, k_value(), 0);
            kpos_props(ks, k_left(), 0);
            kpos_props(ks, k_right(), 0);
            kpos_props(ks, k_items(), 0);
            keys();
            let g = vs[it as int]->Str_0;
            let r1 = seq![k_tag()];
            let r2v = seq![k_tag(), k_value()];
            let r2i = seq![k_tag(), k_items()];
            let r3 = seq![k_tag(), k_left(), k_right()];
            assert(r1[0] == k_tag() && r2v[0] == k_tag() && r2v[1] == k_value() && r2i[0] == k_tag() && r2i[1]
                == k_items() && r3[0] == k_tag() && r3[1] == k_left() && r3[2] == k_right());
            match t {
                Ty::Option(el) => {
                    if !(g == t_none() && only(ks, r1)) {
                        jd_props(vs[iv as int], *el);
                    }
                },
                Ty::Pair(ta, tb) => {
                    jd_props(vs[il as int], *ta);
                    jd_props(vs[ir as int], *tb);
                },
                Ty::List(el) => {
                    if let J::Arr(xs) = vs[ii as int] {
                        jds_props(xs, *el, 0);
                        let w = jds(xs, *el, 0)->Some_0;
                        val_type_list(w, *el);
                        assert(nodup(vs[ii as int]));
                    }
                },
                _ => {},
            }
            assert forall|m: int| 0 <= m < vs.len() implies nodup(#[trigger] vs[m]) by {
                if only(ks, r1) {
                    assert(kpos(ks, r1[0], 0) < ks.len());
                }
                if only(ks, r2v) {
                    assert(kpos(ks, r2v[0], 0) < ks.len());
                    assert(kpos(ks, r2v[1], 0) < ks.len());
                }
                if only(ks, r2i) {
                    assert(kpos(ks, r2i[0], 0) < ks.len());
                    assert(kpos(ks, r2i[1], 0) < ks.len());
                }
                if only(ks, r3) {
                    assert(kpos(ks, r3[0], 0) < ks.len());
                    assert(kpos(ks, r3[1], 0) < ks.len());
                    assert(kpos(ks, r3[2], 0) < ks.len());
                }
            }
            nodups_from_each(vs, 0);
        }
    }
}

pub proof fn jds_props(xs: Seq<J>, t: Ty, i: nat)
    ensures
        jds(xs, t, i) is Some ==> {
            let w = jds(xs, t, i)->Some_0;
            &&& i <= xs.len() ==> w.len() == xs.len() - i
            &&& forall|k: int| 0 <= k < w.len() ==> #[trigger] val_type(w[k], t)
            &&& nodups(xs, i)
        },
    decreases xs, xs.len() - i,
{
    if i < xs.len() {
        jd_props(xs[i as int], t);
        jds_props(xs, t, i + 1);
        if jds(xs, t, i) is Some {
            let w = jds(xs, t, i)->Some_0;
            let r = jds(xs, t, i + 1)->Some_0;
            assert forall|k: int| 0 <= k < w.len() implies #[trigger] val_type(w[k], t) by {
                if k > 0 {
                    assert(w[k] == r[k - 1]);
                }
            }
        }
    }
}

/// 型整合性：入力として受理した値は entry の入力型を持つ。
pub proof fn input_typed(s: Seq<char>, d: nat, t: Ty)
    ensures
        input_val(s, d, t) is Some ==> val_type(input_val(s, d, t)->Some_0, t),
{
    if let Some(j) = jparse(s, d) {
        jd_props(j, t);
    }
}

/// 重複キー拒否：受理した入力 JSON のどの object にも重複キーは無い。
pub proof fn input_nodup(s: Seq<char>, d: nat, t: Ty)
    ensures
        input_val(s, d, t) is Some ==> jparse(s, d) is Some && nodup(jparse(s, d)->Some_0),
{
    if let Some(j) = jparse(s, d) {
        jd_props(j, t);
    }
}

// ------------------------------------------------------------------ 正準形の往復性

/// 値の正準 JSON が表す木。
pub open spec fn jt(v: Val) -> J
    decreases v, 1nat,
{
    match v {
        Val::Int(n) => J::Obj(seq![k_tag(), k_value()], seq![J::Str(t_int()), J::Str(cs(int_dec(n)))]),
        Val::Bool(b) => J::Obj(seq![k_tag(), k_value()], seq![J::Str(t_bool()), J::Bool(b)]),
        Val::Unit => J::Obj(seq![k_tag()], seq![J::Str(t_unit())]),
        Val::None => J::Obj(seq![k_tag()], seq![J::Str(t_none())]),
        Val::Some(x) => J::Obj(seq![k_tag(), k_value()], seq![J::Str(t_some()), jt(*x)]),
        Val::Pair(a, b) => J::Obj(seq![k_tag(), k_left(), k_right()], seq![J::Str(t_pair()), jt(*a), jt(*b)]),
        Val::List(xs) => J::Obj(seq![k_tag(), k_items()], seq![J::Str(t_list()), J::Arr(jts(xs, 0))]),
    }
}

pub open spec fn jts(xs: Seq<Val>, i: nat) -> Seq<J>
    decreases xs, xs.len() - i,
{
    if i >= xs.len() {
        Seq::empty()
    } else {
        seq![jt(xs[i as int])] + jts(xs, i + 1)
    }
}

/// 正準 JSON の構造の入れ子の深さ（リストは object と配列の二段）。
pub open spec fn vdepth(v: Val) -> nat
    decreases v, 1nat,
{
    match v {
        Val::Some(x) => 1 + vdepth(*x),
        Val::Pair(a, b) => 1 + if vdepth(*a) >= vdepth(*b) {
            vdepth(*a)
        } else {
            vdepth(*b)
        },
        Val::List(xs) => 2 + maxd(xs, 0),
        _ => 1,
    }
}

pub open spec fn maxd(xs: Seq<Val>, i: nat) -> nat
    decreases xs, xs.len() - i,
{
    if i >= xs.len() {
        0
    } else {
        let a = vdepth(xs[i as int]);
        let b = maxd(xs, i + 1);
        if a >= b {
            a
        } else {
            b
        }
    }
}

proof fn maxd_ge(xs: Seq<Val>, i: nat, m: int)
    requires
        i <= m < xs.len(),
    ensures
        vdepth(xs[m]) <= maxd(xs, i),
    decreases xs.len() - i,
{
    if i < m {
        maxd_ge(xs, i + 1, m);
    }
}

/// s の位置 p から w が続く。
#[verifier::opaque]
pub open spec fn has(s: Seq<char>, p: int, w: Seq<char>) -> bool {
    &&& 0 <= p
    &&& p + w.len() <= s.len()
    &&& forall|k: int| 0 <= k < w.len() ==> s[(p + k) as int] == #[trigger] w[k]
}

proof fn has_at(s: Seq<char>, p: int, w: Seq<char>, k: int)
    requires
        has(s, p, w),
        0 <= k < w.len(),
    ensures
        s[p + k] == w[k],
        0 <= p,
        p + w.len() <= s.len(),
{
    reveal(has);
}

proof fn has_split(s: Seq<char>, p: int, x: Seq<char>, y: Seq<char>)
    requires
        has(s, p, x + y),
    ensures
        has(s, p, x),
        has(s, p + x.len(), y),
{
    reveal(has);
    assert forall|k: int| 0 <= k < x.len() implies s[(p + k) as int] == #[trigger] x[k] by {
        assert((x + y)[k] == x[k]);
    }
    assert forall|k: int| 0 <= k < y.len() implies s[(p + x.len() + k) as int] == #[trigger] y[k] by {
        assert((x + y)[x.len() + k] == y[k]);
    }
}

proof fn has_join(s: Seq<char>, p: int, x: Seq<char>, y: Seq<char>)
    requires
        has(s, p, x),
        has(s, p + x.len(), y),
    ensures
        has(s, p, x + y),
{
    reveal(has);
    assert forall|k: int| 0 <= k < (x + y).len() implies s[(p + k) as int] == #[trigger] (x + y)[k] by {
        if k < x.len() {
            assert(s[(p + k) as int] == x[k]);
        } else {
            assert(s[(p + x.len() + (k - x.len())) as int] == y[k - x.len()]);
        }
    }
}

pub open spec fn pc(c: char) -> bool {
    c != '"' && c != '\\' && (c as u32) >= 0x20
}

pub open spec fn plain(w: Seq<char>) -> bool {
    forall|k: int| 0 <= k < w.len() ==> pc(#[trigger] w[k])
}

pub open spec fn q() -> Seq<char> {
    seq!['"']
}

pub open spec fn qs(w: Seq<char>) -> Seq<char> {
    q() + w + q()
}

pub open spec fn hdr(w: Seq<char>) -> Seq<char> {
    q() + w + q() + seq![':']
}

/// 共通の先頭 `{"tag":"t"`。
pub open spec fn pre(t: Seq<char>) -> Seq<char> {
    seq!['{'] + hdr(c_tag()) + qs(t)
}

proof fn plain_tag()
    ensures
        plain(c_tag()),
{
    assert forall|k: int| 0 <= k < c_tag().len() implies pc(#[trigger] c_tag()[k]) by {}
}

proof fn plain_value()
    ensures
        plain(c_value()),
{
    assert forall|k: int| 0 <= k < c_value().len() implies pc(#[trigger] c_value()[k]) by {}
}

proof fn plain_left()
    ensures
        plain(c_left()),
{
    assert forall|k: int| 0 <= k < c_left().len() implies pc(#[trigger] c_left()[k]) by {}
}

proof fn plain_right()
    ensures
        plain(c_right()),
{
    assert forall|k: int| 0 <= k < c_right().len() implies pc(#[trigger] c_right()[k]) by {}
}

proof fn plain_items()
    ensures
        plain(c_items()),
{
    assert forall|k: int| 0 <= k < c_items().len() implies pc(#[trigger] c_items()[k]) by {}
}

proof fn plain_int()
    ensures
        plain(c_int()),
{
    assert forall|k: int| 0 <= k < c_int().len() implies pc(#[trigger] c_int()[k]) by {}
}

proof fn plain_bool()
    ensures
        plain(c_bool()),
{
    assert forall|k: int| 0 <= k < c_bool().len() implies pc(#[trigger] c_bool()[k]) by {}
}

proof fn plain_unit()
    ensures
        plain(c_unit()),
{
    assert forall|k: int| 0 <= k < c_unit().len() implies pc(#[trigger] c_unit()[k]) by {}
}

proof fn plain_none()
    ensures
        plain(c_none()),
{
    assert forall|k: int| 0 <= k < c_none().len() implies pc(#[trigger] c_none()[k]) by {}
}

proof fn plain_some()
    ensures
        plain(c_some()),
{
    assert forall|k: int| 0 <= k < c_some().len() implies pc(#[trigger] c_some()[k]) by {}
}

proof fn plain_pair()
    ensures
        plain(c_pair()),
{
    assert forall|k: int| 0 <= k < c_pair().len() implies pc(#[trigger] c_pair()[k]) by {}
}

proof fn plain_list()
    ensures
        plain(c_list()),
{
    assert forall|k: int| 0 <= k < c_list().len() implies pc(#[trigger] c_list()[k]) by {}
}

proof fn lay_int()
    ensures
        l_int1() == pre(c_int()) + seq![','] + hdr(c_value()) + q(),
        l_int2() == q() + seq!['}'],
{
    reveal(l_int1);
    reveal(l_int2);
    assert(l_int1() =~= pre(c_int()) + seq![','] + hdr(c_value()) + q());
    assert(l_int2() =~= q() + seq!['}']);
}

proof fn lay_bool()
    ensures
        l_true() == pre(c_bool()) + seq![','] + hdr(c_value()) + w_true() + seq!['}'],
        l_false() == pre(c_bool()) + seq![','] + hdr(c_value()) + w_false() + seq!['}'],
{
    reveal(l_true);
    reveal(l_false);
    assert(l_true() =~= pre(c_bool()) + seq![','] + hdr(c_value()) + w_true() + seq!['}']);
    assert(l_false() =~= pre(c_bool()) + seq![','] + hdr(c_value()) + w_false() + seq!['}']);
}

proof fn lay_unit()
    ensures
        l_unit() == pre(c_unit()) + seq!['}'],
        l_none() == pre(c_none()) + seq!['}'],
{
    reveal(l_unit);
    reveal(l_none);
    assert(l_unit() =~= pre(c_unit()) + seq!['}']);
    assert(l_none() =~= pre(c_none()) + seq!['}']);
}

proof fn lay_some()
    ensures
        l_some() == pre(c_some()) + seq![','] + hdr(c_value()),
        l_close() == seq!['}'],
{
    reveal(l_some);
    reveal(l_close);
    assert(l_some() =~= pre(c_some()) + seq![','] + hdr(c_value()));
    assert(l_close() =~= seq!['}']);
}

proof fn lay_pair()
    ensures
        l_pair1() == pre(c_pair()) + seq![','] + hdr(c_left()),
        l_pair2() == seq![','] + hdr(c_right()),
        l_close() == seq!['}'],
{
    reveal(l_pair1);
    reveal(l_pair2);
    reveal(l_close);
    assert(l_pair1() =~= pre(c_pair()) + seq![','] + hdr(c_left()));
    assert(l_pair2() =~= seq![','] + hdr(c_right()));
    assert(l_close() =~= seq!['}']);
}

proof fn lay_list()
    ensures
        l_list1() == pre(c_list()) + seq![','] + hdr(c_items()) + seq!['['],
        l_comma() == seq![','],
        l_list2() == seq![']', '}'],
{
    reveal(l_list1);
    reveal(l_comma);
    reveal(l_list2);
    assert(l_list1() =~= pre(c_list()) + seq![','] + hdr(c_items()) + seq!['[']);
    assert(l_comma() =~= seq![',']);
    assert(l_list2() =~= seq![']', '}']);
}

pub proof fn digit_code(d: int)
    requires
        0 <= d < 10,
    ensures
        digit(d) as u32 == 48 + d,
{
}

/// 自然数の十進表記：数字だけで、値が戻り、1 以上なら先頭は 0 でない。
proof fn nd_props(m: nat)
    ensures
        cs(nat_dec(m)).len() >= 1,
        cs(nat_dec(m)).len() == nat_dec(m).len(),
        forall|k: int| 0 <= k < nat_dec(m).len() ==> dig(#[trigger] nat_dec(m)[k] as u32),
        nv(cs(nat_dec(m))) == m,
        m >= 1 ==> cs(nat_dec(m))[0] != 48,
        m < 10 ==> nat_dec(m).len() == 1,
    decreases m,
{
    let x = cs(nat_dec(m));
    if m < 10 {
        digit_code(m as int);
        assert(x.len() == 1);
        assert(x.last() == digit(m as int) as u32);
        assert(x.drop_last() =~= Seq::<u32>::empty());
        assert(nv(x.drop_last()) == 0);
    } else {
        nd_props(m / 10);
        let y = nat_dec(m / 10);
        digit_code((m % 10) as int);
        assert(nat_dec(m) == y.push(digit((m % 10) as int)));
        assert(x.drop_last() =~= cs(y));
        assert(x.last() == digit((m % 10) as int) as u32);
        assert forall|k: int| 0 <= k < nat_dec(m).len() implies dig(#[trigger] nat_dec(m)[k] as u32) by {
            if k < y.len() {
                assert(nat_dec(m)[k] == y[k]);
            }
        }
        assert(x[0] == cs(y)[0]);
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod(m as int, 10);
        assert(nv(x) == nv(cs(y)) * 10 + (x.last() - 48) as nat);
        assert(nv(cs(y)) == m / 10);
        assert((m / 10) * 10 == 10 * (m / 10)) by (nonlinear_arith);
    }
}

proof fn int_dec_plain(n: int)
    ensures
        plain(int_dec(n)),
        cint(cs(int_dec(n))) == Some(n),
{
    if n < 0 {
        let m = (-n) as nat;
        nd_props(m);
        let s = int_dec(n);
        assert forall|k: int| 0 <= k < s.len() implies pc(#[trigger] s[k]) by {
            if k > 0 {
                assert(s[k] == nat_dec(m)[k - 1]);
                assert(dig(nat_dec(m)[k - 1] as u32));
            }
        }
        assert(cs(s).drop_first() =~= cs(nat_dec(m)));
    } else {
        nd_props(n as nat);
        let s = int_dec(n);
        assert forall|k: int| 0 <= k < s.len() implies pc(#[trigger] s[k]) by {
            assert(dig(s[k] as u32));
        }
        assert(dig(s[0] as u32));
    }
}

proof fn jstr_plain(s: Seq<char>, p: nat, w: Seq<char>)
    requires
        has(s, p as int, w),
        plain(w),
        p + w.len() < s.len(),
        s[(p + w.len()) as int] == '"',
    ensures
        jstr(s, p) == Some((cs(w), p + w.len() + 1)),
    decreases w.len(),
{
    reveal(has);
    if w.len() == 0 {
        assert(cs(w) =~= Seq::<u32>::empty());
    } else {
        let w2 = w.drop_first();
        assert forall|k: int| 0 <= k < w2.len() implies s[((p + 1) + k) as int] == #[trigger] w2[k] by {
            assert(w2[k] == w[k + 1]);
            assert(s[(p + (k + 1)) as int] == w[k + 1]);
        }
        assert forall|k: int| 0 <= k < w2.len() implies pc(#[trigger] w2[k]) by {
            assert(w2[k] == w[k + 1]);
        }
        jstr_plain(s, p + 1, w2);
        assert(s[(p + 0) as int] == w[0]);
        assert(pc(w[0]));
        assert(seq![w[0] as u32] + cs(w2) =~= cs(w));
    }
}

#[verifier::spinoff_prover]
#[verifier::rlimit(80)]
proof fn jv_str(s: Seq<char>, p: nat, d: nat, w: Seq<char>)
    requires
        has(s, p as int, qs(w)),
        plain(w),
    ensures
        jv(s, p, d) == Some((J::Str(cs(w)), p + w.len() + 2)),
{
    has_split(s, p as int, q() + w, q());
    has_split(s, p as int, q(), w);
    has_at(s, (p) as int, q(), 0);
    has_at(s, (p + 1 + w.len()) as int, q(), 0);
    jstr_plain(s, p + 1, w);
}

proof fn jv_lit(s: Seq<char>, p: nat, d: nat, b: bool)
    requires
        has(s, p as int, if b { w_true() } else { w_false() }),
    ensures
        jv(s, p, d) == Some((J::Bool(b), p + if b { 4nat } else { 5nat })),
{
    reveal(has);
    let w = if b { w_true() } else { w_false() };
    has_at(s, (p) as int, w, 0);
    assert(s.subrange(p as int, (p + w.len()) as int) =~= w) by {
        assert forall|k: int| 0 <= k < w.len() implies s.subrange(p as int, (p + w.len()) as int)[k] == w[k] by {
            assert(s[(p + k) as int] == w[k]);
        }
    }
    if !b {
        assert(s.subrange(p as int, (p + 4) as int)[0] == 'f');
    }
}

/// メンバー `"w":v` の後に ',' か '}' が続く。
#[verifier::spinoff_prover]
#[verifier::rlimit(80)]
proof fn jm_one(s: Seq<char>, p: nat, d: nat, w: Seq<char>, v: J, e: nat)
    requires
        has(s, p as int, hdr(w)),
        plain(w),
        jv(s, p + w.len() + 3, d) == Some((v, e)),
        p < e < s.len(),
    ensures
        s[e as int] == ',' ==> jmembers(s, p, d) == match jmembers(s, e + 1, d) {
            Some((ks, vs, g)) => Some((seq![cs(w)] + ks, seq![v] + vs, g)),
            None => None,
        },
        s[e as int] == '}' ==> jmembers(s, p, d) == Some((seq![cs(w)], seq![v], e + 1)),
{
    has_split(s, p as int, q() + w + q(), seq![':']);
    has_split(s, p as int, q() + w, q());
    has_split(s, p as int, q(), w);
    has_at(s, (p) as int, q(), 0);
    has_at(s, (p + 1 + w.len()) as int, q(), 0);
    has_at(s, (p + 2 + w.len()) as int, seq![':'], 0);
    jstr_plain(s, p + 1, w);
}

proof fn ji_one(s: Seq<char>, p: nat, d: nat, v: J, e: nat)
    requires
        jv(s, p, d) == Some((v, e)),
        p < e < s.len(),
        p <= s.len(),
    ensures
        s[e as int] == ',' ==> jitems(s, p, d) == match jitems(s, e + 1, d) {
            Some((vs, g)) => Some((seq![v] + vs, g)),
            None => None,
        },
        s[e as int] == ']' ==> jitems(s, p, d) == Some((seq![v], e + 1)),
{
}

/// 共通の先頭 `{"tag":"t"` の後に '}' か ',' が続く。
#[verifier::spinoff_prover]
#[verifier::rlimit(80)]
proof fn head(s: Seq<char>, i: nat, d: nat, t: Seq<char>)
    requires
        has(s, i as int, pre(t)),
        plain(t),
        d >= 1,
        i + 9 + t.len() < s.len(),
    ensures
        s[(i + 9 + t.len()) as int] == '}' ==> jv(s, i, d) == Some(
            (J::Obj(seq![k_tag()], seq![J::Str(cs(t))]), i + 10 + t.len()),
        ),
        s[(i + 9 + t.len()) as int] == ',' ==> jv(s, i, d) == match jmembers(s, i + 10 + t.len(), (d - 1) as nat) {
            Some((ks, vs, g)) => Some((J::Obj(seq![k_tag()] + ks, seq![J::Str(cs(t))] + vs), g)),
            None => None,
        },
{
    plain_tag();
    has_split(s, i as int, seq!['{'] + hdr(c_tag()), qs(t));
    has_split(s, i as int, seq!['{'], hdr(c_tag()));
    has_at(s, (i) as int, seq!['{'], 0);
    assert(hdr(c_tag()).len() == 6);
    has_at(s, (i + 1) as int, hdr(c_tag()), 0);
    jv_str(s, i + 7, (d - 1) as nat, t);
    jm_one(s, i + 1, (d - 1) as nat, c_tag(), J::Str(cs(t)), i + 9 + t.len());
}

/// 正準形の構文解析：値の正準 JSON は jt(v) に読める。
proof fn rt_parse(s: Seq<char>, i: nat, d: nat, v: Val)
    requires
        has(s, i as int, enc(v)),
        vdepth(v) <= d,
    ensures
        jv(s, i, d) == Some((jt(v), i + enc(v).len())),
    decreases v, 1nat,
{
    match v {
        Val::Int(_) => rt_int(s, i, d, v),
        Val::Bool(_) => rt_bool(s, i, d, v),
        Val::Unit => rt_unit(s, i, d, v),
        Val::None => rt_none(s, i, d, v),
        Val::Some(_) => rt_some(s, i, d, v),
        Val::Pair(_, _) => rt_pair(s, i, d, v),
        Val::List(_) => rt_list(s, i, d, v),
    }
}

#[verifier::spinoff_prover]
#[verifier::rlimit(80)]
proof fn rt_int(s: Seq<char>, i: nat, d: nat, v: Val)
    requires
        has(s, i as int, enc(v)),
        vdepth(v) <= d,
        v matches Val::Int(n),
    ensures
        jv(s, i, d) == Some((jt(v), i + enc(v).len())),
    decreases v, 0nat,
{
    lay_int();
    plain_int();
    plain_value();
    if let Val::Int(n) = v {
        let x = int_dec(n);
        int_dec_plain(n);
        has_split(s, i as int, l_int1() + x, l_int2());
        has_split(s, i as int, l_int1(), x);
        has_split(s, i as int, pre(c_int()) + seq![','] + hdr(c_value()), q());
        has_split(s, i as int, pre(c_int()) + seq![','], hdr(c_value()));
        has_split(s, i as int, pre(c_int()), seq![',']);
        has_split(s, (i + 22 + x.len()) as int, q(), seq!['}']);
        has_join(s, (i + 21) as int, q(), x);
        has_join(s, (i + 21) as int, q() + x, q());
        has_at(s, (i + 12) as int, seq![','], 0);
        has_at(s, (i + 23 + x.len()) as int, seq!['}'], 0);
        head(s, i, d, c_int());
        jv_str(s, i + 21, (d - 1) as nat, x);
        jm_one(s, i + 13, (d - 1) as nat, c_value(), J::Str(cs(x)), i + 23 + x.len());
        assert(seq![k_tag()] + seq![k_value()] =~= seq![k_tag(), k_value()]);
        assert(seq![J::Str(t_int())] + seq![J::Str(cs(x))] =~= seq![J::Str(t_int()), J::Str(cs(x))]);
    }
}

#[verifier::spinoff_prover]
#[verifier::rlimit(80)]
proof fn rt_bool(s: Seq<char>, i: nat, d: nat, v: Val)
    requires
        has(s, i as int, enc(v)),
        vdepth(v) <= d,
        v matches Val::Bool(b),
    ensures
        jv(s, i, d) == Some((jt(v), i + enc(v).len())),
    decreases v, 0nat,
{
    lay_bool();
    plain_bool();
    plain_value();
    if let Val::Bool(b) = v {
        let w = if b { w_true() } else { w_false() };
        let lit = pre(c_bool()) + seq![','] + hdr(c_value()) + w + seq!['}'];
        assert(enc(v) == lit);
        has_split(s, i as int, pre(c_bool()) + seq![','] + hdr(c_value()) + w, seq!['}']);
        has_split(s, i as int, pre(c_bool()) + seq![','] + hdr(c_value()), w);
        has_split(s, i as int, pre(c_bool()) + seq![','], hdr(c_value()));
        has_split(s, i as int, pre(c_bool()), seq![',']);
        has_at(s, (i + 13) as int, seq![','], 0);
        has_at(s, (i + 22 + w.len()) as int, seq!['}'], 0);
        head(s, i, d, c_bool());
        jv_lit(s, i + 22, (d - 1) as nat, b);
        jm_one(s, i + 14, (d - 1) as nat, c_value(), J::Bool(b), i + 22 + w.len());
        assert(seq![k_tag()] + seq![k_value()] =~= seq![k_tag(), k_value()]);
        assert(seq![J::Str(t_bool())] + seq![J::Bool(b)] =~= seq![J::Str(t_bool()), J::Bool(b)]);
    }
}

proof fn rt_unit(s: Seq<char>, i: nat, d: nat, v: Val)
    requires
        has(s, i as int, enc(v)),
        vdepth(v) <= d,
        v matches Val::Unit,
    ensures
        jv(s, i, d) == Some((jt(v), i + enc(v).len())),
    decreases v, 0nat,
{
    lay_unit();
    plain_unit();
        has_split(s, i as int, pre(c_unit()), seq!['}']);
        has_at(s, (i + 13) as int, seq!['}'], 0);
        head(s, i, d, c_unit());
}

proof fn rt_none(s: Seq<char>, i: nat, d: nat, v: Val)
    requires
        has(s, i as int, enc(v)),
        vdepth(v) <= d,
        v matches Val::None,
    ensures
        jv(s, i, d) == Some((jt(v), i + enc(v).len())),
    decreases v, 0nat,
{
    lay_unit();
    plain_none();
        has_split(s, i as int, pre(c_none()), seq!['}']);
        has_at(s, (i + 13) as int, seq!['}'], 0);
        head(s, i, d, c_none());
}

#[verifier::spinoff_prover]
#[verifier::rlimit(80)]
proof fn rt_some(s: Seq<char>, i: nat, d: nat, v: Val)
    requires
        has(s, i as int, enc(v)),
        vdepth(v) <= d,
        v matches Val::Some(x),
    ensures
        jv(s, i, d) == Some((jt(v), i + enc(v).len())),
    decreases v, 0nat,
{
    if let Val::Some(x) = v {
        let ex = enc(*x);
        let e = i + 22 + ex.len();
        assert(enc(v) == l_some() + ex + l_close());
        assert(l_some().len() == 22 && l_close().len() == 1 && l_close()[0] == '}') by {
            lay_some();
        }
        assert(has(s, (i + 22) as int, ex) && has(s, i as int, l_some()) && e < s.len() && s[e as int] == '}') by {
            has_split(s, i as int, l_some() + ex, l_close());
            has_split(s, i as int, l_some(), ex);
            has_at(s, e as int, l_close(), 0);
        }
        assert(vdepth(*x) <= d - 1);
        rt_parse(s, i + 22, (d - 1) as nat, *x);
        assert(jmembers(s, i + 14, (d - 1) as nat) == Some((seq![k_value()], seq![jt(*x)], e + 1))) by {
            lay_some();
            plain_value();
            has_split(s, i as int, pre(c_some()) + seq![','], hdr(c_value()));
            jm_one(s, i + 14, (d - 1) as nat, c_value(), jt(*x), e);
        }
        assert(jv(s, i, d) == Some((J::Obj(seq![k_tag()] + seq![k_value()], seq![J::Str(t_some())] + seq![jt(*x)]), e + 1))) by {
            lay_some();
            plain_some();
            has_split(s, i as int, pre(c_some()) + seq![','], hdr(c_value()));
            has_split(s, i as int, pre(c_some()), seq![',']);
            has_at(s, (i + 13) as int, seq![','], 0);
            head(s, i, d, c_some());
        }
        assert(seq![k_tag()] + seq![k_value()] =~= seq![k_tag(), k_value()]);
        assert(seq![J::Str(t_some())] + seq![jt(*x)] =~= seq![J::Str(t_some()), jt(*x)]);
    }
}

#[verifier::spinoff_prover]
#[verifier::rlimit(80)]
proof fn rt_pair(s: Seq<char>, i: nat, d: nat, v: Val)
    requires
        has(s, i as int, enc(v)),
        vdepth(v) <= d,
        v matches Val::Pair(a, b),
    ensures
        jv(s, i, d) == Some((jt(v), i + enc(v).len())),
    decreases v, 0nat,
{
    if let Val::Pair(a, b) = v {
        let ea = enc(*a);
        let eb = enc(*b);
        assert(enc(v) == l_pair1() + ea + l_pair2() + eb + l_close());
        assert(has(s, (i + 21) as int, ea) && has(s, (i + 30 + ea.len()) as int, eb)) by {
            lay_pair();
            has_split(s, i as int, l_pair1() + ea + l_pair2() + eb, l_close());
            has_split(s, i as int, l_pair1() + ea + l_pair2(), eb);
            has_split(s, i as int, l_pair1() + ea, l_pair2());
            has_split(s, i as int, l_pair1(), ea);
        }
        assert(vdepth(*a) <= d - 1 && vdepth(*b) <= d - 1);
        rt_parse(s, i + 21, (d - 1) as nat, *a);
        rt_parse(s, i + 30 + ea.len(), (d - 1) as nat, *b);
        pair_tail(s, i, d, ea, eb, jt(*a), jt(*b));
        assert(enc(v).len() == 31 + ea.len() + eb.len()) by {
            lay_pair();
        }
    }
}

#[verifier::spinoff_prover]
#[verifier::rlimit(80)]
proof fn pair_tail(s: Seq<char>, i: nat, d: nat, ea: Seq<char>, eb: Seq<char>, ja: J, jb: J)
    requires
        has(s, i as int, l_pair1() + ea + l_pair2() + eb + l_close()),
        d >= 1,
        jv(s, i + 21, (d - 1) as nat) == Some((ja, i + 21 + ea.len())),
        jv(s, i + 30 + ea.len(), (d - 1) as nat) == Some((jb, i + 30 + ea.len() + eb.len())),
    ensures
        jv(s, i, d) == Some(
            (
                J::Obj(seq![k_tag(), k_left(), k_right()], seq![J::Str(t_pair()), ja, jb]),
                i + 31 + ea.len() + eb.len(),
            ),
        ),
{
    let e1 = i + 21 + ea.len();
    let e2 = i + 30 + ea.len() + eb.len();
    assert(l_pair1().len() == 21 && l_pair2().len() == 9 && l_close().len() == 1) by {
        lay_pair();
    }
    assert(has(s, i as int, l_pair1()) && has(s, e1 as int, l_pair2()) && e2 < s.len() && s[e2 as int] == '}') by {
        lay_pair();
        has_split(s, i as int, l_pair1() + ea + l_pair2() + eb, l_close());
        has_split(s, i as int, l_pair1() + ea + l_pair2(), eb);
        has_split(s, i as int, l_pair1() + ea, l_pair2());
        has_split(s, i as int, l_pair1(), ea);
        has_at(s, e2 as int, l_close(), 0);
    }
    assert(jmembers(s, e1 + 1, (d - 1) as nat) == Some((seq![k_right()], seq![jb], e2 + 1))) by {
        lay_pair();
        plain_right();
        has_split(s, e1 as int, seq![','], hdr(c_right()));
        jm_one(s, e1 + 1, (d - 1) as nat, c_right(), jb, e2);
    }
    assert(jmembers(s, i + 14, (d - 1) as nat) == Some(
        (seq![k_left()] + seq![k_right()], seq![ja] + seq![jb], e2 + 1),
    )) by {
        lay_pair();
        plain_left();
        has_split(s, i as int, pre(c_pair()) + seq![','], hdr(c_left()));
        has_split(s, e1 as int, seq![','], hdr(c_right()));
        has_at(s, e1 as int, seq![','], 0);
        jm_one(s, i + 14, (d - 1) as nat, c_left(), ja, e1);
    }
    assert(jv(s, i, d) == Some(
        (
            J::Obj(seq![k_tag()] + (seq![k_left()] + seq![k_right()]), seq![J::Str(t_pair())] + (seq![ja] + seq![jb])),
            e2 + 1,
        ),
    )) by {
        lay_pair();
        plain_pair();
        has_split(s, i as int, pre(c_pair()) + seq![','], hdr(c_left()));
        has_split(s, i as int, pre(c_pair()), seq![',']);
        has_at(s, (i + 13) as int, seq![','], 0);
        head(s, i, d, c_pair());
    }
    assert(seq![k_tag()] + (seq![k_left()] + seq![k_right()]) =~= seq![k_tag(), k_left(), k_right()]);
    assert(seq![J::Str(t_pair())] + (seq![ja] + seq![jb]) =~= seq![J::Str(t_pair()), ja, jb]);
}

#[verifier::spinoff_prover]
#[verifier::rlimit(80)]
proof fn rt_list(s: Seq<char>, i: nat, d: nat, v: Val)
    requires
        has(s, i as int, enc(v)),
        vdepth(v) <= d,
        v matches Val::List(xs),
    ensures
        jv(s, i, d) == Some((jt(v), i + enc(v).len())),
    decreases v, 0nat,
{
    lay_list();
    plain_list();
    plain_items();
    if let Val::List(xs) = v {
        let ei = enc_items(xs, 0);
        has_split(s, i as int, l_list1() + ei, l_list2());
        has_split(s, i as int, l_list1(), ei);
        has_split(s, i as int, pre(c_list()) + seq![','] + hdr(c_items()), seq!['[']);
        has_split(s, i as int, pre(c_list()) + seq![','], hdr(c_items()));
        has_split(s, i as int, pre(c_list()), seq![',']);
        has_at(s, (i + 13) as int, seq![','], 0);
        has_at(s, (i + 22) as int, seq!['['], 0);
        has_at(s, (i + 23 + ei.len()) as int, l_list2(), 0);
        has_at(s, (i + 23 + ei.len()) as int, l_list2(), 1);
        let arr = J::Arr(jts(xs, 0));
        if xs.len() == 0 {
            assert(ei.len() == 0);
            assert(jts(xs, 0) =~= Seq::<J>::empty());
            assert(jv(s, i + 22, (d - 1) as nat) == Some((arr, i + 24)));
        } else {
            assert(ei == enc(xs[0]) + enc_items(xs, 1)) by {
                assert(ei == Seq::<char>::empty() + enc(xs[0]) + enc_items(xs, 1));
                assert(Seq::<char>::empty() + enc(xs[0]) =~= enc(xs[0]));
            }
            enc_first(xs[0]);
            has_split(s, (i + 23) as int, enc(xs[0]), enc_items(xs, 1));
            has_at(s, (i + 23) as int, enc(xs[0]), 0);
            assert forall|m: int| 0 <= m < xs.len() implies vdepth(#[trigger] xs[m]) <= (d - 2) as nat by {
                maxd_ge(xs, 0, m);
            }
            rt_items(s, i + 23, (d - 2) as nat, xs, 0);
            assert(jv(s, i + 22, (d - 1) as nat) == Some((arr, i + 24 + ei.len())));
        }
        head(s, i, d, c_list());
        jm_one(s, i + 14, (d - 1) as nat, c_items(), arr, i + 24 + ei.len());
        assert(seq![k_tag()] + seq![k_items()] =~= seq![k_tag(), k_items()]);
        assert(seq![J::Str(t_list())] + seq![arr] =~= seq![J::Str(t_list()), arr]);
    }
}

#[verifier::spinoff_prover]
#[verifier::rlimit(80)]
proof fn rt_items(s: Seq<char>, p: nat, d: nat, xs: Seq<Val>, k: nat)
    requires
        k < xs.len(),
        has(s, p as int, enc(xs[k as int]) + enc_items(xs, k + 1)),
        p + enc(xs[k as int]).len() + enc_items(xs, k + 1).len() < s.len(),
        s[(p + enc(xs[k as int]).len() + enc_items(xs, k + 1).len()) as int] == ']',
        forall|m: int| 0 <= m < xs.len() ==> vdepth(#[trigger] xs[m]) <= d,
    ensures
        jitems(s, p, d) == Some((jts(xs, k), p + enc(xs[k as int]).len() + enc_items(xs, k + 1).len() + 1)),
    decreases xs, xs.len() - k,
{
    let x = enc(xs[k as int]);
    let rest = enc_items(xs, k + 1);
    has_split(s, p as int, x, rest);
    enc_first(xs[k as int]);
    rt_parse(s, p, d, xs[k as int]);
    lay_list();
    if k + 1 >= xs.len() {
        assert(rest.len() == 0);
        ji_one(s, p, d, jt(xs[k as int]), p + x.len());
        assert(jts(xs, k) =~= seq![jt(xs[k as int])]);
    } else {
        let y = enc(xs[(k + 1) as int]);
        let r2 = enc_items(xs, k + 2);
        assert(rest == l_comma() + y + r2);
        assert(l_comma().len() == 1);
        has_split(s, (p + x.len()) as int, l_comma() + y, r2);
        has_split(s, (p + x.len()) as int, l_comma(), y);
        has_join(s, (p + x.len() + 1) as int, y, r2);
        has_at(s, (p + x.len()) as int, l_comma(), 0);
        rt_items(s, p + x.len() + 1, d, xs, k + 1);
        ji_one(s, p, d, jt(xs[k as int]), p + x.len());
    }
}

proof fn jds_shift(a: J, zs: Seq<J>, t: Ty, k: nat)
    ensures
        jds(seq![a] + zs, t, k + 1) == jds(zs, t, k),
    decreases zs.len() - k,
{
    let ys = seq![a] + zs;
    if k < zs.len() {
        assert(ys[(k + 1) as int] == zs[k as int]);
        jds_shift(a, zs, t, k + 1);
    }
}

/// 正準形の木の復号：型 t を持つ値 v の木を読むと v に戻る。
proof fn rt_dec(v: Val, t: Ty)
    requires
        val_type(v, t),
    ensures
        jd(jt(v), t) == Some(v),
    decreases v, 1nat,
{
    keys();
    reveal_with_fuel(kpos, 4);
    match v {
        Val::Some(x) => {
            rt_dec(*x, *t->Option_0);
        },
        Val::Pair(a, b) => {
            rt_dec(*a, *t->Pair_0);
            rt_dec(*b, *t->Pair_1);
        },
        Val::List(xs) => {
            let el = *t->List_0;
            val_type_list(xs, el);
            rt_decs(xs, el, 0);
            assert(xs.subrange(0, xs.len() as int) =~= xs);
        },
        Val::Int(n) => {
            int_dec_plain(n);
        },
        _ => {},
    }
    if let J::Obj(ks, vs) = jt(v) {
        assert(distinct(ks));
        assert forall|r: int| 0 <= r < ks.len() implies #[trigger] kpos(ks, ks[r], 0) < ks.len() by {}
        let r1 = seq![k_tag()];
        let r2v = seq![k_tag(), k_value()];
        let r2i = seq![k_tag(), k_items()];
        let r3 = seq![k_tag(), k_left(), k_right()];
        assert(ks == r1 || ks == r2v || ks == r2i || ks == r3);
        assert(only(ks, ks));
    }
}

proof fn rt_decs(xs: Seq<Val>, t: Ty, i: nat)
    requires
        i <= xs.len(),
        forall|k: int| 0 <= k < xs.len() ==> #[trigger] val_type(xs[k], t),
    ensures
        jds(jts(xs, i), t, 0) == Some(xs.subrange(i as int, xs.len() as int)),
    decreases xs, xs.len() - i,
{
    if i >= xs.len() {
        assert(xs.subrange(i as int, xs.len() as int) =~= Seq::<Val>::empty());
    } else {
        let ys = jts(xs, i);
        assert(ys[0] == jt(xs[i as int]));
        rt_dec(xs[i as int], t);
        rt_decs(xs, t, i + 1);
        jds_shift(jt(xs[i as int]), jts(xs, i + 1), t, 0);
        assert(seq![xs[i as int]] + xs.subrange((i + 1) as int, xs.len() as int) =~= xs.subrange(i as int, xs.len() as int));
    }
}

/// 往復性：型 t を持つ値 v の正準 JSON は、構造の深さが上限内なら strict JSON として受理され、v に戻る。
pub proof fn input_roundtrip(v: Val, t: Ty, d: nat)
    requires
        val_type(v, t),
        vdepth(v) <= d,
    ensures
        input_val(enc(v), d, t) == Some(v),
{
    reveal(has);
    let s = enc(v);
    assert forall|k: int| 0 <= k < s.len() implies s[(0 + k) as int] == #[trigger] s[k] by {}
    rt_parse(s, 0, d, v);
    rt_dec(v, t);
}

} // verus!
