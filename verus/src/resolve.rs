//! 名前解決（設計書 §5.1、§5.2、§11.2 の 3）。
//!
//! spec の `resolve` は表面 AST（名前付き）から名前解決済み AST（spec::Prog の関数列と entry）を作る。
//! - トップレベル関数名は相異なり（`distinct(fs)`）。全関数は全体で可視で、前方参照できる。
//! - 宣言した型（記録・直和型）の名前は相異なり、字段名はプログラム全体で一意（`decl_table`）。
//!   宣言の字段の型と直和型の中身は、その宣言より前の型だけを引く。関数の注釈と本体は全部の型を引く。
//! - 引数名は関数ごとに相異なる。
//! - `let x = a in b` の x は b でだけ見え、外側の可視変数をシャドーできない。
//! - fold の二 binder は相異なり、本体でだけ見え、外側をシャドーできない。
//! - 変数は可視変数の列（scope）での位置に、呼出しは関数の位置に置き換える。
//! - entry 宣言はちょうど一つで、既知の関数を指し、その関数の引数は一つ。
//! exec の `resolve_e` が spec の `resolve` と同じ結果を返すことを証明する。

use crate::ir::*;
use crate::records_exec::*;
use crate::records_proof::*;
use crate::spec::*;
use crate::surface::*;
use crate::syntax::*;
use vstd::prelude::*;

verus! {

// ------------------------------------------------------------------ spec

pub open spec fn idx(s: Seq<Seq<char>>, x: Seq<char>, i: nat) -> Option<nat>
    decreases s.len() - i,
{
    if i >= s.len() {
        None
    } else if s[i as int] == x {
        Some(i)
    } else {
        idx(s, x, i + 1)
    }
}

pub open spec fn distinct(s: Seq<Seq<char>>) -> bool {
    forall|i: int, j: int| 0 <= i < j < s.len() ==> s[i] != s[j]
}

/// 空でない名前は列の中で相異なる（空の名前は束縛の印。何個あってもよく、参照されない）。scope の列に使う。
pub open spec fn dsc(s: Seq<Seq<char>>) -> bool {
    forall|i: int, j: int| 0 <= i < j < s.len() && s[i].len() > 0 ==> s[i] != s[j]
}

/// 相異なる列は dsc。
pub proof fn distinct_dsc(s: Seq<Seq<char>>)
    requires
        distinct(s),
    ensures
        dsc(s),
{
    assert forall|i: int, j: int| 0 <= i < j < s.len() && s[i].len() > 0 implies s[i] != s[j] by {}
}

/// 空の名前（印）を足しても dsc は保たれる。
pub proof fn dsc_push_empty(s: Seq<Seq<char>>)
    requires
        dsc(s),
    ensures
        dsc(s.push(Seq::empty())),
{
    let t = s.push(Seq::<char>::empty());
    assert forall|i: int, j: int| 0 <= i < j < t.len() && t[i].len() > 0 implies t[i] != t[j] by {
        if j < s.len() {
            assert(t[i] == s[i]);
            assert(t[j] == s[j]);
        } else {
            assert(t[j].len() == 0);
        }
    }
}

/// 位置に無い名前を足しても dsc は保たれる。
pub proof fn dsc_push(s: Seq<Seq<char>>, x: Seq<char>)
    requires
        dsc(s),
        idx(s, x, 0) is None,
    ensures
        dsc(s.push(x)),
{
    idx_props(s, x, 0);
    let t = s.push(x);
    assert forall|i: int, j: int| 0 <= i < j < t.len() && t[i].len() > 0 implies t[i] != t[j] by {
        if j < s.len() {
            assert(t[i] == s[i]);
            assert(t[j] == s[j]);
        } else {
            assert(t[j] == x);
            assert(t[i] == s[i]);
        }
    }
}

/// 文字列リテラルは文字のリストの式になる。
pub open spec fn str_exprs(w: Seq<char>) -> Seq<Expr> {
    Seq::new(w.len(), |i: int| Expr::Char(w[i] as u32 as int))
}

/// 名前表の項目：宣言した型の名前、記録の印なしの展開（直和型は None）、記録の字段の名前（直和型は空）、
/// 記録の印つきの展開（S3c：字段の型を印つきで写した構造。名前つきの字段は Pair<tag, 展開>。直和型は None）。
/// 項目の位置が名義の番号になる（設計の B2）。字段の持ち主は、その字段名を持つ項目の位置。
pub open spec fn tnames(tb: Seq<(Seq<char>, Option<Ty>, Seq<Seq<char>>, Option<Ty>)>) -> Seq<Seq<char>> {
    Seq::new(tb.len(), |i: int| tb[i].0)
}

/// 字段名 x は、名前表のどの記録の字段でもない（字段名はプログラム全体で一意：規則 4）。
pub open spec fn fresh(tb: Seq<(Seq<char>, Option<Ty>, Seq<Seq<char>>, Option<Ty>)>, x: Seq<char>) -> bool {
    forall|j: int| 0 <= j < tb.len() ==> idx(tb[j].2, x, 0) is None
}

/// 型の名前が、名前表の項目だけを引く（規則 1）。構造は to_ty と同じ。
pub open spec fn tyn(t: SType, tb: Seq<(Seq<char>, Option<Ty>, Seq<Seq<char>>, Option<Ty>)>) -> bool
    decreases t,
{
    match t {
        SType::Int => true,
        SType::Bool => true,
        SType::Unit => true,
        SType::Char => true,
        SType::List(a) => tyn(*a, tb),
        SType::Option(a) => tyn(*a, tb),
        SType::Pair(a, b) => tyn(*a, tb) && tyn(*b, tb),
        SType::Result(a, b) => tyn(*a, tb) && tyn(*b, tb),
        SType::Named(x) => idx(tnames(tb), x, 0) is Some,
        SType::Dict(a, b) => tyn(*a, tb) && tyn(*b, tb),
    }
}

/// 記録の字段の列：字段名は相異なり（規則 4）、どれもほかの記録の字段でなく、型は前の項目だけを引く（規則 1）。
pub open spec fn fields_ok(fs: Seq<(Seq<char>, SType)>, tb: Seq<(Seq<char>, Option<Ty>, Seq<Seq<char>>, Option<Ty>)>) -> bool {
    distinct(pnames(fs)) && forall|i: int| 0 <= i < fs.len() ==> fresh(tb, fs[i].0) && tyn(fs[i].1, tb)
}

/// 直和型の中身（構築子ごとの型の並び）は、前の項目と自分自身だけを引く（規則 1）。自分を引くのは再帰する直和型
/// （trusted の v1.14：`type L = Nil | Cons(Int, L)` は受理する）。tb は自分を足した表。不透明にして、表の等しさで書き換える。
#[verifier::opaque]
pub open spec fn vars_ok(vs: Seq<(Seq<char>, Seq<SType>)>, tb: Seq<(Seq<char>, Option<Ty>, Seq<Seq<char>>, Option<Ty>)>) -> bool {
    forall|i: int, a: int| 0 <= i < vs.len() && 0 <= a < vs[i].1.len() ==> tyn(vs[i].1[a], tb)
}

/// 型が名前 r を書いている（入れ子の中も）。再帰する直和型かどうかの判定に使う（trusted の recursive_names）。
pub open spec fn sty_mentions(t: SType, r: Seq<char>) -> bool
    decreases t,
{
    match t {
        SType::Int => false,
        SType::Bool => false,
        SType::Unit => false,
        SType::Char => false,
        SType::List(a) => sty_mentions(*a, r),
        SType::Option(a) => sty_mentions(*a, r),
        SType::Pair(a, b) => sty_mentions(*a, r) || sty_mentions(*b, r),
        SType::Result(a, b) => sty_mentions(*a, r) || sty_mentions(*b, r),
        SType::Named(x) => x == r,
        SType::Dict(a, b) => sty_mentions(*a, r) || sty_mentions(*b, r),
    }
}

/// 再帰する直和型の項の型は、Int、Bool、その型自身のどれか（v1.14）。
pub open spec fn sty_rec_item(t: SType, r: Seq<char>) -> bool {
    t is Int || t is Bool || (t is Named && t->Named_0 == r)
}

/// 直和型の項（r は直和型の名前）は、どれも r を書かない（再帰しない）か、どれも Int、Bool、r のどれか（再帰する）。
/// 再帰する直和型の規則は v1.14 のとおり。不透明にして、exec の二つの判定と結び付ける。
#[verifier::opaque]
pub open spec fn rec_items(vs: Seq<(Seq<char>, Seq<SType>)>, r: Seq<char>) -> bool {
    (forall|i: int, a: int| 0 <= i < vs.len() && 0 <= a < vs[i].1.len() ==> !sty_mentions(#[trigger] vs[i].1[a], r))
        || (forall|i: int, a: int| 0 <= i < vs.len() && 0 <= a < vs[i].1.len() ==> sty_rec_item(#[trigger] vs[i].1[a], r))
}

/// 記録の字段 i から末尾までの展開（tagged = false は印なし、true は印つき）。右結合の Pair の入れ子で、末尾の字段の型はそのまま
/// （trusted の records.rs の record_type と同じ形）。
pub open spec fn rec_from(fs: Seq<(Seq<char>, SType)>, i: nat, tb: Seq<(Seq<char>, Option<Ty>, Seq<Seq<char>>, Option<Ty>)>, tagged: bool) -> Option<Ty>
    decreases fs.len() - i,
{
    if i >= fs.len() {
        None
    } else if i + 1 == fs.len() {
        to_ty(fs[i as int].1, tb, tagged)
    } else {
        match (to_ty(fs[i as int].1, tb, tagged), rec_from(fs, i + 1, tb, tagged)) {
            (Some(u), Some(v)) => Some(Ty::Pair(Box::new(u), Box::new(v))),
            _ => None,
        }
    }
}

/// 直和型の一つの構築子の中身（項の並び）の展開。項がなければ Unit、一つならその型、複数なら右に入れ子にした Pair
/// （sums.rs の payload_type と同じ形）。
pub open spec fn pay_ty(ts: Seq<SType>, tb: Seq<(Seq<char>, Option<Ty>, Seq<Seq<char>>, Option<Ty>)>, tagged: bool) -> Option<Ty> {
    if ts.len() == 0 {
        Some(Ty::Unit)
    } else {
        pay_from(ts, 0, tb, tagged)
    }
}

/// 項 i から末尾までの展開（rec_from と同じ形。末尾の項の型はそのまま）。
pub open spec fn pay_from(ts: Seq<SType>, i: nat, tb: Seq<(Seq<char>, Option<Ty>, Seq<Seq<char>>, Option<Ty>)>, tagged: bool) -> Option<Ty>
    decreases ts.len() - i,
{
    if i >= ts.len() {
        None
    } else if i + 1 == ts.len() {
        to_ty(ts[i as int], tb, tagged)
    } else {
        match (to_ty(ts[i as int], tb, tagged), pay_from(ts, i + 1, tb, tagged)) {
            (Some(u), Some(v)) => Some(Ty::Pair(Box::new(u), Box::new(v))),
            _ => None,
        }
    }
}

/// 直和型の中身の展開：構築子 k から末尾までの入れ子の Result（sums.rs の chain と同じ形。構築子が一つなら中身の型）。
pub open spec fn sum_from(vs: Seq<(Seq<char>, Seq<SType>)>, k: nat, tb: Seq<(Seq<char>, Option<Ty>, Seq<Seq<char>>, Option<Ty>)>, tagged: bool) -> Option<Ty>
    decreases vs.len() - k,
{
    if k >= vs.len() {
        None
    } else if k + 1 == vs.len() {
        pay_ty(vs[k as int].1, tb, tagged)
    } else {
        match (pay_ty(vs[k as int].1, tb, tagged), sum_from(vs, k + 1, tb, tagged)) {
            (Some(u), Some(v)) => Some(Ty::Result(Box::new(u), Box::new(v))),
            _ => None,
        }
    }
}

/// 直和型が再帰する（中身の型のどれかが名前 r を書く）。
pub open spec fn sum_rec(vs: Seq<(Seq<char>, Seq<SType>)>, r: Seq<char>) -> bool {
    !(forall|i: int, a: int| 0 <= i < vs.len() && 0 <= a < vs[i].1.len() ==> !sty_mentions(#[trigger] vs[i].1[a], r))
}

/// 直和型の名前表の展開。再帰する直和型は None（符号化は recursive.rs が受け持つ）。
pub open spec fn sum_exp(vs: Seq<(Seq<char>, Seq<SType>)>, r: Seq<char>, tb: Seq<(Seq<char>, Option<Ty>, Seq<Seq<char>>, Option<Ty>)>, tagged: bool) -> Option<Ty> {
    if sum_rec(vs, r) {
        None
    } else {
        sum_from(vs, 0, tb, tagged)
    }
}

/// 構築子の項目（直和型の名前表の三つ目の並びに入る）：'#'、構築子の名前、'#'、続けて字段の数だけの 'x'。
/// 識別子は '#' を含まないので、記録の字段名と混ざらない。字段の数は、構築子の並びから取り出せるように入れる。
pub open spec fn vent(c: Seq<char>, m: nat) -> Seq<char> {
    seq!['#'] + c + seq!['#'] + Seq::new(m, |i: int| 'x')
}

/// 直和型の宣言の構築子の項目の並び（宣言の順）。
pub open spec fn vents(vs: Seq<(Seq<char>, Seq<SType>)>) -> Seq<Seq<char>> {
    Seq::new(vs.len(), |k: int| vent(vs[k].0, vs[k].1.len()))
}

/// 項目 e が構築子 c のものなら、その字段の数。
pub open spec fn vent_arity(e: Seq<char>, c: Seq<char>) -> Option<nat> {
    let n = c.len() as int;
    if e.len() as int >= n + 2 && e[0] == '#' && e.subrange(1, n + 1) == c && e[n + 1] == '#' && (forall|j: int| n + 2 <= j < e.len() ==> e[j] == 'x') {
        Some((e.len() as int - n - 2) as nat)
    } else {
        None
    }
}

/// 構築子 c の項目を、一つの直和型の項目の並びの中で探す（位置 k と字段の数 m。最初に見つかったもの）。
pub open spec fn vidx(es: Seq<Seq<char>>, c: Seq<char>, i: nat) -> Option<(nat, nat)>
    decreases es.len() - i,
{
    if i >= es.len() {
        None
    } else {
        match vent_arity(es[i as int], c) {
            Some(m) => Some((i, m)),
            None => vidx(es, c, i + 1),
        }
    }
}

/// 構築子 c の項目を名前表で探す（最初に見つかったもの）：直和型の番号 i、位置 k、字段の数 m。
pub open spec fn vlook_from(tb: Seq<(Seq<char>, Option<Ty>, Seq<Seq<char>>, Option<Ty>)>, c: Seq<char>, i: nat) -> Option<(nat, nat, nat)>
    decreases tb.len() - i,
{
    if i >= tb.len() {
        None
    } else {
        match vidx(tb[i as int].2, c, 0) {
            Some((k, m)) => Some((i, k, m)),
            None => vlook_from(tb, c, i + 1),
        }
    }
}

pub open spec fn vlook(tb: Seq<(Seq<char>, Option<Ty>, Seq<Seq<char>>, Option<Ty>)>, c: Seq<char>) -> Option<(nat, nat, nat)> {
    vlook_from(tb, c, 0)
}

/// 名前表の三つ目の並びが記録の字段の並びか（直和型の並びは '#' で始まる項目だけを持つ）。
pub open spec fn is_rec_slot(fs: Seq<Seq<char>>) -> bool {
    fs.len() > 0 && fs[0].len() > 0 && fs[0][0] != '#'
}

/// 展開の型から、k 段の Result をはずした残りの型（k = 0 なら型そのもの）。
pub open spec fn tail_ty(t: Ty, k: nat) -> Option<Ty>
    decreases k,
{
    if k == 0 {
        Some(t)
    } else {
        match t {
            Ty::Result(_, b) => tail_ty(*b, (k - 1) as nat),
            _ => None,
        }
    }
}

/// 構築子 k の中身の型（構築子が n 個）：k 段目の Result の左（最後の構築子なら残りの型そのもの）。
pub open spec fn pay_at(t: Ty, n: nat, k: nat) -> Option<Ty> {
    if k + 1 < n {
        match tail_ty(t, k) {
            Some(Ty::Result(a, _)) => Some(*a),
            _ => None,
        }
    } else if k + 1 == n {
        tail_ty(t, k)
    } else {
        None
    }
}

/// 構築子 k の値を、層 j（j <= k）から作る：層 k より前は Err、層 k で Ok（最後の構築子なら中身そのもの）。
pub open spec fn inj_from(t: Ty, n: nat, k: nat, j: nat, p: Expr) -> Option<Expr>
    decreases k - j,
{
    if j >= k {
        if k + 1 < n {
            match (pay_at(t, n, k), tail_ty(t, k + 1)) {
                (Some(u), Some(v)) => Some(Expr::Inj(true, u, v, Box::new(p))),
                _ => None,
            }
        } else {
            Some(p)
        }
    } else {
        match (pay_at(t, n, j), tail_ty(t, j + 1), inj_from(t, n, k, j + 1, p)) {
            (Some(u), Some(v), Some(x)) => Some(Expr::Inj(false, u, v, Box::new(x))),
            _ => None,
        }
    }
}

/// 構築子 k の値（印つきの写しは、型の印の値を前に付ける）。i は直和型の名前表の番号。
pub open spec fn ctor_val(tagged: bool, i: nat, t: Ty, n: nat, k: nat, p: Expr) -> Option<Expr> {
    match inj_from(t, n, k, 0, p) {
        Some(v) => if tagged { Some(Expr::Pair(Box::new(tag_expr(i)), Box::new(v))) } else { Some(v) },
        None => None,
    }
}

/// 構築子の中身の式（字段が 0 または 1 個のとき）：字段が無ければ Unit、一つならその式。
pub open spec fn pay1(xs: Seq<Expr>) -> Expr {
    if xs.len() == 0 {
        Expr::Unit
    } else {
        xs[0]
    }
}

/// 構築子 c への呼出し（字段の式の列 xs）。字段が 0 または 1 個の構築子だけを作る。
pub open spec fn rctor(tb: Seq<(Seq<char>, Option<Ty>, Seq<Seq<char>>, Option<Ty>)>, tagged: bool, c: Seq<char>, xs: Seq<Expr>) -> Option<Expr> {
    match vlook(tb, c) {
        Some((i, k, m)) => if m > 1 || m != xs.len() || k >= tb[i as int].2.len() {
            None
        } else {
            match (if tagged { tb[i as int].3 } else { tb[i as int].1 }) {
                Some(t) => ctor_val(tagged, i, t, tb[i as int].2.len(), k, pay1(xs)),
                None => None,
            }
        },
        None => None,
    }
}

/// 宣言を名前表の末尾に足す。記録は、型名が新しく、字段の列が規則 1・4 を満たすときに足す。
/// 直和型は、型名が新しく、中身の型が前の項目と自分だけを引くときに足す（規則 1・3）。再帰しない直和型は展開も入れる。
/// 関数と entry は表に入らない。
#[verifier::opaque]
pub open spec fn tb_push(tb: Seq<(Seq<char>, Option<Ty>, Seq<Seq<char>>, Option<Ty>)>, d: Sd) -> Option<Seq<(Seq<char>, Option<Ty>, Seq<Seq<char>>, Option<Ty>)>> {
    match d {
        Sd::Fn(_, _, _, _) => Some(tb),
        Sd::Entry(_) => Some(tb),
        Sd::RecTy(r, fs, _) => if idx(tnames(tb), r, 0) is Some || !fields_ok(fs, tb) {
            None
        } else {
            Some(tb.push((r, rec_from(fs, 0, tb, false), pnames(fs), rec_from(fs, 0, tb, true))))
        },
        Sd::Sum(r, vs) => if idx(tnames(tb), r, 0) is Some || !vars_ok(vs, tb.push((r, None, Seq::empty(), None))) || !rec_items(vs, r) {
            None
        } else {
            Some(tb.push((r, sum_exp(vs, r, tb, false), vents(vs), sum_exp(vs, r, tb, true))))
        },
    }
}

/// tb_push の場合分けの補題。tb_push は不透明で、ここでだけ開く。宣言の形（vd）を経由しても、
/// 構築子の形で書いた結論と同じ項として扱えるようにする（exec 側で使う）。
proof fn tb_push_rec_none(tb: Seq<(Seq<char>, Option<Ty>, Seq<Seq<char>>, Option<Ty>)>, r: Seq<char>, fs: Seq<(Seq<char>, SType)>, tc: bool)
    requires
        idx(tnames(tb), r, 0) is Some || !fields_ok(fs, tb),
    ensures
        tb_push(tb, Sd::RecTy(r, fs, tc)) is None,
{
    reveal(tb_push);
}

proof fn tb_push_rec_some(tb: Seq<(Seq<char>, Option<Ty>, Seq<Seq<char>>, Option<Ty>)>, r: Seq<char>, fs: Seq<(Seq<char>, SType)>, tc: bool)
    requires
        idx(tnames(tb), r, 0) is None,
        fields_ok(fs, tb),
    ensures
        tb_push(tb, Sd::RecTy(r, fs, tc)) == Some(tb.push((r, rec_from(fs, 0, tb, false), pnames(fs), rec_from(fs, 0, tb, true)))),
{
    reveal(tb_push);
}

proof fn tb_push_sum_none(tb: Seq<(Seq<char>, Option<Ty>, Seq<Seq<char>>, Option<Ty>)>, r: Seq<char>, vs: Seq<(Seq<char>, Seq<SType>)>)
    requires
        idx(tnames(tb), r, 0) is Some || !vars_ok(vs, tb.push((r, None, Seq::empty(), None))) || !rec_items(vs, r),
    ensures
        tb_push(tb, Sd::Sum(r, vs)) is None,
{
    reveal(tb_push);
}

proof fn tb_push_sum_some(tb: Seq<(Seq<char>, Option<Ty>, Seq<Seq<char>>, Option<Ty>)>, r: Seq<char>, vs: Seq<(Seq<char>, Seq<SType>)>)
    requires
        idx(tnames(tb), r, 0) is None,
        vars_ok(vs, tb.push((r, None, Seq::empty(), None))),
        rec_items(vs, r),
    ensures
        tb_push(tb, Sd::Sum(r, vs)) == Some(tb.push((r, sum_exp(vs, r, tb, false), vents(vs), sum_exp(vs, r, tb, true)))),
{
    reveal(tb_push);
}

proof fn tb_push_other(tb: Seq<(Seq<char>, Option<Ty>, Seq<Seq<char>>, Option<Ty>)>, d: Sd)
    requires
        d matches Sd::Fn(..) || d matches Sd::Entry(..),
    ensures
        tb_push(tb, d) == Some(tb),
{
    reveal(tb_push);
}

/// 宣言の先頭 n 個の名前表（宣言の順）。どれかの宣言が規則に反すれば None。
/// 型名と関数名の一致は許す（規則 5）。関数の注釈と本体は、ここで作る表の全部を引く（規則 2）。
pub open spec fn decl_table(p: Seq<Sd>, n: nat) -> Option<Seq<(Seq<char>, Option<Ty>, Seq<Seq<char>>, Option<Ty>)>>
    decreases n,
{
    if n == 0 {
        Some(Seq::empty())
    } else if n > p.len() {
        None
    } else {
        match decl_table(p, (n - 1) as nat) {
            Some(tb) => tb_push(tb, p[(n - 1) as int]),
            None => None,
        }
    }
}

// ------------------------------------------------------------------ 印と番号（S2b）

/// 印の型 tag(k)：`Pair<Unit, Unit>` を k 段、`Pair<Unit, _>` で包んだもの（nominal.rs の tag_ty と同じ形）。
pub open spec fn tag_ty(k: nat) -> Ty
    decreases k,
{
    if k == 0 {
        Ty::Pair(Box::new(Ty::Unit), Box::new(Ty::Unit))
    } else {
        Ty::Pair(Box::new(Ty::Unit), Box::new(tag_ty((k - 1) as nat)))
    }
}

/// 印の値（tag_ty(k) の値）。
pub open spec fn tag_val(k: nat) -> Val
    decreases k,
{
    if k == 0 {
        Val::Pair(Box::new(Val::Unit), Box::new(Val::Unit))
    } else {
        Val::Pair(Box::new(Val::Unit), Box::new(tag_val((k - 1) as nat)))
    }
}

/// 印の型は k について単射（段数が違えば別の型）。k の帰納。
pub proof fn tag_ty_inj(k: nat, j: nat)
    requires
        tag_ty(k) == tag_ty(j),
    ensures
        k == j,
    decreases k + j,
{
    if k == 0 && j == 0 {
    } else if k == 0 {
        assert(tag_ty(j) == Ty::Pair(Box::new(Ty::Unit), Box::new(tag_ty((j - 1) as nat))));
        assert(tag_ty((j - 1) as nat) matches Ty::Pair(..));
        assert(false);
    } else if j == 0 {
        assert(tag_ty(k) == Ty::Pair(Box::new(Ty::Unit), Box::new(tag_ty((k - 1) as nat))));
        assert(tag_ty((k - 1) as nat) matches Ty::Pair(..));
        assert(false);
    } else {
        assert(tag_ty(k) == Ty::Pair(Box::new(Ty::Unit), Box::new(tag_ty((k - 1) as nat))));
        assert(tag_ty(j) == Ty::Pair(Box::new(Ty::Unit), Box::new(tag_ty((j - 1) as nat))));
        tag_ty_inj((k - 1) as nat, (j - 1) as nat);
    }
}

/// 印の値も k について単射。k の帰納。
pub proof fn tag_val_inj(k: nat, j: nat)
    requires
        tag_val(k) == tag_val(j),
    ensures
        k == j,
    decreases k + j,
{
    if k == 0 && j == 0 {
    } else if k == 0 {
        assert(tag_val(j) == Val::Pair(Box::new(Val::Unit), Box::new(tag_val((j - 1) as nat))));
        assert(tag_val((j - 1) as nat) matches Val::Pair(..));
        assert(false);
    } else if j == 0 {
        assert(tag_val(k) == Val::Pair(Box::new(Val::Unit), Box::new(tag_val((k - 1) as nat))));
        assert(tag_val((k - 1) as nat) matches Val::Pair(..));
        assert(false);
    } else {
        assert(tag_val(k) == Val::Pair(Box::new(Val::Unit), Box::new(tag_val((k - 1) as nat))));
        assert(tag_val(j) == Val::Pair(Box::new(Val::Unit), Box::new(tag_val((j - 1) as nat))));
        tag_val_inj((k - 1) as nat, (j - 1) as nat);
    }
}

/// 印の値は印の型の値。
pub proof fn tag_val_typed(k: nat)
    ensures
        val_type(tag_val(k), tag_ty(k)),
    decreases k,
{
    reveal_with_fuel(val_type, 2);
    if k == 0 {
        assert(tag_val(k) == Val::Pair(Box::new(Val::Unit), Box::new(Val::Unit)));
        assert(tag_ty(k) == Ty::Pair(Box::new(Ty::Unit), Box::new(Ty::Unit)));
    } else {
        tag_val_typed((k - 1) as nat);
        assert(tag_val(k) == Val::Pair(Box::new(Val::Unit), Box::new(tag_val((k - 1) as nat))));
        assert(tag_ty(k) == Ty::Pair(Box::new(Ty::Unit), Box::new(tag_ty((k - 1) as nat))));
    }
}

/// 印つきの型：記録の項目（番号 k、印つきの展開 s）は Pair<tag(k), s>。印なしは印なしの展開 u のまま。
pub proof fn named_tagged(tb: Seq<(Seq<char>, Option<Ty>, Seq<Seq<char>>, Option<Ty>)>, x: Seq<char>, k: nat)
    requires
        idx(tnames(tb), x, 0) == Some(k),
        k < tb.len(),
        tb[k as int].3 is Some,
    ensures
        to_ty(SType::Named(x), tb, true) == Some(Ty::Pair(Box::new(tag_ty(k)), Box::new(tb[k as int].3->Some_0))),
        to_ty(SType::Named(x), tb, false) == tb[k as int].1,
{
}

/// 型の宣言（記録と直和型）か。
pub open spec fn is_type_decl(d: Sd) -> bool {
    d matches Sd::RecTy(..) || d matches Sd::Sum(..)
}

/// 宣言 i の番号：型の宣言なら、その項目が名前表に入る位置（宣言の直前の名前表の長さ）。関数と entry は None。
pub open spec fn nums_of(p: Seq<Sd>, i: nat) -> Option<nat> {
    if i < p.len() && is_type_decl(p[i as int]) {
        match decl_table(p, i) {
            Some(tb) => Some(tb.len()),
            None => None,
        }
    } else {
        None
    }
}

/// 宣言の全部の番号（宣言の順）。名前表が作れるときだけ。
pub open spec fn decl_nums(p: Seq<Sd>) -> Option<Seq<Option<nat>>> {
    match decl_table(p, p.len()) {
        Some(_) => Some(Seq::new(p.len(), |i: int| nums_of(p, i as nat))),
        None => None,
    }
}

/// 番号の exec 版の写し（usize を nat に）。
pub open spec fn nums_conv(x: Option<usize>) -> Option<nat> {
    match x {
        Some(k) => Some(k as nat),
        None => None,
    }
}

pub open spec fn nums_view(s: Seq<Option<usize>>) -> Seq<Option<nat>> {
    Seq::new(s.len(), |k: int| nums_conv(s[k]))
}

/// 名前表に項目を足す。型の宣言なら長さが一つ増え、前の項目は変わらず、新しい項目は宣言の名前を持つ。
proof fn tb_push_facts(tb: Seq<(Seq<char>, Option<Ty>, Seq<Seq<char>>, Option<Ty>)>, d: Sd)
    ensures
        match tb_push(tb, d) {
            Some(nb) => (is_type_decl(d) ==> nb.len() == tb.len() + 1)
                && (!is_type_decl(d) ==> nb.len() == tb.len())
                && (forall|k: int| 0 <= k < tb.len() ==> nb[k] == tb[k])
                && (is_type_decl(d) ==> nb[tb.len() as int].0 == fname(d)),
            None => true,
        },
{
    reveal(tb_push);
}

/// 名前表の作り方（一つ前の表に、次の宣言を足す）。
proof fn decl_table_unfold(p: Seq<Sd>, n: nat)
    requires
        0 < n,
        n <= p.len(),
        decl_table(p, n) is Some,
    ensures
        decl_table(p, (n - 1) as nat) is Some,
        decl_table(p, n) == tb_push(decl_table(p, (n - 1) as nat)->Some_0, p[(n - 1) as int]),
{
}

/// 表の長さは、宣言を足すたびに増えるか変わらず、減らない。
proof fn decl_table_mono(p: Seq<Sd>, a: nat, b: nat)
    requires
        a <= b,
        b <= p.len(),
        decl_table(p, b) is Some,
    ensures
        decl_table(p, a) is Some,
        decl_table(p, a)->Some_0.len() <= decl_table(p, b)->Some_0.len(),
    decreases b - a,
{
    if a < b {
        decl_table_unfold(p, b);
        decl_table_mono(p, a, (b - 1) as nat);
        tb_push_facts(decl_table(p, (b - 1) as nat)->Some_0, p[(b - 1) as int]);
    }
}

/// 型の宣言 i が入った位置（宣言の直前の長さ）には、その宣言の名前の項目があり、後の表でも動かない。
proof fn decl_table_entry(p: Seq<Sd>, i: nat, n: nat)
    requires
        i < n,
        n <= p.len(),
        is_type_decl(p[i as int]),
        decl_table(p, n) is Some,
    ensures
        decl_table(p, i) is Some,
        decl_table(p, i)->Some_0.len() < decl_table(p, n)->Some_0.len(),
        decl_table(p, n)->Some_0[decl_table(p, i)->Some_0.len() as int].0 == fname(p[i as int]),
    decreases n - i,
{
    decl_table_unfold(p, n);
    if n == i + 1 {
        tb_push_facts(decl_table(p, i)->Some_0, p[i as int]);
    } else {
        decl_table_entry(p, i, (n - 1) as nat);
        tb_push_facts(decl_table(p, (n - 1) as nat)->Some_0, p[(n - 1) as int]);
    }
}

/// 番号の位置：型の宣言 i の番号は、全体の名前表の中で、その宣言の名前の項目の位置。
proof fn num_position(p: Seq<Sd>, i: nat)
    requires
        i < p.len(),
        is_type_decl(p[i as int]),
        decl_table(p, p.len()) is Some,
    ensures
        nums_of(p, i) is Some,
        nums_of(p, i)->Some_0 < decl_table(p, p.len())->Some_0.len(),
        decl_table(p, p.len())->Some_0[nums_of(p, i)->Some_0 as int].0 == fname(p[i as int]),
{
    decl_table_entry(p, i, p.len());
}

/// 番号は相異なる：宣言の順に、後の型の宣言の番号は前の型の宣言の番号より大きい。
proof fn num_distinct(p: Seq<Sd>, i: nat, j: nat)
    requires
        i < j,
        j < p.len(),
        is_type_decl(p[i as int]),
        is_type_decl(p[j as int]),
        decl_table(p, p.len()) is Some,
    ensures
        nums_of(p, i) is Some,
        nums_of(p, j) is Some,
        nums_of(p, i)->Some_0 < nums_of(p, j)->Some_0,
{
    decl_table_mono(p, j, p.len());
    decl_table_mono(p, i + 1, j);
    decl_table_mono(p, i, i + 1);
    decl_table_unfold(p, i + 1);
    tb_push_facts(decl_table(p, i)->Some_0, p[i as int]);
}

/// 表面の型から核の型へ。宣言された名前（Named）は名前表から引く。印なし（tagged = false）は項目の展開、
/// 印つき（tagged = true）は記録の Pair<tag(k), 印つきの展開>（直和型は展開が None なので None）。
/// Dict は v1.9 の消去で List<Pair<K, V>> になる（dict.rs の erase_in_place と同じ形）。
/// `tagged` は印つきの写し（S2b）。resolve と resolve_e は印なし（false）を使う。
pub open spec fn to_ty(t: SType, tb: Seq<(Seq<char>, Option<Ty>, Seq<Seq<char>>, Option<Ty>)>, tagged: bool) -> Option<Ty>
    decreases t,
{
    match t {
        SType::Int => Some(Ty::Int),
        SType::Bool => Some(Ty::Bool),
        SType::Unit => Some(Ty::Unit),
        SType::Char => Some(Ty::Char),
        SType::List(a) => match to_ty(*a, tb, tagged) {
            Some(u) => Some(Ty::List(Box::new(u))),
            None => None,
        },
        SType::Option(a) => match to_ty(*a, tb, tagged) {
            Some(u) => Some(Ty::Option(Box::new(u))),
            None => None,
        },
        SType::Pair(a, b) => match (to_ty(*a, tb, tagged), to_ty(*b, tb, tagged)) {
            (Some(u), Some(v)) => Some(Ty::Pair(Box::new(u), Box::new(v))),
            _ => None,
        },
        SType::Result(a, b) => match (to_ty(*a, tb, tagged), to_ty(*b, tb, tagged)) {
            (Some(u), Some(v)) => Some(Ty::Result(Box::new(u), Box::new(v))),
            _ => None,
        },
        SType::Named(x) => match idx(tnames(tb), x, 0) {
            Some(k) => if tagged {
                match tb[k as int].3 {
                    Some(s) => Some(Ty::Pair(Box::new(tag_ty(k)), Box::new(s))),
                    None => None,
                }
            } else {
                tb[k as int].1
            },
            None => None,
        },
        SType::Dict(a, b) => match (to_ty(*a, tb, tagged), to_ty(*b, tb, tagged)) {
            (Some(u), Some(v)) => Some(Ty::List(Box::new(Ty::Pair(Box::new(u), Box::new(v))))),
            _ => None,
        },
    }
}

/// 核の型の表現。to_ty が成功する型についてだけ使う（既定の Unit は、検査の済んだ呼出しでは現れない）。
pub open spec fn ty_or_unit(t: SType, tb: Seq<(Seq<char>, Option<Ty>, Seq<Seq<char>>, Option<Ty>)>, tagged: bool) -> Ty {
    match to_ty(t, tb, tagged) {
        Some(u) => u,
        None => Ty::Unit,
    }
}

/// 引数の型は全て核の型に写せる。
pub open spec fn params_ok(ps: Seq<(Seq<char>, SType)>, tb: Seq<(Seq<char>, Option<Ty>, Seq<Seq<char>>, Option<Ty>)>, tagged: bool) -> bool {
    forall|k: int| 0 <= k < ps.len() ==> to_ty(#[trigger] ps[k].1, tb, tagged) is Some
}

/// 枝の束縛の名前：字段が無ければ空の名前（参照されない束縛の印）、字段が一つなら、その名前（空でないもの）。
/// 字段が二つ以上の枝と、空でない名前の無い枝は、後の段階（None）。
pub open spec fn arm_name(bs: Seq<Seq<char>>) -> Option<Seq<char>> {
    if bs.len() == 0 {
        Some(Seq::empty())
    } else if bs.len() == 1 && bs[0].len() > 0 {
        Some(bs[0])
    } else {
        None
    }
}

/// 枝の左辺の束縛の名前（構築子の枝だけ）。
pub open spec fn arm_bind(p: Spat) -> Option<Seq<char>> {
    match p {
        Spat::Ctor(_, bs) => arm_name(bs),
        _ => None,
    }
}

/// 枝 j 以降は、直和型 i の構築子を宣言の順に並べたもの（枝 j は項目 j の構築子で、字段の数も項目と同じ）。
pub open spec fn arms_ctors(tb: Seq<(Seq<char>, Option<Ty>, Seq<Seq<char>>, Option<Ty>)>, i: nat, arms: Seq<(Spat, Sx)>, j: nat) -> bool
    decreases arms.len() - j,
{
    if j >= arms.len() {
        true
    } else {
        match arms[j as int].0 {
            Spat::Ctor(c, bs) => vent_arity(tb[i as int].2[j as int], c) == Some(bs.len()) && arm_name(bs) is Some && arms_ctors(tb, i, arms, j + 1),
            _ => false,
        }
    }
}

/// 枝の並びが、一つの直和型の構築子を宣言の順にちょうど一つずつ並べたものなら、その型の名前表の番号。
pub open spec fn arms_sum(tb: Seq<(Seq<char>, Option<Ty>, Seq<Seq<char>>, Option<Ty>)>, arms: Seq<(Spat, Sx)>) -> Option<nat> {
    if arms.len() == 0 {
        None
    } else {
        match arms[0].0 {
            Spat::Ctor(c, _) => match vlook(tb, c) {
                Some((i, _, _)) => if tb[i as int].2.len() == arms.len() && arms_ctors(tb, i, arms, 0) {
                    Some(i)
                } else {
                    None
                },
                None => None,
            },
            _ => None,
        }
    }
}

/// 直和型の枝の鎖（層 j から）。被験式 s は scope sc で整合する（sc.len() は層 j の束縛の位置）。
/// 構築子 j の枝は、中身の束縛（位置 sc.len()）で本体を解決する。最後の構築子以外は、Err の側（同じ位置）で次の層を続け、
/// その被験式は Err の束縛。最後の構築子は、残りの値そのものが中身なので let で束縛する。
pub open spec fn smatch_from(fs: Seq<Seq<char>>, tb: Seq<(Seq<char>, Option<Ty>, Seq<Seq<char>>, Option<Ty>)>, tagged: bool, sc: Seq<Seq<char>>, arms: Seq<(Spat, Sx)>, n: nat, j: nat, s: Expr) -> Option<Expr>
    decreases arms, n - j,
{
    if j >= n || j >= arms.len() {
        None
    } else {
        match arm_bind(arms[j as int].0) {
            Some(b) => if b.len() > 0 && idx(sc, b, 0) is Some {
                None
            } else {
                match rx(fs, tb, tagged, sc.push(b), arms[j as int].1) {
                    Some(body) => if j + 1 == n {
                        Some(Expr::Let(sc.len(), Box::new(s), Box::new(body)))
                    } else {
                        match smatch_from(fs, tb, tagged, sc.push(Seq::empty()), arms, n, j + 1, Expr::Var(sc.len())) {
                            Some(rest) => Some(Expr::MatchR(Box::new(s), sc.len(), Box::new(body), sc.len(), Box::new(rest))),
                            None => None,
                        }
                    },
                    None => None,
                }
            },
            None => None,
        }
    }
}

/// 直和型の枝（SumMatch）の鎖の頭。印つきの写しは、被験式を t（位置 d）に束縛し、印（構築子の番号 i の印）を検査して、
/// 中身（snd）から鎖を作る（tfield と同じ印の検査）。印なしは鎖をそのまま作る。n は直和型の構築子の数。
pub open spec fn smatch_top(fs: Seq<Seq<char>>, tb: Seq<(Seq<char>, Option<Ty>, Seq<Seq<char>>, Option<Ty>)>, tagged: bool, sc: Seq<Seq<char>>, arms: Seq<(Spat, Sx)>, i: nat, n: nat, rm: Expr) -> Option<Expr>
    decreases arms, n + 1,
{
    if tagged {
        let d = sc.len();
        match smatch_from(fs, tb, tagged, sc.push(Seq::empty()).push(Seq::empty()), arms, n, 0, Expr::Builtin(Builtin::Snd, seq![Expr::Var(d)])) {
            Some(c) => Some(Expr::Let(
                d,
                Box::new(rm),
                Box::new(Expr::Let(
                    d + 1,
                    Box::new(Expr::If(
                        Box::new(Expr::Builtin(Builtin::Eq, seq![Expr::Builtin(Builtin::Fst, seq![Expr::Var(d)]), tag_expr(i)])),
                        Box::new(Expr::Unit),
                        Box::new(Expr::Unit),
                    )),
                    Box::new(c),
                )),
            )),
            None => None,
        }
    } else {
        smatch_from(fs, tb, tagged, sc, arms, n, 0, rm)
    }
}

/// 式の名前解決。fs は関数名の列、tb は名前表、sc は可視変数の列（外側から順）。
pub open spec fn rx(fs: Seq<Seq<char>>, tb: Seq<(Seq<char>, Option<Ty>, Seq<Seq<char>>, Option<Ty>)>, tagged: bool, sc: Seq<Seq<char>>, e: Sx) -> Option<Expr>
    decreases e, 0nat,
{
    match e {
        Sx::Int(n) => Some(Expr::Int(n)),
        Sx::Chr(c) => Some(Expr::Char(c as u32 as int)),
        Sx::Str(w) => Some(Expr::List(Ty::Char, str_exprs(w))),
        Sx::Bool(b) => Some(Expr::Bool(b)),
        Sx::Unit => Some(Expr::Unit),
        // 空の名前は識別子にならない。記録の字段の式の scope に足す空の名前（rec_expr）は、参照されない。
        Sx::Var(x) => if x.len() == 0 {
            None
        } else {
            match idx(sc, x, 0) {
                Some(k) => Some(Expr::Var(k)),
                // 局所の名前でないもの：字段のない構築子（大文字の名前）。
                None => rctor(tb, tagged, x, Seq::empty()),
            }
        },
        Sx::List(t, es) => match (to_ty(t, tb, tagged), rxs(fs, tb, tagged, sc, es, 0)) {
            (Some(u), Some(xs)) => Some(Expr::List(u, xs)),
            _ => None,
        },
        Sx::Some(a) => match rx(fs, tb, tagged, sc, *a) {
            Some(x) => Some(Expr::Some(Box::new(x))),
            None => None,
        },
        Sx::None(t) => match to_ty(t, tb, tagged) {
            Some(u) => Some(Expr::None(u)),
            None => None,
        },
        Sx::Pair(a, b) => match (rx(fs, tb, tagged, sc, *a), rx(fs, tb, tagged, sc, *b)) {
            (Some(x), Some(y)) => Some(Expr::Pair(Box::new(x), Box::new(y))),
            _ => None,
        },
        Sx::Builtin(b, es) => match rxs(fs, tb, tagged, sc, es, 0) {
            Some(xs) => Some(Expr::Builtin(b, xs)),
            None => None,
        },
        Sx::Call(f, es) => match idx(fs, f, 0) {
            Some(g) => match rxs(fs, tb, tagged, sc, es, 0) {
                Some(xs) => Some(Expr::Call(g, xs)),
                None => None,
            },
            // 関数でない名前への呼出しは構築子の呼出し（字段が一つ以上。`A()` は字段のない構築子として書けない）。
            None => if es.len() == 0 {
                None
            } else {
                match rxs(fs, tb, tagged, sc, es, 0) {
                    Some(xs) => rctor(tb, tagged, f, xs),
                    None => None,
                }
            },
        },
        Sx::Let(x, a, b) => if idx(sc, x, 0) is Some {
            None
        } else {
            match (rx(fs, tb, tagged, sc, *a), rx(fs, tb, tagged, sc.push(x), *b)) {
                (Some(ra), Some(rb)) => Some(Expr::Let(sc.len(), Box::new(ra), Box::new(rb))),
                _ => None,
            }
        },
        Sx::If(c, a, b) => match (rx(fs, tb, tagged, sc, *c), rx(fs, tb, tagged, sc, *a), rx(fs, tb, tagged, sc, *b)) {
            (Some(x), Some(y), Some(z)) => Some(Expr::If(Box::new(x), Box::new(y), Box::new(z))),
            _ => None,
        },
        Sx::Fold(l, i, a, x, b) => if a == x || idx(sc, a, 0) is Some || idx(sc, x, 0) is Some {
            None
        } else {
            match (rx(fs, tb, tagged, sc, *l), rx(fs, tb, tagged, sc, *i), rx(fs, tb, tagged, sc.push(a).push(x), *b)) {
                (Some(rl), Some(ri), Some(rb)) => Some(
                    Expr::Fold(Box::new(rl), Box::new(ri), sc.len(), sc.len() + 1, Box::new(rb)),
                ),
                _ => None,
            }
        },
        Sx::Match(m, n, x, b) => if idx(sc, x, 0) is Some {
            None
        } else {
            match (rx(fs, tb, tagged, sc, *m), rx(fs, tb, tagged, sc, *n), rx(fs, tb, tagged, sc.push(x), *b)) {
                (Some(rm), Some(rn), Some(rb)) => Some(Expr::Match(Box::new(rm), Box::new(rn), sc.len(), Box::new(rb))),
                _ => None,
            }
        },
        Sx::Inj(ok, t, u, a) => match (to_ty(t, tb, tagged), to_ty(u, tb, tagged), rx(fs, tb, tagged, sc, *a)) {
            (Some(t1), Some(u1), Some(x)) => Some(Expr::Inj(ok, t1, u1, Box::new(x))),
            _ => None,
        },
        Sx::MatchR(m, x, a, y, b) => if idx(sc, x, 0) is Some || idx(sc, y, 0) is Some {
            None
        } else {
            match (rx(fs, tb, tagged, sc, *m), rx(fs, tb, tagged, sc.push(x), *a), rx(fs, tb, tagged, sc.push(y), *b)) {
                (Some(rm), Some(ra), Some(rb)) => Some(
                    Expr::MatchR(Box::new(rm), sc.len(), Box::new(ra), sc.len(), Box::new(rb)),
                ),
                _ => None,
            }
        },
        // 記録（段階 2 の S3a の印なし、S3b の印つき）：e.f の連鎖（持ち主は名前で引く）と、構築・更新（rec_t）。
        Sx::Fld(a, fls) => match rx(fs, tb, tagged, sc, *a) {
            Some(x) => if tagged { fld_chain_t(tb, x, fls, 0, sc.len()) } else { fld_chain(tb, x, fls, 0) },
            None => None,
        },
        Sx::Rec(r, fls, base) => match idx(tnames(tb), r, 0) {
            Some(k) => if !is_rec_slot(tb[k as int].2) || idx(sc, Seq::empty(), 0) is Some {
                None
            } else {
                match base {
                    None => rec_t(fs, tb, tagged, sc, k, tb[k as int].2, fls, None),
                    Some(b) => match rx(fs, tb, tagged, sc, *b) {
                        Some(bx) => rec_t(fs, tb, tagged, sc, k, tb[k as int].2, fls, Some(bx)),
                        None => None,
                    },
                }
            },
            None => None,
        },
        // 直和型の枝（v1.4）：枝の並びが一つの直和型の構築子の並びなら、その型の鎖にする（印つきは印を検査する）。
        Sx::SumMatch(m, arms) => match arms_sum(tb, arms) {
            Some(i) => match rx(fs, tb, tagged, sc, *m) {
                Some(rm) => smatch_top(fs, tb, tagged, sc, arms, i, tb[i as int].2.len(), rm),
                None => None,
            },
            None => None,
        },
        // hof は名前解決の対象外（字句・構文の段階だけで扱う）。
        Sx::Hof(..) => None,
        // loop も名前解決の対象外（字句・構文の段階だけで扱う）。
        Sx::Loop(..) => None,
        // dict の形も名前解決の対象外（字句・構文の段階だけで扱う）。
        Sx::DictNew(..) | Sx::DictOp(..) => None,
    }
}

pub open spec fn rxs(fs: Seq<Seq<char>>, tb: Seq<(Seq<char>, Option<Ty>, Seq<Seq<char>>, Option<Ty>)>, tagged: bool, sc: Seq<Seq<char>>, es: Seq<Sx>, i: nat) -> Option<Seq<Expr>>
    decreases es, es.len() - i,
{
    if i >= es.len() {
        Some(Seq::empty())
    } else {
        match (rx(fs, tb, tagged, sc, es[i as int]), rxs(fs, tb, tagged, sc, es, i + 1)) {
            (Some(x), Some(xs)) => Some(seq![x] + xs),
            _ => None,
        }
    }
}

// ------------------------------------------------------------------ 式の記録（段階 2 の S3a、印なし）

/// 字段名 f の持ち主：名前表の k 番目以降で、字段の列に f を持つ最初の項目の（位置、字段の数）。
/// 字段名はプログラム全体で一意（規則 4）なので、持ち主は一つだけ（records.rs の `owner` と同じ見方）。
pub open spec fn owner_pos(tb: Seq<(Seq<char>, Option<Ty>, Seq<Seq<char>>, Option<Ty>)>, f: Seq<char>, k: nat) -> Option<(nat, nat)>
    decreases tb.len() - k,
{
    if k >= tb.len() {
        None
    } else {
        match idx(tb[k as int].2, f, 0) {
            Some(i) => Some((i, tb[k as int].2.len())),
            None => owner_pos(tb, f, k + 1),
        }
    }
}

/// `e.f1…fn` の展開（records.rs の `field_access` を字段の順に重ねる）。i 番目の字段から。
pub open spec fn fld_chain(tb: Seq<(Seq<char>, Option<Ty>, Seq<Seq<char>>, Option<Ty>)>, e: Expr, fls: Seq<Seq<char>>, i: nat) -> Option<Expr>
    decreases fls.len() - i,
{
    if i >= fls.len() {
        Some(e)
    } else {
        match owner_pos(tb, fls[i as int], 0) {
            Some((p, n)) => fld_chain(tb, rfield(e, p, n), fls, i + 1),
            None => None,
        }
    }
}

/// fld_chain の一段（字段 i の持ち主が (p, m) のとき）。
proof fn fld_chain_step(tb: Seq<(Seq<char>, Option<Ty>, Seq<Seq<char>>, Option<Ty>)>, e: Expr, fls: Seq<Seq<char>>, i: nat, p: nat, m: nat)
    requires
        i < fls.len(),
        owner_pos(tb, fls[i as int], 0) == Some((p, m)),
    ensures
        fld_chain(tb, e, fls, i) == fld_chain(tb, rfield(e, p, m), fls, i + 1),
{
    reveal_with_fuel(fld_chain, 2);
}

/// fld_chain の一段（字段 i に持ち主がないとき）。
proof fn fld_chain_none(tb: Seq<(Seq<char>, Option<Ty>, Seq<Seq<char>>, Option<Ty>)>, e: Expr, fls: Seq<Seq<char>>, i: nat)
    requires
        i < fls.len(),
        owner_pos(tb, fls[i as int], 0) is None,
    ensures
        fld_chain(tb, e, fls, i) is None,
{
    reveal_with_fuel(fld_chain, 2);
}

/// fld_chain の終わり（字段がすべて済んだとき）。
proof fn fld_chain_end(tb: Seq<(Seq<char>, Option<Ty>, Seq<Seq<char>>, Option<Ty>)>, e: Expr, fls: Seq<Seq<char>>, i: nat)
    requires
        i >= fls.len(),
    ensures
        fld_chain(tb, e, fls, i) == Some(e),
{
    reveal_with_fuel(fld_chain, 2);
}

// ------------------------------------------------------------------ 印つきの写し（段階 2 の S3b）

/// 印の式（tag_val(k) に対応する式）。印は Pair<Unit, Unit> を k 段入れ子にした値（tag_val と同じ形）。
pub open spec fn tag_expr(k: nat) -> Expr
    decreases k,
{
    if k == 0 {
        Expr::Pair(Box::new(Expr::Unit), Box::new(Expr::Unit))
    } else {
        Expr::Pair(Box::new(Expr::Unit), Box::new(tag_expr((k - 1) as nat)))
    }
}

/// 印の式は変数を含まない（どの scope でも整合）。
proof fn tag_expr_scoped(k: nat, n: nat)
    ensures
        scoped(tag_expr(k), n),
    decreases k,
{
    reveal_with_fuel(scoped, 2);
    if k > 0 {
        tag_expr_scoped((k - 1) as nat, n);
    }
}

/// 印つきの字段の参照の一段（S3b）。let t = e in let u = if eq(fst(t), tag(k)) then unit else unit in
/// rfield(snd(t), i, n)。t は位置 d、u は位置 d + 1。持ち主の印 k と値の印が違えば、eq の両辺の型が違い、
/// 核の型検査（ty_expr の Eq）が拒否する。
pub open spec fn tfield(e: Expr, k: nat, i: nat, n: nat, d: nat) -> Expr {
    Expr::Let(
        d,
        Box::new(e),
        Box::new(Expr::Let(
            d + 1,
            Box::new(Expr::If(
                Box::new(Expr::Builtin(
                    Builtin::Eq,
                    seq![Expr::Builtin(Builtin::Fst, seq![Expr::Var(d)]), tag_expr(k)],
                )),
                Box::new(Expr::Unit),
                Box::new(Expr::Unit),
            )),
            Box::new(rfield(Expr::Builtin(Builtin::Snd, seq![Expr::Var(d)]), i, n)),
        )),
    )
}

/// 二つの引数の組込み（eq など）の scope 整合。
proof fn builtin2_scoped(b: Builtin, x: Expr, y: Expr, n: nat)
    requires
        scoped(x, n),
        scoped(y, n),
    ensures
        scoped(Expr::Builtin(b, seq![x, y]), n),
{
    reveal_with_fuel(scoped_all, 3);
    reveal_with_fuel(scoped, 2);
    let es = seq![x, y];
    assert(es.len() == 2);
    assert(es[0] == x);
    assert(es[1] == y);
    assert(scoped_all(es, n, 2));
    assert(scoped_all(es, n, 1));
    assert(scoped_all(es, n, 0));
}

/// 印つきの字段の参照の一段は、e が位置 d の scope にあれば、d の scope にある。
proof fn tfield_scoped(e: Expr, k: nat, i: nat, n: nat, d: nat)
    requires
        scoped(e, d),
    ensures
        scoped(tfield(e, k, i, n, d), d),
{
    reveal_with_fuel(scoped, 4);
    tag_expr_scoped(k, d + 1);
    assert(scoped(Expr::Var(d), d + 1));
    builtin1_scoped(Builtin::Fst, Expr::Var(d), d + 1);
    builtin2_scoped(Builtin::Eq, Expr::Builtin(Builtin::Fst, seq![Expr::Var(d)]), tag_expr(k), d + 1);
    assert(scoped(Expr::Var(d), d + 2));
    builtin1_scoped(Builtin::Snd, Expr::Var(d), d + 2);
    rfield_scoped(Expr::Builtin(Builtin::Snd, seq![Expr::Var(d)]), i, n, d + 2);
}

/// 字段名 f の持ち主（owner_pos と同じ探索）。宣言の番号 k、字段の位置 i、字段の数 n を返す。
pub open spec fn owner_at(tb: Seq<(Seq<char>, Option<Ty>, Seq<Seq<char>>, Option<Ty>)>, f: Seq<char>, k: nat) -> Option<(nat, nat, nat)>
    decreases tb.len() - k,
{
    if k >= tb.len() {
        None
    } else {
        match idx(tb[k as int].2, f, 0) {
            Some(i) => Some((k, i, tb[k as int].2.len())),
            None => owner_at(tb, f, k + 1),
        }
    }
}

/// `e.f1…fn` の印つきの展開（fld_chain の印つきの版）。持ち主の印で検査してから字段を取る。
pub open spec fn fld_chain_t(tb: Seq<(Seq<char>, Option<Ty>, Seq<Seq<char>>, Option<Ty>)>, e: Expr, fls: Seq<Seq<char>>, i: nat, d: nat) -> Option<Expr>
    decreases fls.len() - i,
{
    if i >= fls.len() {
        Some(e)
    } else {
        match owner_at(tb, fls[i as int], 0) {
            Some((k, p, n)) => fld_chain_t(tb, tfield(e, k, p, n, d), fls, i + 1, d),
            None => None,
        }
    }
}

/// fld_chain_t の一段（字段 i の持ち主が (k, p, n) のとき）。
proof fn fld_chain_t_step(tb: Seq<(Seq<char>, Option<Ty>, Seq<Seq<char>>, Option<Ty>)>, e: Expr, fls: Seq<Seq<char>>, i: nat, k: nat, p: nat, n: nat, d: nat)
    requires
        i < fls.len(),
        owner_at(tb, fls[i as int], 0) == Some((k, p, n)),
    ensures
        fld_chain_t(tb, e, fls, i, d) == fld_chain_t(tb, tfield(e, k, p, n, d), fls, i + 1, d),
{
    reveal_with_fuel(fld_chain_t, 2);
}

/// fld_chain_t の一段（字段 i に持ち主がないとき）。
proof fn fld_chain_t_none(tb: Seq<(Seq<char>, Option<Ty>, Seq<Seq<char>>, Option<Ty>)>, e: Expr, fls: Seq<Seq<char>>, i: nat, d: nat)
    requires
        i < fls.len(),
        owner_at(tb, fls[i as int], 0) is None,
    ensures
        fld_chain_t(tb, e, fls, i, d) is None,
{
    reveal_with_fuel(fld_chain_t, 2);
}

/// fld_chain_t の終わり（字段がすべて済んだとき）。
proof fn fld_chain_t_end(tb: Seq<(Seq<char>, Option<Ty>, Seq<Seq<char>>, Option<Ty>)>, e: Expr, fls: Seq<Seq<char>>, i: nat, d: nat)
    requires
        i >= fls.len(),
    ensures
        fld_chain_t(tb, e, fls, i, d) == Some(e),
{
    reveal_with_fuel(fld_chain_t, 2);
}

/// fld_chain_t の scope 整合。
proof fn fld_chain_t_scoped(tb: Seq<(Seq<char>, Option<Ty>, Seq<Seq<char>>, Option<Ty>)>, e: Expr, fls: Seq<Seq<char>>, i: nat, d: nat)
    requires
        scoped(e, d),
    ensures
        fld_chain_t(tb, e, fls, i, d) matches Some(x) ==> scoped(x, d),
    decreases fls.len() - i,
{
    if i < fls.len() {
        if let Some((k, p, n)) = owner_at(tb, fls[i as int], 0) {
            tfield_scoped(e, k, p, n, d);
            fld_chain_t_scoped(tb, tfield(e, k, p, n, d), fls, i + 1, d);
        }
    }
}

/// 書いた字段（fls の i 番目から）を宣言の位置に置く。u は宣言順の列（書いていない位置は None）。
/// 宣言にない字段名、同じ字段の二度目、解決できない値は None（UNKNOWN-FIELD、DUPLICATE-FIELD）。
pub open spec fn rec_upd(fs: Seq<Seq<char>>, tb: Seq<(Seq<char>, Option<Ty>, Seq<Seq<char>>, Option<Ty>)>, tagged: bool, sc: Seq<Seq<char>>, decl: Seq<Seq<char>>, fls: Seq<(Seq<char>, Sx)>, i: nat, u: Seq<Option<Expr>>) -> Option<Seq<Option<Expr>>>
    decreases fls, fls.len() - i,
{
    if i >= fls.len() {
        Some(u)
    } else {
        match idx(decl, fls[i as int].0, 0) {
            Some(j) => if u[j as int] is Some {
                None
            } else {
                match rx(fs, tb, tagged, sc, fls[i as int].1) {
                    Some(x) => rec_upd(fs, tb, tagged, sc, decl, fls, i + 1, u.update(j as int, Some(x))),
                    None => None,
                }
            },
            None => None,
        }
    }
}

/// 書いた字段のない初期の列（宣言の数だけ None）。rec_upd の初期値として、spec と exec の両方で同じ項を使う。
pub open spec fn none_upd(n: nat) -> Seq<Option<Expr>> {
    Seq::new(n, |j: int| None::<Expr>)
}

/// rec_upd の一段（字段 i の名前が宣言に無いとき）。
proof fn rec_upd_none_idx(fs: Seq<Seq<char>>, tb: Seq<(Seq<char>, Option<Ty>, Seq<Seq<char>>, Option<Ty>)>, tagged: bool, sc: Seq<Seq<char>>, decl: Seq<Seq<char>>, fls: Seq<(Seq<char>, Sx)>, i: nat, u: Seq<Option<Expr>>)
    requires
        i < fls.len(),
        idx(decl, fls[i as int].0, 0) is None,
    ensures
        rec_upd(fs, tb, tagged, sc, decl, fls, i, u) is None,
{
    reveal_with_fuel(rec_upd, 2);
}

/// rec_upd の一段（字段 i の位置 j に、既に書いた字段があるとき：DUPLICATE-FIELD）。
proof fn rec_upd_none_dup(fs: Seq<Seq<char>>, tb: Seq<(Seq<char>, Option<Ty>, Seq<Seq<char>>, Option<Ty>)>, tagged: bool, sc: Seq<Seq<char>>, decl: Seq<Seq<char>>, fls: Seq<(Seq<char>, Sx)>, i: nat, u: Seq<Option<Expr>>, j: nat)
    requires
        i < fls.len(),
        idx(decl, fls[i as int].0, 0) == Some(j),
        j < u.len(),
        u[j as int] is Some,
    ensures
        rec_upd(fs, tb, tagged, sc, decl, fls, i, u) is None,
{
    reveal_with_fuel(rec_upd, 2);
}

/// rec_upd の一段（字段 i の式が解決しないとき）。
proof fn rec_upd_none_rx(fs: Seq<Seq<char>>, tb: Seq<(Seq<char>, Option<Ty>, Seq<Seq<char>>, Option<Ty>)>, tagged: bool, sc: Seq<Seq<char>>, decl: Seq<Seq<char>>, fls: Seq<(Seq<char>, Sx)>, i: nat, u: Seq<Option<Expr>>, j: nat)
    requires
        i < fls.len(),
        idx(decl, fls[i as int].0, 0) == Some(j),
        j < u.len(),
        u[j as int] is None,
        rx(fs, tb, tagged, sc, fls[i as int].1) is None,
    ensures
        rec_upd(fs, tb, tagged, sc, decl, fls, i, u) is None,
{
    reveal_with_fuel(rec_upd, 2);
}

/// rec_upd の一段（字段 i を位置 j に置く）。
proof fn rec_upd_step(fs: Seq<Seq<char>>, tb: Seq<(Seq<char>, Option<Ty>, Seq<Seq<char>>, Option<Ty>)>, tagged: bool, sc: Seq<Seq<char>>, decl: Seq<Seq<char>>, fls: Seq<(Seq<char>, Sx)>, i: nat, u: Seq<Option<Expr>>, j: nat, x: Expr)
    requires
        i < fls.len(),
        idx(decl, fls[i as int].0, 0) == Some(j),
        j < u.len(),
        u[j as int] is None,
        rx(fs, tb, tagged, sc, fls[i as int].1) == Some(x),
    ensures
        rec_upd(fs, tb, tagged, sc, decl, fls, i, u) == rec_upd(fs, tb, tagged, sc, decl, fls, i + 1, u.update(j as int, Some(x))),
{
    reveal_with_fuel(rec_upd, 2);
}

/// rec_upd の終わり（字段がすべて済んだとき）。
proof fn rec_upd_end(fs: Seq<Seq<char>>, tb: Seq<(Seq<char>, Option<Ty>, Seq<Seq<char>>, Option<Ty>)>, tagged: bool, sc: Seq<Seq<char>>, decl: Seq<Seq<char>>, fls: Seq<(Seq<char>, Sx)>, i: nat, u: Seq<Option<Expr>>)
    requires
        i >= fls.len(),
    ensures
        rec_upd(fs, tb, tagged, sc, decl, fls, i, u) == Some(u),
{
    reveal_with_fuel(rec_upd, 2);
}

/// 記録の式の本体（bx は解決済みの base）。字段を宣言の位置に置き、records_exec の rrecord で拒否（MISSING-FIELD、
/// BASE-REDUNDANT）と展開を決める。基を let で束縛するのは、基が変数でなく書いていない字段が二つ以上あるとき
/// （rupdate と同じ条件）だけで、そのときは字段の式を一つ深い scope（空の名前を一つ足した列）で解決する。
/// 空の名前は識別子にならず（rx の Var の腕）、この scope の番号を字段の式は読まない。
pub open spec fn rec_expr(fs: Seq<Seq<char>>, tb: Seq<(Seq<char>, Option<Ty>, Seq<Seq<char>>, Option<Ty>)>, tagged: bool, sc: Seq<Seq<char>>, decl: Seq<Seq<char>>, fls: Seq<(Seq<char>, Sx)>, bx: Option<Expr>) -> Option<Expr>
    decreases fls, fls.len() + 1,
{
    let deep = match bx {
        Some(b) => !(b is Var) && decl.len() >= fls.len() + 2,
        None => false,
    };
    let sc2 = if deep { sc.push(Seq::empty()) } else { sc };
    match rec_upd(fs, tb, tagged, sc2, decl, fls, 0, none_upd(decl.len())) {
        Some(u) => match rrecord(u, bx, sc.len()) {
            Ok(e) => Some(e),
            Err(_) => None,
        },
        None => None,
    }
}

/// 記録の構築（S3b）。印なし（tagged = false）は rec_expr。印つきは、基底を印の検査で外してから rec_expr に渡し、
/// 結果を pair(tag(k), ·) で包む（印つきの記録の値は印と展開の組）。k は記録の宣言の番号、基底の束縛は sc.len() の位置。
pub open spec fn rec_t(fs: Seq<Seq<char>>, tb: Seq<(Seq<char>, Option<Ty>, Seq<Seq<char>>, Option<Ty>)>, tagged: bool, sc: Seq<Seq<char>>, k: nat, decl: Seq<Seq<char>>, fls: Seq<(Seq<char>, Sx)>, bx: Option<Expr>) -> Option<Expr>
    decreases fls, fls.len() + 2,
{
    if tagged {
        let bx2 = match bx {
            Some(b) => Some(tfield(b, k, 0, 1, sc.len())),
            None => None,
        };
        match rec_expr(fs, tb, tagged, sc, decl, fls, bx2) {
            Some(e) => Some(Expr::Pair(Box::new(tag_expr(k)), Box::new(e))),
            None => None,
        }
    } else {
        rec_expr(fs, tb, tagged, sc, decl, fls, bx)
    }
}

/// p[0..n] の関数宣言。
pub open spec fn fns_upto(p: Seq<Sd>, n: nat) -> Seq<Sd>
    decreases n,
{
    if n == 0 || n > p.len() {
        Seq::empty()
    } else if p[n - 1] is Fn {
        fns_upto(p, (n - 1) as nat).push(p[n - 1])
    } else {
        fns_upto(p, (n - 1) as nat)
    }
}

/// p[0..n] の entry 宣言の名前。
pub open spec fn ents_upto(p: Seq<Sd>, n: nat) -> Seq<Seq<char>>
    decreases n,
{
    if n == 0 || n > p.len() {
        Seq::empty()
    } else if p[n - 1] is Entry {
        ents_upto(p, (n - 1) as nat).push(p[n - 1]->Entry_0)
    } else {
        ents_upto(p, (n - 1) as nat)
    }
}

pub open spec fn fname(d: Sd) -> Seq<char> {
    match d {
        Sd::Fn(f, _, _, _) => f,
        Sd::Entry(x) => x,
        Sd::RecTy(r, _, _) => r,
        Sd::Sum(r, _) => r,
    }
}

pub open spec fn names_of(ds: Seq<Sd>) -> Seq<Seq<char>> {
    Seq::new(ds.len(), |i: int| fname(ds[i]))
}

pub open spec fn pnames(ps: Seq<(Seq<char>, SType)>) -> Seq<Seq<char>> {
    Seq::new(ps.len(), |i: int| ps[i].0)
}

pub open spec fn rparams(ps: Seq<(Seq<char>, SType)>, tb: Seq<(Seq<char>, Option<Ty>, Seq<Seq<char>>, Option<Ty>)>, tagged: bool) -> Seq<(nat, Ty)> {
    Seq::new(ps.len(), |k: int| (k as nat, ty_or_unit(ps[k].1, tb, tagged)))
}

/// 関数の宣言の名前解決。型の注釈と本体は、名前表の全部の項目を引く（規則 2）。
pub open spec fn rfunc(fs: Seq<Seq<char>>, tb: Seq<(Seq<char>, Option<Ty>, Seq<Seq<char>>, Option<Ty>)>, tagged: bool, d: Sd) -> Option<Func> {
    match d {
        Sd::Fn(_, ps, r, b) => if !distinct(pnames(ps)) || !params_ok(ps, tb, tagged) || to_ty(r, tb, tagged) is None {
            None
        } else {
            match rx(fs, tb, tagged, pnames(ps), b) {
                Some(body) => Some(Func { params: rparams(ps, tb, tagged), ret: ty_or_unit(r, tb, tagged), body }),
                None => None,
            }
        },
        Sd::Entry(_) => None,
        Sd::RecTy(_, _, _) => None,
        Sd::Sum(_, _) => None,
    }
}

/// ds[0..n] の各関数の名前解決。
pub open spec fn rfuncs(fs: Seq<Seq<char>>, tb: Seq<(Seq<char>, Option<Ty>, Seq<Seq<char>>, Option<Ty>)>, tagged: bool, ds: Seq<Sd>, n: nat) -> Option<Seq<Func>>
    decreases n,
{
    if n == 0 {
        Some(Seq::empty())
    } else if n > ds.len() {
        None
    } else {
        match (rfuncs(fs, tb, tagged, ds, (n - 1) as nat), rfunc(fs, tb, tagged, ds[n - 1])) {
            (Some(a), Some(f)) => Some(a.push(f)),
            _ => None,
        }
    }
}

/// プログラムの名前解決と entry 検査。関数列と entry の添字を返す。名前表は宣言から作る。
/// 写しの印（tagged）を引数に取る。resolve は印なし（tagged = false）。印つきは resolve_tagged_e（S3b）。
pub open spec fn resolve_t(p: Seq<Sd>, tagged: bool) -> Option<(Seq<Func>, nat)> {
    let ds = fns_upto(p, p.len());
    let fs = names_of(ds);
    let es = ents_upto(p, p.len());
    match decl_table(p, p.len()) {
        None => None,
        Some(tb) => if !distinct(fs) || es.len() != 1 {
            None
        } else {
            match (rfuncs(fs, tb, tagged, ds, ds.len()), idx(fs, es[0], 0)) {
                (Some(funcs), Some(g)) => if g < funcs.len() && funcs[g as int].params.len() == 1 {
                    Some((funcs, g))
                } else {
                    None
                },
                _ => None,
            }
        },
    }
}

/// 印なしの名前解決（resolve_t の印なしの場合）。
pub open spec fn resolve(p: Seq<Sd>) -> Option<(Seq<Func>, nat)> {
    resolve_t(p, false)
}

// ------------------------------------------------------------------ 性質

/// 見つかった位置には x があり、それより前には x はない。
pub proof fn idx_props(s: Seq<Seq<char>>, x: Seq<char>, i: nat)
    ensures
        idx(s, x, i) matches Some(k) ==> i <= k < s.len() && s[k as int] == x && forall|j: int|
            i <= j < k ==> s[j] != x,
        idx(s, x, i) is None ==> forall|j: int| i <= j < s.len() ==> s[j] != x,
    decreases s.len() - i,
{
    if i < s.len() {
        idx_props(s, x, i + 1);
    }
}

/// 名前が相異なる列では、位置 k の名前の位置は k（解決は一意）。
pub proof fn idx_unique(s: Seq<Seq<char>>, k: int)
    requires
        distinct(s),
        0 <= k < s.len(),
    ensures
        idx(s, s[k], 0) == Some(k as nat),
{
    idx_props(s, s[k], 0);
    if let Some(m) = idx(s, s[k], 0) {
        if (m as int) < k {
            assert(s[m as int] != s[k]);
        }
    }
}

/// 基を let で束縛するか（rupdate の条件の否定）。
pub open spec fn deep_upd(upd: Seq<Option<Expr>>, base: Expr) -> bool {
    !(base is Var) && nmissing(upd) > 1
}

/// 基が let で束縛されるか（rrecord の Some の場合）。
pub open spec fn deep_opt(upd: Seq<Option<Expr>>, bx: Option<Expr>) -> bool {
    match bx {
        Some(b) => deep_upd(upd, b),
        None => false,
    }
}

/// 一つの引数の組込みは、引数が scope 整合なら scope 整合。
proof fn builtin1_scoped(b: Builtin, x: Expr, n: nat)
    requires
        scoped(x, n),
    ensures
        scoped(Expr::Builtin(b, seq![x]), n),
{
    reveal_with_fuel(scoped_all, 2);
    reveal_with_fuel(scoped, 2);
    let es = seq![x];
    assert(es.len() == 1);
    assert(es[0] == x);
    assert(scoped_all(es, n, 1));
    assert(scoped_all(es, n, 0));
    assert(scoped(Expr::Builtin(b, es), n));
}

proof fn snds_scoped(e: Expr, n: nat, i: nat)
    requires
        scoped(e, n),
    ensures
        scoped(snds(e, i), n),
    decreases i,
{
    if i > 0 {
        builtin1_scoped(Builtin::Snd, e, n);
        snds_scoped(Expr::Builtin(Builtin::Snd, seq![e]), n, (i - 1) as nat);
    }
}

proof fn rfield_scoped(e: Expr, p: nat, m: nat, n: nat)
    requires
        scoped(e, n),
    ensures
        scoped(rfield(e, p, m), n),
{
    snds_scoped(e, n, p);
    if p + 1 < m {
        builtin1_scoped(Builtin::Fst, snds(e, p), n);
    }
}

proof fn fld_chain_scoped(tb: Seq<(Seq<char>, Option<Ty>, Seq<Seq<char>>, Option<Ty>)>, e: Expr, fls: Seq<Seq<char>>, i: nat, n: nat)
    requires
        scoped(e, n),
    ensures
        fld_chain(tb, e, fls, i) matches Some(x) ==> scoped(x, n),
    decreases fls.len() - i,
{
    if i < fls.len() {
        if let Some((p, m)) = owner_pos(tb, fls[i as int], 0) {
            rfield_scoped(e, p, m, n);
            fld_chain_scoped(tb, rfield(e, p, m), fls, i + 1, n);
        }
    }
}

proof fn fill_scoped(u: Seq<Option<Expr>>, b: Expr, n: nat)
    requires
        scoped(b, n),
        forall|k: int| 0 <= k < u.len() && (#[trigger] u[k]) is Some ==> scoped(u[k]->Some_0, n),
    ensures
        forall|k: int| 0 <= k < fill(u, b).len() ==> scoped(#[trigger] fill(u, b)[k], n),
{
    assert forall|k: int| 0 <= k < fill(u, b).len() implies scoped(#[trigger] fill(u, b)[k], n) by {
        if u[k] is Some {
            assert(fill(u, b)[k] == u[k]->Some_0);
        } else {
            assert(fill(u, b)[k] == rfield(b, k as nat, u.len()));
            rfield_scoped(b, k as nat, u.len(), n);
        }
    }
}

proof fn rbuild_scoped(es: Seq<Expr>, n: nat)
    requires
        es.len() >= 1,
        forall|k: int| 0 <= k < es.len() ==> scoped(#[trigger] es[k], n),
    ensures
        scoped(rbuild(es), n),
    decreases es.len(),
{
    if es.len() > 1 {
        let t = es.drop_first();
        assert forall|k: int| 0 <= k < t.len() implies scoped(#[trigger] t[k], n) by {
            assert(t[k] == es[k + 1]);
        }
        rbuild_scoped(t, n);
        assert(rbuild(es) == Expr::Pair(Box::new(es[0]), Box::new(rbuild(t))));
    }
}

proof fn rupdate_scoped(upd: Seq<Option<Expr>>, base: Expr, n: nat)
    requires
        upd.len() >= 1,
        scoped(base, n),
        forall|k: int| 0 <= k < upd.len() && (#[trigger] upd[k]) is Some ==> scoped(
            upd[k]->Some_0,
            if deep_upd(upd, base) { n + 1 } else { n },
        ),
    ensures
        scoped(rupdate(upd, base, n), n),
{
    if deep_upd(upd, base) {
        let body = rbuild(fill(upd, Expr::Var(n)));
        assert(scoped(Expr::Var(n), n + 1));
        fill_scoped(upd, Expr::Var(n), n + 1);
        rbuild_scoped(fill(upd, Expr::Var(n)), n + 1);
        assert(rupdate(upd, base, n) == Expr::Let(n, Box::new(base), Box::new(body)));
    } else {
        fill_scoped(upd, base, n);
        rbuild_scoped(fill(upd, base), n);
    }
}

proof fn nmissing_zero_all(upd: Seq<Option<Expr>>)
    requires
        nmissing(upd) == 0,
    ensures
        forall|k: int| 0 <= k < upd.len() ==> (#[trigger] upd[k]) is Some,
    decreases upd.len(),
{
    if upd.len() > 0 {
        nmissing_zero_all(upd.drop_last());
        assert forall|k: int| 0 <= k < upd.len() implies (#[trigger] upd[k]) is Some by {
            if k < upd.len() - 1 {
                assert(upd.drop_last()[k] == upd[k]);
            } else {
                assert(upd.last() is Some);
            }
        }
    }
}

pub proof fn nmissing_none(n: nat)
    ensures
        nmissing(Seq::new(n, |j: int| None::<Expr>)) == n,
    decreases n,
{
    if n > 0 {
        let s = Seq::new(n, |j: int| None::<Expr>);
        assert(s.drop_last() =~= Seq::new((n - 1) as nat, |j: int| None::<Expr>));
        nmissing_none((n - 1) as nat);
    }
}

/// 空でない位置の一つを埋めると、書いていない位置の数が一つ減る。
proof fn nmissing_set(u: Seq<Option<Expr>>, j: int, x: Expr)
    requires
        0 <= j < u.len(),
        u[j] is None,
    ensures
        nmissing(u.update(j, Some(x))) + 1 == nmissing(u),
    decreases u.len(),
{
    let v = u.update(j, Some(x));
    assert(u.len() > 0);
    if j == u.len() - 1 {
        assert(v.drop_last() =~= u.drop_last());
        assert(v.last() == Some(x));
        assert(u.last() is None);
    } else {
        assert(v.drop_last() =~= u.drop_last().update(j, Some(x)));
        assert(u.drop_last()[j] is None);
        nmissing_set(u.drop_last(), j, x);
        assert(v.last() == u.last());
    }
}

/// 字段を置いた後、書いていない位置の数は、置く前から置いた字段の数を引いたもの（字段名は相異なる宣言の位置）。
pub proof fn rec_upd_count(fs: Seq<Seq<char>>, tb: Seq<(Seq<char>, Option<Ty>, Seq<Seq<char>>, Option<Ty>)>, tagged: bool, sc: Seq<Seq<char>>, decl: Seq<Seq<char>>, fls: Seq<(Seq<char>, Sx)>, i: nat, u: Seq<Option<Expr>>)
    requires
        i <= fls.len(),
        u.len() == decl.len(),
    ensures
        rec_upd(fs, tb, tagged, sc, decl, fls, i, u) matches Some(u2) ==> u2.len() == u.len() && nmissing(u2) + (fls.len()
            - i) == nmissing(u),
    decreases fls.len() - i,
{
    if i < fls.len() {
        if let Some(j) = idx(decl, fls[i as int].0, 0) {
            idx_props(decl, fls[i as int].0, 0);
            if u[j as int] is None {
                if let Some(x) = rx(fs, tb, tagged, sc, fls[i as int].1) {
                    nmissing_set(u, j as int, x);
                    rec_upd_count(fs, tb, tagged, sc, decl, fls, i + 1, u.update(j as int, Some(x)));
                }
            }
        }
    }
}

proof fn rec_upd_scoped(fs: Seq<Seq<char>>, tb: Seq<(Seq<char>, Option<Ty>, Seq<Seq<char>>, Option<Ty>)>, tagged: bool, sc: Seq<Seq<char>>, decl: Seq<Seq<char>>, fls: Seq<(Seq<char>, Sx)>, i: nat, u: Seq<Option<Expr>>)
    requires
        dsc(sc),
        forall|k: int| 0 <= k < u.len() && (#[trigger] u[k]) is Some ==> scoped(u[k]->Some_0, sc.len()),
    ensures
        rec_upd(fs, tb, tagged, sc, decl, fls, i, u) matches Some(u2) ==> forall|k: int|
            0 <= k < u2.len() && (#[trigger] u2[k]) is Some ==> scoped(u2[k]->Some_0, sc.len()),
    decreases fls, fls.len() - i,
{
    if i < fls.len() {
        if let Some(j) = idx(decl, fls[i as int].0, 0) {
            if u[j as int] is None {
                rx_scoped(fs, tb, tagged, sc, fls[i as int].1);
                if let Some(x) = rx(fs, tb, tagged, sc, fls[i as int].1) {
                    let u1 = u.update(j as int, Some(x));
                    assert forall|k: int| 0 <= k < u1.len() && (#[trigger] u1[k]) is Some implies scoped(
                        u1[k]->Some_0,
                        sc.len(),
                    ) by {
                        if k != j {
                            assert(u1[k] == u[k]);
                        }
                    }
                    rec_upd_scoped(fs, tb, tagged, sc, decl, fls, i + 1, u1);
                }
            }
        }
    }
}

/// 記録の式の本体は、基と字段が scope 整合なら scope 整合（rec_expr の一つの場合の証明）。
proof fn rec_expr_scoped(fs: Seq<Seq<char>>, tb: Seq<(Seq<char>, Option<Ty>, Seq<Seq<char>>, Option<Ty>)>, tagged: bool, sc: Seq<Seq<char>>, decl: Seq<Seq<char>>, fls: Seq<(Seq<char>, Sx)>, bx: Option<Expr>)
    requires
        dsc(sc),
        decl.len() >= 1,
        bx is Some ==> scoped(bx->Some_0, sc.len()),
    ensures
        rec_expr(fs, tb, tagged, sc, decl, fls, bx) matches Some(e) ==> scoped(e, sc.len()),
    decreases fls, fls.len() + 1,
{
    let deep = match bx {
        Some(b) => !(b is Var) && decl.len() >= fls.len() + 2,
        None => false,
    };
    let sc2 = if deep { sc.push(Seq::empty()) } else { sc };
    if deep {
        dsc_push_empty(sc);
    }
    let u0 = Seq::new(decl.len(), |j: int| None::<Expr>);
    assert(forall|k: int| 0 <= k < u0.len() && (#[trigger] u0[k]) is Some ==> scoped(u0[k]->Some_0, sc2.len()));
    rec_upd_scoped(fs, tb, tagged, sc2, decl, fls, 0, u0);
    rec_upd_count(fs, tb, tagged, sc2, decl, fls, 0, u0);
    nmissing_none(decl.len());
    if let Some(u) = rec_upd(fs, tb, tagged, sc2, decl, fls, 0, u0) {
        assert(nmissing(u) + fls.len() == decl.len());
        assert(deep_opt(u, bx) == deep);
        rrecord_scoped(u, bx, sc.len());
    }
}

proof fn rrecord_scoped(u: Seq<Option<Expr>>, bx: Option<Expr>, n: nat)
    requires
        u.len() >= 1,
        bx is Some ==> scoped(bx->Some_0, n),
        forall|k: int| 0 <= k < u.len() && (#[trigger] u[k]) is Some ==> scoped(
            u[k]->Some_0,
            if deep_opt(u, bx) { n + 1 } else { n },
        ),
    ensures
        rrecord(u, bx, n) matches Ok(e) ==> scoped(e, n),
{
    match bx {
        None => {
            if nmissing(u) == 0 {
                nmissing_zero_all(u);
                let es = written(u);
                assert(es.len() == u.len());
                assert forall|k: int| 0 <= k < es.len() implies scoped(#[trigger] es[k], n) by {
                    assert(u[k] is Some);
                    assert(es[k] == u[k]->Some_0);
                }
                rbuild_scoped(es, n);
            }
        },
        Some(b) => {
            if nmissing(u) != 0 {
                rupdate_scoped(u, b, n);
            }
        },
    }
}

/// 解決した変数は可視変数の範囲内を指す（scope 整合性）。
pub open spec fn scoped(e: Expr, n: nat) -> bool
    decreases e, 0nat,
{
    match e {
        Expr::Var(k) => k < n,
        Expr::List(_, es) => scoped_all(es, n, 0),
        Expr::Some(a) => scoped(*a, n),
        Expr::Pair(a, b) => scoped(*a, n) && scoped(*b, n),
        Expr::Builtin(_, es) => scoped_all(es, n, 0),
        Expr::Call(_, es) => scoped_all(es, n, 0),
        Expr::Let(x, a, b) => x == n && scoped(*a, n) && scoped(*b, n + 1),
        Expr::If(c, a, b) => scoped(*c, n) && scoped(*a, n) && scoped(*b, n),
        Expr::Fold(l, i, a, x, b) => a == n && x == n + 1 && scoped(*l, n) && scoped(*i, n) && scoped(*b, n + 2),
        Expr::Match(m, nb, x, b) => x == n && scoped(*m, n) && scoped(*nb, n) && scoped(*b, n + 1),
        Expr::Inj(_, _, _, a) => scoped(*a, n),
        Expr::MatchR(m, x, a, y, b) => x == n && y == n && scoped(*m, n) && scoped(*a, n + 1) && scoped(*b, n + 1),
        _ => true,
    }
}

pub open spec fn scoped_all(es: Seq<Expr>, n: nat, i: nat) -> bool
    decreases es, es.len() - i,
{
    i >= es.len() || (scoped(es[i as int], n) && scoped_all(es, n, i + 1))
}

/// 構築（rec_t）の scope 整合（S3b の印つきの腕を含む）。印つきは基底の検査と印の pair を足す。
proof fn rec_t_scoped(fs: Seq<Seq<char>>, tb: Seq<(Seq<char>, Option<Ty>, Seq<Seq<char>>, Option<Ty>)>, tagged: bool, sc: Seq<Seq<char>>, k: nat, decl: Seq<Seq<char>>, fls: Seq<(Seq<char>, Sx)>, bx: Option<Expr>)
    requires
        dsc(sc),
        decl.len() >= 1,
        bx is Some ==> scoped(bx->Some_0, sc.len()),
    ensures
        rec_t(fs, tb, tagged, sc, k, decl, fls, bx) matches Some(e) ==> scoped(e, sc.len()),
    decreases fls, fls.len() + 2,
{
    reveal_with_fuel(scoped, 2);
    if tagged {
        let bx2 = match bx {
            Some(b) => Some(tfield(b, k, 0, 1, sc.len())),
            None => None,
        };
        if let Some(b) = bx {
            tfield_scoped(b, k, 0, 1, sc.len());
        }
        rec_expr_scoped(fs, tb, tagged, sc, decl, fls, bx2);
        if let Some(e) = rec_expr(fs, tb, tagged, sc, decl, fls, bx2) {
            tag_expr_scoped(k, sc.len());
        }
    } else {
        rec_expr_scoped(fs, tb, tagged, sc, decl, fls, bx);
    }
}

/// 参照（Sx::Fld）の scope 整合（印なし・印つき）。rx_scoped の本体から分けて、rlimit を抑える。
proof fn rx_fld_scoped(fs: Seq<Seq<char>>, tb: Seq<(Seq<char>, Option<Ty>, Seq<Seq<char>>, Option<Ty>)>, tagged: bool, sc: Seq<Seq<char>>, e: Sx)
    requires
        dsc(sc),
        e is Fld,
    ensures
        rx(fs, tb, tagged, sc, e) matches Some(x) ==> scoped(x, sc.len()),
    decreases e, 0nat,
{
    if let Sx::Fld(a, fls) = e {
        rx_scoped(fs, tb, tagged, sc, *a);
        if let Some(x) = rx(fs, tb, tagged, sc, *a) {
            if tagged {
                fld_chain_t_scoped(tb, x, fls, 0, sc.len());
            } else {
                fld_chain_scoped(tb, x, fls, 0, sc.len());
            }
        }
    }
}

/// 記録の式（Sx::Rec）は scope 整合（rx_scoped の記録の腕。本体を分けて、rlimit を抑える）。
proof fn rx_rec_scoped(fs: Seq<Seq<char>>, tb: Seq<(Seq<char>, Option<Ty>, Seq<Seq<char>>, Option<Ty>)>, tagged: bool, sc: Seq<Seq<char>>, e: Sx)
    requires
        dsc(sc),
        e is Rec,
    ensures
        rx(fs, tb, tagged, sc, e) matches Some(x) ==> scoped(x, sc.len()),
    decreases e, 0nat,
{
    if let Sx::Rec(r, fls, base) = e {
        idx_props(tnames(tb), r, 0);
        if let Some(k) = idx(tnames(tb), r, 0) {
            if is_rec_slot(tb[k as int].2) && idx(sc, Seq::empty(), 0) is None {
                match base {
                    None => rec_t_scoped(fs, tb, tagged, sc, k as nat, tb[k as int].2, fls, None),
                    Some(b) => {
                        rx_scoped(fs, tb, tagged, sc, *b);
                        if let Some(bx) = rx(fs, tb, tagged, sc, *b) {
                            rec_t_scoped(fs, tb, tagged, sc, k as nat, tb[k as int].2, fls, Some(bx));
                        }
                    },
                }
            }
        }
    }
}

/// rx_scoped の束縛（Let）の腕。rx_scoped の本体を腕ごとに分けて、rlimit を抑える。
proof fn rx_let_scoped(fs: Seq<Seq<char>>, tb: Seq<(Seq<char>, Option<Ty>, Seq<Seq<char>>, Option<Ty>)>, tagged: bool, sc: Seq<Seq<char>>, e: Sx)
    requires
        dsc(sc),
        e is Let,
    ensures
        rx(fs, tb, tagged, sc, e) matches Some(x) ==> scoped(x, sc.len()),
    decreases e, 0nat,
{
    if let Sx::Let(x, a, b) = e {
        idx_props(sc, x, 0);
        rx_scoped(fs, tb, tagged, sc, *a);
        if idx(sc, x, 0) is None {
            let s2 = sc.push(x);
            assert forall|i: int, j: int| 0 <= i < j < s2.len() && s2[i].len() > 0 implies s2[i] != s2[j] by {
                if j == sc.len() {
                    assert(sc[i] != x);
                }
            }
            rx_scoped(fs, tb, tagged, s2, *b);
        }
    }
}

/// rx_scoped の畳み込み（Fold）の腕。
proof fn rx_fold_scoped(fs: Seq<Seq<char>>, tb: Seq<(Seq<char>, Option<Ty>, Seq<Seq<char>>, Option<Ty>)>, tagged: bool, sc: Seq<Seq<char>>, e: Sx)
    requires
        dsc(sc),
        e is Fold,
    ensures
        rx(fs, tb, tagged, sc, e) matches Some(x) ==> scoped(x, sc.len()),
    decreases e, 0nat,
{
    if let Sx::Fold(l, i, a, x, b) = e {
        idx_props(sc, a, 0);
        idx_props(sc, x, 0);
        rx_scoped(fs, tb, tagged, sc, *l);
        rx_scoped(fs, tb, tagged, sc, *i);
        if !(a == x || idx(sc, a, 0) is Some || idx(sc, x, 0) is Some) {
            let s2 = sc.push(a).push(x);
            assert forall|p: int, q: int| 0 <= p < q < s2.len() && s2[p].len() > 0 implies s2[p] != s2[q] by {
                if q == sc.len() + 1 {
                    if p < sc.len() {
                        assert(sc[p] != x);
                    }
                } else if q == sc.len() {
                    assert(sc[p] != a);
                }
            }
            rx_scoped(fs, tb, tagged, s2, *b);
        }
    }
}

/// rx_scoped の一致（Match）の腕。
proof fn rx_match_scoped(fs: Seq<Seq<char>>, tb: Seq<(Seq<char>, Option<Ty>, Seq<Seq<char>>, Option<Ty>)>, tagged: bool, sc: Seq<Seq<char>>, e: Sx)
    requires
        dsc(sc),
        e is Match,
    ensures
        rx(fs, tb, tagged, sc, e) matches Some(x) ==> scoped(x, sc.len()),
    decreases e, 0nat,
{
    if let Sx::Match(m, n, x, b) = e {
        idx_props(sc, x, 0);
        rx_scoped(fs, tb, tagged, sc, *m);
        rx_scoped(fs, tb, tagged, sc, *n);
        if idx(sc, x, 0) is None {
            let s2 = sc.push(x);
            assert forall|i: int, j: int| 0 <= i < j < s2.len() && s2[i].len() > 0 implies s2[i] != s2[j] by {
                if j == sc.len() {
                    assert(sc[i] != x);
                }
            }
            rx_scoped(fs, tb, tagged, s2, *b);
        }
    }
}

/// rx_scoped の二つの束縛を持つ一致（MatchR）の腕。
proof fn rx_matchr_scoped(fs: Seq<Seq<char>>, tb: Seq<(Seq<char>, Option<Ty>, Seq<Seq<char>>, Option<Ty>)>, tagged: bool, sc: Seq<Seq<char>>, e: Sx)
    requires
        dsc(sc),
        e is MatchR,
    ensures
        rx(fs, tb, tagged, sc, e) matches Some(x) ==> scoped(x, sc.len()),
    decreases e, 0nat,
{
    if let Sx::MatchR(m, x, a, y, b) = e {
        idx_props(sc, x, 0);
        idx_props(sc, y, 0);
        rx_scoped(fs, tb, tagged, sc, *m);
        if idx(sc, x, 0) is None {
            let s2 = sc.push(x);
            assert forall|i: int, j: int| 0 <= i < j < s2.len() && s2[i].len() > 0 implies s2[i] != s2[j] by {
                if j == sc.len() {
                    assert(sc[i] != x);
                }
            }
            rx_scoped(fs, tb, tagged, s2, *a);
        }
        if idx(sc, y, 0) is None {
            let s3 = sc.push(y);
            assert forall|i: int, j: int| 0 <= i < j < s3.len() && s3[i].len() > 0 implies s3[i] != s3[j] by {
                if j == sc.len() {
                    assert(sc[i] != y);
                }
            }
            rx_scoped(fs, tb, tagged, s3, *b);
        }
    }
}

/// 名前解決の結果は scope 整合で、scope 内の名前は常に相異なる（シャドーがない）。
/// 構築子の中身の式（字段が 0 か 1 個）は、字段の式が範囲に収まれば収まる。
proof fn pay1_scoped(xs: Seq<Expr>, m: nat)
    requires
        scoped_all(xs, m, 0),
    ensures
        scoped(pay1(xs), m),
{
    if xs.len() > 0 {
        assert(scoped(xs[0], m));
    }
}

/// 層 j から作る構築子の値は、中身が範囲に収まれば収まる。
proof fn inj_from_scoped(t: Ty, n: nat, k: nat, j: nat, p: Expr, m: nat)
    requires
        scoped(p, m),
        j <= k,
    ensures
        inj_from(t, n, k, j, p) matches Some(x) ==> scoped(x, m),
    decreases k - j,
{
    if j < k {
        inj_from_scoped(t, n, k, j + 1, p, m);
    }
}

/// 構築子の値は、中身が範囲に収まれば収まる。
proof fn ctor_val_scoped(tagged: bool, i: nat, t: Ty, n: nat, k: nat, p: Expr, m: nat)
    requires
        scoped(p, m),
    ensures
        ctor_val(tagged, i, t, n, k, p) matches Some(x) ==> scoped(x, m),
{
    inj_from_scoped(t, n, k, 0, p, m);
    tag_expr_scoped(i, m);
}

/// 構築子への呼出しは、字段の式が範囲に収まれば収まる。
proof fn rctor_scoped(tb: Seq<(Seq<char>, Option<Ty>, Seq<Seq<char>>, Option<Ty>)>, tagged: bool, c: Seq<char>, xs: Seq<Expr>, m: nat)
    requires
        scoped_all(xs, m, 0),
    ensures
        rctor(tb, tagged, c, xs) matches Some(x) ==> scoped(x, m),
{
    pay1_scoped(xs, m);
    if let Some((i, k, mm)) = vlook(tb, c) {
        if mm > 1 || mm != xs.len() || k >= tb[i as int].2.len() {
        } else {
            match (if tagged { tb[i as int].3 } else { tb[i as int].1 }) {
                Some(t) => ctor_val_scoped(tagged, i, t, tb[i as int].2.len(), k, pay1(xs), m),
                None => {},
            }
        }
    }
}

/// 直和型の枝の鎖（smatch_from）の scope 整合。被験式が scope sc で整合し、枝の本体が解決できれば、scope sc で整合する。
proof fn smatch_from_scoped(fs: Seq<Seq<char>>, tb: Seq<(Seq<char>, Option<Ty>, Seq<Seq<char>>, Option<Ty>)>, tagged: bool, sc: Seq<Seq<char>>, arms: Seq<(Spat, Sx)>, n: nat, j: nat, s: Expr)
    requires
        dsc(sc),
        scoped(s, sc.len()),
    ensures
        smatch_from(fs, tb, tagged, sc, arms, n, j, s) matches Some(x) ==> scoped(x, sc.len()),
    decreases arms, n - j,
{
    reveal_with_fuel(scoped, 2);
    reveal_with_fuel(smatch_from, 2);
    if j < n && j < arms.len() {
        if let Some(b) = arm_bind(arms[j as int].0) {
            if !(b.len() > 0 && idx(sc, b, 0) is Some) {
                if b.len() > 0 {
                    idx_props(sc, b, 0);
                    dsc_push(sc, b);
                } else {
                    dsc_push_empty(sc);
                }
                rx_scoped(fs, tb, tagged, sc.push(b), arms[j as int].1);
                if let Some(body) = rx(fs, tb, tagged, sc.push(b), arms[j as int].1) {
                    if j + 1 == n {
                        assert(scoped(Expr::Let(sc.len(), Box::new(s), Box::new(body)), sc.len()));
                    } else {
                        dsc_push_empty(sc);
                        smatch_from_scoped(fs, tb, tagged, sc.push(Seq::empty()), arms, n, j + 1, Expr::Var(sc.len()));
                        if let Some(rest) = smatch_from(fs, tb, tagged, sc.push(Seq::empty()), arms, n, j + 1, Expr::Var(sc.len())) {
                            assert(scoped(Expr::MatchR(Box::new(s), sc.len(), Box::new(body), sc.len(), Box::new(rest)), sc.len()));
                        }
                    }
                }
            }
        }
    }
}

/// 直和型の枝の頭（smatch_top、印つきの印の検査を含む）の scope 整合。
proof fn smatch_top_scoped(fs: Seq<Seq<char>>, tb: Seq<(Seq<char>, Option<Ty>, Seq<Seq<char>>, Option<Ty>)>, tagged: bool, sc: Seq<Seq<char>>, arms: Seq<(Spat, Sx)>, i: nat, n: nat, rm: Expr)
    requires
        dsc(sc),
        scoped(rm, sc.len()),
    ensures
        smatch_top(fs, tb, tagged, sc, arms, i, n, rm) matches Some(x) ==> scoped(x, sc.len()),
    decreases arms, n + 1,
{
    reveal_with_fuel(scoped, 3);
    if tagged {
        let d = sc.len();
        dsc_push_empty(sc);
        dsc_push_empty(sc.push(Seq::empty()));
        builtin1_scoped(Builtin::Snd, Expr::Var(d), d + 2);
        smatch_from_scoped(fs, tb, tagged, sc.push(Seq::empty()).push(Seq::empty()), arms, n, 0, Expr::Builtin(Builtin::Snd, seq![Expr::Var(d)]));
        tag_expr_scoped(i, d + 1);
        builtin1_scoped(Builtin::Fst, Expr::Var(d), d + 1);
        builtin2_scoped(Builtin::Eq, Expr::Builtin(Builtin::Fst, seq![Expr::Var(d)]), tag_expr(i), d + 1);
    } else {
        smatch_from_scoped(fs, tb, tagged, sc, arms, n, 0, rm);
    }
}

/// 直和型の枝（Sx::SumMatch）の scope 整合（rx_scoped の腕）。
proof fn rx_sum_scoped(fs: Seq<Seq<char>>, tb: Seq<(Seq<char>, Option<Ty>, Seq<Seq<char>>, Option<Ty>)>, tagged: bool, sc: Seq<Seq<char>>, e: Sx)
    requires
        dsc(sc),
        e is SumMatch,
    ensures
        rx(fs, tb, tagged, sc, e) matches Some(x) ==> scoped(x, sc.len()),
    decreases e, 0nat,
{
    if let Sx::SumMatch(m, arms) = e {
        rx_scoped(fs, tb, tagged, sc, *m);
        if let Some(i) = arms_sum(tb, arms) {
            if let Some(rm) = rx(fs, tb, tagged, sc, *m) {
                smatch_top_scoped(fs, tb, tagged, sc, arms, i, tb[i as int].2.len(), rm);
            }
        }
    }
}

pub proof fn rx_scoped(fs: Seq<Seq<char>>, tb: Seq<(Seq<char>, Option<Ty>, Seq<Seq<char>>, Option<Ty>)>, tagged: bool, sc: Seq<Seq<char>>, e: Sx)
    requires
        dsc(sc),
    ensures
        rx(fs, tb, tagged, sc, e) matches Some(x) ==> scoped(x, sc.len()),
    decreases e, 1nat,
{
    match e {
        Sx::Var(x) => {
            idx_props(sc, x, 0);
            if x.len() != 0 && idx(sc, x, 0) is None {
                rctor_scoped(tb, tagged, x, Seq::empty(), sc.len());
            }
        },
        Sx::Str(w) => str_scoped(w, sc.len(), 0),
        Sx::List(_, es) => rxs_scoped(fs, tb, tagged, sc, es, 0),
        Sx::Some(a) => rx_scoped(fs, tb, tagged, sc, *a),
        Sx::Pair(a, b) => {
            rx_scoped(fs, tb, tagged, sc, *a);
            rx_scoped(fs, tb, tagged, sc, *b);
        },
        Sx::Builtin(_, es) => rxs_scoped(fs, tb, tagged, sc, es, 0),
        Sx::Call(f, es) => {
            rxs_scoped(fs, tb, tagged, sc, es, 0);
            if idx(fs, f, 0) is None && es.len() != 0 {
                if let Some(xs) = rxs(fs, tb, tagged, sc, es, 0) {
                    rctor_scoped(tb, tagged, f, xs, sc.len());
                }
            }
        },
        Sx::Let(..) => rx_let_scoped(fs, tb, tagged, sc, e),
        Sx::If(c, a, b) => {
            rx_scoped(fs, tb, tagged, sc, *c);
            rx_scoped(fs, tb, tagged, sc, *a);
            rx_scoped(fs, tb, tagged, sc, *b);
        },
        Sx::Fold(..) => rx_fold_scoped(fs, tb, tagged, sc, e),
        Sx::Match(..) => rx_match_scoped(fs, tb, tagged, sc, e),
        Sx::Fld(..) => rx_fld_scoped(fs, tb, tagged, sc, e),
        Sx::Rec(..) => rx_rec_scoped(fs, tb, tagged, sc, e),
        Sx::Inj(_, _, _, a) => rx_scoped(fs, tb, tagged, sc, *a),
        Sx::MatchR(..) => rx_matchr_scoped(fs, tb, tagged, sc, e),
        Sx::SumMatch(..) => rx_sum_scoped(fs, tb, tagged, sc, e),
        _ => {},
    }
}

pub proof fn rxs_scoped(fs: Seq<Seq<char>>, tb: Seq<(Seq<char>, Option<Ty>, Seq<Seq<char>>, Option<Ty>)>, tagged: bool, sc: Seq<Seq<char>>, es: Seq<Sx>, i: nat)
    requires
        dsc(sc),
    ensures
        rxs(fs, tb, tagged, sc, es, i) matches Some(xs) ==> scoped_all(xs, sc.len(), 0),
    decreases es, es.len() - i,
{
    if i < es.len() {
        rx_scoped(fs, tb, tagged, sc, es[i as int]);
        rxs_scoped(fs, tb, tagged, sc, es, i + 1);
        if let Some(xs) = rxs(fs, tb, tagged, sc, es, i) {
            let x = rx(fs, tb, tagged, sc, es[i as int])->Some_0;
            let ys = rxs(fs, tb, tagged, sc, es, i + 1)->Some_0;
            scoped_all_cons(x, ys, sc.len(), 0);
        }
    }
}

proof fn str_scoped(w: Seq<char>, n: nat, i: nat)
    ensures
        scoped_all(str_exprs(w), n, i),
    decreases w.len() - i,
{
    let es = str_exprs(w);
    assert(es.len() == w.len());
    if i < w.len() {
        str_scoped(w, n, i + 1);
        assert(es[i as int] == Expr::Char(w[i as int] as u32 as int));
        assert(scoped(es[i as int], n));
    }
}

proof fn scoped_all_cons(x: Expr, ys: Seq<Expr>, n: nat, i: nat)
    requires
        scoped(x, n),
        scoped_all(ys, n, i),
    ensures
        scoped_all(seq![x] + ys, n, i + 1) && (i == 0 ==> scoped_all(seq![x] + ys, n, 0)),
    decreases ys.len() - i,
{
    let s = seq![x] + ys;
    assert(s.len() == ys.len() + 1);
    if i < ys.len() {
        assert(s[(i + 1) as int] == ys[i as int]);
        scoped_all_cons(x, ys, n, i + 1);
        assert(scoped_all(s, n, i + 1));
    }
    if i == 0 {
        assert(s[0] == x);
        assert(scoped_all(s, n, 1));
        assert(scoped_all(s, n, 0));
    }
}

// ------------------------------------------------------------------ exec

pub open spec fn vnames(v: Seq<Vec<char>>) -> Seq<Seq<char>> {
    Seq::new(v.len(), |i: int| v[i]@)
}

/// exec の名前表の view（字段名の Vec の列は vnames で写す）。
pub open spec fn vtb(tb: Seq<(Vec<char>, Option<Ty>, Vec<Vec<char>>, Option<Ty>)>) -> Seq<(Seq<char>, Option<Ty>, Seq<Seq<char>>, Option<Ty>)> {
    Seq::new(tb.len(), |i: int| (tb[i].0@, tb[i].1, vnames(tb[i].2@), tb[i].3))
}

pub fn idx_e(s: &Vec<Vec<char>>, x: &Vec<char>) -> (r: Option<usize>)
    ensures
        match r {
            Some(k) => idx(vnames(s@), x@, 0) == Some(k as nat) && k < s@.len(),
            None => idx(vnames(s@), x@, 0) is None,
        },
{
    let ghost v = vnames(s@);
    let mut i: usize = 0;
    while i < s.len()
        invariant
            v == vnames(s@),
            i <= s@.len(),
            idx(v, x@, 0) == idx(v, x@, i as nat),
        decreases s@.len() - i,
    {
        proof {
            assert(v[i as int] == s@[i as int]@);
        }
        if eq_chars(&s[i], x) {
            return Some(i);
        }
        i += 1;
    }
    None
}

pub fn distinct_e(s: &Vec<Vec<char>>) -> (r: bool)
    ensures
        r == distinct(vnames(s@)),
{
    let ghost v = vnames(s@);
    let mut j: usize = 0;
    while j < s.len()
        invariant
            v == vnames(s@),
            j <= s@.len(),
            forall|a: int, b: int| 0 <= a < b < j ==> v[a] != v[b],
        decreases s@.len() - j,
    {
        let mut i: usize = 0;
        while i < j
            invariant
                v == vnames(s@),
                i <= j < s@.len(),
                forall|a: int| 0 <= a < i ==> v[a] != v[j as int],
            decreases j - i,
        {
            proof {
                assert(v[i as int] == s@[i as int]@);
                assert(v[j as int] == s@[j as int]@);
            }
            if eq_chars(&s[i], &s[j]) {
                return false;
            }
            i += 1;
        }
        j += 1;
    }
    true
}

/// 空の名前（x@ が空）を足した列の名前の列は、名前の列に空の名前を足したもの（印の束縛の位置）。
pub proof fn vnames_push_nil(a: Seq<Vec<char>>, x: Vec<char>)
    requires
        x@ == Seq::<char>::empty(),
    ensures
        vnames(a.push(x)) == vnames(a).push(Seq::empty()),
{
    assert(vnames(a.push(x)) =~= vnames(a).push(Seq::empty()));
}

pub proof fn vnames_push(a: Seq<Vec<char>>, x: Vec<char>)
    ensures
        vnames(a.push(x)) == vnames(a).push(x@),
{
    assert(vnames(a.push(x)) =~= vnames(a).push(x@));
}

proof fn view_exprs_push(a: Vec<EExpr>, b: Vec<EExpr>, e: EExpr)
    requires
        b@ == a@.push(e),
    ensures
        view_exprs(b) == view_exprs(a) + seq![view_expr(e)],
{
    assert(view_exprs(b) =~= view_exprs(a) + seq![view_expr(e)]);
}

pub open spec fn cato(u: Seq<Expr>, o: Option<Seq<Expr>>) -> Option<Seq<Expr>> {
    match o {
        Some(w) => Some(u + w),
        None => None,
    }
}

/// 名前表の中で名前 x の位置（to_ty の Named の腕と同じ）。
fn tidx_e(tb: &Vec<(Vec<char>, Option<Ty>, Vec<Vec<char>>, Option<Ty>)>, x: &Vec<char>) -> (r: Option<usize>)
    ensures
        match r {
            Some(k) => idx(tnames(vtb(tb@)), x@, 0) == Some(k as nat) && k < tb@.len(),
            None => idx(tnames(vtb(tb@)), x@, 0) is None,
        },
{
    let ghost v = tnames(vtb(tb@));
    let mut i: usize = 0;
    while i < tb.len()
        invariant
            v == tnames(vtb(tb@)),
            i <= tb@.len(),
            idx(v, x@, 0) == idx(v, x@, i as nat),
        decreases tb@.len() - i,
    {
        proof {
            assert(v[i as int] == tb@[i as int].0@);
        }
        if eq_chars(&tb[i].0, x) {
            return Some(i);
        }
        i += 1;
    }
    None
}

/// 名前表の項目の印なしの展開を複製する。
fn clone_opt(o: &Option<Ty>) -> (r: Option<Ty>)
    ensures
        r == *o,
{
    match o {
        Some(u) => Some(ty_clone(u)),
        None => None,
    }
}

/// 印の型の exec 版（tag_ty の exec 版）。nominal.rs の印の型（tag_ty）が、これを呼ぶ。
pub fn tag_ty_e(k: usize) -> (r: Ty)
    ensures
        r == tag_ty(k as nat),
    decreases k,
{
    if k == 0 {
        Ty::Pair(Box::new(Ty::Unit), Box::new(Ty::Unit))
    } else {
        Ty::Pair(Box::new(Ty::Unit), Box::new(tag_ty_e(k - 1)))
    }
}

/// 表面の型から核の型へ（to_ty の exec 版）。
pub fn to_ty_e(t: &STy, tb: &Vec<(Vec<char>, Option<Ty>, Vec<Vec<char>>, Option<Ty>)>, tagged: bool) -> (r: Option<Ty>)
    ensures
        match r {
            Some(u) => to_ty(vty(*t), vtb(tb@), tagged) == Some(u),
            None => to_ty(vty(*t), vtb(tb@), tagged) is None,
        },
    decreases t,
{
    match t {
        STy::Int => Some(Ty::Int),
        STy::Bool => Some(Ty::Bool),
        STy::Unit => Some(Ty::Unit),
        STy::Char => Some(Ty::Char),
        STy::List(a) => match to_ty_e(a, tb, tagged) {
            Some(u) => Some(Ty::List(Box::new(u))),
            None => None,
        },
        STy::Option(a) => match to_ty_e(a, tb, tagged) {
            Some(u) => Some(Ty::Option(Box::new(u))),
            None => None,
        },
        STy::Pair(a, b) => match (to_ty_e(a, tb, tagged), to_ty_e(b, tb, tagged)) {
            (Some(u), Some(v)) => Some(Ty::Pair(Box::new(u), Box::new(v))),
            _ => None,
        },
        STy::Result(a, b) => match (to_ty_e(a, tb, tagged), to_ty_e(b, tb, tagged)) {
            (Some(u), Some(v)) => Some(Ty::Result(Box::new(u), Box::new(v))),
            _ => None,
        },
        STy::Named(x) => match tidx_e(tb, x) {
            Some(k) => if tagged {
                match clone_opt(&tb[k].3) {
                    Some(s) => Some(Ty::Pair(Box::new(tag_ty_e(k)), Box::new(s))),
                    None => None,
                }
            } else {
                clone_opt(&tb[k].1)
            },
            None => None,
        },
        STy::Dict(a, b) => match (to_ty_e(a, tb, tagged), to_ty_e(b, tb, tagged)) {
            (Some(u), Some(v)) => Some(Ty::List(Box::new(Ty::Pair(Box::new(u), Box::new(v))))),
            _ => None,
        },
    }
}

/// 型の名前が、名前表の項目だけを引くか（tyn の exec 版）。
fn tyn_e(t: &STy, tb: &Vec<(Vec<char>, Option<Ty>, Vec<Vec<char>>, Option<Ty>)>) -> (r: bool)
    ensures
        r == tyn(vty(*t), vtb(tb@)),
    decreases t,
{
    match t {
        STy::Int => true,
        STy::Bool => true,
        STy::Unit => true,
        STy::Char => true,
        STy::List(a) => tyn_e(a, tb),
        STy::Option(a) => tyn_e(a, tb),
        STy::Pair(a, b) => tyn_e(a, tb) && tyn_e(b, tb),
        STy::Result(a, b) => tyn_e(a, tb) && tyn_e(b, tb),
        STy::Named(x) => tidx_e(tb, x).is_some(),
        STy::Dict(a, b) => tyn_e(a, tb) && tyn_e(b, tb),
    }
}

/// 字段名の列（pnames の exec 版）。
fn field_names_e(fs: &Vec<(Vec<char>, STy)>) -> (r: Vec<Vec<char>>)
    ensures
        vnames(r@) == pnames(vps(fs@)),
{
    let mut out: Vec<Vec<char>> = Vec::new();
    let mut i: usize = 0;
    proof {
        assert(vnames(out@) =~= pnames(vps(fs@)).subrange(0, 0));
    }
    while i < fs.len()
        invariant
            i <= fs@.len(),
            vnames(out@) == pnames(vps(fs@)).subrange(0, i as int),
        decreases fs@.len() - i,
    {
        let c = clone_chars(&fs[i].0);
        let ghost o0 = out@;
        proof {
            assert(c@ == fs@[i as int].0@);
        }
        out.push(c);
        proof {
            vnames_push(o0, out@[o0.len() as int]);
            assert(vnames(out@) =~= pnames(vps(fs@)).subrange(0, (i + 1) as int));
        }
        i += 1;
    }
    proof {
        assert(pnames(vps(fs@)).subrange(0, fs@.len() as int) =~= pnames(vps(fs@)));
    }
    out
}

/// 字段名 x が、名前表のどの記録の字段でもないか（fresh の exec 版）。
fn fresh_e(tb: &Vec<(Vec<char>, Option<Ty>, Vec<Vec<char>>, Option<Ty>)>, x: &Vec<char>) -> (r: bool)
    ensures
        r == fresh(vtb(tb@), x@),
{
    let mut j: usize = 0;
    while j < tb.len()
        invariant
            j <= tb@.len(),
            forall|a: int| 0 <= a < j ==> idx(vnames(tb@[a].2@), x@, 0) is None,
        decreases tb@.len() - j,
    {
        if idx_e(&tb[j].2, x).is_some() {
            proof {
                assert(vtb(tb@)[j as int].2 == vnames(tb@[j as int].2@));
            }
            return false;
        }
        j += 1;
    }
    true
}

/// 記録の展開（rec_from(…, 0, tagged) の exec 版）。字段の列の末尾から組み立てる。tagged は印つきの展開か。
fn rec_exp_e(fs: &Vec<(Vec<char>, STy)>, tb: &Vec<(Vec<char>, Option<Ty>, Vec<Vec<char>>, Option<Ty>)>, tagged: bool) -> (r: Option<Ty>)
    ensures
        r == rec_from(vps(fs@), 0, vtb(tb@), tagged),
{
    let n = fs.len();
    if n == 0 {
        return None;
    }
    let mut i: usize = n - 1;
    let mut acc: Option<Ty> = to_ty_e(&fs[i].1, tb, tagged);
    while i > 0
        invariant
            n == fs@.len(),
            i < n,
            acc == rec_from(vps(fs@), i as nat, vtb(tb@), tagged),
        decreases i,
    {
        i -= 1;
        let u = to_ty_e(&fs[i].1, tb, tagged);
        acc = match (u, acc) {
            (Some(u), Some(v)) => Some(Ty::Pair(Box::new(u), Box::new(v))),
            _ => None,
        };
    }
    acc
}

/// 記録の字段の列が規則 1・4 を満たすか（fields_ok の exec 版）。fnv は fs の字段名の列。
fn fields_ok_e(fs: &Vec<(Vec<char>, STy)>, tb: &Vec<(Vec<char>, Option<Ty>, Vec<Vec<char>>, Option<Ty>)>, fnv: &Vec<Vec<char>>) -> (r: bool)
    requires
        fnv@.len() == fs@.len(),
        vnames(fnv@) == pnames(vps(fs@)),
    ensures
        r == fields_ok(vps(fs@), vtb(tb@)),
{
    if !distinct_e(fnv) {
        proof {
            assert(!distinct(pnames(vps(fs@))));
        }
        return false;
    }
    let mut j: usize = 0;
    while j < fs.len()
        invariant
            j <= fs@.len(),
            fnv@.len() == fs@.len(),
            vnames(fnv@) == pnames(vps(fs@)),
            forall|a: int| 0 <= a < j ==> fresh(vtb(tb@), fnv@[a]@) && tyn(vty(fs@[a].1), vtb(tb@)),
        decreases fs@.len() - j,
    {
        let fok = fresh_e(tb, &fnv[j]);
        let tok = tyn_e(&fs[j].1, tb);
        if !fok || !tok {
            proof {
                assert(vnames(fnv@)[j as int] == pnames(vps(fs@))[j as int]);
                assert(pnames(vps(fs@))[j as int] == vps(fs@)[j as int].0);
                assert(vnames(fnv@)[j as int] == fnv@[j as int]@);
                assert(vps(fs@)[j as int].0 == fnv@[j as int]@);
                assert(vps(fs@)[j as int].1 == vty(fs@[j as int].1));
                assert(!(fresh(vtb(tb@), vps(fs@)[j as int].0) && tyn(vps(fs@)[j as int].1, vtb(tb@))));
                assert(!fields_ok(vps(fs@), vtb(tb@)));
            }
            return false;
        }
        j += 1;
    }
    proof {
        assert forall|i: int| 0 <= i < fs@.len() implies fresh(vtb(tb@), #[trigger] vps(fs@)[i].0) && tyn(vps(fs@)[i].1, vtb(tb@)) by {
            assert(pnames(vps(fs@))[i] == vps(fs@)[i].0);
            assert(vnames(fnv@)[i] == pnames(vps(fs@))[i]);
            assert(vnames(fnv@)[i] == fnv@[i]@);
            assert(vps(fs@)[i].0 == fnv@[i]@);
            assert(vps(fs@)[i].1 == vty(fs@[i].1));
        }
        assert(distinct(pnames(vps(fs@))));
        assert(fields_ok(vps(fs@), vtb(tb@)));
    }
    true
}

/// 直和型の中身の型が、名前表の前の項目だけを引くか（vars_ok の exec 版）。
fn vars_ok_e(vs: &Vec<(Vec<char>, Vec<STy>)>, tb: &Vec<(Vec<char>, Option<Ty>, Vec<Vec<char>>, Option<Ty>)>) -> (r: bool)
    ensures
        r == vars_ok(vvars(vs@), vtb(tb@)),
{
    proof {
        reveal(vars_ok);
    }
    let mut a: usize = 0;
    while a < vs.len()
        invariant
            a <= vs@.len(),
            forall|c: int, b: int| 0 <= c < a && 0 <= b < vs@[c].1@.len() ==> tyn(vty(vs@[c].1@[b]), vtb(tb@)),
        decreases vs@.len() - a,
    {
        let mut b: usize = 0;
        while b < vs[a].1.len()
            invariant
                a < vs@.len(),
                b <= vs@[a as int].1@.len(),
                forall|c: int, k: int| 0 <= c < a && 0 <= k < vs@[c].1@.len() ==> tyn(vty(vs@[c].1@[k]), vtb(tb@)),
                forall|k: int| 0 <= k < b ==> tyn(vty(vs@[a as int].1@[k]), vtb(tb@)),
            decreases vs@[a as int].1@.len() - b,
        {
            let ok_t = tyn_e(&vs[a].1[b], tb);
            if !ok_t {
                proof {
                    reveal(vars_ok);
                    assert(vvars(vs@)[a as int].1[b as int] == vty(vs@[a as int].1@[b as int]));
                    assert(!vars_ok(vvars(vs@), vtb(tb@)));
                }
                return false;
            }
            b += 1;
        }
        a += 1;
    }
    proof {
        reveal(vars_ok);
        assert forall|i: int, k: int| 0 <= i < vvars(vs@).len() && 0 <= k < vvars(vs@)[i].1.len() implies tyn(#[trigger] vvars(vs@)[i].1[k], vtb(tb@)) by {
            assert(vvars(vs@)[i].1[k] == vty(vs@[i].1@[k]));
        }
        assert(vars_ok(vvars(vs@), vtb(tb@)));
    }
    true
}

/// 型が名前を書いているか（sty_mentions の exec 版）。
fn sty_mentions_e(t: &STy, r: &Vec<char>) -> (res: bool)
    ensures
        res == sty_mentions(vty(*t), r@),
    decreases t,
{
    match t {
        STy::Int => false,
        STy::Bool => false,
        STy::Unit => false,
        STy::Char => false,
        STy::List(a) => sty_mentions_e(a, r),
        STy::Option(a) => sty_mentions_e(a, r),
        STy::Pair(a, b) => sty_mentions_e(a, r) || sty_mentions_e(b, r),
        STy::Result(a, b) => sty_mentions_e(a, r) || sty_mentions_e(b, r),
        STy::Named(x) => eq_chars(x, r),
        STy::Dict(a, b) => sty_mentions_e(a, r) || sty_mentions_e(b, r),
    }
}

/// 再帰する直和型の項か（sty_rec_item の exec 版）。
fn sty_rec_item_e(t: &STy, r: &Vec<char>) -> (res: bool)
    ensures
        res == sty_rec_item(vty(*t), r@),
{
    match t {
        STy::Int => true,
        STy::Bool => true,
        STy::Named(x) => eq_chars(x, r),
        _ => false,
    }
}

/// 直和型の項のどれも名前 r を書かない（rec_items の一つ目の選択肢）。
fn plain_items_e(vs: &Vec<(Vec<char>, Vec<STy>)>, r: &Vec<char>) -> (res: bool)
    ensures
        res == (forall|i: int, a: int| 0 <= i < vvars(vs@).len() && 0 <= a < vvars(vs@)[i].1.len() ==> !sty_mentions(#[trigger] vvars(vs@)[i].1[a], r@)),
{
    let mut a: usize = 0;
    while a < vs.len()
        invariant
            a <= vs@.len(),
            forall|c: int, k: int| 0 <= c < a && 0 <= k < vs@[c].1@.len() ==> !sty_mentions(vty(vs@[c].1@[k]), r@),
        decreases vs@.len() - a,
    {
        let mut b: usize = 0;
        while b < vs[a].1.len()
            invariant
                a < vs@.len(),
                b <= vs@[a as int].1@.len(),
                forall|c: int, k: int| 0 <= c < a && 0 <= k < vs@[c].1@.len() ==> !sty_mentions(vty(vs@[c].1@[k]), r@),
                forall|k: int| 0 <= k < b ==> !sty_mentions(vty(vs@[a as int].1@[k]), r@),
            decreases vs@[a as int].1@.len() - b,
        {
            if sty_mentions_e(&vs[a].1[b], r) {
                proof {
                    assert(vvars(vs@)[a as int].1[b as int] == vty(vs@[a as int].1@[b as int]));
                }
                return false;
            }
            b += 1;
        }
        a += 1;
    }
    proof {
        assert forall|i: int, k: int| 0 <= i < vvars(vs@).len() && 0 <= k < vvars(vs@)[i].1.len() implies !sty_mentions(#[trigger] vvars(vs@)[i].1[k], r@) by {
            assert(vvars(vs@)[i].1[k] == vty(vs@[i].1@[k]));
        }
    }
    true
}

/// 直和型の項のどれも、Int、Bool、r のどれか（rec_items の二つ目の選択肢）。
fn each_items_e(vs: &Vec<(Vec<char>, Vec<STy>)>, r: &Vec<char>) -> (res: bool)
    ensures
        res == (forall|i: int, a: int| 0 <= i < vvars(vs@).len() && 0 <= a < vvars(vs@)[i].1.len() ==> sty_rec_item(#[trigger] vvars(vs@)[i].1[a], r@)),
{
    let mut a: usize = 0;
    while a < vs.len()
        invariant
            a <= vs@.len(),
            forall|c: int, k: int| 0 <= c < a && 0 <= k < vs@[c].1@.len() ==> sty_rec_item(vty(vs@[c].1@[k]), r@),
        decreases vs@.len() - a,
    {
        let mut b: usize = 0;
        while b < vs[a].1.len()
            invariant
                a < vs@.len(),
                b <= vs@[a as int].1@.len(),
                forall|c: int, k: int| 0 <= c < a && 0 <= k < vs@[c].1@.len() ==> sty_rec_item(vty(vs@[c].1@[k]), r@),
                forall|k: int| 0 <= k < b ==> sty_rec_item(vty(vs@[a as int].1@[k]), r@),
            decreases vs@[a as int].1@.len() - b,
        {
            if !sty_rec_item_e(&vs[a].1[b], r) {
                proof {
                    assert(vvars(vs@)[a as int].1[b as int] == vty(vs@[a as int].1@[b as int]));
                }
                return false;
            }
            b += 1;
        }
        a += 1;
    }
    proof {
        assert forall|i: int, k: int| 0 <= i < vvars(vs@).len() && 0 <= k < vvars(vs@)[i].1.len() implies sty_rec_item(#[trigger] vvars(vs@)[i].1[k], r@) by {
            assert(vvars(vs@)[i].1[k] == vty(vs@[i].1@[k]));
        }
    }
    true
}

/// 直和型の項の規則（rec_items の exec 版）。再帰しない形か、再帰する形（Int、Bool、r だけ）であること。
fn rec_items_e(vs: &Vec<(Vec<char>, Vec<STy>)>, r: &Vec<char>) -> (res: bool)
    ensures
        res == rec_items(vvars(vs@), r@),
{
    let plain = plain_items_e(vs, r);
    let each = each_items_e(vs, r);
    proof {
        reveal(rec_items);
    }
    plain || each
}

/// 中身の項の並びの展開の exec 版（pay_ty）。項がなければ Unit。
fn pay_e(ts: &Vec<STy>, tb: &Vec<(Vec<char>, Option<Ty>, Vec<Vec<char>>, Option<Ty>)>, tagged: bool) -> (r: Option<Ty>)
    ensures
        r == pay_ty(vtys(ts@), vtb(tb@), tagged),
{
    let n = ts.len();
    if n == 0 {
        return Some(Ty::Unit);
    }
    let mut i: usize = n - 1;
    let mut acc: Option<Ty> = to_ty_e(&ts[i], tb, tagged);
    while i > 0
        invariant
            n == ts@.len(),
            i < n,
            acc == pay_from(vtys(ts@), i as nat, vtb(tb@), tagged),
        decreases i,
    {
        i -= 1;
        let u = to_ty_e(&ts[i], tb, tagged);
        acc = match (u, acc) {
            (Some(u), Some(v)) => Some(Ty::Pair(Box::new(u), Box::new(v))),
            _ => None,
        };
    }
    acc
}

/// 構築子の項目の exec 版（vent）。
fn vent_e(c: &Vec<char>, m: usize) -> (r: Vec<char>)
    ensures
        r@ == vent(c@, m as nat),
{
    let mut r: Vec<char> = Vec::new();
    r.push('#');
    let mut i: usize = 0;
    while i < c.len()
        invariant
            i <= c.len(),
            r@ == seq!['#'] + c@.subrange(0, i as int),
        decreases c.len() - i,
    {
        r.push(c[i]);
        i += 1;
    }
    assert(c@.subrange(0, c@.len() as int) =~= c@);
    r.push('#');
    let mut j: usize = 0;
    while j < m
        invariant
            j <= m,
            r@ == seq!['#'] + c@ + seq!['#'] + Seq::new(j as nat, |t: int| 'x'),
        decreases m - j,
    {
        assert(Seq::new((j + 1) as nat, |t: int| 'x') =~= Seq::new(j as nat, |t: int| 'x').push('x'));
        r.push('x');
        j += 1;
    }
    r
}

/// 直和型の構築子の項目の並びの exec 版（vents）。
fn vents_e(vs: &Vec<(Vec<char>, Vec<STy>)>) -> (r: Vec<Vec<char>>)
    ensures
        vnames(r@) == vents(vvars(vs@)),
{
    let mut out: Vec<Vec<char>> = Vec::new();
    let mut k: usize = 0;
    while k < vs.len()
        invariant
            k <= vs.len(),
            out@.len() == k,
            forall|t: int| 0 <= t < k ==> out@[t]@ == vent(vvars(vs@)[t].0, vvars(vs@)[t].1.len()),
        decreases vs.len() - k,
    {
        let e = vent_e(&vs[k].0, vs[k].1.len());
        out.push(e);
        k += 1;
    }
    assert(vnames(out@) =~= vents(vvars(vs@)));
    out
}

/// 名前表の三つ目の並びが記録の字段の並びか（is_rec_slot の exec 版）。
fn is_rec_slot_e(fs: &Vec<Vec<char>>) -> (r: bool)
    ensures
        r == is_rec_slot(vnames(fs@)),
{
    fs.len() > 0 && fs[0].len() > 0 && fs[0][0] != '#'
}

/// 直和型の中身の展開の exec 版（sum_from の k = 0）。構築子の中身を後ろから入れ子の Result にする。
fn sum_from_e(vs: &Vec<(Vec<char>, Vec<STy>)>, tb: &Vec<(Vec<char>, Option<Ty>, Vec<Vec<char>>, Option<Ty>)>, tagged: bool) -> (r: Option<Ty>)
    ensures
        r == sum_from(vvars(vs@), 0, vtb(tb@), tagged),
{
    let n = vs.len();
    if n == 0 {
        return None;
    }
    let mut i: usize = n - 1;
    let mut acc: Option<Ty> = pay_e(&vs[i].1, tb, tagged);
    while i > 0
        invariant
            n == vs@.len(),
            i < n,
            acc == sum_from(vvars(vs@), i as nat, vtb(tb@), tagged),
        decreases i,
    {
        i -= 1;
        let u = pay_e(&vs[i].1, tb, tagged);
        acc = match (u, acc) {
            (Some(u), Some(v)) => Some(Ty::Result(Box::new(u), Box::new(v))),
            _ => None,
        };
    }
    acc
}

/// 直和型の名前表の展開の exec 版（sum_exp）。再帰する直和型は None。
fn sum_exp_e(vs: &Vec<(Vec<char>, Vec<STy>)>, r: &Vec<char>, tb: &Vec<(Vec<char>, Option<Ty>, Vec<Vec<char>>, Option<Ty>)>, tagged: bool) -> (res: Option<Ty>)
    ensures
        res == sum_exp(vvars(vs@), r@, vtb(tb@), tagged),
{
    if plain_items_e(vs, r) {
        sum_from_e(vs, tb, tagged)
    } else {
        None
    }
}

/// 宣言を名前表の末尾に足す（tb_push の exec 版）。足せないときは None。
/// 字段と直和型の中身は、移す前の名前表 tb だけを引いて調べ（ループは補助関数に置く）、通ったあとで tb を移して足す。
fn tb_push_e(tb: Vec<(Vec<char>, Option<Ty>, Vec<Vec<char>>, Option<Ty>)>, d: &SDecl) -> (r: Option<Vec<(Vec<char>, Option<Ty>, Vec<Vec<char>>, Option<Ty>)>>)
    ensures
        match r {
            Some(nb) => tb_push(vtb(tb@), vd(*d)) == Some(vtb(nb@)),
            None => tb_push(vtb(tb@), vd(*d)) is None,
        },
{
    match d {
        SDecl::Fn(_, _, _, _) => {
            proof {
                assert(vd(*d) matches Sd::Fn(..));
                tb_push_other(vtb(tb@), vd(*d));
            }
            Some(tb)
        },
        SDecl::Entry(_) => {
            proof {
                assert(vd(*d) matches Sd::Entry(..));
                tb_push_other(vtb(tb@), vd(*d));
            }
            Some(tb)
        },
        SDecl::RecTy(r, fs, tc) => {
            proof {
                assert(vd(*d) == Sd::RecTy(r@, vps(fs@), *tc));
            }
            if tidx_e(&tb, r).is_some() {
                proof {
                    tb_push_rec_none(vtb(tb@), r@, vps(fs@), *tc);
                    assert(tb_push(vtb(tb@), vd(*d)) == tb_push(vtb(tb@), Sd::RecTy(r@, vps(fs@), *tc)));
                }
                return None;
            }
            let fnv = field_names_e(fs);
            proof {
                assert(vnames(fnv@).len() == fnv@.len());
                assert(pnames(vps(fs@)).len() == vps(fs@).len());
                assert(vps(fs@).len() == fs@.len());
            }
            if !fields_ok_e(fs, &tb, &fnv) {
                proof {
                    tb_push_rec_none(vtb(tb@), r@, vps(fs@), *tc);
                    assert(tb_push(vtb(tb@), vd(*d)) == tb_push(vtb(tb@), Sd::RecTy(r@, vps(fs@), *tc)));
                }
                return None;
            }
            proof {
                tb_push_rec_some(vtb(tb@), r@, vps(fs@), *tc);
                assert(tb_push(vtb(tb@), vd(*d)) == tb_push(vtb(tb@), Sd::RecTy(r@, vps(fs@), *tc)));
            }
            let exp = rec_exp_e(fs, &tb, false);
            let exp_t = rec_exp_e(fs, &tb, true);
            let mut out = tb;
            out.push((clone_chars(r), exp, fnv, exp_t));
            proof {
                assert(vtb(out@) =~= vtb(tb@).push((r@, rec_from(vps(fs@), 0, vtb(tb@), false), pnames(vps(fs@)), rec_from(vps(fs@), 0, vtb(tb@), true))));
            }
            Some(out)
        },
        SDecl::Sum(r, vs) => {
            proof {
                assert(vd(*d) == Sd::Sum(r@, vvars(vs@)));
            }
            if tidx_e(&tb, r).is_some() {
                proof {
                    tb_push_sum_none(vtb(tb@), r@, vvars(vs@));
                    assert(tb_push(vtb(tb@), vd(*d)) == tb_push(vtb(tb@), Sd::Sum(r@, vvars(vs@))));
                }
                return None;
            }
            // 自分の名前を先に足し、中身の型は自分を含む表で調べる（再帰する直和型）。
            let mut out = tb;
            out.push((clone_chars(r), None, Vec::new(), None));
            proof {
                assert(vnames(Seq::<Vec<char>>::empty()) =~= Seq::<Seq<char>>::empty());
                assert(vtb(out@) =~= vtb(tb@).push((r@, None, Seq::empty(), None)));
                assert(vars_ok(vvars(vs@), vtb(out@)) == vars_ok(vvars(vs@), vtb(tb@).push((r@, None, Seq::empty(), None))));
            }
            if !vars_ok_e(vs, &out) {
                proof {
                    tb_push_sum_none(vtb(tb@), r@, vvars(vs@));
                    assert(tb_push(vtb(tb@), vd(*d)) == tb_push(vtb(tb@), Sd::Sum(r@, vvars(vs@))));
                }
                return None;
            }
            if !rec_items_e(vs, r) {
                proof {
                    tb_push_sum_none(vtb(tb@), r@, vvars(vs@));
                    assert(tb_push(vtb(tb@), vd(*d)) == tb_push(vtb(tb@), Sd::Sum(r@, vvars(vs@))));
                }
                return None;
            }
            proof {
                tb_push_sum_some(vtb(tb@), r@, vvars(vs@));
                assert(tb_push(vtb(tb@), vd(*d)) == tb_push(vtb(tb@), Sd::Sum(r@, vvars(vs@))));
            }
            // 展開は、自分を足す前の表で作る（自分を足したものは調べるための表で、中身は自分を引かない）。
            let _ = out.pop();
            proof {
                assert(vtb(out@) =~= vtb(tb@));
            }
            let exp = sum_exp_e(vs, r, &out, false);
            let exp_t = sum_exp_e(vs, r, &out, true);
            out.push((clone_chars(r), exp, vents_e(vs), exp_t));
            proof {
                assert(vtb(out@) =~= vtb(tb@).push((r@, sum_exp(vvars(vs@), r@, vtb(tb@), false), vents(vvars(vs@)), sum_exp(vvars(vs@), r@, vtb(tb@), true))));
            }
            Some(out)
        },
    }
}

/// 名前表の exec 版（decl_table の exec 版）。宣言の順に足す。規則に反すれば None。
fn decl_table_e(p: &Vec<SDecl>) -> (r: Option<Vec<(Vec<char>, Option<Ty>, Vec<Vec<char>>, Option<Ty>)>>)
    ensures
        match r {
            Some(tb) => decl_table(vds(p@), p@.len() as nat) == Some(vtb(tb@)),
            None => decl_table(vds(p@), p@.len() as nat) is None,
        },
{
    let mut tb: Vec<(Vec<char>, Option<Ty>, Vec<Vec<char>>, Option<Ty>)> = Vec::new();
    let mut i: usize = 0;
    while i < p.len()
        invariant
            i <= p@.len(),
            decl_table(vds(p@), i as nat) == Some(vtb(tb@)),
        decreases p@.len() - i,
    {
        let ghost t0 = tb@;
        match tb_push_e(tb, &p[i]) {
            Some(nb) => {
                tb = nb;
            },
            None => {
                proof {
                    assert(vds(p@)[i as int] == vd(p@[i as int]));
                    assert(decl_table(vds(p@), i as nat) == Some(vtb(t0)));
                    assert(decl_table(vds(p@), (i + 1) as nat) is None);
                    decl_none_mono(vds(p@), (i + 1) as nat, p@.len() as nat);
                }
                return None;
            },
        }
        proof {
            assert(vds(p@)[i as int] == vd(p@[i as int]));
            assert(decl_table(vds(p@), (i + 1) as nat) == Some(vtb(tb@)));
        }
        i += 1;
    }
    Some(tb)
}

/// 宣言の番号を一つ作る（型の宣言なら n、関数と entry なら None）。n は、その宣言の直前の名前表の長さ。
fn num_e(d: &SDecl, n: usize) -> (r: Option<usize>)
    ensures
        is_type_decl(vd(*d)) ==> r == Some(n),
        !is_type_decl(vd(*d)) ==> r is None,
{
    match d {
        SDecl::RecTy(_, _, _) => {
            proof {
                assert(vd(*d) matches Sd::RecTy(..));
            }
            Some(n)
        },
        SDecl::Sum(_, _) => {
            proof {
                assert(vd(*d) matches Sd::Sum(..));
            }
            Some(n)
        },
        SDecl::Fn(_, _, _, _) => {
            proof {
                assert(vd(*d) matches Sd::Fn(..));
            }
            None
        },
        SDecl::Entry(_) => {
            proof {
                assert(vd(*d) matches Sd::Entry(..));
            }
            None
        },
    }
}

/// 宣言の番号の exec 版（decl_nums の exec 版）。宣言の順に、型の宣言なら名前表に入る位置（その直前の長さ）、
/// 関数と entry は None。名前表が作れるときだけ Some。記録と直和型の番号は、宣言の順に区別なく数える。
pub fn decl_numbers_e(p: &Vec<SDecl>) -> (r: Option<Vec<Option<usize>>>)
    ensures
        match r {
            Some(ns) => decl_nums(vds(p@)) == Some(nums_view(ns@)),
            None => decl_nums(vds(p@)) is None,
        },
{
    let mut tb: Vec<(Vec<char>, Option<Ty>, Vec<Vec<char>>, Option<Ty>)> = Vec::new();
    let mut ns: Vec<Option<usize>> = Vec::new();
    let mut i: usize = 0;
    while i < p.len()
        invariant
            i <= p@.len(),
            ns@.len() == i,
            decl_table(vds(p@), i as nat) == Some(vtb(tb@)),
            forall|k: int| 0 <= k < i ==> nums_conv(#[trigger] ns@[k]) == nums_of(vds(p@), k as nat),
        decreases p@.len() - i,
    {
        let ghost t0 = tb@;
        let ghost ns0 = ns@;
        let num = num_e(&p[i], tb.len());
        proof {
            assert(vds(p@)[i as int] == vd(p@[i as int]));
            assert(decl_table(vds(p@), i as nat) == Some(vtb(t0)));
            assert(nums_conv(num) == nums_of(vds(p@), i as nat));
        }
        match tb_push_e(tb, &p[i]) {
            Some(nb) => {
                tb = nb;
            },
            None => {
                proof {
                    assert(vds(p@).len() == p@.len());
                    assert(decl_table(vds(p@), (i + 1) as nat) is None);
                    decl_none_mono(vds(p@), (i + 1) as nat, p@.len() as nat);
                    assert(decl_nums(vds(p@)) is None);
                }
                return None;
            },
        }
        ns.push(num);
        proof {
            assert(vds(p@)[i as int] == vd(p@[i as int]));
            assert(decl_table(vds(p@), (i + 1) as nat) == Some(vtb(tb@)));
            assert(ns@ == ns0.push(num));
            assert forall|k: int| 0 <= k < i + 1 implies nums_conv(#[trigger] ns@[k]) == nums_of(vds(p@), k as nat) by {
                if k < i as int {
                    assert(ns@[k] == ns0[k]);
                }
            }
        }
        i += 1;
    }
    proof {
        let ds = vds(p@);
        assert(ds.len() == p@.len());
        assert(ns@.len() == ds.len());
        assert(decl_table(ds, ds.len()) == Some(vtb(tb@)));
        assert(decl_nums(ds) == Some(Seq::new(ds.len(), |j: int| nums_of(ds, j as nat))));
        assert forall|k: int| 0 <= k < ds.len() implies nums_view(ns@)[k] == Seq::new(ds.len(), |j: int| nums_of(ds, j as nat))[k] by {
            assert(nums_conv(ns@[k]) == nums_of(ds, k as nat));
        }
        assert(nums_view(ns@) =~= Seq::new(ds.len(), |j: int| nums_of(ds, j as nat)));
    }
    Some(ns)
}

/// 途中の宣言の名前表が無ければ、後の名前表も無い。
proof fn decl_none_mono(p: Seq<Sd>, n: nat, m: nat)
    requires
        decl_table(p, n) is None,
        n <= m,
    ensures
        decl_table(p, m) is None,
    decreases m - n,
{
    if n < m {
        decl_none_mono(p, n, (m - 1) as nat);
    }
}

/// 展開の型から k 段の Result をはずした型の exec 版（tail_ty）。
fn tail_ty_e(t: &Ty, k: usize) -> (r: Option<Ty>)
    ensures
        r == tail_ty(*t, k as nat),
    decreases k,
{
    if k == 0 {
        Some(ty_clone(t))
    } else {
        match t {
            Ty::Result(_, b) => tail_ty_e(&**b, k - 1),
            _ => None,
        }
    }
}

/// 構築子 k の中身の型の exec 版（pay_at）。
fn pay_at_e(t: &Ty, n: usize, k: usize) -> (r: Option<Ty>)
    requires
        k < n,
    ensures
        r == pay_at(*t, n as nat, k as nat),
{
    if k + 1 < n {
        match tail_ty_e(t, k) {
            Some(Ty::Result(a, _)) => Some(*a),
            _ => None,
        }
    } else {
        tail_ty_e(t, k)
    }
}

/// 構築子の値を層 j から作る exec 版（inj_from）。
fn inj_from_e(t: &Ty, n: usize, k: usize, j: usize, p: EExpr) -> (r: Option<EExpr>)
    requires
        k < n,
        j <= k,
    ensures
        match r {
            Some(x) => inj_from(*t, n as nat, k as nat, j as nat, view_expr(p)) == Some(view_expr(x)),
            None => inj_from(*t, n as nat, k as nat, j as nat, view_expr(p)) is None,
        },
    decreases k - j,
{
    if j >= k {
        if k + 1 < n {
            match (pay_at_e(t, n, k), tail_ty_e(t, k + 1)) {
                (Some(u), Some(v)) => Some(EExpr::Inj(true, u, v, Box::new(p))),
                _ => None,
            }
        } else {
            Some(p)
        }
    } else {
        match (pay_at_e(t, n, j), tail_ty_e(t, j + 1)) {
            (Some(u), Some(v)) => match inj_from_e(t, n, k, j + 1, p) {
                Some(x) => Some(EExpr::Inj(false, u, v, Box::new(x))),
                None => None,
            },
            _ => None,
        }
    }
}

/// 構築子の値の exec 版（ctor_val）。印つきのときは印を前に付ける。
fn ctor_val_e(tagged: bool, i: usize, t: &Ty, n: usize, k: usize, p: EExpr) -> (r: Option<EExpr>)
    requires
        k < n,
    ensures
        match r {
            Some(x) => ctor_val(tagged, i as nat, *t, n as nat, k as nat, view_expr(p)) == Some(view_expr(x)),
            None => ctor_val(tagged, i as nat, *t, n as nat, k as nat, view_expr(p)) is None,
        },
{
    match inj_from_e(t, n, k, 0, p) {
        Some(v) => if tagged {
            Some(EExpr::Pair(Box::new(tag_expr_e(i)), Box::new(v)))
        } else {
            Some(v)
        },
        None => None,
    }
}

/// 字句 e が構築子 c のものなら、その字段の数の exec 版（vent_arity）。
fn vent_arity_e(e: &Vec<char>, c: &Vec<char>) -> (r: Option<usize>)
    ensures
        match r {
            Some(m) => vent_arity(e@, c@) == Some(m as nat),
            None => vent_arity(e@, c@) is None,
        },
{
    let n = c.len();
    if n > e.len() || e.len() - n < 2 || e[0] != '#' || e[n + 1] != '#' {
        return None;
    }
    let mut t: usize = 0;
    while t < n
        invariant
            n == c@.len(),
            t <= n,
            e@.len() >= n + 2,
            e@[0] == '#',
            e@[n as int + 1] == '#',
            forall|u: int| 0 <= u < t ==> e@[u + 1] == c@[u],
        decreases n - t,
    {
        if e[t + 1] != c[t] {
            assert(e@.subrange(1, n as int + 1)[t as int] != c@[t as int]);
            return None;
        }
        t += 1;
    }
    assert(e@.subrange(1, n as int + 1) =~= c@);
    let mut j: usize = n + 2;
    while j < e.len()
        invariant
            n + 2 <= j,
            j <= e.len(),
            e@.len() >= n + 2,
            e@[0] == '#',
            e@[n as int + 1] == '#',
            e@.subrange(1, n as int + 1) =~= c@,
            forall|u: int| n as int + 2 <= u < j ==> e@[u] == 'x',
        decreases e.len() - j,
    {
        if e[j] != 'x' {
            return None;
        }
        j += 1;
    }
    Some(e.len() - n - 2)
}

/// 構築子 c の項目を、一つの直和型の項目の並びの中で探す exec 版（vidx）。
fn vidx_e(es: &Vec<Vec<char>>, c: &Vec<char>, i: usize) -> (r: Option<(usize, usize)>)
    ensures
        match r {
            Some((k, m)) => k < es@.len() && vidx(vnames(es@), c@, i as nat) == Some((k as nat, m as nat)),
            None => vidx(vnames(es@), c@, i as nat) is None,
        },
    decreases es.len() - i,
{
    if i >= es.len() {
        None
    } else {
        match vent_arity_e(&es[i], c) {
            Some(m) => Some((i, m)),
            None => vidx_e(es, c, i + 1),
        }
    }
}

/// 構築子 c の項目を名前表で探す exec 版（vlook_from）。
fn vlook_from_e(tb: &Vec<(Vec<char>, Option<Ty>, Vec<Vec<char>>, Option<Ty>)>, c: &Vec<char>, i: usize) -> (r: Option<(usize, usize, usize)>)
    ensures
        match r {
            Some((a, k, m)) => a < tb@.len() && k < vtb(tb@)[a as int].2.len() && vlook_from(vtb(tb@), c@, i as nat) == Some((a as nat, k as nat, m as nat)),
            None => vlook_from(vtb(tb@), c@, i as nat) is None,
        },
    decreases tb.len() - i,
{
    if i >= tb.len() {
        None
    } else {
        match vidx_e(&tb[i].2, c, 0) {
            Some((k, m)) => Some((i, k, m)),
            None => vlook_from_e(tb, c, i + 1),
        }
    }
}

/// 構築子 c の項目を名前表で探す exec 版（vlook）。
fn vlook_e(tb: &Vec<(Vec<char>, Option<Ty>, Vec<Vec<char>>, Option<Ty>)>, c: &Vec<char>) -> (r: Option<(usize, usize, usize)>)
    ensures
        match r {
            Some((a, k, m)) => a < tb@.len() && k < vtb(tb@)[a as int].2.len() && vlook(vtb(tb@), c@) == Some((a as nat, k as nat, m as nat)),
            None => vlook(vtb(tb@), c@) is None,
        },
{
    vlook_from_e(tb, c, 0)
}

/// 構築子の中身の式の exec 版（pay1）：字段が無ければ Unit、一つならその式。
fn pay1_e(xs: Vec<EExpr>) -> (r: EExpr)
    requires
        xs.len() <= 1,
    ensures
        view_expr(r) == pay1(view_exprs(xs)),
{
    let mut xs = xs;
    match xs.pop() {
        Some(x) => x,
        None => EExpr::Unit,
    }
}

/// 構築子への呼出しの exec 版（rctor）。字段が 0 または 1 個の構築子だけを作る。
fn rctor_e(tb: &Vec<(Vec<char>, Option<Ty>, Vec<Vec<char>>, Option<Ty>)>, tagged: bool, c: &Vec<char>, xs: Vec<EExpr>) -> (r: Option<EExpr>)
    ensures
        match r {
            Some(x) => rctor(vtb(tb@), tagged, c@, view_exprs(xs)) == Some(view_expr(x)),
            None => rctor(vtb(tb@), tagged, c@, view_exprs(xs)) is None,
        },
{
    match vlook_e(tb, c) {
        Some((i, k, m)) => {
            if m > 1 || m != xs.len() || k >= tb[i].2.len() {
                None
            } else {
                let p = pay1_e(xs);
                match if tagged { clone_opt(&tb[i].3) } else { clone_opt(&tb[i].1) } {
                    Some(t) => ctor_val_e(tagged, i, &t, tb[i].2.len(), k, p),
                    None => None,
                }
            }
        },
        None => None,
    }
}

/// 枝の束縛の名前の exec 版（arm_name）。
fn arm_name_e(bs: &Vec<Vec<char>>) -> (r: Option<Vec<char>>)
    ensures
        match r {
            Some(x) => arm_name(vnames(bs@)) == Some(x@),
            None => arm_name(vnames(bs@)) is None,
        },
{
    if bs.len() == 0 {
        Some(Vec::new())
    } else if bs.len() == 1 && bs[0].len() > 0 {
        Some(clone_chars(&bs[0]))
    } else {
        None
    }
}

/// 枝 j 以降が、直和型 i の構築子を宣言の順に並べたもの（arms_ctors の exec 版）。
fn arms_ctors_e(tb: &Vec<(Vec<char>, Option<Ty>, Vec<Vec<char>>, Option<Ty>)>, i: usize, ps: &Vec<SPat>, es: &Vec<SExpr>, j: usize) -> (r: bool)
    requires
        i < tb.len(),
        ps.len() == es.len(),
        ps.len() <= tb[i as int].2.len(),
    ensures
        r == arms_ctors(vtb(tb@), i as nat, varms(ps@, es@), j as nat),
    decreases ps.len() - j,
{
    if j >= ps.len() {
        true
    } else {
        match &ps[j] {
            SPat::Ctor(c, bs) => match vent_arity_e(&tb[i].2[j], c) {
                Some(m) => m == bs.len() && arm_name_e(bs).is_some() && arms_ctors_e(tb, i, ps, es, j + 1),
                None => false,
            },
            _ => false,
        }
    }
}

/// 枝の並びが一つの直和型の構築子を宣言の順に並べたものなら、その型の番号（arms_sum の exec 版）。
fn arms_sum_e(tb: &Vec<(Vec<char>, Option<Ty>, Vec<Vec<char>>, Option<Ty>)>, ps: &Vec<SPat>, es: &Vec<SExpr>) -> (r: Option<usize>)
    requires
        ps.len() == es.len(),
    ensures
        match r {
            Some(i) => i < tb.len() && tb@[i as int].2.len() == ps@.len() && arms_sum(vtb(tb@), varms(ps@, es@)) == Some(i as nat),
            None => arms_sum(vtb(tb@), varms(ps@, es@)) is None,
        },
{
    if ps.len() == 0 {
        return None;
    }
    match &ps[0] {
        SPat::Ctor(c, _) => match vlook_e(tb, c) {
            Some((i, _, _)) => if tb[i].2.len() == ps.len() && arms_ctors_e(tb, i, ps, es, 0) {
                Some(i)
            } else {
                None
            },
            None => None,
        },
        _ => None,
    }
}

/// 直和型の枝の鎖の exec 版（smatch_from）。被験式 s は scope sc で整合する（sc は戻す）。
fn smatch_e(fs: &Vec<Vec<char>>, tb: &Vec<(Vec<char>, Option<Ty>, Vec<Vec<char>>, Option<Ty>)>, tagged: bool, sc: &mut Vec<Vec<char>>, ps: &Vec<SPat>, es: &Vec<SExpr>, n: usize, j: usize, s: EExpr) -> (r: Option<EExpr>)
    requires
        ps.len() == es.len(),
        n == ps.len(),
    ensures
        final(sc)@ == old(sc)@,
        match r {
            Some(x) => smatch_from(vnames(fs@), vtb(tb@), tagged, vnames(old(sc)@), varms(ps@, es@), n as nat, j as nat, view_expr(s)) == Some(view_expr(x)),
            None => smatch_from(vnames(fs@), vtb(tb@), tagged, vnames(old(sc)@), varms(ps@, es@), n as nat, j as nat, view_expr(s)) is None,
        },
    decreases es, n - j,
{
    let ghost s0 = sc@;
    if j >= n || j >= ps.len() {
        return None;
    }
    let b = match &ps[j] {
        SPat::Ctor(_, bs) => match arm_name_e(bs) {
            Some(b) => b,
            None => return None,
        },
        _ => return None,
    };
    if b.len() > 0 && idx_e(sc, &b).is_some() {
        return None;
    }
    let slot = sc.len();
    sc.push(b);
    proof {
        vnames_push(s0, sc@[slot as int]);
    }
    let body = rx_e(fs, tb, tagged, sc, &es[j]);
    let _ = sc.pop();
    proof {
        assert(sc@ =~= s0);
    }
    let body = match body {
        Some(x) => x,
        None => return None,
    };
    if j + 1 == n {
        Some(EExpr::Let(slot, Box::new(s), Box::new(body)))
    } else {
        sc.push(Vec::new());
        proof {
            vnames_push(s0, sc@[slot as int]);
        }
        let rest = smatch_e(fs, tb, tagged, sc, ps, es, n, j + 1, EExpr::Var(slot));
        let _ = sc.pop();
        proof {
            assert(sc@ =~= s0);
        }
        match rest {
            Some(rest) => Some(EExpr::MatchR(Box::new(s), slot, Box::new(body), slot, Box::new(rest))),
            None => None,
        }
    }
}

/// 直和型の枝の頭の exec 版（smatch_top）。印つきは、被験式を t（位置 d）に束縛し、印を検査してから中身から鎖を作る（tfield と同じ）。
fn smatch_top_e(fs: &Vec<Vec<char>>, tb: &Vec<(Vec<char>, Option<Ty>, Vec<Vec<char>>, Option<Ty>)>, tagged: bool, sc: &mut Vec<Vec<char>>, ps: &Vec<SPat>, es: &Vec<SExpr>, i: usize, n: usize, rm: EExpr) -> (r: Option<EExpr>)
    requires
        ps.len() == es.len(),
        n == ps.len(),
    ensures
        final(sc)@ == old(sc)@,
        match r {
            Some(x) => smatch_top(vnames(fs@), vtb(tb@), tagged, vnames(old(sc)@), varms(ps@, es@), i as nat, n as nat, view_expr(rm)) == Some(view_expr(x)),
            None => smatch_top(vnames(fs@), vtb(tb@), tagged, vnames(old(sc)@), varms(ps@, es@), i as nat, n as nat, view_expr(rm)) is None,
        },
    decreases es, n + 2,
{
    proof {
        reveal_with_fuel(smatch_top, 1);
    }
    if !tagged {
        return smatch_e(fs, tb, tagged, sc, ps, es, n, 0, rm);
    }
    smatch_tag_e(fs, tb, sc, ps, es, i, n, rm)
}

/// 印つきの直和型の枝の頭（smatch_top の印つきの腕）の exec 版。被験式を t（位置 d）に束縛し、印を検査してから中身から鎖を作る。
fn smatch_tag_e(fs: &Vec<Vec<char>>, tb: &Vec<(Vec<char>, Option<Ty>, Vec<Vec<char>>, Option<Ty>)>, sc: &mut Vec<Vec<char>>, ps: &Vec<SPat>, es: &Vec<SExpr>, i: usize, n: usize, rm: EExpr) -> (r: Option<EExpr>)
    requires
        ps.len() == es.len(),
        n == ps.len(),
    ensures
        final(sc)@ == old(sc)@,
        match r {
            Some(x) => smatch_top(vnames(fs@), vtb(tb@), true, vnames(old(sc)@), varms(ps@, es@), i as nat, n as nat, view_expr(rm)) == Some(view_expr(x)),
            None => smatch_top(vnames(fs@), vtb(tb@), true, vnames(old(sc)@), varms(ps@, es@), i as nat, n as nat, view_expr(rm)) is None,
        },
    decreases es, n + 1,
{
    proof {
        reveal_with_fuel(smatch_top, 1);
        reveal_with_fuel(view_expr, 4);
    }
    let ghost s0 = sc@;
    let d = sc.len();
    let e0: Vec<char> = Vec::new();
    sc.push(e0);
    proof {
        vnames_push_nil(s0, sc@[d as int]);
    }
    let ghost s1 = sc@;
    let d1 = sc.len();
    let e1: Vec<char> = Vec::new();
    sc.push(e1);
    proof {
        vnames_push_nil(s1, sc@[d1 as int]);
        assert(vnames(sc@) =~= vnames(s0).push(Seq::empty()).push(Seq::empty()));
    }
    proof {
        assert(d1 as int == d as int + 1);
    }
    let mut sa: Vec<EExpr> = Vec::new();
    sa.push(EExpr::Var(d));
    proof {
        assert(view_exprs(sa) =~= seq![Expr::Var(d as nat)]);
    }
    let snd = EExpr::Builtin(Builtin::Snd, sa);
    let ghost sndv = view_expr(snd);
    proof {
        assert(sndv == Expr::Builtin(Builtin::Snd, seq![Expr::Var(d as nat)]));
    }
    let c = smatch_e(fs, tb, true, sc, ps, es, n, 0, snd);
    let _ = sc.pop();
    let _ = sc.pop();
    proof {
        assert(sc@ =~= s0);
    }
    let c = match c {
        Some(c) => c,
        None => return None,
    };
    let mut fa: Vec<EExpr> = Vec::new();
    fa.push(EExpr::Var(d));
    proof {
        assert(view_exprs(fa) =~= seq![Expr::Var(d as nat)]);
    }
    let fst = EExpr::Builtin(Builtin::Fst, fa);
    let ghost fstv = view_expr(fst);
    proof {
        assert(fstv == Expr::Builtin(Builtin::Fst, seq![Expr::Var(d as nat)]));
    }
    let tg = tag_expr_e(i);
    let ghost tgv = view_expr(tg);
    let mut ea: Vec<EExpr> = Vec::new();
    ea.push(fst);
    ea.push(tg);
    proof {
        assert(view_exprs(ea) =~= seq![fstv, tgv]);
    }
    let eq = EExpr::Builtin(Builtin::Eq, ea);
    let cond = EExpr::If(Box::new(eq), Box::new(EExpr::Unit), Box::new(EExpr::Unit));
    let inner = EExpr::Let(d1, Box::new(cond), Box::new(c));
    Some(EExpr::Let(d, Box::new(rm), Box::new(inner)))
}

/// 直和型の枝（SExpr::SumMatch）の exec 版。長さの違う枝の並びは空（vx）なので、拒否する。
fn rx_sum_e(fs: &Vec<Vec<char>>, tb: &Vec<(Vec<char>, Option<Ty>, Vec<Vec<char>>, Option<Ty>)>, tagged: bool, sc: &mut Vec<Vec<char>>, e: &SExpr) -> (r: Option<EExpr>)
    requires
        e is SumMatch,
    ensures
        final(sc)@ == old(sc)@,
        match r {
            Some(x) => rx(vnames(fs@), vtb(tb@), tagged, vnames(old(sc)@), vx(*e)) == Some(view_expr(x)),
            None => rx(vnames(fs@), vtb(tb@), tagged, vnames(old(sc)@), vx(*e)) is None,
        },
    decreases e, 0nat,
{
    if let SExpr::SumMatch(m, ps, es) = e {
        if ps.len() != es.len() {
            return None;
        }
        let i = match arms_sum_e(tb, ps, es) {
            Some(i) => i,
            None => return None,
        };
        let n = tb[i].2.len();
        match rx_e(fs, tb, tagged, sc, m) {
            Some(rm) => smatch_top_e(fs, tb, tagged, sc, ps, es, i, n, rm),
            None => None,
        }
    } else {
        None
    }
}

pub fn rx_e(fs: &Vec<Vec<char>>, tb: &Vec<(Vec<char>, Option<Ty>, Vec<Vec<char>>, Option<Ty>)>, tagged: bool, sc: &mut Vec<Vec<char>>, e: &SExpr) -> (r: Option<EExpr>)
    ensures
        final(sc)@ == old(sc)@,
        match r {
            Some(x) => rx(vnames(fs@), vtb(tb@), tagged, vnames(old(sc)@), vx(*e)) == Some(view_expr(x)),
            None => rx(vnames(fs@), vtb(tb@), tagged, vnames(old(sc)@), vx(*e)) is None,
        },
    decreases e, 1nat,
{
    let ghost f = vnames(fs@);
    let ghost s = vnames(sc@);
    match e {
        SExpr::Int(n) => Some(EExpr::Int(n.copy())),
        SExpr::Chr(c) => Some(EExpr::Char(*c as u32)),
        SExpr::Str(w) => {
            let mut xs: Vec<EExpr> = Vec::new();
            let mut i: usize = 0;
            while i < w.len()
                invariant
                    i <= w.len(),
                    xs@.len() == i,
                    forall|j: int| 0 <= j < i ==> view_expr(#[trigger] xs@[j]) == Expr::Char(w@[j] as u32 as int),
                decreases w.len() - i,
            {
                xs.push(EExpr::Char(w[i] as u32));
                i += 1;
            }
            proof {
                assert(view_exprs(xs) =~= str_exprs(w@));
            }
            Some(EExpr::List(Ty::Char, xs))
        },
        SExpr::Bool(b) => Some(EExpr::Bool(*b)),
        SExpr::Unit => Some(EExpr::Unit),
        SExpr::Var(x) => if x.len() == 0 {
            None
        } else {
            match idx_e(sc, x) {
                Some(k) => Some(EExpr::Var(k)),
                // 局所の名前でないもの：字段のない構築子（大文字の名前）。
                None => rctor_e(tb, tagged, x, Vec::new()),
            }
        },
        SExpr::List(t, es) => match (to_ty_e(t, tb, tagged), rxs_e(fs, tb, tagged, sc, es)) {
            (Some(u), Some(xs)) => Some(EExpr::List(u, xs)),
            _ => None,
        },
        SExpr::Some(a) => match rx_e(fs, tb, tagged, sc, a) {
            Some(x) => Some(EExpr::Some(Box::new(x))),
            None => None,
        },
        SExpr::None(t) => match to_ty_e(t, tb, tagged) {
            Some(u) => Some(EExpr::None(u)),
            None => None,
        },
        SExpr::Pair(a, b) => {
            let x = rx_e(fs, tb, tagged, sc, a);
            let y = rx_e(fs, tb, tagged, sc, b);
            match (x, y) {
                (Some(x), Some(y)) => Some(EExpr::Pair(Box::new(x), Box::new(y))),
                _ => None,
            }
        },
        SExpr::Builtin(b, es) => match rxs_e(fs, tb, tagged, sc, es) {
            Some(xs) => Some(EExpr::Builtin(*b, xs)),
            None => None,
        },
        SExpr::Call(g, es) => match idx_e(fs, g) {
            Some(gi) => match rxs_e(fs, tb, tagged, sc, es) {
                Some(xs) => Some(EExpr::Call(gi, xs)),
                None => None,
            },
            // 関数でない名前への呼出しは構築子の呼出し（字段が一つ以上）。
            None => if es.len() == 0 {
                None
            } else {
                match rxs_e(fs, tb, tagged, sc, es) {
                    Some(xs) => rctor_e(tb, tagged, g, xs),
                    None => None,
                }
            },
        },
        SExpr::Let(..) => rx_let_e(fs, tb, tagged, sc, e),
        SExpr::If(c, a, b) => {
            let x = rx_e(fs, tb, tagged, sc, c);
            let y = rx_e(fs, tb, tagged, sc, a);
            let z = rx_e(fs, tb, tagged, sc, b);
            match (x, y, z) {
                (Some(x), Some(y), Some(z)) => Some(EExpr::If(Box::new(x), Box::new(y), Box::new(z))),
                _ => None,
            }
        },
        SExpr::Fold(..) => rx_fold_e(fs, tb, tagged, sc, e),
        SExpr::Match(..) => rx_match_e(fs, tb, tagged, sc, e),
        SExpr::Inj(ok, t, u, a) => match (to_ty_e(t, tb, tagged), to_ty_e(u, tb, tagged), rx_e(fs, tb, tagged, sc, a)) {
            (Some(t1), Some(u1), Some(x)) => Some(EExpr::Inj(*ok, t1, u1, Box::new(x))),
            _ => None,
        },
        SExpr::MatchR(..) => rx_matchr_e(fs, tb, tagged, sc, e),
        // 記録（段階 2 の S3a、印なし）。
        SExpr::Fld(..) => rx_fld_e(fs, tb, tagged, sc, e),
        SExpr::Rec(..) => rx_rec_e(fs, tb, tagged, sc, e),
        // match 式は名前解決の対象外（段階 1a の範囲では核に入れない）。
        SExpr::SumMatch(..) => rx_sum_e(fs, tb, tagged, sc, e),
        // hof は名前解決の対象外（字句・構文の段階だけで扱う）。
        SExpr::Hof(..) => None,
        // loop も名前解決の対象外（字句・構文の段階だけで扱う）。
        SExpr::Loop(..) => None,
        // dict の形も名前解決の対象外（字句・構文の段階だけで扱う）。
        SExpr::DictNew(..) | SExpr::DictOp(..) => None,
    }
}

fn rx_matchr_e(fs: &Vec<Vec<char>>, tb: &Vec<(Vec<char>, Option<Ty>, Vec<Vec<char>>, Option<Ty>)>, tagged: bool, sc: &mut Vec<Vec<char>>, e: &SExpr) -> (r: Option<EExpr>)
    requires
        e is MatchR,
    ensures
        final(sc)@ == old(sc)@,
        match r {
            Some(x) => rx(vnames(fs@), vtb(tb@), tagged, vnames(old(sc)@), vx(*e)) == Some(view_expr(x)),
            None => rx(vnames(fs@), vtb(tb@), tagged, vnames(old(sc)@), vx(*e)) is None,
        },
    decreases e, 0nat,
{
    let ghost s0 = sc@;
    if let SExpr::MatchR(m, x, a, y, b) = e {
        if idx_e(sc, x).is_some() || idx_e(sc, y).is_some() {
            return None;
        }
        let rm = rx_e(fs, tb, tagged, sc, m);
        if rm.is_none() {
            return None;
        }
        sc.push(clone_chars(x));
        let k = sc.len() - 1;
        proof {
            vnames_push(s0, sc@[k as int]);
        }
        let ra = rx_e(fs, tb, tagged, sc, a);
        sc.pop();
        proof {
            assert(sc@ =~= s0);
        }
        if ra.is_none() {
            return None;
        }
        sc.push(clone_chars(y));
        proof {
            vnames_push(s0, sc@[k as int]);
        }
        let rb = rx_e(fs, tb, tagged, sc, b);
        sc.pop();
        proof {
            assert(sc@ =~= s0);
        }
        match (rm, ra, rb) {
            (Some(rm), Some(ra), Some(rb)) => Some(EExpr::MatchR(Box::new(rm), k, Box::new(ra), k, Box::new(rb))),
            _ => None,
        }
    } else {
        None
    }
}

fn rx_match_e(fs: &Vec<Vec<char>>, tb: &Vec<(Vec<char>, Option<Ty>, Vec<Vec<char>>, Option<Ty>)>, tagged: bool, sc: &mut Vec<Vec<char>>, e: &SExpr) -> (r: Option<EExpr>)
    requires
        e is Match,
    ensures
        final(sc)@ == old(sc)@,
        match r {
            Some(x) => rx(vnames(fs@), vtb(tb@), tagged, vnames(old(sc)@), vx(*e)) == Some(view_expr(x)),
            None => rx(vnames(fs@), vtb(tb@), tagged, vnames(old(sc)@), vx(*e)) is None,
        },
    decreases e, 0nat,
{
    let ghost s0 = sc@;
    if let SExpr::Match(m, n, x, b) = e {
        if idx_e(sc, x).is_some() {
            return None;
        }
        let rm = rx_e(fs, tb, tagged, sc, m);
        let rn = rx_e(fs, tb, tagged, sc, n);
        if rm.is_none() || rn.is_none() {
            return None;
        }
        sc.push(clone_chars(x));
        let k = sc.len() - 1;
        proof {
            vnames_push(s0, sc@[k as int]);
        }
        let rb = rx_e(fs, tb, tagged, sc, b);
        sc.pop();
        proof {
            assert(sc@ =~= s0);
        }
        match (rm, rn, rb) {
            (Some(rm), Some(rn), Some(rb)) => Some(EExpr::Match(Box::new(rm), Box::new(rn), k, Box::new(rb))),
            _ => None,
        }
    } else {
        None
    }
}

/// 字段名の持ち主（owner_pos）の exec 版：名前表で字段名を持つ最初の項目の（位置、字段の数）。
fn owner_pos_e(tb: &Vec<(Vec<char>, Option<Ty>, Vec<Vec<char>>, Option<Ty>)>, f: &Vec<char>) -> (r: Option<(usize, usize)>)
    ensures
        match r {
            Some((p, m)) => owner_pos(vtb(tb@), f@, 0) == Some((p as nat, m as nat)) && p < m,
            None => owner_pos(vtb(tb@), f@, 0) is None,
        },
{
    let ghost v = vtb(tb@);
    let mut k: usize = 0;
    while k < tb.len()
        invariant
            v == vtb(tb@),
            k <= tb@.len(),
            owner_pos(v, f@, 0) == owner_pos(v, f@, k as nat),
        decreases tb@.len() - k,
    {
        proof {
            assert(v[k as int].2 == vnames(tb@[k as int].2@));
        }
        match idx_e(&tb[k].2, f) {
            Some(i) => {
                return Some((i, tb[k].2.len()));
            },
            None => {},
        }
        k += 1;
    }
    None
}

/// `e.f1…fn` の展開（fld_chain）の再帰の版：字段 i から、持ち主の位置で rfield_e を重ねて次の字段へ。
/// ループにしない（ループの頭では e の写しの関係が失われ、None の腕が示せないため）。
fn fld_chain_rec(tb: &Vec<(Vec<char>, Option<Ty>, Vec<Vec<char>>, Option<Ty>)>, e: EExpr, ns: &Vec<Vec<char>>, i: usize) -> (r: Option<EExpr>)
    requires
        i <= ns.len(),
    ensures
        match r {
            Some(x) => fld_chain(vtb(tb@), view_expr(e), vnames(ns@), i as nat) == Some(view_expr(x)),
            None => fld_chain(vtb(tb@), view_expr(e), vnames(ns@), i as nat) is None,
        },
    decreases ns.len() - i,
{
    if i >= ns.len() {
        proof {
            fld_chain_end(vtb(tb@), view_expr(e), vnames(ns@), i as nat);
        }
        return Some(e);
    }
    let ghost v = vtb(tb@);
    let ghost f = vnames(ns@);
    match owner_pos_e(tb, &ns[i]) {
        Some((p, m)) => {
            let ghost cv = view_expr(e);
            proof {
                assert(f.len() == ns@.len());
                assert(f[i as int] == ns@[i as int]@);
                assert(owner_pos(v, f[i as int], 0) == Some((p as nat, m as nat)));
                fld_chain_step(v, cv, f, i as nat, p as nat, m as nat);
            }
            let cur = rfield_e(e, p, m);
            proof {
                assert(view_expr(cur) == rfield(cv, p as nat, m as nat));
            }
            fld_chain_rec(tb, cur, ns, i + 1)
        },
        None => {
            proof {
                assert(f.len() == ns@.len());
                assert(f[i as int] == ns@[i as int]@);
                assert(owner_pos(v, f[i as int], 0) is None);
                fld_chain_none(v, view_expr(e), f, i as nat);
            }
            None
        },
    }
}

/// `e.f1…fn` の展開（fld_chain）の exec 版：字段の名前の列の順に、持ち主の位置で rfield_e を重ねる（全体は字段 0 から）。
fn fld_chain_e(tb: &Vec<(Vec<char>, Option<Ty>, Vec<Vec<char>>, Option<Ty>)>, e: EExpr, ns: &Vec<Vec<char>>) -> (r: Option<EExpr>)
    ensures
        match r {
            Some(x) => fld_chain(vtb(tb@), view_expr(e), vnames(ns@), 0) == Some(view_expr(x)),
            None => fld_chain(vtb(tb@), view_expr(e), vnames(ns@), 0) is None,
        },
{
    fld_chain_rec(tb, e, ns, 0)
}

/// 印の式の exec 版（tag_expr）：Pair(Unit, ·) の k 段の入れ子。nominal.rs の印の値（tag_val）が、これを呼ぶ。
pub fn tag_expr_e(k: usize) -> (r: EExpr)
    ensures
        view_expr(r) == tag_expr(k as nat),
    decreases k,
{
    proof {
        reveal_with_fuel(view_expr, 4);
    }
    if k == 0 {
        let r = EExpr::Pair(Box::new(EExpr::Unit), Box::new(EExpr::Unit));
        proof {
            assert(view_expr(r) == Expr::Pair(Box::new(Expr::Unit), Box::new(Expr::Unit)));
            assert(tag_expr(k as nat) == Expr::Pair(Box::new(Expr::Unit), Box::new(Expr::Unit)));
        }
        r
    } else {
        let rest = tag_expr_e(k - 1);
        let ghost restv = view_expr(rest);
        proof {
            assert((k - 1) as nat == ((k as nat) - 1) as nat);
        }
        let r = EExpr::Pair(Box::new(EExpr::Unit), Box::new(rest));
        proof {
            assert(view_expr(r) == Expr::Pair(Box::new(Expr::Unit), Box::new(restv)));
            assert(tag_expr(k as nat) == Expr::Pair(Box::new(Expr::Unit), Box::new(tag_expr(((k as nat) - 1) as nat))));
        }
        r
    }
}

/// 印つきの字段の参照の exec 版（tfield）。d は t の位置、d1 は u の位置（d1 = d + 1）。
/// 呼び出し側は scope に一つ足して d1 を得る（usize の加算を使わない）。
fn tfield_e(e: EExpr, k: usize, i: usize, n: usize, d: usize, d1: usize) -> (r: EExpr)
    requires
        i < n,
        d1 as int == d as int + 1,
    ensures
        view_expr(r) == tfield(view_expr(e), k as nat, i as nat, n as nat, d as nat),
{
    proof {
        reveal_with_fuel(view_expr, 4);
    }
    let ghost ev = view_expr(e);
    let mut fa: Vec<EExpr> = Vec::new();
    fa.push(EExpr::Var(d));
    proof {
        assert(view_exprs(fa) =~= seq![Expr::Var(d as nat)]);
    }
    let fst = EExpr::Builtin(Builtin::Fst, fa);
    let ghost fstv = view_expr(fst);
    proof {
        assert(fstv == Expr::Builtin(Builtin::Fst, seq![Expr::Var(d as nat)]));
    }
    let tg = tag_expr_e(k);
    let ghost tgv = view_expr(tg);
    let mut ea: Vec<EExpr> = Vec::new();
    ea.push(fst);
    ea.push(tg);
    proof {
        assert(view_exprs(ea) =~= seq![fstv, tgv]);
    }
    let cond = EExpr::Builtin(Builtin::Eq, ea);
    let ghost condv = view_expr(cond);
    proof {
        assert(condv == Expr::Builtin(Builtin::Eq, seq![fstv, tgv]));
    }
    let mut sa: Vec<EExpr> = Vec::new();
    sa.push(EExpr::Var(d));
    proof {
        assert(view_exprs(sa) =~= seq![Expr::Var(d as nat)]);
    }
    let snd = EExpr::Builtin(Builtin::Snd, sa);
    let ghost sndv = view_expr(snd);
    proof {
        assert(sndv == Expr::Builtin(Builtin::Snd, seq![Expr::Var(d as nat)]));
    }
    let body = rfield_e(snd, i, n);
    let ghost bodyv = view_expr(body);
    proof {
        assert(bodyv == rfield(sndv, i as nat, n as nat));
    }
    let guard = EExpr::If(Box::new(cond), Box::new(EExpr::Unit), Box::new(EExpr::Unit));
    let ghost guardv = view_expr(guard);
    proof {
        assert(guardv == Expr::If(Box::new(condv), Box::new(Expr::Unit), Box::new(Expr::Unit)));
    }
    let inner = EExpr::Let(d1, Box::new(guard), Box::new(body));
    let ghost innerv = view_expr(inner);
    proof {
        assert(innerv == Expr::Let((d1 as nat), Box::new(guardv), Box::new(bodyv)));
        assert(d1 as nat == d as nat + 1);
    }
    let res = EExpr::Let(d, Box::new(e), Box::new(inner));
    proof {
        assert(view_expr(res) == Expr::Let(d as nat, Box::new(ev), Box::new(innerv)));
    }
    res
}

/// owner_at の exec 版：名前表で字段名を持つ最初の項目の（宣言の番号、字段の位置、字段の数）。
fn owner_at_e(tb: &Vec<(Vec<char>, Option<Ty>, Vec<Vec<char>>, Option<Ty>)>, f: &Vec<char>) -> (r: Option<(usize, usize, usize)>)
    ensures
        match r {
            Some((k, p, m)) => owner_at(vtb(tb@), f@, 0) == Some((k as nat, p as nat, m as nat)) && p < m,
            None => owner_at(vtb(tb@), f@, 0) is None,
        },
{
    let ghost v = vtb(tb@);
    let mut k: usize = 0;
    while k < tb.len()
        invariant
            v == vtb(tb@),
            k <= tb@.len(),
            owner_at(v, f@, 0) == owner_at(v, f@, k as nat),
        decreases tb@.len() - k,
    {
        proof {
            assert(v[k as int].2 == vnames(tb@[k as int].2@));
        }
        match idx_e(&tb[k].2, f) {
            Some(i) => {
                return Some((k, i, tb[k].2.len()));
            },
            None => {},
        }
        k += 1;
    }
    None
}

/// fld_chain_t の exec 版（字段 i から、印の検査と字段の取り出しを重ねる）。d と d1 = d + 1 は束縛の位置。
fn fld_chain_t_rec(tb: &Vec<(Vec<char>, Option<Ty>, Vec<Vec<char>>, Option<Ty>)>, e: EExpr, ns: &Vec<Vec<char>>, i: usize, d: usize, d1: usize) -> (r: Option<EExpr>)
    requires
        i <= ns.len(),
        d1 as int == d as int + 1,
    ensures
        match r {
            Some(x) => fld_chain_t(vtb(tb@), view_expr(e), vnames(ns@), i as nat, d as nat) == Some(view_expr(x)),
            None => fld_chain_t(vtb(tb@), view_expr(e), vnames(ns@), i as nat, d as nat) is None,
        },
    decreases ns.len() - i,
{
    if i >= ns.len() {
        proof {
            fld_chain_t_end(vtb(tb@), view_expr(e), vnames(ns@), i as nat, d as nat);
        }
        return Some(e);
    }
    let ghost v = vtb(tb@);
    let ghost f = vnames(ns@);
    match owner_at_e(tb, &ns[i]) {
        Some((k, p, m)) => {
            let ghost cv = view_expr(e);
            proof {
                assert(f.len() == ns@.len());
                assert(f[i as int] == ns@[i as int]@);
                assert(owner_at(v, f[i as int], 0) == Some((k as nat, p as nat, m as nat)));
                fld_chain_t_step(v, cv, f, i as nat, k as nat, p as nat, m as nat, d as nat);
            }
            let cur = tfield_e(e, k, p, m, d, d1);
            proof {
                assert(view_expr(cur) == tfield(cv, k as nat, p as nat, m as nat, d as nat));
            }
            fld_chain_t_rec(tb, cur, ns, i + 1, d, d1)
        },
        None => {
            proof {
                assert(f.len() == ns@.len());
                assert(f[i as int] == ns@[i as int]@);
                assert(owner_at(v, f[i as int], 0) is None);
                fld_chain_t_none(v, view_expr(e), f, i as nat, d as nat);
            }
            None
        },
    }
}

/// 宣言の位置 j に式を置く（view_upd の上での一回の更新と同じ）。
fn set_upd_e(u: &mut Vec<Option<EExpr>>, j: usize, x: EExpr)
    requires
        j < u@.len(),
    ensures
        final(u)@.len() == old(u)@.len(),
        view_upd(final(u)@) == view_upd(old(u)@).update(j as int, Some(view_expr(x))),
{
    let ghost up = u@;
    let ghost xv = view_expr(x);
    u.set(j, Some(x));
    proof {
        assert forall|k: int| 0 <= k < view_upd(up).len() implies view_upd(u@)[k] == view_upd(up).update(j as int, Some(xv))[k] by {
            if k == j as int {
            } else {
                assert(u@[k] == up[k]);
            }
        }
        assert(view_upd(u@) =~= view_upd(up).update(j as int, Some(xv)));
    }
}

/// 書いた字段を宣言の位置に置く（rec_upd）の exec 版。字段の名前の列 ns と式の列 es は同じ長さで並ぶ
/// （構文の解析が作る。式の列が短い分は Unit と写し、rec_upd の写しと同じ）。
fn rec_upd_e(fs: &Vec<Vec<char>>, tb: &Vec<(Vec<char>, Option<Ty>, Vec<Vec<char>>, Option<Ty>)>, tagged: bool, sc: &mut Vec<Vec<char>>, decl: &Vec<Vec<char>>, ns: &Vec<Vec<char>>, es: &Vec<SExpr>) -> (r: Option<Vec<Option<EExpr>>>)
    ensures
        final(sc)@ == old(sc)@,
        match r {
            Some(u) => u@.len() == decl@.len() && rec_upd(vnames(fs@), vtb(tb@), tagged, vnames(old(sc)@), vnames(decl@), vfields(ns@, es@), 0, none_upd(
                decl@.len(),
            )) == Some(view_upd(u@)),
            None => rec_upd(vnames(fs@), vtb(tb@), tagged, vnames(old(sc)@), vnames(decl@), vfields(ns@, es@), 0, none_upd(
                decl@.len(),
            )) is None,
        },
    decreases es, 0nat,
{
    let ghost f = vnames(fs@);
    let ghost tv = vtb(tb@);
    let ghost d = vnames(decl@);
    let ghost s = vnames(sc@);
    let ghost s0 = sc@;
    let ghost fl = vfields(ns@, es@);
    let ghost u0 = none_upd(decl@.len());
    let mut u: Vec<Option<EExpr>> = Vec::new();
    let mut j0: usize = 0;
    while j0 < decl.len()
        invariant
            j0 <= decl@.len(),
            u@.len() == j0,
            forall|k: int| 0 <= k < j0 ==> (#[trigger] u@[k]) is None,
        decreases decl@.len() - j0,
    {
        u.push(None);
        j0 += 1;
    }
    proof {
        assert(view_upd(u@) =~= u0);
    }
    let mut i: usize = 0;
    while i < ns.len()
        invariant
            f == vnames(fs@),
            tv == vtb(tb@),
            d == vnames(decl@),
            s == vnames(sc@),
            s0 == sc@,
            s0 == old(sc)@,
            fl == vfields(ns@, es@),
            i <= ns@.len(),
            u@.len() == decl@.len(),
            rec_upd(f, tv, tagged, s, d, fl, 0, none_upd(decl@.len())) == rec_upd(f, tv, tagged, s, d, fl, i as nat, view_upd(u@)),
        decreases ns.len() - i,
    {
        proof {
            assert(fl[i as int].0 == ns@[i as int]@);
            if i < es@.len() {
                assert(fl[i as int].1 == vx(es@[i as int]));
            } else {
                assert(fl[i as int].1 == Sx::Unit);
            }
        }
        let j = match idx_e(decl, &ns[i]) {
            Some(j) => j,
            None => {
                proof {
                    rec_upd_none_idx(f, tv, tagged, s, d, fl, i as nat, view_upd(u@));
                }
                return None;
            },
        };
        if let Some(_) = &u[j] {
            proof {
                assert(view_upd(u@)[j as int] is Some);
                rec_upd_none_dup(f, tv, tagged, s, d, fl, i as nat, view_upd(u@), j as nat);
            }
            return None;
        }
        let ghost ui = view_upd(u@);
        proof {
            assert(u@[j as int] is None);
            assert(ui[j as int] is None);
        }
        if i < es.len() {
            match rx_e(fs, tb, tagged, sc, &es[i]) {
                Some(y) => {
                    proof {
                        assert(fl[i as int].1 == vx(es@[i as int]));
                        rec_upd_step(f, tv, tagged, s, d, fl, i as nat, ui, j as nat, view_expr(y));
                    }
                    set_upd_e(&mut u, j, y);
                },
                None => {
                    proof {
                        assert(fl[i as int].1 == vx(es@[i as int]));
                        rec_upd_none_rx(f, tv, tagged, s, d, fl, i as nat, ui, j as nat);
                    }
                    return None;
                },
            }
        } else {
            proof {
                assert(fl[i as int].1 == Sx::Unit);
                assert(rx(f, tv, tagged, s, Sx::Unit) == Some(Expr::Unit));
                rec_upd_step(f, tv, tagged, s, d, fl, i as nat, ui, j as nat, Expr::Unit);
            }
            set_upd_e(&mut u, j, EExpr::Unit);
        }
        i += 1;
    }
    proof {
        rec_upd_end(f, tv, tagged, s, d, fl, i as nat, view_upd(u@));
    }
    Some(u)
}

/// 記録の式の本体（rec_expr）の exec 版。基（解決済み）を受け、字段を置いて records_exec の record_e で拒否と展開を決める。
/// 基を let で束縛するときだけ、字段の式は空の名前を一つ足した scope で解決する（spec の rec_expr と同じ）。
fn rec_expr_e(fs: &Vec<Vec<char>>, tb: &Vec<(Vec<char>, Option<Ty>, Vec<Vec<char>>, Option<Ty>)>, tagged: bool, sc: &mut Vec<Vec<char>>, decl: &Vec<Vec<char>>, ns: &Vec<Vec<char>>, es: &Vec<SExpr>, base: Option<EExpr>) -> (r: Option<EExpr>)
    requires
        decl@.len() >= 1,
    ensures
        final(sc)@ == old(sc)@,
        match r {
            Some(x) => rec_expr(vnames(fs@), vtb(tb@), tagged, vnames(old(sc)@), vnames(decl@), vfields(ns@, es@), view_slot(base))
                == Some(view_expr(x)),
            None => rec_expr(vnames(fs@), vtb(tb@), tagged, vnames(old(sc)@), vnames(decl@), vfields(ns@, es@), view_slot(base))
                is None,
        },
    decreases es, 1nat,
{
    let deep = match &base {
        Some(e) => match e {
            EExpr::Var(_) => false,
            _ => ns.len() <= decl.len() && decl.len() - ns.len() >= 2,
        },
        None => false,
    };
    proof {
        if let Some(e) = &base {
            assert(view_expr(*e) is Var <==> (*e) is Var);
        }
    }
    let ghost s0 = sc@;
    if deep {
        sc.push(Vec::new());
        proof {
            vnames_push(s0, sc@[s0.len() as int]);
        }
    }
    let r_u = rec_upd_e(fs, tb, tagged, sc, decl, ns, es);
    if deep {
        let _ = sc.pop();
    }
    match r_u {
        Some(u) => match record_e(u, base, sc.len()) {
            Ok(x) => Some(x),
            Err(_) => None,
        },
        None => None,
    }
}

/// 構築（rec_t）の exec 版。印つきは基底を印の検査（tfield）で外してから rec_expr_e に渡し、pair(tag(k), ·) で包む。
fn rec_t_e(fs: &Vec<Vec<char>>, tb: &Vec<(Vec<char>, Option<Ty>, Vec<Vec<char>>, Option<Ty>)>, tagged: bool, sc: &mut Vec<Vec<char>>, k: usize, decl: &Vec<Vec<char>>, ns: &Vec<Vec<char>>, es: &Vec<SExpr>, base: Option<EExpr>) -> (r: Option<EExpr>)
    requires
        decl@.len() >= 1,
    ensures
        final(sc)@ == old(sc)@,
        match r {
            Some(x) => rec_t(vnames(fs@), vtb(tb@), tagged, vnames(old(sc)@), k as nat, vnames(decl@), vfields(ns@, es@), view_slot(base))
                == Some(view_expr(x)),
            None => rec_t(vnames(fs@), vtb(tb@), tagged, vnames(old(sc)@), k as nat, vnames(decl@), vfields(ns@, es@), view_slot(base))
                is None,
        },
    decreases es, 2nat,
{
    if tagged {
        let base2: Option<EExpr> = match base {
            Some(b) => {
                let ghost s0 = sc@;
                sc.push(Vec::new());
                let d1 = sc.len();
                let d = d1 - 1;
                let t = tfield_e(b, k, 0, 1, d, d1);
                let _ = sc.pop();
                proof {
                    assert(sc@ =~= s0);
                }
                Some(t)
            },
            None => None,
        };
        match rec_expr_e(fs, tb, tagged, sc, decl, ns, es, base2) {
            Some(x) => Some(EExpr::Pair(Box::new(tag_expr_e(k)), Box::new(x))),
            None => None,
        }
    } else {
        rec_expr_e(fs, tb, tagged, sc, decl, ns, es, base)
    }
}

/// 記録の式（SExpr::Rec）の exec 版：名前表の記録（字段を持つ項目）を見て、rec_expr に渡す。
fn rx_rec_e(fs: &Vec<Vec<char>>, tb: &Vec<(Vec<char>, Option<Ty>, Vec<Vec<char>>, Option<Ty>)>, tagged: bool, sc: &mut Vec<Vec<char>>, e: &SExpr) -> (r: Option<EExpr>)
    requires
        e is Rec,
    ensures
        final(sc)@ == old(sc)@,
        match r {
            Some(x) => rx(vnames(fs@), vtb(tb@), tagged, vnames(old(sc)@), vx(*e)) == Some(view_expr(x)),
            None => rx(vnames(fs@), vtb(tb@), tagged, vnames(old(sc)@), vx(*e)) is None,
        },
    decreases e, 0nat,
{
    if let SExpr::Rec(r, ns, es, base) = e {
        let k = match tidx_e(tb, r) {
            Some(k) => k,
            None => return None,
        };
        if !is_rec_slot_e(&tb[k].2) {
            return None;
        }
        let empty: Vec<char> = Vec::new();
        match idx_e(sc, &empty) {
            Some(_) => return None,
            None => {},
        }
        let decl = &tb[k].2;
        proof {
            assert(decl@ == tb@[k as int].2@);
            assert(decl@.len() >= 1);
            assert(vx(*e) == Sx::Rec(r@, vfields(ns@, es@), vbase(*base)));
        }
        match base {
            None => rec_t_e(fs, tb, tagged, sc, k, decl, ns, es, None),
            Some(b) => match rx_e(fs, tb, tagged, sc, b) {
                Some(bx) => rec_t_e(fs, tb, tagged, sc, k, decl, ns, es, Some(bx)),
                None => None,
            },
        }
    } else {
        None
    }
}

/// 記録の参照（SExpr::Fld）の exec 版：受ける式を解決し、字段の連鎖を展開する。
fn rx_fld_e(fs: &Vec<Vec<char>>, tb: &Vec<(Vec<char>, Option<Ty>, Vec<Vec<char>>, Option<Ty>)>, tagged: bool, sc: &mut Vec<Vec<char>>, e: &SExpr) -> (r: Option<EExpr>)
    requires
        e is Fld,
    ensures
        final(sc)@ == old(sc)@,
        match r {
            Some(x) => rx(vnames(fs@), vtb(tb@), tagged, vnames(old(sc)@), vx(*e)) == Some(view_expr(x)),
            None => rx(vnames(fs@), vtb(tb@), tagged, vnames(old(sc)@), vx(*e)) is None,
        },
    decreases e, 0nat,
{
    if let SExpr::Fld(a, ns) = e {
        let inner = match rx_e(fs, tb, tagged, sc, a) {
            Some(x) => x,
            None => return None,
        };
        if tagged {
            let ghost s0 = sc@;
            sc.push(Vec::new());
            let d1 = sc.len();
            let d = d1 - 1;
            let r = fld_chain_t_rec(tb, inner, ns, 0, d, d1);
            let _ = sc.pop();
            proof {
                assert(sc@ =~= s0);
            }
            r
        } else {
            fld_chain_e(tb, inner, ns)
        }
    } else {
        None
    }
}

fn rx_let_e(fs: &Vec<Vec<char>>, tb: &Vec<(Vec<char>, Option<Ty>, Vec<Vec<char>>, Option<Ty>)>, tagged: bool, sc: &mut Vec<Vec<char>>, e: &SExpr) -> (r: Option<EExpr>)
    requires
        e is Let,
    ensures
        final(sc)@ == old(sc)@,
        match r {
            Some(x) => rx(vnames(fs@), vtb(tb@), tagged, vnames(old(sc)@), vx(*e)) == Some(view_expr(x)),
            None => rx(vnames(fs@), vtb(tb@), tagged, vnames(old(sc)@), vx(*e)) is None,
        },
    decreases e, 0nat,
{
    let ghost s0 = sc@;
    if let SExpr::Let(x, a, b) = e {
        if idx_e(sc, x).is_some() {
            return None;
        }
        let ra = rx_e(fs, tb, tagged, sc, a);
        if ra.is_none() {
            return None;
        }
        sc.push(clone_chars(x));
        let k = sc.len() - 1;
        proof {
            vnames_push(s0, sc@[k as int]);
        }
        let rb = rx_e(fs, tb, tagged, sc, b);
        sc.pop();
        proof {
            assert(sc@ =~= s0);
        }
        match (ra, rb) {
            (Some(ra), Some(rb)) => Some(EExpr::Let(k, Box::new(ra), Box::new(rb))),
            _ => None,
        }
    } else {
        None
    }
}

fn rx_fold_e(fs: &Vec<Vec<char>>, tb: &Vec<(Vec<char>, Option<Ty>, Vec<Vec<char>>, Option<Ty>)>, tagged: bool, sc: &mut Vec<Vec<char>>, e: &SExpr) -> (r: Option<EExpr>)
    requires
        e is Fold,
    ensures
        final(sc)@ == old(sc)@,
        match r {
            Some(x) => rx(vnames(fs@), vtb(tb@), tagged, vnames(old(sc)@), vx(*e)) == Some(view_expr(x)),
            None => rx(vnames(fs@), vtb(tb@), tagged, vnames(old(sc)@), vx(*e)) is None,
        },
    decreases e, 0nat,
{
    let ghost s0 = sc@;
    if let SExpr::Fold(l, i, a, x, b) = e {
        if eq_chars(a, x) || idx_e(sc, a).is_some() || idx_e(sc, x).is_some() {
            return None;
        }
        let rl = rx_e(fs, tb, tagged, sc, l);
        let ri = rx_e(fs, tb, tagged, sc, i);
        if rl.is_none() || ri.is_none() {
            return None;
        }
        sc.push(clone_chars(a));
        let ghost s1 = sc@;
        sc.push(clone_chars(x));
        let k1 = sc.len() - 1;
        let k = k1 - 1;
        proof {
            vnames_push(s0, s1[k as int]);
            vnames_push(s1, sc@[k1 as int]);
        }
        let rb = rx_e(fs, tb, tagged, sc, b);
        sc.pop();
        sc.pop();
        proof {
            assert(sc@ =~= s0);
        }
        match (rl, ri, rb) {
            (Some(rl), Some(ri), Some(rb)) => Some(EExpr::Fold(Box::new(rl), Box::new(ri), k, k1, Box::new(rb))),
            _ => None,
        }
    } else {
        None
    }
}

pub fn rxs_e(fs: &Vec<Vec<char>>, tb: &Vec<(Vec<char>, Option<Ty>, Vec<Vec<char>>, Option<Ty>)>, tagged: bool, sc: &mut Vec<Vec<char>>, es: &Vec<SExpr>) -> (r: Option<Vec<EExpr>>)
    ensures
        final(sc)@ == old(sc)@,
        match r {
            Some(xs) => rxs(vnames(fs@), vtb(tb@), tagged, vnames(old(sc)@), vxs(*es), 0) == Some(view_exprs(xs)),
            None => rxs(vnames(fs@), vtb(tb@), tagged, vnames(old(sc)@), vxs(*es), 0) is None,
        },
    decreases es, 0nat,
{
    let ghost f = vnames(fs@);
    let ghost tv = vtb(tb@);
    let ghost s = vnames(sc@);
    let ghost s0 = sc@;
    let ghost v = vxs(*es);
    let mut out: Vec<EExpr> = Vec::new();
    let mut i: usize = 0;
    proof {
        assert(view_exprs(out) =~= Seq::<Expr>::empty());
        if let Some(w) = rxs(f, tv, tagged, s, v, 0) {
            assert(Seq::<Expr>::empty() + w =~= w);
        }
    }
    while i < es.len()
        invariant
            f == vnames(fs@),
            tv == vtb(tb@),
            s == vnames(sc@),
            sc@ == s0,
            s0 == old(sc)@,
            v == vxs(*es),
            i <= es@.len(),
            rxs(f, tv, tagged, s, v, 0) == cato(view_exprs(out), rxs(f, tv, tagged, s, v, i as nat)),
        decreases es@.len() - i,
    {
        proof {
            vstd::std_specs::vec::axiom_vec_index_decreases(*es, i as int);
            assert(v[i as int] == vx(es@[i as int]));
        }
        let ghost o0 = out;
        match rx_e(fs, tb, tagged, sc, &es[i]) {
            Some(x) => {
                let ghost xv = view_expr(x);
                out.push(x);
                proof {
                    view_exprs_push(o0, out, x);
                    if let Some(w) = rxs(f, tv, tagged, s, v, (i + 1) as nat) {
                        assert(view_exprs(o0) + (seq![xv] + w) =~= view_exprs(out) + w);
                    }
                }
                i += 1;
            },
            None => return None,
        }
    }
    proof {
        assert(view_exprs(out) + Seq::<Expr>::empty() =~= view_exprs(out));
    }
    Some(out)
}

pub open spec fn vfuncs(fs: Seq<EFunc>) -> Seq<Func> {
    Seq::new(fs.len(), |i: int| view_func(fs[i]))
}

fn rfunc_e(fs: &Vec<Vec<char>>, tb: &Vec<(Vec<char>, Option<Ty>, Vec<Vec<char>>, Option<Ty>)>, tagged: bool, d: &SDecl) -> (r: Option<EFunc>)
    ensures
        match r {
            Some(f) => rfunc(vnames(fs@), vtb(tb@), tagged, vd(*d)) == Some(view_func(f)),
            None => rfunc(vnames(fs@), vtb(tb@), tagged, vd(*d)) is None,
        },
{
    match d {
        SDecl::Fn(fname, ps, ret, body) => {
            let ghost pv = vps(ps@);
            let ghost tv = vtb(tb@);
            let mut sc: Vec<Vec<char>> = Vec::new();
            let mut params: Vec<(usize, Ty)> = Vec::new();
            let mut i: usize = 0;
            while i < ps.len()
                invariant
                    pv == vps(ps@),
                    tv == vtb(tb@),
                    i <= ps@.len(),
                    vnames(sc@) == pnames(pv).subrange(0, i as int),
                    view_params(params@) == rparams(pv, tv, tagged).subrange(0, i as int),
                    sc@.len() == i as int,
                    vd(*d) == Sd::Fn(fname@, pv, vty(*ret), vx(*body)),
                    forall|k: int| 0 <= k < i ==> to_ty(#[trigger] pv[k].1, tv, tagged) is Some,
                decreases ps@.len() - i,
            {
                let ghost s0 = sc@;
                let ghost q0 = params@;
                let (x, t) = &ps[i];
                let u = match to_ty_e(t, tb, tagged) {
                    Some(u) => u,
                    None => {
                        proof {
                            assert(to_ty(pv[i as int].1, tv, tagged) is None);
                            assert(!params_ok(pv, tv, tagged));
                            assert(rfunc(vnames(fs@), tv, tagged, vd(*d)) is None);
                        }
                        return None;
                    },
                };
                sc.push(clone_chars(x));
                params.push((i, ty_clone(&u)));
                proof {
                    vnames_push(s0, sc@[i as int]);
                    assert(pv[i as int] == (x@, vty(*t)));
                    assert(vnames(sc@) == vnames(s0).push(x@));
                    assert(pnames(pv).subrange(0, i + 1) =~= pnames(pv).subrange(0, i as int).push(x@));
                    assert(view_params(params@) =~= view_params(q0).push((i as nat, u)));
                    assert(rparams(pv, tv, tagged).subrange(0, i + 1) =~= rparams(pv, tv, tagged).subrange(0, i as int).push((i as nat, u)));
                }
                i += 1;
            }
            proof {
                assert(pnames(pv).subrange(0, i as int) =~= pnames(pv));
                assert(rparams(pv, tv, tagged).subrange(0, i as int) =~= rparams(pv, tv, tagged));
            }
            proof {
                assert(params_ok(pv, tv, tagged));
            }
            if !distinct_e(&sc) {
                return None;
            }
            let ret1 = match to_ty_e(ret, tb, tagged) {
                Some(u) => u,
                None => return None,
            };
            match rx_e(fs, tb, tagged, &mut sc, body) {
                Some(b) => Some(EFunc { params, ret: ret1, body: b }),
                None => None,
            }
        },
        SDecl::Entry(_) => None,
        SDecl::RecTy(_, _, _) | SDecl::Sum(_, _) => None,
    }
}

/// 名前解決と entry 検査。関数列と entry の添字を返す。写しは印なし（tagged = false）。
fn resolve_e_t(p: &Vec<SDecl>, tagged: bool) -> (r: Option<(Vec<EFunc>, usize)>)
    ensures
        match r {
            Some((fs, g)) => resolve_t(vds(p@), tagged) == Some((vfuncs(fs@), g as nat)) && g < fs@.len(),
            None => resolve_t(vds(p@), tagged) is None,
        },
{
    let tb = match decl_table_e(p) {
        Some(t) => t,
        None => return None,
    };
    let ghost tv = vtb(tb@);
    let ghost v = vds(p@);
    proof {
        assert(v.len() == p@.len());
    }
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
            tv == vtb(tb@),
            i <= p@.len(),
            vnames(names@) == names_of(fns_upto(v, i as nat)),
            fns_upto(v, i as nat) == Seq::new(fidx@.len(), |m: int| v[fidx@[m] as int]),
            forall|k: int| 0 <= k < fidx@.len() ==> #[trigger] fidx@[k] < p@.len(),
            ents_upto(v, i as nat) == Seq::new(ents@.len(), |m: int| v[ents@[m] as int]->Entry_0),
            forall|k: int| 0 <= k < ents@.len() ==> #[trigger] ents@[k] < p@.len() && v[ents@[k] as int] is Entry,
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
                    assert(fns_upto(v, (i + 1) as nat) == f0);
                    assert(ents_upto(v, (i + 1) as nat) == e0.push(v[i as int]->Entry_0));
                    assert(e0.push(v[i as int]->Entry_0) =~= Seq::new(ents@.len(), |m: int| v[ents@[m] as int]->Entry_0));
                }
            },
            // 型の宣言（記録・直和型）は名前表（decl_table_e）が検査し、関数の名前解決の対象外。
            SDecl::RecTy(_, _, _) | SDecl::Sum(_, _) => {
                proof {
                    assert(fns_upto(v, (i + 1) as nat) == f0);
                    assert(ents_upto(v, (i + 1) as nat) == e0);
                }
            },
        }
        i += 1;
    }
    let ghost ds = fns_upto(v, v.len());
    let ghost fsv = names_of(ds);
    if !distinct_e(&names) || ents.len() != 1 {
        return None;
    }
    let mut out: Vec<EFunc> = Vec::new();
    let mut k: usize = 0;
    proof {
        assert(vfuncs(out@) =~= Seq::<Func>::empty());
    }
    while k < fidx.len()
        invariant
            v == vds(p@),
            tv == vtb(tb@),
            ds == fns_upto(v, v.len()),
            fsv == names_of(ds),
            vnames(names@) == fsv,
            ds == Seq::new(fidx@.len(), |m: int| v[fidx@[m] as int]),
            forall|m: int| 0 <= m < fidx@.len() ==> #[trigger] fidx@[m] < p@.len(),
            k <= fidx@.len(),
            out@.len() == k,
            decl_table(vds(p@), p@.len() as nat) == Some(tv),
            rfuncs(fsv, tv, tagged, ds, k as nat) == Some(vfuncs(out@)),
        decreases fidx@.len() - k,
    {
        let j = fidx[k];
        proof {
            assert(ds[k as int] == v[j as int]);
            assert(v[j as int] == vd(p@[j as int]));
        }
        match rfunc_e(&names, &tb, tagged, &p[j]) {
            Some(f) => {
                let ghost o0 = out@;
                out.push(f);
                proof {
                    assert(vfuncs(out@) =~= vfuncs(o0).push(view_func(f)));
                }
                k += 1;
            },
            None => {
                proof {
                    rfuncs_none(fsv, tv, tagged, ds, (k + 1) as nat, ds.len());
                    assert(rfuncs(fsv, tv, tagged, ds, ds.len()) is None);
                    resolve_none(vds(p@), tv, tagged);
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
    }
    if out[g].params.len() != 1 {
        return None;
    }
    Some((out, g))
}

/// 印なしの名前解決（resolve）の exec 版。パイプラインと既存の試験が使う。
pub fn resolve_e(p: &Vec<SDecl>) -> (r: Option<(Vec<EFunc>, usize)>)
    ensures
        match r {
            Some((fs, g)) => resolve(vds(p@)) == Some((vfuncs(fs@), g as nat)) && g < fs@.len(),
            None => resolve(vds(p@)) is None,
        },
{
    resolve_e_t(p, false)
}

/// 印つきの名前解決（S3b）の exec 版。印つきの写しを検証済みの型検査（check_prog）へ渡す試験に使う。
pub fn resolve_tagged_e(p: &Vec<SDecl>) -> (r: Option<(Vec<EFunc>, usize)>)
    ensures
        match r {
            Some((fs, g)) => resolve_t(vds(p@), true) == Some((vfuncs(fs@), g as nat)) && g < fs@.len(),
            None => resolve_t(vds(p@), true) is None,
        },
{
    resolve_e_t(p, true)
}

/// 名前表が作れて、関数の解決が失敗すれば、resolve も失敗する（字段の名前の一意と entry の検査が
/// 通らなくても、結果は None なので、ここでは仮定しない）。
proof fn resolve_none(p: Seq<Sd>, tb: Seq<(Seq<char>, Option<Ty>, Seq<Seq<char>>, Option<Ty>)>, tagged: bool)
    requires
        decl_table(p, p.len()) == Some(tb),
        rfuncs(names_of(fns_upto(p, p.len())), tb, tagged, fns_upto(p, p.len()), fns_upto(p, p.len()).len()) is None,
    ensures
        resolve_t(p, tagged) is None,
{
}

/// 途中の関数が解決できなければ全体も解決できない。
proof fn rfuncs_none(fs: Seq<Seq<char>>, tb: Seq<(Seq<char>, Option<Ty>, Seq<Seq<char>>, Option<Ty>)>, tagged: bool, ds: Seq<Sd>, n: nat, m: nat)
    requires
        rfuncs(fs, tb, tagged, ds, n) is None,
        n <= m,
    ensures
        rfuncs(fs, tb, tagged, ds, m) is None,
    decreases m - n,
{
    if n < m {
        rfuncs_none(fs, tb, tagged, ds, n + 1, m);
    }
}

} // verus!
