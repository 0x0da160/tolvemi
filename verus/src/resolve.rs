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

/// 文字列リテラルは文字のリストの式になる。
pub open spec fn str_exprs(w: Seq<char>) -> Seq<Expr> {
    Seq::new(w.len(), |i: int| Expr::Char(w[i] as u32 as int))
}

/// 名前表の項目：宣言した型の名前、記録の印なしの展開（直和型は None）、記録の字段の名前（直和型は空）。
/// 項目の位置が名義の番号になる（設計の B2）。字段の持ち主は、その字段名を持つ項目の位置。
pub open spec fn tnames(tb: Seq<(Seq<char>, Option<Ty>, Seq<Seq<char>>)>) -> Seq<Seq<char>> {
    Seq::new(tb.len(), |i: int| tb[i].0)
}

/// 字段名 x は、名前表のどの記録の字段でもない（字段名はプログラム全体で一意：規則 4）。
pub open spec fn fresh(tb: Seq<(Seq<char>, Option<Ty>, Seq<Seq<char>>)>, x: Seq<char>) -> bool {
    forall|j: int| 0 <= j < tb.len() ==> idx(tb[j].2, x, 0) is None
}

/// 型の名前が、名前表の項目だけを引く（規則 1）。構造は to_ty と同じ。
pub open spec fn tyn(t: SType, tb: Seq<(Seq<char>, Option<Ty>, Seq<Seq<char>>)>) -> bool
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
pub open spec fn fields_ok(fs: Seq<(Seq<char>, SType)>, tb: Seq<(Seq<char>, Option<Ty>, Seq<Seq<char>>)>) -> bool {
    distinct(pnames(fs)) && forall|i: int| 0 <= i < fs.len() ==> fresh(tb, fs[i].0) && tyn(fs[i].1, tb)
}

/// 直和型の中身（構築子ごとの型の並び）は、前の項目と自分自身だけを引く（規則 1）。自分を引くのは再帰する直和型
/// （trusted の v1.14：`type L = Nil | Cons(Int, L)` は受理する）。tb は自分を足した表。不透明にして、表の等しさで書き換える。
#[verifier::opaque]
pub open spec fn vars_ok(vs: Seq<(Seq<char>, Seq<SType>)>, tb: Seq<(Seq<char>, Option<Ty>, Seq<Seq<char>>)>) -> bool {
    forall|i: int, a: int| 0 <= i < vs.len() && 0 <= a < vs[i].1.len() ==> tyn(vs[i].1[a], tb)
}

/// 記録の字段 i から末尾までの印なしの展開。右結合の Pair の入れ子で、末尾の字段の型はそのまま
/// （trusted の records.rs の record_type と同じ形）。
pub open spec fn rec_from(fs: Seq<(Seq<char>, SType)>, i: nat, tb: Seq<(Seq<char>, Option<Ty>, Seq<Seq<char>>)>) -> Option<Ty>
    decreases fs.len() - i,
{
    if i >= fs.len() {
        None
    } else if i + 1 == fs.len() {
        to_ty(fs[i as int].1, tb, false)
    } else {
        match (to_ty(fs[i as int].1, tb, false), rec_from(fs, i + 1, tb)) {
            (Some(u), Some(v)) => Some(Ty::Pair(Box::new(u), Box::new(v))),
            _ => None,
        }
    }
}

/// 宣言を名前表の末尾に足す。記録は、型名が新しく、字段の列が規則 1・4 を満たすときに足す。
/// 直和型は、型名が新しく、中身の型が前の項目と自分だけを引くときに足す（規則 1・3）。関数と entry は表に入らない。
#[verifier::opaque]
pub open spec fn tb_push(tb: Seq<(Seq<char>, Option<Ty>, Seq<Seq<char>>)>, d: Sd) -> Option<Seq<(Seq<char>, Option<Ty>, Seq<Seq<char>>)>> {
    match d {
        Sd::Fn(_, _, _, _) => Some(tb),
        Sd::Entry(_) => Some(tb),
        Sd::RecTy(r, fs, _) => if idx(tnames(tb), r, 0) is Some || !fields_ok(fs, tb) {
            None
        } else {
            Some(tb.push((r, rec_from(fs, 0, tb), pnames(fs))))
        },
        Sd::Sum(r, vs) => if idx(tnames(tb), r, 0) is Some || !vars_ok(vs, tb.push((r, None, Seq::empty()))) {
            None
        } else {
            Some(tb.push((r, None, Seq::empty())))
        },
    }
}

/// tb_push の場合分けの補題。tb_push は不透明で、ここでだけ開く。宣言の形（vd）を経由しても、
/// 構築子の形で書いた結論と同じ項として扱えるようにする（exec 側で使う）。
proof fn tb_push_rec_none(tb: Seq<(Seq<char>, Option<Ty>, Seq<Seq<char>>)>, r: Seq<char>, fs: Seq<(Seq<char>, SType)>, tc: bool)
    requires
        idx(tnames(tb), r, 0) is Some || !fields_ok(fs, tb),
    ensures
        tb_push(tb, Sd::RecTy(r, fs, tc)) is None,
{
    reveal(tb_push);
}

proof fn tb_push_rec_some(tb: Seq<(Seq<char>, Option<Ty>, Seq<Seq<char>>)>, r: Seq<char>, fs: Seq<(Seq<char>, SType)>, tc: bool)
    requires
        idx(tnames(tb), r, 0) is None,
        fields_ok(fs, tb),
    ensures
        tb_push(tb, Sd::RecTy(r, fs, tc)) == Some(tb.push((r, rec_from(fs, 0, tb), pnames(fs)))),
{
    reveal(tb_push);
}

proof fn tb_push_sum_none(tb: Seq<(Seq<char>, Option<Ty>, Seq<Seq<char>>)>, r: Seq<char>, vs: Seq<(Seq<char>, Seq<SType>)>)
    requires
        idx(tnames(tb), r, 0) is Some || !vars_ok(vs, tb.push((r, None, Seq::empty()))),
    ensures
        tb_push(tb, Sd::Sum(r, vs)) is None,
{
    reveal(tb_push);
}

proof fn tb_push_sum_some(tb: Seq<(Seq<char>, Option<Ty>, Seq<Seq<char>>)>, r: Seq<char>, vs: Seq<(Seq<char>, Seq<SType>)>)
    requires
        idx(tnames(tb), r, 0) is None,
        vars_ok(vs, tb.push((r, None, Seq::empty()))),
    ensures
        tb_push(tb, Sd::Sum(r, vs)) == Some(tb.push((r, None, Seq::empty()))),
{
    reveal(tb_push);
}

proof fn tb_push_other(tb: Seq<(Seq<char>, Option<Ty>, Seq<Seq<char>>)>, d: Sd)
    requires
        d matches Sd::Fn(..) || d matches Sd::Entry(..),
    ensures
        tb_push(tb, d) == Some(tb),
{
    reveal(tb_push);
}

/// 宣言の先頭 n 個の名前表（宣言の順）。どれかの宣言が規則に反すれば None。
/// 型名と関数名の一致は許す（規則 5）。関数の注釈と本体は、ここで作る表の全部を引く（規則 2）。
pub open spec fn decl_table(p: Seq<Sd>, n: nat) -> Option<Seq<(Seq<char>, Option<Ty>, Seq<Seq<char>>)>>
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

/// 印つきの型：記録の項目（番号 k、印なしの展開 u）は Pair<tag(k), u>。印なしは u のまま。
pub proof fn named_tagged(tb: Seq<(Seq<char>, Option<Ty>, Seq<Seq<char>>)>, x: Seq<char>, k: nat)
    requires
        idx(tnames(tb), x, 0) == Some(k),
        k < tb.len(),
        tb[k as int].1 is Some,
    ensures
        to_ty(SType::Named(x), tb, true) == Some(Ty::Pair(Box::new(tag_ty(k)), Box::new(tb[k as int].1->Some_0))),
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
proof fn tb_push_facts(tb: Seq<(Seq<char>, Option<Ty>, Seq<Seq<char>>)>, d: Sd)
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
/// 印つき（tagged = true）は記録の Pair<tag(k), 展開>（直和型は展開が None なので None）。
/// Dict は v1.9 の消去で List<Pair<K, V>> になる（dict.rs の erase_in_place と同じ形）。
/// `tagged` は印つきの写し（S2b）。resolve と resolve_e は印なし（false）を使う。
pub open spec fn to_ty(t: SType, tb: Seq<(Seq<char>, Option<Ty>, Seq<Seq<char>>)>, tagged: bool) -> Option<Ty>
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
            Some(k) => match tb[k as int].1 {
                Some(u) => if tagged { Some(Ty::Pair(Box::new(tag_ty(k)), Box::new(u))) } else { Some(u) },
                None => None,
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
pub open spec fn ty_or_unit(t: SType, tb: Seq<(Seq<char>, Option<Ty>, Seq<Seq<char>>)>, tagged: bool) -> Ty {
    match to_ty(t, tb, tagged) {
        Some(u) => u,
        None => Ty::Unit,
    }
}

/// 引数の型は全て核の型に写せる。
pub open spec fn params_ok(ps: Seq<(Seq<char>, SType)>, tb: Seq<(Seq<char>, Option<Ty>, Seq<Seq<char>>)>, tagged: bool) -> bool {
    forall|k: int| 0 <= k < ps.len() ==> to_ty(#[trigger] ps[k].1, tb, tagged) is Some
}

/// 式の名前解決。fs は関数名の列、tb は名前表、sc は可視変数の列（外側から順）。
pub open spec fn rx(fs: Seq<Seq<char>>, tb: Seq<(Seq<char>, Option<Ty>, Seq<Seq<char>>)>, tagged: bool, sc: Seq<Seq<char>>, e: Sx) -> Option<Expr>
    decreases e, 0nat,
{
    match e {
        Sx::Int(n) => Some(Expr::Int(n)),
        Sx::Chr(c) => Some(Expr::Char(c as u32 as int)),
        Sx::Str(w) => Some(Expr::List(Ty::Char, str_exprs(w))),
        Sx::Bool(b) => Some(Expr::Bool(b)),
        Sx::Unit => Some(Expr::Unit),
        Sx::Var(x) => match idx(sc, x, 0) {
            Some(k) => Some(Expr::Var(k)),
            None => None,
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
        Sx::Call(f, es) => match (idx(fs, f, 0), rxs(fs, tb, tagged, sc, es, 0)) {
            (Some(g), Some(xs)) => Some(Expr::Call(g, xs)),
            _ => None,
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
        // レコードは検証済みの核にまだ入っていない（段階 2）。
        Sx::Fld(..) | Sx::Rec(..) => None,
        // match 式は名前解決の対象外（段階 1a の範囲では核に入れない）。
        Sx::SumMatch(..) => None,
        // hof は名前解決の対象外（字句・構文の段階だけで扱う）。
        Sx::Hof(..) => None,
        // loop も名前解決の対象外（字句・構文の段階だけで扱う）。
        Sx::Loop(..) => None,
        // dict の形も名前解決の対象外（字句・構文の段階だけで扱う）。
        Sx::DictNew(..) | Sx::DictOp(..) => None,
    }
}

pub open spec fn rxs(fs: Seq<Seq<char>>, tb: Seq<(Seq<char>, Option<Ty>, Seq<Seq<char>>)>, tagged: bool, sc: Seq<Seq<char>>, es: Seq<Sx>, i: nat) -> Option<Seq<Expr>>
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

pub open spec fn rparams(ps: Seq<(Seq<char>, SType)>, tb: Seq<(Seq<char>, Option<Ty>, Seq<Seq<char>>)>, tagged: bool) -> Seq<(nat, Ty)> {
    Seq::new(ps.len(), |k: int| (k as nat, ty_or_unit(ps[k].1, tb, tagged)))
}

/// 関数の宣言の名前解決。型の注釈と本体は、名前表の全部の項目を引く（規則 2）。
pub open spec fn rfunc(fs: Seq<Seq<char>>, tb: Seq<(Seq<char>, Option<Ty>, Seq<Seq<char>>)>, tagged: bool, d: Sd) -> Option<Func> {
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
pub open spec fn rfuncs(fs: Seq<Seq<char>>, tb: Seq<(Seq<char>, Option<Ty>, Seq<Seq<char>>)>, tagged: bool, ds: Seq<Sd>, n: nat) -> Option<Seq<Func>>
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
/// 写しは印なし（tagged = false）。印つきの写しは S5b で pipeline から渡す。
pub open spec fn resolve(p: Seq<Sd>) -> Option<(Seq<Func>, nat)> {
    let ds = fns_upto(p, p.len());
    let fs = names_of(ds);
    let es = ents_upto(p, p.len());
    match decl_table(p, p.len()) {
        None => None,
        Some(tb) => if !distinct(fs) || es.len() != 1 {
            None
        } else {
            match (rfuncs(fs, tb, false, ds, ds.len()), idx(fs, es[0], 0)) {
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

/// 名前解決の結果は scope 整合で、scope 内の名前は常に相異なる（シャドーがない）。
pub proof fn rx_scoped(fs: Seq<Seq<char>>, tb: Seq<(Seq<char>, Option<Ty>, Seq<Seq<char>>)>, tagged: bool, sc: Seq<Seq<char>>, e: Sx)
    requires
        distinct(sc),
    ensures
        rx(fs, tb, tagged, sc, e) matches Some(x) ==> scoped(x, sc.len()),
    decreases e, 0nat,
{
    match e {
        Sx::Var(x) => idx_props(sc, x, 0),
        Sx::Str(w) => str_scoped(w, sc.len(), 0),
        Sx::List(_, es) => rxs_scoped(fs, tb, tagged, sc, es, 0),
        Sx::Some(a) => rx_scoped(fs, tb, tagged, sc, *a),
        Sx::Pair(a, b) => {
            rx_scoped(fs, tb, tagged, sc, *a);
            rx_scoped(fs, tb, tagged, sc, *b);
        },
        Sx::Builtin(_, es) => rxs_scoped(fs, tb, tagged, sc, es, 0),
        Sx::Call(_, es) => rxs_scoped(fs, tb, tagged, sc, es, 0),
        Sx::Let(x, a, b) => {
            idx_props(sc, x, 0);
            rx_scoped(fs, tb, tagged, sc, *a);
            if idx(sc, x, 0) is None {
                let s2 = sc.push(x);
                assert forall|i: int, j: int| 0 <= i < j < s2.len() implies s2[i] != s2[j] by {
                    if j == sc.len() {
                        assert(sc[i] != x);
                    }
                }
                rx_scoped(fs, tb, tagged, s2, *b);
            }
        },
        Sx::If(c, a, b) => {
            rx_scoped(fs, tb, tagged, sc, *c);
            rx_scoped(fs, tb, tagged, sc, *a);
            rx_scoped(fs, tb, tagged, sc, *b);
        },
        Sx::Fold(l, i, a, x, b) => {
            idx_props(sc, a, 0);
            idx_props(sc, x, 0);
            rx_scoped(fs, tb, tagged, sc, *l);
            rx_scoped(fs, tb, tagged, sc, *i);
            if !(a == x || idx(sc, a, 0) is Some || idx(sc, x, 0) is Some) {
                let s2 = sc.push(a).push(x);
                assert forall|p: int, q: int| 0 <= p < q < s2.len() implies s2[p] != s2[q] by {
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
        },
        Sx::Match(m, n, x, b) => {
            idx_props(sc, x, 0);
            rx_scoped(fs, tb, tagged, sc, *m);
            rx_scoped(fs, tb, tagged, sc, *n);
            if idx(sc, x, 0) is None {
                let s2 = sc.push(x);
                assert forall|i: int, j: int| 0 <= i < j < s2.len() implies s2[i] != s2[j] by {
                    if j == sc.len() {
                        assert(sc[i] != x);
                    }
                }
                rx_scoped(fs, tb, tagged, s2, *b);
            }
        },
        Sx::Inj(_, _, _, a) => rx_scoped(fs, tb, tagged, sc, *a),
        Sx::MatchR(m, x, a, y, b) => {
            idx_props(sc, x, 0);
            idx_props(sc, y, 0);
            rx_scoped(fs, tb, tagged, sc, *m);
            if idx(sc, x, 0) is None {
                let s2 = sc.push(x);
                assert forall|i: int, j: int| 0 <= i < j < s2.len() implies s2[i] != s2[j] by {
                    if j == sc.len() {
                        assert(sc[i] != x);
                    }
                }
                rx_scoped(fs, tb, tagged, s2, *a);
            }
            if idx(sc, y, 0) is None {
                let s3 = sc.push(y);
                assert forall|i: int, j: int| 0 <= i < j < s3.len() implies s3[i] != s3[j] by {
                    if j == sc.len() {
                        assert(sc[i] != y);
                    }
                }
                rx_scoped(fs, tb, tagged, s3, *b);
            }
        },
        _ => {},
    }
}

pub proof fn rxs_scoped(fs: Seq<Seq<char>>, tb: Seq<(Seq<char>, Option<Ty>, Seq<Seq<char>>)>, tagged: bool, sc: Seq<Seq<char>>, es: Seq<Sx>, i: nat)
    requires
        distinct(sc),
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
pub open spec fn vtb(tb: Seq<(Vec<char>, Option<Ty>, Vec<Vec<char>>)>) -> Seq<(Seq<char>, Option<Ty>, Seq<Seq<char>>)> {
    Seq::new(tb.len(), |i: int| (tb[i].0@, tb[i].1, vnames(tb[i].2@)))
}

fn idx_e(s: &Vec<Vec<char>>, x: &Vec<char>) -> (r: Option<usize>)
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

fn distinct_e(s: &Vec<Vec<char>>) -> (r: bool)
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

proof fn vnames_push(a: Seq<Vec<char>>, x: Vec<char>)
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
fn tidx_e(tb: &Vec<(Vec<char>, Option<Ty>, Vec<Vec<char>>)>, x: &Vec<char>) -> (r: Option<usize>)
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

/// 印の型の exec 版（tag_ty の exec 版）。
fn tag_ty_e(k: usize) -> (r: Ty)
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
fn to_ty_e(t: &STy, tb: &Vec<(Vec<char>, Option<Ty>, Vec<Vec<char>>)>, tagged: bool) -> (r: Option<Ty>)
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
            Some(k) => match clone_opt(&tb[k].1) {
                Some(u) => if tagged {
                    Some(Ty::Pair(Box::new(tag_ty_e(k)), Box::new(u)))
                } else {
                    Some(u)
                },
                None => None,
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
fn tyn_e(t: &STy, tb: &Vec<(Vec<char>, Option<Ty>, Vec<Vec<char>>)>) -> (r: bool)
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
fn fresh_e(tb: &Vec<(Vec<char>, Option<Ty>, Vec<Vec<char>>)>, x: &Vec<char>) -> (r: bool)
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

/// 記録の印なしの展開（rec_from(…, 0) の exec 版）。字段の列の末尾から組み立てる。
fn rec_exp_e(fs: &Vec<(Vec<char>, STy)>, tb: &Vec<(Vec<char>, Option<Ty>, Vec<Vec<char>>)>) -> (r: Option<Ty>)
    ensures
        r == rec_from(vps(fs@), 0, vtb(tb@)),
{
    let n = fs.len();
    if n == 0 {
        return None;
    }
    let mut i: usize = n - 1;
    let mut acc: Option<Ty> = to_ty_e(&fs[i].1, tb, false);
    while i > 0
        invariant
            n == fs@.len(),
            i < n,
            acc == rec_from(vps(fs@), i as nat, vtb(tb@)),
        decreases i,
    {
        i -= 1;
        let u = to_ty_e(&fs[i].1, tb, false);
        acc = match (u, acc) {
            (Some(u), Some(v)) => Some(Ty::Pair(Box::new(u), Box::new(v))),
            _ => None,
        };
    }
    acc
}

/// 記録の字段の列が規則 1・4 を満たすか（fields_ok の exec 版）。fnv は fs の字段名の列。
fn fields_ok_e(fs: &Vec<(Vec<char>, STy)>, tb: &Vec<(Vec<char>, Option<Ty>, Vec<Vec<char>>)>, fnv: &Vec<Vec<char>>) -> (r: bool)
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
fn vars_ok_e(vs: &Vec<(Vec<char>, Vec<STy>)>, tb: &Vec<(Vec<char>, Option<Ty>, Vec<Vec<char>>)>) -> (r: bool)
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

/// 宣言を名前表の末尾に足す（tb_push の exec 版）。足せないときは None。
/// 字段と直和型の中身は、移す前の名前表 tb だけを引いて調べ（ループは補助関数に置く）、通ったあとで tb を移して足す。
fn tb_push_e(tb: Vec<(Vec<char>, Option<Ty>, Vec<Vec<char>>)>, d: &SDecl) -> (r: Option<Vec<(Vec<char>, Option<Ty>, Vec<Vec<char>>)>>)
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
            let exp = rec_exp_e(fs, &tb);
            let mut out = tb;
            out.push((clone_chars(r), exp, fnv));
            proof {
                assert(vtb(out@) =~= vtb(tb@).push((r@, rec_from(vps(fs@), 0, vtb(tb@)), pnames(vps(fs@)))));
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
            out.push((clone_chars(r), None, Vec::new()));
            proof {
                assert(vnames(Seq::<Vec<char>>::empty()) =~= Seq::<Seq<char>>::empty());
                assert(vtb(out@) =~= vtb(tb@).push((r@, None, Seq::empty())));
                assert(vars_ok(vvars(vs@), vtb(out@)) == vars_ok(vvars(vs@), vtb(tb@).push((r@, None, Seq::empty()))));
            }
            if !vars_ok_e(vs, &out) {
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
            Some(out)
        },
    }
}

/// 名前表の exec 版（decl_table の exec 版）。宣言の順に足す。規則に反すれば None。
fn decl_table_e(p: &Vec<SDecl>) -> (r: Option<Vec<(Vec<char>, Option<Ty>, Vec<Vec<char>>)>>)
    ensures
        match r {
            Some(tb) => decl_table(vds(p@), p@.len() as nat) == Some(vtb(tb@)),
            None => decl_table(vds(p@), p@.len() as nat) is None,
        },
{
    let mut tb: Vec<(Vec<char>, Option<Ty>, Vec<Vec<char>>)> = Vec::new();
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
    let mut tb: Vec<(Vec<char>, Option<Ty>, Vec<Vec<char>>)> = Vec::new();
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

pub fn rx_e(fs: &Vec<Vec<char>>, tb: &Vec<(Vec<char>, Option<Ty>, Vec<Vec<char>>)>, tagged: bool, sc: &mut Vec<Vec<char>>, e: &SExpr) -> (r: Option<EExpr>)
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
        SExpr::Var(x) => match idx_e(sc, x) {
            Some(k) => Some(EExpr::Var(k)),
            None => None,
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
        SExpr::Call(g, es) => {
            let gi = idx_e(fs, g);
            let xs = rxs_e(fs, tb, tagged, sc, es);
            match (gi, xs) {
                (Some(gi), Some(xs)) => Some(EExpr::Call(gi, xs)),
                _ => None,
            }
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
        // レコードは検証済みの核にまだ入っていない（段階 2）。
        SExpr::Fld(..) | SExpr::Rec(..) => None,
        // match 式は名前解決の対象外（段階 1a の範囲では核に入れない）。
        SExpr::SumMatch(..) => None,
        // hof は名前解決の対象外（字句・構文の段階だけで扱う）。
        SExpr::Hof(..) => None,
        // loop も名前解決の対象外（字句・構文の段階だけで扱う）。
        SExpr::Loop(..) => None,
        // dict の形も名前解決の対象外（字句・構文の段階だけで扱う）。
        SExpr::DictNew(..) | SExpr::DictOp(..) => None,
    }
}

fn rx_matchr_e(fs: &Vec<Vec<char>>, tb: &Vec<(Vec<char>, Option<Ty>, Vec<Vec<char>>)>, tagged: bool, sc: &mut Vec<Vec<char>>, e: &SExpr) -> (r: Option<EExpr>)
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

fn rx_match_e(fs: &Vec<Vec<char>>, tb: &Vec<(Vec<char>, Option<Ty>, Vec<Vec<char>>)>, tagged: bool, sc: &mut Vec<Vec<char>>, e: &SExpr) -> (r: Option<EExpr>)
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

fn rx_let_e(fs: &Vec<Vec<char>>, tb: &Vec<(Vec<char>, Option<Ty>, Vec<Vec<char>>)>, tagged: bool, sc: &mut Vec<Vec<char>>, e: &SExpr) -> (r: Option<EExpr>)
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

fn rx_fold_e(fs: &Vec<Vec<char>>, tb: &Vec<(Vec<char>, Option<Ty>, Vec<Vec<char>>)>, tagged: bool, sc: &mut Vec<Vec<char>>, e: &SExpr) -> (r: Option<EExpr>)
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

pub fn rxs_e(fs: &Vec<Vec<char>>, tb: &Vec<(Vec<char>, Option<Ty>, Vec<Vec<char>>)>, tagged: bool, sc: &mut Vec<Vec<char>>, es: &Vec<SExpr>) -> (r: Option<Vec<EExpr>>)
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

fn rfunc_e(fs: &Vec<Vec<char>>, tb: &Vec<(Vec<char>, Option<Ty>, Vec<Vec<char>>)>, tagged: bool, d: &SDecl) -> (r: Option<EFunc>)
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
pub fn resolve_e(p: &Vec<SDecl>) -> (r: Option<(Vec<EFunc>, usize)>)
    ensures
        match r {
            Some((fs, g)) => resolve(vds(p@)) == Some((vfuncs(fs@), g as nat)) && g < fs@.len(),
            None => resolve(vds(p@)) is None,
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
            rfuncs(fsv, tv, false, ds, k as nat) == Some(vfuncs(out@)),
        decreases fidx@.len() - k,
    {
        let j = fidx[k];
        proof {
            assert(ds[k as int] == v[j as int]);
            assert(v[j as int] == vd(p@[j as int]));
        }
        match rfunc_e(&names, &tb, false, &p[j]) {
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
                    rfuncs_none(fsv, tv, false, ds, (k + 1) as nat, ds.len());
                    assert(rfuncs(fsv, tv, false, ds, ds.len()) is None);
                    resolve_none(vds(p@), tv);
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

/// 名前表が作れて、関数の解決が失敗すれば、resolve も失敗する（字段の名前の一意と entry の検査が
/// 通らなくても、結果は None なので、ここでは仮定しない）。
proof fn resolve_none(p: Seq<Sd>, tb: Seq<(Seq<char>, Option<Ty>, Seq<Seq<char>>)>)
    requires
        decl_table(p, p.len()) == Some(tb),
        rfuncs(names_of(fns_upto(p, p.len())), tb, false, fns_upto(p, p.len()), fns_upto(p, p.len()).len()) is None,
    ensures
        resolve(p) is None,
{
}

/// 途中の関数が解決できなければ全体も解決できない。
proof fn rfuncs_none(fs: Seq<Seq<char>>, tb: Seq<(Seq<char>, Option<Ty>, Seq<Seq<char>>)>, tagged: bool, ds: Seq<Sd>, n: nat, m: nat)
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
