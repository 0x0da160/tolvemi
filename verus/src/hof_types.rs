//! HofTypes の写し（SH1、DECISION-38「一致だけ証明」）。
//!
//! `crates/tlvm/src/checker.rs` の `HofTypes`（node ごとの型の対。`hof::lower` と `dict::dict_op` が書換えの
//! 型の注釈に使う）は信頼する Rust のまま残す（checker は検証しない）。ここでは表に入る項目を spec に写し
//! （`hof_entry`）、checker がその形に返す型（`form_ty`）も写す。この写しが検証済みの型付け規則と一致すること
//! と、書換えが表を引く形に項目が無いことはないこと（全域性）は、この写しの上で別のモジュールで示す。
//!
//! 写しは checker.rs の `TypeChecker::hof`、`TypeChecker::loop_`、`TypeChecker::call`（引数の数の検査と、
//! dict_from・ほかの辞書の操作の腕）に対応する。ErrorType は None で表す。資源の上限による打ち切り
//! （`build` と `event` の Err）は検査全体を止めるので写さない。型は核の Ty で表す（型引数・名前の印は写さない。
//! 単相化の後の第二パスの表を書換えが使う）。写しと Rust の表が同じことは crates/tlvm/tests/hof_types.rs で
//! 確かめる（試験であって証明ではない）。

use crate::spec::*;
use vstd::prelude::*;

verus! {

/// syntax.rs の `HofOp`。
pub enum HofOp {
    Map,
    Filter,
    Any,
    All,
    Find,
    SortBy,
}

/// syntax.rs の `DICT_OPS` の九つ。
pub enum DictOp {
    Get,
    Put,
    Remove,
    Has,
    Size,
    Keys,
    Values,
    Entries,
    From,
}

/// 書換え（hof.rs の `Lower::expr`）が `HofTypes` を引く形：`ExprKind::Hof`、`ExprKind::Loop`、辞書の操作の
/// 組込みの呼出し。空の辞書 `dict<K, V>()` は表を引かない（型は node に書いてある。dict.rs の `lower_new`）。
pub enum Form {
    Hof(HofOp),
    Loop,
    Dict(DictOp),
}

/// 被演算子の数：hof は列と本体、loop は init・max・本体、辞書の操作は syntax.rs の `builtin_arity`。
/// 辞書の操作の引数の数が違えば checker は E-ARITY-BUILTIN で ErrorType を返す。
pub open spec fn operands(f: Form) -> nat {
    match f {
        Form::Hof(_) => 2,
        Form::Loop => 3,
        Form::Dict(op) => match op {
            DictOp::Put => 3,
            DictOp::Get | DictOp::Remove | DictOp::Has => 2,
            _ => 1,
        },
    }
}

/// checker が束縛に与える型：hof は列の要素の型（列が List でなければ ErrorType）、loop は init の型。
pub open spec fn binder_ty(f: Form, t0: Option<Ty>) -> Option<Ty> {
    match f {
        Form::Hof(_) => match t0 {
            Some(Ty::List(a)) => Some(*a),
            _ => None,
        },
        Form::Loop => t0,
        Form::Dict(_) => None,
    }
}

/// hof の本体に求める型（checker.rs の `want`）：map は無し、sort_by は Int、ほかは Bool。
pub open spec fn hof_want(op: HofOp) -> Option<Ty> {
    match op {
        HofOp::Map => None,
        HofOp::SortBy => Some(Ty::Int),
        _ => Some(Ty::Bool),
    }
}

/// 辞書の操作（dict_from 以外）の鍵と値の引数：第 2 引数は鍵の型 k、第 3 引数（dict_put）は値の型 v。
pub open spec fn dict_args_ok(ts: Seq<Option<Ty>>, k: Ty, v: Ty) -> bool {
    &&& (ts.len() >= 2 ==> ts[1] == Some(k))
    &&& (ts.len() == 3 ==> ts[2] == Some(v))
}

/// 辞書の操作の結果の型（checker.rs の `call` の辞書の腕）。dict_put・dict_remove は引数の辞書の型。
pub open spec fn dict_result(op: DictOp, k: Ty, v: Ty) -> Ty {
    match op {
        DictOp::Get => Ty::Option(Box::new(v)),
        DictOp::Put | DictOp::Remove | DictOp::From => Ty::Dict(Box::new(k), Box::new(v)),
        DictOp::Has => Ty::Bool,
        DictOp::Size => Ty::Int,
        DictOp::Keys => Ty::List(Box::new(k)),
        DictOp::Values => Ty::List(Box::new(v)),
        DictOp::Entries => Ty::List(Box::new(Ty::Pair(Box::new(k), Box::new(v)))),
    }
}

/// checker が形に返す型（None は ErrorType）。ts は被演算子の型（hof：列、本体。loop：init、max、本体。
/// 辞書の操作：引数）。
pub open spec fn form_ty(f: Form, ts: Seq<Option<Ty>>) -> Option<Ty> {
    if ts.len() != operands(f) {
        None
    } else {
        match f {
            Form::Hof(op) => match (ts[0], ts[1]) {
                (Some(Ty::List(a)), Some(bt)) => if hof_want(op) is None || hof_want(op) == Some(bt) {
                    Some(
                        match op {
                            HofOp::Map => Ty::List(Box::new(bt)),
                            HofOp::Filter | HofOp::SortBy => Ty::List(a),
                            HofOp::Any | HofOp::All => Ty::Bool,
                            HofOp::Find => Ty::Option(a),
                        },
                    )
                } else {
                    None
                },
                _ => None,
            },
            Form::Loop => match (ts[0], ts[1], ts[2]) {
                (Some(st), Some(mt), Some(bt)) => if mt == Ty::Int && bt == Ty::Option(Box::new(st)) {
                    Some(bt)
                } else {
                    None
                },
                _ => None,
            },
            Form::Dict(op) => if op is From {
                match ts[0] {
                    Some(Ty::List(e)) => match *e {
                        Ty::Pair(k, v) => Some(Ty::Dict(k, v)),
                        _ => None,
                    },
                    _ => None,
                }
            } else {
                match ts[0] {
                    Some(Ty::Dict(k, v)) => if dict_args_ok(ts, *k, *v) {
                        Some(dict_result(op, *k, *v))
                    } else {
                        None
                    },
                    _ => None,
                }
            },
        }
    }
}

/// checker が `HofTypes` に入れる項目（None は入れない）。hof は（要素の型、本体の型）、loop は（状態の型 S、
/// 本体の型）、辞書の操作は（鍵の型、値の型）。
pub open spec fn hof_entry(f: Form, ts: Seq<Option<Ty>>) -> Option<(Ty, Ty)> {
    if ts.len() != operands(f) {
        None
    } else {
        match f {
            Form::Hof(op) => match (ts[0], ts[1]) {
                (Some(Ty::List(a)), Some(bt)) => if hof_want(op) is None || hof_want(op) == Some(bt) {
                    Some((*a, bt))
                } else {
                    None
                },
                _ => None,
            },
            Form::Loop => match (ts[0], ts[1], ts[2]) {
                (Some(st), Some(mt), Some(bt)) => if mt == Ty::Int && bt == Ty::Option(Box::new(st)) {
                    Some((st, bt))
                } else {
                    None
                },
                _ => None,
            },
            Form::Dict(op) => if op is From {
                match ts[0] {
                    Some(Ty::List(e)) => match *e {
                        Ty::Pair(k, v) => Some((*k, *v)),
                        _ => None,
                    },
                    _ => None,
                }
            } else {
                match ts[0] {
                    Some(Ty::Dict(k, v)) => if dict_args_ok(ts, *k, *v) {
                        Some((*k, *v))
                    } else {
                        None
                    },
                    _ => None,
                }
            },
        }
    }
}

} // verus!
