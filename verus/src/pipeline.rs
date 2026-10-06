//! 検査済み実行（§11.2 の 6、8、10 をつなぐ中心定理）。
//!
//! `run_checked` は、検証済み型検査器でプログラムが整形式であることと、入力値が entry の
//! 入力型を持つことを確かめてから、検証済み評価器で実行する。値を返したなら、それは
//! spec の評価が返す唯一の値で、entry の出力型を持つ。

use crate::check::*;
use crate::eval::*;
use crate::ir::*;
use crate::json::*;
use crate::proof::*;
use crate::spec::*;
use crate::value::*;
use std::rc::Rc;
use vstd::prelude::*;

verus! {

pub enum Checked {
    /// 検証済み型検査器がプログラムを受理しなかった
    NotWellFormed,
    /// 入力値が entry の入力型を持たなかった
    InputTypeMismatch,
    /// 実行した（結果、step 数、割当 node 数）
    Ran(Result<Rc<Value>, Stop>, u64, u64),
}

/// entry の結果として spec が定める唯一の値。
pub open spec fn is_entry_result(p: Prog, v: Val, w: Val) -> bool {
    &&& exists|n: nat| #[trigger] eval_entry(p, n, v) == Res::Done(w)
    &&& forall|n: nat| #[trigger] eval_entry(p, n, v) is Done ==> eval_entry(p, n, v) == Res::Done(w)
}

pub fn run_checked(p: &EProg, input: Rc<Value>, lim: Limits) -> (r: Checked)
    requires
        limits_ok(lim),
    ensures
        r is Ran ==> wf(view_prog(*p)),
        r is Ran ==> val_type(view_val(*input), view_prog(*p).funcs[p.entry as int].params[0].1),
        r matches Checked::Ran(Ok(w), _, _) ==> is_entry_result(view_prog(*p), view_val(*input), view_val(*w))
            && val_type(view_val(*w), view_prog(*p).funcs[p.entry as int].ret),
{
    if !check_prog(p) {
        return Checked::NotWellFormed;
    }
    let ghost pp = view_prog(*p);
    let ghost iv = vv(input);
    let f = &p.funcs[p.entry];
    proof {
        assert(pp.funcs[p.entry as int] == view_func(p.funcs@[p.entry as int]));
        assert(view_params(f.params@)[0].1 == f.params@[0].1);
    }
    if !has_type(&input, &f.params[0].1) {
        return Checked::InputTypeMismatch;
    }
    let (res, steps, alloc) = run(p, input, lim);
    proof {
        if res is Ok {
            let w = vv(res->Ok_0);
            let n0 = choose|n: nat| #[trigger] eval_entry(pp, n, iv) == Res::Done(w);
            entry_total(pp, iv);
            let (n1, w1) = choose|n1: nat, w1: Val|
                #![trigger eval_entry(pp, n1, iv), val_type(w1, pp.funcs[pp.entry as int].ret)]
                eval_entry(pp, n1, iv) == Res::Done(w1) && val_type(w1, pp.funcs[pp.entry as int].ret);
            entry_deterministic(pp, n0, n1, iv);
            assert forall|n: nat| #[trigger] eval_entry(pp, n, iv) is Done implies eval_entry(pp, n, iv) == Res::Done(w) by {
                entry_deterministic(pp, n0, n, iv);
            }
        }
    }
    Checked::Ran(res, steps, alloc)
}

pub enum Output {
    NotWellFormed,
    InputTypeMismatch,
    /// 実行した（正準 JSON の結果または打ち切り理由、step 数、割当 node 数）
    Ran(Result<String, Stop>, u64, u64),
}

/// 検査済み実行の結果を正準 JSON で返す。出力 o は spec の唯一の結果 w の `enc(w)` で、
/// 出力型に沿って復号すると w に戻る。
pub fn run_checked_json(p: &EProg, input: Rc<Value>, lim: Limits) -> (r: Output)
    requires
        limits_ok(lim),
    ensures
        r is Ran ==> wf(view_prog(*p)),
        r matches Output::Ran(Ok(o), _, _) ==> exists|w: Val|
            #![trigger is_entry_result(view_prog(*p), view_val(*input), w)]
            is_entry_result(view_prog(*p), view_val(*input), w) && val_type(
                w,
                view_prog(*p).funcs[p.entry as int].ret,
            ) && o@ == enc(w) && dec(o@, 0, view_prog(*p).funcs[p.entry as int].ret) == Some((w, o@.len() as int)),
{
    let ghost iv = vv(input);
    match run_checked(p, input, lim) {
        Checked::NotWellFormed => Output::NotWellFormed,
        Checked::InputTypeMismatch => Output::InputTypeMismatch,
        Checked::Ran(Err(s), steps, alloc) => Output::Ran(Err(s), steps, alloc),
        Checked::Ran(Ok(w), steps, alloc) => {
            let mut o = String::new();
            encode(&w, &mut o);
            proof {
                let pp = view_prog(*p);
                let wv = vv(w);
                assert(o@ =~= enc(wv));
                output_roundtrip(wv, pp.funcs[p.entry as int].ret);
                assert(is_entry_result(pp, iv, wv));
            }
            Output::Ran(Ok(o), steps, alloc)
        },
    }
}

} // verus!
