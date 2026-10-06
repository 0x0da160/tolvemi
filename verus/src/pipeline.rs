//! 検査済み実行（§11.2 の 6、8、10 をつなぐ中心定理）。
//!
//! `run_checked` は、検証済み型検査器でプログラムが整形式であることと、入力値が entry の
//! 入力型を持つことを確かめてから、検証済み評価器で実行する。値を返したなら、それは
//! spec の評価が返す唯一の値で、entry の出力型を持つ。

use crate::check::*;
use crate::eval::*;
use crate::input::*;
use crate::input_exec::*;
use crate::ir::*;
use crate::json::*;
use crate::parse_proof::*;
use crate::proof::*;
use crate::resolve::*;
use crate::surface::*;
use crate::syntax::*;
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
        r matches Checked::Ran(res, _, _) ==> !is_fault(res),
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
        if is_fault(res) {
            // 整形式のプログラムに型の合う入力を与えると、ある燃料で Done になる（entry_total）。
            entry_total(pp, iv);
            let (n1, w1) = choose|n1: nat, w1: Val|
                #![trigger eval_entry(pp, n1, iv), val_type(w1, pp.funcs[pp.entry as int].ret)]
                eval_entry(pp, n1, iv) == Res::Done(w1) && val_type(w1, pp.funcs[pp.entry as int].ret);
            assert(eval_entry(pp, n1, iv) is Done);
        }
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
        r matches Output::Ran(res, _, _) ==> !is_fault(res),
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

// ------------------------------------------------------------------ 入力 JSON から実行まで（§11.2 の 9、10）

pub enum InputRun {
    /// 検証済み型検査器がプログラムを受理しなかった
    NotWellFormed,
    /// 入力 JSON が strict JSON・値 JSON の規則に合わないか、entry の入力型の値でない
    InputRejected,
    /// 実行した（正準 JSON の結果または打ち切り理由、step 数、割当 node 数）
    Ran(Result<String, Stop>, u64, u64),
}

/// entry の入力型。
pub open spec fn in_ty(p: EProg) -> Ty {
    view_prog(p).funcs[p.entry as int].params[0].1
}

/// 入力 JSON 文書を検証済みの復号器で読み、検証済み評価器で実行する。
/// - 復号の拒否と実行の失敗は別の結果に分かれ、復号を拒否するのは spec の `input_val` が None のときだけ。
/// - 実行が Fault（spec の行き詰まり）で終わることはない。
/// - 出力 o は、復号した入力に対する spec の唯一の結果 w の正準 JSON。
pub fn run_input_json(p: &EProg, text: &Vec<char>, d: usize, lim: Limits) -> (r: InputRun)
    requires
        limits_ok(lim),
        text@.len() < 0x1000_0000,
    ensures
        r is InputRejected ==> wf(view_prog(*p)) && input_val(text@, d as nat, in_ty(*p)) is None,
        r is Ran ==> wf(view_prog(*p)) && input_val(text@, d as nat, in_ty(*p)) is Some,
        r matches InputRun::Ran(res, _, _) ==> !is_fault(res),
        r matches InputRun::Ran(Ok(o), _, _) ==> exists|w: Val|
            #![trigger is_entry_result(view_prog(*p), input_val(text@, d as nat, in_ty(*p))->Some_0, w)]
            is_entry_result(view_prog(*p), input_val(text@, d as nat, in_ty(*p))->Some_0, w) && val_type(
                w,
                view_prog(*p).funcs[p.entry as int].ret,
            ) && o@ == enc(w),
{
    if !check_prog(p) {
        return InputRun::NotWellFormed;
    }
    let ghost pp = view_prog(*p);
    let f = &p.funcs[p.entry];
    proof {
        assert(pp.funcs[p.entry as int] == view_func(p.funcs@[p.entry as int]));
        assert(view_params(f.params@)[0].1 == f.params@[0].1);
    }
    let v = match decode_input_e(text, d, &f.params[0].1) {
        Some(v) => v,
        None => return InputRun::InputRejected,
    };
    let ghost iv = vv(v);
    match run_checked_json(p, v, lim) {
        Output::Ran(res, steps, alloc) => {
            proof {
                if res is Ok {
                    let o = res->Ok_0;
                    let w = choose|w: Val|
                        #![trigger is_entry_result(pp, iv, w)]
                        is_entry_result(pp, iv, w) && val_type(w, pp.funcs[p.entry as int].ret) && o@ == enc(w)
                            && dec(o@, 0, pp.funcs[p.entry as int].ret) == Some((w, o@.len() as int));
                    assert(is_entry_result(pp, input_val(text@, d as nat, in_ty(*p))->Some_0, w));
                }
            }
            InputRun::Ran(res, steps, alloc)
        },
        _ => InputRun::NotWellFormed,
    }
}

// ------------------------------------------------------------------ source から実行可能プログラムまで

/// source が表す名前解決済みプログラム（関数列と entry）。d、td は式と型の入れ子の深さ上限。
pub open spec fn source_prog(src: Seq<char>, d: nat, td: nat) -> Option<(Seq<Func>, nat)> {
    match parse(src, d, td) {
        Some(p) => resolve(p),
        None => None,
    }
}

pub enum Compiled {
    /// 字句・構文の規則に合わない
    ParseRejected,
    /// 名前解決・entry 検査に通らない
    NameRejected,
    /// 型検査またはランク証明書の検査に通らない
    NotWellFormed,
    Accepted(EProg),
}

/// 検証済みの lexer・parser・名前解決・型検査を通して実行可能プログラムを作る。
/// rank は呼出しグラフのランク（未検証の Tarjan が作る）で、ここで検査する。
pub fn compile_source(src: &Vec<char>, d: usize, td: usize, rank: Vec<usize>) -> (r: Compiled)
    requires
        src@.len() < 0x1000_0000,
    ensures
        r is ParseRejected <==> parse(src@, d as nat, td as nat) is None,
        r is NameRejected ==> parse(src@, d as nat, td as nat) is Some && source_prog(src@, d as nat, td as nat) is None,
        r matches Compiled::Accepted(p) ==> source_prog(src@, d as nat, td as nat) == Some(
            (view_prog(p).funcs, view_prog(p).entry),
        ) && wf(view_prog(p)),
{
    let sp = match parse_e(src, d, td) {
        Some(sp) => sp,
        None => return Compiled::ParseRejected,
    };
    let (funcs, entry) = match resolve_e(&sp) {
        Some(r) => r,
        None => return Compiled::NameRejected,
    };
    let p = EProg { funcs, rank, entry };
    proof {
        assert(view_prog(p).funcs =~= vfuncs(p.funcs@));
    }
    if !check_prog(&p) {
        return Compiled::NotWellFormed;
    }
    Compiled::Accepted(p)
}

/// 正準ソース。受理した source の整形結果は、parse すると同じ AST に戻り、
/// 字句解析すると元の source と同じ token 列になる（parse_proof::format_idempotent）。
pub fn canonical_source(src: &Vec<char>, d: usize, td: usize) -> (r: Option<Vec<char>>)
    requires
        src@.len() < 0x1000_0000,
    ensures
        r is None <==> parse(src@, d as nat, td as nat) is None,
        r matches Some(o) ==> o@ == fds(parse(src@, d as nat, td as nat)->Some_0, 0)
            && parse(o@, d as nat, td as nat) == parse(src@, d as nat, td as nat)
            && lex(o@) == lex(src@),
{
    match parse_e(src, d, td) {
        Some(sp) => {
            let o = format_e(&sp);
            proof {
                format_idempotent(src@, d as nat, td as nat);
            }
            Some(o)
        },
        None => None,
    }
}

} // verus!
