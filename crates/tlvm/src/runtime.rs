//! v1.3 入出力ランタイム（`tlvm exec`）。
//!
//! プログラムをコマンドとして実行する。entry の入力型で渡すものが決まる：
//!
//! | entry の入力型 | 渡すもの |
//! |---|---|
//! | `String` | 標準入力の全文 |
//! | `List<String>` | コマンドライン引数 |
//! | `Pair<List<String>, String>` | 引数と標準入力の全文 |
//!
//! 出力が `String` ならその文字列をそのまま、それ以外は plain JSON を一行で標準出力に書く。
//! v1.4：出力が `Result<String, String>` なら、`ok(s)` は s をそのまま標準出力に（終了コード 0）、
//! `err(s)` は s をそのまま標準エラーに書く（終了コード 1）。
//! テキストと値の変換（`tlvm_verified::io`）と実行（`pipeline::run_checked`）は検証済み部品が行う。
//! ここにあるのは入力の形の選択と、結果を `ExecResult` に写す接着部分だけである（`trust-boundary.toml`）。

use crate::checker::TypedProgram;
use crate::evaluator::RunResult;
use crate::plain::encode_plain;
use crate::profiles::{ExecutionProfile, HostPolicy};
use crate::syntax::Ty;
use crate::values::release;
use std::rc::Rc;
use tlvm_verified::eval::{Limits, Resource, Stop};
use tlvm_verified::io::{args_value, text_codes, text_value};
use tlvm_verified::json::encode;
use tlvm_verified::pipeline::{run_checked, Checked};
use tlvm_verified::value::Value as EV;

/// entry が受け取るもの。
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ExecInput {
    Stdin,
    Args,
    ArgsAndStdin,
}

pub fn exec_input(p: &TypedProgram) -> Option<ExecInput> {
    let s = Ty::string();
    let ls = Ty::list(s.clone());
    if p.input_type == s {
        Some(ExecInput::Stdin)
    } else if p.input_type == ls {
        Some(ExecInput::Args)
    } else if p.input_type == Ty::pair(ls, s) {
        Some(ExecInput::ArgsAndStdin)
    } else {
        None
    }
}

#[derive(Debug, PartialEq, Eq)]
pub enum ExecResult {
    /// 標準出力に書く内容（String の出力はそのまま、それ以外は plain JSON と改行）
    Output(String),
    /// v1.4：出力型 `Result<String, String>` の `err(s)`。s を標準エラーに書き、終了コード 1 で終わる
    Failure(String),
    /// 実行の打ち切りなど（`run` と同じ envelope）
    Stopped(RunResult),
}

/// 型検査済みのプログラムを、引数と標準入力の全文で実行する。深い再帰に備えて host-policy のスタック量を
/// 持つスレッドで評価する（`api::run` と同じ）。
pub fn exec(p: &TypedProgram, args: &[String], stdin: &str, prof: &ExecutionProfile, host: &HostPolicy) -> Result<ExecResult, String> {
    std::thread::scope(|s| {
        let h = std::thread::Builder::new()
            .stack_size(host.stack_bytes)
            .spawn_scoped(s, || exec_here(p, args, stdin, prof, host))
            .map_err(|e| e.to_string())?;
        match h.join() {
            Ok(r) => r,
            Err(_) => Ok(ExecResult::Stopped(RunResult::InternalFault("evaluator-panic".into()))),
        }
    })
}

fn exec_here(p: &TypedProgram, args: &[String], stdin: &str, prof: &ExecutionProfile, host: &HostPolicy) -> Result<ExecResult, String> {
    let shape = exec_input(p).ok_or_else(|| format!("exec の entry の入力型は String、List<String>、Pair<List<String>, String> のどれか（この entry は {}）", p.input_type))?;
    let Some(vp) = p.verified.as_ref() else {
        return Ok(ExecResult::Stopped(RunResult::InternalFault("no-verified-program".into())));
    };
    let text = || text_value(&stdin.chars().collect());
    let argv = || args_value(&args.iter().map(|a| a.chars().collect()).collect());
    let input = match shape {
        ExecInput::Stdin => text(),
        ExecInput::Args => argv(),
        ExecInput::ArgsAndStdin => Rc::new(EV::Pair(argv(), text())),
    };
    let lim = Limits {
        steps: prof.steps.min(u64::MAX - 1),
        integer_bits: prof.integer_bits,
        allocated_nodes: prof.allocated_nodes.min(u64::MAX - 1),
        max_depth: (host.max_eval_depth as u64).min(u64::MAX - 1),
    };
    let r = run_checked(&vp.0, input.clone(), lim);
    release(input);
    let stopped = |r: RunResult| Ok(ExecResult::Stopped(r));
    match r {
        Checked::NotWellFormed => stopped(RunResult::InternalFault("verified-check-rejected-program".into())),
        Checked::InputTypeMismatch => stopped(RunResult::InternalFault("verified-input-type-mismatch".into())),
        Checked::Ran(Err(Stop::Exhausted(kind, observed, limit)), _, _) => {
            let kind = match kind {
                Resource::Steps => "Steps",
                Resource::IntegerBits => "IntegerBits",
                Resource::AllocatedNodes => "AllocatedNodes",
            };
            stopped(RunResult::ResourceExhausted { kind, observed, limit })
        }
        Checked::Ran(Err(Stop::HostDepth), _, _) => stopped(RunResult::HostAborted("eval-depth".into())),
        Checked::Ran(Err(Stop::Fault), _, _) => stopped(RunResult::InternalFault("stuck".into())),
        Checked::Ran(Ok(w), _, _) => {
            let text = |v: &Rc<EV>| -> Option<String> {
                // 出力型 String の値の文字はスカラー値（検証済み：val_type）
                text_codes(v).map(|cs| cs.into_iter().map(|c| char::from_u32(c).unwrap_or('\u{FFFD}')).collect())
            };
            let mut failed = false;
            let out = if p.output_type == Ty::string() {
                match text(&w) {
                    Some(s) => s,
                    None => {
                        release(w);
                        return stopped(RunResult::InternalFault("output-not-text".into()));
                    }
                }
            } else if p.output_type == Ty::result(Ty::string(), Ty::string()) {
                let inner = match &*w {
                    EV::Ok(x) => Some(text(x)),
                    EV::Err(x) => {
                        failed = true;
                        Some(text(x))
                    }
                    _ => None,
                };
                match inner.flatten() {
                    Some(s) => s,
                    None => {
                        release(w);
                        return stopped(RunResult::InternalFault("output-not-text".into()));
                    }
                }
            } else {
                let mut o = String::new();
                encode(&w, &mut o);
                encode_plain(&p.output_type, &o)? + "\n"
            };
            release(w);
            if out.len() as u64 > prof.output_bytes {
                return stopped(RunResult::ResourceExhausted { kind: "OutputBytes", observed: prof.output_bytes + 1, limit: prof.output_bytes });
            }
            Ok(if failed { ExecResult::Failure(out) } else { ExecResult::Output(out) })
        }
    }
}
