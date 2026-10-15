//! v1.3 入出力ランタイム（`tlvm exec`）。
//!
//! プログラムをコマンドとして実行する。entry の入力型で渡すものが決まる：
//!
//! | entry の入力型 | 渡すもの |
//! |---|---|
//! | `String` | 標準入力の全文 |
//! | `List<String>` | コマンドライン引数 |
//! | `Pair<List<String>, String>` | 引数と標準入力の全文 |
//! | `Dict<String, String>`・`Dict<String, Int>`（v1.13） | 標準入力の行（`key<TAB>value`）から作った辞書（`lines` モジュール） |
//!
//! 出力が `String` ならその文字列をそのまま、それ以外は plain JSON を一行で標準出力に書く。
//! v1.4：出力が `Result<String, String>` なら、`ok(s)` は s をそのまま標準出力に（終了コード 0）、
//! `err(s)` は s をそのまま標準エラーに書く（終了コード 1）。
//! テキストと値の変換（`tlvm_verified::io`）と実行（`pipeline::run_checked`）は検証済み部品が行う。
//! v1.13 の辞書は、行から作った普通の JSON を `run --plain` と同じ `api::decode_plain_input` で読み、
//! 検証済みの復号器（`decode_input_e`。`run_input_json` と同じ）で値にする。
//! ここにあるのは入力の形の選択と、結果を `ExecResult` に写す接着部分だけである（`trust-boundary.toml`）。

use crate::checker::TypedProgram;
use crate::diagnostics::Diagnostic;
use crate::evaluator::{input_bits_over, RunResult};
use crate::lines::{self, LinesResult};
use crate::plain::encode_plain;
use crate::profiles::{ExecutionProfile, HostPolicy};
use crate::syntax::Ty;
use crate::values::{release, verified_ty};
use std::rc::Rc;
use tlvm_verified::eval::{Limits, Resource, Stop};
use tlvm_verified::input_exec::decode_input_e;
use tlvm_verified::io::{args_value, text_codes, text_value};
use tlvm_verified::json::encode;
use tlvm_verified::pipeline::{run_checked, Checked};
use tlvm_verified::value::Value as EV;

/// exec の entry の入力型として受け付ける形（UnsupportedEntry の説明に使う）。
pub const ENTRY_SHAPES: &str =
    "String、List<String>、Pair<List<String>, String>、Dict<String, String>、Dict<String, Int>";

/// entry が受け取るもの。
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ExecInput {
    Stdin,
    Args,
    ArgsAndStdin,
    /// v1.13：標準入力の行（`key<TAB>value`）から作る `Dict<String, V>`（V は String か Int）
    Lines,
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
    } else if lines::accepts(&p.input_type) {
        Some(ExecInput::Lines)
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
    /// v1.13：標準入力の行の形が合わない（`InputBoundaryFailure` の envelope。理由は行番号つき）
    InputBoundaryFailure(String),
    /// v1.13：辞書の入力の復号が拒否した（鍵の重複、資源上限など）。span は標準入力の上の行の範囲
    InputInvalid(Vec<Diagnostic>),
}

/// 型検査済みのプログラムを、引数と標準入力の全文で実行する。深い再帰に備えて host-policy のスタック量を
/// 持つスレッドで評価する（`api::run` と同じ）。
pub fn exec(
    p: &TypedProgram,
    args: &[String],
    stdin: &str,
    prof: &ExecutionProfile,
    host: &HostPolicy,
) -> Result<ExecResult, String> {
    std::thread::scope(|s| {
        let h = std::thread::Builder::new()
            .stack_size(host.stack_bytes)
            .spawn_scoped(s, || exec_here(p, args, stdin, prof, host))
            .map_err(|e| e.to_string())?;
        match h.join() {
            Ok(r) => r,
            Err(_) => Ok(ExecResult::Stopped(RunResult::InternalFault(
                "evaluator-panic".into(),
            ))),
        }
    })
}

fn exec_here(
    p: &TypedProgram,
    args: &[String],
    stdin: &str,
    prof: &ExecutionProfile,
    host: &HostPolicy,
) -> Result<ExecResult, String> {
    let shape = exec_input(p).ok_or_else(|| {
        format!(
            "exec の entry の入力型は {} のどれか（この entry は {}）",
            ENTRY_SHAPES, p.input_type
        )
    })?;
    let Some(vp) = p.verified.as_ref() else {
        return Ok(ExecResult::Stopped(RunResult::InternalFault(
            "no-verified-program".into(),
        )));
    };
    let text = || text_value(&stdin.chars().collect());
    let argv = || args_value(&args.iter().map(|a| a.chars().collect()).collect());
    let input = match shape {
        ExecInput::Stdin => text(),
        ExecInput::Args => argv(),
        ExecInput::ArgsAndStdin => Rc::new(EV::Pair(argv(), text())),
        ExecInput::Lines => match lines_input(p, stdin, prof) {
            Ok(v) => v,
            Err(r) => return Ok(r),
        },
    };
    let lim = Limits {
        steps: prof.steps.min(u64::MAX - 1),
        integer_bits: prof.integer_bits,
        allocated_nodes: prof.allocated_nodes.min(u64::MAX - 1),
        max_depth: (host.max_eval_depth as u64).min(u64::MAX - 1),
        max_slots: (host.max_ref_slots as u64).min(u64::MAX - 1),
    };
    let r = run_checked(&vp.0, input.clone(), lim);
    release(input);
    let stopped = |r: RunResult| Ok(ExecResult::Stopped(r));
    match r {
        Checked::NotWellFormed => stopped(RunResult::InternalFault(
            "verified-check-rejected-program".into(),
        )),
        Checked::InputTypeMismatch => stopped(RunResult::InternalFault(
            "verified-input-type-mismatch".into(),
        )),
        Checked::Ran(Err(Stop::Exhausted(kind, observed, limit)), _, _) => {
            let kind = match kind {
                Resource::Steps => "Steps",
                Resource::IntegerBits => "IntegerBits",
                Resource::AllocatedNodes => "AllocatedNodes",
            };
            stopped(RunResult::ResourceExhausted {
                kind,
                observed,
                limit,
            })
        }
        Checked::Ran(Err(Stop::HostDepth), _, _) => {
            stopped(RunResult::HostAborted("eval-depth".into()))
        }
        Checked::Ran(Err(Stop::HostSlots), _, _) => {
            stopped(RunResult::HostAborted("ref-slots".into()))
        }
        Checked::Ran(Err(Stop::Fault), _, _) => stopped(RunResult::InternalFault("stuck".into())),
        Checked::Ran(Ok(w), _, _) => {
            let text = |v: &Rc<EV>| -> Option<String> {
                // 出力型 String の値の文字はスカラー値（検証済み：val_type）
                text_codes(v).map(|cs| {
                    cs.into_iter()
                        .map(|c| char::from_u32(c).unwrap_or('\u{FFFD}'))
                        .collect()
                })
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
                return stopped(RunResult::ResourceExhausted {
                    kind: "OutputBytes",
                    observed: prof.output_bytes + 1,
                    limit: prof.output_bytes,
                });
            }
            Ok(if failed {
                ExecResult::Failure(out)
            } else {
                ExecResult::Output(out)
            })
        }
    }
}

/// v1.13：標準入力の行から辞書の入力を作り、検証済みの復号器で値にする。`run --plain` と同じ経路を通る
/// （`lines::dict_from_lines` が普通の JSON にして `api::decode_plain_input` で読み、`run_input_json` と同じく
/// `decode_input_e` で値にする）。行の形の誤りと復号の拒否は、そのまま `ExecResult` で返す。
fn lines_input(
    p: &TypedProgram,
    stdin: &str,
    prof: &ExecutionProfile,
) -> Result<Rc<EV>, ExecResult> {
    let tv = match lines::dict_from_lines(&p.input_type, stdin) {
        LinesResult::Decoded(tv) => tv,
        LinesResult::BoundaryFailure(reason) => {
            return Err(ExecResult::InputBoundaryFailure(reason))
        }
        LinesResult::Invalid(ds) => return Err(ExecResult::InputInvalid(ds)),
    };
    // evaluator::run と同じ：入力の整数の bit 長が上限を超えるなら、実行せずに打ち切る
    if let Some(observed) = input_bits_over(&tv.value, prof.integer_bits) {
        return Err(ExecResult::Stopped(RunResult::ResourceExhausted {
            kind: "IntegerBits",
            observed,
            limit: prof.integer_bits,
        }));
    }
    if tv.text.len() >= 0x1000_0000 {
        return Err(ExecResult::Stopped(RunResult::InternalFault(
            "input-too-long-for-verified-decoder".into(),
        )));
    }
    let Some(vt) = verified_ty(&tv.ty) else {
        return Err(ExecResult::Stopped(RunResult::InternalFault(
            "no-verified-type".into(),
        )));
    };
    decode_input_e(&tv.text, tv.json_depth, &vt).ok_or_else(|| {
        ExecResult::Stopped(RunResult::InternalFault(
            "verified-decoder-rejected-input".into(),
        ))
    })
}
