//! 公開 API：compile / compile_ast / decode_input / run（設計書 §9.1）。

use crate::ast_codec::{self, Transport};
use crate::checker::{check_program, CheckOutcome, TypedProgram, VerifiedProgram, WorkCounter};
use crate::diagnostics::{finalize, suggest_repairs, Diagnostic};
use crate::plain::{canonical_profile, decode_plain, PlainDecode};
use crate::evaluator::{self, RunResult};
use crate::dict;
use crate::generics;
use crate::imports;
use std::collections::BTreeMap;
use crate::hof;
use crate::lexer::lex;
use crate::parser::{ParseOutcome, Parser};
use crate::profiles::*;
use crate::records;
use crate::sums;
use crate::syntax::{Program, Ty};
use crate::values::{self, DecodeResult, TypedValue};
use crate::formatter::format_program;
use std::sync::Arc;
use tlvm_verified::pipeline::{canonical_source, compile_source, Compiled};
use tlvm_verified::resolve::resolve_e;
use tlvm_verified::surface::parse_e;

#[derive(Debug)]
pub enum CompileResult {
    Accepted { program: TypedProgram, warnings: Vec<Diagnostic>, work: Option<WorkCounter> },
    Rejected { errors: Vec<Diagnostic>, warnings: Vec<Diagnostic>, work: Option<WorkCounter> },
}

impl CompileResult {
    pub fn errors(&self) -> &[Diagnostic] {
        match self {
            CompileResult::Accepted { .. } => &[],
            CompileResult::Rejected { errors, .. } => errors,
        }
    }
    pub fn warnings(&self) -> &[Diagnostic] {
        match self {
            CompileResult::Accepted { warnings, .. } | CompileResult::Rejected { warnings, .. } => warnings,
        }
    }
    pub fn work(&self) -> Option<WorkCounter> {
        match self {
            CompileResult::Accepted { work, .. } | CompileResult::Rejected { work, .. } => *work,
        }
    }
    pub fn program(&self) -> Option<&TypedProgram> {
        match self {
            CompileResult::Accepted { program, .. } => Some(program),
            _ => None,
        }
    }
}

#[derive(Debug)]
pub enum SourceCompile {
    SourceBoundaryFailure,
    Result(CompileResult),
}

#[derive(Debug)]
pub enum AstCompile {
    AstBoundaryFailure,
    AstInvalid(Vec<Diagnostic>),
    Result(CompileResult),
}

pub(crate) fn result(diags: Vec<Diagnostic>, outcome: Option<CheckOutcome>) -> CompileResult {
    let (errors, warnings) = finalize(diags);
    let work = outcome.as_ref().and_then(|o| o.work);
    match outcome.and_then(|o| o.typed) {
        Some(program) if errors.is_empty() => CompileResult::Accepted { program, warnings, work },
        _ => CompileResult::Rejected { errors, warnings, work },
    }
}

pub enum Parsed {
    Program(Program),
    Failed(SourceCompile),
}

/// source-boundary → lex → parse。
pub fn parse_source(source: &[u8], profile: &StaticProfile) -> Parsed {
    if source.len() > profile.source_bytes {
        let d = Diagnostic::error("source-boundary", "E-LIMIT-STATIC-SOURCE-BYTES", (0, 0))
            .exp(profile.source_bytes.to_string())
            .act(source.len().to_string());
        return Parsed::Failed(SourceCompile::Result(result(vec![d], None)));
    }
    if std::str::from_utf8(source).is_err() {
        return Parsed::Failed(SourceCompile::SourceBoundaryFailure);
    }
    let toks = match lex(source, profile) {
        Ok(t) => t,
        Err(d) => return Parsed::Failed(SourceCompile::Result(result(vec![d], None))),
    };
    match Parser::new(toks, profile).parse_program() {
        ParseOutcome::Ok(p) => Parsed::Program(p),
        ParseOutcome::Errors(d) | ParseOutcome::Cutoff(d) => Parsed::Failed(SourceCompile::Result(result(d, None))),
    }
}

/// v1.11：ファイル `path` を import ごと検査する（CLI 用）。import がなければ `compile` と同じ（診断に `file` は付かない）。
/// 返す対応表は読んだファイルの名前と中身（根が先頭）で、診断の `file` から表示用の source を引くのに使う。
/// 根のファイルが読めなければ Err。
pub fn compile_path(path: &str, profile: &StaticProfile) -> Result<(SourceCompile, Vec<(String, Vec<u8>)>), String> {
    let data = std::fs::read(path).map_err(|e| format!("{path}: {e}"))?;
    let rel = std::path::Path::new(path).file_name().map(|n| n.to_string_lossy().into_owned()).unwrap_or_default();
    Ok(imports::compile_root(path, &rel, &data, &mut imports::FsLoader::new(path), profile))
}

/// v1.11：名前と source の対応表 `files` から、`root` を根に import ごと検査する（ファイルシステムには触れない）。
/// key は `/` 区切りのパス（`.`・`..` を含まない）で、import のパスは import を書いたファイルのディレクトリから解決する
/// （根の key のディレクトリより上は指せない）。import がなければ `compile(files[root])` と同じ。
pub fn compile_files(root: &str, files: &BTreeMap<String, String>, profile: &StaticProfile) -> SourceCompile {
    let Some(src) = files.get(root) else {
        let mut d = Diagnostic::error("import", "E-IMPORT-NOT-FOUND", (0, 0)).act(format!("{root}: not in the map of sources"));
        d.file = Some(root.to_string());
        return SourceCompile::Result(result(vec![d], None));
    };
    let (dir, rel) = root.rsplit_once('/').unwrap_or(("", root));
    let mut loader = imports::MapLoader { root_dir: dir.to_string(), files };
    imports::compile_root(root, rel, src.as_bytes(), &mut loader, profile).0
}

pub fn compile(source: &[u8], profile: &StaticProfile) -> SourceCompile {
    match compile_unrepaired(source, profile) {
        SourceCompile::Result(r) => SourceCompile::Result(with_repairs(r, source)),
        f => f,
    }
}

/// source API の診断に修復ヒントを付ける（§10.1。AST API では付けない）。
fn with_repairs(r: CompileResult, source: &[u8]) -> CompileResult {
    match r {
        CompileResult::Rejected { mut errors, warnings, work } => {
            suggest_repairs(&mut errors, source);
            CompileResult::Rejected { errors, warnings, work }
        }
        accepted => accepted,
    }
}

fn compile_unrepaired(source: &[u8], profile: &StaticProfile) -> SourceCompile {
    match parse_source(source, profile) {
        Parsed::Failed(SourceCompile::Result(r)) => {
            // parse_source が SourceBoundaryFailure を返さなかったので UTF-8 として妥当
            let text = std::str::from_utf8(source).unwrap_or("");
            SourceCompile::Result(cross_check(text, r, profile))
        }
        Parsed::Failed(f) => f,
        // v1.11：source の文字列だけでは import を解決できない（ファイルからの検査は compile_path・compile_files）
        Parsed::Program(p) if !p.imports.is_empty() => SourceCompile::Result(result(
            p.imports
                .iter()
                .map(|i| Diagnostic::error("import", "E-IMPORT-UNSUPPORTED", i.span.t()).act(format!("import \"{}\"", i.path)))
                .collect(),
            None,
        )),
        Parsed::Program(p) if needs_glue(&p) => {
            // v1.1：レコードを展開し、検証済み部品には fst／snd に書き換えたプログラムの整形ソースを渡す。
            // v1.4：直和型と match も同じく展開し、ok／err・match_result などに書き換えたものを渡す。
            // v1.5：map などは型検査の後に fold などへ書き換える（v1.6 の loop も）
            match expand(&p) {
                Err(d) => SourceCompile::Result(result(d, None)),
                Ok(px) => {
                    // v1.10：総称の関数は型検査の後で単相化し、以降は単相化したプログラムを書き換える
                    let (o, pm) = generics::check(&px, source.len(), profile);
                    // v1.7：印 `rec` は検証済み parser の構文にないので外して整形し、印は別に渡す（cross_check）
                    // v1.9：辞書の操作は hof::lower が書き換え、最後に型の Dict<K, V> を List<Pair<K, V>> にする
                    let text = format_program(&dict::erase(&lower(&hof::lower(&pm, &o.hof))).unmarked());
                    let r = result(o.diagnostics.clone(), Some(o));
                    SourceCompile::Result(cross_check(&text, r, profile))
                }
            }
        }
        Parsed::Program(p) => {
            let o = check_program(&p, source.len(), profile);
            let r = result(o.diagnostics.clone(), Some(o));
            let text = without_rec_markers(std::str::from_utf8(source).unwrap_or(""), &p);
            SourceCompile::Result(cross_check(&text, r, profile))
        }
    }
}

/// レコード（v1.1）か直和型・match（v1.4）、型引数（v1.10）を含み、検査の前に展開が要るか。
pub fn needs_expansion(p: &Program) -> bool {
    sums::has_sums(p) || records::has_records(p) || generics::has_generics(p)
}

/// 検証済み部品に渡す前に書き換えが要るか（レコード・直和型・match の展開か、v1.5 の map など・v1.6 の loop・
/// v1.9 の辞書の書き換え）。こうしたプログラムは検証済み formatter の対象外で、`tlvm fmt` は診断用 formatter の出力を出す。
pub fn needs_glue(p: &Program) -> bool {
    needs_expansion(p) || hof::has_hof(p) || dict::has_dict(p)
}

/// 型引数、直和型、レコードの順に展開する（診断の phase は name）。結果は型検査器が検査できる形。
/// map などはそのまま残る（型検査の後で `hof::lower` が書き換える）。総称の関数も残る（型検査の後で
/// `generics::check` が単相化する）。
pub fn expand(p: &Program) -> Result<Program, Vec<crate::diagnostics::Diagnostic>> {
    let p = if generics::has_generics(p) { generics::resolve(p)? } else { p.clone() };
    let p = if sums::has_sums(&p) { sums::expand(&p)? } else { p };
    if records::has_records(&p) {
        records::expand(&p)
    } else {
        Ok(p)
    }
}

/// 展開したプログラムを、検証済み部品が読む形（match_result、fst／snd など）に書き換える。
pub fn lower(px: &Program) -> Program {
    records::lower(&sums::lower(px))
}

// ---------------------------------------------------------------- 検証済み部品による確認

/// v1.7：source から印 `rec`（`rec fn` の `rec`。parser が記録した span）を同じ長さの空白に置き換える。
/// 検証済み parser は `rec` を知らないので、印を外した source を読ませ、印の列は `compile_source` に別に渡す。
/// 変数名などの `rec` は印ではないのでそのまま残る。
pub fn without_rec_markers(source: &str, p: &Program) -> String {
    let mut b = source.as_bytes().to_vec();
    for f in p.functions().filter(|f| f.rec) {
        let (s, e) = f.rec_span.t();
        if e <= b.len() && &b[s..e] == crate::syntax::REC.as_bytes() {
            b[s..e].fill(b' ');
        }
    }
    // `rec` は ASCII なので UTF-8 のまま
    String::from_utf8(b).unwrap_or_default()
}

/// 検証済み parser に渡す式・型の入れ子の深さ上限。診断用 parser の上限（structural-limits）より
/// 大きく取り、診断用 parser が受理したものを深さの数え方の違いで拒否しないようにする。
fn depth_bounds(p: &StaticProfile) -> (usize, usize) {
    (p.expr_depth.saturating_mul(2).saturating_add(2), p.type_depth.saturating_mul(2).saturating_add(2))
}

/// 検証済み部品に渡せる長さ（tlvm_verified::surface::parse_e の前提）。
const VERIFIED_MAX_CHARS: usize = 0x1000_0000;

fn mismatch(why: &str) -> Diagnostic {
    Diagnostic::error("internal", "E-INTERNAL-VERIFIED-MISMATCH", (0, 0)).act(why)
}

/// 診断用の検査器（lexer・parser・checker）の判定を、検証済み部品で確かめる。
///
/// - 受理したなら、検証済みの lexer・parser・名前解決・型検査（compile_source）も受理し、
///   その結果の中間表現を実行に使う。受理しなければ E-INTERNAL-VERIFIED-MISMATCH で拒否する。
/// - 字句・構文・名前・entry の段階で拒否したなら（資源上限による打切りを除く）、
///   検証済み部品もその段階までに拒否することを確かめる（誤拒否の検出）。
fn cross_check(text: &str, r: CompileResult, profile: &StaticProfile) -> CompileResult {
    let chars: Vec<char> = text.chars().collect();
    if chars.len() >= VERIFIED_MAX_CHARS {
        return match r {
            CompileResult::Accepted { warnings, work, .. } => {
                CompileResult::Rejected { errors: vec![mismatch("source-too-long-for-verified-parser")], warnings, work }
            }
            rejected => rejected,
        };
    }
    let (d, td) = depth_bounds(profile);
    match r {
        CompileResult::Accepted { mut program, warnings, work } => {
            let rank: Vec<usize> =
                program.program.functions().map(|f| program.rank.get(&f.name).copied().unwrap_or(usize::MAX)).collect();
            // v1.7：関数ごとの印 `rec`（検証済みプログラムの関数と同じ宣言順）
            let rec: Vec<bool> = program.program.functions().map(|f| f.rec).collect();
            match compile_source(&chars, d, td, rank, rec) {
                Compiled::Accepted(p) => {
                    program.verified = Some(Arc::new(VerifiedProgram(p)));
                    CompileResult::Accepted { program, warnings, work }
                }
                Compiled::ParseRejected => {
                    CompileResult::Rejected { errors: vec![mismatch("verified-parser-rejected")], warnings, work }
                }
                Compiled::NameRejected => {
                    CompileResult::Rejected { errors: vec![mismatch("verified-resolver-rejected")], warnings, work }
                }
                Compiled::NotWellFormed => {
                    CompileResult::Rejected { errors: vec![mismatch("verified-typechecker-rejected")], warnings, work }
                }
            }
        }
        CompileResult::Rejected { mut errors, warnings, work } => {
            let cutoff = errors.iter().any(|e| e.is_cutoff() || e.phase == "diagnostic-limit");
            let syntax = errors.iter().any(|e| matches!(e.phase, "lex" | "parse"));
            let names = errors.iter().any(|e| matches!(e.phase, "name" | "entry"));
            if !cutoff && (syntax || names) && !hof_word_called(text, profile) {
                match parse_e(&chars, d, td) {
                    Some(sp) => {
                        if syntax {
                            errors.push(mismatch("verified-parser-accepted"));
                        } else if resolve_e(&sp).is_some() {
                            errors.push(mismatch("verified-resolver-accepted"));
                        }
                    }
                    None => {}
                }
            }
            CompileResult::Rejected { errors, warnings, work }
        }
    }
}

/// v1.5：map などの 6 語（v1.6 の `loop`、v1.9 の `dict` と `dict_get` なども）が呼び出し・宣言の名前の位置
/// （直後が `(` か `<`、直前が `fn`・`entry`）にあるか。検証済みの構文規則ではこれらは普通の名前なので、
/// `map(xs, f)` や `fn find(...)` を受理しうる。診断用 parser はそれらを拒否する（`E-PARSE-EXPECTED-LAMBDA`、
/// `E-PARSE-EXPECTED-IDENT` など）ので、その場合は誤拒否の確かめを省く。
fn hof_word_called(text: &str, profile: &StaticProfile) -> bool {
    let Ok(toks) = lex(text.as_bytes(), profile) else { return false };
    toks.iter().enumerate().any(|(i, t)| {
        let dict = crate::syntax::is_dict_word(&t.text);
        (crate::syntax::is_lambda_form(&t.text) || dict)
            && (toks.get(i + 1).is_some_and(|n| n.is_punct("(") || (dict && n.is_punct("<")))
                || (i > 0 && (toks[i - 1].is_kw("fn") || toks[i - 1].is_kw("entry"))))
    })
}

/// 正準ソース（検証済み formatter）。受理できない source なら None。
pub fn canonical(text: &str, profile: &StaticProfile) -> Option<String> {
    let chars: Vec<char> = text.chars().collect();
    if chars.len() >= VERIFIED_MAX_CHARS {
        return None;
    }
    let (d, td) = depth_bounds(profile);
    canonical_source(&chars, d, td).map(|o| o.into_iter().collect())
}

pub enum ParsedAst {
    Program(Program),
    Failed(AstCompile),
}

pub fn parse_ast(data: &[u8], profile: &StaticProfile, tp: &AstTransportProfile) -> ParsedAst {
    match ast_codec::transport(data, tp, profile) {
        Transport::BoundaryFailure => ParsedAst::Failed(AstCompile::AstBoundaryFailure),
        Transport::Invalid(d) => ParsedAst::Failed(AstCompile::AstInvalid(d)),
        Transport::Ok(root) => match ast_codec::build(&root, profile) {
            Ok(p) => ParsedAst::Program(p),
            Err(cutoff) => ParsedAst::Failed(AstCompile::Result(result(vec![cutoff], None))),
        },
    }
}

pub fn compile_ast(data: &[u8], profile: &StaticProfile, tp: &AstTransportProfile) -> AstCompile {
    match parse_ast(data, profile, tp) {
        ParsedAst::Failed(f) => f,
        ParsedAst::Program(p) => {
            // v1.10：型引数を解決し、総称の関数は型検査の後で単相化する
            let p = if generics::has_generics(&p) {
                match generics::resolve(&p) {
                    Ok(p) => p,
                    Err(d) => return AstCompile::Result(without_repairs(result(d, None))),
                }
            } else {
                p
            };
            let (o, p) = generics::check(&p, data.len(), profile);
            // AST は正準ソースに整形してから検証済み部品に通す（整形は診断用 formatter）。
            // v1.5：map など（v1.6 の loop も）は fold などに書き換えてから整形する
            // v1.7：印 `rec` は外して整形する（印は cross_check が別に渡す）
            // v1.9：辞書も同じく書き換え、型の Dict<K, V> を List<Pair<K, V>> にする
            let text = if hof::has_hof(&p) || dict::has_dict(&p) {
                format_program(&dict::erase(&hof::lower(&p, &o.hof)).unmarked())
            } else {
                format_program(&p.unmarked())
            };
            let r = result(o.diagnostics.clone(), Some(o));
            AstCompile::Result(without_repairs(cross_check(&text, r, profile)))
        }
    }
}

/// AST API は安全な JSON 部分木の置換を指定できないので repair を出さない（§10.1）。
fn without_repairs(r: CompileResult) -> CompileResult {
    let strip = |ds: Vec<Diagnostic>| ds.into_iter().map(|d| Diagnostic { repair: None, ..d }).collect::<Vec<_>>();
    match r {
        CompileResult::Rejected { errors, warnings, work } => {
            CompileResult::Rejected { errors: strip(errors), warnings: strip(warnings), work }
        }
        CompileResult::Accepted { program, warnings, work } => CompileResult::Accepted { program, warnings: strip(warnings), work },
    }
}

pub fn decode_input(t_in: &Ty, data: &[u8], profile: &InputProfile) -> DecodeResult {
    values::decode_input(t_in, data, profile)
}

/// 普通の JSON（`plain` モジュールの対応表）で入力を読む。値 JSON へ変換してから `decode_input` と同じ
/// 経路（診断付きの復号器と検証済みの復号器の突き合わせ）で復号する。診断の span は plain JSON の bytes 上。
pub fn decode_plain_input(t_in: &Ty, data: &[u8], profile: &InputProfile) -> DecodeResult {
    match decode_plain(t_in, data, profile) {
        PlainDecode::Canonical(text) => values::decode_input(t_in, text.as_bytes(), &canonical_profile(profile)),
        PlainDecode::Invalid(d) => DecodeResult::Invalid(d),
        PlainDecode::InputBoundaryFailure => DecodeResult::InputBoundaryFailure,
    }
}

/// 深い再帰に備えて host-policy のスタック量を持つスレッドで評価する。
pub fn run(program: &TypedProgram, input: &TypedValue, profile: &ExecutionProfile, host: &HostPolicy) -> Result<RunResult, String> {
    std::thread::scope(|s| {
        let h = std::thread::Builder::new()
            .stack_size(host.stack_bytes)
            .spawn_scoped(s, || evaluator::run(program, input, profile, host))
            .map_err(|e| e.to_string())?;
        match h.join() {
            Ok(r) => r,
            Err(_) => Ok(RunResult::InternalFault("evaluator-panic".into())),
        }
    })
}
