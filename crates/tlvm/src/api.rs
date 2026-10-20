//! 公開 API：compile / compile_ast / decode_input / run（設計書 §9.1）。

use crate::ast_codec::{self, Transport};
use crate::checker::{check_program, CheckOutcome, TypedProgram, VerifiedProgram, WorkCounter};
use crate::diagnostics::{finalize, suggest_repairs, Diagnostic};
use crate::dict;
use crate::evaluator::{self, RunResult};
use crate::formatter::format_program;
use crate::generics;
use crate::hof;
use crate::imports;
use crate::lexer::lex;
use crate::parser::{ParseOutcome, Parser};
use crate::plain::{canonical_profile, decode_plain, PlainDecode};
use crate::profiles::*;
use crate::records;
use crate::recursive;
use crate::sums;
use crate::syntax::{Program, Ty};
use crate::values::{self, DecodeResult, TypedValue};
use std::collections::BTreeMap;
use std::sync::Arc;
use tlvm_verified::pipeline::{canonical_source, compile_source, Compiled};
use tlvm_verified::resolve::resolve_e;
use tlvm_verified::surface::parse_e;

#[derive(Debug)]
pub enum CompileResult {
    Accepted {
        program: TypedProgram,
        warnings: Vec<Diagnostic>,
        work: Option<WorkCounter>,
    },
    Rejected {
        errors: Vec<Diagnostic>,
        warnings: Vec<Diagnostic>,
        work: Option<WorkCounter>,
    },
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
            CompileResult::Accepted { warnings, .. } | CompileResult::Rejected { warnings, .. } => {
                warnings
            }
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
        Some(program) if errors.is_empty() => CompileResult::Accepted {
            program,
            warnings,
            work,
        },
        _ => CompileResult::Rejected {
            errors,
            warnings,
            work,
        },
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
        ParseOutcome::Errors(d) | ParseOutcome::Cutoff(d) => {
            Parsed::Failed(SourceCompile::Result(result(d, None)))
        }
    }
}

/// v1.11：ファイル `path` を import ごと検査する（CLI 用）。import がなければ `compile` と同じ（診断に `file` は付かない）。
/// 返す対応表は読んだファイルの名前と中身（根が先頭）で、診断の `file` から表示用の source を引くのに使う。
/// 根のファイルが読めなければ Err。
pub fn compile_path(
    path: &str,
    profile: &StaticProfile,
) -> Result<(SourceCompile, Vec<(String, Vec<u8>)>), String> {
    let data = std::fs::read(path).map_err(|e| format!("{path}: {e}"))?;
    let rel = std::path::Path::new(path)
        .file_name()
        .map(|n| n.to_string_lossy().into_owned())
        .unwrap_or_default();
    Ok(imports::compile_root(
        path,
        &rel,
        &data,
        &mut imports::FsLoader::new(path),
        profile,
    ))
}

/// v1.11：名前と source の対応表 `files` から、`root` を根に import ごと検査する（ファイルシステムには触れない）。
/// key は `/` 区切りのパス（`.`・`..` を含まない）で、import のパスは import を書いたファイルのディレクトリから解決する
/// （根の key のディレクトリより上は指せない）。import がなければ `compile(files[root])` と同じ。
pub fn compile_files(
    root: &str,
    files: &BTreeMap<String, String>,
    profile: &StaticProfile,
) -> SourceCompile {
    let Some(src) = files.get(root) else {
        let mut d = Diagnostic::error("import", "E-IMPORT-NOT-FOUND", (0, 0))
            .act(format!("{root}: not in the map of sources"));
        d.file = Some(root.to_string());
        return SourceCompile::Result(result(vec![d], None));
    };
    let (dir, rel) = root.rsplit_once('/').unwrap_or(("", root));
    let mut loader = imports::MapLoader {
        root_dir: dir.to_string(),
        files,
    };
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
        CompileResult::Rejected {
            mut errors,
            warnings,
            work,
        } => {
            suggest_repairs(&mut errors, source);
            CompileResult::Rejected {
                errors,
                warnings,
                work,
            }
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
                .map(|i| {
                    Diagnostic::error("import", "E-IMPORT-UNSUPPORTED", i.span.t())
                        .act(format!("import \"{}\"", i.path))
                })
                .collect(),
            None,
        )),
        Parsed::Program(p) if needs_glue(&p) => {
            // v1.1：レコードを展開し、検証済み部品には fst／snd に書き換えたプログラムの整形ソースを渡す。
            // v1.4：直和型と match も同じく展開し、ok／err・match_result などに書き換えたものを渡す。
            // v1.5：map などは型検査の後に fold などへ書き換える（v1.6 の loop も）
            // v1.14・v1.15：宣言した型のあるプログラムは、印つきの写しを先に検査してから印なしの写しを検査する
            if declares_types(&p) {
                SourceCompile::Result(compile_nominal(&p, source, profile))
            } else {
                SourceCompile::Result(compile_expanded(&p, source, profile, false))
            }
        }
        Parsed::Program(p) => {
            let o = check_program(&p, source.len(), profile);
            let r = result(o.diagnostics.clone(), Some(o));
            let text = without_rec_markers(std::str::from_utf8(source).unwrap_or(""), &p);
            // 書換えのないプログラムも、検証済み部品へ渡す文字列の大きさを検査する（オーナーの決定 2026-10-19 23:38）
            let r = check_rewritten_size(&text, r, profile);
            SourceCompile::Result(cross_check(&text, r, profile))
        }
    }
}

/// 展開から検証済み部品の検査までの一通り。`tagged` は名義の型の印つきの写し（v1.15）。
fn compile_expanded(
    p: &Program,
    source: &[u8],
    profile: &StaticProfile,
    tagged: bool,
) -> CompileResult {
    match expand_with(p, tagged) {
        Err(d) => expansion_rejected(source, p, d, profile),
        Ok(px) => {
            // v1.10：総称の関数は型検査の後で単相化し、以降は単相化したプログラムを書き換える
            let (o, pm) = generics::check(&px, source.len(), profile);
            // v1.7：印 `rec` は検証済み parser の構文にないので外して整形し、印は別に渡す（cross_check）
            // v1.9：辞書の操作は hof::lower が書き換え、最後に型の Dict<K, V> を List<Pair<K, V>> にする
            let mut glued = hof::lower(&pm, &o.hof);
            lower_in_place(&mut glued);
            dict::erase_in_place(&mut glued);
            glued.unmark();
            let text = format_program(&glued);
            let at = hof::deepest_loop_nest(&pm).map_or((0, 0), |(_, s)| s);
            let r = check_rewritten_size(&text, result(o.diagnostics.clone(), Some(o)), profile);
            cross_check_at(&text, r, profile, at)
        }
    }
}

/// v1.15：宣言した型（レコード型・直和型・再帰する型）を含むプログラムは、印つきの写し（宣言ごとに違う印を値の型に
/// 付けた同じプログラム）を先に検査する。型の名前による区別は、ここで検証済みの部品が判定する。受理されたら、印なし
/// の写しを検査して実行する。印つきの再帰する型の文面は、名前に直す（レコード型と直和型は型の名前で表示される）。
fn compile_nominal(p: &Program, source: &[u8], profile: &StaticProfile) -> CompileResult {
    match compile_expanded(p, source, profile, true) {
        CompileResult::Rejected {
            errors,
            warnings,
            work,
        } => {
            let names = recursive::tagged_names(p);
            CompileResult::Rejected {
                errors: recursive::show_names(errors, &names),
                warnings,
                work,
            }
        }
        CompileResult::Accepted { .. } => compile_expanded(p, source, profile, false),
    }
}

/// 型の宣言（レコード型・直和型。再帰する型を含む）を含むか。含めば名義の型の印（v1.15）が要る。
fn declares_types(p: &Program) -> bool {
    p.declarations.iter().any(|d| {
        matches!(
            d,
            crate::syntax::Decl::Type(_) | crate::syntax::Decl::Sum(_)
        )
    })
}

/// レコード（v1.1）か直和型・match（v1.4）、型引数（v1.10）を含み、検査の前に展開が要るか。
pub fn needs_expansion(p: &Program) -> bool {
    sums::has_sums(p)
        || records::has_records(p)
        || generics::has_generics(p)
        || recursive::has_recursive(p)
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
    expand_with(p, false)
}

/// `tagged` は名義の型の印つきの写し（v1.15。`compile_nominal` が使う）。
fn expand_with(p: &Program, tagged: bool) -> Result<Program, Vec<crate::diagnostics::Diagnostic>> {
    let p = if generics::has_generics(p) {
        generics::resolve(p)?
    } else {
        p.clone()
    };
    // v1.15：宣言の番号（名義の型の印）は展開の前に一度だけ決め、どの展開にも同じ番号を渡す
    let tags = tagged.then(|| crate::nominal::Tags::of(&p));
    // v1.14：再帰する直和型は List<Int>（印つきの写しでは印の付いた型）に書き換える（再帰しない直和型の展開より前）
    let p = if recursive::has_recursive(&p) {
        recursive::expand(&p, tags.as_ref())?
    } else {
        p
    };
    let p = if sums::has_sums(&p) {
        sums::expand(&p, tags.as_ref())?
    } else {
        p
    };
    if records::has_records(&p) {
        records::expand(&p, tags.as_ref())
    } else {
        Ok(p)
    }
}

/// 展開したプログラムを、検証済み部品が読む形（match_result、fst／snd など）に書き換える。
pub fn lower(px: &Program) -> Program {
    let mut p = px.clone();
    lower_in_place(&mut p);
    p
}

/// `lower` と同じ。書き換えるところだけを、その場で書き換える（複製しない。整形の前の一通りに使う）。
pub fn lower_in_place(p: &mut Program) {
    sums::lower_in_place(p);
    records::lower_in_place(p);
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

/// 検証済み parser に渡す式・型の入れ子の深さ上限。式の上限は §18.1 の E そのもの（検証済み parser の d と診断用
/// parser の式の深さは同じ単位で、書換えの後の式の深さもこの上限で検査する）。型の上限は 2T + 2 のまま（型の深さの
/// 超過は診断用 parser が先に拒否するので、報告値には影響しない）。
fn depth_bounds(p: &StaticProfile) -> (usize, usize) {
    (
        p.expr_depth,
        p.type_depth.saturating_mul(2).saturating_add(2),
    )
}

/// 検証済み部品に渡せる長さ（tlvm_verified::surface::parse_e の前提）。
const VERIFIED_MAX_CHARS: usize = 0x1000_0000;

fn mismatch(why: &str) -> Diagnostic {
    Diagnostic::error("internal", "E-INTERNAL-VERIFIED-MISMATCH", (0, 0)).act(why)
}

/// 書換え後のプログラムの大きさの上限（§18.1）。型検査を通ったプログラムの、検証済み部品へ渡す文字列の bytes が
/// 上限を超えれば拒否する。検証済み部品に渡す前に検査するので、上限を超える文字列は検証済み部品の検査に入らない。
/// 型検査で拒否されたプログラムは書換えが途中までなので、大きさを測らない。書換えのないプログラム（source の経路）も、
/// 同じく検査する（オーナーの決定 2026-10-19 23:38）。
fn check_rewritten_size(text: &str, r: CompileResult, profile: &StaticProfile) -> CompileResult {
    match r {
        CompileResult::Accepted { warnings, work, .. } if text.len() > profile.rewritten_bytes => {
            CompileResult::Rejected {
                errors: vec![Diagnostic::error(
                    "semantic-limits",
                    "E-LIMIT-STATIC-REWRITTEN-BYTES",
                    (0, 0),
                )
                .exp(profile.rewritten_bytes.to_string())
                .act(text.len().to_string())],
                warnings,
                work,
            }
        }
        r => r,
    }
}

/// 診断用の検査器（lexer・parser・checker）の判定を、検証済み部品で確かめる。
///
/// - 受理したなら、検証済みの lexer・parser・名前解決・型検査（compile_source）も受理し、
///   その結果の中間表現を実行に使う。受理しなければ E-INTERNAL-VERIFIED-MISMATCH で拒否する。
/// - 字句・構文・名前・entry の段階で拒否したなら（資源上限による打切りを除く）、
///   検証済み部品もその段階までに拒否することを確かめる（誤拒否の検出）。
fn cross_check(text: &str, r: CompileResult, profile: &StaticProfile) -> CompileResult {
    cross_check_at(text, r, profile, (0, 0))
}

/// 検証済み parser が式の深さの上限で拒否したとき、受理に要る式の深さ（source と同じ単位）を返す。
/// 上限を十分大きくすると受理するなら深さの超過で、受理する最小の上限 d をそのまま返す（拒否の理由が他にあれば None）。
fn expr_depth_needed(chars: &Vec<char>, td: usize) -> Option<usize> {
    const HUGE: usize = 1 << 24;
    parse_e(chars, HUGE, td)?;
    // lo は拒否、hi は受理
    let (mut lo, mut hi) = (0usize, HUGE);
    while hi - lo > 1 {
        let mid = lo + (hi - lo) / 2;
        if parse_e(chars, mid, td).is_some() {
            hi = mid;
        } else {
            lo = mid;
        }
    }
    Some(hi)
}

/// `cross_check` と同じ。深さの超過は `at`（書き換え前の最も深い loop の入れ子の位置）に E-LIMIT-STATIC-EXPR-DEPTH で報告する。
fn cross_check_at(
    text: &str,
    r: CompileResult,
    profile: &StaticProfile,
    at: crate::diagnostics::Span,
) -> CompileResult {
    // 上限（資源・意味の上限）で打ち切った拒否は、検証済み部品の判定と比べず、そのまま返す（文字列の変換も省く）。
    if let CompileResult::Rejected { errors, .. } = &r {
        if errors
            .iter()
            .any(|e| e.is_cutoff() || e.phase == "diagnostic-limit")
        {
            return r;
        }
    }
    let chars: Vec<char> = text.chars().collect();
    if chars.len() >= VERIFIED_MAX_CHARS {
        return match r {
            CompileResult::Accepted { warnings, work, .. } => CompileResult::Rejected {
                errors: vec![mismatch("source-too-long-for-verified-parser")],
                warnings,
                work,
            },
            rejected => rejected,
        };
    }
    let (d, td) = depth_bounds(profile);
    match r {
        CompileResult::Accepted {
            mut program,
            warnings,
            work,
        } => {
            let rank: Vec<usize> = program
                .program
                .functions()
                .map(|f| program.rank.get(&f.name).copied().unwrap_or(usize::MAX))
                .collect();
            // v1.7：関数ごとの印 `rec`（検証済みプログラムの関数と同じ宣言順）
            let rec: Vec<bool> = program.program.functions().map(|f| f.rec).collect();
            match compile_source(&chars, d, td, rank, rec) {
                Compiled::Accepted(p) => {
                    program.verified = Some(Arc::new(VerifiedProgram(p)));
                    CompileResult::Accepted {
                        program,
                        warnings,
                        work,
                    }
                }
                Compiled::ParseRejected => match expr_depth_needed(&chars, td) {
                    // 書き換えた式が検証済み parser の式の深さの上限を超えた（式の深さの上限を超えた入力の診断）
                    Some(need) => {
                        let mut d =
                            Diagnostic::error("semantic-limits", "E-LIMIT-STATIC-EXPR-DEPTH", at)
                                .exp(profile.expr_depth.to_string())
                                .act(need.to_string());
                        if at != (0, 0) {
                            d = d.fix(
                                "replace_expression",
                                at,
                                "the nested loop is too deep to lower: fold over a List, or move an inner loop into a named rec fn and call it",
                            );
                        }
                        CompileResult::Rejected {
                            errors: vec![d],
                            warnings,
                            work,
                        }
                    }
                    None => CompileResult::Rejected {
                        errors: vec![mismatch("verified-parser-rejected")],
                        warnings,
                        work,
                    },
                },
                Compiled::NameRejected => CompileResult::Rejected {
                    errors: vec![mismatch("verified-resolver-rejected")],
                    warnings,
                    work,
                },
                Compiled::NotWellFormed => CompileResult::Rejected {
                    errors: vec![mismatch("verified-typechecker-rejected")],
                    warnings,
                    work,
                },
            }
        }
        CompileResult::Rejected {
            mut errors,
            warnings,
            work,
        } => {
            let cutoff = errors
                .iter()
                .any(|e| e.is_cutoff() || e.phase == "diagnostic-limit");
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
            CompileResult::Rejected {
                errors,
                warnings,
                work,
            }
        }
    }
}

/// v1.5：map などの 6 語（v1.6 の `loop`、v1.9 の `dict` と `dict_get` なども）が呼び出し・宣言の名前の位置
/// （直後が `(` か `<`、直前が `fn`・`entry`）にあるか。検証済みの構文規則ではこれらは普通の名前なので、
/// `map(xs, f)` や `fn find(...)` を受理しうる。診断用 parser はそれらを拒否する（`E-PARSE-EXPECTED-LAMBDA`、
/// `E-PARSE-EXPECTED-IDENT` など）ので、その場合は誤拒否の確かめを省く。
fn hof_word_called(text: &str, profile: &StaticProfile) -> bool {
    let Ok(toks) = lex(text.as_bytes(), profile) else {
        return false;
    };
    toks.iter().enumerate().any(|(i, t)| {
        let dict = crate::syntax::is_dict_word(&t.text);
        (crate::syntax::is_lambda_form(&t.text) || dict)
            && (toks
                .get(i + 1)
                .is_some_and(|n| n.is_punct("(") || (dict && n.is_punct("<")))
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
                let mut glued = hof::lower(&p, &o.hof);
                dict::erase_in_place(&mut glued);
                glued.unmark();
                format_program(&glued)
            } else if p.has_rec() {
                format_program(&p.unmarked())
            } else {
                format_program(&p)
            };
            let at = hof::deepest_loop_nest(&p).map_or((0, 0), |(_, s)| s);
            let r = check_rewritten_size(&text, result(o.diagnostics.clone(), Some(o)), profile);
            AstCompile::Result(without_repairs(cross_check_at(&text, r, profile, at)))
        }
    }
}

/// AST API は安全な JSON 部分木の置換を指定できないので repair を出さない（§10.1）。
fn without_repairs(r: CompileResult) -> CompileResult {
    let strip = |ds: Vec<Diagnostic>| {
        ds.into_iter()
            .map(|d| Diagnostic { repair: None, ..d })
            .collect::<Vec<_>>()
    };
    match r {
        CompileResult::Rejected {
            errors,
            warnings,
            work,
        } => CompileResult::Rejected {
            errors: strip(errors),
            warnings: strip(warnings),
            work,
        },
        CompileResult::Accepted {
            program,
            warnings,
            work,
        } => CompileResult::Accepted {
            program,
            warnings: strip(warnings),
            work,
        },
    }
}

pub fn decode_input(t_in: &Ty, data: &[u8], profile: &InputProfile) -> DecodeResult {
    values::decode_input(t_in, data, profile)
}

/// 普通の JSON（`plain` モジュールの対応表）で入力を読む。値 JSON へ変換してから `decode_input` と同じ
/// 経路（診断付きの復号器と検証済みの復号器の突き合わせ）で復号する。診断の span は plain JSON の bytes 上。
pub fn decode_plain_input(t_in: &Ty, data: &[u8], profile: &InputProfile) -> DecodeResult {
    match decode_plain(t_in, data, profile) {
        PlainDecode::Canonical(text) => {
            values::decode_input(t_in, text.as_bytes(), &canonical_profile(profile))
        }
        PlainDecode::Invalid(d) => DecodeResult::Invalid(d),
        PlainDecode::InputBoundaryFailure => DecodeResult::InputBoundaryFailure,
    }
}

/// 深い再帰に備えて host-policy のスタック量を持つスレッドで評価する。
pub fn run(
    program: &TypedProgram,
    input: &TypedValue,
    profile: &ExecutionProfile,
    host: &HostPolicy,
) -> Result<RunResult, String> {
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

/// 展開段階の名前の診断を、検証済み部品と突き合わせる（S5a、F3）。突き合わせるのは、診断の全部のコードが
/// `CHECKED_EXPANSION_CODES` に入るときだけ。外れるコードが一つでもあれば、検証済み部品と比べずにそのまま返す。
/// 展開は失敗しているので、突き合わせに渡すのは書き換える前の源の文字列（診断の文面と位置は変えない）。
/// 行の位置は、この関数より前の行を動かさないため、ファイルの末尾に置く（knowledge/diagnostics の位置の記録）。
fn expansion_rejected(
    source: &[u8],
    p: &Program,
    d: Vec<Diagnostic>,
    profile: &StaticProfile,
) -> CompileResult {
    let checked = !d.is_empty() && d.iter().all(|x| CHECKED_EXPANSION_CODES.contains(&x.code));
    let r = result(d, None);
    if !checked {
        return r;
    }
    let text = without_rec_markers(std::str::from_utf8(source).unwrap_or(""), p);
    cross_check(&text, r, profile)
}

/// 展開段階の名前の診断のうち、検証済み部品と突き合わせるコード（S5a）。ここに無いコードは突き合わせず、
/// そのまま返す（F3）。入れる根拠は、検証済みの名前の規則が同じ判定をすること（record_verified.rs の V1、V2、
/// V4、S2C_RECURSIVE と V7）。入れないコードと理由：
/// - E-SUM-NAME-CONFLICT、E-SUM-DUPLICATE-CTOR：検証済みの宣言の表に構築子の名前の規則が無く、検証済みが受理する。
/// - E-SUM-UNKNOWN-CTOR、E-SUM-CTOR-ARITY、E-MATCH-MISSING、E-MATCH-DUPLICATE、E-MATCH-UNREACHABLE、
///   E-MATCH-MIXED：検証済みの解決器は直和型の match を拒否し（SumMatch は None）、構築子は関数でないので呼出しも拒否する。
///   その拒否は規則の証拠にならない。
/// - E-TYPE-GENERIC-*、E-REC-TYPE-PARAM：検証済みの構文に型引数が無い（G1）ので、突き合わせが働かない。
///   （`fn g(x: U)` の例だけは構文が通るが、拒否は未知の型の規則による。総称の規則の証拠にはならない。）
pub const CHECKED_EXPANSION_CODES: &[&str] = &[
    "E-RECORD-UNKNOWN-TYPE",
    "E-RECORD-UNKNOWN-FIELD",
    "E-RECORD-DUPLICATE-FIELD",
    "E-RECORD-MISSING-FIELD",
    "E-RECORD-BASE-REDUNDANT",
    "E-RECORD-DUPLICATE-TYPE",
    "E-RECORD-FIELD-CONFLICT",
    "E-REC-FIELD-TYPE",
];
