//! 診断の点検（G0 の diag-02 と diag-10）。crates/tlvm/src の文字列リテラルから診断のコードと phase を集め、
//! 文面・順位・配置が揃っているかを確かめる。

use std::collections::BTreeSet;
use std::fs;
use std::path::{Path, PathBuf};

use tlvm::diagnostics::{message_for, PHASE_ORDER, UNREGISTERED_MESSAGE};

fn rust_files(dir: &Path, out: &mut Vec<PathBuf>) {
    for entry in fs::read_dir(dir).expect("read src") {
        let path = entry.expect("dir entry").path();
        if path.is_dir() {
            rust_files(&path, out);
        } else if path.extension().is_some_and(|e| e == "rs") {
            out.push(path);
        }
    }
}

fn sources() -> Vec<PathBuf> {
    let mut files = Vec::new();
    rust_files(&Path::new(env!("CARGO_MANIFEST_DIR")).join("src"), &mut files);
    files
}

fn read(path: impl AsRef<Path>) -> String {
    fs::read_to_string(Path::new(env!("CARGO_MANIFEST_DIR")).join(path)).expect("read file")
}

/// 引用符で囲まれた中身が診断コードの形をしているものを集める。
/// 末尾が '-' のものは接頭辞（E-TYPE- など）なので除く。
fn codes_in(src: &str) -> BTreeSet<String> {
    let mut found = BTreeSet::new();
    for (i, _) in src.match_indices('"') {
        let body = &src[i + 1..];
        if !(body.starts_with("E-") || body.starts_with("W-")) {
            continue;
        }
        let Some(end) = body.find('"') else { continue };
        let code = &body[..end];
        let shaped = code.len() > 2
            && !code.ends_with('-')
            && code.bytes().all(|b| b.is_ascii_uppercase() || b.is_ascii_digit() || b == b'-');
        if shaped {
            found.insert(code.to_string());
        }
    }
    found
}

/// `Diagnostic::error(` と `Diagnostic::warning(` の最初の引数（phase の文字列）を集める。
fn phases_in(src: &str) -> BTreeSet<String> {
    let mut found = BTreeSet::new();
    for marker in ["Diagnostic::error(", "Diagnostic::warning("] {
        for (i, _) in src.match_indices(marker) {
            let rest = src[i + marker.len()..].trim_start();
            if let Some(body) = rest.strip_prefix('"') {
                if let Some(end) = body.find('"') {
                    found.insert(body[..end].to_string());
                }
            }
        }
    }
    found
}

#[test]
fn every_code_in_the_source_has_a_message() {
    let mut codes = BTreeSet::new();
    for f in sources() {
        codes.extend(codes_in(&fs::read_to_string(&f).expect("read source")));
    }
    // 走査が壊れて空に近くなっても通らないように、下限を置く（現在は 136 件）。
    assert!(codes.len() >= 130, "only {} codes found; the scan is broken", codes.len());
    let missing: Vec<&String> = codes
        .iter()
        .filter(|c| message_for(c).is_empty() || message_for(c) == UNREGISTERED_MESSAGE)
        .collect();
    assert!(missing.is_empty(), "codes without a message template: {missing:?}");
}

#[test]
fn every_emitted_phase_has_a_rank() {
    let mut phases = BTreeSet::new();
    for f in sources() {
        phases.extend(phases_in(&fs::read_to_string(&f).expect("read source")));
    }
    assert!(phases.len() >= 20, "only {} phases found; the scan is broken", phases.len());
    let unranked: Vec<&String> = phases.iter().filter(|p| !PHASE_ORDER.contains(&p.as_str())).collect();
    assert!(unranked.is_empty(), "phases without a rank in PHASE_ORDER: {unranked:?}");
    let distinct: BTreeSet<&str> = PHASE_ORDER.iter().copied().collect();
    assert_eq!(distinct.len(), PHASE_ORDER.len(), "PHASE_ORDER lists a phase twice");
}

#[test]
fn expression_depth_has_one_phase() {
    // 式の深さは設計書 §10.2 の表で structural-limits。api.rs・parser.rs・台帳が同じ phase を使う。
    let api = read("src/api.rs");
    let parser = read("src/parser.rs");
    assert!(api.contains(r#"Diagnostic::error("structural-limits", "E-LIMIT-STATIC-EXPR-DEPTH""#));
    assert!(!api.contains(r#""semantic-limits", "E-LIMIT-STATIC-EXPR-DEPTH""#));
    assert!(parser.contains(r#"Diagnostic::error("structural-limits", code, span)"#));
    let catalog = read("../../knowledge/diagnostics/diagnostic-codes.md");
    let row = catalog.lines().find(|l| l.contains("`-EXPR-DEPTH`")).expect("catalog row for the expression depth");
    assert!(row.contains("structural-limits"), "{row}");
}
