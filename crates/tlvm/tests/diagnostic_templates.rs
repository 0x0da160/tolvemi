//! 診断の文面（G0 の diag-02）：crates/tlvm/src に現れるすべての診断コード（"E-…" と "W-…" の文字列）に、
//! 空でない文面の template があることを確かめる。コードを足して文面を忘れると、ここで失敗する。

use std::collections::BTreeSet;
use std::fs;
use std::path::{Path, PathBuf};

use tlvm::diagnostics::{message_for, UNREGISTERED_MESSAGE};

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

#[test]
fn every_code_in_the_source_has_a_message() {
    let mut files = Vec::new();
    rust_files(&Path::new(env!("CARGO_MANIFEST_DIR")).join("src"), &mut files);
    let mut codes = BTreeSet::new();
    for f in &files {
        codes.extend(codes_in(&fs::read_to_string(f).expect("read source")));
    }
    // 走査が壊れて空に近くなっても通らないように、下限を置く（現在は 136 件）。
    assert!(codes.len() >= 130, "only {} codes found; the scan is broken", codes.len());
    let missing: Vec<&String> = codes
        .iter()
        .filter(|c| message_for(c).is_empty() || message_for(c) == UNREGISTERED_MESSAGE)
        .collect();
    assert!(missing.is_empty(), "codes without a message template: {missing:?}");
}
