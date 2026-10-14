//! v1.12：型比較の共有（比較 cache）の切替は、論理 trace・仕事量・cutoff を変えない（設計書 §18.1a）。

use std::path::{Path, PathBuf};
use tlvm::api::{parse_source, Parsed};
use tlvm::checker::{check_program_with, CheckOptions, CheckOutcome, TypeSharing};
use tlvm::profiles::StaticProfile;

fn check(src: &[u8], sharing: TypeSharing, semantic_work: u64) -> Option<CheckOutcome> {
    let profile = StaticProfile { semantic_work, ..StaticProfile::default() };
    match parse_source(src, &profile) {
        Parsed::Program(p) => Some(check_program_with(&p, src.len(), &profile, &CheckOptions { sharing, trace: true })),
        Parsed::Failed(_) => None,
    }
}

/// 論理 trace・仕事量・診断（code、span、論理 node index）が同じことを確かめる。
fn assert_same(off: &CheckOutcome, on: &CheckOutcome, name: &str) {
    assert_eq!(off.work, on.work, "{name}");
    assert_eq!(off.trace, on.trace, "{name}");
    let key = |o: &CheckOutcome| o.diagnostics.iter().map(|d| (d.code, d.span, d.node_index)).collect::<Vec<_>>();
    assert_eq!(key(off), key(on), "{name}");
}

fn walk(dir: &Path, out: &mut Vec<PathBuf>) {
    for e in std::fs::read_dir(dir).unwrap() {
        let p = e.unwrap().path();
        let name = p.file_name().unwrap().to_string_lossy().into_owned();
        if p.is_dir() {
            if name != "target" && !name.starts_with('.') {
                walk(&p, out);
            }
        } else if p.extension().is_some_and(|x| x == "tlvm") {
            out.push(p);
        }
    }
}

#[test]
fn sharing_replays_cached_comparisons() {
    // 同じ型の対を何度も照合する。On は二回目以降を cache から再生する。
    let src = b"fn f(x: Pair<Int, Int>) -> Bool = if(eq(x, x), eq(x, x), eq(x, x)) entry f";
    let off = check(src, TypeSharing::Off, 1 << 20).unwrap();
    let on = check(src, TypeSharing::On, 1 << 20).unwrap();
    assert_eq!(off.sharing_hits, 0);
    assert!(on.sharing_hits > 0);
    assert_same(&off, &on, "fixture");
}

#[test]
fn sharing_keeps_trace_work_and_cutoff() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
    let mut files = vec![];
    walk(&root, &mut files);
    files.sort();
    assert!(!files.is_empty());
    let default_work = StaticProfile::default().semantic_work;
    let mut hits = 0;
    for f in &files {
        let src = std::fs::read(f).unwrap();
        // 上限なしと、途中で cutoff する小さい上限の三通り
        for work in [default_work, 40, 400] {
            let Some(off) = check(&src, TypeSharing::Off, work) else { continue };
            let on = check(&src, TypeSharing::On, work).unwrap();
            assert_same(&off, &on, &f.display().to_string());
            hits += on.sharing_hits;
        }
    }
    assert!(hits > 0);
}
