//! v1.12：型比較の共有（比較 cache）と型の正準化（interning）は、論理 trace・仕事量・cutoff・診断・型を変えない
//! （設計書 §18.1a）。

use std::path::{Path, PathBuf};
use tlvm::api::{expand, parse_source, Parsed};
use tlvm::checker::{check_program_with, CheckOptions, CheckOutcome, TypeSharing};
use tlvm::generics::check_with;
use tlvm::profiles::StaticProfile;

/// Off と比べる共有の方式（比較 cache のみ、比較 cache と正準化）。
const SHARED: [TypeSharing; 2] = [TypeSharing::On, TypeSharing::Interned];

fn check(src: &[u8], sharing: TypeSharing, semantic_work: u64) -> Option<CheckOutcome> {
    let profile = StaticProfile {
        semantic_work,
        ..StaticProfile::default()
    };
    match parse_source(src, &profile) {
        Parsed::Program(p) => Some(check_program_with(
            &p,
            src.len(),
            &profile,
            &CheckOptions {
                sharing,
                trace: true,
            },
        )),
        Parsed::Failed(_) => None,
    }
}

/// 総称のプログラムの二つのパス（`generics::check_with`。`compile` と同じ経路）。
fn check_two_pass(src: &[u8], sharing: TypeSharing, semantic_work: u64) -> Option<CheckOutcome> {
    let profile = StaticProfile {
        semantic_work,
        ..StaticProfile::default()
    };
    let Parsed::Program(p) = parse_source(src, &profile) else {
        return None;
    };
    let px = expand(&p).ok()?;
    let opts = CheckOptions {
        sharing,
        trace: true,
    };
    Some(check_with(&px, src.len(), &profile, &opts).0)
}

/// 受理した型（入出力）と、map などと総称の呼出しの型の表。型の名前の印を含む表示で比べる。
fn types(o: &CheckOutcome) -> String {
    let mut hof: Vec<String> = o
        .hof
        .iter()
        .map(|(i, (a, b))| format!("{i}:{a}:{b}"))
        .collect();
    hof.sort();
    let mut inst: Vec<String> = o
        .inst
        .iter()
        .map(|(i, ts)| {
            let ts: Vec<String> = ts.iter().map(|t| t.to_string()).collect();
            format!("{i}:{}", ts.join(","))
        })
        .collect();
    inst.sort();
    let typed = o
        .typed
        .as_ref()
        .map(|t| format!("{} -> {}", t.input_type, t.output_type));
    format!("hof {hof:?} inst {inst:?} typed {typed:?}")
}

/// 論理 trace・仕事量・診断（全体）・型が同じことを確かめる。
fn assert_same(off: &CheckOutcome, on: &CheckOutcome, name: &str) {
    assert_eq!(off.work, on.work, "{name}");
    assert_eq!(off.trace, on.trace, "{name}");
    assert_eq!(off.diagnostics, on.diagnostics, "{name}");
    assert_eq!(types(off), types(on), "{name}");
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

fn repo_programs() -> Vec<PathBuf> {
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
    let mut files = vec![];
    walk(&root, &mut files);
    files.sort();
    assert!(!files.is_empty());
    files
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
fn interning_shares_equal_types_that_the_cache_misses() {
    // 作った場所の違う同じ Int は、正準化しないと cache の鍵（node の address）が違って当たらない。正準化すると
    // 同じ node になり、比較の結果と論理イベント列が再生される。
    let src = b"fn f(x: Int) -> Int = add(add(x, 1), 2) entry f";
    let off = check(src, TypeSharing::Off, 1 << 20).unwrap();
    let on = check(src, TypeSharing::On, 1 << 20).unwrap();
    let interned = check(src, TypeSharing::Interned, 1 << 20).unwrap();
    assert_eq!(off.sharing_hits, 0);
    assert_eq!(on.sharing_hits, 0);
    assert!(interned.sharing_hits > 0);
    assert_same(&off, &interned, "fixture");
}

#[test]
fn sharing_keeps_trace_work_and_cutoff() {
    let default_work = StaticProfile::default().semantic_work;
    let mut hits = 0;
    for f in repo_programs() {
        let src = std::fs::read(&f).unwrap();
        // 上限なしと、途中で cutoff する小さい上限の三通り
        for work in [default_work, 40, 400] {
            let Some(off) = check(&src, TypeSharing::Off, work) else {
                continue;
            };
            for mode in SHARED {
                let on = check(&src, mode, work).unwrap();
                assert_same(&off, &on, &format!("{mode:?} {} {work}", f.display()));
                hits += on.sharing_hits;
            }
        }
    }
    assert!(hits > 0);
}

#[test]
fn sharing_keeps_trace_work_and_cutoff_on_the_two_pass_path() {
    // 総称のプログラムは二つのパスを続けて検査する。正準化の表は二つのパスで共有するので、その経路でも同じ。
    let default_work = StaticProfile::default().semantic_work;
    for f in repo_programs() {
        let src = std::fs::read(&f).unwrap();
        for work in [default_work, 40, 400] {
            let Some(off) = check_two_pass(&src, TypeSharing::Off, work) else {
                continue;
            };
            for mode in SHARED {
                let on = check_two_pass(&src, mode, work).unwrap();
                assert_same(&off, &on, &format!("{mode:?} {} {work}", f.display()));
            }
        }
    }
}
