//! 拒否したプログラムの診断を、検証済み部品との食い違いの検査つきで取る。record_names.rs と record_verified.rs が使う。

#![allow(dead_code)]

use tlvm::api::*;
use tlvm::profiles::*;

pub const MISMATCH: &str = "E-INTERNAL-VERIFIED-MISMATCH";

/// 診断の (phase, code, expected, actual)。値のない欄は空文字。
pub type Row = (String, String, String, String);

pub fn row(phase: &str, code: &str, expected: &str, actual: &str) -> Row {
    (phase.into(), code.into(), expected.into(), actual.into())
}

/// 拒否したプログラムの診断。検証済み部品との食い違い（E-INTERNAL-VERIFIED-MISMATCH）は出てはいけない。
pub fn rejected(src: &str) -> Vec<Row> {
    match compile(src.as_bytes(), &StaticProfile::default()) {
        SourceCompile::Result(CompileResult::Rejected { errors, .. }) => {
            let rows: Vec<Row> = errors
                .iter()
                .map(|d| {
                    row(
                        d.phase,
                        d.code,
                        d.expected.as_deref().unwrap_or(""),
                        d.actual.as_deref().unwrap_or(""),
                    )
                })
                .collect();
            assert!(
                rows.iter().all(|r| r.1 != MISMATCH),
                "検証済み部品との食い違い: {src}\n{rows:?}"
            );
            rows
        }
        SourceCompile::Result(CompileResult::Accepted { .. }) => panic!("受理された: {src}"),
        _ => panic!("結果が出ない: {src}"),
    }
}
