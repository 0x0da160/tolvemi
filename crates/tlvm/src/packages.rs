//! v1.16：パッケージ（ローカルの依存）。差分仕様 `spec/lptl-v1.16`。
//!
//! マニフェスト `tlvm.json`（厳格な JSON）を読み、宣言した名前・版・依存の場所を取り出す。依存のディレクトリを読むこと、
//! `@名前/パス` の import を依存のファイルに結びつけることは `imports.rs` が行う。ここは検証されていない接着部分で、
//! 検査・実行の対象は、解決の結果つないだ一つの source（v1.11 と同じ）である。

use crate::strict_json::{self, JKind, JNode};
use std::collections::BTreeMap;

/// マニフェストの名前（根のディレクトリと依存のディレクトリに置く）。
pub const MANIFEST: &str = "tlvm.json";
/// マニフェストの大きさの上限（bytes）。
pub const MANIFEST_MAX_BYTES: usize = 64 * 1024;
/// マニフェストの JSON の入れ子の深さの上限。
const MANIFEST_DEPTH: usize = 4;

/// 宣言した依存。各 span は宣言したマニフェストの中の位置。
#[derive(Clone, Debug)]
pub struct Dep {
    /// 宣言したパッケージのディレクトリからの相対パス（未正規化）
    pub path: String,
    pub path_span: (usize, usize),
    /// 版の固定（`"version"` を書いたとき）
    pub pin: Option<String>,
    pub pin_span: (usize, usize),
    /// 依存の名前（鍵）の位置
    pub name_span: (usize, usize),
}

/// 読んだマニフェスト。
#[derive(Clone, Debug, Default)]
pub struct Manifest {
    pub name: Option<String>,
    pub version: Option<String>,
    /// 依存の名前から宣言へ（名前の順）
    pub deps: BTreeMap<String, Dep>,
}

/// 名前の形（パッケージ・依存）：`[a-z][a-z0-9_]*`、64 bytes まで。
pub fn valid_name(s: &str) -> bool {
    let mut cs = s.chars();
    s.len() <= 64 && matches!(cs.next(), Some('a'..='z')) && cs.all(|c| matches!(c, 'a'..='z' | '0'..='9' | '_'))
}

/// 版の形：`MAJOR.MINOR.PATCH`（十進の数字の三つ組。各部は 1〜9 桁）。
pub fn valid_version(s: &str) -> bool {
    let parts: Vec<&str> = s.split('.').collect();
    parts.len() == 3 && parts.iter().all(|p| (1..=9).contains(&p.len()) && p.bytes().all(|b| b.is_ascii_digit()))
}

/// 誤りの理由と、マニフェストの中の位置。
pub type Failure = (String, (usize, usize));

/// マニフェストを読む。
pub fn parse(bytes: &[u8]) -> Result<Manifest, Failure> {
    if bytes.len() > MANIFEST_MAX_BYTES {
        return Err((format!("larger than {MANIFEST_MAX_BYTES} bytes"), (0, 0)));
    }
    let root = strict_json::parse(bytes, MANIFEST_DEPTH).map_err(|f| ("not valid JSON, or nested too deeply".to_string(), f.span))?;
    if root.kind != JKind::Object {
        return Err(("the top level must be an object".into(), root.span()));
    }
    let mut m = Manifest::default();
    for mem in &root.members {
        match mem.key.as_str() {
            "name" => m.name = Some(name_of(&mem.value, "name")?),
            "version" => m.version = Some(version_of(&mem.value, "version")?),
            "dependencies" => {
                if mem.value.kind != JKind::Object {
                    return Err(("\"dependencies\" must be an object".into(), mem.value.span()));
                }
                for d in &mem.value.members {
                    if !valid_name(&d.key) {
                        return Err((format!("dependency name \"{}\" must match [a-z][a-z0-9_]*", d.key), d.key_span));
                    }
                    m.deps.insert(d.key.clone(), dep_of(&d.value, d.key_span)?);
                }
            }
            other => return Err((format!("unknown key \"{other}\" (allowed: name, version, dependencies)"), mem.key_span)),
        }
    }
    Ok(m)
}

fn string_of<'a>(n: &'a JNode, what: &str) -> Result<&'a str, Failure> {
    if n.kind != JKind::String {
        return Err((format!("\"{what}\" must be a string"), n.span()));
    }
    Ok(&n.text)
}

fn name_of(n: &JNode, what: &str) -> Result<String, Failure> {
    let s = string_of(n, what)?;
    if !valid_name(s) {
        return Err((format!("\"{what}\" \"{s}\" must match [a-z][a-z0-9_]*"), n.span()));
    }
    Ok(s.to_string())
}

fn version_of(n: &JNode, what: &str) -> Result<String, Failure> {
    let s = string_of(n, what)?;
    if !valid_version(s) {
        return Err((format!("\"{what}\" \"{s}\" must be MAJOR.MINOR.PATCH (digits)"), n.span()));
    }
    Ok(s.to_string())
}

fn dep_of(n: &JNode, name_span: (usize, usize)) -> Result<Dep, Failure> {
    if n.kind != JKind::Object {
        return Err(("a dependency must be an object with \"path\" (and optionally \"version\")".into(), n.span()));
    }
    let mut path = None;
    let mut pin = None;
    for mem in &n.members {
        match mem.key.as_str() {
            "path" => path = Some((string_of(&mem.value, "path")?.to_string(), mem.value.span())),
            "version" => pin = Some((version_of(&mem.value, "version")?, mem.value.span())),
            other => return Err((format!("unknown key \"{other}\" in a dependency (allowed: path, version)"), mem.key_span)),
        }
    }
    let Some((path, path_span)) = path else {
        return Err(("a dependency needs \"path\"".into(), n.span()));
    };
    let (pin, pin_span) = match pin {
        Some((v, s)) => (Some(v), s),
        None => (None, (0, 0)),
    };
    Ok(Dep { path, path_span, pin, pin_span, name_span })
}

/// 宣言したパッケージのディレクトリ `dir`（根からの正規形。根は空）に対して、依存の `path` を解決して正規形にする。
/// 区切りは `/`。`.`・`..` を含んでよいが、根のディレクトリより上へは出られない。
pub fn join_dir(dir: &str, path: &str) -> Result<String, &'static str> {
    if path.is_empty() {
        return Err("empty path");
    }
    if path.starts_with('/') {
        return Err("absolute paths are not allowed");
    }
    if path.chars().any(|c| c == '\\' || c == ':' || c.is_control()) {
        return Err("use '/' as the separator; '\\', ':' and control characters are not allowed");
    }
    let mut parts: Vec<&str> = dir.split('/').filter(|s| !s.is_empty()).collect();
    for c in path.split('/') {
        match c {
            "" => return Err("empty path component ('//' or a trailing '/')"),
            "." => {}
            ".." => {
                if parts.pop().is_none() {
                    return Err("'..' must not go above the root file's directory");
                }
            }
            c => parts.push(c),
        }
    }
    Ok(parts.join("/"))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn names_and_versions() {
        assert!(valid_name("stats") && valid_name("a_1") && !valid_name("Stats") && !valid_name("1a") && !valid_name("a-b"));
        assert!(valid_version("1.0.0") && valid_version("10.2.333") && !valid_version("1.0") && !valid_version("1.0.0-rc") && !valid_version("01.0.0.0"));
    }

    #[test]
    fn dependency_paths_stay_under_the_root() {
        assert_eq!(join_dir("", "deps/stats").unwrap(), "deps/stats");
        assert_eq!(join_dir("deps/a", "../b").unwrap(), "deps/b");
        assert_eq!(join_dir("deps/a", "./x/").err(), Some("empty path component ('//' or a trailing '/')"));
        assert!(join_dir("", "../x").is_err());
        assert!(join_dir("", "/x").is_err());
        assert!(join_dir("", "a\\b").is_err());
    }

    #[test]
    fn manifest_shapes() {
        let m = parse(br#"{"name":"app","version":"1.0.0","dependencies":{"stats":{"path":"deps/stats","version":"0.2.0"}}}"#).unwrap();
        assert_eq!(m.name.as_deref(), Some("app"));
        assert_eq!(m.deps["stats"].pin.as_deref(), Some("0.2.0"));
        assert!(parse(br#"{"nmae":"x"}"#).is_err());
        assert!(parse(br#"{"dependencies":{"x":{}}}"#).is_err());
        assert!(parse(br#"{"dependencies":{"X":{"path":"a"}}}"#).is_err());
        assert!(parse(b"[]").is_err());
        assert!(parse(b"{").is_err());
    }
}
