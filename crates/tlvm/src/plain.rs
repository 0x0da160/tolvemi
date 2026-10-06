//! 普通の JSON（plain JSON）と値 JSON（設計書 §9.2）の相互変換。
//!
//! 設計書の入出力は tag 付きの値 JSON だけを定める。ここではホストから使いやすいよう、型で読む
//! 普通の JSON を値 JSON へ変換する層を設ける。設計書の外側の便宜であり、変換は検証されていない
//! （接着部分。`trust-boundary.toml`）。変換後の値 JSON は通常どおり診断付きの復号器と検証済みの
//! 復号器で読むので、プログラムが受け取る値の型整合性は従来どおり保たれる。
//!
//! 対応（型ごとに値と plain JSON が一対一に対応する）：
//!
//! | 型 | plain JSON |
//! |---|---|
//! | `Int` | 整数の JSON number（`-42`）。桁の多い整数のため正規形の十進文字列（`"-42"`）も受理する。出力は number |
//! | `Bool` | `true`、`false` |
//! | `Unit` | `null` |
//! | `List<T>` | 配列 |
//! | `Pair<A, B>` | 二要素の配列 `[a, b]` |
//! | `Option<T>` | `none` は `null`。`some(v)` は v の plain JSON。ただし T が `Unit` か `Option` なら `null` と区別できないので `{"some": v}` |

use crate::diagnostics::Diagnostic;
use crate::profiles::InputProfile;
use crate::strict_json::{parse, smallest_key, JKind, JNode, JsonFailKind};
use crate::syntax::{Ty, TyTag};
use crate::values::is_canonical_int;

pub enum PlainDecode {
    /// 変換した値 JSON
    Canonical(String),
    Invalid(Vec<Diagnostic>),
    InputBoundaryFailure,
}

/// `some(v)` を `{"some": v}` で包む必要がある型（plain JSON で `null` になりうる型）。
fn nullable(t: &Ty) -> bool {
    matches!(t.tag(), TyTag::Unit | TyTag::Option)
}

/// plain JSON での型の説明（診断の expected）。
pub fn plain_shape(t: &Ty) -> String {
    match t.tag() {
        TyTag::Int => "integer".into(),
        TyTag::Bool => "boolean".into(),
        TyTag::Unit => "null".into(),
        TyTag::List => "array".into(),
        TyTag::Pair => "array of 2 elements".into(),
        TyTag::Option if nullable(&t.arg(0)) => "null | {\"some\": ...}".into(),
        TyTag::Option => format!("null | {}", plain_shape(&t.arg(0))),
        TyTag::Error => "".into(),
    }
}

/// plain JSON の bytes を型 `t` で読み、値 JSON の文字列にする。
/// 入力の資源上限（bytes、JSON の深さ、値の深さ・node 数・整数の桁数）は plain JSON の上で数える。
pub fn decode_plain(t: &Ty, data: &[u8], profile: &InputProfile) -> PlainDecode {
    if data.len() > profile.json_bytes {
        return PlainDecode::Invalid(vec![Diagnostic::error("input-boundary", "E-LIMIT-INPUT-JSON-BYTES", (0, 0))
            .exp(profile.json_bytes.to_string())
            .act(data.len().to_string())]);
    }
    if std::str::from_utf8(data).is_err() {
        return PlainDecode::InputBoundaryFailure;
    }
    let root = match parse(data, profile.json_depth) {
        Ok(r) => r,
        Err(f) => {
            let code = match f.kind {
                JsonFailKind::Syntax => "E-INPUT-JSON-SYNTAX",
                JsonFailKind::Depth => "E-LIMIT-INPUT-JSON-DEPTH",
                JsonFailKind::Scalar => "E-INPUT-STRING-SCALAR",
                JsonFailKind::Duplicate => "E-INPUT-DUPLICATE-KEY",
            };
            return PlainDecode::Invalid(vec![Diagnostic::error("input-parse", code, f.span)]);
        }
    };
    let mut c = Conv { p: profile, nodes: 0, out: String::new() };
    match c.value(&root, t, 1) {
        Ok(()) => PlainDecode::Canonical(c.out),
        Err(d) => PlainDecode::Invalid(vec![d]),
    }
}

/// 値 JSON を復号するときの profile。plain JSON の上で上限を検査済みなので、値 JSON の bytes と
/// 構造の深さ（tag 付き object と配列で plain JSON より大きくなる）だけを広げる。
pub fn canonical_profile(p: &InputProfile) -> InputProfile {
    InputProfile {
        json_bytes: usize::MAX,
        json_depth: p.value_depth.saturating_mul(2).saturating_add(2).max(p.json_depth),
        ..p.clone()
    }
}

struct Conv<'a> {
    p: &'a InputProfile,
    nodes: usize,
    out: String,
}

impl Conv<'_> {
    fn shape_err(&self, n: &JNode, t: &Ty) -> Diagnostic {
        Diagnostic::error("input-decode", "E-INPUT-FIELD-TYPE", n.span()).exp(plain_shape(t)).act(n.kind.name())
    }

    fn admit(&mut self, n: &JNode, depth: usize) -> Result<(), Diagnostic> {
        if depth > self.p.value_depth {
            return Err(Diagnostic::error("input-decode", "E-LIMIT-INPUT-VALUE-DEPTH", n.span())
                .exp(self.p.value_depth.to_string())
                .act(depth.to_string()));
        }
        if self.nodes + 1 > self.p.value_nodes {
            return Err(Diagnostic::error("input-decode", "E-LIMIT-INPUT-VALUE-NODES", n.span())
                .exp(self.p.value_nodes.to_string())
                .act((self.nodes + 1).to_string()));
        }
        self.nodes += 1;
        Ok(())
    }

    fn value(&mut self, n: &JNode, t: &Ty, depth: usize) -> Result<(), Diagnostic> {
        match t.tag() {
            TyTag::Int => {
                if n.kind != JKind::Number && n.kind != JKind::String {
                    return Err(self.shape_err(n, t));
                }
                self.admit(n, depth)?;
                if !is_canonical_int(&n.text) {
                    return Err(Diagnostic::error("input-decode", "E-INPUT-INTEGER", n.span()).act(n.text.clone()));
                }
                let digits = n.text.trim_start_matches('-').len();
                if digits > self.p.integer_digits {
                    return Err(Diagnostic::error("input-decode", "E-LIMIT-INPUT-INTEGER-DIGITS", n.span())
                        .exp(self.p.integer_digits.to_string())
                        .act(digits.to_string()));
                }
                self.out.push_str("{\"tag\":\"int\",\"value\":\"");
                self.out.push_str(&n.text);
                self.out.push_str("\"}");
            }
            TyTag::Bool => {
                if n.kind != JKind::Boolean {
                    return Err(self.shape_err(n, t));
                }
                self.admit(n, depth)?;
                self.out.push_str(if n.boolean { "{\"tag\":\"bool\",\"value\":true}" } else { "{\"tag\":\"bool\",\"value\":false}" });
            }
            TyTag::Unit => {
                if n.kind != JKind::Null {
                    return Err(self.shape_err(n, t));
                }
                self.admit(n, depth)?;
                self.out.push_str("{\"tag\":\"unit\"}");
            }
            TyTag::List => {
                if n.kind != JKind::Array {
                    return Err(self.shape_err(n, t));
                }
                self.admit(n, depth)?;
                let el = t.arg(0);
                self.out.push_str("{\"tag\":\"list\",\"items\":[");
                for (i, c) in n.items.iter().enumerate() {
                    if i > 0 {
                        self.out.push(',');
                    }
                    self.value(c, &el, depth + 1)?;
                }
                self.out.push_str("]}");
            }
            TyTag::Pair => {
                if n.kind != JKind::Array {
                    return Err(self.shape_err(n, t));
                }
                if n.items.len() != 2 {
                    return Err(Diagnostic::error("input-decode", "E-INPUT-FIELD-TYPE", n.span())
                        .exp(plain_shape(t))
                        .act(format!("array of {} elements", n.items.len())));
                }
                self.admit(n, depth)?;
                self.out.push_str("{\"tag\":\"pair\",\"left\":");
                self.value(&n.items[0], &t.arg(0), depth + 1)?;
                self.out.push_str(",\"right\":");
                self.value(&n.items[1], &t.arg(1), depth + 1)?;
                self.out.push('}');
            }
            TyTag::Option => {
                if n.kind == JKind::Null {
                    self.admit(n, depth)?;
                    self.out.push_str("{\"tag\":\"none\"}");
                    return Ok(());
                }
                let inner = t.arg(0);
                let payload = if nullable(&inner) {
                    if n.kind != JKind::Object {
                        return Err(self.shape_err(n, t));
                    }
                    let Some(v) = n.get("some") else {
                        return Err(Diagnostic::error("input-decode", "E-INPUT-MISSING-FIELD", n.close_span()).exp("some"));
                    };
                    if let Some(k) = smallest_key(n.members.iter().map(|m| m.key.as_str()).filter(|k| *k != "some")) {
                        return Err(Diagnostic::error("input-decode", "E-INPUT-UNKNOWN-FIELD", n.key_span(k)).act(k));
                    }
                    v
                } else {
                    n
                };
                self.admit(n, depth)?;
                self.out.push_str("{\"tag\":\"some\",\"value\":");
                self.value(payload, &inner, depth + 1)?;
                self.out.push('}');
            }
            TyTag::Error => return Err(self.shape_err(n, t)),
        }
        Ok(())
    }
}

/// 値 JSON（処理系が出した正準出力）を型 `t` の plain JSON（最小空白）にする。
pub fn encode_plain(t: &Ty, canonical: &str) -> Result<String, String> {
    let root = parse(canonical.as_bytes(), usize::MAX).map_err(|f| format!("値 JSON を読めません（{:?}）", f.kind))?;
    let mut out = String::new();
    write_plain(&root, t, &mut out)?;
    Ok(out)
}

fn write_plain(n: &JNode, t: &Ty, out: &mut String) -> Result<(), String> {
    let field = |k: &str| n.get(k).ok_or_else(|| format!("値 JSON に {k} がありません"));
    let tag = field("tag")?.text.as_str();
    match (t.tag(), tag) {
        (TyTag::Int, "int") => out.push_str(&field("value")?.text),
        (TyTag::Bool, "bool") => out.push_str(if field("value")?.boolean { "true" } else { "false" }),
        (TyTag::Unit, "unit") | (TyTag::Option, "none") => out.push_str("null"),
        (TyTag::List, "list") => {
            out.push('[');
            for (i, c) in field("items")?.items.iter().enumerate() {
                if i > 0 {
                    out.push(',');
                }
                write_plain(c, &t.arg(0), out)?;
            }
            out.push(']');
        }
        (TyTag::Pair, "pair") => {
            out.push('[');
            write_plain(field("left")?, &t.arg(0), out)?;
            out.push(',');
            write_plain(field("right")?, &t.arg(1), out)?;
            out.push(']');
        }
        (TyTag::Option, "some") => {
            let inner = t.arg(0);
            if nullable(&inner) {
                out.push_str("{\"some\":");
                write_plain(field("value")?, &inner, out)?;
                out.push('}');
            } else {
                write_plain(field("value")?, &inner, out)?;
            }
        }
        _ => return Err(format!("値 JSON の tag {tag} が型 {t} と一致しません")),
    }
    Ok(())
}
