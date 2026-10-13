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
//! | `Char` | 1 文字の JSON 文字列（`"a"`） |
//! | `String`（= `List<Char>`） | JSON 文字列（`"abc"`） |
//! | `List<T>` | 配列（T が `Char` なら上の `String`） |
//! | `Pair<A, B>` | 二要素の配列 `[a, b]` |
//! | `Option<T>` | `none` は `null`。`some(v)` は v の plain JSON。ただし T が `Unit` か `Option` なら `null` と区別できないので `{"some": v}` |
//! | `Result<T, E>`（v1.4） | `{"ok": v}`、`{"err": e}` |
//! | `Dict<K, V>`（v1.9） | `[key, value]` の配列の配列（挿入順。`[["a", 1], ["b", 2]]`）。入力で鍵が重なれば拒否 |
//! | レコード型（v1.1） | field 名を key にした object |
//! | 直和型（v1.4） | variant 名を key にし、中身を配列にした object（`{"Rect": [2, 3]}`、`{"Empty": []}`） |

use crate::diagnostics::Diagnostic;
use crate::formatter::json_string;
use crate::profiles::InputProfile;
use crate::strict_json::{parse, smallest_key, JKind, JNode, JsonFailKind};
use crate::syntax::{Ty, TyTag};
use crate::values::{is_canonical_int, DICT_DUPLICATE_KEY};

pub enum PlainDecode {
    /// 変換した値 JSON
    Canonical(String),
    Invalid(Vec<Diagnostic>),
    InputBoundaryFailure,
}

/// `some(v)` を `{"some": v}` で包む必要がある型（plain JSON で `null` になりうる型）。
fn nullable(t: &Ty) -> bool {
    t.sum().is_none() && matches!(t.tag(), TyTag::Unit | TyTag::Option)
}

/// v1.4：直和型の k 番目の variant の中身の型（展開後の `Result<P1, Result<P2, ... Pn>>` から取り出す）。
fn sum_payload(t: &Ty, n: usize, k: usize) -> Ty {
    let mut cur = t.unlabeled();
    if n == 1 {
        return match t.sum() {
            Some(s) if s.inner.0.is_some() => cur.labeled(s.inner.clone()),
            _ => cur,
        };
    }
    for _ in 0..k {
        cur = cur.arg(1);
    }
    if k + 1 < n {
        cur.arg(0)
    } else {
        cur
    }
}

/// 中身の型の並び（`Unit`、その型一つ、右に入れ子にした `Pair`）を m 個に分ける。
fn payload_fields(p: &Ty, m: usize) -> Vec<Ty> {
    let mut out = vec![];
    let mut cur = p.clone();
    for i in 0..m {
        if i + 1 == m {
            out.push(cur.clone());
        } else {
            out.push(cur.arg(0));
            cur = cur.arg(1);
        }
    }
    out
}

/// plain JSON での型の説明（診断の expected）。
pub fn plain_shape(t: &Ty) -> String {
    if let Some(r) = t.record() {
        return format!("object with keys {}", r.fields.join(", "));
    }
    if let Some(s) = t.sum() {
        let vs: Vec<&str> = s.variants.iter().map(|(v, _)| v.as_str()).collect();
        return format!("object with one key ({}) whose value is an array of the fields", vs.join(" | "));
    }
    match t.tag() {
        TyTag::Int => "integer".into(),
        TyTag::Bool => "boolean".into(),
        TyTag::Unit => "null".into(),
        TyTag::Char => "string of one char".into(),
        TyTag::List if t.is_string() => "string".into(),
        TyTag::List => "array".into(),
        TyTag::Pair => "array of 2 elements".into(),
        TyTag::Option if nullable(&t.arg(0)) => "null | {\"some\": ...}".into(),
        TyTag::Option => format!("null | {}", plain_shape(&t.arg(0))),
        TyTag::Result => "{\"ok\": ...} | {\"err\": ...}".into(),
        TyTag::Dict => "array of [key, value] arrays".into(),
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

    fn push_char(&mut self, c: char) {
        self.out.push_str("{\"tag\":\"char\",\"value\":\"");
        self.out.push_str(&(c as u32).to_string());
        self.out.push_str("\"}");
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

    /// v1.1：レコード型は field 名を key にした object。値 JSON では pair の入れ子になる。
    fn record(&mut self, n: &JNode, t: &Ty, fields: &[String], depth: usize) -> Result<(), Diagnostic> {
        if n.kind != JKind::Object {
            return Err(self.shape_err(n, t));
        }
        if let Some(k) = smallest_key(n.members.iter().map(|m| m.key.as_str()).filter(|k| !fields.iter().any(|f| f == k))) {
            return Err(Diagnostic::error("input-decode", "E-INPUT-UNKNOWN-FIELD", n.key_span(k)).act(k));
        }
        if let Some(f) = fields.iter().find(|f| n.get(f).is_none()) {
            return Err(Diagnostic::error("input-decode", "E-INPUT-MISSING-FIELD", n.close_span()).exp(f.as_str()));
        }
        let mut cur = t.unlabeled();
        for (i, f) in fields.iter().enumerate() {
            let v = n.get(f).unwrap();
            if i + 1 == fields.len() {
                self.value(v, &cur, depth + i)?;
            } else {
                self.admit(n, depth + i)?;
                self.out.push_str("{\"tag\":\"pair\",\"left\":");
                self.value(v, &cur.arg(0), depth + i + 1)?;
                self.out.push_str(",\"right\":");
                cur = cur.arg(1);
            }
        }
        for _ in 1..fields.len() {
            self.out.push('}');
        }
        Ok(())
    }

    /// v1.4：直和型は `{"Variant": [fields...]}`。値 JSON では ok／err の入れ子と、中身の pair の入れ子になる。
    fn sum(&mut self, n: &JNode, t: &Ty, variants: &[(String, usize)], depth: usize) -> Result<(), Diagnostic> {
        if n.kind != JKind::Object || n.members.len() != 1 {
            let act = if n.kind == JKind::Object { format!("object with {} keys", n.members.len()) } else { n.kind.name().to_string() };
            return Err(Diagnostic::error("input-decode", "E-INPUT-FIELD-TYPE", n.span()).exp(plain_shape(t)).act(act));
        }
        let key = &n.members[0].key;
        let Some(k) = variants.iter().position(|(v, _)| v == key) else {
            let names: Vec<&str> = variants.iter().map(|(v, _)| v.as_str()).collect();
            return Err(Diagnostic::error("input-decode", "E-INPUT-TAG", n.key_span(key)).exp(names.join(" | ")).act(key.clone()));
        };
        let arr = n.get(key).unwrap();
        let m = variants[k].1;
        if arr.kind != JKind::Array || arr.items.len() != m {
            let act = if arr.kind == JKind::Array { format!("array of {} elements", arr.items.len()) } else { arr.kind.name().to_string() };
            return Err(Diagnostic::error("input-decode", "E-INPUT-FIELD-TYPE", arr.span()).exp(format!("array of {m} elements")).act(act));
        }
        let nv = variants.len();
        let mut d = depth;
        let mut close = 0;
        if nv > 1 {
            for _ in 0..k {
                self.admit(n, d)?;
                self.out.push_str("{\"tag\":\"err\",\"value\":");
                d += 1;
                close += 1;
            }
            if k + 1 < nv {
                self.admit(n, d)?;
                self.out.push_str("{\"tag\":\"ok\",\"value\":");
                d += 1;
                close += 1;
            }
        }
        let payload = sum_payload(t, nv, k);
        if m == 0 {
            self.admit(n, d)?;
            self.out.push_str("{\"tag\":\"unit\"}");
        } else {
            let tys = payload_fields(&payload, m);
            for (i, (item, ty)) in arr.items.iter().zip(&tys).enumerate() {
                if i + 1 == m {
                    self.value(item, ty, d + i)?;
                } else {
                    self.admit(arr, d + i)?;
                    self.out.push_str("{\"tag\":\"pair\",\"left\":");
                    self.value(item, ty, d + i + 1)?;
                    self.out.push_str(",\"right\":");
                    close += 1;
                }
            }
        }
        for _ in 0..close {
            self.out.push('}');
        }
        Ok(())
    }

    fn value(&mut self, n: &JNode, t: &Ty, depth: usize) -> Result<(), Diagnostic> {
        if let Some(r) = t.record() {
            let fields = r.fields.clone();
            return self.record(n, t, &fields, depth);
        }
        if let Some(s) = t.sum() {
            let variants = s.variants.clone();
            return self.sum(n, t, &variants, depth);
        }
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
            TyTag::Char => {
                let mut cs = n.text.chars();
                let c = cs.next();
                if n.kind != JKind::String || c.is_none() || cs.next().is_some() {
                    let act = if n.kind == JKind::String { format!("string of {} chars", n.text.chars().count()) } else { n.kind.name().to_string() };
                    return Err(Diagnostic::error("input-decode", "E-INPUT-FIELD-TYPE", n.span()).exp(plain_shape(t)).act(act));
                }
                self.admit(n, depth)?;
                self.push_char(c.unwrap());
            }
            TyTag::List if t.is_string() => {
                // v1.2：String は JSON 文字列。値 JSON では char の list（各文字が値の node）
                if n.kind != JKind::String {
                    return Err(self.shape_err(n, t));
                }
                self.admit(n, depth)?;
                self.out.push_str("{\"tag\":\"list\",\"items\":[");
                for (i, c) in n.text.chars().enumerate() {
                    if i > 0 {
                        self.out.push(',');
                    }
                    self.admit(n, depth + 1)?;
                    self.push_char(c);
                }
                self.out.push_str("]}");
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
            TyTag::Dict => {
                // v1.9：`[[k, v], ...]`。値 JSON では pair のリスト。鍵は相異なる（正準の値 JSON で比べる）
                if n.kind != JKind::Array {
                    return Err(self.shape_err(n, t));
                }
                self.admit(n, depth)?;
                let mut keys = std::collections::HashSet::new();
                self.out.push_str("{\"tag\":\"list\",\"items\":[");
                for (i, c) in n.items.iter().enumerate() {
                    if i > 0 {
                        self.out.push(',');
                    }
                    if c.kind != JKind::Array || c.items.len() != 2 {
                        let act = if c.kind == JKind::Array { format!("array of {} elements", c.items.len()) } else { c.kind.name().to_string() };
                        return Err(Diagnostic::error("input-decode", "E-INPUT-FIELD-TYPE", c.span()).exp("[key, value]").act(act));
                    }
                    self.admit(c, depth + 1)?;
                    self.out.push_str("{\"tag\":\"pair\",\"left\":");
                    let at = self.out.len();
                    self.value(&c.items[0], &t.arg(0), depth + 2)?;
                    let key = self.out[at..].to_string();
                    if !keys.insert(key) {
                        let d = Diagnostic::error("input-decode", DICT_DUPLICATE_KEY, c.items[0].span());
                        return Err(if c.items[0].text.is_empty() { d } else { d.act(c.items[0].text.clone()) });
                    }
                    self.out.push_str(",\"right\":");
                    self.value(&c.items[1], &t.arg(1), depth + 2)?;
                    self.out.push('}');
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
            TyTag::Result => {
                if n.kind != JKind::Object {
                    return Err(self.shape_err(n, t));
                }
                let (key, inner) = if n.get("ok").is_some() {
                    ("ok", t.arg(0))
                } else if n.get("err").is_some() {
                    ("err", t.arg(1))
                } else {
                    return Err(Diagnostic::error("input-decode", "E-INPUT-MISSING-FIELD", n.close_span()).exp("ok | err"));
                };
                if let Some(k) = smallest_key(n.members.iter().map(|m| m.key.as_str()).filter(|k| *k != key)) {
                    return Err(Diagnostic::error("input-decode", "E-INPUT-UNKNOWN-FIELD", n.key_span(k)).act(k));
                }
                self.admit(n, depth)?;
                self.out.push_str(if key == "ok" { "{\"tag\":\"ok\",\"value\":" } else { "{\"tag\":\"err\",\"value\":" });
                self.value(n.get(key).unwrap(), &inner, depth + 1)?;
                self.out.push('}');
            }
            TyTag::Error => return Err(self.shape_err(n, t)),
        }
        Ok(())
    }
}

/// 正準十進表記の整数が |n| <= 2^53 - 1（JavaScript の安全な整数）か。
fn js_safe(dec: &str) -> bool {
    const MAX: &str = "9007199254740991";
    let digits = dec.strip_prefix('-').unwrap_or(dec);
    digits.len() < MAX.len() || (digits.len() == MAX.len() && digits <= MAX)
}

/// 値 JSON（処理系が出した正準出力）を型 `t` の plain JSON（最小空白）にする。
pub fn encode_plain(t: &Ty, canonical: &str) -> Result<String, String> {
    encode_plain_with(t, canonical, false)
}

/// `exact` なら整数を桁数によらず JSON number で出す（任意精度の整数を読めるホスト、たとえば Python 用）。
pub fn encode_plain_with(t: &Ty, canonical: &str, exact: bool) -> Result<String, String> {
    let root = parse(canonical.as_bytes(), usize::MAX).map_err(|f| format!("値 JSON を読めません（{:?}）", f.kind))?;
    let mut out = String::new();
    write_plain(&root, t, &mut out, exact)?;
    Ok(out)
}

/// 値 JSON の char の value（code point の十進）。
fn plain_char(v: &JNode) -> Result<char, String> {
    v.text.parse::<u32>().ok().and_then(char::from_u32).ok_or_else(|| format!("値 JSON の char {} が不正です", v.text))
}

fn write_plain(n: &JNode, t: &Ty, out: &mut String, exact: bool) -> Result<(), String> {
    if let Some(r) = t.record() {
        // v1.1：レコード型は field 名を key にした object（key は宣言順）
        out.push('{');
        let (mut node, mut cur) = (n, t.unlabeled());
        for (i, f) in r.fields.iter().enumerate() {
            if i > 0 {
                out.push(',');
            }
            out.push_str(&format!("\"{f}\":"));
            if i + 1 == r.fields.len() {
                write_plain(node, &cur, out, exact)?;
            } else {
                let get = |k: &str| node.get(k).ok_or_else(|| format!("値 JSON に {k} がありません"));
                write_plain(get("left")?, &cur.arg(0), out, exact)?;
                node = get("right")?;
                cur = cur.arg(1);
            }
        }
        out.push('}');
        return Ok(());
    }
    if let Some(s) = t.sum() {
        // v1.4：直和型は `{"Variant": [fields...]}`
        let nv = s.variants.len();
        let mut node = n;
        let mut k = 0;
        while nv > 1 && k + 1 < nv {
            let tag = node.get("tag").map(|x| x.text.as_str()).unwrap_or("");
            let v = node.get("value").ok_or("値 JSON に value がありません")?;
            node = v;
            if tag == "ok" {
                break;
            }
            k += 1;
        }
        let (name, m) = &s.variants[k];
        out.push('{');
        json_string(name, out);
        out.push_str(":[");
        let payload = sum_payload(t, nv, k);
        if *m > 0 {
            let tys = payload_fields(&payload, *m);
            for (i, ty) in tys.iter().enumerate() {
                if i > 0 {
                    out.push(',');
                }
                if i + 1 == *m {
                    write_plain(node, ty, out, exact)?;
                } else {
                    write_plain(node.get("left").ok_or("値 JSON に left がありません")?, ty, out, exact)?;
                    node = node.get("right").ok_or("値 JSON に right がありません")?;
                }
            }
        }
        out.push_str("]}");
        return Ok(());
    }
    let field = |k: &str| n.get(k).ok_or_else(|| format!("値 JSON に {k} がありません"));
    let tag = field("tag")?.text.as_str();
    match (t.tag(), tag) {
        (TyTag::Int, "int") => {
            let v = &field("value")?.text;
            if exact || js_safe(v) {
                out.push_str(v);
            } else {
                // JavaScript の number で正確に表せない整数は、入力でも受理する十進文字列にする
                out.push('"');
                out.push_str(v);
                out.push('"');
            }
        }
        (TyTag::Char, "char") => json_string(&plain_char(field("value")?)?.to_string(), out),
        (TyTag::List, "list") if t.is_string() => {
            let mut w = String::new();
            for c in field("items")?.items.iter() {
                w.push(plain_char(c.get("value").ok_or("値 JSON に value がありません")?)?);
            }
            json_string(&w, out);
        }
        (TyTag::Bool, "bool") => out.push_str(if field("value")?.boolean { "true" } else { "false" }),
        (TyTag::Unit, "unit") | (TyTag::Option, "none") => out.push_str("null"),
        (TyTag::List, "list") => {
            out.push('[');
            for (i, c) in field("items")?.items.iter().enumerate() {
                if i > 0 {
                    out.push(',');
                }
                write_plain(c, &t.arg(0), out, exact)?;
            }
            out.push(']');
        }
        // v1.9：辞書は `[[k, v], ...]`（挿入順）
        (TyTag::Dict, "list") => {
            let entry = Ty::pair(t.arg(0), t.arg(1));
            out.push('[');
            for (i, c) in field("items")?.items.iter().enumerate() {
                if i > 0 {
                    out.push(',');
                }
                write_plain(c, &entry, out, exact)?;
            }
            out.push(']');
        }
        (TyTag::Pair, "pair") => {
            out.push('[');
            write_plain(field("left")?, &t.arg(0), out, exact)?;
            out.push(',');
            write_plain(field("right")?, &t.arg(1), out, exact)?;
            out.push(']');
        }
        (TyTag::Result, "ok" | "err") => {
            out.push_str(if tag == "ok" { "{\"ok\":" } else { "{\"err\":" });
            write_plain(field("value")?, &t.arg(if tag == "ok" { 0 } else { 1 }), out, exact)?;
            out.push('}');
        }
        (TyTag::Option, "some") => {
            let inner = t.arg(0);
            if nullable(&inner) {
                out.push_str("{\"some\":");
                write_plain(field("value")?, &inner, out, exact)?;
                out.push('}');
            } else {
                write_plain(field("value")?, &inner, out, exact)?;
            }
        }
        _ => return Err(format!("値 JSON の tag {tag} が型 {t} と一致しません")),
    }
    Ok(())
}
