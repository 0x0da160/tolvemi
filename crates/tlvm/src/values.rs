//! 実行時の値と値 JSON codec（設計書 §3.2、§8.4、§9）。
//!
//! 値は有限木の意味を持つ不変 DAG。Unit／none／空リスト／bool は割当0の値として表す。
//! 深い値でもスタックを使い切らないよう、解放・encode・比較は反復で行う。

use crate::diagnostics::Diagnostic;
use crate::profiles::InputProfile;
use crate::strict_json::{parse, smallest_key, JKind, JNode, JsonFailKind};
use crate::syntax::{Ty, TyTag};
use num_bigint::BigInt;
use std::ops::Deref;
use std::sync::Arc;

pub enum Value {
    Int(BigInt),
    Bool(bool),
    Unit,
    None,
    Some(V),
    Pair(V, V),
    Nil,
    Cons(V, V),
}

/// 共有参照。Drop は反復で行う。
pub struct V(Option<Arc<Value>>);

impl V {
    pub fn new(v: Value) -> V {
        V(Some(Arc::new(v)))
    }
    pub fn ptr_eq(&self, other: &V) -> bool {
        Arc::ptr_eq(self.0.as_ref().unwrap(), other.0.as_ref().unwrap())
    }
}

impl Clone for V {
    fn clone(&self) -> V {
        V(self.0.clone())
    }
}

impl Deref for V {
    type Target = Value;
    fn deref(&self) -> &Value {
        self.0.as_ref().expect("live value")
    }
}

impl Drop for V {
    fn drop(&mut self) {
        let mut stack: Vec<Arc<Value>> = Vec::new();
        if let Some(rc) = self.0.take() {
            stack.push(rc);
        }
        while let Some(rc) = stack.pop() {
            if let Ok(v) = Arc::try_unwrap(rc) {
                match v {
                    Value::Some(mut a) => stack.extend(a.0.take()),
                    Value::Pair(mut a, mut b) | Value::Cons(mut a, mut b) => {
                        stack.extend(a.0.take());
                        stack.extend(b.0.take());
                    }
                    _ => {}
                }
            }
        }
    }
}

pub fn list_from(items: Vec<V>) -> V {
    let mut out = V::new(Value::Nil);
    for v in items.into_iter().rev() {
        out = V::new(Value::Cons(v, out));
    }
    out
}

pub fn list_items(v: &V) -> Vec<V> {
    let mut out = vec![];
    let mut cur = v.clone();
    loop {
        let next = match &*cur {
            Value::Cons(h, t) => {
                out.push(h.clone());
                t.clone()
            }
            _ => return out,
        };
        cur = next;
    }
}

// ---------------------------------------------------------------- encode

enum Piece<'a> {
    Val(&'a V),
    Lit(&'static str),
}

/// 正準 JSON（最小空白、正準 key 順）。
pub fn encode_value(v: &V) -> String {
    let mut out = String::new();
    let mut stack = vec![Piece::Val(v)];
    while let Some(p) = stack.pop() {
        let x = match p {
            Piece::Lit(s) => {
                out.push_str(s);
                continue;
            }
            Piece::Val(x) => x,
        };
        match &**x {
            Value::Int(n) => {
                out.push_str("{\"tag\":\"int\",\"value\":\"");
                out.push_str(&n.to_string());
                out.push_str("\"}");
            }
            Value::Bool(b) => out.push_str(if *b { "{\"tag\":\"bool\",\"value\":true}" } else { "{\"tag\":\"bool\",\"value\":false}" }),
            Value::Unit => out.push_str("{\"tag\":\"unit\"}"),
            Value::None => out.push_str("{\"tag\":\"none\"}"),
            Value::Some(a) => {
                out.push_str("{\"tag\":\"some\",\"value\":");
                stack.push(Piece::Lit("}"));
                stack.push(Piece::Val(a));
            }
            Value::Pair(a, b) => {
                out.push_str("{\"tag\":\"pair\",\"left\":");
                stack.push(Piece::Lit("}"));
                stack.push(Piece::Val(b));
                stack.push(Piece::Lit(",\"right\":"));
                stack.push(Piece::Val(a));
            }
            Value::Nil | Value::Cons(..) => {
                out.push_str("{\"tag\":\"list\",\"items\":[");
                let mut cells = vec![];
                let mut cur = x;
                while let Value::Cons(h, t) = &**cur {
                    cells.push(h);
                    cur = t;
                }
                stack.push(Piece::Lit("]}"));
                for (k, h) in cells.into_iter().enumerate().rev() {
                    stack.push(Piece::Val(h));
                    if k > 0 {
                        stack.push(Piece::Lit(","));
                    }
                }
            }
        }
    }
    out
}

// ---------------------------------------------------------------- decode

#[derive(Debug)]
pub enum DecodeResult {
    Decoded(TypedValue),
    Invalid(Vec<Diagnostic>),
    InputBoundaryFailure,
}

pub struct TypedValue {
    pub value: V,
    pub ty: Ty,
}

impl std::fmt::Debug for TypedValue {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "TypedValue({})", encode_value(&self.value))
    }
}

fn fields(tag: &str) -> &'static [(&'static str, JKind)] {
    match tag {
        "int" => &[("value", JKind::String)],
        "bool" => &[("value", JKind::Boolean)],
        "list" => &[("items", JKind::Array)],
        "some" => &[("value", JKind::Object)],
        "pair" => &[("left", JKind::Object), ("right", JKind::Object)],
        _ => &[],
    }
}

fn tags_for(t: &Ty) -> &'static [&'static str] {
    match t.tag() {
        TyTag::Int => &["int"],
        TyTag::Bool => &["bool"],
        TyTag::Unit => &["unit"],
        TyTag::List => &["list"],
        TyTag::Option => &["some", "none"],
        TyTag::Pair => &["pair"],
        TyTag::Error => &[],
    }
}

pub fn is_canonical_int(s: &str) -> bool {
    let d = s.strip_prefix('-').unwrap_or(s);
    if d.is_empty() || !d.bytes().all(|b| b.is_ascii_digit()) {
        return false;
    }
    if d == "0" {
        return !s.starts_with('-');
    }
    !d.starts_with('0')
}

pub fn decode_input(t_in: &Ty, data: &[u8], profile: &InputProfile) -> DecodeResult {
    if data.len() > profile.json_bytes {
        return DecodeResult::Invalid(vec![Diagnostic::error("input-boundary", "E-LIMIT-INPUT-JSON-BYTES", (0, 0))
            .exp(profile.json_bytes.to_string())
            .act(data.len().to_string())]);
    }
    if std::str::from_utf8(data).is_err() {
        return DecodeResult::InputBoundaryFailure;
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
            return DecodeResult::Invalid(vec![Diagnostic::error("input-parse", code, f.span)]);
        }
    };
    let mut dec = Decoder { p: profile, nodes: 0 };
    match dec.value(&root, t_in, 1) {
        Ok(value) => DecodeResult::Decoded(TypedValue { value, ty: t_in.clone() }),
        Err(d) => DecodeResult::Invalid(vec![d]),
    }
}

struct Decoder<'a> {
    p: &'a InputProfile,
    nodes: usize,
}

impl Decoder<'_> {
    fn fail<T>(&self, code: &'static str, span: (usize, usize)) -> Result<T, Diagnostic> {
        Err(Diagnostic::error("input-decode", code, span))
    }

    fn value(&mut self, n: &JNode, t: &Ty, depth: usize) -> Result<V, Diagnostic> {
        // 1. object であること
        if n.kind != JKind::Object {
            return Err(Diagnostic::error("input-decode", "E-INPUT-FIELD-TYPE", n.span()).exp("object").act(n.kind.name()));
        }
        // 2. tag
        let tag_node = match n.get("tag") {
            Some(t) => t,
            None => return Err(Diagnostic::error("input-decode", "E-INPUT-MISSING-FIELD", n.close_span()).exp("tag")),
        };
        let allowed = tags_for(t);
        if tag_node.kind != JKind::String || !allowed.contains(&tag_node.text.as_str()) {
            return Err(Diagnostic::error("input-decode", "E-INPUT-TAG", tag_node.span()).exp(allowed.join(" | ")).act(t.to_string()));
        }
        let tag = tag_node.text.as_str();
        let fs = fields(tag);
        // 3. 必須キー → 余分キー
        for (k, _) in fs {
            if n.get(k).is_none() {
                return Err(Diagnostic::error("input-decode", "E-INPUT-MISSING-FIELD", n.close_span()).exp(*k));
            }
        }
        let extra = smallest_key(n.members.iter().map(|m| m.key.as_str()).filter(|k| *k != "tag" && !fs.iter().any(|(f, _)| f == k)));
        if let Some(k) = extra {
            return Err(Diagnostic::error("input-decode", "E-INPUT-UNKNOWN-FIELD", n.key_span(k)).act(k));
        }
        // 4. 浅い JSON 型（正準 key 順）
        for (k, kind) in fs {
            let c = n.get(k).unwrap();
            if c.kind != *kind {
                return Err(Diagnostic::error("input-decode", "E-INPUT-FIELD-TYPE", c.span()).exp(kind.name()).act(c.kind.name()));
            }
        }
        // 5. InputAdmission（深さ超過を優先）
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
        // 6. 内容
        Ok(match tag {
            "int" => {
                let s = n.get("value").unwrap();
                if !is_canonical_int(&s.text) {
                    return self.fail("E-INPUT-INTEGER", s.span());
                }
                let digits = s.text.trim_start_matches('-').len();
                if digits > self.p.integer_digits {
                    return Err(Diagnostic::error("input-decode", "E-LIMIT-INPUT-INTEGER-DIGITS", s.span())
                        .exp(self.p.integer_digits.to_string())
                        .act(digits.to_string()));
                }
                V::new(Value::Int(s.text.parse().unwrap()))
            }
            "bool" => V::new(Value::Bool(n.get("value").unwrap().boolean)),
            "unit" => V::new(Value::Unit),
            "none" => V::new(Value::None),
            "some" => V::new(Value::Some(self.value(n.get("value").unwrap(), &t.arg(0), depth + 1)?)),
            "pair" => {
                let l = self.value(n.get("left").unwrap(), &t.arg(0), depth + 1)?;
                let r = self.value(n.get("right").unwrap(), &t.arg(1), depth + 1)?;
                V::new(Value::Pair(l, r))
            }
            _ => {
                let el = t.arg(0);
                let mut items = vec![];
                for c in &n.get("items").unwrap().items {
                    items.push(self.value(c, &el, depth + 1)?);
                }
                list_from(items)
            }
        })
    }
}
