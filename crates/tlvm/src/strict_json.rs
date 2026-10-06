//! strict JSON transport（設計書 §9.3a、§19.3）。
//!
//! 段階順：JSON 文法／構造深さ → string scalar 妥当性 → 重複キー。
//! 各段階が全体で成功した場合だけ次の段階へ進む。span は元 bytes 上の offset。

use std::collections::HashSet;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum JKind {
    Object,
    Array,
    String,
    Number,
    Boolean,
    Null,
}

impl JKind {
    pub fn name(self) -> &'static str {
        match self {
            JKind::Object => "object",
            JKind::Array => "array",
            JKind::String => "string",
            JKind::Number => "number",
            JKind::Boolean => "boolean",
            JKind::Null => "null",
        }
    }
}

#[derive(Clone, Debug)]
pub struct Member {
    pub key: String,
    pub key_span: (usize, usize),
    pub value: JNode,
}

#[derive(Clone, Debug)]
pub struct JNode {
    pub kind: JKind,
    pub start: usize,
    pub end: usize,
    /// string の decode 後の値、number の字面
    pub text: String,
    pub boolean: bool,
    pub members: Vec<Member>,
    pub items: Vec<JNode>,
}

impl JNode {
    fn new(kind: JKind, start: usize) -> JNode {
        JNode { kind, start, end: start, text: String::new(), boolean: false, members: vec![], items: vec![] }
    }
    pub fn span(&self) -> (usize, usize) {
        (self.start, self.end)
    }
    pub fn get(&self, key: &str) -> Option<&JNode> {
        self.members.iter().find(|m| m.key == key).map(|m| &m.value)
    }
    pub fn key_span(&self, key: &str) -> (usize, usize) {
        self.members.iter().find(|m| m.key == key).map(|m| m.key_span).expect("key present")
    }
    /// object 閉じ括弧直前のゼロ幅位置
    pub fn close_span(&self) -> (usize, usize) {
        (self.end - 1, self.end - 1)
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum JsonFailKind {
    Syntax,
    Depth,
    Scalar,
    Duplicate,
}

#[derive(Debug)]
pub struct JsonFailure {
    pub kind: JsonFailKind,
    pub span: (usize, usize),
}

struct P<'a> {
    d: &'a [u8],
    i: usize,
    max_depth: usize,
    scalar: Option<(usize, usize)>,
}

type R<T> = Result<T, JsonFailure>;

impl<'a> P<'a> {
    fn fail<T>(&self, at: usize) -> R<T> {
        let end = if at >= self.d.len() { at } else { at + 1 };
        Err(JsonFailure { kind: JsonFailKind::Syntax, span: (at, end) })
    }

    fn ws(&mut self) {
        while self.i < self.d.len() && matches!(self.d[self.i], b' ' | b'\t' | b'\n' | b'\r') {
            self.i += 1;
        }
    }

    fn peek(&self) -> Option<u8> {
        self.d.get(self.i).copied()
    }

    fn value(&mut self, depth: usize) -> R<JNode> {
        self.ws();
        let c = match self.peek() {
            Some(c) => c,
            None => return self.fail(self.i),
        };
        match c {
            b'{' | b'[' => {
                if depth + 1 > self.max_depth {
                    return Err(JsonFailure { kind: JsonFailKind::Depth, span: (self.i, self.i + 1) });
                }
                if c == b'{' {
                    self.object(depth + 1)
                } else {
                    self.array(depth + 1)
                }
            }
            b'"' => self.string(),
            b'-' | b'0'..=b'9' => self.number(),
            _ => {
                for (lit, kind, b) in [(&b"true"[..], JKind::Boolean, true), (b"false", JKind::Boolean, false), (b"null", JKind::Null, false)] {
                    if self.d[self.i..].starts_with(lit) {
                        let mut n = JNode::new(kind, self.i);
                        n.boolean = b;
                        self.i += lit.len();
                        n.end = self.i;
                        return Ok(n);
                    }
                }
                self.fail(self.i)
            }
        }
    }

    fn object(&mut self, depth: usize) -> R<JNode> {
        let mut node = JNode::new(JKind::Object, self.i);
        self.i += 1;
        self.ws();
        if self.peek() == Some(b'}') {
            self.i += 1;
            node.end = self.i;
            return Ok(node);
        }
        loop {
            self.ws();
            if self.peek() != Some(b'"') {
                return self.fail(self.i);
            }
            let key = self.string()?;
            self.ws();
            if self.peek() != Some(b':') {
                return self.fail(self.i);
            }
            self.i += 1;
            let v = self.value(depth)?;
            node.members.push(Member { key: key.text, key_span: (key.start, key.end), value: v });
            self.ws();
            match self.peek() {
                Some(b',') => self.i += 1,
                Some(b'}') => {
                    self.i += 1;
                    node.end = self.i;
                    return Ok(node);
                }
                _ => return self.fail(self.i),
            }
        }
    }

    fn array(&mut self, depth: usize) -> R<JNode> {
        let mut node = JNode::new(JKind::Array, self.i);
        self.i += 1;
        self.ws();
        if self.peek() == Some(b']') {
            self.i += 1;
            node.end = self.i;
            return Ok(node);
        }
        loop {
            node.items.push(self.value(depth)?);
            self.ws();
            match self.peek() {
                Some(b',') => self.i += 1,
                Some(b']') => {
                    self.i += 1;
                    node.end = self.i;
                    return Ok(node);
                }
                _ => return self.fail(self.i),
            }
        }
    }

    fn digits(&mut self) -> R<()> {
        if !matches!(self.peek(), Some(b'0'..=b'9')) {
            return self.fail(self.i);
        }
        while matches!(self.peek(), Some(b'0'..=b'9')) {
            self.i += 1;
        }
        Ok(())
    }

    fn number(&mut self) -> R<JNode> {
        let mut node = JNode::new(JKind::Number, self.i);
        if self.peek() == Some(b'-') {
            self.i += 1;
        }
        match self.peek() {
            Some(b'0') => self.i += 1,
            Some(b'1'..=b'9') => self.digits()?,
            _ => return self.fail(self.i),
        }
        if self.peek() == Some(b'.') {
            self.i += 1;
            self.digits()?;
        }
        if matches!(self.peek(), Some(b'e' | b'E')) {
            self.i += 1;
            if matches!(self.peek(), Some(b'+' | b'-')) {
                self.i += 1;
            }
            self.digits()?;
        }
        node.end = self.i;
        node.text = String::from_utf8_lossy(&self.d[node.start..node.end]).into_owned();
        Ok(node)
    }

    fn hex4(&self, at: usize) -> R<u32> {
        let mut v = 0u32;
        for k in 0..4 {
            match self.d.get(at + k).and_then(|b| (*b as char).to_digit(16)) {
                Some(h) => v = v * 16 + h,
                None => return self.fail(at + k),
            }
        }
        Ok(v)
    }

    fn string(&mut self) -> R<JNode> {
        let mut node = JNode::new(JKind::String, self.i);
        self.i += 1;
        let mut out = String::new();
        let mut bad = false;
        loop {
            let c = match self.peek() {
                Some(c) => c,
                None => return self.fail(self.i),
            };
            if c == b'"' {
                self.i += 1;
                break;
            }
            if c < 0x20 {
                return self.fail(self.i);
            }
            if c == b'\\' {
                let e = match self.d.get(self.i + 1) {
                    Some(e) => *e,
                    None => return self.fail(self.i + 1),
                };
                let simple = match e {
                    b'"' => Some('"'),
                    b'\\' => Some('\\'),
                    b'/' => Some('/'),
                    b'b' => Some('\u{8}'),
                    b'f' => Some('\u{c}'),
                    b'n' => Some('\n'),
                    b'r' => Some('\r'),
                    b't' => Some('\t'),
                    _ => None,
                };
                if let Some(ch) = simple {
                    out.push(ch);
                    self.i += 2;
                    continue;
                }
                if e != b'u' {
                    return self.fail(self.i + 1);
                }
                let cu = self.hex4(self.i + 2)?;
                self.i += 6;
                if (0xD800..=0xDBFF).contains(&cu) {
                    if self.d.get(self.i) == Some(&b'\\') && self.d.get(self.i + 1) == Some(&b'u') {
                        let lo = self.hex4(self.i + 2)?;
                        if (0xDC00..=0xDFFF).contains(&lo) {
                            self.i += 6;
                            out.push(char::from_u32(0x10000 + ((cu - 0xD800) << 10) + (lo - 0xDC00)).unwrap());
                            continue;
                        }
                    }
                    bad = true;
                    continue;
                }
                match char::from_u32(cu) {
                    Some(ch) => out.push(ch),
                    None => bad = true,
                }
                continue;
            }
            let len = if c < 0x80 {
                1
            } else if c < 0xE0 {
                2
            } else if c < 0xF0 {
                3
            } else {
                4
            };
            out.push_str(std::str::from_utf8(&self.d[self.i..self.i + len]).expect("validated UTF-8"));
            self.i += len;
        }
        node.end = self.i;
        node.text = out;
        if bad && self.scalar.is_none() {
            self.scalar = Some((node.start, node.end));
        }
        Ok(node)
    }
}

/// UTF-8 検査済みの bytes を strict に解析する。
pub fn parse(data: &[u8], max_depth: usize) -> Result<JNode, JsonFailure> {
    let mut p = P { d: data, i: 0, max_depth, scalar: None };
    let root = p.value(0)?;
    p.ws();
    if p.i != data.len() {
        return p.fail(p.i);
    }
    if let Some(span) = p.scalar {
        return Err(JsonFailure { kind: JsonFailKind::Scalar, span });
    }
    if let Some(span) = first_duplicate(&root) {
        return Err(JsonFailure { kind: JsonFailKind::Duplicate, span });
    }
    Ok(root)
}

fn first_duplicate(root: &JNode) -> Option<(usize, usize)> {
    let mut best: Option<(usize, usize)> = None;
    let mut stack = vec![root];
    while let Some(n) = stack.pop() {
        let mut seen = HashSet::new();
        for m in &n.members {
            if !seen.insert(m.key.as_str()) && best.is_none_or(|b| m.key_span.0 < b.0) {
                best = Some(m.key_span);
            }
            stack.push(&m.value);
        }
        stack.extend(n.items.iter());
    }
    best
}

/// unknown key の辞書順（scalar 整数値列の辞書順）。Rust の `str` 比較は scalar 順と一致する。
pub fn smallest_key<'a>(keys: impl Iterator<Item = &'a str>) -> Option<&'a str> {
    keys.min_by(|a, b| a.chars().cmp(b.chars()))
}
