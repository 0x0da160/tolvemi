//! 字句解析と lexical-limits（設計書 §4.2、§18.1）。
//!
//! 入力は UTF-8 検査済みの bytes。span は bytes offset。lex は最初の error で停止する。
//!
//! v1.2：文字リテラル `'c'` と文字列リテラル `"..."`。リテラルの中では非 ASCII 文字を書ける。
//! エスケープは `\\`、区切りの引用符（`\'` か `\"`）、`\n`、`\t`、`\r` だけで、生の制御文字は書けない
//! （検証済み lexer の `slit`、`unesc`、`lex` と同じ規則）。

use crate::diagnostics::Diagnostic;
use crate::profiles::StaticProfile;
use crate::syntax::is_keyword;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum TokKind {
    Int,
    /// v1.2：文字リテラル（`lit` が復号した 1 文字）
    Char,
    /// v1.2：文字列リテラル（`lit` が復号した中身）
    Str,
    Ident,
    Kw,
    Punct,
    Eof,
}

#[derive(Clone, Debug)]
pub struct Token {
    pub kind: TokKind,
    /// source 上の綴り
    pub text: String,
    /// 文字・文字列リテラルの復号した中身（それ以外は空）
    pub lit: String,
    pub start: usize,
    pub end: usize,
}

impl Token {
    pub fn span(&self) -> (usize, usize) {
        (self.start, self.end)
    }
    pub fn describe(&self) -> String {
        if self.kind == TokKind::Eof {
            "EOF".to_string()
        } else {
            self.text.clone()
        }
    }
    pub fn is_kw(&self, s: &str) -> bool {
        self.kind == TokKind::Kw && self.text == s
    }
    pub fn is_punct(&self, s: &str) -> bool {
        self.kind == TokKind::Punct && self.text == s
    }
}

fn ident_start(b: u8) -> bool {
    b.is_ascii_alphabetic() || b == b'_'
}

fn ident_char(b: u8) -> bool {
    b.is_ascii_alphanumeric() || b == b'_'
}

/// エスケープ `\x` が表す文字（q は区切りの引用符）。検証済み lexer の `unesc`。
pub fn unescape(x: char, q: char) -> Option<char> {
    match x {
        '\\' => Some('\\'),
        'n' => Some('\n'),
        't' => Some('\t'),
        'r' => Some('\r'),
        _ if x == q => Some(q),
        _ => None,
    }
}

/// 正準形での 1 文字の綴り（q は区切りの引用符）。検証済み formatter の `esc`。
pub fn escape_into(out: &mut String, c: char, q: char) {
    match c {
        '\\' => out.push_str("\\\\"),
        '\n' => out.push_str("\\n"),
        '\t' => out.push_str("\\t"),
        '\r' => out.push_str("\\r"),
        _ if c == q => {
            out.push('\\');
            out.push(q);
        }
        _ => out.push(c),
    }
}

/// 正準形のリテラル（引用符を含む）。
pub fn quote(s: &str, q: char) -> String {
    let mut out = String::new();
    out.push(q);
    for c in s.chars() {
        escape_into(&mut out, c, q);
    }
    out.push(q);
    out
}

/// 位置 i の文字（UTF-8 検査済み）と、その次の位置。
fn char_at(src: &[u8], i: usize) -> Option<(char, usize)> {
    if i >= src.len() {
        return None;
    }
    let end = (i + utf8_len(src[i])).min(src.len());
    std::str::from_utf8(&src[i..end]).ok().and_then(|s| s.chars().next()).map(|c| (c, end))
}

fn control_char(c: char, at: usize, end: usize) -> Diagnostic {
    Diagnostic::error("lex", "E-LEX-CONTROL-CHAR-IN-LITERAL", (at, end)).act(format!("U+{:04X}", c as u32))
}

/// 文字リテラル（src[i] は `'`）。成功なら（文字, 閉じ引用符の次の位置）。
fn char_literal(src: &[u8], i: usize) -> Result<(char, usize), Diagnostic> {
    let bad = |end: usize| Diagnostic::error("lex", "E-LEX-INVALID-CHAR-LITERAL", (i, end));
    let Some((c1, j)) = char_at(src, i + 1) else {
        return Err(bad(i + 1));
    };
    let (c, k) = match c1 {
        '\'' => return Err(bad(j).act("''")),
        '\\' => {
            let Some((x, k)) = char_at(src, j) else {
                return Err(bad(j));
            };
            match unescape(x, '\'') {
                Some(c) => (c, k),
                None => {
                    return Err(Diagnostic::error("lex", "E-LEX-INVALID-ESCAPE", (i + 1, k)).act(format!("\\{x}")));
                }
            }
        }
        _ if (c1 as u32) < 0x20 => return Err(control_char(c1, i + 1, j)),
        _ => (c1, j),
    };
    match char_at(src, k) {
        Some(('\'', end)) => Ok((c, end)),
        _ => {
            // 閉じ引用符が同じ行のもっと先にあれば（`'ab'` など）そこまでを示す
            let mut e = k;
            while e < src.len() && !matches!(src[e], b'\'' | b'\n' | b'\r') {
                e += 1;
            }
            let end = if e < src.len() && src[e] == b'\'' { e + 1 } else { k };
            Err(bad(end).act(String::from_utf8_lossy(&src[i..end]).into_owned()))
        }
    }
}

/// 文字列リテラル（src[i] は `"`）。成功なら（中身, 閉じ引用符の次の位置）。
fn string_literal(src: &[u8], i: usize) -> Result<(String, usize), Diagnostic> {
    let unterminated = |end: usize| Diagnostic::error("lex", "E-LEX-UNTERMINATED-STRING", (i, end));
    let mut out = String::new();
    let mut j = i + 1;
    loop {
        let Some((c, k)) = char_at(src, j) else {
            return Err(unterminated(src.len()));
        };
        match c {
            '"' => return Ok((out, k)),
            '\\' => {
                let Some((x, m)) = char_at(src, k) else {
                    return Err(unterminated(src.len()));
                };
                match unescape(x, '"') {
                    Some(e) => out.push(e),
                    None => {
                        return Err(Diagnostic::error("lex", "E-LEX-INVALID-ESCAPE", (j, m)).act(format!("\\{x}")));
                    }
                }
                j = m;
            }
            // 行末までに閉じていない
            '\n' | '\r' => return Err(unterminated(j)),
            _ if (c as u32) < 0x20 => return Err(control_char(c, j, k)),
            _ => {
                out.push(c);
                j = k;
            }
        }
    }
}

fn utf8_len(b: u8) -> usize {
    if b >= 0xF0 {
        4
    } else if b >= 0xE0 {
        3
    } else if b >= 0xC0 {
        2
    } else {
        1
    }
}

/// token 列（末尾に EOF）を返す。失敗時は最初の診断を返す。
pub fn lex(src: &[u8], profile: &StaticProfile) -> Result<Vec<Token>, Diagnostic> {
    let n = src.len();
    let mut toks: Vec<Token> = Vec::new();
    let mut i = 0;
    let text = |a: usize, b: usize| String::from_utf8_lossy(&src[a..b]).into_owned();
    macro_rules! push {
        ($kind:expr, $a:expr, $b:expr) => {
            push!($kind, $a, $b, String::new())
        };
        ($kind:expr, $a:expr, $b:expr, $lit:expr) => {{
            let t = Token { kind: $kind, text: text($a, $b), lit: $lit, start: $a, end: $b };
            toks.push(t);
            if toks.len() > profile.tokens {
                return Err(Diagnostic::error("lexical-limits", "E-LIMIT-STATIC-TOKENS", ($a, $b))
                    .exp(profile.tokens.to_string())
                    .act(toks.len().to_string()));
            }
        }};
    }
    while i < n {
        let b = src[i];
        if matches!(b, b' ' | b'\t' | b'\r' | b'\n') {
            i += 1;
            continue;
        }
        if b == b'/' {
            if i + 1 < n && src[i + 1] == b'/' {
                i += 2;
                while i < n && src[i] != b'\n' && src[i] != b'\r' {
                    i += 1;
                }
                continue;
            }
            return Err(Diagnostic::error("lex", "E-LEX-UNEXPECTED-CHARACTER", (i, i + 1)).act("/"));
        }
        if b == b'\'' {
            let (c, j) = char_literal(src, i)?;
            push!(TokKind::Char, i, j, c.to_string());
            i = j;
            continue;
        }
        if b == b'"' {
            let (w, j) = string_literal(src, i)?;
            push!(TokKind::Str, i, j, w);
            i = j;
            continue;
        }
        if b >= 0x80 {
            return Err(Diagnostic::error("lex", "E-LEX-NON-ASCII", (i, n.min(i + utf8_len(b)))));
        }
        if ident_start(b) {
            let mut j = i + 1;
            while j < n && ident_char(src[j]) {
                j += 1;
            }
            let kind = if is_keyword(&text(i, j)) { TokKind::Kw } else { TokKind::Ident };
            push!(kind, i, j);
            i = j;
            continue;
        }
        let signed = (b == b'-' || b == b'+') && i + 1 < n && src[i + 1].is_ascii_digit();
        if b.is_ascii_digit() || signed {
            let start = i;
            let d0 = if signed { i + 1 } else { i };
            let mut j = d0;
            while j < n && src[j].is_ascii_digit() {
                j += 1;
            }
            // 正規形・数値境界を桁上限より先に判定する（§18.1）
            if b == b'+' || (src[d0] == b'0' && (j - d0 > 1 || b == b'-')) {
                return Err(Diagnostic::error("lex", "E-LEX-INVALID-INTEGER", (start, j)).act(text(start, j)));
            }
            if j < n && (ident_start(src[j]) || src[j] == b'-' || src[j] == b'.') {
                let mut k = j + 1;
                while k < n && ident_char(src[k]) {
                    k += 1;
                }
                return Err(Diagnostic::error("lex", "E-LEX-INVALID-NUMERIC-BOUNDARY", (start, k)));
            }
            if j - d0 > profile.integer_digits {
                return Err(Diagnostic::error("lexical-limits", "E-LIMIT-STATIC-INTEGER-DIGITS", (start, j))
                    .exp(profile.integer_digits.to_string())
                    .act((j - d0).to_string()));
            }
            push!(TokKind::Int, start, j);
            i = j;
            continue;
        }
        if b == b'-' {
            if i + 1 < n && src[i + 1] == b'>' {
                push!(TokKind::Punct, i, i + 2);
                i += 2;
                continue;
            }
            return Err(Diagnostic::error("lex", "E-LEX-UNEXPECTED-CHARACTER", (i, i + 1)).act("-"));
        }
        if b"()[]<>,:=|.{}".contains(&b) {
            push!(TokKind::Punct, i, i + 1);
            i += 1;
            continue;
        }
        return Err(Diagnostic::error("lex", "E-LEX-UNEXPECTED-CHARACTER", (i, i + 1)).act(format!("{:?}", b as char)));
    }
    toks.push(Token { kind: TokKind::Eof, text: String::new(), lit: String::new(), start: n, end: n });
    Ok(toks)
}
