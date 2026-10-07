//! 字句解析と lexical-limits（設計書 §4.2、§18.1）。
//!
//! 入力は UTF-8 検査済みの bytes。span は bytes offset。lex は最初の error で停止する。

use crate::diagnostics::Diagnostic;
use crate::profiles::StaticProfile;
use crate::syntax::is_keyword;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum TokKind {
    Int,
    Ident,
    Kw,
    Punct,
    Eof,
}

#[derive(Clone, Debug)]
pub struct Token {
    pub kind: TokKind,
    pub text: String,
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
        ($kind:expr, $a:expr, $b:expr) => {{
            let t = Token { kind: $kind, text: text($a, $b), start: $a, end: $b };
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
    toks.push(Token { kind: TokKind::Eof, text: String::new(), start: n, end: n });
    Ok(toks)
}
