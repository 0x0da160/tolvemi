//! 構文解析、parse Admission、bounded recovery（設計書 §4.1、§10.3、§18.1b）。

use crate::diagnostics::{Diagnostic, Span};
use crate::lexer::{TokKind, Token};
use crate::profiles::StaticProfile;
use crate::softnames::is_soft_keyword;
use crate::syntax::*;
use num_bigint::BigInt;

pub const MAX_SYNCS: usize = 8;

/// parse-admission-v1 の論理計数。Surface と AST API で共有する。
pub struct Admission {
    profile: StaticProfile,
    pub ast_nodes: usize,
    pub functions: usize,
    pub index: usize,
}

#[derive(Default, Clone, Copy)]
pub struct Depths {
    pub fn_: bool,
    pub ty: Option<usize>,
    pub expr: Option<usize>,
    pub let_: Option<usize>,
    pub fold: Option<usize>,
}

impl Admission {
    pub fn new(profile: &StaticProfile) -> Admission {
        Admission { profile: profile.clone(), ast_nodes: 0, functions: 0, index: 0 }
    }

    /// guard 超過時は structural-limits の cutoff 診断を返す。
    pub fn admit(&mut self, span: Span, d: Depths) -> Result<usize, Diagnostic> {
        let p = &self.profile;
        let violation = if d.fn_ && self.functions + 1 > p.functions {
            Some(("E-LIMIT-STATIC-FUNCTIONS", p.functions, self.functions + 1))
        } else if self.ast_nodes + 1 > p.ast_nodes {
            Some(("E-LIMIT-STATIC-AST-NODES", p.ast_nodes, self.ast_nodes + 1))
        } else if let Some(x) = d.ty.filter(|x| *x > p.type_depth) {
            Some(("E-LIMIT-STATIC-TYPE-DEPTH", p.type_depth, x))
        } else if let Some(x) = d.expr.filter(|x| *x > p.expr_depth) {
            Some(("E-LIMIT-STATIC-EXPR-DEPTH", p.expr_depth, x))
        } else if let Some(x) = d.let_.filter(|x| *x > p.let_depth) {
            Some(("E-LIMIT-STATIC-LET-DEPTH", p.let_depth, x))
        } else if let Some(x) = d.fold.filter(|x| *x > p.fold_depth) {
            Some(("E-LIMIT-STATIC-FOLD-DEPTH", p.fold_depth, x))
        } else {
            None
        };
        if let Some((code, limit, observed)) = violation {
            return Err(Diagnostic::error("structural-limits", code, span)
                .exp(limit.to_string())
                .act(observed.to_string())
                .at(self.index));
        }
        self.ast_nodes += 1;
        if d.fn_ {
            self.functions += 1;
        }
        self.index += 1;
        Ok(self.index - 1)
    }
}

/// v1.1：宣言の先頭の `type` は文脈上のキーワード（予約語ではないので、v1 の名前 `type` はそのまま使える）。
fn is_type_kw(t: &Token) -> bool {
    t.kind == TokKind::Ident && t.text == "type"
}

/// v1.7：宣言の先頭の `rec` で、直後が `fn`（印）か `entry`（E-PARSE-REC-ENTRY）か。
/// `rec` は予約語ではないので、それ以外の位置では普通の名前。
fn is_rec_at(toks: &[Token], i: usize) -> bool {
    let t = &toks[i];
    t.kind == TokKind::Ident
        && t.text == REC
        && toks.get(i + 1).is_some_and(|n| n.is_kw("fn") || n.is_kw("entry"))
}

pub const CTOR_EXPECTED: &str = "constructor name starting with an uppercase letter";
pub const PATTERN_EXPECTED: &str = "pattern: Ctor, Ctor(x, ...), ok(x), err(e), some(x), none or _";
/// v1.5：`map(xs, ...)` などの第 2 引数にラムダがない
pub const LAMBDA_EXPECTED: &str = "|x| e";
/// v1.5：ラムダの binder が一つでない（`|acc, x|`、`||` など）
pub const LAMBDA_ONE_BINDER: &str = "exactly one binder: |x|";
/// v1.6：`loop(init, max, ...)` の第 3 引数にラムダがない
pub const LOOP_LAMBDA_EXPECTED: &str = "|s| e";
/// v1.6：`loop` のラムダの binder が一つでない
pub const LOOP_ONE_BINDER: &str = "exactly one binder: |s|";

pub fn expr_depths(expr: usize) -> Depths {
    Depths { expr: Some(expr), ..Default::default() }
}

enum Fail {
    /// `at`：token の span の代わりに示す span と actual（`List<Char>` など複数 token にわたる誤り）
    Parse { code: &'static str, index: usize, expected: Option<&'static str>, at: Option<(Span, String)> },
    Cutoff(Diagnostic),
}

impl From<Diagnostic> for Fail {
    fn from(d: Diagnostic) -> Fail {
        Fail::Cutoff(d)
    }
}

type R<T> = Result<T, Fail>;

pub struct Parser {
    toks: Vec<Token>,
    pos: usize,
    pub adm: Admission,
    pub diags: Vec<Diagnostic>,
    prev_end: usize,
    /// v1.4：`match` の対象の先頭 token の位置。そこでは `Name {` をレコードの構築として読まない
    no_record_at: Option<usize>,
}

pub enum ParseOutcome {
    Ok(Program),
    /// parse error のみ（recovery 済み）。
    Errors(Vec<Diagnostic>),
    /// structural cutoff（それまでの parse error を含む）。
    Cutoff(Vec<Diagnostic>),
}

impl Parser {
    pub fn new(toks: Vec<Token>, profile: &StaticProfile) -> Parser {
        Parser { toks, pos: 0, adm: Admission::new(profile), diags: vec![], prev_end: 0, no_record_at: None }
    }

    fn peek(&self, k: usize) -> &Token {
        &self.toks[(self.pos + k).min(self.toks.len() - 1)]
    }

    fn advance(&mut self) -> Token {
        let t = self.toks[self.pos].clone();
        if t.kind != TokKind::Eof {
            self.pos += 1;
            self.prev_end = t.end;
        }
        t
    }

    fn perr<T>(&self, code: &'static str, expected: &'static str) -> R<T> {
        Err(Fail::Parse { code, index: self.pos, expected: Some(expected), at: None })
    }

    fn expect(&mut self, s: &'static str) -> R<Token> {
        let t = self.peek(0);
        if t.is_punct(s) || t.is_kw(s) {
            Ok(self.advance())
        } else {
            self.perr("E-PARSE-EXPECTED-TOKEN", s)
        }
    }

    fn expect_ident(&mut self) -> R<Token> {
        if self.peek(0).kind == TokKind::Ident {
            Ok(self.advance())
        } else {
            self.perr("E-PARSE-EXPECTED-IDENT", "identifier")
        }
    }

    /// 変数・引数・束縛・field の名前。組み込み関数と値の構築子の名前（文脈キーワード）も使える。
    fn expect_binder(&mut self) -> R<Token> {
        if self.at_binder(0) {
            Ok(self.advance())
        } else {
            self.perr("E-PARSE-EXPECTED-IDENT", "identifier")
        }
    }

    fn at_binder(&self, k: usize) -> bool {
        let t = self.peek(k);
        t.kind == TokKind::Ident || (t.kind == TokKind::Kw && is_soft_keyword(&t.text))
    }

    fn emit(&mut self, code: &'static str, index: usize, expected: Option<&'static str>) {
        let tok = &self.toks[index];
        let mut d = Diagnostic::error("parse", code, tok.span()).act(tok.describe()).at(self.adm.index);
        if let Some(e) = expected {
            d.expected = Some(e.to_string());
        }
        d.seq = self.diags.len();
        self.diags.push(d);
    }

    fn at_decl_end(&self) -> bool {
        let t = self.peek(0);
        t.kind == TokKind::Eof || t.is_kw("fn") || t.is_kw("entry") || is_type_kw(t) || is_rec_at(&self.toks, self.pos)
    }

    fn is_sync(&self, i: usize) -> bool {
        let t = &self.toks[i];
        t.kind == TokKind::Eof || t.is_kw("fn") || t.is_kw("entry") || is_type_kw(t) || is_rec_at(&self.toks, i)
    }

    pub fn parse_program(mut self) -> ParseOutcome {
        let prog_idx = match self.adm.admit((0, 0), Depths::default()) {
            Ok(i) => i,
            Err(d) => return ParseOutcome::Cutoff(vec![d]),
        };
        let mut decls = vec![];
        let mut syncs = 0;
        loop {
            let s = self.pos;
            if self.peek(0).kind == TokKind::Eof {
                break;
            }
            let r = if self.peek(0).is_kw("fn") {
                self.parse_fn().map(Decl::Fn)
            } else if is_rec_at(&self.toks, self.pos) {
                // v1.7：`rec fn`。`rec entry` は書けない
                if self.peek(1).is_kw("entry") {
                    Err(Fail::Parse { code: "E-PARSE-REC-ENTRY", index: self.pos, expected: Some("fn"), at: None })
                } else {
                    let m = self.advance();
                    self.parse_fn().map(|mut f| {
                        f.rec = true;
                        f.rec_span = Sp(m.start, m.end);
                        Decl::Fn(f)
                    })
                }
            } else if self.peek(0).is_kw("entry") {
                self.parse_entry().map(Decl::Entry)
            } else if is_type_kw(self.peek(0)) {
                self.parse_type_decl()
            } else {
                self.perr("E-PARSE-UNEXPECTED-TOKEN", "fn | entry | type")
            };
            match r {
                Ok(d) => decls.push(d),
                Err(Fail::Cutoff(d)) => {
                    let mut all = self.diags;
                    all.push(d);
                    return ParseOutcome::Cutoff(all);
                }
                Err(Fail::Parse { code, index: p, expected, at }) => {
                    self.emit(code, p, expected);
                    if let Some((span, actual)) = at {
                        let d = self.diags.last_mut().unwrap();
                        d.span = span;
                        d.actual = Some(actual);
                    }
                    if self.toks[p].kind == TokKind::Eof {
                        break;
                    }
                    if syncs == MAX_SYNCS {
                        self.emit("E-PARSE-RECOVERY-LIMIT", p, None);
                        break;
                    }
                    let mut q = p.max(s + 1);
                    while !self.is_sync(q) {
                        q += 1;
                    }
                    syncs += 1;
                    self.pos = q;
                    if self.toks[q].kind == TokKind::Eof {
                        break;
                    }
                }
            }
        }
        if !self.diags.is_empty() {
            return ParseOutcome::Errors(self.diags);
        }
        let end = self.toks.last().unwrap().end;
        ParseOutcome::Ok(Program { declarations: decls, meta: Meta::new((0, end), prog_idx) })
    }

    fn parse_fn(&mut self) -> R<FnDecl> {
        let kw = self.advance();
        let idx = self.adm.admit(kw.span(), Depths { fn_: true, ..Default::default() })?;
        let name = self.expect_ident()?;
        self.expect("(")?;
        let mut params = vec![];
        if !self.peek(0).is_punct(")") {
            loop {
                if !self.at_binder(0) {
                    return self.perr("E-PARSE-EXPECTED-IDENT", "identifier");
                }
                let ptok = self.peek(0).clone();
                let pidx = self.adm.admit(ptok.span(), Depths::default())?;
                self.advance();
                self.expect(":")?;
                let ty = self.parse_type(1)?;
                params.push(Param {
                    name: ptok.text.clone(),
                    name_span: Sp(ptok.start, ptok.end),
                    ty,
                    meta: Meta::new((ptok.start, self.prev_end), pidx),
                });
                if self.peek(0).is_punct(",") {
                    self.advance();
                    continue;
                }
                break;
            }
        }
        self.expect(")")?;
        self.expect("->")?;
        let ret = self.parse_type(1)?;
        self.expect("=")?;
        let body = self.parse_expr(1, 0, 0)?;
        if !self.at_decl_end() {
            return self.perr("E-PARSE-UNEXPECTED-TOKEN", "fn | entry | type | EOF");
        }
        Ok(FnDecl {
            name: name.text,
            name_span: Sp(name.start, name.end),
            params,
            return_type: ret,
            body,
            meta: Meta::new((kw.start, self.prev_end), idx),
            rec: false,
            rec_span: Sp::default(),
        })
    }

    fn parse_entry(&mut self) -> R<EntryDecl> {
        let kw = self.advance();
        let idx = self.adm.admit(kw.span(), Depths::default())?;
        let name = self.expect_ident()?;
        if !self.at_decl_end() {
            return self.perr("E-PARSE-UNEXPECTED-TOKEN", "fn | entry | type | EOF");
        }
        Ok(EntryDecl { name: name.text, name_span: Sp(name.start, name.end), meta: Meta::new((kw.start, self.prev_end), idx) })
    }

    /// v1.1：`type Name = { f: T, ... }`。v1.4：`type Name = A | B(T, ...) | ...`
    fn parse_type_decl(&mut self) -> R<Decl> {
        let kw = self.advance();
        let idx = self.adm.admit(kw.span(), Depths::default())?;
        let name = self.expect_ident()?;
        self.expect("=")?;
        if !self.peek(0).is_punct("{") {
            return self.parse_sum_decl(kw, idx, name).map(Decl::Sum);
        }
        self.expect("{")?;
        let mut fields = vec![];
        loop {
            let f = self.expect_binder()?;
            self.expect(":")?;
            let ty = self.parse_type(1)?;
            fields.push(FieldDecl { name: f.text, name_span: Sp(f.start, f.end), ty });
            if self.peek(0).is_punct(",") {
                self.advance();
                if self.peek(0).is_punct("}") {
                    break;
                }
                continue;
            }
            break;
        }
        self.expect("}")?;
        if !self.at_decl_end() {
            return self.perr("E-PARSE-UNEXPECTED-TOKEN", "fn | entry | type | EOF");
        }
        Ok(Decl::Type(TypeDecl {
            name: name.text,
            name_span: Sp(name.start, name.end),
            fields,
            meta: Meta::new((kw.start, self.prev_end), idx),
        }))
    }

    /// v1.4：`=` の後の `A | B(T, ...) | ...`。構築子の名前は大文字で始まる。
    fn parse_sum_decl(&mut self, kw: Token, idx: usize, name: Token) -> R<SumDecl> {
        let mut variants = vec![];
        loop {
            let c = self.peek(0).clone();
            if c.kind != TokKind::Ident || !c.text.starts_with(|ch: char| ch.is_ascii_uppercase()) {
                return self.perr("E-PARSE-EXPECTED-IDENT", CTOR_EXPECTED);
            }
            self.advance();
            let mut fields = vec![];
            if self.peek(0).is_punct("(") {
                self.advance();
                loop {
                    fields.push(self.parse_type(1)?);
                    if self.peek(0).is_punct(",") {
                        self.advance();
                        continue;
                    }
                    break;
                }
                self.expect(")")?;
            }
            variants.push(VariantDecl { name: c.text, name_span: Sp(c.start, c.end), fields });
            if self.peek(0).is_punct("|") {
                self.advance();
                continue;
            }
            break;
        }
        if !self.at_decl_end() {
            return self.perr("E-PARSE-UNEXPECTED-TOKEN", "fn | entry | type | EOF");
        }
        Ok(SumDecl { name: name.text, name_span: Sp(name.start, name.end), variants, meta: Meta::new((kw.start, self.prev_end), idx) })
    }

    /// v1.4：`match` で始まるのが match 式か（`match` は文脈キーワード。直後に式が続くときだけ。
    /// 括弧で囲んだ式はないので、`match(` は関数 `match` の呼び出し）。
    fn match_starts(&self) -> bool {
        let t = self.peek(1);
        match t.kind {
            // 次の宣言の始まり（`entry f`、`type T =`）なら `match` は変数
            TokKind::Ident if is_type_kw(t) && self.peek(2).kind == TokKind::Ident && self.peek(3).is_punct("=") => false,
            TokKind::Int | TokKind::Char | TokKind::Str | TokKind::Ident => true,
            TokKind::Kw if t.text == "entry" => self.peek(2).kind != TokKind::Ident,
            TokKind::Kw => !matches!(t.text.as_str(), "in" | "fn"),
            _ => false,
        }
    }

    /// v1.4：`match` の pattern。
    fn parse_pattern(&mut self) -> R<Pattern> {
        let tok = self.peek(0).clone();
        let start = tok.start;
        let (kind, arity) = match tok.kind {
            TokKind::Ident if tok.text == "_" => (PatKind::Wild, None),
            TokKind::Ident => (PatKind::Ctor(tok.text.clone()), None),
            TokKind::Kw if tok.text == "ok" => (PatKind::Ok, Some(1)),
            TokKind::Kw if tok.text == "err" => (PatKind::Err, Some(1)),
            TokKind::Kw if tok.text == "some" => (PatKind::Some, Some(1)),
            TokKind::Kw if tok.text == "none" => (PatKind::None, Some(0)),
            _ => return self.perr("E-PARSE-EXPECTED-PATTERN", PATTERN_EXPECTED),
        };
        self.advance();
        let mut binds = vec![];
        let mut parens = false;
        if (matches!(kind, PatKind::Ctor(_)) && self.peek(0).is_punct("(")) || arity == Some(1) {
            parens = true;
            self.expect("(")?;
            if !(arity.is_none() && self.peek(0).is_punct(")")) {
                loop {
                    let b = self.expect_binder()?;
                    binds.push((b.text, Sp(b.start, b.end)));
                    if arity.is_none() && self.peek(0).is_punct(",") {
                        self.advance();
                        continue;
                    }
                    break;
                }
            }
            self.expect(")")?;
        }
        Ok(Pattern { kind, span: Sp(start, self.prev_end), parens, binds })
    }

    /// v1.4：`match e { P => e, ... }`（`match` は読む前）
    fn parse_match(&mut self, d: usize, ld: usize, fd: usize) -> R<ExprKind> {
        let kw = self.advance();
        self.no_record_at = Some(self.pos);
        let scrutinee = self.parse_expr(d + 1, ld + 1, fd);
        self.no_record_at = None;
        let scrutinee = scrutinee?;
        self.expect("{")?;
        let mut arms = vec![];
        loop {
            if !arms.is_empty() && self.peek(0).is_punct("}") {
                break;
            }
            let pat = self.parse_pattern()?;
            self.expect("=>")?;
            let body = self.parse_expr(d + 1, ld + 1, fd)?;
            let span = Sp(pat.span.0, self.prev_end);
            arms.push(Arm { pat, body, span, variant: None });
            if self.peek(0).is_punct(",") {
                self.advance();
                continue;
            }
            break;
        }
        let close = self.expect("}")?;
        Ok(ExprKind::SumMatch {
            scrutinee: Box::new(scrutinee),
            arms,
            kw_span: Sp(kw.start, kw.end),
            close_span: Sp(close.start, close.end),
            kind: None,
        })
    }

    /// v1.5：`map(xs, |x| e)` など（名前は読む前）。第 2 引数は一つの binder のラムダ。
    fn parse_hof(&mut self, op: HofOp, d: usize, ld: usize, fd: usize) -> R<ExprKind> {
        self.advance();
        self.expect("(")?;
        let list = self.parse_expr(d + 1, ld, fd + 1)?;
        if !self.peek(0).is_punct(",") {
            // `map(xs)`：ラムダがない（区切りの誤りでなく、閉じ括弧が来たとき）
            if self.peek(0).is_punct(")") {
                return Err(Fail::Parse { code: "E-PARSE-EXPECTED-LAMBDA", index: self.pos, expected: Some(LAMBDA_EXPECTED), at: None });
            }
            self.expect(",")?;
        }
        self.advance();
        if !self.peek(0).is_punct("|") {
            return Err(Fail::Parse { code: "E-PARSE-EXPECTED-LAMBDA", index: self.pos, expected: Some(LAMBDA_EXPECTED), at: None });
        }
        self.advance();
        if !self.at_binder(0) {
            return Err(Fail::Parse { code: "E-PARSE-EXPECTED-LAMBDA", index: self.pos, expected: Some(LAMBDA_ONE_BINDER), at: None });
        }
        let x = self.advance();
        if !self.peek(0).is_punct("|") {
            return Err(Fail::Parse { code: "E-PARSE-EXPECTED-LAMBDA", index: self.pos, expected: Some(LAMBDA_ONE_BINDER), at: None });
        }
        self.advance();
        let body = self.parse_expr(d + 1, ld, fd + 1)?;
        self.expect(")")?;
        Ok(ExprKind::Hof { op, list: Box::new(list), binder: x.text, binder_span: Sp(x.start, x.end), body: Box::new(body) })
    }

    /// v1.6：`loop(init, max, |s| e)`（名前は読む前）。第 3 引数は一つの binder のラムダ。
    fn parse_loop(&mut self, d: usize, ld: usize, fd: usize) -> R<ExprKind> {
        self.advance();
        self.expect("(")?;
        let init = self.parse_expr(d + 1, ld, fd + 1)?;
        self.expect(",")?;
        let max = self.parse_expr(d + 1, ld, fd + 1)?;
        let lambda = |p: &Self, expected| Fail::Parse { code: "E-PARSE-EXPECTED-LAMBDA", index: p.pos, expected: Some(expected), at: None };
        if !self.peek(0).is_punct(",") {
            // `loop(init, max)`：ラムダがない
            if self.peek(0).is_punct(")") {
                return Err(lambda(self, LOOP_LAMBDA_EXPECTED));
            }
            self.expect(",")?;
        }
        self.advance();
        if !self.peek(0).is_punct("|") {
            return Err(lambda(self, LOOP_LAMBDA_EXPECTED));
        }
        self.advance();
        if !self.at_binder(0) {
            return Err(lambda(self, LOOP_ONE_BINDER));
        }
        let x = self.advance();
        if !self.peek(0).is_punct("|") {
            return Err(lambda(self, LOOP_ONE_BINDER));
        }
        self.advance();
        let body = self.parse_expr(d + 1, ld, fd + 1)?;
        self.expect(")")?;
        Ok(ExprKind::Loop {
            init: Box::new(init),
            max: Box::new(max),
            binder: x.text,
            binder_span: Sp(x.start, x.end),
            body: Box::new(body),
        })
    }

    fn parse_type(&mut self, depth: usize) -> R<TypeNode> {
        let tok = self.peek(0).clone();
        if tok.kind == TokKind::Ident && tok.text == DICT_TYPE && self.peek(1).is_punct("<") {
            // v1.9：`Dict<K, V>`。`Dict` は予約語でなく、直後が `<` のときだけ辞書の型（レコード型の名前は型引数を取らない）
            let idx = self.adm.admit(tok.span(), Depths { ty: Some(depth), ..Default::default() })?;
            self.advance();
            self.expect("<")?;
            let k = self.parse_type(depth + 1)?;
            self.expect(",")?;
            let v = self.parse_type(depth + 1)?;
            self.expect(">")?;
            return Ok(TypeNode::new(TyTag::Dict, vec![k, v], Meta::new((tok.start, self.prev_end), idx)));
        }
        if tok.kind == TokKind::Ident {
            // v1.1：レコード型の名前
            let idx = self.adm.admit(tok.span(), Depths { ty: Some(depth), ..Default::default() })?;
            self.advance();
            let mut t = TypeNode::new(TyTag::Error, vec![], Meta::new(tok.span(), idx));
            t.name = Some(tok.text);
            return Ok(t);
        }
        if tok.is_kw("String") {
            // v1.2：`String` は `List<Char>`。一つの型 node として数える（検証済み parser の `pt`、`bt` と同じ）
            let idx = self.adm.admit(tok.span(), Depths { ty: Some(depth), ..Default::default() })?;
            self.advance();
            let meta = Meta::new(tok.span(), idx);
            return Ok(TypeNode::new(TyTag::List, vec![TypeNode::new(TyTag::Char, vec![], meta)], meta));
        }
        let tag = match (tok.kind, TyTag::from_keyword(&tok.text)) {
            (TokKind::Kw, Some(t)) => t,
            _ => return self.perr("E-PARSE-EXPECTED-TYPE", "type"),
        };
        let idx = self.adm.admit(tok.span(), Depths { ty: Some(depth), ..Default::default() })?;
        let at = self.pos;
        self.advance();
        let mut args = vec![];
        if tag.arity() > 0 {
            self.expect("<")?;
            args.push(self.parse_type(depth + 1)?);
            // v1.2：`List<Char>` は `String` と書く（正準形が一つになるよう、検証済み parser も拒否する）
            if tag == TyTag::List && args[0].tag == TyTag::Char && self.peek(0).is_punct(">") {
                let end = self.peek(0).end;
                return Err(Fail::Parse {
                    code: "E-PARSE-STRING-TYPE",
                    index: at,
                    expected: Some("String"),
                    at: Some(((tok.start, end), "List<Char>".to_string())),
                });
            }
            if tag.arity() == 2 {
                self.expect(",")?;
                args.push(self.parse_type(depth + 1)?);
            }
            self.expect(">")?;
        }
        Ok(TypeNode::new(tag, args, Meta::new((tok.start, self.prev_end), idx)))
    }

    fn parse_args(&mut self, d: usize, ld: usize, fd: usize) -> R<Vec<Expr>> {
        let mut args = vec![];
        if self.peek(0).is_punct(")") {
            return Ok(args);
        }
        loop {
            args.push(self.parse_expr(d, ld, fd)?);
            if self.peek(0).is_punct(",") {
                self.advance();
                continue;
            }
            return Ok(args);
        }
    }

    fn parse_expr(&mut self, d: usize, ld: usize, fd: usize) -> R<Expr> {
        let mut e = self.parse_primary(d, ld, fd)?;
        // v1.1：field の参照 `e.f`（後置、左結合）
        while self.peek(0).is_punct(".") {
            let dot = self.peek(0).clone();
            let idx = self.adm.admit(dot.span(), Depths { expr: Some(d), ..Default::default() })?;
            self.advance();
            let f = self.expect_binder()?;
            let start = e.meta.span().0;
            e = Expr {
                kind: ExprKind::Field { expr: Box::new(e), field: f.text, field_span: Sp(f.start, f.end), target: None },
                meta: Meta::new((start, self.prev_end), idx),
            };
        }
        Ok(e)
    }

    /// v1.1：`Name { f: e, ..., ..base }`（名前は読んだ後）
    fn parse_record(&mut self, d: usize, ld: usize, fd: usize) -> R<(Vec<RecordField>, Option<Box<Expr>>)> {
        self.expect("{")?;
        let mut fields = vec![];
        let mut base = None;
        loop {
            if self.peek(0).is_punct("}") {
                break;
            }
            if self.peek(0).is_punct(".") && self.peek(1).is_punct(".") {
                self.advance();
                self.advance();
                base = Some(Box::new(self.parse_expr(d + 1, ld, fd)?));
                break;
            }
            let f = self.expect_binder()?;
            self.expect(":")?;
            let value = self.parse_expr(d + 1, ld, fd)?;
            fields.push(RecordField { name: f.text, name_span: Sp(f.start, f.end), value });
            if self.peek(0).is_punct(",") {
                self.advance();
                continue;
            }
            break;
        }
        self.expect("}")?;
        Ok((fields, base))
    }

    fn parse_primary(&mut self, d: usize, ld: usize, fd: usize) -> R<Expr> {
        let tok = self.peek(0).clone();
        let start = tok.start;
        let sp = tok.span();
        let simple = Depths { expr: Some(d), ..Default::default() };
        let kind;
        let idx;
        match tok.kind {
            TokKind::Int => {
                idx = self.adm.admit(sp, simple)?;
                self.advance();
                kind = ExprKind::Int(tok.text.parse::<BigInt>().expect("lexed integer"));
            }
            TokKind::Char => {
                idx = self.adm.admit(sp, simple)?;
                self.advance();
                kind = ExprKind::Char(tok.lit.chars().next().expect("lexed char literal"));
            }
            TokKind::Str => {
                idx = self.adm.admit(sp, simple)?;
                self.advance();
                kind = ExprKind::Str(tok.lit);
            }
            TokKind::Ident if tok.text == "match" && self.match_starts() => {
                idx = self.adm.admit(sp, Depths { expr: Some(d), let_: Some(ld + 1), ..Default::default() })?;
                kind = self.parse_match(d, ld, fd)?;
            }
            TokKind::Ident => {
                idx = self.adm.admit(sp, simple)?;
                let at = self.pos;
                self.advance();
                if self.peek(0).is_punct("{") && self.no_record_at == Some(at) {
                    kind = ExprKind::Var(tok.text);
                } else if self.peek(0).is_punct("(") {
                    self.advance();
                    let args = self.parse_args(d + 1, ld, fd)?;
                    self.expect(")")?;
                    kind = ExprKind::Call { callee: tok.text, args, builtin: false, callee_span: Sp(sp.0, sp.1) };
                } else if self.peek(0).is_punct("{") {
                    let (fields, base) = self.parse_record(d, ld, fd)?;
                    kind = ExprKind::Record { name: tok.text, name_span: Sp(sp.0, sp.1), fields, base };
                } else {
                    kind = ExprKind::Var(tok.text);
                }
            }
            // 文脈キーワード：呼び出しの形（直後が `(`、`<`、v1 の `[`）でなければ変数の参照。
            // v1.5 の map など（v1.6 の loop も）は直後が `(` のときだけ特殊形式
            TokKind::Kw
                if is_soft_keyword(&tok.text)
                    && !(self.peek(1).is_punct("(")
                        || (!is_lambda_form(&tok.text) && ["<", "["].iter().any(|p| self.peek(1).is_punct(p)))) =>
            {
                idx = self.adm.admit(sp, simple)?;
                self.advance();
                kind = ExprKind::Var(tok.text);
            }
            TokKind::Kw => match tok.text.as_str() {
                "true" | "false" | "unit" => {
                    idx = self.adm.admit(sp, simple)?;
                    self.advance();
                    kind = match tok.text.as_str() {
                        "true" => ExprKind::Bool(true),
                        "false" => ExprKind::Bool(false),
                        _ => ExprKind::Unit,
                    };
                }
                "list" => {
                    idx = self.adm.admit(sp, simple)?;
                    self.advance();
                    self.expect("<")?;
                    let ty = self.parse_type(1)?;
                    self.expect(">")?;
                    self.expect("(")?;
                    let items = self.parse_args(d + 1, ld, fd)?;
                    self.expect(")")?;
                    kind = ExprKind::List { element_type: ty, items };
                }
                // v1.9：空の辞書 `dict<K, V>()`
                DICT_NEW => {
                    idx = self.adm.admit(sp, simple)?;
                    self.advance();
                    self.expect("<")?;
                    let k = self.parse_type(1)?;
                    self.expect(",")?;
                    let v = self.parse_type(1)?;
                    self.expect(">")?;
                    let ty = TypeNode::new(TyTag::Dict, vec![k, v], Meta::new((start, self.prev_end), idx));
                    if !self.peek(0).is_punct("(") {
                        return self.perr("E-PARSE-EXPECTED-TOKEN", "()");
                    }
                    self.advance();
                    self.expect(")")?;
                    kind = ExprKind::DictNew(ty);
                }
                "some" => {
                    idx = self.adm.admit(sp, simple)?;
                    self.advance();
                    self.expect("(")?;
                    let v = self.parse_expr(d + 1, ld, fd)?;
                    self.expect(")")?;
                    kind = ExprKind::Some(Box::new(v));
                }
                "none" => {
                    idx = self.adm.admit(sp, simple)?;
                    self.advance();
                    self.expect("<")?;
                    let ty = self.parse_type(1)?;
                    self.expect(">")?;
                    // v1 の `none[T]` に慣れた書き手向けに、欠けているのが `()` 全体だと示す
                    if !self.peek(0).is_punct("(") {
                        return self.perr("E-PARSE-EXPECTED-TOKEN", "()");
                    }
                    self.advance();
                    self.expect(")")?;
                    kind = ExprKind::None(ty);
                }
                "ok" | "err" => {
                    idx = self.adm.admit(sp, simple)?;
                    self.advance();
                    self.expect("<")?;
                    let t = self.parse_type(1)?;
                    self.expect(",")?;
                    let u = self.parse_type(1)?;
                    self.expect(">")?;
                    let ty = TypeNode::new(TyTag::Result, vec![t, u], Meta::new((start, self.prev_end), idx));
                    self.expect("(")?;
                    let v = self.parse_expr(d + 1, ld, fd)?;
                    self.expect(")")?;
                    kind = ExprKind::Inj { ok: tok.text == "ok", ty, value: Box::new(v) };
                }
                "match_result" => {
                    idx = self.adm.admit(sp, Depths { expr: Some(d), let_: Some(ld + 1), ..Default::default() })?;
                    self.advance();
                    self.expect("(")?;
                    let scrutinee = self.parse_expr(d + 1, ld + 1, fd)?;
                    self.expect(",")?;
                    self.expect("|")?;
                    let x = self.expect_binder()?;
                    self.expect("|")?;
                    let on_ok = self.parse_expr(d + 1, ld + 1, fd)?;
                    self.expect(",")?;
                    self.expect("|")?;
                    let y = self.expect_binder()?;
                    self.expect("|")?;
                    let on_err = self.parse_expr(d + 1, ld + 1, fd)?;
                    self.expect(")")?;
                    kind = ExprKind::MatchResult {
                        scrutinee: Box::new(scrutinee),
                        ok_binder: x.text,
                        ok_span: Sp(x.start, x.end),
                        on_ok: Box::new(on_ok),
                        err_binder: y.text,
                        err_span: Sp(y.start, y.end),
                        on_err: Box::new(on_err),
                    };
                }
                "pair" => {
                    idx = self.adm.admit(sp, simple)?;
                    self.advance();
                    self.expect("(")?;
                    let a = self.parse_expr(d + 1, ld, fd)?;
                    self.expect(",")?;
                    let b = self.parse_expr(d + 1, ld, fd)?;
                    self.expect(")")?;
                    kind = ExprKind::Pair(Box::new(a), Box::new(b));
                }
                "let" => {
                    idx = self.adm.admit(sp, Depths { expr: Some(d), let_: Some(ld + 1), ..Default::default() })?;
                    self.advance();
                    let name = self.expect_binder()?;
                    self.expect("=")?;
                    let v = self.parse_expr(d + 1, ld + 1, fd)?;
                    self.expect("in")?;
                    let body = self.parse_expr(d + 1, ld + 1, fd)?;
                    kind = ExprKind::Let {
                        name: name.text,
                        name_span: Sp(name.start, name.end),
                        value: Box::new(v),
                        body: Box::new(body),
                    };
                }
                "if" => {
                    idx = self.adm.admit(sp, simple)?;
                    self.advance();
                    self.expect("(")?;
                    let c = self.parse_expr(d + 1, ld, fd)?;
                    self.expect(",")?;
                    let t = self.parse_expr(d + 1, ld, fd)?;
                    self.expect(",")?;
                    let e = self.parse_expr(d + 1, ld, fd)?;
                    self.expect(")")?;
                    kind = ExprKind::If(Box::new(c), Box::new(t), Box::new(e));
                }
                "fold" => {
                    idx = self.adm.admit(sp, Depths { expr: Some(d), fold: Some(fd + 1), ..Default::default() })?;
                    self.advance();
                    self.expect("(")?;
                    let xs = self.parse_expr(d + 1, ld, fd + 1)?;
                    self.expect(",")?;
                    let init = self.parse_expr(d + 1, ld, fd + 1)?;
                    self.expect(",")?;
                    self.expect("|")?;
                    let acc = self.expect_binder()?;
                    self.expect(",")?;
                    let item = self.expect_binder()?;
                    self.expect("|")?;
                    let body = self.parse_expr(d + 1, ld, fd + 1)?;
                    self.expect(")")?;
                    kind = ExprKind::Fold {
                        list: Box::new(xs),
                        init: Box::new(init),
                        acc: acc.text,
                        acc_span: Sp(acc.start, acc.end),
                        item: item.text,
                        item_span: Sp(item.start, item.end),
                        body: Box::new(body),
                    };
                }
                "match_option" => {
                    idx = self.adm.admit(sp, Depths { expr: Some(d), let_: Some(ld + 1), ..Default::default() })?;
                    self.advance();
                    self.expect("(")?;
                    let scrutinee = self.parse_expr(d + 1, ld + 1, fd)?;
                    self.expect(",")?;
                    let on_none = self.parse_expr(d + 1, ld + 1, fd)?;
                    self.expect(",")?;
                    self.expect("|")?;
                    let binder = self.expect_binder()?;
                    self.expect("|")?;
                    let on_some = self.parse_expr(d + 1, ld + 1, fd)?;
                    self.expect(")")?;
                    kind = ExprKind::Match {
                        scrutinee: Box::new(scrutinee),
                        on_none: Box::new(on_none),
                        binder: binder.text,
                        binder_span: Sp(binder.start, binder.end),
                        on_some: Box::new(on_some),
                    };
                }
                name if HofOp::from_name(name).is_some() => {
                    idx = self.adm.admit(sp, Depths { expr: Some(d), fold: Some(fd + 1), ..Default::default() })?;
                    kind = self.parse_hof(HofOp::from_name(name).unwrap(), d, ld, fd)?;
                }
                LOOP => {
                    idx = self.adm.admit(sp, Depths { expr: Some(d), fold: Some(fd + 1), ..Default::default() })?;
                    kind = self.parse_loop(d, ld, fd)?;
                }
                name if is_builtin(name) => {
                    idx = self.adm.admit(sp, simple)?;
                    self.advance();
                    self.expect("(")?;
                    let args = self.parse_args(d + 1, ld, fd)?;
                    self.expect(")")?;
                    kind = ExprKind::Call { callee: tok.text.clone(), args, builtin: true, callee_span: Sp(sp.0, sp.1) };
                }
                _ => return self.perr("E-PARSE-EXPECTED-EXPR", "expression"),
            },
            _ => return self.perr("E-PARSE-EXPECTED-EXPR", "expression"),
        }
        Ok(Expr { kind, meta: Meta::new((start, self.prev_end), idx) })
    }
}
