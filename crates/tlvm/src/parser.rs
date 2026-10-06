//! 構文解析、parse Admission、bounded recovery（設計書 §4.1、§10.3、§18.1b）。

use crate::diagnostics::{Diagnostic, Span};
use crate::lexer::{TokKind, Token};
use crate::profiles::StaticProfile;
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

pub fn expr_depths(expr: usize) -> Depths {
    Depths { expr: Some(expr), ..Default::default() }
}

enum Fail {
    Parse { code: &'static str, index: usize, expected: Option<&'static str> },
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
        Parser { toks, pos: 0, adm: Admission::new(profile), diags: vec![], prev_end: 0 }
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
        Err(Fail::Parse { code, index: self.pos, expected: Some(expected) })
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
        t.kind == TokKind::Eof || t.is_kw("fn") || t.is_kw("entry")
    }

    fn is_sync(&self, i: usize) -> bool {
        let t = &self.toks[i];
        t.kind == TokKind::Eof || t.is_kw("fn") || t.is_kw("entry")
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
            } else if self.peek(0).is_kw("entry") {
                self.parse_entry().map(Decl::Entry)
            } else {
                self.perr("E-PARSE-UNEXPECTED-TOKEN", "fn | entry")
            };
            match r {
                Ok(d) => decls.push(d),
                Err(Fail::Cutoff(d)) => {
                    let mut all = self.diags;
                    all.push(d);
                    return ParseOutcome::Cutoff(all);
                }
                Err(Fail::Parse { code, index: p, expected }) => {
                    self.emit(code, p, expected);
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
                if self.peek(0).kind != TokKind::Ident {
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
            return self.perr("E-PARSE-UNEXPECTED-TOKEN", "fn | entry | EOF");
        }
        Ok(FnDecl {
            name: name.text,
            name_span: Sp(name.start, name.end),
            params,
            return_type: ret,
            body,
            meta: Meta::new((kw.start, self.prev_end), idx),
        })
    }

    fn parse_entry(&mut self) -> R<EntryDecl> {
        let kw = self.advance();
        let idx = self.adm.admit(kw.span(), Depths::default())?;
        let name = self.expect_ident()?;
        if !self.at_decl_end() {
            return self.perr("E-PARSE-UNEXPECTED-TOKEN", "fn | entry | EOF");
        }
        Ok(EntryDecl { name: name.text, name_span: Sp(name.start, name.end), meta: Meta::new((kw.start, self.prev_end), idx) })
    }

    fn parse_type(&mut self, depth: usize) -> R<TypeNode> {
        let tok = self.peek(0).clone();
        let tag = match (tok.kind, TyTag::from_keyword(&tok.text)) {
            (TokKind::Kw, Some(t)) => t,
            _ => return self.perr("E-PARSE-EXPECTED-TYPE", "type"),
        };
        let idx = self.adm.admit(tok.span(), Depths { ty: Some(depth), ..Default::default() })?;
        self.advance();
        let mut args = vec![];
        if tag.arity() > 0 {
            self.expect("<")?;
            args.push(self.parse_type(depth + 1)?);
            if tag == TyTag::Pair {
                self.expect(",")?;
                args.push(self.parse_type(depth + 1)?);
            }
            self.expect(">")?;
        }
        Ok(TypeNode { tag, args, meta: Meta::new((tok.start, self.prev_end), idx) })
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
            TokKind::Ident => {
                idx = self.adm.admit(sp, simple)?;
                self.advance();
                if self.peek(0).is_punct("(") {
                    self.advance();
                    let args = self.parse_args(d + 1, ld, fd)?;
                    self.expect(")")?;
                    kind = ExprKind::Call { callee: tok.text, args, builtin: false, callee_span: Sp(sp.0, sp.1) };
                } else {
                    kind = ExprKind::Var(tok.text);
                }
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
                    self.expect("[")?;
                    let ty = self.parse_type(1)?;
                    self.expect("]")?;
                    self.expect("(")?;
                    let items = self.parse_args(d + 1, ld, fd)?;
                    self.expect(")")?;
                    kind = ExprKind::List { element_type: ty, items };
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
                    self.expect("[")?;
                    let ty = self.parse_type(1)?;
                    self.expect("]")?;
                    kind = ExprKind::None(ty);
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
                    let name = self.expect_ident()?;
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
                    let acc = self.expect_ident()?;
                    self.expect(",")?;
                    let item = self.expect_ident()?;
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
