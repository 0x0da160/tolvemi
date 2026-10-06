//! 診断 schema・整列・件数上限（設計書 §10）。

use std::collections::HashSet;

pub type Span = (usize, usize);

pub const PHASE_ORDER: [&str; 11] = [
    "source-boundary",
    "lex",
    "lexical-limits",
    "parse",
    "structural-limits",
    "name",
    "call-graph",
    "typecheck",
    "semantic-limits",
    "entry",
    "warnings",
];

pub const MAX_PER_SEVERITY: usize = 32;

/// message テンプレート。正式な diagnostic registry は未作成（G0 未達）なので暫定版。
pub fn message_for(code: &str) -> &'static str {
    match code {
        "E-LEX-NON-ASCII" => "コメント外に非 ASCII 文字があります",
        "E-LEX-UNEXPECTED-CHARACTER" => "この文字はトークンを開始できません",
        "E-LEX-INVALID-INTEGER" => "整数リテラルが正規形ではありません",
        "E-LEX-INVALID-NUMERIC-BOUNDARY" => "整数の直後に識別子文字や符号が続いています",
        "E-PARSE-UNEXPECTED-TOKEN" => "ここには fn、entry、EOF のいずれかが必要です",
        "E-PARSE-EXPECTED-TOKEN" => "必要な区切り記号がありません",
        "E-PARSE-EXPECTED-TYPE" => "型が必要です",
        "E-PARSE-EXPECTED-IDENT" => "識別子が必要です（予約語は使えません）",
        "E-PARSE-EXPECTED-EXPR" => "式が必要です",
        "E-PARSE-RECOVERY-LIMIT" => "parse error が多すぎるため解析を打ち切りました",
        "E-NAME-UNKNOWN-FUNCTION" => "未定義の関数です",
        "E-NAME-UNBOUND-VARIABLE" => "未束縛の変数です",
        "E-NAME-DUPLICATE-FUNCTION" => "同名のトップレベル関数が既に定義されています",
        "E-NAME-DUPLICATE-PARAM" => "同名の引数が既にあります",
        "E-NAME-DUPLICATE-BINDER" => "fold の acc と item は相異なる名前でなければなりません",
        "E-NAME-SHADOW" => "外側の変数をシャドーする束縛は書けません",
        "E-ENTRY-UNKNOWN" => "entry が未定義の関数を指しています",
        "E-ENTRY-MISSING" => "entry 宣言がありません",
        "E-ENTRY-DUPLICATE" => "entry 宣言は一つだけにしてください",
        "E-ENTRY-ARITY" => "entry 関数はちょうど一つの引数を取らなければなりません",
        "E-CYCLE-CALL" => "関数呼出しが循環しています",
        "E-ARITY-USER" => "関数の引数の数が一致しません",
        "E-ARITY-BUILTIN" => "組込み関数の引数の数が一致しません",
        "E-TYPE-ARG" => "引数の型が一致しません",
        "E-TYPE-EQ-OPERANDS" => "eq の両引数は同じ型でなければなりません",
        "E-TYPE-FST-ARG" => "fst の引数は Pair でなければなりません",
        "E-TYPE-SND-ARG" => "snd の引数は Pair でなければなりません",
        "E-TYPE-EXPECTED-LIST" => "List 型の値が必要です",
        "E-TYPE-LIST-ITEM" => "リスト要素の型が注釈と一致しません",
        "E-TYPE-IF-CONDITION" => "if の条件は Bool でなければなりません",
        "E-TYPE-IF-BRANCH" => "if の両分岐は同じ型でなければなりません",
        "E-TYPE-FOLD-LIST" => "fold の第1引数は List でなければなりません",
        "E-TYPE-FOLD-BODY" => "fold 本体の型は初期値の型と一致しなければなりません",
        "E-TYPE-RETURN" => "関数本体の型が宣言した戻り型と一致しません",
        "E-LIMIT-STATIC-SOURCE-BYTES" => "source bytes が上限を超えました",
        "E-LIMIT-STATIC-TOKENS" => "token 数が上限を超えました",
        "E-LIMIT-STATIC-INTEGER-DIGITS" => "整数リテラルの桁数が上限を超えました",
        "E-LIMIT-STATIC-FUNCTIONS" => "関数数が上限を超えました",
        "E-LIMIT-STATIC-AST-NODES" => "AST node 数が上限を超えました",
        "E-LIMIT-STATIC-TYPE-DEPTH" => "型構文の深さが上限を超えました",
        "E-LIMIT-STATIC-EXPR-DEPTH" => "式の深さが上限を超えました",
        "E-LIMIT-STATIC-LET-DEPTH" => "let のネスト深さが上限を超えました",
        "E-LIMIT-STATIC-FOLD-DEPTH" => "fold のネスト深さが上限を超えました",
        "E-LIMIT-STATIC-SEMANTIC-TYPE-DEPTH" => "推論された型の深さが上限を超えました",
        "E-LIMIT-STATIC-SEMANTIC-WORK" => "型検査の仕事量が上限を超えました",
        "E-INTERNAL-VERIFIED-MISMATCH" => "検証済み部品と診断用の検査器の判定が食い違いました（処理系の不具合）",
        "E-DIAG-LIMIT" => "error が多すぎるため以降を省略しました",
        "W-DIAG-LIMIT" => "warning が多すぎるため以降を省略しました",
        "W-UNUSED-FUNCTION" => "entry から到達しない関数です",
        "E-INPUT-JSON-SYNTAX" => "入力 JSON の文法が不正です",
        "E-INPUT-STRING-SCALAR" => "入力 JSON の文字列に不正な Unicode scalar があります",
        "E-INPUT-DUPLICATE-KEY" => "入力 JSON に重複キーがあります",
        "E-INPUT-FIELD-TYPE" => "入力値の JSON 型が不正です",
        "E-INPUT-MISSING-FIELD" => "入力値に必須キーがありません",
        "E-INPUT-TAG" => "入力値の tag が期待型と一致しません",
        "E-INPUT-UNKNOWN-FIELD" => "入力値に未知のキーがあります",
        "E-INPUT-INTEGER" => "入力整数が正規形ではありません",
        "E-LIMIT-INPUT-JSON-BYTES" => "入力 JSON bytes が上限を超えました",
        "E-LIMIT-INPUT-JSON-DEPTH" => "入力 JSON の構造深さが上限を超えました",
        "E-LIMIT-INPUT-VALUE-DEPTH" => "入力値の深さが上限を超えました",
        "E-LIMIT-INPUT-VALUE-NODES" => "入力値の node 数が上限を超えました",
        "E-LIMIT-INPUT-INTEGER-DIGITS" => "入力整数の桁数が上限を超えました",
        "E-AST-JSON-SYNTAX" => "AST JSON の文法が不正です",
        "E-AST-STRING-SCALAR" => "AST JSON の文字列に不正な Unicode scalar があります",
        "E-AST-DUPLICATE-KEY" => "AST JSON に重複キーがあります",
        "E-AST-CODEC" => "codec は \"ast_codec_v1\" でなければなりません",
        "E-AST-TAG" => "この位置で許されない tag です",
        "E-AST-MISSING-FIELD" => "必須キーがありません",
        "E-AST-UNKNOWN-FIELD" => "未知のキーがあります",
        "E-AST-FIELD-TYPE" => "JSON 型が不正です",
        "E-AST-IDENTIFIER" => "識別子が不正です",
        "E-AST-INTEGER" => "整数が正規形ではありません",
        "E-AST-LIMIT-BYTES" => "AST JSON bytes が上限を超えました",
        "E-AST-LIMIT-JSON-DEPTH" => "AST JSON の構造深さが上限を超えました",
        "E-AST-LIMIT-INTEGER-DIGITS" => "整数の桁数が上限を超えました",
        _ => "",
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Diagnostic {
    pub severity: &'static str,
    pub phase: &'static str,
    pub code: &'static str,
    pub span: Span,
    pub expected: Option<String>,
    pub actual: Option<String>,
    pub message: String,
    pub node_index: usize,
    pub seq: usize,
    pub repair: Option<Repair>,
}

/// 修復ヒント（設計書 §10.1）。修復の正しさ・唯一性は保証しない。
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Repair {
    /// replace_expression | replace_identifier | replace_type | insert_text | delete_span
    pub kind: &'static str,
    pub target_span: Span,
    pub constraint: String,
}

impl Diagnostic {
    pub fn error(phase: &'static str, code: &'static str, span: Span) -> Diagnostic {
        Diagnostic {
            severity: "error",
            phase,
            code,
            span,
            expected: None,
            actual: None,
            message: message_for(code).to_string(),
            node_index: 0,
            seq: 0,
            repair: None,
        }
    }

    pub fn warning(phase: &'static str, code: &'static str, span: Span) -> Diagnostic {
        Diagnostic { severity: "warning", ..Diagnostic::error(phase, code, span) }
    }

    pub fn exp(mut self, e: impl Into<String>) -> Self {
        self.expected = Some(e.into());
        self
    }

    pub fn act(mut self, a: impl Into<String>) -> Self {
        self.actual = Some(a.into());
        self
    }

    pub fn fix(mut self, kind: &'static str, target_span: Span, constraint: impl Into<String>) -> Self {
        self.repair = Some(Repair { kind, target_span, constraint: constraint.into() });
        self
    }

    pub fn at(mut self, node_index: usize) -> Self {
        self.node_index = node_index;
        self
    }

    pub fn is_cutoff(&self) -> bool {
        matches!(self.phase, "lexical-limits" | "structural-limits" | "semantic-limits")
    }

    /// 正準 key 順の一行 JSON（§10.1）。repair は実装した規則（`suggest_repairs` と名前検査）が出したものだけ。
    pub fn to_json(&self) -> String {
        let opt = |o: &Option<String>| match o {
            Some(s) => json_string(s),
            None => "null".to_string(),
        };
        let repair = match &self.repair {
            Some(r) => format!(
                "{{\"kind\":{},\"target_span\":{{\"start\":{},\"end\":{}}},\"constraint\":{}}}",
                json_string(r.kind),
                r.target_span.0,
                r.target_span.1,
                json_string(&r.constraint)
            ),
            None => "null".to_string(),
        };
        format!(
            "{{\"severity\":{},\"phase\":{},\"code\":{},\"span\":{{\"start\":{},\"end\":{}}},\"expected\":{},\"actual\":{},\"message\":{},\"repair\":{}}}",
            json_string(self.severity),
            json_string(self.phase),
            json_string(self.code),
            self.span.0,
            self.span.1,
            opt(&self.expected),
            opt(&self.actual),
            json_string(&self.message),
            repair
        )
    }
}

pub fn json_string(s: &str) -> String {
    let mut out = String::with_capacity(s.len() + 2);
    out.push('"');
    for c in s.chars() {
        match c {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            '\n' => out.push_str("\\n"),
            '\r' => out.push_str("\\r"),
            '\t' => out.push_str("\\t"),
            c if (c as u32) < 0x20 => out.push_str(&format!("\\u{:04x}", c as u32)),
            c => out.push(c),
        }
    }
    out.push('"');
    out
}

fn phase_rank(p: &str) -> usize {
    PHASE_ORDER.iter().position(|x| *x == p).unwrap_or(PHASE_ORDER.len())
}

/// phase 順・span 順に整列し、同一 node・同一 code を統合し、件数上限を適用する。
pub fn finalize(diags: Vec<Diagnostic>) -> (Vec<Diagnostic>, Vec<Diagnostic>) {
    let mut seen = HashSet::new();
    let mut unique = Vec::new();
    for d in diags {
        let key = if d.phase == "parse" {
            (d.phase, d.code, d.span, d.seq)
        } else {
            (d.phase, d.code, d.span, d.node_index)
        };
        if seen.insert(key) {
            unique.push(d);
        }
    }
    unique.sort_by(|a, b| {
        let ra = phase_rank(a.phase);
        let rb = phase_rank(b.phase);
        ra.cmp(&rb).then_with(|| {
            if a.phase == "parse" {
                a.seq.cmp(&b.seq)
            } else {
                (a.span.0, a.span.1, a.code, a.node_index).cmp(&(b.span.0, b.span.1, b.code, b.node_index))
            }
        })
    });
    let (errors, warnings): (Vec<_>, Vec<_>) = unique.into_iter().partition(|d| d.severity == "error");
    (limit(errors, "E-DIAG-LIMIT"), limit(warnings, "W-DIAG-LIMIT"))
}

fn limit(diags: Vec<Diagnostic>, code: &'static str) -> Vec<Diagnostic> {
    if diags.len() <= MAX_PER_SEVERITY {
        return diags;
    }
    let severity = diags[0].severity;
    let cutoff = diags.iter().find(|d| d.is_cutoff()).cloned();
    let mut kept: Vec<Diagnostic> = match cutoff {
        Some(c) => {
            let mut v: Vec<_> = diags.into_iter().filter(|d| !d.is_cutoff()).take(MAX_PER_SEVERITY - 2).collect();
            v.push(c);
            v
        }
        None => diags.into_iter().take(MAX_PER_SEVERITY - 1).collect(),
    };
    let mut d = Diagnostic::error("diagnostic-limit", code, (0, 0));
    d.severity = severity;
    kept.push(d);
    kept
}

// ---------------------------------------------------------------- 修復ヒント

/// 型・引数数・構文・entry の診断に修復ヒントを付ける（source API 用。AST API では付けない）。
/// どれも診断が既に持つ span と expected から機械的に決まるものだけで、推測で式を作らない。
pub fn suggest_repairs(diags: &mut [Diagnostic]) {
    for d in diags.iter_mut() {
        if d.repair.is_some() {
            continue;
        }
        let span = d.span;
        let exp = d.expected.clone();
        let r: Option<(&'static str, Span, String)> = match d.code {
            "E-TYPE-RETURN" | "E-TYPE-ARG" | "E-TYPE-LIST-ITEM" | "E-TYPE-IF-CONDITION" | "E-TYPE-IF-BRANCH"
            | "E-TYPE-FOLD-BODY" | "E-TYPE-EQ-OPERANDS" => exp.map(|t| ("replace_expression", span, format!("expression of type {t}"))),
            "E-TYPE-FOLD-LIST" | "E-TYPE-EXPECTED-LIST" => Some(("replace_expression", span, "expression of type List<...>".into())),
            "E-TYPE-FST-ARG" | "E-TYPE-SND-ARG" => Some(("replace_expression", span, "expression of type Pair<..., ...>".into())),
            "E-ARITY-USER" | "E-ARITY-BUILTIN" => exp.map(|n| ("replace_expression", span, format!("call with {n}"))),
            "E-NAME-SHADOW" | "E-NAME-DUPLICATE-BINDER" | "E-NAME-DUPLICATE-PARAM" => {
                Some(("replace_identifier", span, "identifier not bound in any enclosing scope".into()))
            }
            "E-NAME-DUPLICATE-FUNCTION" => Some(("replace_identifier", span, "function name not used by another function".into())),
            "E-ENTRY-MISSING" => Some(("insert_text", (span.0, span.0), "entry declaration naming a one-parameter function".into())),
            "E-LEX-INVALID-INTEGER" => {
                Some(("replace_expression", span, "canonical integer literal (no '+', no leading zeros, no -0)".into()))
            }
            "E-PARSE-EXPECTED-IDENT" => Some(("replace_identifier", span, "identifier that is not a reserved word".into())),
            "E-PARSE-EXPECTED-TYPE" => {
                Some(("replace_type", span, "type: Int | Bool | Unit | List<T> | Option<T> | Pair<A, B>".into()))
            }
            _ => None,
        };
        if let Some((kind, target_span, constraint)) = r {
            d.repair = Some(Repair { kind, target_span, constraint });
        }
    }
}

/// 編集距離（候補名の提示用）。
pub fn edit_distance(a: &str, b: &str) -> usize {
    let a: Vec<char> = a.chars().collect();
    let b: Vec<char> = b.chars().collect();
    let mut prev: Vec<usize> = (0..=b.len()).collect();
    for i in 1..=a.len() {
        let mut cur = vec![i; b.len() + 1];
        for j in 1..=b.len() {
            let c = if a[i - 1] == b[j - 1] { 0 } else { 1 };
            cur[j] = (prev[j] + 1).min(cur[j - 1] + 1).min(prev[j - 1] + c);
        }
        prev = cur;
    }
    prev[b.len()]
}

/// `name` に近い候補を距離・名前の順に最大 `max` 件（距離は名前の長さに応じて 1〜3 まで）。
pub fn closest<'a>(name: &str, candidates: impl Iterator<Item = &'a str>, max: usize) -> Vec<&'a str> {
    let limit = (name.chars().count() / 3).clamp(1, 3);
    let mut v: Vec<(usize, &str)> =
        candidates.map(|c| (edit_distance(name, c), c)).filter(|(d, c)| *d <= limit && *c != name).collect();
    v.sort();
    v.dedup();
    v.into_iter().take(max).map(|(_, c)| c).collect()
}

// ---------------------------------------------------------------- 人間向けの表示

/// byte offset の 1 始まりの行と列（列は文字数）。
pub fn line_col(src: &[u8], offset: usize) -> (usize, usize) {
    let offset = offset.min(src.len());
    let before = &src[..offset];
    let line = before.iter().filter(|b| **b == b'\n').count() + 1;
    let line_start = before.iter().rposition(|b| *b == b'\n').map_or(0, |i| i + 1);
    let col = String::from_utf8_lossy(&src[line_start..offset]).chars().count() + 1;
    (line, col)
}

/// `file:行:列: error[CODE]: message` の形で、該当行と下線、expected／actual、修復ヒントを添える。
/// JSON 診断（§10.1）の代わりではなく、同じ内容を読みやすくしたもの。
pub fn render_human(d: &Diagnostic, label: &str, src: &[u8]) -> String {
    let (line, col) = line_col(src, d.span.0);
    let mut out = format!("{label}:{line}:{col}: {}[{}]: {}", d.severity, d.code, d.message);
    match (&d.expected, &d.actual) {
        (Some(e), Some(a)) => out.push_str(&format!(" (expected {e}, found {a})")),
        (Some(e), None) => out.push_str(&format!(" (expected {e})")),
        (None, Some(a)) => out.push_str(&format!(" (found {a})")),
        (None, None) => {}
    }
    if !src.is_empty() && d.span.0 <= src.len() {
        let start = d.span.0;
        let line_start = src[..start].iter().rposition(|b| *b == b'\n').map_or(0, |i| i + 1);
        let line_end = src[start..].iter().position(|b| *b == b'\n').map_or(src.len(), |i| start + i);
        let text = String::from_utf8_lossy(&src[line_start..line_end]);
        let end = d.span.1.clamp(start, line_end);
        let width = String::from_utf8_lossy(&src[start..end]).chars().count().max(1);
        let num = line.to_string();
        let pad = " ".repeat(num.len());
        out.push_str(&format!("\n {num} | {text}\n {pad} | {}{}", " ".repeat(col - 1), "^".repeat(width)));
    }
    if let Some(r) = &d.repair {
        out.push_str(&format!("\n = repair ({}): {}", r.kind, r.constraint));
    }
    out
}
