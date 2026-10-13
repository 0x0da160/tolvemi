//! 正準フォーマッタ（設計書 §4.3）と ast_codec_v1 の encoder（§19.4）。

use crate::lexer::quote;
use crate::syntax::*;

pub const FORMATTER_VERSION: &str = "tlvm-format-v1";

pub fn format_type(t: &TypeNode) -> String {
    if let Some(n) = &t.name {
        return n.clone();
    }
    if t.is_string() {
        return "String".to_string();
    }
    if t.args.is_empty() {
        return t.tag.name().to_string();
    }
    let args: Vec<String> = t.args.iter().map(format_type).collect();
    format!("{}<{}>", t.tag.name(), args.join(", "))
}

fn join(xs: &[Expr]) -> String {
    xs.iter().map(format_expr).collect::<Vec<_>>().join(", ")
}

pub fn format_expr(e: &Expr) -> String {
    match &e.kind {
        ExprKind::Int(n) => n.to_string(),
        ExprKind::Char(c) => quote(&c.to_string(), '\''),
        ExprKind::Str(w) => quote(w, '"'),
        ExprKind::Bool(b) => b.to_string(),
        ExprKind::Unit => "unit".into(),
        ExprKind::Var(n) => n.clone(),
        ExprKind::List { element_type, items } => format!("list<{}>({})", format_type(element_type), join(items)),
        ExprKind::Some(v) => format!("some({})", format_expr(v)),
        ExprKind::None(t) => format!("none<{}>()", format_type(t)),
        ExprKind::Pair(a, b) => format!("pair({}, {})", format_expr(a), format_expr(b)),
        ExprKind::Call { callee, args, .. } => format!("{}({})", callee, join(args)),
        ExprKind::Let { name, value, body, .. } => format!("let {} = {} in {}", name, format_expr(value), format_expr(body)),
        ExprKind::If(c, t, f) => format!("if({}, {}, {})", format_expr(c), format_expr(t), format_expr(f)),
        ExprKind::Fold { list, init, acc, item, body, .. } => {
            format!("fold({}, {}, |{}, {}| {})", format_expr(list), format_expr(init), acc, item, format_expr(body))
        }
        // v1.5：`map(xs, |x| e)` など
        ExprKind::Hof { op, list, binder, body, .. } => format!("{}({}, |{}| {})", op.name(), format_expr(list), binder, format_expr(body)),
        // v1.6：`loop(init, max, |s| e)`
        ExprKind::Loop { init, max, binder, body, .. } => {
            format!("loop({}, {}, |{}| {})", format_expr(init), format_expr(max), binder, format_expr(body))
        }
        ExprKind::Match { scrutinee, on_none, binder, on_some, .. } => {
            format!("match_option({}, {}, |{}| {})", format_expr(scrutinee), format_expr(on_none), binder, format_expr(on_some))
        }
        ExprKind::Record { name, fields, base, .. } => {
            let mut parts: Vec<String> = fields.iter().map(|f| format!("{}: {}", f.name, format_expr(&f.value))).collect();
            if let Some(b) = base {
                parts.push(format!("..{}", format_expr(b)));
            }
            format!("{} {{ {} }}", name, parts.join(", "))
        }
        ExprKind::Field { expr, field, .. } => format!("{}.{}", format_expr(expr), field),
        ExprKind::Inj { ok, ty, value } => format!(
            "{}<{}, {}>({})",
            if *ok { "ok" } else { "err" },
            format_type(&ty.args[0]),
            format_type(&ty.args[1]),
            format_expr(value)
        ),
        ExprKind::MatchResult { scrutinee, ok_binder, on_ok, err_binder, on_err, .. } => format!(
            "match_result({}, |{}| {}, |{}| {})",
            format_expr(scrutinee),
            ok_binder,
            format_expr(on_ok),
            err_binder,
            format_expr(on_err)
        ),
        ExprKind::SumMatch { scrutinee, arms, .. } => {
            let arms: Vec<String> = arms.iter().map(|a| format!("{} => {}", format_pattern(&a.pat), format_expr(&a.body))).collect();
            format!("match {} {{ {} }}", format_expr(scrutinee), arms.join(", "))
        }
    }
}

/// v1.4：`match` の pattern。
pub fn format_pattern(p: &Pattern) -> String {
    let binds: Vec<&str> = p.binds.iter().map(|(b, _)| b.as_str()).collect();
    let head = match &p.kind {
        PatKind::Ctor(c) => c.as_str(),
        PatKind::Ok => "ok",
        PatKind::Err => "err",
        PatKind::Some => "some",
        PatKind::None => "none",
        PatKind::Wild => "_",
    };
    if p.parens {
        format!("{head}({})", binds.join(", "))
    } else {
        head.to_string()
    }
}

pub fn format_program(p: &Program) -> String {
    let mut out = String::new();
    for d in &p.declarations {
        match d {
            Decl::Fn(f) => {
                let params: Vec<String> = f.params.iter().map(|p| format!("{}: {}", p.name, format_type(&p.ty))).collect();
                out.push_str(&format!(
                    "fn {}({}) -> {} = {}",
                    f.name,
                    params.join(", "),
                    format_type(&f.return_type),
                    format_expr(&f.body)
                ));
            }
            Decl::Entry(e) => out.push_str(&format!("entry {}", e.name)),
            Decl::Type(t) => {
                let fs: Vec<String> = t.fields.iter().map(|f| format!("{}: {}", f.name, format_type(&f.ty))).collect();
                out.push_str(&format!("type {} = {{ {} }}", t.name, fs.join(", ")));
            }
            Decl::Sum(t) => {
                let vs: Vec<String> = t
                    .variants
                    .iter()
                    .map(|v| {
                        if v.fields.is_empty() {
                            v.name.clone()
                        } else {
                            format!("{}({})", v.name, v.fields.iter().map(format_type).collect::<Vec<_>>().join(", "))
                        }
                    })
                    .collect();
                out.push_str(&format!("type {} = {}", t.name, vs.join(" | ")));
            }
        }
        out.push('\n');
    }
    out
}

// ---------------------------------------------------------------- AST encoder

fn type_json(t: &TypeNode, out: &mut String) {
    if t.is_string() {
        // v1.2：`String` は一つの node（`List<Char>` の形は transport でも書けない）
        out.push_str("{\"tag\":\"string\"}");
        return;
    }
    let tag = t.tag.name().to_ascii_lowercase();
    out.push_str(&format!("{{\"tag\":\"{tag}\""));
    match t.tag {
        TyTag::List | TyTag::Option => {
            out.push_str(",\"element\":");
            type_json(&t.args[0], out);
        }
        TyTag::Pair => {
            out.push_str(",\"left\":");
            type_json(&t.args[0], out);
            out.push_str(",\"right\":");
            type_json(&t.args[1], out);
        }
        TyTag::Result => {
            out.push_str(",\"ok\":");
            type_json(&t.args[0], out);
            out.push_str(",\"err\":");
            type_json(&t.args[1], out);
        }
        _ => {}
    }
    out.push('}');
}

/// JSON 文字列（`"`、`\\`、制御文字を escape する。それ以外は UTF-8 のまま）。
pub fn json_string(s: &str, out: &mut String) {
    out.push('"');
    for c in s.chars() {
        match c {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            '\n' => out.push_str("\\n"),
            '\t' => out.push_str("\\t"),
            '\r' => out.push_str("\\r"),
            c if (c as u32) < 0x20 => out.push_str(&format!("\\u{:04x}", c as u32)),
            c => out.push(c),
        }
    }
    out.push('"');
}

fn exprs_json(xs: &[Expr], out: &mut String) {
    out.push('[');
    for (i, x) in xs.iter().enumerate() {
        if i > 0 {
            out.push(',');
        }
        expr_json(x, out);
    }
    out.push(']');
}

fn expr_json(e: &Expr, out: &mut String) {
    match &e.kind {
        ExprKind::Int(n) => out.push_str(&format!("{{\"tag\":\"int\",\"value\":\"{n}\"}}")),
        // v1.2：文字は code point の十進（値 JSON の char と同じ）、文字列は JSON 文字列
        ExprKind::Char(c) => out.push_str(&format!("{{\"tag\":\"char\",\"value\":\"{}\"}}", *c as u32)),
        ExprKind::Str(w) => {
            out.push_str("{\"tag\":\"string\",\"value\":");
            json_string(w, out);
            out.push('}');
        }
        ExprKind::Bool(b) => out.push_str(&format!("{{\"tag\":\"bool\",\"value\":{b}}}")),
        ExprKind::Unit => out.push_str("{\"tag\":\"unit\"}"),
        ExprKind::Var(n) => out.push_str(&format!("{{\"tag\":\"var\",\"name\":\"{n}\"}}")),
        ExprKind::List { element_type, items } => {
            out.push_str("{\"tag\":\"list\",\"element_type\":");
            type_json(element_type, out);
            out.push_str(",\"items\":");
            exprs_json(items, out);
            out.push('}');
        }
        ExprKind::Some(v) => {
            out.push_str("{\"tag\":\"some\",\"value\":");
            expr_json(v, out);
            out.push('}');
        }
        ExprKind::None(t) => {
            out.push_str("{\"tag\":\"none\",\"element_type\":");
            type_json(t, out);
            out.push('}');
        }
        ExprKind::Pair(a, b) => {
            out.push_str("{\"tag\":\"pair\",\"left\":");
            expr_json(a, out);
            out.push_str(",\"right\":");
            expr_json(b, out);
            out.push('}');
        }
        ExprKind::Call { callee, args, .. } => {
            out.push_str(&format!("{{\"tag\":\"call\",\"callee\":\"{callee}\",\"args\":"));
            exprs_json(args, out);
            out.push('}');
        }
        ExprKind::Let { name, value, body, .. } => {
            out.push_str(&format!("{{\"tag\":\"let\",\"name\":\"{name}\",\"value\":"));
            expr_json(value, out);
            out.push_str(",\"body\":");
            expr_json(body, out);
            out.push('}');
        }
        ExprKind::If(c, t, f) => {
            out.push_str("{\"tag\":\"if\",\"condition\":");
            expr_json(c, out);
            out.push_str(",\"then\":");
            expr_json(t, out);
            out.push_str(",\"else\":");
            expr_json(f, out);
            out.push('}');
        }
        ExprKind::Fold { list, init, acc, item, body, .. } => {
            out.push_str("{\"tag\":\"fold\",\"list\":");
            expr_json(list, out);
            out.push_str(",\"init\":");
            expr_json(init, out);
            out.push_str(&format!(",\"acc\":\"{acc}\",\"item\":\"{item}\",\"body\":"));
            expr_json(body, out);
            out.push('}');
        }
        ExprKind::Match { scrutinee, on_none, binder, on_some, .. } => {
            out.push_str("{\"tag\":\"match_option\",\"scrutinee\":");
            expr_json(scrutinee, out);
            out.push_str(",\"on_none\":");
            expr_json(on_none, out);
            out.push_str(&format!(",\"binder\":\"{binder}\",\"on_some\":"));
            expr_json(on_some, out);
            out.push('}');
        }
        // v1.5：`{"tag":"map","list":...,"binder":"x","body":...}` など
        ExprKind::Hof { op, list, binder, body, .. } => {
            out.push_str(&format!("{{\"tag\":\"{}\",\"list\":", op.name()));
            expr_json(list, out);
            out.push_str(&format!(",\"binder\":\"{binder}\",\"body\":"));
            expr_json(body, out);
            out.push('}');
        }
        // v1.6：`{"tag":"loop","init":...,"max":...,"binder":"s","body":...}`
        ExprKind::Loop { init, max, binder, body, .. } => {
            out.push_str("{\"tag\":\"loop\",\"init\":");
            expr_json(init, out);
            out.push_str(",\"max\":");
            expr_json(max, out);
            out.push_str(&format!(",\"binder\":\"{binder}\",\"body\":"));
            expr_json(body, out);
            out.push('}');
        }
        ExprKind::Inj { ok, ty, value } => {
            out.push_str(if *ok { "{\"tag\":\"ok\",\"ok_type\":" } else { "{\"tag\":\"err\",\"ok_type\":" });
            type_json(&ty.args[0], out);
            out.push_str(",\"err_type\":");
            type_json(&ty.args[1], out);
            out.push_str(",\"value\":");
            expr_json(value, out);
            out.push('}');
        }
        ExprKind::MatchResult { scrutinee, ok_binder, on_ok, err_binder, on_err, .. } => {
            out.push_str("{\"tag\":\"match_result\",\"scrutinee\":");
            expr_json(scrutinee, out);
            out.push_str(&format!(",\"ok_binder\":\"{ok_binder}\",\"on_ok\":"));
            expr_json(on_ok, out);
            out.push_str(&format!(",\"err_binder\":\"{err_binder}\",\"on_err\":"));
            expr_json(on_err, out);
            out.push('}');
        }
        // AST transport にレコード・直和型・match の形はない。呼び出し側が展開と lower を済ませてから渡す
        ExprKind::Record { .. } | ExprKind::Field { .. } | ExprKind::SumMatch { .. } => out.push_str("{\"tag\":\"unit\"}"),
    }
}

/// 正準 AST JSON（UTF-8、最小空白、表の key 順、末尾改行なし）。名前は ASCII なので escape 不要
/// （文字列リテラルだけは `json_string` で escape する）。
pub fn encode_ast(p: &Program) -> String {
    let mut out = String::from("{\"codec\":\"ast_codec_v1\",\"declarations\":[");
    for (i, d) in p.declarations.iter().enumerate() {
        if i > 0 {
            out.push(',');
        }
        match d {
            Decl::Fn(f) => {
                out.push_str(&format!("{{\"tag\":\"fn\",\"name\":\"{}\",\"params\":[", f.name));
                for (j, p) in f.params.iter().enumerate() {
                    if j > 0 {
                        out.push(',');
                    }
                    out.push_str(&format!("{{\"name\":\"{}\",\"type\":", p.name));
                    type_json(&p.ty, &mut out);
                    out.push('}');
                }
                out.push_str("],\"return_type\":");
                type_json(&f.return_type, &mut out);
                out.push_str(",\"body\":");
                expr_json(&f.body, &mut out);
                out.push('}');
            }
            Decl::Entry(e) => out.push_str(&format!("{{\"tag\":\"entry\",\"name\":\"{}\"}}", e.name)),
            Decl::Type(_) | Decl::Sum(_) => {}
        }
    }
    out.push_str("]}");
    out
}
