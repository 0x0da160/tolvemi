//! v1.13：`tlvm exec` の辞書の入力。標準入力の行から `Dict<String, V>` を作る接着部分（検証されていない）。
//!
//! 標準入力の各行は `key<TAB>value` の形で、値は `V` が `String` なら任意の文字列、`Int` なら正規の十進表記。
//! 規則（spec/lptl-v1.13）：
//!
//! - 改行 `\n` で行に分け、行末の CR を一つ取る（CRLF の入力を読める）。長さ 0 の行は読まない（末尾の改行で増える
//!   空の行を含む）。行番号は改行で数えた物理の行（読まない行も数える）。
//! - 鍵は最初の TAB より前で、空でない。値は TAB より後で、TAB を含まない（TAB は一つだけ）。
//! - `Int` の値は `values::is_canonical_int`（`-` の後に数字、先頭に 0 を置かない、`-0` は不可）。
//!
//! 受理した行は普通の JSON の配列 `[["鍵","値"], ...]` にし、`run --plain` と同じ `api::decode_plain_input`
//! （診断付きの復号器と検証済みの復号器の突き合わせ、鍵の重複の拒否、資源上限）で読む。診断の span は生成した JSON の
//! bytes 上の位置なので、もとの行の範囲（標準入力の bytes 上）に直す。
//! 標準入力の UTF-8 の検査は呼び出し側（main.rs）が済ませている。

use crate::api::decode_plain_keeping;
use crate::diagnostics::{json_string, Diagnostic};
use crate::profiles::InputProfile;
use crate::syntax::{Ty, TyTag};
use crate::values::{is_canonical_int, DecodeResult, TypedValue, Verified};

/// 標準入力の行から作った辞書の入力の結果。
pub enum LinesResult {
    /// 復号できた（`run --plain` で同じ辞書を読んだときと同じ TypedValue と、検証済みの復号器の値）
    Decoded(TypedValue, Verified),
    /// 行の形が合わない（InputBoundaryFailure。理由に行番号を含む）
    BoundaryFailure(String),
    /// 辞書の復号が拒否した（鍵の重複、資源上限など）。span は標準入力の上のもとの行の範囲
    Invalid(Vec<Diagnostic>),
}

/// entry の入力型が標準入力の行から作れる辞書か（`Dict<String, String>` か `Dict<String, Int>`）。
pub fn accepts(t: &Ty) -> bool {
    t.tag() == TyTag::Dict
        && t.arg(0) == Ty::string()
        && (t.arg(1) == Ty::string() || t.arg(1) == Ty::int())
}

/// 生成した JSON の項の位置（JSON の bytes 上、項の `[` の位置）と、もとの行の範囲（標準入力の bytes 上）。
type Item = (usize, (usize, usize));

/// 標準入力 `stdin` を辞書の入力 `t`（`accepts` が真の型）の値にする。
pub fn dict_from_lines(t: &Ty, stdin: &str) -> LinesResult {
    let int_values = t.arg(1) == Ty::int();
    let mut json = String::from("[");
    let mut items: Vec<Item> = vec![];
    let mut line_start = 0usize;
    for (i, piece) in stdin.split('\n').enumerate() {
        let n = i + 1;
        let start = line_start;
        line_start += piece.len() + 1;
        let body = piece.strip_suffix('\r').unwrap_or(piece);
        if body.is_empty() {
            continue;
        }
        let Some(tab) = body.find('\t') else {
            return LinesResult::BoundaryFailure(line_error(n, "鍵と値を分ける TAB がありません"));
        };
        let (key, value) = (&body[..tab], &body[tab + 1..]);
        if key.is_empty() {
            return LinesResult::BoundaryFailure(line_error(
                n,
                "鍵が空です（TAB より前に文字がありません）",
            ));
        }
        if value.contains('\t') {
            return LinesResult::BoundaryFailure(line_error(
                n,
                "値に TAB があります（TAB は鍵と値の間に一つだけ）",
            ));
        }
        if int_values && !is_canonical_int(value) {
            return LinesResult::BoundaryFailure(line_error(
                n,
                "値が Int の正規の表記ではありません（- の後に数字、先頭に 0 を置かない、-0 は不可）",
            ));
        }
        if !items.is_empty() {
            json.push(',');
        }
        items.push((json.len(), (start, start + body.len())));
        json.push('[');
        json.push_str(&json_string(key));
        json.push(',');
        json.push_str(&json_string(value));
        json.push(']');
    }
    json.push(']');
    match decode_plain_keeping(t, json.as_bytes(), &InputProfile::default(), true) {
        (DecodeResult::Decoded(tv), verified) => LinesResult::Decoded(tv, verified),
        (DecodeResult::Invalid(ds), _) => {
            LinesResult::Invalid(ds.into_iter().map(|d| on_stdin(d, &items)).collect())
        }
        // 生成した JSON は構成上 UTF-8 なので届かない（届いても拒否する）
        (DecodeResult::InputBoundaryFailure, _) => {
            LinesResult::BoundaryFailure("InvalidUtf8".into())
        }
    }
}

fn line_error(n: usize, why: &str) -> String {
    format!("行 {n}: {why}")
}

/// 診断の span（生成した JSON の bytes 上）を、その項のもとの行の範囲（標準入力の bytes 上）に直す。
/// 項の外の位置（JSON 全体に関わる診断の (0, 0)）は直さない。
fn on_stdin(mut d: Diagnostic, items: &[Item]) -> Diagnostic {
    let k = items.partition_point(|(at, _)| *at <= d.span.0);
    if k > 0 {
        d.span = items[k - 1].1;
    }
    d
}
