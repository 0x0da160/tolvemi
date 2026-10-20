//! 書換えの後の大きさと式深さの上限（段階 0・SH7。式深さの上限は §18.1 の単位に合わせて改めた）。
//!
//! crates/tlvm/src/api.rs の書換え後の検査（check_rewritten_size と cross_check_at の式深さの判定）を、
//! 検証済み部品の述語で書き直し、判定が検証済み部品の受理と一致することを示す。
//!
//! - 大きさ：書換えた文字列の UTF-8 の bytes（Rust の text.len()）が上限以下なら通る（境界を含む）。
//!   書換えのないプログラムも同じ（オーナーの決定 2026-10-19 23:38）。
//! - 式深さ：検証済み parser が上限 d = E（§18.1 の式深さ 256）で受理すれば通る。parser の d は、入れ子の式の深さを
//!   一段ごとに 1 ずつ数える（§18.1 の式深さと同じ単位）。報告値 act は、受理する最小の d そのもの（半分にしない）。
//!   診断用 parser の式の深さと d は同じ値になる（calls、loop の書換え、.tlvm の corpus で測定）。
//!
//! 信頼する仮定（未証明。名前を付けて引数や述語に書く。一覧は trust-boundary.toml の resource-limits-after-lowering）：
//! - H26（h26）：loop だけの k 段の入れ子を書き換えた文字列は、検証済み parser が上限 d >= 26k + c で受理する
//!   （c は 1 か 2。HEAD での測定は c = 2）。書換え（hof::lower など）は未検証（段階 4）なので、仮定として書く。
//! - T-mono（t_mono）：検証済み parser の受理は、上限 d について単調。未証明（段階 4 より前に証明するかは未定）。
//! - 書換えの文字列を作る関数（format_program、hof::lower など）は未検証。この模型は、文字列を引数に取る。

use crate::surface::parse_e;
use crate::syntax::*;
use vstd::prelude::*;

verus! {

/// 検証済み parser の入力の上限（文字数）。parse_e と compile_source の前提。api.rs の VERIFIED_MAX_CHARS と同じ値。
pub const VERIFIED_MAX_CHARS: usize = 0x1000_0000;

/// 式の深さの上限の既定値（§18.1、profiles.rs の expr_depth）。
pub const EXPR_DEPTH_REF: usize = 256;

/// 書換え後の bytes の上限の既定値（§18.1、profiles.rs の rewritten_bytes）。
pub const REWRITTEN_BYTES_REF: usize = 4_194_304;

// ------------------------------------------------------------------ 大きさ（UTF-8 の bytes）

/// 文字一つの UTF-8 の bytes（Rust の char::len_utf8 と同じ区切り）。
pub open spec fn utf8_char_len(c: char) -> nat {
    if (c as u32) < 0x80 {
        1
    } else if (c as u32) < 0x800 {
        2
    } else if (c as u32) < 0x1_0000 {
        3
    } else {
        4
    }
}

/// 文字列の UTF-8 の bytes（Rust の String::len に当たる）。末尾の文字から足す。
pub open spec fn utf8_len(s: Seq<char>) -> nat
    decreases s.len(),
{
    if s.len() == 0 {
        0
    } else {
        utf8_len(s.drop_last()) + utf8_char_len(s.last())
    }
}

pub proof fn lemma_utf8_char_len_range(c: char)
    ensures
        1 <= utf8_char_len(c) <= 4,
{
}

pub proof fn lemma_utf8_push(s: Seq<char>, c: char)
    ensures
        utf8_len(s.push(c)) == utf8_len(s) + utf8_char_len(c),
{
    assert(s.push(c).drop_last() =~= s);
    assert(s.push(c).last() == c);
}

/// L2：文字列の bytes は文字数以上で、文字数の 4 倍以下。
pub proof fn lemma_utf8_bounds(s: Seq<char>)
    ensures
        s.len() <= utf8_len(s) <= 4 * s.len(),
    decreases s.len(),
{
    if s.len() > 0 {
        lemma_utf8_bounds(s.drop_last());
        lemma_utf8_char_len_range(s.last());
    }
}

/// 文字一つの UTF-8 の bytes（utf8_char_len の exec 版）。
pub fn utf8_char_len_exec(c: char) -> (n: usize)
    ensures
        n as nat == utf8_char_len(c),
        1 <= n <= 4,
{
    let v = c as u32;
    if v < 0x80 {
        1
    } else if v < 0x800 {
        2
    } else if v < 0x1_0000 {
        3
    } else {
        4
    }
}

/// 文字列の UTF-8 の bytes の exec 版（Rust の text.len() に当たる）。
pub fn utf8_len_exec(s: &Vec<char>) -> (n: usize)
    requires
        s@.len() < 0x1000_0000,
    ensures
        n as nat == utf8_len(s@),
{
    let mut n: usize = 0;
    let mut i: usize = 0;
    while i < s.len()
        invariant
            s@.len() < 0x1000_0000,
            i <= s@.len(),
            n as nat == utf8_len(s@.subrange(0, i as int)),
            n <= 4 * i,
        decreases s@.len() - i,
    {
        let c = s[i];
        let k = utf8_char_len_exec(c);
        proof {
            assert(s@.subrange(0, i as int + 1) =~= s@.subrange(0, i as int).push(s@[i as int]));
            lemma_utf8_push(s@.subrange(0, i as int), s@[i as int]);
        }
        n = n + k;
        i = i + 1;
    }
    proof {
        assert(s@.subrange(0, i as int) =~= s@);
    }
    n
}

/// api.rs の check_rewritten_size の判定。bytes が上限より大きければ拒否する（上限と等しければ通る）。
pub fn rewritten_fits(s: &Vec<char>, limit: usize) -> (r: bool)
    requires
        s@.len() < 0x1000_0000,
    ensures
        r == (utf8_len(s@) <= limit as nat),
{
    utf8_len_exec(s) <= limit
}

/// L3：書換えの bytes が上限以下で、上限が 2^28 未満なら、検証済み部品の入力の前提（文字数 < 2^28）を満たす。
pub proof fn lemma_size_gives_parse_precondition(s: Seq<char>, limit: nat)
    requires
        utf8_len(s) <= limit,
        limit < 0x1000_0000,
    ensures
        s.len() < 0x1000_0000,
{
    lemma_utf8_bounds(s);
}

/// 既定の上限（4 MiB）は、検証済み部品の入力の上限より小さい。既定の profile では大きさの判定が前提を満たす。
pub proof fn lemma_reference_limit_is_below_parse_bound()
    ensures
        REWRITTEN_BYTES_REF < VERIFIED_MAX_CHARS,
{
}

// ------------------------------------------------------------------ 式深さ（検証済み parser の d）

/// 検証済み parser が、深さの上限 d（型の深さの上限 td）で s を受理する。
pub open spec fn accepts(s: Seq<char>, d: nat, td: nat) -> bool {
    parse(s, d, td) is Some
}

/// api.rs の depth_bounds：式の深さの上限 e に対する、検証済み parser の上限 d（e そのもの）。
pub open spec fn depth_bound(e: nat) -> nat {
    e
}

/// api.rs の expr_depth_needed の報告値（act）：受理する最小の d そのもの。
pub open spec fn need_of(d: nat) -> nat {
    d
}

/// 検証済み parser の受理の判定（api.rs の cross_check_at が式の深さの判定に使う）。
pub fn depth_accepts(s: &Vec<char>, d: usize, td: usize) -> (r: bool)
    requires
        s@.len() < 0x1000_0000,
    ensures
        r == accepts(s@, d as nat, td as nat),
{
    match parse_e(s, d, td) {
        Some(_) => true,
        None => false,
    }
}

/// api.rs の書換え後の検査の通過：大きさを先に調べ、通ればそのあと式の深さを調べる。
pub open spec fn passes(s: Seq<char>, limit: nat, bound: nat, td: nat) -> bool {
    utf8_len(s) <= limit && accepts(s, bound, td)
}

/// 大きさと式の深さの二つの判定。二つとも通れば、同じ文字列が上限の内で検証済み parser に受理される。
pub fn guards_pass(s: &Vec<char>, limit: usize, bound: usize, td: usize) -> (r: bool)
    requires
        s@.len() < 0x1000_0000,
    ensures
        r == passes(s@, limit as nat, bound as nat, td as nat),
{
    rewritten_fits(s, limit) && depth_accepts(s, bound, td)
}

/// L5：報告値 act が上限 e より大きいのは、d が e より大きいときだけ（同値）。
pub proof fn lemma_need_exceeds_iff(d: nat, e: nat)
    ensures
        need_of(d) > e <==> d > depth_bound(e),
{
}

/// T-mono（信頼する仮定、未証明）：受理は上限 d について単調。d1 <= d2 で d1 が受理するなら d2 も受理する。
/// 受理かどうかの判定には要らない。報告値 act が最小の上限であることと、超過の報告の正しさに要る。
pub open spec fn t_mono(td: nat) -> bool {
    forall|s: Seq<char>, d1: nat, d2: nat|
        #![trigger accepts(s, d1, td), accepts(s, d2, td)]
        d1 <= d2 && accepts(s, d1, td) ==> accepts(s, d2, td)
}

/// L6（T-mono を使う）：上限 e で受理しない文字列が、ある上限 hi で受理するなら、
/// hi は e より大きく、報告値 need_of(hi) は e より大きい。超過の報告は、実際に上限を超えたことを示す。
pub proof fn lemma_depth_report_is_honest(s: Seq<char>, e: nat, hi: nat, td: nat)
    requires
        t_mono(td),
        accepts(s, hi, td),
        !accepts(s, depth_bound(e), td),
    ensures
        hi > depth_bound(e),
        need_of(hi) > e,
{
    if hi <= depth_bound(e) {
        assert(accepts(s, depth_bound(e), td));
    }
    lemma_need_exceeds_iff(hi, e);
}

/// L7（算術）：loop だけの k 段の入れ子の数。c は 1 か 2。報告値は 26k + c（HEAD の測定では c = 2）。
/// 上限 E = 256 で受理するのは k < 10 だけ（k = 9 で d = 236、k = 10 で d = 262）。
pub proof fn lemma_loop_nest_numbers(c: nat, k: nat)
    requires
        c == 1 || c == 2,
    ensures
        need_of(26 * k + c) == 26 * k + c,
        (26 * k + c <= depth_bound(256)) <==> k < 10,
{
}

/// 書換えの後の、loop だけの k 段の入れ子（tests/rewritten.rs の nested_loops と同じ形）。
/// 中身は未検証の書換えが作るので、定義しない（段階 4 で定める）。
pub uninterp spec fn lowered_nest(k: nat) -> Seq<char>;

/// H26（信頼する仮定、測定による）：lowered_nest(k) を上限 d で検証済み parser が受理するのは、d >= 26k + c のときだけ。
/// c は 1 か 2（HEAD での測定は c = 2。k = 1, 2, 3, 8, 9, 10, 11, 12, 19, 20 で d = 28, 54, 80, 210, 236, 262, 288, 314, 496, 522）。
/// if で包んだ本体には当てはまらない（同じ段数で d = 27k + 3）。
pub open spec fn h26(c: nat, td: nat) -> bool {
    forall|k: nat, d: nat| #[trigger] accepts(lowered_nest(k), d, td) == (26 * k + c <= d)
}

/// L8（H26 のもと）：loop だけの入れ子は、上限 E = 256 で k < 10 のとき受理し、k >= 10 で拒否する。
/// 拒否のときの報告値は 26k + c（> 256）。api.rs の cross_check_at の判定と報告値は、この述語に一致する。
pub proof fn lemma_loop_nest_guard(c: nat, td: nat, k: nat)
    requires
        c == 1 || c == 2,
        h26(c, td),
    ensures
        accepts(lowered_nest(k), depth_bound(256), td) <==> k < 10,
        !accepts(lowered_nest(k), depth_bound(256), td) ==> need_of(26 * k + c) > 256,
{
    lemma_loop_nest_numbers(c, k);
    assert(accepts(lowered_nest(k), depth_bound(256), td) == (26 * k + c <= depth_bound(256)));
}

} // verus!
