//! 信頼する多倍長整数（設計書 §11.3 の V1-A）。
//!
//! num-bigint の BigInt を包み、各演算の数学的意味を `ensures` で宣言する。本体は
//! `external_body` で Verus は検査しない。ここに書いた事後条件が num-bigint の実際の
//! 振る舞いと一致することは信頼仮定であり、trust-boundary.toml に記録する。

use num_integer::Integer;
use num_traits::Signed;
use vstd::prelude::*;

verus! {

#[verifier::external_body]
pub struct Int {
    pub n: num_bigint::BigInt,
}

impl View for Int {
    type V = int;

    uninterp spec fn view(&self) -> int;
}

pub open spec fn digit(d: int) -> char {
    if d == 0 {
        '0'
    } else if d == 1 {
        '1'
    } else if d == 2 {
        '2'
    } else if d == 3 {
        '3'
    } else if d == 4 {
        '4'
    } else if d == 5 {
        '5'
    } else if d == 6 {
        '6'
    } else if d == 7 {
        '7'
    } else if d == 8 {
        '8'
    } else {
        '9'
    }
}

/// 非負整数の十進表記（先頭ゼロなし）。
pub open spec fn nat_dec(n: nat) -> Seq<char>
    decreases n,
{
    if n < 10 {
        seq![digit(n as int)]
    } else {
        nat_dec(n / 10).push(digit((n % 10) as int))
    }
}

/// 整数の正準十進表記（設計書 §9 の値 JSON の `int`）。
pub open spec fn int_dec(n: int) -> Seq<char> {
    if n < 0 {
        seq!['-'] + nat_dec((-n) as nat)
    } else {
        nat_dec(n as nat)
    }
}

impl Int {
    #[verifier::external_body]
    pub fn from_u64(n: u64) -> (r: Int)
        ensures
            r@ == n as int,
    {
        Int { n: num_bigint::BigInt::from(n) }
    }

    #[verifier::external_body]
    pub fn copy(&self) -> (r: Int)
        ensures
            r@ == self@,
    {
        Int { n: self.n.clone() }
    }

    #[verifier::external_body]
    pub fn add(&self, o: &Int) -> (r: Int)
        ensures
            r@ == self@ + o@,
    {
        Int { n: &self.n + &o.n }
    }

    #[verifier::external_body]
    pub fn sub(&self, o: &Int) -> (r: Int)
        ensures
            r@ == self@ - o@,
    {
        Int { n: &self.n - &o.n }
    }

    #[verifier::external_body]
    pub fn mul(&self, o: &Int) -> (r: Int)
        ensures
            r@ == self@ * o@,
    {
        Int { n: &self.n * &o.n }
    }

    #[verifier::external_body]
    pub fn neg(&self) -> (r: Int)
        ensures
            r@ == -self@,
    {
        Int { n: -&self.n }
    }

    #[verifier::external_body]
    pub fn lt(&self, o: &Int) -> (r: bool)
        ensures
            r == (self@ < o@),
    {
        self.n < o.n
    }

    #[verifier::external_body]
    pub fn le(&self, o: &Int) -> (r: bool)
        ensures
            r == (self@ <= o@),
    {
        self.n <= o.n
    }

    #[verifier::external_body]
    pub fn eq(&self, o: &Int) -> (r: bool)
        ensures
            r == (self@ == o@),
    {
        self.n == o.n
    }

    #[verifier::external_body]
    pub fn is_positive(&self) -> (r: bool)
        ensures
            r == (self@ > 0),
    {
        self.n.is_positive()
    }

    /// 正の除数に対する床剰余。正の除数では Euclid 剰余（Verus の `%`）と一致する。
    #[verifier::external_body]
    pub fn mod_pos(&self, o: &Int) -> (r: Int)
        requires
            o@ > 0,
        ensures
            r@ == self@ % o@,
    {
        Int { n: self.n.mod_floor(&o.n) }
    }

    /// 正準十進表記。num-bigint の `to_string` がこれを満たすことは信頼仮定。
    #[verifier::external_body]
    pub fn to_dec(&self) -> (r: String)
        ensures
            r@ == int_dec(self@),
    {
        self.n.to_string()
    }

    /// 正準十進表記の文字列。`to_dec` と同じ信頼仮定（num-bigint の `to_string`）。
    #[verifier::external_body]
    pub fn to_dec_chars(&self) -> (r: Vec<char>)
        ensures
            r@ == int_dec(self@),
    {
        self.n.to_string().chars().collect()
    }

    /// 絶対値の bit 長（IntegerBits 上限の判定に使うだけで、証明には現れない）。
    #[verifier::external_body]
    pub fn bits(&self) -> u64 {
        self.n.magnitude().bits()
    }
}

} // verus!
