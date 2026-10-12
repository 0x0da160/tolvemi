//! v1.3 入出力ランタイム：テキストと値の相互変換。
//!
//! `tlvm exec` は標準入力の全文とコマンドライン引数をここで値にし（`text_value`、`args_value`）、
//! 検証済みの `pipeline::run_checked` で実行する。出力が String なら `text_codes` で文字の番号の列に戻す。
//! JSON を経由しないので、大きなテキストでも入力の復号が速い。

use crate::spec::*;
use crate::value::*;
use std::rc::Rc;
use vstd::prelude::*;

verus! {

/// テキストの値（String = List<Char>）。
pub open spec fn text_val(s: Seq<char>) -> Val {
    Val::List(chars(s))
}

/// 引数の列の値（List<String>）。
pub open spec fn args_val(a: Seq<Vec<char>>) -> Val {
    Val::List(Seq::new(a.len(), |i: int| text_val(a[i]@)))
}

pub fn text_value(s: &Vec<char>) -> (r: Rc<Value>)
    ensures
        view_val(*r) == text_val(s@),
{
    let ghost w = chars(s@);
    let mut out = Rc::new(Value::Nil);
    let mut k = s.len();
    proof {
        assert(spine(*out) =~= w.subrange(k as int, s@.len() as int));
    }
    while k > 0
        invariant
            w == chars(s@),
            k <= s@.len(),
            is_list(*out),
            spine(*out) == w.subrange(k as int, s@.len() as int),
        decreases k,
    {
        k = k - 1;
        let v = Rc::new(Value::Char(s[k] as u32));
        let ghost old_out = out;
        proof {
            spine_cons(v, old_out);
            assert(seq![vv(v)] + sp(old_out) =~= w.subrange(k as int, s@.len() as int));
        }
        out = Rc::new(Value::Cons(v, out));
    }
    proof {
        assert(w.subrange(0, s@.len() as int) =~= w);
    }
    out
}

pub fn args_value(a: &Vec<Vec<char>>) -> (r: Rc<Value>)
    ensures
        view_val(*r) == args_val(a@),
{
    let ghost w = Seq::new(a@.len(), |i: int| text_val(a@[i]@));
    let mut out = Rc::new(Value::Nil);
    let mut k = a.len();
    proof {
        assert(spine(*out) =~= w.subrange(k as int, a@.len() as int));
    }
    while k > 0
        invariant
            w == Seq::new(a@.len(), |i: int| text_val(a@[i]@)),
            k <= a@.len(),
            is_list(*out),
            spine(*out) == w.subrange(k as int, a@.len() as int),
        decreases k,
    {
        k = k - 1;
        let v = text_value(&a[k]);
        let ghost old_out = out;
        proof {
            spine_cons(v, old_out);
            assert(seq![vv(v)] + sp(old_out) =~= w.subrange(k as int, a@.len() as int));
        }
        out = Rc::new(Value::Cons(v, out));
    }
    proof {
        assert(w.subrange(0, a@.len() as int) =~= w);
    }
    out
}

/// 文字の番号の列が表すリストの値。
pub open spec fn codes_val(cs: Seq<u32>) -> Val {
    Val::List(Seq::new(cs.len(), |i: int| Val::Char(cs[i] as int)))
}

/// 文字のリストの値なら、その文字の番号の列。
pub fn text_codes(v: &Rc<Value>) -> (r: Option<Vec<u32>>)
    ensures
        r matches Some(cs) ==> view_val(**v) == codes_val(cs@),
{
    match &**v {
        Value::Nil | Value::Cons(_, _) => {},
        _ => return None,
    }
    let ghost s = sp(dr(v));
    let mut acc: Vec<u32> = Vec::new();
    let mut cur = v.clone();
    let ghost mut j: int = 0;
    proof {
        assert(s.subrange(0, s.len() as int) =~= s);
    }
    loop
        invariant
            is_list(*dr(v)),
            s == sp(dr(v)),
            0 <= j <= s.len(),
            acc@.len() == j,
            spine(*cur) == s.subrange(j, s.len() as int),
            forall|i: int| 0 <= i < j ==> s[i] == Val::Char(#[trigger] acc@[i] as int),
        decreases s.len() - j,
    {
        let (h, t) = match &*cur {
            Value::Cons(h, t) => (h.clone(), t.clone()),
            _ => {
                proof {
                    spine_end(cur);
                    assert(j == s.len());
                    assert(view_val(**v) == Val::List(s));
                    assert(s =~= Seq::new(acc@.len(), |i: int| Val::Char(acc@[i] as int)));
                }
                return Some(acc);
            },
        };
        proof {
            spine_step(s, j, h, t);
        }
        match &*h {
            Value::Char(c) => {
                acc.push(*c);
                proof {
                    j = j + 1;
                }
                cur = t;
            },
            _ => return None,
        }
    }
}

} // verus!
