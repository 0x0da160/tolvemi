//! exec の値表現と、その spec の値 `Val` への写像。
//!
//! リストは共有可能な cons セルで表し、`view_val` で有限列に写す。cons の尾が
//! リストでない値（型付きプログラムでは起きない）は列の終端として扱う。

use crate::bigint::Int;
use crate::spec::*;
use std::rc::Rc;
use vstd::prelude::*;

verus! {

pub enum Value {
    Int(Int),
    Bool(bool),
    Unit,
    None,
    Some(Rc<Value>),
    Pair(Rc<Value>, Rc<Value>),
    Nil,
    Cons(Rc<Value>, Rc<Value>),
}

pub open spec fn is_list(v: Value) -> bool {
    v is Nil || v is Cons
}

pub open spec fn view_val(v: Value) -> Val
    decreases v, 1nat,
{
    match v {
        Value::Int(n) => Val::Int(n@),
        Value::Bool(b) => Val::Bool(b),
        Value::Unit => Val::Unit,
        Value::None => Val::None,
        Value::Some(x) => Val::Some(Box::new(view_val(*x))),
        Value::Pair(a, b) => Val::Pair(Box::new(view_val(*a)), Box::new(view_val(*b))),
        Value::Nil => Val::List(spine(v)),
        Value::Cons(_, _) => Val::List(spine(v)),
    }
}

/// cons 列の要素の値列。
pub open spec fn spine(v: Value) -> Seq<Val>
    decreases v, 0nat,
{
    match v {
        Value::Cons(h, t) => seq![view_val(*h)] + spine(*t),
        _ => Seq::empty(),
    }
}

/// 証明ブロック内で Rc の中身を写すための補助（`*rc` の移動を避ける）。
pub open spec fn vv(v: Rc<Value>) -> Val {
    view_val(*v)
}

pub open spec fn sp(v: Rc<Value>) -> Seq<Val> {
    spine(*v)
}

/// 証明ブロック内で参照先を値として取り出す補助。
pub open spec fn dr<T>(r: &T) -> T {
    *r
}

pub open spec fn view_vals(s: Seq<Rc<Value>>) -> Seq<Val> {
    Seq::new(s.len(), |i: int| view_val(*s[i]))
}

pub proof fn spine_cons(h: Rc<Value>, t: Rc<Value>)
    ensures
        spine(Value::Cons(h, t)) == seq![view_val(*h)] + spine(*t),
        spine(Value::Cons(h, t)).len() == spine(*t).len() + 1,
        spine(Value::Cons(h, t))[0] == view_val(*h),
{
}

pub proof fn spine_end(v: Rc<Value>)
    requires
        !(*v is Cons),
    ensures
        sp(v) == Seq::<Val>::empty(),
{
}

/// 列 s の位置 j からの残りが cons セルの spine と等しいなら、先頭と尾が分かる。
pub proof fn spine_step(s: Seq<Val>, j: int, h: Rc<Value>, t: Rc<Value>)
    requires
        0 <= j <= s.len(),
        spine(Value::Cons(h, t)) == s.subrange(j, s.len() as int),
    ensures
        j < s.len(),
        view_val(*h) == s[j],
        spine(*t) == s.subrange(j + 1, s.len() as int),
{
    spine_cons(h, t);
    assert(spine(*t) =~= s.subrange(j + 1, s.len() as int)) by {
        assert forall|k: int| 0 <= k < spine(*t).len() implies spine(*t)[k] == s.subrange(j + 1, s.len() as int)[k] by {
            assert(spine(Value::Cons(h, t))[k + 1] == spine(*t)[k]);
        }
    }
}

// ------------------------------------------------------------------ 環境

/// 後に積んだ束縛が前を隠す連想列としての環境。
pub open spec fn env_view(s: Seq<(usize, Rc<Value>)>) -> Map<nat, Val>
    decreases s.len(),
{
    if s.len() == 0 {
        Map::empty()
    } else {
        env_view(s.drop_last()).insert(s.last().0 as nat, view_val(*s.last().1))
    }
}

pub proof fn env_view_push(s: Seq<(usize, Rc<Value>)>, x: usize, v: Rc<Value>)
    ensures
        env_view(s.push((x, v))) == env_view(s).insert(x as nat, view_val(*v)),
{
    assert(s.push((x, v)).drop_last() =~= s);
}

/// 後ろから最初に見つかった束縛が環境の値。
pub proof fn env_view_lookup(s: Seq<(usize, Rc<Value>)>, i: int, x: usize)
    requires
        0 <= i < s.len(),
        s[i].0 == x,
        forall|j: int| i < j < s.len() ==> (#[trigger] s[j]).0 != x,
    ensures
        env_view(s).contains_key(x as nat),
        env_view(s)[x as nat] == view_val(*s[i].1),
    decreases s.len(),
{
    if i < s.len() - 1 {
        let d = s.drop_last();
        assert forall|j: int| i < j < d.len() implies (#[trigger] d[j]).0 != x by {
            assert(d[j] == s[j]);
        }
        env_view_lookup(d, i, x);
        assert(s[s.len() - 1].0 != x);
    }
}

/// どの束縛も x でなければ、環境は x を含まない。
pub proof fn env_view_absent(s: Seq<(usize, Rc<Value>)>, x: usize)
    requires
        forall|j: int| 0 <= j < s.len() ==> (#[trigger] s[j]).0 != x,
    ensures
        !env_view(s).contains_key(x as nat),
    decreases s.len(),
{
    if s.len() > 0 {
        let d = s.drop_last();
        assert forall|j: int| 0 <= j < d.len() implies (#[trigger] d[j]).0 != x by {
            assert(d[j] == s[j]);
        }
        env_view_absent(d, x);
        assert(s[s.len() - 1].0 != x);
    }
}

pub fn lookup(env: &Vec<(usize, Rc<Value>)>, x: usize) -> (r: Option<Rc<Value>>)
    ensures
        r is None ==> !env_view(env@).contains_key(x as nat),
        r is Some ==> env_view(env@).contains_key(x as nat) && env_view(env@)[x as nat] == view_val(
            *r->Some_0,
        ),
{
    let mut i = env.len();
    while i > 0
        invariant
            i <= env@.len(),
            forall|j: int| i <= j < env@.len() ==> (#[trigger] env@[j]).0 != x,
        decreases i,
    {
        i = i - 1;
        if env[i].0 == x {
            proof {
                env_view_lookup(env@, i as int, x);
            }
            return Some(env[i].1.clone());
        }
    }
    proof {
        env_view_absent(env@, x);
    }
    None
}

} // verus!
