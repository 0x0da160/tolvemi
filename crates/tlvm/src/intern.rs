//! 型の interning（構造による正準化）。v1.12 の `TypeSharing::Interned` のときだけ働く。
//!
//! 型検査の一回の実行（`checker::check_scoped`。総称のプログラムでは `generics::check_with` が二つのパスを
//! 一つの実行にまとめる）の間だけ、同じ構成子・同じ子の node・同じ名前の印・同じ型引数の名前をもつ型を一つの共有
//! node にする。表は実行の終わりに捨てる。実行の外で作った型は従来どおり別々の node である。
//!
//! 正準化は表現の共有だけを変え、論理イベント列・仕事量・cutoff は変えない（設計書 §18.1a）。同じ node は同じ構造を
//! 指すので、比較 cache は node の address を鍵にできる（`TypeChecker::equal`）。表が保持する node は address が
//! 再利用されないので、別の型と取り違えることはない。

use crate::syntax::{Ty, TyTag};
use std::cell::{Cell, RefCell};
use std::collections::HashMap;
use std::hash::BuildHasherDefault;
use std::sync::Arc;

/// 正準化の鍵。子の node は address で表す（表が子を保持するので、実行の間は address が一意である）。
#[derive(Clone, PartialEq, Eq, Hash)]
pub(crate) struct Key {
    pub(crate) tag: TyTag,
    /// 子の数（二つまで）
    pub(crate) arity: u8,
    /// 子の node の address（使わない欄は 0）
    pub(crate) kids: [usize; 2],
    /// 名前の印（レコード型・直和型）の実体の address。0 は印なし
    pub(crate) label: usize,
    /// 型引数の名前
    pub(crate) pname: Option<Arc<str>>,
}

/// 鍵の hash。鍵は address と小さい整数だけなので、SipHash の強さは要らない（乗算と回転で混ぜる）。
#[derive(Default)]
pub(crate) struct Mix(u64);

impl Mix {
    fn add(&mut self, w: u64) {
        self.0 = (self.0.rotate_left(5) ^ w).wrapping_mul(0x51_7c_c1_b7_27_22_0a_95);
    }
}

impl std::hash::Hasher for Mix {
    fn write(&mut self, bytes: &[u8]) {
        for &b in bytes {
            self.add(u64::from(b));
        }
    }
    fn write_u8(&mut self, i: u8) {
        self.add(u64::from(i));
    }
    fn write_usize(&mut self, i: usize) {
        self.add(i as u64);
    }
    fn finish(&self) -> u64 {
        self.0
    }
}

/// 表の初期の容量（小さい検査で作り直しが起きないように）
const TABLE_CAPACITY: usize = 64;

thread_local! {
    /// このスレッドで開いている正準化の表（None のときは正準化しない）
    static TABLE: RefCell<Option<HashMap<Key, Ty, BuildHasherDefault<Mix>>>> =
        const { RefCell::new(None) };
    /// 表が開いているか（型を作るたびに表へ触れずに済ませる）
    static OPEN: Cell<bool> = const { Cell::new(false) };
}

/// 正準化するか（表が開いているか）。
pub(crate) fn active() -> bool {
    OPEN.with(|c| c.get())
}

/// 正準化の範囲。`on` のとき、このスレッドで表が開いていなければ開き、表を開いた範囲を出るとき閉じる。表が既に
/// 開いていれば（外側の実行が開いた）それを使う。`on` が偽の範囲（Off の検査）の中では、外側の表が開いていても
/// 正準化しない。`generics::check_with` は二つのパスの外側でこれを作る。
pub(crate) struct Scope {
    /// この範囲が表を開いたか（そのときは範囲を出るとき表を捨てる）
    owner: bool,
    /// この範囲に入る前の正準化の状態（範囲を出るとき戻す）
    before: bool,
}

impl Scope {
    pub(crate) fn enter(on: bool) -> Scope {
        let before = active();
        let owner = on && TABLE.with(|t| t.borrow().is_none());
        if owner {
            let table = HashMap::with_capacity_and_hasher(TABLE_CAPACITY, Default::default());
            TABLE.with(|t| *t.borrow_mut() = Some(table));
        }
        OPEN.with(|c| c.set(on));
        Scope { owner, before }
    }
}

impl Drop for Scope {
    fn drop(&mut self) {
        OPEN.with(|c| c.set(self.before));
        if self.owner {
            // 表の破棄（保持していた node の参照を外す）は借用の外で行う
            let table = TABLE.with(|t| t.borrow_mut().take());
            drop(table);
        }
    }
}

/// 鍵と同じ構造の node が表にあればそれを返し、なければ `make` で作って表に入れる。鍵がない（表が閉じている、
/// 子が三つ以上）ときは `make` の結果をそのまま返す。
pub(crate) fn canonical(key: Option<Key>, make: impl FnOnce() -> Ty) -> Ty {
    let Some(key) = key else {
        return make();
    };
    TABLE.with(|t| {
        let mut t = t.borrow_mut();
        let Some(table) = t.as_mut() else {
            return make();
        };
        if let Some(ty) = table.get(&key) {
            return ty.clone();
        }
        let ty = make();
        table.insert(key, ty.clone());
        ty
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn equal_types_share_one_node_inside_a_scope() {
        let _s = Scope::enter(true);
        let a = Ty::list(Ty::int());
        let b = Ty::list(Ty::int());
        assert_eq!(a.addr(), b.addr());
        assert_ne!(a.addr(), Ty::option(Ty::int()).addr());
        assert_eq!(Ty::param("T").addr(), Ty::param("T").addr());
        assert_ne!(Ty::param("T").addr(), Ty::param("U").addr());
        assert_eq!(Ty::int().unlabeled().addr(), Ty::int().addr());
    }

    #[test]
    fn nothing_is_shared_outside_a_scope() {
        // 値を持ったまま比べる（解放された node の address は再利用されうる）
        let (a, b) = (Ty::int(), Ty::int());
        assert_ne!(a.addr(), b.addr());
        {
            let _s = Scope::enter(false);
            assert!(!active());
            let (c, d) = (Ty::int(), Ty::int());
            assert_ne!(c.addr(), d.addr());
        }
        let _outer = Scope::enter(true);
        {
            // 外側の表を引き継ぐので、内側の範囲は表を閉じない
            let _inner = Scope::enter(true);
            assert_eq!(Ty::int().addr(), Ty::int().addr());
        }
        assert!(active());
        assert_eq!(Ty::int().addr(), Ty::int().addr());
    }

    #[test]
    fn an_off_range_inside_an_open_table_does_not_intern() {
        let _s = Scope::enter(true);
        let shared = Ty::list(Ty::int());
        {
            let _off = Scope::enter(false);
            assert!(!active());
            let (c, d) = (Ty::list(Ty::int()), Ty::list(Ty::int()));
            assert_ne!(c.addr(), d.addr());
            assert_ne!(c.addr(), shared.addr());
        }
        // 表は外側の範囲のもので、出た後は正準化が続く
        assert!(active());
        assert_eq!(Ty::list(Ty::int()).addr(), shared.addr());
    }

    #[test]
    fn the_table_closes_with_its_owner() {
        {
            let _s = Scope::enter(true);
            assert!(active());
        }
        assert!(!active());
        let (a, b) = (Ty::int(), Ty::int());
        assert_ne!(a.addr(), b.addr());
    }
}
