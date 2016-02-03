// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

extern crate quickcheck;
extern crate hamt;
use quickcheck::{Arbitrary, Gen, quickcheck};
use std::iter::FromIterator;
use std::cmp::max;
use hamt::HamtArc;

#[derive(Clone, Debug)]
struct Hamt {
    unwrap: HamtArc<isize, isize>,
}

impl Arbitrary for Hamt {
    fn arbitrary<G: Gen>(g: &mut G) -> Self {
        let mut hamt = HamtArc::new();
        let length: usize = Arbitrary::arbitrary(g);
        for _ in 0..max(length, 2048) {
            let kv: (isize, isize) = Arbitrary::arbitrary(g);
            hamt = hamt.insert(&kv.0, &kv.1);
        }
        return Hamt { unwrap: hamt };
    }
}

fn prop_insert_then_get(hamt: Hamt, key: isize, value: isize) -> bool {
    hamt.unwrap.insert(&key, &value).get(&key) == Option::Some(&value)
}

fn prop_insert_then_remove(hamt: Hamt, key: isize) -> bool {
    hamt.unwrap.insert(&key, &0).remove(&key).contains_key(&key) == false
}

fn prop_insert_then_remove_length_check(hamt: Hamt, key: isize) -> bool {
    let hamt_with_key = hamt.unwrap.insert(&key, &0);
    let hamt_without_key = hamt_with_key.remove(&key);
    hamt_with_key.len() == hamt_without_key.len() + 1
}

fn prop_from_iter_eq(hamt: Hamt) -> bool {
    HamtArc::<isize, isize>::from_iter(hamt.unwrap.iter()) == hamt.unwrap
}

#[test]
fn test_prop_insert_then_get() {
    quickcheck(prop_insert_then_get as fn(Hamt, isize, isize) -> bool);
}

#[test]
fn test_prop_insert_then_remove() {
    quickcheck(prop_insert_then_remove as fn(Hamt, isize) -> bool);
}

#[test]
fn test_prop_insert_then_remove_length_check() {
    quickcheck(prop_insert_then_remove_length_check as fn(Hamt, isize) -> bool);
}

#[test]
fn test_prop_from_iter_eq() {
    quickcheck(prop_from_iter_eq as fn(Hamt) -> bool);
}
