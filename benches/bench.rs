// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

#![feature(test)]

extern crate test;
extern crate hamt;
use test::Bencher;
use std::collections::HashMap;
use hamt::HamtRc;

#[bench]
fn bench_add_one_hundred_keys_hamtrc(b: &mut Bencher) {
    b.iter(|| {
        (0..100).fold(HamtRc::<isize, isize>::new(), |acc, x| acc.insert(&x, &x));
    })
}

#[bench]
fn bench_add_one_hundred_keys_hashmap(b: &mut Bencher) {
    b.iter(|| {
        let mut hm = HashMap::new();
        for i in 0..100 {
            hm.insert(i, i);
        }
    })
}

#[bench]
fn bench_look_up_one_hundred_keys_hamtrc(b: &mut Bencher) {
    let hamt = (0..1000).fold(HamtRc::<isize, isize>::new(), |acc, x| acc.insert(&x, &x));
    b.iter(|| {
        for i in 400..500 {
            assert!(hamt.get(&i).is_some());
        }
    })
}

#[bench]
fn bench_look_up_one_hundred_keys_hashmap(b: &mut Bencher) {
    let mut hm = HashMap::new();
    for i in 0..1000 {
        hm.insert(i, i);
    }
    b.iter(|| {
        for i in 400..500 {
            assert!(hm.get(&i).is_some());
        }
    })
}

#[bench]
fn bench_remove_one_hundred_keys_hamtrc(b: &mut Bencher) {
    let hamt_orig = (0..1000).fold(HamtRc::<isize, isize>::new(), |acc, x| acc.insert(&x, &x));
    let mut hamt = hamt_orig.clone();
    b.iter(|| {
        for i in 400..500 {
            hamt = hamt.remove(&i);
        }
    })
}

#[bench]
fn bench_remove_one_hundred_keys_hashmap(b: &mut Bencher) {
    let mut hashmap_orig = HashMap::new();
    for i in 0..1000 {
        hashmap_orig.insert(i, i);
    }
    let mut hashmap = hashmap_orig.clone();
    b.iter(|| {
        for i in 400..500 {
            hashmap.remove(&i);
        }
    })
}

#[bench]
fn bench_iterate_hamtrc(b: &mut Bencher) {
    let hamt = (0..1000).fold(HamtRc::<isize, isize>::new(), |acc, x| acc.insert(&x, &x));
    let mut count = 0;

    b.iter(|| {
        for (_, _) in &hamt {
            count += 1;
        }
    })
}

#[bench]
fn bench_iterate_hashmap(b: &mut Bencher) {
    let mut hashmap = HashMap::new();
    for i in 0..1000 {
        hashmap.insert(i, i);
    }
    let mut count = 0;

    b.iter(|| {
        for (_, _) in &hashmap {
            count += 1;
        }
    })
}
