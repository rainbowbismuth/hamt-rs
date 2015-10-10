#![feature(test)]

extern crate test;
extern crate hamt;
use test::Bencher;
use std::collections::HashMap;
use hamt::HamtRc;

#[bench]
fn bench_add_one_hundred_keys_hamtrc(b: &mut Bencher) {
    b.iter(|| {
        (0..100).fold(HamtRc::<isize, isize>::new(), |acc, x| acc.insert(x, x));
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
    let hamt = (0..1000).fold(HamtRc::<isize, isize>::new(), |acc, x| acc.insert(x, x));
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
    let hamt_orig = (0..1000).fold(HamtRc::<isize, isize>::new(), |acc, x| acc.insert(x, x));
    b.iter(|| {
        let mut hamt = hamt_orig.clone();
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

    b.iter(|| {
        let mut hashmap = hashmap_orig.clone();
        for i in 400..500 {
            hashmap.remove(&i);
        }
    })
}

#[bench]
fn bench_iterate_hamtrc(b: &mut Bencher) {
    let hamt = (0..1000).fold(HamtRc::<isize, isize>::new(), |acc, x| acc.insert(x, x));
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