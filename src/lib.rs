// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

#![cfg_attr(feature="clippy", feature(plugin))]

#![cfg_attr(feature="clippy", plugin(clippy))]

mod internal {
    pub type Bitmap = u64;
    pub type HashBits = u64;
    pub type Shift = u64;

    pub const BITS_PER_SUBKEY: u64 = 4;
    //const MAX_CHILDREN: u64 = 16;
    pub const SUBKEY_MASK: Bitmap = 15;
    pub const FULL_NODE_MASK: Bitmap = 65535;

    pub fn index(h: HashBits, s: Shift) -> usize {
        ((h >> s) & SUBKEY_MASK) as usize
    }

    pub fn mask(h: HashBits, s: Shift) -> u64 {
        1 << index(h, s)
    }

    pub fn sparse_index(b: Bitmap, m: Bitmap) -> usize {
        ((b & (m - 1)).count_ones()) as usize
    }
}

//TODO: Try adding something like this for collision & two.
// enum SmallVec<T> {
//     One(T),
//     Two(T, T),
//     Big(Vec<T>)
// }

//TODO: Then it might be interesting to remove Leaf and turn it and Collision into 'Leaves'
//TODO: Full could be an array with known size.
//TODO: Try to mutate in place with Rc/Arc.get_mut().

macro_rules! make_hamt_type {
    ($hamt:ident, $rc:ty, $rc_new:path, $rc_alt:ty) => {
        use std::iter::{Map, FromIterator};
        use std::hash::{Hash, Hasher};
        use std::hash::SipHasher;
        use std::borrow::Borrow;
        use std::ops::{Deref, Index};
        use std::slice;
        use super::internal::{
            Bitmap, HashBits, Shift, BITS_PER_SUBKEY, FULL_NODE_MASK, index, mask,
            sparse_index};

        /// A persistent hash array mapped trie implementation using reference counting.
        ///
        /// Keys are required to implement `Hash` and `Eq` like `std::collections::HashMap`, but
        /// both keys and values are also required to implement `Clone`. If you have an expensive
        /// to clone key or value type like a `String` or `Vec`, you can wrap it in a reference
        /// counting smart pointer.

        #[derive(Clone, Debug)]
        pub struct $hamt<K, V> {
            inline: Inline<K, V>
        }

        #[derive(Clone, Debug)]
        enum Inline<K, V> {
            Empty,
            Leaf(HashBits, K, V),
            Alt($rc_alt)
        }

        #[derive(Debug, PartialEq, Eq)]
        enum Alt<K, V> {
            Bitmap(usize, Bitmap, Vec<$hamt<K, V>>),
            Full(usize, Vec<$hamt<K, V>>),
            Collision(HashBits, Vec<(K, V)>)
        }

        #[derive(Clone)]
        enum Traversing<'a, K, V> where K: 'a, V: 'a {
            Leaf(&'a K, &'a V),
            BitmapOrFull(slice::Iter<'a, $hamt<K, V>>),
            Collision(slice::Iter<'a, (K, V)>)
        }

        /// A key value iterator that iterates in an unspecified order.
        #[derive(Clone)]
        pub struct Iter<'a, K, V> where K: 'a, V: 'a {
            size: usize,
            count: usize,
            stack: Vec<Traversing<'a, K, V>>
        }

        /// Key iterator
        #[derive(Clone)]
        pub struct Keys<'a, K, V> where K: 'a, V: 'a {
            iter: Map<Iter<'a, K, V>, fn((&'a K, &'a V)) -> &'a K>
        }

        /// Value iterator
        #[derive(Clone)]
        pub struct Values<'a, K, V> where K: 'a, V: 'a {
            iter: Map<Iter<'a, K, V>, fn((&'a K, &'a V)) -> &'a V>
        }

        impl<'a, K, V> Iterator for Keys<'a, K, V> where K: 'a + Clone, V: 'a + Clone {
            type Item = &'a K;

            fn next(&mut self) -> Option<Self::Item> {
                self.iter.next()
            }
        }

        impl<'a, K, V> Iterator for Values<'a, K, V> where K: 'a + Clone, V: 'a + Clone {
            type Item = &'a V;

            fn next(&mut self) -> Option<Self::Item> {
                self.iter.next()
            }
        }

        fn pair_to_key<'a, K, V>(kv: (&'a K, &'a V)) -> &'a K {
            kv.0
        }

        fn pair_to_value<'a, K, V>(kv: (&'a K, &'a V)) -> &'a V {
            kv.1
        }

        impl<K, V> Eq for $hamt<K, V> where K: Eq, V: Eq { }

        impl<K, V> PartialEq for $hamt<K, V> where K: PartialEq, V: PartialEq {
            fn eq(&self, other: &$hamt<K, V>) -> bool {
                match (&self.inline, &other.inline) {
                    (&Inline::Empty, &Inline::Empty) => true,
                    (&Inline::Leaf(h1, ref k1, ref v1), &Inline::Leaf(h2, ref k2, ref v2)) => {
                        h1 == h2 && k1 == k2 && v1 == v2
                    }
                    (&Inline::Alt(ref rc1), &Inline::Alt(ref rc2)) => {
                        let ptr1: *const Alt<K, V> = rc1.deref();
                        let ptr2: *const Alt<K, V> = rc2.deref();
                        if ptr1 == ptr2 {
                            true // don't have to check shared structure
                        } else {
                            rc1.deref() == rc2.deref()
                        }
                    }
                    (_, _) => false
                }
            }
        }

        impl<'a, K, V> Iterator for Iter<'a, K, V> where K: 'a + Clone, V: 'a + Clone {
            type Item = (&'a K, &'a V);

            fn next(&mut self) -> Option<Self::Item> {
                let last = match self.stack.last() {
                    Some(iter) => (*iter).clone(),
                    None => { return None; }
                };
                match last {
                    Traversing::Leaf(k, v) => {
                        self.stack.pop();
                        self.count += 1;
                        Some((k, v))
                    },
                    Traversing::BitmapOrFull(mut iter) => {
                        let next = iter.next();
                        self.stack.pop();
                        self.stack.push(Traversing::BitmapOrFull(iter));
                        match next {
                            Some(ref hamt) => match hamt.inline {
                                Inline::Empty => {
                                    self.next()
                                },
                                Inline::Leaf(_, ref k, ref v) => {
                                    self.count += 1;
                                    Some((k, v))
                                },
                                Inline::Alt(ref rc) => match *rc.deref() {
                                    Alt::Bitmap(_, _, ref vs) => {
                                        self.stack.push(Traversing::BitmapOrFull(vs.iter()));
                                        self.next()
                                    },
                                    Alt::Full(_, ref vs) => {
                                        self.stack.push(Traversing::BitmapOrFull(vs.iter()));
                                        self.next()
                                    },
                                    Alt::Collision(_, ref vs) => {
                                        self.stack.push(Traversing::Collision(vs.iter()));
                                        self.next()
                                    }
                                }
                            },
                            None => {
                                self.stack.pop();
                                self.next()
                            }
                        }
                    },
                    Traversing::Collision(mut iter) => match iter.next() {
                        Some(ref kv) => {
                            self.count += 1;
                            self.stack.pop();
                            self.stack.push(Traversing::Collision(iter));
                            Some((&kv.0, &kv.1))
                        },
                        None => {
                            self.stack.pop();
                            self.next()
                        }
                    }
                }
            }

            fn size_hint(&self) -> (usize, Option<usize>) {
                (self.size - self.count, Some(self.size - self.count))
            }
        }

        impl<K, V> FromIterator<(K, V)> for $hamt<K, V> where K: Eq + Hash + Clone, V: Clone{
            fn from_iter<T>(iterator: T) -> Self where T: IntoIterator<Item=(K, V)> {
                iterator.into_iter().fold($hamt::new(), |x, kv| x.insert(&kv.0, &kv.1))
            }
        }

        impl<'a, K, V> FromIterator<(&'a K, &'a V)> for $hamt<K, V> where K: Eq + Hash + Clone, V: Clone{
            fn from_iter<T>(iterator: T) -> Self where T: IntoIterator<Item=(&'a K, &'a V)> {
                iterator.into_iter().fold($hamt::new(), |x, kv| x.insert(kv.0, kv.1))
            }
        }

        impl<'a, K, V> IntoIterator for &'a $hamt<K, V> where K: Hash + Eq + Clone + 'a, V: Clone + 'a {
            type Item = (&'a K, &'a V);
            type IntoIter = Iter<'a, K, V>;

            fn into_iter(self) -> Iter<'a, K, V> {
                self.iter()
            }
        }

        impl<'a, K, Q: ?Sized, V> Index<&'a Q> for $hamt<K, V>
            where K: Hash + Eq + Clone + Borrow<Q>, V: Clone, Q: Eq + Hash {
            type Output = V;
            fn index(&self, index: &Q) -> &Self::Output {
                self.get(index).expect("key not in hamt")
            }
        }

        impl<K, V> $hamt<K, V> where K: Hash + Eq + Clone, V: Clone {
            /// Creates an empty map.
            pub fn new() -> Self {
                $hamt {
                    inline: Inline::Empty
                }
            }

            fn leaf(h: HashBits, k: K, v: V) -> Self {
                $hamt {
                    inline: Inline::Leaf(h, k, v)
                }
            }

            fn collision(h: HashBits, k: K, v: V, k0: &K, v0: &V) -> Self {
                $hamt {
                    inline: Inline::Alt($rc_new(Alt::Collision(h, vec![(k, v), (k0.clone(), v0.clone())])))
                }
            }

            fn collision_delete(h: HashBits, idx: usize, vs: &[(K, V)]) -> Self {
                let mut vs_prime = vs.clone().to_vec();
                vs_prime.remove(idx);
                $hamt {
                    inline: Inline::Alt($rc_new(Alt::Collision(h, vs_prime)))
                }
            }

            fn collision_update<Q: ?Sized>(h: HashBits, k: &Q, v: V, vs: &[(K, V)]) -> Self
                where K: Borrow<Q>, Q: Hash + Eq + ToOwned<Owned=K> {
                let mut vs_prime = vs.clone().to_vec();
                match vs.iter().position(|ref i| i.0.borrow() == k) {
                    Some(idx) => {
                        vs_prime[idx].1 = v;
                    },
                    None => {
                        vs_prime.push((k.to_owned(), v));
                    }
                }
                $hamt {
                    inline: Inline::Alt($rc_new(Alt::Collision(h, vs_prime)))
                }
            }

            fn collision_adjust<F, Q: ?Sized>(h: HashBits, key: &Q, f: F, vs: &[(K, V)]) -> Self
                where F: FnOnce(&V) -> V, K: Borrow<Q>, Q: Hash + Eq {
                let mut vs_prime = vs.clone().to_vec();
                match vs.iter().position(|ref i| i.0.borrow() == key) {
                    Some(idx) => {
                        vs_prime[idx].1 = f(&vs_prime[idx].1);
                    },
                    _ => {
                        ;
                    }
                }
                $hamt {
                    inline: Inline::Alt($rc_new(Alt::Collision(h, vs_prime)))
                }
            }

            fn bitmap_indexed_or_full(b: Bitmap, vs: Vec<$hamt<K, V>>) -> Self {
                if b == FULL_NODE_MASK {
                    let size = (&vs).iter().map(|ref st| st.len()).fold(0, |x,y| x+y);
                    $hamt {
                        inline: Inline::Alt($rc_new(Alt::Full(size, vs)))
                    }
                } else {
                    $hamt::bitmap(b, vs)
                }
            }

            fn bitmap(b: Bitmap, vs: Vec<$hamt<K, V>>) -> Self {
                let size = (&vs).iter().map(|ref st| st.len()).fold(0, |x,y| x+y);
                $hamt {
                    inline: Inline::Alt($rc_new(Alt::Bitmap(size, b, vs)))
                }
            }

            fn full(vs: Vec<$hamt<K, V>>) -> Self {
                let size = (&vs).iter().map(|ref st| st.len()).fold(0, |x,y| x+y);
                $hamt {
                    inline: Inline::Alt($rc_new(Alt::Full(size, vs)))
                }
            }

            fn two(h: HashBits, s: Shift, k: K, v: V, h0: HashBits, k0: &K, v0: &V) -> Self {
                let bp1 = mask(h, s);
                let bp2 = mask(h0, s);
                if bp1 == bp2 {
                    let st = $hamt::two(h, s + BITS_PER_SUBKEY, k, v, h0, k0, v0);
                    $hamt::bitmap(bp1, vec![st])
                } else {
                    let l1 = $hamt::leaf(h, k, v);
                    let l2 = $hamt::leaf(h0, k0.clone(), v0.clone());
                    if index(h, s) < index(h0, s) {
                        $hamt::bitmap(bp1 | bp2, vec![l1, l2])
                    } else {
                        $hamt::bitmap(bp1 | bp2, vec![l2, l1])
                    }
                }
            }

            fn is_leaf_or_collision(&self) -> bool {
                match self.inline {
                    Inline::Leaf(_, _, _) => true,
                    Inline::Alt(ref rc) => match *rc.deref() {
                        Alt::Collision(_, _) => true,
                        _ => false
                    },
                    _ => false
                }
            }

            /// Returns how many key value pairs are in the map.
            pub fn len(&self) -> usize {
                match self.inline {
                    Inline::Empty => 0,
                    Inline::Leaf(_, _, _) => 1,
                    Inline::Alt(ref rc) => match *rc.deref() {
                        Alt::Bitmap(size, _, _) => size,
                        Alt::Full(size, _) => size,
                        Alt::Collision(_, ref vs) => vs.len()
                    }
                }
            }

            /// Returns true if there are no key value pairs in the map, false otherwise.
            pub fn is_empty(&self) -> bool {
                self.len() == 0
            }

            /// Returns a key value iterator.
            pub fn iter(&self) -> Iter<K, V> {
                Iter {
                    size: self.len(),
                    count: 0,
                    stack: match self.inline {
                        Inline::Empty => vec![],
                        Inline::Leaf(_, ref k, ref v) => vec![Traversing::Leaf(k, v)],
                        Inline::Alt(ref rc) => match *rc.deref() {
                            Alt::Bitmap(_, _, ref vs) => vec![Traversing::BitmapOrFull(vs.iter())],
                            Alt::Full(_, ref vs) => vec![Traversing::BitmapOrFull(vs.iter())],
                            Alt::Collision(_, ref vs) => vec![Traversing::Collision(vs.iter())]
                        }
                    }
                }
            }

            /// Returns an iterator that visits every key in an unspecified order.
            pub fn keys(&self) -> Keys<K, V> {
                Keys { iter: self.iter().map(pair_to_key) }
            }

            /// Returns an iterator that visits every value in an unspecified order.
            pub fn values(&self) -> Values<K, V> {
                Values { iter: self.iter().map(pair_to_value) }
            }

            /// Returns a reference to the value corresponding to the given key, or None if there
            /// is no value associated with the key.
            pub fn get<Q: ?Sized>(&self, k: &Q) -> Option<&V>
                where K: Borrow<Q>, Q: Hash + Eq
            {
                let mut sh = SipHasher::new();
                k.hash(&mut sh);
                let h = sh.finish();
                let mut shift = 0;
                let mut hamt = self;
                loop {
                    match hamt.inline {
                        Inline::Empty => {
                            return None;
                        },
                        Inline::Leaf(lh, ref lk, ref lv) => {
                            if h == lh && k == lk.borrow() {
                                return Some(&lv);
                            } else {
                                return None;
                            }
                        },
                        Inline::Alt(ref rc) => match *rc.deref() {
                            Alt::Bitmap(_, b, ref vs) => {
                                let m = mask(h, shift);
                                if b & m == 0 {
                                    return None;
                                } else {
                                    shift += BITS_PER_SUBKEY;
                                    hamt = &vs[sparse_index(b, m)];
                                    continue;
                                }
                            },
                            Alt::Full(_, ref vs) => {
                                hamt = &vs[index(h, shift)];
                                shift += BITS_PER_SUBKEY;
                                continue;
                            },
                            Alt::Collision(hx, ref vs) => {
                                if h == hx {
                                    for kv in vs {
                                        if k == kv.0.borrow() {
                                            return Some(&kv.1);
                                        }
                                    }
                                }
                                return None;
                            }
                        }
                    }
                }
            }

            /// Returns true if the map contains the given key.
            pub fn contains_key<Q: ?Sized>(&self, k: &Q) -> bool
                where K: Borrow<Q>, Q: Hash + Eq
            {
                self.get(k).is_some()
            }

            // TODO: Upgrade API to use refs and ToOwned everywhere.
            /// Returns a new map that includes the given key value pair, replacing the old value
            /// if the key was already in the map.
            pub fn insert<Q: ?Sized, R: ?Sized>(&self, k: &Q, v: &R) -> Self
                where K: Borrow<Q>, Q: Hash + Eq + ToOwned<Owned=K>,
                      V: Borrow<R>, R: ToOwned<Owned=V>  {
                let mut sh = SipHasher::new();
                k.hash(&mut sh);
                let h = sh.finish();
                self.insert_recur(h, k, v.to_owned(), 0)
            }

            fn insert_recur<Q: ?Sized>(&self, h: HashBits, k: &Q, v: V, s: Shift) -> Self
                where K: Borrow<Q>, Q: Hash + Eq + ToOwned<Owned=K> {
                match self.inline {
                    Inline::Empty => {
                        $hamt::leaf(h, k.to_owned(), v)
                    },
                    Inline::Leaf(h0, ref k0, ref v0) => {
                        if h == h0 {
                            if k == k0.borrow() {
                                $hamt::leaf(h, k.to_owned(), v)
                            } else {
                                $hamt::collision(h, k.to_owned(), v, k0, v0)
                            }
                        } else {
                            $hamt::two(h, s, k.to_owned(), v, h0, k0, v0)
                        }
                    },
                    Inline::Alt(ref rc) => match *rc.deref() {
                        Alt::Bitmap(_, b, ref vs) => {
                            let m = mask(h, s);
                            let i = sparse_index(b, m);
                            if b & m == 0 {
                                let mut vs_prime: Vec<$hamt<K,V>> = (*vs).clone();
                                vs_prime.insert(i, $hamt::leaf(h, k.to_owned(), v));
                                $hamt::bitmap_indexed_or_full(b | m, vs_prime)
                            } else {
                                let st = &vs[i];
                                let new_t = st.insert_recur(h, k, v, s + BITS_PER_SUBKEY);
                                let mut vs_prime: Vec<$hamt<K,V>> = (*vs).clone();
                                vs_prime[i] = new_t;
                                $hamt::bitmap(b, vs_prime)
                            }
                        },
                        Alt::Full(_, ref vs) => {
                            let i = index(h, s);
                            let st = &vs[i];
                            let new_t = st.insert_recur(h, k, v, s + BITS_PER_SUBKEY);
                            let mut new_vs: Vec<$hamt<K,V>> = (*vs).clone();
                            new_vs[i] = new_t;
                            $hamt::full(new_vs)
                        },
                        Alt::Collision(hx, ref vs) => {
                            if h == hx {
                                $hamt::collision_update(h, k, v, vs)
                            } else {
                                let bi = $hamt::bitmap(mask(hx, s), vec![self.clone()]);
                                bi.insert_recur(h, k, v, s)
                            }
                        }
                    }
                }
            }

            /// Returns a new map without an entry corresponding to the given key.
            pub fn remove<Q: ?Sized>(&self, k: &Q) -> Self
                where K: Borrow<Q>, Q: Hash + Eq
            {
                let mut sh = SipHasher::new();
                k.hash(&mut sh);
                let h = sh.finish();
                self.remove_recur(h, k, 0)
            }

            fn remove_recur<Q: ?Sized>(&self, h: HashBits, k: &Q, s: Shift) -> Self
                where K: Borrow<Q>, Q: Hash + Eq
            {
                match self.inline {
                    Inline::Empty => {
                        $hamt::new()
                    },
                    Inline::Leaf(h0, ref k0, _) => {
                        if h == h0 && k == k0.borrow() {
                            $hamt::new()
                        } else {
                            self.clone()
                        }
                    },
                    Inline::Alt(ref rc) => match *rc.deref() {
                        Alt::Bitmap(_, b, ref vs) => {
                            let m = mask(h, s);
                            let i = sparse_index(b, m);
                            if b & m == 0 {
                                return self.clone();
                            }
                            let st = &vs[i];
                            let st_prime = st.remove_recur(h, k, s + BITS_PER_SUBKEY);
                            match st_prime.inline {
                                Inline::Empty => match vs.len() {
                                    1 => {
                                        $hamt::new()
                                    },
                                    2 => {
                                        match (i, &vs[0], &vs[1]) {
                                            (0, _, l) => {
                                                if l.is_leaf_or_collision() {
                                                    return l.clone();
                                                }
                                                let mut vs_prime = vs.clone();
                                                vs_prime.remove(i);
                                                $hamt::bitmap(b & (!m), vs_prime)
                                            },
                                            (1, l, _) => {
                                                if l.is_leaf_or_collision() {
                                                    return l.clone();
                                                }
                                                let mut vs_prime = vs.clone();
                                                vs_prime.remove(i);
                                                $hamt::bitmap(b & (!m), vs_prime)
                                            },
                                            _ => {
                                                let mut vs_prime = vs.clone();
                                                vs_prime.remove(i);
                                                $hamt::bitmap(b & (!m), vs_prime)
                                            }
                                        }
                                    },
                                    _ => {
                                        let mut vs_prime = vs.clone();
                                        vs_prime.remove(i);
                                        $hamt::bitmap(b & (!m), vs_prime)
                                    }
                                },
                                _ => {
                                    if st_prime.is_leaf_or_collision() && vs.len() == 1 {
                                        return st_prime;
                                    }
                                    let mut vs_prime = vs.clone();
                                    vs_prime[i] = st_prime;
                                    $hamt::bitmap(b, vs_prime)
                                }
                            }
                        },
                        Alt::Full(_, ref vs) => {
                            let i = index(h, s);
                            let st = &vs[i];
                            let st_prime = st.remove_recur(h, k, s + BITS_PER_SUBKEY);
                            match st_prime.inline {
                                Inline::Empty => {
                                    let mut vs_prime = vs.clone();
                                    vs_prime.remove(i);
                                    let bm = FULL_NODE_MASK & !(1 << i);
                                    $hamt::bitmap(bm, vs_prime)
                                }
                                _ => {
                                    let mut vs_prime = vs.clone();
                                    vs_prime[i] = st_prime;
                                    $hamt::full(vs_prime)
                                }
                            }
                        }
                        Alt::Collision(hx, ref vs) => {
                            if h == hx {
                                match vs.iter().position(|ref i| i.0.borrow() == k) {
                                    Some(i) => {
                                        if vs.len() == 2 {
                                            if i == 0 {
                                                return $hamt::leaf(h, vs[1].0.clone(), vs[1].1.clone());
                                            } else {
                                                return $hamt::leaf(h, vs[0].0.clone(), vs[0].1.clone());
                                            }
                                        } else {
                                            return $hamt::collision_delete(h, i, vs);
                                        }
                                    },
                                    _ => { return self.clone(); }
                                }
                            }
                            self.clone()
                        }
                    }
                }
            }

            /// Modifies the value tied to the given key with the function `f`. Otherwise, the map returned is identical.
            pub fn adjust<F, Q: ?Sized>(&self, key: &Q, f: F) -> Self
                where F: FnOnce(&V) -> V, K: Borrow<Q>, Q: Hash + Eq {
                let mut sh = SipHasher::new();
                key.hash(&mut sh);
                let h = sh.finish();
                self.adjust_recur(h, key, 0, f)
            }

            fn adjust_recur<F, Q: ?Sized>(&self, h: HashBits, key: &Q, s: Shift, f: F) -> Self
                where F: FnOnce(&V) -> V, K: Borrow<Q>, Q: Hash + Eq {
                match self.inline {
                    Inline::Empty => self.clone(),
                    Inline::Leaf(lh, ref lk, ref lv) => {
                        if h == lh && key == lk.borrow() {
                            $hamt::leaf(h, lk.clone(), f(&lv))
                        } else {
                            self.clone()
                        }
                    },
                    Inline::Alt(ref rc) => match *rc.deref() {
                        Alt::Bitmap(_, b, ref vs) => {
                            let m = mask(h, s);
                            let i = sparse_index(b, m);
                            if b & m == 0 {
                                self.clone()
                            } else {
                                let st = &vs[i];
                                let st_prime = st.adjust_recur(h, key, s + BITS_PER_SUBKEY, f);
                                let mut vs_prime = vs.clone();
                                vs_prime[i] = st_prime;
                                $hamt::bitmap(b, vs_prime)
                            }
                        },
                        Alt::Full(_, ref vs) => {
                            let i = index(h, s);
                            let st = &vs[i];
                            let st_prime = st.adjust_recur(h, key, s + BITS_PER_SUBKEY, f);
                            let mut vs_prime = vs.clone();
                            vs_prime[i] = st_prime;
                            $hamt::full(vs_prime)
                        },
                        Alt::Collision(_, ref vs) => {
                            $hamt::collision_adjust(h, key, f, vs)
                        }
                    }
                }
            }

            /// Updates the value at the given key using `f`. If `f` returns None, then the entry
            /// is removed.
            pub fn update<F, Q: ?Sized>(&self, key: &Q, f: F) -> Self
                where F: FnOnce(&V) -> Option<V>, K: Borrow<Q>, Q: Hash + Eq + ToOwned<Owned=K> {
                match self.get(key) {
                    Some(ref value) => match f(value) {
                        Some(value_prime) => self.insert(key, &value_prime),
                        None => self.remove(key)
                    },
                    None => self.clone()
                }
            }

            /// Updates the value at the given key using `f` as in `Self::update`. If no value exists for
            /// the given key, then `f` is passed `None`.
            pub fn alter<F, Q: ?Sized>(&self, key: &Q, f: F) -> Self
                where F: FnOnce(Option<&V>) -> Option<V>, K: Borrow<Q>, Q: Hash + Eq + ToOwned<Owned=K> {
                match f(self.get(key)) {
                    Some(value) => {
                        self.insert(key, &value)
                    },
                    None => self.remove(key)
                }
            }
        }
    }
}

macro_rules! make_hamt_set_type {
    ($hamtset: ident, $hamt: ident) => {
        #[derive(Clone, Debug)]
        pub struct $hamtset<K> {
            map: $hamt<K, ()>
        }

        impl<K> Eq for $hamtset<K> where K: Eq { }

        impl<K> PartialEq for $hamtset<K> where K: PartialEq {
            fn eq(&self, other: &$hamtset<K>) -> bool {
                self.map.eq(&other.map)
            }
        }

        impl<K> FromIterator<K> for $hamtset<K> where K: Eq + Hash + Clone {
            fn from_iter<T>(iterator: T) -> Self where T: IntoIterator<Item=K> {
                iterator.into_iter().fold($hamtset::new(), |x, k| x.insert(&k))
            }
        }

        impl<'a, K> FromIterator<&'a K> for $hamtset<K> where K: Eq + Hash + Clone {
            fn from_iter<T>(iterator: T) -> Self where T: IntoIterator<Item=&'a K> {
                iterator.into_iter().fold($hamtset::new(), |x, k| x.insert(&k))
            }
        }

        impl<'a, K> IntoIterator for &'a $hamtset<K> where K: Hash + Eq + Clone + 'a {
            type Item = &'a K;
            type IntoIter = Keys<'a, K, ()>;

            fn into_iter(self) -> Keys<'a, K, ()> {
                self.iter()
            }
        }

        impl<K> $hamtset<K> where K: Hash + Eq + Clone {
            /// Returns an empty set.
            pub fn new() -> Self {
                $hamtset { map: $hamt::new() }
            }

            /// Returns how many items are in the set.
            pub fn len(&self) -> usize {
                self.map.len()
            }

            /// Returns true if the set is empty, false otherwise.
            pub fn is_empty(&self) -> bool {
                self.map.is_empty()
            }

            /// Inserts an item into the set.
            pub fn insert<Q: ?Sized>(&self, k: &Q) -> Self where K: Borrow<Q>, Q: Hash + Eq + ToOwned<Owned=K> {
                $hamtset { map: self.map.insert(k,&()) }
            }

            /// Returns true if the set contains the given item, false otherwise.
            pub fn contains<Q: ?Sized>(&self, k: &Q) -> bool where K: Borrow<Q>, Q: Hash + Eq {
                self.map.contains_key(k)
            }

            /// Removes the given item from the set.
            pub fn remove<Q: ?Sized>(&self, k: &Q) -> Self where K: Borrow<Q>, Q: Hash + Eq {
                $hamtset { map: self.map.remove(k) }
            }

            /// Iterates over each item in the set in an unspecified order.
            pub fn iter(&self) -> Keys<K, ()> {
                self.map.keys()
            }
        }
    }
}

pub mod rc {
    use std::rc::Rc;
    make_hamt_type!(HamtRc, Rc, Rc::new, Rc<Alt<K,V>>);
    make_hamt_set_type!(HamtSetRc, HamtRc);

}

pub mod arc {
    use std::sync::Arc;
    make_hamt_type!(HamtArc, Arc, Arc::new, Arc<Alt<K,V>>);
    make_hamt_set_type!(HamtSetArc, HamtArc);
}

pub use rc::{HamtRc, HamtSetRc};
pub use arc::{HamtArc, HamtSetArc};
