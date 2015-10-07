use std::rc::Rc;
use std::sync::Arc;
use std::hash::{Hash, Hasher};
use std::hash::SipHasher;
use std::borrow::Borrow;
use std::ops::Deref;

type Bitmap = u64;
type HashBits = u64;
type Shift = u64;

const BITS_PER_SUBKEY: u64 = 4;
//const MAX_CHILDREN: u64 = 16;
const SUBKEY_MASK: Bitmap = 15;
const FULL_NODE_MASK: Bitmap = 65535;

fn index(h: HashBits, s: Shift) -> usize {
    ((h >> s) & SUBKEY_MASK) as usize
}

fn mask(h: HashBits, s: Shift) -> u64 {
    1 << index(h, s)
}

fn sparse_index(b: Bitmap, m: Bitmap) -> usize {
    ((b & (m - 1)).count_ones()) as usize
}

macro_rules! make_hamt_type {
    ($hamt:ident, $alt:ident, $rc:ty, $rc_new:path, $rc_alt:ty) => {
        /// A persistent hash array mapped trie implementation using reference counting.
        ///
        /// Keys are required to implement `Hash` and `Eq` like `std::collections::HashMap`, but
        /// also both keys and values are required to implement `Clone`. If you have an expensive
        /// to clone key or value type like a `String` or `Vec`, you can wrap it in a reference
        /// counting smart pointer.

        #[derive(Clone, Debug)]
        pub struct $hamt<K, V> {
            size: usize,
            alt: Option<$rc_alt>
        }

        #[derive(Debug)]
        enum $alt<K, V> {
            Leaf(HashBits, K, V),
            Bitmap(Bitmap, Vec<$hamt<K, V>>),
            Full(Vec<$hamt<K, V>>),
            Collision(HashBits, Vec<(K, V)>)
        }

        impl<K, V> $hamt<K, V> where K: Hash + Eq + Clone, V: Clone {
            /// Creates an empty map.
            pub fn new() -> Self {
                $hamt {
                    size: 0,
                    alt: Option::None
                }
            }

            fn leaf(h: HashBits, k: K, v: V) -> Self {
                $hamt {
                    size: 1,
                    alt: Option::Some($rc_new($alt::Leaf(h, k, v)))
                }
            }

            fn collision(h: HashBits, k: K, v: V, k0: &K, v0: &V) -> Self {
                $hamt {
                    size: 2,
                    alt: Option::Some($rc_new($alt::Collision(h, vec![(k, v), (k0.clone(), v0.clone())])))
                }
            }

            fn collision_delete(h: HashBits, idx: usize, vs: &Vec<(K, V)>) -> Self {
                let mut vs_prime = vs.clone();
                vs_prime.remove(idx);
                let len = vs_prime.len();
                $hamt {
                    size: len,
                    alt: Option::Some($rc_new($alt::Collision(h, vs_prime)))
                }
            }

            fn collision_update(h: HashBits, k: K, v: V, vs: &Vec<(K, V)>) -> Self {
                let mut vs_prime = vs.clone();
                match vs.iter().position(|ref i| &i.0 == &k) {
                    Option::Some(idx) => {
                        vs_prime[idx] = (k, v);
                    },
                    Option::None => {
                        vs_prime.push((k, v));
                    }
                }
                let len = vs_prime.len();
                $hamt {
                    size: len,
                    alt: Option::Some($rc_new($alt::Collision(h, vs_prime)))
                }
            }

            fn bitmap_indexed_or_full(b: Bitmap, vs: Vec<$hamt<K, V>>) -> Self {
                if b == FULL_NODE_MASK {
                    let size = (&vs).iter().map(|ref st| st.len()).fold(0, |x,y| x+y);
                    $hamt {
                        size: size,
                        alt: Option::Some($rc_new($alt::Full(vs)))
                    }
                } else {
                    $hamt::bitmap(b, vs)
                }
            }

            fn bitmap(b: Bitmap, vs: Vec<$hamt<K, V>>) -> Self {
                let size = (&vs).iter().map(|ref st| st.len()).fold(0, |x,y| x+y);
                $hamt {
                    size: size,
                    alt: Option::Some($rc_new($alt::Bitmap(b, vs)))
                }
            }

            fn full(vs: Vec<$hamt<K, V>>) -> Self {
                let size = (&vs).iter().map(|ref st| st.len()).fold(0, |x,y| x+y);
                $hamt {
                    size: size,
                    alt: Option::Some($rc_new($alt::Full(vs)))
                }
            }

            fn two(h: HashBits, s: Shift, k: K, v: V, h0: HashBits, k0: &K, v0: &V) -> Self {
                let bp1 = mask(h, s);
                let bp2 = mask(h0, s);
                if bp1 == bp2 {
                    let st = $hamt::two(h, s + BITS_PER_SUBKEY, k, v, h0, k0, v0);
                    return $hamt::bitmap(bp1, vec![st]);
                } else {
                    let l1 = $hamt::leaf(h, k, v);
                    let l2 = $hamt::leaf(h0, k0.clone(), v0.clone());
                    if index(h, s) < index(h0, s) {
                        return $hamt::bitmap(bp1 | bp2, vec![l1, l2]);
                    } else {
                        return $hamt::bitmap(bp1 | bp2, vec![l2, l1]);
                    }
                }
            }

            fn is_leaf_or_collision(&self) -> bool {
                match self.alt {
                    Option::None => {
                        false
                    },
                    Option::Some(ref rc) => {
                        match rc.deref() {
                            &$alt::Leaf(_, _, _) => true,
                            &$alt::Collision(_, _) => true,
                            _ => false
                        }
                    }
                }
            }

            /// Returns how many key value pairs are in the map.
            pub fn len(&self) -> usize {
                return self.size
            }

            /// Returns true if there are no key value pairs in the map, false otherwise.
            pub fn is_empty(&self) -> bool {
                return self.size == 0
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
                    match hamt.alt {
                        Option::None => {
                            return Option::None;
                        },
                        Option::Some(ref rc) => {
                            match rc.deref() {
                                &$alt::Leaf(lh, ref lk, ref lv) => {
                                    if h == lh && k == lk.borrow() {
                                        return Option::Some(&lv);
                                    } else {
                                        return Option::None;
                                    }
                                },
                                &$alt::Bitmap(b, ref vs) => {
                                    let m = mask(h, shift);
                                    if b & m == 0 {
                                        return Option::None;
                                    } else {
                                        shift += BITS_PER_SUBKEY;
                                        hamt = &vs[sparse_index(b, m)];
                                        continue;
                                    }
                                },
                                &$alt::Full(ref vs) => {
                                    hamt = &vs[index(h, shift)];
                                    shift += BITS_PER_SUBKEY;
                                    continue;
                                },
                                &$alt::Collision(hx, ref vs) => {
                                    if h == hx {
                                        for kv in vs {
                                            if k == kv.0.borrow() {
                                                return Option::Some(&kv.1);
                                            }
                                        }
                                    }
                                    return Option::None;
                                }
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

            /// Returns a new map that includes the given key value pair, replacing the old value
            /// if the key was already in the map.
            pub fn insert(&self, k: K, v: V) -> Self {
                let mut sh = SipHasher::new();
                k.hash(&mut sh);
                let h = sh.finish();
                return self.insert_recur(h, k, v, 0);
            }

            fn insert_recur(&self, h: HashBits, k: K, v: V, s: Shift) -> Self {
                match self.alt {
                    Option::None => {
                        return $hamt::leaf(h, k, v);
                    },
                    Option::Some(ref rc) => {
                        match rc.deref() {
                            &$alt::Leaf(h0, ref k0, ref v0) => {
                                if h == h0 {
                                    if &k == k0 {
                                        return $hamt::leaf(h, k, v);
                                    } else {
                                        return $hamt::collision(h, k, v, k0, v0);
                                    }
                                } else {
                                    return $hamt::two(h, s, k, v, h0, k0, v0);
                                }
                            },
                            &$alt::Bitmap(b, ref vs) => {
                                let m = mask(h, s);
                                let i = sparse_index(b, m);
                                if b & m == 0 {
                                    let mut vs_prime: Vec<$hamt<K,V>> = (*vs).clone();
                                    vs_prime.insert(i, $hamt::leaf(h, k, v));
                                    return $hamt::bitmap_indexed_or_full(b | m, vs_prime);
                                } else {
                                    let ref st = vs[i];
                                    let new_t = st.insert_recur(h, k, v, s + BITS_PER_SUBKEY);
                                    let mut vs_prime: Vec<$hamt<K,V>> = (*vs).clone();
                                    vs_prime[i] = new_t;
                                    return $hamt::bitmap(b, vs_prime);
                                }
                            },
                            &$alt::Full(ref vs) => {
                                let i = index(h, s);
                                let ref st = vs[i];
                                let new_t = st.insert_recur(h, k, v, s + BITS_PER_SUBKEY);
                                let mut new_vs: Vec<$hamt<K,V>> = (*vs).clone();
                                new_vs[i] = new_t;
                                return $hamt::full(new_vs);
                            },
                            &$alt::Collision(hx, ref vs) => {
                                if h == hx {
                                    return $hamt::collision_update(h, k, v, vs);
                                } else {
                                    let bi = $hamt::bitmap(mask(hx, s), vec![self.clone()]);
                                    return bi.insert_recur(h, k, v, s);
                                }
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
                return self.remove_recur(h, k, 0);
            }

            fn remove_recur<Q: ?Sized>(&self, h: HashBits, k: &Q, s: Shift) -> Self
                where K: Borrow<Q>, Q: Hash + Eq
            {
                match self.alt {
                    Option::None => {
                        return $hamt::new();
                    },
                    Option::Some(ref rc) => {
                        match rc.deref() {
                            &$alt::Leaf(h0, ref k0, _) => {
                                if h == h0 && k == k0.borrow() {
                                    return $hamt::new();
                                } else {
                                    return self.clone();
                                }
                            },
                            &$alt::Bitmap(b, ref vs) => {
                                let m = mask(h, s);
                                let i = sparse_index(b, m);
                                if b & m == 0 {
                                    return self.clone();
                                }
                                let st = &vs[i];
                                let st_prime = st.remove_recur(h, k, s + BITS_PER_SUBKEY);
                                match st_prime.alt {
                                    Option::None => {
                                        match vs.len() {
                                            1 => {
                                                return $hamt::new();
                                            },
                                            2 => {
                                                match (i, &vs[0], &vs[1]) {
                                                    (0, _, l) => {
                                                        if l.is_leaf_or_collision() {
                                                            return l.clone();
                                                        }
                                                        let mut vs_prime = vs.clone();
                                                        vs_prime.remove(i);
                                                        return $hamt::bitmap(b & (!m), vs_prime);
                                                    },
                                                    (1, l, _) => {
                                                        if l.is_leaf_or_collision() {
                                                            return l.clone();
                                                        }
                                                        let mut vs_prime = vs.clone();
                                                        vs_prime.remove(i);
                                                        return $hamt::bitmap(b & (!m), vs_prime);
                                                    },
                                                    _ => {
                                                        let mut vs_prime = vs.clone();
                                                        vs_prime.remove(i);
                                                        return $hamt::bitmap(b & (!m), vs_prime);
                                                    }
                                                }
                                            },
                                            _ => {
                                                let mut vs_prime = vs.clone();
                                                vs_prime.remove(i);
                                                return $hamt::bitmap(b & (!m), vs_prime);
                                            }
                                        }
                                    },
                                    _ => {
                                        if st_prime.is_leaf_or_collision() && vs.len() == 1 {
                                            return st_prime;
                                        }
                                        let mut vs_prime = vs.clone();
                                        vs_prime[i] = st_prime;
                                        return $hamt::bitmap(b, vs_prime);
                                    }
                                }
                            },
                            &$alt::Full(ref vs) => {
                                let i = index(h, s);
                                let st = &vs[i];
                                let st_prime = st.remove_recur(h, k, s + BITS_PER_SUBKEY);
                                match st_prime.alt {
                                    Option::None => {
                                        let mut vs_prime = vs.clone();
                                        vs_prime.remove(i);
                                        let bm = FULL_NODE_MASK & !(1 << i);
                                        return $hamt::bitmap(bm, vs_prime);
                                    }
                                    _ => {
                                        let mut vs_prime = vs.clone();
                                        vs_prime[i] = st_prime;
                                        return $hamt::full(vs_prime);
                                    }
                                }
                            }
                            &$alt::Collision(hx, ref vs) => {
                                if h == hx {
                                    match vs.iter().position(|ref i| i.0.borrow() == k) {
                                        Option::Some(i) => {
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
                                return self.clone();
                            }
                        }
                    }
                }
            }
        }
    }
}

make_hamt_type!(HamtRc, AltRc, Rc, Rc::new, Rc<AltRc<K,V>>);
make_hamt_type!(HamtArc, AltArc, Arc, Arc::new, Arc<AltArc<K,V>>);

#[cfg(test)]
mod tests {
    extern crate quickcheck;
    use self::quickcheck::{Arbitrary, Gen, quickcheck};
    use std::cmp::max;
    use super::*;

    type Hamt = HamtArc<isize, isize>;

    impl Arbitrary for Hamt {
        fn arbitrary<G: Gen>(g: &mut G) -> Self {
            let mut hamt = HamtArc::new();
            let length: usize = Arbitrary::arbitrary(g);
            for _ in 0 .. max(length, 2048) {
                let kv: (isize, isize) = Arbitrary::arbitrary(g);
                hamt = hamt.insert(kv.0, kv.1);
            }
            return hamt;
        }
    }

    fn prop_insert_then_get(hamt: Hamt, key: isize, value: isize) -> bool {
        hamt.insert(key, value).get(&key) == Option::Some(&value)
    }

    fn prop_insert_then_remove(hamt: Hamt, key: isize) -> bool {
        hamt.insert(key, 0).remove(&key).contains_key(&key) == false
    }

    fn prop_insert_then_remove_length_check(hamt: Hamt, key: isize) -> bool {
        let hamt_with_key = hamt.insert(key, 0);
        let hamt_without_key = hamt_with_key.remove(&key);
        hamt_with_key.len() == hamt_without_key.len() + 1
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
}
