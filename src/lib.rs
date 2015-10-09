// TODO: Figure out what to do about 'warning: unused or unknown feature'
#![feature(test)]

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
//TODO: size can be moved into Alt, not needed when you have a Leaf or Collision.
//TODO: Try to mutate in place with Rc/Arc.get_mut().

macro_rules! make_hamt_type {
    ($hamt:ident, $rc:ty, $rc_new:path, $rc_alt:ty) => {
        use std::iter::FromIterator;
        use std::hash::{Hash, Hasher};
        use std::hash::SipHasher;
        use std::borrow::Borrow;
        use std::ops::Deref;
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

        pub struct Iter<'a, K, V> where K: 'a, V: 'a {
            size: usize,
            count: usize,
            stack: Vec<Traversing<'a, K, V>>
        }

        impl<K, V> Eq for $hamt<K, V> where K: Eq, V: Eq { }

        impl<K, V> PartialEq for $hamt<K, V> where K: PartialEq, V: PartialEq {
            fn eq(&self, other: &$hamt<K, V>) -> bool {
                match (&self.inline, &other.inline) {
                    (&Inline::Empty, &Inline::Empty) => { return true; },
                    (&Inline::Leaf(h1, ref k1, ref v1), &Inline::Leaf(h2, ref k2, ref v2)) => {
                        return h1 == h2 && k1 == k2 && v1 == v2;
                    }
                    (&Inline::Alt(ref rc1), &Inline::Alt(ref rc2)) => {
                        let ptr1: *const Alt<K, V> = rc1.deref();
                        let ptr2: *const Alt<K, V> = rc2.deref();
                        if ptr1 == ptr2 {
                            return true; // don't have to check shared structure
                        } else {
                            return rc1.deref() == rc2.deref();
                        }
                    }
                    (_, _) => {
                        return false;
                    }
                }
            }
        }

        impl<'a, K, V> Iterator for Iter<'a, K, V> where K: 'a + Clone, V: 'a + Clone {
            type Item = (&'a K, &'a V);

            fn next(&mut self) -> Option<Self::Item> {
                let last = match self.stack.last() {
                    Option::Some(iter) => (*iter).clone(),
                    Option::None => { return Option::None; }
                };
                match last {
                    Traversing::Leaf(k, v) => {
                        self.stack.pop();
                        self.count += 1;
                        return Option::Some((k, v));
                    },
                    Traversing::BitmapOrFull(mut iter) => {
                        let next = iter.next();
                        self.stack.pop();
                        self.stack.push(Traversing::BitmapOrFull(iter));
                        match next {
                            Option::Some(ref hamt) => match hamt.inline {
                                Inline::Empty => {
                                    return self.next();
                                },
                                Inline::Leaf(_, ref k, ref v) => {
                                    self.count += 1;
                                    return Option::Some((k, v));
                                },
                                Inline::Alt(ref rc) => match rc.deref() {
                                    &Alt::Bitmap(_, _, ref vs) => {
                                        self.stack.push(Traversing::BitmapOrFull(vs.iter()));
                                        return self.next();
                                    },
                                    &Alt::Full(_, ref vs) => {
                                        self.stack.push(Traversing::BitmapOrFull(vs.iter()));
                                        return self.next();
                                    },
                                    &Alt::Collision(_, ref vs) => {
                                        self.stack.push(Traversing::Collision(vs.iter()));
                                        return self.next();
                                    }
                                }
                            },
                            Option::None => {
                                self.stack.pop();
                                return self.next();
                            }
                        }
                    },
                    Traversing::Collision(mut iter) => match iter.next() {
                        Option::Some(ref kv) => {
                            self.count += 1;
                            self.stack.pop();
                            self.stack.push(Traversing::Collision(iter));
                            return Option::Some((&kv.0, &kv.1));
                        },
                        Option::None => {
                            self.stack.pop();
                            return self.next();
                        }
                    }
                }
            }

            fn size_hint(&self) -> (usize, Option<usize>) {
                (self.size - self.count, Option::Some(self.size - self.count))
            }
        }

        impl<K, V> FromIterator<(K, V)> for $hamt<K, V> where K: Eq + Hash + Clone, V: Clone{
            fn from_iter<T>(iterator: T) -> Self where T: IntoIterator<Item=(K, V)> {
                iterator.into_iter().fold($hamt::new(), |x, kv| x.insert(kv.0, kv.1))
            }
        }

        impl<'a, K, V> FromIterator<(&'a K, &'a V)> for $hamt<K, V> where K: Eq + Hash + Clone, V: Clone{
            fn from_iter<T>(iterator: T) -> Self where T: IntoIterator<Item=(&'a K, &'a V)> {
                iterator.into_iter().fold($hamt::new(), |x, kv| x.insert(kv.0.clone(), kv.1.clone()))
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

            fn collision_update(h: HashBits, k: K, v: V, vs: &[(K, V)]) -> Self {
                let mut vs_prime = vs.clone().to_vec();
                match vs.iter().position(|ref i| &i.0 == &k) {
                    Option::Some(idx) => {
                        vs_prime[idx] = (k, v);
                    },
                    Option::None => {
                        vs_prime.push((k, v));
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
                match self.inline {
                    Inline::Leaf(_, _, _) => true,
                    Inline::Alt(ref rc) => match rc.deref() {
                        &Alt::Collision(_, _) => true,
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
                    Inline::Alt(ref rc) => match rc.deref() {
                        &Alt::Bitmap(size, _, _) => size,
                        &Alt::Full(size, _) => size,
                        &Alt::Collision(_, ref vs) => vs.len()
                    }
                }
            }

            /// Returns true if there are no key value pairs in the map, false otherwise.
            pub fn is_empty(&self) -> bool {
                return self.len() == 0
            }

            pub fn iter<'a>(&'a self) -> Iter<'a, K, V> {
                Iter {
                    size: self.len(),
                    count: 0,
                    stack: match self.inline {
                        Inline::Empty => vec![],
                        Inline::Leaf(_, ref k, ref v) => vec![Traversing::Leaf(k, v)],
                        Inline::Alt(ref rc) => match rc.deref() {
                            &Alt::Bitmap(_, _, ref vs) => vec![Traversing::BitmapOrFull(vs.iter())],
                            &Alt::Full(_, ref vs) => vec![Traversing::BitmapOrFull(vs.iter())],
                            &Alt::Collision(_, ref vs) => vec![Traversing::Collision(vs.iter())]
                        }
                    }
                }
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
                            return Option::None;
                        },
                        Inline::Leaf(lh, ref lk, ref lv) => {
                            if h == lh && k == lk.borrow() {
                                return Option::Some(&lv);
                            } else {
                                return Option::None;
                            }
                        },
                        Inline::Alt(ref rc) => match rc.deref() {
                            &Alt::Bitmap(_, b, ref vs) => {
                                let m = mask(h, shift);
                                if b & m == 0 {
                                    return Option::None;
                                } else {
                                    shift += BITS_PER_SUBKEY;
                                    hamt = &vs[sparse_index(b, m)];
                                    continue;
                                }
                            },
                            &Alt::Full(_, ref vs) => {
                                hamt = &vs[index(h, shift)];
                                shift += BITS_PER_SUBKEY;
                                continue;
                            },
                            &Alt::Collision(hx, ref vs) => {
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
                match self.inline {
                    Inline::Empty => {
                        return $hamt::leaf(h, k, v);
                    },
                    Inline::Leaf(h0, ref k0, ref v0) => {
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
                    Inline::Alt(ref rc) => match rc.deref() {
                        &Alt::Bitmap(_, b, ref vs) => {
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
                        &Alt::Full(_, ref vs) => {
                            let i = index(h, s);
                            let ref st = vs[i];
                            let new_t = st.insert_recur(h, k, v, s + BITS_PER_SUBKEY);
                            let mut new_vs: Vec<$hamt<K,V>> = (*vs).clone();
                            new_vs[i] = new_t;
                            return $hamt::full(new_vs);
                        },
                        &Alt::Collision(hx, ref vs) => {
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
                match self.inline {
                    Inline::Empty => {
                        return $hamt::new();
                    },
                    Inline::Leaf(h0, ref k0, _) => {
                        if h == h0 && k == k0.borrow() {
                            return $hamt::new();
                        } else {
                            return self.clone();
                        }
                    },
                    Inline::Alt(ref rc) => match rc.deref() {
                        &Alt::Bitmap(_, b, ref vs) => {
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
                        &Alt::Full(_, ref vs) => {
                            let i = index(h, s);
                            let st = &vs[i];
                            let st_prime = st.remove_recur(h, k, s + BITS_PER_SUBKEY);
                            match st_prime.inline {
                                Inline::Empty => {
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
                        &Alt::Collision(hx, ref vs) => {
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

pub mod rc {
    use std::rc::Rc;
    make_hamt_type!(HamtRc, Rc, Rc::new, Rc<Alt<K,V>>);
}

pub mod arc {
    use std::sync::Arc;
    make_hamt_type!(HamtArc, Arc, Arc::new, Arc<Alt<K,V>>);
}

pub use rc::HamtRc;
pub use arc::HamtArc;

#[cfg(test)]
mod tests {
    extern crate test;
    extern crate quickcheck;
    use self::quickcheck::{Arbitrary, Gen, quickcheck};
    use std::cmp::max;
    use self::test::Bencher;
    use super::{HamtRc, HamtArc};
    use std::collections::HashMap;
    use std::iter::FromIterator;

    impl Arbitrary for HamtArc<isize, isize> {
        fn arbitrary<G: Gen>(g: &mut G) -> Self {
            let mut hamt = HamtArc::new();
            let length: usize = Arbitrary::arbitrary(g);
            for _ in 0..max(length, 2048) {
                let kv: (isize, isize) = Arbitrary::arbitrary(g);
                hamt = hamt.insert(kv.0, kv.1);
            }
            return hamt;
        }
    }

    fn prop_insert_then_get(hamt: HamtArc<isize, isize>, key: isize, value: isize) -> bool {
        hamt.insert(key, value).get(&key) == Option::Some(&value)
    }

    fn prop_insert_then_remove(hamt: HamtArc<isize, isize>, key: isize) -> bool {
        hamt.insert(key, 0).remove(&key).contains_key(&key) == false
    }

    fn prop_insert_then_remove_length_check(hamt: HamtArc<isize, isize>, key: isize) -> bool {
        let hamt_with_key = hamt.insert(key, 0);
        let hamt_without_key = hamt_with_key.remove(&key);
        hamt_with_key.len() == hamt_without_key.len() + 1
    }

    fn prop_from_iter_eq(hamt: HamtArc<isize, isize>) -> bool {
        HamtArc::<isize, isize>::from_iter(hamt.iter()) == hamt
    }

    #[derive(Copy, Clone, Debug)]
    enum Command {
        Insert(isize, isize),
        Remove(isize),
        CheckEquals(isize),
    }

    impl Arbitrary for Command {
        fn arbitrary<G: Gen>(g: &mut G) -> Self {
            let cmd: usize = Arbitrary::arbitrary(g);
            let key: isize = Arbitrary::arbitrary(g);
            match cmd % 5 {
                0 => {
                    Command::CheckEquals(key % 200)
                }
                1 => {
                    Command::Remove(key % 200)
                }
                _ => {
                    let value: isize = Arbitrary::arbitrary(g);
                    Command::Insert(key % 200, value % 200)
                }
            }
        }
    }

    #[derive(Clone, Debug)]
    struct Commands {
        cmds: Vec<Command>,
    }

    impl Arbitrary for Commands {
        fn arbitrary<G: Gen>(g: &mut G) -> Self {
            let mut cmds = Vec::new();
            for _ in 0..50000 {
                cmds.push(Arbitrary::arbitrary(g));
            }
            return Commands { cmds: cmds };
        }
    }

    fn simulation_testing(v: Commands) -> bool {
        let mut hamt: HamtRc<isize, isize> = HamtRc::new();
        let mut hashmap: HashMap<isize, isize> = HashMap::new();
        for cmd in v.cmds {
            match cmd {
                Command::Insert(k, v) => {
                    hamt = hamt.insert(k, v);
                    hashmap.insert(k, v);

                    if hamt.contains_key(&k) != hashmap.contains_key(&k) {
                        return false;
                    }
                }
                Command::Remove(k) => {
                    hamt = hamt.remove(&k);
                    hashmap.remove(&k);

                    if hamt.contains_key(&k) != hashmap.contains_key(&k) {
                        return false;
                    }
                }
                Command::CheckEquals(k) => {
                    if hamt.get(&k) != hashmap.get(&k) {
                        return false;
                    }
                }
            }
            if hamt.len() != hashmap.len() {
                return false;
            }
        }

        for (key, val) in hashmap.iter() {
            if hamt.get(key).unwrap() != val {
                return false;
            }
        }

        for (key, val) in hamt.iter() {
            if hashmap.get(key).unwrap() != val {
                return false;
            }
        }
        return true;
    }

    #[test]
    fn test_prop_insert_then_get() {
        quickcheck(prop_insert_then_get as fn(HamtArc<isize, isize>, isize, isize) -> bool);
    }

    #[test]
    fn test_prop_insert_then_remove() {
        quickcheck(prop_insert_then_remove as fn(HamtArc<isize, isize>, isize) -> bool);
    }

    #[test]
    fn test_prop_insert_then_remove_length_check() {
        quickcheck(prop_insert_then_remove_length_check as fn(HamtArc<isize, isize>, isize) -> bool);
    }

    #[test]
    fn test_prop_from_iter_eq() {
        quickcheck(prop_from_iter_eq as fn(HamtArc<isize, isize>) -> bool);
    }

    #[test]
    fn test_simulation_testing() {
        quickcheck(simulation_testing as fn(Commands) -> bool);
    }

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
            for (_, _) in hamt.iter() {
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
            for (_, _) in hashmap.iter() {
                count += 1;
            }
        })
    }
}
