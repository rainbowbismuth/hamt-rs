// TODO: Figure out what to do about 'warning: unused or unknown feature'
#![feature(test)]

mod internal {
    use std::ops::Index;
    use std::slice;

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

    #[derive(Clone, Debug)]
    pub enum SmallVec<T> {
        Zero,
        One(T),
        Two(T, T),
        Big(Vec<T>),
    }

    impl<T> SmallVec<T> {
        pub fn new() -> Self {
            SmallVec::Zero
        }

        pub fn one(t: T) -> Self {
            SmallVec::One(t)
        }

        pub fn two(x: T, y: T) -> Self {
            SmallVec::Two(x, y)
        }

        pub fn big(ts: Vec<T>) -> Self {
            SmallVec::Big(ts)
        }

        #[inline]
        pub fn len(&self) -> usize {
            match self {
                &SmallVec::Big(ref ts) => ts.len(),
                &SmallVec::Zero => 0,
                &SmallVec::One(_) => 1,
                &SmallVec::Two(_, _) => 2,
            }
        }

        pub fn push(self, t: T) -> Self {
            match self {
                SmallVec::Big(mut ts) => {
                    ts.push(t);
                    SmallVec::Big(ts)
                }
                SmallVec::Zero => {
                    SmallVec::One(t)
                }
                SmallVec::One(x) => {
                    SmallVec::Two(x, t)
                }
                SmallVec::Two(x, y) => {
                    SmallVec::Big(vec![x, y, t])
                }
            }
        }

        pub fn insert(self, idx: usize, t: T) -> Self {
            match self {
                SmallVec::Big(mut ts) => {
                    ts.insert(idx, t);
                    return SmallVec::Big(ts);
                }
                SmallVec::Zero => {
                    assert!(idx == 0);
                    return SmallVec::One(t);
                }
                SmallVec::One(x) => {
                    match idx {
                        0 => {
                            return SmallVec::Two(t, x);
                        }
                        1 => {
                            return SmallVec::Two(x, t);
                        }
                        _ => {
                            panic!("index out of bounds");
                        }
                    }
                }
                SmallVec::Two(x, y) => {
                    match idx {
                        0 => {
                            return SmallVec::Big(vec![t, x, y]);
                        }
                        1 => {
                            return SmallVec::Big(vec![x, t, y]);
                        }
                        2 => {
                            return SmallVec::Big(vec![x, y, t]);
                        }
                        _ => {
                            panic!("index out of bounds");
                        }
                    }
                }
            }
        }

        pub fn remove(self, idx: usize) -> Self {
            match self {
                SmallVec::Big(mut ts) => {
                    ts.remove(idx);
                    return SmallVec::Big(ts);
                }
                SmallVec::Zero => {
                    panic!("empty smallvec");
                }
                SmallVec::One(_) => {
                    assert!(idx == 0, "index out of bounds");
                    return SmallVec::Zero;
                }
                SmallVec::Two(x, y) => {
                    match idx {
                        0 => {
                            return SmallVec::One(y);
                        }
                        1 => {
                            return SmallVec::One(x);
                        }
                        _ => {
                            panic!("index out of bounds");
                        }
                    }
                }
            }
        }

        pub fn update(self, idx: usize, t: T) -> Self {
            match self {
                SmallVec::Big(mut ts) => {
                    ts[idx] = t;
                    return SmallVec::Big(ts);
                }
                SmallVec::Zero => {
                    panic!("empty smallvec");
                }
                SmallVec::One(_) => {
                    assert!(idx == 0, "index out of bounds");
                    return SmallVec::One(t);
                }
                SmallVec::Two(x, y) => {
                    match idx {
                        0 => {
                            return SmallVec::Two(t, y);
                        }
                        1 => {
                            return SmallVec::Two(x, t);
                        }
                        _ => {
                            panic!("index out of bounds");
                        }
                    }
                }
            }
        }

        pub fn iter<'a>(&'a self) -> Iter<'a, T> {
            match self {
                &SmallVec::Big(ref ts) => {
                    return Iter { state: IterState::SliceIter(ts.iter()) };
                }
                &SmallVec::Zero => {
                    return Iter { state: IterState::Done };
                }
                &SmallVec::One(ref x) => {
                    return Iter { state: IterState::OneLeft(x) };
                }
                &SmallVec::Two(ref x, ref y) => {
                    return Iter { state: IterState::TwoLeft(x, y) };
                }
            }
        }

        pub fn steal_big(self) -> Vec<T> {
            match self {
                SmallVec::Big(ts) => ts,
                _ => { panic!("not a big smallvec"); }
            }
        }
    }

    impl<T> Index<usize> for SmallVec<T> {
        type Output = T;

        fn index<'a>(&'a self, idx: usize) -> &'a Self::Output {
            match self {
                &SmallVec::Big(ref ts) => {
                    return &ts[idx];
                }
                &SmallVec::Zero => {
                    panic!("empty smallvec");
                }
                &SmallVec::One(ref x) => {
                    assert!(idx == 0, "index out of bounds");
                    return x;
                }
                &SmallVec::Two(ref x, ref y) => {
                    match idx {
                        0 => {
                            return x;
                        }
                        1 => {
                            return y;
                        }
                        _ => {
                            panic!("index out of bounds");
                        }
                    }
                }
            }
        }
    }

    enum IterState<'a, T>
        where T: 'a
{
        Done,
        OneLeft(&'a T),
        TwoLeft(&'a T, &'a T),
        SliceIter(slice::Iter<'a, T>),
    }

    pub struct Iter<'a, T>
        where T: 'a
{
        state: IterState<'a, T>,
    }

    impl<'a, T> Iterator for Iter<'a, T> where T: 'a {
        type Item = &'a T;

        fn next(&mut self) -> Option<Self::Item> {
            let (res, state_prime) = match &self.state {
                &IterState::SliceIter(ref i) => {
                    let mut i_prime = i.clone();
                    let res = i_prime.next();
                    (res, IterState::SliceIter(i_prime))
                }
                &IterState::Done => {
                    (Option::None, IterState::Done)
                }
                &IterState::OneLeft(x) => {
                    (Option::Some(x), IterState::Done)
                }
                &IterState::TwoLeft(x, y) => {
                    (Option::Some(x), IterState::OneLeft(y))
                }
            };
            self.state = state_prime;
            return res;
        }
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

        use std::hash::{Hash, Hasher};
        use std::hash::SipHasher;
        use std::borrow::Borrow;
        use std::ops::Deref;
        use super::internal::{
            Bitmap, HashBits, Shift, BITS_PER_SUBKEY, FULL_NODE_MASK, index, mask,
            sparse_index, SmallVec};

        /// A persistent hash array mapped trie implementation using reference counting.
        ///
        /// Keys are required to implement `Hash` and `Eq` like `std::collections::HashMap`, but
        /// both keys and values are also required to implement `Clone`. If you have an expensive
        /// to clone key or value type like a `String` or `Vec`, you can wrap it in a reference
        /// counting smart pointer.

        #[derive(Clone, Debug)]
        pub struct $hamt<K, V> {
            size: usize,
            alt: Option<$rc_alt>
        }

        #[derive(Debug)]
        enum Alt<K, V> {
            Bitmap(Bitmap, SmallVec<$hamt<K, V>>),
            Full(Vec<$hamt<K, V>>),
            Collision(HashBits, SmallVec<(K, V)>)
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
                    alt: Option::Some($rc_new(Alt::Collision(h,
                        SmallVec::one((k,v)))))
                }
            }

            fn collision_delete(h: HashBits, idx: usize, vs: &SmallVec<(K, V)>) -> Self {
                let vs_prime = vs.clone().remove(idx);
                let len = vs_prime.len();
                $hamt {
                    size: len,
                    alt: Option::Some($rc_new(Alt::Collision(h, vs_prime)))
                }
            }

            fn collision_update(h: HashBits, k: K, v: V, vs: &SmallVec<(K, V)>) -> Self {
                let mut vs_prime = vs.clone();
                match vs.iter().position(|ref i| &i.0 == &k) {
                    Option::Some(idx) => {
                        vs_prime = vs_prime.update(idx, (k, v));
                    },
                    Option::None => {
                        vs_prime = vs_prime.push((k, v));
                    }
                }
                let len = vs_prime.len();
                $hamt {
                    size: len,
                    alt: Option::Some($rc_new(Alt::Collision(h, vs_prime)))
                }
            }

            fn bitmap_indexed_or_full(b: Bitmap, vs: SmallVec<$hamt<K, V>>) -> Self {
                if b == FULL_NODE_MASK {
                    let size = (&vs).iter().map(|ref st| st.len()).fold(0, |x,y| x+y);
                    $hamt {
                        size: size,
                        alt: Option::Some($rc_new(Alt::Full(vs.steal_big())))
                    }
                } else {
                    $hamt::bitmap(b, vs)
                }
            }

            fn bitmap(b: Bitmap, vs: SmallVec<$hamt<K, V>>) -> Self {
                let size = (&vs).iter().map(|ref st| st.len()).fold(0, |x,y| x+y);
                $hamt {
                    size: size,
                    alt: Option::Some($rc_new(Alt::Bitmap(b, vs)))
                }
            }

            fn full(vs: Vec<$hamt<K, V>>) -> Self {
                let size = (&vs).iter().map(|ref st| st.len()).fold(0, |x,y| x+y);
                $hamt {
                    size: size,
                    alt: Option::Some($rc_new(Alt::Full(vs)))
                }
            }

            fn is_leaf_or_collision(&self) -> bool {
                match self.alt {
                    Option::None => {
                        false
                    },
                    Option::Some(ref rc) => {
                        match rc.deref() {
                            &Alt::Collision(_, _) => true,
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
                                &Alt::Bitmap(b, ref vs) => {
                                    let m = mask(h, shift);
                                    if b & m == 0 {
                                        return Option::None;
                                    } else {
                                        shift += BITS_PER_SUBKEY;
                                        hamt = &vs[sparse_index(b, m)];
                                        continue;
                                    }
                                },
                                &Alt::Full(ref vs) => {
                                    hamt = &vs[index(h, shift)];
                                    shift += BITS_PER_SUBKEY;
                                    continue;
                                },
                                &Alt::Collision(hx, ref vs) => {
                                    if h == hx {
                                        for kv in vs.iter() {
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
                            &Alt::Bitmap(b, ref vs) => {
                                let m = mask(h, s);
                                let i = sparse_index(b, m);
                                if b & m == 0 {
                                    let mut vs_prime: SmallVec<$hamt<K,V>> = (*vs).clone();
                                    vs_prime = vs_prime.insert(i, $hamt::leaf(h, k, v));
                                    return $hamt::bitmap_indexed_or_full(b | m, vs_prime);
                                } else {
                                    let ref st = vs[i];
                                    let new_t = st.insert_recur(h, k, v, s + BITS_PER_SUBKEY);
                                    let mut vs_prime: SmallVec<$hamt<K,V>> = (*vs).clone();
                                    vs_prime = vs_prime.update(i, new_t);
                                    return $hamt::bitmap(b, vs_prime);
                                }
                            },
                            &Alt::Full(ref vs) => {
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
                                    let bi = $hamt::bitmap(mask(hx, s), SmallVec::one(self.clone()));
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
                            &Alt::Bitmap(b, ref vs) => {
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
                                                        vs_prime = vs_prime.remove(i);
                                                        return $hamt::bitmap(b & (!m), vs_prime);
                                                    },
                                                    (1, l, _) => {
                                                        if l.is_leaf_or_collision() {
                                                            return l.clone();
                                                        }
                                                        let mut vs_prime = vs.clone();
                                                        vs_prime = vs_prime.remove(i);
                                                        return $hamt::bitmap(b & (!m), vs_prime);
                                                    },
                                                    _ => {
                                                        let mut vs_prime = vs.clone();
                                                        vs_prime = vs_prime.remove(i);
                                                        return $hamt::bitmap(b & (!m), vs_prime);
                                                    }
                                                }
                                            },
                                            _ => {
                                                let mut vs_prime = vs.clone();
                                                vs_prime = vs_prime.remove(i);
                                                return $hamt::bitmap(b & (!m), vs_prime);
                                            }
                                        }
                                    },
                                    _ => {
                                        if st_prime.is_leaf_or_collision() && vs.len() == 1 {
                                            return st_prime;
                                        }
                                        let mut vs_prime = vs.clone();
                                        vs_prime = vs_prime.update(i, st_prime);
                                        return $hamt::bitmap(b, vs_prime);
                                    }
                                }
                            },
                            &Alt::Full(ref vs) => {
                                let i = index(h, s);
                                let st = &vs[i];
                                let st_prime = st.remove_recur(h, k, s + BITS_PER_SUBKEY);
                                match st_prime.alt {
                                    Option::None => {
                                        let mut vs_prime = vs.clone();
                                        vs_prime.remove(i);
                                        let bm = FULL_NODE_MASK & !(1 << i);
                                        return $hamt::bitmap(bm, SmallVec::big(vs_prime));
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
}
