// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

#![cfg_attr(feature="clippy", feature(plugin))]

#![cfg_attr(feature="clippy", plugin(clippy))]

use std::iter::{Map, FromIterator};
use std::hash::{Hash, Hasher};
use std::hash::SipHasher;
use std::borrow::Borrow;
use std::convert::From;
use std::ops::{Deref, Index};
use std::slice;
use std::rc::Rc;
use std::sync::Arc;

pub type Bitmap = u64;
pub type Size = usize;
pub type HashBits = u64;
pub type Shift = u64;

const BITS_PER_SUBKEY: u64 = 4;
const SUBKEY_MASK: Bitmap = 15;

fn index(h: HashBits, s: Shift) -> usize {
    ((h >> s) & SUBKEY_MASK) as usize
}

fn mask(h: HashBits, s: Shift) -> Bitmap {
    1 << index(h, s)
}

fn sparse_index(b: Bitmap, m: Bitmap) -> usize {
    ((b & (m - 1)).count_ones()) as usize
}

#[derive(Debug, Clone)]
pub enum Hamt<K, V, HamtRef> {
    Empty,
    Leaf(HashBits, K, V),
    Bitmap(Size, Bitmap, Vec<HamtRef>),
    Collision(HashBits, Vec<(K, V)>),
}

#[derive(Clone)]
enum Traversing<'a, K, V, HamtRef>
    where K: 'a,
          V: 'a,
          HamtRef: 'a
{
    Leaf(&'a K, &'a V),
    Bitmap(slice::Iter<'a, HamtRef>),
    Collision(slice::Iter<'a, (K, V)>),
}

/// A key value iterator that iterates in an unspecified order.
#[derive(Clone)]
pub struct Iter<'a, K, V, HamtRef>
    where K: 'a,
          V: 'a,
          HamtRef: 'a
{
    size: usize,
    count: usize,
    stack: Vec<Traversing<'a, K, V, HamtRef>>,
}

type KeySelectFn<'a, K, V> = fn((&'a K, &'a V)) -> &'a K;
type ValSelectFn<'a, K, V> = fn((&'a K, &'a V)) -> &'a V;

/// Key iterator
#[derive(Clone)]
pub struct Keys<'a, K, V, HamtRef>
    where K: 'a,
          V: 'a,
          HamtRef: 'a
{
    iter: Map<Iter<'a, K, V, HamtRef>, KeySelectFn<'a, K, V>>,
}

/// Value iterator
#[derive(Clone)]
pub struct Values<'a, K, V, HamtRef>
    where K: 'a,
          V: 'a,
          HamtRef: 'a
{
    iter: Map<Iter<'a, K, V, HamtRef>, ValSelectFn<'a, K, V>>,
}

pub trait HamtRefLike<K, V> : Clone + Deref<Target = Hamt<K, V, Self>> + From<Hamt<K, V, Self>> { }

impl<'a, K, V, HamtRef> Iterator for Keys<'a, K, V, HamtRef>
    where K: 'a + Clone,
          V: 'a + Clone,
          HamtRef: 'a + HamtRefLike<K, V>
{
    type Item = &'a K;

    fn next(&mut self) -> Option<Self::Item> {
        self.iter.next()
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.iter.size_hint()
    }
}

impl<'a, K, V, HamtRef> Iterator for Values<'a, K, V, HamtRef>
    where K: 'a + Clone,
          V: 'a + Clone,
          HamtRef: 'a + HamtRefLike<K, V>
{
    type Item = &'a V;

    fn next(&mut self) -> Option<Self::Item> {
        self.iter.next()
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.iter.size_hint()
    }
}

fn pair_to_key<'a, K, V>(kv: (&'a K, &'a V)) -> &'a K {
    kv.0
}

fn pair_to_value<'a, K, V>(kv: (&'a K, &'a V)) -> &'a V {
    kv.1
}

impl<K, V, HamtRef> Eq for Hamt<K, V, HamtRef>
    where K: Eq,
          V: Eq,
          HamtRef: Eq
{
}

impl<K, V, HamtRef> PartialEq for Hamt<K, V, HamtRef>
    where K: PartialEq,
          V: PartialEq,
          HamtRef: PartialEq
{
    fn eq(&self, other: &Hamt<K, V, HamtRef>) -> bool {
        match (self, other) {
            (&Hamt::Empty, &Hamt::Empty) => true,
            (&Hamt::Leaf(h1, ref k1, ref v1),
             &Hamt::Leaf(h2, ref k2, ref v2)) => h1 == h2 && k1 == k2 && v1 == v2,
            (&Hamt::Bitmap(s1, b1, ref vs1),
             &Hamt::Bitmap(s2, b2, ref vs2)) => s1 == s2 && b1 == b2 && vs1 == vs2,
            (&Hamt::Collision(hx1, ref kvs1),
             &Hamt::Collision(hx2, ref kvs2)) => {
                hx1 == hx2 && kvs1.len() == kvs2.len() && kvs1.iter().all(|kv| kvs2.contains(kv))
            }
            (_, _) => false,
        }
    }
}
impl<'a, K, V, HamtRef> Iterator for Iter<'a, K, V, HamtRef>
    where K: 'a + Clone,
          V: 'a + Clone,
          HamtRef: 'a + HamtRefLike<K, V>
{
    type Item = (&'a K, &'a V);

    fn next(&mut self) -> Option<Self::Item> {
        let last = match self.stack.last() {
            Some(iter) => (*iter).clone(),
            None => {
                return None;
            }
        };
        match last {
            Traversing::Leaf(k, v) => {
                self.stack.pop();
                self.count += 1;
                Some((k, v))
            }
            Traversing::Bitmap(mut iter) => {
                let next = iter.next();
                self.stack.pop();
                self.stack.push(Traversing::Bitmap(iter));
                match next {
                    Some(hamt) => {
                        match *hamt.deref() {
                            Hamt::Empty => self.next(),
                            Hamt::Leaf(_, ref k, ref v) => {
                                self.count += 1;
                                Some((k, v))
                            }
                            Hamt::Bitmap(_, _, ref vs) => {
                                self.stack.push(Traversing::Bitmap(vs.iter()));
                                self.next()
                            }
                            Hamt::Collision(_, ref vs) => {
                                self.stack.push(Traversing::Collision(vs.iter()));
                                self.next()
                            }
                        }
                    }
                    None => {
                        self.stack.pop();
                        self.next()
                    }
                }
            }
            Traversing::Collision(mut iter) => {
                match iter.next() {
                    Some(ref kv) => {
                        self.count += 1;
                        self.stack.pop();
                        self.stack.push(Traversing::Collision(iter));
                        Some((&kv.0, &kv.1))
                    }
                    None => {
                        self.stack.pop();
                        self.next()
                    }
                }
            }
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.size - self.count, Some(self.size - self.count))
    }
}

impl<K, V, HamtRef> FromIterator<(K, V)> for Hamt<K, V, HamtRef>
    where K: Eq + Hash + Clone,
          V: Clone,
          HamtRef: HamtRefLike<K, V>
{
    fn from_iter<T>(iterator: T) -> Self
        where T: IntoIterator<Item = (K, V)>
    {
        iterator.into_iter().fold(Hamt::new(), |x, kv| x.insert(&kv.0, &kv.1))
    }
}

impl<'a, K, V, HamtRef> FromIterator<(&'a K, &'a V)> for Hamt<K, V, HamtRef>
    where K: Eq + Hash + Clone,
          V: Clone,
          HamtRef: HamtRefLike<K, V>
{
    fn from_iter<T>(iterator: T) -> Self
        where T: IntoIterator<Item = (&'a K, &'a V)>
    {
        iterator.into_iter().fold(Hamt::new(), |x, kv| x.insert(kv.0, kv.1))
    }
}

impl<'a, K, V, HamtRef> IntoIterator for &'a Hamt<K, V, HamtRef>
    where K: 'a + Clone + Hash + Eq,
          V: 'a + Clone,
          HamtRef: 'a + HamtRefLike<K, V>
{
    type Item = (&'a K, &'a V);
    type IntoIter = Iter<'a, K, V, HamtRef>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

impl<'a, K, Q: ?Sized, V, HamtRef> Index<&'a Q> for Hamt<K, V, HamtRef>
    where K: Hash + Eq + Clone + Borrow<Q>,
          V: Clone,
          Q: Eq + Hash,
          HamtRef: HamtRefLike<K, V>
{
    type Output = V;
    fn index(&self, index: &Q) -> &Self::Output {
        self.get(index).expect("key not in hamt")
    }
}

impl<K, V, HamtRef> Hamt<K, V, HamtRef>
    where K: Hash + Eq + Clone,
          V: Clone,
          HamtRef: HamtRefLike<K, V>
{
    pub fn new() -> Self {
        Hamt::Empty
    }

    pub fn len(&self) -> usize {
        match *self {
            Hamt::Empty => 0,
            Hamt::Leaf(_, _, _) => 1,
            Hamt::Bitmap(s, _, _) => s,
            Hamt::Collision(_, ref kvs) => kvs.len(),
        }
    }

    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    fn is_leaf_or_collision(&self) -> bool {
        match *self {
            Hamt::Leaf(_, _, _) => true,
            Hamt::Collision(_, _) => true,
            _ => false,
        }
    }

    fn collision(h: HashBits, k0: K, v0: V, k1: &K, v1: &V) -> Self {
        Hamt::Collision(h, vec![(k0, v0), (k1.clone(), v1.clone())])
    }

    fn collision_update<Q: ?Sized>(h: HashBits, k: &Q, v: V, vs: &[(K, V)]) -> Self
        where K: Borrow<Q>,
              Q: Hash + Eq + ToOwned<Owned = K>
    {
        let mut vs_prime = vs.clone().to_vec();
        match vs.iter().position(|ref i| i.0.borrow() == k) {
            Some(idx) => {
                vs_prime[idx].1 = v;
            }
            None => {
                vs_prime.push((k.to_owned(), v));
            }
        }
        Hamt::Collision(h, vs_prime)
    }

    fn collision_delete(h: HashBits, idx: usize, vs: &[(K, V)]) -> Self {
        let mut vs_prime = vs.clone().to_vec();
        vs_prime.remove(idx);
        Hamt::Collision(h, vs_prime)
    }

    fn collision_adjust<F, Q: ?Sized>(h: HashBits, key: &Q, f: F, vs: &[(K, V)]) -> Self
        where F: FnOnce(&V) -> V,
              K: Borrow<Q>,
              Q: Hash + Eq
    {
        let mut vs_prime = vs.clone().to_vec();
        if let Some(idx) = vs.iter().position(|ref i| i.0.borrow() == key) {
            vs_prime[idx].1 = f(&vs_prime[idx].1);
        }
        Hamt::Collision(h, vs_prime)
    }

    fn bitmap(b: Bitmap, vs: Vec<HamtRef>) -> Self {
        let size = (&vs).iter().map(|ref st| st.len()).fold(0, |x, y| x + y);
        Hamt::Bitmap(size, b, vs)
    }

    fn two(s: Shift, h0: HashBits, k0: K, v0: V, h1: HashBits, k1: &K, v1: &V) -> Self {
        let bp1 = mask(h0, s);
        let bp2 = mask(h1, s);
        if bp1 == bp2 {
            let st = HamtRef::from(Self::two(s + BITS_PER_SUBKEY, h0, k0, v0, h1, k1, v1));
            Self::bitmap(bp1, vec![st])
        } else {
            let l1 = HamtRef::from(Hamt::Leaf(h0, k0, v0));
            let l2 = HamtRef::from(Hamt::Leaf(h1, k1.clone(), v1.clone()));
            if index(h0, s) < index(h1, s) {
                Self::bitmap(bp1 | bp2, vec![l1, l2])
            } else {
                Self::bitmap(bp1 | bp2, vec![l2, l1])
            }
        }
    }

    /// Returns a key value iterator.
    pub fn iter(&self) -> Iter<K, V, HamtRef> {
        Iter {
            size: self.len(),
            count: 0,
            stack: match *self {
                Hamt::Empty => vec![],
                Hamt::Leaf(_, ref k, ref v) => vec![Traversing::Leaf(k, v)],
                Hamt::Bitmap(_, _, ref vs) => vec![Traversing::Bitmap(vs.iter())],
                Hamt::Collision(_, ref vs) => vec![Traversing::Collision(vs.iter())],
            },
        }
    }

    /// Returns an iterator that visits every key in an unspecified order.
    pub fn keys(&self) -> Keys<K, V, HamtRef> {
        Keys { iter: self.iter().map(pair_to_key) }
    }

    /// Returns an iterator that visits every value in an unspecified order.
    pub fn values(&self) -> Values<K, V, HamtRef> {
        Values { iter: self.iter().map(pair_to_value) }
    }

    /// Returns a reference to the value corresponding to the given key, or None if there
    /// is no value associated with the key.
    pub fn get<Q: ?Sized>(&self, k: &Q) -> Option<&V>
        where K: Borrow<Q>,
              Q: Hash + Eq
    {
        let mut sh = SipHasher::new();
        k.hash(&mut sh);
        let h = sh.finish();
        let mut shift = 0;
        let mut hamt = self;
        loop {
            match *hamt {
                Hamt::Empty => {
                    return None;
                }
                Hamt::Leaf(lh, ref lk, ref lv) => {
                    if h == lh && k == lk.borrow() {
                        return Some(&lv);
                    } else {
                        return None;
                    }
                }
                Hamt::Bitmap(_, b, ref vs) => {
                    let m = mask(h, shift);
                    if b & m == 0 {
                        return None;
                    } else {
                        shift += BITS_PER_SUBKEY;
                        hamt = vs[sparse_index(b, m)].deref();
                        continue;
                    }
                }
                Hamt::Collision(hx, ref vs) => {
                    if h == hx {
                        for kv in vs {
                            if k == kv.0.borrow() {
                                return Some(&kv.1);
                            }
                        }
                    } else {
                        return None;
                    }
                }
            }
        }
    }

    /// Returns true if the map contains the given key.
    pub fn contains_key<Q: ?Sized>(&self, k: &Q) -> bool
        where K: Borrow<Q>,
              Q: Hash + Eq
    {
        self.get(k).is_some()
    }

    pub fn insert<Q: ?Sized, R: ?Sized>(&self, k: &Q, v: &R) -> Self
        where K: Borrow<Q>,
              Q: Hash + Eq + ToOwned<Owned = K>,
              V: Borrow<R>,
              R: ToOwned<Owned = V>
    {
        let mut sh = SipHasher::new();
        k.hash(&mut sh);
        let h = sh.finish();
        self.insert_recur(h, k, v.to_owned(), 0)
    }

    fn insert_recur<Q: ?Sized>(&self, h: HashBits, k: &Q, v: V, s: Shift) -> Self
        where K: Borrow<Q>,
              Q: Hash + Eq + ToOwned<Owned = K>
    {
        match *self {
            Hamt::Empty => Hamt::Leaf(h, k.to_owned(), v),
            Hamt::Leaf(lh, ref lk, ref lv) => {
                if h == lh {
                    if k == lk.borrow() {
                        Hamt::Leaf(h, k.to_owned(), v)
                    } else {
                        Self::collision(h, k.to_owned(), v, lk, lv)
                    }
                } else {
                    Self::two(s, h, k.to_owned(), v, lh, lk, lv)
                }
            }
            Hamt::Bitmap(_, b, ref vs) => {
                let m = mask(h, s);
                let i = sparse_index(b, m);
                if b & m == 0 {
                    let mut vs_prime = (*vs).clone();
                    vs_prime.insert(i, HamtRef::from(Hamt::Leaf(h, k.to_owned(), v)));
                    Self::bitmap(b | m, vs_prime)
                } else {
                    let st = &vs[i];
                    let new_t = HamtRef::from(st.insert_recur(h, k, v, s + BITS_PER_SUBKEY));
                    let mut vs_prime = vs.clone();
                    vs_prime[i] = new_t;
                    Self::bitmap(b, vs_prime)
                }
            }
            Hamt::Collision(hx, ref vs) => {
                if h == hx {
                    Self::collision_update(h, k, v, vs)
                } else {
                    let bi = Self::bitmap(mask(hx, s), vec![HamtRef::from(self.clone())]);
                    bi.insert_recur(h, k, v, s)
                }
            }
        }
    }

    /// Returns a new map without an entry corresponding to the given key.
    pub fn remove<Q: ?Sized>(&self, k: &Q) -> Self
        where K: Borrow<Q>,
              Q: Hash + Eq
    {
        let mut sh = SipHasher::new();
        k.hash(&mut sh);
        let h = sh.finish();
        self.remove_recur(h, k, 0)
    }

    fn remove_recur<Q: ?Sized>(&self, h: HashBits, k: &Q, s: Shift) -> Self
        where K: Borrow<Q>,
              Q: Hash + Eq
    {
        match *self {
            Hamt::Empty => Hamt::Empty,
            Hamt::Leaf(lh, ref lk, _) => {
                if h == lh && k == lk.borrow() {
                    Hamt::Empty
                } else {
                    self.clone()
                }
            }
            Hamt::Bitmap(_, b, ref vs) => {
                let m = mask(h, s);
                let i = sparse_index(b, m);
                if b & m == 0 {
                    self.clone()
                } else {
                    let st = &vs[i];
                    let st_prime = st.remove_recur(h, k, s + BITS_PER_SUBKEY);
                    match st_prime {
                        Hamt::Empty => {
                            match vs.len() {
                                1 => Hamt::Empty,
                                2 => {
                                    match (i, &vs[0], &vs[1]) {
                                        (0, _, l) => {
                                            if l.is_leaf_or_collision() {
                                                l.deref().clone()
                                            } else {
                                                Self::bitmap(b & (!m), vec![l.clone()])
                                            }
                                        }
                                        (1, l, _) => {
                                            if l.is_leaf_or_collision() {
                                                l.deref().clone()
                                            } else {
                                                Self::bitmap(b & (!m), vec![l.clone()])
                                            }
                                        }
                                        _ => panic!("i can only be 0 or 1"),
                                    }
                                }
                                _ => {
                                    let mut vs_prime = vs.clone();
                                    vs_prime.remove(i);
                                    Self::bitmap(b & (!m), vs_prime)
                                }
                            }
                        }
                        _ => {
                            if st_prime.is_leaf_or_collision() && vs.len() == 1 {
                                st_prime
                            } else {
                                let mut vs_prime = vs.clone();
                                vs_prime[i] = HamtRef::from(st_prime);
                                Self::bitmap(b, vs_prime)
                            }
                        }
                    }
                }
            }
            Hamt::Collision(hx, ref vs) => {
                if h == hx {
                    match vs.iter().position(|ref kv| kv.0.borrow() == k) {
                        Some(i) => {
                            if vs.len() == 2 {
                                if i == 0 {
                                    Hamt::Leaf(h, vs[1].0.clone(), vs[1].1.clone())
                                } else {
                                    Hamt::Leaf(h, vs[0].0.clone(), vs[0].1.clone())
                                }
                            } else {
                                Self::collision_delete(h, i, vs)
                            }
                        }
                        _ => self.clone(),
                    }
                } else {
                    self.clone()
                }
            }
        }
    }

    /// Modifies the value tied to the given key with the function `f`. Otherwise, the map returned
    /// is identical.
    pub fn adjust<F, Q: ?Sized>(&self, key: &Q, f: F) -> Self
        where F: FnOnce(&V) -> V,
              K: Borrow<Q>,
              Q: Hash + Eq
    {
        let mut sh = SipHasher::new();
        key.hash(&mut sh);
        let h = sh.finish();
        self.adjust_recur(h, key, 0, f)
    }

    fn adjust_recur<F, Q: ?Sized>(&self, h: HashBits, key: &Q, s: Shift, f: F) -> Self
        where F: FnOnce(&V) -> V,
              K: Borrow<Q>,
              Q: Hash + Eq
    {
        match *self {
            Hamt::Empty => Hamt::Empty,
            Hamt::Leaf(lh, ref lk, ref lv) => {
                if h == lh && key == lk.borrow() {
                    Hamt::Leaf(h, lk.clone(), f(&lv))
                } else {
                    self.clone()
                }
            }
            Hamt::Bitmap(_, b, ref vs) => {
                let m = mask(h, s);
                let i = sparse_index(b, m);
                if b & m == 0 {
                    self.clone()
                } else {
                    let st = &vs[i];
                    let st_prime = HamtRef::from(st.adjust_recur(h, key, s + BITS_PER_SUBKEY, f));
                    let mut vs_prime = vs.clone();
                    vs_prime[i] = st_prime;
                    Self::bitmap(b, vs_prime)
                }
            }
            Hamt::Collision(_, ref vs) => Self::collision_adjust(h, key, f, vs),
        }
    }

    /// Updates the value at the given key using `f`. If `f` returns None, then the entry
    /// is removed.
    pub fn update<F, Q: ?Sized>(&self, key: &Q, f: F) -> Self
        where F: FnOnce(&V) -> Option<V>,
              K: Borrow<Q>,
              Q: Hash + Eq + ToOwned<Owned = K>
    {
        match self.get(key) {
            Some(ref value) => {
                match f(value) {
                    Some(value_prime) => self.insert(key, &value_prime),
                    None => self.remove(key),
                }
            }
            None => self.clone(),
        }

    }

    /// Updates the value at the given key using `f` as in `Self::update`. If no value exists for
    /// the given key, then `f` is passed `None`.
    pub fn alter<F, Q: ?Sized>(&self, key: &Q, f: F) -> Self
        where F: FnOnce(Option<&V>) -> Option<V>,
              K: Borrow<Q>,
              Q: Hash + Eq + ToOwned<Owned = K>
    {
        match f(self.get(key)) {
            Some(value) => self.insert(key, &value),
            None => self.remove(key),
        }
    }
}

pub mod internal {

    use super::Hamt;
    use std::rc::Rc;
    use std::sync::Arc;

    #[derive(Clone, Debug, PartialEq, Eq)]
    pub enum RcTrick<K, V> {
        RcTrick(Rc<Hamt<K, V, RcTrick<K, V>>>),
    }

    #[derive(Clone, Debug, PartialEq, Eq)]
    pub enum ArcTrick<K, V> {
        ArcTrick(Arc<Hamt<K, V, ArcTrick<K, V>>>),
    }

}

impl<K, V> HamtRefLike<K, V> for internal::RcTrick<K, V>
    where K: Clone,
          V: Clone
{
}

impl<K, V> HamtRefLike<K, V> for internal::ArcTrick<K, V>
    where K: Clone,
          V: Clone
{
}

impl<K, V> From<Hamt<K, V, internal::RcTrick<K, V>>> for internal::RcTrick<K, V> {
    fn from(t: Hamt<K, V, internal::RcTrick<K, V>>) -> Self {
        internal::RcTrick::RcTrick(Rc::from(t))
    }
}

impl<K, V> From<Hamt<K, V, internal::ArcTrick<K, V>>> for internal::ArcTrick<K, V> {
    fn from(t: Hamt<K, V, internal::ArcTrick<K, V>>) -> Self {
        internal::ArcTrick::ArcTrick(Arc::from(t))
    }
}

impl<K, V> Deref for internal::RcTrick<K, V> {
    type Target = Hamt<K, V, internal::RcTrick<K, V>>;
    fn deref(&self) -> &Self::Target {
        match *self {
            internal::RcTrick::RcTrick(ref rc) => rc.deref(),
        }
    }
}

impl<K, V> Deref for internal::ArcTrick<K, V> {
    type Target = Hamt<K, V, internal::ArcTrick<K, V>>;
    fn deref(&self) -> &Self::Target {
        match *self {
            internal::ArcTrick::ArcTrick(ref arc) => arc.deref(),
        }
    }
}

pub type HamtRc<K, V> = Hamt<K, V, internal::RcTrick<K, V>>;
pub type HamtArc<K, V> = Hamt<K, V, internal::ArcTrick<K, V>>;
