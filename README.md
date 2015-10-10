# hamt
:construction: This library is under construction! :construction:

[![Build Status](https://travis-ci.org/rainbowbismuth/hamt-rs.svg?branch=master)](https://travis-ci.org/rainbowbismuth/hamt-rs)

An implementation of a persistent hash array mapped trie in Rust, based on those found in the [unordered-containers](https://github.com/tibbe/unordered-containers) Haskell library.

There are two versions of the data structure, HamtRc which is limited to a single thread, and HamtArc which can be freely shared.

# Examples
```rust
extern crate hamt;
use hamt::HamtRc;

let hamt = HamtRc::<isize,isize>::new().insert(0, 1).insert(1, 10).insert(2, 100);
assert!(hamt.get(&1) == Option::Some(&10));
```

# Performance
Unknown :space_invader:.

# Planned features
* Data.HashSet equivalent,
* Useful functions like insertWith, adjust, union, difference, intersection.
