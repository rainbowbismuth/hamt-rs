# hamt
A generic implementation of a persistent hash array map trie in Rust, based on those found in the [unordered-containers](https://github.com/tibbe/unordered-containers) Haskell library.

There are two versions of the data structure, HamtRc which is limited to a single thread, and HamtArc which can be freely shared.
