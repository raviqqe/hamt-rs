# hamt-rs

[![GitHub Action](https://img.shields.io/github/actions/workflow/status/raviqqe/hamt-rs/test.yaml?branch=main&style=flat-square)](https://github.com/raviqqe/hamt-rs/actions?query=workflow%3Atest)
[![License](https://img.shields.io/github/license/raviqqe/hamt-rs.svg?style=flat-square)](https://opensource.org/licenses/MIT)

HAMT implementation whose sub-trees can be shared over threads.

[Hash-Array Mapped Trie (HAMT)](https://en.wikipedia.org/wiki/Hash_array_mapped_trie)
is a data structure popular as a map (a.k.a. associative array or dictionary)
or set.
Its immutable variant is adopted widely by functional programming languages
like Scala and Clojure to implement immutable and memory-efficient associative
arrays and sets.

## Technical notes

The implementation normalizes tree structures of HAMTs by eliminating
intermediate nodes during delete operations as described
in [the CHAMP paper][champ].

## References

- [Ideal Hash Trees](https://infoscience.epfl.ch/record/64398/files/idealhashtrees.pdf)
- [Optimizing Hash-Array Mapped Tries for Fast and Lean Immutable JVM Collections][champ]

## License

[MIT](LICENSE)

[champ]: https://michael.steindorfer.name/publications/oopsla15.pdf
