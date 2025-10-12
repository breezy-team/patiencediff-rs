patiencediff
============

This package contains implementations of the `patiencediff` and `histogram` diff algorithms for
Rust. The patience diff algorithm was
[first described](https://bramcohen.livejournal.com/73318.html) by Bram Cohen.

Like Python's `difflib`, this module provides both a convenience `unified_diff`
function for the generation of unified diffs of text files
as well as a SequenceMatcher that can be used on arbitrary lists.

## Algorithms

### Patience Diff (default)
Patiencediff provides a good balance of performance, nice output for humans,
and implementation simplicity. It matches only lines that appear exactly once
in both sequences, making it effective at finding the "correct" alignment in
many real-world scenarios.

### Histogram Diff
Histogram diff is a more flexible variant that matches lines occurring up to a
configurable threshold (typically 512). This can produce better results than
patience diff when dealing with files that have some repeated lines.

## Usage

```rust
use patiencediff::{SequenceMatcher, DiffAlgorithm};

// Use patience diff (default)
let mut matcher = SequenceMatcher::new(a, b);

// Use histogram diff
let mut matcher = SequenceMatcher::with_algorithm(
    a, b, DiffAlgorithm::Histogram { max_count: 512 }
);
```

The code in this package was extracted from the [Bazaar](https://www.bazaar-vcs.org/)
code base, and ported to Rust.
