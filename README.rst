patiencediff
############

This package contains the implementation of the ``patiencediff`` algorithm for
Rust, as
`first described <https://bramcohen.livejournal.com/73318.html>`_ by Bram Cohen.

Like Python's ``difflib``, this module provides both a convenience ``unified_diff``
function for the generation of unified diffs of text files
as well as a SequenceMatcher that can be used on arbitrary lists.

Patiencediff provides a good balance of performance, nice output for humans,
and implementation simplicity.

The code in this package was extracted from the `Bazaar <https://www.bazaar-vcs.org/>`_
code base.
