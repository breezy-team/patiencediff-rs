// Copyright (C) 2005 Bram Cohen
// Copyright (C) 2005, 2006 Canonical Ltd
// Copyright (C) 2023 Jelmer Vernooĳ
//
// This program is free software; you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation; either version 2 of the License, or
// (at your option) any later version.
//
// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.
//
// You should have received a copy of the GNU General Public License
// along with this program; if not, write to the Free Software
// Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA 02110-1301 USA

use std::collections::HashMap;
use std::hash::Hash;

pub fn unique_lcs<A: Eq + Hash>(a: &[A], b: &[A]) -> Vec<(usize, usize)> {
    // Create a mapping of line -> position in a, filtering out duplicate lines
    let mut index: HashMap<&A, Option<usize>> = HashMap::new();
    for (i, line) in a.iter().enumerate() {
        if !index.contains_key(line) {
            index.insert(line, Some(i));
        } else {
            index.insert(line, None);
        }
    }

    // Create an array btoa where btoa[i] = position of line i in a, unless
    // that line doesn't occur exactly once in both, in which case it's set to None
    let mut btoa: Vec<Option<usize>> = vec![None; b.len()];
    let mut index2: HashMap<&A, usize> = HashMap::new();
    for (pos, line) in b.iter().enumerate() {
        if let Some(Some(next)) = index.get(line) {
            if index2.contains_key(line) {
                // Unset the previous mapping, which we now know to be invalid because the line isn't unique
                btoa[index2[line]] = None;
                index.remove(line);
            } else {
                index2.insert(line, pos);
                btoa[pos] = Some(*next);
            }
        }
    }

    // Use the Patience Sorting algorithm to find the longest common subset
    // See http://en.wikipedia.org/wiki/Patience_sorting for more information
    let mut backpointers: Vec<Option<usize>> = vec![None; b.len()];
    let mut stacks: Vec<usize> = Vec::new();
    let mut lasts: Vec<usize> = Vec::new();
    let mut k: usize = 0;

    for (bpos, apos_opt) in btoa.iter().enumerate() {
        if let Some(apos) = apos_opt {
            // As an optimization, check if the next line comes at the end,
            // because it usually does
            if !stacks.is_empty() && stacks[stacks.len() - 1] < *apos {
                k = stacks.len();
            // As an optimization, check if the next line comes right after
            // the previous line, because usually it does
            } else if !stacks.is_empty()
                && stacks[k] < *apos
                && (k == stacks.len() - 1 || stacks[k + 1] > *apos)
            {
                k += 1;
            } else {
                k = stacks.binary_search(apos).unwrap_or_else(|x| x);
            }
            if k > 0 {
                backpointers[bpos] = Some(lasts[k - 1]);
            }
            if k < stacks.len() {
                stacks[k] = *apos;
                lasts[k] = bpos;
            } else {
                stacks.push(*apos);
                lasts.push(bpos);
            }
        }
    }

    if lasts.is_empty() {
        return vec![];
    }

    let mut result = Vec::new();
    let mut m_opt = Some(*lasts.last().unwrap());
    while let Some(m) = m_opt {
        result.push((btoa[m].unwrap(), m));
        m_opt = backpointers[m];
    }
    result.reverse();
    result
}

#[test]
fn test_unique_lcs() {
    assert_eq!(unique_lcs(b"", b""), vec![]);
    assert_eq!(unique_lcs(b"", b"a"), []);
    assert_eq!(unique_lcs(b"a", b""), []);
    assert_eq!(unique_lcs(b"a", b"a"), [(0, 0)]);
    assert_eq!(unique_lcs(b"a", b"b"), []);
    assert_eq!(unique_lcs(b"ab", b"ab"), [(0, 0), (1, 1)]);
    assert_eq!(unique_lcs(b"abcde", b"cdeab"), [(2, 0), (3, 1), (4, 2)]);
    assert_eq!(unique_lcs(b"cdeab", b"abcde"), [(0, 2), (1, 3), (2, 4)]);
    assert_eq!(
        unique_lcs(b"abXde", b"abYde"),
        [(0, 0), (1, 1), (3, 3), (4, 4)]
    );
    assert_eq!(unique_lcs(b"acbac", b"abc"), [(2, 1)]);
}

/// Find all of the matching text in the lines of a and b.
///
/// Args:
///   a: A sequence
///   b: Another sequence
///   alo: The start location of a to check, typically 0
///   ahi: The start location of b to check, typically 0
///   ahi: The maximum length of a to check, typically len(a)
///   bhi: The maximum length of b to check, typically len(b)
///   answer: The return array. Will be filled with tuples indicating [(line_in_a, line_in_b)]
///   maxrecursion: The maximum depth to recurse.  Must be a positive integer.
/// Returns: None, the return value is in the parameter answer, which should be a list
pub fn recurse_matches<T: PartialEq + Hash + Eq>(
    a: &[T],
    b: &[T],
    alo: usize,
    blo: usize,
    ahi: usize,
    bhi: usize,
    answer: &mut Vec<(usize, usize)>,
    maxrecursion: i32,
) {
    if maxrecursion < 0 {
        panic!("Max recursion depth reached");
    }
    let old_length = answer.len();
    if alo == ahi || blo == bhi {
        return;
    }
    let mut last_a_pos: isize = alo as isize - 1;
    let mut last_b_pos: isize = blo as isize - 1;
    for (apos, bpos) in unique_lcs(&a[alo..ahi], &b[blo..bhi]) {
        let apos = apos + alo;
        let bpos = bpos + blo;
        // Most of the time, you will have a sequence of similar entries
        if (last_a_pos + 1) as usize != apos || (last_b_pos + 1) as usize != bpos {
            recurse_matches(
                a,
                b,
                (last_a_pos + 1) as usize,
                (last_b_pos + 1) as usize,
                apos,
                bpos,
                answer,
                maxrecursion - 1,
            );
        }
        last_a_pos = apos as isize;
        last_b_pos = bpos as isize;
        answer.push((apos, bpos));
    }
    if answer.len() > old_length {
        // find matches between the last match and the end
        recurse_matches(
            a,
            b,
            (last_a_pos + 1) as usize,
            (last_b_pos + 1) as usize,
            ahi,
            bhi,
            answer,
            maxrecursion - 1,
        );
    } else if a[alo] == b[blo] {
        // find matching lines at the very beginning
        let mut nalo = alo;
        let mut nblo = blo;
        while nalo < ahi && nblo < bhi && a[nalo] == b[nblo] {
            answer.push((nalo, nblo));
            nalo += 1;
            nblo += 1;
        }
        recurse_matches(a, b, nalo, nblo, ahi, bhi, answer, maxrecursion - 1);
    } else if a[ahi - 1] == b[bhi - 1] {
        // find matching lines at the very end
        let mut nahi = ahi - 1;
        let mut nbhi = bhi - 1;
        while nahi > alo && nbhi > blo && a[nahi - 1] == b[nbhi - 1] {
            nahi -= 1;
            nbhi -= 1;
        }
        recurse_matches(
            a,
            b,
            (last_a_pos + 1) as usize,
            (last_b_pos + 1) as usize,
            nahi,
            nbhi,
            answer,
            maxrecursion - 1,
        );
        for i in 0..(ahi - nahi) {
            answer.push((nahi + i, nbhi + i));
        }
    }
}

#[test]
fn test_recurse_matches() {
    fn test_one<A: Hash + Eq + PartialEq>(a: &[A], b: &[A], matches: &[(usize, usize)]) {
        let mut test_matches = vec![];
        recurse_matches(a, b, 0, 0, a.len(), b.len(), &mut test_matches, 10);
        assert_eq!(test_matches, matches);
    }

    test_one(
        &["a", "", "b", "", "c"],
        &["a", "a", "b", "c", "c"],
        &[(0, 0), (2, 2), (4, 4)],
    );
    test_one(
        &["a", "c", "b", "a", "c"],
        &["a", "b", "c"],
        &[(0, 0), (2, 1), (4, 2)],
    );

    // Even though "bc" is not unique globally, and is surrounded by
    // non-matching lines, we should still match, because they are locally
    // unique
    test_one(
        b"abcdbce",
        b"afbcgdbce",
        &[(0, 0), (1, 2), (2, 3), (3, 5), (4, 6), (5, 7), (6, 8)],
    );

    // recurse_matches doesn"t match non-unique
    // lines surrounded by bogus text.
    // The update has been done in patiencediff.SequenceMatcher instead

    // This is what it could be
    // test_one("aBccDe", "abccde", [(0,0), (2,2), (3,3), (5,5)])

    // This is what it currently gives:
    test_one(b"aBccDe", b"abccde", &[(0, 0), (5, 5)]);
}

/// Find sequences of lines.
///
/// Given a sequence of [(line_in_a, line_in_b),]
/// find regions where they both increment at the same time
pub fn collapse_sequences(matches: &[(usize, usize)]) -> Vec<(usize, usize, usize)> {
    let mut answer = Vec::new();
    let mut start_a = None;
    let mut start_b = None;
    let mut length = 0;

    for &(i_a, i_b) in matches.iter() {
        if let Some(s_a) = start_a {
            if i_a == s_a + length && i_b == start_b.unwrap() + length {
                length += 1;
                continue;
            } else {
                answer.push((s_a, start_b.unwrap(), length));
            }
        }
        start_a = Some(i_a);
        start_b = Some(i_b);
        length = 1;
    }

    if length != 0 {
        answer.push((start_a.unwrap(), start_b.unwrap(), length));
    }

    answer
}

fn check_consistency(answer: &[(usize, usize, usize)]) {
    // For consistency sake, make sure all matches are only increasing
    let mut next_a = 0;
    let mut next_b = 0;
    for (a, b, match_len) in answer {
        assert!(a >= &next_a, "Non increasing matches for a");
        assert!(b >= &next_b, "Non increasing matches for b");
        next_a = a + match_len;
        next_b = b + match_len;
    }
}

pub struct SequenceMatcher<'a, T: PartialEq + Hash + Eq> {
    a: &'a [T],
    b: &'a [T],
    matching_blocks: Option<Vec<(usize, usize, usize)>>,
}

impl<'a, T: PartialEq + Hash + Eq> SequenceMatcher<'a, T> {
    pub fn new(a: &'a [T], b: &'a [T]) -> SequenceMatcher<'a, T> {
        SequenceMatcher {
            a,
            b,
            matching_blocks: None,
        }
    }

    /// Return list of triples describing matching subsequences.
    ///
    /// Each triple is of the form (i, j, n), and means that
    /// a[i:i+n] == b[j:j+n].  The triples are monotonically increasing in
    /// i and in j.
    ///
    /// The last triple is a dummy, (len(a), len(b), 0), and is the only
    /// triple with n==0.
    ///
    pub fn get_matching_blocks(&mut self) -> &[(usize, usize, usize)] {
        if let Some(ref matching_blocks) = self.matching_blocks {
            return matching_blocks;
        }

        let mut matches = vec![];
        recurse_matches(
            self.a,
            self.b,
            0,
            0,
            self.a.len(),
            self.b.len(),
            &mut matches,
            10,
        );
        // Matches now has individual line pairs of
        // line A matches line B, at the given offsets
        let mut matching_blocks = collapse_sequences(&matches);
        matching_blocks.push((self.a.len(), self.b.len(), 0));
        if cfg!(debug_assertions) {
            check_consistency(&matching_blocks);
        }

        self.matching_blocks = Some(matching_blocks);
        self.matching_blocks.as_ref().unwrap()
    }
}

#[test]
fn test_sequence_matcher() {
    let mut s = SequenceMatcher::new(b"abxcd", b"abcd");
    assert_eq!(
        s.get_matching_blocks(),
        vec![(0, 0, 2), (3, 2, 2), (5, 4, 0)]
    );
}

#[cfg(test)]
mod sequence_matcher_tests {
    use super::*;

    #[test]
    fn test_diff_unicode_string() {
        let a = (4000..4500)
            .step_by(3)
            .map(|x| std::char::from_u32(x).unwrap())
            .collect::<String>();
        let b = (4300..4800)
            .step_by(2)
            .map(|x| std::char::from_u32(x).unwrap())
            .collect::<String>();
        let a_chars = a.chars().collect::<Vec<char>>();
        let b_chars = b.chars().collect::<Vec<char>>();
        let mut sm = SequenceMatcher::new(&a_chars, &b_chars);
        let mb = sm.get_matching_blocks();
        assert_eq!(35, mb.len())
    }

    /// Check that the sequence matcher returns the correct blocks.
    ///
    /// # Arguments
    /// * `a` - A sequence to match
    /// * `b` - Another sequence to match
    /// * `expected_blocks` - The expected output, not including the final matching block (a.len(), b.len(), 0)
    fn assert_diff_blocks<T: Eq + std::hash::Hash>(
        a: &[T],
        b: &[T],
        expected_blocks: &[(usize, usize, usize)],
    ) {
        let mut matcher = SequenceMatcher::new(a, b);
        let blocks = matcher.get_matching_blocks();
        let last = blocks.last().unwrap();
        assert_eq!(&(a.len(), b.len(), 0), last);
        assert_eq!(expected_blocks, &blocks[0..blocks.len() - 1]);
    }

    #[test]
    fn test_matching_blocks() {
        // Some basic matching tests
        assert_diff_blocks("".as_bytes(), "".as_bytes(), &[]);
        assert_diff_blocks::<i32>(&[], &[], &[]);
        assert_diff_blocks("abc".as_bytes(), "".as_bytes(), &[]);
        assert_diff_blocks("".as_bytes(), "abc".as_bytes(), &[]);
        assert_diff_blocks("abcd".as_bytes(), "abcd".as_bytes(), &[(0, 0, 4)]);
        assert_diff_blocks("abcd".as_bytes(), "abce".as_bytes(), &[(0, 0, 3)]);
        assert_diff_blocks("eabc".as_bytes(), "abce".as_bytes(), &[(1, 0, 3)]);
        assert_diff_blocks("eabce".as_bytes(), "abce".as_bytes(), &[(1, 0, 4)]);
        assert_diff_blocks(
            "abcde".as_bytes(),
            "abXde".as_bytes(),
            &[(0, 0, 2), (3, 3, 2)],
        );
        assert_diff_blocks(
            "abcde".as_bytes(),
            "abXYZde".as_bytes(),
            &[(0, 0, 2), (3, 5, 2)],
        );
        assert_diff_blocks(
            "abde".as_bytes(),
            "abXYZde".as_bytes(),
            &[(0, 0, 2), (2, 5, 2)],
        );
        // This may check too much, but it checks to see that
        // a copied block stays attached to the previous section,
        // not the later one.
        // difflib would tend to grab the trailing longest match
        // which would make the diff not look right
        assert_diff_blocks(
            "abcdefghijklmnop".as_bytes(),
            "abcdefxydefghijklmnop".as_bytes(),
            &[(0, 0, 6), (6, 11, 10)],
        );

        // make sure it supports passing in lists
        assert_diff_blocks(
            &["hello there\n", "world\n", "how are you today?\n"],
            &["hello there\n", "how are you today?\n"],
            &[(0, 0, 1), (2, 1, 1)],
        );

        // non unique lines surrounded by non-matching lines
        // won"t be found
        assert_diff_blocks(
            "aBccDe".as_bytes(),
            "abccde".as_bytes(),
            &[(0, 0, 1), (5, 5, 1)],
        );

        // But they only need to be locally unique
        assert_diff_blocks(
            "aBcDec".as_bytes(),
            "abcdec".as_bytes(),
            &[(0, 0, 1), (2, 2, 1), (4, 4, 2)],
        );

        // non unique blocks won"t be matched
        assert_diff_blocks(
            "aBcdEcdFg".as_bytes(),
            "abcdecdfg".as_bytes(),
            &[(0, 0, 1), (8, 8, 1)],
        );

        // but locally unique ones will
        assert_diff_blocks(
            "aBcdEeXcdFg".as_bytes(),
            "abcdecdfg".as_bytes(),
            &[(0, 0, 1), (2, 2, 2), (5, 4, 1), (7, 5, 2), (10, 8, 1)],
        );

        assert_diff_blocks("abbabbXd".as_bytes(), "cabbabxd".as_bytes(), &[(7, 7, 1)]);
        assert_diff_blocks("abbabbbb".as_bytes(), "cabbabbc".as_bytes(), &[]);
        assert_diff_blocks("bbbbbbbb".as_bytes(), "cbbbbbbc".as_bytes(), &[]);
    }

    #[test]
    fn test_matching_blocks_tuples() {
        // Some basic matching tests
        assert_diff_blocks::<i32>(&[], &[], &[]);
        assert_diff_blocks(&[["a"], ["b"], ["c,"]], &[], &[]);
        assert_diff_blocks(&[], &[["a"], ["b"], ["c,"]], &[]);
        assert_diff_blocks(
            &[["a"], ["b"], ["c,"]],
            &[["a"], ["b"], ["c,"]],
            &[(0, 0, 3)],
        );
        assert_diff_blocks(
            &[["a"], ["b"], ["c,"]],
            &[["a"], ["b"], ["d,"]],
            &[(0, 0, 2)],
        );
        assert_diff_blocks(
            &[["d"], ["b"], ["c,"]],
            &[["a"], ["b"], ["c,"]],
            &[(1, 1, 2)],
        );
        assert_diff_blocks(
            &[["d"], ["a"], ["b"], ["c,"]],
            &[["a"], ["b"], ["c,"]],
            &[(1, 0, 3)],
        );
        assert_diff_blocks(
            &[["a", "b"], ["c", "d"], ["e", "f"]],
            &[["a", "b"], ["c", "X"], ["e", "f"]],
            &[(0, 0, 1), (2, 2, 1)],
        );
        assert_diff_blocks(
            &[["a", "b"], ["c", "d"], ["e", "f"]],
            &[["a", "b"], ["c", "dX"], ["e", "f"]],
            &[(0, 0, 1), (2, 2, 1)],
        );
    }

    #[test]
    fn test_multiple_ranges() {
        // There was an earlier bug where we used a bad set of ranges,
        // this triggers that specific bug, to make sure it doesn"t regress
        assert_diff_blocks(
            "abcdefghijklmnop".as_bytes(),
            "abcXghiYZQRSTUVWXYZijklmnop".as_bytes(),
            &[(0, 0, 3), (6, 4, 3), (9, 20, 7)],
        );

        assert_diff_blocks(
            "ABCd efghIjk  L".as_bytes(),
            "AxyzBCn mo pqrstuvwI1 2  L".as_bytes(),
            &[(0, 0, 1), (1, 4, 2), (9, 19, 1), (12, 23, 3)],
        );

        // These are rot13 code snippets.
        assert_diff_blocks(
            &r###"    trg nqqrq jura lbh nqq n svyr va gur qverpgbel.
        """
        gnxrf_netf = ['svyr*']
        gnxrf_bcgvbaf = ['ab-erphefr']

        qrs eha(frys, svyr_yvfg, ab_erphefr=Snyfr):
            sebz omeyvo.nqq vzcbeg fzneg_nqq, nqq_ercbegre_cevag, nqq_ercbegre_ahyy
            vs vf_dhvrg():
                ercbegre = nqq_ercbegre_ahyy
            ryfr:
                ercbegre = nqq_ercbegre_cevag
            fzneg_nqq(svyr_yvfg, abg ab_erphefr, ercbegre)


    pynff pzq_zxqve(Pbzznaq):
    "###
            .split_inclusive('\n')
            .collect::<Vec<&str>>(),
            &r###"    trg nqqrq jura lbh nqq n svyr va gur qverpgbel.

        --qel-eha jvyy fubj juvpu svyrf jbhyq or nqqrq, ohg abg npghnyyl
        nqq gurz.
        """
        gnxrf_netf = ['svyr*']
        gnxrf_bcgvbaf = ['ab-erphefr', 'qel-eha']

        qrs eha(frys, svyr_yvfg, ab_erphefr=Snyfr, qel_eha=Snyfr):
            vzcbeg omeyvo.nqq

            vs qel_eha:
                vs vf_dhvrg():
                    # Guvf vf cbvagyrff, ohg V'q engure abg envfr na reebe
                    npgvba = omeyvo.nqq.nqq_npgvba_ahyy
                ryfr:
      npgvba = omeyvo.nqq.nqq_npgvba_cevag
            ryvs vf_dhvrg():
                npgvba = omeyvo.nqq.nqq_npgvba_nqq
            ryfr:
           npgvba = omeyvo.nqq.nqq_npgvba_nqq_naq_cevag

            omeyvo.nqq.fzneg_nqq(svyr_yvfg, abg ab_erphefr, npgvba)


    pynff pzq_zxqve(Pbzznaq):
   "###
            .split_inclusive('\n')
            .collect::<Vec<&str>>(),
            &[(0, 0, 1), (1, 4, 2), (9, 19, 1), (12, 23, 3)],
        );
    }

    /* TODO
        #[test]
        fn test_opcodes() {
            fn chk_ops(a, b, expected_codes):
                let s = PatienceSequenceMatcher::new(a, b);
                assert_eq!(expected_codes, s.get_opcodes())
            }

            chk_ops("", "", []);
            chk_ops([], [], []);
            chk_ops("abc", "", [("delete", 0, 3, 0, 0)]);
            chk_ops("", "abc", [("insert", 0, 0, 0, 3)]);
            chk_ops("abcd", "abcd", [("equal",    0, 4, 0, 4)]);
            chk_ops("abcd", "abce", [("equal",   0, 3, 0, 3),
                                     ("replace", 3, 4, 3, 4)
                                     ]);
            chk_ops("eabc", "abce", [("delete", 0, 1, 0, 0),
                                     ("equal",  1, 4, 0, 3),
                                     ("insert", 4, 4, 3, 4)
                                     ]);
            chk_ops("eabce", "abce", [("delete", 0, 1, 0, 0),
                                      ("equal",  1, 5, 0, 4)
                                      ])
            chk_ops("abcde", "abXde", [("equal",   0, 2, 0, 2),
                                       ("replace", 2, 3, 2, 3),
                                       ("equal",   3, 5, 3, 5)
                                       ])
            chk_ops("abcde", "abXYZde", [("equal",   0, 2, 0, 2),
                                         ("replace", 2, 3, 2, 5),
                                         ("equal",   3, 5, 5, 7)
                                         ])
            chk_ops("abde", "abXYZde", [("equal",  0, 2, 0, 2),
                                        ("insert", 2, 2, 2, 5),
                                        ("equal",  2, 4, 5, 7)
                                        ])
            chk_ops("abcdefghijklmnop", "abcdefxydefghijklmnop",
                    [("equal",  0, 6,  0, 6),
                     ("insert", 6, 6,  6, 11),
                     ("equal",  6, 16, 11, 21)
                     ])
            chk_ops(
                    ["hello there\n", "world\n", "how are you today?\n"],
                    ["hello there\n", "how are you today?\n"],
                    [("equal",  0, 1, 0, 1),
                     ("delete", 1, 2, 1, 1),
                     ("equal",  2, 3, 1, 2),
                     ])
            chk_ops("aBccDe", "abccde",
                    [("equal",   0, 1, 0, 1),
                     ("replace", 1, 5, 1, 5),
                     ("equal",   5, 6, 5, 6),
                     ])
            chk_ops("aBcDec", "abcdec",
                    [("equal",   0, 1, 0, 1),
                     ("replace", 1, 2, 1, 2),
                     ("equal",   2, 3, 2, 3),
                     ("replace", 3, 4, 3, 4),
                     ("equal",   4, 6, 4, 6),
                     ])
            chk_ops("aBcdEcdFg", "abcdecdfg",
                    [("equal",   0, 1, 0, 1),
                     ("replace", 1, 8, 1, 8),
                     ("equal",   8, 9, 8, 9)
                     ])
            chk_ops("aBcdEeXcdFg", "abcdecdfg",
                    [("equal",   0, 1, 0, 1),
                     ("replace", 1, 2, 1, 2),
                     ("equal",   2, 4, 2, 4),
                     ("delete", 4, 5, 4, 4),
                     ("equal",   5, 6, 4, 5),
                     ("delete", 6, 7, 5, 5),
                     ("equal",   7, 9, 5, 7),
                     ("replace", 9, 10, 7, 8),
                     ("equal",   10, 11, 8, 9)
                     ]);
        }

        fn test_grouped_opcodes() {
            fn chk_ops(a, b, expected_codes, n=3) {
                s = self._PatienceSequenceMatcher(None, a, b)
                assert_eq!(expected_codes, list(s.get_grouped_opcodes(n)));
            }

            chk_ops("", "", [])
            chk_ops([], [], [])
            chk_ops("abc", "", [[("delete", 0, 3, 0, 0)]])
            chk_ops("", "abc", [[("insert", 0, 0, 0, 3)]])
            chk_ops("abcd", "abcd", [])
            chk_ops("abcd", "abce", [[("equal",   0, 3, 0, 3),
                                      ("replace", 3, 4, 3, 4)
                                      ]])
            chk_ops("eabc", "abce", [[("delete", 0, 1, 0, 0),
                                     ("equal",  1, 4, 0, 3),
                                     ("insert", 4, 4, 3, 4)]])
            chk_ops("abcdefghijklmnop", "abcdefxydefghijklmnop",
                    [[("equal",  3, 6, 3, 6),
                      ("insert", 6, 6, 6, 11),
                      ("equal",  6, 9, 11, 14)
                      ]])
            chk_ops("abcdefghijklmnop", "abcdefxydefghijklmnop",
                    [[("equal",  2, 6, 2, 6),
                      ("insert", 6, 6, 6, 11),
                      ("equal",  6, 10, 11, 15)
                      ]], 4)
            chk_ops("Xabcdef", "abcdef",
                    [[("delete", 0, 1, 0, 0),
                      ("equal",  1, 4, 0, 3)
                      ]])
            chk_ops("abcdef", "abcdefX",
                    [[("equal",  3, 6, 3, 6),
                      ("insert", 6, 6, 6, 7)
                      ]])
        }


        #[test]
        fn test_patience_unified_diff() {
            let txt_a = ["hello there\n",
                     "world\n",
                     "how are you today?\n"]
            txt_b = ["hello there\n",
                     "how are you today?\n"]
            unified_diff = patiencediff.unified_diff
            psm = self._PatienceSequenceMatcher
            assert_eq!(["--- \n",
                        "+++ \n",
                        "@@ -1,3 +1,2 @@\n",
                        " hello there\n",
                        "-world\n",
                        " how are you today?\n"
                        ], list(unified_diff(
                                 txt_a, txt_b, sequencematcher=psm)))
            txt_a = [x+"\n" for x in "abcdefghijklmnop"]
            txt_b = [x+"\n" for x in "abcdefxydefghijklmnop"]
            // This is the result with LongestCommonSubstring matching
            assert_eq!(["--- \n",
                        "+++ \n",
                        "@@ -1,6 +1,11 @@\n",
                        " a\n",
                        " b\n",
                        " c\n",
                        "+d\n",
                        "+e\n",
                        "+f\n",
                        "+x\n",
                        "+y\n",
                        " d\n",
                        " e\n",
                        " f\n"], list(unified_diff(txt_a, txt_b)))
            // And the patience diff
            assert_eq!(["--- \n",
                              "+++ \n",
                              "@@ -4,6 +4,11 @@\n",
                              " d\n",
                              " e\n",
                              " f\n",
                              "+x\n",
                              "+y\n",
                              "+d\n",
                              "+e\n",
                              "+f\n",
                              " g\n",
                              " h\n",
                              " i\n",
                              ], list(unified_diff(
                                  txt_a, txt_b, sequencematcher=psm)))
        }

        #[test]
        fn test_patience_unified_diff_with_dates() {
            txt_a = ["hello there\n",
                     "world\n",
                     "how are you today?\n"]
            txt_b = ["hello there\n",
                     "how are you today?\n"]
            unified_diff = patiencediff.unified_diff
            psm = self._PatienceSequenceMatcher
            assert_eq!(["--- a\t2008-08-08\n",
                              "+++ b\t2008-09-09\n",
                              "@@ -1,3 +1,2 @@\n",
                              " hello there\n",
                              "-world\n",
                              " how are you today?\n"
                              ], list(unified_diff(
                                  txt_a, txt_b, fromfile="a", tofile="b",
                                  fromfiledate="2008-08-08",
                                  tofiledate="2008-09-09",
                                  sequencematcher=psm)))
        }
    */
}
