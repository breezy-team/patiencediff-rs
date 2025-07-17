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
        index
            .entry(line)
            .and_modify(|e| *e = None)
            .or_insert(Some(i));
    }

    // Create an array btoa where btoa[i] = position of line i in a, unless
    // that line doesn't occur exactly once in both, in which case it's set to None
    let mut btoa: Vec<Option<usize>> = vec![None; b.len()];
    let mut index2: HashMap<&A, usize> = HashMap::new();
    for (pos, line) in b.iter().enumerate() {
        if let Some(&Some(next)) = index.get(line) {
            match index2.entry(line) {
                std::collections::hash_map::Entry::Occupied(e) => {
                    // Unset the previous mapping, which we now know to be invalid because the line isn't unique
                    btoa[*e.get()] = None;
                    index.remove(line);
                }
                std::collections::hash_map::Entry::Vacant(e) => {
                    e.insert(pos);
                    btoa[pos] = Some(next);
                }
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

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Opcode {
    Replace(usize, usize, usize, usize),
    Delete(usize, usize, usize, usize),
    Insert(usize, usize, usize, usize),
    Equal(usize, usize, usize, usize),
}

impl Opcode {
    pub fn a_start(&self) -> usize {
        match self {
            Opcode::Replace(a_start, _, _, _)
            | Opcode::Delete(a_start, _, _, _)
            | Opcode::Insert(a_start, _, _, _)
            | Opcode::Equal(a_start, _, _, _) => *a_start,
        }
    }

    pub fn a_end(&self) -> usize {
        match self {
            Opcode::Replace(_, a_end, _, _)
            | Opcode::Delete(_, a_end, _, _)
            | Opcode::Insert(_, a_end, _, _)
            | Opcode::Equal(_, a_end, _, _) => *a_end,
        }
    }

    pub fn b_start(&self) -> usize {
        match self {
            Opcode::Replace(_, _, b_start, _)
            | Opcode::Delete(_, _, b_start, _)
            | Opcode::Insert(_, _, b_start, _)
            | Opcode::Equal(_, _, b_start, _) => *b_start,
        }
    }

    pub fn b_end(&self) -> usize {
        match self {
            Opcode::Replace(_, _, _, b_end)
            | Opcode::Delete(_, _, _, b_end)
            | Opcode::Insert(_, _, _, b_end)
            | Opcode::Equal(_, _, _, b_end) => *b_end,
        }
    }

    pub fn dupe(&self, a_start: usize, a_end: usize, b_start: usize, b_end: usize) -> Opcode {
        match self {
            Opcode::Replace(_, _, _, _) => Opcode::Replace(a_start, a_end, b_start, b_end),
            Opcode::Delete(_, _, _, _) => Opcode::Delete(a_start, a_end, b_start, b_end),
            Opcode::Insert(_, _, _, _) => Opcode::Insert(a_start, a_end, b_start, b_end),
            Opcode::Equal(_, _, _, _) => Opcode::Equal(a_start, a_end, b_start, b_end),
        }
    }
}

pub struct SequenceMatcher<'a, T>
where
    T: PartialEq + Hash + Eq,
{
    a: &'a [T],
    b: &'a [T],
    matching_blocks: Option<Vec<(usize, usize, usize)>>,
    opcodes: Option<Vec<Opcode>>,
}

impl<'a, T> SequenceMatcher<'a, T>
where
    T: PartialEq + Hash + Eq,
{
    pub fn new(a: &'a [T], b: &'a [T]) -> Self {
        SequenceMatcher {
            a,
            b,
            matching_blocks: None,
            opcodes: None,
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

    pub fn get_opcodes(&mut self) -> &[Opcode] {
        if self.opcodes.is_none() {
            self.opcodes = Some(matching_blocks_to_opcodes(self.get_matching_blocks()));
        }
        self.opcodes.as_ref().unwrap()
    }

    pub fn get_grouped_opcodes(&mut self, n: usize) -> Vec<Vec<Opcode>> {
        let mut res = Vec::new();
        let mut codes = self.get_opcodes().to_vec();
        if codes.is_empty() {
            codes.push(Opcode::Equal(0, 1, 0, 1));
        }

        if let Some(Opcode::Equal(a_start, a_end, b_start, b_end)) = codes.first_mut() {
            *a_start = std::cmp::max(*a_start, (*a_end).saturating_sub(n));
            *b_start = std::cmp::max(*b_start, (*b_end).saturating_sub(n));
        }
        if let Some(Opcode::Equal(a_start, a_end, b_start, b_end)) = codes.last_mut() {
            *a_end = std::cmp::min(*a_start + n, *a_end);
            *b_end = std::cmp::min(*b_start + n, *b_end);
        }
        let nn = n + n;
        let mut group = Vec::new();
        for code in &codes {
            let mut first_start = code.a_start();
            let mut second_start = code.b_start();
            if let Opcode::Equal(a_start, a_end, b_start, b_end) = code {
                if a_end - a_start > nn {
                    group.push(Opcode::Equal(
                        *a_start,
                        std::cmp::min(*a_end, *a_start + n),
                        *b_start,
                        std::cmp::min(*b_end, *b_start + n),
                    ));
                    res.push(group.clone());
                    group.clear();
                    first_start = std::cmp::max(first_start, (*a_end).saturating_sub(n));
                    second_start = std::cmp::max(second_start, (*b_end).saturating_sub(n));
                }
            }
            group.push(code.dupe(first_start, code.a_end(), second_start, code.b_end()));
        }
        if !(group.len() == 1 && matches!(group[0], Opcode::Equal { .. })) || group.is_empty() {
            res.push(group.clone());
        }
        res
    }
}

fn matching_blocks_to_opcodes(matching_blocks: &[(usize, usize, usize)]) -> Vec<Opcode> {
    let mut opcodes = Vec::new();
    let (mut i, mut j) = (0, 0);
    for (first_start, second_start, size) in matching_blocks {
        if i < *first_start && j < *second_start {
            opcodes.push(Opcode::Replace(i, *first_start, j, *second_start));
        } else if i < *first_start {
            opcodes.push(Opcode::Delete(i, *first_start, j, *second_start));
        } else if j < *second_start {
            opcodes.push(Opcode::Insert(i, *first_start, j, *second_start));
        };
        i = first_start + size;
        j = second_start + size;
        if *size != 0 {
            opcodes.push(Opcode::Equal(*first_start, i, *second_start, j));
        }
    }
    opcodes
}

#[test]
fn test_sequence_matcher() {
    // Test with byte string slices
    let mut s = SequenceMatcher::new(b"abxcd", b"abcd");
    assert_eq!(
        s.get_matching_blocks(),
        vec![(0, 0, 2), (3, 2, 2), (5, 4, 0)]
    );

    // Test with owned vectors
    let vec_a = vec![1, 2, 3, 4, 5];
    let vec_b = vec![1, 2, 7, 4, 5];
    let mut s = SequenceMatcher::new(&vec_a, &vec_b);
    assert_eq!(
        s.get_matching_blocks(),
        vec![(0, 0, 2), (3, 3, 2), (5, 5, 0)]
    );

    // Test with slices from arrays
    let arr_a = [10, 20, 30, 40];
    let arr_b = [10, 20, 30, 50];
    let mut s = SequenceMatcher::new(&arr_a[..], &arr_b[..]);
    assert_eq!(s.get_matching_blocks(), vec![(0, 0, 3), (4, 4, 0)]);
}

#[cfg(feature = "patchkit")]
use patchkit::unified::{Hunk, HunkLine, UnifiedPatch};

#[cfg(feature = "patchkit")]
/// Compare two sequences of lines; generate the delta as a unified diff.
///
/// Unified diffs are a compact way of showing line changes and a few
/// lines of context.  The number of context lines is set by 'n' which
/// defaults to three.
///
/// By default, the diff control lines (those with ---, +++, or @@) are
/// created with a trailing newline.  This is helpful so that inputs
/// created from file.readlines() result in diffs that are suitable for
/// file.writelines() since both the inputs and outputs have trailing
/// newlines.
///
/// For inputs that do not have trailing newlines, set the lineterm
/// argument to "" so that the output will be uniformly newline free.
///
/// The unidiff format normally has a header for filenames and modification
/// times.  Any or all of these may be specified using strings for
/// 'fromfile', 'tofile', 'fromfiledate', and 'tofiledate'.  The modification
/// times are normally expressed in the format returned by time.ctime().
///
/// # Example
///
/// ```rust
/// use patiencediff::unified_diff;
///
/// let lines = unified_diff(
///     &["one\n", "two\n", "three\n", "four\n"],
///     &["zero\n", "one\n", "tree\n", "four\n"],
///     Some("Original"), Some("Current"),
///     Some("Sat Jan 26 23:30:50 1991"), Some("Fri Jun 06 10:20:52 2003"),
///     Some(3)).concat();
///
/// assert_eq!(lines, r#"--- Original	Sat Jan 26 23:30:50 1991
/// +++ Current	Fri Jun 06 10:20:52 2003
/// @@ -1,4 +1,4 @@
/// +zero
///  one
/// -two
/// -three
/// +tree
///  four
/// "#);
/// ```
pub fn unified_diff(
    a: &[&str],
    b: &[&str],
    from_file: Option<&str>,
    to_file: Option<&str>,
    from_file_date: Option<&str>,
    to_file_date: Option<&str>,
    n: Option<usize>,
) -> Vec<String> {
    let n = n.unwrap_or(3);
    let mut sm = SequenceMatcher::new(a, b);

    let mut patch = UnifiedPatch {
        orig_name: from_file.map_or(&b""[..], |x| x.as_bytes()).to_vec(),
        mod_name: to_file.map_or(&b""[..], |x| x.as_bytes()).to_vec(),
        orig_ts: from_file_date.map(|x| x.as_bytes().to_vec()),
        mod_ts: to_file_date.map(|x| x.as_bytes().to_vec()),
        hunks: vec![],
    };

    for group in sm.get_grouped_opcodes(n) {
        let mut hunk = Hunk {
            orig_pos: group[0].a_start() + 1,
            orig_range: group.last().unwrap().a_end() - group[0].a_start(),
            mod_pos: group[0].b_start() + 1,
            mod_range: group.last().unwrap().b_end() - group[0].b_start(),
            lines: Vec::new(),
            tail: None,
        };

        for opcode in group {
            if let Opcode::Equal(a_start, a_end, ..) = opcode {
                for line in a[a_start..a_end].iter() {
                    hunk.lines
                        .push(HunkLine::ContextLine(line.as_bytes().to_vec()));
                }
                continue;
            }

            if matches!(opcode, Opcode::Replace(..) | Opcode::Delete(..)) {
                for line in a[opcode.a_start()..opcode.a_end()].iter() {
                    hunk.lines
                        .push(HunkLine::RemoveLine(line.as_bytes().to_vec()));
                }
            }

            if matches!(opcode, Opcode::Replace(..) | Opcode::Insert(..)) {
                for line in b[opcode.b_start()..opcode.b_end()].iter() {
                    hunk.lines
                        .push(HunkLine::InsertLine(line.as_bytes().to_vec()));
                }
            }
        }

        patch.hunks.push(hunk);
    }

    if patch.hunks.is_empty() {
        Vec::new()
    } else {
        String::from_utf8(patch.as_bytes())
            .unwrap()
            .split_inclusive('\n')
            .map(|x| x.to_string())
            .collect()
    }
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
    fn assert_diff_blocks<T: Eq + std::hash::Hash + Clone>(
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

    #[test]
    fn test_opcodes() {
        fn chk_ops_str(a: &str, b: &str, expected_codes: &[Opcode]) {
            let a = a.as_bytes();
            let b = b.as_bytes();
            let mut sm = SequenceMatcher::new(a, b);
            assert_eq!(expected_codes, sm.get_opcodes());
        }

        fn chk_ops_strlist(a: &[&str], b: &[&str], expected_codes: &[Opcode]) {
            let a = a.iter().map(|x| x.as_bytes()).collect::<Vec<&[u8]>>();
            let b = b.iter().map(|x| x.as_bytes()).collect::<Vec<&[u8]>>();
            let mut sm = SequenceMatcher::new(&a, &b);
            assert_eq!(expected_codes, sm.get_opcodes());
        }

        chk_ops_str("", "", &[]);
        chk_ops_strlist(&[], &[], &[]);
        chk_ops_str("abc", "", &[Opcode::Delete(0, 3, 0, 0)]);
        chk_ops_str("", "abc", &[Opcode::Insert(0, 0, 0, 3)]);
        chk_ops_str("abcd", "abcd", &[Opcode::Equal(0, 4, 0, 4)]);
        chk_ops_str(
            "abcd",
            "abce",
            &[Opcode::Equal(0, 3, 0, 3), Opcode::Replace(3, 4, 3, 4)],
        );
        chk_ops_str(
            "eabc",
            "abce",
            &[
                Opcode::Delete(0, 1, 0, 0),
                Opcode::Equal(1, 4, 0, 3),
                Opcode::Insert(4, 4, 3, 4),
            ],
        );
        chk_ops_str(
            "eabce",
            "abce",
            &[Opcode::Delete(0, 1, 0, 0), Opcode::Equal(1, 5, 0, 4)],
        );
        chk_ops_str(
            "abcde",
            "abXde",
            &[
                Opcode::Equal(0, 2, 0, 2),
                Opcode::Replace(2, 3, 2, 3),
                Opcode::Equal(3, 5, 3, 5),
            ],
        );
        chk_ops_str(
            "abcde",
            "abXYZde",
            &[
                Opcode::Equal(0, 2, 0, 2),
                Opcode::Replace(2, 3, 2, 5),
                Opcode::Equal(3, 5, 5, 7),
            ],
        );
        chk_ops_str(
            "abde",
            "abXYZde",
            &[
                Opcode::Equal(0, 2, 0, 2),
                Opcode::Insert(2, 2, 2, 5),
                Opcode::Equal(2, 4, 5, 7),
            ],
        );
        chk_ops_str(
            "abcdefghijklmnop",
            "abcdefxydefghijklmnop",
            &[
                Opcode::Equal(0, 6, 0, 6),
                Opcode::Insert(6, 6, 6, 11),
                Opcode::Equal(6, 16, 11, 21),
            ],
        );
        chk_ops_strlist(
            &["hello there\n", "world\n", "how are you today?\n"],
            &["hello there\n", "how are you today?\n"],
            &[
                Opcode::Equal(0, 1, 0, 1),
                Opcode::Delete(1, 2, 1, 1),
                Opcode::Equal(2, 3, 1, 2),
            ],
        );
        chk_ops_str(
            "aBccDe",
            "abccde",
            &[
                Opcode::Equal(0, 1, 0, 1),
                Opcode::Replace(1, 5, 1, 5),
                Opcode::Equal(5, 6, 5, 6),
            ],
        );
        chk_ops_str(
            "aBcDec",
            "abcdec",
            &[
                Opcode::Equal(0, 1, 0, 1),
                Opcode::Replace(1, 2, 1, 2),
                Opcode::Equal(2, 3, 2, 3),
                Opcode::Replace(3, 4, 3, 4),
                Opcode::Equal(4, 6, 4, 6),
            ],
        );
        chk_ops_str(
            "aBcdEcdFg",
            "abcdecdfg",
            &[
                Opcode::Equal(0, 1, 0, 1),
                Opcode::Replace(1, 8, 1, 8),
                Opcode::Equal(8, 9, 8, 9),
            ],
        );
        chk_ops_str(
            "aBcdEeXcdFg",
            "abcdecdfg",
            &[
                Opcode::Equal(0, 1, 0, 1),
                Opcode::Replace(1, 2, 1, 2),
                Opcode::Equal(2, 4, 2, 4),
                Opcode::Delete(4, 5, 4, 4),
                Opcode::Equal(5, 6, 4, 5),
                Opcode::Delete(6, 7, 5, 5),
                Opcode::Equal(7, 9, 5, 7),
                Opcode::Replace(9, 10, 7, 8),
                Opcode::Equal(10, 11, 8, 9),
            ],
        );
    }

    #[test]
    fn test_grouped_opcodes() {
        fn chk_ops_str(a: &str, b: &str, expected_codes: &[&[Opcode]], c: Option<usize>) {
            let a = a.as_bytes();
            let b = b.as_bytes();
            let c = c.unwrap_or(3);
            let mut sm = SequenceMatcher::new(a, b);
            assert_eq!(expected_codes, sm.get_grouped_opcodes(c));
        }

        fn chk_ops_strlist(a: &[&str], b: &[&str], expected_codes: &[&[Opcode]], c: Option<usize>) {
            let a = a.iter().map(|x| x.as_bytes()).collect::<Vec<&[u8]>>();
            let b = b.iter().map(|x| x.as_bytes()).collect::<Vec<&[u8]>>();
            let c = c.unwrap_or(3);
            let mut sm = SequenceMatcher::new(&a, &b);
            assert_eq!(expected_codes, sm.get_grouped_opcodes(c));
        }

        chk_ops_str("", "", &[], None);
        chk_ops_strlist(&[], &[], &[], None);
        chk_ops_str("abc", "", &[&[Opcode::Delete(0, 3, 0, 0)]], None);
        chk_ops_str("", "abc", &[&[Opcode::Insert(0, 0, 0, 3)]], None);
        chk_ops_str("abcd", "abcd", &[], None);
        chk_ops_str(
            "abcd",
            "abce",
            &[&[Opcode::Equal(0, 3, 0, 3), Opcode::Replace(3, 4, 3, 4)]],
            None,
        );
        chk_ops_str(
            "eabc",
            "abce",
            &[&[
                Opcode::Delete(0, 1, 0, 0),
                Opcode::Equal(1, 4, 0, 3),
                Opcode::Insert(4, 4, 3, 4),
            ]],
            None,
        );
        chk_ops_str(
            "abcdefghijklmnop",
            "abcdefxydefghijklmnop",
            &[&[
                Opcode::Equal(3, 6, 3, 6),
                Opcode::Insert(6, 6, 6, 11),
                Opcode::Equal(6, 9, 11, 14),
            ]],
            None,
        );
        chk_ops_str(
            "abcdefghijklmnop",
            "abcdefxydefghijklmnop",
            &[&[
                Opcode::Equal(2, 6, 2, 6),
                Opcode::Insert(6, 6, 6, 11),
                Opcode::Equal(6, 10, 11, 15),
            ]],
            Some(4),
        );
        chk_ops_str(
            "Xabcdef",
            "abcdef",
            &[&[Opcode::Delete(0, 1, 0, 0), Opcode::Equal(1, 4, 0, 3)]],
            None,
        );
        chk_ops_str(
            "abcdef",
            "abcdefX",
            &[&[Opcode::Equal(3, 6, 3, 6), Opcode::Insert(6, 6, 6, 7)]],
            None,
        );
    }

    #[cfg(feature = "patchkit")]
    #[test]
    fn test_patience_unified_diff() {
        let txt_a = vec!["hello there\n", "world\n", "how are you today?\n"];
        let txt_b = vec!["hello there\n", "how are you today?\n"];

        assert_eq!(
            vec![
                "--- \n",
                "+++ \n",
                "@@ -1,3 +1,2 @@\n",
                " hello there\n",
                "-world\n",
                " how are you today?\n"
            ],
            unified_diff(
                txt_a.as_slice(),
                txt_b.as_slice(),
                None,
                None,
                None,
                None,
                Some(3)
            )
        );
        let txt_a = "abcdefghijklmnop"
            .chars()
            .map(|x| format!("{}\n", x))
            .collect::<Vec<String>>();
        let txt_b = "abcdefxydefghijklmnop"
            .chars()
            .map(|x| format!("{}\n", x))
            .collect::<Vec<String>>();
        assert_eq!(
            vec![
                "--- \n",
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
            ],
            unified_diff(
                txt_a
                    .iter()
                    .map(|x| x.as_str())
                    .collect::<Vec<&str>>()
                    .as_slice(),
                txt_b
                    .iter()
                    .map(|x| x.as_str())
                    .collect::<Vec<&str>>()
                    .as_slice(),
                None,
                None,
                None,
                None,
                Some(3)
            )
        );
    }

    #[cfg(feature = "patchkit")]
    #[test]
    fn test_patience_unified_diff_with_dates() {
        let txt_a = vec!["hello there\n", "world\n", "how are you today?\n"];
        let txt_b = vec!["hello there\n", "how are you today?\n"];
        assert_eq!(
            vec![
                "--- a\t2008-08-08\n",
                "+++ b\t2008-09-09\n",
                "@@ -1,3 +1,2 @@\n",
                " hello there\n",
                "-world\n",
                " how are you today?\n"
            ],
            unified_diff(
                txt_a.as_slice(),
                txt_b.as_slice(),
                Some("a"),
                Some("b"),
                Some("2008-08-08"),
                Some("2008-09-09"),
                None
            )
        );
    }
}
