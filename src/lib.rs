use std::collections::HashMap;
use std::hash::Hash;

pub fn unique_lcs<A: Eq + Hash + Clone>(
    a: &[A],
    b: &[A],
) -> Vec<(usize, usize)> {
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
        match index.get(line) {
            Some(Some(next)) => {
                if index2.contains_key(line) {
                    // Unset the previous mapping, which we now know to be invalid because the line isn't unique
                    btoa[index2[line]] = None;
                    index.remove(line);
                } else {
                    index2.insert(line, pos);
                    btoa[pos] = Some(*next);
                }
            }
            _ => {}
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
            } else if !stacks.is_empty() && stacks[k] < *apos &&
                        (k == stacks.len() - 1 ||
                         stacks[k+1] > *apos) {
                k += 1;
            } else {
                k = stacks.binary_search(apos).unwrap_or_else(|x| x);
            }
            if k > 0 {
                backpointers[bpos] = Some(lasts[k-1]);
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
    let mut m_opt = Some(lasts.last().unwrap().clone());
    while let Some(m) = m_opt {
        result.push((btoa[m].unwrap(), m));
        m_opt = backpointers[m];
    }
    result.reverse();
    result
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
pub fn recurse_matches<T: PartialEq + Clone + Hash + Eq>(
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
    let mut last_a_pos = alo - 1;
    let mut last_b_pos = blo - 1;
    for (apos, bpos) in unique_lcs(&a[alo..ahi], &b[blo..bhi]) {
        let apos = apos + alo;
        let bpos = bpos + blo;
        // Most of the time, you will have a sequence of similar entries
        if last_a_pos + 1 != apos || last_b_pos + 1 != bpos {
            recurse_matches(
                a,
                b,
                last_a_pos + 1,
                last_b_pos + 1,
                apos,
                bpos,
                answer,
                maxrecursion - 1,
            );
        }
        last_a_pos = apos;
        last_b_pos = bpos;
        answer.push((apos, bpos));
    }
    if answer.len() > old_length {
        // find matches between the last match and the end
        recurse_matches(
            a,
            b,
            last_a_pos + 1,
            last_b_pos + 1,
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
        recurse_matches(
            a,
            b,
            nalo,
            nblo,
            ahi,
            bhi,
            answer,
            maxrecursion - 1,
        );
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
            last_a_pos + 1,
            last_b_pos + 1,
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
