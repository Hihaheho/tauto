//! The name a misspelled one most likely meant, for a "did you mean" hint.
//!
//! Both checkers (the kernel's and the one of executable code) ask this with
//! the same candidates, so that their messages agree.

/// The candidate `name` most likely meant: the first one that differs from it
/// only in case and underscores (`mk_pair` for `MkPair`), else the closest one
/// by edit distance within a third of its length. `None` when nothing is close.
pub fn closest_name<'a>(
    name: &str,
    candidates: impl IntoIterator<Item = &'a str>,
) -> Option<&'a str> {
    let want = key(name);
    let limit = (want.len() / 3).max(1);
    let mut best: Option<(usize, &'a str)> = None;
    for c in candidates {
        if c == name {
            continue;
        }
        let d = distance(&want, &key(c));
        if d == 0 {
            return Some(c);
        }
        if d <= limit && best.is_none_or(|(b, _)| d < b) {
            best = Some((d, c));
        }
    }
    best.map(|(_, c)| c)
}

/// The one candidate that is `name` written in another case convention
/// (`DrainFree` for `drain_free`): the same letters, differing only in case
/// and underscores. `None` when no candidate is, or more than one is, since a
/// guess between them would not be a hint the reader can trust.
pub fn respelled<'a>(name: &str, candidates: impl IntoIterator<Item = &'a str>) -> Option<&'a str> {
    let want = key(name);
    let mut found = None;
    for c in candidates {
        if c != name && key(c) == want {
            if found.is_some_and(|f| f != c) {
                return None;
            }
            found = Some(c);
        }
    }
    found
}

fn key(s: &str) -> Vec<char> {
    s.chars()
        .filter(|c| *c != '_')
        .flat_map(char::to_lowercase)
        .collect()
}

fn distance(a: &[char], b: &[char]) -> usize {
    let mut row: Vec<usize> = (0..=b.len()).collect();
    for (i, x) in a.iter().enumerate() {
        let mut diag = row[0];
        row[0] = i + 1;
        for (j, y) in b.iter().enumerate() {
            let up = row[j + 1];
            row[j + 1] = (up + 1).min(row[j] + 1).min(diag + usize::from(x != y));
            diag = up;
        }
    }
    row[b.len()]
}

#[cfg(test)]
mod tests {
    use super::{closest_name, respelled};

    #[test]
    fn case_convention_only() {
        assert_eq!(
            respelled("drain_free", ["Nil", "DrainFree"]),
            Some("DrainFree")
        );
        assert_eq!(respelled("drain_fre", ["DrainFree"]), None);
        assert_eq!(respelled("held_root", ["HeldRoot", "Held_Root"]), None);
        assert_eq!(respelled("DrainFree", ["DrainFree"]), None);
    }

    #[test]
    fn case_and_underscores() {
        assert_eq!(closest_name("mk_pair", ["Other", "MkPair"]), Some("MkPair"));
        assert_eq!(
            closest_name("mk_calc_Expr_I", ["Mk_calc_Expr_I"]),
            Some("Mk_calc_Expr_I")
        );
    }

    #[test]
    fn edit_distance() {
        assert_eq!(closest_name("Conss", ["Nil", "Cons"]), Some("Cons"));
        assert_eq!(closest_name("BxOf", ["Nil", "Cons"]), None);
    }
}
