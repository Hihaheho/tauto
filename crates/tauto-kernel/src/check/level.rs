//! Universe levels: the `l` of `Type(l)`.
//!
//! A level is the largest of a number and some level variables each raised by
//! a number, `max(c, u + a, v + b, …)`, kept in a normal form (one offset per
//! variable, and the number only when it is above every offset), so that two
//! levels are the same level exactly when they are equal as values. A level
//! variable stands for any natural number; one is bound by a declaration
//! (`theorem id<u: Level, A: Type(u)>(a: A): A`) and never inside a term.

use std::collections::BTreeMap;
use std::fmt;

#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct Level {
    /// The number, when it is above every variable's offset (else 0).
    c: u32,
    /// Each variable with the largest offset it is raised by.
    vars: BTreeMap<String, u32>,
}

impl Level {
    pub fn konst(n: u32) -> Level {
        Level {
            c: n,
            vars: BTreeMap::new(),
        }
    }

    pub fn var(name: &str) -> Level {
        Level {
            c: 0,
            vars: BTreeMap::from([(name.to_string(), 0)]),
        }
    }

    /// The number this level is, when it has no variable.
    pub fn as_const(&self) -> Option<u32> {
        self.vars.is_empty().then_some(self.c)
    }

    pub fn succ(&self) -> Option<Level> {
        self.plus(1)
    }

    /// `n` more than this level, or `None` if a component exceeds `u32`.
    pub fn plus(&self, n: u32) -> Option<Level> {
        let c = self.c.checked_add(n)?;
        let vars = self
            .vars
            .iter()
            .map(|(v, k)| Some((v.clone(), k.checked_add(n)?)))
            .collect::<Option<BTreeMap<_, _>>>()?;
        Some(Level { c, vars }.normal())
    }

    pub fn join(&self, other: &Level) -> Level {
        let mut vars = self.vars.clone();
        for (v, k) in &other.vars {
            let e = vars.entry(v.clone()).or_insert(*k);
            *e = (*e).max(*k);
        }
        Level {
            c: self.c.max(other.c),
            vars,
        }
        .normal()
    }

    /// The number is dropped when some variable is raised by at least as
    /// much: `max(c, u + k)` is `u + k` when `k >= c`.
    fn normal(mut self) -> Level {
        if self.vars.values().any(|k| *k >= self.c) {
            self.c = 0;
        }
        self
    }

    /// The largest number the level is at least, whatever the variables are.
    pub fn floor(&self) -> u32 {
        self.vars.values().copied().max().unwrap_or(0).max(self.c)
    }

    /// `self ≤ other` for every value of the variables.
    pub fn le(&self, other: &Level) -> bool {
        if self.c > other.floor() {
            return false;
        }
        self.vars
            .iter()
            .all(|(v, k)| other.vars.get(v).is_some_and(|o| k <= o))
    }

    /// The number, when it is above every variable's offset.
    pub fn constant_floor(&self) -> Option<u32> {
        (self.c > 0 && !self.vars.is_empty()).then_some(self.c)
    }

    /// Each variable with its offset.
    pub fn terms(&self) -> impl Iterator<Item = (&str, u32)> {
        self.vars.iter().map(|(v, k)| (v.as_str(), *k))
    }

    /// The variables, in order.
    pub fn variables(&self) -> impl Iterator<Item = &str> {
        self.vars.keys().map(String::as_str)
    }

    /// Each variable replaced by a level: the largest of the replacements
    /// raised by the offset.
    #[cfg(test)]
    pub fn subst(&self, map: &BTreeMap<String, Level>) -> Option<Level> {
        let mut out = Level::konst(self.c);
        for (v, k) in &self.vars {
            let by = map.get(v).cloned().unwrap_or_else(|| Level::var(v));
            out = out.join(&by.plus(*k)?);
        }
        Some(out)
    }
}

impl fmt::Display for Level {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut parts: Vec<String> = Vec::new();
        if self.c > 0 || self.vars.is_empty() {
            parts.push(self.c.to_string());
        }
        for (v, k) in &self.vars {
            parts.push(if *k == 0 {
                v.clone()
            } else {
                format!("{v} + {k}")
            });
        }
        match parts.as_slice() {
            [one] => write!(f, "{one}"),
            _ => write!(f, "max({})", parts.join(", ")),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn u() -> Level {
        Level::var("u")
    }
    fn v() -> Level {
        Level::var("v")
    }

    #[test]
    fn numbers_compare_as_numbers() {
        assert!(Level::konst(1).le(&Level::konst(3)));
        assert!(!Level::konst(3).le(&Level::konst(1)));
        assert_eq!(Level::konst(2).succ().unwrap(), Level::konst(3));
    }

    #[test]
    fn a_variable_is_below_what_it_is_raised_to() {
        assert!(u().le(&u().succ().unwrap()));
        assert!(!u().succ().unwrap().le(&u()));
        assert!(u().le(&u().join(&v())));
        assert!(!u().le(&v()));
        // Any value of `u` is at least 0, but not at least 1.
        assert!(Level::konst(0).le(&u()));
        assert!(!Level::konst(1).le(&u()));
        assert!(Level::konst(1).le(&u().succ().unwrap()));
    }

    #[test]
    fn the_normal_form_is_one_value() {
        assert_eq!(u().join(&v()), v().join(&u()));
        assert_eq!(u().join(&u().succ().unwrap()), u().succ().unwrap());
        assert_eq!(
            Level::konst(1).join(&u().succ().unwrap()),
            u().succ().unwrap()
        );
        assert_eq!(
            Level::konst(3).join(&u().succ().unwrap()).to_string(),
            "max(3, u + 1)"
        );
        assert_eq!(u().join(&u()), u());
    }

    #[test]
    fn substituting_a_level() {
        let map = BTreeMap::from([("u".to_string(), v().succ().unwrap())]);
        assert_eq!(
            u().succ().unwrap().subst(&map).unwrap(),
            v().plus(2).unwrap()
        );
        let by_const = BTreeMap::from([("u".to_string(), Level::konst(2))]);
        assert_eq!(
            u().succ().unwrap().join(&v()).subst(&by_const).unwrap(),
            v().join(&Level::konst(3))
        );
    }
    #[test]
    fn level_arithmetic_rejects_overflow() {
        let top = Level::konst(u32::MAX);
        assert_eq!(Level::konst(u32::MAX - 1).succ(), Some(top.clone()));
        assert_eq!(top.succ(), None);
        assert_eq!(top.plus(1), None);
        let raised = u().plus(u32::MAX).unwrap();
        assert_eq!(raised.succ(), None);
        assert_eq!(raised.plus(1), None);
        assert_eq!(
            raised.subst(&BTreeMap::from([("u".into(), Level::konst(1))])),
            None
        );
    }
}
