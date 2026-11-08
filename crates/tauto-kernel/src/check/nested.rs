//! Nested patterns. `Kapp(Klam(b), a) => e` is read as a `match` on the
//! field, inside the arm of `Kapp`: the arms become an exact case tree of
//! plain matches, which are compiled and checked as if written by hand.
//!
//! The tree splits a field only when every arm that reaches it splits it, so
//! no two written arms are ordered: `Pair(Zero, y)` beside `Pair(x, Succ(m))`
//! is rejected. The one arm that stands for "the other cases" is a last
//! `_ =>`: it reaches every case no written arm matches, and stands for at
//! least one.

use crate::surface::Name;
use crate::surface::{MatchArm, Pattern, SurfaceTerm, TermKind};

use super::{Diagnostic, Kernel, err};
use tauto_message::msg;

type T = SurfaceTerm;

/// One arm on its way down the tree: the patterns the fields still have to
/// match, by the name the field is bound to, and the arm's body.
struct Row {
    cols: Vec<(Name, Pattern)>,
    body: T,
    /// The row of the default arm `_ =>`, which every other row comes before.
    default: bool,
}

impl Kernel {
    /// The arms of a `match`, with nested patterns turned into `match`es in
    /// the arms' bodies (each without a result type: it is the arm's goal).
    pub(super) fn nest_arms(&mut self, arms: &[MatchArm]) -> Result<Vec<MatchArm>, Diagnostic> {
        let read;
        let arms = if arms.iter().any(|a| has_numeral(&a.pattern)) {
            read = arms
                .iter()
                .map(|a| {
                    Ok(MatchArm {
                        pattern: numerals(&a.pattern, a.body.span)?,
                        ..a.clone()
                    })
                })
                .collect::<Result<Vec<_>, Diagnostic>>()?;
            &read[..]
        } else {
            arms
        };
        if !arms.iter().any(|a| self.is_nested(&a.pattern)) {
            return Ok(arms.to_vec());
        }
        let x = self.fresh_name("x");
        let mut rows = Vec::new();
        for (at, arm) in arms.iter().enumerate() {
            if arm.guard.is_some() {
                return err(msg!("kernel-match-guards"), arm.body.span);
            }
            let default = arm.pattern == Pattern::Wild;
            if default && at + 1 != arms.len() {
                return err(msg!("kernel-match-default-last"), arm.body.span);
            }
            rows.push(Row {
                cols: vec![(x.clone(), arm.pattern.clone())],
                body: arm.body.clone(),
                default,
            });
        }
        let span = arms[0].body.span;
        let mut used = false;
        let has_default = rows.last().is_some_and(|r| r.default);
        let default_span = rows.last().map(|r| r.body.span);
        let arms = self.split(rows, 0, span, &mut used)?.1;
        if has_default && !used {
            return err(
                msg!("kernel-nested-default-unused"),
                default_span.unwrap_or(span),
            );
        }
        Ok(arms)
    }

    /// The first name in `C<n: m>(…)` that is not an implicit argument of
    /// `C`, if any.
    pub(super) fn unknown_implicit(&self, c: &Name, args: &[Pattern]) -> Option<String> {
        let (fam, j) = self.ctors.get(c)?;
        let ctor = &self.inds[fam].ctors[*j];
        let Some(Pattern::Record { name, fields }) = args.first() else {
            return None;
        };
        if name.spelling() != Some(tauto_surface::IMPLICITS) {
            return None;
        }
        let generics = &ctor.fields[..ctor.implicit.min(ctor.fields.len())];
        fields
            .iter()
            .find(|(n, _)| !generics.iter().any(|g| g.as_str() == n))
            .map(|(n, _)| n.clone())
    }

    /// A constructor's fields as a pattern lists them: all of them, or only
    /// those after its generics (which then match anything).
    pub(super) fn full_fields(&self, c: &Name, args: Vec<Pattern>) -> Vec<Pattern> {
        let Some((fam, j)) = self.ctors.get(c) else {
            return args;
        };
        let ctor = &self.inds[fam].ctors[*j];
        // `C<n: m>(…)`: the reader puts the implicit arguments named in the
        // pattern first, as a record of the internal name `IMPLICITS`; each
        // goes to the generic of its name, and the others are not bound.
        let mut args = args;
        if let Some(Pattern::Record { name, fields }) = args.first()
            && name.spelling() == Some(tauto_surface::IMPLICITS)
        {
            let named = fields.clone();
            args.remove(0);
            let generics = &ctor.fields[..ctor.implicit.min(ctor.fields.len())];
            let mut full: Vec<Pattern> = generics
                .iter()
                .map(|g| {
                    named
                        .iter()
                        .find(|(n, _)| n == g.as_str())
                        .map(|(_, p)| p.clone())
                        .unwrap_or(Pattern::Wild)
                })
                .collect();
            // A name that is not one of the generics is left for the arity
            // check to report: the pattern then has one argument too many.
            if named
                .iter()
                .any(|(n, _)| !generics.iter().any(|g| g.as_str() == n))
            {
                full.push(Pattern::Wild);
            }
            full.extend(args);
            return full;
        }
        if args.len() + ctor.implicit == ctor.args.len() && ctor.implicit > 0 {
            let mut full = vec![Pattern::Wild; ctor.implicit];
            full.extend(args);
            full
        } else {
            args
        }
    }

    fn is_nested(&self, p: &Pattern) -> bool {
        match p {
            Pattern::Ctor { args, .. } => args.iter().any(|a| match a {
                Pattern::Record { name, fields }
                    if name.spelling() == Some(tauto_surface::IMPLICITS) =>
                {
                    fields.iter().any(|(_, q)| self.as_ctor(q).is_some())
                }
                _ => self.as_ctor(a).is_some(),
            }),
            _ => false,
        }
    }

    /// `c(…)`, or a bare name that is a constructor.
    fn as_ctor<'p>(&self, p: &'p Pattern) -> Option<(Name, &'p [Pattern])> {
        let (name, args) = match p {
            Pattern::Ctor { name, args } => (name, args.as_slice()),
            Pattern::Bind(name) if self.pattern_constructor(name) => (name, &[][..]),
            _ => return None,
        };
        let name = if let Name::Selection(selection) = name {
            let mut candidates = selection
                .candidates()
                .iter()
                .map(|reference| Name::Global(reference.clone()))
                .filter(|reference| self.ctors.contains_key(reference));
            match (candidates.next(), candidates.next()) {
                (Some(reference), None) => reference,
                _ => name.clone(),
            }
        } else {
            name.clone()
        };
        Some((name, args))
    }

    /// The body that matches what the rows still have to match. `used` is
    /// set once the default row is the body of a case.
    fn tree(
        &mut self,
        rows: Vec<Row>,
        span: tauto_parol::Span,
        used: &mut bool,
    ) -> Result<T, Diagnostic> {
        let written: Vec<&Row> = rows.iter().filter(|r| !r.default).collect();
        let split = written.first().and_then(|first| {
            (0..first.cols.len())
                .find(|&k| written.iter().all(|r| self.as_ctor(&r.cols[k].1).is_some()))
        });
        let Some(col) = split else {
            // Nothing every written row splits: the written rows must be
            // done, and at most one; with none, the default is the body.
            if written
                .iter()
                .any(|r| r.cols.iter().any(|(_, p)| self.as_ctor(p).is_some()))
            {
                return err(msg!("kernel-nested-overlap"), span);
            }
            if written.len() > 1 {
                return err(msg!("kernel-nested-same"), written[1].body.span);
            }
            let row = match rows.iter().position(|r| !r.default) {
                Some(at) => rows.into_iter().nth(at).expect("a row"),
                None => {
                    *used = true;
                    rows.into_iter().next().expect("a row")
                }
            };
            let origins = self
                .ctor_site_origins
                .get(&row.body.id())
                .cloned()
                .unwrap_or_else(|| vec![row.body.id()]);
            let mut body = row.body;
            for (name, p) in &row.cols {
                if let Pattern::Bind(n) = p
                    && n != name
                {
                    body = self.subst(&body, n, &T::var(name, span));
                }
            }
            if self.record_sites {
                self.ctor_site_origins.insert(body.id(), origins);
            }
            return Ok(body);
        };
        let (scrutinee, arms) = self.split(rows, col, span, used)?;
        Ok(T::new(
            TermKind::Match {
                binder: None,
                scrutinee: Box::new(T::var(&scrutinee, span)),
                result: None,
                arms,
            },
            span,
        ))
    }

    /// Splits the rows on column `col`: one arm per constructor, in the
    /// order they are first written, each binding the constructor's fields.
    /// A default row goes to every constructor, with its fields `_`, and with
    /// one the constructors no row names have an arm of it alone.
    fn split(
        &mut self,
        rows: Vec<Row>,
        col: usize,
        span: tauto_parol::Span,
        used: &mut bool,
    ) -> Result<(Name, Vec<MatchArm>), Diagnostic> {
        let scrutinee = rows[0].cols[col].0.clone();
        let mut groups: Vec<(Name, Vec<Row>)> = Vec::new();
        let mut defaults: Vec<Row> = Vec::new();
        for mut row in rows {
            if row.default {
                row.cols.remove(col);
                defaults.push(row);
                continue;
            }
            let (_, p) = row.cols.remove(col);
            let Some((c, args)) = self.as_ctor(&p) else {
                return err(msg!("kernel-nested-lists-ctors"), row.body.span);
            };
            if let Some(n) = self.unknown_implicit(&c, args) {
                return err(
                    msg!(
                        "kernel-pattern-unknown-implicit",
                        name = (&c).to_string(),
                        implicit = &n
                    ),
                    row.body.span,
                );
            }
            let args = self.full_fields(&c, args.to_vec());
            let at = match groups.iter().position(|(g, _)| *g == c) {
                Some(at) => at,
                None => {
                    groups.push((c, Vec::new()));
                    groups.len() - 1
                }
            };
            if let Some(first) = groups[at].1.first()
                && first.cols.len() != row.cols.len() + args.len()
            {
                return err(
                    msg!(
                        "kernel-nested-field-numbers",
                        name = (&groups[at].0).to_string()
                    ),
                    row.body.span,
                );
            }
            // The fields come first, so the tree splits them before the
            // fields of the constructors around them.
            let mut cols: Vec<(Name, Pattern)> =
                args.into_iter().map(|a| (Name::default(), a)).collect();
            cols.extend(row.cols);
            groups[at].1.push(Row {
                cols,
                body: row.body,
                default: false,
            });
        }
        if !defaults.is_empty()
            && let Some((fam, _)) = groups.first().and_then(|(c, _)| self.ctors.get(c)).cloned()
        {
            for ctor in &self.inds[&fam].ctors {
                if !groups.iter().any(|(g, _)| *g == ctor.name) {
                    groups.push((ctor.name.clone(), Vec::new()));
                }
            }
        }
        let mut arms = Vec::new();
        for (c, mut group) in groups {
            let width = match self.ctors.get(&c) {
                Some((fam, j)) if !defaults.is_empty() => self.inds[fam].ctors[*j].args.len(),
                _ => fields_of(&group),
            };
            // The defaults are given the constructor's own fields, so the rows
            // must have them all; without defaults the flat match says so.
            if let Some(row) = group.first()
                && fields_of(&group) != width
            {
                return err(
                    format!(
                        "`{c}` has {width} fields, the pattern has {}",
                        fields_of(&group)
                    ),
                    row.body.span,
                );
            }
            for d in &defaults {
                let mut cols: Vec<(Name, Pattern)> = (0..width)
                    .map(|_| (Name::default(), Pattern::Wild))
                    .collect();
                cols.extend(d.cols.iter().cloned());
                group.push(Row {
                    cols,
                    body: d.body.clone(),
                    default: true,
                });
            }
            let mut names = Vec::new();
            for k in 0..width {
                let mut binds = group
                    .iter()
                    .filter(|r| !r.default)
                    .map(|r| match &r.cols[k].1 {
                        Pattern::Bind(n) if !self.pattern_constructor(n) => Some(n.clone()),
                        _ => None,
                    });
                let first = binds.next().flatten();
                let name = match first {
                    Some(n) if binds.all(|b| b.as_ref() == Some(&n)) => n,
                    _ => self.fresh_name("f"),
                };
                for r in &mut group {
                    r.cols[k].0 = name.clone();
                }
                names.push(name);
            }
            let origins = group
                .iter()
                .flat_map(|row| {
                    self.ctor_site_origins
                        .get(&row.body.id())
                        .cloned()
                        .unwrap_or_else(|| vec![row.body.id()])
                })
                .collect();
            let body = self.tree(group, span, used)?;
            if self.record_sites {
                self.ctor_site_origins.insert(body.id(), origins);
            }
            arms.push(MatchArm {
                goal: None,
                pattern: Pattern::Ctor {
                    name: c,
                    args: names.into_iter().map(Pattern::Bind).collect(),
                },
                guard: None,
                body,
            });
        }
        Ok((scrutinee, arms))
    }
}

fn fields_of(group: &[Row]) -> usize {
    group[0]
        .cols
        .iter()
        .take_while(|(n, _)| n.is_empty())
        .count()
}

/// The largest numeral a pattern may be: `n` is read as `n` nested `Succ`s,
/// so the case tree it makes is `n` matches deep.
const NUMERAL_PATTERN_MAX: i64 = 1024;

fn has_numeral(p: &Pattern) -> bool {
    match p {
        Pattern::Int(_) | Pattern::Bool(_) => true,
        Pattern::Ctor { args, .. } => args.iter().any(has_numeral),
        Pattern::Record { fields, .. } => fields.iter().any(|(_, p)| has_numeral(p)),
        Pattern::Tuple(items) => items.iter().any(has_numeral),
        _ => false,
    }
}

/// The pattern with each numeral `n` read as the `Nat` constructors
/// `Succ(…Succ(Zero))`, and `false` and `true` as the constructors of `Bool`
/// they are: the arm is a nested pattern, and the kernel gets the same
/// matches as if the constructors were written.
fn numerals(p: &Pattern, span: tauto_parol::Span) -> Result<Pattern, Diagnostic> {
    Ok(match p {
        Pattern::Int(n) if *n < 0 => {
            return err(
                msg!("kernel-nested-numeral-type", name = n.to_string()),
                span,
            );
        }
        Pattern::Int(n) if *n > NUMERAL_PATTERN_MAX => {
            return err(
                msg!(
                    "kernel-nested-numeral-large",
                    numeral = n.to_string(),
                    max = NUMERAL_PATTERN_MAX.to_string()
                ),
                span,
            );
        }
        Pattern::Bool(b) => Pattern::Bind(tauto_surface::bindings::library_name(if *b {
            "true"
        } else {
            "false"
        })),
        Pattern::Int(n) => {
            let mut q = Pattern::Bind(tauto_surface::bindings::library_name("Zero"));
            for _ in 0..*n {
                q = Pattern::Ctor {
                    name: tauto_surface::bindings::library_name("Succ"),
                    args: vec![q],
                };
            }
            q
        }
        Pattern::Ctor { name, args } => Pattern::Ctor {
            name: name.clone(),
            args: args
                .iter()
                .map(|a| numerals(a, span))
                .collect::<Result<_, _>>()?,
        },
        Pattern::Record { name, fields } => Pattern::Record {
            name: name.clone(),
            fields: fields
                .iter()
                .map(|(f, a)| Ok((f.clone(), numerals(a, span)?)))
                .collect::<Result<_, Diagnostic>>()?,
        },
        Pattern::Tuple(items) => Pattern::Tuple(
            items
                .iter()
                .map(|a| numerals(a, span))
                .collect::<Result<_, _>>()?,
        ),
        other => other.clone(),
    })
}
