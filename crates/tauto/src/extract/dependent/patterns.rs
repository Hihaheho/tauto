//! Checked pattern decomposition and fall-through.
use super::*;

fn selected(site: &CtorSite, written: &Name) -> bool {
    site.written == *written
        || matches!(written, Name::Selection(selection)
        if site.written.as_global().is_some_and(|reference| selection.candidates().contains(reference)))
}

impl Eraser<'_> {
    pub(super) fn prop(&self, t: &SurfaceTerm) -> bool {
        match &*t.kind {
            TermKind::Var(n) => {
                self.checked.props.contains(n)
                    || n.sort_symbol() == Some(tauto_surface::identity::SortSymbol::Proposition)
                    || tauto_surface::bindings::is_library(n, "=")
            }
            TermKind::App { function, .. } => self.prop(function),
            TermKind::Pi { result, .. } => self.prop(result),
            _ => false,
        }
    }
    pub(super) fn matching(
        &mut self,
        s: &SurfaceTerm,
        arms: &[MatchArm],
        locals: &Scope,
    ) -> Result<String, Message> {
        if arms.is_empty() {
            return Ok("extract_unreachable()".into());
        }
        let proof_match = arms.iter().any(|arm| {
            let written = match &arm.pattern {
                Pattern::Bind(n) | Pattern::Ctor { name: n, .. } => n,
                _ => return false,
            };
            let name = self
                .checked
                .ctor_sites
                .iter()
                .find(|site| {
                    !site.expression && site.occurrence == arm.body.id() && selected(site, written)
                })
                .map_or(written, |site| &site.resolved);
            self.checked
                .families
                .values()
                .any(|family| family.prop && family.ctors.contains(name))
        });
        if proof_match {
            let [arm] = arms else {
                return Err(msg!("tauto-extract-a-match-on-a-proof"));
            };
            let mut inner = locals.clone();
            inner.erase_pattern(&arm.pattern);
            return self.expr(&arm.body, &inner);
        }
        let value = self.expr(s, locals)?;
        let subject = self.fresh("Subject");
        let mut out = Vec::new();
        let mut rows = Vec::new();
        let mut nested_tests = false;
        for arm in arms {
            let notes: Vec<_> = self
                .checked
                .ctor_sites
                .iter()
                .filter(|s| !s.expression && s.occurrence == arm.body.id())
                .collect();
            let mut inner = locals.clone();
            let mut tests = Vec::new();
            let mut binds = Vec::new();
            let mut at = 0;
            let p = self.pattern(
                &arm.pattern,
                &notes,
                &mut at,
                &mut inner,
                &mut tests,
                &mut binds,
            )?;
            if arm.guard.is_some() {
                return Err("dependent extraction: guarded patterns are not supported".into());
            }
            let body = self.expr(&arm.body, &inner)?;
            binds.push(body);
            let guard = if tests.is_empty() {
                String::new()
            } else {
                format!(" if {}", tests.join(" && "))
            };
            let body = format!("{{\n{}\n}}", binds.join("\n"));
            nested_tests |= !tests.is_empty() && !p.starts_with(&format!("{NAT}("));
            out.push(format!("{p}{guard} => {body}"));
            rows.push((p, tests, body));
        }
        if nested_tests {
            // Test recursive fields after decomposition. A shared subject keeps
            // the fall-through branch available without moving a guard's input.
            let mut rest = "extract_unreachable()".to_string();
            for (pattern, tests, body) in rows.into_iter().rev() {
                let next = self.fresh("NextArm");
                let resume = format!("TautoErasedApply#r0({next}, [])");
                let branch = if tests.is_empty() {
                    body
                } else {
                    format!("if {} {body} else {{ {resume} }}", tests.join(" && "))
                };
                let continuation = self.closure(&[], &rest);
                rest = format!(
                    "{{ let {next} := {continuation}\nmatch {subject} {{ {pattern} => {branch}\n _ => {resume} }} }}"
                );
            }
            return Ok(format!("{{ let {subject} := {value}\n{rest} }}"));
        }
        out.push("_ => extract_unreachable()".into());
        Ok(format!(
            "{{ let {subject} := {value}\nmatch {subject} {{\n{}\n}} }}",
            out.join("\n")
        ))
    }
    pub(super) fn pattern(
        &mut self,
        p: &Pattern,
        notes: &[&CtorSite],
        at: &mut usize,
        locals: &mut Scope,
        tests: &mut Vec<String>,
        binds: &mut Vec<String>,
    ) -> Result<String, Message> {
        let (written, args) = match p {
            Pattern::Wild => return Ok("_".into()),
            Pattern::Bind(n)
                if !self.checked.signatures.contains_key(n)
                    && !notes.get(*at).is_some_and(|s| selected(s, n)) =>
            {
                locals.insert(n.clone());
                return Ok(self.symbol(n));
            }
            Pattern::Bind(n) => (n, &[][..]),
            Pattern::Ctor { name, args } => (name, args.as_slice()),
            Pattern::Bool(b) => return Ok(format!("{BOOL}({b})")),
            Pattern::Int(n) => return Ok(format!("{NAT}({n})")),
            _ => return Err("dependent extraction: unsupported pattern".into()),
        };
        let name = if let Some(site) = notes.get(*at)
            && selected(site, written)
        {
            *at += 1;
            site.resolved.clone()
        } else {
            written.clone()
        };
        match self.std.of(&name) {
            Some("Zero") => return Ok(format!("{NAT}(0)")),
            Some("Succ") => {
                let n = self.fresh("Nat");
                let [tail] = args else {
                    return Err("dependent extraction: successor arity".into());
                };
                self.nat_tail(tail, notes, at, locals, tests, binds, &n, 1)?;
                return Ok(format!("{NAT}({n})"));
            }
            Some("true" | "True") => return Ok(format!("{BOOL}(true)")),
            Some("false" | "False") => return Ok(format!("{BOOL}(false)")),
            Some("I64::Mk") => {
                let [Pattern::Bind(value), _] = args else {
                    return Err(
                        "dependent extraction: signed integer pattern requires a value binder"
                            .into(),
                    );
                };
                locals.erase_pattern(&args[1]);
                let n = self.fresh("Integer");
                let (_, pack, _) = self.integer_bridge()?;
                locals.insert(value.clone());
                binds.push(format!(
                    "let {} := {}",
                    self.symbol(value),
                    pack.replace("$v", &format!("extract_i64_int({n})"))
                ));
                return Ok(format!("TautoErasedI64#r0({n})"));
            }
            _ => {}
        }
        let sig = self
            .checked
            .signatures
            .get(&name)
            .ok_or_else(|| format!("dependent extraction: pattern {name}"))?;
        let roles = &sig.params[sig.params.len() - args.len()..];
        for (pattern, role) in args.iter().zip(roles) {
            if *role != Role::Value {
                locals.erase_pattern(pattern);
            }
        }
        let kept: Vec<_> = args
            .iter()
            .zip(roles)
            .filter(|(_, r)| **r == Role::Value)
            .map(|(p, _)| p.clone())
            .collect();
        let mut fields = Vec::new();
        for p in &kept {
            fields.push(self.pattern(p, notes, at, locals, tests, binds)?);
        }
        let c = self.ctor(&name)?;
        Ok(if fields.is_empty() {
            c
        } else {
            format!("{c}({})", fields.join(", "))
        })
    }
    pub(super) fn nat_tail(
        &mut self,
        pattern: &Pattern,
        notes: &[&CtorSite],
        at: &mut usize,
        locals: &mut Scope,
        tests: &mut Vec<String>,
        binds: &mut Vec<String>,
        value: &str,
        depth: usize,
    ) -> Result<(), Message> {
        let name = match pattern {
            Pattern::Bind(n) | Pattern::Ctor { name: n, .. } => Some(n),
            _ => None,
        };
        let resolved = name.map(|n| {
            if let Some(site) = notes.get(*at)
                && selected(site, n)
            {
                *at += 1;
                &site.resolved
            } else {
                n
            }
        });
        match (resolved.and_then(|n| self.std.of(n)), pattern) {
            (Some("Succ"), Pattern::Ctor { args, .. }) => {
                let [tail] = args.as_slice() else {
                    return Err("dependent extraction: successor arity".into());
                };
                self.nat_tail(tail, notes, at, locals, tests, binds, value, depth + 1)
            }
            (Some("Zero"), _) => {
                tests.push(format!("{value} == {depth}"));
                Ok(())
            }
            (_, Pattern::Int(n)) => {
                tests.push(format!("{value} == ({n} + {depth})"));
                Ok(())
            }
            (None, Pattern::Bind(n)) => {
                tests.push(if depth == 1 {
                    format!("{value} > 0")
                } else {
                    format!("{value} >= {depth}")
                });
                locals.insert(n.clone());
                binds.push(format!(
                    "let {} := {NAT}({value} - {depth})",
                    self.symbol(n)
                ));
                Ok(())
            }
            (_, Pattern::Wild) => {
                tests.push(format!("{value} >= {depth}"));
                Ok(())
            }
            _ => Err("dependent extraction: invalid natural pattern".into()),
        }
    }
}
