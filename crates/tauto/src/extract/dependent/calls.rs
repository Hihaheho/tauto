//! Source-slot calling convention and direct-call specialization.
use super::*;

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
struct Prefix {
    count: usize,
    needs_value: bool,
}

type Callees = BTreeMap<String, std::collections::BTreeSet<Prefix>>;

#[derive(Default)]
pub(super) struct Applications {
    sites: HashMap<(u32, u32, usize), Callees>,
}

impl Applications {
    pub(super) fn new(checked: &Checked) -> Self {
        let parameters: HashMap<_, _> = checked
            .families
            .values()
            .flat_map(|family| {
                family
                    .ctors
                    .iter()
                    .map(move |name| (name.as_str(), family.params))
            })
            .collect();
        let mut out = Self::default();
        for site in &checked.application_sites {
            let skip = parameters.get(site.callee.as_str()).copied().unwrap_or(0);
            let needs_value = site.omitted > 0
                && checked.signatures.get(&site.callee).is_none_or(|sig| {
                    sig.result == Role::Value
                        && sig
                            .params
                            .get(skip.min(site.omitted)..site.omitted)
                            .is_none_or(|roles| roles.contains(&Role::Value))
                });
            out.sites
                .entry((site.span.start, site.span.end, site.written))
                .or_default()
                .entry(site.callee.clone())
                .or_default()
                .insert(Prefix {
                    count: site.omitted,
                    needs_value,
                });
        }
        out
    }

    fn omitted(
        &self,
        span: Span,
        written: usize,
        callee: Option<&str>,
    ) -> Result<Option<usize>, String> {
        let Some(site) = self.sites.get(&(span.start, span.end, written)) else {
            return Ok(None);
        };
        let exact = callee.and_then(|name| site.get(name));
        let candidates: std::collections::BTreeSet<_> = match exact {
            Some(counts) => counts.clone(),
            None => site
                .values()
                .flat_map(|counts| counts.iter().copied())
                .collect(),
        };
        if candidates.iter().any(|prefix| prefix.needs_value) {
            return Err(
                "dependent extraction: supply runtime implicit arguments explicitly".into(),
            );
        }
        if candidates.len() > 1 {
            return Err(format!(
                "dependent extraction: inconsistent implicit application metadata for {callee:?} at {span:?}: {candidates:?}"
            ));
        }
        Ok(candidates.into_iter().next().map(|prefix| prefix.count))
    }
}

impl Eraser<'_> {
    pub(super) fn arity(&self, name: &str) -> usize {
        self.checked
            .arities
            .get(name)
            .copied()
            .unwrap_or(self.checked.signatures[name].params.len())
    }
    pub(super) fn roles(&self, name: &str) -> Result<Vec<Role>, String> {
        let sig = self
            .checked
            .signatures
            .get(name)
            .ok_or_else(|| format!("dependent extraction: no signature for {name}"))?;
        let mut rs = sig.params.clone();
        if let Some(fam) = self
            .checked
            .families
            .values()
            .find(|f| f.ctors.iter().any(|c| c == name))
        {
            rs[..fam.params].fill(Role::Proof);
        }
        rs.truncate(self.arity(name));
        Ok(rs)
    }
    pub(super) fn omitted(
        &self,
        span: Span,
        written: usize,
        callee: Option<&str>,
    ) -> Result<Option<usize>, String> {
        self.applications.omitted(span, written, callee)
    }

    pub(super) fn lift(&mut self, name: &str) -> Result<String, String> {
        let roles = self.roles(name)?;
        let slots: Vec<_> = roles.iter().map(|_| self.fresh("Arg")).collect();
        let values = slots
            .iter()
            .zip(roles)
            .filter(|(_, role)| *role == Role::Value)
            .map(|(name, _)| name.clone())
            .collect::<Vec<_>>();
        let body = self.call(name, &values)?;
        Ok(self.closure(&slots, &body))
    }

    pub(super) fn global(
        &mut self,
        name: &str,
        args: &[SurfaceTerm],
        locals: &Scope,
        span: Span,
        applied: bool,
    ) -> Result<String, String> {
        if name == "the" {
            return self.expr(args.last().ok_or("empty ascription")?, locals);
        }
        if self.checked.families.contains_key(name)
            || name == "Type"
            || name == "Prop"
            || name == "="
            || self.std.of(name) == Some("Quot")
        {
            return Ok(ERASED.into());
        }
        let builtin = self.std.of(name).unwrap_or(name);
        if matches!(builtin, "+" | "-" | "*" | "==" | "<" | "<=" | ">" | ">=") {
            let values = args
                .iter()
                .map(|a| {
                    self.expr(a, locals)
                        .map(|s| format!("TautoErasedGetNat#r0({s})"))
                })
                .collect::<Result<Vec<_>, _>>()?;
            let [a, b] = values.as_slice() else {
                return Err("dependent extraction: binary operation arity".into());
            };
            let op = if builtin == "-" {
                format!("extract_nat_sub({a}, {b})")
            } else {
                format!("({a} {builtin} {b})")
            };
            return Ok(format!(
                "{}({op})",
                if matches!(builtin, "+" | "-" | "*") {
                    NAT
                } else {
                    BOOL
                }
            ));
        }
        let sig = self
            .checked
            .signatures
            .get(name)
            .ok_or_else(|| format!("dependent extraction: unknown global {name}"))?;
        if sig.result != Role::Value {
            return Ok(ERASED.into());
        }
        let arity = self.arity(name);
        let constructor = self
            .checked
            .families
            .values()
            .any(|family| family.ctors.iter().any(|ctor| ctor == name));
        if !applied && arity > 0 && (!constructor || sig.params[..arity].contains(&Role::Value)) {
            return self.lift(name);
        }
        let inserted = if sig.implicit == 0 {
            Some(0)
        } else {
            self.omitted(span, args.len(), Some(name))?
        };
        let omitted = match inserted {
            Some(count) => count,
            None if args.len() == arity => 0,
            None if args.len() + sig.implicit == arity => sig.implicit,
            None => {
                return Err(format!(
                    "dependent extraction: missing implicit application metadata for {name}"
                ));
            }
        };
        let roles = self.roles(name)?;
        if roles
            .get(..omitted)
            .is_none_or(|prefix| prefix.contains(&Role::Value))
        {
            return Err(
                "dependent extraction: supply runtime implicit arguments explicitly".into(),
            );
        }
        if args.len() + omitted == arity {
            let values = args
                .iter()
                .zip(&roles[omitted..])
                .filter(|(_, role)| **role == Role::Value)
                .map(|(arg, _)| self.expr(arg, locals))
                .collect::<Result<Vec<_>, _>>()?;
            self.call(name, &values)
        } else {
            let f = self.lift(name)?;
            let mut values = vec![ERASED.to_string(); omitted];
            for arg in args {
                values.push(self.expr(arg, locals)?);
            }
            Ok(format!("TautoErasedApply#r0({f}, [{}])", values.join(", ")))
        }
    }
    pub(super) fn call(&mut self, name: &str, values: &[String]) -> Result<String, String> {
        let builtin = self.std.of(name);
        match (builtin, values) {
            (Some("Quot::mk"), [value]) => return Ok(value.clone()),
            (Some("Quot::lift"), [function, value]) => {
                return Ok(format!("TautoErasedApply#r0({function}, [{value}])"));
            }
            (Some("Zero"), []) => return Ok(format!("{NAT}(0)")),
            (Some("Succ"), [n]) => return Ok(format!("{NAT}(TautoErasedGetNat#r0({n}) + 1)")),
            (Some("true" | "True"), []) => return Ok(format!("{BOOL}(true)")),
            (Some("false" | "False"), []) => return Ok(format!("{BOOL}(false)")),
            (Some("I64::Mk"), [value]) => {
                let (_, _, unpack) = self.integer_bridge()?;
                return Ok(format!(
                    "TautoErasedI64#r0(extract_i64_of_fitting({}))",
                    unpack.replace("$v", value)
                ));
            }
            _ => {}
        }
        if self
            .checked
            .families
            .values()
            .any(|f| f.ctors.iter().any(|c| c == name))
        {
            let c = self.ctor(name)?;
            return Ok(if values.is_empty() {
                c
            } else {
                format!("{c}({})", values.join(", "))
            });
        }
        let f = self.function(name)?;
        Ok(format!("{f}({})", values.join(", ")))
    }
    pub(super) fn closure(&mut self, xs: &[String], body: &str) -> String {
        let args = self.fresh("Args");
        let pattern = xs.iter().rev().fold("Nil".to_string(), |tail, x| {
            format!("Cons({}, {tail})", raw(x))
        });
        format!(
            "{FUN}({}, ({args}: List({VALUE})) => match {args} {{ {pattern} => {body}\n _ => extract_unreachable() }})",
            xs.len()
        )
    }
}
