//! Structural explanations of complete recorded derivations.
use super::*;
use crate::surface::Name;
use tauto_surface::identity::{Generation, LocalId};

pub(super) struct Edge<'a> {
    left: T,
    right: T,
    proof: &'a Derivation,
    congruence: bool,
    reversed: bool,
}

fn application(d: &Derivation) -> (&Derivation, Vec<&Derivation>) {
    let mut head = d;
    let mut args = Vec::new();
    while head.rule == Rule::Application
        && head.premises.len() == 2
        && same_context(d, &head.premises[0])
    {
        args.push(&head.premises[1]);
        head = &head.premises[0];
    }
    args.reverse();
    (head, args)
}
fn library(d: &Derivation, name: &str) -> bool {
    matches!(&*d.term.kind, TermKind::Var(n) if tauto_surface::bindings::is_library(n, name))
}
fn judgment(d: &Derivation) -> Judgment {
    (d.context.clone(), d.term.clone(), d.ty.clone())
}

impl Writer<'_> {
    pub(super) fn count(&mut self, d: &Derivation) {
        let key = judgment(d);
        if let Some((_, count)) = self.uses.iter_mut().find(|(k, _)| same_judgment(k, &key)) {
            *count += 1;
        } else {
            self.uses.push((key, 1));
        }
        for p in &d.premises {
            self.count(p);
        }
    }
    pub(super) fn use_count(&self, d: &Derivation) -> usize {
        self.uses
            .iter()
            .find(|(key, _)| same_judgment(key, &judgment(d)))
            .map_or(1, |(_, n)| *n)
    }
    fn equal(&mut self, ctx: &[(Name, T)], a: &T, b: &T) -> bool {
        super::super::same_term(a, b)
            || self.inspector.definitionally_equal(ctx, a, b) == Some(true)
    }
    fn type_only(&mut self, d: &Derivation) -> bool {
        d.is_complete()
            && self.inspector.is_proof(d) == Some(false)
            && d.premises.iter().all(|p| self.type_only(p))
    }
    pub(super) fn display_type(&mut self, ctx: &[(Name, T)], ty: &T) -> T {
        if matches!(&*ty.kind, TermKind::App { function, .. } if matches!(&*function.kind, TermKind::Lam { .. }))
        {
            if let Some(reduced) = self.inspector.reduce(ctx, ty) {
                return reduced.normal;
            }
        }
        ty.clone()
    }
    pub(super) fn transparent<'a>(&mut self, d: &'a Derivation) -> Option<&'a Derivation> {
        if !d.is_complete() {
            return None;
        }
        if d.rule == Rule::Conversion
            && d.premises.len() == 1
            && self.inspector.is_proof(d) == Some(true)
        {
            let p = &d.premises[0];
            // A computation that closes the goal retains its start and finish.
            let (head, _) = application(p);
            if (!library(head, "Refl") || super::super::same_term(&p.ty, &d.ty))
                && self.equal(&d.context, &p.ty, &d.ty)
            {
                return Some(p);
            }
        }
        let (head, args) = application(d);
        if library(head, "the")
            && args.len() == 2
            && self.type_only(args[0])
            && self.equal(&d.context, &args[0].term, &d.ty)
            && self.equal(&d.context, &args[1].ty, &d.ty)
        {
            return Some(args[1]);
        }
        None
    }
    pub(super) fn chain<'a>(&mut self, d: &'a Derivation, nested: bool) -> Option<Vec<Edge<'a>>> {
        if !d.is_complete() {
            return None;
        }
        if nested && self.use_count(d) > 1 {
            return self.edge(d);
        }
        if let Some(p) = self.transparent(d) {
            let mut edges = self.chain(p, nested)?;
            let eq = equality(&d.ty)?;
            if self.equal(&d.context, &edges.first()?.left, &eq[1])
                && self.equal(&d.context, &edges.last()?.right, &eq[2])
            {
                if show(&eq[1]).chars().count() < show(&edges.first()?.left).chars().count() {
                    edges.first_mut()?.left = eq[1].clone();
                }
                if show(&eq[2]).chars().count() < show(&edges.last()?.right).chars().count() {
                    edges.last_mut()?.right = eq[2].clone();
                }
                return Some(edges);
            }
            return None;
        }
        let eq = equality(&d.ty)?;
        let (head, args) = application(d);
        if library(head, "Eq::trans") && args.len() == 6 {
            let a = equality(&args[4].ty)?;
            let b = equality(&args[5].ty)?;
            if !self.equal(&d.context, &a[0], &eq[0])
                || !self.equal(&d.context, &b[0], &eq[0])
                || !self.equal(&d.context, &a[1], &eq[1])
                || !self.equal(&d.context, &a[2], &b[1])
                || !self.equal(&d.context, &b[2], &eq[2])
            {
                return None;
            }
            let mut left = self.chain(args[4], true)?;
            let mut right = self.chain(args[5], true)?;
            if !self.equal(&d.context, &left.last()?.right, &right.first()?.left) {
                return None;
            }
            let a = &left.last()?.right;
            let b = &right.first()?.left;
            let middle = if show(a).chars().count() <= show(b).chars().count() {
                a.clone()
            } else {
                b.clone()
            };
            left.last_mut()?.right = middle.clone();
            right.first_mut()?.left = middle;
            left.extend(right);
            return Some(left);
        }
        if library(head, "Eq::sym") && args.len() == 4 {
            let p = equality(&args[3].ty)?;
            if !self.equal(&d.context, &p[0], &eq[0])
                || !self.equal(&d.context, &p[1], &eq[2])
                || !self.equal(&d.context, &p[2], &eq[1])
            {
                return None;
            }
            let mut edges = self.chain(args[3], true)?;
            edges.reverse();
            for edge in &mut edges {
                std::mem::swap(&mut edge.left, &mut edge.right);
                edge.reversed = !edge.reversed;
            }
            return Some(edges);
        }
        if library(head, "Eq::congr") && args.len() == 6 && {
            let applied = |arg: &T| {
                T::new(
                    TermKind::App {
                        function: Box::new(args[4].term.clone()),
                        arguments: vec![arg.clone()],
                    },
                    Default::default(),
                )
            };
            equality(&args[5].ty).is_some_and(|p| {
                self.equal(&d.context, &p[0], &args[0].term)
                    && self.equal(&d.context, &p[1], &args[2].term)
                    && self.equal(&d.context, &p[2], &args[3].term)
                    && self.equal(&d.context, &eq[0], &args[1].term)
                    && self.equal(&d.context, &eq[1], &applied(&args[2].term))
                    && self.equal(&d.context, &eq[2], &applied(&args[3].term))
            })
        } {
            return Some(vec![Edge {
                left: eq[1].clone(),
                right: eq[2].clone(),
                proof: args[5],
                congruence: true,
                reversed: false,
            }]);
        }
        if nested { self.edge(d) } else { None }
    }
    fn edge<'a>(&mut self, d: &'a Derivation) -> Option<Vec<Edge<'a>>> {
        let e = equality(&d.ty)?;
        Some(vec![Edge {
            left: e[1].clone(),
            right: e[2].clone(),
            proof: d,
            congruence: false,
            reversed: false,
        }])
    }
    pub(super) fn emit_chain(
        &mut self,
        d: &Derivation,
        key: Judgment,
        depth: usize,
        mut edges: Vec<Edge<'_>>,
    ) -> Option<Text> {
        let eq = equality(&d.ty)?;
        if !self.equal(&d.context, &edges.first()?.left, &eq[1])
            || !self.equal(&d.context, &edges.last()?.right, &eq[2])
        {
            return None;
        }
        edges.first_mut()?.left = eq[1].clone();
        edges.last_mut()?.right = eq[2].clone();
        let mut reasons = Vec::new();
        for edge in &edges {
            let proof = self
                .emit(edge.proof, depth, false)
                .used(&mut self.referenced);
            let reason = match (edge.congruence, edge.reversed) {
                (true, false) => msg!("proof-chain-congruence", proof = proof).to_string(),
                (true, true) => msg!("proof-chain-congruence-reverse", proof = proof).to_string(),
                (false, true) => msg!("proof-chain-reverse", proof = proof).to_string(),
                _ => proof,
            };
            reasons.push(reason);
        }
        let lines: Vec<_> = edges
            .iter()
            .zip(reasons)
            .enumerate()
            .map(|(i, (edge, reason))| {
                let left = if i == 0 {
                    self.notation.show(&edge.left, &d.context, true)
                } else {
                    String::new()
                };
                format!(
                    "{left} = {}    ({reason})",
                    self.notation.show(&edge.right, &d.context, true)
                )
            })
            .collect();
        Some(self.step(
            key,
            &"  ".repeat(depth),
            lines.join(&format!("\n{}", "  ".repeat(depth))),
            None,
        ))
    }

    pub(super) fn construction(
        &mut self,
        d: &Derivation,
        key: Judgment,
        depth: usize,
    ) -> Option<Text> {
        let (head, args) = application(d);
        if library(head, "Refl") {
            return None;
        }
        let TermKind::Var(n) = &*head.term.kind else {
            return None;
        };
        let entry = self
            .library
            .iter()
            .find(|g| g.name == *n && g.kind == "constructor")?;
        // Only saturated constructors, whose remaining type is not a function.
        if matches!(&*d.ty.kind, TermKind::Pi { .. }) {
            return None;
        }
        let implicit = entry.implicit;
        let roles: Vec<_> = args.iter().map(|a| self.inspector.is_proof(a)).collect();
        if roles.iter().any(Option::is_none) {
            return None;
        }
        let mut data = Vec::new();
        let mut conditions = Vec::new();
        for (i, arg) in args.iter().enumerate() {
            match roles[i] {
                Some(true) => {
                    let evidence = self.emit(arg, depth, false).used(&mut self.referenced);
                    let ty = self.display_type(&arg.context, &arg.ty);
                    conditions.push(format!(
                        "{} ({evidence})",
                        self.notation.show(&ty, &arg.context, true)
                    ));
                }
                Some(false) if i < implicit && self.inline_value(arg) => {}
                Some(false) => data.push(self.emit(arg, depth, false).used(&mut self.referenced)),
                None => return None,
            }
        }
        let message = match (data.is_empty(), conditions.is_empty()) {
            (true, true) => "proof-construct-empty",
            (true, false) => "proof-construct-conditions",
            (false, true) => "proof-construct-data",
            _ => "proof-construct",
        };
        let sentence = msg!(
            message,
            constructor = self.notation.show(&head.term, &head.context, true),
            data = data.join(", "),
            conditions = conditions.join("; "),
            goal = claim(d, Some(true), self.notation)
        )
        .to_string();
        Some(self.step(key, &"  ".repeat(depth), sentence, None))
    }

    pub(super) fn elimination(
        &mut self,
        d: &Derivation,
        key: Judgment,
        depth: usize,
    ) -> Option<Text> {
        let (head, args) = application(d);
        let TermKind::Var(Name::Global(rec)) = &*head.term.kind else {
            return None;
        };
        if !matches!(
            rec.generation(),
            Some(Generation::Induction | Generation::Recursion)
        ) {
            return None;
        }
        let owner = rec.owner()?;
        if tauto_surface::bindings::is_library(&Name::Global(owner.clone()), "Eq") {
            return None;
        }
        let info = self
            .library
            .iter()
            .find(|g| matches!(&g.name, Name::Global(n) if n == owner))?
            .inductive
            .clone()?;
        let expected = info.params + 1 + info.ctors.len() + info.indices + 1;
        // Mutual eliminators have several motives and are kept in their full form.
        if args.len() != expected {
            return None;
        }
        let minors = &args[info.params + 1..info.params + 1 + info.ctors.len()];
        let mut branches = Vec::new();
        for (ctor, minor) in info.ctors.iter().zip(minors) {
            let mut body = *minor;
            let mut local = Vec::new();
            while body.rule == Rule::Introduction && body.premises.len() == 1 {
                local.extend(body.introduced.iter().cloned());
                body = &body.premises[0];
            }
            if local.len() != ctor.fields.len() + ctor.recursive.len() {
                return None;
            }
            if body.context.len() < local.len() {
                return None;
            }
            let body = {
                let mut body = body.clone();
                body.ty = self.display_type(&body.context, &body.ty);
                body
            };
            branches.push((ctor, local, body));
        }
        let major = self
            .emit(args.last()?, depth, false)
            .used(&mut self.referenced);
        let indent = "  ".repeat(depth);
        let induction = info.ctors.iter().any(|c| !c.recursive.is_empty());
        writeln!(
            self.out,
            "{indent}{}",
            msg!(
                if induction {
                    "proof-induction"
                } else if info.ctors.len() == 1 {
                    "proof-decompose"
                } else {
                    "proof-cases"
                },
                term = major,
                goal = self.notation.show(&d.ty, &d.context, true)
            )
        )
        .unwrap();
        for (ctor, local, body) in branches {
            let context_len = body.context.len().checked_sub(local.len())?;
            let mut used = HashSet::new();
            fn references(t: &T, used: &mut HashSet<Name>) {
                crate::surface::walk::term(&mut t.clone(), &mut |t| {
                    if let TermKind::Var(n) = &*t.kind {
                        used.insert(n.clone());
                    }
                });
            }
            references(&body.term, &mut used);
            references(&body.ty, &mut used);
            loop {
                let before = used.len();
                for (n, ty) in &local {
                    if used.contains(n) {
                        references(ty, &mut used);
                    }
                }
                if used.len() == before {
                    break;
                }
            }
            let assumptions = bindings(
                &local
                    .iter()
                    .enumerate()
                    .filter(|(_, (n, _))| used.contains(n))
                    .map(|(i, (n, ty))| {
                        (n.to_string(), {
                            let ctx = &body.context[..context_len + i];
                            let ty = self.display_type(ctx, ty);
                            self.notation.show(&ty, ctx, true)
                        })
                    })
                    .collect::<Vec<_>>(),
            );
            writeln!(
                self.out,
                "{indent}  {}",
                msg!(
                    if !local.iter().any(|(n, _)| used.contains(n)) {
                        "proof-branch-empty"
                    } else {
                        "proof-branch"
                    },
                    constructor = ctor.name.to_string(),
                    assumptions = assumptions,
                    goal = self.notation.show(&body.ty, &body.context, true)
                )
            )
            .unwrap();
            let previous = self.scope;
            self.next_scope += 1;
            self.scope = self.next_scope;
            self.emit(&body, depth + 2, true);
            self.scope = previous;
        }
        Some(
            self.step(
                key,
                &indent,
                msg!(
                    "proof-branches-conclude",
                    goal = self.notation.show(&d.ty, &d.context, true)
                )
                .to_string(),
                None,
            ),
        )
    }
}

/// Display-only alpha-renaming preserves each lexical identity.
pub(super) fn names(root: &Derivation) -> Derivation {
    let mut names = HashMap::<LocalId, Name>::new();
    fn register(ctx: &[(Name, T)], names: &mut HashMap<LocalId, Name>) {
        let mut used = HashSet::new();
        for (n, _) in ctx {
            if let Name::Local(r) = n {
                if !names.contains_key(&r.id()) {
                    if let Some((base, _)) = r.display().split_once('\'') {
                        if !base.is_empty() && base != "_" {
                            let mut chosen = base.to_string();
                            let mut i = 2;
                            while used.contains(&chosen)
                                || ctx
                                    .iter()
                                    .any(|(other, _)| other != n && other.as_str() == chosen)
                            {
                                let digits = i
                                    .to_string()
                                    .chars()
                                    .map(|c| {
                                        char::from_u32('₀' as u32 + c.to_digit(10).unwrap())
                                            .unwrap()
                                    })
                                    .collect::<String>();
                                chosen = format!("{base}{digits}");
                                i += 1;
                            }
                            names.insert(r.id(), Name::Local(r.with_display(chosen)));
                        }
                    }
                }
            }
            used.insert(match n {
                Name::Local(r) => names.get(&r.id()).unwrap_or(n).to_string(),
                _ => n.to_string(),
            });
        }
    }
    fn collect(d: &Derivation, names: &mut HashMap<LocalId, Name>) {
        register(&d.context, names);
        let mut ctx = d.context.clone();
        ctx.extend(d.introduced.clone());
        register(&ctx, names);
        for p in &d.premises {
            collect(p, names);
        }
    }
    collect(root, &mut names);
    fn name(n: &mut Name, names: &HashMap<LocalId, Name>) {
        if let Name::Local(r) = n {
            if let Some(chosen) = names.get(&r.id()) {
                *n = chosen.clone();
            }
        }
    }
    fn term(t: &mut T, names: &HashMap<LocalId, Name>) {
        crate::surface::walk::term(t, &mut |t| match std::sync::Arc::make_mut(&mut t.kind) {
            TermKind::Var(n) => name(n, names),
            TermKind::Lam { params, .. } => {
                for n in params {
                    name(n, names);
                }
            }
            TermKind::Pi { params, .. } => {
                for (n, _) in params {
                    if let Some(n) = n {
                        name(n, names);
                    }
                }
            }
            _ => {}
        });
    }
    fn visit(d: &mut Derivation, names: &HashMap<LocalId, Name>) {
        for (n, ty) in d.context.iter_mut().chain(&mut d.introduced) {
            name(n, names);
            term(ty, names);
        }
        term(&mut d.term, names);
        term(&mut d.ty, names);
        for p in &mut d.premises {
            visit(p, names);
        }
    }
    let mut out = root.clone();
    visit(&mut out, &names);
    out
}
