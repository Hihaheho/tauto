//! Typed macros: a macro whose function
//! takes a `Judgement` is run on a declaration that has been checked without it,
//! and what it makes is checked again in the declaration's place.

use std::cell::RefCell;

use super::*;
use crate::lin;
use crate::macros::checker::Verdict;
use crate::macros::syn::SpanTable;
use crate::rows::Row;
use tauto_message::{Message, msg};

/// One call of a typed macro in a declaration.
struct Site {
    name: String,
    call: Span,
    arg: SurfaceTerm,
}

/// What a checked declaration shows of itself.
struct Checked {
    report: TypeReport,
    rows: RowReport,
    lin: Vec<String>,
}

impl Expander<'_> {
    /// Whether the call is of a macro whose function takes a `Judgement`.
    pub(super) fn is_typed(&mut self, t: &SurfaceTerm) -> bool {
        let TermKind::MacroCall { name: marked, arg } = &*t.kind else {
            return false;
        };
        if matches!(&*arg.kind, TermKind::SyntaxLit(_)) {
            return false;
        }
        let (name, _) = split(marked);
        self.typed_macro(name)
    }

    fn typed_macro(&mut self, name: &str) -> bool {
        let Some(reg) = self.macros.get(name) else {
            return false;
        };
        if reg.file >= self.file {
            return false;
        }
        let function = reg.function.clone();
        self.library();
        let Some(lib) = self.lib.as_ref() else {
            return false;
        };
        match lib.report.schemes.get(&function).map(|s| &s.ty) {
            Some(Ty::Fn(params, _, _)) => matches!(
                params.as_slice(),
                [p] if matches!(p.unborrowed(), Ty::Named(n, _) if n == "Judgement")
            ),
            _ => false,
        }
    }

    /// Runs the typed macros of the declarations of this file, one by one.
    pub(super) fn typed_pass(&mut self, stmts: Vec<Stmt>) -> Vec<Stmt> {
        if self.macros.is_empty() {
            return stmts;
        }
        let names: Vec<String> = self.macros.keys().cloned().collect();
        let typed: HashSet<String> = names.into_iter().filter(|n| self.typed_macro(n)).collect();
        if typed.is_empty() {
            return stmts;
        }
        let mut out: Vec<Stmt> = Vec::new();
        for s in stmts {
            let mut probe = s.clone();
            let mut any = false;
            walk::stmt(&mut probe, &mut |t| any |= is_site(t, &typed));
            if any {
                let done = self.typed_decl(s, &out, &typed);
                out.push(done);
            } else {
                out.push(s);
            }
        }
        out
    }

    fn check(&self, before: &[Stmt], d: &Stmt) -> Checked {
        // The earlier files that check as executable code, and this file's
        // declarations so far.
        let mut all: Vec<Stmt> = match &self.lib {
            Some(lib) => lib.program.stmts.clone(),
            None => self.done.clone(),
        };
        all.extend(before.iter().cloned());
        all.push(d.clone());
        let (stmts, errors) = crate::surface::modules::resolve_in_prelude(all);
        let program = Program { stmts, errors };
        let report = check_program(&program);
        let rows = check_program_rows(&program);
        let lin = if report.errors.is_empty() {
            lin::check(&program, &report, &rows)
                .iter()
                .map(|e| e.message.clone())
                .collect()
        } else {
            Vec::new()
        };
        Checked { report, rows, lin }
    }

    fn typed_decl(&mut self, d: Stmt, before: &[Stmt], typed: &HashSet<String>) -> Stmt {
        if let Some(problem) = self.lib.as_ref().and_then(|l| l.problem.clone()) {
            let mut probe = d.clone();
            let mut first = None;
            walk::stmt(&mut probe, &mut |t| {
                if first.is_none() && is_site(t, typed) {
                    first = Some(t.span);
                }
            });
            self.error(
                "macro.library",
                msg!("macro-library", problem = problem),
                first.unwrap_or(Span::new(0, 0)),
            );
            return d;
        }
        {
            let mut all: Vec<Stmt> = self.done.clone();
            all.extend(before.iter().cloned());
            self.elab_prefix = crate::surface::modules::resolve_in_prelude(all).0;
        }
        // 1. The declaration without its typed calls.
        let mut sites: Vec<Site> = Vec::new();
        let mut plain = d.clone();
        walk::stmt(&mut plain, &mut |t| {
            if is_site(t, typed)
                && let TermKind::MacroCall { name, arg } = &*t.kind
            {
                sites.push(Site {
                    name: split(name).0.to_string(),
                    call: t.span,
                    arg: (**arg).clone(),
                });
                let arg = (**arg).clone();
                *t = arg;
            }
        });
        // A typed macro call is rejected if its argument contains another typed call.
        let mut nested = false;
        for s in &sites {
            let mut arg = s.arg.clone();
            walk::term(&mut arg, &mut |t| nested |= is_site(t, typed));
        }
        if nested {
            let at = sites[0].call;
            self.error("macro.nested_typed", msg!("macro-nested-typed"), at);
            return plain;
        }
        if matches!(d, Stmt::Theorem(_) | Stmt::Def(_)) {
            return self.typed_kernel(d, before, sites, plain, typed);
        }
        if matches!(d, Stmt::Inductive(_)) {
            let at = sites[0].call;
            self.error("macro.fragment", msg!("macro-fragment"), at);
            return plain;
        }
        // 2. It has to check as it is.
        let first = self.check(before, &plain);
        if !first.report.errors.is_empty() {
            // A function of the kernel's language is checked by the kernel.
            if matches!(d, Stmt::Fn(_)) {
                return self.typed_kernel(d, before, sites, plain, typed);
            }
            return plain;
        }
        if !self.lib_ok() {
            return plain;
        }
        // 3. Run each macro on its expression.
        let mut outputs: Vec<(SurfaceTerm, Vec<String>)> = Vec::new();
        let mut made: Vec<Expansion> = Vec::new();
        for site in &sites {
            let id = (self.expansions.len() + made.len()) as u32 + 1;
            match self.run_typed(site, id, &first) {
                Some((term, proof, row, exp)) => {
                    if let Some(proof) = proof
                        && !self.proof_holds(&d, before, site, &first, &term, proof)
                    {
                        return plain;
                    }
                    outputs.push((term, row));
                    made.push(exp);
                }
                None => return plain,
            }
        }
        // 4. Put them in the declaration's place.
        let mut next = d.clone();
        let mut at = 0usize;
        walk::stmt(&mut next, &mut |t| {
            if is_site(t, typed) && at < outputs.len() {
                *t = outputs[at].0.clone();
                at += 1;
            }
        });
        let ctors = ctor_names(
            self.done
                .iter()
                .chain(before.iter())
                .chain(std::iter::once(&next)),
        );
        let mut resolved = scope::resolve(vec![next], &ctors);
        let next = resolved.pop().expect("one statement");
        // 5. It has to check again, and mean the same.
        let second = self.check(before, &next);
        if let Some(e) = second.report.errors.first() {
            let at = sites[0].call;
            self.error(
                "macro.output_ill_typed",
                msg!("macro-output-not-check", message = e.message.clone()),
                at,
            );
            return plain;
        }
        for (site, (out, row)) in sites.iter().zip(&outputs) {
            if let Some(why) = self.compare(site, out, row, &first, &second) {
                self.error(why.0, why.1, site.call);
                return plain;
            }
        }
        // A row that is written is the signature; one that is not is inferred.
        if let (Stmt::Fn(a), Stmt::Fn(b)) = (&plain, &next)
            && a.effects.is_none()
        {
            let row_of = |c: &Checked, n: &str| {
                c.rows
                    .functions
                    .iter()
                    .find(|(f, _)| f == n)
                    .map(|(_, r)| r.clone())
            };
            if row_of(&first, &a.name) != row_of(&second, &b.name) {
                self.error(
                    "macro.signature_changed",
                    msg!("macro-signature-changed", name = &a.name),
                    sites[0].call,
                );
                return plain;
            }
        }
        // A message the declaration already had, as many times, is not the
        // macro's; one more of the same is.
        for message in &second.lin {
            let count = |c: &Checked| c.lin.iter().filter(|m| *m == message).count();
            if count(&second) > count(&first) {
                self.error(
                    "macro.ownership_rejected",
                    msg!("macro-ownership-rejected", message = message),
                    sites[0].call,
                );
                return plain;
            }
        }
        self.expansions.extend(made);
        self.file_expanded = true;
        next
    }

    /// A theorem or a definition of the kernel: the expected type and the
    /// variables at the call are what a hole in its place would have (as
    /// `tauto goals` shows them); what the macro made has to be accepted there.
    fn typed_kernel(
        &mut self,
        d: Stmt,
        before: &[Stmt],
        sites: Vec<Site>,
        plain: Stmt,
        typed: &HashSet<String>,
    ) -> Stmt {
        let mut all: Vec<Stmt> = self.done.clone();
        all.extend(before.iter().cloned());
        let (prefix, _) = crate::surface::modules::resolve_in_prelude(all);
        let checker = self.checker.clone();
        let verdict = |decl: &Stmt| -> Option<Verdict> {
            checker
                .check_in(&prefix, decl)
                .ok()?
                .into_iter()
                .last()
                .map(|e| e.verdict)
        };
        if !matches!(verdict(&plain), Some(Verdict::Checked { .. })) || !self.lib_ok() {
            return plain;
        }
        let mut outputs: Vec<SurfaceTerm> = Vec::new();
        let mut made: Vec<Expansion> = Vec::new();
        for site in sites.iter() {
            let Some(decl) = kernel_decl(&plain) else {
                return plain;
            };
            let found = self
                .checker
                .goal_of(&prefix, &decl, &site.arg)
                .map(|(context, goal)| crate::macros::checker::HoleGoal {
                    name: "macro_probe".into(),
                    span: site.arg.span,
                    goal,
                    context,
                    statement: None,
                    params: Vec::new(),
                });
            let goal = match found {
                Ok(g) => g,
                Err(m) => {
                    self.error(
                        "macro.code",
                        msg!("macro-code-no-goal", message = m),
                        site.call,
                    );
                    return plain;
                }
            };
            let id = (self.expansions.len() + made.len()) as u32 + 1;
            match self.run_kernel(site, id, &goal) {
                Some((term, proof, exp)) => {
                    if let Some(proof) = proof {
                        // The proof is for the kernel: `Eq(A, e, term)`.
                        let statement = SurfaceTerm::app(
                            "Eq",
                            vec![goal.goal.clone(), site.arg.clone(), term.clone()],
                            site.call,
                        );
                        let lemma = Stmt::Theorem(crate::surface::TheoremDecl {
            budget: None,
                            vis: Default::default(),
                            decreasing_by: None,
                            name: "macro_proof".into(),
                            implicit: 0,
                            params: goal.context.clone(),
                            ty: statement,
                            body: Some(proof),
                            span: site.call,
                        });
                        let ctors = ctor_names(self.done.iter().chain(before.iter()));
                        let lemma = scope::resolve(vec![lemma], &ctors)
                            .pop()
                            .expect("one statement");
                        match verdict(&lemma) {
                            Some(Verdict::Checked { .. }) => {}
                            Some(Verdict::Failed(e)) => {
                                self.error(
                                    "macro.proof_rejected",
                                    msg!("macro-proof-rejected", message = e.message.clone()),
                                    site.call,
                                );
                                return plain;
                            }
                            _ => {
                                self.error(
                                    "macro.proof_rejected",
                                    msg!("macro-proof-incomplete"),
                                    site.call,
                                );
                                return plain;
                            }
                        }
                    }
                    outputs.push(term);
                    made.push(exp);
                }
                None => return plain,
            }
        }
        let mut next = d.clone();
        let mut at = 0usize;
        walk::stmt(&mut next, &mut |t| {
            if is_site(t, typed) && at < outputs.len() {
                *t = outputs[at].clone();
                at += 1;
            }
        });
        let ctors = ctor_names(
            self.done
                .iter()
                .chain(before.iter())
                .chain(std::iter::once(&next)),
        );
        let next = scope::resolve(vec![next], &ctors)
            .pop()
            .expect("one statement");
        match verdict(&next) {
            Some(Verdict::Checked { .. }) => {}
            Some(Verdict::Failed(e)) if is_type_mismatch(&e.message) => {
                self.error(
                    "macro.dependent_use",
                    msg!("macro-dependent-use", message = e.message.clone()),
                    sites[0].call,
                );
                return plain;
            }
            Some(Verdict::Failed(e)) => {
                self.error(
                    "macro.output_ill_typed",
                    msg!("macro-output-rejected", message = e.message.clone()),
                    sites[0].call,
                );
                return plain;
            }
            _ => {
                self.error(
                    "macro.output_ill_typed",
                    msg!("macro-output-rejected-plain"),
                    sites[0].call,
                );
                return plain;
            }
        }
        self.expansions.extend(made);
        self.file_expanded = true;
        next
    }

    /// What answers the `elab_*` of a macro run for the expansion `id`.
    pub(super) fn elab_for(&self, id: u32) -> crate::eval::ElabFn {
        let env = super::elab::ElabEnv {
            checker: self.checker.clone(),
            prefix: self.elab_prefix.clone(),
            scope: u64::from(id),
            ctors: ctor_names(self.done.iter().chain(self.elab_prefix.iter())),
            families: ctor_families(self.done.iter().chain(self.elab_prefix.iter())),
            arities: ctor_arities(self.done.iter().chain(self.elab_prefix.iter())),
        };
        std::rc::Rc::new(move |op, args| env.call(op, args))
    }

    fn run_kernel(
        &mut self,
        site: &Site,
        id: u32,
        goal: &crate::macros::checker::HoleGoal,
    ) -> Option<(SurfaceTerm, Option<SurfaceTerm>, Expansion)> {
        let info = self.registration(&site.name, site.call)?;
        let mut atoms: HashMap<String, u64> = HashMap::new();
        for (i, (name, _)) in goal.context.iter().enumerate() {
            atoms.insert(name.clone(), i as u64 + 1);
        }
        let table = RefCell::new(SpanTable::default());
        let lift = crate::macros::syn::Lift {
            scopes: &[u64::from(id)],
            quote: false,
            atoms: Some(&atoms),
            spans: Some(&table),
            reflip: None,
        };
        let built = (|| -> Result<Node, String> {
            let mut binders = Vec::new();
            for (i, (name, ty)) in goal.context.iter().enumerate() {
                binders.push(Node::Ctor(
                    "Judgement::Binder".into(),
                    vec![
                        (Some("atom".into()), Node::Int(i as i64 + 1)),
                        (Some("name".into()), Node::text(name)),
                        (Some("ty".into()), lift.expr(ty)?),
                    ],
                ));
            }
            let term = lift.expr(&site.arg)?;
            let ty = lift.expr(&goal.goal)?;
            let code = Node::Ctor(
                "Judgement".into(),
                vec![
                    (Some("term".into()), term),
                    (Some("ty".into()), ty),
                    (Some("row".into()), Node::List(Vec::new())),
                    (Some("ctx".into()), Node::List(binders)),
                    (Some("fragment".into()), Node::text("Kernel")),
                    (Some("tys".into()), Node::List(Vec::new())),
                    (Some("usage".into()), Node::List(Vec::new())),
                    (
                        Some("span".into()),
                        Node::Ctor(
                            "SynSpan".into(),
                            vec![(Some("id".into()), Node::Int(i64::from(site.arg.span.start)))],
                        ),
                    ),
                ],
            );
            Ok(code)
        })();
        let code = match built {
            Ok(c) => c,
            Err(m) => {
                self.error("macro.code", m, site.call);
                return None;
            }
        };
        let lib = self.lib.as_ref().expect("the library is built");
        let function = self.macros[&site.name].function.clone();
        let mut host = Host::new(self.opts.call_steps, self.opts.allocations);
        host.elab = Some(self.elab_for(id));
        let ran = call_function(&lib.program, &lib.report, &function, &[code], &mut host);
        let (out, stats) = match ran {
            Ok(r) => r,
            Err(e) => {
                self.run_error(&site.name, e, site.call);
                return None;
            }
        };
        let names: HashMap<u64, String> = atoms.iter().map(|(n, a)| (*a, n.clone())).collect();
        let mut captures = Vec::new();
        let lowered = {
            let spans = &mut self.spans;
            let mut fresh = |written: u32| spans.fresh(written, id);
            let mut lower = Lower {
                scope: u64::from(id),
                fresh: &mut fresh,
                captures: Vec::new(),
                atoms: &names,
                opened: Vec::new(),
            };
            let r = match info.shape {
                Shape::Proved => match (out.named("term"), out.named("proof")) {
                    (Some(t), Some(p)) => lower
                        .expr(t)
                        .and_then(|t| lower.expr(p).map(|p| (t, Some(p)))),
                    _ => Err(format!("macro.shape: {}", msg!("macro-proved-shape"))),
                },
                _ => lower.expr(&out).map(|t| (t, None)),
            };
            captures.append(&mut lower.captures);
            r
        };
        let (mut term, mut proof) = match lowered {
            Ok(t) => t,
            Err(m) => {
                let (code, message) = m
                    .split_once(": ")
                    .filter(|(c, _)| c.starts_with("macro."))
                    .unwrap_or(("macro.shape", &m));
                self.error(code, message.to_string(), site.call);
                return None;
            }
        };
        self.term(&mut term);
        if let Some(p) = &mut proof {
            self.term(p);
        }
        let exp = Expansion {
            id,
            macro_name: site.name.clone(),
            function,
            kind: "typed",
            parent: None,
            call: site.call,
            root: 0,
            syntax: String::new(),
            text: crate::surface::print::print_term(&site.arg),
            steps: stats.steps,
            allocations: stats.allocations,
            captures,
            input: format!(
                "{} |- {} : {}",
                goal.context
                    .iter()
                    .map(|(n, t)| format!("{n}: {}", crate::surface::print::print_term(t)))
                    .collect::<Vec<_>>()
                    .join(", "),
                crate::surface::print::print_term(&site.arg),
                crate::surface::print::print_term(&goal.goal)
            ),
            output: crate::surface::print::print_term(&term),
        };
        Some((term, proof, exp))
    }

    /// A `Proved` in a function: the kernel checks `Eq(A, e, term)` with the
    /// parameters of the function for its variables.
    fn proof_holds(
        &mut self,
        d: &Stmt,
        before: &[Stmt],
        site: &Site,
        first: &Checked,
        term: &SurfaceTerm,
        proof: SurfaceTerm,
    ) -> bool {
        let Stmt::Fn(f) = d else {
            self.error(
                "macro.proof_rejected",
                msg!("macro-proved-where"),
                site.call,
            );
            return false;
        };
        let Some(ty) = first.report.terms.get(&site.arg.id()) else {
            self.error(
                "macro.proof_rejected",
                msg!("macro-proof-no-type"),
                site.call,
            );
            return false;
        };
        let Ok(ty) = crate::surface::parse_expr_at(&ty.to_string(), 0) else {
            self.error(
                "macro.proof_rejected",
                msg!("macro-proof-type-unwritable"),
                site.call,
            );
            return false;
        };
        let params: Vec<(String, SurfaceTerm)> = f
            .params
            .iter()
            .zip(&f.param_types)
            .filter_map(|(n, t)| t.clone().map(|t| (n.clone(), t)))
            .collect();
        let lemma = Stmt::Theorem(crate::surface::TheoremDecl {
            budget: None,
            vis: Default::default(),
            decreasing_by: None,
            name: "macro_proof".into(),
            implicit: 0,
            params,
            ty: SurfaceTerm::app("Eq", vec![ty, site.arg.clone(), term.clone()], site.call),
            body: Some(proof),
            span: site.call,
        });
        let mut all: Vec<Stmt> = self.done.clone();
        all.extend(before.iter().cloned());
        let (prefix, _) = crate::surface::modules::resolve_in_prelude(all);
        let ctors = ctor_names(self.done.iter().chain(before.iter()));
        let lemma = scope::resolve(vec![lemma], &ctors)
            .pop()
            .expect("one statement");
        match self
            .checker
            .check_in(&prefix, &lemma)
            .ok()
            .and_then(|e| e.into_iter().last())
            .map(|e| e.verdict)
        {
            Some(Verdict::Checked { .. }) => true,
            Some(Verdict::Failed(e)) => {
                self.error(
                    "macro.proof_rejected",
                    msg!("macro-proof-rejected", message = e.message.clone()),
                    site.call,
                );
                false
            }
            _ => {
                self.error(
                    "macro.proof_rejected",
                    msg!("macro-proof-incomplete"),
                    site.call,
                );
                false
            }
        }
    }

    fn lib_ok(&self) -> bool {
        self.lib.as_ref().is_some_and(|l| l.problem.is_none())
    }

    /// The type, and the effects, of what the macro made against what it was given.
    fn compare(
        &self,
        site: &Site,
        out: &SurfaceTerm,
        _row: &[String],
        first: &Checked,
        second: &Checked,
    ) -> Option<(&'static str, Message)> {
        let key = |t: &SurfaceTerm| t.id();
        let before = first.report.terms.get(&key(&site.arg));
        let after = second.report.terms.get(&key(out));
        if let (Some(b), Some(a)) = (before, after)
            && b.to_string() != a.to_string()
        {
            return Some((
                "macro.type_changed",
                msg!(
                    "macro-type-changed",
                    before = b.to_string(),
                    after = a.to_string()
                ),
            ));
        }
        let within = |t: &SurfaceTerm, rows: &RowReport| -> Row {
            let mut t = t.clone();
            let mut row = Row::new();
            walk::term(&mut t, &mut |x| {
                if let Some(r) = rows.calls.get(&x.id()) {
                    row.extend(r.iter().cloned());
                }
            });
            row
        };
        let was = within(&site.arg, &first.rows);
        let now = within(out, &second.rows);
        if let Some(extra) = now.difference(&was).next() {
            return Some((
                "macro.row_grew",
                msg!("macro-row-grew", effect = extra.to_string()),
            ));
        }
        None
    }

    /// Makes the `Judgement` of the argument, runs the macro, and reads what it made.
    fn run_typed(
        &mut self,
        site: &Site,
        id: u32,
        first: &Checked,
    ) -> Option<(SurfaceTerm, Option<SurfaceTerm>, Vec<String>, Expansion)> {
        let info = self.registration(&site.name, site.call)?;
        let (code, atoms, row, judgement) = match self.code_of(&site.arg, first, id) {
            Ok(c) => c,
            Err(m) => {
                self.error("macro.code", m, site.call);
                return None;
            }
        };
        let lib = self.lib.as_ref().expect("the library is built");
        let function = self.macros[&site.name].function.clone();
        let mut host = Host::new(self.opts.call_steps, self.opts.allocations);
        host.elab = Some(self.elab_for(id));
        let ran = call_function(&lib.program, &lib.report, &function, &[code], &mut host);
        for (m, at, code) in std::mem::take(&mut host.warnings) {
            let span = if at > 0 {
                Span::new(at as u32, at as u32 + 1)
            } else {
                site.call
            };
            self.warnings.push((format!("{code}: {m}"), span));
        }
        let (out, stats) = match ran {
            Ok(r) => r,
            Err(e) => {
                self.run_error(&site.name, e, site.call);
                return None;
            }
        };
        self.file_steps += stats.steps;
        if out.size() > self.opts.output_nodes {
            self.error(
                "macro.output_too_large",
                msg!(
                    "macro-output-too-large",
                    name = &site.name,
                    nodes = self.opts.output_nodes
                ),
                site.call,
            );
            return None;
        }
        let names: HashMap<u64, String> = atoms.iter().map(|(n, a)| (*a, n.clone())).collect();
        let mut captures = Vec::new();
        let lowered = {
            let spans = &mut self.spans;
            let mut fresh = |written: u32| spans.fresh(written, id);
            let mut lower = Lower {
                scope: u64::from(id),
                fresh: &mut fresh,
                captures: Vec::new(),
                atoms: &names,
                opened: Vec::new(),
            };
            let r = match info.shape {
                Shape::Proved => match (out.named("term"), out.named("proof")) {
                    (Some(t), Some(p)) => lower
                        .expr(t)
                        .and_then(|t| lower.expr(p).map(|p| (t, Some(p)))),
                    _ => Err(format!("macro.shape: {}", msg!("macro-proved-shape"))),
                },
                _ => lower.expr(&out).map(|t| (t, None)),
            };
            captures.append(&mut lower.captures);
            r
        };
        let (mut term, mut proof) = match lowered {
            Ok(t) => t,
            Err(m) => {
                let (code, message) = m
                    .split_once(": ")
                    .filter(|(c, _)| c.starts_with("macro."))
                    .unwrap_or(("macro.shape", &m));
                self.error(code, message.to_string(), site.call);
                return None;
            }
        };
        // What the macro made may call syntactic macros itself.
        self.term(&mut term);
        if let Some(p) = &mut proof {
            self.term(p);
        }
        let exp = Expansion {
            id,
            macro_name: site.name.clone(),
            function,
            kind: "typed",
            parent: None,
            call: site.call,
            root: 0,
            syntax: String::new(),
            text: crate::surface::print::print_term(&site.arg),
            steps: stats.steps,
            allocations: stats.allocations,
            captures,
            input: judgement,
            output: crate::surface::print::print_term(&term),
        };
        Some((term, proof, row, exp))
    }

    /// The `Judgement` for the argument: the term with the variables of the
    /// context as atoms, its type and effects, and the types of its parts.
    fn code_of(&self, arg: &SurfaceTerm, c: &Checked, id: u32) -> Result<CodeOf, String> {
        let key = arg.id();
        // A type written where a type goes (a field, an annotation) is not a term the
        // checker records a type for: it is a term of `Type`.
        let universe = Ty::Named("Type".into(), Vec::new());
        let ty = c.report.terms.get(&key).unwrap_or(&universe);
        let locals: HashSet<&String> = c.report.locals.keys().map(|(n, _)| n).collect();
        let mut atoms: HashMap<String, u64> = HashMap::new();
        let mut binders = Vec::new();
        for name in lin::free_vars(arg) {
            if locals.contains(&name) && !c.report.schemes.contains_key(&name) {
                let n = atoms.len() as u64 + 1;
                atoms.insert(name.clone(), n);
                // The type at the first place the name is used.
                let mut probe = arg.clone();
                let mut found: Option<Ty> = None;
                walk::term(&mut probe, &mut |t| {
                    if found.is_none()
                        && matches!(&*t.kind, TermKind::Var(v) if *v == name)
                        && let Some(ty) = c.report.terms.get(&t.id())
                    {
                        found = Some(ty.clone());
                    }
                });
                let ty =
                    found.ok_or_else(|| msg!("macro-code-no-type", name = &name).to_string())?;
                binders.push(Node::Ctor(
                    "Judgement::Binder".into(),
                    vec![
                        (Some("atom".into()), Node::Int(n as i64)),
                        (Some("name".into()), Node::text(&name)),
                        (Some("ty".into()), type_node(&ty)?),
                    ],
                ));
            }
        }
        // How the argument uses each variable of the context: moved (an affine or
        // linear value taken), borrowed, borrowed mutably, or not at all (a copy is
        // not a use that matters to ownership).
        let mut usage = Vec::new();
        for (name, atom) in &atoms {
            let mut probe = arg.clone();
            let (mut all, mut shared, mut mutable) = (0usize, 0usize, 0usize);
            walk::term(&mut probe, &mut |t| match &*t.kind {
                TermKind::Var(v) if v == name => all += 1,
                TermKind::Borrow { mutable: m, term } if matches!(&*term.kind, TermKind::Var(v) if v == name) => {
                    if *m {
                        mutable += 1;
                    } else {
                        shared += 1;
                    }
                }
                _ => {}
            });
            let moves = all.saturating_sub(shared + mutable);
            let class = c
                .report
                .locals
                .iter()
                .find(|((n, _), _)| n == name)
                .map(|(_, ty)| c.report.kind(ty));
            let owned = matches!(
                class,
                Some(crate::types::Kind::Affine | crate::types::Kind::Linear)
            );
            let how = if mutable > 0 {
                "borrowed_mut"
            } else if shared > 0 && moves == 0 {
                "borrowed"
            } else if moves > 0 && owned {
                "moved"
            } else {
                "unused"
            };
            usage.push((*atom, how));
        }
        usage.sort();
        let usage = Node::List(
            usage
                .into_iter()
                .map(|(a, how)| {
                    Node::Ctor(
                        "Judgement::Use".into(),
                        vec![
                            (Some("atom".into()), Node::Int(a as i64)),
                            (Some("how".into()), Node::text(how)),
                        ],
                    )
                })
                .collect(),
        );
        let table = RefCell::new(SpanTable::default());
        // The names the macro is given carry the scope of this expansion, which
        // lowering takes off again: what it passes on is not renamed.
        let lift = crate::macros::syn::Lift {
            scopes: &[u64::from(id)],
            quote: false,
            atoms: Some(&atoms),
            spans: Some(&table),
            reflip: None,
        };
        let term = lift.expr(arg)?;
        let mut tys = Vec::new();
        for (id, occurrence) in table.borrow().terms.iter() {
            if let Some(t) = c.report.terms.get(occurrence) {
                tys.push(Node::product(vec![
                    (None, "u64", Node::Int(*id as i64)),
                    (None, "SynExpr", type_node(t)?),
                ]));
            }
        }
        let mut row = Row::new();
        let mut probe = arg.clone();
        walk::term(&mut probe, &mut |t| {
            if let Some(r) = c.rows.calls.get(&t.id()) {
                row.extend(r.iter().cloned());
            }
        });
        let row: Vec<String> = row.into_iter().collect();
        let st = |n: &str, f: Vec<(&str, Node)>| {
            Node::Ctor(
                n.into(),
                f.into_iter()
                    .map(|(k, v)| (Some(k.to_string()), v))
                    .collect(),
            )
        };
        let code = st(
            "Judgement",
            vec![
                ("term", term),
                ("ty", type_node(ty)?),
                (
                    "row",
                    Node::List(row.iter().map(|r| Node::text(r)).collect()),
                ),
                ("ctx", Node::List(binders)),
                ("fragment", Node::text("Program")),
                ("tys", Node::List(tys)),
                ("usage", usage),
                (
                    "span",
                    st(
                        "SynSpan",
                        vec![("id", Node::Int(i64::from(arg.span.start)))],
                    ),
                ),
            ],
        );
        let ctx: Vec<String> = {
            let mut v: Vec<(&String, &u64)> = atoms.iter().collect();
            v.sort_by_key(|(_, n)| **n);
            v.iter().map(|(name, n)| format!("{name}#{n}")).collect()
        };
        let judgement = format!(
            "{} |- {} : {} ! {{{}}}",
            ctx.join(", "),
            crate::surface::print::print_term(arg),
            ty,
            row.join(", ")
        );
        Ok((code, atoms, row, judgement))
    }
}

/// The `Judgement` of an argument, the atoms of its context, its effects and its judgement.
type CodeOf = (Node, HashMap<String, u64>, Vec<String>, String);

/// A call of a typed macro with an expression for its argument.
fn is_site(t: &SurfaceTerm, typed: &HashSet<String>) -> bool {
    matches!(&*t.kind, TermKind::MacroCall { name, arg }
        if typed.contains(split(name).0) && !matches!(&*arg.kind, TermKind::SyntaxLit(_)))
}

/// A type as the syntax of a type: what the checker shows, read again.
fn type_node(ty: &Ty) -> Result<Node, String> {
    let text = ty.to_string();
    let lift = crate::macros::syn::Lift {
        scopes: &[],
        quote: false,
        atoms: None,
        spans: None,
        reflip: None,
    };
    match crate::surface::parse_expr_at(&text, 0) {
        Ok(term) => lift.expr(&term),
        Err(_) => lift.expr(&SurfaceTerm::var(&text, Span::new(0, 0))),
    }
}

/// A theorem, a definition, or a function of the kernel's language, as the
/// declaration the kernel takes.
pub(super) fn kernel_decl(d: &Stmt) -> Option<crate::surface::TheoremDecl> {
    match d {
        Stmt::Theorem(t) | Stmt::Def(t) => Some(t.clone()),
        Stmt::Fn(f) => {
            let result = f.result.clone()?;
            let mut params = Vec::new();
            for (n, t) in f.params.iter().zip(&f.param_types) {
                params.push((n.clone(), t.clone()?));
            }
            Some(crate::surface::TheoremDecl {
            budget: None,
                vis: Default::default(),
                decreasing_by: None,
                name: f.name.clone(),
                implicit: 0,
                params,
                ty: result,
                body: Some(f.body.clone()),
                span: f.span,
            })
        }
        _ => None,
    }
}

/// Whether a verdict's message is the kernel's type mismatch.
fn is_type_mismatch(message: &Message) -> bool {
    // A mismatch may come with lines added after it, as the message of another.
    matches!(
        message.id.as_ref(),
        "kernel-core-type-mismatch" | "kernel-mismatch"
    ) || message
        .as_text()
        .is_some_and(|t| t.starts_with("type mismatch"))
        || message.args.iter().any(|(_, v)| match v {
            tauto_message::Value::Message(m) => is_type_mismatch(m),
            _ => false,
        })
}
