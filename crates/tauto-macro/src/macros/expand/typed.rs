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

struct Site {
    name: String,
    call: Span,
    arg: SurfaceTerm,
    /// A placed macro: checked as a hole, given what is written unchecked.
    placed: bool,
}

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
        let (name, _) = split(marked);
        if matches!(&*arg.kind, TermKind::SyntaxLit(_)) {
            return self.placed_macro(name);
        }
        self.typed_macro(name)
    }

    fn typed_macro(&mut self, name: &str) -> bool {
        let Some(reg) = self.macros.get(name) else {
            return false;
        };
        if reg.file >= self.file {
            return false;
        }
        if let Some(typed) = self.typed_macros.get(name) {
            return *typed;
        }
        let function = reg.function.clone();
        self.library_holding(&function);
        let Some(lib) = self.lib.as_ref() else {
            return false;
        };
        let typed = match lib.function(&function).map(|(_, s)| &s.ty) {
            // A typed macro takes a `Judgement`; a placed one takes it and what is written.
            Some(Ty::Fn(params, _, _)) => match params.as_slice() {
                [p] | [p, _] => {
                    matches!(p.unborrowed(), Ty::Named(n, _) if tauto_surface::bindings::is_library(&n, "Judgement"))
                }
                _ => false,
            },
            _ => false,
        };
        self.typed_macros.insert(name.to_string(), typed);
        typed
    }

    /// Whether `t` calls a tactic: a macro whose function takes a `ProofStep`. A tactic runs
    /// only as a step (`by t!(…): G { … }`); a call of one anywhere else is what a macro reads
    /// to make a step, so it waits for that macro.
    pub(super) fn is_tactic(&mut self, t: &SurfaceTerm) -> bool {
        let TermKind::MacroCall { name: marked, arg } = &*t.kind else {
            return false;
        };
        if matches!(&*arg.kind, TermKind::SyntaxLit(_)) {
            return false;
        }
        let name = split(marked).0;
        let Some(reg) = self.macros.get(name) else {
            return false;
        };
        if reg.file >= self.file {
            return false;
        }
        let function = reg.function.clone();
        self.library_holding(&function);
        let Some(lib) = self.lib.as_ref() else {
            return false;
        };
        matches!(lib.function(&function).map(|(_, s)| &s.ty), Some(Ty::Fn(params, _, _))
            if matches!(params.as_slice(), [p] if matches!(p.unborrowed(), Ty::Named(n, _) if tauto_surface::bindings::is_library(&n, "ProofStep"))))
    }

    /// Whether the macro's function takes the goal of its place and what is written, unchecked.
    pub(super) fn placed_macro(&mut self, name: &str) -> bool {
        if !self.typed_macro(name) {
            return false;
        }
        let function = self.macros[name].function.clone();
        let Some(lib) = self.lib.as_ref() else {
            return false;
        };
        matches!(lib.function(&function).map(|(_, s)| &s.ty), Some(Ty::Fn(params, _, _)) if params.len() == 2)
    }

    pub(super) fn typed_pass(&mut self, mut stmts: Vec<Stmt>) -> Vec<Stmt> {
        if self.macros.is_empty() {
            return stmts;
        }
        // The names the file wrote in a literal a macro read (`${lem(n)}` in
        // `proof!`), still as written, by where. A name a macro makes is bound in
        // the macro's file already.
        let literals: Vec<Span> = self
            .syntaxes
            .uses
            .borrow()
            .iter()
            .map(|u| u.lit.span)
            .collect();
        // A node of an expansion stands where it was written; one a macro made
        // stands at the call, outside the literal.
        let spans = &self.spans;
        let in_literal = |at: Span| {
            let at = spans
                .origin(at.start)
                .map_or(at.start, |(written, _)| written);
            literals.iter().any(|l| l.start <= at && at < l.end)
        };
        let mut written: Vec<HashMap<Span, String>> = Vec::new();
        for s in &mut stmts {
            let mut here = HashMap::new();
            walk::stmt(s, &mut |t| {
                if let TermKind::Var(crate::surface::Name::Spelled(spelling)) = &*t.kind
                    && in_literal(t.span)
                {
                    here.insert(t.span, spelling.clone());
                }
            });
            written.push(here);
        }
        // Embedded syntax is still source syntax here. Bind it in the caller's
        // file environment before the typed checker retains its references.
        self.bind_outside_placed(&mut stmts);
        for (s, here) in stmts.iter_mut().zip(&written) {
            if here.is_empty() {
                continue;
            }
            // Inside `module M`, a short name means `M`'s declaration where
            // there is one, as it does outside the literal.
            // Only a `module`: the namespace of a type (`Tm` of `Tm::check`) is a
            // declaration itself, and a module is not.
            let is_module = |m: &str| self.bindings.source_reference(m).is_none();
            let module = declared_module(s);
            let bindings = &self.bindings;
            let mut found = Vec::new();
            walk::stmt(s, &mut |t| {
                let Some(spelling) = here.get(&t.span) else {
                    return;
                };
                let TermKind::Var(name) = &*t.kind else {
                    return;
                };
                if !matches!(name, crate::surface::Name::Global(_)) {
                    return;
                }
                let mut name = name.clone();
                if let Some(module) = &module
                    && !spelling.contains("::")
                {
                    let mut prefix = module.as_str();
                    loop {
                        if is_module(prefix)
                            && let Some(inner) =
                                bindings.source_reference(&format!("{prefix}::{spelling}"))
                            && inner.as_global().is_some()
                        {
                            name = inner;
                            t.kind = std::sync::Arc::new(TermKind::Var(name.clone()));
                            break;
                        }
                        match prefix.rsplit_once("::") {
                            Some((outer, _)) => prefix = outer,
                            None => break,
                        }
                    }
                }
                found.push((name, spelling.clone(), t.span));
            });
            let file = self.file;
            self.written
                .extend(found.into_iter().map(|(n, w, at)| (file, n, w, at)));
        }
        let names: Vec<String> = self.macros.keys().cloned().collect();
        let typed: HashSet<String> = names.into_iter().filter(|n| self.typed_macro(n)).collect();
        if typed.is_empty() {
            return stmts;
        }
        self.typed_items(stmts, &[], &[], &typed)
    }

    /// `stmts` in the modules `path`, innermost last, after the declarations `outer`.
    fn typed_items(
        &mut self,
        stmts: Vec<Stmt>,
        path: &[(String, tauto_parol::Span)],
        outer: &[Stmt],
        typed: &HashSet<String>,
    ) -> Vec<Stmt> {
        let mut out: Vec<Stmt> = Vec::new();
        let all = stmts;
        for (i, s) in all.iter().cloned().enumerate() {
            let mut probe = s.clone();
            let mut any = false;
            walk::stmt(&mut probe, &mut |t| any |= is_site(t, typed));
            if !any {
                out.push(s);
                continue;
            }
            let mut before = outer.to_vec();
            before.extend(super::step::wrap(path, out.clone()));
            match s {
                Stmt::Module { name, items, span } => {
                    let mut inner = path.to_vec();
                    inner.push((name.clone(), span));
                    let items = self.typed_items(items, &inner, &before, typed);
                    out.push(Stmt::Module { name, items, span });
                }
                s if path.is_empty() => {
                    // A declaration of a module already written out keeps the
                    // module in its name.
                    self.elab_module = kernel_decl(&s)
                        .map(|d| d.name.to_string())
                        .and_then(|n| n.rsplit_once("::").map(|(m, _)| m.to_string()))
                        .map(|m| m.split("::").map(str::to_string).collect())
                        .unwrap_or_default();
                    let mut s = s;
                    let names = self.module_names();
                    walk::stmt(&mut s, &mut |t| super::elab::module_resolved(t, &names));
                    // The file's check declares a helper written further on
                    // before its first use, so the macro's check does too.
                    let later: Vec<Stmt> = all[i + 1..]
                        .iter()
                        .map(|l| {
                            let mut l = l.clone();
                            walk::stmt(&mut l, &mut |t| {
                                if is_site(t, typed)
                                    && let TermKind::MacroCall { arg, .. } = &*t.kind
                                {
                                    *t = (**arg).clone();
                                }
                            });
                            l
                        })
                        .collect();
                    let later = self.checker.used_later(&s, &later);
                    let mut before = before;
                    before.extend(later);
                    let done = self.typed_decl(s, &before, typed);
                    self.elab_module.clear();
                    out.push(done);
                }
                s => {
                    // The declaration is checked with its names written out,
                    // and keeps its own name, which the module still gives it.
                    let mut all: Vec<Stmt> = self.done.clone();
                    all.extend(before.iter().cloned());
                    all.extend(super::step::wrap(path, vec![s]));
                    let flat = crate::surface::modules::resolve_in_prelude(all)
                        .0
                        .pop()
                        .expect("the declaration");
                    self.elab_module = path.iter().map(|(n, _)| n.clone()).collect();
                    let done = self.typed_decl(flat, &before, typed);
                    self.elab_module.clear();
                    out.push(done);
                }
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
        let (mut stmts, errors) = crate::surface::modules::resolve_in_prelude(all);
        self.bindings.clone().statements(&mut stmts);
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
        // The declaration is checked with every file before this one.
        self.current_library();
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
            all.extend(signature_only(&d));
            self.elab_prefix = crate::surface::modules::resolve_in_prelude(all).0;
        }
        let placed_names: HashSet<String> = typed
            .iter()
            .filter(|n| self.placed_macro(n))
            .cloned()
            .collect();
        let mut sites: Vec<Site> = Vec::new();
        let mut plain = d.clone();
        walk::stmt(&mut plain, &mut |t| {
            if is_site(t, typed)
                && let TermKind::MacroCall { name, arg } = &*t.kind
            {
                let placed = placed_names.contains(split(name).0);
                let hole = SurfaceTerm::new(TermKind::Hole(placed_hole(sites.len())), t.span);
                sites.push(Site {
                    name: split(name).0.to_string(),
                    call: t.span,
                    arg: (**arg).clone(),
                    placed,
                });
                *t = if placed { hole } else { (**arg).clone() };
            }
        });
        // A call a macro made calls its macro as one written in the file: the
        // file's import of the macro is used.
        for s in &sites {
            if self.spans.origin(s.call.start).is_some() {
                self.written.push((
                    self.file,
                    crate::surface::Name::from(s.name.as_str()),
                    format!("{}{}", crate::surface::qualify::CALLED, s.name),
                    s.call,
                ));
            }
        }
        // A typed macro call is rejected if its argument contains another typed call.
        let mut nested = false;
        // What a placed macro is given is data: the calls in it are not expanded with it.
        for s in sites.iter().filter(|s| !s.placed) {
            let mut arg = s.arg.clone();
            walk::term(&mut arg, &mut |t| nested |= is_site(t, typed));
        }
        if nested {
            let at = sites[0].call;
            self.error("macro.nested_typed", msg!("macro-nested-typed"), at);
            return plain;
        }
        // The steps of the declaration, those in the arguments too, run first,
        // with the arguments where they are: a step's goal is the type at its
        // place in the argument the macro is given.
        let (d, plain) = if super::step::has_step(&plain) {
            let errors = self.errors.len();
            let ids: Vec<_> = sites.iter().map(|s| s.arg.id()).collect();
            let expanded = self.step_decl(plain, before);
            {
                let mut all: Vec<Stmt> = self.done.clone();
                all.extend(before.iter().cloned());
                all.extend(signature_only(&d));
                self.elab_prefix = crate::surface::modules::resolve_in_prelude(all).0;
            }
            if self.errors.len() > errors {
                return expanded;
            }
            // What a placed macro is given is data, and stays as it is; its place is a hole.
            let mut args: Vec<Option<SurfaceTerm>> = sites
                .iter()
                .map(|s| s.placed.then(|| s.arg.clone()))
                .collect();
            let mut probe = expanded.clone();
            walk::stmt(&mut probe, &mut |t| {
                if let Some(k) = ids
                    .iter()
                    .zip(&sites)
                    .position(|(id, s)| !s.placed && *id == t.id())
                {
                    args[k].get_or_insert_with(|| t.clone());
                }
            });
            let Some(args) = args.into_iter().collect::<Option<Vec<_>>>() else {
                self.error(
                    "step.fragment",
                    msg!("macro-step-typed-argument"),
                    sites[0].call,
                );
                return expanded;
            };
            for (site, arg) in sites.iter_mut().zip(&args) {
                site.arg = arg.clone();
            }
            let mut next = d;
            let mut k = 0usize;
            walk::stmt(&mut next, &mut |t| {
                if is_site(t, typed)
                    && k < args.len()
                    && let TermKind::MacroCall { name, .. } = &*t.kind
                {
                    *t = SurfaceTerm::new(
                        TermKind::MacroCall {
                            name: name.clone(),
                            arg: Box::new(args[k].clone()),
                        },
                        t.span,
                    );
                    k += 1;
                }
            });
            (next, expanded)
        } else {
            (d, plain)
        };
        if matches!(d, Stmt::Theorem(_) | Stmt::Def(_)) {
            return self.typed_kernel(d, before, sites, plain, typed);
        }
        if matches!(d, Stmt::Inductive(_)) {
            let at = sites[0].call;
            self.error("macro.fragment", msg!("macro-fragment"), at);
            return plain;
        }
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
            let row_of = |c: &Checked, n: &crate::surface::Name| {
                c.rows
                    .functions
                    .iter()
                    .find(|(f, _)| f == n)
                    .map(|(_, r)| r.clone())
            };
            if row_of(&first, &a.name) != row_of(&second, &b.name) {
                self.error(
                    "macro.signature_changed",
                    msg!("macro-signature-changed", name = a.name.to_string()),
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
        let (mut prefix, _) = crate::surface::modules::resolve_in_prelude(all);
        self.bindings.clone().statements(&mut prefix);
        let checker = self.checker.clone();
        let verdict = |decl: &Stmt| -> Option<Verdict> {
            checker
                .check_in(&prefix, decl)
                .ok()?
                .into_iter()
                .last()
                .map(|e| e.verdict)
        };
        // A placed macro is checked as a hole, so the plain declaration is incomplete.
        let first = verdict(&plain);
        let holes = match &first {
            Some(Verdict::Incomplete { holes, .. }) => holes.clone(),
            _ => Vec::new(),
        };
        let placed_any = sites.iter().any(|s| s.placed);
        let checked = matches!(first, Some(Verdict::Checked { .. }))
            || (placed_any && matches!(first, Some(Verdict::Incomplete { .. })));
        if !checked || !self.lib_ok() {
            // A declaration a placed macro's output made reports why it does not check.
            if placed_any && let Some(Verdict::Failed(e)) = &first {
                self.error(
                    "macro.output_ill_typed",
                    msg!("macro-output-rejected", message = e.message.clone()),
                    sites[0].call,
                );
            }
            return plain;
        }
        let mut outputs: Vec<SurfaceTerm> = Vec::new();
        let mut made: Vec<Expansion> = Vec::new();
        for (index, site) in sites.iter().enumerate() {
            let Some(decl) = kernel_decl(&plain) else {
                return plain;
            };
            let found = if site.placed {
                holes
                    .iter()
                    .find(|h| h.name == placed_hole(index))
                    .cloned()
                    .ok_or_else(|| "the place of the macro has no goal".to_string())
            } else {
                self.checker
                    .goal_of(&prefix, &decl, &site.arg)
                    .map(|(context, goal)| crate::macros::checker::HoleGoal {
                        name: "macro_probe".into(),
                        span: site.arg.span,
                        goal,
                        context,
                        statement: None,
                        params: Vec::new(),
                    })
            };
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
                Some((mut term, proof, exp)) => {
                    super::elab::module_resolved(&mut term, &self.module_names());
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
        if self.has_site(&next, typed) {
            self.expansions.extend(made);
            self.file_expanded = true;
            self.typed_rounds += 1;
            if self.typed_rounds > self.opts.depth {
                self.error(
                    "macro.depth_exceeded",
                    msg!(
                        "macro-depth-exceeded",
                        depth = self.opts.depth,
                        chain = String::new()
                    ),
                    sites[0].call,
                );
                return next;
            }
            // The output's binders are bound as the declaration's are, so the next
            // round's places see the same variables the declaration binds.
            let mut next = next;
            self.bind_outside_placed(std::slice::from_mut(&mut next));
            return self.typed_decl(next, before, typed);
        }
        // A step the output made, with no place left around it, is expanded as a
        // written step is; a round with places left expands its steps first
        // (`typed_decl`). Either way the kernel checks what the tactic made.
        let next = if super::step::has_step(&next) {
            self.expansions.extend(std::mem::take(&mut made));
            self.file_expanded = true;
            let errors = self.errors.len();
            let next = self.step_decl(next, before);
            if self.errors.len() > errors {
                return next;
            }
            next
        } else {
            next
        };
        match verdict(&next) {
            Some(Verdict::Checked { .. }) => {}
            Some(Verdict::Failed(e)) if is_type_mismatch(&e.message) => {
                self.error(
                    "macro.dependent_use",
                    msg!("macro-dependent-use", message = e.message.clone()),
                    sites[0].call,
                );
                return if placed_any { next } else { plain };
            }
            Some(Verdict::Failed(e)) => {
                self.error(
                    "macro.output_ill_typed",
                    msg!("macro-output-rejected", message = e.message.clone()),
                    sites[0].call,
                );
                return if placed_any { next } else { plain };
            }
            _ => {
                self.error(
                    "macro.output_ill_typed",
                    msg!("macro-output-rejected-plain"),
                    sites[0].call,
                );
                return if placed_any { next } else { plain };
            }
        }
        self.expansions.extend(made);
        self.file_expanded = true;
        next
    }

    /// The declarations of the enclosing modules by their names there, inner
    /// modules winning.
    pub(super) fn module_names(&self) -> HashMap<String, tauto_surface::identity::DeclRef> {
        let mut names = HashMap::new();
        let declarations = self.bindings.declarations();
        for depth in 1..=self.elab_module.len() {
            let module = format!("{}::", self.elab_module[..depth].join("::"));
            for (_, reference) in declarations.bindings() {
                if let Some(short) = reference.display().strip_prefix(&module) {
                    // A name the file already gives a declaration keeps it.
                    if self.bindings.source_reference(short).is_some() {
                        continue;
                    }
                    names.insert(short.to_string(), reference.clone());
                }
            }
        }
        names
    }

    /// Binds the names of `stmts` in the file's environment, but not in what a
    /// placed macro is given: that is data the macro reads, and a name in it
    /// stays as written for the place the macro's output takes.
    fn bind_outside_placed(&mut self, stmts: &mut [Stmt]) {
        let names: Vec<String> = self.macros.keys().cloned().collect();
        let placed: HashSet<String> = names.into_iter().filter(|n| self.placed_macro(n)).collect();
        let mut held: Vec<SurfaceTerm> = Vec::new();
        for s in stmts.iter_mut() {
            walk::stmt(s, &mut |t| {
                if let TermKind::MacroCall { name, arg } = &*t.kind
                    && placed.contains(split(name).0)
                {
                    held.push((**arg).clone());
                    let hole = SurfaceTerm::new(TermKind::Hole(HELD.into()), arg.span);
                    *t = t.with_kind(
                        TermKind::MacroCall {
                            name: name.clone(),
                            arg: Box::new(hole),
                        },
                        t.span,
                    );
                }
            });
        }
        self.file_bindings().statements(stmts);
        let mut held = held.into_iter();
        for s in stmts.iter_mut() {
            walk::stmt(s, &mut |t| {
                if let TermKind::MacroCall { name, arg } = &*t.kind
                    && matches!(&*arg.kind, TermKind::Hole(h) if h == HELD)
                    && let Some(given) = held.next()
                {
                    *t = t.with_kind(
                        TermKind::MacroCall {
                            name: name.clone(),
                            arg: Box::new(given),
                        },
                        t.span,
                    );
                }
            });
        }
    }

    fn has_site(&self, s: &Stmt, typed: &HashSet<String>) -> bool {
        let mut probe = s.clone();
        let mut any = false;
        walk::stmt(&mut probe, &mut |t| any |= is_site(t, typed));
        any
    }

    /// What answers the `elab_*` of a macro run for the expansion `id`.
    pub(super) fn elab_for(
        &self,
        id: u32,
        atoms: &HashMap<crate::surface::Name, u64>,
    ) -> crate::eval::ElabFn {
        let mut prefix = crate::surface::modules::resolve_in_prelude(self.elab_prefix.clone()).0;
        let mut bindings = self.bindings.clone();
        bindings.statements(&mut prefix);
        // Syntax read by the macro names a declaration of an enclosing module
        // as the module's own items do: inner modules first.
        let module_names = self.module_names();
        let mut metadata = kernel_prelude().to_vec();
        metadata.extend(prelude().stmts.clone());
        tauto_surface::resolve::Resolver::new(
            tauto_surface::bindings::library_definition_bindings(),
        )
        .statements(&mut metadata);
        metadata.extend(prefix.iter().cloned());
        let env = super::elab::ElabEnv {
            bindings,
            checker: self.checker.clone(),
            atoms: std::cell::RefCell::new(
                atoms
                    .iter()
                    .map(|(name, atom)| (*atom, name.clone()))
                    .collect(),
            ),
            prefix,
            module_names,
            scope: u64::from(id),
            ctors: ctor_names(self.done.iter().chain(self.elab_prefix.iter())),
            families: ctor_families(metadata.iter()),
            arities: ctor_arities(metadata.iter()),
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
        let mut atoms: HashMap<crate::surface::Name, u64> = HashMap::new();
        for (i, (name, _)) in goal.context.iter().enumerate() {
            atoms.insert(name.clone(), i as u64 + 1);
        }
        // What the macro makes of an atom is the variable as the declaration binds
        // it: a variable the checker copied (a `match` that generalizes, a hole
        // checked again) is named after the one it was copied from.
        let rooted: HashMap<u64, crate::surface::Name> = goal
            .context
            .iter()
            .enumerate()
            .map(|(i, (name, _))| (i as u64 + 1, root_name(name)))
            .collect();
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
            let term = if site.placed {
                lift.expr(&SurfaceTerm::new(
                    TermKind::Hole("placed".into()),
                    site.call,
                ))?
            } else {
                lift.expr(&site.arg)?
            };
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
        let mut args = vec![code];
        if site.placed {
            let written = match (&*site.arg.kind, &info.input) {
                (TermKind::SyntaxLit(lit), super::Input::Syntax(s)) => {
                    match self.syntaxes.read(s, lit, site.call, &[u64::from(id)]) {
                        Ok(n) => n,
                        Err((m, at)) => {
                            self.errors.push((m, at));
                            return None;
                        }
                    }
                }
                (_, super::Input::Expr) => {
                    let lift = crate::macros::syn::Lift {
                        scopes: &[u64::from(id)],
                        quote: false,
                        atoms: None,
                        spans: None,
                        reflip: Some(u64::from(id)),
                    };
                    match lift.expr(&site.arg) {
                        Ok(n) => n,
                        Err(m) => {
                            self.error("macro.argument", m, site.call);
                            return None;
                        }
                    }
                }
                _ => {
                    self.error(
                        "macro.argument",
                        msg!("macro-argument-literal", name = &site.name),
                        site.call,
                    );
                    return None;
                }
            };
            args.push(written);
        }
        let function = self.macros[&site.name].function.clone();
        let mut host = Host::new(self.opts.call_steps, self.opts.allocations);
        host.resolve_global = Some(self.global_resolver(&site.name));
        host.elab = Some(self.elab_for(id, &atoms));
        // A macro that asks `syn_expand` is run again with the answer, as `call` runs it.
        let ran = loop {
            let lib = self.lib.as_ref().expect("the library is built");
            let ran =
                call_bound_function(&lib.program, &lib.report, &info.function, &args, &mut host);
            let Err(RunError::NeedExpand(asked)) = ran else {
                break ran;
            };
            if host.expanded.len() >= self.opts.depth * 4 {
                self.error(
                    "macro.depth_exceeded",
                    msg!(
                        "macro-expand-exceeded",
                        name = &site.name,
                        count = self.opts.depth * 4
                    ),
                    site.call,
                );
                return None;
            }
            let errors = self.errors.len();
            match self.expand_node(&asked, id, site.call) {
                Some(a) if self.errors.len() == errors => host.expanded.push((asked, a)),
                _ => return None,
            }
        };
        let (out, stats) = match ran {
            Ok(r) => r,
            Err(e) => {
                self.run_error(&site.name, e, site.call);
                return None;
            }
        };
        let names = rooted;
        let mut captures = Vec::new();
        let lowered = {
            let spans = &mut self.spans;
            let mut fresh = |written: u32| spans.fresh(written, id, site.call.start);
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
            function: function.to_string(),
            kind: "typed",
            parent: None,
            call: site.call,
            root: 0,
            syntax: String::new(),
            text: crate::surface::print::print_term(&site.arg),
            steps: stats.steps,
            allocations: stats.allocations,
            captures,
            input_tree: None,
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
        let Ok(ty) = type_term(ty) else {
            self.error(
                "macro.proof_rejected",
                msg!("macro-proof-type-unwritable"),
                site.call,
            );
            return false;
        };
        let params: Vec<(crate::surface::Name, SurfaceTerm)> = f
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
        let (mut prefix, _) = crate::surface::modules::resolve_in_prelude(all);
        self.bindings.clone().statements(&mut prefix);
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
        host.resolve_global = Some(self.global_resolver(&site.name));
        host.elab = Some(self.elab_for(id, &atoms));
        let ran = call_bound_function(
            &lib.program,
            &lib.report,
            &info.function,
            &[code],
            &mut host,
        );
        for (m, at, code) in std::mem::take(&mut host.warnings) {
            let span = if at > 0 {
                Span::new(at as u32, at as u32 + 1)
            } else {
                site.call
            };
            self.warnings.push((format!("{code}: {m}").into(), span));
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
        let names: HashMap<u64, crate::surface::Name> =
            atoms.iter().map(|(n, a)| (*a, n.clone())).collect();
        let mut captures = Vec::new();
        let lowered = {
            let spans = &mut self.spans;
            let mut fresh = |written: u32| spans.fresh(written, id, site.call.start);
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
            function: function.to_string(),
            kind: "typed",
            parent: None,
            call: site.call,
            root: 0,
            syntax: String::new(),
            text: crate::surface::print::print_term(&site.arg),
            steps: stats.steps,
            allocations: stats.allocations,
            captures,
            input_tree: None,
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
        let locals: HashSet<&crate::surface::Name> =
            c.report.locals.keys().map(|(n, _)| n).collect();
        let mut atoms: HashMap<crate::surface::Name, u64> = HashMap::new();
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
                let ty = found.ok_or_else(|| {
                    msg!("macro-code-no-type", name = name.to_string()).to_string()
                })?;
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
        let mut selected = arg.clone();
        let mut selection_error = None;
        walk::term(&mut selected, &mut |term| {
            if let Err(error) = c.report.resolve_selection_at(term) {
                selection_error.get_or_insert(error);
            }
        });
        if let Some(error) = selection_error {
            return Err(error.to_string());
        }
        let term = lift.expr(&selected)?;
        let mut tys = Vec::new();
        for (id, occurrence) in table.borrow().terms.iter() {
            if let Some(t) = c.report.terms.get(occurrence) {
                tys.push(Node::product(vec![type_node(t)?, Node::Int(*id as i64)]));
            }
        }
        let mut row = Row::new();
        let mut probe = arg.clone();
        walk::term(&mut probe, &mut |t| {
            if let Some(r) = c.rows.calls.get(&t.id()) {
                row.extend(r.iter().cloned());
            }
        });
        let row: Vec<String> = row.into_iter().map(|n| n.to_string()).collect();
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
            let mut v: Vec<(&crate::surface::Name, &u64)> = atoms.iter().collect();
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
type CodeOf = (
    Node,
    HashMap<crate::surface::Name, u64>,
    Vec<String>,
    String,
);

fn is_site(t: &SurfaceTerm, typed: &HashSet<String>) -> bool {
    matches!(&*t.kind, TermKind::MacroCall { name, arg }
        if typed.contains(split(name).0) && !matches!(&*arg.kind, TermKind::SyntaxLit(_)))
}

/// The type's structural syntax, retaining every nominal and parameter reference.
fn type_term(ty: &Ty) -> Result<SurfaceTerm, String> {
    let span = Span::new(0, 0);
    let make = |kind| SurfaceTerm::new(kind, span);
    let apply = |function: SurfaceTerm, arguments: Vec<SurfaceTerm>| {
        if arguments.is_empty() {
            function
        } else {
            make(TermKind::App {
                function: Box::new(function),
                arguments,
            })
        }
    };
    let parts = |types: &[Ty]| types.iter().map(type_term).collect::<Result<Vec<_>, _>>();
    Ok(match ty {
        Ty::Named(name, arguments) => apply(SurfaceTerm::var(name, span), parts(arguments)?),
        Ty::Param(parameter, _) => SurfaceTerm::var(parameter.reference(), span),
        Ty::App(head, argument) => apply(type_term(head)?, vec![type_term(argument)?]),
        Ty::Union(types) => make(TermKind::Union(parts(types)?)),
        Ty::Tagged(tags, inner) => {
            let mut term = type_term(inner)?;
            for tag in tags.iter().rev() {
                term = make(TermKind::Tagged {
                    tag: tag.clone(),
                    term: Box::new(term),
                });
            }
            term
        }
        Ty::Borrow(inner, mutable) => make(TermKind::Borrow {
            mutable: *mutable,
            term: Box::new(type_term(inner)?),
        }),
        Ty::Info(inner) => apply(
            SurfaceTerm::var(&tauto_surface::bindings::library_name("Info"), span),
            vec![type_term(inner)?],
        ),
        Ty::Fn(parameters, result, kind) => {
            let term = make(TermKind::Pi {
                params: parts(parameters)?
                    .into_iter()
                    .map(|ty| (None, ty))
                    .collect(),
                result: Box::new(type_term(result)?),
                effects: None,
            });
            if matches!(
                kind,
                crate::types::Kind::Affine | crate::types::Kind::Linear
            ) {
                make(TermKind::FnKind {
                    kind: kind.to_string(),
                    ty: Box::new(term),
                })
            } else {
                term
            }
        }
        Ty::Var(_) | Ty::Poly(..) => {
            return Err("the type has no closed surface representation".into());
        }
        Ty::Int(_)
        | Ty::Bool
        | Ty::Text
        | Ty::Unit
        | Ty::Never
        | Ty::Decimal
        | Ty::Float
        | Ty::Float32 => SurfaceTerm::var(
            &tauto_surface::bindings::library_name(&ty.to_string()),
            span,
        ),
    })
}

fn type_node(ty: &Ty) -> Result<Node, String> {
    crate::macros::syn::Lift {
        scopes: &[],
        quote: false,
        atoms: None,
        spans: None,
        reflip: None,
    }
    .expr(&type_term(ty)?)
}

/// The declaration `d` without its body, for what a macro in its body
/// elaborates: a call of the declaration itself (its induction hypothesis
/// once the body is checked) has the type the declaration states.
fn signature_only(d: &Stmt) -> Option<Stmt> {
    let mut t = kernel_decl(d)?;
    t.body = None;
    t.decreasing_by = None;
    Some(Stmt::Theorem(t))
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

#[cfg(test)]
mod identity_tests {
    use super::*;

    #[test]
    fn type_syntax_keeps_distinct_declarations_with_the_same_display() {
        let first = crate::surface::Name::Global(tauto_surface::identity::DeclRef::fresh("T"));
        let second = crate::surface::Name::Global(tauto_surface::identity::DeclRef::fresh("T"));
        let first_node = type_node(&Ty::Named(first.clone(), vec![])).unwrap();
        let second_node = type_node(&Ty::Named(second.clone(), vec![])).unwrap();
        assert_ne!(first_node, second_node);
        assert!(
            matches!(&*type_term(&Ty::Named(first.clone(), vec![])).unwrap().kind, TermKind::Var(name) if name == &first)
        );
        assert!(
            matches!(&*type_term(&Ty::Named(second.clone(), vec![])).unwrap().kind, TermKind::Var(name) if name == &second)
        );
    }
}

/// The module a declaration is in, from its full name (`M` of `M::t`).
fn declared_module(s: &Stmt) -> Option<String> {
    let name = match s {
        Stmt::Fn(f) => &f.name,
        Stmt::Theorem(d) | Stmt::Def(d) => &d.name,
        Stmt::Attributed { stmt, .. } => return declared_module(stmt),
        _ => return None,
    };
    let text = match name.as_global() {
        Some(reference) => reference.display().to_string(),
        None => name.spelling()?.to_string(),
    };
    text.rsplit_once("::").map(|(module, _)| module.to_string())
}

/// The hole a placed macro's call is checked as.
fn placed_hole(index: usize) -> String {
    format!("placed'{index}")
}

/// Stands for what a placed macro is given while the file's names are bound.
const HELD: &str = "placed'held";

/// The variable a copied local was made from, through every copy.
fn root_name(name: &crate::surface::Name) -> crate::surface::Name {
    match name {
        crate::surface::Name::Local(reference) => {
            let mut at = reference;
            while let Some(origin) = at.origin() {
                at = origin;
            }
            crate::surface::Name::Local(at.clone())
        }
        other => other.clone(),
    }
}
