//! Presentation rules over recorded judgments. Every claim still points to
//! that judgment; bounded core queries only choose how to explain it.
use super::bindings;
fn show(t: &T) -> String {
    crate::surface::print::print_term(&crate::check::Kernel::eqs_written(t))
}
use crate::check::{Derivation, InferenceRule as Rule, LibEntry, ProofInspector};
use crate::surface::{SurfaceTerm as T, TermKind};
use std::{
    collections::{HashMap, HashSet},
    fmt::Write,
};
use tauto_message::msg;

struct Text {
    reference: String,
    number: Option<usize>,
    dependencies: Vec<usize>,
}
impl Text {
    fn inline(reference: String) -> Self {
        Self {
            reference,
            number: None,
            dependencies: Vec::new(),
        }
    }
    fn result(n: usize, labels: Option<&HashMap<usize, usize>>) -> Self {
        let label = labels
            .and_then(|labels| labels.get(&n))
            .copied()
            .unwrap_or(n);
        Self {
            reference: format!("[{label}]"),
            number: Some(n),
            dependencies: vec![n],
        }
    }
    fn used(&self, referenced: &mut HashSet<usize>) -> String {
        referenced.extend(&self.dependencies);
        self.reference.clone()
    }
    fn application(function: &Self, supplied: &[Self]) -> Self {
        Self {
            reference: format!(
                "{}({})",
                function.reference,
                supplied
                    .iter()
                    .map(|t| t.reference.as_str())
                    .collect::<Vec<_>>()
                    .join(", ")
            ),
            number: None,
            dependencies: function
                .dependencies
                .iter()
                .chain(supplied.iter().flat_map(|t| &t.dependencies))
                .copied()
                .collect(),
        }
    }
}

pub(super) fn render(
    root: &Derivation,
    library: &[LibEntry],
    inspector: &mut ProofInspector,
    notation: &super::notation::Notation,
    out: &mut String,
) {
    // Plan labels from actual uses, including references inside inline calls.
    // Displayed DSL text is never searched for strings resembling a label.
    let mut scratch = String::new();
    let mut plan = Writer::new(library, inspector, notation, &mut scratch, None);
    plan.emit(root, 0, true);
    let mut referenced: Vec<_> = plan.referenced.into_iter().collect();
    referenced.sort_unstable();
    let labels: HashMap<_, _> = referenced
        .into_iter()
        .enumerate()
        .map(|(i, n)| (n, i + 1))
        .collect();
    let mut writer = Writer::new(library, inspector, notation, out, Some(&labels));
    if !root.context.is_empty() {
        writeln!(
            writer.out,
            "{}",
            msg!(
                "proof-natural-context",
                assumptions = bindings(
                    &root
                        .context
                        .iter()
                        .enumerate()
                        .map(|(i, (n, t))| (n.clone(), notation.show(t, &root.context[..i], true)))
                        .collect::<Vec<_>>()
                )
            )
        )
        .unwrap();
    }
    let role = writer.inspector.is_proof(root);
    let goal = if role == Some(true) {
        msg!(
            "proof-natural-goal",
            goal = notation.show(&root.ty, &root.context, true)
        )
    } else {
        msg!(
            "proof-natural-goal-typed",
            goal = claim(root, role, notation)
        )
    };
    writeln!(writer.out, "{goal}\n").unwrap();
    writer.emit(root, 0, true);
}

struct Writer<'a> {
    notation: &'a super::notation::Notation,
    library: &'a [LibEntry],
    inspector: &'a mut ProofInspector,
    out: &'a mut String,
    next: usize,
    scope: usize,
    next_scope: usize,
    known: HashMap<(usize, String), usize>,
    labels: Option<&'a HashMap<usize, usize>>,
    referenced: HashSet<usize>,
}

impl<'a> Writer<'a> {
    fn new(
        library: &'a [LibEntry],
        inspector: &'a mut ProofInspector,
        notation: &'a super::notation::Notation,
        out: &'a mut String,
        labels: Option<&'a HashMap<usize, usize>>,
    ) -> Self {
        Self {
            library,
            inspector,
            notation,
            out,
            labels,
            next: 0,
            scope: 0,
            next_scope: 0,
            known: HashMap::new(),
            referenced: HashSet::new(),
        }
    }
    fn emit(&mut self, d: &Derivation, depth: usize, force: bool) -> Text {
        let key = format!(
            "{}\n{}\n{}",
            bindings(
                &d.context
                    .iter()
                    .map(|(n, t)| (n.clone(), show(t)))
                    .collect::<Vec<_>>()
            ),
            show(&d.term),
            show(&d.ty)
        );
        if let Some(n) = self.known.get(&(self.scope, key.clone())) {
            return Text::result(*n, self.labels);
        }
        let indent = "  ".repeat(depth);
        let is_proof = self.inspector.is_proof(d);
        if !force && is_proof == Some(false) && d.rule == Rule::Introduction && self.inline_value(d)
        {
            return Text::inline(self.notation.show(&d.term, &d.context, true));
        }
        let mut args = Vec::new();
        let mut head = d;
        if d.rule == Rule::Application {
            while head.rule == Rule::Application
                && head.premises.len() == 2
                && same_context(d, &head.premises[0])
            {
                args.push(&head.premises[1]);
                head = &head.premises[0];
            }
            args.reverse();
        }
        if d.rule == Rule::Introduction {
            let local = bindings(
                &d.introduced
                    .iter()
                    .map(|(n, t)| (n.clone(), self.notation.show(t, &d.context, true)))
                    .collect::<Vec<_>>(),
            );
            writeln!(
                self.out,
                "{indent}{}",
                msg!("proof-suppose", assumptions = local)
            )
            .unwrap();
            let before = self.scope;
            self.next_scope += 1;
            self.scope = self.next_scope;
            let premises: Vec<_> = d
                .premises
                .iter()
                .map(|p| self.emit(p, depth + 1, true))
                .collect();
            self.scope = before;
            let from = references(&premises, &mut self.referenced);
            let sentence = if d.is_complete() {
                msg!(
                    "proof-natural-introduction",
                    premises = from,
                    names = d
                        .introduced
                        .iter()
                        .map(|(n, _)| n.as_str())
                        .collect::<Vec<_>>()
                        .join(", "),
                    goal = claim(d, is_proof, self.notation)
                )
                .to_string()
            } else {
                msg!(
                    "proof-natural-pending",
                    premises = from,
                    goal = self.notation.show(&d.ty, &d.context, true)
                )
                .to_string()
            };
            return self.step(key, &indent, sentence, None);
        }
        if d.rule == Rule::Application && !args.is_empty() {
            let function = self.emit(head, depth, false);
            let supplied: Vec<_> = args.iter().map(|p| self.emit(p, depth, false)).collect();
            let call = Text::application(&function, &supplied);
            if is_proof == Some(false) && d.is_complete() && !force {
                return if call.dependencies.is_empty() {
                    Text::inline(self.notation.show(&d.term, &d.context, true))
                } else {
                    call
                };
            }
            let equation = congruence(d, head, &args);
            let sentence = if !d.is_complete() {
                msg!(
                    "proof-natural-pending",
                    premises = call.used(&mut self.referenced),
                    goal = claim(d, is_proof, self.notation)
                )
                .to_string()
            } else if equation.is_some() {
                msg!(
                    "proof-natural-congruence",
                    hypothesis = supplied[5].used(&mut self.referenced),
                    function = supplied[4].used(&mut self.referenced),
                    lemma = self.notation.show(&head.term, &head.context, true),
                    goal = claim(d, is_proof, self.notation)
                )
                .to_string()
            } else if reflexivity(d, head, &args) {
                msg!(
                    "proof-natural-reflexivity",
                    goal = self.notation.show(&d.ty, &d.context, true)
                )
                .to_string()
            } else {
                msg!(
                    "proof-natural-application",
                    call = call.used(&mut self.referenced),
                    goal = claim(d, is_proof, self.notation)
                )
                .to_string()
            };
            return self.step(key, &indent, sentence, None);
        }
        if d.rule == Rule::Conversion && d.premises.len() == 1 {
            let previous = &d.premises[0];
            let evidence = self.emit(previous, depth, true);
            let from = evidence.used(&mut self.referenced);
            let (reason, calculations, forward) = self.calculation(previous, d);
            let sentence = if !d.is_complete() {
                msg!(
                    "proof-natural-pending",
                    premises = from,
                    goal = self.notation.show(&d.ty, &d.context, true)
                )
                .to_string()
            } else if let Some(reason) = reason {
                msg!(
                    if forward {
                        "proof-natural-calculation"
                    } else {
                        "proof-natural-reverse-calculation"
                    },
                    premises = from,
                    reason = reason,
                    goal = claim(d, is_proof, self.notation)
                )
                .to_string()
            } else {
                let reason =
                    match self
                        .inspector
                        .definitionally_equal(&d.context, &previous.ty, &d.ty)
                    {
                        Some(true) => msg!("proof-natural-definitional").to_string(),
                        Some(false) => msg!("proof-natural-cumulative").to_string(),
                        None => msg!("proof-natural-recorded-conversion").to_string(),
                    };
                msg!(
                    "proof-natural-conversion",
                    premises = from,
                    reason = reason,
                    goal = claim(d, is_proof, self.notation)
                )
                .to_string()
            };
            return self.step(key, &indent, sentence, Some(&calculations));
        }
        // Lookup judgments are references at their use sites, not additional
        // mathematical steps. Open leaves must always remain visible.
        if !force
            && d.is_complete()
            && matches!(
                d.rule,
                Rule::Assumption | Rule::Constant | Rule::Literal | Rule::Sort
            )
        {
            return Text::inline(self.notation.show(&d.term, &d.context, true));
        }
        let premises: Vec<_> = d
            .premises
            .iter()
            .map(|p| self.emit(p, depth, false))
            .collect();
        if !force && d.is_complete() && is_proof == Some(false) && matches!(d.rule, Rule::Formation)
        {
            return Text::inline(self.notation.show(&d.term, &d.context, true));
        }
        let evidence = references(&premises, &mut self.referenced);
        let id = match d.rule {
            Rule::Assumption => "proof-natural-assumption",
            Rule::Constant => "proof-natural-declaration",
            Rule::Hole => "proof-natural-hole",
            Rule::UnverifiedReference => "proof-natural-unverified",
            _ if !d.is_complete() => "proof-natural-pending",
            _ if evidence.is_empty() => "proof-natural-rule",
            _ => "proof-natural-judgment",
        };
        let sentence = tauto_message::Message::new(id)
            .arg("term", self.notation.show(&d.term, &d.context, true))
            .arg("goal", claim(d, is_proof, self.notation))
            .arg("premises", evidence)
            .arg("rule", super::rule_name(d))
            .to_string();
        self.step(key, &indent, sentence, None)
    }

    fn inline_value(&mut self, d: &Derivation) -> bool {
        if !d.is_complete() {
            return false;
        }
        if matches!(
            d.rule,
            Rule::Assumption | Rule::Constant | Rule::Literal | Rule::Sort
        ) {
            return true;
        }
        matches!(
            d.rule,
            Rule::Introduction | Rule::Application | Rule::Formation
        ) && self.inspector.is_proof(d) == Some(false)
            && d.premises.iter().all(|p| self.inline_value(p))
    }

    fn step(
        &mut self,
        key: String,
        indent: &str,
        sentence: String,
        calculations: Option<&[String]>,
    ) -> Text {
        self.next += 1;
        let n = self.next;
        if let Some(label) = self.labels.map_or(Some(&n), |labels| labels.get(&n)) {
            writeln!(self.out, "{indent}[{label}] {sentence}").unwrap();
        } else {
            writeln!(self.out, "{indent}{sentence}").unwrap();
        }
        if let Some(lines) = calculations {
            for line in lines {
                writeln!(self.out, "{indent}    {line}").unwrap();
            }
        }
        self.out.push('\n');
        self.known.insert((self.scope, key), n);
        Text::result(n, self.labels)
    }

    fn calculation(
        &mut self,
        before: &Derivation,
        after: &Derivation,
    ) -> (Option<String>, Vec<String>, bool) {
        let mut pairs = Vec::new();
        if let (Some(a), Some(b)) = (equality(&before.ty), equality(&after.ty)) {
            if show(&a[0]) == show(&b[0]) {
                pairs.push((&a[1], &b[1]));
                pairs.push((&a[2], &b[2]));
            }
        }
        if pairs.is_empty() {
            pairs.push((&before.ty, &after.ty));
        }
        let mut calculations = Vec::new();
        let mut definitions = Vec::new();
        let mut forward = true;
        for (a, b) in pairs {
            if show(a) == show(b) {
                continue;
            }
            let Some(left) = self.inspector.reduce(&after.context, a) else {
                return (None, Vec::new(), false);
            };
            let Some(right) = self.inspector.reduce(&after.context, b) else {
                return (None, Vec::new(), false);
            };
            if show(&left.normal) != show(&right.normal) {
                return (None, Vec::new(), false);
            }
            let normal = show(&left.normal);
            if show(a) != normal {
                calculations.push(format!(
                    "{} → {}",
                    self.notation.show(a, &after.context, true),
                    self.notation.show(&left.normal, &after.context, true)
                ));
            }
            if show(b) != normal {
                forward = false;
                let line = format!(
                    "{} → {}",
                    self.notation.show(b, &after.context, true),
                    self.notation.show(&right.normal, &after.context, true)
                );
                if !calculations.contains(&line) {
                    calculations.push(line);
                }
            }
            for n in left.unfolded.into_iter().chain(right.unfolded) {
                if self.library.iter().any(|g| g.name == n && g.kind == "def")
                    && !definitions.contains(&n)
                {
                    definitions.push(n);
                }
            }
        }
        if calculations.is_empty() {
            return (None, Vec::new(), false);
        }
        let reason = if definitions.is_empty() {
            msg!("proof-natural-computation").to_string()
        } else {
            msg!("proof-natural-definitions", names = definitions.join(", ")).to_string()
        };
        (Some(reason), calculations, forward)
    }
}

fn references(items: &[Text], referenced: &mut HashSet<usize>) -> String {
    items
        .iter()
        .filter(|t| t.number.is_some())
        .map(|t| t.used(referenced))
        .collect::<Vec<_>>()
        .join(", ")
}
fn same_context(a: &Derivation, b: &Derivation) -> bool {
    a.context
        .iter()
        .map(|(n, t)| (n, show(t)))
        .eq(b.context.iter().map(|(n, t)| (n, show(t))))
}
fn equality(t: &T) -> Option<&[T]> {
    match &*t.kind {
        TermKind::App {
            function,
            arguments,
        } if matches!(&*function.kind,TermKind::Var(n) if n=="Eq") && arguments.len() == 3 => {
            Some(arguments)
        }
        _ => None,
    }
}
fn congruence(d: &Derivation, head: &Derivation, args: &[&Derivation]) -> Option<(String, String)> {
    if !matches!(&*head.term.kind,TermKind::Var(n) if n=="Eq::congr") || args.len() != 6 {
        return None;
    }
    let premise = equality(&args[5].ty)?;
    let result = equality(&d.ty)?;
    if show(&premise[0]) != show(&args[0].term)
        || show(&premise[1]) != show(&args[2].term)
        || show(&premise[2]) != show(&args[3].term)
        || show(&result[0]) != show(&args[1].term)
    {
        return None;
    }
    for (side, arg) in result[1..].iter().zip([args[2], args[3]]) {
        match &*side.kind {
            TermKind::App {
                function,
                arguments,
            } if show(function) == show(&args[4].term)
                && arguments.len() == 1
                && show(&arguments[0]) == show(&arg.term) => {}
            _ => return None,
        }
    }
    Some((show(&args[4].term), show(&args[5].term)))
}
fn reflexivity(d: &Derivation, head: &Derivation, args: &[&Derivation]) -> bool {
    matches!(&*head.term.kind,TermKind::Var(n) if n=="Refl")
        && args.len() == 2
        && equality(&d.ty).is_some_and(|e| {
            show(&e[0]) == show(&args[0].term)
                && show(&e[1]) == show(&args[1].term)
                && show(&e[1]) == show(&e[2])
        })
}
fn claim(d: &Derivation, is_proof: Option<bool>, notation: &super::notation::Notation) -> String {
    if is_proof == Some(true) {
        notation.show(&d.ty, &d.context, true)
    } else {
        format!(
            "{} : {}",
            notation.show(&d.term, &d.context, true),
            notation.show(&d.ty, &d.context, true)
        )
    }
}

/// Full mode follows every recorded inference, including lookups and each
/// individual application. It neither shares nor abbreviates proof steps.
pub(super) fn render_full(root: &Derivation, scopes: &super::Scopes, out: &mut String) {
    scopes.text(out);
    fn visit(d: &Derivation, scopes: &super::Scopes, next: &mut usize, out: &mut String) -> usize {
        let premises = d
            .premises
            .iter()
            .map(|p| format!("[{}]", visit(p, scopes, next, out)))
            .collect::<Vec<_>>()
            .join(", ");
        *next += 1;
        let id = if !d.is_complete() && premises.is_empty() {
            "proof-full-open-leaf"
        } else if !d.is_complete() {
            "proof-full-open"
        } else if premises.is_empty() {
            "proof-full-leaf"
        } else {
            "proof-full-step"
        };
        let sentence = tauto_message::Message::new(id)
            .arg("premises", premises)
            .arg("rule", super::rule_name(d))
            .arg("claim", super::judgment(d, scopes))
            .to_string();
        writeln!(out, "[{}] {}", next, sentence).unwrap();
        *next
    }
    visit(root, scopes, &mut 0, out);
}
