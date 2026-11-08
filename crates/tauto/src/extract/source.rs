//! Source names allocated from references. This is an output boundary: the
//! executable tree keeps its identities and is never replaced by this copy.

use super::*;
use crate::surface::{references, walk};

struct Names {
    written: HashMap<Name, String>,
    occupied: HashSet<String>,
    library: HashMap<Name, String>,
    error: Option<Message>,
}

impl Names {
    fn new() -> Self {
        let bindings = crate::bindings::library_bindings();
        let mut aliases: Vec<_> = bindings.bindings().collect();
        aliases.sort_by_key(|(text, reference)| {
            (
                bindings.is_constructor(&Name::Global((*reference).clone()))
                    && !text.contains("::"),
                text.len(),
                *text,
            )
        });
        let mut library = HashMap::new();
        let mut occupied = HashSet::new();
        for (text, reference) in aliases {
            library
                .entry(Name::Global(reference.clone()))
                .or_insert_with(|| text.to_string());
            occupied.insert(text.to_string());
            occupied.extend(text.split("::").map(str::to_string));
        }
        Self {
            written: HashMap::new(),
            occupied,
            library,
            error: None,
        }
    }

    fn allocate(&mut self, name: &Name) -> String {
        if let Some(written) = self.written.get(name) {
            return written.clone();
        }
        let base: String = name
            .chars()
            .map(|c| {
                if c.is_alphanumeric() || c == '_' || (name.as_global().is_some() && c == ':') {
                    c
                } else {
                    '_'
                }
            })
            .collect();
        let base = if base.is_empty() || base.starts_with(|c: char| c.is_ascii_digit()) {
            format!("id_{base}")
        } else {
            base
        };
        let written = (0..)
            .map(|i| {
                if i == 0 {
                    base.clone()
                } else {
                    format!("{base}_{i}")
                }
            })
            .find(|candidate| {
                let leaf = candidate.rsplit("::").next().unwrap();
                !self.occupied.contains(candidate) && !self.occupied.contains(leaf)
            })
            .unwrap();
        self.occupied.insert(written.clone());
        if name.as_global().is_some() {
            self.occupied
                .extend(written.split("::").map(str::to_string));
        }
        self.written.insert(name.clone(), written.clone());
        written
    }

    fn name(&mut self, name: &mut Name) {
        if let Name::Local(reference) = name {
            let reference = reference.clone();
            let written = self.allocate(name);
            *name = Name::Local(reference.with_display(written));
            return;
        }
        if let Some(written) = self.written.get(name).or_else(|| self.library.get(name)) {
            *name = written.clone().into();
            return;
        }
        let written = match name {
            Name::Local(_) => unreachable!("local references are displayed above"),
            Name::Global(reference) if reference.sort().is_some() => reference.to_string(),
            Name::Global(_) => {
                self.error.get_or_insert_with(|| {
                    msg!(
                        "tauto-extract-unavailable-declaration",
                        name = name.to_string()
                    )
                });
                return;
            }
            Name::Selection(selection) => {
                let mut names = Vec::new();
                for candidate in selection.candidates() {
                    let mut candidate = Name::Global(candidate.clone());
                    self.name(&mut candidate);
                    names.push(candidate.to_string());
                }
                if let [only] = names.as_slice() {
                    only.clone()
                } else {
                    self.error.get_or_insert_with(|| {
                        msg!(
                            "tauto-extract-candidates-not-selected",
                            name = name.to_string()
                        )
                    });
                    return;
                }
            }
            Name::Effect(effect) => {
                let mut operation = Name::Global(effect.effect().clone());
                self.name(&mut operation);
                let mut arguments = effect.arguments().to_vec();
                for argument in &mut arguments {
                    references::term(argument, &mut |name| self.name(name));
                }
                let arguments: Vec<_> = arguments
                    .iter()
                    .map(crate::surface::print::print_term)
                    .collect();
                let application = format!("{operation}({})", arguments.join(", "));
                if effect.is_universal() {
                    let parameters: Vec<_> = effect
                        .parameters()
                        .iter()
                        .map(|p| {
                            let mut name = Name::Local(p.clone());
                            self.name(&mut name);
                            name.to_string()
                        })
                        .collect();
                    format!("\u{2200}{}. {application}", parameters.join(", "))
                } else {
                    application
                }
            }
            Name::Spelled(_) => return,
        };
        *name = written.into();
    }
}

pub(super) fn write(statements: &[Stmt]) -> Result<String, Message> {
    let program = crate::surface::Program {
        stmts: statements.to_vec(),
        errors: Vec::new(),
    };
    let expanded = crate::types::expand_classes(program, crate::macros::EXPANSION_BASE);
    let report = crate::types::check_program(&expanded);
    if let Some(error) = report.errors.first() {
        return Err(msg!(
            "tauto-extract-ill-typed-program",
            why = error.message.to_string()
        ));
    }
    let mut names = Names::new();
    // Constructors are emitted under their owner. Their labels stay shared
    // when a source occurrence selects among several owners by type.
    let mut constructors = HashSet::new();
    for statement in statements {
        if let Stmt::Struct(data) | Stmt::Enum(data) = statement {
            constructors.extend(data.constructors.iter().map(|ctor| ctor.name.clone()));
        }
    }
    for name in crate::bindings::declared_names(statements) {
        if !constructors.contains(name) {
            names.allocate(name);
        }
    }
    for statement in statements {
        if let Stmt::Struct(data) | Stmt::Enum(data) = statement {
            let owner = names.allocate(&data.name);
            for constructor in &data.constructors {
                let leaf = constructor.name.rsplit("::").next().unwrap();
                names
                    .written
                    .insert(constructor.name.clone(), format!("{owner}::{leaf}"));
            }
        }
    }
    for statement in statements {
        if let Stmt::Class(class) = statement {
            let owner = names.allocate(&class.name);
            if let Some(reference) = class.name.as_global() {
                for (index, method) in class.methods.iter().enumerate() {
                    let member = reference.class_member(index, false, method.name.as_str());
                    names
                        .written
                        .insert(member.into(), format!("{owner}::{}", method.name));
                }
            }
        }
    }
    let mut written = statements.to_vec();
    for statement in &mut written {
        let occupied = names.occupied.clone();
        walk::stmt(statement, &mut |term| {
            if let Err(error) = report.resolve_selection_at(term) {
                names.error.get_or_insert(error.into());
            }
            if matches!(&*term.kind, TermKind::Declaration(_)) {
                names
                    .error
                    .get_or_insert_with(|| msg!("tauto-extract-opaque-value-no-literal"));
            }
        });
        references::statement(statement, &mut |name| names.name(name));
        if !matches!(statement, Stmt::Let { .. } | Stmt::Var { .. }) {
            names.occupied = occupied;
        }
    }
    if let Some(error) = names.error {
        return Err(error);
    }
    Ok(crate::surface::print::print_stmts(&written))
}
