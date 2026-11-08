//! Source aliases and constructor candidates for one binding environment.
//! Reserving an identity does not admit a declaration to the kernel.
use crate::identity::{DeclRef, Declarations, Generation, Name, Selection, SortSymbol};
use crate::surface::SurfaceTerm;
use std::collections::{HashMap, HashSet};

#[derive(Clone, Default)]
pub struct Bindings {
    identities: Declarations,
    owned: HashMap<String, DeclRef>,
    library_definitions: bool,
    names: HashMap<String, DeclRef>,
    constructors: HashSet<DeclRef>,
    selections: HashMap<String, Vec<DeclRef>>,
    types: HashSet<DeclRef>,
    effects: HashMap<String, DeclRef>,
    owned_effects: HashMap<String, DeclRef>,
}

/// What one spelling means in a [`Bindings`], kept to put back later
/// ([`Bindings::spelling_state`]).
#[derive(Clone)]
pub struct SpellingState {
    owned: Option<DeclRef>,
    names: Option<DeclRef>,
    selections: Option<Vec<DeclRef>>,
    effects: Option<DeclRef>,
    owned_effects: Option<DeclRef>,
}

impl Bindings {
    /// What `spelling` means now, to be put back by [`Self::restore_spelling`].
    pub fn spelling_state(&self, spelling: &str) -> SpellingState {
        SpellingState {
            owned: self.owned.get(spelling).cloned(),
            names: self.names.get(spelling).cloned(),
            selections: self.selections.get(spelling).cloned(),
            effects: self.effects.get(spelling).cloned(),
            owned_effects: self.owned_effects.get(spelling).cloned(),
        }
    }

    /// Makes `spelling` mean again what it meant when `state` was taken.
    pub fn restore_spelling(&mut self, spelling: &str, state: SpellingState) {
        fn put<V>(map: &mut HashMap<String, V>, spelling: &str, value: Option<V>) {
            match value {
                Some(v) => {
                    map.insert(spelling.into(), v);
                }
                None => {
                    map.remove(spelling);
                }
            }
        }
        put(&mut self.owned, spelling, state.owned);
        put(&mut self.names, spelling, state.names);
        put(&mut self.selections, spelling, state.selections);
        put(&mut self.effects, spelling, state.effects);
        put(&mut self.owned_effects, spelling, state.owned_effects);
    }

    /// Reuses source declaration identities across edits, with visibility rebuilt
    /// from the declarations and imports of the new revision.
    pub fn next_revision(&self) -> Self {
        Self {
            identities: self.identities.clone(),
            owned: self.owned.clone(),
            owned_effects: self.owned_effects.clone(),
            ..library_bindings()
        }
    }

    /// A source spelling for an already selected declaration. This does not
    /// declare or certify the target, and never rewrites an existing reference.
    pub fn source_alias(&mut self, spelling: impl Into<String>, reference: DeclRef) {
        let spelling = spelling.into();
        if self.constructors.contains(&reference) {
            self.selections
                .insert(spelling.clone(), vec![reference.clone()]);
        }
        if self.effects.values().any(|effect| effect == &reference) {
            self.effects.insert(spelling.clone(), reference.clone());
        }
        self.names.insert(spelling, reference);
    }

    /// A quotation can introduce declarations that shadow its definition
    /// environment. Such declarations belong to the expansion, not this table.
    pub(crate) fn quotation_environment(&self) -> Self {
        Self {
            names: self.names.clone(),
            constructors: self.constructors.clone(),
            selections: self.selections.clone(),
            types: self.types.clone(),
            effects: self.effects.clone(),
            ..Self::default()
        }
    }

    pub fn get(&self, spelling: &str) -> Option<&DeclRef> {
        self.names
            .get(spelling)
            .or_else(|| library_by_full_name(spelling))
    }

    pub fn reserve_source_effect(&mut self, spelling: &str, full: &str) {
        let reference = self
            .owned_effects
            .entry(full.into())
            .or_insert_with(|| DeclRef::fresh(full))
            .clone();
        self.owned_effects
            .insert(spelling.into(), reference.clone());
        self.effects.insert(spelling.into(), reference.clone());
        self.effects.insert(full.into(), reference);
    }

    pub fn declare_effect(&mut self, name: &Name) -> DeclRef {
        let reference = match name {
            Name::Global(reference) => reference.clone(),
            Name::Spelled(spelling) => {
                self.owned_effects
                    .get(spelling)
                    .cloned()
                    .unwrap_or_else(|| {
                        if self.library_definitions {
                            if let Some(reference) = self.effects.get(spelling) {
                                return reference.clone();
                            }
                        }
                        DeclRef::fresh(spelling)
                    })
            }
            _ => panic!("an effect declaration requires a global reference"),
        };
        self.owned_effects
            .insert(name.to_string(), reference.clone());
        self.effects.insert(name.to_string(), reference.clone());
        self.names
            .entry(name.to_string())
            .or_insert_with(|| reference.clone());
        reference
    }

    pub fn effect(&self, spelling: &str) -> Option<&DeclRef> {
        self.effects.get(spelling)
    }

    pub fn declare_type(&mut self, name: &Name) {
        let reference = self.declare(name);
        self.types.insert(reference);
    }

    /// Reserves a source declaration under the full name assigned by its file.
    pub fn reserve_source_declaration(&mut self, spelling: &str, full: &str) {
        let reference = self.identities.reserve(full);
        self.owned.insert(spelling.into(), reference.clone());
        self.owned.insert(full.into(), reference.clone());
        self.names.insert(spelling.into(), reference.clone());
        self.names.insert(full.into(), reference);
    }

    /// A type and a visible value constructor may share a source spelling.
    /// Both references are captured here; the type checker chooses from them.
    pub fn type_constructor_selection(&self, spelling: &str) -> Option<Name> {
        let family = self.get(spelling).filter(|r| self.types.contains(*r))?;
        let constructors = self.selections.get(spelling)?;
        if !constructors
            .iter()
            .any(|c| c.display().rsplit("::").next() == spelling.rsplit("::").next())
        {
            return None;
        }
        Some(
            Selection::new(
                spelling,
                std::iter::once(family.clone())
                    .chain(constructors.iter().cloned())
                    .collect(),
            )
            .into(),
        )
    }
    pub fn bindings(&self) -> impl Iterator<Item = (&str, &DeclRef)> {
        self.names
            .iter()
            .chain(self.effects.iter())
            .map(|(name, reference)| (name.as_str(), reference))
    }
    pub fn reserve(&mut self, spelling: &str) -> DeclRef {
        self.get(spelling).cloned().unwrap_or_else(|| {
            DeclRef::primitive(spelling)
                .or_else(|| SortSymbol::parse(spelling).map(DeclRef::of_sort))
                .or_else(|| state_reference(spelling))
                .unwrap_or_else(|| self.identities.reserve(spelling))
        })
    }
    pub fn register(&mut self, name: &Name) -> DeclRef {
        match name {
            Name::Global(reference) => reference.clone(),
            Name::Spelled(spelling) => self.reserve(spelling),
            _ => panic!("a declaration must have a global identity"),
        }
    }
    pub fn declare(&mut self, name: &Name) -> DeclRef {
        let reference = match name {
            Name::Spelled(spelling) => self.owned.get(spelling).cloned().unwrap_or_else(|| {
                let reference = if self.library_definitions {
                    self.names
                        .get(spelling)
                        .cloned()
                        .unwrap_or_else(|| self.identities.reserve(spelling))
                } else {
                    self.identities.reserve(spelling)
                };
                self.owned.insert(spelling.clone(), reference.clone());
                reference
            }),
            Name::Global(reference) => {
                self.owned.insert(name.to_string(), reference.clone());
                reference.clone()
            }
            _ => self.register(name),
        };
        self.names.insert(name.to_string(), reference.clone());
        reference
    }
    pub fn generated(&mut self, owner: &Name, kind: Generation) -> DeclRef {
        let owner = self.register(owner);
        let reference = owner.generated(kind);
        self.owned
            .insert(reference.display().into(), reference.clone());
        if self.names.get(owner.display()) == Some(&owner) {
            self.names
                .insert(reference.display().into(), reference.clone());
        }
        reference
    }
    pub fn class_member(&mut self, class: &Name, label: &Name, index: usize, law: bool) -> Name {
        let owner = self.register(class);
        let reference = owner.class_member(index, law, label.as_str());
        self.owned
            .insert(reference.display().into(), reference.clone());
        self.names
            .insert(reference.display().into(), reference.clone());
        reference.into()
    }

    pub fn owned_constructor(&mut self, family: &Name, name: &Name, index: usize) -> Name {
        if !matches!(name, Name::Spelled(_)) {
            return name.clone();
        }
        // A quotation splice supplies the identifier when it is expanded;
        // it is not a declaration belonging to the quotation's family.
        if name.starts_with('$') {
            return name.clone();
        }
        let owner = self.register(family);
        if DeclRef::primitive(owner.display()).as_ref() == Some(&owner) {
            if let Some(reference) =
                DeclRef::primitive(name.as_str()).filter(|r| self.constructors.contains(r))
            {
                return reference.into();
            }
        }
        owner
            .constructor(index, name.rsplit("::").next().unwrap())
            .into()
    }
    pub fn constructor_in(&mut self, family: &Name, name: &Name) {
        let reference = self.register(name);
        self.constructors.insert(reference.clone());
        let owner = self.register(family);
        if self.names.get(owner.display()) == Some(&owner) {
            let leaf = name.rsplit("::").next().unwrap();
            self.names
                .insert(format!("{family}::{leaf}"), reference.clone());
            let choices = self.selections.entry(leaf.into()).or_default();
            if let Some(existing) = self.names.get(leaf)
                && self.constructors.contains(existing)
                && !choices.contains(existing)
            {
                choices.push(existing.clone());
            }
            if !choices.contains(&reference) {
                choices.push(reference);
            }
        }
    }
    pub fn constructor_alias(&mut self, spelling: &str, name: &Name) {
        let reference = self.register(name);
        let choices = self.selections.entry(spelling.into()).or_default();
        if let Some(existing) = self.names.get(spelling) {
            if self.constructors.contains(existing) && !choices.contains(existing) {
                choices.push(existing.clone());
            }
        }
        if !choices.contains(&reference) {
            choices.push(reference);
        }
    }
    pub(crate) fn restrict_constructor_owners(
        &mut self,
        owners: &HashSet<DeclRef>,
    ) -> (HashMap<String, DeclRef>, HashMap<String, Vec<DeclRef>>) {
        let original = (self.names.clone(), self.selections.clone());
        self.names.retain(|_, reference| {
            !self.constructors.contains(reference)
                || reference.display().starts_with(crate::records::PREFIX)
                || owners.contains(reference)
                || reference
                    .owner()
                    .is_some_and(|owner| owners.contains(owner))
        });
        self.selections.retain(|_, candidates| {
            candidates.retain(|candidate| {
                candidate.display().starts_with(crate::records::PREFIX)
                    || owners.contains(candidate)
                    || candidate
                        .owner()
                        .is_some_and(|owner| owners.contains(owner))
            });
            !candidates.is_empty()
        });
        original
    }

    pub(crate) fn restore_constructor_candidates(
        &mut self,
        candidates: (HashMap<String, DeclRef>, HashMap<String, Vec<DeclRef>>),
    ) {
        (self.names, self.selections) = candidates;
    }

    /// Whether `reference`, the library's declaration of `spelling` that
    /// this source does not declare itself, is hidden by a constructor the
    /// source declares with that spelling. The library keeps some names
    /// with no source declaration (`Info`, `Char`, `Div`); a file's own
    /// constructor of such a name is what the file means by it, as it is
    /// for any other name the library declares (`List`).
    pub fn source_constructor_hides(&self, spelling: &str, reference: &DeclRef) -> bool {
        let library = prelude_declarations();
        !self.owned.contains_key(spelling)
            && library.names.get(spelling) == Some(reference)
            && self.selections.get(spelling).is_some_and(|choices| {
                choices
                    .iter()
                    .any(|choice| !library.constructors.contains(choice))
            })
    }

    pub fn selection(&self, spelling: &str) -> Option<Name> {
        let choices = self.selections.get(spelling)?;
        match choices.as_slice() {
            [] => None,
            [reference] => Some(reference.clone().into()),
            _ => Some(Selection::new(spelling, choices.clone()).into()),
        }
    }
    pub fn is_constructor(&self, name: &Name) -> bool {
        match name {
            Name::Global(reference) => self.constructors.contains(reference),
            Name::Selection(selection) => selection
                .candidates()
                .iter()
                .any(|r| self.constructors.contains(r)),
            Name::Spelled(text) => {
                self.get(text)
                    .is_some_and(|r| self.constructors.contains(r))
                    || self
                        .selections
                        .get(text)
                        .is_some_and(|choices| !choices.is_empty())
            }
            _ => false,
        }
    }
}

/// A structural key containing identities rather than their display names.
/// It is local to the binding session, not a serialized declaration handle.
pub fn argument_key(arguments: &[SurfaceTerm]) -> String {
    let mut parts = arguments.to_vec();
    for part in &mut parts {
        crate::surface::walk::term(part, &mut |term| term.span = tauto_parol::Span::new(0, 0));
        crate::surface::references::term(part, &mut |name| {
            *name = Name::Spelled(match name {
                Name::Global(reference) => format!("global:{:?}", reference.id()),
                Name::Local(reference) => format!("local:{:?}", reference.id()),
                Name::Selection(selection) => format!(
                    "selection:{:?}:{:?}",
                    selection.binding().map(|binding| binding.id()),
                    selection
                        .candidates()
                        .iter()
                        .map(DeclRef::id)
                        .collect::<Vec<_>>()
                ),
                Name::Effect(use_) => {
                    format!(
                        "effect:{:?}:{:?}:{}:{}",
                        use_.effect().id(),
                        use_.parameters()
                            .iter()
                            .map(|parameter| parameter.id())
                            .collect::<Vec<_>>(),
                        use_.is_universal(),
                        use_.argument_key()
                    )
                }
                Name::Spelled(text) => format!("source:{text}"),
            });
        });
    }
    format!("{parts:?}")
}

struct PreludeDeclarations {
    types: HashSet<DeclRef>,
    selections: HashMap<String, Vec<DeclRef>>,
    effects: HashMap<String, DeclRef>,
    names: HashMap<String, DeclRef>,
    constructors: HashSet<DeclRef>,
    /// The functions of the prelude's `module Host`, which wraps the host's
    /// externs with the permission check and the waiting.
    host_module_fns: HashSet<DeclRef>,
    /// Each prelude declaration by the full name a file writes to mean it
    /// whatever else it declares (`std::prelude::Text`).
    qualified: HashMap<String, DeclRef>,
}

/// The prelude declaration a full name (`std::prelude::Text`) writes.
pub fn library_by_full_name(full: &str) -> Option<&'static DeclRef> {
    prelude_declarations().qualified.get(full)
}

/// Whether `name` is a function of the prelude's `module Host`.
pub fn is_host_module_fn(name: &Name) -> bool {
    name.as_global()
        .is_some_and(|reference| prelude_declarations().host_module_fns.contains(reference))
}

/// The library's `Tuple`, the head of every product the syntax writes (`#()`, `#(a, b)`).
/// It is made on its own, not by reading the prelude, so the parser can write it while the
/// prelude is being read.
pub fn tuple_reference() -> &'static DeclRef {
    static TUPLE: std::sync::OnceLock<DeclRef> = std::sync::OnceLock::new();
    TUPLE.get_or_init(|| DeclRef::fresh("Tuple"))
}

fn prelude_declarations() -> &'static PreludeDeclarations {
    static PRELUDE: std::sync::OnceLock<PreludeDeclarations> = std::sync::OnceLock::new();
    PRELUDE.get_or_init(|| {
        let sources = [
            crate::nibstd::KERNEL,
            crate::nibstd::PRELUDE,
            include_str!("../../tauto-kernel/src/prelude_nat.taut"),
            include_str!("../../tauto-kernel/src/prelude_deq.taut"),
        ];
        let mut names = HashMap::new();
        let mut families = Vec::new();
        // These host effects have no source declaration in the prelude.
        let mut effects = vec!["show".to_string(), "exceeded".to_string()];

        let mut owned = Vec::new();
        let mut host_fns: Vec<String> = Vec::new();
        let mut class_members = Vec::new();
        let mut insert = |name: &str| {
            names.entry(name.to_string()).or_insert_with(|| {
                if name == "Tuple" {
                    return tuple_reference().clone();
                }
                DeclRef::primitive(name)
                    .or_else(|| SortSymbol::parse(name).map(DeclRef::of_sort))
                    .unwrap_or_else(|| DeclRef::fresh(name))
            });
        };
        for name in [
            "Nat",
            "Zero",
            "Succ",
            "Bool",
            "true",
            "false",
            "+",
            "*",
            "-",
            "Nat::eq",
            "Nat::lt",
            "Nat::sub",
            "Nat::div_nz",
            "Nat::rem_nz",
            "Quot",
            "Quot::mk",
            "Quot::lift",
            "Quot::ind",
            "Eq",
            "…",
            "Type",
            "Type1",
            "Type2",
            "Prop",
            "Level",
            "Text",
            "Bytes",
            "Char",
            "Never",
            "Shared",
            "Affine",
            "Linear",
            "PartialEq",
            "DecEq",
            "Hash",
            "Div",
            "Exceeded",
            "clone",
            "div",
            "mod",
            "recursor",
            "/",
            "i8",
            "i16",
            "i32",
            "i64",
            "u8",
            "u16",
            "u32",
            "u64",
            "nat",
            "Decimal",
            "Float",
            "Float32",
            "Info",
            "show",
            "exceeded",
            "=",
            "==",
            "!=",
            "<",
            "<=",
            ">",
            ">=",
            "/",
            "%",
            "&&",
            "||",
            "!",
            "¬",
            "#()",
            "Tuple",
            "_",
            "max",
        ] {
            insert(name);
        }
        for source in sources {
            let program = crate::surface::parse_program_unresolved_at(source, 0)
                .expect("the bundled prelude parses");
            for statement in &program.stmts {
                if let crate::surface::Stmt::Module { name, items, .. } = statement
                    && name == "Host"
                {
                    host_fns.extend(items.iter().filter_map(|item| match item {
                        crate::surface::Stmt::Fn(f) => Some(format!("{name}::{}", f.name)),
                        _ => None,
                    }));
                }
            }
            let (statements, _) = crate::surface::modules::resolve(program.stmts);
            for name in declared_names(&statements) {
                insert(name.as_str());
            }
            for statement in &statements {
                match statement {
                    crate::surface::Stmt::Effect(effect) => {
                        effects.push(effect.name.to_string());
                    }
                    crate::surface::Stmt::Class(class) => {
                        for (index, method) in class.methods.iter().enumerate() {
                            class_members.push((
                                class.name.to_string(),
                                index,
                                false,
                                method.name.to_string(),
                            ));
                        }
                        for (index, law) in class.laws.iter().enumerate() {
                            class_members.push((
                                class.name.to_string(),
                                index,
                                true,
                                law.name.to_string(),
                            ));
                        }
                    }
                    crate::surface::Stmt::Inductive(d) => {
                        owned.extend(
                            d.constructors
                                .iter()
                                .enumerate()
                                .map(|(index, c)| (d.name.to_string(), index, c.name.to_string())),
                        );
                    }
                    crate::surface::Stmt::Struct(d) => {
                        let constructor = format!("{}::Mk", d.name);
                        insert(&constructor);
                        owned.push((d.name.to_string(), 0, constructor.clone()));
                    }
                    crate::surface::Stmt::Enum(d) => {
                        owned.extend(
                            d.constructors
                                .iter()
                                .enumerate()
                                .map(|(index, c)| (d.name.to_string(), index, c.name.to_string())),
                        );
                    }
                    _ => {}
                }
                let family = match statement {
                    crate::surface::Stmt::Inductive(d) => Some(&d.name),
                    crate::surface::Stmt::Struct(d) | crate::surface::Stmt::Enum(d) => {
                        Some(&d.name)
                    }
                    _ => None,
                };
                if let Some(family) = family {
                    families.push(family.to_string());
                }
            }
        }
        drop(insert);
        for (class, index, law, label) in class_members {
            let owner = names[&class].clone();
            let reference = owner.class_member(index, law, &label);
            names.insert(reference.display().into(), reference);
            let laws = owner.generated(Generation::ClassLaws);
            names.insert(laws.display().into(), laws);
        }
        let family_references: HashMap<_, _> = families
            .iter()
            .map(|family| (family.clone(), names[family].clone()))
            .collect();
        let types = family_references.values().cloned().collect();
        let mut constructors = HashSet::new();
        let mut selections: HashMap<String, Vec<DeclRef>> = HashMap::new();
        for (family, index, spelling) in owned {
            let owner = &family_references[&family];
            let leaf = spelling.rsplit("::").next().unwrap();
            let reference =
                DeclRef::primitive(&spelling).unwrap_or_else(|| owner.constructor(index, leaf));
            let qualified = format!("{family}::{leaf}");
            constructors.insert(reference.clone());
            for alias in [&spelling, &qualified] {
                let candidates = selections.entry(alias.clone()).or_default();
                if !candidates.contains(&reference) {
                    candidates.push(reference.clone());
                }
            }
            if !family_references.contains_key(&spelling) {
                names.insert(spelling, reference.clone());
            }
            names.insert(qualified, reference);
        }
        for family in families {
            let owner = names[&family].clone();
            for kind in [
                Generation::Induction,
                Generation::Recursion,
                Generation::NoConfusionType,
                Generation::NoConfusionDiagonal,
                Generation::NoConfusion,
                Generation::Equality,
                Generation::EqualityReflexivity,
                Generation::EqualitySoundness,
                Generation::DecidableEquality,
            ] {
                let reference = owner.generated(kind);
                names.insert(reference.display().into(), reference);
            }
        }
        let qualified = names
            .iter()
            .map(|(name, reference)| {
                (
                    format!("{}::{name}", crate::surface::qualify::PRELUDE_MODULE),
                    reference.clone(),
                )
            })
            .collect::<Vec<_>>();
        let qualified_names: HashMap<String, DeclRef> = qualified.iter().cloned().collect();
        names.extend(qualified);
        let qualified_selections = selections
            .iter()
            .map(|(name, choices)| {
                (
                    format!("{}::{name}", crate::surface::qualify::PRELUDE_MODULE),
                    choices.clone(),
                )
            })
            .collect::<Vec<_>>();
        selections.extend(qualified_selections);
        let effects = effects
            .into_iter()
            .flat_map(|name| {
                let reference = names[&name].clone();
                [
                    (format!("std::prelude::{name}"), reference.clone()),
                    (name, reference),
                ]
            })
            .collect();
        let host_module_fns = host_fns
            .iter()
            .filter_map(|name| names.get(name).cloned())
            .collect();
        PreludeDeclarations {
            host_module_fns,
            qualified: qualified_names,
            types,
            selections,
            names,
            constructors,
            effects,
        }
    })
}

pub fn declared_names(stmts: &[crate::surface::Stmt]) -> Vec<&Name> {
    use crate::surface::Stmt;
    fn collect<'a>(s: &'a Stmt, out: &mut Vec<&'a Name>) {
        match s {
            Stmt::Fn(f) => out.push(&f.name),
            Stmt::Theorem(d) | Stmt::Def(d) => out.push(&d.name),
            Stmt::Struct(d) | Stmt::Enum(d) => {
                out.push(&d.name);
                out.extend(d.constructors.iter().map(|c| &c.name));
            }
            Stmt::Inductive(d) => {
                out.push(&d.name);
                out.extend(d.constructors.iter().map(|c| &c.name));
            }
            Stmt::Effect(d) => out.push(&d.name),
            Stmt::Class(d) => out.push(&d.name),
            Stmt::Let { name, .. } | Stmt::Var { name, .. } => out.push(name),
            Stmt::Extern { fns, types, .. } => {
                out.extend(fns.iter().map(|f| &f.name));
                out.extend(types.iter().map(|t| &t.name));
            }
            Stmt::Mutual { items, .. } | Stmt::Module { items, .. } => {
                for item in items {
                    collect(item, out);
                }
            }
            Stmt::Attributed { stmt, .. } => collect(stmt, out),
            _ => {}
        }
    }
    let mut out = Vec::new();
    for stmt in stmts {
        collect(stmt, &mut out);
    }
    out
}

/// Bindings for the language library, shared by its checked and executable views.
pub fn library_bindings() -> Bindings {
    Bindings {
        names: prelude_declarations().names.clone(),
        types: prelude_declarations().types.clone(),
        selections: prelude_declarations().selections.clone(),
        constructors: prelude_declarations().constructors.clone(),
        effects: prelude_declarations().effects.clone(),
        ..Bindings::default()
    }
}

/// Binds the library's own definitions to the designated library references.
/// User declarations use `library_bindings` and own distinct identities.
pub fn library_definition_bindings() -> Bindings {
    Bindings {
        library_definitions: true,
        ..library_bindings()
    }
}

/// The labels of the prelude's `Pair`, which `#(a, b)` is read to.
pub const PAIR_LABELS: [&str; 2] = ["fst", "snd"];

/// Whether a record named `name` with these field labels is the prelude's
/// `Pair { fst, snd }`, the form `#(a, b)` is read to.
pub fn is_pair_record<'a>(name: &Name, labels: impl IntoIterator<Item = &'a str>) -> bool {
    (is_library(name, "Pair") || is_library(name, "Pair::Mk")) && labels.into_iter().eq(PAIR_LABELS)
}

pub fn library_name(spelling: &str) -> Name {
    library_reference(spelling).unwrap_or_else(|| panic!("unknown library declaration: {spelling}"))
}

/// The designated library reference, when the library declares this spelling.
pub fn library_reference(spelling: &str) -> Option<Name> {
    prelude_declarations()
        .names
        .get(spelling)
        .cloned()
        .map(Name::from)
}

/// Recognizes the designated library declaration, never a same-display local.
/// Source syntax is recognized before the binding phase.
pub fn is_library(name: &Name, spelling: &str) -> bool {
    match name {
        Name::Spelled(text) => text == spelling,
        Name::Global(reference) => prelude_declarations().names.get(spelling) == Some(reference),
        _ => false,
    }
}

/// Recognizes a library declaration or a specialization of that declaration.
pub fn is_library_instance(name: &Name, spelling: &str) -> bool {
    let Some(mut reference) = name.as_global() else {
        return is_library(name, spelling);
    };
    while let Some(origin) = reference.origin() {
        reference = origin;
    }
    prelude_declarations().names.get(spelling) == Some(reference)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn host_effects_keep_their_namespace_when_a_value_shares_the_spelling() {
        for spelling in ["show", "exceeded"] {
            let mut bindings = library_bindings();
            let effect = bindings.effect(spelling).unwrap().clone();
            assert_eq!(Some(&effect), bindings.get(spelling));
            let value = DeclRef::fresh(spelling);
            bindings.source_alias(spelling, value.clone());
            assert_eq!(bindings.get(spelling), Some(&value));
            assert_eq!(bindings.effect(spelling), Some(&effect));
        }
    }

    #[test]
    fn a_library_type_keeps_its_identity_when_a_constructor_shares_its_name() {
        let bindings = library_bindings();
        let family = bindings.get("Cancelled").unwrap();
        let constructor = bindings.get("Cancelled::Cancelled").unwrap();
        assert_ne!(family, constructor);
        assert!(bindings.types.contains(family));
        assert!(bindings.constructors.contains(constructor));
        assert_eq!(
            bindings.selection("Cancelled"),
            Some(constructor.clone().into())
        );
        assert!(bindings.type_constructor_selection("Cancelled").is_some());
    }

    #[test]
    fn a_revision_retains_reservations_without_retaining_visibility() {
        let mut first = library_bindings();
        let declaration = first.declare(&Name::from("module::value"));
        let mut next = first.next_revision();
        assert!(next.get("module::value").is_none());
        assert_eq!(next.declare(&Name::from("module::value")), declaration);
        assert_ne!(
            library_bindings().declare(&Name::from("module::value")),
            declaration
        );
        assert_eq!(first.get("module::value"), Some(&declaration));
    }

    #[test]
    fn a_source_declaration_does_not_reuse_an_inherited_library_identity() {
        let mut bindings = library_bindings();
        let inherited = bindings.get("List").unwrap().clone();
        let mut sibling = bindings.clone();
        let own = bindings.declare(&Name::from("List"));
        assert_ne!(own, inherited);
        assert_eq!(bindings.get("List"), Some(&own));
        assert_eq!(sibling.get("List"), Some(&inherited));
        assert_eq!(sibling.declare(&Name::from("List")), own);
        assert_eq!(bindings.declare(&Name::from("List")), own);
        assert!(!is_library(&Name::Global(own), "List"));
    }

    #[test]
    fn declaring_a_bound_reference_retains_it_in_cloned_source_views() {
        let mut bindings = library_bindings();
        let reference = DeclRef::fresh("module::value");
        bindings.declare(&Name::Global(reference.clone()));
        let mut copy = bindings.clone();
        assert_eq!(copy.declare(&Name::from("module::value")), reference);
    }

    #[test]
    fn generated_declarations_keep_their_reserved_identity_when_defined() {
        let mut bindings = library_bindings();
        let family: Name = bindings.declare(&Name::from("Family")).into();
        let generated = bindings.generated(&family, Generation::Equality);
        assert_eq!(
            bindings.declare(&Name::from(generated.display())),
            generated
        );
    }

    #[test]
    fn effect_and_value_identities_survive_a_revision_separately() {
        let mut bindings = library_bindings();
        let spelling = Name::from("answer");
        let effect = bindings.declare_effect(&spelling);
        let function = bindings.declare(&spelling);
        assert_ne!(effect, function);
        assert_eq!(bindings.effect("answer"), Some(&effect));
        assert_eq!(bindings.get("answer"), Some(&function));
        let mut revision = bindings.next_revision();
        assert_eq!(revision.declare_effect(&spelling), effect);
        assert_eq!(revision.declare(&spelling), function);
        assert_eq!(revision.effect("answer"), Some(&effect));
        let designated = library_name("fail");
        revision.declare(&Name::from("fail"));
        assert_eq!(revision.effect("fail"), designated.as_global());
    }

    #[test]
    fn library_definitions_use_the_designated_references() {
        let mut bindings = library_definition_bindings();
        for name in ["List", "Pair", "Nat", "SynIdent"] {
            assert_eq!(
                Name::Global(bindings.declare(&Name::from(name))),
                library_name(name)
            );
        }
    }
}

/// Compiler state products share references between source binding and lowering.
/// Allocating these references does not admit their declarations to the kernel.
pub fn state_family(arity: usize) -> (DeclRef, DeclRef) {
    static FAMILIES: std::sync::LazyLock<std::sync::Mutex<HashMap<usize, (DeclRef, DeclRef)>>> =
        std::sync::LazyLock::new(Default::default);
    FAMILIES
        .lock()
        .expect("state family table")
        .entry(arity)
        .or_insert_with(|| {
            let family = DeclRef::fresh(format!("Mut{arity}"));
            let constructor = family.constructor(0, &format!("mut{arity}"));
            (family, constructor)
        })
        .clone()
}

fn state_reference(spelling: &str) -> Option<DeclRef> {
    let (digits, constructor) = spelling
        .strip_prefix("Mut")
        .map(|s| (s, false))
        .or_else(|| spelling.strip_prefix("mut").map(|s| (s, true)))?;
    let arity: usize = digits.parse().ok()?;
    if digits != arity.to_string() {
        return None;
    }
    let (family, member) = state_family(arity);
    Some(if constructor { member } else { family })
}
