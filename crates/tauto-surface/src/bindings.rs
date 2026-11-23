//! Source aliases and constructor candidates for one binding environment.
//! Reserving an identity does not admit a declaration to the kernel.
use crate::identity::{
    DeclRef, Declarations, ForkedMap, ForkedSet, Generation, Name, Selection, SortSymbol,
};
use crate::surface::SurfaceTerm;
use std::collections::{HashMap, HashSet};

#[derive(Clone, Default)]
pub struct Bindings {
    identities: Declarations,
    owned: ForkedMap<String, DeclRef>,
    library_definitions: bool,
    names: ForkedMap<String, DeclRef>,
    constructors: ForkedSet<DeclRef>,
    selections: ForkedMap<String, Vec<DeclRef>>,
    types: ForkedSet<DeclRef>,
    effects: ForkedMap<String, DeclRef>,
    owned_effects: ForkedMap<String, DeclRef>,
    /// What a copy added to and removed from the choices of each spelling,
    /// left by [`Self::subtract`] for [`Self::absorb`]; empty otherwise.
    chose: HashMap<String, (Vec<DeclRef>, Vec<DeclRef>)>,
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

impl crate::identity::Detach for Bindings {
    /// A copy whose reservations are its own from now on
    /// ([`Declarations::detached`]).
    fn detached(&self) -> Self {
        Self {
            identities: self.identities.detached(),
            ..self.clone()
        }
    }
}

impl Bindings {
    /// Takes in what a copy of these bindings (a clone, which shares its
    /// reservations) wrote since it was made ([`ForkedMap::absorb`]): what
    /// the files it declared made each spelling mean. False when another
    /// copy taken in since wrote one of the same spellings.
    pub fn absorb(&mut self, other: Bindings) -> bool {
        let mut alone = self.identities.absorb(other.identities);
        alone &= self.owned.absorb(other.owned);
        alone &= self.names.absorb(other.names);
        alone &= self.constructors.absorb(other.constructors);
        // A spelling's choices are a set (`Selection::new` sorts them): what
        // copies added and removed is added and removed, whichever came
        // first, as declaring the files in turn would.
        for (spelling, (added, removed)) in other.chose {
            let mut choices = self.selections.get(&spelling).cloned().unwrap_or_default();
            choices.retain(|c| !removed.contains(c));
            for c in added {
                if !choices.contains(&c) {
                    choices.push(c);
                }
            }
            if choices.is_empty() {
                self.selections.remove(&spelling);
            } else {
                self.selections.put(spelling, choices);
            }
        }
        alone &= self.types.absorb(other.types);
        alone &= self.effects.absorb(other.effects);
        alone &= self.owned_effects.absorb(other.owned_effects);
        alone
    }

    /// Leaves in this copy, made of `base` in generation `since`, only what
    /// it wrote, for [`Self::absorb`].
    pub fn subtract(&mut self, since: u64, base: &Bindings) {
        self.identities.subtract(since);
        self.owned.subtract(since);
        self.names.subtract(since);
        self.constructors.subtract(since);
        let empty = Vec::new();
        self.chose = self
            .selections
            .written_since(since)
            .map(|spelling| {
                let mine = self.selections.get(spelling).unwrap_or(&empty);
                let theirs = base.selections.get(spelling).unwrap_or(&empty);
                let added = mine
                    .iter()
                    .filter(|c| !theirs.contains(c))
                    .cloned()
                    .collect();
                let removed = theirs
                    .iter()
                    .filter(|c| !mine.contains(c))
                    .cloned()
                    .collect();
                (spelling.clone(), (added, removed))
            })
            .collect();
        self.selections = ForkedMap::default();
        self.types.subtract(since);
        self.effects.subtract(since);
        self.owned_effects.subtract(since);
    }

    /// What `spelling` means now, to be put back by [`Self::restore_spelling`].
    /// The declarations a spelling may select, in the order they were added.
    pub fn choices(&self, spelling: &str) -> Option<&Vec<DeclRef>> {
        self.selections.get(spelling)
    }

    /// Whether `reference` is a type these bindings know.
    pub fn is_type(&self, reference: &DeclRef) -> bool {
        self.types.contains(reference)
    }

    /// Whether `reference` is a constructor these bindings know.
    pub fn is_constructor_reference(&self, reference: &DeclRef) -> bool {
        self.constructors.contains(reference)
    }

    /// Counts `reference` as a constructor.
    pub fn add_constructor(&mut self, reference: DeclRef) {
        self.constructors.insert(reference);
    }

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
        fn put<V>(map: &mut ForkedMap<String, V>, spelling: &str, value: Option<V>) {
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

    pub(crate) fn effect_alias(&mut self, spelling: &str, reference: DeclRef) {
        self.effects.insert(spelling.into(), reference.clone());
        self.names
            .entry(spelling.into())
            .or_insert_with(|| reference);
    }

    pub fn effect(&self, spelling: &str) -> Option<&DeclRef> {
        self.effects.get(spelling)
    }

    /// The type declared under `spelling`, if it is one.
    pub fn type_named(&self, spelling: &str) -> Option<&DeclRef> {
        self.get(spelling).filter(|r| self.types.contains(*r))
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
        // The family may itself be a splice (`enum $name { Execute }`): owning
        // `Execute` under `$name` would spell `$name::Execute`, which Lift
        // would misread as a hole for `name::Execute`.
        if name.starts_with('$') || family.starts_with('$') {
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
        let original = ((*self.names).clone(), (*self.selections).clone());
        // Only a constructor written alone is held back: a lone name that is
        // not a constructor binds a variable in a pattern, while a qualified
        // one (`Rect::Mk`, `modu::geom::Rect::Mk`) names the declaration
        // wherever it is written, as a macro's output writes it too.
        self.names.retain(|spelling, reference| {
            spelling.contains(crate::surface::qualify::SEPARATOR)
                || !self.constructors.contains(reference)
                || reference.display().starts_with(crate::records::PREFIX)
                || owners.contains(reference)
                || reference
                    .owner()
                    .is_some_and(|owner| owners.contains(owner))
        });
        self.selections.retain(|spelling, candidates| {
            if spelling.contains(crate::surface::qualify::SEPARATOR) {
                return true;
            }
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
        let (names, selections) = candidates;
        self.names.set_to(names);
        self.selections.set_to(selections);
    }

    /// Whether `reference`, the library's declaration of `spelling` that
    /// this source does not declare itself, is hidden by a constructor the
    /// source declares with that spelling. The library keeps some names
    /// with no source declaration (`Info`); a file's own
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
/// Identities are written by number at a fixed width, so that comparing two
/// keys as text orders the identities as numbers: the row of effect instances
/// is sorted by this key, and a declaration made earlier sorts first.
pub fn argument_key(arguments: &[SurfaceTerm]) -> String {
    fn number(index: u64) -> String {
        format!("{index:020}")
    }
    let mut parts = arguments.to_vec();
    for part in &mut parts {
        crate::surface::walk::term(part, &mut |term| term.span = crate::span::Span::new(0, 0));
        crate::surface::references::term(part, &mut |name| {
            *name = Name::Spelled(match name {
                Name::Global(reference) => format!("global:{}", number(reference.id().index())),
                Name::Local(reference) => format!("local:{}", number(reference.id().index())),
                Name::Selection(selection) => format!(
                    "selection:{:?}:{:?}",
                    selection.binding().map(|binding| number(binding.id().index())),
                    selection
                        .candidates()
                        .iter()
                        .map(|candidate| number(candidate.id().index()))
                        .collect::<Vec<_>>()
                ),
                Name::Written(written) => format!("written:{}", written.display()),
                Name::Effect(use_) => {
                    format!(
                        "effect:{}:{:?}:{}:{}",
                        number(use_.effect().id().index()),
                        use_.parameters()
                            .iter()
                            .map(|parameter| number(parameter.id().index()))
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

/// The spelling of the effect of a computation that may not return.
pub const DIVERGENCE: &str = "div";

/// Marks, in the list of the prelude's own names, where the effect of
/// divergence is made. It is no name.
const DIVERGENCE_PLACE: &str = "\0div";

struct PreludeDeclarations {
    divergence: DeclRef,
    types: HashSet<DeclRef>,
    selections: HashMap<String, Vec<DeclRef>>,
    effects: HashMap<String, DeclRef>,
    names: HashMap<String, DeclRef>,
    constructors: HashSet<DeclRef>,
    /// Each prelude declaration by the full name a file writes to mean it
    /// whatever else it declares (`std::prelude::Text`).
    qualified: HashMap<String, DeclRef>,
}

/// The prelude declaration a full name (`std::prelude::Text`) writes.
pub fn library_by_full_name(full: &str) -> Option<&'static DeclRef> {
    prelude_declarations().qualified.get(full)
}

/// The library declarations the reader writes by reference: a product type `A × B` is `Pair(A, B)`,
/// a product value `#(a, b)` is `Pair::Mk(a, b)`, and `#()` is `Star` of `Unit`. They are made on their
/// own, not by reading the prelude, so the parser can write them while the prelude is being read.
fn reader_reference(spelling: &str) -> Option<&'static DeclRef> {
    use std::sync::OnceLock;
    static PAIR: OnceLock<DeclRef> = OnceLock::new();
    static PAIR_MK: OnceLock<DeclRef> = OnceLock::new();
    static STAR: OnceLock<DeclRef> = OnceLock::new();
    static UNIT: OnceLock<DeclRef> = OnceLock::new();
    let family =
        |cell: &'static OnceLock<DeclRef>, name: &str| cell.get_or_init(|| DeclRef::fresh(name));
    Some(match spelling {
        "Pair" => family(&PAIR, "Pair"),
        "Unit" => family(&UNIT, "Unit"),
        // A constructor is its family's, as the prelude's table makes it.
        "Pair::Mk" => PAIR_MK.get_or_init(|| family(&PAIR, "Pair").constructor(0, "Mk")),
        "Star" => STAR.get_or_init(|| family(&UNIT, "Unit").constructor(0, "Star")),
        _ => return None,
    })
}

/// Whether `name` is the reader's own reference to the library declaration `spelling` (see
/// [`reader_reference`]). Compared with the reference itself, not through the prelude's table:
/// the parser asks this while the prelude is being read.
pub fn is_reader_reference(name: &Name, spelling: &str) -> bool {
    name.as_global()
        .is_some_and(|r| Some(r) == reader_reference(spelling))
}

/// The prelude's `Pair`, the type of every product (`A × B`).
pub fn pair_reference() -> &'static DeclRef {
    reader_reference("Pair").expect("a reader reference")
}

/// The constructor `Pair::Mk`, the value of every product (`#(a, b)`).
pub fn pair_mk_reference() -> &'static DeclRef {
    reader_reference("Pair::Mk").expect("a reader reference")
}

/// The unit's value `Star`, written `#()`.
pub fn star_reference() -> &'static DeclRef {
    reader_reference("Star").expect("a reader reference")
}

/// The unit type `Unit`.
pub fn unit_reference() -> &'static DeclRef {
    reader_reference("Unit").expect("a reader reference")
}

/// The prelude's type under `spelling` (`Bool`), whatever else a file declares under that spelling:
/// where a type is wanted, a constructor of the file with the same name is not one.
pub fn library_type(spelling: &str) -> Option<&'static DeclRef> {
    let prelude = prelude_declarations();
    prelude
        .names
        .get(spelling)
        .filter(|r| !prelude.constructors.contains(*r) && !prelude.selections.contains_key(spelling))
}

fn prelude_declarations() -> &'static PreludeDeclarations {
    static PRELUDE: std::sync::OnceLock<PreludeDeclarations> = std::sync::OnceLock::new();
    PRELUDE.get_or_init(|| {
        struct Reading;
        impl Drop for Reading {
            fn drop(&mut self) {
                READING_PRELUDE.with(|r| r.set(false));
            }
        }
        READING_PRELUDE.with(|r| r.set(true));
        let _reading = Reading;
        let sources = [
            crate::nibstd::KERNEL,
            crate::nibstd::PRELUDE,
            include_str!("../../tauto-kernel/src/prelude_nat.taut"),
            include_str!("../../tauto-kernel/src/prelude_deq.taut"),
            include_str!("../../tauto-kernel/src/prelude_eq.taut"),
        ];
        let mut names = HashMap::new();
        let mut families = Vec::new();
        // This host effect has no source declaration in the prelude.
        let mut effects = vec!["exceeded".to_string()];

        let mut owned = Vec::new();
        let mut class_members = Vec::new();
        let mut divergence = None;
        let mut insert = |name: &str| {
            if name == DIVERGENCE_PLACE {
                divergence = Some(DeclRef::fresh(DIVERGENCE));
                return;
            }
            names.entry(name.to_string()).or_insert_with(|| {
                if let Some(reference) =
                    reader_reference(name).filter(|_| matches!(name, "Pair" | "Unit"))
                {
                    return reference.clone();
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
            "Never",
            "Shared",
            "Affine",
            "Linear",
            "PartialEq",
            "DecEq",
            // The effect of divergence is made here, between `DecEq` and
            // `budget`, as it was when it was a name of this table: the
            // order of the effects of a row follows the order they are made.
            DIVERGENCE_PLACE,
            "budget",
            "budget_memory",
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
            "uhost",
            "nat",
            "Decimal",
            "Float",
            "Float32",
            "Info",
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
            "_",
            "max",
        ] {
            insert(name);
        }
        for source in sources {
            let program =
                crate::surface::parse_builtin_at(source, 0).expect("the bundled prelude parses");
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
        let divergence = divergence.expect("the list of names has the place of divergence");
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
        let mut effects: HashMap<String, DeclRef> = effects
            .into_iter()
            .flat_map(|name| {
                let reference = names[&name].clone();
                [
                    (format!("std::prelude::{name}"), reference.clone()),
                    (name, reference),
                ]
            })
            .collect();
        // The effect of a function that may not return. It has a reference of
        // its own, as effects and functions are different namespaces: the
        // function `div` and this effect share a spelling and not an identity.
        let diverge = divergence;
        effects.insert(format!("std::prelude::{DIVERGENCE}"), diverge.clone());
        effects.insert(DIVERGENCE.to_string(), diverge.clone());
        PreludeDeclarations {
            divergence: diverge,
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
            Stmt::Extern {
                fns,
                types,
                structs,
                enums,
                ..
            } => {
                out.extend(fns.iter().map(|f| &f.name));
                out.extend(types.iter().map(|t| &t.name));
                out.extend(structs.iter().map(|t| &t.name));
                out.extend(enums.iter().map(|t| &t.name));
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
        names: prelude_declarations().names.clone().into(),
        types: prelude_declarations().types.clone().into(),
        selections: prelude_declarations().selections.clone().into(),
        constructors: prelude_declarations().constructors.clone().into(),
        effects: prelude_declarations().effects.clone().into(),
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

/// The library's effect of divergence, `div`, which is not the function `div`.
pub fn divergence() -> Name {
    Name::from(prelude_declarations().divergence.clone())
}

/// Whether `name` is the library's effect of divergence (never the function
/// `div`, whose spelling it shares). Source syntax is recognized before the
/// binding phase, where the spelling is all there is.
pub fn is_divergence(name: &Name) -> bool {
    match name {
        Name::Spelled(text) => text == DIVERGENCE,
        Name::Global(reference) => reference == &prelude_declarations().divergence,
        Name::Effect(use_) => use_.effect() == &prelude_declarations().divergence,
        _ => false,
    }
}

/// Whether `name` is the library's effect spelled `spelling`: `is_library`,
/// except that `div` is the effect of divergence and not the function.
pub fn is_library_effect(name: &Name, spelling: &str) -> bool {
    if spelling == DIVERGENCE {
        is_divergence(name)
    } else {
        is_library(name, spelling)
    }
}

/// The library's effect spelled `spelling`: `library_name`, except that `div`
/// is the effect of divergence and not the function.
/// The library's effect declared under `spelling`, by its reference.
/// None while the library's own declarations are being read.
pub fn library_effect(spelling: &str) -> Option<&'static DeclRef> {
    if READING_PRELUDE.with(|r| r.get()) {
        return None;
    }
    prelude_declarations().effects.get(spelling)
}

thread_local! {
    static READING_PRELUDE: std::cell::Cell<bool> = const { std::cell::Cell::new(false) };
}

pub fn library_effect_name(spelling: &str) -> Name {
    if spelling == DIVERGENCE {
        divergence()
    } else {
        library_name(spelling)
    }
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

/// Every spelling a library declaration has, sorted: a name the JavaScript
/// backend writes as the library's (`library_reference`).
pub fn library_spellings() -> Vec<String> {
    let mut out: Vec<String> = prelude_declarations().names.keys().cloned().collect();
    out.sort();
    out
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

/// Whether `name` is the library declaration spelled `spelling`, also when
/// the name is a selection among declarations that include it.
pub fn is_library_selected(name: &Name, spelling: &str) -> bool {
    match name {
        Name::Selection(selection) => selection
            .candidates()
            .iter()
            .any(|reference| is_library(&Name::Global(reference.clone()), spelling)),
        _ => is_library(name, spelling),
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

/// The constant a text literal `s` made with the constructor `ctor` is: one
/// reference for each pair, shown as the literal is written, so that copies
/// of a term that holds the literal hold one name and not its bytes.
pub fn text_literal(ctor: &DeclRef, s: &str) -> DeclRef {
    type Table = HashMap<(DeclRef, String), DeclRef>;
    static LITERALS: std::sync::LazyLock<std::sync::Mutex<Table>> =
        std::sync::LazyLock::new(Default::default);
    LITERALS
        .lock()
        .expect("text literal table")
        .entry((ctor.clone(), s.to_string()))
        .or_insert_with(|| DeclRef::fresh(format!("{s:?}")))
        .clone()
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
