//! Identities of declarations and lexical bindings.
//!
//! A name is resolved once, where it is written, and is carried afterwards as
//! an identity. Display names never take part in equality, ordering or
//! hashing: two declarations that are displayed alike are two declarations.
//! Reserving an identity does not mean that the declaration is accepted;
//! acceptance is the kernel's.
//!
//! This module depends on nothing else of the crate. It knows no module paths,
//! imports or visibility: a declaration's display is the full name the
//! qualifier gives it (`app::List`, `std::prelude::List`, `M::T::C`), and
//! which names a file may use stays with the qualifier.

use std::collections::{HashMap, HashSet};
use std::hash::{Hash, Hasher};
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::{Arc, Mutex, OnceLock, Weak};

/// Identities below this are the primitives; everything else is allocated.
const FIRST_FRESH: u64 = 1024;

static NEXT: AtomicU64 = AtomicU64::new(FIRST_FRESH);

fn fresh() -> u64 {
    let id = NEXT.fetch_add(1, Ordering::Relaxed);
    assert!(id != u64::MAX, "identity space exhausted");
    id
}

fn locked<T>(mutex: &Mutex<T>) -> std::sync::MutexGuard<'_, T> {
    mutex.lock().expect("identity tables are available")
}

/// The identity of a declaration. Distinct from [`LocalId`]: the two never
/// stand for one another.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct DeclId(u64);

impl DeclId {
    /// The number, for tables that record identities by position.
    pub fn index(self) -> u64 {
        self.0
    }
}

/// The identity of a lexical binding (a parameter, a `let`, a pattern
/// variable, a local function).
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct LocalId(u64);

impl LocalId {
    pub fn fresh() -> Self {
        Self(fresh())
    }
    pub fn index(self) -> u64 {
        self.0
    }
}

/// The sorts. A declaration is a sort only if its reference says so; a
/// declaration that is merely displayed as `Type7` is not.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum SortSymbol {
    Proposition,
    Type(u32),
}

impl SortSymbol {
    /// `Prop`, `Type`, `Type<n>`.
    pub fn parse(name: &str) -> Option<Self> {
        if name == "Prop" {
            return Some(Self::Proposition);
        }
        let suffix = name.strip_prefix("Type")?;
        Some(Self::Type(if suffix.is_empty() {
            0
        } else {
            suffix.parse().ok()?
        }))
    }

    pub fn display(self) -> String {
        match self {
            Self::Proposition => "Prop".into(),
            Self::Type(0) => "Type".into(),
            Self::Type(n) => format!("Type{n}"),
        }
    }
}

/// The declarations whose rules the core implements. Their identities are
/// fixed and the same in every session; their types and definitions are still
/// accepted by the core like any other declaration's.
const PRIMITIVES: &[&str] = &[
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
];

/// What a generated declaration is for. A generated declaration is identified
/// by its owner and its kind (and position, where the kind has one).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Generation {
    Induction,
    Recursion,
    NoConfusionType,
    NoConfusionDiagonal,
    NoConfusion,
    Equality,
    EqualityReflexivity,
    EqualitySoundness,
    DecidableEquality,
    /// The auxiliary declarations of the `n`-th nested occurrence.
    Nested(usize),
    /// The constructor at position `n` of an owner type.
    Constructor(usize),
    EffectOperations,
    EffectArguments,
    EffectResult,
    EffectArm,
}

impl Generation {
    fn suffix(self) -> String {
        match self {
            Self::EffectOperations => "@op".into(),
            Self::EffectArguments => "@args".into(),
            Self::EffectResult => "@res".into(),
            Self::EffectArm => "@arm".into(),
            Self::Induction => "ind".into(),
            Self::Recursion => "rec".into(),
            Self::NoConfusionType => "nc".into(),
            Self::NoConfusionDiagonal => "nc_diag".into(),
            Self::NoConfusion => "noconf".into(),
            Self::Equality => "beq".into(),
            Self::EqualityReflexivity => "beq_refl".into(),
            Self::EqualitySoundness => "beq_sound".into(),
            Self::DecidableEquality => "deq".into(),
            Self::Nested(index) => format!("nested{index}"),
            Self::Constructor(index) => format!("ctor{index}"),
        }
    }
}

struct Declaration {
    id: DeclId,
    display: String,
    sort: Option<SortSymbol>,
    /// Declarations generated from this one, by kind.
    generated: Mutex<HashMap<Generation, DeclRef>>,
    /// Instances made from this declaration, by their argument key. Weak: an
    /// instance nobody holds is forgotten.
    instances: Mutex<HashMap<String, Weak<Declaration>>>,
    /// The declaration this is an instance of.
    origin: Option<DeclRef>,
}

impl Declaration {
    fn new(id: u64, display: String, sort: Option<SortSymbol>, origin: Option<DeclRef>) -> Self {
        Self {
            id: DeclId(id),
            display,
            sort,
            generated: Default::default(),
            instances: Default::default(),
            origin,
        }
    }
}

/// A reference to a declaration. Equality, ordering and hashing are by
/// [`DeclId`]; clones are the same reference.
#[derive(Clone)]
pub struct DeclRef(Arc<Declaration>);

impl DeclRef {
    /// A new declaration, unequal to every other. `display` is the full name.
    pub fn fresh(display: impl Into<String>) -> Self {
        Self(Arc::new(Declaration::new(
            fresh(),
            display.into(),
            None,
            None,
        )))
    }

    /// The declaration generated from this one. The same owner and kind give
    /// the same reference; another owner gives another.
    pub fn generated(&self, kind: Generation) -> Self {
        let suffix = kind.suffix();
        let display = if suffix.starts_with('@') {
            format!("{self}{suffix}")
        } else {
            format!("{self}::{suffix}")
        };
        self.generated_named(kind, display)
    }

    fn generated_named(&self, kind: Generation, display: String) -> Self {
        locked(&self.0.generated)
            .entry(kind)
            .or_insert_with(|| Self::fresh(display))
            .clone()
    }

    /// The constructor at `index` of this type, displayed as `<this>::<leaf>`.
    /// The reference depends on this type and the position, not on the leaf's
    /// spelling: types that have a constructor of the same name do not share
    /// it.
    pub fn constructor(&self, index: usize, leaf: &str) -> Self {
        self.generated_named(Generation::Constructor(index), format!("{self}::{leaf}"))
    }

    /// The instance of this declaration for the arguments with the canonical
    /// rendering `key`. The same key gives the same reference while any holder
    /// keeps it.
    pub fn specialize(&self, key: &str, display: impl Into<String>) -> Self {
        let mut instances = locked(&self.0.instances);
        if let Some(existing) = instances.get(key).and_then(Weak::upgrade) {
            return Self(existing);
        }
        let instance = Self(Arc::new(Declaration::new(
            fresh(),
            display.into(),
            None,
            Some(self.clone()),
        )));
        instances.insert(key.to_string(), Arc::downgrade(&instance.0));
        instance
    }

    /// The declaration this is an instance of, if it is one.
    pub fn origin(&self) -> Option<&DeclRef> {
        self.0.origin.as_ref()
    }

    pub fn id(&self) -> DeclId {
        self.0.id
    }

    /// The full name this reference is displayed as.
    pub fn display(&self) -> &str {
        &self.0.display
    }

    /// The sort this reference is, if it is one.
    pub fn sort(&self) -> Option<SortSymbol> {
        self.0.sort
    }

    /// The reference of a sort. One per sort in the whole process.
    pub fn of_sort(sort: SortSymbol) -> Self {
        static SORTS: OnceLock<Mutex<HashMap<u32, DeclRef>>> = OnceLock::new();
        let key = match sort {
            SortSymbol::Proposition => u32::MAX,
            SortSymbol::Type(n) => n,
        };
        locked(SORTS.get_or_init(Default::default))
            .entry(key)
            .or_insert_with(|| {
                Self(Arc::new(Declaration::new(
                    fresh(),
                    sort.display(),
                    Some(sort),
                    None,
                )))
            })
            .clone()
    }

    /// The reference of a primitive, by its spelling in the core. One per
    /// primitive in the whole process; `None` for any other spelling.
    pub fn primitive(name: &str) -> Option<Self> {
        static TABLE: OnceLock<Vec<DeclRef>> = OnceLock::new();
        let index = PRIMITIVES.iter().position(|n| *n == name)?;
        Some(
            TABLE.get_or_init(|| {
                PRIMITIVES
                    .iter()
                    .enumerate()
                    .map(|(i, n)| {
                        Self(Arc::new(Declaration::new(
                            i as u64,
                            (*n).into(),
                            None,
                            None,
                        )))
                    })
                    .collect()
            })[index]
                .clone(),
        )
    }

    /// Whether this is the primitive spelled `name`.
    pub fn is_primitive(&self, name: &str) -> bool {
        Self::primitive(name).is_some_and(|p| p == *self)
    }
}

impl PartialEq for DeclRef {
    fn eq(&self, other: &Self) -> bool {
        self.id() == other.id()
    }
}
impl Eq for DeclRef {}
impl Hash for DeclRef {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.id().hash(state);
    }
}
impl PartialOrd for DeclRef {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}
impl Ord for DeclRef {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.id().cmp(&other.id())
    }
}
impl std::fmt::Debug for DeclRef {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "DeclRef({}#{})", self.display(), self.id().0)
    }
}
impl std::fmt::Display for DeclRef {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(self.display())
    }
}

/// What a local binding generates for a row variable.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum LocalGeneration {
    RowOperations,
    RowResults,
}

/// A lexical binding. Copies and display changes preserve its identity.
#[derive(Clone)]
pub struct LocalRef {
    id: LocalId,
    display: String,
    generated: Arc<Mutex<HashMap<LocalGeneration, LocalRef>>>,
}

impl LocalRef {
    pub fn fresh(display: impl Into<String>) -> Self {
        Self {
            id: LocalId::fresh(),
            display: display.into(),
            generated: Default::default(),
        }
    }

    /// The same binding displayed otherwise.
    pub fn with_display(&self, display: impl Into<String>) -> Self {
        Self {
            id: self.id,
            display: display.into(),
            generated: self.generated.clone(),
        }
    }

    /// The binding generated from this one. All displays of one binding share
    /// the generated bindings.
    pub fn generated(&self, kind: LocalGeneration) -> Self {
        let suffix = match kind {
            LocalGeneration::RowOperations => "rowop",
            LocalGeneration::RowResults => "rowres",
        };
        locked(&self.generated)
            .entry(kind)
            .or_insert_with(|| Self::fresh(format!("{}@{suffix}", self.display)))
            .clone()
    }

    pub fn id(&self) -> LocalId {
        self.id
    }

    pub fn display(&self) -> &str {
        &self.display
    }
}

impl PartialEq for LocalRef {
    fn eq(&self, other: &Self) -> bool {
        self.id == other.id
    }
}
impl Eq for LocalRef {}
impl Hash for LocalRef {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.id.hash(state);
    }
}
impl PartialOrd for LocalRef {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}
impl Ord for LocalRef {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.id.cmp(&other.id)
    }
}
impl std::fmt::Debug for LocalRef {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "LocalRef({}#{})", self.display, self.id.0)
    }
}
impl std::fmt::Display for LocalRef {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(&self.display)
    }
}

/// A finite, non-empty set of declarations awaiting a choice that needs a
/// type. Its identity is the set of candidates; the display is only for
/// diagnostics.
#[derive(Debug, Clone)]
pub struct Selection {
    display: String,
    candidates: Vec<DeclRef>,
}

impl Selection {
    /// Candidates are ordered and deduplicated by identity.
    ///
    /// # Panics
    ///
    /// If there are no candidates.
    pub fn new(display: impl Into<String>, mut candidates: Vec<DeclRef>) -> Self {
        candidates.sort();
        candidates.dedup();
        assert!(!candidates.is_empty(), "a selection needs candidates");
        Self {
            display: display.into(),
            candidates,
        }
    }

    pub fn candidates(&self) -> &[DeclRef] {
        &self.candidates
    }

    pub fn display(&self) -> &str {
        &self.display
    }

    /// The only candidate that `accepts`, if exactly one does.
    pub fn choose(&self, mut accepts: impl FnMut(&DeclRef) -> bool) -> Option<&DeclRef> {
        let mut chosen = self.candidates.iter().filter(|c| accepts(c));
        let first = chosen.next()?;
        chosen.next().is_none().then_some(first)
    }
}

impl PartialEq for Selection {
    fn eq(&self, other: &Self) -> bool {
        self.candidates == other.candidates
    }
}
impl Eq for Selection {}
impl Hash for Selection {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.candidates.hash(state);
    }
}
impl PartialOrd for Selection {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}
impl Ord for Selection {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.candidates.cmp(&other.candidates)
    }
}

/// An effect applied to arguments, with the effect already bound. Effects are
/// named apart from other declarations, so this is its own kind of name.
///
/// The arguments are carried as a canonical rendering `key` made by whoever
/// binds them (the rendering distinguishes bound references by identity, not
/// by display); identity is the effect, the key, whether it is universal, and
/// the row parameters.
#[derive(Debug, Clone)]
pub struct EffectUse {
    effect: DeclRef,
    key: String,
    parameters: Vec<LocalRef>,
    universal: bool,
    display: String,
}

impl EffectUse {
    pub fn new(
        effect: DeclRef,
        key: impl Into<String>,
        parameters: Vec<LocalRef>,
        universal: bool,
        display: impl Into<String>,
    ) -> Self {
        Self {
            effect,
            key: key.into(),
            parameters,
            universal,
            display: display.into(),
        }
    }

    pub fn effect(&self) -> &DeclRef {
        &self.effect
    }
    pub fn argument_key(&self) -> &str {
        &self.key
    }
    pub fn parameters(&self) -> &[LocalRef] {
        &self.parameters
    }
    pub fn is_universal(&self) -> bool {
        self.universal
    }
    pub fn display(&self) -> &str {
        &self.display
    }

    fn identity(&self) -> (&DeclRef, &str, bool, &[LocalRef]) {
        (&self.effect, &self.key, self.universal, &self.parameters)
    }
}

impl PartialEq for EffectUse {
    fn eq(&self, other: &Self) -> bool {
        self.identity() == other.identity()
    }
}
impl Eq for EffectUse {}
impl Hash for EffectUse {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.identity().hash(state);
    }
}
impl PartialOrd for EffectUse {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}
impl Ord for EffectUse {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.identity().cmp(&other.identity())
    }
}

/// A name before resolution, or the reference it resolves to. A reference is
/// never equal to a spelling with the same display, and the variants are never
/// equal to one another.
#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum Name {
    /// As written; not yet resolved.
    Spelled(String),
    /// A declaration.
    Global(DeclRef),
    /// A lexical binding.
    Local(LocalRef),
    /// Candidates awaiting a type-directed choice.
    Selection(Selection),
    /// An effect applied to its arguments.
    Effect(Arc<EffectUse>),
}

impl Name {
    /// What the name is displayed as. Never an identity.
    pub fn as_str(&self) -> &str {
        match self {
            Self::Spelled(n) => n,
            Self::Global(r) => r.display(),
            Self::Local(r) => r.display(),
            Self::Selection(s) => s.display(),
            Self::Effect(e) => e.display(),
        }
    }

    pub fn is_resolved(&self) -> bool {
        !matches!(self, Self::Spelled(_))
    }

    pub fn as_global(&self) -> Option<&DeclRef> {
        match self {
            Self::Global(r) => Some(r),
            _ => None,
        }
    }

    pub fn as_local(&self) -> Option<&LocalRef> {
        match self {
            Self::Local(r) => Some(r),
            _ => None,
        }
    }

    /// The sort this name is. Only a spelling or a reference that is a sort
    /// is one: a declaration or a binding displayed as `Prop` is not.
    pub fn sort_symbol(&self) -> Option<SortSymbol> {
        match self {
            Self::Spelled(name) => SortSymbol::parse(name),
            Self::Global(reference) => reference.sort(),
            Self::Local(_) | Self::Selection(_) | Self::Effect(_) => None,
        }
    }
}

impl std::ops::Deref for Name {
    type Target = str;
    fn deref(&self) -> &str {
        self.as_str()
    }
}
impl std::fmt::Display for Name {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(self.as_str())
    }
}
impl Default for Name {
    fn default() -> Self {
        Self::Spelled(String::new())
    }
}
impl From<String> for Name {
    fn from(value: String) -> Self {
        Self::Spelled(value)
    }
}
impl From<&str> for Name {
    fn from(value: &str) -> Self {
        Self::Spelled(value.into())
    }
}
impl From<DeclRef> for Name {
    fn from(value: DeclRef) -> Self {
        Self::Global(value)
    }
}
impl From<LocalRef> for Name {
    fn from(value: LocalRef) -> Self {
        Self::Local(value)
    }
}
impl From<Selection> for Name {
    fn from(value: Selection) -> Self {
        Self::Selection(value)
    }
}
impl From<EffectUse> for Name {
    fn from(value: EffectUse) -> Self {
        Self::Effect(Arc::new(value))
    }
}

/// The index from full names to declarations, used while reserving and
/// resolving. Semantic environments are keyed by [`DeclRef`] instead.
///
/// Two things are kept apart. A name is *reserved* when it has a reference;
/// reservations are shared by the clones of a table (a checkpoint and its
/// branches agree on what a name's reference is). A name is *visible* when it
/// has been declared into this table; visibility belongs to one table. A
/// reserved name that is not declared is not found by [`Declarations::get`].
#[derive(Debug, Clone, Default)]
pub struct Declarations {
    visible: HashMap<String, DeclRef>,
    reservations: Arc<Mutex<HashMap<String, DeclRef>>>,
    constructors: HashSet<DeclRef>,
}

impl Declarations {
    pub fn new() -> Self {
        Self::default()
    }

    /// A table that starts from this one's visible names and shares nothing
    /// with it afterwards: what either reserves later is its own.
    pub fn fork(&self) -> Self {
        Self {
            visible: self.visible.clone(),
            reservations: Default::default(),
            constructors: self.constructors.clone(),
        }
    }

    /// The reference of the full name `name`, made if there is none. It is a
    /// primitive or sort reference if `name` spells one. The name does not
    /// become visible.
    pub fn reserve(&mut self, name: &str) -> DeclRef {
        if let Some(visible) = self.visible.get(name) {
            return visible.clone();
        }
        locked(&self.reservations)
            .entry(name.into())
            .or_insert_with(|| Self::reference_for(name))
            .clone()
    }

    fn reference_for(name: &str) -> DeclRef {
        DeclRef::primitive(name)
            .or_else(|| SortSymbol::parse(name).map(DeclRef::of_sort))
            .unwrap_or_else(|| DeclRef::fresh(name))
    }

    /// Make the full name `name` visible. `Err` carries the reference already
    /// visible under that name; the table is unchanged.
    pub fn declare(&mut self, name: &str) -> Result<DeclRef, DeclRef> {
        if let Some(existing) = self.visible.get(name) {
            return Err(existing.clone());
        }
        let reference = self.reserve(name);
        self.visible.insert(name.into(), reference.clone());
        Ok(reference)
    }

    /// Make an existing reference visible under its own display. `Err` as in
    /// [`Declarations::declare`], also when another reference is visible there.
    pub fn declare_reference(&mut self, reference: &DeclRef) -> Result<(), DeclRef> {
        match self.visible.get(reference.display()) {
            Some(existing) => Err(existing.clone()),
            None => {
                self.visible
                    .insert(reference.display().into(), reference.clone());
                Ok(())
            }
        }
    }

    /// Declare the constructor at `index` of `owner`, visible as
    /// `<owner>::<leaf>`, and record that it is a constructor. `Err` as in
    /// [`Declarations::declare`].
    pub fn declare_constructor(
        &mut self,
        owner: &DeclRef,
        index: usize,
        leaf: &str,
    ) -> Result<DeclRef, DeclRef> {
        let reference = owner.constructor(index, leaf);
        self.declare_reference(&reference)?;
        self.constructors.insert(reference.clone());
        Ok(reference)
    }

    /// Declare what `owner` generates for `kind`, visible under its display.
    pub fn declare_generated(
        &mut self,
        owner: &DeclRef,
        kind: Generation,
    ) -> Result<DeclRef, DeclRef> {
        let reference = owner.generated(kind);
        self.declare_reference(&reference)?;
        Ok(reference)
    }

    /// The reference visible under the full name `name`.
    pub fn get(&self, name: &str) -> Option<&DeclRef> {
        self.visible.get(name)
    }

    /// Whether `reference` is a declared constructor of this table.
    pub fn is_constructor(&self, reference: &DeclRef) -> bool {
        self.constructors.contains(reference)
    }

    /// The visible names and their references.
    pub fn bindings(&self) -> impl Iterator<Item = (&str, &DeclRef)> {
        self.visible.iter().map(|(n, r)| (n.as_str(), r))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn display_does_not_identify_declarations() {
        let a = DeclRef::fresh("app::value");
        let b = DeclRef::fresh("app::value");
        assert_eq!(a.display(), b.display());
        assert_ne!(a, b);
        assert_ne!(Name::Global(a.clone()), Name::Global(b));
        assert_eq!(Name::Global(a.clone()), Name::Global(a.clone()));
        let mut set = HashSet::new();
        set.insert(a.clone());
        assert!(set.contains(&a.clone()));
        assert_eq!(set.len(), 1);
    }

    #[test]
    fn variants_of_name_are_never_equal() {
        let spelled = Name::from("x");
        let global = Name::Global(DeclRef::fresh("x"));
        let local = Name::Local(LocalRef::fresh("x"));
        assert_ne!(spelled, global);
        assert_ne!(spelled, local);
        assert_ne!(global, local);
        assert!(!spelled.is_resolved() && global.is_resolved() && local.is_resolved());
        assert_eq!(&*spelled, "x");
    }

    #[test]
    fn local_identity_survives_display_changes_and_copies() {
        let a = LocalRef::fresh("x");
        let renamed = a.with_display("y");
        assert_eq!(a, renamed);
        assert_eq!(a, a.clone());
        assert_eq!(renamed.display(), "y");
        assert_ne!(a, LocalRef::fresh("x"));
        assert_ne!(LocalId::fresh(), LocalId::fresh());
    }

    #[test]
    fn local_and_declaration_identity_are_separate_types() {
        let local = LocalRef::fresh("x");
        let global = DeclRef::fresh("x");
        // The numbers come from one counter, so they cannot coincide either.
        assert_ne!(local.id().index(), global.id().index());
    }

    #[test]
    fn row_helpers_follow_the_binding_not_its_display() {
        let row = LocalRef::fresh("e");
        let operations = row.generated(LocalGeneration::RowOperations);
        assert_eq!(
            operations,
            row.with_display("renamed")
                .generated(LocalGeneration::RowOperations)
        );
        assert_ne!(operations, row.generated(LocalGeneration::RowResults));
        assert_ne!(
            operations,
            LocalRef::fresh("e").generated(LocalGeneration::RowOperations)
        );
    }

    #[test]
    fn generated_declarations_follow_the_owner() {
        let owner = DeclRef::fresh("app::Tree");
        let rec = owner.generated(Generation::Recursion);
        assert_eq!(rec, owner.clone().generated(Generation::Recursion));
        assert_ne!(rec, owner.generated(Generation::Induction));
        assert_ne!(
            rec,
            DeclRef::fresh("app::Tree").generated(Generation::Recursion)
        );
        assert_eq!(rec.display(), "app::Tree::rec");
        assert_eq!(
            owner.generated(Generation::EffectArm).display(),
            "app::Tree@arm"
        );
    }

    #[test]
    fn nested_declarations_are_identified_by_owner_and_position() {
        let owner = DeclRef::fresh("Tree");
        let nested = owner.generated(Generation::Nested(0));
        assert_eq!(nested, owner.generated(Generation::Nested(0)));
        assert_ne!(nested, owner.generated(Generation::Nested(1)));
        assert_ne!(
            nested,
            DeclRef::fresh("Tree").generated(Generation::Nested(0))
        );
        assert_eq!(
            nested.generated(Generation::Recursion),
            owner
                .generated(Generation::Nested(0))
                .generated(Generation::Recursion)
        );
    }

    #[test]
    fn constructor_identity_depends_on_owner_and_position() {
        let first = DeclRef::fresh("app::A");
        let second = DeclRef::fresh("app::B");
        let a = first.constructor(0, "Mk");
        assert_eq!(a, first.constructor(0, "Mk"));
        assert_ne!(a, second.constructor(0, "Mk"));
        assert_ne!(a, first.constructor(1, "Mk"));
        assert_eq!(a.display(), "app::A::Mk");
    }

    #[test]
    fn specialization_is_keyed_and_remembers_its_origin() {
        let effect = DeclRef::fresh("app::catch");
        let a = effect.specialize("Text", "app::catch@Text");
        assert_eq!(a, effect.specialize("Text", "ignored"));
        assert_ne!(a, effect.specialize("Nat", "app::catch@Nat"));
        assert_ne!(a, DeclRef::fresh("app::catch").specialize("Text", "x"));
        assert_eq!(a.origin(), Some(&effect));
        assert_eq!(effect.origin(), None);
    }

    #[test]
    fn selection_identity_is_its_candidate_set() {
        let a = DeclRef::fresh("Same");
        let b = DeclRef::fresh("Same");
        let first = Selection::new("Same", vec![a.clone(), b.clone()]);
        let reordered = Selection::new("Different", vec![b.clone(), a.clone(), a.clone()]);
        assert_eq!(first, reordered);
        assert_ne!(first, Selection::new("Same", vec![a.clone()]));
        assert_eq!(first.candidates().len(), 2);
        assert_eq!(first.choose(|c| *c == a), Some(&a));
        assert_eq!(first.choose(|_| true), None);
        assert_eq!(first.choose(|_| false), None);
    }

    #[test]
    #[should_panic(expected = "a selection needs candidates")]
    fn a_selection_needs_candidates() {
        Selection::new("none", Vec::new());
    }

    #[test]
    fn effect_use_identity_ignores_display() {
        let effect = DeclRef::fresh("app::E");
        let row = LocalRef::fresh("e");
        let a = EffectUse::new(effect.clone(), "Text", vec![row.clone()], false, "E<Text>");
        let b = EffectUse::new(effect.clone(), "Text", vec![row.clone()], false, "other");
        assert_eq!(a, b);
        assert_ne!(
            a,
            EffectUse::new(effect.clone(), "Nat", vec![row.clone()], false, "E<Text>")
        );
        assert_ne!(
            a,
            EffectUse::new(effect.clone(), "Text", vec![row], true, "E<Text>")
        );
        assert_ne!(
            a,
            EffectUse::new(effect, "Text", vec![LocalRef::fresh("e")], false, "E<Text>")
        );
        assert_eq!(Name::from(a.clone()), Name::from(b));
        assert_eq!(Name::from(a).as_str(), "E<Text>");
    }

    #[test]
    fn sorts_need_their_reference_not_their_display() {
        assert_eq!(
            Name::Global(DeclRef::of_sort(SortSymbol::Type(7))).sort_symbol(),
            Some(SortSymbol::Type(7))
        );
        assert_eq!(
            Name::from("Prop").sort_symbol(),
            Some(SortSymbol::Proposition)
        );
        assert_eq!(Name::Global(DeclRef::fresh("Type7")).sort_symbol(), None);
        assert_eq!(Name::Local(LocalRef::fresh("Prop")).sort_symbol(), None);
        assert_eq!(
            DeclRef::of_sort(SortSymbol::Type(0)),
            DeclRef::of_sort(SortSymbol::Type(0))
        );
        assert_eq!(DeclRef::of_sort(SortSymbol::Type(0)).display(), "Type");
        assert_eq!(SortSymbol::parse("Typed"), None);
    }

    #[test]
    fn primitives_are_the_same_in_every_table() {
        let nat = DeclRef::primitive("Nat").expect("a primitive");
        assert_eq!(nat, Declarations::new().reserve("Nat"));
        assert_eq!(nat, Declarations::new().reserve("Nat"));
        assert!(nat.is_primitive("Nat"));
        assert!(!DeclRef::fresh("Nat").is_primitive("Nat"));
        assert!(DeclRef::primitive("List").is_none());
        assert!(nat.id().index() < FIRST_FRESH);
    }

    #[test]
    fn reservation_is_not_visibility() {
        let mut table = Declarations::new();
        let reference = table.reserve("app::f");
        assert!(table.get("app::f").is_none());
        assert_eq!(table.declare("app::f"), Ok(reference.clone()));
        assert_eq!(table.get("app::f"), Some(&reference));
        assert_eq!(table.declare("app::f"), Err(reference));
    }

    #[test]
    fn clones_share_reservations_but_not_visibility() {
        let mut before = Declarations::new();
        let mut branch = before.clone();
        let reference = branch.declare("app::checkpoint").unwrap();
        assert!(before.get("app::checkpoint").is_none());
        assert_eq!(before.reserve("app::checkpoint"), reference);
        assert_ne!(Declarations::new().reserve("app::checkpoint"), reference);
    }

    #[test]
    fn forks_share_visible_names_but_not_reservations() {
        let mut base = Declarations::new();
        let visible = base.declare("std::prelude::Text").unwrap();
        let mut fork = base.fork();
        assert_eq!(fork.get("std::prelude::Text"), Some(&visible));
        let later = fork.reserve("app::later");
        assert_ne!(base.reserve("app::later"), later);
    }

    #[test]
    fn the_same_display_in_two_tables_is_two_declarations() {
        let left = Declarations::new().declare("app::value").unwrap();
        let right = Declarations::new().declare("app::value").unwrap();
        assert_ne!(left, right);
    }

    #[test]
    fn constructors_are_recorded_under_their_owner() {
        let mut table = Declarations::new();
        let owner = table.declare("app::List").unwrap();
        let cons = table.declare_constructor(&owner, 1, "Cons").unwrap();
        assert_eq!(table.get("app::List::Cons"), Some(&cons));
        assert!(table.is_constructor(&cons));
        assert!(!table.is_constructor(&owner));
        assert_eq!(table.declare_constructor(&owner, 1, "Cons"), Err(cons));
        let other = table.declare("app::Tree").unwrap();
        let tree_cons = table.declare_constructor(&other, 1, "Cons").unwrap();
        assert_eq!(table.get("app::Tree::Cons"), Some(&tree_cons));
        assert_ne!(table.get("app::List::Cons"), table.get("app::Tree::Cons"));
    }

    #[test]
    fn a_foreign_reference_does_not_replace_a_visible_name() {
        let mut table = Declarations::new();
        let own = table.declare("app::f").unwrap();
        let foreign = DeclRef::fresh("app::f");
        assert_eq!(table.declare_reference(&foreign), Err(own.clone()));
        assert_eq!(table.get("app::f"), Some(&own));
    }

    #[test]
    fn generated_declarations_become_visible_on_request() {
        let mut table = Declarations::new();
        let owner = table.declare("app::List").unwrap();
        assert!(table.get("app::List::rec").is_none());
        let rec = table
            .declare_generated(&owner, Generation::Recursion)
            .unwrap();
        assert_eq!(table.get("app::List::rec"), Some(&rec));
        assert_eq!(rec, owner.generated(Generation::Recursion));
    }
}
