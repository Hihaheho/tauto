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

fn allocate(next: &AtomicU64) -> u64 {
    next.try_update(Ordering::Relaxed, Ordering::Relaxed, |value| {
        value.checked_add(1)
    })
    .expect("identity space exhausted")
}

fn fresh() -> u64 {
    allocate(&NEXT)
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
    ClassMethod(usize),
    ClassLaw(usize),
    ClassLaws,
    WellFoundedStep,
    WellFoundedEquation,
    OpaqueBody,
    OpaqueEquation,
    SharedStepRequest,
    SharedStepAnswer,
    SharedStepRead,
    SharedStepZero,
    SharedStepGet(usize),
}

impl Generation {
    fn suffix(self) -> String {
        match self {
            Self::EffectOperations => "@op".into(),
            Self::EffectArguments => "@args".into(),
            Self::EffectResult => "@res".into(),
            Self::EffectArm => "@arm".into(),
            Self::ClassMethod(index) => format!("method{index}"),
            Self::ClassLaw(index) => format!("law{index}"),
            Self::ClassLaws => "laws".into(),
            Self::WellFoundedStep => "@step".into(),
            Self::WellFoundedEquation => "eq".into(),
            Self::OpaqueBody => "@body".into(),
            Self::OpaqueEquation => "eq".into(),
            Self::SharedStepRequest => "@request".into(),
            Self::SharedStepAnswer => "@answer".into(),
            Self::SharedStepRead => "@read".into(),
            Self::SharedStepZero => "@zero".into(),
            Self::SharedStepGet(index) => format!("@get{index}"),
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
    source_offset: OnceLock<usize>,
    /// Declarations generated from this one, by kind.
    generated: Mutex<HashMap<Generation, DeclRef>>,
    /// Instances made from this declaration, by their argument key. Weak: an
    /// instance nobody holds is forgotten.
    instances: Mutex<HashMap<String, Weak<Declaration>>>,
    /// The declaration this is an instance of.
    origin: Option<DeclRef>,
    generation: Option<Generation>,
}

impl Declaration {
    fn new(id: u64, display: String, sort: Option<SortSymbol>, origin: Option<DeclRef>) -> Self {
        Self {
            id: DeclId(id),
            display,
            sort,
            source_offset: OnceLock::new(),
            generated: Default::default(),
            instances: Default::default(),
            origin,
            generation: None,
        }
    }
}

/// A reference to a declaration. Equality, ordering and hashing are by
/// [`DeclId`]; clones are the same reference.
#[derive(Clone)]
pub struct DeclRef(Arc<Declaration>, Option<Arc<DeclRef>>);

impl DeclRef {
    /// A new declaration, unequal to every other. `display` is the full name.
    pub fn fresh(display: impl Into<String>) -> Self {
        Self(
            Arc::new(Declaration::new(fresh(), display.into(), None, None)),
            None,
        )
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
        let mut reference = locked(&self.0.generated)
            .entry(kind)
            .or_insert_with(|| {
                let mut declaration = Declaration::new(fresh(), display, None, None);
                declaration.generation = Some(kind);
                Self(Arc::new(declaration), None)
            })
            .clone();
        // A generated reference retains its owner, including specialized
        // ancestors. The owner's cache stores the reference without this
        // back edge, so retaining the owner does not create an Arc cycle.
        reference.1 = Some(Arc::new(self.clone()));
        reference
    }

    /// The constructor at `index` of this type, displayed as `<this>::<leaf>`.
    /// The reference depends on this type and the position, not on the leaf's
    /// spelling: types that have a constructor of the same name do not share
    /// it.
    pub fn constructor(&self, index: usize, leaf: &str) -> Self {
        self.generated_named(Generation::Constructor(index), format!("{self}::{leaf}"))
    }

    /// A class member is owned by its class and its position. Its label is
    /// retained for display and has no part in its identity.
    pub fn class_member(&self, index: usize, law: bool, label: &str) -> Self {
        let kind = if law {
            Generation::ClassLaw(index)
        } else {
            Generation::ClassMethod(index)
        };
        self.generated_named(kind, format!("{self}::{label}"))
    }

    /// The instance of this declaration for the arguments with the canonical
    /// rendering `key`. The same key gives the same reference while any holder
    /// keeps it.
    pub fn specialize(&self, key: &str, display: impl Into<String>) -> Self {
        let mut instances = locked(&self.0.instances);
        if let Some(existing) = instances.get(key).and_then(Weak::upgrade) {
            return Self(existing, None);
        }
        let instance = Self(
            Arc::new(Declaration::new(
                fresh(),
                display.into(),
                None,
                Some(self.clone()),
            )),
            None,
        );
        instances.insert(key.to_string(), Arc::downgrade(&instance.0));
        instance
    }

    /// The declaration this is an instance of, if it is one.
    pub fn origin(&self) -> Option<&DeclRef> {
        self.0.origin.as_ref()
    }

    /// The declaration that generated this member.
    pub fn owner(&self) -> Option<&DeclRef> {
        self.1.as_deref()
    }

    pub fn generation(&self) -> Option<Generation> {
        self.0.generation
    }

    pub fn id(&self) -> DeclId {
        self.0.id
    }

    /// The full name this reference is displayed as.
    pub fn display(&self) -> &str {
        &self.0.display
    }

    /// Retains the boundary before the source spelling in the display name.
    /// The spelling is presentation metadata and does not affect identity.
    pub fn set_source_offset(&self, offset: usize) {
        assert!(self.display().is_char_boundary(offset));
        let _ = self.0.source_offset.set(offset);
    }

    /// The spelling retained when the declaration was bound in its source.
    pub fn source_display(&self) -> &str {
        let offset = self
            .0
            .source_offset
            .get()
            .copied()
            .or_else(|| {
                self.owner().or_else(|| self.origin()).and_then(|owner| {
                    self.display()
                        .starts_with(owner.display())
                        .then(|| owner.display().len() - owner.source_display().len())
                })
            })
            .unwrap_or(0);
        &self.display()[offset..]
    }

    /// The sort this reference is, if it is one.
    pub fn sort(&self) -> Option<SortSymbol> {
        self.0.sort
    }

    /// The reference of a sort. One per sort in the whole process.
    pub fn of_sort(sort: SortSymbol) -> Self {
        static SORTS: OnceLock<Mutex<HashMap<SortSymbol, DeclRef>>> = OnceLock::new();
        locked(SORTS.get_or_init(Default::default))
            .entry(sort)
            .or_insert_with(|| {
                Self(
                    Arc::new(Declaration::new(fresh(), sort.display(), Some(sort), None)),
                    None,
                )
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
                        Self(
                            Arc::new(Declaration::new(i as u64, (*n).into(), None, None)),
                            None,
                        )
                    })
                    .collect()
            })[index]
                .clone(),
        )
    }

    /// Whether this is the primitive spelled `name`.
    pub fn is_primitive(&self, name: &str) -> bool {
        usize::try_from(self.id().index())
            .ok()
            .and_then(|index| PRIMITIVES.get(index))
            .is_some_and(|primitive| *primitive == name)
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

/// A binding generated from another local binding.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum LocalGeneration {
    RowOperations,
    RowResults,
    InductionHypothesis(usize),
}

/// A lexical binding. Copies and display changes preserve its identity.
#[derive(Clone)]
pub struct LocalRef(Arc<LocalBinding>);

struct LocalBinding {
    id: LocalId,
    display: String,
    generated: Arc<Mutex<HashMap<LocalGeneration, LocalRef>>>,
    origin: Option<LocalRef>,
}

impl LocalRef {
    pub fn fresh(display: impl Into<String>) -> Self {
        Self(Arc::new(LocalBinding {
            id: LocalId::fresh(),
            display: display.into(),
            generated: Default::default(),
            origin: None,
        }))
    }

    /// The same binding displayed otherwise.
    pub fn with_display(&self, display: impl Into<String>) -> Self {
        Self(Arc::new(LocalBinding {
            id: self.id(),
            display: display.into(),
            generated: self.0.generated.clone(),
            origin: self.0.origin.clone(),
        }))
    }

    /// A fresh binder derived from this binder by capture-avoiding renaming.
    pub fn freshened(&self, display: impl Into<String>) -> Self {
        Self(Arc::new(LocalBinding {
            id: LocalId::fresh(),
            display: display.into(),
            generated: Default::default(),
            origin: Some(self.clone()),
        }))
    }

    pub fn origin(&self) -> Option<&LocalRef> {
        self.0.origin.as_ref()
    }

    /// The binding generated from this one. All displays of one binding share
    /// the generated bindings.
    pub fn generated(&self, kind: LocalGeneration) -> Self {
        let suffix = match kind {
            LocalGeneration::RowOperations => "rowop".to_owned(),
            LocalGeneration::RowResults => "rowres".to_owned(),
            LocalGeneration::InductionHypothesis(index) => format!("ih{index}"),
        };
        locked(&self.0.generated)
            .entry(kind)
            .or_insert_with(|| Self::fresh(format!("{}@{suffix}", self.display())))
            .clone()
    }

    pub fn id(&self) -> LocalId {
        self.0.id
    }

    pub fn display(&self) -> &str {
        &self.0.display
    }
}

impl PartialEq for LocalRef {
    fn eq(&self, other: &Self) -> bool {
        self.id() == other.id()
    }
}
impl Eq for LocalRef {}
impl Hash for LocalRef {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.id().hash(state);
    }
}
impl PartialOrd for LocalRef {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}
impl Ord for LocalRef {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.id().cmp(&other.id())
    }
}
impl std::fmt::Debug for LocalRef {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "LocalRef({}#{})", self.display(), self.id().0)
    }
}
impl std::fmt::Display for LocalRef {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(self.display())
    }
}

/// A finite, non-empty set of declarations awaiting a choice that needs a
/// type. Its identity includes the candidates and any bare-pattern local
/// binding; the display is only for diagnostics.
#[derive(Debug, Clone)]
pub struct Selection(Arc<SelectionData>);

#[derive(Debug, Clone)]
struct SelectionData {
    display: String,
    candidates: Vec<DeclRef>,
    binding: Option<LocalRef>,
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
        Self(Arc::new(SelectionData {
            display: display.into(),
            candidates,
            binding: None,
        }))
    }

    /// A bare pattern may bind a local when the selected constructor has fields.
    /// The fallback belongs to this occurrence and never comes from its display.
    pub fn with_binding(mut self, binding: LocalRef) -> Self {
        Arc::make_mut(&mut self.0).binding = Some(binding);
        self
    }

    pub fn binding(&self) -> Option<&LocalRef> {
        self.0.binding.as_ref()
    }

    pub fn candidates(&self) -> &[DeclRef] {
        &self.0.candidates
    }

    pub fn display(&self) -> &str {
        &self.0.display
    }

    /// The only candidate that `accepts`, if exactly one does.
    pub fn choose(&self, mut accepts: impl FnMut(&DeclRef) -> bool) -> Option<&DeclRef> {
        let mut chosen = self.0.candidates.iter().filter(|c| accepts(c));
        let first = chosen.next()?;
        chosen.next().is_none().then_some(first)
    }
}

impl PartialEq for Selection {
    fn eq(&self, other: &Self) -> bool {
        self.0.candidates == other.0.candidates && self.0.binding == other.0.binding
    }
}
impl Eq for Selection {}
impl Hash for Selection {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.0.candidates.hash(state);
        self.0.binding.hash(state);
    }
}
impl PartialOrd for Selection {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}
impl Ord for Selection {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.0
            .candidates
            .cmp(&other.0.candidates)
            .then_with(|| self.0.binding.cmp(&other.0.binding))
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

/// The display contract of an applied effect carried by a reference.
pub trait EffectReference: Clone + std::fmt::Debug + Eq + Hash + Ord {
    fn display(&self) -> &str;
}

impl EffectReference for EffectUse {
    fn display(&self) -> &str {
        self.display()
    }
}

/// References without a source-language syntax payload.
pub type Name = ReferenceName<EffectUse>;

/// A name before resolution, or the reference it resolves to. A reference is
/// never equal to a spelling with the same display, and the variants are never
/// equal to one another.
#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum ReferenceName<E: EffectReference> {
    /// As written; not yet resolved.
    Spelled(String),
    /// A declaration.
    Global(DeclRef),
    /// A lexical binding.
    Local(LocalRef),
    /// Candidates awaiting a type-directed choice.
    Selection(Selection),
    /// An effect applied to its arguments.
    Effect(Arc<E>),
}

impl<E: EffectReference> ReferenceName<E> {
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

    /// The source spelling, only before binding.
    pub fn spelling(&self) -> Option<&str> {
        match self {
            Self::Spelled(n) => Some(n),
            _ => None,
        }
    }

    /// Edit source syntax without altering a resolved reference.
    pub fn spelling_mut(&mut self) -> Option<&mut String> {
        match self {
            Self::Spelled(n) => Some(n),
            _ => None,
        }
    }

    pub fn edit_spelling(&mut self, edit: impl FnOnce(&mut String)) {
        if let Self::Spelled(text) = self {
            edit(text);
        }
    }

    /// A lexical row occurrence, without using a resolved reference's display.
    pub fn row_variable(&self) -> Option<Self> {
        match self {
            Self::Local(_) => Some(self.clone()),
            Self::Spelled(text) => text.strip_prefix('|').map(Self::from),
            Self::Global(_) | Self::Selection(_) | Self::Effect(_) => None,
        }
    }

    /// Use this binding in a row; a resolved binding keeps its identity.
    pub fn in_row(&self) -> Self {
        match self {
            Self::Spelled(text) => Self::Spelled(format!("|{text}")),
            _ => self.clone(),
        }
    }

    pub fn display_in_row(&self) -> String {
        match self {
            Self::Local(_) => format!("|{self}"),
            _ => self.to_string(),
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

impl<E: EffectReference> std::ops::Deref for ReferenceName<E> {
    type Target = str;
    fn deref(&self) -> &str {
        self.as_str()
    }
}
impl<E: EffectReference> AsRef<str> for ReferenceName<E> {
    fn as_ref(&self) -> &str {
        self.as_str()
    }
}

impl<E: EffectReference> std::fmt::Display for ReferenceName<E> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(self.as_str())
    }
}
impl<E: EffectReference> Default for ReferenceName<E> {
    fn default() -> Self {
        Self::Spelled(String::new())
    }
}
impl<E: EffectReference> From<&&ReferenceName<E>> for ReferenceName<E> {
    fn from(value: &&ReferenceName<E>) -> Self {
        (*value).clone()
    }
}
impl<E: EffectReference> From<&ReferenceName<E>> for ReferenceName<E> {
    fn from(value: &ReferenceName<E>) -> Self {
        value.clone()
    }
}

impl<E: EffectReference> From<&String> for ReferenceName<E> {
    fn from(value: &String) -> Self {
        Self::Spelled(value.clone())
    }
}

impl<E: EffectReference> From<String> for ReferenceName<E> {
    fn from(value: String) -> Self {
        Self::Spelled(value)
    }
}
impl<E: EffectReference> From<&str> for ReferenceName<E> {
    fn from(value: &str) -> Self {
        Self::Spelled(value.into())
    }
}
impl<E: EffectReference> From<DeclRef> for ReferenceName<E> {
    fn from(value: DeclRef) -> Self {
        Self::Global(value)
    }
}
impl<E: EffectReference> From<LocalRef> for ReferenceName<E> {
    fn from(value: LocalRef) -> Self {
        Self::Local(value)
    }
}
impl<E: EffectReference> From<Selection> for ReferenceName<E> {
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
    fn class_members_are_owned_by_class_kind_and_position() {
        let first = DeclRef::fresh("C");
        let second = DeclRef::fresh("C");
        let method = first.class_member(0, false, "read");
        assert_eq!(method, first.class_member(0, false, "renamed"));
        assert_ne!(method, first.class_member(1, false, "read"));
        assert_ne!(method, first.class_member(0, true, "read"));
        assert_ne!(method, second.class_member(0, false, "read"));
        assert_ne!(method, first.generated(Generation::ClassLaws));
    }

    #[test]
    fn exhaustion_does_not_reuse_identity_numbers_after_a_caught_panic() {
        let next = AtomicU64::new(u64::MAX - 1);
        assert_eq!(allocate(&next), u64::MAX - 1);
        for _ in 0..2 {
            assert!(std::panic::catch_unwind(|| allocate(&next)).is_err());
            assert_eq!(next.load(Ordering::Relaxed), u64::MAX);
        }
    }

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
    fn induction_hypotheses_follow_the_field_binding() {
        let field = LocalRef::fresh("tail");
        let kind = LocalGeneration::InductionHypothesis(0);
        let hypothesis = field.generated(kind);
        assert_eq!(hypothesis, field.with_display("renamed").generated(kind));
        assert_ne!(
            hypothesis,
            field.generated(LocalGeneration::InductionHypothesis(1))
        );
        assert_ne!(hypothesis, LocalRef::fresh("tail").generated(kind));
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
    fn generated_reference_retains_specialized_ancestors() {
        let family = DeclRef::fresh("Family");
        let instance = family.specialize("level:1", "Family@1");
        let weak = Arc::downgrade(&instance.0);
        let constructor = instance.constructor(0, "Mk");
        let generated = constructor.generated(Generation::Equality);
        drop(constructor);
        drop(instance);
        let kept = family.specialize("level:1", "Family@1");
        assert!(weak.upgrade().is_some());
        assert_eq!(
            generated,
            kept.constructor(0, "Mk").generated(Generation::Equality)
        );
        drop(kept);
        drop(generated);
        assert!(weak.upgrade().is_none());
    }

    #[test]
    fn references_share_payloads_and_keep_names_compact() {
        assert!(std::mem::size_of::<Name>() <= 4 * std::mem::size_of::<usize>());
        let local = LocalRef::fresh("binding");
        assert!(Arc::ptr_eq(&local.0, &local.clone().0));
        let selection = Selection::new("candidate", vec![DeclRef::fresh("candidate")]);
        assert!(Arc::ptr_eq(&selection.0, &selection.clone().0));
        let bound = selection.clone().with_binding(local.clone());
        assert_eq!(bound.binding(), Some(&local));
        assert!(selection.binding().is_none());
    }

    #[test]
    fn pattern_selections_keep_distinct_local_bindings() {
        let constructor = DeclRef::fresh("Same");
        let first_binding = LocalRef::fresh("Same");
        let first =
            Selection::new("Same", vec![constructor.clone()]).with_binding(first_binding.clone());
        let second =
            Selection::new("Same", vec![constructor.clone()]).with_binding(LocalRef::fresh("Same"));
        assert_ne!(first, second);
        assert_eq!(first.binding(), Some(&first_binding));
        assert_eq!(
            first,
            Selection::new("Other", vec![constructor]).with_binding(first_binding)
        );
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
        let proposition = DeclRef::of_sort(SortSymbol::Proposition);
        let largest_type = DeclRef::of_sort(SortSymbol::Type(u32::MAX));
        assert_ne!(proposition, largest_type);
        assert_eq!(
            Name::Global(largest_type).sort_symbol(),
            Some(SortSymbol::Type(u32::MAX))
        );
        assert_eq!(
            Name::Global(proposition).sort_symbol(),
            Some(SortSymbol::Proposition)
        );
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
    fn freshening_retains_the_original_binding_independently_of_display() {
        let original = LocalRef::fresh("value");
        let renamed = original.freshened("unrelated");
        assert_ne!(renamed, original);
        assert_eq!(renamed.origin(), Some(&original));
        assert_eq!(renamed.with_display("value'1").origin(), Some(&original));
        assert_eq!(LocalRef::fresh("value'1").origin(), None);
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
        for name in PRIMITIVES {
            let primitive = DeclRef::primitive(name).unwrap();
            for candidate in PRIMITIVES {
                assert_eq!(primitive.is_primitive(candidate), name == candidate);
            }
            assert!(!DeclRef::fresh(*name).is_primitive(name));
        }
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
    #[test]
    fn source_edits_cannot_rewrite_resolved_references() {
        let global = Name::Global(DeclRef::fresh("value"));
        let local = Name::Local(LocalRef::fresh("value"));
        for original in [global, local] {
            let mut edited = original.clone();
            edited.edit_spelling(|_| panic!("resolved name exposed as editable source"));
            assert!(edited.spelling_mut().is_none());
            assert_eq!(edited, original);
            assert_eq!(Name::from(&edited), original);
        }
        let mut source = Name::from("value");
        source.edit_spelling(|text| *text = "module::value".into());
        assert_eq!(source.spelling(), Some("module::value"));
    }

    #[test]
    fn row_occurrences_keep_local_identity() {
        let local = Name::Local(LocalRef::fresh("row"));
        assert_eq!(local.in_row().row_variable(), Some(local.clone()));
        assert_ne!(local, Name::Local(LocalRef::fresh("row")));
        assert_eq!(local.display_in_row(), "|row");
        assert_eq!(
            Name::from("row").in_row().row_variable(),
            Some(Name::from("row"))
        );
        assert!(
            Name::Global(DeclRef::fresh("|row"))
                .row_variable()
                .is_none()
        );
    }
}

/// `text` (the `Debug` of something that holds references) with the numbers of the references (`LocalRef(a#148223)`,
/// `DeclRef(f#12)`) numbered in the order they appear: a load gives every
/// binder a number from a counter of the whole process, so the same
/// statement read again has other ones.
pub fn refs_in_order(text: &str) -> String {
    let mut seen: std::collections::HashMap<String, usize> = std::collections::HashMap::new();
    let mut out = String::with_capacity(text.len());
    let mut rest = text;
    // One pass: each `Ref(` found is looked at once (looking for each prefix
    // from every reference would read the rest of the text again each time).
    let mut from = 0;
    loop {
        let Some(r) = rest[from..].find("Ref(").map(|r| from + r) else {
            break;
        };
        let (i, len) = if rest[..r].ends_with("Local") {
            (r - 5, 9)
        } else if rest[..r].ends_with("Decl") {
            (r - 4, 8)
        } else {
            from = r + 4;
            continue;
        };
        from = 0;
        let start = i + len;
        out.push_str(&rest[..start]);
        let after = &rest[start..];
        let Some(close) = after.find(')') else {
            rest = after;
            break;
        };
        let inner = &after[..close];
        match inner.rfind('#') {
            Some(h) if h + 1 < inner.len() && inner[h + 1..].bytes().all(|b| b.is_ascii_digit()) => {
                let key = format!("{}{inner}", &rest[i..start]);
                let n = seen.len();
                let n = *seen.entry(key).or_insert(n);
                out.push_str(&format!("{}#{n}", &inner[..h]));
            }
            _ => out.push_str(inner),
        }
        rest = &after[close..];
    }
    out.push_str(rest);
    out
}

#[cfg(test)]
mod refs_tests {
    use super::refs_in_order;

    #[test]
    fn references_are_numbered_in_the_order_they_appear() {
        let a = "App(LocalRef(a#148223), DeclRef(f#9), LocalRef(b#148224), LocalRef(a#148223))";
        let b = "App(LocalRef(a#270296), DeclRef(f#31), LocalRef(b#270297), LocalRef(a#270296))";
        assert_eq!(refs_in_order(a), refs_in_order(b));
        assert_eq!(
            refs_in_order(a),
            "App(LocalRef(a#0), DeclRef(f#1), LocalRef(b#2), LocalRef(a#0))"
        );
        // Two binders stay two.
        assert_ne!(
            refs_in_order("LocalRef(a#1) LocalRef(a#2)"),
            refs_in_order("LocalRef(a#1) LocalRef(a#1)")
        );
    }

}
