//! The core kernel: every declaration the named checker accepts is checked
//! again here, over locally nameless terms, before it is added, with no
//! exception: a term read from the proof cache (`cache.rs`) is checked here
//! as any other is, so the cache is outside the trusted base.
//!
//! The named checker (`check.rs`) elaborates surface terms whose global and
//! local references have distinct identities. This module reads local IDs as
//! de Bruijn indices, and open context variables as fresh atoms. Global IDs
//! identify constants in the accepted declaration environment; neither binder
//! hints nor declaration displays participate in lookup. The core has
//! its own reading of an inductive declaration (strict
//! positivity, uniform parameters, universes, large elimination, the
//! eliminators and their iota rule). A declaration is added only if both
//! accept it.
//!
//! Typing, reduction and conversion are only here: while it elaborates, the
//! named checker asks the core for the type of a term or whether it has one
//! (`type_in`, which says where a term does not type and which holes it
//! met), a weak head normal form, convertibility or subtyping in its context
//! (`whnf_in`, `conv_in`, `subtype_in`).

use crate::surface::Name;
use std::collections::{HashMap, HashSet};
use std::sync::{Arc, Weak};

use super::derivation::{Derivation, InferenceRule};
use super::num::Num;
use super::{Ctx, Sort, T, sort_named, sort_term};
use crate::surface::TermKind;
use tauto_message::{Message, msg};
use tauto_surface::identity::DeclRef;

/// Source spellings used at the named-to-core boundary. This index is not
/// evidence of acceptance; only entries in `Core::globals` have a checked type.
#[derive(Clone, Default)]
struct SourceNames(tauto_identity::ForkedMap<String, DeclRef>);

impl SourceNames {
    fn reserve(&mut self, name: &str) -> DeclRef {
        self.0
            .entry(name.into())
            .or_insert_with(|| DeclRef::primitive(name).unwrap_or_else(|| DeclRef::fresh(name)))
            .clone()
    }

    fn get(&self, name: &str) -> Option<&DeclRef> {
        self.0.get(name)
    }
    fn reference<'a>(&'a self, name: &'a Name) -> Option<&'a DeclRef> {
        match name {
            Name::Global(reference) => Some(reference),
            Name::Spelled(spelling) => self.get(spelling),
            _ => None,
        }
    }
    fn register(&mut self, name: &Name) -> DeclRef {
        match name {
            Name::Global(reference) => reference.clone(),
            Name::Spelled(spelling) => self.reserve(spelling),
            _ => panic!("a core declaration requires a global reference"),
        }
    }
    fn generated(&mut self, owner: &Name, kind: tauto_surface::identity::Generation) -> DeclRef {
        let owner = self.register(owner);
        let reference = owner.generated(kind);
        if self.get(owner.display()) == Some(&owner) {
            self.0.insert(reference.display().into(), reference.clone());
        }
        reference
    }
}

type R = Arc<Tm>;

#[derive(Debug, Clone, Eq, Hash)]
pub(super) enum Tm {
    /// A variable bound by an enclosing `Pi` or `Lam`, counted outwards.
    BVar(usize),
    /// A variable of the context (an atom).
    FVar(u64),
    Sort(Sort),
    Const(DeclRef),
    /// The binder's name is only shown (see [`Hint`]).
    Pi(Hint, R, R),
    Lam(Hint, R),
    App(R, R),
    Lit(Num),
}

/// Structural equality, hints aside. Terms share their nodes (reducing
/// `x * 2` gives `x * 1 + x` with one `x`), so the same pair of nodes can be
/// met many times: walking the tree the nodes make, as a derived equality
/// does, can take time exponential in the size of the terms. Here each pair of
/// nodes is compared once, and a node is equal to itself at once.
impl PartialEq for Tm {
    fn eq(&self, other: &Tm) -> bool {
        // Small terms are compared without keeping the pairs met.
        const KEEP_AFTER: usize = 64;
        let mut steps = 0;
        // Keyed by addresses, as the node tables are (`AddrHasher`).
        let mut seen: HashSet<(*const Tm, *const Tm), AddrBuild> = HashSet::default();
        let mut todo: Vec<(&Tm, &Tm)> = vec![(self, other)];
        while let Some((a, b)) = todo.pop() {
            if std::ptr::eq(a, b) {
                continue;
            }
            steps += 1;
            if steps > KEEP_AFTER && matches!(a, App(..) | Pi(..) | Lam(..)) && !seen.insert((a, b))
            {
                continue;
            }
            match (a, b) {
                (BVar(x), BVar(y)) if x == y => {}
                (FVar(x), FVar(y)) if x == y => {}
                (Sort(x), Sort(y)) if x == y => {}
                (Const(x), Const(y)) if x == y => {}
                (Lit(x), Lit(y)) if x == y => {}
                (Pi(_, x, y), Pi(_, z, w)) => {
                    todo.push((y, w));
                    todo.push((x, z));
                }
                // The argument is compared first: two applications of an
                // eliminator that differ mostly differ in the value it is
                // applied to, which is the last argument, while the cases
                // before it can be large copies of the same terms.
                (App(x, y), App(z, w)) => {
                    todo.push((x, z));
                    todo.push((y, w));
                }
                (Lam(_, x), Lam(_, y)) => todo.push((x, y)),
                _ => return false,
            }
        }
        true
    }
}

/// The source binder retained for writing terms and hole contexts back to
/// the surface. It does not participate in type checking or conversion:
/// two terms that differ only in their hints are the same term.
#[derive(Debug, Clone)]
pub(super) struct Hint(Option<Name>);

impl Hint {
    fn none() -> Self {
        Hint(None)
    }

    fn named(n: impl Into<Name>) -> Self {
        let n = n.into();
        Hint((n.as_str() != "_").then_some(n))
    }
}

impl PartialEq for Hint {
    fn eq(&self, _: &Hint) -> bool {
        true
    }
}

impl Eq for Hint {}

impl std::hash::Hash for Hint {
    fn hash<H: std::hash::Hasher>(&self, _: &mut H) {}
}

use Tm::*;

#[cfg(feature = "selfhost")]
#[path = "selfhost.rs"]
pub mod selfhost;

/// Dropped along the applications in a loop: a list literal, or a text
/// literal's bytes, nests through them once per element, and the drop the
/// compiler writes would recurse as deep.
impl Drop for Tm {
    fn drop(&mut self) {
        thread_local! {
            static LEAF: R = Arc::new(Lit(Num::ZERO));
        }
        // The parts of an application this drop would free: those no other
        // term shares. A shared part only loses a count.
        fn take(t: &mut Tm, next: &mut Vec<R>) {
            if let App(f, a) = t {
                for r in [f, a] {
                    // While the thread is ending, the drop is the compiler's.
                    if Arc::strong_count(r) == 1
                        && matches!(**r, App(..))
                        && let Ok(leaf) = LEAF.try_with(Arc::clone)
                    {
                        next.push(std::mem::replace(r, leaf));
                    }
                }
            }
        }
        let mut next = Vec::new();
        take(self, &mut next);
        while let Some(r) = next.pop() {
            poll_deadline();
            if let Ok(mut t) = Arc::try_unwrap(r) {
                take(&mut t, &mut next);
            }
        }
    }
}

impl Tm {
    fn pi_parts(&self) -> Option<(Hint, R, R)> {
        match self {
            Pi(h, a, b) => Some((h.clone(), a.clone(), b.clone())),
            _ => None,
        }
    }
}

fn app(f: Tm, a: Tm) -> Tm {
    App(Arc::new(f), Arc::new(a))
}

fn apps(f: Tm, args: impl IntoIterator<Item = Tm>) -> Tm {
    args.into_iter().fold(f, app)
}

/// The definitions of the prelude the core computes on numerals ([`Core::numeric`]).
const NUMERIC: &[&str] = &[
    "Nat::eq",
    "Nat::lt",
    "Nat::sub",
    "Nat::div_nz",
    "Nat::rem_nz",
];

/// How many arguments a [`NUMERIC`] definition takes: `Nat::div_nz` and
/// `Nat::rem_nz` take the proof that the divisor is not 0 after the two
/// numbers, and compute without looking at it.
fn numeric_arity(c: &str) -> usize {
    match c {
        "Nat::div_nz" | "Nat::rem_nz" => 3,
        _ => 2,
    }
}

/// `x op y` on two numerals, or `None` past the largest numeral.
fn lit_op(op: &str, x: Num, y: Num) -> Option<Num> {
    match op {
        "+" => x.checked_add(y),
        "*" => x.checked_mul(y),
        _ => Some(x.saturating_sub(y)),
    }
}

/// One step of [`Core::conv_nodes`]: the answer, or the pair of nodes whose
/// answer it is.
enum Conv {
    Is(bool),
    Below(R, R),
}

fn primitive_operator(reference: &DeclRef) -> Option<&'static str> {
    ["+", "*", "-"]
        .into_iter()
        .find(|name| reference.is_primitive(name))
}

fn konst(n: &str) -> Tm {
    Const(DeclRef::primitive(n).expect("core builtin reference"))
}

/// `t` with the variable bound at depth `d` replaced by the locally closed `v`.
/// Indices inside `v` refer only to its own binders, so no shifting is needed.
/// A part that does not change is shared with `t`, not copied.
fn inst_at(t: &Tm, d: usize, v: &Tm) -> Tm {
    inst_at_rc(t, d, &Arc::new(v.clone()))
}

/// [`inst_at`] with `v` shared: every place the variable was is the same
/// node, so what reducing it gives is found again (`Core::whnf_shared`).
fn inst_at_rc(t: &Tm, d: usize, v: &R) -> Tm {
    inst_tm(t, d, v).unwrap_or_else(|| t.clone())
}

/// `None` when `t` does not change.
fn inst_tm(t: &Tm, d: usize, v: &R) -> Option<Tm> {
    poll_deadline();
    match t {
        BVar(i) if *i == d => Some((**v).clone()),
        BVar(i) if *i > d => Some(BVar(i - 1)),
        Pi(h, a, b) => {
            let (a2, b2) = (inst_rc(a, d, v), inst_rc(b, d + 1, v));
            share2(a, b, a2, b2).map(|(a, b)| Pi(h.clone(), a, b))
        }
        Lam(h, b) => inst_rc(b, d + 1, v).map(|b| Lam(h.clone(), b)),
        App(f, a) => {
            let (f2, a2) = (inst_rc(f, d, v), inst_rc(a, d, v));
            share2(f, a, f2, a2).map(|(f, a)| App(f, a))
        }
        BVar(_) | FVar(_) | Sort(_) | Const(_) | Lit(_) => None,
    }
}

fn inst_rc(t: &R, d: usize, v: &R) -> Option<R> {
    match &**t {
        BVar(i) if *i == d => Some(v.clone()),
        BVar(_) => inst_tm(t, d, v).map(Arc::new),
        Pi(..) | Lam(..) | App(..) if loose(t) <= d => None,
        _ => inst_tm(t, d, v).map(Arc::new),
    }
}

/// `t` with the variables bound at depths `d .. d + vals.len()` replaced
/// at once by the locally closed `vals`, the first of them outermost: the
/// variable at depth `d + i` becomes `vals[vals.len() - 1 - i]`, and a
/// variable bound further out loses `vals.len()`. It is the term that
/// [`inst_at`] gives when the values are put in one at a time, the first
/// outermost at depth `d + vals.len() - 1` and the last at `d`, but it walks
/// `t` once instead of once per value: the type of a function applied to
/// many arguments is a telescope, and putting each argument into the whole
/// rest of it in turn walks the telescope once per argument. A part that does
/// not change is shared with `t`, and every place a value goes is that value's
/// node, as with [`inst_at_rc`].
fn inst_env(t: &R, d: usize, vals: &[R]) -> R {
    if vals.is_empty() {
        return t.clone();
    }
    inst_env_rc(t, d, vals).unwrap_or_else(|| t.clone())
}

/// `None` when `t` does not change.
fn inst_env_tm(t: &Tm, d: usize, vals: &[R]) -> Option<Tm> {
    poll_deadline();
    let n = vals.len();
    match t {
        BVar(i) if *i >= d && *i < d + n => Some((*vals[n - 1 - (i - d)]).clone()),
        BVar(i) if *i >= d + n => Some(BVar(i - n)),
        Pi(h, a, b) => {
            let (a2, b2) = (inst_env_rc(a, d, vals), inst_env_rc(b, d + 1, vals));
            share2(a, b, a2, b2).map(|(a, b)| Pi(h.clone(), a, b))
        }
        Lam(h, b) => inst_env_rc(b, d + 1, vals).map(|b| Lam(h.clone(), b)),
        App(f, a) => {
            let (f2, a2) = (inst_env_rc(f, d, vals), inst_env_rc(a, d, vals));
            share2(f, a, f2, a2).map(|(f, a)| App(f, a))
        }
        BVar(_) | FVar(_) | Sort(_) | Const(_) | Lit(_) => None,
    }
}

fn inst_env_rc(t: &R, d: usize, vals: &[R]) -> Option<R> {
    let n = vals.len();
    match &**t {
        BVar(i) if *i >= d && *i < d + n => Some(vals[n - 1 - (i - d)].clone()),
        BVar(_) => inst_env_tm(t, d, vals).map(Arc::new),
        Pi(..) | Lam(..) | App(..) if loose(t) <= d => None,
        _ => inst_env_tm(t, d, vals).map(Arc::new),
    }
}

/// The names reduced on the way to a comparison (`Core::conv_unfolded`),
/// in the order they were met, each with the binders gone under where it
/// was. For each name the least of those binders so far is kept too, so
/// that whether it was met outside the binders in hand (`Core::conv_cut`)
/// is one look. Scanning the list instead takes as long as the list, and a
/// comparison down a stuck chain `n` long meets the eliminator once per
/// link: `n` scans of up to `n` entries.
#[derive(Clone, Default)]
struct Unfolded {
    met: Vec<DeclRef>,
    /// For each name, the least binders among its first `k` entries, for
    /// each `k`.
    least: HashMap<DeclRef, Vec<usize>>,
}

impl Unfolded {
    fn len(&self) -> usize {
        self.met.len()
    }

    fn push(&mut self, (f, at): (DeclRef, usize)) {
        let least = self.least.entry(f.clone()).or_default();
        least.push(least.last().map_or(at, |&l| l.min(at)));
        self.met.push(f);
    }

    fn truncate(&mut self, len: usize) {
        while self.met.len() > len {
            let f = self.met.pop().unwrap();
            if let Some(least) = self.least.get_mut(&f) {
                least.pop();
                if least.is_empty() {
                    self.least.remove(&f);
                }
            }
        }
    }

    /// Whether `f` was met under fewer binders than `binders`.
    fn below(&self, f: &DeclRef, binders: usize) -> bool {
        self.least
            .get(f)
            .and_then(|l| l.last())
            .is_some_and(|&l| l < binders)
    }
}

thread_local! {
    /// The deadline of the declaration being checked (`Core::start_budget`),
    /// for the loops that run without taking a step of reduction.
    static DEADLINE: std::cell::Cell<Option<crate::clock::Instant>> = const { std::cell::Cell::new(None) };
    /// How often [`poll_deadline`] was called, to read the clock only now and then.
    static POLLS: std::cell::Cell<u32> = const { std::cell::Cell::new(0) };
    /// Whether [`poll_deadline`] saw the deadline pass.
    static PASSED: std::cell::Cell<bool> = const { std::cell::Cell::new(false) };
}

/// Notes the passing of the deadline from a loop that takes no step of
/// reduction (copying or substituting in a term, dropping one, reading a
/// numeral), which [`Core::spend`] would never count. It only records the
/// fact: it changes no term and no table. `Core::spend` and
/// `Core::timed_out` then end the reduction the way a deadline reached by
/// counting steps does (`budget.out`), so the declaration is rejected with
/// the existing budget error. Without a deadline, or before it, nothing
/// happens, so no result is different.
fn poll_deadline() {
    let n = POLLS.with(|p| {
        let n = p.get().wrapping_add(1);
        p.set(n);
        n
    });
    if n % 1024 == 0
        && let Some(d) = DEADLINE.with(|d| d.get())
        && crate::clock::Instant::now() >= d
    {
        PASSED.with(|p| p.set(true));
    }
}

/// A hasher for the tables keyed by a node's address (a `usize`), and for
/// those keyed by a declaration or an atom, which hash as one number (a
/// declaration's id, an atom's index) and are looked up at each step of
/// reduction. Only
/// `HashMap` lookups use it: a table's answers do not depend on how its keys
/// are hashed (the hash only chooses where a key is stored, and equal keys
/// always hash alike), so swapping the hasher changes how fast the table is,
/// never what it holds or returns. It multiplies the key by an odd constant
/// and folds the well-mixed high bits of the product into the low ones;
/// addresses are aligned, so their low bits alone would collide.
/// Nothing reads these tables in the order of their entries.
#[derive(Default, Clone, Copy)]
struct AddrHasher(u64);

impl std::hash::Hasher for AddrHasher {
    fn finish(&self) -> u64 {
        self.0 ^ (self.0 >> 32)
    }

    fn write(&mut self, bytes: &[u8]) {
        for b in bytes {
            self.write_u64(*b as u64);
        }
    }

    fn write_usize(&mut self, n: usize) {
        self.write_u64(n as u64);
    }

    fn write_u64(&mut self, n: u64) {
        self.0 = (self.0 ^ n).wrapping_mul(0x9E37_79B9_7F4A_7C15);
    }
}

type AddrBuild = std::hash::BuildHasherDefault<AddrHasher>;

/// A table of nodes by address, held weakly (see [`sweep`]).
#[derive(Clone)]
struct NodeTable<V> {
    entries: HashMap<usize, (Weak<Tm>, V), AddrBuild>,
    /// The size at which [`sweep`] next looks for the entries whose node is gone.
    sweep_at: usize,
}

/// The number of entries from which a table a declaration filled is
/// dropped on a thread of its own ([`drop_aside`]).
const DROP_ASIDE_FROM: usize = 1 << 16;

/// Drops what reducing a declaration remembered (`Core::shared`). A table
/// of a long reduction holds as many nodes as it took steps, and freeing
/// them takes seconds after the declaration's answer, also when it is
/// "out of time": a declaration stopped at its deadline went on that long
/// past it. A large table is freed on another thread, which changes no
/// answer: the nodes are unreachable once taken out. Where no thread can be
/// started (a check in a browser) it is freed here.
fn drop_aside(table: NodeTable<Tm>) {
    if table.entries.len() < DROP_ASIDE_FROM {
        return;
    }
    // Where the thread does not start, the table is freed with the
    // closure that held it.
    #[cfg(not(target_arch = "wasm32"))]
    let _ = std::thread::Builder::new()
        .name("tauto-kernel-drop".into())
        .spawn(move || drop(table));
}

/// The size of a [`NodeTable`] below which [`sweep`] does not run.
const SWEEP_FROM: usize = 4096;

impl<V> Default for NodeTable<V> {
    fn default() -> Self {
        NodeTable {
            entries: HashMap::default(),
            sweep_at: SWEEP_FROM,
        }
    }
}

impl<V> std::ops::Deref for NodeTable<V> {
    type Target = HashMap<usize, (Weak<Tm>, V), AddrBuild>;

    fn deref(&self) -> &Self::Target {
        &self.entries
    }
}

impl<V> std::ops::DerefMut for NodeTable<V> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.entries
    }
}

impl<V> NodeTable<V> {
    fn clear(&mut self) {
        self.entries.clear();
        self.sweep_at = SWEEP_FROM;
    }
}

thread_local! {
    /// [`loose`] of the nodes seen, by address. Each entry holds a weak
    /// reference to its node, so the address is not reused while the entry
    /// is there.
    static LOOSE: std::cell::RefCell<NodeTable<usize>> = Default::default();
}

/// One more than the largest index of a variable `t` leaves unbound (0 when
/// it leaves none). A substitution at a depth at or above it changes
/// nothing in `t`, so it is not walked again.
fn loose(t: &R) -> usize {
    // A node without parts is read at once: keeping it in the table would
    // cost more than reading it, and leaves are about half of the nodes.
    match &**t {
        BVar(i) => i + 1,
        FVar(_) | Sort(_) | Const(_) | Lit(_) => 0,
        Pi(..) | Lam(..) | App(..) => LOOSE.with(|m| {
            // The table is taken once for the whole walk, not at each node.
            let mut m = m.borrow_mut();
            let n = loose_in(&mut m, t);
            sweep(&mut m);
            n
        }),
    }
}

/// [`loose`] with the table in hand.
fn loose_in(m: &mut NodeTable<usize>, t: &R) -> usize {
    let part = |m: &mut NodeTable<usize>, r: &R| match &**r {
        BVar(i) => i + 1,
        FVar(_) | Sort(_) | Const(_) | Lit(_) => 0,
        Pi(..) | Lam(..) | App(..) => loose_in(m, r),
    };
    let key = Arc::as_ptr(t) as *const () as usize;
    if let Some(e) = m.get(&key) {
        return e.1;
    }
    poll_deadline();
    let n = match &**t {
        Pi(_, a, b) => part(m, a).max(part(m, b).saturating_sub(1)),
        Lam(_, b) => part(m, b).saturating_sub(1),
        App(f, a) => part(m, f).max(part(m, a)),
        BVar(i) => i + 1,
        _ => 0,
    };
    m.insert(key, (Arc::downgrade(t), n));
    n
}

/// Drops the entries whose node is gone. A table keyed by address holds its
/// nodes weakly: the address stays reserved while the entry is there, but
/// what the node points to is freed once nothing else uses it, so a long
/// computation does not keep every node it met. Nothing can ask about a
/// node that is gone, so dropping its entry loses no answer. Run when the
/// table has doubled since it last ran (counted from what it kept), so the
/// cost per insertion stays constant: a run at every size that is a power of
/// two would walk the whole table again for each insertion while the table
/// hovers at one, and a deep reduction inserts at every level it returns
/// through. The walk reads the clock, as its length is the table's.
fn sweep<V>(m: &mut NodeTable<V>) {
    if m.entries.len() >= m.sweep_at {
        m.entries.retain(|_, (node, _)| {
            poll_deadline();
            node.strong_count() > 0
        });
        m.sweep_at = m.entries.len().saturating_mul(2).max(SWEEP_FROM);
    }
}

fn forget_loose() {
    LOOSE.with(|m| m.borrow_mut().clear());
}

/// The pair of parts, the changed ones replaced; `None` when neither changed.
fn share2(a: &R, b: &R, a2: Option<R>, b2: Option<R>) -> Option<(R, R)> {
    if a2.is_none() && b2.is_none() {
        return None;
    }
    Some((
        a2.unwrap_or_else(|| a.clone()),
        b2.unwrap_or_else(|| b.clone()),
    ))
}

fn inst(body: &Tm, v: &Tm) -> Tm {
    inst_at(body, 0, v)
}

/// `t` with the atom `x` made the variable bound at depth `d`.
fn abstract_at(t: &Tm, d: usize, x: u64) -> Tm {
    abstract_tm(t, d, x).unwrap_or_else(|| t.clone())
}

/// `None` when `t` does not change.
fn abstract_tm(t: &Tm, d: usize, x: u64) -> Option<Tm> {
    match t {
        FVar(y) if *y == x => Some(BVar(d)),
        Pi(h, a, b) => {
            let (a2, b2) = (abstract_rc(a, d, x), abstract_rc(b, d + 1, x));
            share2(a, b, a2, b2).map(|(a, b)| Pi(h.clone(), a, b))
        }
        Lam(h, b) => abstract_rc(b, d + 1, x).map(|b| Lam(h.clone(), b)),
        App(f, a) => {
            let (f2, a2) = (abstract_rc(f, d, x), abstract_rc(a, d, x));
            share2(f, a, f2, a2).map(|(f, a)| App(f, a))
        }
        FVar(_) | BVar(_) | Sort(_) | Const(_) | Lit(_) => None,
    }
}

fn abstract_rc(t: &R, d: usize, x: u64) -> Option<R> {
    abstract_tm(t, d, x).map(Arc::new)
}

/// `Pi (x: dom). body`, with the atom `x` of `body` bound.
fn pi_over(x: u64, dom: Tm, body: &Tm) -> Tm {
    Pi(
        Hint::none(),
        Arc::new(dom),
        Arc::new(abstract_at(body, 0, x)),
    )
}

fn lam_over(x: u64, body: &Tm) -> Tm {
    Lam(Hint::none(), Arc::new(abstract_at(body, 0, x)))
}

fn has_loose(t: &Tm, d: usize) -> bool {
    match t {
        BVar(i) => *i >= d,
        Pi(_, a, b) => has_loose(a, d) || has_loose(b, d + 1),
        Lam(_, b) => has_loose(b, d + 1),
        App(f, a) => has_loose(f, d) || has_loose(a, d),
        FVar(_) | Sort(_) | Const(_) | Lit(_) => false,
    }
}

fn mentions_const(t: &Tm, names: &[DeclRef]) -> bool {
    match t {
        Const(c) => names.contains(c),
        Pi(_, a, b) => mentions_const(a, names) || mentions_const(b, names),
        Lam(_, b) => mentions_const(b, names),
        App(f, a) => mentions_const(f, names) || mentions_const(a, names),
        BVar(_) | FVar(_) | Sort(_) | Lit(_) => false,
    }
}

/// A small closed term that is not a numeral itself (`p()`,
/// `Nat::sub(p(), two_pow(130))`): one that may compute to a numeral, told
/// apart by walking at most 64 of its nodes.
fn constant_on_numerals(t: &Tm) -> bool {
    fn walk(t: &Tm, left: &mut usize) -> bool {
        if *left == 0 {
            return false;
        }
        *left -= 1;
        match t {
            Const(_) | Lit(_) | Sort(_) => true,
            App(f, a) => walk(f, left) && walk(a, left),
            FVar(_) | BVar(_) | Pi(..) | Lam(..) => false,
        }
    }
    matches!(t, Const(_) | App(..)) && walk(t, &mut 64)
}

fn mentions_fvar(t: &Tm) -> bool {
    match t {
        FVar(_) => true,
        Pi(_, a, b) => mentions_fvar(a) || mentions_fvar(b),
        Lam(_, b) => mentions_fvar(b),
        App(f, a) => mentions_fvar(f) || mentions_fvar(a),
        BVar(_) | Sort(_) | Const(_) | Lit(_) => false,
    }
}

/// The numeral from which `Core::offset_view` takes `x + n` off at once, and
/// from which the turns of a loop over a number are taken at once
/// ([`Core::repeat`]).
const LARGE_OFFSET: Num = Num::small(1 << 12);

/// How many reductions may wait one inside another, each for the weak head
/// normal form of a part it reduces on (the major premise of an eliminator,
/// an operand), as calls on the stack. A reduction that needs one more is
/// set aside with those that wait for it ([`Deep`]) and they are taken up
/// again one at a time ([`Core::drive`]), so the depth of the reductions a
/// term asks for is bounded by the memory, not by the stack.
const DEPTH: usize = 64;

/// How many turns of loops may be tried one inside another
/// ([`Core::repeat`]).
const TRIALS: usize = 8;

/// How far a reduction goes: with every name unfolded (the weak head normal
/// form), without unfolding names, or without unfolding names and leaving an
/// eliminator as it is when its major premise is a constructor only once
/// names are unfolded ([`Core::whnf_lazy`]).
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
enum Mode {
    Full,
    Head,
    Lazy,
}

/// A reduction of a node at its head, as far as it has gone: the state of
/// the loop of [`Core::whnf_steps`], which goes on from it when it is taken
/// up again.
struct Task {
    /// What the node has become.
    t: R,
    mode: Mode,
    /// The shared nodes it went through as the whole term: each reduces to
    /// what the reduction ends in.
    became: Vec<R>,
    /// Whether the head of `t` was just replaced by what it was found to
    /// reduce to (`Core::recalled_head`).
    recalled: bool,
    /// Where the reduction stops short of a weak head normal form
    /// ([`Core::repeat`]), and whether it stopped there.
    watch: Option<Box<Watch>>,
    met: bool,
}

impl Task {
    fn new(t: R, mode: Mode) -> Self {
        Task {
            t,
            mode,
            became: Vec::new(),
            recalled: false,
            watch: None,
            met: false,
        }
    }
}

/// The turn of a loop a reduction is run up to: the eliminator `rec` applied
/// again to the same parameters, motives and minor premises (`before`, the
/// nodes themselves), with the atom `major` as its major premise.
struct Watch {
    rec: DeclRef,
    before: Vec<R>,
    major: u64,
}

impl Watch {
    fn met(&self, c: &DeclRef, args: &[R]) -> bool {
        *c == self.rec
            && args.len() > self.before.len()
            && args
                .iter()
                .zip(&self.before)
                .all(|(a, b)| Arc::ptr_eq(a, b))
            && matches!(&*args[self.before.len()], FVar(x) if *x == self.major)
    }
}

/// A number written with a numeral: `more`, or `base + more`.
struct Counted {
    base: Option<R>,
    more: Num,
}

impl Counted {
    /// `t` as such a number, when it is written as one: a numeral, a sum
    /// whose second operand is a numeral, or the `Succ` of one of them (what
    /// such a sum reduces to).
    fn read(t: &Tm) -> Option<Counted> {
        let (t, succ) = match t {
            App(f, x) if matches!(&**f, Const(c) if c.is_primitive("Succ")) => (&**x, 1),
            _ => (t, 0),
        };
        match t {
            Lit(n) => Some(Counted {
                base: None,
                more: n.checked_add(Num::small(succ))?,
            }),
            App(f, n) => match (&**f, &**n) {
                (App(p, base), Lit(n)) if matches!(&**p, Const(c) if c.is_primitive("+")) => {
                    Some(Counted {
                        base: Some(base.clone()),
                        more: n.checked_add(Num::small(succ))?,
                    })
                }
                _ => None,
            },
            _ => None,
        }
    }

    /// The number with `k` less of its numeral.
    fn less(&self, k: Num) -> R {
        let more = Lit(self.more - k);
        Arc::new(match &self.base {
            None => more,
            Some(base) => App(
                Arc::new(App(Arc::new(konst("+")), base.clone())),
                Arc::new(more),
            ),
        })
    }
}

/// A reduction that needs the weak head normal form of `want` with
/// [`DEPTH`] reductions already waiting on the stack: those reductions,
/// innermost first, each with the node it reduces.
struct Deep {
    want: R,
    mode: Mode,
    tasks: Vec<(R, Task)>,
}

/// What a step of reduction gives, or the reductions set aside ([`Deep`]).
type Step<X> = Result<X, Box<Deep>>;

/// The head of an application and its arguments.
/// [`spine`] with the arguments as the nodes they are, not copies.
fn spine_rc(t: &Tm) -> (&Tm, Vec<R>) {
    let mut head = t;
    let mut args = Vec::new();
    while let App(f, a) = head {
        args.push(a.clone());
        head = f;
    }
    args.reverse();
    (head, args)
}

/// What [`Core::write`] found about the nodes of the term it writes, by
/// address: the levels of the scope a node refers to (`Core::levels`), and
/// whether it uses a name (`Core::mentions`). The term is borrowed for the
/// whole writing, so no address is reused while the memo is there.
#[derive(Default)]
struct WriteMemo<'a> {
    levels: HashMap<(usize, usize), Arc<Vec<usize>>>,
    mentions: HashMap<usize, Arc<HashSet<String>>>,
    /// The whole term being written.
    root: Option<&'a Tm>,
}

/// A last argument [`Core::infer_unrecorded`] types in its loop: where the
/// path comes back to, the argument, its domain, and the rest of the
/// telescope with the arguments before it, which take its variables.
struct Pending {
    mark: (usize, usize),
    arg: R,
    dom: R,
    cod: R,
    env: Vec<R>,
}

/// A pair the conversion found not to be convertible by their arguments,
/// with the hash of the two trees. The hash is found once for each node,
/// however often the trees share it: a value that shares its parts is a tree
/// far larger than its nodes, and hashing it as a tree would walk all of it.
#[derive(Clone)]
struct ConvKey(Tm, Tm, u64);

impl ConvKey {
    fn new(a: Tm, b: Tm) -> Self {
        let mut seen = HashMap::new();
        let h = tree_hash(&a, &mut seen)
            .wrapping_mul(31)
            .wrapping_add(tree_hash(&b, &mut seen));
        ConvKey(a, b, h)
    }
}

impl PartialEq for ConvKey {
    fn eq(&self, other: &Self) -> bool {
        self.2 == other.2 && self.0 == other.0 && self.1 == other.1
    }
}

impl Eq for ConvKey {}

impl std::hash::Hash for ConvKey {
    fn hash<H: std::hash::Hasher>(&self, h: &mut H) {
        self.2.hash(h);
    }
}

/// The hash of `t` as a tree, each shared node hashed once (by its address
/// in `seen`). Hints are not hashed: terms that differ only in them are equal.
fn tree_hash(t: &Tm, seen: &mut HashMap<*const Tm, u64>) -> u64 {
    use std::hash::{Hash, Hasher};
    let child = |r: &R, seen: &mut HashMap<*const Tm, u64>| {
        if let Some(h) = seen.get(&Arc::as_ptr(r)) {
            return *h;
        }
        let h = tree_hash(r, seen);
        seen.insert(Arc::as_ptr(r), h);
        h
    };
    let mut s = std::collections::hash_map::DefaultHasher::new();
    std::mem::discriminant(t).hash(&mut s);
    match t {
        BVar(i) => i.hash(&mut s),
        FVar(x) => x.hash(&mut s),
        Sort(x) => x.hash(&mut s),
        Const(c) => c.hash(&mut s),
        Pi(_, a, b) => (child(a, seen), child(b, seen)).hash(&mut s),
        Lam(_, b) => child(b, seen).hash(&mut s),
        App(f, a) => (child(f, seen), child(a, seen)).hash(&mut s),
        Lit(k) => k.hash(&mut s),
    }
    s.finish()
}

/// How much of a value a message shows (`Core::difference_in`).
const SHOWN_NODES: usize = 2000;

/// `t` with what is past its first `budget` nodes (outermost first) as `…`.
fn pruned(t: &Tm, budget: &mut usize) -> Tm {
    if *budget == 0 {
        return Const(DeclRef::fresh("…"));
    }
    *budget -= 1;
    match t {
        App(f, a) => {
            let f = pruned(f, budget);
            App(Arc::new(f), Arc::new(pruned(a, budget)))
        }
        Pi(h, d, r) => {
            let d = pruned(d, budget);
            Pi(h.clone(), Arc::new(d), Arc::new(pruned(r, budget)))
        }
        Lam(h, b) => Lam(h.clone(), Arc::new(pruned(b, budget))),
        t => t.clone(),
    }
}

/// A numeral `k + 1` as `Succ(k)`, and `0` as `Zero`, to set beside a term
/// written with the constructors.
fn unfold_lit(t: Tm) -> Tm {
    match t {
        Lit(Num::ZERO) => konst("Zero"),
        Lit(k) => App(Arc::new(konst("Succ")), Arc::new(Lit(k - Num::ONE))),
        t => t,
    }
}

/// `f` applied to `args`; `f` itself, the same node, when there are none.
fn apps_node(f: R, args: impl IntoIterator<Item = R>) -> R {
    args.into_iter().fold(f, |f, a| Arc::new(App(f, a)))
}

fn apps_rc(f: Tm, args: impl IntoIterator<Item = R>) -> Tm {
    args.into_iter().fold(f, |f, a| App(Arc::new(f), a))
}

/// The most nodes a reduced term is written out with (`whnf_in`).
const WRITTEN_LIMIT: usize = 1 << 20;

/// The number of nodes `t` has written out as a tree, its shared parts
/// counted at each place they are used; past [`WRITTEN_LIMIT`] it stops
/// counting. Each shared part is counted once (`seen`), so this costs the
/// size of `t` in the core, not written out.
fn written_size(t: &Tm, seen: &mut HashMap<usize, usize, AddrBuild>) -> usize {
    let part = |r: &R, seen: &mut HashMap<usize, usize, AddrBuild>| {
        let key = Arc::as_ptr(r) as usize;
        if let Some(&n) = seen.get(&key) {
            return n;
        }
        let n = written_size(r, seen);
        seen.insert(key, n);
        n
    };
    let n = match t {
        Pi(_, a, b) | App(a, b) => part(a, seen).saturating_add(part(b, seen)),
        Lam(_, b) => part(b, seen),
        _ => 0,
    };
    n.saturating_add(1).min(WRITTEN_LIMIT + 1)
}

fn spine(t: &Tm) -> (&Tm, Vec<Tm>) {
    let mut head = t;
    let mut args = Vec::new();
    while let App(f, a) = head {
        args.push((**a).clone());
        head = f;
    }
    args.reverse();
    (head, args)
}

fn sort_max(a: Sort, b: Sort) -> Sort {
    a.pi(&b)
}

/// What lazy unfolding knows of a name with a value: its height (one more
/// than the highest name its value uses, names that use each other sharing
/// one), and whether its value uses it again, directly or through others.
#[derive(Debug, Clone, Copy)]
struct Def {
    height: u32,
    recursive: bool,
}

/// The walk of [`Core::def`]: the order names were met in, the lowest
/// reached from each, the names met whose group is not closed yet, and what
/// each uses.
#[derive(Default)]
struct DefWalk {
    next: usize,
    index: HashMap<DeclRef, usize>,
    low: HashMap<DeclRef, usize>,
    stack: Vec<DeclRef>,
    on: HashSet<DeclRef>,
    uses: HashMap<DeclRef, Vec<DeclRef>>,
}

#[derive(Debug, Clone)]
struct Global {
    ty: Tm,
    /// One node, so that what it reduces to is found again wherever the
    /// name is unfolded (`Core::whnf_steps`).
    value: Option<R>,
}

#[derive(Debug, Clone)]
struct RecArg {
    arg: usize,
    /// How many binders the argument abstracts.
    ys: usize,
    fam: usize,
    /// Its indices, over the group's parameters, the constructor's
    /// arguments and the binders (bound in that order, outermost first).
    idx: Vec<Tm>,
}

#[derive(Debug, Clone)]
struct CtorInfo {
    name: DeclRef,
    nargs: usize,
    recs: Vec<RecArg>,
}

#[derive(Debug, Clone)]
struct IndInfo {
    params: usize,
    indices: usize,
    group: Vec<DeclRef>,
    pos: usize,
    ctors: Vec<CtorInfo>,
    /// A nested member stands for `J(args)`; its constructors are `J`'s.
    alias: Option<(DeclRef, Vec<Tm>)>,
    /// The result indices of the only constructor, over the parameters,
    /// for the reduction of a proof of an `Eq`-like proposition.
    k_like: Option<Vec<Tm>>,
}

/// The types of the names the named checker has declared.
pub(super) type Declared<'a> = &'a dyn Fn(&Name) -> Option<T>;

/// The atoms a question of the named checker is asked over: its context's
/// variables, each read (with its type) when a term first mentions it, and
/// the parts the core cannot read, each an atom of no type (convertible only
/// to itself). They count down from the top, away from the core's own.
#[derive(Clone)]
struct Open<'a> {
    ctx: &'a Ctx,
    atoms: Vec<Option<u64>>,
    /// The context's variables a name means first: those before the one
    /// whose type is being read. (The named checker's contexts are not
    /// always in order: a `match` puts the variables of a pattern after
    /// those whose types it rewrites to mention them.)
    visible: usize,
    types: Vec<(u64, Tm)>,
    values: Vec<(u64, Arc<Tm>)>,
    opaque: Vec<(u64, T)>,
    /// The names the binders entered while typing are shown under.
    named: Vec<(u64, Name)>,
    /// The types of the names the named checker has declared and the core
    /// has not (yet): each such name is an atom of that type.
    outer: Option<Declared<'a>>,
    declared: Vec<(Name, u64)>,
    next: u64,
    /// Whether known parts are read as atoms (`Core::known`), and whether
    /// the term being read is the question's own (never read as one).
    known: bool,
    top: bool,
    /// The context of the last part `known_part` found typed in this
    /// question's context: the next part typed there is not compared again.
    known_ctx: std::cell::Cell<Option<*const usize>>,
}

/// The context's types by address, as `Core::known` keeps them.
pub(super) fn ctx_addresses(ctx: &Ctx) -> impl Iterator<Item = usize> + '_ {
    ctx.iter()
        .map(|(_, c)| Arc::as_ptr(&c.kind) as *const () as usize)
}

impl<'a> Open<'a> {
    fn new(ctx: &'a Ctx) -> Self {
        Open {
            ctx,
            atoms: vec![None; ctx.len()],
            visible: ctx.len(),
            types: Vec::new(),
            values: Vec::new(),
            opaque: Vec::new(),
            named: Vec::new(),
            outer: None,
            declared: Vec::new(),
            next: u64::MAX,
            known: false,
            top: false,
            known_ctx: std::cell::Cell::new(None),
        }
    }

    fn atom(&mut self) -> u64 {
        self.next -= 1;
        self.next
    }

    /// An unknown name is one atom wherever it occurs; any other part the
    /// core cannot read is an atom of its own.
    fn opaque(&mut self, t: &T) -> Tm {
        if let TermKind::Var(n) = &*t.kind
            && let Some((x, _)) = self
                .opaque
                .iter()
                .find(|(_, u)| matches!(&*u.kind, TermKind::Var(m) if m == n))
        {
            return FVar(*x);
        }
        let x = self.atom();
        self.opaque.push((x, t.clone()));
        FVar(x)
    }

    fn back(&self, x: u64) -> Option<TermKind> {
        if let Some((_, n)) = self.named.iter().find(|(y, _)| *y == x) {
            return Some(TermKind::Var(n.clone()));
        }
        if let Some((n, _)) = self.declared.iter().find(|(_, y)| *y == x) {
            return Some(TermKind::Var(n.clone()));
        }
        if let Some(i) = self.atoms.iter().position(|y| *y == Some(x)) {
            return Some(TermKind::Var(self.ctx[i].0.clone()));
        }
        self.opaque
            .iter()
            .find(|(y, _)| *y == x)
            .map(|(_, t)| (*t.kind).clone())
    }
}

/// The steps of reduction one declaration may take unless it says otherwise
/// (`Kernel::set_step_limit`, `Kernel::set_budget`).
pub(super) const DEFAULT_STEP_LIMIT: u64 = 1 << 30;

/// The reduction done for one declaration: steps of `whnf`, the names
/// unfolded most, a limit on the steps and a deadline. Past either `whnf`
/// stops reducing; the kernel then rejects the declaration whatever the check
/// said (`Kernel::declare`), so giving up never accepts anything. The limit on
/// the steps is the same on every machine; the deadline is not.
#[derive(Clone, Default)]
pub(super) struct Budget {
    deadline: Option<crate::clock::Instant>,
    /// The steps the declaration may take; `None` is no limit.
    limit: Option<u64>,
    steps: u64,
    out: bool,
    /// Whether it was the limit on the steps that stopped reduction.
    out_of_steps: bool,
    /// The name unfolded last before the step past the limit.
    last_unfold: Option<DeclRef>,
    unfolds: HashMap<DeclRef, u64, AddrBuild>,
    /// The first sum or product of two numerals past the largest numeral met, which is
    /// left as it is ([`Core::past_limit`]).
    past_limit: Option<String>,
}

/// What [`Core::end_budget`] says of the declaration just checked.
pub(super) struct Spent {
    pub steps: u64,
    pub out: bool,
    /// Whether the limit on the steps stopped reduction (and not the deadline).
    pub out_of_steps: bool,
    /// The name unfolded last when the limit on the steps was reached.
    pub reached_in: Option<String>,
    /// The names unfolded most, with how often.
    pub top: Vec<(String, u64)>,
    /// A sum or product of two numerals past the largest numeral that was left as it is.
    pub past_limit: Option<String>,
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
enum Elimination {
    Induction,
    Recursion,
    At(super::Level),
}

#[derive(Clone)]
pub(super) struct Core {
    names: SourceNames,
    globals: tauto_identity::ForkedMap<DeclRef, Global, AddrBuild>,
    /// Shared across eliminator steps without copying constructors.
    inds: tauto_identity::ForkedMap<DeclRef, Arc<IndInfo>, AddrBuild>,
    /// Constructor → (family it builds, place among its constructors).
    ctors: tauto_identity::ForkedMap<DeclRef, (DeclRef, usize), AddrBuild>,
    /// Eliminator → (family, whether it is `_rec`).
    recs: tauto_identity::ForkedMap<DeclRef, DeclRef, AddrBuild>,
    rec_targets: tauto_identity::ForkedMap<DeclRef, Vec<DeclRef>, AddrBuild>,
    eliminators: tauto_identity::ForkedMap<(DeclRef, Elimination), DeclRef>,
    /// The quotient's constants declared so far, each without a value and
    /// with the type [`quot_type`] gives it (`Core::quot_iota`).
    quot: tauto_identity::ForkedSet<DeclRef, AddrBuild>,
    /// The types of the atoms in scope.
    lctx: HashMap<u64, Tm, AddrBuild>,
    /// The values of the atoms in scope that stand for a known part
    /// (`Core::known`): such an atom unfolds to its value, as a name does.
    lvals: HashMap<u64, Arc<Tm>, AddrBuild>,
    next: u64,
    /// Applications of the same name found not convertible argument by
    /// argument, during the outermost `conv`: unfolding them can meet them
    /// again, and comparing their arguments each time is exponential.
    conv_no: HashSet<ConvKey>,
    /// Pairs of nodes found not convertible (`Core::conv_node`) during the
    /// outermost `conv`, by address. The nodes are held weakly, so the
    /// addresses are not reused while the entry is there.
    conv_fail: HashMap<(usize, usize), (Weak<Tm>, Weak<Tm>)>,
    conv_depth: usize,
    /// The binders the comparison in hand has gone under.
    conv_binders: usize,
    /// The names that lay open calls of themselves reduced on both sides on
    /// the way to the comparison in hand, each with `conv_binders` where it
    /// was (`Core::conv_cut`).
    conv_unfolded: Unfolded,
    /// The height and recursion of each name with a value, found when first
    /// asked for (`Core::def`).
    defs: HashMap<DeclRef, Def>,
    /// The names whose values were found, by [`Core::no_unfolding_cycle`],
    /// to reach only names in `cycle_names` (their own included), and the
    /// names so reached: a value that reaches such a name reaches through it
    /// only names of `cycle_names`. A change to any global of `cycle_names`
    /// (a value given, taken or replaced, a name added again or removed)
    /// forgets both ([`Core::touch`]).
    cycle_free: HashSet<DeclRef>,
    cycle_names: HashSet<DeclRef>,
    /// How much reduction the declaration in hand has done, and whether it ran
    /// out of time (`Kernel::set_timeout`).
    budget: Budget,
    /// What nodes reduced to, for the declaration in hand (`whnf_shared`).
    shared: NodeTable<Tm>,
    /// `Nat::eq`, `Nat::lt`, `Nat::div_nz` and `Nat::rem_nz` are unfolded, not computed,
    /// and a loop is reduced a turn at a time (a test compares the two).
    numeric_off: bool,
    /// While [`Core::whnf_lazy`] reduces: an eliminator whose major premise
    /// is a constructor only once names are unfolded is left as it is.
    lazy_iota: bool,
    /// How many reductions wait on the stack, one inside another, since the
    /// outermost ([`Core::need`]).
    depth: usize,
    /// How many of [`Core::drive`] are running, one inside another.
    drives: usize,
    /// How many turns of loops are being tried, one inside another
    /// ([`Core::repeat`]).
    trials: usize,
    /// What the nodes that reductions set aside waited for reduce to
    /// ([`Core::drive`]), by address, for each [`Mode`]. Each node is held, so
    /// its address is not reused while the entry is there.
    forced: [HashMap<usize, (R, Tm), AddrBuild>; 3],
    /// The loops found not to come round to themselves ([`Core::repeat`]),
    /// for the declaration in hand: the minor premise of `Succ`, by address,
    /// with which of the arguments after the major premise were numbers and
    /// how far the reduction went ([`Mode`]). The node is held, so its
    /// address is not reused while the entry is there.
    no_repeat: HashMap<(usize, u64), R>,
    /// While a question of the named checker is typed: where the typing is
    /// (`at`), the binders entered on the way (`bound`), and the holes met.
    track: Option<Track>,
    derivation: Option<Vec<Vec<RawDerivation>>>,
    /// The level variables of the universe template being checked once for
    /// every level (`check/universe.rs`): `Type(u + 1)` reads as a sort only
    /// over these, and no declaration outside that check sees one.
    pub(super) level_vars: Vec<Name>,
    /// Parts of terms this core has already typed for the named checker, by
    /// address: the part, the context's types (by address) it was typed in,
    /// and the type the core gave it. While `use_known` is set, a question
    /// reads such a part as an atom of that type instead of typing it again.
    pub(super) known: HashMap<usize, (T, Arc<[usize]>, T)>,
    /// The context (by address) a part was last put into `known` in: the
    /// parts typed in one context share it, so that a question in that
    /// context compares it once, not once for each part.
    pub(super) known_at: Option<Arc<[usize]>>,
    /// The parts of terms whose binders the named checker has found to be
    /// the core's (`kernel_binders`), by address, each held so its address
    /// is not reused: a term typed again inside a larger one is not walked
    /// again.
    pub(super) binders_checked: HashMap<usize, T>,
    pub(super) use_known: bool,
    #[cfg(feature = "selfhost")]
    replay: Option<Vec<(String, bool)>>,
    #[cfg(feature = "selfhost")]
    replay_skipped: usize,
    /// The time spent in the recorded operations, to compare with a replay.
    #[cfg(feature = "selfhost")]
    replay_time: std::time::Duration,
}

impl Core {
    /// Starts the atoms this core makes up `by` further on, so that a copy's
    /// atoms are not another copy's (`check/fork.rs`).
    /// Leaves in this copy only what it added since it was made of `base`.
    pub(super) fn subtract(&mut self, since: u64) {
        self.forget_cycles();
        self.globals.subtract(since);
        self.inds.subtract(since);
        self.ctors.subtract(since);
        self.recs.subtract(since);
        self.rec_targets.subtract(since);
        self.eliminators.subtract(since);
        self.quot.subtract(since);
        // A spelling two copies reserved is two fresh references: taking
        // both in is said like any other key both wrote.
        self.names.0.subtract(since);
    }

    /// Lets go of what [`Core::absorb`] does not take in: what was worked
    /// out while declaring, kept only to be faster later.
    pub(super) fn settle(&mut self) {
        self.lctx = Default::default();
        self.lvals = Default::default();
        self.conv_no = Default::default();
        self.conv_fail = Default::default();
        self.known = Default::default();
        self.known_at = None;
        self.binders_checked = Default::default();
        self.shared = NodeTable::default();
        self.derivation = None;
    }

    pub(super) fn offset_counter(&mut self, by: u64) {
        self.next += by;
    }

    /// Takes in the declarations a copy of this core added (`check/fork.rs`).
    /// What holds for the declaration in hand only is left as it is.
    pub(super) fn absorb(&mut self, other: Core) -> bool {
        let mut alone = self.names.0.absorb(other.names.0);
        self.forget_cycles();
        alone &= self.globals.absorb_any(other.globals);
        alone &= self.inds.absorb_any(other.inds);
        alone &= self.ctors.absorb(other.ctors);
        alone &= self.recs.absorb(other.recs);
        alone &= self.rec_targets.absorb(other.rec_targets);
        alone &= self.eliminators.absorb(other.eliminators);
        alone &= self.quot.absorb(other.quot);
        // What a definition unfolds to is worked out when asked for, from
        // the globals it reaches, which every copy has alike: the first
        // worked out is kept.
        for (k, v) in other.defs {
            self.defs.entry(k).or_insert(v);
        }
        self.next = self.next.max(other.next);
        alone
    }
}

#[derive(Clone)]
struct RawDerivation {
    term: Tm,
    ty: Tm,
    bound: Vec<(u64, Hint)>,
    rule: InferenceRule,
    premises: Vec<RawDerivation>,
}

/// Where a question of the named checker is being typed. `at` is the path
/// from the term asked about to the subterm in hand: 0 for the function of
/// an application or the domain of a `Pi`, 1 for its argument or codomain,
/// 0 for the body of a function. Below a redex typed by its reduct the path
/// stops (`lost`).
#[derive(Default, Clone)]
struct Track {
    at: Vec<u8>,
    lost: usize,
    bound: Vec<(u64, Hint)>,
    holes: HashSet<u64>,
    /// Each hole met, with the type expected there and the binders entered.
    met: Vec<HoleIn>,
}

type HoleIn = (u64, Tm, Vec<(u64, Hint)>);

#[derive(Debug)]
pub(super) struct Fault {
    why: Why,
    at: Vec<u8>,
    bound: Vec<(u64, Hint)>,
}

#[derive(Debug)]
enum Why {
    Said(&'static str),
    Mismatch {
        expected: Tm,
        found: Tm,
    },
    /// An atom of no type: a part the core could not read.
    Unread(u64),
    NotFunction,
    /// A function where `expected` (not a function type) is expected.
    NoPi(Tm),
    NotType,
}

impl From<Box<Fault>> for Message {
    fn from(f: Box<Fault>) -> Message {
        match f.why {
            Why::Said(id) => msg!(id),
            Why::Mismatch { .. } => msg!("kernel-core-type-mismatch"),
            Why::Unread(_) => msg!("kernel-core-unknown-atom"),
            Why::NotFunction => msg!("kernel-core-not-function"),
            Why::NoPi(_) => msg!("kernel-core-unexpected-function"),
            Why::NotType => msg!("kernel-core-not-type"),
        }
    }
}

/// What the named checker asks of a term.
#[derive(Clone, Copy)]
pub(super) enum Ask<'a> {
    Infer,
    Sort,
    Check(&'a T),
}

/// A term that types: its type or sort (as asked), and the holes met, in
/// the order met.
pub(super) struct Typed {
    pub ty: Option<T>,
    pub sort: Option<Sort>,
    pub holes: Vec<Met>,
    pub derivation: Option<Derivation>,
}

/// A hole met where a term of `goal` is expected, under the binders `bound`
/// (outermost first) entered on the way to it.
pub(super) struct Met {
    pub hole: T,
    pub goal: T,
    pub bound: Vec<(Name, T)>,
}

/// Where a term does not type, written back: the path to the subterm (see
/// [`Track`]), the binders entered on the way, and why.
pub(super) struct Failure {
    pub why: Failed,
    pub at: Vec<u8>,
    pub bound: Vec<(Name, T)>,
}

pub(super) enum Failed {
    Said(&'static str),
    Mismatch {
        expected: T,
        found: T,
    },
    /// A part the core could not read (a name it does not know, a hole
    /// where a type is needed, …), as written.
    Unread(T),
    NotFunction,
    NoPi(T),
    NotType,
}

pub(super) type Res<X> = Result<X, Message>;

fn fail<X>(m: impl Into<Message>) -> Res<X> {
    Err(m.into())
}

/// One family of an inductive declaration, as the named checker read it:
/// its type `∀ params indices. Sort`, and each constructor's type
/// `∀ params args. Family(params, indices)`.
pub(super) struct FamSpec {
    pub name: Name,
    pub ty: T,
    pub ctors: Vec<(Name, T)>,
}

/// The quotient: `Quot(A, r)`, `quot_mk(A, r, a)`, and the two ways out of
/// it, `Quot_lift` (into any `B: Type`, given that `f` takes related values
/// to equal ones) and `Quot::ind` (into a proposition). Each is a constant
/// without a value; `Core::quot_iota` is their computation. Reading
/// `Quot(A, r)` as `A`, `quot_mk` as the identity and both ways out as
/// application turns every rule here into rules the core already has, so
/// they prove nothing the core without them does not.
const QUOT: &[&str] = &["Quot", "Quot::mk", "Quot::lift", "Quot::ind"];

/// The equality `Quot::lift` is stated with: the type of the family `eq`
/// and of its one constructor.
fn eq_type(eq: &DeclRef) -> (Tm, Tm) {
    let pi = |a: Tm, b: Tm| Pi(Hint::none(), Arc::new(a), Arc::new(b));
    let ty = || Sort(Sort::ty(0));
    // (A: Type, a: A, b: A): Prop
    let family = pi(ty(), pi(BVar(0), pi(BVar(1), Sort(Sort::Prop))));
    // <A: Type, a: A>: Eq(A, a, a)
    let refl = pi(
        ty(),
        pi(
            BVar(0),
            apps(Const(eq.clone()), [BVar(1), BVar(0), BVar(0)]),
        ),
    );
    (family, refl)
}

/// The type each constant of [`QUOT`] must be declared with.
fn quot_type(name: &str) -> Option<Tm> {
    let ty = || Arc::new(Sort(Sort::ty(0)));
    let prop = || Arc::new(Sort(Sort::Prop));
    let pi = |a: Tm, b: Tm| Pi(Hint::none(), Arc::new(a), Arc::new(b));
    let v = BVar;
    // `(A, A) -> Prop` where `A` is the variable `a`.
    let rel = |a: usize| pi(v(a), Pi(Hint::none(), Arc::new(v(a + 1)), prop()));
    let quot = |a: usize, r: usize| apps(konst("Quot"), [v(a), v(r)]);
    let over_a_r = |rest: Tm| Pi(Hint::none(), ty(), Arc::new(pi(rel(0), rest)));
    Some(match name {
        // (A: Type, r: (A, A) -> Prop): Type
        "Quot" => over_a_r(Sort(Sort::ty(0))),
        // <A, r>(a: A): Quot(A, r)
        "Quot::mk" => over_a_r(pi(v(1), quot(2, 1))),
        // <A, r, B: Type>(f: (A) -> B,
        //   h: ∀ a b. (r(a, b)) -> Eq(B, f(a), f(b)), q: Quot(A, r)): B
        "Quot::lift" => over_a_r(Pi(
            Hint::none(),
            ty(),
            Arc::new(pi(
                pi(v(2), v(1)),
                pi(
                    pi(
                        v(3),
                        pi(
                            v(4),
                            pi(
                                apps(v(4), [v(1), v(0)]),
                                apps(konst("Eq"), [v(4), app(v(3), v(2)), app(v(3), v(1))]),
                            ),
                        ),
                    ),
                    pi(quot(4, 3), v(3)),
                ),
            )),
        )),
        // <A, r>(P: (Quot(A, r)) -> Prop, m: ∀ a. P(quot_mk(A, r, a)),
        //   q: Quot(A, r)): P(q)
        "Quot::ind" => over_a_r(pi(
            Pi(Hint::none(), Arc::new(quot(1, 0)), prop()),
            pi(
                pi(v(2), app(v(1), apps(konst("Quot::mk"), [v(3), v(2), v(0)]))),
                pi(quot(3, 2), app(v(2), v(0))),
            ),
        )),
        _ => return None,
    })
}

impl Core {
    pub(super) fn new() -> Self {
        let mut c = Core {
            names: SourceNames::default(),
            globals: Default::default(),
            inds: Default::default(),
            ctors: Default::default(),
            recs: Default::default(),
            rec_targets: Default::default(),
            eliminators: Default::default(),
            quot: Default::default(),
            lctx: HashMap::default(),
            lvals: HashMap::default(),
            next: 0,
            conv_no: HashSet::new(),
            conv_fail: HashMap::new(),
            conv_depth: 0,
            conv_binders: 0,
            conv_unfolded: Unfolded::default(),
            defs: Default::default(),
            cycle_free: Default::default(),
            cycle_names: Default::default(),
            budget: Budget::default(),
            shared: NodeTable::default(),
            numeric_off: false,
            lazy_iota: false,
            depth: 0,
            drives: 0,
            trials: 0,
            forced: Default::default(),
            no_repeat: HashMap::new(),
            track: None,
            derivation: None,
            level_vars: Vec::new(),
            known: HashMap::new(),
            known_at: None,
            binders_checked: HashMap::new(),
            use_known: false,
            #[cfg(feature = "selfhost")]
            replay: None,
            #[cfg(feature = "selfhost")]
            replay_skipped: 0,
            #[cfg(feature = "selfhost")]
            replay_time: std::time::Duration::ZERO,
        };
        let nat = konst("Nat");
        let binary = Pi(
            Hint::none(),
            Arc::new(nat.clone()),
            Arc::new(Pi(Hint::none(), Arc::new(nat.clone()), Arc::new(nat))),
        );
        for op in ["+", "*", "-"] {
            c.cycle_free.clear();
            c.cycle_names.clear();
            c.globals.insert(
                c.names.reserve(op),
                Global {
                    ty: binary.clone(),
                    value: None,
                },
            );
        }
        c
    }

    #[cfg(feature = "selfhost")]
    pub(super) fn add_decl(
        &mut self,
        name: &Name,
        ty: &T,
        value: Option<&T>,
        transparent: bool,
    ) -> Res<()> {
        let input = self
            .replay
            .as_ref()
            .and_then(|_| selfhost::encode_decl(self, name, ty, value, transparent));
        let result = self.timed(|c| c.add_decl_inner(name, ty, value, transparent));
        self.record(input, result.is_ok());
        result
    }

    #[cfg(feature = "selfhost")]
    pub(super) fn add_constant(&mut self, name: &Name, value: &T) -> Res<()> {
        let input = self.replay.as_ref().and_then(|_| {
            self.read(value)
                .ok()
                .map(|v| format!("C {name} {}", selfhost::term(&v)))
        });
        let result = self.timed(|c| c.add_constant_inner(name, value));
        self.record(input, result.is_ok());
        result
    }

    #[cfg(feature = "selfhost")]
    pub(super) fn set_value(&mut self, name: &Name, value: &T) -> Res<()> {
        let input = self.replay.as_ref().and_then(|_| {
            self.read(value)
                .ok()
                .map(|v| format!("V {name} {}", selfhost::term(&v)))
        });
        let result = self.timed(|c| c.set_value_inner(name, value));
        self.record(input, result.is_ok());
        result
    }

    #[cfg(feature = "selfhost")]
    pub(super) fn add_inductive(&mut self, fams: &[FamSpec], np: usize, out: Sort) -> Res<()> {
        let input = self
            .replay
            .as_ref()
            .and_then(|_| selfhost::encode_inductive(self, fams, np, &out));
        let result = self.timed(|c| c.add_inductive_inner(fams, np, out));
        self.record(input, result.is_ok());
        result
    }

    #[cfg(not(feature = "selfhost"))]
    pub(super) fn add_decl(
        &mut self,
        name: &Name,
        ty: &T,
        value: Option<&T>,
        transparent: bool,
    ) -> Res<()> {
        self.add_decl_inner(name, ty, value, transparent)
    }

    #[cfg(not(feature = "selfhost"))]
    pub(super) fn add_constant(&mut self, name: &Name, value: &T) -> Res<()> {
        self.add_constant_inner(name, value)
    }

    #[cfg(not(feature = "selfhost"))]
    pub(super) fn set_value(&mut self, name: &Name, value: &T) -> Res<()> {
        self.set_value_inner(name, value)
    }

    /// Stops a name from unfolding: an `opaque fn`, once its equation is
    /// checked. Only conversions are lost, so nothing checks that did not
    /// check with the name unfolding. The self-hosted checker does not read
    /// it, and the trace counts it as skipped.
    pub(super) fn seal(&mut self, name: &Name) -> Res<()> {
        let result = match self
            .names
            .reference(name)
            .cloned()
            .inspect(|id| self.touch(id))
            .and_then(|id| self.globals.get_mut(&id))
        {
            Some(g) => {
                g.value = None;
                self.shared.clear();
                self.defs.clear();
                Ok(())
            }
            None => fail(msg!("kernel-core-not-defined", name = (name).to_string())),
        };
        #[cfg(feature = "selfhost")]
        self.record(None, result.is_ok());
        result
    }

    /// Stops a name declared just now from unfolding: a theorem. Nothing
    /// has unfolded it yet, so the caches stay. Only conversions are lost.
    pub(super) fn seal_fresh(&mut self, name: &Name) {
        if let Some(id) = self.names.reference(name).cloned() {
            self.touch(&id);
        }
        if let Some(g) = self
            .names
            .reference(name)
            .and_then(|id| self.globals.get_mut(&id))
        {
            g.value = None;
        }
    }

    #[cfg(not(feature = "selfhost"))]
    pub(super) fn add_inductive(&mut self, fams: &[FamSpec], np: usize, out: Sort) -> Res<()> {
        self.add_inductive_inner(fams, np, out)
    }

    /// A closed surface term: every name is a binder of the term, a sort,
    /// or a global already in the core.
    pub(super) fn read(&self, t: &T) -> Res<Tm> {
        self.read_in(t, &mut Vec::new(), None)
    }

    /// `Type(l)` for a level `l` over the level variables in hand.
    pub(super) fn level_sort(&self, t: &T) -> Option<Sort> {
        if self.level_vars.is_empty() {
            return None;
        }
        let TermKind::App {
            function,
            arguments,
        } = &*t.kind
        else {
            return None;
        };
        if !matches!(&*function.kind, TermKind::Var(n) if tauto_surface::bindings::is_library(&n, "Type"))
            || arguments.len() != 1
        {
            return None;
        }
        let l = super::level_of(&arguments[0])?;
        let bound = l
            .variables()
            .all(|v| self.level_vars.iter().any(|b| b == v));
        (l.as_const().is_none() && bound).then_some(Sort::Type(l))
    }

    /// [`T::last_argument_spine`], stopping at a sort over level variables,
    /// and at a last argument `stop` says is to be read whole: then the
    /// spine's end is that argument (and the flag is set), not an
    /// application whose function is read.
    fn sort_spine<'t>(&self, t: &'t T, stop: impl Fn(&T) -> bool) -> (Vec<&'t T>, &'t T, bool) {
        let mut spine = Vec::new();
        let mut t = t;
        while let TermKind::App { arguments, .. } = &*t.kind
            && let Some(last) = arguments.last()
            && self.level_sort(t).is_none()
        {
            spine.push(t);
            t = last;
            if stop(t) {
                return (spine, t, true);
            }
        }
        (spine, t, false)
    }

    /// Whether `t` is a part the core has typed before, in any context.
    fn is_known(&self, t: &T) -> bool {
        self.known
            .get(&(Arc::as_ptr(&t.kind) as *const () as usize))
            .is_some_and(|(was, _, _)| Arc::ptr_eq(&was.kind, &t.kind))
    }

    /// The type the core gave `t` when it typed it as a part before in the
    /// context `o` reads (`Core::known`), where `t` is read with nothing
    /// bound: `t` is then read as an atom of that type.
    fn known_part<'k>(&'k self, t: &T, scope: &[Name], o: &Open<'_>) -> Option<&'k T> {
        if !o.known || !scope.is_empty() {
            return None;
        }
        let (was, at, ty) = self
            .known
            .get(&(Arc::as_ptr(&t.kind) as *const () as usize))?;
        if !Arc::ptr_eq(&was.kind, &t.kind) || at.len() != o.ctx.len() {
            return None;
        }
        // The question's context does not change while it is read, so a
        // context once found equal to it stays so.
        if o.known_ctx.get() == Some(at.as_ptr()) {
            return Some(ty);
        }
        at.iter()
            .copied()
            .eq(ctx_addresses(o.ctx))
            .then(|| o.known_ctx.set(Some(at.as_ptr())))
            .map(|()| ty)
    }

    /// `t` read with `scope`, the names bound so far (innermost last). With
    /// `open`, a question of the named checker: its context's names are
    /// atoms, and what the core cannot read is an atom of no type.
    fn read_in(&self, t: &T, scope: &mut Vec<Name>, mut open: Option<&mut Open<'_>>) -> Res<Tm> {
        if let Some(o) = open.as_deref_mut()
            && o.known
        {
            if std::mem::take(&mut o.top) {
            } else if let Some(ty) = self.known_part(t, scope, o) {
                let x = o.atom();
                o.opaque.push((x, t.clone()));
                o.known = false;
                let ty = self.read_open(ty, o);
                let value = self.read_in(t, scope, Some(o))?;
                o.known = true;
                o.types.push((x, ty));
                o.values.push((x, Arc::new(value)));
                return Ok(FVar(x));
            }
        }
        self.read_parts(t, scope, open)
    }

    /// [`Self::read_in`] past its reading of known parts.
    fn read_parts(&self, t: &T, scope: &mut Vec<Name>, mut open: Option<&mut Open<'_>>) -> Res<Tm> {
        let opaque = |open: Option<&mut Open<'_>>, why: Message| match open {
            Some(o) => Ok(o.opaque(t)),
            None => Err(why),
        };
        if let Some(s) = self.level_sort(t) {
            return Ok(Sort(s));
        }
        Ok(match &*t.kind {
            TermKind::Var(n) => {
                if let Name::Global(reference) = n {
                    if let Some(sort) = sort_named(n) {
                        return Ok(Sort(sort));
                    }
                    if self.globals.contains_key(reference) {
                        return Ok(Const(reference.clone()));
                    }
                    // During elaboration a recursive declaration's signature
                    // is an explicit open assumption under its exact ID. It
                    // is not installed in the closed declaration environment.
                    if let Some(o) = open.as_deref_mut()
                        && let Some(i) = o.ctx.iter().rposition(|(name, _)| name == n)
                    {
                        return Ok(FVar(self.local(o, i)));
                    }
                    if let Some(o) = open.as_deref_mut()
                        && let Some(atom) = self.declared(o, n)
                    {
                        return Ok(FVar(atom));
                    }
                    return opaque(open, msg!("kernel-core-not-defined", name = n.to_string()));
                }
                if n.spelling() == Some("_") {
                    return opaque(open, msg!("kernel-core-underscore-not-value"));
                }
                if let Some(p) = scope.iter().rposition(|m| m == n) {
                    BVar(scope.len() - 1 - p)
                } else if let Some(o) = open.as_deref_mut()
                    && let Some(i) = o.ctx[..o.visible]
                        .iter()
                        .rposition(|(m, _)| m == n)
                        .or_else(|| o.ctx.iter().rposition(|(m, _)| m == n))
                {
                    FVar(self.local(o, i))
                } else if let Some(s) = sort_named(n) {
                    Sort(s)
                } else if let Some(reference) = self
                    .names
                    .reference(n)
                    .filter(|r| self.globals.contains_key(*r))
                {
                    Const(reference.clone())
                } else if let Some(o) = open.as_deref_mut()
                    && let Some(x) = self.declared(o, n)
                {
                    FVar(x)
                } else {
                    return opaque(
                        open,
                        msg!("kernel-core-not-defined", name = (n).to_string()),
                    );
                }
            }
            TermKind::Nat(n) => match Num::parse(n) {
                Some(k) => Lit(k),
                None => return opaque(open, msg!("kernel-core-numeral-too-large", numeral = n)),
            },
            // `false` and `true` are the constructors of the prelude's `Bool`.
            TermKind::Bool(b) => konst(if *b { "true" } else { "false" }),
            TermKind::App { .. } => {
                // In a loop along the last arguments (`last_argument_spine`),
                // reading the parts in the order the recursion would. A sort
                // over level variables is one part, not an application.
                // A last argument the core has typed before is read as the
                // atom it is (`known_part`), as the recursion would read it.
                let (spine, under, whole) = match open.as_deref() {
                    Some(o) => self.sort_spine(t, |a| {
                        if o.known {
                            self.known_part(a, scope, o).is_some()
                        } else {
                            scope.is_empty() && self.is_known(a)
                        }
                    }),
                    None => self.sort_spine(t, |_| false),
                };
                let mut heads = Vec::with_capacity(spine.len());
                for s in &spine {
                    let TermKind::App {
                        function,
                        arguments,
                    } = &*s.kind
                    else {
                        unreachable!("the spine holds applications")
                    };
                    let mut acc = self.read_in(function, scope, open.as_deref_mut())?;
                    for a in &arguments[..arguments.len() - 1] {
                        acc = app(acc, self.read_in(a, scope, open.as_deref_mut())?);
                    }
                    heads.push(acc);
                }
                let mut acc = match &*under.kind {
                    _ if whole || self.level_sort(under).is_some() => {
                        self.read_in(under, scope, open.as_deref_mut())?
                    }
                    TermKind::App { function, .. } => {
                        self.read_in(function, scope, open.as_deref_mut())?
                    }
                    _ => self.read_in(under, scope, open.as_deref_mut())?,
                };
                for head in heads.into_iter().rev() {
                    acc = app(head, acc);
                }
                acc
            }
            TermKind::Pi { params, result, .. } => {
                let depth = scope.len();
                let mut doms = Vec::new();
                for (n, d) in params {
                    if n.as_ref()
                        .is_some_and(|n| n.is_resolved() && !matches!(n, Name::Local(_)))
                    {
                        return opaque(open, msg!("kernel-core-not-kernel-term"));
                    }
                    let n = n.clone().unwrap_or_else(|| "_".into());
                    doms.push((
                        Hint::named(&n),
                        self.read_in(d, scope, open.as_deref_mut())?,
                    ));
                    scope.push(n);
                }
                let mut acc = self.read_in(result, scope, open)?;
                scope.truncate(depth);
                for (h, d) in doms.into_iter().rev() {
                    acc = Pi(h, Arc::new(d), Arc::new(acc));
                }
                acc
            }
            TermKind::Lam { params, body, .. } => {
                if params
                    .iter()
                    .any(|n| n.is_resolved() && !matches!(n, Name::Local(_)))
                {
                    return opaque(open, msg!("kernel-core-not-kernel-term"));
                }
                let depth = scope.len();
                scope.extend(params.iter().cloned());
                let mut acc = self.read_in(body, scope, open)?;
                scope.truncate(depth);
                for n in params.iter().rev() {
                    acc = Lam(Hint::named(n), Arc::new(acc));
                }
                acc
            }
            _ => return opaque(open, msg!("kernel-core-not-kernel-term")),
        })
    }

    fn fresh(&mut self, ty: Tm) -> u64 {
        self.next += 1;
        self.lctx.insert(self.next, ty);
        self.next
    }

    /// The innermost pair of parts (in weak head normal form) that make `a`
    /// and `b` differ, written back as named terms; `None` when they are
    /// convertible. The walk is over the shared terms, so only the two parts
    /// it ends at are written out, however large the values around them.
    pub(super) fn difference_in(&mut self, ctx: &Ctx, a: &T, b: &T) -> Option<(T, T)> {
        self.ask(ctx, &[a, b], |c, read, o| {
            let (mut x, mut y) = (read[0].clone(), read[1].clone());
            // The last step down was to arguments of a name, as written.
            let mut named = false;
            loop {
                // `b + k` against `c + j` (`Core::offset_view`): the bases
                // when `k` and `j` are the same, else these two, rather than
                // taking `Succ` off one at a time.
                if let Some((p, k)) = c.offset_view_top(&Arc::new(x.clone()))
                    && let Some((q, j)) = c.offset_view_top(&Arc::new(y.clone()))
                {
                    if k != j {
                        break;
                    }
                    (x, y) = (p, q);
                    continue;
                }
                // The same name applied on both sides: the arguments that
                // differ, as written, before the name is unfolded. Unfolding
                // first shows the parts in words the reader did not write,
                // and a name whose value computes deep (`pow2(n + 4000)`)
                // is unfolded and compared again at every step down.
                if let ((Const(f), xs), (Const(g), ys)) = (spine_rc(&x), spine_rc(&y))
                    && f == g
                    && !xs.is_empty()
                    && xs.len() == ys.len()
                    && let Some((p, q)) = xs.iter().zip(&ys).find(|(p, q)| !c.conv(p, q))
                {
                    (x, y) = ((**p).clone(), (**q).clone());
                    named = true;
                    continue;
                }
                // Reduced, the two are shown as they were when they do not
                // come apart any further.
                let (mut wx, mut wy) = (c.whnf(&x), c.whnf(&y));
                if matches!(wx, Lit(_)) != matches!(wy, Lit(_)) {
                    wx = unfold_lit(wx);
                    wy = unfold_lit(wy);
                }
                let (f, xs) = spine_rc(&wx);
                let (g, ys) = spine_rc(&wy);
                if xs.is_empty() || xs.len() != ys.len() || !c.conv(f, g) {
                    // A numeral is shown as the constructor it is beside one.
                    if !named || matches!(x, Lit(_)) || matches!(y, Lit(_)) {
                        (x, y) = (wx, wy);
                    }
                    break;
                }
                let Some((p, q)) = xs.iter().zip(&ys).find(|(p, q)| !c.conv(p, q)) else {
                    (x, y) = (wx, wy);
                    break;
                };
                let (p, q) = ((**p).clone(), (**q).clone());
                x = p;
                y = q;
                named = false;
            }
            // Cut where they grow large: a value that shares its parts is a
            // tree far larger than its nodes.
            let x = Self::write(
                &pruned(&x, &mut SHOWN_NODES.clone()),
                o,
                &mut Vec::new(),
                a.span,
            );
            let y = Self::write(
                &pruned(&y, &mut SHOWN_NODES.clone()),
                o,
                &mut Vec::new(),
                b.span,
            );
            Some((x, y))
        })
    }

    /// `t` in normal form in `ctx`, written back as a named term: reduced at
    /// its head, then in each part. It only shows a value; nothing checks
    /// by it.
    pub(super) fn nf_in(&mut self, ctx: &Ctx, t: &T) -> T {
        self.ask(ctx, &[t], |c, read, o| {
            let n = c.nf(&read[0]);
            Self::write(&n, o, &mut Vec::new(), t.span)
        })
    }

    pub(super) fn proof_reduction_in(
        &mut self,
        ctx: &[(Name, T)],
        t: &T,
    ) -> Option<super::derivation::ProofReduction> {
        self.start_budget(Some(4096), None);
        let normal = self.nf_in(&ctx.to_vec(), t);
        let mut unfolded: Vec<Name> = self
            .budget
            .unfolds
            .keys()
            .cloned()
            .map(Name::Global)
            .collect();
        unfolded.sort();
        let spent = self.end_budget();
        (!spent.out).then_some(super::derivation::ProofReduction { normal, unfolded })
    }

    fn nf(&mut self, t: &Tm) -> Tm {
        let w = self.whnf(t);
        match &w {
            Pi(h, a, b) => Pi(h.clone(), Arc::new(self.nf(a)), Arc::new(self.nf(b))),
            Lam(h, b) => Lam(h.clone(), Arc::new(self.nf(b))),
            App(f, x) => App(Arc::new(self.nf(f)), Arc::new(self.nf(x))),
            _ => w,
        }
    }

    fn whnf(&mut self, t: &Tm) -> Tm {
        self.whnf_with(t, true)
    }

    /// `t` reduced at its head; a name with a value is unfolded only when
    /// `delta`.
    fn whnf_with(&mut self, t: &Tm, delta: bool) -> Tm {
        self.whnf_node(Arc::new(t.clone()), delta)
    }

    /// [`Core::whnf_with`] of a node. With `delta`, reduction is call by
    /// need: every node it goes through as the whole term, or as the head of
    /// it, that is shared with another term (an argument substituted for a
    /// variable, a field of a constructor, the value of a name) keeps the weak
    /// head normal form found (`Core::shared`), and is not reduced again
    /// wherever it is met.
    fn whnf_node(&mut self, t: R, delta: bool) -> Tm {
        // An eliminator is left as it is (`lazy_iota`) only by the reduction
        // without `delta` that `Core::whnf_lazy` asks for. A reduction with
        // `delta` on the way (an operand of `+`, a numeral) reduces fully: what
        // it finds is kept as the node's weak head normal form (`remember`),
        // and an eliminator left there would be found again stuck.
        let mode = match (delta, self.lazy_iota) {
            (true, _) => Mode::Full,
            (false, true) => Mode::Lazy,
            (false, false) => Mode::Head,
        };
        self.drive(t, mode, None).0
    }

    /// The reduction of `t` taken to its end, and whether it ended where
    /// `watch` says.
    ///
    /// A reduction waits for the weak head normal form of a part of its
    /// term wherever it reduces on one: the major premise of an eliminator,
    /// an operand of `+`. The part is reduced in a call inside the
    /// reduction that waits ([`Core::need`]), up to [`DEPTH`] of them one
    /// inside another. One more is not called: the reductions that wait are
    /// set aside as they stand ([`Deep`]) and kept here, outermost first,
    /// while the part is reduced from here; each is then taken up again
    /// where it stopped, and finds what it waited for in `forced`. A term
    /// whose reduction goes through a million of them, one waiting for the
    /// next (`f(n)` that matches on `f(n - 1)`), takes a million entries
    /// here, and no more of the stack than [`DEPTH`] calls.
    fn drive(&mut self, t: R, mode: Mode, watch: Option<Watch>) -> (Tm, bool) {
        let depth = std::mem::replace(&mut self.depth, 1);
        self.drives += 1;
        // The reductions set aside, each with the node it reduces; the one
        // asked for here (the first) has none.
        let mut waiting: Vec<(Option<R>, Task)> = Vec::new();
        let mut node: Option<R> = None;
        let mut task = Task::new(t, mode);
        task.watch = watch.map(Box::new);
        let out = loop {
            match self.run(&mut task) {
                Ok(w) => {
                    let Some(n) = node.take() else {
                        break (w, task.met);
                    };
                    self.forced[task.mode as usize].insert(Arc::as_ptr(&n) as usize, (n, w));
                    (node, task) = waiting.pop().expect("the reduction that waited");
                }
                Err(deep) => {
                    let Deep { want, mode, tasks } = *deep;
                    waiting.push((node.take(), task));
                    waiting.extend(tasks.into_iter().rev().map(|(n, t)| (Some(n), t)));
                    task = Task::new(want.clone(), mode);
                    node = Some(want);
                }
            }
        };
        self.drives -= 1;
        // What was kept for the reductions set aside is of no use once the
        // outermost of these loops ends.
        if self.drives == 0 {
            for kept in &mut self.forced {
                if !kept.is_empty() {
                    kept.clear();
                }
            }
        }
        self.depth = depth;
        out
    }

    /// The weak head normal form of `node` (as far as `mode` goes) for a
    /// reduction that reduces on it. It is found in a call here, unless
    /// [`DEPTH`] reductions already wait on the stack: then nothing is
    /// reduced, and the reduction that asked is set aside ([`Deep`]) until
    /// [`Core::drive`] has reduced `node`.
    fn need(&mut self, node: &R, mode: Mode) -> Step<Tm> {
        let forced = &self.forced[mode as usize];
        if !forced.is_empty()
            && let Some((_, w)) = forced.get(&(Arc::as_ptr(node) as usize))
        {
            return Ok(w.clone());
        }
        // Outside any reduction: nothing waits, and nothing can be set aside.
        if self.depth == 0 {
            return Ok(self.drive(node.clone(), mode, None).0);
        }
        if self.depth >= DEPTH {
            return Err(Box::new(Deep {
                want: node.clone(),
                mode,
                tasks: Vec::new(),
            }));
        }
        let mut task = Task::new(node.clone(), mode);
        self.depth += 1;
        let r = self.run(&mut task);
        self.depth -= 1;
        r.map_err(|mut deep| {
            deep.tasks.push((node.clone(), task));
            deep
        })
    }

    /// `f`, which reduces parts of terms as a step of reduction does
    /// ([`Core::need`]), run outside any reduction: every part is reduced to
    /// its end before `f` goes on, so nothing is set aside. `None` only if
    /// something was, which gives the declaration up (`budget.out`).
    fn top<X>(&mut self, f: impl FnOnce(&mut Self) -> Step<X>) -> Option<X> {
        let depth = std::mem::replace(&mut self.depth, 0);
        let r = f(self);
        self.depth = depth;
        match r {
            Ok(x) => Some(x),
            Err(_) => {
                self.budget.out = true;
                None
            }
        }
    }

    /// The steps of `task` to their end ([`Core::whnf_steps`]). What they end
    /// in is kept as the weak head normal form of the shared nodes on the
    /// way, when the reduction unfolds every name and did not stop short.
    fn run(&mut self, task: &mut Task) -> Step<Tm> {
        let lazy = std::mem::replace(&mut self.lazy_iota, task.mode == Mode::Lazy);
        let r = self.whnf_steps(task);
        self.lazy_iota = lazy;
        let w = r?;
        if task.mode == Mode::Full && !task.met && !self.budget.out {
            for n in std::mem::take(&mut task.became) {
                self.remember(n, w.clone());
            }
        }
        Ok(w)
    }

    /// Keeps `w`, the weak head normal form of `n`, for as long as `n` is
    /// used somewhere. The entry holds `n` weakly: while the entry is there,
    /// `n`'s allocation is not freed and its address not reused, so an entry
    /// is only ever found by `n` itself. The entries of nodes that are gone
    /// are dropped as the table grows, with what they reduced to.
    fn remember(&mut self, n: R, w: Tm) {
        poll_deadline();
        let key = Arc::as_ptr(&n) as usize;
        self.shared.insert(key, (Arc::downgrade(&n), w));
        sweep(&mut self.shared);
    }

    fn recall(&self, n: &R) -> Option<Tm> {
        self.shared
            .get(&(Arc::as_ptr(n) as usize))
            .map(|e| e.1.clone())
    }

    /// The steps of reduction at the head of `task.t`, until none applies.
    /// A step that reduces on a part of the term asks for the part's weak
    /// head normal form ([`Core::need`]); when that sets the reduction aside
    /// (`Err`), `task` stands at the step that asked, which is taken again
    /// when the reduction is taken up.
    fn whnf_steps(&mut self, task: &mut Task) -> Step<Tm> {
        let delta = task.mode == Mode::Full;
        // A head just replaced is in weak head normal form: the next step is
        // one of reduction, so a head is never replaced twice in a row.
        loop {
            if self.spend() {
                return Ok((*task.t).clone());
            }
            // What a node was found to reduce to is a reduct of it with
            // or without `delta`; only with `delta` is what is found kept, as
            // the weak head normal form that unfolds every name.
            if Arc::weak_count(&task.t) > 0
                && let Some(w) = self.recall(&task.t)
            {
                return Ok(w);
            }
            // A node only this loop holds cannot be met again. (A reduction
            // taken up again stands at a node it has noted already.)
            if delta
                && Arc::strong_count(&task.t) > 1
                && !task.became.last().is_some_and(|b| Arc::ptr_eq(b, &task.t))
            {
                task.became.push(task.t.clone());
            }
            // A shared head reduced before goes on as what it became:
            // the same reduction, its first steps not taken again.
            if !task.recalled
                && let Some(next) = self.recalled_head(&task.t)
            {
                task.t = Arc::new(next);
                task.recalled = true;
                continue;
            }
            task.recalled = false;
            let (head, args) = spine_rc(&task.t);
            match head {
                FVar(x) if self.lvals.contains_key(x) => {
                    if !delta {
                        return Ok(Self::stopped(&task.t, &mut task.became));
                    }
                    task.t = apps_node(self.lvals[x].clone(), args);
                }
                Lam(_, body) if !args.is_empty() => {
                    // `inst_rc` gives the argument itself for a body that is
                    // its variable, so that node is still the one met again.
                    // The λs at the head that have an argument each are
                    // gone under together and their values put in at once
                    // (`inst_env`): putting them in one at a time walks the
                    // body once per argument, and the body of a function
                    // that matches is every case of the eliminator.
                    let mut inner = body;
                    let mut taken = 1;
                    while taken < args.len()
                        && let Lam(_, b) = &**inner
                    {
                        inner = b;
                        taken += 1;
                    }
                    let body = if taken == 1 {
                        inst_rc(body, 0, &args[0]).unwrap_or_else(|| body.clone())
                    } else {
                        inst_env(inner, 0, &args[..taken])
                    };
                    task.t = apps_node(body, args.into_iter().skip(taken));
                }
                Const(c) => {
                    // The turn of the loop this reduction is run up to.
                    if task.watch.as_ref().is_some_and(|w| w.met(c, &args)) {
                        task.met = true;
                        return Ok((*task.t).clone());
                    }
                    // A shortcut for unfolding the name, so only with `delta`:
                    // without it, the arguments are not reduced either.
                    if delta && let Some(next) = self.numeric(c, &args)? {
                        task.t = Arc::new(next);
                        continue;
                    }
                    if let Some(v) = self.globals.get(c).and_then(|g| g.value.clone()) {
                        if !delta {
                            return Ok(Self::stopped(&task.t, &mut task.became));
                        }
                        *self.budget.unfolds.entry(c.clone()).or_default() += 1;
                        self.budget.last_unfold = Some(c.clone());
                        task.t = apps_node(v, args);
                        continue;
                    }
                    let c = c.clone();
                    if let Some(op) = primitive_operator(&c)
                        && let Some(next) = self.arith(op, &args)?
                    {
                        task.t = Arc::new(next);
                        continue;
                    }
                    if self.recs.contains_key(&c)
                        && let Some(next) = self.iota(&c, &args, task.mode)?
                    {
                        task.t = next;
                        continue;
                    }
                    if self.quot.contains(&c)
                        && let Some(next) = self.quot_iota(&c, &args)?
                    {
                        task.t = next;
                        continue;
                    }
                    return Ok(Self::stopped(&task.t, &mut task.became));
                }
                _ => return Ok(Self::stopped(&task.t, &mut task.became)),
            }
        }
    }

    /// `t` with the functions at its head applied to their arguments, and
    /// nothing else reduced: a prefix of [`Core::whnf`].
    fn beta_head(&mut self, t: &Tm) -> Tm {
        // The term reached is `apps(inst_env(cur, env), args)`, the
        // arguments not yet taken in `args` from the last: a step of
        // reduction takes the first of them into `env` and goes under the
        // λ, and the body is written out with every value taken only where
        // reduction stops. Putting each argument into the body as it is
        // taken would walk the rest of the body once per step, and a chain of
        // `let`s is one step per `let`. The steps are those of reducing the
        // head one redex at a time, the budget spent at each as there.
        let mut cur: R = Arc::new(t.clone());
        let mut env: Vec<R> = Vec::new();
        let mut args: Vec<R> = Vec::new();
        loop {
            // The head of the term reached, its arguments taken out.
            loop {
                match &*cur {
                    App(..) => {
                        let mut f = cur.clone();
                        let mut own = Vec::new();
                        while let App(g, a) = &*f.clone() {
                            own.push(inst_env(a, 0, &env));
                            f = g.clone();
                        }
                        args.extend(own);
                        cur = f;
                    }
                    BVar(i) if *i < env.len() => {
                        cur = env[env.len() - 1 - i].clone();
                        env.clear();
                    }
                    _ => break,
                }
            }
            if self.spend() {
                break;
            }
            match (&*cur, args.pop()) {
                (Lam(_, body), Some(a)) => {
                    env.push(a);
                    cur = body.clone();
                }
                (_, Some(a)) => {
                    args.push(a);
                    break;
                }
                (_, None) => break,
            }
        }
        apps_rc((*inst_env(&cur, 0, &env)).clone(), args.into_iter().rev())
    }

    /// `t`, where reduction stopped. It reduces to itself, which is not
    /// kept: a node is kept only with what it became by taking steps.
    fn stopped(t: &R, became: &mut Vec<R>) -> Tm {
        if became.last().is_some_and(|b| Arc::ptr_eq(b, t)) {
            became.pop();
        }
        (**t).clone()
    }

    /// `t` with its head replaced by what it was found to reduce to, when a
    /// shared node of its spine below `t` itself was reduced before.
    fn recalled_head(&self, t: &R) -> Option<Tm> {
        let mut node = t;
        let mut args: Vec<R> = Vec::new();
        while let App(f, a) = &**node {
            args.push(a.clone());
            node = f;
            if Arc::weak_count(node) > 0
                && let Some(w) = self.recall(node)
            {
                args.reverse();
                return Some(apps_rc(w, args));
            }
        }
        None
    }

    /// The weak head normal form of `t`, found again when the same node was
    /// reduced before in this declaration. An argument substituted for a
    /// variable is one node wherever the variable was (`inst_at_rc`), so it is
    /// reduced once however often it is used.
    fn whnf_shared(&mut self, t: &R) -> Tm {
        // The form kept for the node is the node's own weak head normal form, so
        // it is never taken lazily ([`Core::whnf_lazy`]): an eliminator left
        // stuck on a major premise that needs unfolding would be found again, as
        // if it were normal, by the next to read the node (the operand of `*`
        // that is `Zero` only once a name is unfolded).
        self.drive(t.clone(), Mode::Full, None).0
    }

    /// One step of reduction; true once the limit on the steps is reached or
    /// the deadline has passed.
    fn spend(&mut self) -> bool {
        let b = &mut self.budget;
        b.steps += 1;
        if !b.out && b.limit.is_some_and(|l| b.steps > l) {
            b.out = true;
            b.out_of_steps = true;
        }
        if !b.out && b.deadline.is_some() && PASSED.with(|p| p.get()) {
            b.out = true;
        }
        if !b.out
            && b.steps % 1024 == 0
            && b.deadline
                .is_some_and(|d| crate::clock::Instant::now() >= d)
        {
            b.out = true;
        }
        b.out
    }

    /// Whether the deadline has passed, for the loops that take no step of
    /// reduction: they stop early once it is, and the declaration is rejected
    /// (`budget.out`), as when [`Self::spend`] sees the deadline.
    fn timed_out(&mut self) -> bool {
        poll_deadline();
        let b = &mut self.budget;
        if !b.out && b.deadline.is_some() && PASSED.with(|p| p.get()) {
            b.out = true;
        }
        b.out
    }

    /// Starts counting the reduction of a declaration, to give up past
    /// `limit` steps or at `deadline`.
    pub(super) fn start_budget(
        &mut self,
        limit: Option<u64>,
        deadline: Option<crate::clock::Instant>,
    ) {
        self.budget = Budget {
            deadline,
            limit,
            ..Budget::default()
        };
        DEADLINE.with(|d| d.set(deadline));
        PASSED.with(|p| p.set(false));
    }

    /// The reduction `other` did, as the declaration in hand's.
    pub(super) fn adopt_budget(&mut self, other: &mut Core) {
        self.budget = std::mem::take(&mut other.budget);
    }

    pub(super) fn budget_out(&self) -> bool {
        self.budget.out || (self.budget.deadline.is_some() && PASSED.with(|p| p.get()))
    }

    /// The reduction the declaration in hand did; the count starts again.
    pub(super) fn end_budget(&mut self) -> Spent {
        let passed = self.budget.deadline.is_some() && PASSED.with(|p| p.get());
        let b = std::mem::take(&mut self.budget);
        DEADLINE.with(|d| d.set(None));
        PASSED.with(|p| p.set(false));
        drop_aside(std::mem::take(&mut self.shared));
        self.no_repeat.clear();
        forget_loose();
        let mut top: Vec<(String, u64)> = b
            .unfolds
            .into_iter()
            .map(|(n, k)| (n.to_string(), k))
            .collect();
        top.sort_by(|x, y| y.1.cmp(&x.1).then_with(|| x.0.cmp(&y.0)));
        top.truncate(3);
        Spent {
            steps: b.steps,
            out: b.out || passed,
            out_of_steps: b.out_of_steps,
            reached_in: b
                .last_unfold
                .filter(|_| b.out_of_steps)
                .map(|n| n.to_string()),
            top,
            past_limit: b.past_limit,
        }
    }

    /// `t` reduced, except that `+`, `*` and `-` are only computed on
    /// numerals: reducing them otherwise can go as deep as their number
    /// (`a * b` past the largest numeral unfolds `b` times), and the steps of [`Self::arith`]
    /// take them one at a time instead.
    /// `a` and `b` the same `+` or `*` stuck on its operands, and the pairs
    /// of operands they are as convertible as. `+` and `*` reduce on their
    /// second operand: when it is stuck on a variable on both sides, so is
    /// each side, on an eliminator whose arguments hold the operands.
    /// `x * k` against `y * k` with the same numeral `k > 0` and stuck `x`
    /// and `y` is as convertible as `x` and `y`: `*` unfolds on `k` to
    /// `x * (k - 1) + x`, stuck on `x`. Reducing them instead to compare
    /// what they reduce to goes as deep as `k`, and for a large `k` (a
    /// limb's `2147483648`) overflows the stack.
    fn stuck_arith(&mut self, a: &R, b: &R) -> Option<Vec<(R, R)>> {
        let ((Const(f), xs), (Const(g), ys)) = (spine_rc(a), spine_rc(b)) else {
            return None;
        };
        let p = self.arith_op(f)?;
        if self.arith_op(g)? != p || xs.len() != 2 || ys.len() != 2 {
            return None;
        }
        if matches!(p, "+" | "*") && self.stuck_number(&xs[1]) && self.stuck_number(&ys[1]) {
            return Some(vec![
                (xs[0].clone(), ys[0].clone()),
                (xs[1].clone(), ys[1].clone()),
            ]);
        }
        if p == "*"
            && matches!(
                (self.number_top(&xs[1]), self.number_top(&ys[1])),
                (Some(k), Some(j)) if k == j && !k.is_zero()
            )
            && self.stuck_number(&xs[0])
            && self.stuck_number(&ys[0])
        {
            return Some(vec![(xs[0].clone(), ys[0].clone())]);
        }
        None
    }

    /// Whether the number `t` reduces to a term stuck on a variable: neither
    /// a numeral, `Zero` nor `Succ`. A `+` or `*`, which
    /// [`Self::literal_or_whnf`] leaves as it is, is stuck when its second
    /// operand, the one it reduces on, is.
    fn stuck_number(&mut self, t: &R) -> bool {
        let mut t = t.clone();
        loop {
            let Some(w) = self.top(|c| c.literal_or_whnf(&t)) else {
                return false;
            };
            let (head, args) = spine_rc(&w);
            let Const(c) = head else {
                return matches!(head, FVar(_));
            };
            if c.is_primitive("Succ") || c.is_primitive("Zero") {
                return false;
            }
            match self.arith_op(c) {
                None => return true,
                Some("+" | "*") if args.len() == 2 => t = args[1].clone(),
                Some(_) => return false,
            }
        }
    }

    fn literal_or_whnf(&mut self, t: &R) -> Step<Tm> {
        let (head, args) = spine_rc(t);
        if let Const(c) = head
            && let Some(op) = primitive_operator(c)
        {
            // The second operand first: when it is not a numeral the first is
            // not looked at. Unfolding `pow2(k + 31)` gives `x * 1 + x` with
            // `x` shared; reading both operands of each node goes through the
            // shared `x` twice per level, `2^31` times.
            if let [x, y] = args.as_slice()
                && let Some(y) = self.number(y)?
                && let Some(x) = self.number(x)?
            {
                match lit_op(op, x, y) {
                    Some(n) => return Ok(Lit(n)),
                    None => self.past_limit(op, x, y),
                }
            }
            return Ok((**t).clone());
        }
        self.need(t, Mode::Full)
    }

    /// The number `t` is when [`Core::literal_or_whnf`] gives a numeral, or a
    /// numeral written with a few constructors (`Succ(Zero)`).
    fn number(&mut self, t: &R) -> Step<Option<Num>> {
        match self.literal_or_whnf(t)? {
            Lit(x) => Ok(Some(x)),
            w => self.numeral_of(w),
        }
    }

    /// One step of `+`, `*` or `-`, which are defined by recursion on the
    /// second operand:
    ///
    /// * `a + Zero = a`, `a + Succ(k) = Succ(a + k)`;
    /// * `a * Zero = Zero`, `a * Succ(k) = a * k + a`;
    /// * `a - Zero = a`, `a - Succ(k) = pred(a - k)`.
    ///
    /// Two numerals are computed at once, which is what these equations give
    /// (a sum or product past the largest numeral is left to them). Otherwise the second
    /// operand must be `Zero` or `Succ(k)` (a numeral reads as one); when it
    /// is not, the term stays as it is.
    fn arith(&mut self, op: &str, args: &[R]) -> Step<Option<Tm>> {
        if args.len() < 2 {
            return Ok(None);
        }
        let b = self.need(&args[1], Mode::Full)?;
        let a = if matches!(b, Lit(_)) {
            // Reduced once here, so that the steps below do not reduce it again.
            self.literal_or_whnf(&args[0])?
        } else {
            (*args[0]).clone()
        };
        self.arith_with(op, a, b, &args[2..])
    }

    /// [`Core::arith`] with its operands in hand: `a` as it reads the first,
    /// `b` the second reduced, and `rest` what the operation is applied to
    /// after them.
    fn arith_with(&mut self, op: &str, a: Tm, b: Tm, rest: &[R]) -> Step<Option<Tm>> {
        let rest = rest.iter().cloned();
        if let Lit(y) = b {
            let x = match &a {
                Lit(x) => Some(*x),
                // `Succ(Zero)` and the like: a numeral written with constructors.
                _ => self.numeral_of(a.clone())?,
            };
            if let Some(x) = x {
                match lit_op(op, x, y) {
                    Some(n) => return Ok(Some(apps_rc(Lit(n), rest))),
                    // Taking it one `Succ` at a time would not end: the term
                    // stays as it is (`Core::past_limit`).
                    None => {
                        self.past_limit(op, x, y);
                        return Ok(None);
                    }
                }
            }
        }
        let Some(view) = self.nat_view(&b) else {
            return Ok(None);
        };
        let out = match (op, view) {
            ("+" | "-", None) => a,
            (_, None) => Lit(Num::ZERO),
            ("+", Some(k)) => app(konst("Succ"), apps(konst("+"), [a, k])),
            ("*", Some(k)) => apps(konst("+"), [apps(konst("*"), [a.clone(), k]), a]),
            (_, Some(k)) => match self.minus(a, k)? {
                Some(out) => out,
                // `pred` of a difference that does not reduce: it stays `a - b`.
                None => return Ok(None),
            },
        };
        Ok(Some(apps_rc(out, rest)))
    }

    /// `pred(a - k)`: what `a - Succ(k)` reduces to, or `None` when it does
    /// not reduce. By the equations of `-` it is one `pred` for each `Succ`
    /// of `k`, and one more, of `a`; each `pred` reduces on what is below
    /// it. They are counted going down `k` and taken coming back up, in two
    /// loops, where taking each inside the next goes as deep as `k`. A
    /// `pred` of what is neither `Zero` nor a `Succ` does not reduce, and
    /// then none above it does.
    fn minus(&mut self, a: Tm, k: Tm) -> Step<Option<Tm>> {
        let mut a = Arc::new(a);
        let mut k = Arc::new(k);
        // The `pred`s met going down, the one this is not counted.
        let mut preds: Num = Num::ZERO;
        // `a - k` at the bottom, reduced.
        let mut d = loop {
            if self.timed_out() {
                return Ok(None);
            }
            let b = self.need(&k, Mode::Full)?;
            if let Lit(y) = b {
                // The first operand is read as `Core::arith` reads it.
                let read = self.literal_or_whnf(&a)?;
                let x = match &read {
                    Lit(x) => Some(*x),
                    _ => self.numeral_of(read.clone())?,
                };
                if let Some(x) = x {
                    break Lit(x.saturating_sub(y));
                }
                let Some(total) = preds.checked_add(y) else {
                    // Leave the difference unreduced when the count cannot be represented.
                    return Ok(None);
                };
                preds = total;
                a = Arc::new(read);
                break self.need(&a, Mode::Full)?;
            }
            match self.nat_view_node(&b) {
                None => return Ok(None),
                Some(None) => break self.need(&a, Mode::Full)?,
                Some(Some(j)) => {
                    preds = preds + Num::ONE;
                    k = j;
                }
            }
        };
        while !preds.is_zero() {
            if self.timed_out() {
                return Ok(None);
            }
            // Nothing is below zero, however many `pred`s are left.
            if let Lit(n) = d {
                d = Lit(n.saturating_sub(preds));
                break;
            }
            match self.nat_view_node(&d) {
                None => return Ok(None),
                Some(None) => {
                    d = Lit(Num::ZERO);
                    break;
                }
                Some(Some(j)) => d = self.need(&j, Mode::Full)?,
            }
            preds = preds - Num::ONE;
        }
        Ok(match self.nat_view(&d) {
            None => None,
            Some(None) => Some(Lit(Num::ZERO)),
            Some(Some(j)) => Some(j),
        })
    }

    /// Notes that `x op y`, two numerals whose result is past the largest numeral, is left
    /// as it is. Computing it by the equations of [`Core::arith`] takes a step
    /// for each `Succ` of the result, which does not end. A term that is not
    /// reduced is never convertible to more than it is, so leaving it is
    /// sound; a comparison that needed its value fails, and the failure says
    /// why ([`Spent::past_limit`]).
    fn past_limit(&mut self, op: &str, x: Num, y: Num) {
        self.budget
            .past_limit
            .get_or_insert_with(|| format!("{x} {op} {y}"));
    }

    /// The number `t` reduces to when it is a numeral, or `Succ`s of one
    /// (`nat_le(a, b)` is `nat_lt(a, Succ(b))`, `list_length(l)` is a
    /// `Succ` for each element).
    fn numeral(&mut self, t: &R) -> Step<Option<Num>> {
        let w = self.need(t, Mode::Full)?;
        self.numeral_of(w)
    }

    /// [`Core::number`], asked outside any reduction ([`Core::top`]).
    fn number_top(&mut self, t: &R) -> Option<Num> {
        self.top(|c| c.number(t)).flatten()
    }

    /// [`Core::offset_view`], asked outside any reduction ([`Core::top`]).
    fn offset_view_top(&mut self, t: &R) -> Option<(Tm, Num)> {
        self.top(|c| c.offset_view(t)).flatten()
    }

    /// [`Core::numeral`] of a term already in weak head normal form.
    ///
    /// Every `Succ` is followed, so a closed number written with
    /// constructors is read whatever its size. Below a `Succ`, a sum,
    /// product or difference is only computed on numerals
    /// ([`Core::literal_or_whnf`]): `x + 1000` with an unknown `x` reduces to
    /// `Succ(x + 999)`, and it stops there instead of unfolding the sum once
    /// for each `Succ`.
    fn numeral_of(&mut self, mut w: Tm) -> Step<Option<Num>> {
        let mut more: Num = Num::ZERO;
        loop {
            if self.timed_out() {
                return Ok(None);
            }
            match &w {
                Lit(k) => return Ok(k.checked_add(more)),
                Const(c) if c.is_primitive("Zero") => return Ok(Some(more)),
                App(f, x) if matches!(&**f, Const(c) if c.is_primitive("Succ")) => {
                    let Some(next) = more.checked_add(Num::ONE) else {
                        return Ok(None);
                    };
                    more = next;
                    let x = x.clone();
                    w = self.literal_or_whnf(&x)?;
                }
                _ => return Ok(None),
            }
        }
    }

    /// `t` as `base + k`: the `Succ`s and the `+ n` of a numeral `n` around
    /// `t` taken off, counted in `k` at once (`x + 9007199254740992` is one
    /// step, not that many `Succ`s). `base` is a weak head normal form that
    /// is neither of those nor a numeral; `None` when `t` is a numeral, when
    /// `k` passes the largest numeral, or when no `+ n` was taken off (a few `Succ`s are
    /// compared as they are). Nothing is reduced unless `t`, under its
    /// `Succ`s, is applied last to a numeral of at least [`LARGE_OFFSET`]
    /// (`x + n` or `Nat::add(x, n)`): below that, `Succ` by `Succ` is as good.
    fn offset_view(&mut self, t: &R) -> Step<Option<(Tm, Num)>> {
        let mut s: &Tm = t;
        while let App(f, x) = s
            && matches!(&**f, Const(c) if c.is_primitive("Succ"))
        {
            s = x;
        }
        // `x + (y + n)` ends in `n` as well: it is `x + y` with `n` more `Succ`s.
        let mut last = s;
        while let (Const(c), args) = spine_rc(last)
            && c.is_primitive("+")
            && let [_, y] = args.as_slice()
            && matches!(spine_rc(y).0, Const(d) if d.is_primitive("+"))
        {
            let App(_, y) = last else { break };
            last = y;
        }
        // The numeral may be a `let` of one (`m := 2^53` in `x + m`), or a
        // closed term that computes to one (`x + p()`).
        let large = match last {
            App(_, n) => match &**n {
                Lit(k) => *k >= LARGE_OFFSET,
                FVar(x) if self.lvals.contains_key(x) => {
                    matches!(self.literal_or_whnf(n)?, Lit(k) if k >= LARGE_OFFSET)
                }
                Const(_) | App(..) if constant_on_numerals(n) => {
                    matches!(self.literal_or_whnf(n)?, Lit(k) if k >= LARGE_OFFSET)
                }
                _ => false,
            },
            _ => false,
        };
        if !large {
            return Ok(None);
        }
        // Only a sum is taken apart: `Nat::lt(x + n, m)` also ends in a
        // numeral, but reducing it to read a `Succ` off runs `lt` down `n`
        // steps, one `Succ` of each side at a time.
        if !matches!(spine_rc(s).0, Const(c) if self.is_sum(c)) {
            return Ok(None);
        }
        let mut k: Num = Num::ZERO;
        let mut plus = false;
        let mut t = t.clone();
        loop {
            if self.timed_out() {
                return Ok(None);
            }
            if let (Const(c), args) = spine_rc(&t)
                && c.is_primitive("+")
                && let [x, y] = args.as_slice()
                && let Lit(n) = self.literal_or_whnf(y)?
            {
                let Some(sum) = k.checked_add(n) else {
                    return Ok(None);
                };
                k = sum;
                plus = true;
                t = x.clone();
                continue;
            }
            // `x + (y + n)` reduces as `x + y` does below `n` `Succ`s: the
            // second operand `y + n` is `n` `Succ`s on `y + 0`, which reduces
            // as `y` does.
            if let (Const(c), args) = spine_rc(&t)
                && c.is_primitive("+")
                && let [x, y] = args.as_slice()
                && let (Const(d), inner) = spine_rc(y)
                && d.is_primitive("+")
                && let [y, n] = inner.as_slice()
                && let Lit(n) = self.literal_or_whnf(n)?
            {
                let Some(sum) = k.checked_add(n) else {
                    return Ok(None);
                };
                k = sum;
                plus = true;
                t = Arc::new(apps(konst("+"), [(**x).clone(), (**y).clone()]));
                continue;
            }
            let w = self.need(&t, Mode::Full)?;
            match &w {
                Lit(_) => return Ok(None),
                Const(c) if c.is_primitive("Zero") => return Ok(None),
                App(f, x) if matches!(&**f, Const(c) if c.is_primitive("Succ")) => {
                    let Some(sum) = k.checked_add(Num::ONE) else {
                        return Ok(None);
                    };
                    k = sum;
                    t = x.clone();
                }
                _ => {
                    if let (Const(c), args) = spine_rc(&w)
                        && c.is_primitive("+")
                        && args.len() == 2
                        && w != *t
                    {
                        t = Arc::new(w);
                        continue;
                    }
                    return Ok(plus.then_some((w, k)));
                }
            }
        }
    }

    /// Whether `c` is `+`, or a name defined as a sum of its parameters
    /// (`Nat::add(a, b)` is `a + b`): what [`Core::offset_view`] reads `+ n`
    /// off.
    fn is_sum(&self, c: &DeclRef) -> bool {
        if c.is_primitive("+") {
            return true;
        }
        let Some(mut v) = self.globals.get(c).and_then(|g| g.value.clone()) else {
            return false;
        };
        while let Lam(_, b) = &*v {
            v = b.clone();
        }
        matches!(spine_rc(&v), (Const(h), args) if h.is_primitive("+") && args.len() == 2)
    }

    /// The operator `+`, `*` or `-` that `c` is: the operator itself, or a
    /// name defined as it on its two parameters in order (`Nat::add(a, b)`
    /// is `a + b`). Two such applications to convertible operands are
    /// convertible without unfolding the name.
    fn arith_op(&self, c: &DeclRef) -> Option<&'static str> {
        let op = primitive_operator;
        if let Some(o) = op(c) {
            return Some(o);
        }
        let v = self.globals.get(c)?.value.clone()?;
        let Lam(_, b) = &*v else { return None };
        let Lam(_, b) = &**b else { return None };
        let (Const(h), args) = spine_rc(b) else {
            return None;
        };
        let in_order = matches!(args.as_slice(), [x, y] if **x == BVar(1) && **y == BVar(0));
        if in_order { op(h) } else { None }
    }

    /// `Nat::eq`, `Nat::lt`, `Nat::sub`, `Nat::div_nz` or `Nat::rem_nz` of the prelude
    /// (`prelude_nat.taut`) on two numerals, computed at once: what unfolding
    /// the definition gives (`numeric_agrees_with_unfolding` checks it). A
    /// program cannot declare these names again, so they are always these
    /// definitions.
    fn numeric(&mut self, c: &DeclRef, args: &[R]) -> Step<Option<Tm>> {
        if self.numeric_off {
            return Ok(None);
        }
        if c.is_primitive("Nat::divmod") {
            return self.divmod_offset(c, args);
        }
        let Some(operation) = NUMERIC.iter().copied().find(|n| c.is_primitive(n)) else {
            return Ok(None);
        };
        let arity = numeric_arity(operation);
        if args.len() < arity {
            return Ok(None);
        }
        let Some(x) = self.numeral(&args[0])? else {
            return Ok(None);
        };
        let Some(y) = self.numeral(&args[1])? else {
            return Ok(None);
        };
        let yn = |b: bool| konst(if b { "true" } else { "false" });
        let out = match operation {
            "Nat::eq" => yn(x == y),
            "Nat::lt" => yn(x < y),
            "Nat::sub" => Lit(x.saturating_sub(y)),
            // A divisor of 0 comes only with a proof of `¬(0 = 0)`, under a
            // false assumption; `Nat::divmod` then never meets a remainder
            // equal to zero: the quotient is 0 and the remainder `a`.
            "Nat::div_nz" => Lit(x.checked_div(y).unwrap_or(Num::ZERO)),
            _ => Lit(x.checked_rem(y).unwrap_or(x)),
        };
        *self.budget.unfolds.entry(c.clone()).or_default() += 1;
        self.budget.last_unfold = Some(c.clone());
        Ok(Some(apps_rc(out, args[arity..].iter().cloned())))
    }

    /// `Nat::divmod(x + n, b, q, r)` with numerals `n`, `b`, `q` and `r`,
    /// taken `n` steps at once to `Nat::divmod(x, b, q', r')`. Each step of
    /// the definition takes one `Succ` off the first argument and counts the
    /// remainder up, carrying into the quotient when it reaches `b`; `n` of
    /// them from `r < b` leave `q' = q + (r + n) / b` and `r' = (r + n) % b`.
    /// With `b = 0` or `r >= b` the remainder never reaches `b`, so it is
    /// `r + n`. Unfolding instead goes `n` steps, and `x + 2^32` modulo
    /// `2^32` would take `2^32` of them. Only an offset of at least
    /// [`LARGE_OFFSET`] is taken this way ([`Core::offset_view`]).
    fn divmod_offset(&mut self, c: &DeclRef, args: &[R]) -> Step<Option<Tm>> {
        if args.len() < 4 {
            return Ok(None);
        }
        let (Some(b), Some(q), Some(r)) = (
            self.numeral(&args[1])?,
            self.numeral(&args[2])?,
            self.numeral(&args[3])?,
        ) else {
            return Ok(None);
        };
        let Some((base, n)) = self.offset_view(&args[0])? else {
            return Ok(None);
        };
        let Some(t) = r.checked_add(n) else {
            return Ok(None);
        };
        let (q, r) = if !b.is_zero() && r < b {
            let Some(q) = q.checked_add(t.checked_div(b).expect("nonzero")) else {
                return Ok(None);
            };
            (q, t.checked_rem(b).expect("nonzero"))
        } else {
            (q, t)
        };
        *self.budget.unfolds.entry(c.clone()).or_default() += 1;
        self.budget.last_unfold = Some(c.clone());
        let head = apps(Const(c.clone()), [base, Lit(b), Lit(q), Lit(r)]);
        Ok(Some(apps_rc(head, args[4..].iter().cloned())))
    }

    /// `Some(None)` for a weak-head normal `t` that is zero, `Some(Some(k))`
    /// for one that is `Succ(k)`; a numeral is read as `Zero`/`Succ`.
    fn nat_view(&self, t: &Tm) -> Option<Option<Tm>> {
        match t {
            Lit(Num::ZERO) => Some(None),
            Lit(k) => Some(Some(Lit(*k - Num::ONE))),
            Const(c) if c.is_primitive("Zero") => Some(None),
            App(f, x) if matches!(&**f, Const(c) if c.is_primitive("Succ")) => {
                Some(Some((**x).clone()))
            }
            _ => None,
        }
    }

    /// [`Core::nat_view`] with the number under a `Succ` as the node it is.
    fn nat_view_node(&self, t: &Tm) -> Option<Option<R>> {
        match t {
            Lit(Num::ZERO) => Some(None),
            Lit(k) => Some(Some(Arc::new(Lit(*k - Num::ONE)))),
            Const(c) if c.is_primitive("Zero") => Some(None),
            App(f, x) if matches!(&**f, Const(c) if c.is_primitive("Succ")) => {
                Some(Some(x.clone()))
            }
            _ => None,
        }
    }

    /// The constructor application a weak-head normal major premise of a
    /// family `of` is, reading a numeral as `Zero`/`Succ`. The arguments are
    /// the nodes of `t` itself, so that what reducing them gives is found
    /// again (`Core::whnf_shared`) wherever the arm uses them.
    fn as_ctor(&self, t: &Tm, of: &DeclRef) -> Option<(DeclRef, Vec<R>)> {
        if let Lit(k) = t {
            if Some(of) != DeclRef::primitive("Nat").as_ref()
                || !self.ctors.contains_key(&DeclRef::primitive("Zero")?)
            {
                return None;
            }
            return Some(if k.is_zero() {
                (DeclRef::primitive("Zero")?, vec![])
            } else {
                (
                    DeclRef::primitive("Succ")?,
                    vec![Arc::new(Lit(*k - Num::ONE))],
                )
            });
        }
        let (head, args) = spine_rc(t);
        match head {
            Const(c) if self.ctors.get(c).is_some_and(|(f, _)| f == of) => Some((c.clone(), args)),
            _ => None,
        }
    }

    /// The step of the eliminator `rec` applied to `shared`: its major
    /// premise is reduced, and when that is a constructor the minor premise
    /// of the constructor is applied to its fields and to the eliminator on
    /// the fields that recur.
    fn iota(&mut self, rec: &DeclRef, shared: &[R], mode: Mode) -> Step<Option<R>> {
        let Some((family, ind)) = self
            .recs
            .get(rec)
            .and_then(|f| Some((f.clone(), self.inds.get(f)?.clone())))
        else {
            return Ok(None);
        };
        let counts: Vec<usize> = ind
            .group
            .iter()
            .map(|g| self.inds.get(g).map_or(0, |i| i.ctors.len()))
            .collect();
        // The major premise comes after the parameters, the motives, the
        // minor premises and the indices.
        let major_at = ind.params + ind.group.len() + counts.iter().sum::<usize>() + ind.indices;
        let Some(major) = shared.get(major_at) else {
            return Ok(None);
        };
        let major = if self.lazy_iota {
            self.need(major, Mode::Lazy)?
        } else {
            self.need(major, Mode::Full)?
        };
        if family.is_primitive("Nat")
            && let Some(next) = self.repeat(rec, shared, major_at, &major, mode)?
        {
            return Ok(Some(next));
        }
        Ok(self.iota_on(rec, shared, &major, &family, &ind, &counts))
    }

    /// Many turns of a loop over a number, taken at once.
    ///
    /// `rec` is an eliminator of `Nat` applied to `shared`, with its major
    /// premise (at `major_at`, reduced to `major`) a number written with a
    /// numeral of at least [`LARGE_OFFSET`]: `n`, or `x + n`. A function
    /// that takes a `Succ` off its arguments together (`lt(Succ(a),
    /// Succ(b))` is `lt(a, b)`) reduces to this eliminator applied to those
    /// arguments, and each turn of it reduces to the same eliminator on one
    /// `Succ` less of each. Whether `rec` does is found by taking one turn
    /// with unknowns: the major premise is `Succ(a)` for an atom `a`, each
    /// argument after it that is such a number too is `Succ(b)` for an atom
    /// of its own, and the others are as they are. When the reduction
    /// comes to `rec` on the same parameters, motive and minor premises with
    /// `a` as its major premise, each `Succ(b)` either now `b` or as it
    /// was, and the other arguments the same, that is one turn, and it did
    /// not look at what `a` and the `b`s are: reduction is the same whatever
    /// is put for an atom. So the turn can be taken again with a `Succ` less
    /// on each number that came round one less, as often as every one of
    /// them still has a `Succ`: `k` times, for the least `k` among their
    /// numerals, which leaves each with its numeral `k` less. This is the term that `k` turns taken one at a time reduce
    /// to, so nothing is convertible that was not.
    ///
    /// `None` when the turn does not come round (the loop does something
    /// else with its arguments, as `a + b` does), which is noted for the
    /// minor premise (`no_repeat`) and not tried again.
    fn repeat(
        &mut self,
        rec: &DeclRef,
        shared: &[R],
        major_at: usize,
        major: &Tm,
        mode: Mode,
    ) -> Step<Option<R>> {
        let large = |n: &Counted| n.more >= LARGE_OFFSET;
        let Some(count) = Counted::read(major).filter(large) else {
            return Ok(None);
        };
        let after = &shared[major_at + 1..];
        // A turn tried inside a turn that is tried, further than loops are
        // written one inside another, is left to the steps.
        if major_at == 0 || after.len() > 60 || self.trials >= TRIALS || self.numeric_off {
            return Ok(None);
        }
        // The arguments after the major premise that are such numbers.
        let mut counts: Vec<Option<Counted>> = Vec::with_capacity(after.len());
        for a in after {
            let read = match Counted::read(a) {
                Some(n) => Some(n),
                None => match self.offset_view(a)? {
                    Some((base, more)) => Some(Counted {
                        base: Some(Arc::new(base)),
                        more,
                    }),
                    None => match &**a {
                        FVar(x) if self.lvals.contains_key(x) => {
                            Counted::read(&self.literal_or_whnf(a)?)
                        }
                        _ => None,
                    },
                },
            };
            counts.push(read.filter(large));
        }
        let which = counts
            .iter()
            .enumerate()
            .fold((mode as u64) << 60, |m, (i, n)| {
                m | (u64::from(n.is_some()) << i)
            });
        // The minor premise of `Succ` is the last argument before the major
        // premise: `Nat` has no index.
        let minor = &shared[major_at - 1];
        let key = (Arc::as_ptr(minor) as usize, which);
        if self.no_repeat.contains_key(&key) {
            return Ok(None);
        }
        let nat = konst("Nat");
        let succ = |x: u64| Arc::new(app(konst("Succ"), FVar(x)));
        let a = self.fresh(nat.clone());
        let bs: Vec<Option<u64>> = counts
            .iter()
            .map(|n| n.as_ref().map(|_| self.fresh(nat.clone())))
            .collect();
        let mut turn: Vec<R> = shared[..major_at].to_vec();
        turn.push(succ(a));
        turn.extend(
            after
                .iter()
                .zip(&bs)
                .map(|(arg, b)| b.map_or_else(|| arg.clone(), succ)),
        );
        let watch = Watch {
            rec: rec.clone(),
            before: shared[..major_at].to_vec(),
            major: a,
        };
        let head = Arc::new(Const(rec.clone()));
        self.trials += 1;
        let (w, met) = self.drive(apps_node(head.clone(), turn.clone()), mode, Some(watch));
        self.trials -= 1;
        self.lctx.remove(&a);
        for b in bs.iter().flatten() {
            self.lctx.remove(b);
        }
        // Whether each number among the arguments came round one less
        // (`Some(true)`) or as it was.
        let mut less: Vec<Option<bool>> = Vec::with_capacity(after.len());
        let came_round = met && {
            let (_, args) = spine_rc(&w);
            args.len() == shared.len()
                && args[major_at + 1..]
                    .iter()
                    .zip(&turn[major_at + 1..])
                    .zip(&bs)
                    .all(|((got, given), b)| {
                        let one_less = matches!((&**got, b), (FVar(x), Some(b)) if x == b);
                        less.push(b.map(|_| one_less));
                        one_less || Arc::ptr_eq(got, given) || got == given
                    })
        };
        if !came_round {
            if !self.budget.out {
                self.no_repeat.insert(key, minor.clone());
            }
            return Ok(None);
        }
        let k = counts
            .iter()
            .zip(&less)
            .filter(|(_, less)| **less == Some(true))
            .filter_map(|(n, _)| n.as_ref())
            .map(|n| n.more)
            .fold(count.more, Num::min);
        let mut next: Vec<R> = shared[..major_at].to_vec();
        next.push(count.less(k));
        next.extend(
            after
                .iter()
                .zip(&counts)
                .zip(&less)
                .map(|((arg, n), less)| match (n, less) {
                    (Some(n), Some(true)) => n.less(k),
                    _ => arg.clone(),
                }),
        );
        Ok(Some(apps_node(head, next)))
    }

    /// [`Core::iota`] with the major premise reduced to `major`, for the
    /// eliminator of `family` (`ind`), whose group has `counts` constructors.
    fn iota_on(
        &mut self,
        rec: &DeclRef,
        shared: &[R],
        major: &Tm,
        family: &DeclRef,
        ind: &IndInfo,
        counts: &[usize],
    ) -> Option<R> {
        let np = ind.params;
        let nf = ind.group.len();
        let nc: usize = counts.iter().sum();
        let major_at = np + nf + nc + ind.indices;
        let (of, cnp) = match &ind.alias {
            Some((j, a)) => (j.clone(), a.len()),
            None => (family.clone(), np),
        };
        let (cname, cargs) = match self.as_ctor(major, &of) {
            Some(found) => found,
            None if self.lazy_iota => return None,
            None => {
                // An `Eq`-like proof reduces whenever the indices agree.
                let want = ind.k_like.clone()?;
                let params: Vec<Tm> = shared[..np].iter().map(|a| (**a).clone()).collect();
                for (k, w) in want.iter().enumerate() {
                    let w = inst_many(w, &params);
                    if !self.conv(&w, &shared[major_at - ind.indices + k]) {
                        return None;
                    }
                }
                (ind.ctors[0].name.clone(), shared[..np].to_vec())
            }
        };
        let (_, j) = self.ctors.get(&cname)?.clone();
        let c = ind.ctors.get(j)?;
        if c.name != cname || cargs.len() != cnp + c.nargs {
            return None;
        }
        // The fields stay the nodes of the major premise: a field the arm
        // uses twice, or the recursion goes on with, is reduced once.
        let actual: Vec<R> = cargs[cnp..].to_vec();
        let offset: usize = counts[..ind.pos].iter().sum();
        // The arm itself, so that an arm that is a node met before (an
        // argument of the function the match is in) is found again.
        let minor = shared[np + nf + offset + j].clone();
        // `T::rec`, `T::ind` or `T::rec@l`: what follows the family's name,
        // which may itself hold dots (`M::T::rec`).
        let targets = self.rec_targets.get(rec)?.clone();
        let mut applied = actual.clone();
        for r in &c.recs {
            let ys: Vec<u64> = (0..r.ys).map(|_| self.fresh(Sort(Sort::Prop))).collect();
            let mut env: Vec<Tm> = shared[..np].iter().map(|a| (**a).clone()).collect();
            env.extend(actual.iter().map(|a| (**a).clone()));
            env.extend(ys.iter().map(|y| FVar(*y)));
            let mut call: Vec<R> = shared[..np + nf + nc].to_vec();
            call.extend(r.idx.iter().map(|t| Arc::new(inst_many(t, &env))));
            call.push(if ys.is_empty() {
                actual[r.arg].clone()
            } else {
                Arc::new(apps((*actual[r.arg]).clone(), ys.iter().map(|y| FVar(*y))))
            });
            let mut ih = apps_rc(Const(targets.get(r.fam)?.clone()), call);
            for y in ys.iter().rev() {
                ih = lam_over(*y, &ih);
            }
            applied.push(Arc::new(ih));
        }
        Some(apps_node(
            apps_node(minor, applied),
            shared[major_at + 1..].iter().cloned(),
        ))
    }

    /// Whether `name` is one of the quotient's constants ([`QUOT`]), and if
    /// so that it has no value and the type it must have. The constants
    /// it mentions must be declared first, as quotient constants.
    fn quot_constant(&self, name: &str, ty: &Tm, valued: bool) -> Res<bool> {
        if !QUOT.contains(&name) {
            return Ok(false);
        }
        let want = quot_type(name).ok_or_else(|| msg!("kernel-core-quot-has-type"))?;
        if valued {
            return fail(msg!("kernel-core-quot-no-value", name = name));
        }
        let needs: &[&str] = match name {
            "Quot" => &[],
            "Quot::ind" => &["Quot", "Quot::mk"],
            _ => &["Quot"],
        };
        if needs.iter().any(|q| {
            !self
                .quot
                .contains(&DeclRef::primitive(q).expect("quotient builtin"))
        }) {
            return fail(msg!(
                "kernel-core-quot-declared-after",
                name = name,
                needs = needs.join(", ")
            ));
        }
        if *ty != want {
            return fail(msg!("kernel-core-quot-type", name = name));
        }
        // `Quot::lift` states its side condition with `Eq`: that name must be
        // the equality, not whatever was declared under it.
        if name == "Quot::lift" && !self.is_equality(&DeclRef::primitive("Eq").expect("Eq")) {
            return fail(msg!(
                "kernel-core-quot-declared-after",
                name = name,
                needs = "Eq"
            ));
        }
        Ok(true)
    }

    /// Whether `eq` is declared as the equality of [`eq_type`]: the family
    /// `(A: Type, a: A): (A) -> Prop` with the one constructor
    /// `Refl: Eq(A, a, a)`.
    fn is_equality(&self, eq: &DeclRef) -> bool {
        let Some(info) = self.inds.get(eq) else {
            return false;
        };
        let Some(g) = self.globals.get(eq) else {
            return false;
        };
        let [refl] = info.ctors.as_slice() else {
            return false;
        };
        let Some(r) = self.globals.get(&refl.name) else {
            return false;
        };
        let (want_ty, want_refl) = eq_type(eq);
        info.params == 2
            && info.indices == 1
            && info.alias.is_none()
            && refl.nargs == 0
            && g.ty == want_ty
            && r.ty == want_refl
    }

    /// `Quot_lift(A, r, B, f, h, quot_mk(A', r', a))` is `f(a)`, and
    /// `Quot::ind(A, r, P, m, quot_mk(A', r', a))` is `m(a)`: the value under
    /// `quot_mk` is passed to the function, whatever the relation.
    fn quot_iota(&mut self, c: &DeclRef, args: &[R]) -> Step<Option<R>> {
        let (f, major) = if c.is_primitive("Quot::lift") {
            (3, 5)
        } else if c.is_primitive("Quot::ind") {
            (3, 4)
        } else {
            return Ok(None);
        };
        let Some(q) = args.get(major) else {
            return Ok(None);
        };
        let q = self.need(q, Mode::Full)?;
        let (head, inner) = spine_rc(&q);
        match head {
            Const(m) if m.is_primitive("Quot::mk") && self.quot.contains(m) && inner.len() == 3 => {
            }
            _ => return Ok(None),
        }
        Ok(Some(apps_node(
            apps_node(args[f].clone(), [inner[2].clone()]),
            args[major + 1..].iter().cloned(),
        )))
    }

    fn expand_lit(t: Tm) -> Tm {
        match t {
            Lit(Num::ZERO) => konst("Zero"),
            Lit(k) => app(konst("Succ"), Lit(k - Num::ONE)),
            other => other,
        }
    }

    /// Convertibility, with proof irrelevance: two proofs of the same
    /// proposition are convertible. The untyped comparison runs first and
    /// settles most questions; only when it fails are the terms compared again
    /// with their types, which a proof inside a term needs to be seen as one.
    fn conv(&mut self, a: &Tm, b: &Tm) -> bool {
        let record = self.derivation.take();
        let result = self.conv_unrecorded(a, b);
        self.derivation = record;
        result
    }

    fn conv_unrecorded(&mut self, a: &Tm, b: &Tm) -> bool {
        if let Some(r) = self.conv_value(a, b) {
            return r;
        }
        self.conv_depth += 1;
        let (a, b) = (Arc::new(a.clone()), Arc::new(b.clone()));
        let r = self.conv_node(&a, &b) || self.conv_typed(&a, &b, None);
        self.conv_depth -= 1;
        if self.conv_depth == 0 {
            self.conv_no.clear();
            self.conv_fail.clear();
        }
        r
    }

    /// When one side is a literal (a number or a truth value): the other is
    /// reduced once, and when it reduces to a literal too the two are
    /// compared as values. Two different literals are never convertible, so
    /// the answer is decided without comparing the steps that led there one
    /// by one, which for a wrong value repeats the computation at each step.
    /// `None` when the other side does not reduce to a literal.
    fn conv_value(&mut self, a: &Tm, b: &Tm) -> Option<bool> {
        let (lit, other) = match (a, b) {
            (Lit(_), _) => (a, b),
            (_, Lit(_)) => (b, a),
            _ => return None,
        };
        // Found different before, during the outermost `conv`: the typed
        // comparison meets the same pair again.
        let key = ConvKey::new(lit.clone(), other.clone());
        if self.conv_no.contains(&key) {
            return Some(false);
        }
        let w = self.whnf_shared(&Arc::new(other.clone()));
        let w = match (lit, w) {
            (Lit(_), w @ App(..)) | (Lit(_), w @ Const(_)) => {
                Lit(self.top(|c| c.numeral_of(w)).flatten()?)
            }
            (_, w) => w,
        };
        let same = match (lit, &w) {
            (Lit(x), Lit(y)) => x == y,
            _ => return None,
        };
        if !same {
            self.conv_no.insert(key);
        }
        Some(same)
    }

    fn is_prop(&mut self, ty: &Tm) -> bool {
        match self.infer(ty) {
            Ok(s) => self.whnf(&s) == Sort(Sort::Prop),
            Err(_) => false,
        }
    }

    /// `a` and `b` compared at the type `ty` when it is known (both are
    /// terms of it): a proof of a proposition equals any other; an
    /// application of a neutral head is compared argument by argument at
    /// the types the head's own type gives them, a function at the
    /// codomain of its type. Without a type, only the parts whose types
    /// the heads give are looked at.
    ///
    /// The parts compared are the nodes of the terms and of what they reduce
    /// to (`Core::whnf_shared`), as in [`Core::conv_node`]: the untyped
    /// comparison asked first at each part is answered at once for a pair it
    /// found different before (`conv_fail`), and a node reduced before is not
    /// reduced again. With copies, each part going down a chain of `n`
    /// reductions compared and reduced again all of the chain below it.
    fn conv_typed(&mut self, a: &R, b: &R, ty: Option<&Tm>) -> bool {
        let unfolded = self.conv_unfolded.len();
        let r = self.conv_typed_at(a, b, ty);
        self.conv_unfolded.truncate(unfolded);
        r
    }

    fn conv_typed_at(&mut self, a: &R, b: &R, ty: Option<&Tm>) -> bool {
        if self.conv_node(a, b) {
            return true;
        }
        if let Some(ty) = ty
            && self.is_prop(ty)
        {
            return true;
        }
        // `b + k` against `c + j` (`Core::offset_view`), as in `conv_nodes`:
        // the bases are compared once rather than `Succ` by `Succ`.
        if let Some((x, k)) = self.offset_view_top(a)
            && let Some((y, j)) = self.offset_view_top(b)
        {
            return k == j && self.conv_typed(&Arc::new(x), &Arc::new(y), ty);
        }
        // `+` and `*` stuck on their operands (`Core::stuck_arith`): the
        // operands, numbers, are compared rather than what the two reduce to.
        if let Some(pairs) = self.stuck_arith(a, b) {
            let nat = konst("Nat");
            return pairs.iter().all(|(x, y)| self.conv_typed(x, y, Some(&nat)));
        }
        // The same recursive name on both sides is compared argument by
        // argument without unfolding it, where `Core::conv_cut` says so.
        let same_rec = self.same_recursive(a, b).map(|r| r.0);
        let cut = same_rec.as_ref().is_some_and(|f| self.conv_cut(f));
        if let Some(f) = same_rec
            && !cut
        {
            self.conv_unfolded.push((f, self.conv_binders));
        }
        let (mut a, mut b) = if cut {
            ((**a).clone(), (**b).clone())
        } else {
            (self.whnf_shared(a), self.whnf_shared(b))
        };
        if matches!(a, Lit(_)) != matches!(b, Lit(_)) {
            a = Self::expand_lit(a);
            b = Self::expand_lit(b);
        }
        match (&a, &b) {
            (App(..), App(..)) => {
                let (h1, xs) = spine_rc(&a);
                let (h2, ys) = spine_rc(&b);
                if xs.len() != ys.len() || !self.conv_plain(h1, h2) {
                    return false;
                }
                let Ok(mut hty) = self.infer(h1) else {
                    return false;
                };
                for (x, y) in xs.iter().zip(&ys) {
                    let Some((_, dom, cod)) = self.whnf(&hty).pi_parts() else {
                        return false;
                    };
                    if !self.conv_typed(x, y, Some(&dom)) {
                        return false;
                    }
                    hty = inst(&cod, &**x);
                }
                true
            }
            (Pi(_, d1, r1), Pi(_, d2, r2)) => {
                if !self.conv_typed(d1, d2, None) {
                    return false;
                }
                let x = self.fresh((**d1).clone());
                self.under_binder(|c| {
                    c.conv_typed(
                        &Arc::new(inst(r1, &FVar(x))),
                        &Arc::new(inst(r2, &FVar(x))),
                        None,
                    )
                })
            }
            (Lam(_, r1), Lam(_, r2)) => {
                let Some((_, dom, cod)) = ty.and_then(|t| self.whnf(t).pi_parts()) else {
                    return false;
                };
                let x = self.fresh((*dom).clone());
                self.under_binder(|c| {
                    c.conv_typed(
                        &Arc::new(inst(r1, &FVar(x))),
                        &Arc::new(inst(r2, &FVar(x))),
                        Some(&inst(&cod, &FVar(x))),
                    )
                })
            }
            (Lam(_, r), other) | (other, Lam(_, r)) => {
                let Some((_, dom, cod)) = ty.and_then(|t| self.whnf(t).pi_parts()) else {
                    return false;
                };
                let x = self.fresh((*dom).clone());
                let applied = Arc::new(app(other.clone(), FVar(x)));
                self.under_binder(|c| {
                    c.conv_typed(
                        &Arc::new(inst(r, &FVar(x))),
                        &applied,
                        Some(&inst(&cod, &FVar(x))),
                    )
                })
            }
            _ => false,
        }
    }

    /// A transparent view through a nonrecursive, single-constructor family.
    /// Reducing its eliminator can expose a shared head without reducing fields.
    fn record_view(&self, t: &Tm) -> bool {
        let (Const(name), arguments) = spine_rc(t) else {
            return false;
        };
        let Some(global) = self.globals.get(name) else {
            return false;
        };
        let Some(value) = &global.value else {
            return false;
        };
        let mut body = &**value;
        let mut binders = 0;
        while let Lam(_, inner) = body {
            body = inner;
            binders += 1;
        }
        if arguments.len() < binders {
            return false;
        }
        let Const(rec) = spine_rc(body).0 else {
            return false;
        };
        self.recs
            .get(rec)
            .and_then(|family| self.inds.get(family))
            .is_some_and(|info| matches!(info.ctors.as_slice(), [ctor] if ctor.recs.is_empty()))
    }

    fn unfold_record_view(&mut self, t: &Tm) -> Option<Tm> {
        let unfolded = self.unfold_head(t)?;
        let lazy = std::mem::replace(&mut self.lazy_iota, false);
        let result = self.whnf_with(&unfolded, false);
        self.lazy_iota = lazy;
        Some(result)
    }

    fn unfold_head(&mut self, t: &Tm) -> Option<Tm> {
        if self.spend() {
            return None;
        }
        let (head, args) = spine_rc(t);
        let Const(c) = head else { return None };
        // On numerals, what unfolding `Nat::rem_nz` and the like gives. The
        // arguments are reduced only here, once the two sides were found to
        // differ without it.
        if let Some(n) = self.top(|k| k.numeric(c, &args)).flatten() {
            return Some(n);
        }
        let v = self.globals.get(c).and_then(|g| g.value.clone())?;
        *self.budget.unfolds.entry(c.clone()).or_default() += 1;
        self.budget.last_unfold = Some(c.clone());
        Some(apps_rc((*v).clone(), args))
    }

    /// The height and recursion of `c` when it has a value. Found for the
    /// names its value reaches at once, a group of names that use each other
    /// together (Tarjan's strongly connected components).
    fn def(&mut self, c: &DeclRef) -> Option<Def> {
        if let Some(d) = self.defs.get(c) {
            return Some(*d);
        }
        self.globals.get(c)?.value.as_ref()?;
        let mut walk = DefWalk::default();
        self.def_visit(c, &mut walk);
        self.defs.get(c).copied()
    }

    fn def_visit(&mut self, c: &DeclRef, w: &mut DefWalk) {
        let at = w.next;
        w.next += 1;
        w.index.insert(c.clone(), at);
        w.low.insert(c.clone(), at);
        w.stack.push(c.clone());
        w.on.insert(c.clone());
        let uses = self.uses(c);
        for d in &uses {
            if self.defs.contains_key(d) {
                continue;
            }
            if let Some(&i) = w.index.get(d) {
                if w.on.contains(d) {
                    let l = w.low[c].min(i);
                    w.low.insert(c.clone(), l);
                }
                continue;
            }
            self.def_visit(d, w);
            let l = w.low[c].min(w.low[d]);
            w.low.insert(c.clone(), l);
        }
        w.uses.insert(c.clone(), uses);
        if w.low[c] != at {
            return;
        }
        let mut group = Vec::new();
        while let Some(d) = w.stack.pop() {
            w.on.remove(&d);
            let last = d == *c;
            group.push(d);
            if last {
                break;
            }
        }
        let recursive = group.len() > 1 || w.uses[c].contains(c);
        let height = 1 + group
            .iter()
            .flat_map(|d| &w.uses[d])
            .filter(|d| !group.contains(d))
            .map(|d| self.defs.get(d).map_or(0, |x| x.height))
            .max()
            .unwrap_or(0);
        for d in group {
            self.defs.insert(d, Def { height, recursive });
        }
    }

    /// The names with a value that the value of `c` uses, each once. The
    /// value is walked as the graph of its shared nodes.
    fn uses(&self, c: &DeclRef) -> Vec<DeclRef> {
        let Some(v) = self.globals.get(c).and_then(|g| g.value.clone()) else {
            return Vec::new();
        };
        let mut seen: HashSet<usize> = HashSet::new();
        let mut out: Vec<DeclRef> = Vec::new();
        let mut todo: Vec<R> = vec![v];
        while let Some(n) = todo.pop() {
            if !seen.insert(Arc::as_ptr(&n) as usize) {
                continue;
            }
            match &*n {
                Const(d) => {
                    if !out.contains(d) && self.globals.get(d).is_some_and(|g| g.value.is_some()) {
                        out.push(d.clone());
                    }
                }
                Pi(_, a, b) | App(a, b) => {
                    todo.push(a.clone());
                    todo.push(b.clone());
                }
                Lam(_, b) => todo.push(b.clone()),
                _ => {}
            }
        }
        out
    }

    fn head_height(&mut self, t: &Tm) -> Option<u32> {
        let Const(c) = spine_rc(t).0 else { return None };
        let c = c.clone();
        self.def(&c).map(|d| d.height)
    }

    /// Whether the comparison of `f` applied on both sides goes no further
    /// than the arguments, without reducing `f`: `f` lays open calls of
    /// itself (`Core::lays_open_itself`) and was reduced on both sides
    /// further out, outside a binder the comparison has since gone under.
    /// Reducing it there laid open its calls of itself under the binders of
    /// the cases of a `match` that does not reduce; reducing these again lays
    /// open the next ones, as deep as a literal bound such as a count of steps
    /// lets it go (`Nat::rec` on `65558`), and when the two sides differ in an
    /// argument that stays the same down the calls, they are found different
    /// only at the bottom.
    ///
    /// Saying "not convertible" is never unsound. What is not seen is a
    /// conversion that needs `f` reduced again below the binders of its own
    /// reduction although its arguments are not convertible; such a "no" is
    /// kept in `conv_fail` like any other until the outermost `conv` ends.
    fn conv_cut(&mut self, f: &DeclRef) -> bool {
        self.lays_open_itself(f) && self.conv_unfolded.below(f, self.conv_binders)
    }

    /// Whether `f` can lay open calls of itself: a name whose value uses it,
    /// or an eliminator, whose step on a constructor applies it again.
    fn lays_open_itself(&mut self, f: &DeclRef) -> bool {
        self.recs.contains_key(f) || self.def(f).is_some_and(|d| d.recursive)
    }

    /// The recursive name (`Core::lays_open_itself`) both `a` and `b` apply to as
    /// many arguments, with the arguments.
    fn same_recursive<'t>(&mut self, a: &'t Tm, b: &'t Tm) -> Option<(DeclRef, Vec<R>, Vec<R>)> {
        let ((ha, xs), (hb, ys)) = (spine_rc(a), spine_rc(b));
        match (ha, hb) {
            (Const(f), Const(g)) if f == g && xs.len() == ys.len() && self.lays_open_itself(f) => {
                Some((f.clone(), xs, ys))
            }
            _ => None,
        }
    }

    fn under_binder<X>(&mut self, f: impl FnOnce(&mut Self) -> X) -> X {
        self.conv_binders += 1;
        let r = f(self);
        self.conv_binders -= 1;
        r
    }

    /// The value of the atom `head` when it is a `let`-like part of the typing
    /// (`Core::lvals`) and `other` is not that same atom.
    fn atom_value(&self, head: &Tm, other: &Tm) -> Option<R> {
        match head {
            FVar(x) if other != head => self.lvals.get(x).cloned(),
            _ => None,
        }
    }

    fn conv_plain(&mut self, a: &Tm, b: &Tm) -> bool {
        self.conv_node(&Arc::new(a.clone()), &Arc::new(b.clone()))
    }

    /// [`Core::conv_plain`] of two nodes: the parts compared are the nodes
    /// of the terms, so that what reducing them gave is found again.
    ///
    /// Two sides that reduce to `Succ(x)` and `Succ(y)` are as convertible
    /// as `x` and `y` ([`Conv::Below`]): the pair below is compared here, in
    /// a loop, and not in a call inside the comparison of the pair above. A
    /// numeral against a sum with a numeral operand lays open a `Succ` at a
    /// time, as many as the numeral, which would otherwise be as many calls
    /// one inside another. Each pair on the way is noted as different
    /// (`conv_fail`) when the answer is no, as each call would note it.
    fn conv_node(&mut self, a: &R, b: &R) -> bool {
        let (mut a, mut b) = (a.clone(), b.clone());
        let mut met: Vec<(R, R)> = Vec::new();
        let same = loop {
            let key = (Arc::as_ptr(&a) as usize, Arc::as_ptr(&b) as usize);
            if self.conv_fail.contains_key(&key) {
                break false;
            }
            let unfolded = self.conv_unfolded.len();
            let step = self.conv_nodes(&a, &b);
            self.conv_unfolded.truncate(unfolded);
            met.push((a, b));
            match step {
                Conv::Is(same) => break same,
                Conv::Below(x, y) => {
                    if self.timed_out() {
                        break false;
                    }
                    (a, b) = (x, y);
                }
            }
        };
        if !same && !self.budget.out {
            for (a, b) in met {
                let key = (Arc::as_ptr(&a) as usize, Arc::as_ptr(&b) as usize);
                self.conv_fail
                    .insert(key, (Arc::downgrade(&a), Arc::downgrade(&b)));
            }
        }
        same
    }

    /// The weak head normal form without `delta` that also leaves an
    /// eliminator as it is when its major premise becomes a constructor only
    /// by unfolding names. [`Core::conv_nodes`] compares the two sides as
    /// they are first: `T::rec(…, f(x))` on both sides is the same term
    /// without reducing `f(x)`, which for a function such as an equality of
    /// values with a count of steps lays open every case of the `match` it
    /// is stuck on. When they differ, [`Core::force_both`] takes the step.
    fn whnf_lazy(&mut self, t: R) -> Tm {
        let lazy = std::mem::replace(&mut self.lazy_iota, true);
        let w = self.whnf_node(t, false);
        self.lazy_iota = lazy;
        w
    }

    /// `a` and `b` reduced as `whnf_node` without `delta` does, which unfolds
    /// the major premises of eliminators; whether either changed.
    fn force_both(&mut self, a: &mut Tm, b: &mut Tm) -> bool {
        let lazy = std::mem::replace(&mut self.lazy_iota, false);
        let fa = self.whnf_with(a, false);
        let fb = self.whnf_with(b, false);
        self.lazy_iota = lazy;
        let changed = fa != *a || fb != *b;
        *a = fa;
        *b = fb;
        changed
    }

    fn conv_nodes(&mut self, a: &R, b: &R) -> Conv {
        if Arc::ptr_eq(a, b) || a == b {
            return Conv::Is(true);
        }
        if let Some(r) = self.conv_value(a, b) {
            return Conv::Is(r);
        }
        // An eliminator reduces below without unfolding anything: whether
        // the comparison is cut is asked before (`Core::conv_cut`).
        if let Some((f, xs, ys)) = self.same_recursive(a, b) {
            if self.conv_cut(&f) {
                return Conv::Is(xs.iter().zip(&ys).all(|(x, y)| self.conv_node(x, y)));
            }
            self.conv_unfolded.push((f, self.conv_binders));
        }
        // `b + k` against `c + j`, both with numerals `k` and `j` and bases
        // `b` and `c` that are not `Succ` nor numerals: different when `k`
        // and `j` differ (one is `Succ` where the other is not), else when
        // `b` and `c` are. Taking `Succ` off one at a time instead goes as
        // deep as the numeral.
        if let Some((x, k)) = self.offset_view_top(a)
            && let Some((y, j)) = self.offset_view_top(b)
        {
            return Conv::Is(k == j && self.conv_plain(&x, &y));
        }
        // `+`, `*` and `-` of convertible operands are convertible, also when
        // one side names the operator (`Nat::add(x, y)` against `x + y`). Asked
        // before a step of `Core::arith`, which lays open a `Succ` for each
        // unit of a numeral operand: `x + n` against `y + n` would otherwise
        // be compared `Succ` by `Succ`, `n` deep. Saying no decides nothing.
        if let ((Const(f), xs), (Const(g), ys)) = (spine_rc(a), spine_rc(b))
            && let (Some(p), Some(q)) = (self.arith_op(f), self.arith_op(g))
            && p == q
            && xs.len() == 2
            && ys.len() == 2
        {
            if xs.iter().zip(&ys).all(|(x, y)| self.conv_node(x, y)) {
                return Conv::Is(true);
            }
            // Saying no here decides it when the two are stuck on the
            // operands just compared (`Core::stuck_arith`).
            if let Some(pairs) = self.stuck_arith(a, b) {
                return Conv::Is(pairs.iter().all(|(x, y)| self.conv_node(x, y)));
            }
        }
        let (na, nb) = (a.clone(), b.clone());
        // Names are unfolded one at a time, both sides together, and before
        // each the two are compared: the same name applied to convertible
        // arguments is convertible without unfolding it. Saying no there
        // decides nothing: unfolding goes on.
        let mut a = self.whnf_lazy(a.clone());
        let mut b = self.whnf_lazy(b.clone());
        loop {
            if a == b {
                return Conv::Is(true);
            }
            let ((ha, xs), (hb, ys)) = (spine_rc(&a), spine_rc(&b));
            // A part the typing read as an atom stands for its value (a
            // `let`): when the other side is not that atom, the value is put in
            // before a name is unfolded. `f(g(c))` against `f(x)` with
            // `x := g(c)` is the same by its arguments; unfolding `f` on both
            // sides first computes with arguments that are not seen to be the
            // same, as far as `f` goes, which for a decision procedure is all of
            // a run on stuck input.
            {
                let (za, zb) = (self.atom_value(ha, hb), self.atom_value(hb, ha));
                if za.is_some() || zb.is_some() {
                    if let Some(v) = za {
                        a = self.whnf_lazy(apps_node(v, xs));
                    }
                    if let Some(v) = zb {
                        b = self.whnf_lazy(apps_node(v, ys));
                    }
                    continue;
                }
            }
            if let (Const(f), Const(g)) = (ha, hb)
                && f == g
                && xs.len() == ys.len()
            {
                // `Succ(x)` against `Succ(y)`: neither unfolds, so they are
                // as convertible as `x` and `y`, which `Core::conv_node`
                // compares next (`Conv::Below`). What reaching here found is
                // kept as below, where neither side unfolds.
                if f.is_primitive("Succ") && xs.len() == 1 {
                    if !self.budget.out {
                        for (n, w) in [(na, &a), (nb, &b)] {
                            if Arc::strong_count(&n) > 1 {
                                self.remember(n, w.clone());
                            }
                        }
                    }
                    return Conv::Below(xs[0].clone(), ys[0].clone());
                }
                // The arguments are nodes: a pair found different before is
                // answered at once (`conv_fail`), so trying them again at
                // the next unfolding costs one look per argument.
                if xs.iter().zip(&ys).all(|(x, y)| self.conv_node(x, y)) {
                    return Conv::Is(true);
                }
                let f = f.clone();
                if self.conv_cut(&f) {
                    // Left by `whnf_lazy`, an eliminator may still reduce
                    // once its major premise is unfolded.
                    if self.force_both(&mut a, &mut b) {
                        continue;
                    }
                    return Conv::Is(false);
                }
                if self.lays_open_itself(&f) {
                    self.conv_unfolded.push((f, self.conv_binders));
                }
            }
            // A record view is reduced before a field's calculation, so its
            // shared head can be compared without unfolding that calculation.
            // Otherwise the higher definition is unfolded first; definitions
            // of the same height unfold together.
            let (ua, ub) = match (self.record_view(&a), self.record_view(&b)) {
                (true, false) => (self.unfold_record_view(&a), None),
                (false, true) => (None, self.unfold_record_view(&b)),
                _ => match (self.head_height(&a), self.head_height(&b)) {
                    (Some(x), Some(y)) if x > y => (self.unfold_head(&a), None),
                    (Some(x), Some(y)) if x < y => (None, self.unfold_head(&b)),
                    _ => (self.unfold_head(&a), self.unfold_head(&b)),
                },
            };
            match (ua, ub) {
                (None, None) if self.force_both(&mut a, &mut b) => {}
                (None, None) => {
                    // Neither unfolds: each is its node's weak head normal
                    // form, found again wherever the node is met.
                    if !self.budget.out {
                        for (n, w) in [(na, &a), (nb, &b)] {
                            if Arc::strong_count(&n) > 1 {
                                self.remember(n, w.clone());
                            }
                        }
                    }
                    break;
                }
                (ua, ub) => {
                    if let Some(x) = ua {
                        a = self.whnf_lazy(Arc::new(x));
                    }
                    if let Some(y) = ub {
                        b = self.whnf_lazy(Arc::new(y));
                    }
                }
            }
        }
        if matches!(a, Lit(_)) != matches!(b, Lit(_)) {
            a = Self::expand_lit(a);
            b = Self::expand_lit(b);
        }
        Conv::Is(match (&a, &b) {
            (BVar(x), BVar(y)) => x == y,
            (FVar(x), FVar(y)) => x == y,
            (Sort(x), Sort(y)) => x == y,
            (Const(x), Const(y)) => x == y,
            (Lit(x), Lit(y)) => x == y,
            (App(f, x), App(g, y)) => self.conv_node(f, g) && self.conv_node(x, y),
            (Pi(_, d1, r1), Pi(_, d2, r2)) => {
                if !self.conv_node(d1, d2) {
                    return Conv::Is(false);
                }
                let x = self.fresh((**d1).clone());
                self.under_binder(|c| c.conv_plain(&inst(r1, &FVar(x)), &inst(r2, &FVar(x))))
            }
            (Lam(_, r1), Lam(_, r2)) => {
                let x = self.fresh(Sort(Sort::Prop));
                self.under_binder(|c| c.conv_plain(&inst(r1, &FVar(x)), &inst(r2, &FVar(x))))
            }
            // Eta: a function is what it does to a variable.
            (Lam(_, r), other) | (other, Lam(_, r)) => {
                let x = self.fresh(Sort(Sort::Prop));
                let applied = app(other.clone(), FVar(x));
                self.under_binder(|c| c.conv_plain(&inst(r, &FVar(x)), &applied))
            }
            _ => false,
        })
    }

    fn subtype(&mut self, a: &Tm, b: &Tm) -> bool {
        let a = self.whnf(a);
        let b = self.whnf(b);
        match (&a, &b) {
            (Sort(x), Sort(y)) => x.le(y),
            (Pi(_, d1, r1), Pi(_, d2, r2)) => {
                if !self.conv(d1, d2) {
                    return false;
                }
                let x = self.fresh((**d1).clone());
                self.subtype(&inst(r1, &FVar(x)), &inst(r2, &FVar(x)))
            }
            _ => self.conv(&a, &b),
        }
    }

    fn fault(&self, why: Why) -> Box<Fault> {
        let (at, bound) = match &self.track {
            Some(tr) => (tr.at.clone(), tr.bound.clone()),
            None => Default::default(),
        };
        Box::new(Fault { why, at, bound })
    }

    /// `f` one step down the path of the typing (`step`), under the binder
    /// of the atom `x` when there is one.
    fn down<X>(&mut self, step: u8, x: Option<(u64, &Hint)>, f: impl FnOnce(&mut Self) -> X) -> X {
        let mark = self.enter(step, x);
        let r = f(self);
        self.leave(mark);
        r
    }

    /// The first half of `down`: one step down the path, returning where to
    /// come back to with `leave`.
    fn enter(&mut self, step: u8, x: Option<(u64, &Hint)>) -> (usize, usize) {
        let Some(tr) = &mut self.track else {
            return (0, 0);
        };
        let mark = (tr.at.len(), tr.bound.len());
        if tr.lost == 0 {
            tr.at.push(step);
        }
        if let Some((x, h)) = x {
            tr.bound.push((x, h.clone()));
        }
        mark
    }

    fn leave(&mut self, (n, m): (usize, usize)) {
        if let Some(tr) = &mut self.track {
            tr.at.truncate(n);
            tr.bound.truncate(m);
        }
    }

    /// The type of `t`. An application whose argument is checked by its
    /// type (`check` with neither a λ nor a hole) is typed in a loop along
    /// the arguments, the rules of `infer_one` and `check` taken in the same
    /// order: a list literal, or a text literal's bytes, nests there once
    /// per element and would recurse as deep.
    fn infer(&mut self, t: &Tm) -> Result<Tm, Box<Fault>> {
        if self.derivation.is_none() {
            return self.infer_unrecorded(t);
        }
        let bound = self
            .track
            .as_ref()
            .map(|tr| tr.bound.clone())
            .unwrap_or_default();
        self.derivation.as_mut().unwrap().push(Vec::new());
        // infer_one is the same core rule as the iterative application path.
        let result = self.infer_one(t);
        let premises = self.derivation.as_mut().unwrap().pop().unwrap();
        if let Ok(ty) = &result {
            let rule = match t {
                FVar(_) => InferenceRule::Assumption,
                Const(_) => InferenceRule::Constant,
                Lit(_) => InferenceRule::Literal,
                Sort(_) => InferenceRule::Sort,
                Pi(..) => InferenceRule::Formation,
                App(..) if matches!(spine(t).0, Lam(..)) => InferenceRule::Reduction,
                App(..) => InferenceRule::Application,
                _ => unreachable!("only inferable terms have a derivation"),
            };
            self.derivation
                .as_mut()
                .unwrap()
                .last_mut()
                .unwrap()
                .push(RawDerivation {
                    term: t.clone(),
                    ty: ty.clone(),
                    bound,
                    rule,
                    premises,
                });
        }
        result
    }

    /// [`Core::infer`] without a derivation. An application is typed along
    /// its spine: the head's type is read once, and its telescope is walked
    /// with the arguments met so far kept aside (`env`) and put in at once
    /// ([`inst_env`]): into each domain when that argument is checked, and
    /// into the rest when the telescope ends or the spine does. This is the
    /// type that `infer_one` finds one application at a time, where each
    /// argument is put into the whole rest of the telescope, but each part of
    /// the telescope is walked once instead of once per argument after it.
    /// The rules are taken in the same order as there, along the same path
    /// (`enter`), so a term that fails fails in the same place: the head
    /// first, then the arguments from the first, each checked against its
    /// domain. A function's type that is not a `Π` as it stands is put in
    /// and reduced to one (`whnf`), as `infer_one` does at each argument (a
    /// `Π` is its own weak head normal form). A last argument checked by its
    /// type (neither a λ nor a hole) is typed in the loop rather than in a
    /// call: a list literal, or a text literal's bytes, nests there once per
    /// element and would recurse as deep.
    fn infer_unrecorded(&mut self, t: &Tm) -> Result<Tm, Box<Fault>> {
        let base = self.enter_none();
        let mut pending: Vec<Pending> = Vec::new();
        let mut t = t.clone();
        let inner = 'term: loop {
            if !matches!(t, App(..)) {
                break self.infer_one(&t);
            }
            let (head, args) = spine_rc(&t);
            if matches!(head, Lam(_, _)) {
                break self.infer_one(&t);
            }
            let head = head.clone();
            let n = args.len();
            // `marks[j]`: the path at the application with `n - j`
            // arguments, `j` steps to the function below the whole spine.
            let marks: Vec<(usize, usize)> = (0..n).map(|_| self.enter(0, None)).collect();
            let mut cod: R = match self.infer(&head) {
                Ok(ty) => Arc::new(ty),
                Err(e) => break Err(e),
            };
            let mut env: Vec<R> = Vec::new();
            for (k, a) in args.into_iter().enumerate() {
                self.leave(marks[n - 1 - k]);
                if !matches!(*cod, Pi(..)) {
                    let full = inst_env(&cod, 0, &env);
                    env.clear();
                    let w = self.whnf(&full);
                    if !matches!(w, Pi(..)) {
                        break 'term Err(self.fault(Why::NotFunction));
                    }
                    cod = Arc::new(w);
                }
                let Pi(_, dom, body) = &*cod else {
                    unreachable!("a Π was just found")
                };
                let dom = inst_env(dom, 0, &env);
                let body = body.clone();
                if k + 1 == n && !matches!(*a, Lam(_, _)) && !self.is_hole(&a) {
                    let mark = self.enter(1, None);
                    pending.push(Pending {
                        mark,
                        arg: a.clone(),
                        dom,
                        cod: body,
                        env,
                    });
                    t = (*a).clone();
                    continue 'term;
                }
                if let Err(e) = self.down(1, None, |c| c.check(&a, &dom)) {
                    break 'term Err(e);
                }
                env.push(a);
                cod = body;
            }
            self.leave(marks[0]);
            break Ok((*inst_env(&cod, 0, &env)).clone());
        };
        let mut ty = match inner {
            Ok(ty) => ty,
            Err(e) => {
                self.leave(base);
                return Err(e);
            }
        };
        while let Some(Pending {
            mark,
            arg,
            dom,
            cod,
            mut env,
        }) = pending.pop()
        {
            if !self.subtype(&ty, &dom) {
                let e = self.fault(Why::Mismatch {
                    expected: (*dom).clone(),
                    found: ty,
                });
                self.leave(base);
                return Err(e);
            }
            self.leave(mark);
            env.push(arg);
            ty = (*inst_env(&cod, 0, &env)).clone();
        }
        Ok(ty)
    }

    /// Where the path is now, for `leave` to come back to.
    fn enter_none(&self) -> (usize, usize) {
        match &self.track {
            Some(tr) => (tr.at.len(), tr.bound.len()),
            None => (0, 0),
        }
    }

    /// Whether `check` takes `t` as a hole of the tracked question.
    fn is_hole(&self, t: &Tm) -> bool {
        matches!(t, FVar(x) if self.track.as_ref().is_some_and(|tr| tr.holes.contains(x)))
    }

    fn infer_one(&mut self, t: &Tm) -> Result<Tm, Box<Fault>> {
        match t {
            BVar(_) => Err(self.fault(Why::Said("kernel-core-bvar-out-of-scope"))),
            FVar(x) => match self.lctx.get(x) {
                Some(ty) => Ok(ty.clone()),
                None => Err(self.fault(Why::Unread(*x))),
            },
            Sort(s) => s
                .next()
                .map(Sort)
                .ok_or_else(|| self.fault(Why::Said("kernel-core-level-overflow"))),
            Const(c) => match self.globals.get(c) {
                Some(g) => Ok(g.ty.clone()),
                None => Err(self.fault(Why::Said("kernel-core-name-not-defined"))),
            },
            Lit(_) => Ok(konst("Nat")),
            Pi(..) if self.derivation.is_none() => self.infer_telescope(t),
            Pi(h, a, b) => {
                let s1 = self.down(0, None, |c| c.infer_sort(a))?;
                let x = self.fresh((**a).clone());
                let s2 = self.down(1, Some((x, h)), |c| c.infer_sort(&inst(b, &FVar(x))))?;
                Ok(Sort(sort_max(s1, s2)))
            }
            Lam(_, _) => Err(self.fault(Why::Said("kernel-core-cannot-infer-function"))),
            App(..) => {
                let (head, args) = spine(t);
                if let Lam(_, _) = head {
                    // A redex is typed by its reduct, once its arguments are
                    // typed (`Typing` needs `a : A` for `(fun b) a`). Below
                    // it, the path is lost.
                    if let Some(tr) = &mut self.track {
                        tr.lost += 1;
                    }
                    let r = (|| {
                        for a in &args {
                            self.infer(a)?;
                        }
                        // Only the redexes at the head are reduced: unfolding
                        // a name or computing would type the same term by a
                        // longer way, and can be a whole computation (a
                        // motive applied to a numeral).
                        let reduct = self.beta_head(t);
                        if matches!(spine(&reduct).0, Lam(_, _)) && matches!(reduct, App(..)) {
                            return Err(self.fault(Why::Said("kernel-core-cannot-type-applied")));
                        }
                        self.infer(&reduct)
                    })();
                    if let Some(tr) = &mut self.track {
                        tr.lost -= 1;
                    }
                    return r;
                }
                let App(f, a) = t else { unreachable!() };
                let ft = self.down(0, None, |c| c.infer(f))?;
                let ft = self.whnf(&ft);
                self.record_conversion(f, &ft);
                let Some((_, dom, cod)) = ft.pi_parts() else {
                    return Err(self.fault(Why::NotFunction));
                };
                self.down(1, None, |c| c.check(a, &dom))?;
                Ok(inst(&cod, a))
            }
        }
    }

    fn infer_sort(&mut self, t: &Tm) -> Result<Sort, Box<Fault>> {
        let ty = self.infer(t)?;
        let normal = self.whnf(&ty);
        self.record_conversion(t, &normal);
        match &normal {
            Sort(s) => Ok(s.clone()),
            _ => Err(self.fault(Why::NotType)),
        }
    }

    fn check(&mut self, t: &Tm, expected: &Tm) -> Result<(), Box<Fault>> {
        if self.derivation.is_none() {
            return self.check_unrecorded(t, expected);
        }
        let bound = self
            .track
            .as_ref()
            .map(|tr| tr.bound.clone())
            .unwrap_or_default();
        self.derivation.as_mut().unwrap().push(Vec::new());
        let result = self.check_unrecorded(t, expected);
        let mut premises = self.derivation.as_mut().unwrap().pop().unwrap();
        if result.is_ok() {
            let node = if self.is_hole(t) {
                RawDerivation {
                    term: t.clone(),
                    ty: expected.clone(),
                    bound,
                    rule: InferenceRule::Hole,
                    premises,
                }
            } else if premises.len() == 1 && premises[0].ty == *expected {
                premises.remove(0)
            } else {
                RawDerivation {
                    term: t.clone(),
                    ty: expected.clone(),
                    bound,
                    rule: InferenceRule::Conversion,
                    premises,
                }
            };
            self.derivation
                .as_mut()
                .unwrap()
                .last_mut()
                .unwrap()
                .push(node);
        }
        result
    }

    fn record_conversion(&mut self, term: &Tm, normal: &Tm) {
        if let Some(frame) = self
            .derivation
            .as_mut()
            .and_then(|frames| frames.last_mut())
            && frame.last().is_some_and(|node| node.ty != *normal)
        {
            let before = frame.pop().unwrap();
            frame.push(RawDerivation {
                term: term.clone(),
                ty: normal.clone(),
                bound: before.bound.clone(),
                rule: InferenceRule::Conversion,
                premises: vec![before],
            });
        }
    }

    /// The sort of the `Π`s nested at the head of `t`, as `infer_one` finds
    /// it one `Π` at a time: each domain's sort under the binders before it,
    /// then the sort of what is under them all. The atoms of the binders
    /// wait (`env`) and are put into each domain as it is read, and into the
    /// rest only where the `Π`s end: putting each into the whole rest of the
    /// telescope walks it once per binder. The path is the one `infer_one`
    /// takes (`enter`), so a part that fails fails in the same place.
    fn infer_telescope(&mut self, t: &Tm) -> Result<Tm, Box<Fault>> {
        let base = self.enter_none();
        let mut env: Vec<R> = Vec::new();
        let mut sorts: Vec<Sort> = Vec::new();
        let mut cur = t;
        let last = loop {
            match cur {
                Pi(h, a, b) => {
                    let a = inst_env(a, 0, &env);
                    let s = match self.down(0, None, |c| c.infer_sort(&a)) {
                        Ok(s) => s,
                        Err(e) => {
                            self.leave(base);
                            return Err(e);
                        }
                    };
                    sorts.push(s);
                    let x = self.fresh((*a).clone());
                    self.enter(1, Some((x, h)));
                    env.push(Arc::new(FVar(x)));
                    cur = b;
                }
                _ => {
                    let rest = Arc::new(cur.clone());
                    let r = self.infer_sort(&inst_env(&rest, 0, &env));
                    break r;
                }
            }
        };
        self.leave(base);
        let mut s = last?;
        while let Some(d) = sorts.pop() {
            s = sort_max(d, s);
        }
        Ok(Sort(s))
    }

    /// `t`, the λs nested at its head, checked against `expected` as
    /// `check_unrecorded` checks them one at a time: each λ against the `Π`
    /// its expected type reduces to, then the body under them all against
    /// what is under the `Π`s. The atoms of the binders wait (`env`) and are
    /// put into the body and the expected type only where the λs end, and
    /// into each domain as it is read: putting each into the whole rest of
    /// the body walks it once per binder. An expected type that is not a `Π`
    /// as it stands is put in and reduced (`whnf`), as there at each λ.
    fn check_lams(&mut self, t: &Tm, expected: &Tm) -> Result<(), Box<Fault>> {
        let base = self.enter_none();
        let mut env_t: Vec<R> = Vec::new();
        let mut env_e: Vec<R> = Vec::new();
        let mut cod: R = Arc::new(expected.clone());
        let mut cur = t;
        let result = loop {
            let Lam(h, body) = cur else {
                let rest = Arc::new(cur.clone());
                break self.check(&inst_env(&rest, 0, &env_t), &inst_env(&cod, 0, &env_e));
            };
            if !matches!(*cod, Pi(..)) {
                let full = inst_env(&cod, 0, &env_e);
                env_e.clear();
                let normal = self.whnf(&full);
                if !matches!(normal, Pi(..)) {
                    break Err(self.fault(Why::NoPi((*full).clone())));
                }
                cod = Arc::new(normal);
            } else {
                // A `Π` is its own weak head normal form: the reduction
                // `check_unrecorded` asks for takes one step of the budget.
                let _ = self.spend();
            }
            let Pi(_, dom, rest) = &*cod else {
                unreachable!("a Π was just found")
            };
            let dom = inst_env(dom, 0, &env_e);
            let rest = rest.clone();
            let x = self.fresh((*dom).clone());
            self.enter(0, Some((x, h)));
            env_t.push(Arc::new(FVar(x)));
            env_e.push(Arc::new(FVar(x)));
            cod = rest;
            cur = body;
        };
        self.leave(base);
        result
    }

    fn check_unrecorded(&mut self, t: &Tm, expected: &Tm) -> Result<(), Box<Fault>> {
        if matches!(t, Lam(..)) && self.derivation.is_none() {
            return self.check_lams(t, expected);
        }
        if let Lam(h, body) = t {
            let normal = self.whnf(expected);
            let Some((_, dom, cod)) = normal.pi_parts() else {
                return Err(self.fault(Why::NoPi(expected.clone())));
            };
            let x = self.fresh((*dom).clone());
            let result = self.down(0, Some((x, h)), |c| {
                c.check(&inst(body, &FVar(x)), &inst(&cod, &FVar(x)))
            });
            if result.is_ok()
                && let Some(frames) = &mut self.derivation
            {
                let frame = frames.last_mut().unwrap();
                let premises = std::mem::take(frame);
                let bound = self
                    .track
                    .as_ref()
                    .map(|tr| tr.bound.clone())
                    .unwrap_or_default();
                frame.push(RawDerivation {
                    term: t.clone(),
                    ty: normal,
                    bound,
                    rule: InferenceRule::Introduction,
                    premises,
                });
            }
            return result;
        }
        if let FVar(x) = t
            && let Some(tr) = &mut self.track
            && tr.holes.contains(x)
        {
            let bound = tr.bound.clone();
            tr.met.push((*x, expected.clone(), bound));
            return Ok(());
        }
        let actual = self.infer(t)?;
        if self.subtype(&actual, expected) {
            Ok(())
        } else {
            Err(self.fault(Why::Mismatch {
                expected: expected.clone(),
                found: actual,
            }))
        }
    }

    /// The atom of the context's `i`-th variable, its type read the first
    /// time.
    fn local(&self, o: &mut Open<'_>, i: usize) -> u64 {
        if let Some(x) = o.atoms[i] {
            return x;
        }
        let x = o.atom();
        o.atoms[i] = Some(x);
        let visible = std::mem::replace(&mut o.visible, i);
        let known = std::mem::replace(&mut o.known, false);
        let ty = self.read_open(&o.ctx[i].1, o);
        o.known = known;
        o.visible = visible;
        o.types.push((x, ty));
        x
    }

    /// The atom of a name only the named checker has declared, its type
    /// read the first time.
    fn declared(&self, o: &mut Open<'_>, n: &Name) -> Option<u64> {
        if let Some((_, x)) = o.declared.iter().find(|(m, _)| m == n) {
            return Some(*x);
        }
        let ty = (o.outer?)(n)?;
        let x = o.atom();
        o.declared.push((n.clone(), x));
        let visible = std::mem::replace(&mut o.visible, 0);
        let known = std::mem::replace(&mut o.known, false);
        let ty = self.read_open(&ty, o);
        o.known = known;
        o.visible = visible;
        o.types.push((x, ty));
        Some(x)
    }

    fn read_open(&self, t: &T, o: &mut Open<'_>) -> Tm {
        self.read_in(t, &mut Vec::new(), Some(o))
            .expect("an open reading reads every term")
    }

    /// Reads `terms` in `ctx` and calls `f` with the resulting terms and the
    /// context's atoms in scope.
    fn ask<X>(
        &mut self,
        ctx: &Ctx,
        terms: &[&T],
        f: impl FnOnce(&mut Self, &[Tm], &Open) -> X,
    ) -> X {
        self.ask_with(ctx, None, terms, f)
    }

    /// [`Self::ask`], with the names `outer` gives a type to read as atoms
    /// of that type.
    fn ask_with<X>(
        &mut self,
        ctx: &Ctx,
        outer: Option<Declared<'_>>,
        terms: &[&T],
        f: impl FnOnce(&mut Self, &[Tm], &Open) -> X,
    ) -> X {
        let mut o = Open::new(ctx);
        o.outer = outer;
        o.known = self.use_known;
        let read: Vec<Tm> = terms
            .iter()
            .map(|t| {
                o.top = o.known;
                self.read_open(t, &mut o)
            })
            .collect();
        self.lctx.extend(o.types.drain(..));
        self.lvals.extend(o.values.drain(..));
        let x = f(self, &read, &o);
        self.lctx.clear();
        self.lvals.clear();
        x
    }

    pub(super) fn conv_in(&mut self, ctx: &Ctx, a: &T, b: &T) -> bool {
        self.ask(ctx, &[a, b], |c, t, _| c.conv(&t[0], &t[1]))
    }

    pub(super) fn proof_conversion_in(
        &mut self,
        ctx: &Ctx,
        a: &T,
        b: &T,
        declared: Declared<'_>,
    ) -> bool {
        self.ask_with(ctx, Some(declared), &[a, b], |c, read, _| {
            c.conv(&read[0], &read[1])
        })
    }

    /// Whether a term of `a` is one of `b` in `ctx` (the sorts are cumulative).
    pub(super) fn subtype_in(&mut self, ctx: &Ctx, a: &T, b: &T) -> bool {
        self.ask(ctx, &[a, b], |c, t, _| c.subtype(&t[0], &t[1]))
    }

    /// [`Self::whnf_in`] for a message: what is past the first nodes of the
    /// result is written as `…` (`pruned`).
    pub(super) fn whnf_shown(&mut self, ctx: &Ctx, t: &T) -> T {
        if self.stuck(ctx, t) {
            return t.clone();
        }
        self.ask(ctx, &[t], |c, read, o| {
            let w = c.whnf(&read[0]);
            if w == read[0] {
                return t.clone();
            }
            Self::write(
                &pruned(&w, &mut SHOWN_NODES.clone()),
                o,
                &mut Vec::new(),
                t.span,
            )
        })
    }

    /// `t` reduced at its head without unfolding names (`whnf_with` without delta), written
    /// back as a named term.
    pub(super) fn beta_in(&mut self, ctx: &Ctx, t: &T) -> T {
        if self.stuck(ctx, t) {
            return t.clone();
        }
        self.ask(ctx, &[t], |c, read, o| {
            let w = c.whnf_with(&read[0], false);
            if w == read[0] || written_size(&w, &mut HashMap::default()) > WRITTEN_LIMIT {
                return t.clone();
            }
            Self::write(&w, o, &mut Vec::new(), t.span)
        })
    }

    /// `t` in weak head normal form in `ctx`, written back as a named term.
    /// What did not reduce is given back as it was written, and so is a form
    /// too large to write: the core shares the parts of a term, a named term
    /// does not, so a form that unfolds a long computation on a variable
    /// (many rounds of a hash on an unknown block) can be small in the core
    /// and larger than memory written out. Either is equal to `t`.
    pub(super) fn whnf_in(&mut self, ctx: &Ctx, t: &T) -> T {
        if self.stuck(ctx, t) {
            return t.clone();
        }
        self.ask(ctx, &[t], |c, read, o| {
            let w = c.whnf(&read[0]);
            if w == read[0] || written_size(&w, &mut HashMap::default()) > WRITTEN_LIMIT {
                return t.clone();
            }
            Self::write(&w, o, &mut Vec::new(), t.span)
        })
    }

    /// `t` typed in `ctx` as `ask` says: what it asked for and the holes
    /// met, or where and why `t` does not type. A name the core does not
    /// have is read as a variable of the type `declared` gives it (the
    /// named checker declares a family before the core reads it, and keeps
    /// declarations the core never gets, such as a theorem with a hole). A
    /// binder entered on the way is shown under the name it was written
    /// with, primed where that is a name of `ctx`, a global, a sort, one of
    /// `avoid`, or an earlier binder's.
    pub(super) fn type_in(
        &mut self,
        ctx: &Ctx,
        t: &T,
        ask: Ask<'_>,
        declared: Declared<'_>,
        avoid: &[&str],
    ) -> Result<Typed, Box<Failure>> {
        let mut terms = vec![t];
        if let Ask::Check(e) = ask {
            terms.push(e);
        }
        self.ask_with(ctx, Some(declared), &terms, |c, read, o| {
            let holes = o
                .opaque
                .iter()
                .filter(|(_, u)| matches!(*u.kind, TermKind::Hole(_)))
                .map(|(x, _)| *x)
                .collect();
            c.track = Some(Track {
                holes,
                ..Default::default()
            });
            let r = match ask {
                Ask::Infer => c.infer(&read[0]).map(|ty| (Some(ty), None)),
                Ask::Sort => c.infer_sort(&read[0]).map(|s| (None, Some(s))),
                Ask::Check(_) => c.check(&read[0], &read[1]).map(|()| (None, None)),
            };
            let track = c.track.take().expect("the typing is tracked");
            let expected = (read.len() > 1).then(|| (&read[1], terms[1]));
            match r {
                Ok((ty, sort)) => Ok(Typed {
                    ty: ty.map(|ty| c.written(&ty, o, expected, t.span)),
                    sort,
                    derivation: c
                        .derivation
                        .as_mut()
                        .and_then(|frames| frames.last_mut())
                        .and_then(|f| f.pop())
                        .map(|raw| {
                            c.write_derivation(raw, ctx, o, avoid, t.span, &mut HashMap::new())
                        }),
                    holes: track
                        .met
                        .iter()
                        .map(|(x, goal, bound)| {
                            let mut o = o.clone();
                            let bound = c.name_bound(bound, &mut o, avoid);
                            let hole = o.opaque.iter().find(|(y, _)| y == x);
                            Met {
                                hole: hole.expect("a hole is an unread part").1.clone(),
                                goal: c.written(goal, &o, expected, t.span),
                                bound,
                            }
                        })
                        .collect(),
                }),
                Err(f) => {
                    let mut o = o.clone();
                    let bound = c.name_bound(&f.bound, &mut o, avoid);
                    let w = |tm: &Tm| c.written(tm, &o, expected, t.span);
                    let why = match f.why {
                        Why::Said(m) => Failed::Said(m),
                        Why::Mismatch { expected, found } => Failed::Mismatch {
                            expected: w(&expected),
                            found: w(&found),
                        },
                        Why::Unread(x) => match o.opaque.iter().find(|(y, _)| *y == x) {
                            Some((_, u)) => Failed::Unread(u.clone()),
                            None => Failed::Said("kernel-core-unknown-atom"),
                        },
                        Why::NotFunction => Failed::NotFunction,
                        Why::NoPi(e) => Failed::NoPi(w(&e)),
                        Why::NotType => Failed::NotType,
                    };
                    Err(Box::new(Failure {
                        why,
                        at: f.at,
                        bound,
                    }))
                }
            }
        })
    }

    pub(super) fn derivation_in(
        &mut self,
        ctx: &Ctx,
        term: &T,
        expected: &T,
        declared: Declared<'_>,
        avoid: &[&str],
    ) -> Result<Typed, Box<Failure>> {
        self.derivation = Some(vec![Vec::new()]);
        let result = self.type_in(ctx, term, Ask::Check(expected), declared, avoid);
        self.derivation = None;
        result
    }

    fn write_derivation(
        &self,
        raw: RawDerivation,
        ctx: &Ctx,
        o: &Open<'_>,
        avoid: &[&str],
        span: tauto_parol::Span,
        bindings: &mut HashMap<u64, Name>,
    ) -> Derivation {
        let mut shown = o.clone();
        let locals = self.name_bound_cached(&raw.bound, &mut shown, avoid, Some(bindings));
        let mut context = ctx.clone();
        context.extend(locals);
        let mut term = Self::write(&raw.term, &shown, &mut Vec::new(), span);
        let ty = Self::write(&raw.ty, &shown, &mut Vec::new(), span);
        let premises: Vec<_> = raw
            .premises
            .into_iter()
            .map(|p| self.write_derivation(p, ctx, o, avoid, span, bindings))
            .collect();
        let introduced: Vec<_> = if raw.rule == InferenceRule::Introduction {
            premises
                .first()
                .map(|p| p.context[context.len()..].to_vec())
                .unwrap_or_default()
        } else {
            Vec::new()
        };
        if raw.rule == InferenceRule::Introduction
            && let Some(body) = premises.first()
        {
            term = T::new(
                TermKind::Lam {
                    params: introduced.iter().map(|(n, _)| n.clone()).collect(),
                    types: Vec::new(),
                    body: Box::new(body.term.clone()),
                    unused_params: Vec::new(),
                },
                span,
            );
        }
        let rule = if raw.rule == InferenceRule::Assumption
            && matches!(&raw.term, FVar(x) if o.declared.iter().any(|(_,y)| x == y))
        {
            InferenceRule::UnverifiedReference
        } else {
            raw.rule
        };
        Derivation {
            context,
            term,
            ty,
            rule,
            introduced,
            premises,
        }
    }

    /// `tm` written back; as it was written when it is the expected type
    /// asked about or the type of a variable of the context.
    fn written(
        &self,
        tm: &Tm,
        o: &Open<'_>,
        expected: Option<(&Tm, &T)>,
        span: tauto_parol::Span,
    ) -> T {
        if let Some((e, written)) = expected
            && e == tm
        {
            return written.clone();
        }
        for (i, x) in o.atoms.iter().enumerate() {
            if let Some(x) = x
                && self.lctx.get(x) == Some(tm)
            {
                return o.ctx[i].1.clone();
            }
        }
        Self::write(tm, o, &mut Vec::new(), span)
    }

    /// The names and types of the binders `bound`, which `o` then shows
    /// under those names.
    fn name_bound(
        &self,
        bound: &[(u64, Hint)],
        o: &mut Open<'_>,
        avoid: &[&str],
    ) -> Vec<(Name, T)> {
        self.name_bound_cached(bound, o, avoid, None)
    }

    fn name_bound_cached(
        &self,
        bound: &[(u64, Hint)],
        o: &mut Open<'_>,
        avoid: &[&str],
        mut bindings: Option<&mut HashMap<u64, Name>>,
    ) -> Vec<(Name, T)> {
        let mut out = Vec::new();
        for (x, h) in bound {
            let base = h.0.as_deref().unwrap_or("x");
            let taken = |n: &str| {
                o.ctx.iter().any(|(m, _)| m.as_str() == n)
                    || o.named.iter().any(|(_, m)| m.as_str() == n)
                    || self
                        .names
                        .get(n)
                        .is_some_and(|id| self.globals.contains_key(id))
                    || sort_named(n).is_some()
                    || avoid.contains(&n)
            };
            let name = (0..)
                .map(|i| match i {
                    0 => base.to_string(),
                    i => format!("{base}'{i}"),
                })
                .find(|n| !taken(n))
                .expect("a fresh name");
            let ty = self.lctx.get(x).expect("a bound atom has a type");
            let ty = Self::write(ty, o, &mut Vec::new(), Default::default());
            let name = if let Some(name) = bindings.as_ref().and_then(|all| all.get(x)) {
                name.clone()
            } else {
                match &h.0 {
                    Some(reference @ Name::Local(_))
                        if !o.ctx.iter().any(|(other, _)| other == reference)
                            && !o.named.iter().any(|(_, other)| other == reference) =>
                    {
                        reference.clone()
                    }
                    _ => Name::from(tauto_surface::identity::LocalRef::fresh(name)),
                }
            };
            if let Some(all) = bindings.as_mut() {
                all.insert(*x, name.clone());
            }
            o.named.push((*x, name.clone()));
            out.push((name, ty));
        }
        out
    }

    /// Whether `t` is in weak head normal form by its head alone: no rule
    /// applies to a binder, a literal, a variable of the context, or a name
    /// with no value that is neither an eliminator nor an operator. Reading a
    /// large term only to find this out is most of what asking would cost.
    fn stuck(&self, ctx: &Ctx, t: &T) -> bool {
        let mut head = t;
        let mut applied = false;
        while let TermKind::App { function, .. } = &*head.kind {
            head = function;
            applied = true;
        }
        match &*head.kind {
            TermKind::Lam { .. } => !applied,
            TermKind::Pi { .. } | TermKind::Nat(_) | TermKind::Bool(_) => true,
            TermKind::Var(n) => {
                ctx.iter().any(|(m, _)| m == n)
                    || sort_named(n).is_some()
                    || self.names.reference(n).is_some_and(|id| {
                        self.globals.get(&id).is_some_and(|g| {
                            g.value.is_none()
                                && !self.recs.contains_key(id)
                                && !matches!(n.as_str(), "+" | "*" | "-")
                        })
                    })
            }
            _ => false,
        }
    }

    /// A term of the core as a named one. A binder keeps the name it was
    /// written with, primed (`n'1`, …) where that would capture a name its
    /// body uses; one written without a name that its body needs is `x`. The
    /// same term is written the same way wherever it is.
    fn write(t: &Tm, o: &Open<'_>, scope: &mut Vec<Name>, span: tauto_parol::Span) -> T {
        let mut memo = WriteMemo::default();
        memo.root = Some(t);
        Self::write_in(t, o, scope, span, &mut memo)
    }

    /// [`Core::write`], with what was found about the nodes met kept in
    /// `memo` for the binders written after.
    fn write_in(
        t: &Tm,
        o: &Open<'_>,
        scope: &mut Vec<Name>,
        span: tauto_parol::Span,
        memo: &mut WriteMemo<'_>,
    ) -> T {
        let kind = match t {
            BVar(i) => TermKind::Var(scope[scope.len() - 1 - i].clone()),
            FVar(x) => o
                .back(*x)
                .unwrap_or_else(|| TermKind::Var(format!("#{x}").into())),
            Sort(s) => return sort_term(s, span),
            Const(c) => TermKind::Var(Name::Global(c.clone())),
            Lit(k) => TermKind::Nat(k.to_string()),
            App(..) => {
                // The spine is read in place: the memo knows a node by its
                // address, which a copy would not keep.
                let mut head = t;
                let mut args: Vec<&Tm> = Vec::new();
                while let App(f, a) = head {
                    args.push(a);
                    head = f;
                }
                args.reverse();
                TermKind::App {
                    function: Box::new(Self::write_in(head, o, scope, span, memo)),
                    arguments: args
                        .into_iter()
                        .map(|a| Self::write_in(a, o, scope, span, memo))
                        .collect(),
                }
            }
            Pi(h, d, r) => {
                let d = Self::write_in(d, o, scope, span, memo);
                let name = match &h.0 {
                    Some(n) => Some(Self::binder(n, r, o, scope, memo)),
                    None => has_loose(r, 0).then(|| Self::binder("x", r, o, scope, memo)),
                };
                scope.push(name.clone().unwrap_or_else(|| "_".into()));
                let r = Self::write_in(r, o, scope, span, memo);
                scope.pop();
                TermKind::Pi {
                    params: vec![(name, d)],
                    result: Box::new(r),
                    effects: None,
                    unused: Vec::new(),
                }
            }
            Lam(h, b) => {
                let name = Self::binder(h.0.as_deref().unwrap_or("x"), b, o, scope, memo);
                scope.push(name.clone());
                let b = Self::write_in(b, o, scope, span, memo);
                scope.pop();
                TermKind::Lam {
                    params: vec![name],
                    body: Box::new(b),
                    types: Vec::new(),
                    unused_params: Vec::new(),
                }
            }
        };
        T::new(kind, span)
    }

    /// `base`, or the first of `base'1`, `base'2`, … that is not a name
    /// `body` (the body of the binder, under `scope`) uses: its globals, its
    /// context variables, the free names of its unread parts, and the
    /// variables of `scope` it refers to. What a node uses is found once per
    /// node and kept in `memo` (by address), not walked again for each binder
    /// above it: a term with many binders, or one that shares its parts, would
    /// be walked once per binder, as a tree far larger than its nodes.
    fn binder(
        base: &str,
        body: &Tm,
        o: &Open<'_>,
        scope: &[Name],
        memo: &mut WriteMemo<'_>,
    ) -> Name {
        // What the body uses is among what the whole term uses and the
        // names in scope: a name that is neither is not used, and is taken
        // without reading the body.
        if let Some(root) = memo.root {
            let all = Self::mentions(root, o, memo);
            if !all.contains(base) && !scope.iter().any(|n| n.to_string() == base) {
                return tauto_surface::identity::LocalRef::fresh(base.to_string()).into();
            }
        }
        let l = scope.len();
        let levels = Self::levels(body, l + 1, memo);
        let used = Self::mentions(body, o, memo);
        (0..)
            .map(|i| match i {
                0 => base.to_string(),
                i => format!("{base}'{i}"),
            })
            .find(|n| {
                !levels.iter().any(|&v| v < l && scope[v].to_string() == *n) && !used.contains(n)
            })
            .map(|display| tauto_surface::identity::LocalRef::fresh(display).into())
            .expect("a fresh name")
    }

    /// The variables of the scope that `t` refers to, by level (the
    /// outermost 0), where `t` sits `at` levels in (the scope's length plus
    /// the binders between it and `t`): a variable `i` there is the one at
    /// level `at - 1 - i`. Only the ones bound outside `t` are kept, below
    /// `at`. The levels do not depend on where in the term a binder is
    /// written from, so a node is read once for each level it sits at.
    fn levels(t: &Tm, at: usize, memo: &mut WriteMemo<'_>) -> Arc<Vec<usize>> {
        let parts = |memo: &mut WriteMemo<'_>, ps: &[(&Tm, usize)]| -> Arc<Vec<usize>> {
            let mut out: Vec<usize> = Vec::new();
            for (p, a) in ps {
                out.extend(Self::levels(p, *a, memo).iter().filter(|&&v| v < at));
            }
            out.sort_unstable();
            out.dedup();
            Arc::new(out)
        };
        match t {
            BVar(i) => Arc::new((at > *i).then(|| at - 1 - i).into_iter().collect()),
            Pi(_, a, b) | App(a, b) | Lam(_, a @ b) => {
                let key = (t as *const Tm as usize, at);
                if let Some(v) = memo.levels.get(&key) {
                    return v.clone();
                }
                poll_deadline();
                let v = match t {
                    Pi(..) => parts(memo, &[(a, at), (b, at + 1)]),
                    Lam(..) => parts(memo, &[(b, at + 1)]),
                    _ => parts(memo, &[(a, at), (b, at)]),
                };
                memo.levels.insert(key, v.clone());
                v
            }
            _ => Arc::new(Vec::new()),
        }
    }

    /// The names `t` uses as globals, context variables, or free names of
    /// its unread parts. They do not depend on the binders above `t`, so they
    /// are found once for each node.
    fn mentions(t: &Tm, o: &Open<'_>, memo: &mut WriteMemo<'_>) -> Arc<HashSet<String>> {
        let key = t as *const Tm as usize;
        if let Some(v) = memo.mentions.get(&key) {
            return v.clone();
        }
        poll_deadline();
        let v = match t {
            FVar(x) => Arc::new(match o.back(*x) {
                Some(TermKind::Var(m)) => [m.to_string()].into_iter().collect(),
                Some(kind) => super::free_vars(&T::new(kind, Default::default()))
                    .into_iter()
                    .map(|m| m.to_string())
                    .collect(),
                None => HashSet::new(),
            }),
            Const(c) => Arc::new([c.to_string()].into_iter().collect()),
            Lam(_, b) => Self::mentions(b, o, memo),
            Pi(_, a, b) | App(a, b) => {
                let (x, y) = (Self::mentions(a, o, memo), Self::mentions(b, o, memo));
                let (big, small) = if x.len() >= y.len() { (x, y) } else { (y, x) };
                if small.iter().all(|n| big.contains(n)) {
                    big
                } else {
                    let mut u = (*big).clone();
                    u.extend(small.iter().cloned());
                    Arc::new(u)
                }
            }
            _ => Arc::new(HashSet::new()),
        };
        memo.mentions.insert(key, v.clone());
        v
    }

    // ---- declarations -----------------------------------------------------

    fn fresh_name(&self, name: &Name) -> Res<()> {
        if self
            .names
            .reference(name)
            .is_some_and(|id| self.globals.contains_key(&id))
        {
            return fail(msg!(
                "kernel-core-already-defined",
                name = (name).to_string()
            ));
        }
        Ok(())
    }

    /// A theorem, definition or function: its statement is a type, and its
    /// value (when given) has that type. `transparent` lets it unfold.
    fn add_decl_inner(
        &mut self,
        name: &Name,
        ty: &T,
        value: Option<&T>,
        transparent: bool,
    ) -> Res<()> {
        self.fresh_name(name)?;
        let ty = self.read(ty)?;
        self.infer_sort(&ty)?;
        let quot = self.quot_constant(name, &ty, value.is_some())?;
        let value = match value {
            Some(v) => {
                let v = self.read(v)?;
                self.check(&v, &ty)?;
                Some(v)
            }
            None => None,
        };
        self.lctx.clear();
        if let Some(id) = self.names.reference(name).cloned() {
            self.touch(&id);
        }
        if let (Some(v), true) = (&value, transparent) {
            self.no_unfolding_cycle(name, v)?;
        }
        let again = self
            .names
            .reference(name)
            .is_some_and(|id| self.globals.contains_key(&id));
        let id = self.names.register(name);
        self.touch(&id);
        self.globals.insert(
            self.names.register(name),
            Global {
                ty,
                value: if transparent {
                    value.map(Arc::new)
                } else {
                    None
                },
            },
        );
        if quot {
            self.quot.insert(self.names.register(name));
        }
        // What nodes reduced to was found with the names as they were.
        self.shared.clear();
        // A new name changes no other's height; a name given again may.
        if again {
            self.defs.clear();
        }
        Ok(())
    }

    /// Takes back a declaration added a moment ago, so that it can be
    /// checked again (`check/cache.rs`).
    pub(super) fn forget(&mut self, name: &Name) {
        #[cfg(feature = "selfhost")]
        if let Some(trace) = &mut self.replay {
            trace.push((format!("F {name}"), true));
        }
        if let Some(id) = self.names.reference(name).cloned() {
            self.touch(&id);
            self.globals.remove(&id);
            self.quot.remove(&id);
        }
        self.shared.clear();
        self.defs.clear();
    }

    /// A top-level `let`: its type is inferred.
    fn add_constant_inner(&mut self, name: &Name, value: &T) -> Res<()> {
        self.fresh_name(name)?;
        let v = self.read(value)?;
        let ty = self.infer(&v)?;
        self.lctx.clear();
        if let Some(id) = self.names.reference(name).cloned() {
            self.touch(&id);
        }
        self.no_unfolding_cycle(name, &v)?;
        let id = self.names.register(name);
        self.touch(&id);
        self.globals.insert(
            self.names.register(name),
            Global {
                ty,
                value: Some(Arc::new(v)),
            },
        );
        self.shared.clear();
        Ok(())
    }

    /// Makes an accepted declaration unfold (a function whose body the
    /// named checker compiled after checking its statement).
    fn set_value_inner(&mut self, name: &Name, value: &T) -> Res<()> {
        if self
            .names
            .reference(name)
            .is_some_and(|id| self.quot.contains(&id))
        {
            return fail(msg!("kernel-core-quot-no-value", name = (name).to_string()));
        }
        let v = self.read(value)?;
        let ty = self
            .names
            .reference(name)
            .and_then(|id| self.globals.get(&id))
            .map(|g| g.ty.clone())
            .ok_or_else(|| msg!("kernel-core-not-defined", name = (name).to_string()))?;
        self.check(&v, &ty)?;
        self.lctx.clear();
        if let Some(id) = self.names.reference(name).cloned() {
            self.touch(&id);
        }
        self.no_unfolding_cycle(name, &v)?;
        if let Some(g) = self
            .names
            .reference(name)
            .and_then(|id| self.globals.get_mut(&id))
        {
            g.value = Some(Arc::new(v));
        }
        self.shared.clear();
        self.defs.clear();
        Ok(())
    }

    /// Termination of unfolding. Recursion reaches the core only through
    /// eliminators (`check/matching.rs` compiles structural recursion to
    /// them, `check/wf.rs` well-founded recursion to `wf_fix`), so no value
    /// needs to reach its own name. A value that does, at once or through the
    /// values of other names, is a definition the core has no reason to
    /// believe terminates: `f := λn. Succ(f n)` would make `f 0 ≡ Succ(f 0)`
    /// hold by reflexivity. Such a value is refused here, by the core itself,
    /// whatever the named checker decided.
    fn no_unfolding_cycle(&mut self, name: &Name, v: &Tm) -> Res<()> {
        let Some(target) = self.names.reference(name).cloned() else {
            return Ok(());
        };
        // `target` is not among `cycle_names`: giving it a value, or adding it,
        // touched it first. So a name of `cycle_free` does not reach it.
        debug_assert!(!self.cycle_names.contains(&target));
        let mut seen_nodes: HashSet<usize> = HashSet::new();
        let mut seen_names: HashSet<DeclRef> = HashSet::new();
        let mut todo: Vec<R> = vec![Arc::new(v.clone())];
        while let Some(n) = todo.pop() {
            if !seen_nodes.insert(Arc::as_ptr(&n) as usize) {
                continue;
            }
            match &*n {
                Const(d) => {
                    if *d == target {
                        return fail(msg!("kernel-core-value-cycle", name = (name).to_string()));
                    }
                    if !self.cycle_free.contains(d)
                        && seen_names.insert(d.clone())
                        && let Some(w) = self.globals.get(d).and_then(|g| g.value.clone())
                    {
                        todo.push(w);
                    }
                }
                Pi(_, a, b) | App(a, b) => {
                    todo.push(a.clone());
                    todo.push(b.clone());
                }
                Lam(_, b) => todo.push(b.clone()),
                _ => {}
            }
        }
        // Every name met had its value followed to the end, or was of
        // `cycle_free`: what each reaches is among the names met and
        // `cycle_names`. So is what `target`'s value reaches.
        self.cycle_free.extend(seen_names.iter().cloned());
        self.cycle_names.extend(seen_names);
        self.cycle_free.insert(target.clone());
        self.cycle_names.insert(target);
        Ok(())
    }

    /// Before a change to the global `id`: what [`Core::no_unfolding_cycle`]
    /// found is forgotten when `id` is among the names it reached.
    fn touch(&mut self, id: &DeclRef) {
        if self.cycle_names.contains(id) {
            self.forget_cycles();
        }
    }

    fn forget_cycles(&mut self) {
        self.cycle_free.clear();
        self.cycle_names.clear();
    }

    /// An inductive declaration (a `mutual` group when there are several
    /// families) with `np` shared parameters, in the sort `out`. On success
    /// the families, constructors, nested members and eliminators are added.
    fn add_inductive_inner(&mut self, fams: &[FamSpec], np: usize, out: Sort) -> Res<()> {
        let saved = (
            self.globals.clone(),
            self.ctors.clone(),
            self.recs.clone(),
            self.inds.clone(),
            self.rec_targets.clone(),
            self.eliminators.clone(),
            self.names.clone(),
        );
        let result = self.inductive_inner(fams, np, out);
        if result.is_err() {
            (
                self.globals,
                self.ctors,
                self.recs,
                self.inds,
                self.rec_targets,
                self.eliminators,
                self.names,
            ) = saved;
            self.forget_cycles();
        }
        self.lctx.clear();
        self.shared.clear();
        self.defs.clear();
        result
    }

    fn inductive_inner(&mut self, specs: &[FamSpec], np: usize, out: Sort) -> Res<()> {
        let names: Vec<DeclRef> = specs.iter().map(|f| self.names.register(&f.name)).collect();
        // Families first, so constructors (and siblings) can mention them.
        let mut fam_tys = Vec::new();
        for f in specs {
            self.fresh_name(&f.name)?;
            let ty = self.read(&f.ty)?;
            self.infer_sort(&ty)?;
            fam_tys.push(ty.clone());
            let id = self.names.register(&f.name);
            self.touch(&id);
            self.globals
                .insert(self.names.register(&f.name), Global { ty, value: None });
        }
        // The parameters are shared by the group, written the same way.
        for ty in &fam_tys[1..] {
            let (mut a, mut b) = (&fam_tys[0], ty);
            for _ in 0..np {
                match (a, b) {
                    (Pi(_, d1, r1), Pi(_, d2, r2)) if d1 == d2 => {
                        a = r1;
                        b = r2;
                    }
                    _ => return fail(msg!("kernel-core-group-share-params")),
                }
            }
        }
        let mut params: Vec<u64> = Vec::new();
        let mut walk = fam_tys[0].clone();
        for _ in 0..np {
            let Some((_, d, b)) = walk.pi_parts() else {
                return fail(msg!("kernel-core-family-fewer-params"));
            };
            let x = self.fresh((*d).clone());
            walk = inst(&b, &FVar(x));
            params.push(x);
        }
        let pvars: Vec<Tm> = params.iter().map(|x| FVar(*x)).collect();
        let mut members: Vec<Member> = Vec::new();
        for (k, ty) in fam_tys.iter().enumerate() {
            let mut walk = ty.clone();
            for x in &params {
                let Some((_, _, b)) = walk.pi_parts() else {
                    return fail(msg!("kernel-core-family-fewer-params"));
                };
                walk = inst(&b, &FVar(*x));
            }
            let index_tel = walk.clone();
            let mut indices = 0;
            while let Some((_, d, b)) = walk.pi_parts() {
                let x = self.fresh((*d).clone());
                walk = inst(&b, &FVar(x));
                indices += 1;
            }
            if self.whnf(&walk) != Sort(out.clone()) {
                return fail(msg!("kernel-core-group-sort"));
            }
            members.push(Member {
                name: names[k].clone(),
                index_tel,
                indices,
                alias: None,
                ctors: Vec::new(),
            });
        }
        // Constructors of the declared families.
        let mut taken: Vec<DeclRef> = names.clone();
        for (k, f) in specs.iter().enumerate() {
            for (cname, cty) in &f.ctors {
                self.fresh_name(cname)?;
                if taken.contains(&self.names.register(cname)) {
                    return fail(msg!(
                        "kernel-core-ctor-already-defined",
                        name = (cname).to_string()
                    ));
                }
                taken.push(self.names.register(cname));
                let ty = self.read(cty)?;
                self.infer_sort(&ty)?;
                let mut walk = ty;
                for x in &params {
                    let Some((_, d, b)) = walk.pi_parts() else {
                        return fail(msg!(
                            "kernel-core-ctor-take-params",
                            name = (cname).to_string()
                        ));
                    };
                    let px = self.lctx[x].clone();
                    if *d != px && !self.conv(&d, &px) {
                        return fail(msg!(
                            "kernel-core-ctor-take-params",
                            name = (cname).to_string()
                        ));
                    }
                    walk = inst(&b, &FVar(*x));
                }
                let mut args = Vec::new();
                while let Some((_, d, b)) = walk.pi_parts() {
                    let s = self.infer_sort(&d)?;
                    if out != Sort::Prop && !s.le(&out) {
                        return fail(msg!(
                            "kernel-core-ctor-arg-universe",
                            name = (cname).to_string()
                        ));
                    }
                    let x = self.fresh((*d).clone());
                    args.push((x, (*d).clone()));
                    walk = inst(&b, &FVar(x));
                }
                let (head, rargs) = spine(&walk);
                if !matches!(head, Const(c) if *c == names[k])
                    || rargs.len() != np + members[k].indices
                    || rargs[..np] != pvars[..]
                {
                    return fail(msg!(
                        "kernel-core-ctor-must-return",
                        name = (cname).to_string(),
                        family = (&f.name).to_string()
                    ));
                }
                let result_idx = rargs[np..].to_vec();
                if result_idx.iter().any(|t| mentions_const(t, &names)) {
                    return fail(msg!(
                        "kernel-core-index-mentions-family",
                        name = (cname).to_string()
                    ));
                }
                members[k].ctors.push(Ctor {
                    name: self.names.register(cname),
                    args,
                    result_idx,
                    recs: Vec::new(),
                });
            }
        }
        // Positivity, nested occurrences and recursive arguments: for the
        // declared families, then for the members nesting adds (whose
        // constructors are those of the type they stand for).
        let mut group: Vec<DeclRef> = names.clone();
        let mut aliases: Vec<(DeclRef, Vec<Tm>)> = Vec::new();
        let mut at = 0;
        while at < members.len() {
            for ci in 0..members[at].ctors.len() {
                for ai in 0..members[at].ctors[ci].args.len() {
                    let d = members[at].ctors[ci].args[ai].1.clone();
                    let internal = self.nest(&d, np, &mut group, &mut aliases)?;
                    positive(&group, &internal)?;
                    if let Some(r) = self.recursive(&group, &members, &pvars, ai, &internal)? {
                        members[at].ctors[ci].recs.push(r);
                    }
                }
            }
            while members.len() < group.len() {
                let (j, jargs) = aliases[members.len() - names.len()].clone();
                let jind = self
                    .inds
                    .get(&j)
                    .cloned()
                    .ok_or_else(|| msg!("kernel-core-nested-not-inductive"))?;
                let mut ctors = Vec::new();
                for jc in &jind.ctors {
                    let mut walk = self.globals[&jc.name].ty.clone();
                    for a in &jargs {
                        let Some((_, _, b)) = walk.pi_parts() else {
                            return fail(msg!("kernel-core-nested-ctor-params"));
                        };
                        walk = inst(&b, a);
                    }
                    let mut args = Vec::new();
                    while let Some((_, d, b)) = walk.pi_parts() {
                        let x = self.fresh((*d).clone());
                        args.push((x, (*d).clone()));
                        walk = inst(&b, &FVar(x));
                    }
                    ctors.push(Ctor {
                        name: jc.name.clone(),
                        args,
                        result_idx: Vec::new(),
                        recs: Vec::new(),
                    });
                }
                members.push(Member {
                    name: group[members.len()].clone(),
                    index_tel: Sort(out.clone()),
                    indices: 0,
                    alias: Some((j, jargs)),
                    ctors,
                });
            }
            at += 1;
        }
        if members.len() > specs.len() && out == Sort::Prop {
            return fail(msg!("kernel-core-nested-only-type"));
        }
        // Large elimination from `Prop`: no constructor, or one whose every
        // argument is a proof or one of the result's indices.
        let large = out != Sort::Prop
            || match members.as_slice() {
                [only] => match only.ctors.as_slice() {
                    [] => true,
                    [c] => {
                        let mut ok = true;
                        for (x, d) in &c.args {
                            let proof = self.infer_sort(d)? == Sort::Prop;
                            if !proof && !c.result_idx.contains(&FVar(*x)) {
                                ok = false;
                            }
                        }
                        ok
                    }
                    _ => false,
                },
                _ => false,
            };
        for m in members.iter().take(specs.len()) {
            for (j, c) in m.ctors.iter().enumerate() {
                let mut ty = apps(
                    Const(m.name.clone()),
                    pvars.iter().cloned().chain(c.result_idx.iter().cloned()),
                );
                for (x, d) in c.args.iter().rev() {
                    ty = pi_over(*x, d.clone(), &ty);
                }
                for x in params.iter().rev() {
                    ty = pi_over(*x, self.lctx[x].clone(), &ty);
                }
                self.touch(&c.name.clone());
                self.globals
                    .insert(c.name.clone(), Global { ty, value: None });
                self.ctors.insert(c.name.clone(), (m.name.clone(), j));
            }
        }
        let mut sorts = vec![Sort::Prop];
        if large {
            sorts.push(Sort::ty(1));
        }
        let mut elims = Vec::new();
        for ms in sorts.iter().cloned() {
            for k in 0..members.len() {
                let name = self.reserve_eliminator(
                    &members[k].name,
                    &if ms == Sort::Prop {
                        Elimination::Induction
                    } else {
                        Elimination::Recursion
                    },
                );
                self.fresh_name(&Name::from(name.clone()))?;
                let ty = self.eliminator(&members, &params, k, ms.clone());
                if mentions_fvar(&ty) || has_loose(&ty, 0) {
                    return fail(msg!("kernel-core-eliminator-not-closed"));
                }
                self.infer_sort(&ty)?;
                elims.push((name, k, ty));
            }
        }
        for group in elims.chunks(members.len()) {
            let targets: Vec<_> = group.iter().map(|(name, _, _)| name.clone()).collect();
            for name in &targets {
                self.rec_targets.insert(name.clone(), targets.clone());
            }
        }
        for (name, k, ty) in elims {
            self.touch(&name);
            self.globals
                .insert(name.clone(), Global { ty, value: None });
            self.recs.insert(name, members[k].name.clone());
        }
        let group_names: Vec<DeclRef> = members.iter().map(|m| m.name.clone()).collect();
        for (pos, m) in members.iter().enumerate() {
            let k_like = match m.ctors.as_slice() {
                [c] if out == Sort::Prop && members.len() == 1 && c.args.is_empty() => Some(
                    c.result_idx
                        .iter()
                        .map(|t| abstract_many(t, &params))
                        .collect(),
                ),
                _ => None,
            };
            let mut ctors = Vec::new();
            for c in &m.ctors {
                let mut env = params.clone();
                env.extend(c.args.iter().map(|(x, _)| *x));
                let recs = c
                    .recs
                    .iter()
                    .map(|r| {
                        let mut env = env.clone();
                        env.extend(r.ys.iter().map(|(y, _)| *y));
                        RecArg {
                            arg: r.arg,
                            ys: r.ys.len(),
                            fam: r.fam,
                            idx: r.idx.iter().map(|t| abstract_many(t, &env)).collect(),
                        }
                    })
                    .collect();
                ctors.push(CtorInfo {
                    name: c.name.clone(),
                    nargs: c.args.len(),
                    recs,
                });
            }
            self.inds.insert(
                m.name.clone(),
                Arc::new(IndInfo {
                    params: np,
                    indices: m.indices,
                    group: group_names.clone(),
                    pos,
                    ctors,
                    alias: m.alias.clone(),
                    k_like,
                }),
            );
        }
        Ok(())
    }

    /// `d` with a nested occurrence `J(args)` (a type outside the group,
    /// whose arguments mention the group) at the end of its `Pi`s replaced
    /// by a member of the group standing for it, created on first use.
    fn nest(
        &mut self,
        d: &Tm,
        np: usize,
        group: &mut Vec<DeclRef>,
        aliases: &mut Vec<(DeclRef, Vec<Tm>)>,
    ) -> Res<Tm> {
        if let Pi(h, a, b) = d {
            return Ok(Pi(
                h.clone(),
                a.clone(),
                Arc::new(self.nest(b, np, group, aliases)?),
            ));
        }
        let (head, args) = spine(d);
        let Const(j) = head else {
            return Ok(d.clone());
        };
        if group.contains(j)
            || !self.inds.contains_key(j)
            || !args.iter().any(|a| mentions_const(a, group))
        {
            return Ok(d.clone());
        }
        let jind = &self.inds[j];
        if np > 0 {
            return fail(msg!("kernel-core-nested-no-params"));
        }
        if jind.indices > 0 || jind.group.len() > 1 || args.len() != jind.params {
            return fail(msg!("kernel-core-cannot-nest", name = j.display()));
        }
        if args.iter().any(|a| mentions_fvar(a) || has_loose(a, 0)) {
            return fail(msg!("kernel-core-nested-depends"));
        }
        if let Some(k) = aliases.iter().position(|(j2, a2)| j2 == j && *a2 == args) {
            return Ok(Const(group[group.len() - aliases.len() + k].clone()));
        }
        let member = group[0].generated(tauto_surface::identity::Generation::Nested(aliases.len()));
        self.fresh_name(&Name::from(member.clone()))?;
        group.push(member.clone());
        aliases.push((j.clone(), args));
        Ok(Const(member))
    }

    /// A recursive argument `∀ ys. G(params, idx)` with `G` in the group.
    fn recursive(
        &mut self,
        group: &[DeclRef],
        members: &[Member],
        pvars: &[Tm],
        arg: usize,
        d: &Tm,
    ) -> Res<Option<Rec>> {
        let mut ys = Vec::new();
        let mut walk = d.clone();
        while let Some((_, a, b)) = walk.pi_parts() {
            let y = self.fresh((*a).clone());
            ys.push((y, (*a).clone()));
            walk = inst(&b, &FVar(y));
        }
        let (head, args) = spine(&walk);
        let Const(g) = head else {
            return Ok(None);
        };
        let Some(fam) = group.iter().position(|n| n == g) else {
            return Ok(None);
        };
        // A member nesting adds has no parameters (nesting needs a group
        // without them).
        let np = if fam < members.len() && members[fam].alias.is_none() {
            pvars.len()
        } else {
            0
        };
        let indices = if fam < members.len() {
            members[fam].indices
        } else {
            0
        };
        if args.len() != np + indices || args[..np] != pvars[..np] {
            return fail(msg!("kernel-core-recursive-arg-params", name = g.display()));
        }
        Ok(Some(Rec {
            arg,
            ys,
            fam,
            idx: args[np..].to_vec(),
        }))
    }

    /// The type of the eliminator of the `k`-th member into `ms`: one motive
    /// per member, one minor premise per constructor of the group.
    fn eliminator(&mut self, members: &[Member], params: &[u64], k: usize, ms: Sort) -> Tm {
        let pvars: Vec<Tm> = params.iter().map(|x| FVar(*x)).collect();
        let over_major = |core: &mut Core, m: &Member, body: &dyn Fn(&[Tm], &Tm) -> Tm| -> Tm {
            let mut walk = m.index_tel.clone();
            let mut is = Vec::new();
            while let Some((_, d, b)) = walk.pi_parts() {
                let x = core.fresh((*d).clone());
                is.push((x, (*d).clone()));
                walk = inst(&b, &FVar(x));
            }
            let ivars: Vec<Tm> = is.iter().map(|(x, _)| FVar(*x)).collect();
            let major_ty = match &m.alias {
                Some((j, a)) => apps(Const(j.clone()), a.iter().cloned()),
                None => apps(
                    Const(m.name.clone()),
                    pvars.iter().cloned().chain(ivars.iter().cloned()),
                ),
            };
            let t = core.fresh(major_ty.clone());
            let mut out = pi_over(t, major_ty, &body(&ivars, &FVar(t)));
            for (x, d) in is.iter().rev() {
                out = pi_over(*x, d.clone(), &out);
            }
            out
        };
        let mut motives = Vec::new();
        for m in members {
            let ty = over_major(self, m, &|_, _| Sort(ms.clone()));
            motives.push((self.fresh(ty.clone()), ty));
        }
        let mvars: Vec<Tm> = motives.iter().map(|(x, _)| FVar(*x)).collect();
        let mut minors = Vec::new();
        for (fi, m) in members.iter().enumerate() {
            for c in &m.ctors {
                let cparams: Vec<Tm> = match &m.alias {
                    Some((_, a)) => a.clone(),
                    None => pvars.clone(),
                };
                let built = apps(
                    Const(c.name.clone()),
                    cparams
                        .into_iter()
                        .chain(c.args.iter().map(|(x, _)| FVar(*x))),
                );
                let mut ihs = Vec::new();
                for r in &c.recs {
                    let field = apps(FVar(c.args[r.arg].0), r.ys.iter().map(|(y, _)| FVar(*y)));
                    let mut ih = apps(mvars[r.fam].clone(), r.idx.iter().cloned().chain([field]));
                    for (y, d) in r.ys.iter().rev() {
                        ih = pi_over(*y, d.clone(), &ih);
                    }
                    ihs.push((self.fresh(ih.clone()), ih));
                }
                let mut ty = apps(
                    mvars[fi].clone(),
                    c.result_idx.iter().cloned().chain([built]),
                );
                for (h, d) in ihs.iter().rev() {
                    ty = pi_over(*h, d.clone(), &ty);
                }
                for (x, d) in c.args.iter().rev() {
                    ty = pi_over(*x, d.clone(), &ty);
                }
                minors.push((self.fresh(ty.clone()), ty));
            }
        }
        let mk = mvars[k].clone();
        let mut ty = over_major(self, &members[k], &|is, t| {
            apps(mk.clone(), is.iter().cloned().chain([t.clone()]))
        });
        for (x, d) in minors.iter().rev() {
            ty = pi_over(*x, d.clone(), &ty);
        }
        for (x, d) in motives.iter().rev() {
            ty = pi_over(*x, d.clone(), &ty);
        }
        for x in params.iter().rev() {
            ty = pi_over(*x, self.lctx[x].clone(), &ty);
        }
        ty
    }
}

struct Member {
    name: DeclRef,
    /// `∀ indices. Sort`, over the parameters (atoms).
    index_tel: Tm,
    indices: usize,
    /// A nested member stands for `J(args)`.
    alias: Option<(DeclRef, Vec<Tm>)>,
    ctors: Vec<Ctor>,
}

struct Ctor {
    name: DeclRef,
    /// Argument atoms and their types (over the parameters and the earlier
    /// arguments).
    args: Vec<(u64, Tm)>,
    result_idx: Vec<Tm>,
    recs: Vec<Rec>,
}

struct Rec {
    arg: usize,
    ys: Vec<(u64, Tm)>,
    fam: usize,
    idx: Vec<Tm>,
}

/// Strict positivity: the group occurs only as the target of `∀`s, applied
/// to arguments that do not mention it.
fn positive(group: &[DeclRef], d: &Tm) -> Res<()> {
    if !mentions_const(d, group) {
        return Ok(());
    }
    if let Pi(_, a, b) = d {
        if mentions_const(a, group) {
            return fail(msg!("kernel-core-negative"));
        }
        return positive(group, b);
    }
    let (head, args) = spine(d);
    match head {
        Const(g) if group.contains(g) && !args.iter().any(|a| mentions_const(a, group)) => Ok(()),
        _ => fail(msg!("kernel-core-nested-or-negative")),
    }
}

/// `t` with the atoms `xs` bound, the first outermost.
fn abstract_many(t: &Tm, xs: &[u64]) -> Tm {
    let mut out = t.clone();
    for (k, x) in xs.iter().rev().enumerate() {
        out = abstract_at(&out, k, *x);
    }
    out
}

/// `t` (from `abstract_many`) with its bound atoms replaced by `vals`.
fn inst_many(t: &Tm, vals: &[Tm]) -> Tm {
    let n = vals.len();
    let mut out = t.clone();
    for (k, v) in vals.iter().enumerate() {
        out = inst_at(&out, n - 1 - k, v);
    }
    out
}

#[cfg(test)]
mod tests {
    /// The numeral `n`.
    fn lit(n: u128) -> Tm {
        Tm::Lit(Num::of_u128(n))
    }
    /// [`LARGE_OFFSET`] as a `u128`.
    const LARGE: u128 = 1 << 12;
    use super::super::{Kernel, Stmt, T, parse_program};
    use super::*;

    #[test]
    fn a_global_reference_cannot_be_used_as_a_lexical_binder() {
        tauto_parse::install();
        let mut core = Core::new();
        let reference = DeclRef::fresh("x");
        let name: Name = reference.clone().into();
        let span = Default::default();
        core.add_decl_inner(
            &name,
            &T::var(
                &Name::from(DeclRef::of_sort(tauto_surface::identity::SortSymbol::Type(
                    0,
                ))),
                span,
            ),
            None,
            false,
        )
        .unwrap();
        let term = T::var(&name, span);
        let context = vec![(name.clone(), T::var("Type", span))];
        let mut open = Open::new(&context);
        assert_eq!(
            core.read_in(&term, &mut vec![name.clone()], Some(&mut open))
                .unwrap(),
            Const(reference)
        );
        let lambda = T::new(
            TermKind::Lam {
                params: vec![name],
                types: Vec::new(),
                body: Box::new(term),
                unused_params: Vec::new(),
            },
            span,
        );
        assert!(core.read(&lambda).is_err());
    }

    #[test]
    fn open_declaration_assumptions_require_exact_identity_and_do_not_escape() {
        tauto_parse::install();
        let mut core = Core::new();
        let name: Name = DeclRef::fresh("recursive").into();
        let other: Name = DeclRef::fresh("recursive").into();
        let span = Default::default();
        let ty = T::var("Type", span);
        let context = vec![(name.clone(), ty)];
        let term = T::var(&name, span);
        assert!(
            core.type_in(&context, &term, Ask::Infer, &|_| None, &[])
                .is_ok()
        );
        assert!(
            core.type_in(&context, &T::var(&other, span), Ask::Infer, &|_| None, &[])
                .is_err()
        );
        assert!(core.read(&term).is_err());
        assert!(
            core.type_in(&vec![], &term, Ask::Infer, &|_| None, &[])
                .is_err()
        );
        assert!(!core.globals.contains_key(name.as_global().unwrap()));
    }

    #[test]
    fn intrinsic_dispatch_requires_the_primitive_reference() {
        tauto_parse::install();
        let mut core = Core::new();
        let impostor = DeclRef::fresh("Nat::eq");
        let args = [Arc::new(lit(3)), Arc::new(lit(3))];
        assert!(
            core.top(|c| c.numeric(&impostor, &args))
                .flatten()
                .is_none()
        );
        assert!(
            core.top(|c| c.numeric(&DeclRef::primitive("Nat::eq").unwrap(), &args))
                .flatten()
                .is_some()
        );
        assert_eq!(primitive_operator(&DeclRef::fresh("+")), None);
        assert_eq!(
            primitive_operator(&DeclRef::primitive("+").unwrap()),
            Some("+")
        );
        let unaccepted = core.names.reserve("unaccepted");
        assert!(core.infer(&Const(unaccepted)).is_err());
    }

    #[test]
    fn equal_display_names_cannot_cross_core_environments() {
        tauto_parse::install();
        let mut left = Core::new();
        let mut right = Core::new();
        let ty = T::var("Type", Default::default());
        left.add_decl_inner(&Name::from("Item"), &ty, None, false)
            .unwrap();
        right
            .add_decl_inner(&Name::from("Item"), &ty, None, false)
            .unwrap();
        let reference = left.names.get("Item").unwrap().clone();
        assert_eq!(
            reference.display(),
            right.names.get("Item").unwrap().display()
        );
        assert_ne!(reference, *right.names.get("Item").unwrap());
        assert!(left.infer(&Const(reference.clone())).is_ok());
        assert!(right.infer(&Const(reference)).is_err());
    }

    /// A kernel with the prelude declared.
    fn kernel() -> Kernel {
        let mut k = Kernel::new();
        let prelude = super::super::kernel_prelude().unwrap();
        for e in k.declare(&prelude, true) {
            assert!(!e.failed(), "{e:?}");
        }
        k
    }

    /// The statement and the proof of `theorem t(): TY { BODY }`, curried.
    /// The proof is not elaborated: the core reads it as written. The
    /// statement is, so that an equation `a = b` is the `Eq` it stands for.
    fn read(k: &mut Kernel, src: &str) -> (T, T) {
        let mut p = parse_program(src).unwrap();
        k.resolve_statements(&mut p.stmts);
        let Stmt::Theorem(t) = &p.stmts[0] else {
            panic!()
        };
        let ty = k.telescope(&t.params, &t.ty).unwrap();
        let ty = k.shape(&ty).unwrap();
        let ty = k.elab(&Vec::new(), &ty, None).unwrap();
        let body = k
            .shape(&k.lambda_of(&t.params, t.body.as_ref().unwrap()).unwrap())
            .unwrap();
        // A proof that writes implicit arguments by name (`Refl(<A: Nat, a: 4>)`) has them
        // filled in as the checker does; any other body reaches the core as written.
        let body = if src.contains("(<") {
            k.elab(&Vec::new(), &body, Some(&ty)).unwrap()
        } else {
            body
        };
        (ty, body)
    }

    /// The number a closed `t: Nat` reduces to, read through `Succ`.
    fn number(c: &mut Core, t: &Tm) -> u128 {
        let mut n = 0;
        let mut t = c.whnf(t);
        loop {
            match c.nat_view(&t) {
                Some(None) => return n,
                Some(Some(k)) => {
                    n += 1;
                    t = c.whnf(&k);
                }
                None => panic!("not a number: {t:?}"),
            }
        }
    }

    /// What `Nat::eq`, `Nat::lt`, `Nat::sub`, `Nat::div_nz` and `Nat::rem_nz` compute on numerals
    /// is what unfolding their definitions in the prelude gives.
    #[test]
    fn numeric_agrees_with_unfolding() {
        tauto_parse::install();
        let mut k = kernel();
        let c = &mut k.core;
        let mut pairs: Vec<(u128, u128)> = Vec::new();
        for x in 0..14 {
            for y in 0..14 {
                pairs.push((x, y));
            }
        }
        pairs.extend([
            (100, 7),
            (365, 12),
            (255, 16),
            (64, 64),
            (63, 64),
            (1000, 1),
        ]);
        for &(x, y) in &pairs {
            for op in NUMERIC {
                // The proof that the divisor is not 0 is not looked at.
                let proof = (numeric_arity(op) == 3).then(|| FVar(42));
                let t = apps(konst(op), [lit(x), lit(y)].into_iter().chain(proof));
                c.numeric_off = false;
                let fast = c.whnf(&t);
                c.numeric_off = true;
                // Nothing the fast way found is found again.
                c.shared.clear();
                let slow = c.whnf(&t);
                match *op {
                    "Nat::eq" | "Nat::lt" => assert_eq!(fast, slow, "{op}({x}, {y})"),
                    _ => {
                        let (fast, slow) = (number(c, &fast), number(c, &slow));
                        assert_eq!(fast, slow, "{op}({x}, {y})");
                    }
                }
            }
        }
        c.numeric_off = false;
    }

    /// `Nat::divmod(x + n, b, q, r)` with a large numeral `n` is taken to
    /// `Nat::divmod(x, b, q', r')` at once, and what it is taken to is what
    /// unfolding the definition `n` times gives.
    #[test]
    fn divmod_of_a_large_offset_agrees_with_unfolding() {
        tauto_parse::install();
        let mut k = kernel();
        let c = &mut k.core;
        let n: u128 = LARGE + 3;
        for (i, (b, q, r)) in [
            (7, 3, 6),
            (0, 0, 3),
            (7, 0, 0),
            (64, 0, 0),
            (5001, 1, 2),
            (3, 0, 9),
        ]
        .into_iter()
        .enumerate()
        {
            let t = (r + n, q);
            let (q2, r2) = if b > 0 && r < b {
                (q + t.0 / b, t.0 % b)
            } else {
                (q, t.0)
            };
            let x = apps(konst("+"), [FVar(0), lit(n)]);
            let a = apps(konst("Nat::divmod"), [x, lit(b), lit(q), lit(r)]);
            let e = apps(konst("Nat::divmod"), [FVar(0), lit(b), lit(q2), lit(r2)]);
            // Unfolding takes `n` steps on each side, so it is done for two only.
            for off in [false, true] {
                if off && i >= 2 {
                    continue;
                }
                c.numeric_off = off;
                c.shared.clear();
                c.start_budget(None, None);
                assert!(
                    c.conv(&a, &e),
                    "divmod(x + {n}, {b}, {q}, {r}), unfolding: {off}"
                );
                let steps = c.end_budget().steps;
                if !off {
                    assert!(steps < 1000, "{steps} steps");
                }
            }
        }
        c.numeric_off = false;
    }

    /// `Nat::lt`, `Nat::eq` and `Nat::sub` of `x + n` and a numeral, with a
    /// large `n`, take the `Succ`s both have off at once ([`Core::repeat`]),
    /// to what unfolding gives.
    #[test]
    fn comparison_with_a_large_offset_agrees_with_unfolding() {
        tauto_parse::install();
        let mut k = kernel();
        let c = &mut k.core;
        // Large with 5 less too.
        let n: u128 = LARGE + 8;
        let x = || apps(konst("+"), [FVar(0), lit(n)]);
        let yn = |b: bool| konst(if b { "true" } else { "false" });
        let cases = [
            (
                apps(konst("Nat::lt"), [x(), lit(n + 5)]),
                apps(konst("Nat::lt"), [FVar(0), lit(5)]),
            ),
            (apps(konst("Nat::lt"), [x(), lit(n - 5)]), yn(false)),
            (
                apps(konst("Nat::lt"), [lit(n + 5), x()]),
                apps(konst("Nat::lt"), [lit(5), FVar(0)]),
            ),
            (apps(konst("Nat::lt"), [lit(n - 5), x()]), yn(true)),
            (
                apps(konst("Nat::eq"), [x(), lit(n + 5)]),
                apps(konst("Nat::eq"), [FVar(0), lit(5)]),
            ),
            (
                apps(konst("Nat::eq"), [lit(n + 5), x()]),
                apps(konst("Nat::eq"), [lit(5), FVar(0)]),
            ),
            (apps(konst("Nat::eq"), [x(), lit(n - 5)]), yn(false)),
            (apps(konst("Nat::eq"), [lit(n - 5), x()]), yn(false)),
            (
                apps(konst("Nat::sub"), [x(), lit(n - 5)]),
                apps(konst("+"), [FVar(0), lit(5)]),
            ),
            (
                apps(konst("Nat::sub"), [x(), lit(n + 5)]),
                apps(konst("Nat::sub"), [FVar(0), lit(5)]),
            ),
            (apps(konst("Nat::sub"), [lit(n - 5), x()]), lit(0)),
        ];
        for (i, (a, e)) in cases.iter().enumerate() {
            for off in [false, true] {
                // Unfolding takes `n` steps, so it is done for a few only.
                if off && i % 3 != 0 {
                    continue;
                }
                c.numeric_off = off;
                c.shared.clear();
                c.start_budget(None, None);
                assert!(c.conv(a, e), "case {i}, unfolding: {off}");
                let steps = c.end_budget().steps;
                if !off {
                    assert!(steps < 1000, "case {i}: {steps} steps");
                }
            }
        }
        c.numeric_off = false;
    }

    /// Two terms that share their nodes are compared once per pair of nodes:
    /// `x * 1 + x` nested 64 deep is a tree of `2^64` nodes.
    #[test]
    fn equality_of_shared_terms_is_linear() {
        tauto_parse::install();
        let mut a = Arc::new(FVar(0));
        let mut b = Arc::new(FVar(0));
        for _ in 0..64 {
            a = Arc::new(apps_rc(
                konst("+"),
                [
                    Arc::new(apps_rc(konst("*"), [a.clone(), Arc::new(lit(1))])),
                    a,
                ],
            ));
            b = Arc::new(apps_rc(
                konst("+"),
                [
                    Arc::new(apps_rc(konst("*"), [b.clone(), Arc::new(lit(1))])),
                    b,
                ],
            ));
        }
        assert!(*a == *b);
        let c = Arc::new(apps_rc(konst("+"), [a.clone(), Arc::new(lit(2))]));
        let d = Arc::new(apps_rc(konst("+"), [b.clone(), Arc::new(lit(3))]));
        assert!(*c != *d);
    }

    /// A number written with many `Succ`s (as `list_length` gives) is read
    /// as a numeral, so `Nat::div_nz` and `*` are computed at once instead of
    /// unfolding; an unknown sum stops at its first `Succ`.
    #[test]
    fn a_long_succ_chain_is_a_numeral() {
        tauto_parse::install();
        let mut k = kernel();
        let c = &mut k.core;
        let chain = (0..300).fold(konst("Zero"), |t, _| app(konst("Succ"), t));
        c.start_budget(None, None);
        let t = apps(
            konst("Nat::div_nz"),
            [apps(konst("*"), [chain, lit(8)]), lit(7), FVar(42)],
        );
        assert_eq!(c.whnf(&t), lit(342));
        assert!(c.end_budget().steps < 2000);
        c.start_budget(None, None);
        let open = Arc::new(apps(konst("+"), [FVar(0), lit(1_000_000)]));
        assert_eq!(c.top(|c| c.numeral(&open)).flatten(), None);
        assert!(c.end_budget().steps < 100);
    }

    /// The bound of loose variables computed with no table at all.
    fn loose_plain(t: &Tm) -> usize {
        match t {
            BVar(i) => i + 1,
            Pi(_, a, b) => loose_plain(a).max(loose_plain(b).saturating_sub(1)),
            Lam(_, b) => loose_plain(b).saturating_sub(1),
            App(f, a) => loose_plain(f).max(loose_plain(a)),
            _ => 0,
        }
    }

    #[test]
    fn the_memo_of_loose_agrees_with_the_plain_walk() {
        tauto_parse::install();
        let shared: R = Arc::new(app(BVar(3), BVar(0)));
        let terms = [
            lit(1),
            BVar(0),
            BVar(7),
            app(BVar(2), lit(4)),
            Lam(Hint::named("_"), Arc::new(app(BVar(0), BVar(4)))),
            Pi(Hint::named("_"), shared.clone(), shared.clone()),
            apps(
                Const(DeclRef::fresh("f")),
                [BVar(1), (*shared).clone(), BVar(5)],
            ),
        ];
        for t in terms {
            let r = Arc::new(t);
            // The first call fills the memo, the second reads it.
            assert_eq!(loose(&r), loose_plain(&r));
            assert_eq!(loose(&r), loose_plain(&r));
        }
        forget_loose();
    }

    #[test]
    fn the_address_hasher_keeps_every_key_apart() {
        tauto_parse::install();
        let mut m: HashMap<usize, usize, AddrBuild> = HashMap::default();
        for i in 0..10_000usize {
            m.insert(i * 16, i);
        }
        assert_eq!(m.len(), 10_000);
        for i in 0..10_000usize {
            assert_eq!(m.get(&(i * 16)), Some(&i));
        }
    }

    #[test]
    fn iota_shares_the_inductive_and_gives_the_same_term() {
        tauto_parse::install();
        let mut k = kernel();
        let c = &mut k.core;
        c.start_budget(None, None);
        let nat = c
            .inds
            .get(&DeclRef::primitive("Nat").unwrap())
            .unwrap()
            .clone();
        let before = Arc::strong_count(&nat);
        let t = apps(
            Const(
                DeclRef::primitive("Nat")
                    .unwrap()
                    .generated(tauto_surface::identity::Generation::Recursion),
            ),
            [
                Sort(Sort::ty(0)),
                lit(0),
                Lam(
                    Hint::named("_"),
                    Arc::new(Lam(
                        Hint::named("_"),
                        Arc::new(app(konst("Succ"), app(konst("Succ"), BVar(0)))),
                    )),
                ),
                lit(3),
            ],
        );
        let _ = c.whnf(&t);
        // The lookup of `iota` took no copy of the inductive that stays.
        assert_eq!(Arc::strong_count(&nat), before);
        c.end_budget();
    }

    #[test]
    fn a_passed_deadline_seen_by_a_loop_without_steps_ends_the_budget() {
        tauto_parse::install();
        let mut k = kernel();
        let c = &mut k.core;
        c.start_budget(None, Some(crate::clock::Instant::now()));
        let r: R = Arc::new(app(BVar(0), BVar(1)));
        for _ in 0..4096 {
            let _ = inst_tm(&r, 0, &Arc::new(lit(0)));
        }
        assert!(c.budget_out());
        assert!(c.end_budget().out);
        c.start_budget(None, None);
        for _ in 0..4096 {
            let _ = inst_tm(&r, 0, &Arc::new(lit(0)));
        }
        assert!(!c.budget_out());
        assert!(!c.end_budget().out);
    }

    fn accepts(src: &str) {
        let mut k = kernel();
        let (ty, body) = read(&mut k, src);
        k.core
            .add_decl(&Name::from("t"), &ty, Some(&body), false)
            .unwrap();
    }

    fn rejects(src: &str) {
        let mut k = kernel();
        let (ty, body) = read(&mut k, src);
        assert!(
            k.core
                .add_decl(&Name::from("t"), &ty, Some(&body), false)
                .is_err(),
            "{src}"
        );
    }

    #[test]
    fn proofs_are_checked() {
        tauto_parse::install();
        accepts(&r#"theorem t(A: Prop, a: A): A { a }"#.to_string());
        accepts(&r#"theorem t(): 2 + 2 = 4 { Refl(<A: Nat, a: 4>) }"#.to_string());
        accepts(
            &r#"theorem t(n: Nat): n + 2 = Succ(Succ(n)) { Refl(<A: Nat, a: Succ(Succ(n))>) }"#
                .to_string(),
        );
        rejects(&r#"theorem t(): 2 + 2 = 5 { Refl(<A: Nat, a: 4>) }"#.to_string());
        rejects(&r#"theorem t(A: Prop, B: Prop, a: A): B { a }"#.to_string());
        rejects(&r#"theorem t(): False { Trivial }"#.to_string());
        accepts(&r#"theorem t(): Nat::rec(k => Nat, 0, k => ih => Succ(Succ(ih)), 3) = 6 { Refl(<A: Nat, a: 6>) }"#.to_string());
        accepts(&r#"theorem t(e: Eq(Nat, 1, 1)): Eq::rec(<A: Nat, a: 1>, y => p => Nat, 7, 1, e) = 7 { Refl(<A: Nat, a: 7>) }"#.to_string());
    }

    #[test]
    fn a_false_equation_is_rejected_without_unfolding_twice() {
        tauto_parse::install();
        // `conv` compares the arguments of two applications of the same name
        // before unfolding it; remembering the pairs that failed keeps that
        // from being exponential.
        let mut k = kernel();
        let defs = parse_program(
            &r#"fn double(n: Nat): Nat { ⊢ Nat from match n { Zero => Zero
 Succ(m) => Succ(Succ(double(m))) } }
fn add2(a: Nat, b: Nat): Nat { ⊢ Nat from match a { Zero => b
 Succ(m) => Succ(add2(m, b)) } }"#
                .to_string(),
        )
        .unwrap();
        for e in k.declare(&defs, false) {
            assert!(!e.failed(), "{e:?}");
        }
        let (ty, body) = read(
            &mut k,
            &r#"theorem t(): double(20) = add2(23, 20) { Refl(<A: Nat, a: double(20)>) }"#
                .to_string(),
        );
        assert!(
            k.core
                .add_decl(&Name::from("t"), &ty, Some(&body), false)
                .is_err()
        );
    }

    /// The steps the core takes to check `theorem` after `defs`, and whether
    /// it accepted it. How many steps the core takes is its own business, so
    /// the sources are here.
    fn steps_for(defs: &str, theorem: &str) -> (u64, bool) {
        let mut k = kernel();
        let defs = parse_program(defs).unwrap();
        for e in k.declare(&defs, false) {
            assert!(!e.failed(), "{e:?}");
        }
        let (ty, body) = read(&mut k, theorem);
        k.core.start_budget(None, None);
        let ok = k
            .core
            .add_decl(&Name::from("t"), &ty, Some(&body), false)
            .is_ok();
        (k.core.end_budget().steps, ok)
    }

    #[test]
    fn a_redex_is_typed_without_computing() {
        tauto_parse::install();
        // The motive applied to a number in the statement is typed by its
        // argument and its body, not by computing `fib(24)`.
        let (steps, ok) = steps_for(
            r#"fn add2(a: Nat, b: Nat): Nat { ⊢ Nat from match a { Zero => b
 Succ(m) => Succ(add2(m, b)) } }
fn fib(n: Nat): Nat { ⊢ Nat from match n { Zero => 1
 Succ(m) => ⊢ Nat from match m { Zero => 1
 Succ(p) => add2(fib(m), fib(p)) } } }"#,
            r#"theorem t(): ((k) => fib(k))(24) = fib(24) { Refl(<A: Nat, a: fib(24)>) }"#,
        );
        assert!(ok);
        assert!(steps < 10_000, "{steps} steps");
    }

    #[test]
    fn a_deep_wrong_argument_is_rejected_in_linear_steps() {
        tauto_parse::install();
        // `big(big(r))` against `big(r)`: both reduce to a chain of 400
        // stuck `2 * pow2(…)`. The typed comparison goes down the chain after
        // the untyped one failed. Comparing copies would compare each link and
        // reduce again all of the chain below it, quadratic in its length.
        let defs = r#"fn pow2(n: Nat): Nat { ⊢ Nat from match n { Zero => 1
 Succ(k) => 2 * pow2(k) } }
fn big(s: Nat): Nat { pow2(s + 400) }
fn is_zero(n: Nat): Bool { ⊢ Bool from match n { Zero => true
 Succ(k) => false } }
fn pos(x: Nat): Prop { is_zero(x) = false }"#;
        let (steps, ok) = steps_for(
            defs,
            r#"theorem t(r: Nat, hb: (s: Nat) -> pos(big(s))): pos(big(r)) { hb(big(r)) }"#,
        );
        assert!(!ok);
        assert!(steps < 100_000, "{steps} steps");
        let (_, ok) = steps_for(
            defs,
            r#"theorem t(r: Nat, hb: (s: Nat) -> pos(big(s))): pos(big(r)) { hb(r) }"#,
        );
        assert!(ok);
    }

    #[test]
    fn an_argument_is_reduced_once() {
        tauto_parse::install();
        // `m(n)` is `mx(n, n)`, whose arms are its arguments: the arm taken
        // is the argument's own node, whose value was found when `nat_lt`
        // compared it, so thirty `m`s reduce each argument once.
        let (steps, ok) = steps_for(
            r#"fn mx(a: Nat, b: Nat): Nat { ⊢ Nat from match Nat::lt(a, b) { false => a
 true => b } }
fn m(n: Nat): Nat { mx(n, n) }"#,
            r#"theorem t(): m(m(m(m(m(m(m(m(m(m(m(m(m(m(m(m(m(m(m(m(m(m(m(m(m(m(m(m(m(m(20)))))))))))))))))))))))))))))) = 20 { Refl(<A: Nat, a: 20>) }"#,
        );
        assert!(ok);
        assert!(steps < 5_000, "{steps} steps");
        let (_, ok) = steps_for(
            r#"fn mx(a: Nat, b: Nat): Nat { ⊢ Nat from match Nat::lt(a, b) { false => a
 true => b } }
fn m(n: Nat): Nat { mx(n, n) }"#,
            r#"theorem t(): m(m(m(m(m(m(m(m(m(m(m(m(m(m(m(m(m(m(m(m(m(m(m(m(m(m(m(m(m(m(20)))))))))))))))))))))))))))))) = 21 { Refl(<A: Nat, a: 20>) }"#,
        );
        assert!(!ok);
    }

    #[test]
    fn a_wrong_number_is_rejected_by_its_value() {
        tauto_parse::install();
        // A number compared with a literal is computed once and compared as a
        // value; a wrong literal costs about what the right one does.
        let defs = r#"fn h(n: Nat): Nat { ⊢ Nat from match n { Zero => 123456789
 Succ(m) => Nat::rem_nz(Nat::sub(h(m), 7), 1000003, (e: Eq(Nat, 1000003, 0)) => Eq::subst((x: Nat) => ⊢ Prop from match x {
   Zero => False
   Succ(_) => True
 }, e, Trivial)) } }"#;
        let right = steps_for(
            defs,
            r#"theorem t(): h(30) = 456210 { Refl(<A: Nat, a: h(30)>) }"#,
        );
        let wrong = steps_for(
            defs,
            r#"theorem t(): h(30) = 456211 { Refl(<A: Nat, a: h(30)>) }"#,
        );
        assert!(right.1 && !wrong.1);
        assert!(
            wrong.0 <= 3 * right.0,
            "{} steps against {}",
            wrong.0,
            right.0
        );
    }

    #[test]
    fn a_table_forgets_the_nodes_that_are_gone() {
        tauto_parse::install();
        let mut m: NodeTable<()> = NodeTable::default();
        let kept = Arc::new(lit(0));
        m.insert(Arc::as_ptr(&kept) as usize, (Arc::downgrade(&kept), ()));
        let mut gone = Vec::new();
        while m.len() < 4096 {
            let n = Arc::new(lit(m.len() as u128));
            m.insert(Arc::as_ptr(&n) as usize, (Arc::downgrade(&n), ()));
            gone.push(n);
        }
        drop(gone);
        sweep(&mut m);
        assert_eq!(m.len(), 1);
    }

    #[test]
    fn a_table_that_kept_its_nodes_is_not_walked_again_until_it_doubles() {
        tauto_parse::install();
        let mut m: NodeTable<()> = NodeTable::default();
        let nodes: Vec<R> = (0..SWEEP_FROM).map(|i| Arc::new(lit(i as u128))).collect();
        for n in &nodes {
            m.insert(Arc::as_ptr(n) as usize, (Arc::downgrade(n), ()));
        }
        sweep(&mut m);
        assert_eq!(m.len(), SWEEP_FROM);
        assert_eq!(m.sweep_at, 2 * SWEEP_FROM);
        // Inserting again under a key it has (as `remember` does) walks nothing.
        m.insert(
            Arc::as_ptr(&nodes[0]) as usize,
            (Arc::downgrade(&nodes[0]), ()),
        );
        sweep(&mut m);
        assert_eq!(m.sweep_at, 2 * SWEEP_FROM);
    }

    #[test]
    fn names_are_read_by_their_binders() {
        tauto_parse::install();
        // A binder named like a sort is just a binder here: names are
        // resolved by their binders, not by their spelling. (A lone `_` is not
        // a name at all and does not parse.)
        rejects(&r#"theorem t(Type: Prop): Type { Nat }"#.to_string());
        rejects(
            &r#"theorem t(): ∀ x: Prop. ∀ y: Prop. ∀ h: y. x { a => b => h => h }"#.to_string(),
        );
    }

    #[test]
    fn a_redex_types_its_argument() {
        tauto_parse::install();
        // `(fun x => 0)(Ω)` with an ill-typed argument.
        rejects(
            &r#"theorem t(): Nat { (x => 0)(Trivial(Trivial)) }
"#
            .to_string(),
        );
        accepts(&r#"theorem t(): Nat { (x => 0)(Trivial) }"#.to_string());
    }

    /// A value that unfolds to its own name, at once or through another
    /// name's value, is refused by the core itself: `f := λn. Succ(f n)`
    /// would make `f 0 ≡ Succ(f 0)` hold by reflexivity. The named checker
    /// never sends one, so this goes to the core directly.
    #[test]
    fn values_that_unfold_to_themselves_are_refused() {
        tauto_parse::install();
        let mut k = kernel();
        let (ty, plain) = read(&mut k, "theorem plain(n: Nat): Nat { n }");
        let (fr, gr) = (DeclRef::fresh("f"), DeclRef::fresh("g"));
        k.source_alias("f", &fr);
        k.source_alias("g", &gr);
        let (f, g) = (Name::Global(fr), Name::Global(gr));
        k.core.add_decl(&f, &ty, None, false).unwrap();
        k.core.add_decl(&g, &ty, None, false).unwrap();
        let (_, own) = read(&mut k, "theorem own(n: Nat): Nat { Succ(f(n)) }");
        let err = k.core.set_value(&f, &own).unwrap_err();
        assert_eq!(err.id, "kernel-core-value-cycle", "{err:?}");
        // Through another name's value.
        let (_, via_f) = read(&mut k, "theorem via_f(n: Nat): Nat { f(n) }");
        let (_, via_g) = read(&mut k, "theorem via_g(n: Nat): Nat { Succ(g(n)) }");
        k.core.set_value(&g, &via_f).unwrap();
        let err = k.core.set_value(&f, &via_g).unwrap_err();
        assert_eq!(err.id, "kernel-core-value-cycle", "{err:?}");
        // A value that reaches other names but not its own is kept.
        k.core.set_value(&f, &plain).unwrap();
    }

    /// What a check for cycles found is not used once a name it reached
    /// changes: a name met without a value that is given one later, or a
    /// value taken and given again, is followed again.
    #[test]
    fn a_cycle_through_a_name_given_a_value_later_is_refused() {
        tauto_parse::install();
        let mut k = kernel();
        let (ty, _) = read(&mut k, "theorem plain(n: Nat): Nat { n }");
        let (fr, hr, jr) = (
            DeclRef::fresh("f"),
            DeclRef::fresh("h"),
            DeclRef::fresh("j"),
        );
        k.source_alias("f", &fr);
        k.source_alias("h", &hr);
        k.source_alias("j", &jr);
        let (f, h, j) = (Name::Global(fr), Name::Global(hr), Name::Global(jr));
        for n in [&f, &h, &j] {
            k.core.add_decl(n, &ty, None, false).unwrap();
        }
        // `h` reaches `f` while `f` has no value.
        let (_, via_f) = read(&mut k, "theorem via_f(n: Nat): Nat { Succ(f(n)) }");
        k.core.set_value(&h, &via_f).unwrap();
        // `j` reaches `h`, and so `f`, after that was found.
        let (_, via_h) = read(&mut k, "theorem via_h(n: Nat): Nat { h(n) }");
        k.core.set_value(&j, &via_h).unwrap();
        let (_, via_j) = read(&mut k, "theorem via_j(n: Nat): Nat { j(n) }");
        let err = k.core.set_value(&f, &via_j).unwrap_err();
        assert_eq!(err.id, "kernel-core-value-cycle", "{err:?}");
        // A value taken (`seal`) and given again is followed again.
        let (_, plain) = read(&mut k, "theorem plain2(n: Nat): Nat { n }");
        k.core.set_value(&f, &plain).unwrap();
        k.core.seal(&h).unwrap();
        let (_, via_j2) = read(&mut k, "theorem via_j2(n: Nat): Nat { Succ(j(n)) }");
        k.core.set_value(&h, &via_j2).unwrap_err();
    }

    /// The quotient's constants are declared once, in order, with the type
    /// the core gives them and no value.
    #[test]
    fn quotient_constants_are_fixed() {
        tauto_parse::install();
        let mut k = kernel();
        let (ty, body) = read(&mut k, "theorem t(n: Nat): Nat { n }");
        assert!(
            k.core
                .add_decl(&Name::from("Quot::lift"), &ty, None, false)
                .is_err()
        );
        assert!(k.core.set_value(&Name::from("Quot::lift"), &body).is_err());
        let mut fresh = Kernel::new();
        let (ty, _) = read(&mut fresh, "theorem t(A: Type): Type { A }");
        let err = fresh
            .core
            .add_decl(&Name::from("Quot::mk"), &ty, None, false)
            .unwrap_err();
        assert_eq!(err.id, "kernel-core-quot-declared-after", "{err:?}");
        let err = fresh
            .core
            .add_decl(&Name::from("Quot"), &ty, None, false)
            .unwrap_err();
        assert_eq!(err.id, "kernel-core-quot-type", "{err:?}");
        // `Quot::lift` is stated with `Eq`, which must be the equality.
        let eq = DeclRef::primitive("Eq").unwrap();
        assert!(kernel().core.is_equality(&eq));
        assert!(!Core::new().is_equality(&eq));
    }

    fn inductive(src: &str) -> Result<(), Message> {
        tauto_messages::install();
        let mut k = kernel();
        let mut p = parse_program(src).unwrap();
        k.resolve_statements(&mut p.stmts);
        let Stmt::Inductive(i) = &p.stmts[0] else {
            panic!()
        };
        let mut params = Vec::new();
        for (n, d) in &i.params {
            params.push((n.clone(), k.shape(d).unwrap()));
        }
        let sort = k.shape(&i.sort).unwrap();
        let mut walk = &sort;
        while let TermKind::Pi { result, .. } = &*walk.kind {
            walk = result;
        }
        let out = super::super::sort_of(walk).unwrap();
        let ctors = i
            .constructors
            .iter()
            .map(|c| {
                let args: Vec<(Name, T)> = c
                    .params
                    .iter()
                    .map(|(n, d)| (n.clone(), k.shape(d).unwrap()))
                    .collect();
                let ty = super::super::inductive::pi_all(
                    &params,
                    super::super::inductive::pi_all(&args, k.shape(&c.result).unwrap()),
                );
                (c.name.clone(), ty)
            })
            .collect();
        let spec = FamSpec {
            name: i.name.clone(),
            ty: super::super::inductive::pi_all(&params, sort),
            ctors,
        };
        k.core.add_inductive(&[spec], params.len(), out)
    }

    /// A part the typing read as an atom (`Core::lvals`) is convertible with
    /// its value, alone and at the head of an application, and an atom is not
    /// taken for another one.
    #[test]
    fn an_atom_with_a_value_is_convertible_with_its_value() {
        tauto_parse::install();
        let mut core = Core::new();
        let x = core.fresh(Sort(Sort::Prop));
        let y = core.fresh(Sort(Sort::Prop));
        let value = Lam(Hint(None), Arc::new(BVar(0)));
        core.lvals.insert(x, Arc::new(value.clone()));
        assert!(core.conv(&FVar(x), &value));
        assert!(core.conv(&value, &FVar(x)));
        let arg = Sort(Sort::Prop);
        assert!(core.conv(&app(FVar(x), arg.clone()), &arg));
        assert!(!core.conv(&FVar(x), &FVar(y)));
    }

    #[test]
    fn inductive_declarations_are_read_again() {
        tauto_parse::install();
        inductive(
            &r#"inductive L(A: Type): Type {
  Nil: L(A)
  Cons(h: A, t: L(A)): L(A)
}"#
            .to_string(),
        )
        .unwrap();
        inductive(
            &r#"inductive V(A: Type): (Nat) -> Type {
  Vnil: V(A, 0)
  Vcons(n: Nat, h: A, t: V(A, n)): V(A, Succ(n))
}"#
            .to_string(),
        )
        .unwrap();
        assert!(
            inductive(
                &r#"inductive I: Type1 {
  C(I: Type): I
}"#
                .to_string()
            )
            .is_err()
        );
        assert!(
            inductive(
                &r#"inductive L(A: Type): Type {
  Z(a: A): L(A)
  C(x: L(Nat)): L(A)
}"#
                .to_string()
            )
            .unwrap_err()
            .to_string()
            .contains("parameters")
        );
        assert!(
            inductive(
                &r#"inductive B: Type {
  Mk(f: (B) -> Nat): B
}"#
                .to_string()
            )
            .is_err()
        );
        assert!(
            inductive(
                &r#"inductive B: Type {
  Mk(f: Eq(Type, B, B)): B
}"#
                .to_string()
            )
            .is_err()
        );
        assert!(
            inductive(
                &r#"inductive U: Type {
  Mk(T: Type): U
}"#
                .to_string()
            )
            .is_err()
        );
        assert!(
            inductive(
                &r#"inductive O: Type {
  Mk: Nat
}"#
                .to_string()
            )
            .is_err()
        );
    }
}

impl Core {
    fn reserve_eliminator(&mut self, family: &DeclRef, sort: &Elimination) -> DeclRef {
        let key = (family.clone(), sort.clone());
        if let Some(reference) = self.eliminators.get(&key) {
            return reference.clone();
        }
        let reference = match sort {
            Elimination::Induction => self.names.generated(
                &Name::from(family.clone()),
                tauto_surface::identity::Generation::Induction,
            ),
            Elimination::Recursion => self.names.generated(
                &Name::from(family.clone()),
                tauto_surface::identity::Generation::Recursion,
            ),
            Elimination::At(level) => DeclRef::fresh(format!("{family}::rec@{level}")),
        };
        self.eliminators.insert(key, reference.clone());
        reference
    }

    /// Specialize the motive universe of an already validated large eliminator.
    /// Its parameters, indices and reduction rule are unchanged.
    pub(super) fn recursor_at(&mut self, family: &Name, level: &super::Level) -> Res<()> {
        #[cfg(feature = "selfhost")]
        let result = self.timed(|c| c.recursor_at_inner(family, level));
        #[cfg(not(feature = "selfhost"))]
        let result = self.recursor_at_inner(family, level);
        self.shared.clear();
        self.defs.clear();
        #[cfg(feature = "selfhost")]
        self.record(Some(format!("R {family} {level}")), result.is_ok());
        result
    }

    pub(super) fn specialized_recursor(&self, family: &Name, level: &super::Level) -> Option<Name> {
        let family = self.names.reference(family)?;
        let reference = self
            .eliminators
            .get(&(family.clone(), Elimination::At(level.clone())))?;
        self.recs
            .contains_key(reference)
            .then(|| Name::from(reference.clone()))
    }

    fn recursor_at_inner(&mut self, family: &Name, level: &super::Level) -> Res<()> {
        if level.floor() > 65535 {
            return fail(msg!("kernel-core-recursor-universe"));
        }
        let info = self
            .names
            .reference(family)
            .and_then(|id| self.inds.get(id))
            .cloned()
            .ok_or_else(|| msg!("kernel-core-unknown-family"))?;
        let mut pending = Vec::new();
        for member in &info.group {
            let original = self
                .eliminators
                .get(&(member.clone(), Elimination::Recursion))
                .cloned()
                .ok_or_else(|| msg!("kernel-core-missing-recursor"))?;
            if self.recs.get(&original) != Some(member) {
                return fail(msg!("kernel-core-no-large-elimination"));
            }
            let name = self.reserve_eliminator(member, &Elimination::At(level.clone()));
            if self.recs.contains_key(&name) {
                continue;
            }
            self.fresh_name(&Name::from(name.clone()))?;
            let ty = self
                .globals
                .get(&original)
                .ok_or_else(|| msg!("kernel-core-missing-recursor"))?
                .ty
                .clone();
            fn change(t: &Tm, skip: usize, count: usize, level: &super::Level) -> Res<Tm> {
                if count == 0 {
                    return Ok(t.clone());
                }
                let Pi(h, dom, cod) = t else {
                    return fail(msg!("kernel-core-invalid-telescope"));
                };
                if skip > 0 {
                    return Ok(Pi(
                        h.clone(),
                        dom.clone(),
                        Arc::new(change(cod, skip - 1, count, level)?),
                    ));
                }
                fn result_sort(t: &Tm, level: &super::Level) -> Res<Tm> {
                    match t {
                        Pi(h, a, b) => {
                            Ok(Pi(h.clone(), a.clone(), Arc::new(result_sort(b, level)?)))
                        }
                        Sort(super::Sort::Type(_)) => Ok(Sort(super::Sort::Type(level.clone()))),
                        _ => fail(msg!("kernel-core-invalid-motive")),
                    }
                }
                Ok(Pi(
                    h.clone(),
                    Arc::new(result_sort(dom, level)?),
                    Arc::new(change(cod, 0, count - 1, level)?),
                ))
            }
            let ty = change(&ty, info.params, info.group.len(), level)?;
            self.infer_sort(&ty)?;
            pending.push((name, member.clone(), ty));
        }
        let targets: Vec<_> = info
            .group
            .iter()
            .map(|member| {
                self.eliminators
                    .get(&(member.clone(), Elimination::At(level.clone())))
                    .cloned()
                    .ok_or_else(|| msg!("kernel-core-missing-recursor"))
            })
            .collect::<Res<_>>()?;
        for name in &targets {
            self.rec_targets.insert(name.clone(), targets.clone());
        }
        for (name, member, ty) in pending {
            self.touch(&name);
            self.globals
                .insert(name.clone(), Global { ty, value: None });
            self.recs.insert(name, member);
        }
        Ok(())
    }
}
