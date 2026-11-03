//! The core kernel: every declaration the named checker accepts is checked
//! again here, over locally nameless terms, before it is added. The one
//! exception is a theorem's proof found in the proof cache (`cache.rs`, keyed
//! by the checker's source, the proof text and the interfaces of what it
//! names), which is taken as checked; `TAUTO_CACHE=off` checks everything.
//!
//! The named checker (`check.rs`) works on the surface AST, where a name may
//! mean a local, a sort or a global, and it renames binders to keep them
//! apart; a mistake in that renaming would be a way to prove `False`.
//! This module reads the elaborated term once, resolving every name by its
//! binder (bound variables become de Bruijn indices, the variables of a
//! context fresh atoms), and checks it independently of local binder names.
//! Global names identify constants; binder hints are only for display. It has
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

use std::collections::{HashMap, HashSet};
use std::rc::{Rc, Weak};

use super::derivation::{Derivation, InferenceRule};
use super::{Ctx, Sort, T, sort_named, sort_term};
use crate::surface::TermKind;
use tauto_message::{Message, msg};

type R = Rc<Tm>;

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(super) enum Tm {
    /// A variable bound by an enclosing `Pi` or `Lam`, counted outwards.
    BVar(usize),
    /// A variable of the context (an atom).
    FVar(u64),
    Sort(Sort),
    Const(Rc<str>),
    /// The binder's name is only shown (see [`Hint`]).
    Pi(Hint, R, R),
    Lam(Hint, R),
    App(R, R),
    Lit(u128),
}

/// The name a binder was written with: shown when a term is written back
/// as a named one, and nothing else. Two terms that differ only in their
/// hints are the same term.
#[derive(Debug, Clone)]
pub(super) struct Hint(Option<Rc<str>>);

impl Hint {
    fn none() -> Self {
        Hint(None)
    }

    fn named(n: &str) -> Self {
        Hint((n != "_").then(|| n.into()))
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
            static LEAF: R = Rc::new(Lit(0));
        }
        // The parts of an application this drop would free: those no other
        // term shares. A shared part only loses a count.
        fn take(t: &mut Tm, next: &mut Vec<R>) {
            if let App(f, a) = t {
                for r in [f, a] {
                    // While the thread is ending, the drop is the compiler's.
                    if Rc::strong_count(r) == 1
                        && matches!(**r, App(..))
                        && let Ok(leaf) = LEAF.try_with(Rc::clone)
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
            if let Ok(mut t) = Rc::try_unwrap(r) {
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
    App(Rc::new(f), Rc::new(a))
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

/// `x op y` on two numerals, or `None` past `u128`.
fn lit_op(op: &str, x: u128, y: u128) -> Option<u128> {
    match op {
        "+" => x.checked_add(y),
        "*" => x.checked_mul(y),
        _ => Some(x.saturating_sub(y)),
    }
}

fn konst(n: &str) -> Tm {
    Const(n.into())
}

/// `t` with the variable bound at depth `d` replaced by the locally closed `v`.
/// Indices inside `v` refer only to its own binders, so no shifting is needed.
/// A part that does not change is shared with `t`, not copied.
fn inst_at(t: &Tm, d: usize, v: &Tm) -> Tm {
    inst_at_rc(t, d, &Rc::new(v.clone()))
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
        _ => None,
    }
}

fn inst_rc(t: &R, d: usize, v: &R) -> Option<R> {
    match &**t {
        BVar(i) if *i == d => Some(v.clone()),
        BVar(_) => inst_tm(t, d, v).map(Rc::new),
        Pi(..) | Lam(..) | App(..) if loose(t) <= d => None,
        _ => inst_tm(t, d, v).map(Rc::new),
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

/// A hasher for the tables keyed by a node's address (a `usize`). Only
/// `HashMap` lookups use it: a table's answers do not depend on how its keys
/// are hashed (the hash only chooses where a key is stored, and equal keys
/// always hash alike), so swapping the hasher changes how fast the table is,
/// never what it holds or returns. It multiplies the key by an odd constant
/// and folds the well-mixed high bits of the product into the low ones;
/// addresses are aligned, so their low bits alone would collide.
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
    let key = Rc::as_ptr(t) as *const () as usize;
    if let Some(n) = LOOSE.with(|m| m.borrow().get(&key).map(|e| e.1)) {
        return n;
    }
    poll_deadline();
    let n = match &**t {
        BVar(i) => i + 1,
        Pi(_, a, b) => loose(a).max(loose(b).saturating_sub(1)),
        Lam(_, b) => loose(b).saturating_sub(1),
        App(f, a) => loose(f).max(loose(a)),
        _ => 0,
    };
    LOOSE.with(|m| {
        let mut m = m.borrow_mut();
        m.insert(key, (Rc::downgrade(t), n));
        sweep(&mut m);
    });
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
        _ => None,
    }
}

fn abstract_rc(t: &R, d: usize, x: u64) -> Option<R> {
    abstract_tm(t, d, x).map(Rc::new)
}

/// `Pi (x: dom). body`, with the atom `x` of `body` bound.
fn pi_over(x: u64, dom: Tm, body: &Tm) -> Tm {
    Pi(Hint::none(), Rc::new(dom), Rc::new(abstract_at(body, 0, x)))
}

fn lam_over(x: u64, body: &Tm) -> Tm {
    Lam(Hint::none(), Rc::new(abstract_at(body, 0, x)))
}

fn has_loose(t: &Tm, d: usize) -> bool {
    match t {
        BVar(i) => *i >= d,
        Pi(_, a, b) => has_loose(a, d) || has_loose(b, d + 1),
        Lam(_, b) => has_loose(b, d + 1),
        App(f, a) => has_loose(f, d) || has_loose(a, d),
        _ => false,
    }
}

fn mentions_const(t: &Tm, names: &[Rc<str>]) -> bool {
    match t {
        Const(c) => names.contains(c),
        Pi(_, a, b) => mentions_const(a, names) || mentions_const(b, names),
        Lam(_, b) => mentions_const(b, names),
        App(f, a) => mentions_const(f, names) || mentions_const(a, names),
        _ => false,
    }
}

fn mentions_fvar(t: &Tm) -> bool {
    match t {
        FVar(_) => true,
        Pi(_, a, b) => mentions_fvar(a) || mentions_fvar(b),
        Lam(_, b) => mentions_fvar(b),
        App(f, a) => mentions_fvar(f) || mentions_fvar(a),
        _ => false,
    }
}

/// The numeral from which `Core::offset_view` takes `x + n` off at once.
const LARGE_OFFSET: u128 = 1 << 12;

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
        if let Some(h) = seen.get(&Rc::as_ptr(r)) {
            return *h;
        }
        let h = tree_hash(r, seen);
        seen.insert(Rc::as_ptr(r), h);
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
        return Const("…".into());
    }
    *budget -= 1;
    match t {
        App(f, a) => {
            let f = pruned(f, budget);
            App(Rc::new(f), Rc::new(pruned(a, budget)))
        }
        Pi(h, d, r) => {
            let d = pruned(d, budget);
            Pi(h.clone(), Rc::new(d), Rc::new(pruned(r, budget)))
        }
        Lam(h, b) => Lam(h.clone(), Rc::new(pruned(b, budget))),
        t => t.clone(),
    }
}

/// A numeral `k + 1` as `Succ(k)`, and `0` as `Zero`, to set beside a term
/// written with the constructors.
fn unfold_lit(t: Tm) -> Tm {
    match t {
        Lit(0) => Const("Zero".into()),
        Lit(k) => App(Rc::new(Const("Succ".into())), Rc::new(Lit(k - 1))),
        t => t,
    }
}

/// `f` applied to `args`; `f` itself, the same node, when there are none.
fn apps_node(f: R, args: impl IntoIterator<Item = R>) -> R {
    args.into_iter().fold(f, |f, a| Rc::new(App(f, a)))
}

fn apps_rc(f: Tm, args: impl IntoIterator<Item = R>) -> Tm {
    args.into_iter().fold(f, |f, a| App(Rc::new(f), a))
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
    index: HashMap<Rc<str>, usize>,
    low: HashMap<Rc<str>, usize>,
    stack: Vec<Rc<str>>,
    on: HashSet<Rc<str>>,
    uses: HashMap<Rc<str>, Vec<Rc<str>>>,
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
    name: Rc<str>,
    nargs: usize,
    recs: Vec<RecArg>,
}

#[derive(Debug, Clone)]
struct IndInfo {
    params: usize,
    indices: usize,
    group: Vec<Rc<str>>,
    pos: usize,
    ctors: Vec<CtorInfo>,
    /// A nested member stands for `J(args)`; its constructors are `J`'s.
    alias: Option<(Rc<str>, Vec<Tm>)>,
    /// The result indices of the only constructor, over the parameters,
    /// for the reduction of a proof of an `Eq`-like proposition.
    k_like: Option<Vec<Tm>>,
}

pub(super) type Declared<'a> = &'a dyn Fn(&str) -> Option<T>;

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
    opaque: Vec<(u64, T)>,
    /// The names the binders entered while typing are shown under.
    named: Vec<(u64, String)>,
    /// The types of the names the named checker has declared and the core
    /// has not (yet): each such name is an atom of that type.
    outer: Option<Declared<'a>>,
    declared: Vec<(String, u64)>,
    next: u64,
}

impl<'a> Open<'a> {
    fn new(ctx: &'a Ctx) -> Self {
        Open {
            ctx,
            atoms: vec![None; ctx.len()],
            visible: ctx.len(),
            types: Vec::new(),
            opaque: Vec::new(),
            named: Vec::new(),
            outer: None,
            declared: Vec::new(),
            next: u64::MAX,
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
    last_unfold: Option<Rc<str>>,
    unfolds: HashMap<Rc<str>, u64>,
    /// The first sum or product of two numerals past `u128` met, which is
    /// left as it is ([`Core::past_u128`]).
    past_u128: Option<String>,
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
    /// A sum or product of two numerals past `u128` that was left as it is.
    pub past_u128: Option<String>,
}

#[derive(Clone)]
pub(super) struct Core {
    globals: HashMap<Rc<str>, Global>,
    /// Behind `Rc` so that [`Core::iota`], which looks one up at every
    /// eliminator step, shares it instead of copying its constructors.
    inds: HashMap<Rc<str>, Rc<IndInfo>>,
    /// Constructor → (family it builds, place among its constructors).
    ctors: HashMap<Rc<str>, (Rc<str>, usize)>,
    /// Eliminator → (family, whether it is `_rec`).
    recs: HashMap<Rc<str>, Rc<str>>,
    /// The quotient's constants declared so far, each without a value and
    /// with the type [`quot_type`] gives it (`Core::quot_iota`).
    quot: HashSet<Rc<str>>,
    lctx: HashMap<u64, Tm>,
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
    conv_unfolded: Vec<(Rc<str>, usize)>,
    /// The height and recursion of each name with a value, found when first
    /// asked for (`Core::def`).
    defs: HashMap<Rc<str>, Def>,
    /// How much reduction the declaration in hand has done, and whether it ran
    /// out of time (`Kernel::set_timeout`).
    budget: Budget,
    /// What nodes reduced to, for the declaration in hand (`whnf_shared`).
    shared: NodeTable<Tm>,
    /// `Nat::eq`, `Nat::lt`, `Nat::div_nz` and `Nat::rem_nz` are unfolded, not computed
    /// (a test compares the two).
    numeric_off: bool,
    /// While [`Core::whnf_lazy`] reduces: an eliminator whose major premise
    /// is a constructor only once names are unfolded is left as it is.
    lazy_iota: bool,
    /// While a question of the named checker is typed: where the typing is
    /// (`at`), the binders entered on the way (`bound`), and the holes met.
    track: Option<Track>,
    derivation: Option<Vec<Vec<RawDerivation>>>,
    /// The level variables of the universe template being checked once for
    /// every level (`check/universe.rs`): `Type(u + 1)` reads as a sort only
    /// over these, and no declaration outside that check sees one.
    pub(super) level_vars: Vec<String>,
    #[cfg(feature = "selfhost")]
    replay: Option<Vec<(String, bool)>>,
    #[cfg(feature = "selfhost")]
    replay_skipped: usize,
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
    pub bound: Vec<(String, T)>,
}

/// Where a term does not type, written back: the path to the subterm (see
/// [`Track`]), the binders entered on the way, and why.
pub(super) struct Failure {
    pub why: Failed,
    pub at: Vec<u8>,
    pub bound: Vec<(String, T)>,
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
    pub name: String,
    pub ty: T,
    pub ctors: Vec<(String, T)>,
}

/// The quotient: `Quot(A, r)`, `quot_mk(A, r, a)`, and the two ways out of
/// it, `Quot_lift` (into any `B: Type`, given that `f` takes related values
/// to equal ones) and `Quot::ind` (into a proposition). Each is a constant
/// without a value; `Core::quot_iota` is their computation. Reading
/// `Quot(A, r)` as `A`, `quot_mk` as the identity and both ways out as
/// application turns every rule here into rules the core already has, so
/// they prove nothing the core without them does not.
const QUOT: &[&str] = &["Quot", "Quot::mk", "Quot::lift", "Quot::ind"];

/// The type each constant of [`QUOT`] must be declared with.
fn quot_type(name: &str) -> Option<Tm> {
    let ty = || Rc::new(Sort(Sort::ty(0)));
    let prop = || Rc::new(Sort(Sort::Prop));
    let pi = |a: Tm, b: Tm| Pi(Hint::none(), Rc::new(a), Rc::new(b));
    let v = BVar;
    // `(A, A) -> Prop` where `A` is the variable `a`.
    let rel = |a: usize| pi(v(a), Pi(Hint::none(), Rc::new(v(a + 1)), prop()));
    let quot = |a: usize, r: usize| apps(konst("Quot"), [v(a), v(r)]);
    let over_a_r = |rest: Tm| Pi(Hint::none(), ty(), Rc::new(pi(rel(0), rest)));
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
            Rc::new(pi(
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
            Pi(Hint::none(), Rc::new(quot(1, 0)), prop()),
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
            globals: HashMap::new(),
            inds: HashMap::new(),
            ctors: HashMap::new(),
            recs: HashMap::new(),
            quot: HashSet::new(),
            lctx: HashMap::new(),
            next: 0,
            conv_no: HashSet::new(),
            conv_fail: HashMap::new(),
            conv_depth: 0,
            conv_binders: 0,
            conv_unfolded: Vec::new(),
            defs: HashMap::new(),
            budget: Budget::default(),
            shared: NodeTable::default(),
            numeric_off: false,
            lazy_iota: false,
            track: None,
            derivation: None,
            level_vars: Vec::new(),
            #[cfg(feature = "selfhost")]
            replay: None,
            #[cfg(feature = "selfhost")]
            replay_skipped: 0,
        };
        let nat = konst("Nat");
        let binary = Pi(
            Hint::none(),
            Rc::new(nat.clone()),
            Rc::new(Pi(Hint::none(), Rc::new(nat.clone()), Rc::new(nat))),
        );
        for op in ["+", "*", "-"] {
            c.globals.insert(
                op.into(),
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
        name: &str,
        ty: &T,
        value: Option<&T>,
        transparent: bool,
    ) -> Res<()> {
        let input = self
            .replay
            .as_ref()
            .and_then(|_| selfhost::encode_decl(self, name, ty, value, transparent));
        let result = self.add_decl_inner(name, ty, value, transparent);
        self.record(input, result.is_ok());
        result
    }

    #[cfg(feature = "selfhost")]
    pub(super) fn add_constant(&mut self, name: &str, value: &T) -> Res<()> {
        let input = self.replay.as_ref().and_then(|_| {
            self.read(value)
                .ok()
                .map(|v| format!("C {name} {}", selfhost::term(&v)))
        });
        let result = self.add_constant_inner(name, value);
        self.record(input, result.is_ok());
        result
    }

    #[cfg(feature = "selfhost")]
    pub(super) fn set_value(&mut self, name: &str, value: &T) -> Res<()> {
        let input = self.replay.as_ref().and_then(|_| {
            self.read(value)
                .ok()
                .map(|v| format!("V {name} {}", selfhost::term(&v)))
        });
        let result = self.set_value_inner(name, value);
        self.record(input, result.is_ok());
        result
    }

    #[cfg(feature = "selfhost")]
    pub(super) fn add_inductive(&mut self, fams: &[FamSpec], np: usize, out: Sort) -> Res<()> {
        let input = self
            .replay
            .as_ref()
            .and_then(|_| selfhost::encode_inductive(self, fams, np, &out));
        let result = self.add_inductive_inner(fams, np, out);
        self.record(input, result.is_ok());
        result
    }

    #[cfg(not(feature = "selfhost"))]
    pub(super) fn add_decl(
        &mut self,
        name: &str,
        ty: &T,
        value: Option<&T>,
        transparent: bool,
    ) -> Res<()> {
        self.add_decl_inner(name, ty, value, transparent)
    }

    #[cfg(not(feature = "selfhost"))]
    pub(super) fn add_constant(&mut self, name: &str, value: &T) -> Res<()> {
        self.add_constant_inner(name, value)
    }

    #[cfg(not(feature = "selfhost"))]
    pub(super) fn set_value(&mut self, name: &str, value: &T) -> Res<()> {
        self.set_value_inner(name, value)
    }

    /// Stops a name from unfolding: an `opaque fn`, once its equation is
    /// checked. Only conversions are lost, so nothing checks that did not
    /// check with the name unfolding. The self-hosted checker does not read
    /// it, and the trace counts it as skipped.
    pub(super) fn seal(&mut self, name: &str) -> Res<()> {
        let result = match self.globals.get_mut(name) {
            Some(g) => {
                g.value = None;
                self.shared.clear();
                self.defs.clear();
                Ok(())
            }
            None => fail(msg!("kernel-core-not-defined", name = name)),
        };
        #[cfg(feature = "selfhost")]
        self.record(None, result.is_ok());
        result
    }

    /// Stops a name declared just now from unfolding: a theorem. Nothing
    /// has unfolded it yet, so the caches stay. Only conversions are lost.
    pub(super) fn seal_fresh(&mut self, name: &str) {
        if let Some(g) = self.globals.get_mut(name) {
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
        if !matches!(&*function.kind, TermKind::Var(n) if n == "Type") || arguments.len() != 1 {
            return None;
        }
        let l = super::level_of(&arguments[0])?;
        let bound = l
            .variables()
            .all(|v| self.level_vars.iter().any(|b| b == v));
        (l.as_const().is_none() && bound).then_some(Sort::Type(l))
    }

    /// [`T::last_argument_spine`], stopping at a sort over level variables.
    fn sort_spine<'t>(&self, t: &'t T) -> (Vec<&'t T>, &'t T) {
        let mut spine = Vec::new();
        let mut t = t;
        while let TermKind::App { arguments, .. } = &*t.kind
            && let Some(last) = arguments.last()
            && self.level_sort(t).is_none()
        {
            spine.push(t);
            t = last;
        }
        (spine, t)
    }

    /// `t` read with `scope`, the names bound so far (innermost last). With
    /// `open`, a question of the named checker: its context's names are
    /// atoms, and what the core cannot read is an atom of no type.
    fn read_in(&self, t: &T, scope: &mut Vec<String>, mut open: Option<&mut Open<'_>>) -> Res<Tm> {
        let opaque = |open: Option<&mut Open<'_>>, why: Message| match open {
            Some(o) => Ok(o.opaque(t)),
            None => Err(why),
        };
        if let Some(s) = self.level_sort(t) {
            return Ok(Sort(s));
        }
        Ok(match &*t.kind {
            TermKind::Var(n) => {
                if n == "_" {
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
                } else if self.globals.contains_key(n.as_str()) {
                    Const(n.as_str().into())
                } else if let Some(o) = open.as_deref_mut()
                    && let Some(x) = self.declared(o, n)
                {
                    FVar(x)
                } else {
                    return opaque(open, msg!("kernel-core-not-defined", name = n));
                }
            }
            TermKind::Nat(n) => match n.parse::<u128>() {
                Ok(k) => Lit(k),
                Err(_) => return opaque(open, msg!("kernel-core-numeral-too-large", numeral = n)),
            },
            // `false` and `true` are the constructors of the prelude's `Bool`.
            TermKind::Bool(b) => konst(if *b { "true" } else { "false" }),
            TermKind::App { .. } => {
                // In a loop along the last arguments (`last_argument_spine`),
                // reading the parts in the order the recursion would. A sort
                // over level variables is one part, not an application.
                let (spine, under) = self.sort_spine(t);
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
                    _ if self.level_sort(under).is_some() => {
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
                    acc = Pi(h, Rc::new(d), Rc::new(acc));
                }
                acc
            }
            TermKind::Lam { params, body, .. } => {
                let depth = scope.len();
                scope.extend(params.iter().cloned());
                let mut acc = self.read_in(body, scope, open)?;
                scope.truncate(depth);
                for n in params.iter().rev() {
                    acc = Lam(Hint::named(n), Rc::new(acc));
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
                if let Some((p, k)) = c.offset_view(&Rc::new(x.clone()))
                    && let Some((q, j)) = c.offset_view(&Rc::new(y.clone()))
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
        ctx: &[(String, T)],
        t: &T,
    ) -> Option<super::derivation::ProofReduction> {
        self.start_budget(Some(4096), None);
        let normal = self.nf_in(&ctx.to_vec(), t);
        let mut unfolded: Vec<String> = self.budget.unfolds.keys().map(|n| n.to_string()).collect();
        unfolded.sort();
        let spent = self.end_budget();
        (!spent.out).then_some(super::derivation::ProofReduction { normal, unfolded })
    }

    fn nf(&mut self, t: &Tm) -> Tm {
        let w = self.whnf(t);
        match &w {
            Pi(h, a, b) => Pi(h.clone(), Rc::new(self.nf(a)), Rc::new(self.nf(b))),
            Lam(h, b) => Lam(h.clone(), Rc::new(self.nf(b))),
            App(f, x) => App(Rc::new(self.nf(f)), Rc::new(self.nf(x))),
            _ => w,
        }
    }

    fn whnf(&mut self, t: &Tm) -> Tm {
        self.whnf_with(t, true)
    }

    /// `t` reduced at its head; a name with a value is unfolded only when
    /// `delta`.
    fn whnf_with(&mut self, t: &Tm, delta: bool) -> Tm {
        self.whnf_node(Rc::new(t.clone()), delta)
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
        let lazy = delta && std::mem::replace(&mut self.lazy_iota, false);
        let mut became: Vec<R> = Vec::new();
        let t = self.whnf_steps(t, delta, &mut became);
        if lazy {
            self.lazy_iota = true;
        }
        if delta && !self.budget.out {
            for n in became {
                self.remember(n, t.clone());
            }
        }
        t
    }

    /// Keeps `w`, the weak head normal form of `n`, for as long as `n` is
    /// used somewhere. The entry holds `n` weakly: while the entry is there,
    /// `n`'s allocation is not freed and its address not reused, so an entry
    /// is only ever found by `n` itself. The entries of nodes that are gone
    /// are dropped as the table grows, with what they reduced to.
    fn remember(&mut self, n: R, w: Tm) {
        poll_deadline();
        let key = Rc::as_ptr(&n) as usize;
        self.shared.insert(key, (Rc::downgrade(&n), w));
        sweep(&mut self.shared);
    }

    fn recall(&self, n: &R) -> Option<Tm> {
        self.shared
            .get(&(Rc::as_ptr(n) as usize))
            .map(|e| e.1.clone())
    }

    fn whnf_steps(&mut self, mut t: R, delta: bool, became: &mut Vec<R>) -> Tm {
        // A head just replaced is in weak head normal form: the next step is
        // one of reduction, so a head is never replaced twice in a row.
        let mut recalled = false;
        loop {
            if self.spend() {
                return (*t).clone();
            }
            // What a node was found to reduce to is a reduct of it with
            // or without `delta`; only with `delta` is what is found kept, as
            // the weak head normal form that unfolds every name.
            if Rc::weak_count(&t) > 0
                && let Some(w) = self.recall(&t)
            {
                return w;
            }
            // A node only this loop holds cannot be met again.
            if delta && Rc::strong_count(&t) > 1 {
                became.push(t.clone());
            }
            // A shared head reduced before goes on as what it became:
            // the same reduction, its first steps not taken again.
            if !recalled && let Some(next) = self.recalled_head(&t) {
                t = Rc::new(next);
                recalled = true;
                continue;
            }
            recalled = false;
            let (head, args) = spine_rc(&t);
            match head {
                Lam(_, body) if !args.is_empty() => {
                    // `inst_rc` gives the argument itself for a body that is
                    // its variable, so that node is still the one met again.
                    let body = inst_rc(body, 0, &args[0]).unwrap_or_else(|| body.clone());
                    t = apps_node(body, args.into_iter().skip(1));
                }
                Const(c) => {
                    // A shortcut for unfolding the name, so only with `delta`:
                    // without it, the arguments are not reduced either.
                    if delta && let Some(next) = self.numeric(c, &args) {
                        t = Rc::new(next);
                        continue;
                    }
                    if let Some(v) = self.globals.get(c).and_then(|g| g.value.clone()) {
                        if !delta {
                            return Self::stopped(t, became);
                        }
                        *self.budget.unfolds.entry(c.clone()).or_default() += 1;
                        self.budget.last_unfold = Some(c.clone());
                        t = apps_node(v, args);
                        continue;
                    }
                    let c = c.clone();
                    if matches!(&*c, "+" | "*" | "-")
                        && let Some(next) = self.arith(&c, &args)
                    {
                        t = Rc::new(next);
                        continue;
                    }
                    if self.recs.contains_key(&c)
                        && let Some(next) = self.iota(&c, &args)
                    {
                        t = next;
                        continue;
                    }
                    if self.quot.contains(&c)
                        && let Some(next) = self.quot_iota(&c, &args)
                    {
                        t = next;
                        continue;
                    }
                    return Self::stopped(t, became);
                }
                _ => return Self::stopped(t, became),
            }
        }
    }

    /// `t` with the functions at its head applied to their arguments, and
    /// nothing else reduced: a prefix of [`Core::whnf`].
    fn beta_head(&mut self, t: &Tm) -> Tm {
        let mut t = t.clone();
        loop {
            if self.spend() {
                return t;
            }
            let (head, args) = spine_rc(&t);
            let Lam(_, body) = head else { return t };
            if args.is_empty() {
                return t;
            }
            let body = inst_at_rc(body, 0, &args[0]);
            t = apps_rc(body, args.into_iter().skip(1));
        }
    }

    /// `t`, where reduction stopped. It reduces to itself, which is not
    /// kept: a node is kept only with what it became by taking steps.
    fn stopped(t: R, became: &mut Vec<R>) -> Tm {
        if became.last().is_some_and(|b| Rc::ptr_eq(b, &t)) {
            became.pop();
        }
        (*t).clone()
    }

    /// `t` with its head replaced by what it was found to reduce to, when a
    /// shared node of its spine below `t` itself was reduced before.
    fn recalled_head(&self, t: &R) -> Option<Tm> {
        let mut node = t;
        let mut args: Vec<R> = Vec::new();
        while let App(f, a) = &**node {
            args.push(a.clone());
            node = f;
            if Rc::weak_count(node) > 0
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
        let lazy = std::mem::replace(&mut self.lazy_iota, false);
        let w = self.whnf_node(t.clone(), true);
        self.lazy_iota = lazy;
        w
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
        self.shared.clear();
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
            past_u128: b.past_u128,
        }
    }

    /// `t` reduced, except that `+`, `*` and `-` are only computed on
    /// numerals: reducing them otherwise can go as deep as their number
    /// (`a * b` past `u128` unfolds `b` times), and the steps of [`Self::arith`]
    /// take them one at a time instead.
    fn literal_or_whnf(&mut self, t: &R) -> Tm {
        let (head, args) = spine_rc(t);
        if let Const(c) = head
            && matches!(&**c, "+" | "*" | "-")
        {
            if let [x, y] = args.as_slice()
                && let (Some(x), Some(y)) = (self.number(x), self.number(y))
            {
                match lit_op(c, x, y) {
                    Some(n) => return Lit(n),
                    None => self.past_u128(c, x, y),
                }
            }
            return (**t).clone();
        }
        self.whnf_shared(t)
    }

    /// The number `t` is when [`Core::literal_or_whnf`] gives a numeral, or a
    /// numeral written with a few constructors (`Succ(Zero)`).
    fn number(&mut self, t: &R) -> Option<u128> {
        match self.literal_or_whnf(t) {
            Lit(x) => Some(x),
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
    /// (a sum or product past `u128` is left to them). Otherwise the second
    /// operand must be `Zero` or `Succ(k)` (a numeral reads as one); when it
    /// is not, the term stays as it is.
    fn arith(&mut self, op: &str, args: &[R]) -> Option<Tm> {
        if args.len() < 2 {
            return None;
        }
        let b = self.whnf_shared(&args[1]);
        let rest = args[2..].iter().cloned();
        let mut a = (*args[0]).clone();
        if let Lit(y) = b {
            // Reduced once here, so that the steps below do not reduce it again.
            a = self.literal_or_whnf(&args[0]);
            let x = match &a {
                Lit(x) => Some(*x),
                // `Succ(Zero)` and the like: a numeral written with constructors.
                _ => self.numeral_of(a.clone()),
            };
            if let Some(x) = x {
                match lit_op(op, x, y) {
                    Some(n) => return Some(apps_rc(Lit(n), rest)),
                    // Taking it one `Succ` at a time would not end: the term
                    // stays as it is (`Core::past_u128`).
                    None => {
                        self.past_u128(op, x, y);
                        return None;
                    }
                }
            }
        }
        let out = match (op, self.nat_view(&b)?) {
            ("+" | "-", None) => a,
            (_, None) => Lit(0),
            ("+", Some(k)) => app(konst("Succ"), apps(konst("+"), [a, k])),
            ("*", Some(k)) => apps(konst("+"), [apps(konst("*"), [a.clone(), k]), a]),
            (_, Some(k)) => {
                let d = self.whnf(&apps(konst("-"), [a, k.clone()]));
                match self.nat_view(&d) {
                    Some(None) => Lit(0),
                    Some(Some(j)) => j,
                    // `pred` of a difference that does not reduce: it stays `a - b`.
                    None => return None,
                }
            }
        };
        Some(apps_rc(out, rest))
    }

    /// Notes that `x op y`, two numerals whose result is past `u128`, is left
    /// as it is. Computing it by the equations of [`Core::arith`] takes a step
    /// for each `Succ` of the result, which does not end. A term that is not
    /// reduced is never convertible to more than it is, so leaving it is
    /// sound; a comparison that needed its value fails, and the failure says
    /// why ([`Spent::past_u128`]).
    fn past_u128(&mut self, op: &str, x: u128, y: u128) {
        self.budget
            .past_u128
            .get_or_insert_with(|| format!("{x} {op} {y}"));
    }

    /// The number `t` reduces to when it is a numeral, or `Succ`s of one
    /// (`nat_le(a, b)` is `nat_lt(a, Succ(b))`, `list_length(l)` is a
    /// `Succ` for each element).
    fn numeral(&mut self, t: &R) -> Option<u128> {
        let w = self.whnf_shared(t);
        self.numeral_of(w)
    }

    /// [`Core::numeral`] of a term already in weak head normal form.
    ///
    /// Every `Succ` is followed, so a closed number written with
    /// constructors is read whatever its size. Below a `Succ`, a sum,
    /// product or difference is only computed on numerals
    /// ([`Core::literal_or_whnf`]): `x + 1000` with an unknown `x` reduces to
    /// `Succ(x + 999)`, and it stops there instead of unfolding the sum once
    /// for each `Succ`.
    fn numeral_of(&mut self, mut w: Tm) -> Option<u128> {
        let mut more: u128 = 0;
        loop {
            if self.timed_out() {
                return None;
            }
            match &w {
                Lit(k) => return k.checked_add(more),
                Const(c) if &**c == "Zero" => return Some(more),
                App(f, x) if matches!(&**f, Const(c) if &**c == "Succ") => {
                    more = more.checked_add(1)?;
                    let x = x.clone();
                    w = self.literal_or_whnf(&x);
                }
                _ => return None,
            }
        }
    }

    /// `t` as `base + k`: the `Succ`s and the `+ n` of a numeral `n` around
    /// `t` taken off, counted in `k` at once (`x + 9007199254740992` is one
    /// step, not that many `Succ`s). `base` is a weak head normal form that
    /// is neither of those nor a numeral; `None` when `t` is a numeral, when
    /// `k` passes `u128`, or when no `+ n` was taken off (a few `Succ`s are
    /// compared as they are). Nothing is reduced unless `t`, under its
    /// `Succ`s, is applied last to a numeral of at least [`LARGE_OFFSET`]
    /// (`x + n` or `Nat::add(x, n)`): below that, `Succ` by `Succ` is as good.
    fn offset_view(&mut self, t: &R) -> Option<(Tm, u128)> {
        let mut s: &Tm = t;
        while let App(f, x) = s
            && matches!(&**f, Const(c) if &**c == "Succ")
        {
            s = x;
        }
        if !matches!(s, App(_, n) if matches!(**n, Lit(n) if n >= LARGE_OFFSET)) {
            return None;
        }
        // Only a sum is taken apart: `Nat::lt(x + n, m)` also ends in a
        // numeral, but reducing it to read a `Succ` off runs `lt` down `n`
        // steps, one `Succ` of each side at a time.
        if !matches!(spine_rc(s).0, Const(c) if self.is_sum(c)) {
            return None;
        }
        let mut k: u128 = 0;
        let mut plus = false;
        let mut t = t.clone();
        loop {
            if self.timed_out() {
                return None;
            }
            if let (Const(c), args) = spine_rc(&t)
                && &**c == "+"
                && let [x, y] = args.as_slice()
                && let Lit(n) = self.literal_or_whnf(y)
            {
                k = k.checked_add(n)?;
                plus = true;
                t = x.clone();
                continue;
            }
            let w = self.whnf_shared(&t);
            match &w {
                Lit(_) => return None,
                Const(c) if &**c == "Zero" => return None,
                App(f, x) if matches!(&**f, Const(c) if &**c == "Succ") => {
                    k = k.checked_add(1)?;
                    t = x.clone();
                }
                _ => {
                    if let (Const(c), args) = spine_rc(&w)
                        && &**c == "+"
                        && args.len() == 2
                        && w != *t
                    {
                        t = Rc::new(w);
                        continue;
                    }
                    return plus.then_some((w, k));
                }
            }
        }
    }

    /// Whether `c` is `+`, or a name defined as a sum of its parameters
    /// (`Nat::add(a, b)` is `a + b`): what [`Core::offset_view`] reads `+ n`
    /// off.
    fn is_sum(&self, c: &str) -> bool {
        if c == "+" {
            return true;
        }
        let Some(mut v) = self.globals.get(c).and_then(|g| g.value.clone()) else {
            return false;
        };
        while let Lam(_, b) = &*v {
            v = b.clone();
        }
        matches!(spine_rc(&v), (Const(h), args) if &**h == "+" && args.len() == 2)
    }

    /// The operator `+`, `*` or `-` that `c` is: the operator itself, or a
    /// name defined as it on its two parameters in order (`Nat::add(a, b)`
    /// is `a + b`). Two such applications to convertible operands are
    /// convertible without unfolding the name.
    fn arith_op(&self, c: &str) -> Option<&'static str> {
        let op = |c: &str| ["+", "*", "-"].into_iter().find(|o| *o == c);
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
    fn numeric(&mut self, c: &Rc<str>, args: &[R]) -> Option<Tm> {
        if self.numeric_off || !NUMERIC.contains(&&**c) {
            return None;
        }
        let arity = numeric_arity(c);
        if args.len() < arity {
            return None;
        }
        let x = self.numeral(&args[0])?;
        let y = self.numeral(&args[1])?;
        let yn = |b: bool| konst(if b { "true" } else { "false" });
        let out = match &**c {
            "Nat::eq" => yn(x == y),
            "Nat::lt" => yn(x < y),
            "Nat::sub" => Lit(x.saturating_sub(y)),
            // A divisor of 0 comes only with a proof of `¬(0 = 0)`, under a
            // false assumption; `Nat::divmod` then never meets a remainder
            // equal to zero: the quotient is 0 and the remainder `a`.
            "Nat::div_nz" => Lit(x.checked_div(y).unwrap_or(0)),
            _ => Lit(x.checked_rem(y).unwrap_or(x)),
        };
        *self.budget.unfolds.entry(c.clone()).or_default() += 1;
        self.budget.last_unfold = Some(c.clone());
        Some(apps_rc(out, args[arity..].iter().cloned()))
    }

    /// `Some(None)` for a weak-head normal `t` that is zero, `Some(Some(k))`
    /// for one that is `Succ(k)`; a numeral is read as `Zero`/`Succ`.
    fn nat_view(&self, t: &Tm) -> Option<Option<Tm>> {
        match t {
            Lit(0) => Some(None),
            Lit(k) => Some(Some(Lit(k - 1))),
            Const(c) if &**c == "Zero" => Some(None),
            App(f, x) if matches!(&**f, Const(c) if &**c == "Succ") => Some(Some((**x).clone())),
            _ => None,
        }
    }

    /// The constructor application a weak-head normal major premise of a
    /// family `of` is, reading a numeral as `Zero`/`Succ`. The arguments are
    /// the nodes of `t` itself, so that what reducing them gives is found
    /// again (`Core::whnf_shared`) wherever the arm uses them.
    fn as_ctor(&self, t: &Tm, of: &str) -> Option<(Rc<str>, Vec<R>)> {
        if let Lit(k) = t {
            if of != "Nat" || !self.ctors.contains_key("Zero") {
                return None;
            }
            return Some(if *k == 0 {
                ("Zero".into(), vec![])
            } else {
                ("Succ".into(), vec![Rc::new(Lit(k - 1))])
            });
        }
        let (head, args) = spine_rc(t);
        match head {
            Const(c) if self.ctors.get(c).is_some_and(|(f, _)| &**f == of) => {
                Some((c.clone(), args))
            }
            _ => None,
        }
    }

    fn iota(&mut self, rec: &Rc<str>, shared: &[R]) -> Option<R> {
        let args: Vec<Tm> = shared.iter().map(|a| (**a).clone()).collect();
        let family = self.recs.get(rec)?.clone();
        let ind = self.inds.get(&family)?.clone();
        let np = ind.params;
        let nf = ind.group.len();
        let counts: Vec<usize> = ind
            .group
            .iter()
            .map(|g| self.inds.get(g).map_or(0, |i| i.ctors.len()))
            .collect();
        let nc: usize = counts.iter().sum();
        let major_at = np + nf + nc + ind.indices;
        let major = if self.lazy_iota {
            self.whnf_node(shared.get(major_at)?.clone(), false)
        } else {
            self.whnf_shared(shared.get(major_at)?)
        };
        let (of, cnp) = match &ind.alias {
            Some((j, a)) => (j.clone(), a.len()),
            None => (family.clone(), np),
        };
        let (cname, cargs) = match self.as_ctor(&major, &of) {
            Some(found) => found,
            None if self.lazy_iota => return None,
            None => {
                // An `Eq`-like proof reduces whenever the indices agree.
                let want = ind.k_like.clone()?;
                let params: Vec<Tm> = args[..np].to_vec();
                for (k, w) in want.iter().enumerate() {
                    let w = inst_many(w, &params);
                    if !self.conv(&w, &args[major_at - ind.indices + k]) {
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
        let suffix = rec.strip_prefix(&*family)?.strip_prefix("::")?.to_string();
        let mut applied = actual.clone();
        for r in &c.recs {
            let ys: Vec<u64> = (0..r.ys).map(|_| self.fresh(Sort(Sort::Prop))).collect();
            let mut env: Vec<Tm> = args[..np].to_vec();
            env.extend(actual.iter().map(|a| (**a).clone()));
            env.extend(ys.iter().map(|y| FVar(*y)));
            let mut call: Vec<R> = shared[..np + nf + nc].to_vec();
            call.extend(r.idx.iter().map(|t| Rc::new(inst_many(t, &env))));
            call.push(if ys.is_empty() {
                actual[r.arg].clone()
            } else {
                Rc::new(apps((*actual[r.arg]).clone(), ys.iter().map(|y| FVar(*y))))
            });
            let target = format!("{}::{suffix}", ind.group[r.fam]);
            let mut ih = apps_rc(Const(target.into()), call);
            for y in ys.iter().rev() {
                ih = lam_over(*y, &ih);
            }
            applied.push(Rc::new(ih));
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
        if needs.iter().any(|q| !self.quot.contains(*q)) {
            return fail(msg!(
                "kernel-core-quot-declared-after",
                name = name,
                needs = needs.join(", ")
            ));
        }
        if *ty != want {
            return fail(msg!("kernel-core-quot-type", name = name));
        }
        Ok(true)
    }

    /// `Quot_lift(A, r, B, f, h, quot_mk(A', r', a))` is `f(a)`, and
    /// `Quot::ind(A, r, P, m, quot_mk(A', r', a))` is `m(a)`: the value under
    /// `quot_mk` is passed to the function, whatever the relation.
    fn quot_iota(&mut self, c: &Rc<str>, args: &[R]) -> Option<R> {
        let (f, major) = match &**c {
            "Quot::lift" => (3, 5),
            "Quot::ind" => (3, 4),
            _ => return None,
        };
        let q = self.whnf_shared(args.get(major)?);
        let (head, inner) = spine_rc(&q);
        match head {
            Const(m) if &**m == "Quot::mk" && self.quot.contains(m) && inner.len() == 3 => {}
            _ => return None,
        }
        Some(apps_node(
            apps_node(args[f].clone(), [inner[2].clone()]),
            args[major + 1..].iter().cloned(),
        ))
    }

    fn expand_lit(t: Tm) -> Tm {
        match t {
            Lit(0) => konst("Zero"),
            Lit(k) => app(konst("Succ"), Lit(k - 1)),
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
        let (a, b) = (Rc::new(a.clone()), Rc::new(b.clone()));
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
        let w = self.whnf_shared(&Rc::new(other.clone()));
        let w = match (lit, w) {
            (Lit(_), w @ App(..)) | (Lit(_), w @ Const(_)) => Lit(self.numeral_of(w)?),
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
        if let Some((x, k)) = self.offset_view(a)
            && let Some((y, j)) = self.offset_view(b)
        {
            return k == j && self.conv_typed(&Rc::new(x), &Rc::new(y), ty);
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
                        &Rc::new(inst(r1, &FVar(x))),
                        &Rc::new(inst(r2, &FVar(x))),
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
                        &Rc::new(inst(r1, &FVar(x))),
                        &Rc::new(inst(r2, &FVar(x))),
                        Some(&inst(&cod, &FVar(x))),
                    )
                })
            }
            (Lam(_, r), other) | (other, Lam(_, r)) => {
                let Some((_, dom, cod)) = ty.and_then(|t| self.whnf(t).pi_parts()) else {
                    return false;
                };
                let x = self.fresh((*dom).clone());
                let applied = Rc::new(app(other.clone(), FVar(x)));
                self.under_binder(|c| {
                    c.conv_typed(
                        &Rc::new(inst(r, &FVar(x))),
                        &applied,
                        Some(&inst(&cod, &FVar(x))),
                    )
                })
            }
            _ => false,
        }
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
        if let Some(n) = self.numeric(c, &args) {
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
    fn def(&mut self, c: &Rc<str>) -> Option<Def> {
        if let Some(d) = self.defs.get(c) {
            return Some(*d);
        }
        self.globals.get(c)?.value.as_ref()?;
        let mut walk = DefWalk::default();
        self.def_visit(c, &mut walk);
        self.defs.get(c).copied()
    }

    fn def_visit(&mut self, c: &Rc<str>, w: &mut DefWalk) {
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
    fn uses(&self, c: &Rc<str>) -> Vec<Rc<str>> {
        let Some(v) = self.globals.get(c).and_then(|g| g.value.clone()) else {
            return Vec::new();
        };
        let mut seen: HashSet<usize> = HashSet::new();
        let mut out: Vec<Rc<str>> = Vec::new();
        let mut todo: Vec<R> = vec![v];
        while let Some(n) = todo.pop() {
            if !seen.insert(Rc::as_ptr(&n) as usize) {
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
    fn conv_cut(&mut self, f: &Rc<str>) -> bool {
        self.lays_open_itself(f)
            && self
                .conv_unfolded
                .iter()
                .any(|(g, at)| g == f && *at < self.conv_binders)
    }

    /// Whether `f` can lay open calls of itself: a name whose value uses it,
    /// or an eliminator, whose step on a constructor applies it again.
    fn lays_open_itself(&mut self, f: &Rc<str>) -> bool {
        self.recs.contains_key(f) || self.def(f).is_some_and(|d| d.recursive)
    }

    /// The recursive name (`Core::lays_open_itself`) both `a` and `b` apply to as
    /// many arguments, with the arguments.
    fn same_recursive<'t>(&mut self, a: &'t Tm, b: &'t Tm) -> Option<(Rc<str>, Vec<R>, Vec<R>)> {
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

    fn conv_plain(&mut self, a: &Tm, b: &Tm) -> bool {
        self.conv_node(&Rc::new(a.clone()), &Rc::new(b.clone()))
    }

    /// [`Core::conv_plain`] of two nodes: the parts compared are the nodes
    /// of the terms, so that what reducing them gave is found again.
    fn conv_node(&mut self, a: &R, b: &R) -> bool {
        let key = (Rc::as_ptr(a) as usize, Rc::as_ptr(b) as usize);
        if self.conv_fail.contains_key(&key) {
            return false;
        }
        let unfolded = self.conv_unfolded.len();
        let same = self.conv_nodes(a, b);
        self.conv_unfolded.truncate(unfolded);
        if !same && !self.budget.out {
            self.conv_fail
                .insert(key, (Rc::downgrade(a), Rc::downgrade(b)));
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

    fn conv_nodes(&mut self, a: &R, b: &R) -> bool {
        if Rc::ptr_eq(a, b) || a == b {
            return true;
        }
        if let Some(r) = self.conv_value(a, b) {
            return r;
        }
        // An eliminator reduces below without unfolding anything: whether
        // the comparison is cut is asked before (`Core::conv_cut`).
        if let Some((f, xs, ys)) = self.same_recursive(a, b) {
            if self.conv_cut(&f) {
                return xs.iter().zip(&ys).all(|(x, y)| self.conv_node(x, y));
            }
            self.conv_unfolded.push((f, self.conv_binders));
        }
        // `b + k` against `c + j`, both with numerals `k` and `j` and bases
        // `b` and `c` that are not `Succ` nor numerals: different when `k`
        // and `j` differ (one is `Succ` where the other is not), else when
        // `b` and `c` are. Taking `Succ` off one at a time instead goes as
        // deep as the numeral.
        if let Some((x, k)) = self.offset_view(a)
            && let Some((y, j)) = self.offset_view(b)
        {
            return k == j && self.conv_plain(&x, &y);
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
            && xs.iter().zip(&ys).all(|(x, y)| self.conv_node(x, y))
        {
            return true;
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
                return true;
            }
            let ((ha, xs), (hb, ys)) = (spine_rc(&a), spine_rc(&b));
            if let (Const(f), Const(g)) = (ha, hb)
                && f == g
                && xs.len() == ys.len()
            {
                // The arguments are nodes: a pair found different before is
                // answered at once (`conv_fail`), so trying them again at
                // the next unfolding costs one look per argument.
                if xs.iter().zip(&ys).all(|(x, y)| self.conv_node(x, y)) {
                    return true;
                }
                let f = f.clone();
                if self.conv_cut(&f) {
                    // Left by `whnf_lazy`, an eliminator may still reduce
                    // once its major premise is unfolded.
                    if self.force_both(&mut a, &mut b) {
                        continue;
                    }
                    return false;
                }
                if self.lays_open_itself(&f) {
                    self.conv_unfolded.push((f, self.conv_binders));
                }
            }
            // The higher name is unfolded first: it may unfold to the lower
            // one, which is then compared as it is (lazy unfolding by
            // height). Names of the same height unfold together.
            let (ua, ub) = match (self.head_height(&a), self.head_height(&b)) {
                (Some(x), Some(y)) if x > y => (self.unfold_head(&a), None),
                (Some(x), Some(y)) if x < y => (None, self.unfold_head(&b)),
                _ => (self.unfold_head(&a), self.unfold_head(&b)),
            };
            match (ua, ub) {
                (None, None) if self.force_both(&mut a, &mut b) => {}
                (None, None) => {
                    // Neither unfolds: each is its node's weak head normal
                    // form, found again wherever the node is met.
                    if !self.budget.out {
                        for (n, w) in [(na, &a), (nb, &b)] {
                            if Rc::strong_count(&n) > 1 {
                                self.remember(n, w.clone());
                            }
                        }
                    }
                    break;
                }
                (ua, ub) => {
                    if let Some(x) = ua {
                        a = self.whnf_lazy(Rc::new(x));
                    }
                    if let Some(y) = ub {
                        b = self.whnf_lazy(Rc::new(y));
                    }
                }
            }
        }
        if matches!(a, Lit(_)) != matches!(b, Lit(_)) {
            a = Self::expand_lit(a);
            b = Self::expand_lit(b);
        }
        match (&a, &b) {
            (BVar(x), BVar(y)) => x == y,
            (FVar(x), FVar(y)) => x == y,
            (Sort(x), Sort(y)) => x == y,
            (Const(x), Const(y)) => x == y,
            (Lit(x), Lit(y)) => x == y,
            (App(f, x), App(g, y)) => self.conv_node(f, g) && self.conv_node(x, y),
            (Pi(_, d1, r1), Pi(_, d2, r2)) => {
                if !self.conv_node(d1, d2) {
                    return false;
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
        }
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

    fn infer_unrecorded(&mut self, t: &Tm) -> Result<Tm, Box<Fault>> {
        // For each application entered: where the path comes back to, its
        // argument, and the domain and codomain of its function's type.
        let mut pending: Vec<((usize, usize), R, R, R)> = Vec::new();
        let mut t = t.clone();
        let inner = loop {
            match &t {
                App(f, a)
                    if !matches!(spine(&t).0, Lam(_, _))
                        && !matches!(**a, Lam(_, _))
                        && !self.is_hole(a) =>
                {
                    let ft = match self.down(0, None, |c| c.infer(f)) {
                        Ok(ft) => ft,
                        Err(e) => break Err(e),
                    };
                    let Some((_, dom, cod)) = self.whnf(&ft).pi_parts() else {
                        break Err(self.fault(Why::NotFunction));
                    };
                    let mark = self.enter(1, None);
                    let a = a.clone();
                    pending.push((mark, a.clone(), dom, cod));
                    t = (*a).clone();
                }
                _ => break self.infer_one(&t),
            }
        };
        let mut ty = match inner {
            Ok(ty) => ty,
            Err(e) => {
                if let Some((mark, ..)) = pending.first() {
                    self.leave(*mark);
                }
                return Err(e);
            }
        };
        while let Some((mark, a, dom, cod)) = pending.pop() {
            if !self.subtype(&ty, &dom) {
                let e = self.fault(Why::Mismatch {
                    expected: (*dom).clone(),
                    found: ty,
                });
                self.leave(pending.first().map_or(mark, |(m, ..)| *m));
                return Err(e);
            }
            self.leave(mark);
            ty = inst(&cod, &a);
        }
        Ok(ty)
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

    fn check_unrecorded(&mut self, t: &Tm, expected: &Tm) -> Result<(), Box<Fault>> {
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
        let ty = self.read_open(&o.ctx[i].1, o);
        o.visible = visible;
        o.types.push((x, ty));
        x
    }

    /// The atom of a name only the named checker has declared, its type
    /// read the first time.
    fn declared(&self, o: &mut Open<'_>, n: &str) -> Option<u64> {
        if let Some((_, x)) = o.declared.iter().find(|(m, _)| m == n) {
            return Some(*x);
        }
        let ty = (o.outer?)(n)?;
        let x = o.atom();
        o.declared.push((n.to_string(), x));
        let visible = std::mem::replace(&mut o.visible, 0);
        let ty = self.read_open(&ty, o);
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
        let read: Vec<Tm> = terms.iter().map(|t| self.read_open(t, &mut o)).collect();
        self.lctx.extend(o.types.drain(..));
        let x = f(self, &read, &o);
        self.lctx.clear();
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
            if w == read[0] {
                return t.clone();
            }
            Self::write(&w, o, &mut Vec::new(), t.span)
        })
    }

    /// `t` in weak head normal form in `ctx`, written back as a named term.
    /// What did not reduce is given back as it was written.
    pub(super) fn whnf_in(&mut self, ctx: &Ctx, t: &T) -> T {
        if self.stuck(ctx, t) {
            return t.clone();
        }
        self.ask(ctx, &[t], |c, read, o| {
            let w = c.whnf(&read[0]);
            if w == read[0] {
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
                        .map(|raw| c.write_derivation(raw, ctx, o, avoid, t.span)),
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
    ) -> Derivation {
        let mut shown = o.clone();
        let locals = self.name_bound(&raw.bound, &mut shown, avoid);
        let mut context = ctx.clone();
        context.extend(locals);
        let mut term = Self::write(&raw.term, &shown, &mut Vec::new(), span);
        let ty = Self::write(&raw.ty, &shown, &mut Vec::new(), span);
        let premises: Vec<_> = raw
            .premises
            .into_iter()
            .map(|p| self.write_derivation(p, ctx, o, avoid, span))
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
    ) -> Vec<(String, T)> {
        let mut out = Vec::new();
        for (x, h) in bound {
            let base = h.0.as_deref().unwrap_or("x");
            let taken = |n: &str| {
                o.ctx.iter().any(|(m, _)| m == n)
                    || o.named.iter().any(|(_, m)| m == n)
                    || self.globals.contains_key(n)
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
                    || self.globals.get(n.as_str()).is_some_and(|g| {
                        g.value.is_none()
                            && !self.recs.contains_key(n.as_str())
                            && !matches!(n.as_str(), "+" | "*" | "-")
                    })
            }
            _ => false,
        }
    }

    /// A term of the core as a named one. A binder keeps the name it was
    /// written with, primed (`n'1`, …) where that would capture a name its
    /// body uses; one written without a name that its body needs is `x`. The
    /// same term is written the same way wherever it is.
    fn write(t: &Tm, o: &Open<'_>, scope: &mut Vec<String>, span: tauto_parol::Span) -> T {
        let kind = match t {
            BVar(i) => TermKind::Var(scope[scope.len() - 1 - i].clone()),
            FVar(x) => o.back(*x).unwrap_or_else(|| TermKind::Var(format!("#{x}"))),
            Sort(s) => return sort_term(s, span),
            Const(c) => TermKind::Var(c.to_string()),
            Lit(k) => TermKind::Nat(k.to_string()),
            App(..) => {
                let (head, args) = spine(t);
                TermKind::App {
                    function: Box::new(Self::write(head, o, scope, span)),
                    arguments: args
                        .iter()
                        .map(|a| Self::write(a, o, scope, span))
                        .collect(),
                }
            }
            Pi(h, d, r) => {
                let d = Self::write(d, o, scope, span);
                let name = match &h.0 {
                    Some(n) => Some(Self::binder(n, r, o, scope)),
                    None => has_loose(r, 0).then(|| Self::binder("x", r, o, scope)),
                };
                scope.push(name.clone().unwrap_or_else(|| "_".into()));
                let r = Self::write(r, o, scope, span);
                scope.pop();
                TermKind::Pi {
                    params: vec![(name, d)],
                    result: Box::new(r),
                    effects: None,
                }
            }
            Lam(h, b) => {
                let name = Self::binder(h.0.as_deref().unwrap_or("x"), b, o, scope);
                scope.push(name.clone());
                let b = Self::write(b, o, scope, span);
                scope.pop();
                TermKind::Lam {
                    params: vec![name],
                    body: Box::new(b),
                    types: Vec::new(),
                }
            }
        };
        T::new(kind, span)
    }

    /// `base`, or the first of `base'1`, `base'2`, … that is not a name
    /// `body` (the body of the binder, under `scope`) uses.
    fn binder(base: &str, body: &Tm, o: &Open<'_>, scope: &[String]) -> String {
        let mut names = Vec::new();
        Self::names(body, 1, o, scope, &mut names);
        (0..)
            .map(|i| match i {
                0 => base.to_string(),
                i => format!("{base}'{i}"),
            })
            .find(|n| !names.contains(n))
            .expect("a fresh name")
    }

    /// The names a term at `depth` binders under `scope` uses: its globals,
    /// its context variables, the free names of its unread parts, and the
    /// variables of `scope` it refers to.
    fn names(t: &Tm, depth: usize, o: &Open<'_>, scope: &[String], out: &mut Vec<String>) {
        match t {
            BVar(i) if *i >= depth => {
                if let Some(n) = scope.get(scope.len().wrapping_sub(1 + i - depth)) {
                    out.push(n.clone());
                }
            }
            FVar(x) => match o.back(*x) {
                Some(TermKind::Var(n)) => out.push(n),
                Some(kind) => out.extend(super::free_vars(&T::new(kind, Default::default()))),
                None => {}
            },
            Const(c) => out.push(c.to_string()),
            Pi(_, a, b) | App(a, b) => {
                Self::names(a, depth, o, scope, out);
                let inner = if matches!(t, Pi(..)) {
                    depth + 1
                } else {
                    depth
                };
                Self::names(b, inner, o, scope, out);
            }
            Lam(_, b) => Self::names(b, depth + 1, o, scope, out),
            _ => {}
        }
    }

    fn fresh_name(&self, name: &str) -> Res<()> {
        if self.globals.contains_key(name) {
            return fail(msg!("kernel-core-already-defined", name = name));
        }
        Ok(())
    }

    /// A theorem, definition or function: its statement is a type, and its
    /// value (when given) has that type. `transparent` lets it unfold.
    fn add_decl_inner(
        &mut self,
        name: &str,
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
        let again = self.globals.contains_key(name);
        self.globals.insert(
            name.into(),
            Global {
                ty,
                value: if transparent {
                    value.map(Rc::new)
                } else {
                    None
                },
            },
        );
        if quot {
            self.quot.insert(name.into());
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
    pub(super) fn forget(&mut self, name: &str) {
        #[cfg(feature = "selfhost")]
        if let Some(trace) = &mut self.replay {
            trace.push((format!("F {name}"), true));
        }
        self.globals.remove(name);
        self.quot.remove(name);
        self.shared.clear();
        self.defs.clear();
    }

    /// A top-level `let`: its type is inferred.
    fn add_constant_inner(&mut self, name: &str, value: &T) -> Res<()> {
        self.fresh_name(name)?;
        let v = self.read(value)?;
        let ty = self.infer(&v)?;
        self.lctx.clear();
        self.globals.insert(
            name.into(),
            Global {
                ty,
                value: Some(Rc::new(v)),
            },
        );
        self.shared.clear();
        Ok(())
    }

    /// Makes an accepted declaration unfold (a function whose body the
    /// named checker compiled after checking its statement).
    fn set_value_inner(&mut self, name: &str, value: &T) -> Res<()> {
        if self.quot.contains(name) {
            return fail(msg!("kernel-core-quot-no-value", name = name));
        }
        let v = self.read(value)?;
        let ty = self
            .globals
            .get(name)
            .map(|g| g.ty.clone())
            .ok_or_else(|| msg!("kernel-core-not-defined", name = name))?;
        self.check(&v, &ty)?;
        self.lctx.clear();
        if let Some(g) = self.globals.get_mut(name) {
            g.value = Some(Rc::new(v));
        }
        self.shared.clear();
        self.defs.clear();
        Ok(())
    }

    /// An inductive declaration (a `mutual` group when there are several
    /// families) with `np` shared parameters, in the sort `out`. On success
    /// the families, constructors, nested members and eliminators are added.
    fn add_inductive_inner(&mut self, fams: &[FamSpec], np: usize, out: Sort) -> Res<()> {
        let saved = (self.globals.clone(), self.ctors.clone(), self.recs.clone());
        let result = self.inductive_inner(fams, np, out);
        if result.is_err() {
            (self.globals, self.ctors, self.recs) = saved;
        }
        self.lctx.clear();
        self.shared.clear();
        self.defs.clear();
        result
    }

    fn inductive_inner(&mut self, specs: &[FamSpec], np: usize, out: Sort) -> Res<()> {
        let names: Vec<Rc<str>> = specs.iter().map(|f| f.name.as_str().into()).collect();
        // Families first, so constructors (and siblings) can mention them.
        let mut fam_tys = Vec::new();
        for f in specs {
            self.fresh_name(&f.name)?;
            let ty = self.read(&f.ty)?;
            self.infer_sort(&ty)?;
            fam_tys.push(ty.clone());
            self.globals
                .insert(f.name.as_str().into(), Global { ty, value: None });
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
        let mut taken: Vec<Rc<str>> = names.clone();
        for (k, f) in specs.iter().enumerate() {
            for (cname, cty) in &f.ctors {
                self.fresh_name(cname)?;
                if taken.iter().any(|c| &**c == cname.as_str()) {
                    return fail(msg!("kernel-core-ctor-already-defined", name = cname));
                }
                taken.push(cname.as_str().into());
                let ty = self.read(cty)?;
                self.infer_sort(&ty)?;
                let mut walk = ty;
                for x in &params {
                    let Some((_, d, b)) = walk.pi_parts() else {
                        return fail(msg!("kernel-core-ctor-take-params", name = cname));
                    };
                    let px = self.lctx[x].clone();
                    if *d != px && !self.conv(&d, &px) {
                        return fail(msg!("kernel-core-ctor-take-params", name = cname));
                    }
                    walk = inst(&b, &FVar(*x));
                }
                let mut args = Vec::new();
                while let Some((_, d, b)) = walk.pi_parts() {
                    let s = self.infer_sort(&d)?;
                    if out != Sort::Prop && !s.le(&out) {
                        return fail(msg!("kernel-core-ctor-arg-universe", name = cname));
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
                        name = cname,
                        family = &f.name
                    ));
                }
                let result_idx = rargs[np..].to_vec();
                if result_idx.iter().any(|t| mentions_const(t, &names)) {
                    return fail(msg!("kernel-core-index-mentions-family", name = cname));
                }
                members[k].ctors.push(Ctor {
                    name: cname.as_str().into(),
                    args,
                    result_idx,
                    recs: Vec::new(),
                });
            }
        }
        // Positivity, nested occurrences and recursive arguments: for the
        // declared families, then for the members nesting adds (whose
        // constructors are those of the type they stand for).
        let mut group: Vec<Rc<str>> = names.clone();
        let mut aliases: Vec<(Rc<str>, Vec<Tm>)> = Vec::new();
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
                let suffix = if ms == Sort::Prop { "ind" } else { "rec" };
                let name: Rc<str> = format!("{}::{suffix}", members[k].name).into();
                self.fresh_name(&name)?;
                let ty = self.eliminator(&members, &params, k, ms.clone());
                if mentions_fvar(&ty) || has_loose(&ty, 0) {
                    return fail(msg!("kernel-core-eliminator-not-closed"));
                }
                self.infer_sort(&ty)?;
                elims.push((name, k, ty));
            }
        }
        for (name, k, ty) in elims {
            self.globals
                .insert(name.clone(), Global { ty, value: None });
            self.recs.insert(name, members[k].name.clone());
        }
        let group_names: Vec<Rc<str>> = members.iter().map(|m| m.name.clone()).collect();
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
                Rc::new(IndInfo {
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
        group: &mut Vec<Rc<str>>,
        aliases: &mut Vec<(Rc<str>, Vec<Tm>)>,
    ) -> Res<Tm> {
        if let Pi(h, a, b) = d {
            return Ok(Pi(
                h.clone(),
                a.clone(),
                Rc::new(self.nest(b, np, group, aliases)?),
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
            return fail(msg!("kernel-core-cannot-nest", name = &**j));
        }
        if args.iter().any(|a| mentions_fvar(a) || has_loose(a, 0)) {
            return fail(msg!("kernel-core-nested-depends"));
        }
        if let Some(k) = aliases.iter().position(|(j2, a2)| j2 == j && *a2 == args) {
            return Ok(Const(group[group.len() - aliases.len() + k].clone()));
        }
        let member: Rc<str> = format!("{}_{}{}", group[0], j, aliases.len() + 1).into();
        self.fresh_name(&member)?;
        group.push(member.clone());
        aliases.push((j.clone(), args));
        Ok(Const(member))
    }

    /// A recursive argument `∀ ys. G(params, idx)` with `G` in the group.
    fn recursive(
        &mut self,
        group: &[Rc<str>],
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
            return fail(msg!("kernel-core-recursive-arg-params", name = &**g));
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
    name: Rc<str>,
    /// `∀ indices. Sort`, over the parameters (atoms).
    index_tel: Tm,
    indices: usize,
    alias: Option<(Rc<str>, Vec<Tm>)>,
    ctors: Vec<Ctor>,
}

struct Ctor {
    name: Rc<str>,
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
fn positive(group: &[Rc<str>], d: &Tm) -> Res<()> {
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
    use super::super::{Kernel, Stmt, T, parse_program};
    use super::*;

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
        let p = parse_program(src).unwrap();
        let Stmt::Theorem(t) = &p.stmts[0] else {
            panic!()
        };
        let ty = k.telescope(&t.params, &t.ty).unwrap();
        let ty = k.shape(&ty).unwrap();
        let ty = k.elab(&Vec::new(), &ty, None).unwrap();
        let body = k
            .shape(&k.lambda_of(&t.params, t.body.as_ref().unwrap()).unwrap())
            .unwrap();
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
                let proof = (numeric_arity(op) == 3).then(|| konst("h"));
                let t = apps(konst(op), [Lit(x), Lit(y)].into_iter().chain(proof));
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

    /// A number written with many `Succ`s (as `list_length` gives) is read
    /// as a numeral, so `Nat::div_nz` and `*` are computed at once instead of
    /// unfolding; an unknown sum stops at its first `Succ`.
    #[test]
    fn a_long_succ_chain_is_a_numeral() {
        let mut k = kernel();
        let c = &mut k.core;
        let chain = (0..300).fold(konst("Zero"), |t, _| app(konst("Succ"), t));
        c.start_budget(None, None);
        let t = apps(
            konst("Nat::div_nz"),
            [apps(konst("*"), [chain, Lit(8)]), Lit(7), konst("h")],
        );
        assert_eq!(c.whnf(&t), Lit(342));
        assert!(c.end_budget().steps < 2000);
        c.start_budget(None, None);
        let open = Rc::new(apps(konst("+"), [FVar(0), Lit(1_000_000)]));
        assert_eq!(c.numeral(&open), None);
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
        let shared: R = Rc::new(app(BVar(3), BVar(0)));
        let terms = [
            Lit(1),
            BVar(0),
            BVar(7),
            app(BVar(2), Lit(4)),
            Lam(Hint::named("_"), Rc::new(app(BVar(0), BVar(4)))),
            Pi(Hint::named("_"), shared.clone(), shared.clone()),
            apps(konst("f"), [BVar(1), (*shared).clone(), BVar(5)]),
        ];
        for t in terms {
            let r = Rc::new(t);
            // The first call fills the memo, the second reads it.
            assert_eq!(loose(&r), loose_plain(&r));
            assert_eq!(loose(&r), loose_plain(&r));
        }
        forget_loose();
    }

    #[test]
    fn the_address_hasher_keeps_every_key_apart() {
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
        let mut k = kernel();
        let c = &mut k.core;
        c.start_budget(None, None);
        let nat = c.inds.get("Nat").unwrap().clone();
        let before = Rc::strong_count(&nat);
        let t = apps(
            konst("Nat::rec"),
            [
                Sort(Sort::ty(0)),
                Lit(0),
                Lam(
                    Hint::named("_"),
                    Rc::new(Lam(
                        Hint::named("_"),
                        Rc::new(app(konst("Succ"), app(konst("Succ"), BVar(0)))),
                    )),
                ),
                Lit(3),
            ],
        );
        let _ = c.whnf(&t);
        // The lookup of `iota` took no copy of the inductive that stays.
        assert_eq!(Rc::strong_count(&nat), before);
        c.end_budget();
    }

    #[test]
    fn a_passed_deadline_seen_by_a_loop_without_steps_ends_the_budget() {
        let mut k = kernel();
        let c = &mut k.core;
        c.start_budget(None, Some(crate::clock::Instant::now()));
        let r: R = Rc::new(app(BVar(0), BVar(1)));
        for _ in 0..4096 {
            let _ = inst_tm(&r, 0, &Rc::new(Lit(0)));
        }
        assert!(c.budget_out());
        assert!(c.end_budget().out);
        c.start_budget(None, None);
        for _ in 0..4096 {
            let _ = inst_tm(&r, 0, &Rc::new(Lit(0)));
        }
        assert!(!c.budget_out());
        assert!(!c.end_budget().out);
    }

    fn accepts(src: &str) {
        let mut k = kernel();
        let (ty, body) = read(&mut k, src);
        k.core.add_decl("t", &ty, Some(&body), false).unwrap();
    }

    fn rejects(src: &str) {
        let mut k = kernel();
        let (ty, body) = read(&mut k, src);
        assert!(
            k.core.add_decl("t", &ty, Some(&body), false).is_err(),
            "{src}"
        );
    }

    #[test]
    fn proofs_are_checked() {
        accepts(&r#"theorem t(A: Prop, a: A): A { a }"#.to_string());
        accepts(&r#"theorem t(): 2 + 2 = 4 { Refl(Nat, 4) }"#.to_string());
        accepts(
            &r#"theorem t(n: Nat): n + 2 = Succ(Succ(n)) { Refl(Nat, Succ(Succ(n))) }"#.to_string(),
        );
        rejects(&r#"theorem t(): 2 + 2 = 5 { Refl(Nat, 4) }"#.to_string());
        rejects(&r#"theorem t(A: Prop, B: Prop, a: A): B { a }"#.to_string());
        rejects(&r#"theorem t(): False { Trivial }"#.to_string());
        accepts(&r#"theorem t(): Nat::rec(k => Nat, 0, k => ih => Succ(Succ(ih)), 3) = 6 { Refl(Nat, 6) }"#.to_string());
        accepts(&r#"theorem t(e: Eq(Nat, 1, 1)): Eq::rec(Nat, 1, y => p => Nat, 7, 1, e) = 7 { Refl(Nat, 7) }"#.to_string());
    }

    #[test]
    fn a_false_equation_is_rejected_without_unfolding_twice() {
        // `conv` compares the arguments of two applications of the same name
        // before unfolding it; remembering the pairs that failed keeps that
        // from being exponential.
        let mut k = kernel();
        let defs = parse_program(
            &r#"fn double(n: Nat): Nat { match n: Nat { Zero => Zero
 Succ(m) => Succ(Succ(double(m))) } }
fn add2(a: Nat, b: Nat): Nat { match a: Nat { Zero => b
 Succ(m) => Succ(add2(m, b)) } }"#
                .to_string(),
        )
        .unwrap();
        for e in k.declare(&defs, false) {
            assert!(!e.failed(), "{e:?}");
        }
        let (ty, body) = read(
            &mut k,
            &r#"theorem t(): double(20) = add2(23, 20) { Refl(Nat, double(20)) }"#.to_string(),
        );
        assert!(k.core.add_decl("t", &ty, Some(&body), false).is_err());
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
        let ok = k.core.add_decl("t", &ty, Some(&body), false).is_ok();
        (k.core.end_budget().steps, ok)
    }

    #[test]
    fn a_redex_is_typed_without_computing() {
        // The motive applied to a number in the statement is typed by its
        // argument and its body, not by computing `fib(24)`.
        let (steps, ok) = steps_for(
            r#"fn add2(a: Nat, b: Nat): Nat { match a: Nat { Zero => b
 Succ(m) => Succ(add2(m, b)) } }
fn fib(n: Nat): Nat { match n: Nat { Zero => 1
 Succ(m) => match m: Nat { Zero => 1
 Succ(p) => add2(fib(m), fib(p)) } } }"#,
            r#"theorem t(): ((k) => fib(k))(24) = fib(24) { Refl(Nat, fib(24)) }"#,
        );
        assert!(ok);
        assert!(steps < 10_000, "{steps} steps");
    }

    #[test]
    fn a_deep_wrong_argument_is_rejected_in_linear_steps() {
        // `big(big(r))` against `big(r)`: both reduce to a chain of 400
        // stuck `2 * pow2(…)`. The typed comparison goes down the chain after
        // the untyped one failed; comparing copies, each link compared and
        // reduced again all of the chain below it, about two million steps.
        let defs = r#"fn pow2(n: Nat): Nat { match n: Nat { Zero => 1
 Succ(k) => 2 * pow2(k) } }
fn big(s: Nat): Nat { pow2(s + 400) }
fn is_zero(n: Nat): Bool { match n: Bool { Zero => true
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
        // `m(n)` is `mx(n, n)`, whose arms are its arguments: the arm taken
        // is the argument's own node, whose value was found when `nat_lt`
        // compared it, so thirty `m`s reduce each argument once.
        let (steps, ok) = steps_for(
            r#"fn mx(a: Nat, b: Nat): Nat { match Nat::lt(a, b): Nat { false => a
 true => b } }
fn m(n: Nat): Nat { mx(n, n) }"#,
            r#"theorem t(): m(m(m(m(m(m(m(m(m(m(m(m(m(m(m(m(m(m(m(m(m(m(m(m(m(m(m(m(m(m(20)))))))))))))))))))))))))))))) = 20 { Refl(Nat, 20) }"#,
        );
        assert!(ok);
        assert!(steps < 5_000, "{steps} steps");
        let (_, ok) = steps_for(
            r#"fn mx(a: Nat, b: Nat): Nat { match Nat::lt(a, b): Nat { false => a
 true => b } }
fn m(n: Nat): Nat { mx(n, n) }"#,
            r#"theorem t(): m(m(m(m(m(m(m(m(m(m(m(m(m(m(m(m(m(m(m(m(m(m(m(m(m(m(m(m(m(m(20)))))))))))))))))))))))))))))) = 21 { Refl(Nat, 20) }"#,
        );
        assert!(!ok);
    }

    #[test]
    fn a_wrong_number_is_rejected_by_its_value() {
        // A number compared with a literal is computed once and compared as a
        // value; a wrong literal costs about what the right one does.
        let defs = r#"fn h(n: Nat): Nat { match n: Nat { Zero => 123456789
 Succ(m) => Nat::rem_nz(Nat::sub(h(m), 7), 1000003, (e: Eq(Nat, 1000003, 0)) => Eq::subst((x: Nat) => match x: Prop {
   Zero => False
   Succ(_) => True
 }, e, Trivial)) } }"#;
        let right = steps_for(defs, r#"theorem t(): h(30) = 456210 { Refl(Nat, h(30)) }"#);
        let wrong = steps_for(defs, r#"theorem t(): h(30) = 456211 { Refl(Nat, h(30)) }"#);
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
        let mut m: NodeTable<()> = NodeTable::default();
        let kept = Rc::new(Lit(0));
        m.insert(Rc::as_ptr(&kept) as usize, (Rc::downgrade(&kept), ()));
        let mut gone = Vec::new();
        while m.len() < 4096 {
            let n = Rc::new(Lit(m.len() as u128));
            m.insert(Rc::as_ptr(&n) as usize, (Rc::downgrade(&n), ()));
            gone.push(n);
        }
        drop(gone);
        sweep(&mut m);
        assert_eq!(m.len(), 1);
    }

    #[test]
    fn a_table_that_kept_its_nodes_is_not_walked_again_until_it_doubles() {
        let mut m: NodeTable<()> = NodeTable::default();
        let nodes: Vec<R> = (0..SWEEP_FROM).map(|i| Rc::new(Lit(i as u128))).collect();
        for n in &nodes {
            m.insert(Rc::as_ptr(n) as usize, (Rc::downgrade(n), ()));
        }
        sweep(&mut m);
        assert_eq!(m.len(), SWEEP_FROM);
        assert_eq!(m.sweep_at, 2 * SWEEP_FROM);
        // Inserting again under a key it has (as `remember` does) walks nothing.
        m.insert(
            Rc::as_ptr(&nodes[0]) as usize,
            (Rc::downgrade(&nodes[0]), ()),
        );
        sweep(&mut m);
        assert_eq!(m.sweep_at, 2 * SWEEP_FROM);
    }

    #[test]
    fn names_are_read_by_their_binders() {
        // A binder named like a sort or `_` is just a binder here: names are
        // resolved by their binders, not by their spelling.
        rejects(&r#"theorem t(Type: Prop): Type { Nat }"#.to_string());
        rejects(
            &r#"theorem t(): ∀ x: Prop. ∀ y: Prop. ∀ h: y. x { _ => _ => h => h }"#.to_string(),
        );
        rejects(
            &r#"theorem t(): ∀ x: Prop. ∀ y: Prop. ∀ h: y. x { a => b => h => h }"#.to_string(),
        );
    }

    #[test]
    fn a_redex_types_its_argument() {
        rejects(
            &r#"theorem t(): Nat { (x => 0)(Trivial(Trivial)) }
"#
            .to_string(),
        );
        accepts(&r#"theorem t(): Nat { (x => 0)(Trivial) }"#.to_string());
    }

    /// The quotient's constants are declared once, in order, with the type
    /// the core gives them and no value.
    #[test]
    fn quotient_constants_are_fixed() {
        let mut k = kernel();
        let (ty, body) = read(&mut k, "theorem t(n: Nat): Nat { n }");
        assert!(k.core.add_decl("Quot::lift", &ty, None, false).is_err());
        assert!(k.core.set_value("Quot::lift", &body).is_err());
        let mut fresh = Kernel::new();
        let (ty, _) = read(&mut fresh, "theorem t(A: Type): Type { A }");
        let err = fresh
            .core
            .add_decl("Quot::mk", &ty, None, false)
            .unwrap_err();
        assert_eq!(err.id, "kernel-core-quot-declared-after", "{err:?}");
        let err = fresh.core.add_decl("Quot", &ty, None, false).unwrap_err();
        assert_eq!(err.id, "kernel-core-quot-type", "{err:?}");
    }

    fn inductive(src: &str) -> Result<(), Message> {
        tauto_messages::install();
        let mut k = kernel();
        let p = parse_program(src).unwrap();
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
                let args: Vec<(String, T)> = c
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

    #[test]
    fn inductive_declarations_are_read_again() {
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
    /// Specialize the motive universe of an already validated large eliminator.
    /// Its parameters, indices and reduction rule are unchanged.
    pub(super) fn recursor_at(&mut self, family: &str, level: &super::Level) -> Res<()> {
        let result = self.recursor_at_inner(family, level);
        self.shared.clear();
        self.defs.clear();
        #[cfg(feature = "selfhost")]
        self.record(Some(format!("R {family} {level}")), result.is_ok());
        result
    }

    fn recursor_at_inner(&mut self, family: &str, level: &super::Level) -> Res<()> {
        if level.floor() > 65535 {
            return fail(msg!("kernel-core-recursor-universe"));
        }
        let info = self
            .inds
            .get(family)
            .cloned()
            .ok_or_else(|| msg!("kernel-core-unknown-family"))?;
        let mut pending = Vec::new();
        for member in &info.group {
            let original: Rc<str> = format!("{member}::rec").into();
            if self.recs.get(&original) != Some(member) {
                return fail(msg!("kernel-core-no-large-elimination"));
            }
            let name: Rc<str> = format!("{member}::rec@{level}").into();
            if self.recs.contains_key(&name) {
                continue;
            }
            self.fresh_name(&name)?;
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
                        Rc::new(change(cod, skip - 1, count, level)?),
                    ));
                }
                fn result_sort(t: &Tm, level: &super::Level) -> Res<Tm> {
                    match t {
                        Pi(h, a, b) => {
                            Ok(Pi(h.clone(), a.clone(), Rc::new(result_sort(b, level)?)))
                        }
                        Sort(super::Sort::Type(_)) => Ok(Sort(super::Sort::Type(level.clone()))),
                        _ => fail(msg!("kernel-core-invalid-motive")),
                    }
                }
                Ok(Pi(
                    h.clone(),
                    Rc::new(result_sort(dom, level)?),
                    Rc::new(change(cod, 0, count - 1, level)?),
                ))
            }
            let ty = change(&ty, info.params, info.group.len(), level)?;
            self.infer_sort(&ty)?;
            pending.push((name, member.clone(), ty));
        }
        for (name, member, ty) in pending {
            self.globals
                .insert(name.clone(), Global { ty, value: None });
            self.recs.insert(name, member);
        }
        Ok(())
    }
}
