//! Declaring files on copies of a kernel, side by side, and taking what each
//! copy declared back into the kernel it was copied from. Files that do not
//! import one another declare nothing the other reads, so each copy can
//! declare its file on the environment they share, and the declarations of
//! each are added to it afterwards (`tauto/src/read.rs` says in what order).
//!
//! A copy costs what the kernel holds of its environment, not what it has
//! recorded of the files declared so far:
//! - [`Kernel::snapshot`] leaves out the records of the files (the sites of
//!   constructors, fields and applications, the timings, what was derived and
//!   elaborated), which no other file reads. Each copy starts them empty, and
//!   [`Kernel::append_logs`] adds them in the files' order.
//! - The maps from occurrences to their origins, which the files declared
//!   later do read, are shared in layers ([`Layered`]) instead of copied.
//!
//! What a copy declared is what it wrote: its tables are
//! [`tauto_identity::ForkedMap`]s and [`tauto_identity::ForkedSet`]s, which
//! know what was written in them since the copy was made — added, changed
//! (a standard file giving a spelling the library had a meaning of its own)
//! or removed. [`Kernel::subtract`] leaves in a copy only that, so that a
//! copy waiting to be taken in is small, and [`Kernel::absorb`] writes it
//! into the kernel, so that each table ends as declaring the files in turn
//! leaves it. A key two copies wrote is not taken in silently: which write
//! stood would depend on which copy finished first, so [`Logs::alone`] says
//! so and the files are declared in turn. The lists that only grow keep
//! what was added after the copy was made. The proof cache's interfaces are
//! what was worked out, not declared: the same global's interface is the same
//! whichever copy found it, and the first found is kept. What
//! holds only for the declaration in hand (unknowns, the binders gone under,
//! the core's comparisons), and what was worked out only to be faster later,
//! is let go ([`Kernel::settle`]); the interfaces the proof cache found are
//! kept, so that no copy finds them again.

use std::collections::HashMap;
use std::hash::Hash;

use super::Kernel;

/// How far apart the counters of the copies start, so that the names one
/// makes up (`x'42`) are never the names another makes up. A 32-bit `usize` (wasm32) cannot
/// hold `1 << 40`, so there the stride is smaller.
const COUNTER_STRIDE: usize = if usize::BITS >= 64 { 1 << 40 } else { 1 << 20 };

/// The lengths of the growing lists of the kernel a copy was made from.
pub struct ForkMark {
    /// The generation the copy was made in (`tauto_identity::forked`).
    since: u64,
    holes: usize,
    class_expansions: usize,
    law_spans: usize,
    source_law_spans: usize,
}

pub(super) fn add_after<T>(into: &mut Vec<T>, mut from: Vec<T>, at: usize) {
    if from.len() > at {
        into.extend(from.drain(at..));
    }
}

impl Kernel {
    /// A copy of this kernel to declare files on beside other copies; the
    /// `index`th copy. What it declares comes back with [`Kernel::absorb`].
    pub fn snapshot(&mut self) -> Kernel {
        // What the kernel has recorded about the files declared so far is
        // not read while other files are declared: the copy starts without
        // it, and what the copy records is added after it.
        self.ctor_site_origins.freeze();
        self.application_heads.freeze();
        let ctor_sites = std::mem::take(&mut self.ctor_sites);
        let field_sites = std::mem::take(&mut self.field_sites);
        let ascription_sites = std::mem::take(&mut self.ascription_sites);
        let application_sites = std::mem::take(&mut self.application_sites);
        let timings = std::mem::take(&mut self.timings);
        let derived = std::mem::take(&mut self.derived);
        let elaborated = self.elaborated.as_mut().map(std::mem::take);
        let derivations = self.derivations.as_mut().map(std::mem::take);
        let copy = self.clone();
        self.ctor_sites = ctor_sites;
        self.field_sites = field_sites;
        self.ascription_sites = ascription_sites;
        self.application_sites = application_sites;
        self.timings = timings;
        self.derived = derived;
        if let (Some(into), Some(from)) = (&mut self.elaborated, elaborated) {
            *into = from;
        }
        if let (Some(into), Some(from)) = (&mut self.derivations, derivations) {
            *into = from;
        }
        copy
    }

    /// A copy of `base`, a [`Kernel::snapshot`], to declare the file at
    /// place `index` on beside other copies. What it declares comes back
    /// with [`Kernel::absorb`] into the kernel `base` was made of.
    pub fn fork_of(base: &Kernel, index: usize) -> (Kernel, ForkMark) {
        let since = tauto_identity::forked::next_generation();
        let mut copy = base.clone();
        // Each file's copy makes up names (`x'42`) no other file's copy makes
        // up, whichever copies run when.
        let offset = (index + 1) * COUNTER_STRIDE;
        copy.fresh += offset;
        copy.core.offset_counter(offset as u64);
        copy.declared_states.clear();
        let mark = ForkMark {
            since,
            holes: base.holes.len(),
            class_expansions: base.class_expansions.len(),
            law_spans: base.classes.law_spans_len(),
            source_law_spans: base.source_classes.law_spans_len(),
        };
        (copy, mark)
    }

    /// The state families this copy declared because the kernel it was made
    /// of had none of them. Such a copy is not taken in: another copy may
    /// have declared the same family, so the family is declared on the
    /// kernel ([`Kernel::declare_states`]) and the file again on a copy that
    /// has it.
    pub fn declared_states(&self) -> &[usize] {
        &self.declared_states
    }

    /// Declares the state families `ks` this kernel does not have yet. False
    /// when one does not check.
    pub fn declare_states(&mut self, ks: &[usize]) -> bool {
        ks.iter()
            .all(|&k| self.declare_mut(k, tauto_parol::Span::new(0, 0)).is_ok())
    }

    /// Leaves in this copy, made of `base` by [`Kernel::fork_of`], only what
    /// it added, so that it is small while it waits to be taken in.
    pub fn subtract(&mut self, base: &Kernel, mark: &mut ForkMark) {
        let since = mark.since;
        self.globals.subtract(since);
        self.skipped.subtract(since);
        self.fns.subtract(since);
        self.item_lends.subtract(since);
        self.inds.subtract(since);
        self.ctors.subtract(since);
        self.recs.subtract(since);
        self.ahead.subtract(since);
        self.core.subtract(since);
        if let (Some(mine), Some(theirs)) = (&mut self.cache, &base.cache) {
            mine.subtract(theirs);
        }
        self.holes.drain(..mark.holes.min(self.holes.len()));
        mark.holes = 0;
        self.hole_lets.subtract(since);
        self.derivation_names.subtract(since);
        self.shown.subtract(since);
        self.seal_after.subtract(since);
        self.deq_listed.subtract(since);
        self.deq_why.subtract(since);
        self.ctor_site_origins.drop_shared();
        self.application_heads.drop_shared();
        self.classes.subtract(since, mark.law_spans);
        mark.law_spans = 0;
        self.source_classes.subtract(since, mark.source_law_spans);
        mark.source_law_spans = 0;
        self.class_expansions
            .drain(..mark.class_expansions.min(self.class_expansions.len()));
        mark.class_expansions = 0;
        self.templates.subtract(since);
        self.level_instances.subtract(since);
        self.budgets.subtract(since);
        self.effects.subtract(since);
        self.resolver.subtract(since, &base.resolver);
    }

    /// Lets go of what [`Kernel::absorb`] does not take in, so that a copy
    /// that has declared its files and waits to be taken in is small.
    pub fn settle(&mut self) {
        self.head_types = Default::default();
        self.term_facts = Default::default();
        self.metas = Default::default();
        if let Some(cache) = &mut self.cache {
            cache.settle();
        }
        self.core.settle();
    }

    /// Takes in what `copy`, made by [`Kernel::fork`] of this kernel,
    /// declared since.
    pub fn absorb(&mut self, copy: Kernel, mark: ForkMark) -> Logs {
        let Kernel {
            resolver,
            written_fields: _,
            head_types: _,
            term_facts: _,
            globals,
            skipped,
            fns,
            item_lends,
            inds,
            ctors,
            recs,
            fresh,
            arrow_binders: _,
            metas: _,
            current: _,
            projecting: _,
            ahead,
            defining: _,
            defining_implicit: _,
            deep: _,
            matched: _,
            core,
            holes,
            hole_lets,
            cache,
            elaborated,
            derivations,
            derivation_names,
            shown,
            deq_started,
            structural_instances: _,
            inference_owners: _,
            seal_after,
            deq_listed,
            deq_why,
            derived,
            record_sites: _,
            group_shared: _,
            ctor_sites,
            field_sites,
            ascription_sites,
            ctor_site_origins,
            application_sites,
            application_heads,
            classes,
            source_classes,
            class_expansions,
            templates,
            level_instances,
            level_depth: _,
            timeout: _,
            file_limit: _,
            statement_only: _,
            step_limit: _,
            budgets,
            gave_up,
            from_cache: _,
            timings,
            declared_states: _,
            text_literals: _,
            text_literal_names: _,
            effects,
        } = copy;
        let mut alone = self.resolver.absorb(resolver);
        alone &= self.globals.absorb_any(globals.into_forked());
        alone &= self.skipped.absorb(skipped);
        alone &= self.fns.absorb(fns);
        alone &= self.item_lends.absorb(item_lends);
        alone &= self.inds.absorb_any(inds.into_forked());
        alone &= self.ctors.absorb(ctors);
        alone &= self.recs.absorb(recs);
        self.fresh = self.fresh.max(fresh);
        alone &= self.ahead.absorb_any(ahead);
        alone &= self.core.absorb(core);
        if let (Some(into), Some(from)) = (&mut self.cache, cache) {
            into.absorb(from);
        }
        add_after(&mut self.holes, holes, mark.holes);
        alone &= self.hole_lets.absorb(hole_lets);
        alone &= self.derivation_names.absorb(derivation_names);
        alone &= self.shown.absorb(shown);
        self.deq_started |= deq_started;
        alone &= self.seal_after.absorb(seal_after);
        alone &= self.deq_listed.absorb(deq_listed);
        alone &= self.deq_why.absorb(deq_why);
        self.ctor_site_origins.absorb(ctor_site_origins);
        self.application_heads.absorb(application_heads);
        alone &= self.classes.absorb(classes, mark.law_spans);
        alone &= self
            .source_classes
            .absorb(source_classes, mark.source_law_spans);
        add_after(
            &mut self.class_expansions,
            class_expansions,
            mark.class_expansions,
        );
        alone &= self.templates.absorb_any(templates);
        alone &= self.level_instances.absorb(level_instances);
        alone &= self.budgets.absorb(budgets);
        if self.gave_up.is_none() {
            self.gave_up = gave_up;
        }
        alone &= self.effects.absorb(effects);
        Logs {
            alone,
            derived,
            ctor_sites,
            field_sites,
            ascription_sites,
            application_sites,
            timings,
            elaborated,
            derivations,
        }
    }

    /// Adds what a copy recorded about its files ([`Kernel::absorb`]); the
    /// records of the files are added in the files' order.
    pub fn append_logs(&mut self, logs: Logs) {
        self.derived.extend(logs.derived);
        self.ctor_sites.extend(logs.ctor_sites);
        self.field_sites.extend(logs.field_sites);
        self.ascription_sites.extend(logs.ascription_sites);
        self.application_sites.extend(logs.application_sites);
        self.timings.extend(logs.timings);
        if let (Some(into), Some(from)) = (&mut self.elaborated, logs.elaborated) {
            into.extend(from);
        }
        if let (Some(into), Some(from)) = (&mut self.derivations, logs.derivations) {
            into.extend(from);
        }
    }
}

impl Logs {
    /// [`Logs::alone`](struct@Logs).
    pub fn alone(&self) -> bool {
        self.alone
    }
}

/// What a copy recorded about the files it declared, which the kernel it was
/// copied from takes in the files' order (`Kernel::append_logs`).
pub struct Logs {
    /// False when the copy wrote something another copy taken in since it
    /// was made wrote too: which write stands would depend on which copy
    /// finished first, so the files are to be declared in turn.
    alone: bool,
    derived: Vec<(super::Name, Vec<crate::surface::Stmt>)>,
    ctor_sites: Vec<super::CtorSite>,
    field_sites: Vec<super::FieldSite>,
    ascription_sites: Vec<super::AscriptionSite>,
    application_sites: Vec<super::ApplicationSite>,
    timings: Vec<super::Timing>,
    elaborated: Option<Vec<(super::Name, super::T)>>,
    derivations: Option<Vec<(super::Name, super::Derivation)>>,
}

/// A map shared by a kernel and the copies made of it: what the kernel had
/// when copies were made (`layers`, shared and not copied), and what was
/// added since (`top`). A copy adds to its own `top`, and the kernel takes
/// those in after; the copies never copy what all of them share.
#[derive(Clone)]
pub(super) struct Layered<K, V> {
    layers: Vec<std::sync::Arc<Map<K, V>>>,
    top: Map<K, V>,
}

/// The maps of a [`Layered`]: their keys are the checker's own serial numbers,
/// not input an adversary picks, and a lookup runs at every substitution, so
/// they hash by one multiplication instead of SipHash.
type Map<K, V> = HashMap<K, V, std::hash::BuildHasherDefault<SerialHasher>>;

/// Hashes the integers a key writes by multiplying them into one word.
#[derive(Default)]
pub(super) struct SerialHasher(u64);

impl std::hash::Hasher for SerialHasher {
    fn finish(&self) -> u64 {
        self.0
    }
    fn write(&mut self, bytes: &[u8]) {
        for b in bytes {
            self.write_u64(u64::from(*b));
        }
    }
    fn write_u64(&mut self, n: u64) {
        self.0 = (self.0.rotate_left(5) ^ n).wrapping_mul(0x9e37_79b9_7f4a_7c15);
    }
}

/// How many shared layers a [`Layered`] keeps before it puts them into one.
const LAYERS: usize = 8;

impl<K, V> Default for Layered<K, V> {
    fn default() -> Self {
        Self {
            layers: Vec::new(),
            top: Map::default(),
        }
    }
}

impl<K: Eq + Hash + Clone, V: Clone> Layered<K, V> {
    pub(super) fn get(&self, k: &K) -> Option<&V> {
        self.top
            .get(k)
            .or_else(|| self.layers.iter().rev().find_map(|l| l.get(k)))
    }

    pub(super) fn insert(&mut self, k: K, v: V) {
        self.top.insert(k, v);
    }

    /// The entry for `k`, made with `f` when there is none.
    pub(super) fn or_insert_with(&mut self, k: K, f: impl FnOnce() -> V) -> &mut V {
        if !self.top.contains_key(&k) {
            let v = self.get(&k).cloned().unwrap_or_else(f);
            self.top.insert(k.clone(), v);
        }
        self.top.get_mut(&k).expect("just inserted")
    }

    /// Moves what was added into the shared part, so that copies made now
    /// share all of it. What a copy still shares is not copied: the added
    /// part becomes a layer of its own, and the layers are put into one only
    /// when there are many.
    pub(super) fn freeze(&mut self) {
        if self.top.is_empty() {
            return;
        }
        let top = std::mem::take(&mut self.top);
        match self.layers.last_mut().and_then(std::sync::Arc::get_mut) {
            Some(last) => last.extend(top),
            None => self.layers.push(std::sync::Arc::new(top)),
        }
        if self.layers.len() > LAYERS {
            let mut all = Map::default();
            for layer in self.layers.drain(..) {
                all.extend(std::sync::Arc::unwrap_or_clone(layer));
            }
            self.layers.push(std::sync::Arc::new(all));
        }
    }

    /// Lets go of the shared part: a copy hands back only what it added.
    pub(super) fn drop_shared(&mut self) {
        self.layers.clear();
    }

    /// Takes in what a copy of this map added; earlier entries win.
    pub(super) fn absorb(&mut self, copy: Self) {
        for (k, v) in copy.top {
            if self.get(&k).is_none() {
                self.top.insert(k, v);
            }
        }
    }
}
