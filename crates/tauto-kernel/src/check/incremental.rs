//! The kernel a statement at a time, for a checker that keeps its work between
//! edits (`crates/tauto-analyzer`). Nothing here decides anything the
//! kernel does not: a statement is declared by the same `Kernel::declare` that
//! `check_file` calls, and a declaration is accepted only by the two checkers.
//! What this adds is a kernel that can be copied (a checkpoint to go on from),
//! a digest of what a statement left in it (so work that depends only on the
//! digest can be kept when a proof, but not its statement, changes), and the
//! pieces of `declare_loaded` a caller needs to lay out the verdicts of one
//! statement.

use crate::surface::Name;
use std::collections::HashSet;

use super::*;

/// A kernel with the prelude declared and some statements of a program; it
/// can be copied and told the next statement.
#[derive(Clone)]
pub struct Checker {
    kernel: Kernel,
}

pub struct Declared {
    /// The verdicts, with spans as the kernel made them (offsets into the
    /// whole program): `tauto::check::localize_entries` turns them into
    /// offsets in a file.
    pub entries: Vec<Entry>,
    /// A SHA-256 of what the statement added to the kernel as a later
    /// statement can see it: statements, not proofs.
    pub digest: String,
}

impl Checker {
    /// The prelude's constants and nothing else. With `proof_cache`, proofs
    /// checked before are taken from the proof cache as `check_file` takes
    /// them (`TAUTO_CACHE`, `check/cache.rs`); without it every proof is
    /// checked.
    pub fn new(proof_cache: bool) -> Result<Checker, String> {
        let mut kernel = Kernel::new();
        declare_prelude(&mut kernel)?;
        if proof_cache {
            kernel.cache = cache::Cache::from_env();
        }
        Ok(Checker { kernel })
    }

    /// What the syntax macros wrote their output as, for the
    /// messages about it.
    pub fn show_syntax(&mut self, shown: HashMap<u32, String>) {
        self.kernel.shown = shown;
    }

    /// [`Kernel::source_alias`].
    pub fn source_alias(&mut self, spelling: &str, reference: &tauto_surface::identity::DeclRef) {
        self.kernel.source_alias(spelling, reference);
    }

    /// The constants the kernel knows now, sorted by name.
    pub fn library(&self) -> Vec<LibEntry> {
        self.kernel.library()
    }

    pub fn declare(&mut self, stmt: &Stmt) -> Declared {
        let before = Names::of(&self.kernel);
        let program = Program {
            stmts: vec![stmt.clone()],
            errors: Vec::new(),
        };
        let entries = self.kernel.declare(&program, false);
        let digest = before.digest_of_new(&self.kernel, &entries);
        Declared { entries, digest }
    }
}

/// The names the kernel knew, to tell what a statement added.
struct Names {
    globals: HashSet<Name>,
    inds: HashSet<Name>,
    ctors: HashSet<Name>,
    recs: HashSet<Name>,
    templates: HashSet<Name>,
}

impl Names {
    fn of(k: &Kernel) -> Names {
        let keys = |m: &mut dyn Iterator<Item = &Name>| m.cloned().collect();
        Names {
            globals: keys(&mut k.globals.keys()),
            inds: keys(&mut k.inds.keys()),
            ctors: keys(&mut k.ctors.keys()),
            recs: keys(&mut k.recs.keys()),
            templates: keys(&mut k.templates.keys()),
        }
    }

    /// The digest of what was added since: each new global's type, value (a
    /// proof is not kept as one), axioms and flags, and each new family,
    /// constructor and eliminator. Places are left out, so a statement that
    /// only moved has the same digest.
    fn digest_of_new(&self, k: &Kernel, entries: &[Entry]) -> String {
        let mut parts: Vec<String> = Vec::new();
        for (name, g) in &k.globals {
            if !self.globals.contains(name) {
                parts.push(format!(
                    "global {name}: {:?} := {:?} axioms {:?} implicit {} failed {} incomplete {}",
                    g.ty, g.value, g.axioms, g.implicit, g.failed, g.incomplete
                ));
            }
        }
        for (name, ind) in &k.inds {
            if !self.inds.contains(name) {
                parts.push(format!("ind {name}: {ind:?}"));
            }
        }
        for (name, c) in &k.ctors {
            if !self.ctors.contains(name) {
                parts.push(format!("ctor {name}: {c:?}"));
            }
        }
        for (name, f) in &k.recs {
            if !self.recs.contains(name) {
                parts.push(format!("rec {name}: {f:?}"));
            }
        }
        // The zero-level instance does not describe future instantiations.
        // Include the original template, including its body, because a later
        // declaration may request a level whose behavior differs after an edit.
        for (name, template) in &k.templates {
            if !self.templates.contains(name) {
                parts.push(format!("template {name}: {template:?}"));
            }
        }
        parts.sort();
        // What a declaration reports that is not in the kernel: that it is
        // incomplete, what it uses, and the axioms of a checked one.
        for e in entries {
            parts.push(match &e.verdict {
                Verdict::Checked { axioms } => format!("entry {} checked {axioms:?}", e.name),
                Verdict::Skipped(why) => format!("entry {} skipped {why}", e.name),
                Verdict::Failed(_) => format!("entry {} failed", e.name),
                Verdict::Incomplete { holes, uses } => format!(
                    "entry {} incomplete {:?} {uses:?}",
                    e.name,
                    holes.iter().map(|h| &h.name).collect::<Vec<_>>()
                ),
            });
        }
        tauto_syntax::sha256_hex(cache::without_places(&parts.join("\n")).as_bytes())
    }
}

/// What identifies a statement for the work done on it: its text without
/// places (a statement that only moved is the same one), or with them when
/// it has no `anchor_of` to follow it by.
pub fn fingerprint(stmt: &Stmt, positional: bool) -> String {
    let text = format!("{stmt:?}");
    let text = if positional {
        text
    } else {
        cache::without_places(&text)
    };
    tauto_syntax::sha256_hex(text.as_bytes())
}

/// The digest of what the statements up to one left in the kernel, from that
/// of the ones up to the one before and the digest the statement made.
pub fn chain_state(previous: &str, digest: &str) -> String {
    tauto_syntax::sha256_hex(format!("{previous}\n{digest}").as_bytes())
}
