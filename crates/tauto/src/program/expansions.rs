//! What the expansion of the first files of a program left, kept for the next reading of a
//! program that begins with the same files (`docs/design/analysis-cache.md`). An editor reads
//! the program of the file it shows again at every edit of that file; the files it imports, read
//! before it, are expanded once.
//!
//! What is kept is used only for files given to the expansion exactly as they were then: the
//! same statements (spans included, so at the same places of the program), what each file's
//! short names mean, its module and the time its expansion may take. A syntax's tables are read
//! once for the thread and kept by the hash of their grammar; an expansion that looked for
//! tables and did not find them is not kept, since the tables may be made later.

use std::cell::{Cell, RefCell};
use std::collections::HashMap;
use std::time::Duration;

use crate::macros::expand::{Saved, expand_files_resuming_bound};
use crate::macros::{Options, Output};
use crate::surface::Stmt;

/// How many expansions are kept: one for each of the last files read.
const KEPT: usize = 8;

/// What file `i` was given to the expansion as.
#[derive(PartialEq)]
struct Given {
    stmts: Vec<Stmt>,
    seeing: HashMap<String, String>,
    module: Option<String>,
    limit: Option<(String, Duration)>,
    standard: bool,
}

struct Kept {
    given: Vec<Given>,
    saved: Saved,
}

thread_local! {
    static KEEP: Cell<bool> = const { Cell::new(false) };
    /// The most recently used last.
    static KEPT_EXPANSIONS: RefCell<Vec<Kept>> = const { RefCell::new(Vec::new()) };
}

/// Whether the programs this thread reads keep what the expansion of the files before the last
/// one left, for the next reading of a program that begins with the same files (an editor's
/// server); off by default.
pub fn keep_expansions(keep: bool) {
    KEEP.with(|k| k.set(keep));
    crate::surface::parsed::keep(keep);
    tauto_macro::macros::expand::keep_steps(keep);
    if !keep {
        KEPT_EXPANSIONS.with(|k| k.borrow_mut().clear());
    }
}

/// Whether this thread keeps what it reads ([`keep_expansions`]).
pub fn keeps_expansions() -> bool {
    KEEP.with(Cell::get)
}

/// Expands the files, going on from what was kept of the longest run of first files given the
/// same, and keeping what is left before the last file.
pub(super) fn expand(
    files: Vec<Vec<Stmt>>,
    seeing: Vec<HashMap<String, String>>,
    modules: Vec<String>,
    limits: Vec<(String, Duration)>,
    bindings: Option<tauto_surface::resolve::Resolver>,
    standard_files: Vec<bool>,
) -> Output {
    let opts = Options::default();
    // A revision of a program (`load_revision`) is given the identities of the one before; the
    // files kept from before already have theirs, so it goes on from them when they are kept.
    if bindings.is_some() && !KEEP.with(Cell::get) {
        return crate::macros::expand::expand_files_resuming_bound(
            files,
            &opts,
            seeing,
            modules,
            limits,
            None,
            None,
            bindings,
            standard_files,
        )
        .0;
    }
    if !KEEP.with(Cell::get) || files.is_empty() {
        return expand_files_resuming_bound(
            files,
            &opts,
            seeing,
            modules,
            limits,
            None,
            None,
            bindings,
            standard_files,
        )
        .0;
    }
    let given: Vec<Given> = files
        .iter()
        .enumerate()
        .map(|(i, stmts)| Given {
            stmts: stmts.clone(),
            seeing: seeing.get(i).cloned().unwrap_or_default(),
            module: modules.get(i).cloned(),
            limit: limits.get(i).cloned(),
            standard: standard_files.get(i).copied().unwrap_or(false),
        })
        .collect();
    let last = files.len() - 1;
    let from = KEPT_EXPANSIONS.with(|k| {
        let mut kept = k.borrow_mut();
        let found = kept
            .iter()
            .enumerate()
            .filter(|(_, e)| e.given.len() <= given.len() && given[..e.given.len()] == e.given[..])
            .max_by_key(|(_, e)| e.given.len())
            .map(|(j, _)| j)?;
        let e = kept.remove(found);
        let saved = e.saved.clone();
        kept.push(e);
        Some(saved)
    });
    let resumed = from.as_ref().map(Saved::files);
    let missed = crate::syntax::tables_missed();
    let (out, saved) = expand_files_resuming_bound(
        files,
        &opts,
        seeing,
        modules,
        limits,
        from,
        resumed.is_none_or(|r| r < last).then_some(last),
        if resumed.is_none() { bindings } else { None },
        standard_files,
    );
    let complete = crate::syntax::tables_missed() == missed;
    if let Some(saved) = saved
        && complete
    {
        let mut given = given;
        given.truncate(last);
        KEPT_EXPANSIONS.with(|k| {
            let mut kept = k.borrow_mut();
            kept.retain(|e| e.given != given);
            if kept.len() >= KEPT {
                kept.remove(0);
            }
            kept.push(Kept { given, saved });
        });
    }
    out
}
