//! What the queries share and cannot hand each other as outputs: the program as
//! the loader made it and the kernels that checked its statements. The kernel
//! holds `Rc`s, so none of it is `Send`; it lives in a thread-local table keyed
//! by the workspace, and a [`crate::Workspace`] is not `Send` either.
//!
//! None of this is a hidden input of a query: a query reads it only after it
//! has asked, through query-flow, for the texts, fingerprints and states it
//! is a function of, and it keeps a kernel only under the state it was in.

use std::cell::RefCell;
use std::collections::{BTreeMap, HashMap};
use std::path::{Path, PathBuf};
use std::rc::Rc;
use std::sync::Arc;

use tauto::check::{Checker, KernelStatements};
use tauto::program::Loaded;

use crate::queries::Decl;

#[derive(Default)]
pub(crate) struct Session {
    /// The program of the last load.
    pub loaded: Option<Rc<Loaded>>,
    /// What the kernel is given of it, as `tauto check` gives it.
    pub kernel: Option<Rc<KernelStatements>>,
    /// The file and the place in it of each statement, in checking order.
    pub index: Vec<(usize, usize)>,
    /// The kernel after the first `n` statements, for `n` a multiple of the
    /// interval, with the digest of the state it was in. It is used again
    /// only when the statements before are still in that state.
    pub checkpoints: BTreeMap<usize, (String, Checker)>,
    /// The kernel after the statement checked last, the next one's way on.
    pub tip: Option<(usize, String, Checker)>,
    /// Declarations checked before, by the state before, the statement and
    /// the file: a statement given back (a candidate tried and undone) is not
    /// checked again.
    pub memo: HashMap<(String, String, PathBuf), Arc<Decl>>,
    pub stats: crate::Stats,
}

/// How many declarations the memo holds before it is emptied.
pub(crate) const MEMO_LIMIT: usize = 4096;

type Key = (u64, PathBuf);

thread_local! {
    static SESSIONS: RefCell<HashMap<Key, Session>> = RefCell::new(HashMap::new());
    static GENESIS: RefCell<HashMap<bool, Checker>> = RefCell::new(HashMap::new());
}

/// Runs `f` on the session of `entry` in workspace `ws`. `f` must not ask
/// query-flow for anything: it would come back here.
pub(crate) fn with<R>(ws: u64, entry: &Path, f: impl FnOnce(&mut Session) -> R) -> R {
    SESSIONS.with(|s| {
        let mut sessions = s.borrow_mut();
        f(sessions.entry((ws, entry.to_path_buf())).or_default())
    })
}

/// Forgets what was kept for the program of `entry`: its load, kernels and
/// memo. It is made again when asked for.
pub(crate) fn drop_entry(ws: u64, entry: &Path) {
    SESSIONS.with(|s| s.borrow_mut().remove(&(ws, entry.to_path_buf())));
}

pub(crate) fn drop_workspace(ws: u64) {
    SESSIONS.with(|s| s.borrow_mut().retain(|(w, _), _| *w != ws));
}

/// A kernel with only the prelude, made once per thread.
pub(crate) fn genesis(proof_cache: bool) -> Result<Checker, String> {
    GENESIS.with(|g| {
        let mut g = g.borrow_mut();
        if let Some(c) = g.get(&proof_cache) {
            return Ok(c.clone());
        }
        let c = Checker::new(proof_cache)?;
        g.insert(proof_cache, c.clone());
        Ok(c)
    })
}
