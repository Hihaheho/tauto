//! The queries. The dependency graph, for a program of statements `0..n`:
//!
//! ```text
//! SourceText(file) ─▶ LoadShape ─▶ StmtFp(i) ─┐
//!   (assets)          (parse, expand)         ├─▶ CheckDecl(i) ─▶ StateAfter(i) ─▶ CheckDecl(i+1)
//!                                             │     (one kernel step)  (digest)
//!                      StateAfter(i-1) ───────┘
//! ```
//!
//! `StmtFp` and `StateAfter` are the cut-offs. A statement that only moved, or
//! was reformatted, has the fingerprint it had; a theorem whose proof changed
//! but not its statement leaves the kernel in the state it left it in, so the
//! declarations after it are not checked again. `CheckDecl` is the only query
//! that runs the kernel.

use std::cell::RefCell;
use std::path::{Path, PathBuf};
use std::rc::Rc;
use std::sync::Arc;

use query_flow::{Db, Query, QueryError, asset_key};
use tauto::check::{self, ExpansionInfo, FileEntry};
use tauto::program::{self, canonical_path};

use crate::session::{self, MEMO_LIMIT};

/// The text of a file: an editor's buffer, or the file on disk (which the
/// workspace reads when a query asks for a file it was not given).
#[asset_key(asset = String)]
pub struct SourceText(pub PathBuf);

/// A number the workspace raises to make every load run again, for what a load
/// reads that is not a `SourceText` (the grammars of syntax macros).
#[asset_key(asset = u64)]
pub struct Epoch;

/// What a workspace is configured with, as the queries need it.
#[derive(Clone, Debug, Hash, PartialEq, Eq)]
pub(crate) struct Ctx {
    pub ws: u64,
    pub entry: PathBuf,
    /// Number of statements between kernel checkpoints.
    pub interval: usize,
    pub proof_cache: bool,
}

/// The program as of one load, as data.
pub struct Shape {
    /// Why the program did not load (a file that does not read, an import that
    /// is missing); then there is nothing else.
    pub error: Option<program::LoadError>,
    pub files: Vec<FileShape>,
    pub stmts: Vec<StmtShape>,
    /// What went wrong reading the macros and syntaxes.
    pub macro_failures: Vec<FileEntry>,
    pub expansions: Vec<ExpansionInfo>,
}

pub struct FileShape {
    pub path: PathBuf,
    pub text: Arc<String>,
}

pub struct StmtShape {
    pub fingerprint: String,
    /// Where it starts in its file now (see `check::anchor_of`).
    pub anchor: Option<u32>,
}

#[derive(Clone, Debug, Hash, PartialEq, Eq)]
pub(crate) struct LoadShape(pub Ctx);

impl Query for LoadShape {
    type Output = Shape;

    fn query(self, db: &impl Db) -> Result<Arc<Shape>, QueryError> {
        let ctx = self.0;
        let epoch = db.asset(Epoch)?;
        let failure: RefCell<Option<QueryError>> = RefCell::new(None);
        let source = |path: &Path| -> Option<Result<String, String>> {
            match db.asset(SourceText(path.to_path_buf())) {
                Ok(text) => Some(Ok((*text).clone())),
                Err(QueryError::UserError(e)) => Some(Err(e.to_string())),
                Err(e) => {
                    *failure.borrow_mut() = Some(e);
                    Some(Err(String::new()))
                }
            }
        };
        let previous = session::with(ctx.ws, &ctx.entry, |session| session.loaded.clone());
        let loaded = match previous {
            Some(previous) => program::load_revision(&ctx.entry, &source, &previous),
            None => program::load_with_source(&ctx.entry, &source),
        };
        if let Some(e) = failure.into_inner() {
            return Err(e);
        }
        let _ = epoch;
        // What the kernel is given of the program, as `tauto check` gives it.
        let loaded = loaded.and_then(|l| {
            check::KernelStatements::of(&l)
                .map(|k| (l, k))
                .map_err(program::LoadError::from)
        });
        let (loaded, kernel) = match loaded {
            Ok(l) => l,
            Err(error) => {
                session::with(ctx.ws, &ctx.entry, |s| {
                    s.loaded = None;
                    s.kernel = None;
                    s.index.clear();
                });
                return Ok(Arc::new(Shape {
                    error: Some(error),
                    files: Vec::new(),
                    stmts: Vec::new(),
                    macro_failures: Vec::new(),
                    expansions: Vec::new(),
                }));
            }
        };
        let files = loaded
            .files
            .iter()
            .map(|f| FileShape {
                path: canonical_path(&f.path),
                text: Arc::new(f.text.clone()),
            })
            .collect();
        // What the macro failures of the program change in how every
        // declaration is reported is part of every fingerprint.
        let reported = loaded.program.errors.is_empty();
        let mut stmts = Vec::new();
        let mut index = Vec::new();
        // The statements as `tauto check` gives them to the kernel, in the
        // order it checks them in: a proof may use a lemma written further
        // on in its file. Those of `per_file` are the program as it runs,
        // its classes expanded into dictionaries and what runs as written
        // still in it.
        for (fi, per) in kernel.files.iter().enumerate() {
            for (si, stmt) in per.iter().enumerate() {
                let anchor = check::anchor_of(&loaded, fi, stmt);
                // The fingerprint leaves out places, so that a statement
                // that only moved is not checked again; its text is in it,
                // as a change inside it that the statement does not show
                // (parentheses, spaces) still moves its holes and errors.
                let text = check::text_of(&loaded, fi, stmt).unwrap_or_default();
                let fingerprint = format!(
                    "{reported}:{}:{}",
                    check::fingerprint(stmt, anchor.is_none()),
                    tauto_syntax::sha256_hex(text.as_bytes())
                );
                stmts.push(StmtShape {
                    fingerprint,
                    anchor,
                });
                index.push((fi, si));
            }
        }
        let shape = Shape {
            error: None,
            files,
            macro_failures: check::macro_failures_of(&loaded),
            expansions: check::expansion_infos(&loaded),
            stmts,
        };
        session::with(ctx.ws, &ctx.entry, |s| {
            s.stats.loads += 1;
            s.checkpoints.retain(|&n, _| n <= index.len());
            s.loaded = Some(Rc::new(loaded));
            s.kernel = Some(Rc::new(kernel));
            s.index = index;
        });
        Ok(Arc::new(shape))
    }

    fn output_eq(_old: &Shape, _new: &Shape) -> bool {
        // Recomputed only when a text changed, and carries where everything
        // is now: what is cut off is a statement's fingerprint, below.
        false
    }
}

/// The fingerprint of statement `index`; empty when there is none.
#[derive(Clone, Debug, Hash, PartialEq, Eq)]
pub(crate) struct StmtFp(pub Ctx, pub usize);

impl Query for StmtFp {
    type Output = String;

    fn query(self, db: &impl Db) -> Result<Arc<String>, QueryError> {
        let shape = db.query(LoadShape(self.0))?;
        Ok(Arc::new(
            shape
                .stmts
                .get(self.1)
                .map(|s| s.fingerprint.clone())
                .unwrap_or_default(),
        ))
    }

    fn output_eq(old: &String, new: &String) -> bool {
        old == new
    }
}

/// What the kernel said of one statement.
#[derive(Debug, PartialEq)]
pub struct Decl {
    /// The verdicts, as offsets into their files at the time of checking.
    pub entries: Vec<FileEntry>,
    /// Where the statement started then, to move the verdicts by.
    pub anchor: Option<u32>,
    /// The digest of the kernel after the statement and all before it.
    pub state: String,
    /// A message tells a place in text (a macro expansion's), which a move of
    /// the statement makes wrong: it is checked again when it moves.
    pub positional: bool,
    /// For each place of an expansion a message of a positional statement tells: the span,
    /// the position it was written at and the expansion that made it.
    pub origins: Vec<(u32, u32, u32)>,
    /// The verdicts of a positional statement as the kernel gave them, before they were
    /// placed in the file ([`Decl::moved_entries`]).
    pub given: Vec<tauto::check::Entry>,
}

impl Decl {
    /// The verdicts of this positional statement, checked where it was, now that it is `by`
    /// bytes further on in file `fi` of `loaded`: when each expansion its messages tell a
    /// place of was made again (at the same span, by the same expansion, written where it
    /// was or as far further on), its verdicts read as they did, placed again.
    pub fn moved_entries(
        &self,
        loaded: &program::Loaded,
        fi: usize,
        by: i64,
    ) -> Option<Vec<tauto::check::Entry>> {
        let same = self.origins.iter().all(|&(at, written, expansion)| {
            loaded.spans.origin(at).is_some_and(|(w, e)| {
                e == expansion && (w == written || w as i64 == written as i64 + by)
            })
        });
        if !same {
            return None;
        }
        let mut entries = self.given.clone();
        for e in &mut entries {
            move_written(&mut e.verdict, by);
        }
        check::localize_kept(loaded, fi, &mut entries);
        Some(entries)
    }
}

/// The places of a verdict that were written in a file, moved by `by`; those of expansions stay.
fn move_written(v: &mut tauto::check::Verdict, by: i64) {
    use tauto::check::Verdict;
    let at = |s: tauto_parol::Span| tauto::surface::shift::place(s, by);
    match v {
        Verdict::Failed(d) => {
            d.span = d.span.map(at);
            for a in &mut d.also {
                a.span = a.span.map(at);
            }
        }
        Verdict::Incomplete { holes, .. } => {
            for h in holes {
                h.span = at(h.span);
            }
        }
        _ => {}
    }
}

pub(crate) const GENESIS_STATE: &str = "prelude";

/// The kernel after statement `index`, as a digest.
#[derive(Clone, Debug, Hash, PartialEq, Eq)]
pub(crate) struct StateAfter(pub Ctx, pub usize);

impl Query for StateAfter {
    type Output = String;

    fn query(self, db: &impl Db) -> Result<Arc<String>, QueryError> {
        let decl = db.query(CheckDecl(self.0, self.1))?;
        Ok(Arc::new(decl.state.clone()))
    }

    fn output_eq(old: &String, new: &String) -> bool {
        old == new
    }
}

/// A kernel kept after `.0` statements, in the state with this digest.
type Kept = (usize, String);

/// Where the kernel for a statement starts from.
enum Start {
    Tip,
    Checkpoint(usize),
    Genesis,
}

#[derive(Clone, Debug, Hash, PartialEq, Eq)]
pub(crate) struct CheckDecl(pub Ctx, pub usize);

impl Query for CheckDecl {
    type Output = Decl;

    fn query(self, db: &impl Db) -> Result<Arc<Decl>, QueryError> {
        let CheckDecl(ctx, i) = self;
        let fp = db.query(StmtFp(ctx.clone(), i))?;
        let prev: Arc<String> = if i == 0 {
            Arc::new(GENESIS_STATE.to_string())
        } else {
            db.query(StateAfter(ctx.clone(), i - 1))?
        };
        let start = start_for(db, &ctx, i, &prev)?;
        let decl = session::with(ctx.ws, &ctx.entry, |s| {
            check_one(&ctx, s, i, &prev, &fp, start)
        })
        .map_err(|e| QueryError::from(std::io::Error::other(e)))?;
        Ok(decl)
    }

    fn output_eq(old: &Decl, new: &Decl) -> bool {
        old == new
    }
}

/// Where to start the kernel for the state after `i` statements (which is
/// `prev`): the one the last statement left, or the latest checkpoint whose
/// state is still the state there.
fn start_for(db: &impl Db, ctx: &Ctx, i: usize, prev: &str) -> Result<Start, QueryError> {
    let (tip, kept): (Option<Kept>, Vec<Kept>) = session::with(ctx.ws, &ctx.entry, |s| {
        (
            s.tip.as_ref().map(|t| (t.0, t.1.clone())),
            s.checkpoints
                .iter()
                .map(|(n, (st, _))| (*n, st.clone()))
                .collect(),
        )
    });
    if tip.is_some_and(|(n, st)| n == i && st == prev) {
        return Ok(Start::Tip);
    }
    for (n, st) in kept.into_iter().rev().filter(|(n, _)| *n <= i) {
        let expected = if n == i {
            prev.to_string()
        } else {
            (*db.query(StateAfter(ctx.clone(), n - 1))?).clone()
        };
        if expected == st {
            return Ok(Start::Checkpoint(n));
        }
    }
    Ok(Start::Genesis)
}

/// The kernel brought up to `i` statements from `start`, with the number of
/// statements it has and the digest of its state.
fn bring_up(
    ctx: &Ctx,
    s: &mut session::Session,
    i: usize,
    start: Start,
    loaded: &program::Loaded,
    kernel: &check::KernelStatements,
) -> Result<(check::Checker, usize, String), String> {
    let (mut checker, mut applied, mut state) = match start {
        Start::Tip => {
            let (n, st, c) = s.tip.take().expect("the tip was seen");
            (c, n, st)
        }
        Start::Checkpoint(n) => {
            let (st, c) = &s.checkpoints[&n];
            (c.clone(), n, st.clone())
        }
        Start::Genesis => (
            session::genesis(ctx.proof_cache)?,
            0,
            GENESIS_STATE.to_string(),
        ),
    };
    checker.show_syntax(loaded);
    // The statements between the kernel and `i`, only to bring it up.
    while applied < i {
        let (rf, rs) = s.index[applied];
        let declared = checker.declare_from(kernel, rf, rs);
        state = check::chain_state(&state, &declared.digest);
        applied += 1;
        s.stats.replayed += 1;
        if applied.is_multiple_of(ctx.interval) {
            s.checkpoints
                .insert(applied, (state.clone(), checker.clone()));
        }
    }
    Ok((checker, applied, state))
}

/// The constants in scope after the whole program, for `suggest` and
/// `library`.
#[derive(Clone, Debug, Hash, PartialEq, Eq)]
pub(crate) struct Library(pub Ctx);

impl Query for Library {
    type Output = Vec<check::LibEntry>;

    fn query(self, db: &impl Db) -> Result<Arc<Vec<check::LibEntry>>, QueryError> {
        let ctx = self.0;
        let shape = db.query(LoadShape(ctx.clone()))?;
        let n = shape.stmts.len();
        let state: Arc<String> = if n == 0 {
            Arc::new(GENESIS_STATE.to_string())
        } else {
            db.query(StateAfter(ctx.clone(), n - 1))?
        };
        let start = start_for(db, &ctx, n, &state)?;
        let library = session::with(ctx.ws, &ctx.entry, |s| {
            let loaded = s
                .loaded
                .clone()
                .ok_or_else(|| tauto_message::msg!("analyzer-not-loaded").to_string())?;
            let kernel = s
                .kernel
                .clone()
                .ok_or_else(|| tauto_message::msg!("analyzer-not-loaded").to_string())?;
            let (checker, _, state) = bring_up(&ctx, s, n, start, &loaded, &kernel)?;
            let library = checker.library();
            s.tip = Some((n, state, checker));
            Ok::<_, String>(library)
        })
        .map_err(|e| QueryError::from(std::io::Error::other(e)))?;
        Ok(Arc::new(library))
    }

    // A library is compared by the state it comes from, which the query
    // depends on: it is made again only when that changed.
    fn output_eq(_old: &Vec<check::LibEntry>, _new: &Vec<check::LibEntry>) -> bool {
        false
    }
}

/// Declares statement `i` on a kernel brought up to it, or takes what was said
/// of the same statement in the same state before.
fn check_one(
    ctx: &Ctx,
    s: &mut session::Session,
    i: usize,
    prev: &str,
    fp: &str,
    start: Start,
) -> Result<Arc<Decl>, String> {
    let loaded = s
        .loaded
        .clone()
        .ok_or_else(|| tauto_message::msg!("analyzer-not-loaded").to_string())?;
    let kernel = s
        .kernel
        .clone()
        .ok_or_else(|| tauto_message::msg!("analyzer-not-loaded").to_string())?;
    let &(fi, si) = s
        .index
        .get(i)
        .ok_or_else(|| tauto_message::msg!("analyzer-no-such-statement").to_string())?;
    let file = canonical_path(&loaded.files[fi].path);
    let key = (prev.to_string(), fp.to_string(), file.clone());
    if let Some(d) = s.memo.get(&key) {
        s.stats.memo_hits += 1;
        return Ok(d.clone());
    }
    let (mut checker, _, state) = bring_up(ctx, s, i, start, &loaded, &kernel)?;
    let stmt = &kernel.files[fi][si];
    let declared = checker.declare_from(&kernel, fi, si);
    s.stats.checked += 1;
    let state = check::chain_state(&state, &declared.digest);
    let mut entries = declared.entries;
    check::kept_entries(&loaded, &mut entries);
    let given = entries.clone();
    let origins: Vec<(u32, u32, u32)> = entries
        .iter()
        .filter_map(|entry| match &entry.verdict {
            tauto::check::Verdict::Failed(d) => d.span,
            _ => None,
        })
        .filter_map(|span| {
            let (written, expansion) = loaded.spans.origin(span.start)?;
            Some((span.start, written, expansion))
        })
        .collect();
    let positional = check::localize_entries(&loaded, fi, &mut entries);
    let mut entries: Vec<FileEntry> = entries
        .into_iter()
        .map(|entry| FileEntry {
            file: file.clone(),
            entry,
        })
        .collect();
    kernel.explain(&mut entries);
    let decl = Arc::new(Decl {
        entries,
        anchor: check::anchor_of(&loaded, fi, stmt),
        state: state.clone(),
        positional,
        given: if positional { given } else { Vec::new() },
        origins,
    });
    if (i + 1).is_multiple_of(ctx.interval) {
        s.checkpoints
            .insert(i + 1, (state.clone(), checker.clone()));
    }
    s.tip = Some((i + 1, state, checker));
    if !positional {
        if s.memo.len() >= MEMO_LIMIT {
            s.memo.clear();
        }
        s.memo.insert(key, decl.clone());
    }
    Ok(decl)
}
