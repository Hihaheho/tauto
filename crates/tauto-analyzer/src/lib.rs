//! The editor features of Tauto (`navigate`, `assist`, `editor`) and the incremental
//! checker they run on.
//!
//! An incremental checker for Tauto, on [query-flow]: a [`Workspace`] holds the
//! text of the files it is told about (an editor's buffers first, the disk
//! otherwise) and answers `check`, `goals`, `try` and `fill` for them, checking
//! again only the declarations whose text, or whose predecessors' statements,
//! changed.
//!
//! It does not check anything itself. A declaration is declared by the same
//! kernel as `tauto check` (the named and independent core checkers in
//! `tauto-kernel`), one statement at a time from a copy of the state left by
//! unchanged preceding statements. What the queries decide is only what need not
//! be asked of the kernel again. The queries and their cut-offs are described in
//! `crates/tauto-analyzer/src/queries.rs`; the answers are the [`Report`]s of
//! `tauto::report`, the ones `tauto check --json` and `goals` lay out.
//!
//! [query-flow]: https://crates.io/crates/query-flow

pub mod assist;
pub mod editor;
pub mod lemma_search;
pub mod navigate;
mod queries;
mod session;

use std::collections::{BTreeMap, BTreeSet};
use std::marker::PhantomData;
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicU64, Ordering};

use query_flow::{DurabilityLevel, QueryError, QueryRuntime};
use tauto::check::{FileEntry, Verdict};
use tauto::program::canonical_path;
use tauto::report::{Attempt, Hole, Report, find_hole, splice};
use tauto_parol::Span;

use queries::{CheckDecl, Ctx, Epoch, Library, LoadShape, SourceText};

pub use queries::{Decl, Shape};

/// How much work a workspace has done for a program, to see that an edit cost
/// what it should.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct Stats {
    /// Times the files were read and the program expanded.
    pub loads: usize,
    /// Statements checked to compute the requested answer.
    pub checked: usize,
    /// Earlier statements replayed to reconstruct the kernel state for a check.
    pub replayed: usize,
    /// Declarations answered from what was said of the same statement in the
    /// same state before.
    pub memo_hits: usize,
}

#[derive(Debug, Clone, Copy)]
pub struct Options {
    /// Number of statements between kernel checkpoints. Smaller intervals use
    /// more memory; larger intervals require more replay.
    pub checkpoint_interval: usize,
    /// Take proofs checked before from `tauto`'s proof cache on disk
    /// (`TAUTO_CACHE`), as `tauto check` does. Without it, a kernel brought up
    /// to a statement after an edit checks the proofs it replays again.
    pub proof_cache: bool,
}

impl Default for Options {
    fn default() -> Self {
        Options {
            checkpoint_interval: 8,
            proof_cache: true,
        }
    }
}

static NEXT_WORKSPACE: AtomicU64 = AtomicU64::new(1);

/// The files of a program and what has been checked of them. Not `Send`: the
/// kernels it keeps are not.
pub struct Workspace {
    id: u64,
    options: Options,
    runtime: QueryRuntime,
    /// The files whose text was given with [`set_text`](Workspace::set_text),
    /// the others being read from disk.
    buffers: BTreeSet<PathBuf>,
    epoch: u64,
    _local: PhantomData<*const ()>,
}

impl Default for Workspace {
    fn default() -> Self {
        Workspace::new()
    }
}

impl Drop for Workspace {
    fn drop(&mut self) {
        session::drop_workspace(self.id);
    }
}

impl Workspace {
    pub fn new() -> Workspace {
        Workspace::with_options(Options::default())
    }

    pub fn with_options(options: Options) -> Workspace {
        let runtime = QueryRuntime::new();
        runtime.resolve_asset(Epoch, 0, DurabilityLevel::Static);
        Workspace {
            id: NEXT_WORKSPACE.fetch_add(1, Ordering::Relaxed),
            options: Options {
                checkpoint_interval: options.checkpoint_interval.max(1),
                ..options
            },
            runtime,
            buffers: BTreeSet::new(),
            epoch: 0,
            _local: PhantomData,
        }
    }

    fn ctx(&self, entry: &Path) -> Ctx {
        Ctx {
            ws: self.id,
            entry: canonical_path(entry),
            interval: self.options.checkpoint_interval,
            proof_cache: self.options.proof_cache,
        }
    }

    /// The text of a file as an editor holds it, which wins over the disk
    /// until [`refresh`](Workspace::refresh).
    pub fn set_text(&mut self, path: &Path, text: String) {
        let path = canonical_path(path);
        self.runtime
            .resolve_asset(SourceText(path.clone()), text, DurabilityLevel::Volatile);
        self.buffers.insert(path);
    }

    /// The file as it is on disk: after the editor closed it, or after
    /// something else changed it.
    pub fn refresh(&mut self, path: &Path) {
        let path = canonical_path(path);
        self.buffers.remove(&path);
        self.read_disk(path);
    }

    /// Forgets the kernels and the program kept for `entry` (an editor closed
    /// it): they are the most of what a workspace holds. Asking about it again
    /// loads and checks it again.
    pub fn forget(&mut self, entry: &Path) {
        let ctx = self.ctx(entry);
        session::drop_entry(self.id, &ctx.entry);
        // The queries' answers say what the forgotten session had; they are
        // made again from the next load.
        self.reload();
    }

    /// Makes every program load again, for what a load reads without being
    /// told: the grammars of syntax macros.
    pub fn reload(&mut self) {
        self.epoch += 1;
        self.runtime
            .resolve_asset(Epoch, self.epoch, DurabilityLevel::Static);
    }

    /// The work done for the program of `entry` so far.
    pub fn stats(&self, entry: &Path) -> Stats {
        session::with(self.id, &canonical_path(entry), |s| s.stats)
    }

    /// What `tauto check` says of `entry` and what it imports, as of the texts
    /// the workspace has now. A program that does not load is an error with
    /// its place, when it has one.
    pub fn report(&self, entry: &Path) -> Result<Report, tauto::program::LoadError> {
        let ctx = self.ctx(entry);
        let shape = self.ask(LoadShape(ctx.clone()))?;
        if let Some(error) = &shape.error {
            return Err(error.clone());
        }
        let mut entries: Vec<FileEntry> = Vec::new();
        for (i, stmt) in shape.stmts.iter().enumerate() {
            let query = CheckDecl(ctx.clone(), i);
            let mut decl = self.ask(query.clone())?;
            let mut delta = moved(stmt.anchor, decl.anchor);
            if decl.positional && delta != 0 {
                // Placed again from what the kernel said where the statement was, when
                // the expansions it tells places of were made again; checked again if not.
                let again = session::with(ctx.ws, &ctx.entry, |s| {
                    let loaded = s.loaded.as_ref()?;
                    let &(fi, _) = s.index.get(i)?;
                    let file = canonical_path(&loaded.files[fi].path);
                    let placed = decl.moved_entries(loaded, fi, delta)?;
                    Some(
                        placed
                            .into_iter()
                            .map(|entry| FileEntry {
                                file: file.clone(),
                                entry,
                            })
                            .collect::<Vec<_>>(),
                    )
                });
                if let Some(placed) = again {
                    entries.extend(placed);
                    continue;
                }
                self.runtime.invalidate(&query);
                decl = self.ask(query)?;
                delta = moved(stmt.anchor, decl.anchor);
            }
            entries.extend(decl.entries.iter().map(|e| shifted(e, delta)));
        }
        entries.extend(shape.macro_failures.iter().cloned());
        let sources: BTreeMap<PathBuf, String> = shape
            .files
            .iter()
            .map(|f| (f.path.clone(), (*f.text).clone()))
            .collect();
        let library = self.ask(Library(ctx.clone()))?;
        let source_names = session::with(ctx.ws, &ctx.entry, |session| {
            session
                .loaded
                .as_ref()
                .map(|loaded| loaded.source_names())
                .unwrap_or_default()
        });
        Ok(
            Report::from_parts(entries, shape.expansions.clone(), sources)
                .with_library((*library).clone())
                .with_source_names(source_names),
        )
    }

    /// Runs a query. A file nobody gave the text of is read from disk when a
    /// query first asks for it (it is pending then), and the query asked again.
    fn ask<Q: query_flow::Query>(&self, q: Q) -> Result<std::sync::Arc<Q::Output>, String> {
        loop {
            match self.runtime.query(q.clone()) {
                Err(QueryError::Suspend { .. }) => {
                    let pending = self.runtime.pending_assets_of::<SourceText>();
                    if pending.is_empty() {
                        return Err(
                            tauto_message::msg!("analyzer-query-waits-not-file").to_string()
                        );
                    }
                    for SourceText(path) in pending {
                        self.read_disk(path);
                    }
                }
                Err(e) => return Err(e.to_string()),
                Ok(out) => return Ok(out),
            }
        }
    }

    fn read_disk(&self, path: PathBuf) {
        match std::fs::read_to_string(&path) {
            Ok(text) => {
                self.runtime
                    .resolve_asset(SourceText(path), text, DurabilityLevel::Volatile)
            }
            Err(e) => self.runtime.resolve_asset_error(
                SourceText(path.clone()),
                std::io::Error::new(e.kind(), format!("{}: {e}", path.display())),
                DurabilityLevel::Volatile,
            ),
        }
    }

    /// The holes of `path` (not of the files it imports), or the one named.
    pub fn goals(&self, path: &Path, hole: Option<&str>) -> Result<(Report, Vec<Hole>), String> {
        let report = self.report(path)?;
        let holes = match hole {
            Some(name) => vec![find_hole(&report, path, name)?],
            None => {
                let root = canonical_path(path);
                report
                    .holes()
                    .into_iter()
                    .filter(|h| h.file == root)
                    .collect()
            }
        };
        Ok((report, holes))
    }

    /// `expr` in place of `?hole` in `path`, checked; the text of the file is
    /// as it was after. See `tauto::report::try_fill`, which this answers
    /// the same way without checking the file again.
    pub fn try_fill(&mut self, path: &Path, hole: &str, expr: &str) -> Result<Attempt, String> {
        self.attempt(path, hole, expr, false)
    }

    /// [`try_fill`](Workspace::try_fill), and when the candidate is accepted
    /// the workspace goes on with it as the text of the file. Writing it to
    /// disk, or sending it to an editor, is up to the caller (`candidate`).
    pub fn fill(&mut self, path: &Path, hole: &str, expr: &str) -> Result<Attempt, String> {
        self.attempt(path, hole, expr, true)
    }

    fn attempt(
        &mut self,
        path: &Path,
        name: &str,
        expr: &str,
        keep: bool,
    ) -> Result<Attempt, String> {
        let before = self.report(path)?;
        let hole = find_hole(&before, path, name)?;
        let candidate = splice(&before, &hole, expr)?;
        let file = hole.file.clone();
        let original = before.source(&file).to_string();
        let was_buffer = self.buffers.contains(&file);
        self.set_text(&file, candidate.clone());
        let after = self.report(path);
        let accepted = after.as_ref().is_ok_and(|r| {
            !r.entries
                .iter()
                .any(|e| e.entry.name.as_str() == hole.declaration && e.entry.failed())
        });
        if keep && accepted {
            // The candidate stays the text of the file.
        } else if was_buffer {
            self.set_text(&file, original);
        } else {
            self.refresh(&file);
        }
        let report = after.map_err(|e| {
            tauto_message::msg!(
                "analyzer-fill-no-longer-reads",
                expr = expr,
                name = name,
                error = e.to_string()
            )
            .to_string()
        })?;
        let before_holes = before
            .holes()
            .into_iter()
            .filter(|h| h.file == file)
            .collect();
        Ok(Attempt {
            hole,
            candidate,
            report,
            before: before_holes,
            accepted,
        })
    }
}

/// By how much a statement moved since it was checked.
fn moved(now: Option<u32>, then: Option<u32>) -> i64 {
    match (now, then) {
        (Some(now), Some(then)) => now as i64 - then as i64,
        _ => 0,
    }
}

fn shifted(e: &FileEntry, delta: i64) -> FileEntry {
    let mut e = e.clone();
    if delta != 0 {
        match &mut e.entry.verdict {
            Verdict::Failed(d) => {
                d.span = d.span.map(|s| move_span(s, delta));
                for a in &mut d.also {
                    a.span = a.span.map(|s| move_span(s, delta));
                }
            }
            Verdict::Incomplete { holes, .. } => {
                for h in holes {
                    h.span = move_span(h.span, delta);
                }
            }
            _ => {}
        }
    }
    e
}

fn move_span(s: Span, delta: i64) -> Span {
    let at = |x: u32| (x as i64 + delta).max(0) as u32;
    Span::new(at(s.start), at(s.end))
}
