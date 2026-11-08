//! What the checkers know of a file once it is loaded: the types the Nib
//! checker found for names and expressions, and the macro runs, whose spans
//! `SpanMap` brings back to the text as written.

use std::path::{Path, PathBuf};
use std::{cell::RefCell, collections::HashMap};

use tauto_parol::Span;

use tauto::macros::{EXPANSION_BASE, Expansion};
use tauto::program::Loaded;
use tauto::surface::{PRELUDE_BASE, Stmt};
use tauto::types::{TypeReport, check_program};

pub struct TypeInfo {
    loaded: Loaded,
    report: TypeReport,
    proofs: RefCell<HashMap<(PathBuf, String), Option<String>>>,
}

/// A macro run, for the hover on its call.
pub struct Run<'a> {
    pub expansion: &'a Expansion,
}

impl TypeInfo {
    /// Loads the file (its text given) with its imports, expands its macros
    /// and checks the types. `None` when the program does not load.
    pub fn build(path: &Path, text: &str) -> Option<TypeInfo> {
        let own = tauto::program::canonical_path(path);
        Self::build_with_source(path, &|p| (p == own).then(|| Ok(text.to_string())))
    }

    /// Loads all open buffers, including unsaved imports, as one editor snapshot.
    pub fn build_with_source(path: &Path, source: &tauto::program::Source<'_>) -> Option<TypeInfo> {
        let dirs = vec![path.parent().unwrap_or(Path::new(".")).to_path_buf()];
        let loaded = tauto::syntax::with_search_dirs(dirs, || {
            tauto::program::load_with_source(path, source)
        })
        .ok()?;
        let report = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            check_program(&loaded.program).with_prelude()
        }))
        .ok()?;
        Some(TypeInfo {
            loaded,
            report,
            proofs: RefCell::default(),
        })
    }

    /// The normal natural proof, computed once per theorem in this snapshot.
    pub fn proof_at(&self, path: &Path, span: Span) -> Option<String> {
        fn find(stmts: &[Stmt], at: u32) -> Option<&str> {
            for stmt in stmts {
                match stmt {
                    Stmt::Theorem(d) if d.span.contains(at) => return Some(d.name.as_str()),
                    Stmt::Mutual { items, .. } => {
                        if let Some(name) = find(items, at) {
                            return Some(name);
                        }
                    }
                    _ => {}
                }
            }
            None
        }
        let own = super::index::canonical(path);
        let index = self
            .loaded
            .files
            .iter()
            .position(|f| super::index::canonical(&f.path) == own)?;
        let name = find(
            &self.loaded.kernel_files[index],
            self.loaded.files[index].base + span.start,
        )?;
        let key = (super::index::canonical(path), name.to_string());
        self.proofs
            .borrow_mut()
            .entry(key)
            .or_insert_with(|| {
                tauto::proof::render_loaded(
                    &self.loaded,
                    path,
                    Some(name),
                    tauto::proof::Format::Natural,
                    tauto::proof::Options::default(),
                )
                .ok()
                .map(|view| view.text)
            })
            .clone()
    }

    fn base(&self, path: &Path) -> Option<u32> {
        let own = super::index::canonical(path);
        self.loaded
            .files
            .iter()
            .find(|f| super::index::canonical(&f.path) == own)
            .map(|f| f.base)
    }

    /// The type of the expression written at `span` of the file.
    pub fn term(&self, path: &Path, span: Span) -> Option<String> {
        let base = self.base(path)?;
        let key = (span.start + base, span.end + base);
        let mut found = self.report.terms.iter().filter_map(|(id, t)| {
            let at = id.span();
            ((at.start, at.end) == key).then(|| t.to_string())
        });
        let first = found.next()?;
        found.all(|t| t == first).then_some(first)
    }

    /// The type of the name `name` bound at `site` (a position in the file).
    pub fn local(&self, path: &Path, name: &str, site: u32) -> Option<String> {
        let base = self.base(path)?;
        let mut found = self.report.locals.iter().filter_map(|((n, id), t)| {
            (n.as_str() == name && id.span().start == site + base).then(|| t.to_string())
        });
        let first = found.next()?;
        found.all(|t| t == first).then_some(first)
    }

    /// The position as written, and its file, of a span the checkers use.
    fn written(&self, at: u32) -> Option<(PathBuf, u32)> {
        let mut at = at;
        while let Some((written, _)) = self.loaded.spans.origin(at) {
            at = written;
        }
        let file = self.loaded.files.iter().rev().find(|f| f.base <= at)?;
        Some((file.path.clone(), at - file.base))
    }

    /// The macro run whose call was written across `span` of the file.
    pub fn expansion_at(&self, path: &Path, span: Span) -> Option<Run<'_>> {
        let own = super::index::canonical(path);
        self.loaded
            .expansions
            .iter()
            .filter(|e| e.parent.is_none())
            .find(|e| {
                let Some((file, start)) = self.written(e.call.start) else {
                    return false;
                };
                super::index::canonical(&file) == own && span.start <= start && start <= span.end
            })
            .map(|expansion| Run { expansion })
    }

    /// Where the macro run that made the top-level declaration `name` was
    /// written: its call, found through the span map.
    pub fn generated(&self, name: &str) -> Option<(PathBuf, Span)> {
        for stmts in &self.loaded.per_file {
            for stmt in stmts {
                let Some((n, span)) = declaration(stmt) else {
                    continue;
                };
                if n != name || span.start < EXPANSION_BASE || span.start >= PRELUDE_BASE {
                    continue;
                }
                // The run that made it, then the call that started the runs
                // it was nested in.
                let (_, mut id) = self.loaded.spans.origin(span.start)?;
                let mut run = self.loaded.expansions.iter().find(|e| e.id == id)?;
                while let Some(parent) = run.parent {
                    id = parent;
                    run = self.loaded.expansions.iter().find(|e| e.id == id)?;
                }
                let (file, start) = self.written(run.call.start)?;
                return Some((
                    file,
                    Span::new(start, start + (run.call.end - run.call.start).max(1)),
                ));
            }
        }
        None
    }
}

fn declaration(stmt: &Stmt) -> Option<(&str, Span)> {
    match stmt {
        Stmt::Fn(f) => Some((&f.name, f.span)),
        Stmt::Theorem(t) | Stmt::Def(t) => Some((&t.name, t.span)),
        Stmt::Inductive(i) => Some((&i.name, i.span)),
        Stmt::Struct(d) | Stmt::Enum(d) => Some((&d.name, d.span)),
        Stmt::Effect(e) => Some((&e.name, e.span)),
        _ => None,
    }
}
