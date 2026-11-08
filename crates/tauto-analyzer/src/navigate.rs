//! What an editor asks of a name (`tauto lsp`): the declaration of a use, a
//! hover, the uses of a declaration, and renaming one.
//!
//! The names come from `index`, which reads the text as written. Types come
//! from `typed`, which loads the program, expands its macros and runs the
//! Nib checker; a position the checkers report inside a macro's output is
//! brought back to the text as written through the `SpanMap`.
//!
//! A rename is made only when every use can be found, and is checked: the
//! edited files are read again and every name must resolve to the same
//! declaration as before.

use std::collections::HashMap;
use std::path::{Path, PathBuf};

use tauto_parol::Span;

mod index;
mod typed;

pub use index::{DefId, Kind, is_keyword};
pub use typed::TypeInfo;

use index::{FileIndex, World, canonical, words};

/// A place in a file, as bytes of its text.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Place {
    pub path: PathBuf,
    pub span: Span,
}

/// The new text of one range.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Edit {
    pub path: PathBuf,
    pub span: Span,
    pub text: String,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Hover {
    pub span: Span,
    /// Markdown.
    pub contents: String,
}

pub struct Navigator<'a> {
    read: &'a dyn Fn(&Path) -> Option<String>,
    world: World<'a>,
    entry: usize,
}

/// The `.taut`, `.tauto` and `.nib` files under `root`, skipping hidden and build
/// directories.
pub fn workspace_files(root: &Path) -> Vec<PathBuf> {
    fn go(dir: &Path, out: &mut Vec<PathBuf>, depth: usize) {
        let Ok(entries) = std::fs::read_dir(dir) else {
            return;
        };
        let mut entries: Vec<_> = entries.flatten().collect();
        entries.sort_by_key(|e| e.file_name());
        for e in entries {
            let path = e.path();
            let name = e.file_name().to_string_lossy().to_string();
            if path.is_dir() {
                if depth < 12
                    && !name.starts_with('.')
                    && name != "target"
                    && name != "node_modules"
                {
                    go(&path, out, depth + 1);
                }
            } else if matches!(
                path.extension().and_then(|x| x.to_str()),
                Some("taut" | "tauto" | "nib")
            ) {
                out.push(path);
            }
        }
    }
    let mut out = Vec::new();
    go(root, &mut out, 0);
    out
}

impl<'a> Navigator<'a> {
    /// Reads `path` and what it imports; `read` gives the text of a file
    /// (an open buffer's, or the disk's).
    pub fn open(path: &Path, read: &'a dyn Fn(&Path) -> Option<String>) -> Option<Self> {
        let mut world = World::new(read);
        let entry = world.load(path)?;
        Some(Navigator { read, world, entry })
    }

    /// As [`Navigator::open`], reading the expressions at `splices` (the bytes of the file
    /// between the delimiters of its `${ … }` and `$n`) as tauto in the scope of the literal
    /// they are written in.
    pub fn open_with_splices(
        path: &Path,
        read: &'a dyn Fn(&Path) -> Option<String>,
        splices: Vec<(u32, u32)>,
    ) -> Option<Self> {
        let mut world = World::new(read).with_splices(path, splices);
        let entry = world.load(path)?;
        Some(Navigator { read, world, entry })
    }

    /// The colour of each name the file writes (declared or used), by what it names; a name that
    /// resolves to nothing is a variable.
    pub fn name_colours(&self) -> Vec<(Span, &'static str)> {
        use index::Kind;
        let colour = |kind: Kind| match kind {
            Kind::Fn
            | Kind::Theorem
            | Kind::Axiom
            | Kind::Definition
            | Kind::Method
            | Kind::Law
            | Kind::Macro => "function",
            Kind::Constructor | Kind::Variant => "enumMember",
            Kind::Inductive
            | Kind::Struct
            | Kind::Enum
            | Kind::Class
            | Kind::Effect
            | Kind::Syntax
            | Kind::Generic => "type",
            Kind::Module => "namespace",
            Kind::Field => "property",
            Kind::Param => "parameter",
            Kind::Local | Kind::PatternVar | Kind::Binder => "variable",
        };
        let index = self.index();
        let mut out = Vec::new();
        for (i, d) in index.defs.iter().enumerate() {
            let kind = colour(
                self.world
                    .def(DefId {
                        file: self.entry,
                        index: i,
                    })
                    .kind,
            );
            out.extend(d.spans.iter().map(|s| (*s, kind)));
        }
        for r in &index.refs {
            out.push((r.span, colour(self.world.def(r.target).kind)));
        }
        out.extend(index.unresolved.iter().map(|(s, _)| (*s, "variable")));
        out
    }

    fn index(&self) -> &FileIndex {
        self.world.file(self.entry)
    }

    pub fn path(&self) -> &Path {
        self.index().path.as_deref().unwrap_or(Path::new(""))
    }

    pub fn text(&self, path: &Path) -> Option<&str> {
        let id = self.world.file_id(path)?;
        Some(self.world.file(id).text.as_str())
    }

    fn site(&self, offset: usize) -> Option<(Span, DefId)> {
        self.index().site_at(self.entry, offset)
    }

    fn place(&self, id: DefId) -> Option<Place> {
        let f = self.world.file(id.file);
        let span = *self.world.def(id).spans.first()?;
        Some(Place {
            path: f.path.clone()?,
            span,
        })
    }

    /// The declaration of the name written at `offset`.
    pub fn definition(&self, offset: usize, types: Option<&TypeInfo>) -> Option<Place> {
        match self.site(offset) {
            Some((_, id)) => self.place(id),
            None => {
                // A name the text does not declare may be one a macro made.
                let (span, name) = self.name_at(offset)?;
                let _ = span;
                let (path, span) = types?.generated(&name)?;
                Some(Place { path, span })
            }
        }
    }

    /// The unresolved name written at `offset`.
    fn name_at(&self, offset: usize) -> Option<(Span, String)> {
        let at = offset as u32;
        self.index()
            .unresolved
            .iter()
            .find(|(s, _)| s.contains(at))
            .map(|(s, n)| (*s, n.trim_end_matches('!').to_string()))
    }

    pub fn hover(&self, offset: usize, types: Option<&TypeInfo>) -> Option<Hover> {
        let at = offset as u32;
        let own = self.path().to_path_buf();
        let call = self
            .index()
            .macro_calls
            .iter()
            .filter(|s| s.contains(at))
            .min_by_key(|s| s.end - s.start)
            .copied();
        let site = self.site(offset).or_else(|| {
            self.index()
                .theorem_keywords
                .iter()
                .find_map(|(span, index)| {
                    span.contains(at).then_some((
                        *span,
                        DefId {
                            file: self.entry,
                            index: *index,
                        },
                    ))
                })
        });
        // A name inside a call is its own; the call is the rest of it.
        let on_macro_name = site.is_some_and(|(_, id)| self.world.def(id).kind == Kind::Macro);
        if let (Some(call), true) = (call, site.is_none() || on_macro_name) {
            let run = types.and_then(|t| t.expansion_at(&own, call));
            let mut md = String::new();
            if let Some((_, id)) = site {
                md.push_str(&self.describe(id, None, None));
                md.push_str("\n\n");
            }
            match run {
                Some(r) => {
                    let e = r.expansion;
                    md.push_str(&format!(
                        "expands to ({} steps):\n\n```tauto\n{}\n```",
                        e.steps,
                        without_scopes(e.output.trim_end())
                    ));
                }
                None => md.push_str("macro call"),
            }
            let span = site.map_or(call, |(s, _)| s);
            return Some(Hover { span, contents: md });
        }
        let (span, id) = site?;
        let d = self.world.def(id);
        let is_decl = d.spans.contains(&span);
        let ty = types.and_then(|t| match (is_decl, d.site) {
            (true, Some(s)) => t.local(&own, &d.name, s),
            _ => t.term(&own, span),
        });
        let mut contents = self.describe(id, ty, Some(&own));
        if d.kind == Kind::Theorem
            && let Some(types) = types
            && let Some(path) = &self.world.file(id.file).path
            && let Some(declaration) = d.spans.first()
            && let Some(proof) = types.proof_at(path, *declaration)
        {
            // Indentation preserves proof layout without interpreting source text as Markdown.
            contents.push_str("\n\n");
            for line in proof.lines() {
                contents.push_str("    ");
                contents.push_str(line);
                contents.push('\n');
            }
        }
        Some(Hover { span, contents })
    }

    fn describe(&self, id: DefId, ty: Option<String>, from: Option<&Path>) -> String {
        let d = self.world.def(id);
        let mut md = format!("```tauto\n{}\n```\n\n_{}_", d.signature, d.kind.label());
        if id.file < 2 {
            md.push_str(" · prelude");
        } else if let (Some(p), Some(from)) = (&self.world.file(id.file).path, from)
            && canonical(p) != canonical(from)
        {
            md.push_str(&format!(
                " · `{}`",
                p.file_name()
                    .map_or(String::new(), |n| n.to_string_lossy().to_string())
            ));
        }
        if let Some(t) = ty
            && d.declared.as_deref() != Some(t.as_str())
        {
            md.push_str(&format!("\n\ntype: `{t}`"));
        }
        md
    }

    /// The workspace files that see the file `def` is in (and it).
    fn users(&mut self, def_file: usize, workspace: &[PathBuf]) -> Vec<usize> {
        let mut out = vec![self.entry];
        if def_file != self.entry && def_file >= 2 && !out.contains(&def_file) {
            out.push(def_file);
        }
        for p in workspace {
            if let Some(id) = self.world.load(p)
                && !out.contains(&id)
                && self.world.file(id).closure.contains(&def_file)
            {
                out.push(id);
            }
        }
        out
    }

    /// Every place the declaration of the name at `offset` is used.
    pub fn references(
        &mut self,
        offset: usize,
        with_declaration: bool,
        workspace: &[PathBuf],
    ) -> Vec<Place> {
        let Some((_, id)) = self.site(offset) else {
            return Vec::new();
        };
        let exported = self.world.def(id).exported;
        let files = if exported {
            self.users(id.file, workspace)
        } else {
            vec![self.entry]
        };
        let mut out = Vec::new();
        for f in files {
            let idx = self.world.file(f);
            let Some(path) = idx.path.clone() else {
                continue;
            };
            if with_declaration && f == id.file {
                for s in &self.world.def(id).spans {
                    out.push(Place {
                        path: path.clone(),
                        span: *s,
                    });
                }
            }
            for r in idx.refs.iter().filter(|r| r.target == id) {
                out.push(Place {
                    path: path.clone(),
                    span: r.span,
                });
            }
        }
        out
    }

    /// The range and the name to start a rename from, or why there is none.
    pub fn prepare_rename(&self, offset: usize) -> Result<(Span, String), String> {
        let Some((span, id)) = self.site(offset) else {
            return Err(tauto_message::msg!("analyzer-rename-no-name").to_string());
        };
        let d = self.world.def(id);
        if id.file < 2 {
            return Err(tauto_message::msg!("analyzer-rename-prelude", name = &d.name).to_string());
        }
        if let Some(why) = d.pinned {
            return Err(tauto_message::msg!(
                "analyzer-rename-pinned",
                name = &d.name,
                why = tauto_message::msg!(why)
            )
            .to_string());
        }
        Ok((span, d.name.clone()))
    }

    /// The edits that rename the declaration of the name at `offset`.
    pub fn rename(
        &mut self,
        offset: usize,
        new_name: &str,
        workspace: &[PathBuf],
    ) -> Result<Vec<Edit>, String> {
        let (_, old) = self.prepare_rename(offset)?;
        let (_, id) = self
            .site(offset)
            .ok_or_else(|| tauto_message::msg!("analyzer-rename-no-name-here").to_string())?;
        check_name(new_name)?;
        if new_name == old {
            return Ok(Vec::new());
        }
        let exported = self.world.def(id).exported;
        let files = if exported {
            self.users(id.file, workspace)
        } else {
            vec![self.entry]
        };

        // A local is visible in its top-level statement; the rest, everywhere.
        let scope: Option<Span> = if exported {
            None
        } else {
            let at = self.world.def(id).spans[0].start;
            self.index()
                .top_stmts
                .iter()
                .find(|s| s.contains(at))
                .copied()
        };
        let inside = |s: &Span| scope.is_none_or(|sc| sc.contains(s.start));

        let mut edits: Vec<Edit> = Vec::new();
        for &f in &files {
            let idx = self.world.file(f);
            let path = idx.path.clone().ok_or_else(|| {
                tauto_message::msg!("analyzer-rename-file-without-path").to_string()
            })?;
            if idx.broken {
                return Err(tauto_message::msg!(
                    "analyzer-rename-broken-file",
                    path = path.display().to_string()
                )
                .to_string());
            }
            if idx.opaque.iter().any(|(s, w)| *w == old && inside(s)) {
                return Err(tauto_message::msg!(
                    "analyzer-rename-opaque",
                    old = &old,
                    path = path.display().to_string()
                )
                .to_string());
            }
            if let Some((span, _)) = idx
                .unresolved
                .iter()
                .find(|(s, n)| n.trim_end_matches('!') == old && inside(s))
            {
                let (line, _) = line_col(&idx.text, span.start as usize);
                return Err(tauto_message::msg!(
                    "analyzer-rename-unresolved",
                    old = &old,
                    path = path.display().to_string(),
                    line = line
                )
                .to_string());
            }
            if f == id.file {
                for s in &self.world.def(id).spans {
                    edits.push(Edit {
                        path: path.clone(),
                        span: *s,
                        text: new_name.to_string(),
                    });
                }
            }
            for r in idx.refs.iter().filter(|r| r.target == id) {
                if r.approximate {
                    return Err(tauto_message::msg!(
                        "analyzer-rename-approximate",
                        old = &old,
                        path = path.display().to_string()
                    )
                    .to_string());
                }
                edits.push(Edit {
                    path: path.clone(),
                    span: r.span,
                    text: new_name.to_string(),
                });
            }
        }

        // The files of a tote see each other without imports, and the totes
        // that depend on it see its files: the word must not be there.
        if exported {
            for p in self.tote_mates(id.file, workspace) {
                let p = &p;
                let Some(text) = (self.read)(&canonical(p)).or_else(|| (self.read)(p)) else {
                    continue;
                };
                let cp = canonical(p);
                if files.iter().any(|f| {
                    self.world
                        .file(*f)
                        .path
                        .as_deref()
                        .is_some_and(|q| canonical(q) == cp)
                }) {
                    continue;
                }
                if words(&text).any(|w| w == old) {
                    return Err(tauto_message::msg!(
                        "analyzer-rename-tote-mate",
                        old = &old,
                        path = cp.display().to_string(),
                        file = self
                            .world
                            .file(id.file)
                            .path
                            .as_deref()
                            .map_or(String::new(), |q| q.display().to_string())
                    )
                    .to_string());
                }
            }
        }

        self.verify(&files, &edits, new_name)?;
        edits.sort_by(|a, b| (&a.path, a.span.start).cmp(&(&b.path, b.span.start)));
        edits.dedup();
        Ok(edits)
    }

    /// The workspace files that see the declarations of the file without
    /// importing it: the files of its tote and of the totes that depend on it.
    fn tote_mates(&self, def_file: usize, workspace: &[PathBuf]) -> Vec<PathBuf> {
        let Some(path) = &self.world.file(def_file).path else {
            return Vec::new();
        };
        let Some(root) = tote_root(path) else {
            return Vec::new();
        };
        // The dependents, found by reading every manifest in the workspace.
        let mut roots: HashMap<PathBuf, Vec<PathBuf>> = HashMap::new();
        for f in workspace {
            if let Some(r) = tote_root(f) {
                roots.entry(r).or_insert_with_key(|r| {
                    let deps = tauto::manifest::read(r)
                        .map(|m| m.dependencies)
                        .unwrap_or_default();
                    deps.into_iter()
                        .filter_map(|(name, dependency)| {
                            tauto::manifest::dependency_dir(r, &name, &dependency).ok()
                        })
                        .map(|dir| canonical(&dir))
                        .collect()
                });
            }
        }
        let mut seeing = vec![root];
        loop {
            let more: Vec<PathBuf> = roots
                .iter()
                .filter(|(r, deps)| !seeing.contains(r) && deps.iter().any(|d| seeing.contains(d)))
                .map(|(r, _)| r.clone())
                .collect();
            if more.is_empty() {
                break;
            }
            seeing.extend(more);
        }
        workspace
            .iter()
            .filter(|f| tote_root(f).is_some_and(|r| seeing.contains(&r)))
            .cloned()
            .collect()
    }

    /// Applies the edits and reads the edited files again: each must still
    /// parse, and every name must resolve to the declaration it did.
    fn verify(&self, files: &[usize], edits: &[Edit], new_name: &str) -> Result<(), String> {
        let mut texts: HashMap<PathBuf, String> = HashMap::new();
        for e in edits {
            texts
                .entry(e.path.clone())
                .or_insert_with(|| self.text(&e.path).unwrap_or("").to_string());
        }
        for (path, text) in texts.iter_mut() {
            let mut mine: Vec<&Edit> = edits.iter().filter(|e| &e.path == path).collect();
            mine.sort_by_key(|e| std::cmp::Reverse(e.span.start));
            mine.dedup();
            for e in mine {
                let (s, t) = (e.span.start as usize, e.span.end as usize);
                if text.get(s..t).is_none() {
                    return Err(tauto_message::msg!("analyzer-rename-text-changed").to_string());
                }
                text.replace_range(s..t, &e.text);
            }
        }
        let read = |p: &Path| -> Option<String> {
            texts
                .get(&canonical(p))
                .cloned()
                .or_else(|| texts.get(p).cloned())
                .or_else(|| (self.read)(p))
        };
        let mut after = World::new(&read);
        let entry_path = self
            .index()
            .path
            .clone()
            .ok_or_else(|| tauto_message::msg!("analyzer-rename-no-path").to_string())?;
        let entry = after
            .load(&entry_path)
            .ok_or_else(|| tauto_message::msg!("analyzer-rename-edited-not-load").to_string())?;
        for &f in files {
            let Some(path) = self.world.file(f).path.clone() else {
                continue;
            };
            let g = after.load(&path).ok_or_else(|| {
                tauto_message::msg!("analyzer-rename-an-edited-not-load").to_string()
            })?;
            let (before, now) = (self.world.file(f), after.file(g));
            if now.broken {
                return Err(tauto_message::msg!(
                    "analyzer-rename-leaves-syntax-error",
                    path = path.display().to_string()
                )
                .to_string());
            }
            let key = |w: &World, d: DefId| (w.file(d.file).path.clone(), d.index);
            let same = before.refs.len() == now.refs.len()
                && before.unresolved.len() == now.unresolved.len()
                && before.defs.len() == now.defs.len()
                && before
                    .refs
                    .iter()
                    .zip(&now.refs)
                    .all(|(a, b)| key(&self.world, a.target) == key(&after, b.target));
            if !same {
                return Err(tauto_message::msg!(
                    "analyzer-rename-captures",
                    new_name = new_name,
                    path = path.display().to_string()
                )
                .to_string());
            }
        }
        let _ = entry;
        Ok(())
    }
}

/// The directory with the `Tauto.eure` a file is under.
fn tote_root(file: &Path) -> Option<PathBuf> {
    let file = canonical(file);
    file.ancestors()
        .skip(1)
        .find(|d| d.join("Tauto.eure").is_file())
        .map(Path::to_path_buf)
}

/// A macro's output with the scope each name carries (`Eq@1`) left out.
fn without_scopes(output: &str) -> String {
    let mut out = String::new();
    let mut chars = output.chars().peekable();
    let mut last = ' ';
    while let Some(c) = chars.next() {
        if c == '@'
            && (last.is_alphanumeric() || last == '_')
            && chars.peek().is_some_and(char::is_ascii_digit)
        {
            while chars.peek().is_some_and(char::is_ascii_digit) {
                chars.next();
            }
            continue;
        }
        out.push(c);
        last = c;
    }
    out
}

/// `line` and `column` (from 1, in characters) of a byte offset.
fn line_col(text: &str, offset: usize) -> (usize, usize) {
    tauto::report::line_col(text, offset)
}

fn check_name(name: &str) -> Result<(), String> {
    let mut chars = name.chars();
    let ok = chars.next().is_some_and(|c| c.is_alphabetic() || c == '_')
        && chars.all(|c| c.is_alphanumeric() || c == '_');
    if !ok {
        return Err(tauto_message::msg!("analyzer-rename-not-a-name", name = name).to_string());
    }
    if is_keyword(name) {
        return Err(tauto_message::msg!("analyzer-rename-keyword", name = name).to_string());
    }
    Ok(())
}

impl Navigator<'_> {
    /// The offsets of the names this file declares, for tests that rename each.
    #[doc(hidden)]
    pub fn declared_offsets(&self) -> Vec<usize> {
        self.index()
            .defs
            .iter()
            .filter_map(|d| d.spans.first().map(|s| s.start as usize))
            .collect()
    }

    /// The names this file declares, each with where it is written and what it is.
    #[doc(hidden)]
    pub fn declared_kinds(&self) -> Vec<(usize, String, Kind)> {
        self.index()
            .defs
            .iter()
            .filter_map(|d| {
                d.spans
                    .first()
                    .map(|s| (s.start as usize, d.name.clone(), d.kind))
            })
            .collect()
    }

    #[doc(hidden)]
    pub fn dump(&self) -> (usize, Vec<(String, usize, String)>) {
        let idx = self.index();
        let mut m: HashMap<String, (usize, String)> = HashMap::new();
        for (s, n) in &idx.unresolved {
            let (l, _) = line_col(&idx.text, s.start as usize);
            let e = m
                .entry(n.clone())
                .or_insert((0, format!("{}:{l}", self.path().display())));
            e.0 += 1;
        }
        (
            idx.refs.len(),
            m.into_iter().map(|(n, (c, w))| (n, c, w)).collect(),
        )
    }
}
