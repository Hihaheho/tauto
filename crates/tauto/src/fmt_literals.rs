//! `tauto fmt` inside the text of a syntax: a literal of a syntax that registers a `fmt` function
//! (`syntax s … with fmt f = …`) is laid out by that function, and so is the body of a fenced block
//! (```` ```s ````) in a comment. Both are found in the syntax tree of the file alone
//! ([`crate::surface::lexical`] and [`crate::surface::fence`]), wherever they are: in ordinary
//! code, in a `quote`, in a macro, in a function nothing uses, and in code that does not check or
//! expand. Only when one of them could be laid out is the program read, for the functions and
//! the grammars. Everything else in the file, and the literals of the other syntaxes, are left to
//! [`crate::fmt`].

use std::collections::{HashMap, HashSet};
use std::path::Path;

use tauto_message::{Message, msg};

use crate::fmt::WIDTH;
use crate::registered::Library;
use crate::surface::fence::{Fence, fences};
use crate::surface::{LitForm, LitSite, Stmt, lexical};
use crate::syntax::Role;

type TablesOf = HashMap<String, std::sync::Arc<tauto_syntax::Tables>>;

/// The text of the file at `path` with the bodies of its literals and comment fences laid out,
/// and why some were not. A file that does not parse, or whose imports do not load, has nothing
/// laid out, and the reason is a warning; so is each literal and fence that is left as written.
/// A program that does not check or expand still has its literals laid out: only the functions
/// the syntaxes register are run. The line ends of the file are kept.
pub fn format_literals(path: &Path, source: &str) -> Result<(String, Vec<String>), Message> {
    let dirs = vec![path.parent().unwrap_or(Path::new(".")).to_path_buf()];
    crate::syntax::with_search_dirs(dirs, || format_literals_here(path, source))
}

fn format_literals_here(path: &Path, source: &str) -> Result<(String, Vec<String>), Message> {
    let mut lex = lexical(source);
    if let Some(why) = &lex.error {
        let message = msg!("tauto-fmt-parse-failed", why = why);
        return Ok((source.to_string(), vec![warn(source, path, 0, &message)]));
    }
    let found = fences(source, &lex.comments);
    if found.is_empty() && !lex.literals.iter().any(|s| !s.grammar) {
        return Ok((source.to_string(), Vec::new()));
    }
    let loaded = match crate::program::load_with_text_in(path, Some(source)) {
        Ok(loaded) => loaded,
        Err(why) => {
            let message = msg!("tauto-fmt-load-failed", why = why);
            return Ok((source.to_string(), vec![warn(source, path, 0, &message)]));
        }
    };
    let mut name_edits = Vec::new();
    resolve_literal_names(path, source, &loaded, &mut lex, &mut name_edits);
    let mut sites: Vec<Site<'_>> = lex
        .literals
        .iter()
        .filter(|s| !s.grammar && s.lit.name.is_some())
        .map(Site::Lit)
        .collect();
    sites.extend(found.iter().map(Site::Fence));
    if sites.is_empty() {
        return Ok((apply_edits(source, name_edits), Vec::new()));
    }
    sites.sort_by_key(Site::at);
    laid_out(path, source, sites, Some(&loaded), name_edits)
}

enum Site<'a> {
    Lit(&'a LitSite),
    Fence(&'a Fence),
}

impl Site<'_> {
    fn name(&self) -> &str {
        match self {
            Site::Lit(s) => s.lit.name.as_deref().unwrap_or_default(),
            Site::Fence(f) => &f.name,
        }
    }

    fn at(&self) -> usize {
        match self {
            Site::Lit(s) => s.lit.span.start as usize,
            Site::Fence(f) => f.opening.0,
        }
    }
}

fn laid_out(
    path: &Path,
    source: &str,
    sites: Vec<Site<'_>>,
    loaded: Option<&crate::program::Loaded>,
    name_edits: Vec<(usize, usize, String)>,
) -> Result<(String, Vec<String>), Message> {
    let unchanged = || Ok((apply_edits(source, name_edits.clone()), Vec::new()));
    let Some(loaded) = loaded else {
        let message = msg!(
            "tauto-fmt-load-failed",
            why = "cannot resolve literal syntaxes"
        );
        return Ok((source.to_string(), vec![warn(source, path, 0, &message)]));
    };
    // The syntaxes that name a `fmt` function, whether or not the declaration could be read.
    let mut declared = Vec::new();
    for file in &loaded.files {
        if let Ok(program) = crate::surface::parse_program_unresolved_at(&file.text, file.base) {
            grammars(&program.stmts, &mut declared);
        }
    }
    let names: HashSet<&str> = declared
        .iter()
        .filter(|d| d.fmt)
        .map(|d| d.name.as_str())
        .collect();
    let sites: Vec<Site<'_>> = sites
        .into_iter()
        .filter(|s| names.contains(s.name()))
        .collect();
    if sites.is_empty() {
        return unchanged();
    }
    let library = match Library::open_lenient(loaded.registration_program(), &loaded.registrations)
    {
        Ok(library) => library,
        Err(why) => {
            let message = msg!("tauto-fmt-load-failed", why = why);
            return Ok((source.to_string(), vec![warn(source, path, 0, &message)]));
        }
    };
    let mut tables: TablesOf = HashMap::new();
    let mut failed: HashMap<String, String> = HashMap::new();
    for u in &loaded.literals {
        tables
            .entry(u.syntax.clone())
            .or_insert_with(|| u.tables.clone());
    }
    for d in &declared {
        if d.fmt && !tables.contains_key(&d.name) {
            match crate::syntax::load_tables(&d.grammar) {
                Ok(t) => {
                    tables.insert(d.name.clone(), t);
                }
                Err(why) => {
                    failed.insert(d.name.clone(), why);
                }
            }
        }
    }
    let mut edits = name_edits;
    let mut warnings = Vec::new();
    for site in sites {
        let name = site.name().to_string();
        let left = |why: &str| warn(source, path, site.at(), &literal_left(&name, why));
        let Some(t) = tables.get(&name) else {
            let why = failed
                .get(&name)
                .cloned()
                .unwrap_or_else(|| msg!("surface-not-a-syntax", name = name.as_str()).to_string());
            warnings.push(left(&why.to_string()));
            continue;
        };
        if !library.has(&name, Role::Fmt) {
            let fallback = msg!("tauto-fmt-not-usable");
            warnings.push(left(
                &library
                    .unbound(&name, Role::Fmt)
                    .unwrap_or(&fallback)
                    .to_string(),
            ));
            continue;
        }
        let target = match target(source, &site) {
            Ok(target) => target,
            Err(why) => {
                warnings.push(left(&why.to_string()));
                continue;
            }
        };
        let width = WIDTH.saturating_sub(target.used).max(20) as u64;
        match library.format(&name, t, &target.text, width) {
            Ok(None) => {}
            Ok(Some(laid)) => match target.rebuild(&laid) {
                Some(raw) if raw != source[target.range.0..target.range.1] => {
                    edits.push((target.range.0, target.range.1, raw));
                }
                Some(_) => {}
                None => warnings.push(left(&msg!("tauto-fmt-does-not-fit").to_string())),
            },
            Err(why) => warnings.push(left(&why.to_string())),
        }
    }
    let out = apply_edits(source, edits);
    Ok((out, warnings))
}

struct Declared {
    name: String,
    grammar: String,
    fmt: bool,
}

fn grammars(stmts: &[Stmt], out: &mut Vec<Declared>) {
    for s in stmts {
        match s {
            Stmt::Syntax {
                name,
                grammar,
                uses,
                ..
            } => out.push(Declared {
                name: name.clone(),
                grammar: grammar.text.clone(),
                fmt: uses.iter().any(|u| u.role == "fmt"),
            }),
            Stmt::Module { items, .. } => grammars(items, out),
            _ => {}
        }
    }
}

fn literal_left(syntax: &str, why: &str) -> String {
    msg!("tauto-fmt-literal-left", syntax = syntax, why = why).to_string()
}

fn warn(source: &str, path: &Path, offset: usize, message: &impl std::fmt::Display) -> String {
    let before = &source[..offset];
    let line = before.matches('\n').count() + 1;
    let col = before.rsplit('\n').next().map_or(0, |l| l.chars().count()) + 1;
    format!("{}:{line}:{col}: {message}", path.display())
}

/// What is laid out: its text as the syntax reads it, the bytes of the file that stand for it,
/// and how the laid-out text goes back into them.
struct Target<'a> {
    text: String,
    range: (usize, usize),
    used: usize,
    how: How<'a>,
}

enum How<'a> {
    Lit {
        site: &'a LitSite,
        eol: &'static str,
    },
    Fence(&'a Fence),
}

fn eol_after(source: &str, at: usize) -> &'static str {
    match source[at..].find('\n') {
        Some(i) if source[..at + i].ends_with('\r') => "\r\n",
        _ => "\n",
    }
}

/// The text of a site as its syntax reads it, with the line ends of the file as `\n`. A block
/// whose lines are less indented than its closing fence, or whose closing fence does not start a
/// line, is refused with the reason.
fn target<'a>(source: &str, site: &Site<'a>) -> Result<Target<'a>, Message> {
    match *site {
        Site::Fence(f) => {
            if !f.closed {
                return Err(msg!("tauto-fmt-fence-unclosed"));
            }
            Ok(Target {
                text: f.text(source),
                range: f.body,
                used: f.prefix.chars().count(),
                how: How::Fence(f),
            })
        }
        Site::Lit(s) => {
            if let Some((why, _)) = &s.lit.error {
                return Err(Message::text(why.to_string()));
            }
            if matches!(s.form, LitForm::Block(_)) && !s.own_line {
                return Err(msg!("tauto-fmt-block-inline"));
            }
            let start = s.lit.span.start as usize;
            let column = |at: usize| {
                source[..at]
                    .rsplit('\n')
                    .next()
                    .map_or(0, |l| l.chars().count())
            };
            let used = match s.form {
                LitForm::Block(_) => s.indent.chars().count(),
                _ => column(s.body.start as usize),
            };
            Ok(Target {
                text: s.lit.text.replace("\r\n", "\n"),
                range: (s.body.start as usize, s.body.end as usize),
                used,
                how: How::Lit {
                    site: s,
                    eol: eol_after(source, start),
                },
            })
        }
    }
}

impl Target<'_> {
    /// The bytes that stand for the body when its text is `laid`, or `None` when the form
    /// cannot hold it: a one-line literal with a line break or a backtick, a delimited one with
    /// its closing, a block with a run of its fence's backticks.
    fn rebuild(&self, laid: &str) -> Option<String> {
        let (site, eol) = match &self.how {
            How::Lit { site, eol } => (site, eol),
            How::Fence(f) => return f.render(laid),
        };
        if laid.contains('\r') {
            return None;
        }
        match site.form {
            LitForm::Text => (!laid.contains(['`', '\n'])).then(|| laid.to_string()),
            LitForm::Delim(n) => {
                let close = format!("`{}", ">".repeat(n));
                (!laid.contains(&close)).then(|| laid.replace('\n', eol))
            }
            LitForm::Block(n) => {
                if laid.contains(&"`".repeat(n)) {
                    return None;
                }
                let mut body = String::new();
                for line in laid.split_inclusive('\n') {
                    // A line of white space only is an empty line.
                    if !line.trim().is_empty() {
                        body.push_str(&site.indent);
                        body.push_str(line.trim_end_matches('\n'));
                    }
                    body.push_str(eol);
                }
                Some(body)
            }
        }
    }
}

fn apply_edits(source: &str, mut edits: Vec<(usize, usize, String)>) -> String {
    edits.sort_by_key(|e| std::cmp::Reverse(e.0));
    let mut out = source.to_string();
    for (a, b, raw) in edits {
        out.replace_range(a..b, &raw);
    }
    out
}

/// A literal's syntax can be omitted only at a direct argument of a macro
/// whose successful expansion records the same input syntax. The resolved name
/// stays on the formatting site, including for a source that already omits it.
fn resolve_literal_names(
    path: &Path,
    source: &str,
    loaded: &crate::program::Loaded,
    lex: &mut crate::surface::Lexical,
    edits: &mut Vec<(usize, usize, String)>,
) {
    use crate::surface::{TermKind, parse_program_unresolved_at, walk};
    let canonical = crate::program::canonical_path(path);
    let files: Vec<_> = loaded
        .files
        .iter()
        .filter(|file| file.text == source)
        .collect();
    let Some(file) = files
        .iter()
        .copied()
        .find(|file| crate::program::canonical_path(&file.path) == canonical)
        .or_else(|| (files.len() == 1).then(|| files[0]))
    else {
        return;
    };
    let Ok(mut program) = parse_program_unresolved_at(source, 0) else {
        return;
    };
    let mut inputs = Vec::new();
    for stmt in &mut program.stmts {
        walk::stmt(stmt, &mut |term| {
            if let TermKind::MacroCall { arg, .. } = &*term.kind {
                if let TermKind::SyntaxLit(lit) = &*arg.kind {
                    inputs.push((term.span, lit.span));
                }
            }
        });
    }
    let mut resolved = vec![None; inputs.len()];
    for (index, (call, literal)) in inputs.into_iter().enumerate() {
        let Some(expansion) = loaded.expansions.iter().find(|e| {
            e.kind == "syntax"
                && e.parent.is_none()
                && e.call.start == file.base + call.start
                && e.call.end == file.base + call.end
        }) else {
            continue;
        };
        let Some(site) = lex
            .literals
            .iter_mut()
            .find(|s| !s.grammar && s.lit.span == literal)
        else {
            continue;
        };
        if site.lit.error.is_some() {
            continue;
        }
        if site
            .lit
            .name
            .as_ref()
            .is_some_and(|name| name != &expansion.syntax)
        {
            continue;
        }
        if let Some(name) = &site.lit.name {
            let start = literal.start as usize;
            let offset = match site.form {
                LitForm::Block(ticks) => ticks,
                _ => 0,
            };
            edits.push((start + offset, start + offset + name.len(), String::new()));
        }
        site.lit.name = Some(expansion.syntax.clone());
        resolved[index] = Some(expansion.syntax.clone());
    }
    // Compare before formatting the syntax's body: its registered formatter
    // separately checks the syntax's non-whitespace tokens.
    let elided = apply_edits(source, edits.clone());
    if !matches!((resolved_macro_key(source, &resolved), resolved_macro_key(&elided, &resolved)),
        (Some(before), Some(after)) if before == after)
    {
        edits.clear();
    }
}

fn resolved_macro_key(source: &str, resolved: &[Option<String>]) -> Option<String> {
    use crate::surface::{TermKind, parse_program_unresolved_at, walk};
    let mut program = parse_program_unresolved_at(source, 0).ok()?;
    let mut index = 0;
    for stmt in &mut program.stmts {
        walk::stmt(stmt, &mut |term| {
            if let TermKind::MacroCall { arg, .. } = std::sync::Arc::make_mut(&mut term.kind) {
                if let TermKind::SyntaxLit(lit) = std::sync::Arc::make_mut(&mut arg.kind) {
                    if let Some(Some(name)) = resolved.get(index) {
                        lit.name = Some(name.clone());
                    }
                    index += 1;
                }
            }
        });
    }
    (index == resolved.len()).then(|| crate::surface::dump::formatting_key(&program))
}
