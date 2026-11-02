//! The tokens of the text of a syntax, for an editor's semantic highlighting.
//!
//! Two kinds of text are coloured: every syntax literal written in the file (read from the
//! source text itself, so a literal in a `quote`, in a function nobody calls, or in a file whose
//! declarations do not check is coloured like any other), and the body of a fenced block
//! ```` ```name ```` in the comments of the file. A text of a syntax that registers a
//! `tokens` function (`with(tokens: f)`) is coloured as the function says; the others have their
//! tokens, outside the skipped ones (white space, comments), coloured by how the grammar names
//! the terminal.
//!
//! The grammar of a `syntax` (its ```` ```par ```` literal, and a fenced block ```` ```par ```` in a
//! comment) is coloured by the words the table generators read it as (`totes/parlex`, compiled to
//! Rust by the build script), each word by its kind and the words before it.

use std::collections::{HashMap, HashSet};
use std::path::Path;
use std::rc::Rc;

use tauto::registered::Library;
use tauto::surface::{Stmt, SurfaceTerm, SyntaxLit, TermKind, parse_program_unresolved_at, walk};
use tauto::syntax::Role;
use tauto_syntax::{Event, Limits, Tables, parse};

use super::{DslNote, DslToken, kind_of};

/// The syntaxes the program declares and the macros that read one.
struct Syntaxes {
    tables: HashMap<String, Rc<Tables>>,
    /// The syntax a macro's first parameter is of, by the macro's name.
    macros: HashMap<String, String>,
}

/// A text of a syntax and where each byte of it was written.
struct Piece {
    syntax: String,
    tables: Rc<Tables>,
    text: String,
    origin: Origin,
}

enum Origin {
    /// A literal; `base` is where the file starts in the positions the literal holds.
    Literal { lit: SyntaxLit, base: u32 },
    /// The body of a fenced block, line by line: the range of the line in the text and where it
    /// starts in the file.
    Lines(Vec<(usize, usize, usize)>),
}

impl Piece {
    /// The ranges of the file the range `start..end` of the text is written in (a range over
    /// several lines of a fenced block is one per line), or none when it is not in the file.
    fn ranges(&self, start: u32, end: u32, file_len: usize) -> Vec<(usize, usize)> {
        self.origin.ranges(start, end, file_len)
    }
}

impl Origin {
    fn ranges(&self, start: u32, end: u32, file_len: usize) -> Vec<(usize, usize)> {
        match self {
            Origin::Literal { lit, base } => {
                let (a, b) = (lit.position(start), lit.position(end));
                if a < *base || (b - base) as usize > file_len {
                    return Vec::new();
                }
                vec![((a - base) as usize, (b - base) as usize)]
            }
            Origin::Lines(lines) => {
                let (start, end) = (start as usize, end as usize);
                lines
                    .iter()
                    .filter_map(|&(from, to, at)| {
                        let (lo, hi) = (start.max(from), end.min(to));
                        (lo < hi).then(|| (at + (lo - from), at + (hi - from)))
                    })
                    .collect()
            }
        }
    }
}

/// The tokens of the file at `path` (its text given): its syntax literals, whichever way they are
/// reached, and the fenced blocks in its comments. A text that does not read has none: the error
/// is the diagnostic's to show. A token over several lines is split, one token per line, and a
/// token that begins inside the one before it is left out. With them, the texts whose registered
/// `tokens` function was not used, each with the reason (they are coloured by the names of the
/// grammar's terminals instead).
pub fn dsl_tokens(path: &Path, text: &str) -> Result<(Vec<DslToken>, Vec<DslNote>), String> {
    super::kept::tokens(path, text, || coloured(path, text))
}

fn coloured(path: &Path, text: &str) -> Result<Coloured, String> {
    let (loaded, base) = super::expand(path, text)?;
    tauto::phases::mark("load");
    let syntaxes = syntaxes(&loaded);
    let mut pieces = literals_of(text, &syntaxes);
    pieces.extend(fence_pieces(text, &syntaxes));
    // The literals the expansion read that the source does not show (written by a macro).
    let seen: HashSet<u32> = pieces
        .iter()
        .filter_map(|p| match &p.origin {
            Origin::Literal { lit, .. } => Some(lit.start),
            Origin::Lines(_) => None,
        })
        .collect();
    for u in &loaded.literals {
        if u.lit
            .start
            .checked_sub(base)
            .is_some_and(|s| seen.contains(&s))
        {
            continue;
        }
        pieces.push(Piece {
            syntax: u.syntax.clone(),
            tables: u.tables.clone(),
            text: u.lit.text.clone(),
            origin: Origin::Literal {
                lit: u.lit.clone(),
                base,
            },
        });
    }

    // What the names in the interpolations are: the file is read with them as tauto.
    let mut splices = Vec::new();
    for piece in &pieces {
        for (start, end) in interpolations(piece) {
            if let Some((a, b, _)) = split_interpolation(&piece.text, start, end)
                && let [(from, to)] = piece.ranges(a as u32, b as u32, text.len())[..]
            {
                splices.push((from as u32, to as u32));
            }
        }
    }
    let names = names_of(path, text, splices);
    tauto::phases::mark("names");

    let cx = Context {
        path,
        text,
        expanded: &loaded,
        base,
        library: std::cell::OnceCell::new(),
        registrations: &loaded.registrations,
        names: &names,
        file_len: text.len(),
    };
    let (mut out, mut notes) = (Vec::new(), Vec::new());
    for piece in &pieces {
        colour(piece, &cx, &mut out, &mut notes);
    }
    for (body, origin) in grammars_of(text, &syntaxes) {
        for (start, end, kind) in grammar_marks(&body) {
            for (start, end) in origin.ranges(start as u32, end as u32, text.len()) {
                out.push(DslToken { start, end, kind });
            }
        }
    }
    let tidied = tidy(text, out);
    tauto::phases::mark("colour");
    Ok(Coloured {
        tokens: tidied,
        notes,
        inputs: loaded.inputs.clone(),
    })
}

/// The tokens of a file and the warnings, with what they were made from.
pub(super) struct Coloured {
    pub tokens: Vec<DslToken>,
    pub notes: Vec<DslNote>,
    pub inputs: tauto::program::Inputs,
}

/// What colouring a text needs from the file.
struct Context<'a> {
    path: &'a Path,
    text: &'a str,
    expanded: &'a tauto::program::Expanded,
    /// Where the file starts in the program.
    base: u32,
    /// The registered functions, opened when a text first needs one, or why they cannot run
    /// at all.
    library: std::cell::OnceCell<std::rc::Rc<Result<Library<'static>, String>>>,
    registrations: &'a [tauto::syntax::Registration],
    /// What each name written in an interpolation is, by where it starts in the file.
    names: &'a HashMap<usize, &'static str>,
    file_len: usize,
}

impl<'a> Context<'a> {
    /// The functions run in the program they are written in. When a declaration does not check,
    /// the functions that do not reach it still run (a call of one that does not check is that
    /// call's own error).
    /// A function registered in a file the file imports runs in the program of the files read
    /// before this one, which does not change as this file is edited; one registered in this
    /// file runs in the program of this file.
    fn library(&self) -> Result<&Library<'static>, &str> {
        self.library
            .get_or_init(|| {
                let own = self
                    .registrations
                    .iter()
                    .any(|r| r.role == Role::Tokens && r.span.end > self.base);
                super::kept::library(self.path, self.text, self.expanded, own)
            })
            .as_ref()
            .as_ref()
            .map_err(String::as_str)
    }
}

/// The colour of each name the file writes, by where it starts, with the expressions at
/// `splices` read as tauto in the scope of their literals.
fn names_of(path: &Path, text: &str, splices: Vec<(u32, u32)>) -> HashMap<usize, &'static str> {
    if splices.is_empty() {
        return HashMap::new();
    }
    let own = path.canonicalize().unwrap_or_else(|_| path.to_path_buf());
    let read = |p: &Path| {
        let canonical = p.canonicalize().unwrap_or_else(|_| p.to_path_buf());
        if canonical == own {
            Some(text.to_string())
        } else {
            std::fs::read_to_string(p).ok()
        }
    };
    let Some(navigator) = crate::navigate::Navigator::open_with_splices(path, &read, splices)
    else {
        return HashMap::new();
    };
    navigator
        .name_colours()
        .into_iter()
        .map(|(span, colour)| (span.start as usize, colour))
        .collect()
}

/// A coloured range of the text of a piece.
type Mark = (usize, usize, &'static str);

/// The interpolations (`$x`, `${e}`) of a piece: the ranges of its text the grammar reads as
/// `TautoExpr`.
fn interpolations(piece: &Piece) -> Vec<(usize, usize)> {
    let Ok(events) = parse(&piece.tables, &piece.text, 0, &Limits::default()) else {
        return Vec::new();
    };
    events
        .iter()
        .filter_map(|e| match e {
            Event::Token(t)
                if t.start < t.end
                    && piece.tables.terminals()[t.terminal as usize] == "TautoExpr" =>
            {
                Some((t.start as usize, t.end as usize))
            }
            _ => None,
        })
        .collect()
}

/// The expression of the interpolation `text[start..end]` as the range between its delimiters
/// (`${` and `}`, or `$`), and whether it is braced.
fn split_interpolation(text: &str, start: usize, end: usize) -> Option<(usize, usize, bool)> {
    let body = text.get(start..end)?;
    if body.starts_with("${") && body.ends_with('}') && body.len() >= 3 {
        Some((start + 2, end - 1, true))
    } else if body.starts_with('$') && body.len() > 1 {
        Some((start + 1, end, false))
    } else {
        None
    }
}

fn colour(piece: &Piece, cx: &Context, out: &mut Vec<DslToken>, notes: &mut Vec<DslNote>) {
    let interpolations = interpolations(piece);
    let mut marks: Vec<Mark> = Vec::new();
    // Why the function registered for the colours was not used, when there is one and it was not.
    let mut unused: Option<(String, String)> = None;
    let registered = cx
        .registrations
        .iter()
        .find(|r| r.syntax == piece.syntax && r.role == Role::Tokens);
    let mut from_function = false;
    if let Some(r) = registered {
        let why = match cx.library() {
            Err(why) => Some(why.to_string()),
            Ok(library) if !library.has(&piece.syntax, Role::Tokens) => Some(
                library
                    .unbound(&piece.syntax, Role::Tokens)
                    .unwrap_or_default()
                    .to_string(),
            ),
            Ok(library) => match library.highlight(&piece.syntax, &piece.tables, &piece.text) {
                Ok(Some(found))
                    if found
                        .iter()
                        .all(|m| m.start <= m.end && m.end as usize <= piece.text.len()) =>
                {
                    marks.extend(
                        found
                            .iter()
                            .map(|m| (m.start as usize, m.end as usize, m.kind)),
                    );
                    from_function = true;
                    None
                }
                Ok(Some(_)) => Some(tauto_message::msg!("analyzer-tokens-outside").to_string()),
                Ok(None) => None,
                Err(why) => Some(why),
            },
        };
        if let Some(why) = why {
            unused = Some((r.function.clone(), why));
        }
    }
    if let Some((function, why)) = unused
        && let Some(&(start, end)) = piece
            .ranges(0, piece.text.len() as u32, cx.file_len)
            .first()
    {
        notes.push(DslNote {
            start,
            end,
            message: tauto_message::msg!(
                "analyzer-tokens-unused",
                syntax = &piece.syntax,
                function = &function,
                why = &why
            )
            .to_string(),
        });
    }
    if !from_function && let Ok(events) = parse(&piece.tables, &piece.text, 0, &Limits::default()) {
        // No function, or it failed: how the grammar names the terminals.
        for e in events {
            let Event::Token(t) = e else { continue };
            if t.start == t.end {
                continue;
            }
            let name = &piece.tables.terminals()[t.terminal as usize];
            let kind = if piece.tables.is_skipped(t.terminal) {
                "comment"
            } else {
                kind_of(name)
            };
            marks.push((t.start as usize, t.end as usize, kind));
        }
    }
    // What the syntax colours stops at an interpolation, which is coloured as tauto.
    let mut all: Vec<Mark> = Vec::new();
    for (start, end, kind) in marks {
        for (s, e) in minus(start, end, &interpolations) {
            all.push((s, e, kind));
        }
    }
    for &(start, end) in &interpolations {
        interpolation(piece, cx, start, end, &mut all);
    }
    for (start, end, kind) in all {
        for (start, end) in piece.ranges(start as u32, end as u32, cx.file_len) {
            out.push(DslToken { start, end, kind });
        }
    }
}

/// `start..end` without the ranges in `holes`.
fn minus(start: usize, end: usize, holes: &[(usize, usize)]) -> Vec<(usize, usize)> {
    let mut parts = vec![(start, end)];
    for &(a, b) in holes {
        parts = parts
            .into_iter()
            .flat_map(|(s, e)| {
                if b <= s || e <= a {
                    return vec![(s, e)];
                }
                let mut kept = Vec::new();
                if s < a {
                    kept.push((s, a));
                }
                if b < e {
                    kept.push((b, e));
                }
                kept
            })
            .collect();
    }
    parts
}

/// The colours of the interpolation `text[start..end]`: its delimiters are operators and the
/// expression between them is the tauto of the file, coloured as the file's own tauto is.
fn interpolation(piece: &Piece, cx: &Context, start: usize, end: usize, out: &mut Vec<Mark>) {
    let Some((from, to, braced)) = split_interpolation(&piece.text, start, end) else {
        return;
    };
    out.push((start, from, "operator"));
    if braced {
        out.push((to, end, "operator"));
    }
    tauto_tokens(piece, cx, from, to, out);
}

/// The tokens of the expression `piece.text[from..to]`, read as the language reads a spliced
/// expression: alone. Its words are coloured by what the file's names are.
fn tauto_tokens(piece: &Piece, cx: &Context, from: usize, to: usize, out: &mut Vec<Mark>) {
    use tauto_parol::{NodeKind, TerminalKind as T};
    let Some(expr) = piece.text.get(from..to) else {
        return;
    };
    let parsed = tauto_parol::parse(expr);
    if !parsed.errors.is_empty() {
        return;
    }
    let cst = &parsed.cst;
    let mut stack: Vec<_> = cst.root().into_iter().collect();
    while let Some(id) = stack.pop() {
        match cst.kind(id) {
            NodeKind::NonTerminal(_) => stack.extend(cst.node(id).children.iter().rev().copied()),
            NodeKind::Terminal(kind) => {
                if matches!(kind, T::Whitespace | T::NewLine | T::Nl) {
                    continue;
                }
                let span = cst.span(id);
                let (start, end) = (from + span.start as usize, from + span.end as usize);
                let colour = match kind {
                    T::LineComment | T::BlockComment | T::Comment => "comment",
                    T::Integer | T::Decimal | T::Float => "number",
                    T::Text => "string",
                    T::True | T::False => "keyword",
                    T::Ident | T::Hole => piece
                        .ranges(start as u32, end as u32, cx.file_len)
                        .first()
                        .and_then(|(file, _)| cx.names.get(file).copied())
                        .unwrap_or("variable"),
                    k if format!("{k:?}").starts_with("Kw") => "keyword",
                    _ => "operator",
                };
                out.push((start, end, colour));
            }
        }
    }
}

/// The tokens in order, one per line, without white space alone and without overlaps.
fn tidy(text: &str, mut tokens: Vec<DslToken>) -> Vec<DslToken> {
    tokens.sort_by_key(|t| (t.start, t.end));
    let mut out: Vec<DslToken> = Vec::new();
    let mut last_end = 0;
    for t in tokens {
        if t.start < last_end || t.end <= t.start {
            continue;
        }
        let Some(body) = text.get(t.start..t.end) else {
            continue;
        };
        last_end = t.end;
        let mut at = t.start;
        for line in body.split('\n') {
            let piece = line.strip_suffix('\r').unwrap_or(line);
            if !piece.trim().is_empty() {
                out.push(DslToken {
                    start: at,
                    end: at + piece.len(),
                    kind: t.kind,
                });
            }
            at += line.len() + 1;
        }
    }
    out
}

/// The syntaxes the files of the program declare, with the tables of their grammars, and the
/// macros named for the syntax their first parameter reads.
fn syntaxes(loaded: &tauto::program::Expanded) -> Syntaxes {
    let mut out = Syntaxes {
        tables: HashMap::new(),
        macros: HashMap::new(),
    };
    let mut macros: Vec<(String, String)> = Vec::new();
    let mut first_types: HashMap<String, String> = HashMap::new();
    tauto::syntax::with_search_dirs(loaded.syntax_dirs.clone(), || {
        for file in &loaded.files {
            if !file.text.contains("syntax") && !file.text.contains("macro") {
                continue;
            }
            let Ok(program) = parse_program_unresolved_at(&file.text, 0) else {
                continue;
            };
            for s in &program.stmts {
                match s {
                    Stmt::Syntax { name, grammar, .. } => {
                        if let Ok(tables) = tauto::syntax::load_tables(&grammar.text) {
                            out.tables.entry(name.clone()).or_insert(tables);
                        }
                    }
                    Stmt::Macro { name, function, .. } => {
                        macros.push((name.clone(), function.clone()));
                    }
                    Stmt::Fn(f) => {
                        if let Some(Some(t)) = f.param_types.first()
                            && let TermKind::Var(ty) = &*t.kind
                            && let Some((module, _)) = ty.split_once("::")
                        {
                            first_types.insert(f.name.clone(), module.to_string());
                        }
                    }
                    _ => {}
                }
            }
        }
    });
    for (name, function) in macros {
        if let Some(syntax) = first_types.get(&function)
            && out.tables.contains_key(syntax)
        {
            out.macros
                .insert(name.trim_end_matches('!').to_string(), syntax.clone());
        }
    }
    out
}

/// A literal found in the source, and the macro it is the argument of.
struct Found {
    macro_name: Option<String>,
    lit: SyntaxLit,
}

/// The syntax literals written in the text of the file, wherever they are.
fn literals_of(text: &str, syntaxes: &Syntaxes) -> Vec<Piece> {
    let Ok(mut program) = parse_program_unresolved_at(text, 0) else {
        return Vec::new();
    };
    let mut found = Vec::new();
    for s in &mut program.stmts {
        gather(s, &mut found);
    }
    let mut pieces = Vec::new();
    for f in found {
        let name = f.lit.name.clone().or_else(|| {
            let m = f.macro_name.as_deref()?;
            syntaxes.macros.get(m.trim_end_matches('!')).cloned()
        });
        let Some(name) = name else { continue };
        let Some(tables) = syntaxes.tables.get(&name) else {
            continue;
        };
        pieces.push(Piece {
            syntax: name,
            tables: tables.clone(),
            text: f.lit.text.clone(),
            origin: Origin::Literal {
                lit: f.lit,
                base: 0,
            },
        });
    }
    pieces
}

/// The literals of a statement. The walk leaves a macro's literal argument to the macro, so
/// those are taken here.
fn gather(s: &mut Stmt, out: &mut Vec<Found>) {
    match s {
        Stmt::Attributed {
            name, arg, stmt, ..
        } => {
            if let TermKind::SyntaxLit(l) = &*arg.kind {
                out.push(Found {
                    macro_name: Some(name.clone()),
                    lit: (**l).clone(),
                });
            }
            gather(stmt, out);
        }
        Stmt::Mutual { items, .. } | Stmt::Module { items, .. } => {
            for i in items {
                gather(i, out);
            }
        }
        _ => {}
    }
    walk::stmt(s, &mut |t: &mut SurfaceTerm| match &*t.kind {
        TermKind::SyntaxLit(l) => out.push(Found {
            macro_name: None,
            lit: (**l).clone(),
        }),
        TermKind::MacroCall { name, arg } => {
            if let TermKind::SyntaxLit(l) = &*arg.kind {
                out.push(Found {
                    macro_name: Some(name.clone()),
                    lit: (**l).clone(),
                });
            }
        }
        _ => {}
    });
}

/// The fenced blocks ```` ```name ```` … ```` ``` ```` in the comments of the text, for the syntaxes the
/// program declares (`tauto::surface::fence` says what a fence is). The body is the text of the lines
/// after the prefix, and each line of it is mapped to the file.
fn fence_pieces(text: &str, syntaxes: &Syntaxes) -> Vec<Piece> {
    let lexical = tauto::surface::lexical(text);
    let mut out = Vec::new();
    for fence in tauto::surface::fence::fences(text, &lexical.comments) {
        let Some(tables) = syntaxes.tables.get(&fence.name) else {
            continue;
        };
        if !fence.closed || fence.lines.is_empty() {
            continue;
        }
        let mut lines = Vec::new();
        let mut from = 0;
        for &(a, b) in &fence.lines {
            // A line of the text ends in a newline.
            lines.push((from, from + (b - a), a));
            from += b - a + 1;
        }
        out.push(Piece {
            syntax: fence.name.clone(),
            tables: tables.clone(),
            text: fence.text(text),
            origin: Origin::Lines(lines),
        });
    }
    out
}

mod parlex {
    include!(concat!(env!("OUT_DIR"), "/tauto_parlex.rs"));
}

/// The name a grammar's literal and fence are written with.
const GRAMMAR: &str = "par";

/// The grammars written in the text of the file: the ```` ```par ```` literal of each `syntax`
/// declaration, and the fenced blocks ```` ```par ```` in its comments (unless the program declares
/// a syntax of that name, whose fences are coloured as its own).
fn grammars_of(text: &str, syntaxes: &Syntaxes) -> Vec<(String, Origin)> {
    fn gather(s: &Stmt, out: &mut Vec<(String, Origin)>) {
        match s {
            Stmt::Syntax { grammar, .. } => out.push((
                grammar.text.clone(),
                Origin::Literal {
                    lit: grammar.clone(),
                    base: 0,
                },
            )),
            Stmt::Attributed { stmt, .. } => gather(stmt, out),
            Stmt::Mutual { items, .. } | Stmt::Module { items, .. } => {
                for i in items {
                    gather(i, out);
                }
            }
            _ => {}
        }
    }
    let mut out = Vec::new();
    if let Ok(program) = parse_program_unresolved_at(text, 0) {
        for s in &program.stmts {
            gather(s, &mut out);
        }
    }
    if syntaxes.tables.contains_key(GRAMMAR) {
        return out;
    }
    let lexical = tauto::surface::lexical(text);
    for fence in tauto::surface::fence::fences(text, &lexical.comments) {
        if fence.name != GRAMMAR || !fence.closed || fence.lines.is_empty() {
            continue;
        }
        let mut lines = Vec::new();
        let mut from = 0;
        for &(a, b) in &fence.lines {
            // A line of the text ends in a newline.
            lines.push((from, from + (b - a), a));
            from += b - a + 1;
        }
        out.push((fence.text(text), Origin::Lines(lines)));
    }
    out
}

/// The colours of the grammar `text`. Its words are what `totes/parlex` reads (`PSpan` there lists
/// the kinds); a name is coloured by where it stands: a non-terminal (`type`), the type a symbol is
/// given after `:` or a user type of a directive (`class`), a member after `@` (`property`), a
/// scanner mode (`namespace`). A character that has no place in a grammar is left uncoloured.
fn grammar_marks(text: &str) -> Vec<Mark> {
    let words = parlex::par_spans_text(tauto_rt::Text::from(text)).to_string();
    let numbers: Vec<usize> = words.split(' ').filter_map(|w| w.parse().ok()).collect();
    let mut out = Vec::new();
    // After `%%`: the productions.
    let mut productions = false;
    // At the start of a production, where its non-terminal is written.
    let mut head = false;
    // The `:` after a production's non-terminal is still to come.
    let mut rule_colon = false;
    // The last `:` gives a symbol its type (it is not a production's own).
    let mut annotation = false;
    // Inside `<…>`, the scanner modes of a terminal.
    let mut modes = 0usize;
    let mut previous: Option<(usize, &str)> = None;
    for word in numbers.chunks_exact(3) {
        let (kind, start, end) = (word[0], word[1], word[2]);
        let Some(written) = text.get(start..end) else {
            continue;
        };
        let colour = match kind {
            0 => Some(match previous {
                Some((5, "@")) => "property",
                _ if modes > 0 => "namespace",
                _ if productions && head => {
                    head = false;
                    rule_colon = true;
                    "type"
                }
                Some((5, ":")) if annotation => "class",
                Some((1, "%scanner" | "%enter" | "%push")) => "namespace",
                Some((1, "%user_type" | "%t_type") | (5, "=")) => "class",
                _ => "type",
            }),
            1 => {
                if written == "%%" {
                    productions = true;
                    head = true;
                }
                Some("keyword")
            }
            2 | 3 | 13 => Some("string"),
            4 => Some("regexp"),
            5..=7 => {
                match written {
                    ";" if productions => head = true,
                    ":" => {
                        annotation = productions && !rule_colon;
                        rule_colon = false;
                    }
                    "<" => modes += 1,
                    ">" => modes = modes.saturating_sub(1),
                    _ => {}
                }
                Some("operator")
            }
            9 => Some("number"),
            10 | 11 | 14 => Some("comment"),
            _ => None,
        };
        if let Some(colour) = colour {
            out.push((start, end, colour));
        }
        if !matches!(kind, 10 | 11 | 14) {
            previous = Some((kind, written));
        }
    }
    out
}
