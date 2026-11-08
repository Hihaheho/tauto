//! The names of a file: where each is declared and where it is used. The
//! tree is the concrete syntax tree of the text as written (before any macro
//! expands), so every identifier has the span it is written at. Resolution is
//! lexical: a binder is visible after it in its block, a parameter in the
//! rest of its signature and the body, a pattern's names in its arm, and a
//! top-level declaration everywhere, in the file and in the files it imports.
//!
//! What this cannot see it records instead of guessing: an identifier that
//! resolves to nothing (`FileIndex::unresolved`) and the words inside syntax
//! literals and `quote` (`FileIndex::opaque`). A rename refuses when one of
//! those could be a use of the name.

use std::collections::{HashMap, HashSet};
use std::path::{Path, PathBuf};
use std::sync::OnceLock;

use tauto_parol::{Cst, NodeId, NonTerminalKind as Nt, Span, parse};

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct DefId {
    pub file: usize,
    pub index: usize,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Kind {
    Fn,
    Theorem,
    Axiom,
    Definition,
    Inductive,
    Constructor,
    Struct,
    Enum,
    Variant,
    Field,
    Effect,
    Module,
    Class,
    Method,
    Law,
    Macro,
    Syntax,
    Generic,
    Param,
    Local,
    PatternVar,
    Binder,
}

impl Kind {
    pub fn label(self) -> &'static str {
        match self {
            Kind::Fn => "function",
            Kind::Theorem => "theorem",
            Kind::Axiom => "axiom",
            Kind::Definition => "definition",
            Kind::Inductive => "inductive family",
            Kind::Constructor => "constructor",
            Kind::Struct => "struct",
            Kind::Enum => "enum",
            Kind::Variant => "variant",
            Kind::Field => "field",
            Kind::Effect => "effect",
            Kind::Module => "module",
            Kind::Class => "class",
            Kind::Method => "method",
            Kind::Law => "law",
            Kind::Macro => "macro",
            Kind::Syntax => "syntax",
            Kind::Generic => "generic parameter",
            Kind::Param => "parameter",
            Kind::Local => "variable",
            Kind::PatternVar => "pattern variable",
            Kind::Binder => "binder",
        }
    }

    /// Why a name of this kind is not renamed, when it is not: the id of a
    /// message.
    fn pinned(self) -> Option<&'static str> {
        match self {
            Kind::Field => Some("analyzer-pinned-field"),
            Kind::Syntax => Some("analyzer-pinned-syntax"),
            _ => None,
        }
    }
}

#[derive(Debug, Clone)]
pub struct Def {
    pub name: String,
    pub kind: Kind,
    /// Where the name is written in its declaration. More than one for a
    /// name an or-pattern binds in each alternative.
    pub spans: Vec<Span>,
    /// What a hover shows: the declaration without its body.
    pub signature: String,
    /// The type as written, when the declaration has one.
    pub declared: Option<String>,
    /// Visible to other files (top-level, or a member of something that is).
    pub exported: bool,
    /// Where a type checker keys the name's type (see `types::site`).
    pub site: Option<u32>,
    pub members: Vec<usize>,
    pub parent: Option<usize>,
    /// Why the name cannot be renamed, when it cannot.
    pub pinned: Option<&'static str>,
}

#[derive(Debug, Clone, Copy)]
pub struct Ref {
    pub span: Span,
    pub target: DefId,
    /// Found by the name alone (a field read from a value, a bare variant).
    pub approximate: bool,
}

#[derive(Debug, Default)]
pub struct FileIndex {
    pub path: Option<PathBuf>,
    pub text: String,
    pub defs: Vec<Def>,
    pub refs: Vec<Ref>,
    /// Identifiers that resolved to nothing.
    pub unresolved: Vec<(Span, String)>,
    /// Words written where names are not resolved: syntax literals and `quote`.
    pub opaque: Vec<(Span, String)>,
    /// The top-level statements, whole.
    pub top_stmts: Vec<Span>,
    /// The `name!(…)` calls, whole.
    pub macro_calls: Vec<Span>,
    /// The theorem keyword and the declaration it introduces (hover only).
    pub theorem_keywords: Vec<(Span, usize)>,
    /// The files this one sees, itself last: its imports, transitively.
    pub closure: Vec<usize>,
    /// The top-level names, for the files that see this one.
    pub toplevel: HashMap<String, DefId>,
    /// The text did not read as a whole.
    pub broken: bool,
}

impl FileIndex {
    /// The declaration or use whose name is written at `offset`.
    pub fn site_at(&self, file: usize, offset: usize) -> Option<(Span, DefId)> {
        let at = offset as u32;
        let mut best: Option<(Span, DefId)> = None;
        let mut take = |span: Span, id: DefId| {
            if span.contains(at)
                && best.is_none_or(|(b, _)| span.end - span.start < b.end - b.start)
            {
                best = Some((span, id));
            }
        };
        for (index, d) in self.defs.iter().enumerate() {
            for s in &d.spans {
                take(*s, DefId { file, index });
            }
        }
        for r in &self.refs {
            take(r.span, r.target);
        }
        best
    }
}

/// The files read so far, with the prelude first.
pub struct World<'a> {
    read: &'a dyn Fn(&Path) -> Option<String>,
    /// How many files come before `files`: the prelude's.
    base: usize,
    files: Vec<FileIndex>,
    by_path: HashMap<PathBuf, usize>,
    building: HashSet<PathBuf>,
    /// The expressions of a file's syntax literals (`${ e }`, `$n`): the file and where each is
    /// written. They are read as tauto in the scope of the literal.
    splices: Option<(PathBuf, Vec<(u32, u32)>)>,
}

/// An expression spliced into a syntax literal, read on its own; `start` is where it is
/// written in the file.
struct Splice {
    start: u32,
    end: u32,
    src: String,
    cst: Cst,
}

/// The declarations every program sees, indexed once.
fn preludes() -> &'static [FileIndex; 2] {
    static P: OnceLock<[FileIndex; 2]> = OnceLock::new();
    P.get_or_init(|| {
        let mut world = World::empty(&|_| None, 0);
        for (id, text, closure) in [
            (0, tauto::nibstd::PRELUDE, vec![]),
            (
                1,
                include_str!("../../../tauto-kernel/src/prelude.taut"),
                vec![0],
            ),
        ] {
            let index = world.build(id, None, text, &parse(text), closure);
            world.files.push(index);
        }
        let second = world.files.pop().unwrap_or_default();
        let first = world.files.pop().unwrap_or_default();
        [first, second]
    })
}

pub fn canonical(path: &Path) -> PathBuf {
    path.canonicalize().unwrap_or_else(|_| path.to_path_buf())
}

impl<'a> World<'a> {
    fn empty(read: &'a dyn Fn(&Path) -> Option<String>, base: usize) -> Self {
        World {
            read,
            base,
            files: Vec::new(),
            by_path: HashMap::new(),
            building: HashSet::new(),
            splices: None,
        }
    }

    pub fn new(read: &'a dyn Fn(&Path) -> Option<String>) -> Self {
        Self::empty(read, 2)
    }

    /// Reads the expressions at `ranges` of `path` (the bytes of the file between the
    /// delimiters of its `${ … }` and `$n`) as tauto in the scope of their literals.
    pub fn with_splices(mut self, path: &Path, ranges: Vec<(u32, u32)>) -> Self {
        self.splices = Some((canonical(path), ranges));
        self
    }

    pub fn file(&self, id: usize) -> &FileIndex {
        if id < self.base {
            &preludes()[id]
        } else {
            &self.files[id - self.base]
        }
    }

    pub fn def(&self, id: DefId) -> &Def {
        &self.file(id.file).defs[id.index]
    }

    pub fn file_id(&self, path: &Path) -> Option<usize> {
        self.by_path.get(&canonical(path)).copied()
    }

    /// Reads `path` and what it imports; the file's id.
    pub fn load(&mut self, path: &Path) -> Option<usize> {
        let path = canonical(path);
        if let Some(id) = self.by_path.get(&path) {
            return Some(*id);
        }
        if !self.building.insert(path.clone()) {
            return None;
        }
        let text = match tauto::stdlib::text(&path) {
            Some(text) => text.to_string(),
            None => (self.read)(&path)?,
        };
        let cst = parse(&text);
        let mut imports = Vec::new();
        if let Some(root) = cst.cst.root() {
            let mut paths = Vec::new();
            find_imports(&cst.cst, &text, root, &mut paths);
            for (rel, module) in paths {
                let Ok(target) = tauto::stdlib::import_target(&path, &rel, module) else {
                    continue;
                };
                if let Some(id) = self.load(&target) {
                    imports.push(id);
                }
            }
        }
        let id = self.base + self.files.len();
        let mut closure = vec![0, 1];
        for i in imports {
            for c in self.file(i).closure.clone() {
                if !closure.contains(&c) {
                    closure.push(c);
                }
            }
        }
        let index = self.build(id, Some(path.clone()), &text, &cst, closure);
        self.building.remove(&path);
        self.by_path.insert(path, id);
        self.files.push(index);
        Some(id)
    }

    fn build(
        &self,
        id: usize,
        path: Option<PathBuf>,
        text: &str,
        parsed: &tauto_parol::Parsed,
        mut closure: Vec<usize>,
    ) -> FileIndex {
        let mut globals = HashMap::new();
        for &f in &closure {
            for (name, def) in &self.file(f).toplevel {
                globals.insert(name.clone(), *def);
            }
        }
        let splices: Vec<Splice> = match (&self.splices, &path) {
            (Some((own, ranges)), Some(path)) if own == path => ranges
                .iter()
                .filter_map(|&(start, end)| {
                    let src = text.get(start as usize..end as usize)?.to_string();
                    let parsed = parse(&src);
                    parsed.errors.is_empty().then_some(Splice {
                        start,
                        end,
                        src,
                        cst: parsed.cst,
                    })
                })
                .collect(),
            _ => Vec::new(),
        };
        let mut w = Walk {
            world: self,
            file: id,
            cst: &parsed.cst,
            src: text,
            splices: &splices,
            idx: FileIndex::default(),
            frames: Vec::new(),
            globals,
            node_def: HashMap::new(),
            quoting: 0,
        };
        w.idx.broken = !parsed.errors.is_empty();
        w.idx.path = path;
        w.idx.text = text.to_string();
        if let Some(root) = parsed.cst.root() {
            w.run(root);
        }
        closure.push(id);
        w.idx.closure = closure;
        w.idx
    }
}

/// The paths of the `import "…"` statements at the top of a tree.
fn find_imports(cst: &Cst, src: &str, id: NodeId, out: &mut Vec<(String, bool)>) {
    for c in cst.children(id) {
        match cst.non_terminal(c) {
            Some(Nt::ImportDecl) => {
                let mut names = Vec::new();
                for t in cst.children(c) {
                    match cst.non_terminal(t) {
                        Some(Nt::Text) => {
                            let raw = cst.span(t).text(src);
                            out.push((raw.trim_matches(['"', '\'']).to_string(), false));
                        }
                        Some(Nt::Ident) => names.push(cst.span(t).text(src).trim()),
                        _ => {}
                    }
                }
                // `import std::List`, as the loader spells it.
                if !names.is_empty() {
                    out.push((names.join("::"), true));
                }
            }
            Some(Nt::Root | Nt::Stmts | Nt::StmtsTail | Nt::Stmt | Nt::OtherStmt | Nt::Program) => {
                find_imports(cst, src, c, out)
            }
            _ => {}
        }
    }
}

struct Walk<'w, 'a> {
    world: &'w World<'a>,
    file: usize,
    cst: &'w Cst,
    src: &'w str,
    splices: &'w [Splice],
    idx: FileIndex,
    frames: Vec<HashMap<String, DefId>>,
    globals: HashMap<String, DefId>,
    /// The declaration made for a node, so reading a block twice makes one.
    node_def: HashMap<NodeId, usize>,
    /// Inside a `quote`: names are not resolved.
    quoting: u32,
}

const KEYWORDS: &[&str] = &[
    "fn",
    "let",
    "var",
    "struct",
    "enum",
    "effect",
    "theorem",
    "axiom",
    "def",
    "inductive",
    "match",
    "if",
    "else",
    "loop",
    "while",
    "return",
    "break",
    "continue",
    "handle",
    "with",
    "perform",
    "import",
    "mutual",
    "true",
    "false",
    "decreasing_by",
    "opaque",
    "eqn",
];

pub fn is_keyword(word: &str) -> bool {
    KEYWORDS.contains(&word)
}

impl Walk<'_, '_> {
    fn kids(&self, id: NodeId) -> Vec<NodeId> {
        self.cst.children(id)
    }

    fn nt(&self, id: NodeId) -> Option<Nt> {
        self.cst.non_terminal(id)
    }

    fn first(&self, id: NodeId, kind: Nt) -> Option<NodeId> {
        self.kids(id)
            .into_iter()
            .find(|c| self.nt(*c) == Some(kind))
    }

    /// The type written under `id`: a `Type`, or a `BodyType` where a `{` or `=>` follows it.
    fn ty(&self, id: NodeId) -> Option<NodeId> {
        self.kids(id)
            .into_iter()
            .find(|c| matches!(self.nt(*c), Some(Nt::Type | Nt::BodyType)))
    }

    fn tys(&self, id: NodeId) -> Vec<NodeId> {
        self.kids(id)
            .into_iter()
            .filter(|c| matches!(self.nt(*c), Some(Nt::Type | Nt::BodyType)))
            .collect()
    }

    fn all(&self, id: NodeId, kind: Nt) -> Vec<NodeId> {
        self.kids(id)
            .into_iter()
            .filter(|c| self.nt(*c) == Some(kind))
            .collect()
    }

    fn has(&self, id: NodeId, kind: Nt) -> bool {
        self.first(id, kind).is_some()
    }

    fn text(&self, span: Span) -> &str {
        span.text(self.src)
    }

    /// The items of a list written `{ Sep } [ Item Tail ]`.
    fn list(&self, id: NodeId, item: Nt, tail: Nt) -> Vec<NodeId> {
        let mut out = Vec::new();
        for c in self.kids(id) {
            match self.nt(c) {
                Some(k) if k == item => out.push(c),
                Some(k) if k == tail => out.extend(self.list(c, item, tail)),
                _ => {}
            }
        }
        out
    }

    /// The name an `Ident` node holds and where it is written. `r#name` is the name `name`, written
    /// from after the `r#`.
    fn ident(&self, id: NodeId) -> Option<(String, Span)> {
        let (_, span) = self.cst.token(id)?;
        let text = self.text(span);
        match text.strip_prefix("r#") {
            Some(rest) if !rest.is_empty() => {
                Some((rest.to_string(), Span::new(span.start + 2, span.end)))
            }
            _ => Some((text.to_string(), span)),
        }
    }

    fn first_ident_below(&self, id: NodeId) -> Option<(String, Span)> {
        for c in self.kids(id) {
            if self.nt(c) == Some(Nt::Ident) {
                return self.ident(c);
            }
            if let Some(found) = self.first_ident_below(c) {
                return Some(found);
            }
        }
        None
    }

    /// The segments of a path's names: one token may hold several
    /// (`Shape::Dot`), each with its own span.
    fn path_segments(&self, idents: &[NodeId]) -> Vec<(String, Span)> {
        let mut out = Vec::new();
        for id in idents {
            let Some((name, span)) = self.ident(*id) else {
                continue;
            };
            let mut start = span.start;
            for seg in name.split("::") {
                out.push((seg.to_string(), Span::new(start, start + seg.len() as u32)));
                start += seg.len() as u32 + 2;
            }
        }
        out
    }

    /// The first `Ident` among the children, or the one inside a wrapper.
    fn name_of(&self, id: NodeId) -> Option<(String, Span)> {
        for c in self.kids(id) {
            match self.nt(c) {
                Some(Nt::Ident) => return self.ident(c),
                Some(Nt::FnName) => return self.name_of(c),
                _ => {}
            }
        }
        None
    }

    /// Follows a statement down to the declaration it holds.
    fn inner(&self, id: NodeId) -> NodeId {
        let mut id = id;
        while matches!(
            self.nt(id),
            Some(
                Nt::Stmt
                    | Nt::OtherStmt
                    | Nt::ExternItem
                    | Nt::ClassItem
                    | Nt::InstanceItem
                    | Nt::MutualItem
                    | Nt::MutualMember
            )
        ) {
            let kids = self.kids(id);
            let next = kids
                .iter()
                .find(|k| !matches!(self.nt(**k), Some(Nt::Attribute | Nt::Visibility)));
            match next {
                Some(c) => id = *c,
                None => break,
            }
        }
        id
    }

    fn mutual_items(&self, n: NodeId) -> Vec<NodeId> {
        let Some(items) = self.first(n, Nt::MutualItems) else {
            return Vec::new();
        };
        self.list(items, Nt::MutualItem, Nt::MutualTail)
            .into_iter()
            .map(|i| self.inner(i))
            .collect()
    }

    fn extern_items(&self, n: NodeId) -> Vec<NodeId> {
        let Some(items) = self.first(n, Nt::ExternItems) else {
            return Vec::new();
        };
        self.list(items, Nt::ExternItem, Nt::ExternTail)
            .into_iter()
            .map(|i| self.inner(i))
            .collect()
    }

    /// The text from the start of a node to the start of the first child of
    /// one of these kinds, on one line.
    fn header(&self, id: NodeId, stop: &[Nt]) -> String {
        let span = self.cst.span(id);
        let end = self
            .kids(id)
            .into_iter()
            .find(|c| self.nt(*c).is_some_and(|k| stop.contains(&k)))
            .map_or(span.end, |c| self.cst.span(c).start);
        squeeze(
            self.src
                .get(span.start as usize..end as usize)
                .unwrap_or(""),
        )
    }

    fn whole(&self, id: NodeId) -> String {
        let t = self.text(self.cst.span(id));
        let lines: Vec<&str> = t.lines().collect();
        if lines.len() > 16 {
            format!("{}\n…", lines[..16].join("\n"))
        } else {
            t.to_string()
        }
    }

    fn def_of(&self, id: DefId) -> &Def {
        if id.file == self.file {
            &self.idx.defs[id.index]
        } else {
            self.world.def(id)
        }
    }

    fn me(&self, index: usize) -> DefId {
        DefId {
            file: self.file,
            index,
        }
    }

    #[allow(clippy::too_many_arguments)]
    fn new_def(&mut self, name: &str, kind: Kind, span: Span, signature: String) -> usize {
        self.idx.defs.push(Def {
            name: name.to_string(),
            kind,
            spans: vec![span],
            signature,
            declared: None,
            exported: false,
            site: None,
            members: Vec::new(),
            parent: None,
            pinned: kind.pinned(),
        });
        self.idx.defs.len() - 1
    }

    fn declare(&mut self, key: &str, index: usize) {
        let id = self.me(index);
        if let Some(f) = self.frames.last_mut() {
            f.insert(key.to_string(), id);
        }
    }

    fn lookup(&self, name: &str) -> Option<DefId> {
        for f in self.frames.iter().rev() {
            if let Some(d) = f.get(name) {
                // `usize::MAX`: a bare variant name two enums share.
                return (d.file != usize::MAX).then_some(*d);
            }
        }
        self.globals.get(name).copied()
    }

    fn add_ref(&mut self, span: Span, target: DefId, approximate: bool) {
        self.idx.refs.push(Ref {
            span,
            target,
            approximate,
        });
    }

    fn reference(&mut self, span: Span, name: &str) -> Option<DefId> {
        if self.quoting > 0 {
            self.idx.opaque.push((span, name.to_string()));
            return None;
        }
        match self.lookup(name) {
            Some(d) => {
                self.add_ref(span, d, false);
                Some(d)
            }
            None => {
                self.idx.unresolved.push((span, name.to_string()));
                None
            }
        }
    }

    fn reference_node(&mut self, id: NodeId) -> Option<DefId> {
        let (name, span) = self.ident(id)?;
        self.reference(span, &name)
    }

    /// A use of the member `name` of `owner`: `Shape::Circle`, `File::open`.
    fn member(&mut self, owner: Option<DefId>, span: Span, name: &str) -> Option<DefId> {
        let found = owner.and_then(|o| {
            let d = self.def_of(o);
            let file = o.file;
            d.members
                .iter()
                .find(|m| {
                    let md = if file == self.file {
                        &self.idx.defs[**m]
                    } else {
                        &self.world.file(file).defs[**m]
                    };
                    md.name == name
                })
                .map(|m| DefId { file, index: *m })
        });
        match found {
            Some(d) => {
                self.add_ref(span, d, false);
                Some(d)
            }
            None => {
                self.idx.unresolved.push((span, name.to_string()));
                None
            }
        }
    }

    /// A field read from a value of a type this does not know: found by its
    /// name when only one visible declaration has it.
    fn field_by_name(&mut self, span: Span, name: &str) -> Option<DefId> {
        let mut found: Vec<DefId> = Vec::new();
        let mut scan = |file: usize, idx: &FileIndex| {
            for (i, d) in idx.defs.iter().enumerate() {
                if d.kind == Kind::Field && d.name == name {
                    found.push(DefId { file, index: i });
                }
            }
        };
        scan(self.file, &self.idx);
        for &f in &self.idx.closure.clone() {
            if f != self.file {
                scan(f, self.world.file(f));
            }
        }
        // `closure` is filled when the file is done; read the globals' files too.
        let mut seen: HashSet<usize> = HashSet::new();
        for d in self.globals.values() {
            if d.file != self.file && seen.insert(d.file) {
                scan(d.file, self.world.file(d.file));
            }
        }
        found.sort_by_key(|d| (d.file, d.index));
        found.dedup();
        if found.len() == 1 {
            self.add_ref(span, found[0], true);
            Some(found[0])
        } else {
            self.idx.unresolved.push((span, name.to_string()));
            None
        }
    }

    fn run(&mut self, root: NodeId) {
        self.frames.push(HashMap::new());
        let program = self.first(root, Nt::Program).unwrap_or(root);
        if let Some(stmts) = self.first(program, Nt::Stmts) {
            for n in self.stmt_nodes(stmts) {
                self.idx.top_stmts.push(self.cst.span(n));
            }
            self.stmts_in_frame(stmts);
        }
        let top = self.frames.pop().unwrap_or_default();
        for (name, d) in top {
            if d.file == self.file {
                self.export(d.index);
                self.idx.toplevel.insert(name, d);
            }
        }
    }

    fn export(&mut self, index: usize) {
        self.idx.defs[index].exported = true;
        for m in self.idx.defs[index].members.clone() {
            self.export(m);
        }
    }

    fn stmt_nodes(&self, stmts: NodeId) -> Vec<NodeId> {
        self.list(stmts, Nt::Stmt, Nt::StmtsTail)
            .into_iter()
            .map(|s| self.inner(s))
            .collect()
    }

    /// The statements of a block in the current frame.
    fn stmts_in_frame(&mut self, stmts: NodeId) {
        let nodes = self.stmt_nodes(stmts);
        for n in &nodes {
            self.hoist(*n);
        }
        for n in nodes {
            self.stmt(n);
        }
    }

    fn block(&mut self, block: NodeId) {
        self.frames.push(HashMap::new());
        if let Some(stmts) = self.first(block, Nt::Stmts) {
            self.stmts_in_frame(stmts);
        }
        self.frames.pop();
    }

    /// Declares what a statement names, before any statement is read, so a
    /// declaration is visible above itself.
    fn hoist(&mut self, n: NodeId) {
        let Some(kind) = self.nt(n) else { return };
        match kind {
            Nt::FnDecl | Nt::ExternFn => {
                self.hoist_callable(n, Kind::Fn, &[Nt::Block]);
            }
            Nt::TheoremDecl => {
                self.hoist_callable(n, Kind::Theorem, &[Nt::Block]);
            }
            Nt::AxiomDecl => {
                self.hoist_callable(n, Kind::Axiom, &[]);
            }
            Nt::DefDecl => {
                self.hoist_callable(n, Kind::Definition, &[Nt::Assign]);
            }
            Nt::MutualDecl => {
                for item in self.mutual_items(n) {
                    self.hoist(item);
                }
            }
            Nt::InductiveDecl => self.hoist_inductive(n),
            Nt::StructDecl => self.hoist_struct(n),
            Nt::EnumDecl => self.hoist_enum(n),
            Nt::EffectDecl => {
                if let Some((name, span)) = self.name_of(n) {
                    let sig = self.header(n, &[]);
                    let d = self.def_once(n, &name, Kind::Effect, span, sig);
                    self.declare(&name, d);
                }
            }
            Nt::ModuleDecl => self.hoist_module(n),
            Nt::ExternDecl => {
                for item in self.extern_items(n) {
                    self.hoist(item);
                }
            }
            Nt::ClassDecl => self.hoist_class(n),
            Nt::SyntaxDecl => {
                // `syntax!(NAME, …)`: the first argument is the syntax's name.
                let name = self
                    .first(n, Nt::Expr)
                    .and_then(|e| self.first_ident_below(e));
                if let Some((name, span)) = name {
                    let sig = format!("syntax {name}");
                    let d = self.def_once(n, &name, Kind::Syntax, span, sig);
                    self.declare(&format!("syntax {name}"), d);
                }
            }
            Nt::MacroFnDecl => {
                // `macro fn NAME(…) … { … }`: the function, and the macro of the same name.
                if let Some(f) = self.first(n, Nt::FnDecl) {
                    self.hoist(f);
                    if let Some((name, span)) = self.name_of(f) {
                        let sig = self.header(f, &[Nt::Block]);
                        let d = self.def_once(n, &name, Kind::Macro, span, sig);
                        self.declare(&format!("{name}!"), d);
                    }
                }
            }
            _ => {}
        }
    }

    fn def_once(&mut self, n: NodeId, name: &str, kind: Kind, span: Span, sig: String) -> usize {
        if let Some(d) = self.node_def.get(&n) {
            return *d;
        }
        let d = self.new_def(name, kind, span, sig);
        self.node_def.insert(n, d);
        d
    }

    fn hoist_simple(&mut self, n: NodeId, kind: Kind, stop: &[Nt]) {
        if let Some((name, span)) = self.name_of(n) {
            let sig = self.header(n, stop);
            let d = self.def_once(n, &name, kind, span, sig);
            self.declare(&name, d);
        }
    }

    fn hoist_callable(&mut self, n: NodeId, kind: Kind, stop: &[Nt]) -> Option<usize> {
        let (name, span) = self.name_of(n)?;
        let sig = self.header(n, stop);
        let d = self.def_once(n, &name, kind, span, sig);
        let declared = self.ty(n).map(|t| squeeze(self.text(self.cst.span(t))));
        self.idx.defs[d].declared = declared;
        if kind == Kind::Theorem {
            for child in self.kids(n) {
                let span = self.cst.span(child);
                if self.nt(child) == Some(Nt::KwTheorem) {
                    self.idx.theorem_keywords.push((span, d));
                }
            }
        }
        self.declare(&name, d);
        Some(d)
    }

    fn hoist_inductive(&mut self, n: NodeId) {
        let Some(d) = self.hoist_callable(n, Kind::Inductive, &[Nt::LBrace]) else {
            return;
        };
        let Some(cs) = self.first(n, Nt::Constructors) else {
            return;
        };
        for c in self.list(cs, Nt::Constructor, Nt::ConstructorsTail) {
            let Some((name, span)) = self.name_of(c) else {
                continue;
            };
            let sig = format!(
                "{}\n  // of {}",
                squeeze(self.text(self.cst.span(c))),
                self.idx.defs[d].name
            );
            let m = self.def_once(c, &name, Kind::Constructor, span, sig);
            self.idx.defs[m].parent = Some(d);
            self.idx.defs[m].declared = self.ty(c).map(|t| squeeze(self.text(self.cst.span(t))));
            if !self.idx.defs[d].members.contains(&m) {
                self.idx.defs[d].members.push(m);
            }
            self.declare(&name, m);
        }
    }

    fn hoist_fields(&mut self, owner: usize, fields: NodeId) {
        for f in self.list(fields, Nt::FieldDecl, Nt::FieldsTail) {
            let Some((name, span)) = self.name_of(f) else {
                continue;
            };
            let sig = format!(
                "{}: {}",
                name,
                self.ty(f)
                    .map_or(String::new(), |t| squeeze(self.text(self.cst.span(t))))
            );
            let m = self.def_once(f, &name, Kind::Field, span, sig);
            self.idx.defs[m].parent = Some(owner);
            self.idx.defs[m].declared = self.ty(f).map(|t| squeeze(self.text(self.cst.span(t))));
            if !self.idx.defs[owner].members.contains(&m) {
                self.idx.defs[owner].members.push(m);
            }
        }
    }

    fn hoist_struct(&mut self, n: NodeId) {
        let Some((name, span)) = self.name_of(n) else {
            return;
        };
        let sig = self.header(n, &[Nt::StructBody]);
        let d = self.def_once(n, &name, Kind::Struct, span, self.whole_if_short(n, sig));
        self.declare(&name, d);
        if let Some(body) = self.first(n, Nt::StructBody)
            && let Some(fields) = self.first(body, Nt::Fields)
        {
            self.hoist_fields(d, fields);
        }
    }

    fn whole_if_short(&self, n: NodeId, fallback: String) -> String {
        let w = self.whole(n);
        if w.lines().count() <= 16 { w } else { fallback }
    }

    fn hoist_enum(&mut self, n: NodeId) {
        let Some((name, span)) = self.name_of(n) else {
            return;
        };
        let sig = self.header(n, &[Nt::LBrace]);
        let d = self.def_once(n, &name, Kind::Enum, span, self.whole_if_short(n, sig));
        self.declare(&name, d);
        let Some(vs) = self.first(n, Nt::Variants) else {
            return;
        };
        for v in self.list(vs, Nt::Variant, Nt::VariantsTail) {
            let Some((vname, vspan)) = self.name_of(v) else {
                continue;
            };
            let sig = format!("{name}::{}", squeeze(self.text(self.cst.span(v))));
            let m = self.def_once(v, &vname, Kind::Variant, vspan, sig);
            self.idx.defs[m].parent = Some(d);
            if !self.idx.defs[d].members.contains(&m) {
                self.idx.defs[d].members.push(m);
            }
            // A variant is also written bare, unless that would hide a
            // name (or another variant's, which makes the bare name unusable).
            let bare = self.me(m);
            if let Some(f) = self.frames.last_mut() {
                match f.get(&vname) {
                    None => {
                        f.insert(vname.clone(), bare);
                    }
                    Some(prior) if *prior != bare => {
                        f.insert(
                            vname.clone(),
                            DefId {
                                file: usize::MAX,
                                index: 0,
                            },
                        );
                    }
                    _ => {}
                }
            }
            if let Some(body) = self.first(v, Nt::VariantBody)
                && let Some(fields) = self.first(body, Nt::Fields)
            {
                self.hoist_fields(m, fields);
            }
        }
    }

    fn hoist_module(&mut self, n: NodeId) {
        let Some((name, span)) = self.name_of(n) else {
            return;
        };
        let sig = format!("module {name}");
        let d = self.def_once(n, &name, Kind::Module, span, sig);
        self.declare(&name, d);
        let Some(block) = self.first(n, Nt::Block) else {
            return;
        };
        let Some(stmts) = self.first(block, Nt::Stmts) else {
            return;
        };
        // The members, declared in a frame of their own that is dropped.
        self.frames.push(HashMap::new());
        for s in self.stmt_nodes(stmts) {
            self.hoist(s);
        }
        let frame = self.frames.pop().unwrap_or_default();
        let mut members: Vec<usize> = frame
            .values()
            .filter(|m| m.file == self.file)
            .map(|m| m.index)
            .collect();
        members.sort_unstable();
        for m in members {
            self.idx.defs[m].parent = Some(d);
            if !self.idx.defs[d].members.contains(&m) {
                self.idx.defs[d].members.push(m);
            }
        }
    }

    fn hoist_class(&mut self, n: NodeId) {
        let Some((name, span)) = self.name_of(n) else {
            return;
        };
        let sig = self.header(n, &[Nt::ClassBody]);
        let d = self.def_once(n, &name, Kind::Class, span, self.whole_if_short(n, sig));
        self.declare(&name, d);
        let Some(body) = self.first(n, Nt::ClassBody) else {
            return;
        };
        let Some(items) = self.first(body, Nt::ClassItems) else {
            return;
        };
        for item in self.list(items, Nt::ClassItem, Nt::ClassItemsTail) {
            let item = self.inner(item);
            let (kind, stop) = match self.nt(item) {
                Some(Nt::ExternFn) => (Kind::Method, vec![]),
                Some(Nt::LawDecl) => (Kind::Law, vec![Nt::Block]),
                _ => continue,
            };
            let Some((mname, mspan)) = self.name_of(item) else {
                continue;
            };
            let sig = format!("{}\n  // of {name}", self.header(item, &stop));
            let m = self.def_once(item, &mname, kind, mspan, sig);
            self.idx.defs[m].parent = Some(d);
            self.idx.defs[m].declared = self.ty(item).map(|t| squeeze(self.text(self.cst.span(t))));
            if !self.idx.defs[d].members.contains(&m) {
                self.idx.defs[d].members.push(m);
            }
        }
    }

    fn stmt(&mut self, n: NodeId) {
        let Some(kind) = self.nt(n) else { return };
        match kind {
            Nt::LetDecl | Nt::VarDecl => self.let_decl(n),
            Nt::FnDecl | Nt::ExternFn => self.callable(n, None),
            Nt::TheoremDecl | Nt::AxiomDecl | Nt::DefDecl | Nt::LawDecl => self.callable(n, None),
            Nt::MutualDecl => {
                for item in self.mutual_items(n) {
                    self.stmt(item);
                }
            }
            Nt::InductiveDecl => self.inductive(n),
            Nt::StructDecl => self.data(n, Nt::StructBody),
            Nt::EnumDecl => self.data(n, Nt::Variants),
            Nt::EffectDecl => self.effect(n),
            Nt::ModuleDecl => {
                if let Some(b) = self.first(n, Nt::Block) {
                    self.block(b);
                }
            }
            Nt::ExternDecl => {
                for item in self.extern_items(n) {
                    match self.nt(item) {
                        Some(Nt::ExternInstance) => self.extern_instance(item),
                        _ => self.stmt(item),
                    }
                }
            }
            Nt::ClassDecl => self.class(n),
            Nt::InstanceDecl => self.instance(n),
            Nt::MacroFnDecl => {
                if let Some(f) = self.first(n, Nt::FnDecl) {
                    self.callable(f, None);
                }
            }
            Nt::SyntaxDecl | Nt::ImportDecl => {}
            _ => self.walk(n),
        }
    }

    fn let_decl(&mut self, n: NodeId) {
        let name = self.all(n, Nt::Ident).first().and_then(|i| self.ident(*i));
        let ty = self.ty(n);
        let value = self.first(n, Nt::Expr);
        if let Some(t) = ty {
            self.walk(t);
        }
        if let Some(v) = value {
            self.walk(v);
        }
        if let Some((name, span)) = name {
            let declared = ty.map(|t| squeeze(self.text(self.cst.span(t))));
            let kw = if self.nt(self.kids(n)[0]) == Some(Nt::KwVar) {
                "var"
            } else {
                "let"
            };
            let sig = match &declared {
                Some(t) => format!("{kw} {name}: {t}"),
                None => format!("{kw} {name}"),
            };
            let d = self.new_def(&name, Kind::Local, span, sig);
            self.idx.defs[d].declared = declared;
            self.idx.defs[d].site = value.map(|v| self.cst.span(v).start);
            self.declare(&name, d);
        }
    }

    /// A function, theorem, definition or law: its generics and parameters
    /// are visible to the rest of the signature and to the body.
    /// `instance_of` is the class when this is a method an instance gives.
    fn callable(&mut self, n: NodeId, instance_of: Option<DefId>) {
        self.frames.push(HashMap::new());
        let body = self.first(n, Nt::Block);
        let site = body.map(|b| self.cst.span(b).start);
        if let Some(class) = instance_of
            && let Some((name, span)) = self.name_of(n)
        {
            self.member(Some(class), span, &name);
        }
        for c in self.kids(n) {
            match self.nt(c) {
                Some(Nt::Generics) => self.generics(c),
                Some(Nt::Param) => self.param(c, site),
                Some(Nt::Block) => self.block(c),
                Some(Nt::Type | Nt::BodyType | Nt::FnResult | Nt::WhereClause | Nt::Expr) => {
                    self.walk(c)
                }
                _ => {}
            }
        }
        self.frames.pop();
    }

    /// The node of a declaration's generics: `<A>` of a function or an
    /// operation, `(A: Type)` of a type declaration.
    fn generic_node(&self, n: NodeId) -> Option<NodeId> {
        self.first(n, Nt::Generics)
            .or_else(|| self.first(n, Nt::TypeParams))
    }

    fn generics(&mut self, g: NodeId) {
        let angle = self.nt(g) == Some(Nt::Generics);
        let mut items = self.all(g, Nt::Generic);
        items.extend(self.all(g, Nt::TypeParam));
        for gen_ in items {
            if let Some(kind) = self.first(gen_, Nt::GenericKind)
                && !matches!(
                    self.text(self.cst.span(kind)).trim(),
                    "shared" | "linear" | "affine" | "copy" | "view"
                )
            {
                self.walk(kind);
            }
            if let Some((name, span)) = self.name_of(gen_) {
                let sig = squeeze(self.text(self.cst.span(gen_)));
                let shown = if angle {
                    format!("<{sig}>")
                } else {
                    format!("({sig})")
                };
                let d = self.new_def(&name, Kind::Generic, span, shown);
                self.declare(&name, d);
            }
        }
    }

    fn param(&mut self, p: NodeId, site: Option<u32>) {
        let ty = self.ty(p);
        if let Some(t) = ty {
            self.walk(t);
        }
        if let Some((name, span)) = self.name_of(p) {
            let declared = ty.map(|t| squeeze(self.text(self.cst.span(t))));
            let sig = squeeze(self.text(self.cst.span(p)));
            let d = self.new_def(&name, Kind::Param, span, sig);
            self.idx.defs[d].declared = declared;
            self.idx.defs[d].site = site;
            self.declare(&name, d);
        }
    }

    fn inductive(&mut self, n: NodeId) {
        // The family's parameters are visible to its result type and to
        // the constructors.
        self.frames.push(HashMap::new());
        for c in self.kids(n) {
            match self.nt(c) {
                Some(Nt::Param) => self.param(c, None),
                Some(Nt::Type | Nt::BodyType) => self.walk(c),
                _ => {}
            }
        }
        if let Some(cs) = self.first(n, Nt::Constructors) {
            for c in self.list(cs, Nt::Constructor, Nt::ConstructorsTail) {
                self.callable(c, None);
            }
        }
        self.frames.pop();
    }

    fn data(&mut self, n: NodeId, body: Nt) {
        self.frames.push(HashMap::new());
        if let Some(g) = self.generic_node(n) {
            self.generics(g);
        }
        let types = |this: &mut Self, fields: NodeId| {
            for f in this.list(fields, Nt::FieldDecl, Nt::FieldsTail) {
                if let Some(t) = this.ty(f) {
                    this.walk(t);
                }
            }
        };
        if body == Nt::StructBody {
            if let Some(b) = self.first(n, Nt::StructBody)
                && let Some(f) = self.first(b, Nt::Fields)
            {
                types(self, f);
            }
        } else if let Some(vs) = self.first(n, Nt::Variants) {
            for v in self.list(vs, Nt::Variant, Nt::VariantsTail) {
                let Some(vb) = self.first(v, Nt::VariantBody) else {
                    continue;
                };
                for t in self.tys(vb) {
                    self.walk(t);
                }
                if let Some(f) = self.first(vb, Nt::Fields) {
                    types(self, f);
                }
            }
        }
        self.frames.pop();
    }

    fn effect(&mut self, n: NodeId) {
        self.frames.push(HashMap::new());
        if let Some(g) = self.first(n, Nt::Generics) {
            self.generics(g);
        }
        // `effect ask(q: Text): i64` has the operation's parameters in the
        // parentheses, `effect State(T: Type) {…}` the set's.
        if let Some(params) = self.first(n, Nt::EffectParams) {
            for p in self.all(params, Nt::Param) {
                self.param(p, None);
            }
        }
        if let Some(body) = self.first(n, Nt::EffectBody) {
            // Names written as effects are uses.
            self.walk(body);
        }
        self.frames.pop();
    }

    fn extern_instance(&mut self, n: NodeId) {
        for c in self.kids(n) {
            match self.nt(c) {
                Some(Nt::Ident) => {
                    self.reference_node(c);
                }
                Some(Nt::Type | Nt::BodyType) => self.walk(c),
                _ => {}
            }
        }
    }

    fn class(&mut self, n: NodeId) {
        self.frames.push(HashMap::new());
        if let Some(g) = self.generic_node(n) {
            self.generics(g);
        }
        if let Some(body) = self.first(n, Nt::ClassBody)
            && let Some(items) = self.first(body, Nt::ClassItems)
        {
            for item in self.list(items, Nt::ClassItem, Nt::ClassItemsTail) {
                let item = self.inner(item);
                self.callable(item, None);
            }
        }
        self.frames.pop();
    }

    fn instance(&mut self, n: NodeId) {
        self.frames.push(HashMap::new());
        if let Some(g) = self.first(n, Nt::Generics) {
            self.generics(g);
        }
        // `instance<A> Class(Head) where … { methods }`: the class is the
        // identifier that is not inside the generics.
        let class = self
            .all(n, Nt::Ident)
            .first()
            .and_then(|i| self.reference_node(*i));
        for c in self.kids(n) {
            if let Some(Nt::Type | Nt::BodyType | Nt::WhereClause) = self.nt(c) {
                self.walk(c)
            }
        }
        if let Some(body) = self.first(n, Nt::InstanceBody)
            && let Some(items) = self.first(body, Nt::InstanceItems)
        {
            for item in self.list(items, Nt::InstanceItem, Nt::InstanceItemsTail) {
                let item = self.inner(item);
                self.callable(item, class);
            }
        }
        self.frames.pop();
    }

    fn walk(&mut self, n: NodeId) {
        let Some(kind) = self.nt(n) else { return };
        match kind {
            Nt::Ident => {
                self.reference_node(n);
            }
            Nt::PathExpr | Nt::CondPath => {
                self.path_expr(n);
            }
            Nt::Postfix | Nt::CondPostfix => self.postfix(n),
            Nt::Expr => {
                if self.has(n, Nt::FatArrow) {
                    self.lambda(n)
                } else {
                    self.walk_kids(n)
                }
            }
            Nt::Seq | Nt::BodyType | Nt::Cond => self.sequence(n),
            Nt::Operand | Nt::CondOperand => {
                let open = self.operand(n, false);
                for _ in 0..open {
                    self.frames.pop();
                }
            }
            Nt::Block => self.block(n),
            // A block in an expression, `Brace: LBrace BraceBody`; a record type has no statements.
            Nt::BraceBody if self.first(n, Nt::BraceBody).is_some() => self.walk_kids(n),
            Nt::BraceBody if self.first(n, Nt::Stmts).is_some() => self.block(n),
            Nt::BraceBody if self.first(n, Nt::RecordType).is_none() => {
                // `{ s … }`: its statements are its own `Stmt` and `StmtsTail`.
                self.frames.push(HashMap::new());
                self.stmts_in_frame(n);
                self.frames.pop();
            }
            Nt::MatchExpr => self.match_expr(n),
            Nt::HandleExpr => self.handle(n),
            Nt::BudgetExpr => {
                // `budget(steps: n) { … }`: `steps` is a word of the form.
                for c in self.kids(n) {
                    if matches!(self.nt(c), Some(Nt::Expr | Nt::Block)) {
                        self.walk(c);
                    }
                }
            }
            Nt::MacroCall => self.macro_call(n),
            Nt::QuoteExpr => self.quote(n),
            Nt::SyntaxLit => self.syntax_lit(n),
            Nt::TagPrefix => {
                if let Some(i) = self.first(n, Nt::Ident) {
                    self.reference_node(i);
                }
            }
            Nt::FnDecl | Nt::ExternFn | Nt::TheoremDecl | Nt::LawDecl => self.callable(n, None),
            Nt::Hole | Nt::HoleExpr => {}
            _ => self.walk_kids(n),
        }
    }

    fn walk_kids(&mut self, n: NodeId) {
        for c in self.kids(n) {
            self.walk(c);
        }
    }

    /// `A`, `Shape::Circle`, `Point { x: 1 }`; the declaration it names.
    fn path_expr(&mut self, n: NodeId) -> Option<DefId> {
        let idents = self.all(n, Nt::Ident);
        let mut cur = None;
        for (i, (name, span)) in self.path_segments(&idents).into_iter().enumerate() {
            cur = if i == 0 {
                self.reference(span, &name)
            } else {
                self.member(cur, span, &name)
            };
        }
        if let Some(rb) = self.first(n, Nt::RecordBody) {
            self.record_body(rb, cur);
        }
        cur
    }

    fn record_body(&mut self, rb: NodeId, owner: Option<DefId>) {
        let fields = self.first(rb, Nt::RecordBodyGroup).unwrap_or(rb);
        for f in self.list(fields, Nt::FieldInit, Nt::RecordTail) {
            if let Some(i) = self.first(f, Nt::Ident)
                && let Some((name, span)) = self.ident(i)
            {
                if owner.is_some() {
                    self.member(owner, span, &name);
                } else {
                    self.field_by_name(span, &name);
                }
            }
            if let Some(e) = self.first(f, Nt::Expr) {
                self.walk(e);
            }
        }
    }

    fn peel(&self, id: NodeId) -> NodeId {
        let mut id = id;
        while matches!(
            self.nt(id),
            Some(
                Nt::Expr
                    | Nt::Seq
                    | Nt::Operand
                    | Nt::Postfix
                    | Nt::Primary
                    | Nt::Cond
                    | Nt::CondOperand
                    | Nt::CondPostfix
                    | Nt::CondPrimary
                    | Nt::Item
                    | Nt::Type
                    | Nt::BodyType
            )
        ) {
            let kids = self.kids(id);
            match kids.as_slice() {
                [only] => id = *only,
                _ => break,
            }
        }
        id
    }

    fn postfix(&mut self, n: NodeId) {
        let kids = self.kids(n);
        let mut cur = None;
        for (i, c) in kids.iter().enumerate() {
            match self.nt(*c) {
                Some(Nt::Primary | Nt::CondPrimary) if i == 0 => {
                    let p = self.peel(*c);
                    if matches!(self.nt(p), Some(Nt::PathExpr | Nt::CondPath)) {
                        cur = self.path_expr(p);
                    } else {
                        self.walk(*c);
                    }
                }
                Some(Nt::PostOp) => {
                    let Some(op) = self.kids(*c).first().copied() else {
                        continue;
                    };
                    match self.nt(op) {
                        Some(Nt::Field) => {
                            if let Some(i) = self.first(op, Nt::Ident)
                                && let Some((name, span)) = self.ident(i)
                            {
                                let owner_has_members = cur.is_some_and(|d| {
                                    matches!(
                                        self.def_of(d).kind,
                                        Kind::Module
                                            | Kind::Class
                                            | Kind::Enum
                                            | Kind::Inductive
                                            | Kind::Struct
                                    )
                                });
                                cur = if owner_has_members {
                                    self.member(cur, span, &name)
                                } else {
                                    self.field_by_name(span, &name)
                                };
                            }
                        }
                        _ => {
                            cur = None;
                            self.walk(op);
                        }
                    }
                }
                _ => self.walk(*c),
            }
        }
    }

    /// The parameters a lambda's left side names: `x`, `(x, y)`, `(x: A)`.
    fn lambda_params(&self, left: NodeId) -> Option<Vec<(String, Span, Option<NodeId>)>> {
        let p = self.peel(left);
        let one = |this: &Self, id: NodeId| -> Option<(String, Span)> {
            let id = this.peel(id);
            match this.nt(id) {
                Some(Nt::PathExpr) => {
                    let idents = this.all(id, Nt::Ident);
                    match idents.as_slice() {
                        [i] if !this.has(id, Nt::RecordBody) => this.ident(*i),
                        _ => None,
                    }
                }
                // `&v`: a borrowed parameter.
                Some(Nt::Operand | Nt::CondOperand) => {
                    let post = this
                        .first(id, Nt::Postfix)
                        .or_else(|| this.first(id, Nt::CondPostfix))?;
                    let inner = this.peel(post);
                    let idents = this.all(inner, Nt::Ident);
                    match idents.as_slice() {
                        [i] => this.ident(*i),
                        _ => None,
                    }
                }
                _ => None,
            }
        };
        match self.nt(p) {
            Some(Nt::PathExpr) => {
                let (name, span) = one(self, p)?;
                Some(vec![(name, span, None)])
            }
            Some(Nt::Paren) => {
                let mut out = Vec::new();
                for item in self.all(p, Nt::Item) {
                    let e = self.first(item, Nt::Expr)?;
                    let (name, span) = one(self, e)?;
                    out.push((name, span, self.ty(item)));
                }
                Some(out)
            }
            _ => None,
        }
    }

    fn lambda(&mut self, n: NodeId) {
        let kids = self.kids(n);
        let (Some(left), Some(body)) = (kids.first().copied(), kids.last().copied()) else {
            return;
        };
        let Some(params) = self.lambda_params(left) else {
            self.walk_kids(n);
            return;
        };
        let site = Some(self.cst.span(body).start);
        self.frames.push(HashMap::new());
        for (name, span, ty) in params {
            if let Some(t) = ty {
                self.walk(t);
            }
            if name != "_" {
                let declared = ty.map(|t| squeeze(self.text(self.cst.span(t))));
                let sig = match &declared {
                    Some(t) => format!("{name}: {t}"),
                    None => name.clone(),
                };
                let d = self.new_def(&name, Kind::Param, span, sig);
                self.idx.defs[d].declared = declared;
                self.idx.defs[d].site = site;
                self.declare(&name, d);
            }
        }
        self.walk(body);
        self.frames.pop();
    }

    /// A flat sequence of operands and operators. A binder `∀ x: A.` scopes over the rest of the
    /// sequence, and the named parameters of `(x: A) -> B` over what follows.
    fn sequence(&mut self, n: NodeId) {
        let kids = self.kids(n);
        let mut open = 0;
        for (i, c) in kids.iter().enumerate() {
            match self.nt(*c) {
                Some(Nt::Operand | Nt::CondOperand) => {
                    let arrow = kids
                        .get(i + 1)
                        .is_some_and(|op| self.has(*op, Nt::ThinArrow));
                    open += self.operand(*c, arrow);
                }
                _ => self.walk(*c),
            }
        }
        for _ in 0..open {
            self.frames.pop();
        }
    }

    /// The operand `n`; the frames it leaves open for the rest of its sequence.
    fn operand(&mut self, n: NodeId, before_arrow: bool) -> usize {
        let mut open = 0;
        for c in self.kids(n) {
            match self.nt(c) {
                Some(Nt::PrefixOp) => match self.first(c, Nt::Binder) {
                    Some(binder) => {
                        self.binder(binder);
                        open += 1;
                    }
                    None => self.walk_kids(c),
                },
                Some(Nt::Postfix | Nt::CondPostfix) if before_arrow => match self.peel_paren(c) {
                    Some(paren) => {
                        self.arrow_params(paren);
                        open += 1;
                    }
                    None => self.walk(c),
                },
                _ => self.walk(c),
            }
        }
        open
    }

    /// The parenthesized list `n` is, when it is nothing else.
    fn peel_paren(&self, n: NodeId) -> Option<NodeId> {
        let p = self.peel(n);
        (self.nt(p) == Some(Nt::Paren)).then_some(p)
    }

    /// `∀ x: A.`: opens the scope of `x`; the caller closes it.
    /// `∀ x: A, y: B.`: each name is in scope in the types after it and in the body.
    fn binder(&mut self, n: NodeId) {
        let idents: Vec<NodeId> = self
            .kids(n)
            .into_iter()
            .filter(|c| self.nt(*c) == Some(Nt::Ident))
            .collect();
        let tys = self.tys(n);
        let sig = squeeze(&self.header(n, &[Nt::QDot]));
        self.frames.push(HashMap::new());
        for (k, ident) in idents.into_iter().enumerate() {
            let ty = tys.get(k).copied();
            if let Some(t) = ty {
                self.walk(t);
            }
            if let Some((name, span)) = self.ident(ident) {
                let declared = ty.map(|t| squeeze(self.text(self.cst.span(t))));
                let d = self.new_def(&name, Kind::Binder, span, sig.clone());
                self.idx.defs[d].declared = declared;
                self.declare(&name, d);
            }
        }
    }

    /// The parameters of `(x: A, &y: B) -> C`: opens the scope of the names; the caller closes it.
    fn arrow_params(&mut self, paren: NodeId) {
        self.frames.push(HashMap::new());
        for item in self.all(paren, Nt::Item) {
            let (Some(name_expr), Some(ty)) = (self.first(item, Nt::Expr), self.ty(item)) else {
                self.walk(item);
                continue;
            };
            self.walk(ty);
            let p = self.peel(name_expr);
            let idents = self.all(p, Nt::Ident);
            if self.nt(p) == Some(Nt::PathExpr)
                && let [i] = idents.as_slice()
                && let Some((name, span)) = self.ident(*i)
            {
                let declared = Some(squeeze(self.text(self.cst.span(ty))));
                let d = self.new_def(
                    &name,
                    Kind::Binder,
                    span,
                    squeeze(self.text(self.cst.span(item))),
                );
                self.idx.defs[d].declared = declared;
                self.declare(&name, d);
            } else {
                self.walk(name_expr);
            }
        }
    }

    fn match_expr(&mut self, n: NodeId) {
        for c in self.kids(n) {
            match self.nt(c) {
                Some(Nt::Arms) => {
                    for arm in self.list(c, Nt::Arm, Nt::ArmsTail) {
                        self.arm(arm);
                    }
                }
                _ => self.walk(c),
            }
        }
    }

    fn arm(&mut self, arm: NodeId) {
        self.frames.push(HashMap::new());
        let body = self.first(arm, Nt::ArmBody);
        let site = body.map(|b| self.cst.span(b).start);
        for c in self.kids(arm) {
            match self.nt(c) {
                Some(Nt::Pattern) => self.pattern(c, site),
                Some(Nt::Cond | Nt::ArmBody) => self.walk(c),
                _ => {}
            }
        }
        self.frames.pop();
    }

    fn pattern(&mut self, p: NodeId, site: Option<u32>) {
        for alt in self.all(p, Nt::PatternAlt) {
            for c in self.kids(alt) {
                if self.nt(c) == Some(Nt::PathPattern) {
                    self.path_pattern(c, site);
                }
            }
        }
    }

    /// Binds `name` in the arm, once for an or-pattern's alternatives.
    fn bind_pattern(
        &mut self,
        name: &str,
        span: Span,
        site: Option<u32>,
        pinned: Option<&'static str>,
    ) {
        if let Some(prior) = self.frames.last().and_then(|f| f.get(name)).copied()
            && prior.file == self.file
            && self.idx.defs[prior.index].kind == Kind::PatternVar
        {
            self.idx.defs[prior.index].spans.push(span);
            if pinned.is_some() {
                self.idx.defs[prior.index].pinned = pinned;
            }
            return;
        }
        let d = self.new_def(name, Kind::PatternVar, span, name.to_string());
        self.idx.defs[d].site = site;
        self.idx.defs[d].pinned = pinned;
        self.declare(name, d);
    }

    fn path_pattern(&mut self, n: NodeId, site: Option<u32>) {
        let idents = self.path_segments(&self.all(n, Nt::Ident));
        let args = self.first(n, Nt::PatternArgs);
        let mut cur = None;
        if let [(name, span)] = idents.as_slice()
            && args.is_none()
        {
            let (name, span) = (name.clone(), *span);
            if name == "_" {
                return;
            }
            let known = self.lookup(&name).filter(|d| {
                matches!(
                    self.def_of(*d).kind,
                    Kind::Constructor | Kind::Variant | Kind::Struct | Kind::Fn | Kind::Definition
                )
            });
            match known {
                Some(d) => self.add_ref(span, d, false),
                None => self.bind_pattern(&name, span, site, None),
            }
            return;
        }
        for (i, (name, span)) in idents.into_iter().enumerate() {
            cur = if i == 0 {
                self.reference(span, &name)
            } else {
                self.member(cur, span, &name)
            };
        }
        let Some(args) = args else { return };
        for c in self.kids(args) {
            match self.nt(c) {
                Some(Nt::Pattern) => self.pattern(c, site),
                Some(Nt::FieldPatterns) => {
                    for fp in self.list(c, Nt::FieldPattern, Nt::FieldPatternsTail) {
                        let Some(i) = self.first(fp, Nt::Ident) else {
                            continue;
                        };
                        let Some((name, span)) = self.ident(i) else {
                            continue;
                        };
                        match self.first(fp, Nt::Pattern) {
                            Some(sub) => {
                                self.member(cur, span, &name);
                                self.pattern(sub, site);
                            }
                            None => {
                                // `Point { x }` names the field and binds a
                                // variable of the same name; renaming one
                                // would change the other.
                                self.bind_pattern(
                                    &name,
                                    span,
                                    site,
                                    Some("analyzer-pinned-field-pun"),
                                );
                            }
                        }
                    }
                }
                _ => {}
            }
        }
    }

    fn handle(&mut self, n: NodeId) {
        let Some(subject) = self.first(n, Nt::HandleSubject) else {
            return;
        };
        if let Some(b) = self.first(subject, Nt::Block) {
            self.block(b);
        }
        let Some(tail) = self.first(subject, Nt::HandleTail) else {
            return;
        };
        for with in self.all(tail, Nt::HandleWith) {
            let Some(hs) = self.first(with, Nt::Handlers) else {
                continue;
            };
            for h in self.list(hs, Nt::Handler, Nt::HandlersTail) {
                let h = self.inner_handler(h);
                self.handler(h);
            }
        }
    }

    fn inner_handler(&self, h: NodeId) -> NodeId {
        match self.kids(h).first() {
            Some(c) if matches!(self.nt(*c), Some(Nt::OperationHandler | Nt::ReturnHandler)) => *c,
            _ => h,
        }
    }

    fn handler(&mut self, h: NodeId) {
        self.frames.push(HashMap::new());
        let body = self
            .kids(h)
            .into_iter()
            .rev()
            .find(|c| self.nt(*c) == Some(Nt::Expr));
        let site = body.map(|b| self.cst.span(b).start);
        let mut after_paren = false;
        for c in self.kids(h) {
            match self.nt(c) {
                Some(Nt::OperationName) => {
                    if let Some(i) = self.first(c, Nt::Ident) {
                        self.reference_node(i);
                    }
                }
                Some(Nt::Pattern) => self.pattern(c, site),
                Some(Nt::RParen) => after_paren = true,
                // The continuation: `ask(q), k => …`.
                Some(Nt::Ident) if after_paren => {
                    if let Some((name, span)) = self.ident(c) {
                        let d = self.new_def(
                            &name,
                            Kind::Param,
                            span,
                            format!("{name}  // the continuation"),
                        );
                        self.idx.defs[d].site = site;
                        self.declare(&name, d);
                    }
                }
                Some(Nt::Cond | Nt::Expr) => self.walk(c),
                _ => {}
            }
        }
        self.frames.pop();
    }

    fn macro_call(&mut self, n: NodeId) {
        self.idx.macro_calls.push(self.cst.span(n));
        for c in self.kids(n) {
            match self.nt(c) {
                Some(Nt::MacroName) => {
                    // The token is the name and its `!`; the reference is
                    // recorded under `m!`, with the name's span.
                    let whole = self.cst.span(c);
                    let name = self.text(whole).to_string();
                    let span = Span::new(whole.start, whole.end - 1);
                    self.reference(span, &name);
                }
                Some(Nt::Expr) => self.walk(c),
                _ => {}
            }
        }
    }

    fn syntax_lit(&mut self, n: NodeId) {
        let span = self.cst.span(n);
        let text = self.text(span).to_string();
        for (at, w) in words_at(&text) {
            let start = span.start + at as u32;
            self.idx
                .opaque
                .push((Span::new(start, start + w.len() as u32), w.to_string()));
        }
        self.splices_in(span);
        // ``math`1 + 2` `` or `` ```math … ``` ``: the syntax's name leads.
        let lead = text.trim_start_matches('`');
        let skipped = (text.len() - lead.len()) as u32;
        let name: String = lead
            .chars()
            .take_while(|c| c.is_alphanumeric() || *c == '_')
            .collect();
        if !name.is_empty()
            && let Some(d) = self.lookup(&format!("syntax {name}"))
        {
            let start = span.start + skipped;
            self.add_ref(Span::new(start, start + name.len() as u32), d, false);
        }
    }

    /// The expressions spliced into the literal at `lit`: tauto, read in the scope of the
    /// literal. Each is a tree of its own, so its names are shifted to where it is written.
    fn splices_in(&mut self, lit: Span) {
        let splices = self.splices;
        for sp in splices {
            if sp.start < lit.start || sp.end > lit.end {
                continue;
            }
            let Some(root) = sp.cst.root() else { continue };
            let (cst, src) = (self.cst, self.src);
            let saved = (std::mem::take(&mut self.node_def), self.quoting);
            let (defs, refs, unresolved, opaque) = (
                self.idx.defs.len(),
                self.idx.refs.len(),
                self.idx.unresolved.len(),
                self.idx.opaque.len(),
            );
            self.cst = &sp.cst;
            self.src = &sp.src;
            self.quoting = 0;
            self.walk(root);
            self.cst = cst;
            self.src = src;
            (self.node_def, self.quoting) = saved;
            let shift = |s: Span| Span::new(s.start + sp.start, s.end + sp.start);
            for d in &mut self.idx.defs[defs..] {
                d.spans.iter_mut().for_each(|s| *s = shift(*s));
            }
            for r in &mut self.idx.refs[refs..] {
                r.span = shift(r.span);
            }
            for (s, _) in &mut self.idx.unresolved[unresolved..] {
                *s = shift(*s);
            }
            for (s, _) in &mut self.idx.opaque[opaque..] {
                *s = shift(*s);
            }
        }
    }

    /// `quote { … }`: nothing in it is resolved, except what is filled in:
    /// `$x` is the local `x` of the macro's function and `$(e)` an expression.
    fn quote(&mut self, n: NodeId) {
        self.quoting += 1;
        self.quote_nodes(n);
        self.quoting -= 1;
    }

    fn quote_nodes(&mut self, n: NodeId) {
        for c in self.kids(n) {
            match self.nt(c) {
                Some(Nt::SpliceExpr) => {
                    let saved = self.quoting;
                    self.quoting = 0;
                    if let Some(e) = self.first(c, Nt::Expr) {
                        self.walk(e);
                    }
                    self.quoting = saved;
                }
                Some(Nt::Ident) => {
                    if let Some((name, span)) = self.ident(c) {
                        if let Some(bare) = name.strip_prefix('$') {
                            let saved = self.quoting;
                            self.quoting = 0;
                            self.reference(Span::new(span.start + 1, span.end), bare);
                            self.quoting = saved;
                        } else {
                            self.idx.opaque.push((span, name));
                        }
                    }
                }
                Some(Nt::SyntaxLit) => self.syntax_lit(c),
                Some(_) => self.quote_nodes(c),
                None => {}
            }
        }
    }
}

/// The identifier-like words of a text.
pub fn words(text: &str) -> impl Iterator<Item = &str> {
    text.split(|c: char| !(c.is_alphanumeric() || c == '_'))
        .filter(|w| !w.is_empty())
}

/// The words of a text, with the byte offset each starts at.
fn words_at(text: &str) -> Vec<(usize, &str)> {
    let mut out = Vec::new();
    let mut start = None;
    for (i, c) in text.char_indices() {
        let word = c.is_alphanumeric() || c == '_';
        match (word, start) {
            (true, None) => start = Some(i),
            (false, Some(s)) => {
                out.push((s, &text[s..i]));
                start = None;
            }
            _ => {}
        }
    }
    if let Some(s) = start {
        out.push((s, &text[s..]));
    }
    out
}

pub fn squeeze(text: &str) -> String {
    text.split_whitespace().collect::<Vec<_>>().join(" ")
}
