//! `syntax` declarations and their literals: the types a grammar makes and the value a literal is.
//!
//! The tables of a grammar are looked up by the grammar's SHA-256 in
//! `.tauto-syntax/<sha256>.tables`, in a directory the program is read from
//! or above it (`tauto syntax gen` writes them). After the program is read
//! (`expand`), a `syntax` is its types and a literal is a term that builds the
//! literal's typed tree; the checkers see only that.

use std::cell::RefCell;
use std::collections::HashMap;
use std::path::{Path, PathBuf};
use std::sync::Arc;
use tauto_message::{Message, msg};

use tauto_parol::Span;
use tauto_syntax::{
    Ast, FieldTy, Limits, ParseError, Payload, Tables, TypeDef, build_ast, parse, sha256_hex,
};

pub use tauto_syntax::{start_symbols, tables_key};

use tauto_surface::macros::Node;
use tauto_surface::surface::qualify::SEPARATOR;
use tauto_surface::surface::{
    DataConstructor, DataDecl, FnDecl, Program, Stmt, SurfaceTerm, SyntaxLit, TermKind,
};

thread_local! {
    static SEARCH: RefCell<Vec<PathBuf>> = const { RefCell::new(Vec::new()) };
}

/// The directories now set, which `set_search_dirs` or `with_search_dirs` gave this thread.
pub fn search_dirs() -> Vec<PathBuf> {
    SEARCH.with(|s| s.borrow().clone())
}

/// Sets the directories whose `.tauto-syntax` (or whose ancestors') tables
/// are read, and returns the ones set before.
pub fn set_search_dirs(dirs: Vec<PathBuf>) -> Vec<PathBuf> {
    SEARCH.with(|s| std::mem::replace(&mut *s.borrow_mut(), dirs))
}

pub fn with_search_dirs<T>(dirs: Vec<PathBuf>, f: impl FnOnce() -> T) -> T {
    struct Restore(Vec<PathBuf>);

    impl Drop for Restore {
        fn drop(&mut self) {
            set_search_dirs(std::mem::take(&mut self.0));
        }
    }

    let restore = Restore(set_search_dirs(dirs));
    let out = f();
    drop(restore);
    out
}

pub fn table_path(dir: &Path, sha: &str) -> PathBuf {
    dir.join(".tauto-syntax").join(format!("{sha}.tables"))
}

/// Whether the table file text was made under the current pargen revision.
pub fn tables_text_is_current(text: &str) -> bool {
    Tables::read(text).is_ok_and(|t| t.is_current())
}

fn find_tables(sha: &str) -> Option<PathBuf> {
    SEARCH.with(|s| {
        s.borrow().iter().find_map(|dir| {
            let dir = dir.canonicalize().unwrap_or_else(|_| dir.clone());
            dir.ancestors()
                .map(|d| table_path(d, sha))
                .find(|p| p.is_file())
        })
    })
}

pub fn grammar_sha(grammar: &str) -> String {
    sha256_hex(grammar.as_bytes())
}

thread_local! {
    /// Tables already read, by the hash of their grammar: what a run's
    /// `syn_parse` reads its grammar's tables from.
    static READ: RefCell<HashMap<String, std::sync::Arc<Tables>>> = RefCell::new(HashMap::new());
    /// How many times tables were looked for and not found.
    static MISSED: std::cell::Cell<u64> = const { std::cell::Cell::new(0) };
}

/// How many times this thread looked for tables and did not find them. Tables once found are
/// kept for the thread (by the hash of their grammar); tables not found are looked for again.
pub fn tables_missed() -> u64 {
    MISSED.with(std::cell::Cell::get)
}

/// The tables shipped with a source library, by the hash of their grammar, as
/// text: every thread reads them, whichever one registered them.
static SHIPPED: std::sync::Mutex<Vec<(String, &'static str)>> = std::sync::Mutex::new(Vec::new());

/// Registers a table shipped with a source library. Its grammar fingerprint is
/// read from the validated table, using the same decoder as on-disk tables.
pub fn register_tables(text: &'static str) -> Result<(), String> {
    let sha = Tables::read(text)
        .map_err(|e| e.to_string())?
        .grammar_sha256()
        .to_string();
    let mut shipped = SHIPPED.lock().unwrap_or_else(|e| e.into_inner());
    if !shipped.iter().any(|(s, _)| *s == sha) {
        shipped.push((sha, text));
    }
    Ok(())
}

fn shipped_tables(sha: &str) -> Option<Tables> {
    let text = SHIPPED
        .lock()
        .unwrap_or_else(|e| e.into_inner())
        .iter()
        .find(|(s, _)| s == sha)
        .map(|(_, t)| *t)?;
    Tables::read(text).ok()
}

pub fn load_tables(grammar: &str) -> Result<std::sync::Arc<Tables>, String> {
    tables_of(&grammar_sha(grammar))
}

pub fn tables_of(sha: &str) -> Result<std::sync::Arc<Tables>, String> {
    tables_or_why(sha).map_err(|m| m.to_string())
}

fn tables_or_why(sha: &str) -> Result<std::sync::Arc<Tables>, Message> {
    if let Some(t) = READ.with(|r| r.borrow().get(sha).cloned()) {
        return Ok(t);
    }
    let tables =
        std::sync::Arc::new(read_tables(sha).inspect_err(|_| MISSED.with(|m| m.set(m.get() + 1)))?);
    READ.with(|r| r.borrow_mut().insert(sha.to_string(), tables.clone()));
    Ok(tables)
}

/// The tables kept under `key` ([`tauto_syntax::tables_key`]).
fn read_tables(key: &str) -> Result<Tables, Message> {
    let sha = key.split('.').next().unwrap_or(key);
    if key != sha {
        return read_tables_at(key, sha);
    }
    if let Some(tables) = shipped_tables(sha) {
        if !tables.is_current() {
            return Err(msg!(
                "surface-tables-out-of-date",
                path = "(shipped with the library)"
            ));
        }
        return Ok(tables);
    }
    read_tables_at(key, sha)
}

fn read_tables_at(key: &str, sha: &str) -> Result<Tables, Message> {
    let Some(path) = find_tables(key) else {
        return Err(msg!(
            "surface-tables-missing",
            grammar = &sha[..12.min(sha.len())]
        ));
    };
    // An error of the system or of the tables' format, after the path.
    let text = std::fs::read_to_string(&path)
        .map_err(|e| Message::text(format!("{}: {e}", path.display())))?;
    let tables =
        Tables::read(&text).map_err(|e| Message::text(format!("{}: {e}", path.display())))?;
    if tables.grammar_sha256() != sha {
        return Err(msg!(
            "surface-tables-of-another-grammar",
            path = path.display().to_string()
        ));
    }
    if !tables.is_current() {
        return Err(msg!(
            "surface-tables-out-of-date",
            path = path.display().to_string()
        ));
    }
    Ok(tables)
}

/// The `=> struct Eqn, …` clause of `syntax name` (or `inductive syntax name`) with `tables`: the
/// list of what it makes.
pub fn generated_clause(name: &str, tables: &Tables, inductive: bool) -> String {
    let span = Span::default();
    let mut out = type_decls(name, tables, span);
    out.extend(parse_fn(name, tables, span));
    if inductive {
        out.extend(
            inductive_decls(name, tables, span)
                .map(|(s, _)| s)
                .unwrap_or_default(),
        );
    }
    tauto_surface::generated::clause(&listed_names(name, &out), true)
}

/// What `stmts`, made by `syntax name`, declare, as the list writes them: without the module
/// `name` the names live under.
fn listed_names(name: &str, stmts: &[Stmt]) -> Vec<(String, String)> {
    let mut made = Vec::new();
    for s in stmts {
        tauto_surface::generated::declared(s, &mut made);
    }
    let module = format!("{name}{SEPARATOR}");
    for (_, n) in &mut made {
        if let Some(short) = n.strip_prefix(&module) {
            *n = short.to_string();
        }
    }
    made
}

#[derive(Clone)]
pub struct Syntax {
    pub tables: std::sync::Arc<Tables>,
    /// The start tree declaration in the syntax definition's binding session.
    pub start_reference: Option<tauto_surface::identity::Name>,
    /// The file that declares the syntax: the names its literals' values are
    /// built with are read as that file reads them.
    pub file: Option<usize>,
    /// The start symbols after the first (`%start A, B`): the trees a macro argument may also be.
    pub others: Vec<OtherStart>,
}

/// A start symbol of a syntax other than its first, with the tables made for it.
#[derive(Clone)]
pub struct OtherStart {
    pub symbol: String,
    pub tables: std::sync::Arc<Tables>,
    /// Its tree's declaration in the syntax definition's binding session.
    pub reference: Option<tauto_surface::identity::Name>,
}

/// What a function registered with `syntax s … with fmt f, tokens g` is for.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Role {
    Fmt,
    Tokens,
}

impl Role {
    pub fn word(self) -> &'static str {
        match self {
            Role::Fmt => "fmt",
            Role::Tokens => "tokens",
        }
    }
}

/// A function registered for a syntax; its source name is bound with the program.
#[derive(Debug, Clone, PartialEq)]
pub struct Registration {
    pub syntax: String,
    pub role: Role,
    pub function: tauto_surface::surface::Name,
    pub span: Span,
}

impl Syntax {
    pub fn start_type(&self, name: &str) -> Option<String> {
        Some(format!("{name}::{}", start_type_name(&self.tables)?))
    }

    /// Whether `ty` is the tree of a start symbol: `Some(None)` for the first, `Some(Some(B))`
    /// for another `B`.
    pub fn start_of(&self, ty: &tauto_surface::identity::Name) -> Option<Option<String>> {
        if self.start_reference.as_ref() == Some(ty) {
            return Some(None);
        }
        self.others
            .iter()
            .find(|o| o.reference.as_ref() == Some(ty))
            .map(|o| Some(o.symbol.clone()))
    }
}

/// The name of the type of the tables' start symbol, within its syntax.
fn start_type_name(tables: &Tables) -> Option<&str> {
    Some(
        match tables.schema().types.get(tables.start_type()? as usize)? {
            TypeDef::Struct { name, .. } | TypeDef::Enum { name, .. } => name.as_str(),
        },
    )
}

/// Reads the `syntax` declarations and literals of a program (whose files are
/// all read). Errors are left in `program.errors`.
pub fn expand(mut program: Program) -> Program {
    let mut cx = Syntaxes::default();
    program.stmts = cx.declare_all(std::mem::take(&mut program.stmts));
    for s in &mut program.stmts {
        cx.literals(s);
    }
    program.errors.extend(cx.errors);
    program
}

/// A syntax literal that was read, for the editor (`tauto_analyzer::editor`).
#[derive(Clone)]
pub struct LiteralUse {
    pub syntax: String,
    pub tables: std::sync::Arc<Tables>,
    pub lit: SyntaxLit,
}

#[derive(Default, Clone)]
pub struct Syntaxes {
    pub map: HashMap<String, Syntax>,
    pub errors: Vec<(Message, Span)>,
    pub fixes: Vec<(Span, tauto_surface::surface::Fix)>,
    pub uses: RefCell<Vec<LiteralUse>>,
    /// The file whose statements are being read, when the files are known: a syntax it
    /// declares keeps it ([`Syntax::file`]).
    pub file: Option<usize>,
    pub registrations: Vec<Registration>,
    definitions: HashMap<usize, tauto_surface::resolve::Resolver>,
    /// Executable declarations emitted by inductive syntax declarations.
    pub generated_executable: std::collections::HashSet<tauto_surface::identity::Name>,
    pending_executable: Vec<(usize, String)>,
    /// How many bytes of [`INDUCTIVE_TEXT_BASE`] on the text `inductive_syntax!` makes has
    /// taken so far: each declaration's text is read at a place of its own.
    inductive_text: u32,
    /// The texts made there: the first place, how many bytes, and where the
    /// declaration that made each was written.
    pub inductive_texts: Vec<(u32, u32, u32)>,
    /// The syntaxes of files the file being read does not see ([`Syntaxes::see`]).
    shelved: Vec<(String, Syntax)>,
}

/// Where the text that `inductive_syntax!` makes for the proof side is read: past what the
/// expansions of macros take, below the prelude. It is not the file's text, so no place of it
/// may be a byte of the file (a checker that keys by place, or a step that erases the
/// declarations by their places, would take it for what is written there).
pub const INDUCTIVE_TEXT_BASE: u32 = tauto_surface::macros::EXPANSION_BASE + (1 << 29);

impl Syntaxes {
    /// Keeps to the syntaxes of the files the next file sees: one declared by a file `unseen`
    /// says it does not see is neither read by its literals nor in the way of a syntax of the
    /// same name it declares.
    pub fn see(&mut self, unseen: &dyn Fn(usize) -> bool) {
        let hidden = |s: &Syntax| s.file.is_some_and(|f| unseen(f));
        let shown: Vec<String> = self
            .map
            .iter()
            .filter(|(_, s)| hidden(s))
            .map(|(n, _)| n.clone())
            .collect();
        for name in shown {
            if let Some(syntax) = self.map.remove(&name) {
                self.shelved.push((name, syntax));
            }
        }
        let shelved = std::mem::take(&mut self.shelved);
        for (name, syntax) in shelved {
            if hidden(&syntax) || self.map.contains_key(&name) {
                self.shelved.push((name, syntax));
            } else {
                self.map.insert(name, syntax);
            }
        }
    }

    pub fn bind_definitions(&mut self, file: usize, bindings: tauto_surface::resolve::Resolver) {
        for (name, syntax) in &mut self.map {
            if syntax.file == Some(file) {
                syntax.start_reference = syntax
                    .start_type(name)
                    .and_then(|spelling| bindings.source_reference(&spelling));
                for other in &mut syntax.others {
                    other.reference = start_type_name(&other.tables)
                        .and_then(|ty| bindings.source_reference(&format!("{name}::{ty}")));
                }
            }
        }
        for (_, spelling) in self
            .pending_executable
            .iter()
            .filter(|(owner, _)| *owner == file)
        {
            if let Some(reference) = bindings.source_reference(spelling) {
                self.generated_executable.insert(reference);
            }
        }
        self.pending_executable.retain(|(owner, _)| *owner != file);
        self.definitions.insert(file, bindings);
    }
    /// The statements without the `syntax` declarations, followed (each at its
    /// place) by the types and the `.parse` function they make.
    pub fn declare_all(&mut self, stmts: Vec<Stmt>) -> Vec<Stmt> {
        let mut out = Vec::new();
        for stmt in stmts {
            match stmt {
                Stmt::Syntax {
                    name,
                    grammar,
                    inductive,
                    generates,
                    uses,
                    span,
                } => self.declare(
                    &name, &grammar, inductive, &generates, &uses, span, &mut out,
                ),
                other => out.push(other),
            }
        }
        out
    }

    pub fn literals(&mut self, s: &mut Stmt) {
        tauto_surface::surface::walk::stmt(s, &mut |t| self.term(t));
    }

    fn declare(
        &mut self,
        name: &str,
        grammar: &SyntaxLit,
        inductive: bool,
        generates: &tauto_surface::surface::Generates,
        uses: &[tauto_surface::surface::SyntaxUse],
        span: Span,
        out: &mut Vec<Stmt>,
    ) {
        let first = out.len();
        if let Some((m, at)) = &grammar.error {
            self.errors.push((m.clone().into(), *at));
            return;
        }
        if grammar.name.as_deref() != Some("par") {
            self.errors
                .push((msg!("surface-grammar-not-par", name = name), span));
            return;
        }
        if name == "plaintext" || self.map.contains_key(name) {
            self.errors
                .push((msg!("surface-syntax-declared-twice", name = name), span));
            return;
        }
        let tables = match tables_or_why(&grammar_sha(&grammar.text)) {
            Ok(t) => t,
            Err(e) => {
                self.errors
                    .push((msg!("surface-syntax-error", name = name, error = e), span));
                return;
            }
        };
        out.extend(type_decls(name, &tables, span));
        out.extend(parse_fn(name, &tables, span));
        if inductive {
            if let Some(file) = self.file {
                self.pending_executable.extend(
                    tauto_surface::bindings::declared_names(&out[first..])
                        .into_iter()
                        .map(|name| (file, name.to_string())),
                );
            }
        }
        let mut unmade = false;
        if inductive {
            let at = INDUCTIVE_TEXT_BASE.saturating_add(self.inductive_text);
            match inductive_decls(name, &tables, Span::new(at, at)) {
                Ok((stmts, len)) => {
                    self.inductive_texts.push((at, len, span.start));
                    // A byte between two texts, so that no place ends where the next starts.
                    self.inductive_text = self.inductive_text.saturating_add(len).saturating_add(1);
                    if let Some(file) = self.file {
                        self.pending_executable.extend(stmts.iter().filter_map(
                            |stmt| match stmt {
                                Stmt::Fn(function) => Some((file, function.name.to_string())),
                                _ => None,
                            },
                        ));
                    }
                    out.extend(stmts);
                }
                Err(e) => {
                    self.errors
                        .push((msg!("surface-syntax-error", name = name, error = e), span));
                    unmade = true;
                }
            }
        }
        let made = listed_names(name, &out[first..]);
        let start = msg!("surface-syntax-generates-mismatch", name = name);
        // What was not made for an error said above is not said again as missing from the list.
        if let Some(why) =
            tauto_surface::generated::mismatch(start, &generates.items, &made).filter(|_| !unmade)
        {
            self.errors.push((why.into(), span));
            self.fixes
                .push((span, tauto_surface::generated::fix(generates, &made)));
        }
        let mut others = Vec::new();
        let sha = grammar_sha(&grammar.text);
        for symbol in tauto_syntax::start_symbols(&grammar.text)
            .into_iter()
            .skip(1)
        {
            match tables_or_why(&tauto_syntax::tables_key(&sha, Some(&symbol))) {
                Ok(t) if start_type_name(&t) == Some(symbol.as_str()) => others.push(OtherStart {
                    symbol,
                    tables: t,
                    reference: None,
                }),
                Ok(_) => self.errors.push((
                    msg!(
                        "surface-syntax-start-tables",
                        name = name,
                        start = symbol.as_str()
                    ),
                    span,
                )),
                Err(e) => self
                    .errors
                    .push((msg!("surface-syntax-error", name = name, error = e), span)),
            }
        }
        self.register(name, uses);
        self.map.insert(
            name.to_string(),
            Syntax {
                start_reference: None,
                tables,
                file: self.file,
                others,
            },
        );
    }

    fn register(&mut self, name: &str, uses: &[tauto_surface::surface::SyntaxUse]) {
        let mut seen = Vec::new();
        for u in uses {
            let role = match u.role.as_str() {
                "fmt" => Role::Fmt,
                "tokens" => Role::Tokens,
                other => {
                    self.errors.push((
                        msg!("surface-syntax-with-role", name = name, role = other),
                        u.span,
                    ));
                    continue;
                }
            };
            if seen.contains(&role) {
                self.errors.push((
                    msg!(
                        "surface-syntax-registered-twice",
                        name = name,
                        role = role.word()
                    ),
                    u.span,
                ));
                continue;
            }
            seen.push(role);
            self.registrations.push(Registration {
                syntax: name.to_string(),
                role,
                function: u.function.clone(),
                span: u.span,
            });
        }
    }

    fn term(&mut self, t: &mut SurfaceTerm) {
        let TermKind::SyntaxLit(lit) = &*t.kind else {
            return;
        };
        let lit = (**lit).clone();
        match self.literal(&lit, t.span) {
            Ok(new) => {
                t.kind = Arc::new(new);
                // The constructors of the syntax value retain their definition
                // references. Embedded source subtrees keep their own environment.
                let definition = lit
                    .name
                    .as_deref()
                    .and_then(|name| self.map.get(name))
                    .and_then(|syntax| syntax.file)
                    .and_then(|file| self.definitions.get(&file));
                if let Some(definition) = definition {
                    let mut definition = definition.clone();
                    let at = t.span;
                    tauto_surface::surface::walk::term(t, &mut |node| {
                        if node.span != at {
                            return;
                        }
                        match Arc::make_mut(&mut node.kind) {
                            TermKind::Var(name)
                            | TermKind::Record { name, .. }
                            | TermKind::Perform { effect: name, .. } => {
                                definition.source_name(name)
                            }
                            _ => {}
                        }
                    });
                }
            }
            // The literal stays, so the checkers go on without a second error.
            Err((message, at)) => self.errors.push((message.into(), at)),
        }
    }

    /// The typed tree of a literal's text in syntax `name`, as values: the
    /// scopes go on each token.
    /// `start` is a start symbol other than the first, whose tree the text is read as.
    pub fn read(
        &self,
        name: &str,
        start: Option<&str>,
        lit: &SyntaxLit,
        span: Span,
        scopes: &[u64],
    ) -> Result<Node, (Message, Span)> {
        if let Some(e) = &lit.error {
            return Err(e.clone());
        }
        let Some(syntax) = self.map.get(name) else {
            return Err((msg!("surface-not-a-syntax", name = name), span));
        };
        let tables = match start {
            None => &syntax.tables,
            Some(symbol) => match syntax.others.iter().find(|o| o.symbol == symbol) {
                Some(o) => &o.tables,
                None => return Err((msg!("surface-not-a-syntax", name = name), span)),
            },
        };
        self.uses.borrow_mut().push(LiteralUse {
            syntax: name.to_string(),
            tables: tables.clone(),
            lit: lit.clone(),
        });
        let events = parse(tables, &lit.text, 0, &Limits::default())
            .map_err(|e| describe(tables, name, lit, &e))?;
        let ast = build_ast(tables, &events).map_err(|e| {
            let m = msg!(tauto_syntax::SCHEMA, detail = e.0);
            (coded(m), span)
        })?;
        let builder = Builder {
            name,
            tables,
            lit,
            scopes,
        };
        let mut node = builder.node(&ast)?;
        if let Some(definition) = syntax.file.and_then(|file| self.definitions.get(&file)) {
            fn bind(node: &mut Node, definition: &mut tauto_surface::resolve::Resolver) {
                match node {
                    Node::Ctor(constructor, fields) => {
                        let schema = constructor.as_str().to_string();
                        let mut reference = constructor.reference().clone();
                        definition.source_name(&mut reference);
                        *constructor = tauto_surface::macros::node::ConstructorRef::resolved(
                            reference, schema,
                        );
                        for (_, field) in fields {
                            bind(field, definition);
                        }
                    }
                    Node::Pair(pair) => {
                        bind(&mut pair.0, definition);
                        bind(&mut pair.1, definition);
                    }
                    Node::List(items) => {
                        for item in items {
                            bind(item, definition);
                        }
                    }
                    Node::Option(Some(node)) => bind(node, definition),
                    _ => {}
                }
            }
            bind(&mut node, &mut definition.clone());
        }
        Ok(node)
    }

    fn literal(&self, lit: &SyntaxLit, span: Span) -> Result<TermKind, (Message, Span)> {
        if let Some(e) = &lit.error {
            return Err(e.clone());
        }
        let Some(name) = lit.name.as_deref() else {
            return Err((msg!("surface-literal-needs-name"), span));
        };
        if name == "plaintext" {
            return Ok(TermKind::Text(lit.text.clone()));
        }
        Ok((*self.read(name, None, lit, span, &[])?.to_term(span).kind).clone())
    }
}

/// `macro.syntax_error`, and where the text stopped making sense.
fn describe(tables: &Tables, syntax: &str, lit: &SyntaxLit, e: &ParseError) -> (Message, Span) {
    let span = |start: u32, end: u32| Span::new(lit.position(start), lit.position(end));
    let end = lit.text.len() as u32;
    let d = tauto_syntax::describe(syntax, tables, &lit.text, e);
    let at = match e {
        ParseError::Lex(l) => span(l.at, (l.at + 1).min(end)),
        ParseError::Syntax(s) => match s.at {
            Some(t) => span(t.start, t.end),
            None => span(end, end),
        },
        ParseError::Limit(_) => span(0, end),
    };
    (coded(syntax_message(&d.message, &d.args)), at)
}

/// `macro.syntax_error: ` and the message.
fn coded(m: Message) -> Message {
    msg!("macro-coded", code = "macro.syntax_error", message = m)
}

/// The message of a syntax error by its id and arguments (a `SynDiag` of
/// `macro.syntax_error`, or a [`tauto_syntax::Diagnostic`]), written in the
/// language of the tool: the `expected` arguments are the terminals one of
/// which would have been taken.
pub fn syntax_message(id: &str, args: &[(String, String)]) -> Message {
    let expected: Vec<&str> = args
        .iter()
        .filter(|(n, _)| n == "expected")
        .map(|(_, v)| v.as_str())
        .collect();
    let alternatives = match expected.split_last() {
        None => msg!("macro-syntax-something-else"),
        Some((last, rest)) => rest
            .iter()
            .rev()
            .fold(msg!("macro-syntax-terminal", name = *last), |or, first| {
                msg!("macro-syntax-or", first = *first, rest = or)
            }),
    };
    let mut m = Message::new(id.to_string()).arg("expected", alternatives);
    for (n, v) in args.iter().filter(|(n, _)| n != "expected") {
        m = m.arg(n.clone(), v.as_str());
    }
    m
}

pub enum SynOutcome {
    Parsed(std::sync::Arc<Tables>, Ast),
    Failed(tauto_syntax::Diagnostic),
}

pub fn parse_text(name: &str, sha: &str, text: &str) -> SynOutcome {
    let tables = match tables_of(sha) {
        Ok(t) => t,
        Err(m) => {
            return SynOutcome::Failed(tauto_syntax::Diagnostic {
                message: tauto_syntax::TABLES.into(),
                at: 0,
                expected: Vec::new(),
                args: vec![
                    ("syntax".into(), name.into()),
                    ("detail".into(), m.to_string()),
                ],
            });
        }
    };
    match tauto_syntax::parse_ast(name, &tables, text) {
        Ok(ast) => SynOutcome::Parsed(tables, ast),
        Err(d) => SynOutcome::Failed(d),
    }
}

/// Makes the typed tree of a text a [`Node`]: the values of the syntax's
/// types.
pub struct Builder<'a> {
    pub name: &'a str,
    pub tables: &'a Tables,
    pub lit: &'a SyntaxLit,
    /// The scopes every token carries (the expansion's, for a macro's input).
    pub scopes: &'a [u64],
}

impl Builder<'_> {
    fn type_name(&self, n: &str) -> String {
        tauto_syntax::type_name(&self.name, n)
    }

    fn syn_span(&self, start: u32) -> Node {
        // The id is the position as written; the table of origins replaces it.
        let at = self.lit.position(start);
        Node::Ctor(
            "SynSpan".into(),
            vec![(Some("id".into()), Node::Int(i64::from(at)))],
        )
    }

    fn token(&self, t: tauto_syntax::Token) -> Result<Node, (Message, Span)> {
        if Some(t.terminal) == self.tables.embed_terminal() {
            return self.embed(t);
        }
        let text = self
            .lit
            .text
            .get(t.start as usize..t.end as usize)
            .unwrap_or("");
        let scopes = self.scopes.iter().map(|s| Node::Int(*s as i64)).collect();
        Ok(Node::Ctor(
            "SynToken".into(),
            vec![
                (Some("text".into()), Node::text(text)),
                (Some("span".into()), self.syn_span(t.start)),
                (
                    Some("ctx".into()),
                    Node::Ctor(
                        "SynCtx".into(),
                        vec![(Some("scopes".into()), Node::List(scopes))],
                    ),
                ),
            ],
        ))
    }

    /// `${ e }`: the expression, as a `SynExpr` whose names carry the scopes.
    fn embed(&self, t: tauto_syntax::Token) -> Result<Node, (Message, Span)> {
        let whole = Span::new(self.lit.position(t.start), self.lit.position(t.end));
        let text = self
            .lit
            .text
            .get(t.start as usize..t.end as usize)
            .unwrap_or("");
        // `$n` is a name alone; `${ … }` is a block body: its `{ … }` reads
        // as the block it is, so one expression is that expression and
        // statements before it (`let`, …) scope over the rest.
        let inner = &text[1..];
        let term = crate::parse_expr_at(inner, self.lit.position(t.start + 1)).map_err(|e| {
            (
                coded(msg!("macro-syntax-embedded", detail = e.to_string())),
                whole,
            )
        })?;
        tauto_surface::macros::syn::Lift {
            scopes: self.scopes,
            quote: false,
            atoms: None,
            spans: None,
            reflip: None,
        }
        .expr(&term)
        .map_err(|e| {
            (
                coded(msg!("macro-syntax-embedded", detail = e.to_string())),
                whole,
            )
        })
    }

    pub fn node(&self, ast: &Ast) -> Result<Node, (Message, Span)> {
        Ok(match ast {
            Ast::Token(t) => self.token(*t)?,
            Ast::List(items) => Node::List(
                items
                    .iter()
                    .map(|i| self.node(i))
                    .collect::<Result<_, _>>()?,
            ),
            Ast::Opt(v) => Node::opt(match v {
                Some(v) => Some(self.node(v)?),
                None => None,
            }),
            Ast::Node {
                ty,
                ctor,
                span,
                fields,
            } => {
                let def = &self.tables.schema().types[*ty as usize];
                let span_value = self.syn_span(span.0);
                let named = |names: &[(String, FieldTy)]| -> Result<_, (Message, Span)> {
                    let mut out = vec![(Some("span".to_string()), span_value.clone())];
                    for ((n, _), v) in names.iter().zip(fields) {
                        out.push((Some(n.clone()), self.node(v)?));
                    }
                    Ok(out)
                };
                match def {
                    TypeDef::Struct {
                        name,
                        fields: names,
                        ..
                    } => {
                        let schema = self.type_name(name);
                        Node::Ctor(
                            tauto_surface::macros::node::ConstructorRef::resolved(
                                format!("{schema}::Mk").into(),
                                schema,
                            ),
                            named(names)?,
                        )
                    }
                    TypeDef::Enum { name, ctors } => {
                        let c = &ctors[*ctor as usize];
                        let qualified = format!("{}::{}", self.type_name(name), c.name);
                        match &c.payload {
                            Payload::Single(_) => Node::Ctor(
                                qualified.into(),
                                fields
                                    .iter()
                                    .map(|f| Ok((None, self.node(f)?)))
                                    .collect::<Result<_, (Message, Span)>>()?,
                            ),
                            Payload::Record(names) => Node::Ctor(qualified.into(), named(names)?),
                        }
                    }
                }
            }
        })
    }
}

/// `fn <syntax>_parse(t: Text): Result(<Start>, SynDiag)`, over `syn_parse`.
fn parse_fn(syntax: &str, tables: &Tables, span: Span) -> Option<Stmt> {
    let start = tables.schema().types.get(tables.start_type()? as usize)?;
    let ty_name = match start {
        TypeDef::Struct { name, .. } | TypeDef::Enum { name, .. } => {
            tauto_syntax::type_name(syntax, name)
        }
    };
    let var = |n: &str| SurfaceTerm::var(n, span);
    let text = |t: &str| SurfaceTerm::new(TermKind::Text(t.to_string()), span);
    let library = |name| SurfaceTerm::var(&tauto_surface::bindings::library_name(name), span);
    let app = |f: SurfaceTerm, arguments: Vec<SurfaceTerm>| {
        SurfaceTerm::new(
            TermKind::App {
                function: Box::new(f),
                arguments,
            },
            span,
        )
    };
    Some(Stmt::Fn(FnDecl {
        lends: None,
        budget: None,
        vis: tauto_surface::surface::Vis::Open,
        opaque: false,
        ghost: false,
        decreasing_by: None,
        generates: None,
        name: format!("{syntax}::parse").into(),
        unused: None,
        generic_types: Vec::new(),
        generics: Vec::new(),
        rows: Vec::new(),
        bounds: Vec::new(),
        bound_spans: Vec::new(),
        params: vec![tauto_surface::identity::Name::Spelled("t".to_string())],
        unused_generics: Vec::new(),
        unused_params: vec![None],
        borrows: vec![None],
        param_types: vec![Some(library("Text"))],
        result: Some(app(
            library("Result"),
            vec![var(&ty_name), library("SynDiag")],
        )),
        effects: None,
        written_effects: None,
        row_hole: None,
        where_: Vec::new(),
        span,
        body: app(
            library("Syn::parse"),
            vec![text(syntax), text(tables.grammar_sha256()), var("t")],
        ),
    }))
}

fn type_decls(syntax: &str, tables: &Tables, span: Span) -> Vec<Stmt> {
    let ty = |t: &FieldTy| field_ty(syntax, t, span);
    let span_field = (
        Some("span".to_string()),
        SurfaceTerm::var(&tauto_surface::bindings::library_name("SynSpan"), span),
    );
    let record = |fields: &[(String, FieldTy)]| {
        let mut out = vec![span_field.clone()];
        out.extend(fields.iter().map(|(n, t)| (Some(n.clone()), ty(t))));
        out
    };
    tables
        .schema()
        .types
        .iter()
        .map(|def| match def {
            TypeDef::Struct { name, fields, .. } => {
                let name = tauto_syntax::type_name(syntax, name);
                Stmt::Struct(DataDecl {
                    vis: tauto_surface::surface::Vis::Open,
                    kind: None,
                    name: tauto_surface::identity::Name::Spelled(name.clone()),
                    generics: Vec::new(),
                    unused_generics: Vec::new(),
                    unused_fields: Vec::new(),
                    rows: Vec::new(),
                    constructors: vec![DataConstructor {
                        name: tauto_surface::identity::Name::Spelled(name),
                        fields: record(fields),
                    }],
                    host: false,
                    borrowed: false,
                    coerce: None,
                    span,
                })
            }
            TypeDef::Enum { name, ctors } => Stmt::Enum(DataDecl {
                vis: tauto_surface::surface::Vis::Open,
                kind: None,
                name: tauto_surface::identity::Name::Spelled(tauto_syntax::type_name(syntax, name)),
                generics: Vec::new(),
                unused_generics: Vec::new(),
                unused_fields: Vec::new(),
                rows: Vec::new(),
                constructors: ctors
                    .iter()
                    .map(|c| DataConstructor {
                        name: tauto_surface::identity::Name::Spelled(c.name.clone()),
                        fields: match &c.payload {
                            Payload::Single(t) => vec![(None, ty(t))],
                            Payload::Record(fields) => record(fields),
                        },
                    })
                    .collect(),
                host: false,
                borrowed: false,
                coerce: None,
                span,
            }),
        })
        .collect()
}

/// The types of a syntax as Nib source, the way `tauto syntax show` prints them.
pub fn types_text(syntax: &str, tables: &Tables) -> String {
    fn ty(syntax: &str, t: &FieldTy) -> String {
        match t {
            FieldTy::Token => "SynToken".into(),
            FieldTy::Expr => "SynExpr".into(),
            FieldTy::Named(n) => format!("{syntax}::{n}"),
            FieldTy::List(i) => format!("List({})", ty(syntax, i)),
            FieldTy::Opt(i) => format!("Option({})", ty(syntax, i)),
        }
    }
    let record = |fields: &[(String, FieldTy)]| {
        let mut out = vec!["span: SynSpan".to_string()];
        out.extend(
            fields
                .iter()
                .map(|(n, t)| format!("{n}: {}", ty(syntax, t))),
        );
        out.join(", ")
    };
    let mut out = String::new();
    for def in &tables.schema().types {
        match def {
            TypeDef::Struct { name, fields, .. } => {
                out.push_str(&format!(
                    "struct {syntax}::{name} {{ {} }}\n",
                    record(fields)
                ));
            }
            TypeDef::Enum { name, ctors } => {
                out.push_str(&format!("enum {syntax}::{name} {{\n"));
                for c in ctors {
                    match &c.payload {
                        Payload::Single(t) => {
                            out.push_str(&format!("  {}({})\n", c.name, ty(syntax, t)))
                        }
                        Payload::Record(fields) => {
                            out.push_str(&format!("  {} {{ {} }}\n", c.name, record(fields)))
                        }
                    }
                }
                out.push_str("}\n");
            }
        }
    }
    out
}

fn field_ty(syntax: &str, t: &FieldTy, span: Span) -> SurfaceTerm {
    let app = |f: &str, inner: SurfaceTerm| {
        SurfaceTerm::new(
            TermKind::App {
                function: Box::new(SurfaceTerm::var(
                    &tauto_surface::bindings::library_name(f),
                    span,
                )),
                arguments: vec![inner],
            },
            span,
        )
    };
    match t {
        FieldTy::Token => {
            SurfaceTerm::var(&tauto_surface::bindings::library_name("SynToken"), span)
        }
        FieldTy::Expr => SurfaceTerm::var(&tauto_surface::bindings::library_name("SynExpr"), span),
        FieldTy::Named(n) => SurfaceTerm::var(&format!("{syntax}::{n}"), span),
        FieldTy::List(inner) => app("List", field_ty(syntax, inner, span)),
        FieldTy::Opt(inner) => app("Option", field_ty(syntax, inner, span)),
    }
}

fn inductive_name(syntax: &str, ty: &str) -> String {
    format!("{syntax}::{ty}__I")
}

/// The field type in the proof side's `inductive`: the text of a token, no span.
fn inductive_field_ty(syntax: &str, t: &FieldTy) -> String {
    match t {
        FieldTy::Token => "Text".into(),
        // A hole is not a field of the proof side's trees (`hole_places`).
        FieldTy::Expr => unreachable!("holes are checked to be whole alternatives"),
        FieldTy::Named(n) => inductive_name(syntax, n),
        FieldTy::List(i) => format!("List({})", inductive_field_ty(syntax, i)),
        FieldTy::Opt(i) => format!("Option({})", inductive_field_ty(syntax, i)),
    }
}

/// The conversion of `value` of type `t`: of type `Option(…)` when the grammar has holes.
fn inductive_convert(syntax: &str, t: &FieldTy, value: &str, holes: bool) -> String {
    match t {
        FieldTy::Token if holes => format!("Some({value}.text)"),
        FieldTy::Token => format!("{value}.text"),
        FieldTy::Expr => unreachable!("holes are checked to be whole alternatives"),
        FieldTy::Named(n) => format!("{syntax}::{n}__to_i({value})"),
        FieldTy::List(i) => format!("{}_list__to_i({value})", converter_stem(syntax, i)),
        FieldTy::Opt(i) => format!("{}_opt__to_i({value})", converter_stem(syntax, i)),
    }
}

/// `build` of the values of `parts`: with holes each part is an `Option`, and a `None` of any
/// part is the `None` of the whole.
fn bind_all(parts: &[String], build: impl FnOnce(&[String]) -> String, holes: bool) -> String {
    if !holes {
        return build(parts);
    }
    let names: Vec<String> = (0..parts.len()).map(|i| format!("y{i}")).collect();
    let mut out = format!("Some({})", build(&names));
    for (part, name) in parts.iter().zip(&names).rev() {
        out = format!("match {part} {{\n    None => None\n    Some({name}) => {out}\n  }}");
    }
    out
}

fn converter_stem(syntax: &str, t: &FieldTy) -> String {
    match t {
        FieldTy::Token => format!("{syntax}::token"),
        FieldTy::Expr => format!("{syntax}::expr"),
        FieldTy::Named(n) => format!("{syntax}::{n}"),
        FieldTy::List(i) => format!("{}_list", converter_stem(syntax, i)),
        FieldTy::Opt(i) => format!("{}_opt", converter_stem(syntax, i)),
    }
}

fn has_hole(t: &FieldTy) -> bool {
    match t {
        FieldTy::Expr => true,
        FieldTy::List(i) | FieldTy::Opt(i) => has_hole(i),
        FieldTy::Token | FieldTy::Named(_) => false,
    }
}

/// A hole (`TautoExpr`) of an inductive syntax stands for the non-terminal whose alternative
/// it is, so it is a whole alternative and nothing else: the first type where it is not.
fn misplaced_hole(tables: &Tables) -> Option<&str> {
    tables.schema().types.iter().find_map(|def| match def {
        TypeDef::Struct { name, fields, .. } => fields
            .iter()
            .any(|(_, t)| has_hole(t))
            .then_some(name.as_str()),
        TypeDef::Enum { name, ctors } => ctors
            .iter()
            .any(|c| match &c.payload {
                Payload::Single(FieldTy::Expr) => false,
                Payload::Single(t) => has_hole(t),
                Payload::Record(fs) => fs.iter().any(|(_, t)| has_hole(t)),
            })
            .then_some(name.as_str()),
    })
}

/// `inductive syntax`: the `inductive` types the proofs see (a token is its text),
/// in one `mutual` block, and `<syntax>.<Type>.to_i`, which turns the tree
/// `<syntax>.parse` reads into them.
///
/// A hole is a macro argument's alone: the proof side's types have no constructor for it, and
/// in a grammar with holes `to_i` is `None` on a tree that holds one.
///
/// The fields of the proof side's `inductive` types are the grammar's names behind `f_`: a name
/// like `plus` or `Star` is a global of `std/`, which a field must not shadow.
/// With the number of bytes of the text read, from `span.start` on.
fn inductive_decls(syntax: &str, tables: &Tables, span: Span) -> Result<(Vec<Stmt>, u32), Message> {
    if let Some(ty) = misplaced_hole(tables) {
        return Err(msg!("surface-inductive-syntax-hole-place", ty = ty));
    }
    let holes = tables.embed_terminal().is_some();
    let result = |ty: &str| {
        if holes {
            format!("Option({ty})")
        } else {
            ty.to_string()
        }
    };
    let mut types = String::new();
    let mut convert = String::new();
    let mut helpers: Vec<(String, FieldTy)> = Vec::new();
    let note = |t: &FieldTy, helpers: &mut Vec<(String, FieldTy)>| {
        let mut t = t;
        while let FieldTy::List(i) | FieldTy::Opt(i) = t {
            if !helpers.iter().any(|(_, h)| h == t) {
                helpers.push((converter_stem(syntax, t), (*t).clone()));
            }
            t = i;
        }
    };
    // The fields of a constructor in parentheses; none without fields.
    let fields = |fs: &[(String, FieldTy)]| -> String {
        let all: Vec<String> = fs
            .iter()
            .map(|(n, t)| format!("f_{n}: {}", inductive_field_ty(syntax, t)))
            .collect();
        if all.is_empty() {
            String::new()
        } else {
            format!("({})", all.join(", "))
        }
    };
    for def in &tables.schema().types {
        match def {
            TypeDef::Struct {
                name, fields: fs, ..
            } => {
                let ty = inductive_name(syntax, name);
                types.push_str(&format!(
                    "  pub(open) inductive {ty}: Type {{\n    Mk{}: {ty}\n  }}\n",
                    fields(fs)
                ));
                // One constructor with fields is a struct once extracted: the value is written as one.
                let parts: Vec<String> = fs
                    .iter()
                    .map(|(n, t)| {
                        note(t, &mut helpers);
                        inductive_convert(syntax, t, &format!("x.{n}"), holes)
                    })
                    .collect();
                let body = bind_all(
                    &parts,
                    |vs| {
                        let args: Vec<String> = fs
                            .iter()
                            .zip(vs)
                            .map(|((n, _), v)| format!("f_{n}: {v}"))
                            .collect();
                        format!("{ty} {{ {} }}", args.join(", "))
                    },
                    holes,
                );
                convert.push_str(&format!(
                    "pub(open) fn {syntax}::{name}__to_i(x: {syntax}::{name}): {} ! {{div}} {{\n  {body}\n}}\n",
                    result(&ty)
                ));
            }
            TypeDef::Enum { name, ctors } => {
                // `<Type>::I` and `<Type>::to_i` are made under the enum: a constructor of
                // that name would be a second meaning of the same name.
                if let Some(c) = ctors.iter().find(|c| c.name == "I" || c.name == "to_i") {
                    return Err(msg!(
                        "surface-inductive-syntax-ctor-taken",
                        ty = name.as_str(),
                        ctor = c.name.as_str()
                    ));
                }
                let ty = inductive_name(syntax, name);
                // The constructors are written with their type (`ir::Callee::I::Global_I`): another
                // enum of the grammar may have an alternative of the same name, and the value
                // made here is this type's.
                types.push_str(&format!("  pub(open) inductive {ty}: Type {{\n"));
                let mut arms = String::new();
                for c in ctors {
                    match &c.payload {
                        Payload::Single(FieldTy::Expr) => {
                            arms.push_str(&format!("    {}(v) => None\n", c.name));
                        }
                        Payload::Single(t) => {
                            note(t, &mut helpers);
                            types.push_str(&format!(
                                "    {}_I{}: {ty}\n",
                                c.name,
                                fields(&[("value".to_string(), t.clone())])
                            ));
                            let part = inductive_convert(syntax, t, "v", holes);
                            let body = bind_all(
                                &[part],
                                |vs| format!("{ty}::{}_I({})", c.name, vs[0]),
                                holes,
                            );
                            arms.push_str(&format!("    {}(v) => {body}\n", c.name));
                        }
                        Payload::Record(fs) => {
                            types.push_str(&format!("    {}_I{}: {ty}\n", c.name, fields(fs)));
                            let parts: Vec<String> = fs
                                .iter()
                                .map(|(n, t)| {
                                    note(t, &mut helpers);
                                    inductive_convert(syntax, t, &format!("r.{n}"), holes)
                                })
                                .collect();
                            let body = bind_all(
                                &parts,
                                |vs| {
                                    if vs.is_empty() {
                                        format!("{ty}::{}_I", c.name)
                                    } else {
                                        format!("{ty}::{}_I({})", c.name, vs.join(", "))
                                    }
                                },
                                holes,
                            );
                            arms.push_str(&format!("    {}(r) => {body}\n", c.name));
                        }
                    }
                }
                types.push_str("  }\n");
                convert.push_str(&format!(
                    "pub(open) fn {syntax}::{name}__to_i(x: {syntax}::{name}): {} ! {{div}} {{\n  match x {{\n{arms}  }}\n}}\n",
                    result(&ty)
                ));
            }
        }
    }
    let mut source = format!("mutual {{\n{types}}}\n{convert}");
    for (stem, t) in &helpers {
        let (kind, inner) = match t {
            FieldTy::List(i) => ("list", i),
            FieldTy::Opt(i) => ("opt", i),
            _ => continue,
        };
        let from = nib_field_ty(syntax, inner);
        let to = inductive_field_ty(syntax, inner);
        let item = inductive_convert(syntax, inner, "h", holes);
        if kind == "list" {
            let rest = format!("{stem}__to_i(rest)");
            let cons = bind_all(
                &[item, rest],
                |vs| format!("Cons({}, {})", vs[0], vs[1]),
                holes,
            );
            let nil = if holes { "Some(Nil)" } else { "Nil" };
            source.push_str(&format!(
                "pub(open) fn {stem}__to_i(xs: List({from})): {} ! {{div}} {{\n  match xs {{\n    Nil => {nil}\n    Cons(h, rest) => {cons}\n  }}\n}}\n",
                result(&format!("List({to})"))
            ));
        } else {
            let some = bind_all(&[item], |vs| format!("Some({})", vs[0]), holes);
            let none = if holes { "Some(None)" } else { "None" };
            source.push_str(&format!(
                "pub(open) fn {stem}__to_i(xs: Option({from})): {} ! {{div}} {{\n  match xs {{\n    None => {none}\n    Some(h) => {some}\n  }}\n}}\n",
                result(&format!("Option({to})"))
            ));
        }
    }
    // The text is read with `syntax__Name` for the `syntax.Name` it makes (and `syntax__Name__I`
    // for `syntax.Name.I`): a name under a module is
    // not written in a declaration.
    let source = underscore_module(&source, syntax);
    let program = crate::parse_program_unresolved_at(&source, span.start)
        .map_err(|e| format!("the inductive types: {e}"))?;
    let mut stmts = program.stmts;
    for s in &mut stmts {
        under_module(s, syntax);
    }
    Ok((stmts, u32::try_from(source.len()).unwrap_or(u32::MAX)))
}

fn underscore_module(source: &str, syntax: &str) -> String {
    let prefix = format!("{syntax}::");
    let mut out = String::new();
    let mut rest = source;
    while let Some(i) = rest.find(&prefix) {
        let before = rest[..i].chars().next_back();
        out.push_str(&rest[..i]);
        if before.is_some_and(|c| c.is_alphanumeric() || c == '_' || c == ':') {
            out.push_str(&prefix);
        } else {
            out.push_str(&format!("{syntax}__"));
        }
        rest = &rest[i + prefix.len()..];
    }
    out.push_str(rest);
    out
}

fn under_module(s: &mut Stmt, syntax: &str) {
    let flat = format!("{syntax}__");
    let rename = |n: &mut String| {
        if let Some(short) = n.strip_prefix(&flat) {
            *n = format!("{syntax}::{}", short.replace("__", "::"));
        }
    };
    match s {
        Stmt::Fn(f) => f.name.edit_spelling(rename),
        Stmt::Inductive(i) => i.name.edit_spelling(rename),
        Stmt::Mutual { items, .. } => {
            for i in items {
                under_module(i, syntax);
            }
        }
        _ => {}
    }
    tauto_surface::surface::walk::stmt(s, &mut |t| {
        if let TermKind::Var(n) = &*t.kind
            && let Some(short) = n.strip_prefix(&flat)
        {
            t.kind = Arc::new(TermKind::Var(
                format!("{syntax}::{}", short.replace("__", "::")).into(),
            ));
        }
        if let TermKind::Record { name, fields, base } = &*t.kind
            && let Some(short) = name.strip_prefix(&flat)
        {
            t.kind = Arc::new(TermKind::Record {
                name: format!("{syntax}::{}", short.replace("__", "::")).into(),
                fields: fields.clone(),
                base: base.clone(),
            });
        }
    });
}

fn nib_field_ty(syntax: &str, t: &FieldTy) -> String {
    match t {
        FieldTy::Token => "SynToken".into(),
        FieldTy::Expr => "SynExpr".into(),
        FieldTy::Named(n) => format!("{syntax}::{n}"),
        FieldTy::List(i) => format!("List({})", nib_field_ty(syntax, i)),
        FieldTy::Opt(i) => format!("Option({})", nib_field_ty(syntax, i)),
    }
}
