//! The table file `totes/llkgen` and `totes/lalrgen` write: one line per
//! section, the section's name first, numbers and names separated by single
//! spaces, a list as its length and then its elements.
//!
//! Derived from parol and scnr2 by Jörg Singer (MIT OR Apache-2.0); see NOTICE.

use std::fmt;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TableError(pub String);

impl fmt::Display for TableError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "bad syntax tables: {}", self.0)
    }
}

impl std::error::Error for TableError {}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum NtKind {
    Declared,
    Token,
    Rep,
    Opt,
    Group,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Sym {
    Nt(u32),
    Term(u32),
}

#[derive(Debug, Clone)]
pub struct Production {
    pub lhs: u32,
    /// 0 none, 1 collection start, 2 add to collection, 3 optional some, 4 optional none.
    pub attr: u8,
    pub rhs: Vec<Sym>,
    /// Parallel to `rhs`: the terminal is dropped from the tree (`^`).
    pub clipped: Vec<bool>,
}

#[derive(Debug, Clone)]
pub(crate) struct Lookahead {
    pub prod0: i64,
    pub k: usize,
    /// (from, terminal, to, production), sorted by (from, terminal).
    pub transitions: Vec<(u32, u32, u32, i64)>,
}

/// A state of an LALR(1) parse (`lr`).
#[derive(Debug, Clone)]
pub(crate) struct LrState {
    /// (terminal, kind, argument), sorted by terminal: kind 0 shifts to the state, 1 reduces by
    /// the production, 2 accepts by the production (one of the start symbol).
    pub actions: Vec<(u32, u8, u32)>,
    /// (non-terminal, state), sorted by non-terminal.
    pub gotos: Vec<(u32, u32)>,
}

#[derive(Debug, Clone)]
pub(crate) struct Accept {
    pub terminal: u32,
    pub priority: usize,
    /// 0 none, 1 positive, 2 negative.
    pub la_kind: u8,
    pub la_dfa: usize,
}

#[derive(Debug, Clone)]
pub(crate) struct State {
    pub accepts: Vec<Accept>,
    /// (class, target), sorted by class.
    pub transitions: Vec<(u32, u32)>,
}

/// A state of the scanner (`%state`): a count of a unit from `min` to `max`, or a text.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum DynState {
    Count { min: usize, max: usize },
    Str,
}

/// A side of the range of a `%validate`: `a`, `a + b` (op 1) or `a - b` (op 2), where each is a
/// number or, when its flag is set, the value the state holds.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) struct DynExpr {
    pub a_state: bool,
    pub a: usize,
    pub op: u8,
    pub b_state: bool,
    pub b: usize,
}

impl DynExpr {
    pub(crate) fn eval(&self, stored: usize) -> Option<usize> {
        let a = if self.a_state { stored } else { self.a };
        let b = if self.b_state { stored } else { self.b };
        match self.op {
            0 => Some(a),
            1 => a.checked_add(b),
            _ => a.checked_sub(b),
        }
    }
}

/// What a terminal written with `%capture` or `%validate` does with the scanner's state.
#[derive(Debug, Clone)]
pub(crate) struct Dynamic {
    /// 0 capture a count, 1 validate a count, 2 capture a text, 3 validate a text.
    pub op: u8,
    pub state: usize,
    pub unit: String,
    /// From, below: `None` when the count must equal the state's value.
    pub range: Option<(DynExpr, DynExpr)>,
    /// Indices into `dynamic_dfas`: the parts before and after the operator, and the captured text.
    pub prefix: usize,
    pub suffix: usize,
    pub capture: Option<usize>,
}

#[derive(Debug, Clone)]
pub(crate) struct Mode {
    pub name: String,
    /// (terminal, kind, target): kind 0 enter, 1 push, 2 pop.
    pub transitions: Vec<(u32, u8, u32)>,
    pub states: Vec<State>,
}

/// The type of a field of a generated struct or constructor.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum FieldTy {
    Token,
    /// A tauto expression written in the text (`TautoExpr`).
    Expr,
    Named(String),
    List(Box<FieldTy>),
    Opt(Box<FieldTy>),
}

#[derive(Debug, Clone)]
pub enum Payload {
    Record(Vec<(String, FieldTy)>),
    Single(FieldTy),
}

#[derive(Debug, Clone)]
pub struct Ctor {
    pub name: String,
    pub production: u32,
    pub payload: Payload,
}

#[derive(Debug, Clone)]
pub enum TypeDef {
    Struct {
        name: String,
        production: u32,
        fields: Vec<(String, FieldTy)>,
    },
    Enum {
        name: String,
        ctors: Vec<Ctor>,
    },
}

#[derive(Debug, Clone, Default)]
pub struct Schema {
    pub types: Vec<TypeDef>,
}

#[derive(Debug, Clone)]
pub struct Tables {
    source: String,
    pub(crate) sha256: String,
    pub(crate) generator: String,
    pub(crate) title: Option<String>,
    pub(crate) max_k: usize,
    pub(crate) terminals: Vec<String>,
    pub(crate) non_terminals: Vec<String>,
    pub(crate) nt_kinds: Vec<NtKind>,
    pub(crate) start: u32,
    pub(crate) productions: Vec<Production>,
    /// (type, constructor) per production; the type is -1 when the production builds none.
    pub(crate) prod_types: Vec<(i64, u32)>,
    /// Indexed by non-terminal.
    pub(crate) lookahead: Vec<Option<Lookahead>>,
    /// The states of an LALR(1) grammar's parse, in place of `lookahead`.
    pub(crate) lr: Option<Vec<LrState>>,
    /// Per mode.
    pub(crate) skip: Vec<Vec<u32>>,
    /// (first, last, class) over code points, sorted.
    pub(crate) classes: Vec<(u32, u32, u32)>,
    pub(crate) modes: Vec<Mode>,
    pub(crate) lookahead_dfas: Vec<Vec<State>>,
    /// The states of the scanner; empty when the grammar declares none.
    pub(crate) dyn_states: Vec<DynState>,
    /// Indexed by terminal.
    pub(crate) dynamic: Vec<Option<Dynamic>>,
    pub(crate) dynamic_dfas: Vec<Vec<State>>,
    pub(crate) schema: Schema,
}

struct Cursor<'a> {
    words: std::str::SplitWhitespace<'a>,
    section: &'a str,
}

impl<'a> Cursor<'a> {
    fn word(&mut self) -> Result<&'a str, TableError> {
        self.words
            .next()
            .ok_or_else(|| TableError(format!("section {} ends too early", self.section)))
    }

    fn num<T: std::str::FromStr>(&mut self) -> Result<T, TableError> {
        let w = self.word()?;
        w.parse()
            .map_err(|_| TableError(format!("section {}: {w:?} is not a number", self.section)))
    }

    fn end(&mut self) -> Result<(), TableError> {
        match self.words.next() {
            None => Ok(()),
            Some(w) => Err(TableError(format!(
                "section {} has extra {w:?}",
                self.section
            ))),
        }
    }
}

impl Tables {
    /// The validated serialized tables, for embedding in generated programs.
    pub fn source(&self) -> &str {
        &self.source
    }

    pub fn read(text: &str) -> Result<Tables, TableError> {
        let mut lines = text.lines();
        let magic = lines.next().unwrap_or("");
        if magic != "tauto-syntax-tables 1" {
            return Err(TableError(format!("unknown header {magic:?}")));
        }
        let mut sha256 = None;
        let mut generator = String::new();
        let mut title = None;
        let mut max_k = 0;
        let mut t = Tables {
            source: text.to_owned(),
            sha256: String::new(),
            generator: String::new(),
            title: None,
            max_k: 0,
            terminals: Vec::new(),
            non_terminals: Vec::new(),
            nt_kinds: Vec::new(),
            start: 0,
            productions: Vec::new(),
            prod_types: Vec::new(),
            lookahead: Vec::new(),
            lr: None,
            skip: Vec::new(),
            classes: Vec::new(),
            modes: Vec::new(),
            lookahead_dfas: Vec::new(),
            dyn_states: Vec::new(),
            dynamic: Vec::new(),
            dynamic_dfas: Vec::new(),
            schema: Schema::default(),
        };
        let mut dynamic: Vec<(u32, Dynamic)> = Vec::new();
        let mut clipped: Vec<(u32, u32)> = Vec::new();
        let mut seen = Vec::new();
        for line in lines {
            if line.trim().is_empty() {
                continue;
            }
            let (name, rest) = line.split_once(' ').unwrap_or((line, ""));
            seen.push(name);
            let mut c = Cursor {
                words: rest.split_whitespace(),
                section: name,
            };
            match name {
                "grammar_sha256" => sha256 = Some(rest.trim().to_string()),
                "generator" => generator = rest.trim().to_string(),
                "title" => title = (rest.trim() != "-").then(|| rest.trim().to_string()),
                "max_k" => max_k = c.num()?,
                "terminals" => t.terminals = names(&mut c)?,
                "non_terminals" => t.non_terminals = names(&mut c)?,
                "nt_kinds" => {
                    let n: usize = c.num()?;
                    for _ in 0..n {
                        t.nt_kinds.push(match c.num::<u8>()? {
                            0 => NtKind::Declared,
                            1 => NtKind::Token,
                            2 => NtKind::Rep,
                            3 => NtKind::Opt,
                            4 => NtKind::Group,
                            k => return Err(TableError(format!("unknown non-terminal kind {k}"))),
                        });
                    }
                }
                "start" => t.start = c.num()?,
                "productions" => {
                    let n: usize = c.num()?;
                    for _ in 0..n {
                        let lhs = c.num()?;
                        let attr = c.num()?;
                        let len: usize = c.num()?;
                        let mut rhs = Vec::with_capacity(len);
                        for _ in 0..len {
                            let s: i64 = c.num()?;
                            rhs.push(if s >= 0 {
                                Sym::Nt(s as u32)
                            } else {
                                Sym::Term((-s - 1) as u32)
                            });
                        }
                        t.productions.push(Production {
                            lhs,
                            attr,
                            clipped: vec![false; len],
                            rhs,
                        });
                    }
                }
                "symbol_attrs" => {
                    let n: usize = c.num()?;
                    for _ in 0..n {
                        let (p, pos, attr): (u32, u32, u32) = (c.num()?, c.num()?, c.num()?);
                        if attr == 1 {
                            clipped.push((p, pos));
                        }
                    }
                }
                "prod_types" => {
                    let n: usize = c.num()?;
                    for _ in 0..n {
                        t.prod_types.push((c.num()?, c.num()?));
                    }
                }
                "lookahead" => {
                    let n: usize = c.num()?;
                    t.lookahead = vec![None; t.non_terminals.len()];
                    for _ in 0..n {
                        let nt: usize = c.num()?;
                        let prod0 = c.num()?;
                        let k = c.num()?;
                        let m: usize = c.num()?;
                        let mut transitions = Vec::with_capacity(m);
                        for _ in 0..m {
                            transitions.push((c.num()?, c.num()?, c.num()?, c.num()?));
                        }
                        transitions.sort();
                        *t.lookahead.get_mut(nt).ok_or_else(|| {
                            TableError("lookahead for an unknown non-terminal".into())
                        })? = Some(Lookahead {
                            prod0,
                            k,
                            transitions,
                        });
                    }
                }
                "lr" => {
                    let n: usize = c.num()?;
                    let mut states = Vec::with_capacity(n);
                    for _ in 0..n {
                        let m: usize = c.num()?;
                        let mut actions = Vec::with_capacity(m);
                        for _ in 0..m {
                            actions.push((c.num()?, c.num()?, c.num()?));
                        }
                        actions.sort();
                        let m: usize = c.num()?;
                        let mut gotos = Vec::with_capacity(m);
                        for _ in 0..m {
                            gotos.push((c.num()?, c.num()?));
                        }
                        gotos.sort();
                        states.push(LrState { actions, gotos });
                    }
                    t.lr = Some(states);
                }
                "skip" => {
                    let n: usize = c.num()?;
                    for _ in 0..n {
                        let m: usize = c.num()?;
                        t.skip
                            .push((0..m).map(|_| c.num()).collect::<Result<_, _>>()?);
                    }
                }
                "classes" => {
                    let n: usize = c.num()?;
                    for _ in 0..n {
                        t.classes.push((c.num()?, c.num()?, c.num()?));
                    }
                    t.classes.sort();
                }
                "modes" => {
                    let n: usize = c.num()?;
                    for _ in 0..n {
                        let name = c.word()?.to_string();
                        let m: usize = c.num()?;
                        let mut transitions = Vec::with_capacity(m);
                        for _ in 0..m {
                            transitions.push((c.num()?, c.num()?, c.num()?));
                        }
                        let states = states(&mut c)?;
                        t.modes.push(Mode {
                            name,
                            transitions,
                            states,
                        });
                    }
                }
                "lookahead_dfas" => {
                    let n: usize = c.num()?;
                    for _ in 0..n {
                        t.lookahead_dfas.push(states(&mut c)?);
                    }
                }
                "dyn_states" => {
                    let n: usize = c.num()?;
                    for _ in 0..n {
                        let (kind, min, max): (u8, usize, usize) = (c.num()?, c.num()?, c.num()?);
                        t.dyn_states.push(match kind {
                            0 => DynState::Count { min, max },
                            1 => DynState::Str,
                            k => return Err(TableError(format!("unknown state kind {k}"))),
                        });
                    }
                }
                "dynamic" => {
                    let n: usize = c.num()?;
                    for _ in 0..n {
                        let terminal = c.num()?;
                        let op = c.num()?;
                        let state = c.num()?;
                        let len: usize = c.num()?;
                        let mut unit = String::new();
                        for _ in 0..len {
                            let cp: u32 = c.num()?;
                            unit.push(
                                char::from_u32(cp).ok_or_else(|| {
                                    TableError(format!("{cp} is not a character"))
                                })?,
                            );
                        }
                        let range = match c.num::<u8>()? {
                            0 => None,
                            _ => Some((dyn_expr(&mut c)?, dyn_expr(&mut c)?)),
                        };
                        let prefix = c.num()?;
                        let suffix = c.num()?;
                        let capture: i64 = c.num()?;
                        dynamic.push((
                            terminal,
                            Dynamic {
                                op,
                                state,
                                unit,
                                range,
                                prefix,
                                suffix,
                                capture: usize::try_from(capture).ok(),
                            },
                        ));
                    }
                }
                "dynamic_dfas" => {
                    let n: usize = c.num()?;
                    for _ in 0..n {
                        t.dynamic_dfas.push(states(&mut c)?);
                    }
                }
                "schema" => t.schema = schema(&mut c)?,
                _ => return Err(TableError(format!("unknown section {name:?}"))),
            }
            if !matches!(name, "grammar_sha256" | "generator" | "title") {
                c.end()?;
            }
        }
        for want in [
            "grammar_sha256",
            "terminals",
            "non_terminals",
            "nt_kinds",
            "start",
            "productions",
            "prod_types",
            "classes",
            "modes",
            "schema",
        ] {
            if !seen.contains(&want) {
                return Err(TableError(format!("section {want} is missing")));
            }
        }
        if !seen.contains(&"lookahead") && !seen.contains(&"lr") {
            return Err(TableError("section lookahead (or lr) is missing".into()));
        }
        t.dynamic = vec![None; t.terminals.len()];
        for (terminal, d) in dynamic {
            *t.dynamic
                .get_mut(terminal as usize)
                .ok_or_else(|| TableError("a dynamic entry names an unknown terminal".into()))? =
                Some(d);
        }
        t.sha256 = sha256.unwrap_or_default();
        t.generator = generator;
        t.title = title;
        t.max_k = max_k;
        for (p, pos) in clipped {
            let prod = t
                .productions
                .get_mut(p as usize)
                .ok_or_else(|| TableError("symbol_attrs names an unknown production".into()))?;
            *prod
                .clipped
                .get_mut(pos as usize)
                .ok_or_else(|| TableError("symbol_attrs names an unknown symbol".into()))? = true;
        }
        t.check()?;
        Ok(t)
    }

    /// The indices every later step trusts.
    fn check(&self) -> Result<(), TableError> {
        let bad = |what: &str| Err(TableError(format!("{what} is out of range")));
        if self.nt_kinds.len() != self.non_terminals.len() {
            return bad("nt_kinds");
        }
        if self.start as usize >= self.non_terminals.len() {
            return bad("start");
        }
        if self.prod_types.len() != self.productions.len() {
            return bad("prod_types");
        }
        for p in &self.productions {
            if p.lhs as usize >= self.non_terminals.len() {
                return bad("a production's left side");
            }
            for s in &p.rhs {
                match *s {
                    Sym::Nt(n) if n as usize >= self.non_terminals.len() => {
                        return bad("a production's symbol");
                    }
                    Sym::Term(n) if n as usize >= self.terminals.len() => {
                        return bad("a production's terminal");
                    }
                    _ => {}
                }
            }
        }
        for (ty, ctor) in &self.prod_types {
            let ok = match self.schema.types.get(*ty as usize) {
                _ if *ty < 0 => true,
                Some(TypeDef::Struct { .. }) => *ctor == 0,
                Some(TypeDef::Enum { ctors, .. }) => (*ctor as usize) < ctors.len(),
                None => false,
            };
            if !ok {
                return bad("prod_types");
            }
        }
        for la in self.lookahead.iter().flatten() {
            if la.prod0 >= self.productions.len() as i64 {
                return bad("a lookahead's production");
            }
            for &(_, _, _, p) in &la.transitions {
                if p >= self.productions.len() as i64 {
                    return bad("a lookahead's production");
                }
            }
        }
        if let Some(states) = &self.lr {
            if states.is_empty() {
                return bad("the lr states");
            }
            for st in states {
                for &(term, kind, arg) in &st.actions {
                    let ok = (term as usize) < self.terminals.len()
                        && match kind {
                            0 => (arg as usize) < states.len(),
                            1 => (arg as usize) < self.productions.len(),
                            2 => self
                                .productions
                                .get(arg as usize)
                                .is_some_and(|p| p.lhs == self.start),
                            _ => false,
                        };
                    if !ok {
                        return bad("an lr action");
                    }
                }
                for &(nt, to) in &st.gotos {
                    if nt as usize >= self.non_terminals.len() || to as usize >= states.len() {
                        return bad("an lr goto");
                    }
                }
            }
        }
        let n_classes = self
            .classes
            .iter()
            .map(|c| c.2 as usize + 1)
            .max()
            .unwrap_or(0);
        // The accepts of a lookahead DFA carry no terminal (scnr2 numbers them u32::MAX).
        let check_states =
            |states: &[State], dfas: usize, terminals: bool| -> Result<(), TableError> {
                for s in states {
                    for &(class, target) in &s.transitions {
                        if class as usize >= n_classes || target as usize >= states.len() {
                            return bad("a scanner transition");
                        }
                    }
                    for a in &s.accepts {
                        if (terminals && a.terminal as usize >= self.terminals.len())
                            || (a.la_kind != 0 && a.la_dfa >= dfas)
                        {
                            return bad("a scanner accept");
                        }
                    }
                }
                Ok(())
            };
        for m in &self.modes {
            check_states(&m.states, self.lookahead_dfas.len(), true)?;
            for &(term, kind, target) in &m.transitions {
                if term as usize >= self.terminals.len()
                    || (kind != 2 && target as usize >= self.modes.len())
                {
                    return bad("a mode transition");
                }
            }
        }
        for d in &self.lookahead_dfas {
            check_states(d, self.lookahead_dfas.len(), false)?;
        }
        if self.modes.is_empty() {
            return bad("the mode list");
        }
        for d in &self.dynamic_dfas {
            check_states(d, self.lookahead_dfas.len(), false)?;
        }
        for d in self.dynamic.iter().flatten() {
            let n = self.dynamic_dfas.len();
            let kind_ok = match (self.dyn_states.get(d.state), d.op) {
                (Some(DynState::Count { .. }), 0 | 1) => !d.unit.is_empty(),
                (Some(DynState::Str), 2) => d.capture.is_some(),
                (Some(DynState::Str), 3) => true,
                _ => false,
            };
            if !kind_ok || d.prefix >= n || d.suffix >= n || d.capture.is_some_and(|c| c >= n) {
                return bad("a dynamic entry");
            }
        }
        Ok(())
    }

    pub fn grammar_sha256(&self) -> &str {
        &self.sha256
    }

    pub fn generator(&self) -> &str {
        &self.generator
    }

    pub fn title(&self) -> Option<&str> {
        self.title.as_deref()
    }

    pub fn max_k(&self) -> usize {
        self.max_k
    }

    pub fn schema(&self) -> &Schema {
        &self.schema
    }

    pub fn terminals(&self) -> &[String] {
        &self.terminals
    }

    pub fn non_terminals(&self) -> &[String] {
        &self.non_terminals
    }

    pub fn start(&self) -> u32 {
        self.start
    }

    pub fn productions(&self) -> &[Production] {
        &self.productions
    }

    /// The terminal for a tauto expression in the text (`TautoExpr`), when the
    /// grammar has one.
    pub fn embed_terminal(&self) -> Option<u32> {
        self.terminals
            .iter()
            .position(|t| t == "TautoExpr")
            .map(|i| i as u32)
    }

    /// The type of the start symbol: an index into the schema's types.
    pub fn start_type(&self) -> Option<u32> {
        let p = self.productions.iter().position(|p| p.lhs == self.start)?;
        u32::try_from(self.prod_types[p].0).ok()
    }

    pub fn mode_names(&self) -> impl Iterator<Item = &str> {
        self.modes.iter().map(|m| m.name.as_str())
    }

    /// The scanner as the texts `totes/scan` reads (`scan_tables_read_dynamic`):
    /// `meta`, `classes`, `states`, `rows` and `dynamic`, numbers separated by single spaces.
    /// The automata are numbered together: the modes', the lookaheads', then those of the
    /// terminals written with `%capture` or `%validate`.
    pub fn scan_texts(&self) -> [String; 5] {
        let n_classes = self.classes.iter().map(|c| c.2 + 1).max().unwrap_or(0) as usize;
        let n_modes = self.modes.len();
        let first_dynamic = n_modes + self.lookahead_dfas.len();
        let automata: Vec<&[State]> = self
            .modes
            .iter()
            .map(|m| m.states.as_slice())
            .chain(self.lookahead_dfas.iter().map(Vec::as_slice))
            .chain(self.dynamic_dfas.iter().map(Vec::as_slice))
            .collect();
        let mut meta = vec![n_classes, n_modes, automata.len()];
        for m in &self.modes {
            meta.push(m.transitions.len());
            for &(token, kind, to) in &m.transitions {
                let to = if kind == 2 { 0 } else { to as usize };
                meta.extend([kind as usize, token as usize, to]);
            }
        }
        let mut classes = vec![self.classes.len()];
        for &(first, last, class) in &self.classes {
            classes.extend([first as usize, last as usize, class as usize]);
        }
        let mut states = Vec::new();
        let mut rows = Vec::new();
        for dfa in &automata {
            states.push(dfa.len());
            for s in *dfa {
                states.push(s.accepts.len());
                for a in &s.accepts {
                    let nested = if a.la_kind == 0 {
                        0
                    } else {
                        n_modes + a.la_dfa
                    };
                    states.extend([a.terminal as usize, a.la_kind as usize, nested]);
                }
                let mut row = vec![0usize; n_classes];
                for &(class, to) in &s.transitions {
                    row[class as usize] = to as usize + 1;
                }
                let mut i = 0;
                while i < row.len() {
                    let j = (i..row.len())
                        .find(|&j| row[j] != row[i])
                        .unwrap_or(row.len());
                    rows.extend([j - i, row[i]]);
                    i = j;
                }
            }
        }
        let mut dynamic = Vec::new();
        if !self.dyn_states.is_empty() {
            dynamic.push(self.dyn_states.len());
            for s in &self.dyn_states {
                match *s {
                    DynState::Count { min, max } => dynamic.extend([0, min, max]),
                    DynState::Str => dynamic.extend([1, 0, 0]),
                }
            }
            let entries: Vec<(usize, &Dynamic)> = self
                .dynamic
                .iter()
                .enumerate()
                .filter_map(|(i, d)| Some((i, d.as_ref()?)))
                .collect();
            dynamic.push(entries.len());
            for (token, d) in entries {
                dynamic.extend([token, d.op as usize, d.state, d.unit.chars().count()]);
                dynamic.extend(d.unit.chars().map(|c| c as usize));
                match d.range {
                    None => dynamic.push(0),
                    Some((from, below)) => {
                        dynamic.push(1);
                        for e in [from, below] {
                            dynamic.extend([e.a_state as usize, e.a, e.op as usize]);
                            dynamic.extend([e.b_state as usize, e.b]);
                        }
                    }
                }
                dynamic.extend([first_dynamic + d.prefix, first_dynamic + d.suffix]);
                dynamic.push(d.capture.map_or(0, |c| first_dynamic + c + 1));
            }
        }
        let text = |v: Vec<usize>| v.iter().map(usize::to_string).collect::<Vec<_>>().join(" ");
        [
            text(meta),
            text(classes),
            text(states),
            text(rows),
            text(dynamic),
        ]
    }

    /// An LALR(1) parser as the texts `totes/lr` reads (`lr_tables_read`): `meta`, `skip`,
    /// `actions`, `gotos` and `productions`, numbers separated by single spaces; `None` for
    /// LL(k) tables.
    ///
    /// - `meta`: the start symbol and the numbers of terminals, non-terminals and states.
    /// - `skip`: the number of modes, then for each the number of terminals it skips and those.
    /// - `actions`: a cell per state and terminal, run-length encoded (how many, then which):
    ///   0 none, `s * 4 + 1` shift to `s`, `p * 4 + 2` reduce by `p`, `p * 4 + 3` accept by `p`.
    /// - `gotos`: a cell per state and non-terminal, run-length encoded: 0 none, `s + 1` the state.
    /// - `productions`: their number, then for each the left side, the length of the right side
    ///   and its symbols last first, each 0 and a non-terminal or 1 and a terminal.
    pub fn lr_texts(&self) -> Option<[String; 5]> {
        let states = self.lr.as_ref()?;
        let (nt, nn) = (self.terminals.len(), self.non_terminals.len());
        let mut actions = vec![0usize; states.len() * nt];
        let mut gotos = vec![0usize; states.len() * nn];
        for (i, st) in states.iter().enumerate() {
            for &(term, kind, arg) in &st.actions {
                actions[i * nt + term as usize] = arg as usize * 4 + kind as usize + 1;
            }
            for &(n, to) in &st.gotos {
                gotos[i * nn + n as usize] = to as usize + 1;
            }
        }
        let runs = |values: Vec<usize>| {
            let mut out = Vec::new();
            let mut i = 0;
            while i < values.len() {
                let j = (i..values.len())
                    .find(|&j| values[j] != values[i])
                    .unwrap_or(values.len());
                out.extend([j - i, values[i]]);
                i = j;
            }
            out
        };
        let mut skip = vec![self.skip.len()];
        for s in &self.skip {
            skip.push(s.len());
            skip.extend(s.iter().map(|&t| t as usize));
        }
        let mut productions = vec![self.productions.len()];
        for p in &self.productions {
            productions.extend([p.lhs as usize, p.rhs.len()]);
            for s in p.rhs.iter().rev() {
                productions.extend(match *s {
                    Sym::Nt(n) => [0, n as usize],
                    Sym::Term(t) => [1, t as usize],
                });
            }
        }
        let text = |v: Vec<usize>| v.iter().map(usize::to_string).collect::<Vec<_>>().join(" ");
        Some([
            text(vec![self.start as usize, nt, nn, states.len()]),
            text(skip),
            text(runs(actions)),
            text(runs(gotos)),
            text(productions),
        ])
    }

    pub fn kind(&self, non_terminal: u32) -> NtKind {
        self.nt_kinds[non_terminal as usize]
    }

    /// The scanner drops these terminals from the parse: newlines, white space and comments,
    /// and whatever a mode lists to skip.
    pub fn is_skipped(&self, terminal: u32) -> bool {
        (1..=4).contains(&terminal) || self.skip.iter().any(|s| s.contains(&terminal))
    }
}

fn names(c: &mut Cursor) -> Result<Vec<String>, TableError> {
    let n: usize = c.num()?;
    (0..n).map(|_| c.word().map(str::to_string)).collect()
}

fn states(c: &mut Cursor) -> Result<Vec<State>, TableError> {
    let n: usize = c.num()?;
    let mut out = Vec::with_capacity(n);
    for _ in 0..n {
        let na: usize = c.num()?;
        let mut accepts = Vec::with_capacity(na);
        for _ in 0..na {
            accepts.push(Accept {
                terminal: c.num()?,
                priority: c.num()?,
                la_kind: c.num()?,
                la_dfa: c.num()?,
            });
        }
        let nt: usize = c.num()?;
        let mut transitions = Vec::with_capacity(nt);
        for _ in 0..nt {
            transitions.push((c.num()?, c.num()?));
        }
        transitions.sort();
        out.push(State {
            accepts,
            transitions,
        });
    }
    Ok(out)
}

fn dyn_expr(c: &mut Cursor) -> Result<DynExpr, TableError> {
    Ok(DynExpr {
        a_state: c.num::<u8>()? != 0,
        a: c.num()?,
        op: c.num()?,
        b_state: c.num::<u8>()? != 0,
        b: c.num()?,
    })
}

fn field_ty(c: &mut Cursor) -> Result<FieldTy, TableError> {
    Ok(match c.word()? {
        "K" => FieldTy::Token,
        "E" => FieldTy::Expr,
        "N" => FieldTy::Named(c.word()?.to_string()),
        "L" => FieldTy::List(Box::new(field_ty(c)?)),
        "O" => FieldTy::Opt(Box::new(field_ty(c)?)),
        w => return Err(TableError(format!("unknown field type {w:?}"))),
    })
}

fn record(c: &mut Cursor) -> Result<Vec<(String, FieldTy)>, TableError> {
    let n: usize = c.num()?;
    (0..n)
        .map(|_| Ok((c.word()?.to_string(), field_ty(c)?)))
        .collect()
}

fn schema(c: &mut Cursor) -> Result<Schema, TableError> {
    let n: usize = c.num()?;
    let mut types = Vec::with_capacity(n);
    for _ in 0..n {
        match c.word()? {
            "S" => {
                let name = c.word()?.to_string();
                let production = c.num()?;
                types.push(TypeDef::Struct {
                    name,
                    production,
                    fields: record(c)?,
                });
            }
            "E" => {
                let name = c.word()?.to_string();
                let m: usize = c.num()?;
                let mut ctors = Vec::with_capacity(m);
                for _ in 0..m {
                    let cname = c.word()?.to_string();
                    let production = c.num()?;
                    let payload = match c.word()? {
                        "R" => Payload::Record(record(c)?),
                        "P" => Payload::Single(field_ty(c)?),
                        w => return Err(TableError(format!("unknown payload {w:?}"))),
                    };
                    ctors.push(Ctor {
                        name: cname,
                        production,
                        payload,
                    });
                }
                types.push(TypeDef::Enum { name, ctors });
            }
            w => return Err(TableError(format!("unknown type kind {w:?}"))),
        }
    }
    Ok(Schema { types })
}
