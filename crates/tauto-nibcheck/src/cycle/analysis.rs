//! Which mutable storages may hold which others: the graph the level order
//! must be a topological order of.
//!
//! `docs/design/shared-levels.md`. Every syntactic place that makes a mutable
//! storage (a `var`, `ref_new`, `vec_new`, …) is one *site*; a site stands for
//! all the storages made there at run time. The analysis computes, for every
//! site, the set of sites its content may reach through immutable values and
//! closures, stopping at the first storage (its *frontier*). The program is
//! accepted when that graph on sites has no cycle: a topological order of it
//! is the level assignment, and a run-time strong-reference path between two
//! storages is an edge between their sites, so a run-time cycle would be a
//! cycle here (`lean/Proto/Cycle.lean` for the graph argument).
//!
//! The values are flattened: a record, a list or a closure's environment is
//! the set of atoms it may hold, with no field or position. That loses
//! precision and never soundness. Anything the analysis does not model is an
//! `Unknown` atom, and an `Unknown` in a frontier is an error, so it is never
//! read as the empty set.

use std::collections::{BTreeSet, HashMap, HashSet};
use std::rc::Rc;

use tauto_parol::Span;

use crate::lin::pattern_names;
use crate::surface::{FnDecl, Handler, Pattern, Program, Stmt, SurfaceTerm, TermKind};
use crate::types::{Datas, ParamId, Ty, TypeReport, prelude, site};

/// A reason the program may have a strong reference cycle.
#[derive(Debug, Clone, PartialEq)]
pub struct CycleDiag {
    pub message: String,
    pub span: Span,
}

type Node = usize;

/// What a value may be, ignoring where it sits in a data structure.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
enum Atom {
    /// A strong reference to a mutable storage.
    Cell(usize),
    /// A borrowed `var` (or container) place: never stored, read through.
    Place(usize),
    /// A function or closure.
    Lam(usize),
    /// A value nothing is known about.
    Unknown(usize),
    /// A `Weak` on the storage of a site: no edge, a `Cell` again through
    /// `weak_get`.
    Weak(usize),
}

#[derive(Debug, Clone)]
struct CellInfo {
    contents: Node,
    span: Span,
    what: String,
}

#[derive(Debug, Clone)]
struct LamInfo {
    params: Vec<Node>,
    ret: Node,
    /// What the closure holds: its captured values and storages.
    env: Node,
    /// What a frame of it holds while it runs: its parameters, locals and
    /// the values it is in the middle of, and the frames of what it calls.
    /// A continuation captured below it holds all of that.
    frame: Node,
}

struct Call {
    callee: Node,
    args: Vec<Node>,
    res: Node,
    /// The frame the call is made from: it holds the callee's frame.
    frame: Node,
}

/// How a name is bound.
#[derive(Clone, Copy, Debug)]
enum Bound {
    /// A value.
    Val(Node),
    /// A borrowed parameter or view: the place it stands for is read through.
    Place(Node),
    /// A `var` of this site.
    Var(usize),
}

struct Binding {
    name: String,
    bound: Bound,
    frame: usize,
}

struct Frame {
    lam: Option<usize>,
    ret: Node,
    /// The function returns a borrow, so its result is not read through.
    raw: bool,
}

/// What a prelude `extern` does with the storages it is given.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Extern {
    /// The result holds what the arguments held: an immutable value built
    /// from them, or nothing at all when its type holds no storage.
    Flatten,
    /// A function the host provides: it keeps what it is given in a state of
    /// its own, which it may give back, and its handles are that state.
    Host,
    /// Makes a storage holding the value arguments.
    Alloc,
    /// Puts the value arguments into the storage of the first.
    Store,
    /// Takes a value out of the storage of the first.
    Load,
    /// `Store`, and the old content comes back.
    Swap,
    /// `weak_of`: a `Weak` on each storage of the first.
    Downgrade,
    /// `weak_get`: the storage of each `Weak` of the first.
    Upgrade,
    /// `replace(&mut x, v)`: the place itself is written, not what it holds.
    Replace,
    /// A `&mut` into the storage of the first: writing through it writes
    /// that storage.
    LoadMut,
    /// Consumes the storage of the first: the result is an immutable value
    /// of its content.
    Convert,
}

fn extern_model(name: &str) -> Option<Extern> {
    use Extern::*;
    Some(match name {
        "Ref::new" | "Mutex::new" | "Vec::new" | "HashMap::new" => Alloc,
        "Ref::set" | "Mutex::put" | "Vec::push" => Store,
        "HashMap::insert" => Swap,
        "replace" => Replace,
        "Weak::of" => Downgrade,
        "Weak::get" => Upgrade,
        "Vec::get_mut" | "Vec::last_mut" | "Vec::as_mut_slice" | "HashMap::get_mut" => LoadMut,
        "Ref::get" | "Mutex::take_claimed" | "Vec::pop" | "Vec::index" | "Vec::get" | "Vec::as_slice"
        | "Slice::get" | "HashMap::get" | "HashMap::index" => Load,
        "Vec::into_list" | "Vec::into_array" | "HashMap::into_vec" => Convert,
        "Vec::len" | "Vec::clear" | "Vec::truncate" | "Vec::swap" | "Slice::len" | "Text::of"
        | "Buf::of" | "Buf::clone" | "Buf::new" | "Buf::push" | "Syn::parse" | "Syn::expr_of"
        | "Syn::expand" | "Syn::open" | "Judgement::mentions" | "Judgement::same_atom" | "Elab::whnf"
        | "Elab::defeq" | "Elab::check" | "Elab::global" | "Elab::resolve" | "I64::of_i32"
        | "I32::of_i64" | "I64::of_u64" | "U64::of_i64" | "U64::of_u32" | "U32::of_u64"
        | "U64::of_u8" | "U8::of_u64" | "Os::args" | "Os::read_file" | "Os::write_file"
        | "Os::read_bytes" | "Os::write_bytes" | "Os::secure_random" | "Os::create_dir"
        | "Os::list_dir" | "Os::remove" | "Os::temp_dir" | "Os::run" | "Os::print" | "Os::eprint"
        | "Os::tcp_listen" | "Os::tcp_accept" | "Os::tcp_connect" | "Os::tcp_read" | "Os::tcp_write"
        | "Os::tcp_shutdown" | "Os::tcp_close" | "Os::tcp_unlisten" | "Os::tls_accept"
        | "Os::tls_connect" | "Os::tls_read" | "Os::tls_write" | "Os::tls_shutdown"
        | "Os::tls_close" | "Os::exit" | "Os::stop" | "Os::sleep_pending" | "Os::offload"
        | "Pending::ready" | "Pending::take" | "Pending::is_ready" | "Pending::signal"
        | "Mutex::claim" | "Atomic::new" | "Atomic::load" | "Atomic::store" | "Atomic::fetch_add"
        | "words" | "concat" | "Array::of_list" | "Array::get" | "Array::len" | "Array::to_list"
        | "Bytes::of_list" | "Bytes::to_list" | "Bytes::len" | "Bytes::get" | "Bytes::slice"
        | "Bytes::concat" | "Bytes::eq" | "Bytes::of_text" | "Text::of_bytes" | "Text::len"
        | "Text::byte" | "Text::slice" | "Text::compare" | "Text::of_code_point" | "Text::of_utf8"
        | "Text::of_i64" | "Text::of_u64" | "U32::and" | "U32::or" | "U32::xor" | "U32::shl"
        | "U32::shr" | "U32::rotl" | "U32::rotr" | "U64::and" | "U64::or" | "U64::xor" | "U64::shl"
        | "U64::shr" | "U64::rotl" | "U64::rotr" | "Text::of_nat" | "Nat::of_u64" | "U64::of_nat"
        | "Float::of_i64" | "I64::of_float" | "Float::of_text" | "Text::of_float" | "Float::bits"
        | "Float::of_bits" | "Float::is_nan" | "Float::abs" | "Float::floor" | "Float::ceil"
        | "Float::trunc" | "Float::round" | "Float::sqrt" | "Float::cbrt" | "Float::exp"
        | "Float::ln" | "Float::log2" | "Float::log10" | "Float::pow" | "Float::sin" | "Float::cos"
        | "Float::tan" | "Float::asin" | "Float::acos" | "Float::atan" | "Float::atan2"
        | "Float::sinh" | "Float::cosh" | "Float::tanh" | "secret" | "expose" => Flatten,
        // `Float32`'s functions (`std/prelude/Num.taut`).
        n if n.starts_with("Float32::") || n == "Float::of_float32" => Flatten,
        // The secret words (`std/prelude/Secret.taut`).
        n if n.starts_with("Ct::") => Flatten,
        _ => return None,
    })
}

pub struct Analysis<'a> {
    types: &'a TypeReport,
    pts: Vec<BTreeSet<Atom>>,
    succ: Vec<Vec<Node>>,
    /// `dst ⊇ contents(c)` for each storage `c` in `src`.
    loads: Vec<(Node, Node)>,
    /// `dst ⊇ src` without its places, and the content of each place.
    reads: Vec<(Node, Node)>,
    /// `contents(c) ⊇ src` for each storage or place `c` in `dst`.
    stores: Vec<(Node, Node)>,
    calls: Vec<Call>,
    /// `dst ∋ Place(c)` for each storage `c` in `src`.
    places: Vec<(Node, Node)>,
    /// `dst ∋ Weak(c)` for each storage `c` in `src`.
    weakens: Vec<(Node, Node)>,
    /// `dst ∋ Cell(c)` for each `Weak(c)` in `src`.
    upgrades: Vec<(Node, Node)>,
    /// `dst ⊇ src` without the storages its type rules out: a storage made
    /// by an allocation whose kind is not in the set.
    filters: Vec<(Node, Node, BTreeSet<&'static str>)>,
    cells: Vec<CellInfo>,
    lams: Vec<LamInfo>,
    unknowns: Vec<(String, Span)>,
    /// The values performed at each effect's operation, and what resumes it.
    effect_args: HashMap<String, Vec<Node>>,
    effect_resume: HashMap<String, Node>,
    globals: HashMap<String, usize>,
    methods: HashMap<String, Vec<usize>>,
    bindings: Vec<Binding>,
    frames: Vec<Frame>,
    /// The frames being built, innermost last: every value made and every
    /// name bound flows into the last.
    scopes: Vec<Node>,
    /// Nodes of the global function declarations by name.
    lam_names: Vec<String>,
    hosts: HashMap<String, usize>,
    /// Functions an `extern` block declares that the checker does not know.
    host_fns: HashSet<String>,
    /// The generic global functions, analysed afresh at each direct call.
    generic_fns: HashMap<String, Rc<FnDecl>>,
    /// The generic functions being analysed afresh now, innermost last.
    cloning: Vec<String>,
    /// How many fresh copies have been made: past `MAX_CLONES` a call
    /// shares the one copy every other use reads.
    clones: usize,
}

const EMPTY: Node = 0;

/// The most fresh copies of generic functions one program makes.
const MAX_CLONES: usize = 4096;

impl<'a> Analysis<'a> {
    fn new(types: &'a TypeReport) -> Self {
        let mut a = Analysis {
            types,
            pts: Vec::new(),
            succ: Vec::new(),
            loads: Vec::new(),
            reads: Vec::new(),
            stores: Vec::new(),
            calls: Vec::new(),
            places: Vec::new(),
            weakens: Vec::new(),
            upgrades: Vec::new(),
            filters: Vec::new(),
            cells: Vec::new(),
            lams: Vec::new(),
            unknowns: Vec::new(),
            effect_args: HashMap::new(),
            effect_resume: HashMap::new(),
            globals: HashMap::new(),
            methods: HashMap::new(),
            bindings: Vec::new(),
            frames: Vec::new(),
            scopes: Vec::new(),
            lam_names: Vec::new(),
            hosts: HashMap::new(),
            host_fns: HashSet::new(),
            generic_fns: HashMap::new(),
            cloning: Vec::new(),
            clones: 0,
        };
        let empty = a.node();
        debug_assert_eq!(empty, EMPTY);
        a
    }

    fn node(&mut self) -> Node {
        self.pts.push(BTreeSet::new());
        self.succ.push(Vec::new());
        self.pts.len() - 1
    }

    fn flow(&mut self, from: Node, to: Node) {
        if from != EMPTY && to != EMPTY && from != to && !self.succ[from].contains(&to) {
            self.succ[from].push(to);
        }
    }

    fn atom(&mut self, a: Atom) -> Node {
        let n = self.node();
        self.pts[n].insert(a);
        n
    }

    fn unknown(&mut self, why: &str, span: Span) -> Node {
        self.unknowns.push((why.to_string(), span));
        let id = self.unknowns.len() - 1;
        self.atom(Atom::Unknown(id))
    }

    fn cell(&mut self, what: &str, span: Span) -> (usize, Node) {
        let contents = self.node();
        self.cells.push(CellInfo {
            contents,
            span,
            what: what.to_string(),
        });
        let site = self.cells.len() - 1;
        (site, contents)
    }

    /// The state of a host function, one for all its calls.
    fn host_cell(&mut self, name: &str, span: Span) -> usize {
        if let Some(s) = self.hosts.get(name) {
            return *s;
        }
        let (s, _) = self.cell(&format!("the host state of {name}"), span);
        self.hosts.insert(name.to_string(), s);
        s
    }

    fn new_lam(&mut self, arity: usize) -> usize {
        let params = (0..arity).map(|_| self.node()).collect();
        let ret = self.node();
        let env = self.node();
        let frame = self.node();
        self.lams.push(LamInfo {
            params,
            ret,
            env,
            frame,
        });
        self.lams.len() - 1
    }

    /// The union of some nodes.
    fn join(&mut self, parts: &[Node]) -> Node {
        let parts: Vec<Node> = parts.iter().copied().filter(|n| *n != EMPTY).collect();
        match parts.as_slice() {
            [] => EMPTY,
            [one] => *one,
            _ => {
                let n = self.node();
                for p in parts {
                    self.flow(p, n);
                }
                n
            }
        }
    }

    // ---- types ----

    fn ty(&self, t: &SurfaceTerm) -> Option<&Ty> {
        // The prelude's bodies are not typed here: what they hold is not
        // known, which holds.
        self.types.term(t)
    }

    fn local_ty(&self, name: &str, at: &SurfaceTerm) -> Option<&Ty> {
        self.types.local(name, site(at))
    }

    /// Whether a value of this type may hold a storage or a closure. `None`
    /// is not known, which holds.
    fn holds(&self, ty: Option<&Ty>) -> bool {
        match ty {
            None => true,
            Some(t) => holds(&self.types.datas, t, &mut HashSet::new()),
        }
    }

    // ---- names ----

    fn find(&self, name: &str) -> Option<usize> {
        self.bindings.iter().rposition(|b| b.name == name)
    }

    /// The current frame holds `n`.
    fn hold(&mut self, n: Node) {
        if let Some(f) = self.scopes.last().copied() {
            self.flow(n, f);
        }
    }

    /// The node of what a binding holds.
    fn bound_node(&mut self, bound: Bound) -> Node {
        match bound {
            Bound::Val(n) | Bound::Place(n) => n,
            Bound::Var(s) => self.atom(Atom::Cell(s)),
        }
    }

    fn bind(&mut self, name: &str, bound: Bound) {
        let held = self.bound_node(bound);
        self.hold(held);
        let frame = self.frames.len() - 1;
        self.bindings.push(Binding {
            name: name.to_string(),
            bound,
            frame,
        });
    }

    /// A name used from a frame inside the one that binds it is captured by
    /// every closure in between.
    fn capture(&mut self, b: usize) {
        let (bound, from) = (self.bindings[b].bound, self.bindings[b].frame);
        for f in from + 1..self.frames.len() {
            let Some(l) = self.frames[f].lam else {
                continue;
            };
            let env = self.lams[l].env;
            match bound {
                Bound::Val(n) | Bound::Place(n) => self.flow(n, env),
                Bound::Var(s) => {
                    self.pts[env].insert(Atom::Cell(s));
                }
            }
        }
    }

    // ---- program ----

    fn collect_fns(&mut self, stmts: &[Stmt], decls: &mut Vec<(usize, FnDecl)>) {
        for s in stmts {
            match s {
                Stmt::Fn(f) => {
                    let l = self.new_lam(f.params.len());
                    self.globals.insert(f.name.clone(), l);
                    self.lam_names.push(f.name.clone());
                    if !f.generics.is_empty() {
                        self.generic_fns.insert(f.name.clone(), Rc::new(f.clone()));
                    }
                    decls.push((l, f.clone()));
                }
                Stmt::Instance(i) => {
                    for m in &i.methods {
                        let l = self.new_lam(m.params.len());
                        self.methods.entry(m.name.clone()).or_default().push(l);
                        decls.push((l, m.clone()));
                    }
                }
                Stmt::Mutual { items, .. } => self.collect_fns(items, decls),
                Stmt::Extern { fns, .. } => {
                    for f in fns {
                        self.lam_names.push(f.name.clone());
                        if extern_model(&f.name).is_none() {
                            self.host_fns.insert(f.name.clone());
                        }
                    }
                }
                _ => {}
            }
        }
    }

    fn function(&mut self, l: usize, f: &FnDecl) {
        let raw = matches!(
            f.result.as_ref().map(|r| &*r.kind),
            Some(TermKind::Borrow { .. })
        );
        let ret = self.lams[l].ret;
        self.frames.push(Frame {
            lam: Some(l),
            ret,
            raw,
        });
        self.scopes.push(self.lams[l].frame);
        let mark = self.bindings.len();
        for (i, p) in f.params.iter().enumerate() {
            let n = self.lams[l].params[i];
            let bound = match f.borrows.get(i) {
                Some(Some(_)) => Bound::Place(n),
                _ => Bound::Val(n),
            };
            self.bind(p, bound);
        }
        let v = self.eval(&f.body, raw);
        self.flow(v, ret);
        self.bindings.truncate(mark);
        self.scopes.pop();
        self.frames.pop();
    }

    // ---- terms ----

    /// The node of the value of `t`. `raw` leaves places unread (a function
    /// that returns a borrow).
    fn eval(&mut self, t: &SurfaceTerm, raw: bool) -> Node {
        let n = self.eval_inner(t, raw);
        if n != EMPTY && !self.holds(self.ty(t)) {
            return EMPTY;
        }
        let n = self.typed(n, self.ty(t).cloned().as_ref());
        self.hold(n);
        n
    }

    /// `n` without the storages a value of type `ty` cannot be: the
    /// flattening merges values of different types, and a value of type
    /// `HashMap(K, V)` is never a `Ref`, whatever it was merged with.
    fn typed(&mut self, n: Node, ty: Option<&Ty>) -> Node {
        let Some(t) = ty else {
            return n;
        };
        if n == EMPTY {
            return n;
        }
        let mut kinds = BTreeSet::new();
        if !storage_kinds(&self.types.datas, t, &mut kinds, &mut HashSet::new()) {
            return n;
        }
        let d = self.node();
        self.filters.push((d, n, kinds));
        d
    }

    /// `read_through` of an argument, kept to what the argument's type allows.
    fn read_through_typed(&mut self, n: Node, t: &SurfaceTerm) -> Node {
        let v = self.read_through(n);
        self.typed(v, self.ty(t).cloned().as_ref())
    }

    fn read_through(&mut self, n: Node) -> Node {
        if n == EMPTY {
            return EMPTY;
        }
        let d = self.node();
        self.reads.push((d, n));
        d
    }

    fn eval_inner(&mut self, t: &SurfaceTerm, raw: bool) -> Node {
        match &*t.kind {
            TermKind::Var(name) => self.var(name, t, raw),
            TermKind::Nat(_)
            | TermKind::Float(_)
            | TermKind::Text(_)
            | TermKind::Bool(_)
            | TermKind::Hole(_) => EMPTY,
            TermKind::Pi { .. }
            | TermKind::Row(_)
            | TermKind::Exists { .. }
            | TermKind::Union(_)
            | TermKind::FnKind { .. } => EMPTY,
            TermKind::Tagged { term, .. } => self.eval(term, raw),
            TermKind::Field { base, .. } => {
                let b = self.eval(base, false);
                b
            }
            TermKind::Ascribe { term: base, .. } => self.eval(base, false),
            // A product as a value: it holds what its members hold.
            TermKind::Product(members) | TermKind::Tuple(members) => {
                let parts: Vec<Node> = members.iter().map(|m| self.eval(m, false)).collect();
                self.join(&parts)
            }
            TermKind::Record { fields, .. } => {
                let parts: Vec<Node> = fields.iter().map(|(_, v)| self.eval(v, false)).collect();
                self.join(&parts)
            }
            TermKind::If {
                condition,
                then,
                otherwise,
            } => {
                self.eval(condition, false);
                let a = self.eval(then, raw);
                let b = otherwise
                    .as_ref()
                    .map(|o| self.eval(o, raw))
                    .unwrap_or(EMPTY);
                self.join(&[a, b])
            }
            TermKind::Block(stmts) => self.block(stmts, raw),
            TermKind::Lam { params, body, .. } => {
                self.closure(params, &vec![None; params.len()], body, false)
            }
            TermKind::BorrowLam { borrows, lam } => match &*lam.kind {
                TermKind::Lam { params, body, .. } => self.closure(params, borrows, body, false),
                _ => self.unknown("a borrowing closure of an unexpected shape", t.span),
            },
            TermKind::Borrow { term, .. } => self.borrow(term),
            TermKind::App {
                function,
                arguments,
            } => self.app(t, function, arguments),
            TermKind::Perform { effect, args } => {
                let nodes: Vec<Node> = args.iter().map(|a| self.eval(a, false)).collect();
                let slots = self.effect_slots(effect, nodes.len());
                for (n, s) in nodes.iter().zip(slots) {
                    self.flow(*n, s);
                }
                // The handler of an effect nothing here handles (the
                // runtime's) may keep or return what it is given.
                let resume = self.effect_resume_node(effect);
                let mut parts = nodes;
                parts.push(resume);
                self.join(&parts)
            }
            TermKind::Handle { body, handlers } => self.handle(body, handlers),
            TermKind::Budget { steps, body, .. } => {
                self.eval(steps, false);
                self.eval(body, raw)
            }
            TermKind::Match {
                scrutinee, arms, ..
            } => {
                let s = self.eval(scrutinee, false);
                let mut results = Vec::new();
                for arm in arms {
                    let mark = self.bindings.len();
                    self.bind_pattern(&arm.pattern, s, &arm.body);
                    if let Some(g) = &arm.guard {
                        self.eval(g, false);
                    }
                    results.push(self.eval(&arm.body, raw));
                    self.bindings.truncate(mark);
                }
                self.join(&results)
            }
            TermKind::Step(_)
            | TermKind::Splice(_)
            | TermKind::SyntaxLit(_)
            | TermKind::MacroCall { .. }
            | TermKind::Quote { .. }
            | TermKind::Other(_) => self.unknown("syntax the cycle check does not read", t.span),
        }
    }

    fn effect_slots(&mut self, effect: &str, arity: usize) -> Vec<Node> {
        if !self.effect_args.contains_key(effect) {
            self.effect_args.insert(effect.to_string(), Vec::new());
        }
        while self.effect_args[effect].len() < arity {
            let n = self.node();
            self.effect_args.get_mut(effect).unwrap().push(n);
        }
        self.effect_args[effect][..arity].to_vec()
    }

    fn effect_resume_node(&mut self, effect: &str) -> Node {
        if let Some(n) = self.effect_resume.get(effect) {
            return *n;
        }
        let n = self.node();
        self.effect_resume.insert(effect.to_string(), n);
        n
    }

    fn var(&mut self, name: &str, t: &SurfaceTerm, raw: bool) -> Node {
        if let Some(b) = self.find(name) {
            self.capture(b);
            return match self.bindings[b].bound {
                Bound::Val(n) if raw => n,
                // A name a borrowed `match` binds to a `&mut` holds the place:
                // using it as a value copies what the place holds.
                Bound::Val(n) => self.read_through(n),
                Bound::Place(n) if raw => n,
                Bound::Place(n) => self.read_through(n),
                Bound::Var(s) => {
                    // The content of the `var`: a read, which is a copy.
                    self.cells[s].contents
                }
            };
        }
        if let Some(l) = self.globals.get(name).copied() {
            return self.atom(Atom::Lam(l));
        }
        if let Some(ls) = self.methods.get(name).cloned() {
            let n = self.node();
            for l in ls {
                self.pts[n].insert(Atom::Lam(l));
            }
            return n;
        }
        if self.types.datas.has_ctor(name)
            || extern_model(name).is_some()
            || self.host_fns.contains(name)
            || is_operator(name)
        {
            return EMPTY;
        }
        self.unknown(
            &format!("the name {name} is not known to the cycle check"),
            t.span,
        )
    }

    /// `&p` or `&mut p`: the place of a `var`, or the value.
    fn borrow(&mut self, term: &SurfaceTerm) -> Node {
        if let Some(root) = place_root(term)
            && let Some(b) = self.find(&root)
        {
            self.capture(b);
            return match self.bindings[b].bound {
                Bound::Var(s) => self.atom(Atom::Place(s)),
                Bound::Place(n) => n,
                Bound::Val(n) => n,
            };
        }
        self.eval(term, false)
    }

    fn block(&mut self, stmts: &[Stmt], raw: bool) -> Node {
        let mark = self.bindings.len();
        let mut last = EMPTY;
        let n = stmts.len();
        for (i, s) in stmts.iter().enumerate() {
            let tail = i + 1 == n;
            last = self.stmt(s, tail && raw);
            if !tail {
                last = EMPTY;
            }
        }
        self.bindings.truncate(mark);
        last
    }

    fn stmt(&mut self, s: &Stmt, raw: bool) -> Node {
        match s {
            Stmt::Let {
                name,
                value,
                borrow,
                borrow_mut,
                ..
            } => {
                let place = *borrow || *borrow_mut;
                let v = self.eval(value, place);
                let v = if self.holds(self.local_ty(name, value)) {
                    v
                } else {
                    EMPTY
                };
                self.bind(
                    name,
                    if place {
                        Bound::Place(v)
                    } else {
                        Bound::Val(v)
                    },
                );
                EMPTY
            }
            Stmt::Var {
                name,
                value,
                borrow,
                ..
            } => {
                if *borrow {
                    let v = self.eval(value, true);
                    self.bind(name, Bound::Place(v));
                } else {
                    let v = self.eval(value, false);
                    let (site, contents) = self.cell(&format!("var {name}"), value.span);
                    self.flow(v, contents);
                    self.bind(name, Bound::Var(site));
                }
                EMPTY
            }
            Stmt::Assign { name, value, .. } => {
                let v = self.eval(value, false);
                match self.find(name) {
                    Some(b) => {
                        self.capture(b);
                        match self.bindings[b].bound {
                            Bound::Var(s) => {
                                let c = self.cells[s].contents;
                                self.flow(v, c);
                            }
                            Bound::Place(p) => self.stores.push((p, v)),
                            // A name a borrowed `match` binds to a `&mut`.
                            Bound::Val(n) => self.stores.push((n, v)),
                        }
                    }
                    None => {}
                }
                EMPTY
            }
            Stmt::Fn(f) => {
                let l = self.local_fn(f);
                let n = self.atom(Atom::Lam(l));
                self.bind(&f.name, Bound::Val(n));
                EMPTY
            }
            Stmt::While { condition, body } => {
                self.eval(condition, false);
                self.eval(body, false);
                EMPTY
            }
            Stmt::Return(e) => {
                if let Some(e) = e {
                    let raw = self.frames.last().is_some_and(|f| f.raw);
                    let v = self.eval(e, raw);
                    let ret = self.frames.last().unwrap().ret;
                    self.flow(v, ret);
                }
                EMPTY
            }
            Stmt::Expr(e) => self.eval(e, raw),
            _ => EMPTY,
        }
    }

    fn local_fn(&mut self, f: &FnDecl) -> usize {
        let l = self.new_lam(f.params.len());
        // The name is visible in its own body.
        let me = self.atom(Atom::Lam(l));
        self.bind(&f.name, Bound::Val(me));
        let raw = matches!(
            f.result.as_ref().map(|r| &*r.kind),
            Some(TermKind::Borrow { .. })
        );
        self.closure_body(l, &f.params, &f.borrows, &f.body, raw);
        // `bind` is repeated by the caller with the same node; drop ours.
        self.bindings.pop();
        l
    }

    fn closure(
        &mut self,
        params: &[String],
        borrows: &[Option<bool>],
        body: &SurfaceTerm,
        raw: bool,
    ) -> Node {
        let l = self.new_lam(params.len());
        self.closure_body(l, params, borrows, body, raw);
        self.atom(Atom::Lam(l))
    }

    fn closure_body(
        &mut self,
        l: usize,
        params: &[String],
        borrows: &[Option<bool>],
        body: &SurfaceTerm,
        raw: bool,
    ) {
        let ret = self.lams[l].ret;
        self.frames.push(Frame {
            lam: Some(l),
            ret,
            raw,
        });
        self.scopes.push(self.lams[l].frame);
        let mark = self.bindings.len();
        for (i, p) in params.iter().enumerate() {
            let n = self.lams[l].params[i];
            let bound = match borrows.get(i) {
                Some(Some(_)) => Bound::Place(n),
                _ => Bound::Val(n),
            };
            self.bind(p, bound);
        }
        let v = self.eval(body, raw);
        self.flow(v, ret);
        self.bindings.truncate(mark);
        self.scopes.pop();
        self.frames.pop();
    }

    fn app(&mut self, t: &SurfaceTerm, function: &SurfaceTerm, arguments: &[SurfaceTerm]) -> Node {
        let named = match &*function.kind {
            TermKind::Var(n) if self.find(n).is_none() => Some(n.as_str()),
            _ => None,
        };
        if let Some(name) = named {
            if let Some(l) = self.clone_of(name) {
                self.args(arguments, Some(l));
                self.hold(self.lams[l].frame);
                return self.lams[l].ret;
            }
            if let Some(l) = self.globals.get(name).copied() {
                let args = self.args(arguments, Some(l));
                let res = self.lams[l].ret;
                self.hold(self.lams[l].frame);
                let _ = args;
                return res;
            }
            if let Some(model) = extern_model(name) {
                return self.extern_call(model, name, t, arguments);
            }
            if self.host_fns.contains(name) {
                return self.extern_call(Extern::Host, name, t, arguments);
            }
            if let Some(ls) = self.methods.get(name).cloned() {
                let args: Vec<Node> = arguments.iter().map(|a| self.eval(a, false)).collect();
                let res = self.node();
                for l in ls {
                    for (a, p) in args.iter().zip(self.lams[l].params.clone()) {
                        self.flow(*a, p);
                    }
                    let r = self.lams[l].ret;
                    self.flow(r, res);
                    self.hold(self.lams[l].frame);
                }
                return res;
            }
            if self.types.datas.has_ctor(name) || is_operator(name) || name == "Tuple" {
                let parts: Vec<Node> = arguments.iter().map(|a| self.eval(a, false)).collect();
                return self.join(&parts);
            }
            self.unknown(
                &format!("the function {name} is not known to the cycle check"),
                t.span,
            );
        }
        let callee = self.eval(function, false);
        let args: Vec<Node> = arguments.iter().map(|a| self.eval(a, false)).collect();
        let res = self.node();
        let frame = self.scopes.last().copied().unwrap_or(EMPTY);
        self.calls.push(Call {
            callee,
            args,
            res,
            frame,
        });
        res
    }

    /// A copy of the generic function `name` for one call, so that what one
    /// caller passes through it does not come back to another: a generic
    /// body cannot look into the values of its type parameters, and one
    /// shared copy would merge, say, the contents of every mutex a
    /// `mutex_with` is ever given. A copy is the same body over fresh nodes,
    /// so it makes every value and storage the call may make; a call to a
    /// function already being copied (recursion) and every use as a value
    /// read the shared copy instead.
    fn clone_of(&mut self, name: &str) -> Option<usize> {
        let decl = self.generic_fns.get(name)?.clone();
        if self.cloning.iter().any(|n| n == name) || self.clones >= MAX_CLONES {
            return None;
        }
        self.clones += 1;
        let l = self.new_lam(decl.params.len());
        // The body sees what a global body sees: no local name.
        let frames = std::mem::replace(
            &mut self.frames,
            vec![Frame {
                lam: None,
                ret: EMPTY,
                raw: false,
            }],
        );
        let bindings = std::mem::take(&mut self.bindings);
        let scopes = std::mem::take(&mut self.scopes);
        self.cloning.push(name.to_string());
        self.function(l, &decl);
        self.cloning.pop();
        self.frames = frames;
        self.bindings = bindings;
        self.scopes = scopes;
        Some(l)
    }

    /// Evaluates the arguments of a call to a known function into its
    /// parameters.
    fn args(&mut self, arguments: &[SurfaceTerm], lam: Option<usize>) -> Vec<Node> {
        let nodes: Vec<Node> = arguments.iter().map(|a| self.eval(a, false)).collect();
        if let Some(l) = lam {
            for (a, p) in nodes.iter().zip(self.lams[l].params.clone()) {
                self.flow(*a, p);
            }
        }
        nodes
    }

    fn extern_call(
        &mut self,
        model: Extern,
        name: &str,
        t: &SurfaceTerm,
        arguments: &[SurfaceTerm],
    ) -> Node {
        let args: Vec<Node> = arguments.iter().map(|a| self.eval(a, true)).collect();
        // The storage an operation works on is the first argument, read
        // through when it is a place.
        let target = |s: &mut Self| match args.first() {
            Some(a) => s.read_through_typed(*a, &arguments[0]),
            None => EMPTY,
        };
        match model {
            Extern::Flatten => {
                let parts: Vec<Node> = args.iter().map(|a| self.read_through(*a)).collect();
                self.join(&parts)
            }
            Extern::Host => {
                let h = self.host_cell(name, t.span);
                let contents = self.cells[h].contents;
                for a in &args {
                    let v = self.read_through(*a);
                    self.flow(v, contents);
                }
                let handle = self.atom(Atom::Cell(h));
                let d = self.node();
                self.flow(contents, d);
                self.join(&[handle, d])
            }
            Extern::Alloc => {
                let (site, contents) = self.cell(name, t.span);
                for a in &args {
                    let v = self.read_through(*a);
                    self.flow(v, contents);
                }
                self.atom(Atom::Cell(site))
            }
            Extern::Store => {
                let c = target(self);
                for a in args.iter().skip(1) {
                    let v = self.read_through(*a);
                    self.stores.push((c, v));
                }
                EMPTY
            }
            Extern::Load => {
                let c = target(self);
                let d = self.node();
                self.loads.push((d, c));
                d
            }
            Extern::Swap => {
                let c = target(self);
                for a in args.iter().skip(1) {
                    let v = self.read_through(*a);
                    self.stores.push((c, v));
                }
                let d = self.node();
                self.loads.push((d, c));
                d
            }
            Extern::Replace => {
                let c = args.first().copied().unwrap_or(EMPTY);
                for a in args.iter().skip(1) {
                    let v = self.read_through(*a);
                    self.stores.push((c, v));
                }
                let d = self.node();
                self.reads.push((d, c));
                d
            }
            Extern::Downgrade => {
                let c = target(self);
                let d = self.node();
                self.weakens.push((d, c));
                d
            }
            Extern::Upgrade => {
                let c = target(self);
                let d = self.node();
                self.upgrades.push((d, c));
                d
            }
            Extern::LoadMut => {
                let c = target(self);
                let d = self.node();
                self.places.push((d, c));
                d
            }
            Extern::Convert if storage_kind(name).is_some() => {
                // A storage of another kind, holding what the first held.
                let c = target(self);
                let (site, contents) = self.cell(name, t.span);
                self.loads.push((contents, c));
                self.atom(Atom::Cell(site))
            }
            Extern::Convert => {
                let c = target(self);
                let d = self.node();
                self.loads.push((d, c));
                d
            }
        }
    }

    fn bind_pattern(&mut self, p: &Pattern, from: Node, at: &SurfaceTerm) {
        let mut names = Vec::new();
        pattern_names(p, &mut names);
        for n in names {
            let v = if self.holds(self.local_ty(&n, at)) {
                from
            } else {
                EMPTY
            };
            self.bind(&n, Bound::Val(v));
        }
    }

    fn handle(&mut self, body: &SurfaceTerm, handlers: &[Handler]) -> Node {
        // What the body holds at a `perform`: the stack up to this handle.
        let stack = self.node();
        self.scopes.push(stack);
        let b = self.eval(body, false);
        self.scopes.pop();
        // The body runs in the frame around the handle.
        self.hold(stack);
        // The frames of the body hold the scope of the handle (the evaluator's
        // frames hold their whole environment), and a resume reinstalls the
        // handler, whose arms see that scope too.
        for i in 0..self.bindings.len() {
            let held = self.bound_node(self.bindings[i].bound);
            self.flow(held, stack);
        }
        let res = self.node();
        let mut returned = false;
        for h in handlers {
            let mark = self.bindings.len();
            match h {
                Handler::Return { pattern, body: arm } => {
                    returned = true;
                    self.bind_pattern(pattern, b, arm);
                    let v = self.eval(arm, false);
                    self.flow(v, res);
                }
                Handler::Operation {
                    effect,
                    patterns,
                    cont,
                    guard,
                    body: arm,
                    ..
                } => {
                    let slots = self.effect_slots(effect, patterns.len());
                    for (p, s) in patterns.iter().zip(slots) {
                        self.bind_pattern(p, s, arm);
                    }
                    if let Some(k) = cont {
                        // The continuation holds the stack of the body and
                        // the handler.
                        let l = self.new_lam(1);
                        let resume = self.effect_resume_node(effect);
                        let p = self.lams[l].params[0];
                        self.flow(p, resume);
                        self.flow(res, self.lams[l].ret);
                        let env = self.lams[l].env;
                        self.flow(stack, env);
                        self.flow(env, self.lams[l].frame);
                        let n = self.atom(Atom::Lam(l));
                        self.bind(k, Bound::Val(n));
                    }
                    if let Some(g) = guard {
                        self.eval(g, false);
                    }
                    let v = self.eval(arm, false);
                    self.flow(v, res);
                }
            }
            self.bindings.truncate(mark);
        }
        if !returned {
            self.flow(b, res);
        }
        res
    }

    // ---- solving ----

    fn solve(&mut self) {
        loop {
            let mut changed = false;
            // Copy edges.
            for n in 0..self.pts.len() {
                if self.pts[n].is_empty() {
                    continue;
                }
                let targets = self.succ[n].clone();
                for m in targets {
                    let src: Vec<Atom> = self.pts[n].iter().copied().collect();
                    for a in src {
                        changed |= self.pts[m].insert(a);
                    }
                }
            }
            // Loads, reads, stores.
            for i in 0..self.loads.len() {
                let (dst, src) = self.loads[i];
                for a in self.pts[src].clone() {
                    if let Atom::Cell(c) | Atom::Place(c) = a {
                        let contents = self.cells[c].contents;
                        for x in self.pts[contents].clone() {
                            changed |= self.pts[dst].insert(x);
                        }
                    }
                }
            }
            for i in 0..self.reads.len() {
                let (dst, src) = self.reads[i];
                for a in self.pts[src].clone() {
                    match a {
                        Atom::Place(c) => {
                            let contents = self.cells[c].contents;
                            for x in self.pts[contents].clone() {
                                changed |= self.pts[dst].insert(x);
                            }
                        }
                        other => changed |= self.pts[dst].insert(other),
                    }
                }
            }
            for i in 0..self.places.len() {
                let (dst, src) = self.places[i];
                for a in self.pts[src].clone() {
                    if let Atom::Cell(c) | Atom::Place(c) = a {
                        changed |= self.pts[dst].insert(Atom::Place(c));
                    }
                }
            }
            for i in 0..self.weakens.len() {
                let (dst, src) = self.weakens[i];
                for a in self.pts[src].clone() {
                    if let Atom::Cell(c) = a {
                        changed |= self.pts[dst].insert(Atom::Weak(c));
                    }
                }
            }
            for i in 0..self.upgrades.len() {
                let (dst, src) = self.upgrades[i];
                for a in self.pts[src].clone() {
                    if let Atom::Weak(c) = a {
                        changed |= self.pts[dst].insert(Atom::Cell(c));
                    }
                }
            }
            for i in 0..self.filters.len() {
                let (dst, src) = (self.filters[i].0, self.filters[i].1);
                for a in self.pts[src].clone() {
                    let kept = match a {
                        Atom::Cell(c) => storage_kind(&self.cells[c].what)
                            .is_none_or(|k| self.filters[i].2.contains(k)),
                        _ => true,
                    };
                    if kept {
                        changed |= self.pts[dst].insert(a);
                    }
                }
            }
            for i in 0..self.stores.len() {
                let (dst, src) = self.stores[i];
                for a in self.pts[dst].clone() {
                    if let Atom::Cell(c) | Atom::Place(c) = a {
                        let contents = self.cells[c].contents;
                        let before = self.succ[src].len();
                        self.flow(src, contents);
                        changed |= self.succ[src].len() != before;
                    }
                }
            }
            for i in 0..self.calls.len() {
                let (callee, res, frame) =
                    (self.calls[i].callee, self.calls[i].res, self.calls[i].frame);
                for a in self.pts[callee].clone() {
                    match a {
                        Atom::Lam(l) => {
                            let args = self.calls[i].args.clone();
                            let before = self.succ.iter().map(Vec::len).sum::<usize>();
                            for (x, p) in args.iter().zip(self.lams[l].params.clone()) {
                                self.flow(*x, p);
                            }
                            let r = self.lams[l].ret;
                            self.flow(r, res);
                            self.flow(self.lams[l].frame, frame);
                            changed |= self.succ.iter().map(Vec::len).sum::<usize>() != before;
                        }
                        Atom::Unknown(_) => changed |= self.pts[res].insert(a),
                        _ => {}
                    }
                }
            }
            if !changed {
                break;
            }
        }
    }

    // ---- result ----

    /// The sites a content reaches through immutable values and closures.
    fn frontier(&self, contents: Node) -> (BTreeSet<usize>, Vec<usize>) {
        let mut cells = BTreeSet::new();
        let mut unknown = Vec::new();
        let mut seen_lams = BTreeSet::new();
        let mut stack: Vec<Atom> = self.pts[contents].iter().copied().collect();
        while let Some(a) = stack.pop() {
            match a {
                Atom::Cell(c) | Atom::Place(c) => {
                    cells.insert(c);
                }
                Atom::Lam(l) => {
                    if seen_lams.insert(l) {
                        stack.extend(self.pts[self.lams[l].env].iter().copied());
                    }
                }
                Atom::Unknown(u) => unknown.push(u),
                // A `Weak` keeps nothing alive.
                Atom::Weak(_) => {}
            }
        }
        (cells, unknown)
    }

    /// The errors, each independent of the order the analysis numbered
    /// things in, sorted by where they are: what the self-hosted checker
    /// computes the same.
    fn diagnostics(&self) -> Vec<CycleDiag> {
        let mut out = Vec::new();
        let n = self.cells.len();
        let mut edges: Vec<BTreeSet<usize>> = vec![BTreeSet::new(); n];
        for (c, info) in self.cells.iter().enumerate() {
            let (cells, unknown) = self.frontier(info.contents);
            edges[c] = cells;
            if let Some((why, _)) = unknown
                .iter()
                .map(|u| &self.unknowns[*u])
                .min_by_key(|(why, span)| (span.start, why.clone()))
            {
                out.push(CycleDiag {
                    message: format!(
                        "{} may hold a value that cannot be checked for reference cycles: {why}",
                        info.what
                    ),
                    span: info.span,
                });
            }
        }
        // What each storage reaches; a storage on a cycle reaches itself, and
        // its component is the storages that reach it back.
        let reach: Vec<BTreeSet<usize>> = (0..n)
            .map(|c| {
                let mut seen = BTreeSet::new();
                let mut stack: Vec<usize> = edges[c].iter().copied().collect();
                while let Some(d) = stack.pop() {
                    if seen.insert(d) {
                        stack.extend(edges[d].iter().copied());
                    }
                }
                seen
            })
            .collect();
        let mut done: BTreeSet<usize> = BTreeSet::new();
        for c in 0..n {
            if done.contains(&c) || !reach[c].contains(&c) {
                continue;
            }
            let mut component: Vec<usize> = (0..n)
                .filter(|d| reach[c].contains(d) && reach[*d].contains(&c))
                .collect();
            done.extend(component.iter().copied());
            let base = tauto_surface_prelude_base();
            component.sort_by_key(|d| {
                let s = self.cells[*d].span.start;
                (s >= base, s, self.cells[*d].what.clone())
            });
            let names: Vec<String> = component
                .iter()
                .map(|d| self.cells[*d].what.clone())
                .collect();
            let message = if names.len() == 1 {
                format!(
                    "{} may hold itself through a closure or a data structure, which is a strong reference cycle",
                    names[0]
                )
            } else {
                format!("strong reference cycle among {}", names.join(", "))
            };
            out.push(CycleDiag {
                message,
                span: self.cells[component[0]].span,
            });
        }
        out.sort_by(|a, b| {
            (a.span.start, a.span.end, &a.message).cmp(&(b.span.start, b.span.end, &b.message))
        });
        out.dedup();
        out
    }
}

fn tauto_surface_prelude_base() -> u32 {
    crate::surface::PRELUDE_BASE
}

fn is_operator(name: &str) -> bool {
    name.bytes()
        .next()
        .is_some_and(|c| c.is_ascii_punctuation() && c != b'_')
}

/// The name a place starts at: `x`, `x.f`.
fn place_root(t: &SurfaceTerm) -> Option<String> {
    match &*t.kind {
        TermKind::Var(n) => Some(n.clone()),
        TermKind::Field { base, .. } => place_root(base),
        _ => None,
    }
}

fn holds(datas: &Datas, t: &Ty, seen: &mut HashSet<String>) -> bool {
    match t {
        Ty::Int(_)
        | Ty::Bool
        | Ty::Text
        | Ty::Unit
        | Ty::Never
        | Ty::Decimal
        | Ty::Float
        | Ty::Float32 => false,
        // A parameter of a data type, met in the fields of one: it stands for
        // an argument the `Named` case has already read, so it adds nothing.
        // A recursive field such as the tail of a `List(A)` is read without
        // its parameter counting as an unknown type.
        Ty::Param(p, _) if matches!(p.id(), ParamId::Data { .. }) => false,
        Ty::Fn(..) | Ty::Poly(..) | Ty::Var(_) | Ty::Param(..) | Ty::App(..) => true,
        Ty::Union(ts) | Ty::Product(ts) => ts.iter().any(|t| holds(datas, t, seen)),
        Ty::Tagged(_, t) | Ty::Info(t) | Ty::Borrow(t, _) => holds(datas, t, seen),
        Ty::Named(n, args) => {
            if matches!(
                n.as_str(),
                "Ref" | "Mutex" | "Vec" | "HashMap" | "Slice" | "Task" | "Pending"
            ) {
                return true;
            }
            if matches!(n.as_str(), "Atomic" | "Buf" | "Bytes") {
                return false;
            }
            if args.iter().any(|a| holds(datas, a, seen)) {
                return true;
            }
            let Some(d) = datas.decls.get(n) else {
                return true;
            };
            // A type with no fields and no case is a handle the host
            // provides.
            if d.constructors.iter().all(|c| c.fields.is_empty())
                && d.constructors.len() <= 1
                && d.is_struct
            {
                return true;
            }
            // `seen` keeps every type already entered, not only those on the
            // current path: a type reached twice reaches the same fields, so
            // reading it again adds nothing. Taking it off again on the way
            // out made the walk follow every path through the fields, which
            // grows exponentially with the depth of nested data types.
            if !seen.insert(n.clone()) {
                return false;
            }
            d.constructors
                .iter()
                .flat_map(|c| c.fields.iter())
                .any(|(_, f)| holds(datas, f, seen))
        }
    }
}

/// The kind of storage an allocation makes, by the name of the `extern`
/// that makes it; `None` for every other storage (a `var`, a host state).
fn storage_kind(what: &str) -> Option<&'static str> {
    Some(match what {
        "Ref::new" => "Ref",
        "Mutex::new" => "Mutex",
        "Vec::new" | "HashMap::into_vec" => "Vec",
        "HashMap::new" => "HashMap",
        _ => return None,
    })
}

/// The kinds of storage a value of type `t` may hold without going through
/// a storage or a closure, into `kinds`; `false` when any storage may be
/// (a function, a type parameter, a type the check does not know).
fn storage_kinds(
    datas: &Datas,
    t: &Ty,
    kinds: &mut BTreeSet<&'static str>,
    seen: &mut HashSet<String>,
) -> bool {
    match t {
        Ty::Int(_)
        | Ty::Bool
        | Ty::Text
        | Ty::Unit
        | Ty::Never
        | Ty::Decimal
        | Ty::Float
        | Ty::Float32 => true,
        // As in `holds`: the argument the `Named` case has already read.
        Ty::Param(p, _) if matches!(p.id(), ParamId::Data { .. }) => true,
        Ty::Fn(..) | Ty::Poly(..) | Ty::Var(_) | Ty::Param(..) | Ty::App(..) => false,
        Ty::Union(ts) | Ty::Product(ts) => ts.iter().all(|t| storage_kinds(datas, t, kinds, seen)),
        Ty::Tagged(_, t) | Ty::Info(t) | Ty::Borrow(t, _) => storage_kinds(datas, t, kinds, seen),
        Ty::Named(n, args) => {
            // The storages the prelude declares, read by name as `holds`
            // reads them.
            if let Some(k) = storage_kind_of_type(n) {
                kinds.insert(k);
                return true;
            }
            if matches!(n.as_str(), "Atomic" | "Buf" | "Bytes") {
                return true;
            }
            if !args.iter().all(|a| storage_kinds(datas, a, kinds, seen)) {
                return false;
            }
            let Some(d) = datas.decls.get(n) else {
                return false;
            };
            // A host handle.
            if d.constructors.iter().all(|c| c.fields.is_empty())
                && d.constructors.len() <= 1
                && d.is_struct
            {
                return false;
            }
            if !seen.insert(n.clone()) {
                return true;
            }
            d.constructors
                .iter()
                .flat_map(|c| c.fields.iter())
                .all(|(_, f)| storage_kinds(datas, f, kinds, seen))
        }
    }
}

fn storage_kind_of_type(name: &str) -> Option<&'static str> {
    Some(match name {
        "Ref" => "Ref",
        "Mutex" => "Mutex",
        "Vec" => "Vec",
        "HashMap" => "HashMap",
        _ => return None,
    })
}

/// The reference cycles a program may build, as errors.
pub fn check(program: &Program, types: &TypeReport) -> Vec<CycleDiag> {
    let mut a = Analysis::new(types);
    let mut decls = Vec::new();
    a.collect_fns(&prelude().stmts, &mut decls);
    a.collect_fns(&program.stmts, &mut decls);
    a.frames.push(Frame {
        lam: None,
        ret: EMPTY,
        raw: false,
    });
    for (l, f) in &decls {
        a.function(*l, f);
    }
    // The top level is a body of its own.
    let stmts: Vec<Stmt> = program
        .stmts
        .iter()
        .filter(|s| !matches!(s, Stmt::Fn(_)))
        .cloned()
        .collect();
    a.block(&stmts, false);
    a.solve();
    a.diagnostics()
}

#[cfg(test)]
mod tests {
    use crate::lin::check_lin_program;
    use crate::surface::parse_program_as_written;

    fn errors(source: &str) -> Vec<String> {
        let program = parse_program_as_written(source).expect("parses");
        match check_lin_program(&program) {
            Ok(errors) => errors.into_iter().map(|e| e.message).collect(),
            Err(e) => panic!("{e}"),
        }
    }

    fn accepts(source: &str) {
        let e = errors(source);
        assert!(e.is_empty(), "{e:?}");
    }

    fn rejects(source: &str, needle: &str) {
        let e = errors(source);
        assert!(
            e.iter().any(|m| m.contains(needle)),
            "expected an error with {needle:?}, got {e:?}"
        );
    }

    #[test]
    fn a_counter_closure_is_free() {
        accepts(
            "fn make(): () -> i64 {\n  let n := Ref::new(0)\n  () => {\n    Ref::set(n, Ref::get(n) + 1)\n    Ref::get(n)\n  }\n}\nlet c := make()\nlet x := c()",
        );
    }

    #[test]
    fn a_ref_that_holds_a_closure_over_itself_is_a_cycle() {
        rejects(
            "let r := Ref::new(() => 0)\nRef::set(r, () => Ref::get(r)())",
            "Ref::new",
        );
    }

    #[test]
    fn two_cells_through_immutable_pairs_are_a_cycle() {
        rejects(
            "let a := Ref::new(Pair { fst: () => 0, snd: 0 })\nlet b := Ref::new(() => 0)\nRef::set(a, Pair { fst: () => Ref::get(b)(), snd: 1 })\nRef::set(b, () => Ref::get(a).fst())",
            "cycle",
        );
    }

    #[test]
    fn a_long_immutable_list_is_free() {
        accepts(
            "fn build(n: u64): List(u64) {\n  if n == 0 { Nil } else { Cons(n, build(n - 1)) }\n}\nlet xs := build(10)",
        );
    }

    #[test]
    fn independent_cells_are_free() {
        accepts(
            "let a := ref_new(1)\nlet b := ref_new(2)\nref_set(a, ref_get(b))\nlet n := ref_get(a)",
        );
    }

    #[test]
    fn a_vec_in_a_ref_that_holds_a_closure_over_the_ref_is_a_cycle() {
        rejects(
            "let r := Ref::new(0)\nlet m := Mutex::new(Vec::new())\nMutex::lock(m, (&mut v) => Vec::push(&mut v, () => Mutex::lock(m, (&mut w) => Vec::len(&w))))",
            "cycle",
        );
    }

    #[test]
    fn a_weak_back_reference_is_free() {
        accepts(
            "let a := Ref::new(() => 0)\nlet w := Weak::of(a)\nRef::set(a, () => match Weak::get(w) { Some(r) => 1\n None => 0 })",
        );
    }

    #[test]
    fn a_weak_made_strong_again_is_a_cycle() {
        rejects(
            "let a := Ref::new(() => 0)\nlet w := Weak::of(a)\nmatch Weak::get(w) {\n  Some(r) => Ref::set(a, () => Ref::get(r)())\n  None => ()\n}",
            "cycle",
        );
    }

    #[test]
    fn replace_writes_the_place() {
        rejects(
            "let m := Mutex::new(() => 0)\nMutex::lock(m, (&mut f) => replace(&mut f, () => Mutex::lock(m, (&mut g) => 1)))",
            "cycle",
        );
    }

    // A program that keeps a continuation: a generator stepped from outside.
    const GEN: &str = "effect tick(n: i64): ()\naffine enum S { Done, More(i64, affine (()) -> S ! {}) }\nfn gen(n: i64): S ! {} {\n  handle { perform tick(n)\n perform tick(n + 1) } with {\n    return _ => Done\n    tick(x), k => More(x, k)\n  }\n}\n";

    #[test]
    fn a_continuation_kept_in_a_mutex_is_free() {
        accepts(&format!(
            "{GEN}let m := Mutex::new(gen(1))\nlet s := Mutex::take(m)\nmatch s {{ More(_, k) => Mutex::put(m, k(()))\n Done => Mutex::put(m, Done) }}"
        ));
    }

    #[test]
    fn a_continuation_whose_body_holds_its_mutex_is_a_cycle() {
        rejects(
            "effect tick(): ()\naffine enum S { Done, More(affine (()) -> S ! {}) }\nlet m := Mutex::new(Done)\nlet s := handle { perform tick()\n Mutex::put(m, Done) } with {\n  return _ => Done\n  tick(), k => More(k)\n}\nMutex::put(m, s)",
            "cycle",
        );
    }

    #[test]
    fn a_continuation_whose_handler_holds_its_mutex_is_a_cycle() {
        rejects(
            "effect tick(): ()\naffine enum S { Done, More(affine (()) -> S ! {}) }\nlet m := Mutex::new(Done)\nlet t := handle { perform tick()\n Done } with {\n  tick(), k => {\n Mutex::put(m, More(k))\n Done }\n}",
            "cycle",
        );
    }

    #[test]
    fn a_continuation_holds_the_frames_it_was_performed_in() {
        rejects(
            "effect tick(): ()\naffine enum S { Done, More(affine (()) -> S ! {}) }\nlet m := Mutex::new(Done)\nfn inner(q: Mutex(S)): () ! {tick} {\n  perform tick()\n  Mutex::put(q, Done)\n}\nlet s := handle { inner(m) } with {\n  return _ => Done\n  tick(), k => More(k)\n}\nMutex::put(m, s)",
            "cycle",
        );
    }

    #[test]
    fn a_continuation_holds_the_scope_of_its_handle() {
        rejects(
            "effect tick(): ()\naffine enum S { Done, More(affine (()) -> S ! {}) }\nlet m := Mutex::new(Done)\nlet s := handle { perform tick()\n Done } with {\n  return _ => Done\n  tick(), k => More(k)\n}\nMutex::put(m, s)",
            "cycle",
        );
    }

    #[test]
    fn reading_a_slot_of_a_vec_copies_its_content() {
        accepts(
            "fn push_at(&mut v: Vec(List(u64)), i: u64, p: u64): () {\n  match Vec::get_mut(&mut v, i) {\n    Some(slot) => {\n      slot := Cons(p, slot)\n    }\n    None => ()\n  }\n}\nvar v: Vec(List(u64)) := Vec::new()\nVec::push(&mut v, Nil)\npush_at(&mut v, 0, 1)",
        );
    }
}
