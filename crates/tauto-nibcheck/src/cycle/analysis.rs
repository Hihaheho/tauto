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
//! A record literal keeps its fields apart (a `Rec` atom), so reading one
//! field holds only what that field holds. Every other value is flattened: a
//! list, an enum or a closure's environment is the set of atoms it may hold,
//! with no position, and so is a record once a pattern takes it apart or it is
//! written or read through a place inside another value. That loses precision
//! and never soundness. Anything the analysis does not model is an
//! `Unknown` atom, and an `Unknown` in a frontier is an error, so it is never
//! read as the empty set.

use crate::surface::Name;
use std::collections::{BTreeSet, HashMap, HashSet};
use std::rc::Rc;
use tauto_message::{Message, msg};

use tauto_parol::Span;

use crate::lin::pattern_names;
use crate::rows::RowReport;
use crate::surface::{FnDecl, Handler, Pattern, Program, Stmt, SurfaceTerm, TermKind};
use crate::types::{Datas, ParamId, Ty, TypeReport, site};

#[derive(Debug, Clone, PartialEq)]
pub struct CycleDiag {
    pub message: Message,
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
    Lam(usize),
    /// A value nothing is known about.
    Unknown(usize),
    /// A `Weak` on the storage of a site: no edge, a `Cell` again through
    /// `weak_get`.
    Weak(usize),
    /// A record made by a literal: what it holds, field by field.
    Rec(usize),
    /// A place inside the storage of a site (`&mut x.f`): read and written as
    /// the place of the whole storage, with records flattened, since which
    /// part of the content it is is not kept.
    Part(usize),
}

#[derive(Debug, Clone)]
struct RecInfo {
    fields: Vec<(String, Node)>,
    /// The record a `{ ..base }` update takes its other fields from.
    rest: Option<Node>,
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

#[derive(Clone, Copy, Debug)]
enum Bound {
    Val(Node),
    /// A borrowed parameter or view: the place it stands for is read through.
    Place(Node),
    Var(usize),
}

struct Binding {
    name: Name,
    bound: Bound,
    frame: usize,
}

struct Frame {
    lam: Option<usize>,
    ret: Node,
    /// The function returns a borrow, so its result is not read through.
    raw: bool,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Extern {
    /// The result holds what the arguments held: an immutable value built
    /// from them, or nothing at all when its type holds no storage.
    Flatten,
    /// A function the host provides: it keeps what it is given in a state of
    /// its own, which it may give back, and its handles are that state.
    Host,
    Alloc,
    Store,
    Load,
    Downgrade,
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

/// The `extern` the host answers a storage operation with.
fn storage_operation(effect: &Name) -> Option<&'static str> {
    [
        ("ref_new", "Ref::new"),
        ("ref_get", "Ref::get"),
        ("ref_set", "Ref::set"),
        ("weak_of", "Weak::of"),
        ("weak_get", "Weak::get"),
        ("mutex_new", "Mutex::new"),
        ("mutex_claim", "Mutex::claim"),
        ("mutex_take_claimed", "Mutex::take_claimed"),
        ("mutex_put", "Mutex::put"),
        ("mutex_withdraw", "Mutex::withdraw"),
        ("atomic_new", "Atomic::new"),
        ("atomic_load", "Atomic::load"),
        ("atomic_store", "Atomic::store"),
        ("atomic_fetch_add", "Atomic::fetch_add"),
    ]
    .into_iter()
    .find(|(op, _)| tauto_surface::bindings::is_library(effect, op))
    .map(|(_, what)| what)
}

fn extern_model(name: &str) -> Option<Extern> {
    use Extern::*;
    Some(match name {
        "Ref::new" | "Mutex::new" | "Vec::new" | "Slots::new" | "Slots::copy" => Alloc,
        "Ref::set" | "Mutex::put" | "Vec::push" | "Slots::put" | "Slots::resize" => Store,
        "replace" => Replace,
        "Weak::of" => Downgrade,
        "Weak::get" => Upgrade,
        "Vec::get_mut"
        | "Vec::last_mut"
        | "Vec::as_mut_slice"
        | "Slots::get_mut"
        | "MutexGuard::get_mut" => LoadMut,
        "Ref::get"
        | "Mutex::take_claimed"
        | "Mutex::withdraw"
        | "Vec::pop"
        | "Vec::get"
        | "Vec::as_slice"
        | "Slice::get"
        | "Slots::get"
        | "Slots::take"
        | "MutexGuard::get" => Load,
        "Vec::into_list" | "Vec::into_array" => Convert,
        "Vec::len"
        | "Vec::clear"
        | "Vec::truncate"
        | "Vec::swap_within"
        | "Slots::state"
        | "Slots::mark"
        | "Slots::cap"
        | "Slice::len"
        | "Text::of"
        | "Buf::of"
        | "Buf::clone"
        | "Buf::new"
        | "Buf::push"
        | "Syn::parse"
        | "Syn::expr_of"
        | "Syn::expand"
        | "Syn::open"
        | "Judgement::mentions"
        | "Judgement::same_atom"
        | "Elab::Raw::whnf"
        | "Elab::Raw::defeq"
        | "Elab::Raw::check"
        | "Elab::Raw::global"
        | "Elab::Raw::resolve"
        | "I64::of_i8"
        | "I64::of_i16"
        | "I8::of_i64"
        | "I16::of_i64"
        | "U64::of_u16"
        | "U16::of_u64"
        | "I64::of_i32"
        | "I32::of_i64"
        | "I64::of_u64"
        | "U64::of_i64"
        | "U64::of_u32"
        | "U32::of_u64"
        | "U64::of_u8"
        | "U64::of_uhost"
        | "UHost::succ_below"
        | "UHost::pred_nz"
        | "UHost::add_within"
        | "UHost::sub"
        | "UHost::of_u64_below"
        | "U8::of_u64"
        | "Os::args"
        | "Os::read_file"
        | "Os::write_file"
        | "Os::read_bytes"
        | "Os::write_bytes"
        | "Os::read_under"
        | "Os::read_bytes_under"
        | "Os::secure_random"
        | "Os::create_dir"
        | "Os::list_dir"
        | "Os::remove"
        | "Os::temp_dir"
        | "Os::run"
        | "Os::child_spawn"
        | "Os::child_read"
        | "Os::child_write"
        | "Os::child_close_stdin"
        | "Os::child_wait"
        | "Os::child_close"
        | "Os::print"
        | "Os::eprint"
        | "Os::http_open"
        | "Os::http_write"
        | "Os::http_finish"
        | "Os::http_read"
        | "Os::http_close"
        | "Os::tcp_listen"
        | "Os::tcp_accept"
        | "Os::tcp_connect"
        | "Os::tcp_read"
        | "Os::tcp_write"
        | "Os::tcp_shutdown"
        | "Os::tcp_close"
        | "Os::tcp_unlisten"
        | "Os::tls_accept"
        | "Os::tls_connect"
        | "Os::tls_read"
        | "Os::tls_write"
        | "Os::tls_shutdown"
        | "Os::tls_close"
        | "Os::exit"
        | "Os::stop"
        | "Os::sleep_pending"
        | "Os::tcp_ready"
        | "Os::tcp_send"
        | "Os::tls_ready"
        | "Os::tls_send"
        | "Os::offload"
        | "Pending::ready"
        | "Pending::take"
        | "Pending::is_ready"
        | "Pending::signal"
        | "Signal::fresh"
        | "Signal::raise"
        | "Signal::is_raised"
        | "Signal::either"
        | "Signal::listen"
        | "Mutex::claim"
        // The guard holds the mutex, so reading or writing through it is
        // reading or writing the mutex's content.
        | "MutexGuard::claimed"
        | "Atomic::new"
        | "Atomic::load"
        | "Atomic::store"
        | "Atomic::fetch_add"
        | "words"
        | "concat"
        | "Array::of_list"
        | "Array::get"
        | "Array::len"
        | "Array::set"
        | "Array::to_list"
        | "Bytes::of_list"
        | "Bytes::to_list"
        | "Bytes::len"
        | "Bytes::get"
        | "Bytes::find"
        | "Bytes::slice"
        | "Bytes::concat"
        | "Bytes::eq"
        | "Bytes::of_text"
        | "Text::of_bytes"
        | "Text::len"
        | "Text::byte"
        | "Text::slice"
        | "Text::compare"
        | "Text::of_code_point"
        | "Text::escape_debug"
        | "Text::of_utf8"
        | "Text::of_i64"
        | "Text::of_u64"
        | "U32::and"
        | "U32::or"
        | "U32::xor"
        | "U32::shl"
        | "U32::shr"
        | "U32::rotl"
        | "U32::rotr"
        | "U64::and"
        | "U64::or"
        | "U64::xor"
        | "U64::shl"
        | "U64::shr"
        | "U64::rotl"
        | "U64::rotr"
        | "U64::wrapping_add"
        | "U64::wrapping_sub"
        | "U64::wrapping_mul"
        | "Text::of_nat"
        | "Nat::of_u64"
        | "U64::of_nat"
        | "Float::of_i64"
        | "I64::of_float"
        | "Float::of_text"
        | "Text::of_float"
        | "Float::bits"
        | "Float::of_bits"
        | "Float::is_nan"
        | "Float::abs"
        | "Float::floor"
        | "Float::ceil"
        | "Float::trunc"
        | "Float::round"
        | "Float::sqrt"
        | "Float::cbrt"
        | "Float::exp"
        | "Float::ln"
        | "Float::log2"
        | "Float::log10"
        | "Float::pow"
        | "Float::sin"
        | "Float::cos"
        | "Float::tan"
        | "Float::asin"
        | "Float::acos"
        | "Float::atan"
        | "Float::atan2"
        | "Float::sinh"
        | "Float::cosh"
        | "Float::tanh"
        | "secret"
        | "expose" => Flatten,
        // `Float32`'s functions (`std/prelude/num.taut`).
        n if n.starts_with("Float32::") || n == "Float::of_float32" => Flatten,
        // The secret words (`std/builtin/secret.taut`).
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
    /// `dst ⊇` field `f` of each record in `src`, and every other atom of it.
    projections: Vec<(Node, Node, String)>,
    /// `dst ⊇ src` with every record replaced by everything it holds.
    flattens: Vec<(Node, Node)>,
    /// `dst ∋ Part(c)` for each storage or place `c` in `src`, and the
    /// flattened rest of it.
    parts: Vec<(Node, Node)>,
    /// The projections and flattenings made, so the solver adds each once.
    made: HashSet<(Node, Node, Option<String>)>,
    recs: Vec<RecInfo>,
    cells: Vec<CellInfo>,
    lams: Vec<LamInfo>,
    unknowns: Vec<(String, Span)>,
    /// The values performed at each effect's operation, and what resumes it.
    effect_args: HashMap<Name, Vec<Node>>,
    effect_resume: HashMap<Name, Node>,
    globals: HashMap<Name, usize>,
    methods: HashMap<Name, Vec<usize>>,
    bindings: Vec<Binding>,
    frames: Vec<Frame>,
    /// The frames being built, innermost last: every value made and every
    /// name bound flows into the last.
    scopes: Vec<Node>,
    /// Calls whose row has no effect a handler captures a continuation of: their
    /// frames are not on the stack of any continuation (`lean/Proto/Nib/KeptFrames.lean`).
    settled_calls: HashSet<crate::surface::TermId>,
    /// What made each closure or continuation, for the path of a cycle.
    lam_sites: HashMap<usize, (&'static str, Span)>,
    next_lam_site: Option<(&'static str, Span)>,
    /// Nodes of the global function declarations by name.
    lam_names: Vec<String>,
    hosts: HashMap<Name, usize>,
    /// Functions an `extern` block declares that the checker does not know.
    host_fns: HashSet<Name>,
    /// The generic global functions, analysed afresh at each direct call.
    generic_fns: HashMap<Name, Rc<FnDecl>>,
    /// The generic functions being analysed afresh now, innermost last.
    cloning: Vec<Name>,
    /// How many fresh copies have been made: past `MAX_CLONES` a call
    /// shares the one copy every other use reads.
    clones: usize,
    /// How many edges `succ` has: the solver asks after each call it reads
    /// whether any was added, and counting them again each time took most of
    /// the check of a large program.
    edges: usize,
}

const EMPTY: Node = 0;

/// The most fresh copies of generic functions one program makes.
const MAX_CLONES: usize = 4096;

impl<'a> Analysis<'a> {
    fn new(types: &'a TypeReport) -> Self {
        let mut a = Analysis {
            types,
            edges: 0,
            settled_calls: HashSet::new(),
            lam_sites: HashMap::new(),
            next_lam_site: None,
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
            projections: Vec::new(),
            flattens: Vec::new(),
            parts: Vec::new(),
            made: HashSet::new(),
            recs: Vec::new(),
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
            self.edges += 1;
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
    fn host_cell(&mut self, name: &Name, span: Span) -> usize {
        if let Some(s) = self.hosts.get(name) {
            return *s;
        }
        let (s, _) = self.cell(&format!("the host state of {name}"), span);
        self.hosts.insert(name.clone(), s);
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
        let l = self.lams.len() - 1;
        if let Some(site) = self.next_lam_site.take() {
            self.lam_sites.insert(l, site);
        }
        l
    }

    /// `src` with its records taken apart: what a value holds once its
    /// structure is not followed.
    fn flatten(&mut self, src: Node) -> Node {
        if src == EMPTY {
            return EMPTY;
        }
        let d = self.node();
        self.add_flatten(d, src);
        d
    }

    fn add_flatten(&mut self, dst: Node, src: Node) -> bool {
        if src == EMPTY || !self.made.insert((dst, src, None)) {
            return false;
        }
        self.flattens.push((dst, src));
        true
    }

    fn add_projection(&mut self, dst: Node, src: Node, field: &str) -> bool {
        if src == EMPTY || !self.made.insert((dst, src, Some(field.to_string()))) {
            return false;
        }
        self.projections.push((dst, src, field.to_string()));
        true
    }

    /// Every node a record holds.
    fn rec_nodes(&self, r: usize) -> Vec<Node> {
        let info = &self.recs[r];
        info.fields
            .iter()
            .map(|(_, n)| *n)
            .chain(info.rest)
            .collect()
    }

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

    fn ty(&self, t: &SurfaceTerm) -> Option<&Ty> {
        // The prelude's bodies are not typed here: what they hold is not
        // known, which holds.
        self.types.term(t)
    }

    fn local_ty(&self, name: &Name, at: &SurfaceTerm) -> Option<&Ty> {
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

    fn find(&self, name: &Name) -> Option<usize> {
        self.bindings.iter().rposition(|b| b.name == *name)
    }

    fn hold(&mut self, n: Node) {
        if let Some(f) = self.scopes.last().copied() {
            self.flow(n, f);
        }
    }

    fn bound_node(&mut self, bound: Bound) -> Node {
        match bound {
            Bound::Val(n) | Bound::Place(n) => n,
            Bound::Var(s) => self.atom(Atom::Cell(s)),
        }
    }

    fn bind(&mut self, name: &Name, bound: Bound) {
        let held = self.bound_node(bound);
        self.hold(held);
        let frame = self.frames.len() - 1;
        self.bindings.push(Binding {
            name: name.clone(),
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

    fn collect_fns(&mut self, stmts: &[Stmt], decls: &mut Vec<(usize, FnDecl)>) {
        for s in stmts {
            match s {
                Stmt::Fn(f) => {
                    let l = self.new_lam(f.params.len());
                    self.globals.insert(f.name.clone(), l);
                    self.lam_names.push(f.name.to_string());
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
                        self.lam_names.push(f.name.to_string());
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
            Some(TermKind::Borrow { rc: false, .. })
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
    /// `Vec(A)` is never a `Ref`, whatever it was merged with.
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
            // `#()` holds nothing.
            _ if t.is_unit() => self.join(&[]),
            // A product as a value: it holds what its members hold.
            TermKind::App { .. } if let Some(members) = t.product_value_members() => {
                let parts: Vec<Node> = members.iter().map(|m| self.eval(m, false)).collect();
                self.join(&parts)
            }
            TermKind::Var(name) => self.var(name, t, raw),
            TermKind::Declaration(_)
            | TermKind::Nat(_)
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
            TermKind::Field { base, name } => {
                let b = self.eval(base, false);
                if b == EMPTY {
                    return EMPTY;
                }
                let d = self.node();
                self.add_projection(d, b, name);
                d
            }
            TermKind::Ascribe { term: base, .. } => self.eval(base, false),
            TermKind::Record { fields, base, .. } => {
                let fields: Vec<(String, Node)> = fields
                    .iter()
                    .map(|(f, v)| (f.clone(), self.eval(v, false)))
                    .collect();
                let rest = base.as_ref().map(|b| self.eval(b, false));
                self.recs.push(RecInfo { fields, rest });
                self.atom(Atom::Rec(self.recs.len() - 1))
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
                self.next_lam_site = Some(("closure", t.span));
                self.closure(params, &vec![None; params.len()], body, false)
            }
            TermKind::BorrowLam { borrows, lam } => match &*lam.kind {
                TermKind::Lam { params, body, .. } => {
                    self.next_lam_site = Some(("closure", t.span));
                    self.closure(params, borrows, body, false)
                }
                _ => self.unknown("a borrowing closure of an unexpected shape", t.span),
            },
            TermKind::Borrow { term, .. } => self.borrow(term),
            TermKind::App {
                function,
                arguments,
            } => self.app(t, function, arguments),
            TermKind::Perform { effect, args } => {
                // A storage operation is read as the `extern` the host
                // answers it with.
                if let Some(what) = storage_operation(effect) {
                    let model = extern_model(what).expect("a storage operation's extern");
                    return self.extern_call(model, what, t, args);
                }
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

    fn effect_slots(&mut self, effect: &Name, arity: usize) -> Vec<Node> {
        if !self.effect_args.contains_key(effect) {
            self.effect_args.insert(effect.clone(), Vec::new());
        }
        while self.effect_args[effect].len() < arity {
            let n = self.node();
            self.effect_args.get_mut(effect).unwrap().push(n);
        }
        self.effect_args[effect][..arity].to_vec()
    }

    fn effect_resume_node(&mut self, effect: &Name) -> Node {
        if let Some(n) = self.effect_resume.get(effect) {
            return *n;
        }
        let n = self.node();
        self.effect_resume.insert(effect.clone(), n);
        n
    }

    fn var(&mut self, name: &Name, t: &SurfaceTerm, raw: bool) -> Node {
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
            if matches!(&*term.kind, TermKind::Field { .. }) {
                // A place inside: a field of an immutable value is that
                // field's value, and one inside a storage is a part of it.
                return match self.bindings[b].bound {
                    Bound::Val(_) => self.eval(term, false),
                    Bound::Var(s) => {
                        self.capture(b);
                        self.atom(Atom::Part(s))
                    }
                    Bound::Place(n) => {
                        self.capture(b);
                        let d = self.node();
                        self.parts.push((d, n));
                        d
                    }
                };
            }
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
            // `lower_fors` / `lower_loops` expand them where the program is read.
            Stmt::For { .. } | Stmt::Loop { .. } | Stmt::Break(_) | Stmt::Continue => EMPTY,
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
            Some(TermKind::Borrow { rc: false, .. })
        );
        self.closure_body(l, &f.params, &f.borrows, &f.body, raw);
        // `bind` is repeated by the caller with the same node; drop ours.
        self.bindings.pop();
        l
    }

    fn closure(
        &mut self,
        params: &[Name],
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
        params: &[Name],
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
            TermKind::Var(n) if self.find(n).is_none() => Some(n),
            _ => None,
        };
        let settled = self.settled_calls.contains(&t.id());
        if let Some(name) = named {
            if let Some(l) = self.clone_of(name) {
                self.args(arguments, Some(l));
                if !settled {
                    self.hold(self.lams[l].frame);
                }
                return self.lams[l].ret;
            }
            if let Some(l) = self.globals.get(name).copied() {
                let args = self.args(arguments, Some(l));
                let res = self.lams[l].ret;
                if !settled {
                    self.hold(self.lams[l].frame);
                }
                let _ = args;
                return res;
            }
            if let Some(model) = extern_model(name) {
                return self.extern_call(model, name, t, arguments);
            }
            if self.host_fns.contains(name) {
                return self.host_call(name, t, arguments);
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
            if self.types.datas.has_ctor(name) || is_operator(name) {
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
        let frame = if settled {
            self.node()
        } else {
            self.scopes.last().copied().unwrap_or(EMPTY)
        };
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
    fn clone_of(&mut self, name: &Name) -> Option<usize> {
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
        self.cloning.push(name.clone());
        self.function(l, &decl);
        self.cloning.pop();
        self.frames = frames;
        self.bindings = bindings;
        self.scopes = scopes;
        Some(l)
    }

    fn args(&mut self, arguments: &[SurfaceTerm], lam: Option<usize>) -> Vec<Node> {
        let nodes: Vec<Node> = arguments.iter().map(|a| self.eval(a, false)).collect();
        if let Some(l) = lam {
            for (a, p) in nodes.iter().zip(self.lams[l].params.clone()) {
                self.flow(*a, p);
            }
        }
        nodes
    }

    /// A call of a host function: its state holds what it is given.
    fn host_call(&mut self, name: &Name, t: &SurfaceTerm, arguments: &[SurfaceTerm]) -> Node {
        let args: Vec<Node> = arguments.iter().map(|a| self.eval(a, true)).collect();
        let h = self.host_cell(name, t.span);
        let contents = self.cells[h].contents;
        for a in &args {
            let v = self.read_through(*a);
            let v = self.flatten(v);
            self.flow(v, contents);
        }
        let handle = self.atom(Atom::Cell(h));
        let d = self.node();
        self.flow(contents, d);
        self.join(&[handle, d])
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
                let j = self.join(&parts);
                self.flatten(j)
            }
            Extern::Host => unreachable!("a host call is read by `host_call`"),
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
        // A pattern that takes the value apart binds parts of it, which
        // are not the records it is made of.
        let from = match p {
            Pattern::Bind { .. } | Pattern::Wild => from,
            _ => self.flatten(from),
        };
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
                    // The host's arms for the storage operations: each
                    // `perform` of one is read as what they answer it with.
                    if storage_operation(effect).is_some()
                        && arm.span.start >= tauto_surface_prelude_base()
                    {
                        self.bindings.truncate(mark);
                        continue;
                    }
                    let slots = self.effect_slots(effect, patterns.len());
                    for (p, s) in patterns.iter().zip(slots) {
                        self.bind_pattern(p, s, arm);
                    }
                    if let Some(k) = cont {
                        // The continuation holds the stack of the body and
                        // the handler.
                        self.next_lam_site = Some(("continuation", arm.span));
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

    fn solve(&mut self) {
        loop {
            let mut changed = false;
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
            for i in 0..self.loads.len() {
                let (dst, src) = self.loads[i];
                for a in self.pts[src].clone() {
                    match a {
                        Atom::Cell(c) | Atom::Place(c) => {
                            let contents = self.cells[c].contents;
                            for x in self.pts[contents].clone() {
                                changed |= self.pts[dst].insert(x);
                            }
                        }
                        Atom::Part(c) => {
                            changed |= self.add_flatten(dst, self.cells[c].contents);
                        }
                        _ => {}
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
                        Atom::Part(c) => {
                            changed |= self.add_flatten(dst, self.cells[c].contents);
                        }
                        other => changed |= self.pts[dst].insert(other),
                    }
                }
            }
            for i in 0..self.places.len() {
                let (dst, src) = self.places[i];
                for a in self.pts[src].clone() {
                    match a {
                        Atom::Cell(c) | Atom::Place(c) => {
                            changed |= self.pts[dst].insert(Atom::Place(c));
                        }
                        Atom::Part(c) => changed |= self.pts[dst].insert(Atom::Part(c)),
                        _ => {}
                    }
                }
            }
            for i in 0..self.parts.len() {
                let (dst, src) = self.parts[i];
                for a in self.pts[src].clone() {
                    match a {
                        Atom::Cell(c) | Atom::Place(c) | Atom::Part(c) => {
                            changed |= self.pts[dst].insert(Atom::Part(c));
                        }
                        Atom::Rec(r) => {
                            for n in self.rec_nodes(r) {
                                changed |= self.add_flatten(dst, n);
                            }
                        }
                        other => changed |= self.pts[dst].insert(other),
                    }
                }
            }
            let mut i = 0;
            while i < self.projections.len() {
                let (dst, src, field) = self.projections[i].clone();
                for a in self.pts[src].clone() {
                    match a {
                        Atom::Rec(r) => {
                            let info = &self.recs[r];
                            let found = info
                                .fields
                                .iter()
                                .find(|(f, _)| *f == field)
                                .map(|(_, n)| *n);
                            let rest = info.rest;
                            match (found, rest) {
                                (Some(n), _) => {
                                    let before = self.succ[n].len();
                                    self.flow(n, dst);
                                    changed |= self.succ[n].len() != before;
                                }
                                (None, Some(b)) => changed |= self.add_projection(dst, b, &field),
                                // A field the literal does not name: the
                                // whole record, taken apart.
                                (None, None) => {
                                    for n in self.rec_nodes(r) {
                                        changed |= self.add_flatten(dst, n);
                                    }
                                }
                            }
                        }
                        other => changed |= self.pts[dst].insert(other),
                    }
                }
                i += 1;
            }
            let mut i = 0;
            while i < self.flattens.len() {
                let (dst, src) = self.flattens[i];
                for a in self.pts[src].clone() {
                    match a {
                        Atom::Rec(r) => {
                            for n in self.rec_nodes(r) {
                                changed |= self.add_flatten(dst, n);
                            }
                        }
                        other => changed |= self.pts[dst].insert(other),
                    }
                }
                i += 1;
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
                    match a {
                        Atom::Cell(c) | Atom::Place(c) => {
                            let contents = self.cells[c].contents;
                            let before = self.succ[src].len();
                            self.flow(src, contents);
                            changed |= self.succ[src].len() != before;
                        }
                        // Written somewhere inside the content: its
                        // records are not the content's.
                        Atom::Part(c) => {
                            changed |= self.add_flatten(self.cells[c].contents, src);
                        }
                        _ => {}
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
                            let before = self.edges;
                            for (x, p) in args.iter().zip(self.lams[l].params.clone()) {
                                self.flow(*x, p);
                            }
                            let r = self.lams[l].ret;
                            self.flow(r, res);
                            self.flow(self.lams[l].frame, frame);
                            changed |= self.edges != before;
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

    /// The sites a content reaches through immutable values and closures.
    fn frontier(&self, contents: Node) -> (BTreeSet<usize>, Vec<usize>) {
        let mut cells = BTreeSet::new();
        let mut unknown = Vec::new();
        let mut seen_lams = BTreeSet::new();
        let mut seen_recs = BTreeSet::new();
        let mut stack: Vec<Atom> = self.pts[contents].iter().copied().collect();
        while let Some(a) = stack.pop() {
            match a {
                Atom::Cell(c) | Atom::Place(c) | Atom::Part(c) => {
                    cells.insert(c);
                }
                Atom::Rec(r) => {
                    if seen_recs.insert(r) {
                        for n in self.rec_nodes(r) {
                            stack.extend(self.pts[n].iter().copied());
                        }
                    }
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

    /// The closures and continuations through which `contents` holds `target`.
    fn held_through(&self, contents: Node, target: usize) -> Vec<usize> {
        let mut stack: Vec<(Atom, Vec<usize>)> = self.pts[contents]
            .iter()
            .map(|a| (*a, Vec::new()))
            .collect();
        let mut seen = BTreeSet::new();
        let mut seen_recs = BTreeSet::new();
        while let Some((atom, path)) = stack.pop() {
            match atom {
                Atom::Cell(c) | Atom::Place(c) | Atom::Part(c) if c == target => return path,
                Atom::Rec(r) if seen_recs.insert(r) => {
                    for n in self.rec_nodes(r) {
                        stack.extend(self.pts[n].iter().map(|a| (*a, path.clone())));
                    }
                }
                Atom::Lam(l) if seen.insert(l) => {
                    let mut next = path.clone();
                    next.push(l);
                    stack.extend(
                        self.pts[self.lams[l].env]
                            .iter()
                            .map(|a| (*a, next.clone())),
                    );
                }
                _ => {}
            }
        }
        Vec::new()
    }

    /// The shortest way from storage `start` back to itself, one step a line. A place is
    /// written `«byte N»`, which whoever knows the files replaces.
    fn cycle_path(&self, start: usize, edges: &[BTreeSet<usize>]) -> String {
        let mut parent: HashMap<usize, usize> = HashMap::new();
        let mut queue: std::collections::VecDeque<usize> = edges[start].iter().copied().collect();
        for d in edges[start].iter() {
            parent.insert(*d, start);
        }
        while let Some(c) = queue.pop_front() {
            if c == start {
                break;
            }
            for d in &edges[c] {
                if !parent.contains_key(d) {
                    parent.insert(*d, c);
                    queue.push_back(*d);
                }
            }
        }
        let mut steps = vec![start];
        let mut at = parent[&start];
        while at != start {
            steps.push(at);
            at = parent[&at];
        }
        steps.reverse();
        let mut out = String::new();
        for (i, c) in steps.iter().enumerate() {
            let next = steps[(i + 1) % steps.len()];
            let info = &self.cells[*c];
            out.push_str(&format!(
                "\n  {} «byte {}» holds",
                info.what, info.span.start
            ));
            for l in self.held_through(info.contents, next) {
                if let Some((what, span)) = self.lam_sites.get(&l) {
                    out.push_str(&format!(" {what} «byte {}» which holds", span.start));
                }
            }
            let target = &self.cells[next];
            out.push_str(&format!(" {} «byte {}»", target.what, target.span.start));
        }
        out
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
                    message: msg!(
                        "nibcheck-cycle-unchecked",
                        what = info.what.clone(),
                        why = why.clone()
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
            let path = self.cycle_path(c, &edges);
            let message = if names.len() == 1 {
                msg!("nibcheck-cycle-self", what = names[0].clone(), path = path)
            } else {
                msg!(
                    "nibcheck-cycle-among",
                    names = names.join(", "),
                    path = path
                )
            };
            out.push(CycleDiag {
                message,
                span: self.cells[component[0]].span,
            });
        }
        out.sort_by(|a, b| {
            (a.span.start, a.span.end, format!("{:?}", a.message)).cmp(&(
                b.span.start,
                b.span.end,
                format!("{:?}", b.message),
            ))
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
fn place_root(t: &SurfaceTerm) -> Option<Name> {
    match &*t.kind {
        TermKind::Var(n) => Some(n.clone()),
        TermKind::Field { base, .. } => place_root(base),
        _ => None,
    }
}

fn holds(datas: &Datas, t: &Ty, seen: &mut HashSet<Name>) -> bool {
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
        Ty::Union(ts) => ts.iter().any(|t| holds(datas, t, seen)),
        // A `&rc T` is a container that is never written: what it reaches is
        // what its contents reach.
        Ty::Tagged(_, t) | Ty::Info(t) | Ty::Borrow(t, _) | Ty::Orig(t) | Ty::Rc(t) => {
            holds(datas, t, seen)
        }
        Ty::Named(n, args) => {
            if tauto_surface::bindings::is_library(n, n.as_str())
                && matches!(
                    n.as_str(),
                    "Ref" | "Mutex" | "MutexGuard" | "Vec" | "Slots" | "Slice" | "Task" | "Pending"
                )
            {
                return true;
            }
            if tauto_surface::bindings::is_library(n, n.as_str())
                && matches!(n.as_str(), "Atomic" | "Buf" | "Bytes" | "SynDeclaration")
            {
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
        "Vec::new" => "Vec",
        "Slots::new" => "Slots",
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
    seen: &mut HashSet<Name>,
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
        Ty::Union(ts) => ts.iter().all(|t| storage_kinds(datas, t, kinds, seen)),
        Ty::Tagged(_, t) | Ty::Info(t) | Ty::Borrow(t, _) | Ty::Orig(t) | Ty::Rc(t) => {
            storage_kinds(datas, t, kinds, seen)
        }
        Ty::Named(n, args) => {
            // The storages the prelude declares, read by name as `holds`
            // reads them.
            if let Some(k) = storage_kind_of_type(n) {
                kinds.insert(k);
                return true;
            }
            if tauto_surface::bindings::is_library(n, n.as_str())
                && matches!(n.as_str(), "Atomic" | "Buf" | "Bytes" | "SynDeclaration")
            {
                return true;
            }
            if !args.iter().all(|a| storage_kinds(datas, a, kinds, seen)) {
                return false;
            }
            let Some(d) = datas.decls.get(n) else {
                return false;
            };
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

fn storage_kind_of_type(name: &Name) -> Option<&'static str> {
    if !tauto_surface::bindings::is_library(name, name.as_str()) {
        return None;
    }
    Some(match name.as_str() {
        "Ref" => "Ref",
        "Mutex" => "Mutex",
        "Vec" => "Vec",
        "Slots" => "Slots",
        _ => return None,
    })
}

/// The reference cycles a program may build, as errors.
/// The calls that cannot be on the stack when a continuation is kept: an arm that only calls its
/// `k` keeps nothing. A row that cannot be
/// read (an error, a row variable, an effect not followed) keeps the call.
fn settled_calls(program: &Program, rows: &RowReport) -> HashSet<crate::surface::TermId> {
    if !rows.errors.is_empty() {
        return HashSet::new();
    }
    let mut captured: HashSet<Name> = HashSet::new();
    let prelude = crate::types::prelude_for(program);
    for stmt in prelude.stmts.iter().chain(&program.stmts) {
        let mut stmt = stmt.clone();
        crate::surface::walk::stmt(&mut stmt, &mut |t| {
            if let TermKind::Handle { handlers, .. } = &*t.kind {
                for h in handlers {
                    if let Handler::Operation {
                        effect,
                        cont: Some(k),
                        guard,
                        body,
                        ..
                    } = h
                        && crate::lin::keeps_continuation(k, guard.as_ref(), body)
                    {
                        captured.insert(effect.clone());
                    }
                }
            }
        });
    }
    rows.calls
        .iter()
        .filter(|(_, row)| {
            row.iter()
                .all(|e| e.row_variable().is_none() && !e.starts_with('?') && !captured.contains(e))
        })
        .map(|(id, _)| *id)
        .collect()
}

/// `rows` is the caller's effect report of `program`. Whichever variant it
/// is (extraction-trusted totality, the JavaScript host) changes only `div`
/// and callback diagnostics, and neither changes which calls are settled.
pub fn check(program: &Program, types: &TypeReport, rows: &RowReport) -> Vec<CycleDiag> {
    let mut a = Analysis::new(types);
    a.settled_calls = settled_calls(program, rows);
    let mut decls = Vec::new();
    a.collect_fns(&crate::types::prelude_for(program).stmts, &mut decls);
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
    use tauto_parse::parse_program_as_written;

    fn errors(source: &str) -> Vec<String> {
        let program = parse_program_as_written(source).expect("parses");
        match check_lin_program(&program) {
            Ok(errors) => errors
                .into_iter()
                .map(|e| tauto_messages::english(&e.message))
                .collect(),
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

    const UI: &str = "struct U { tree: Ref(() -> i64), lift: () -> i64 }\nlet u := U { tree: Ref::new(() => 0), lift: () => 1 }\n";

    #[test]
    fn a_field_read_holds_only_that_field() {
        accepts(&format!("{UI}let l := u.lift\nRef::set(u.tree, () => l())"));
    }

    #[test]
    fn a_field_read_of_the_storage_is_still_a_cycle() {
        rejects(
            &format!("{UI}let t := u.tree\nRef::set(u.tree, () => Ref::get(t)())"),
            "cycle",
        );
    }

    #[test]
    fn a_closure_over_the_whole_struct_is_still_a_cycle() {
        rejects(&format!("{UI}Ref::set(u.tree, () => u.lift())"), "cycle");
    }

    #[test]
    fn a_field_of_a_struct_pattern_is_read_whole() {
        rejects(
            &format!(
                "{UI}match u {{\n  U {{ tree: t, lift: _ }} => Ref::set(u.tree, () => Ref::get(t)())\n}}"
            ),
            "cycle",
        );
    }

    #[test]
    fn a_field_of_a_nested_struct_is_followed() {
        rejects(
            &format!(
                "{UI}struct W {{ inner: U }}\nlet w := W {{ inner: u }}\nlet t := w.inner.tree\nRef::set(u.tree, () => Ref::get(t)())"
            ),
            "cycle",
        );
        accepts(&format!(
            "{UI}struct W {{ inner: U }}\nlet w := W {{ inner: u }}\nlet l := w.inner.lift\nRef::set(u.tree, () => l())"
        ));
    }

    #[test]
    fn a_write_through_a_field_place_is_read_whole() {
        rejects(
            "struct P { r: Ref(() -> i64), f: () -> i64 }\nstruct Q { p: P, g: () -> i64 }\nlet r := Ref::new(() => 0)\nvar q := Q { p: P { r: Ref::new(() => 0), f: () => 0 }, g: () => 0 }\nreplace(&mut q.p, P { r: r, f: () => 0 })\nlet s := q.p.r\nRef::set(r, () => Ref::get(s)())",
            "cycle",
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
            "let a := Ref::new(#(() => 0, 0))\nlet b := Ref::new(() => 0)\nRef::set(a, #(() => Ref::get(b)(), 1))\nRef::set(b, () => Ref::get(a).fst())",
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
            "let a := Ref::new(1)\nlet b := Ref::new(2)\nRef::set(a, Ref::get(b))\nlet n := Ref::get(a)",
        );
    }

    #[test]
    fn a_vec_in_a_ref_that_holds_a_closure_over_the_ref_is_a_cycle() {
        rejects(
            "let r := Ref::new(0)\nlet m := Mutex::new(Vec::new())\nvar g := Mutex::lock(m)\nlet v := MutexGuard::get_mut(&mut g)\nVec::push(&mut v, () => {\n  let h := Mutex::lock(m)\n  let w := MutexGuard::get(&h)\n  Vec::len(&w)\n})",
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
            "let m := Mutex::new(() => 0)\nvar g := Mutex::lock(m)\nlet f := MutexGuard::get_mut(&mut g)\nreplace(&mut f, () => {\n  let h := Mutex::lock(m)\n  let k := MutexGuard::get(&h)\n  1\n})",
            "cycle",
        );
    }

    // A program that keeps a continuation: a generator stepped from outside.
    const GEN: &str = "effect tick(n: i64): ()\nenum(affine) S { Done, More(i64, affine (()) -> S ! {}) }\nfn gen(n: i64): S ! {} {\n  handle { perform tick(n)\n perform tick(n + 1) } with {\n    return _ => Done\n    tick(x), k => More(x, k)\n  }\n}\n";

    #[test]
    fn a_continuation_kept_in_a_mutex_is_free() {
        accepts(&format!(
            "{GEN}let m := Mutex::new(gen(1))\nlet s := Mutex::take(m)\nmatch s {{ More(_, k) => Mutex::put(m, k(()))\n Done => Mutex::put(m, Done) }}"
        ));
    }

    #[test]
    fn a_continuation_whose_body_holds_its_mutex_is_a_cycle() {
        rejects(
            "effect tick(): ()\nenum(affine) S { Done, More(affine (()) -> S ! {}) }\nlet m := Mutex::new(Done)\nlet s := handle { perform tick()\n Mutex::put(m, Done) } with {\n  return _ => Done\n  tick(), k => More(k)\n}\nMutex::put(m, s)",
            "cycle",
        );
    }

    #[test]
    fn a_continuation_whose_handler_holds_its_mutex_is_a_cycle() {
        rejects(
            "effect tick(): ()\nenum(affine) S { Done, More(affine (()) -> S ! {}) }\nlet m := Mutex::new(Done)\nlet t := handle { perform tick()\n Done } with {\n  tick(), k => {\n Mutex::put(m, More(k))\n Done }\n}",
            "cycle",
        );
    }

    #[test]
    fn a_continuation_holds_the_frames_it_was_performed_in() {
        rejects(
            "effect tick(): ()\nenum(affine) S { Done, More(affine (()) -> S ! {}) }\nlet m := Mutex::new(Done)\nfn inner(q: Mutex(S)): () ! {tick} {\n  perform tick()\n  Mutex::put(q, Done)\n}\nlet s := handle { inner(m) } with {\n  return _ => Done\n  tick(), k => More(k)\n}\nMutex::put(m, s)",
            "cycle",
        );
    }

    #[test]
    fn a_continuation_holds_the_scope_of_its_handle() {
        rejects(
            "effect tick(): ()\nenum(affine) S { Done, More(affine (()) -> S ! {}) }\nlet m := Mutex::new(Done)\nlet s := handle { perform tick()\n Done } with {\n  return _ => Done\n  tick(), k => More(k)\n}\nMutex::put(m, s)",
            "cycle",
        );
    }

    #[test]
    fn reading_a_slot_of_a_vec_copies_its_content() {
        accepts(
            "fn push_at(v: &mut Vec(List(u64)), i: u64, p: u64): () {\n  match Vec::get_mut(&mut v, i) {\n    Some(slot) => {\n      *slot := Cons(p, slot)\n    }\n    None => ()\n  }\n}\nvar v: Vec(List(u64)) := Vec::new()\nVec::push(&mut v, Nil)\npush_at(&mut v, 0, 1)",
        );
    }
}
