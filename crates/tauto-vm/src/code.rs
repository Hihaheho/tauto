//! The bytecode, and the compiler that writes it from the program each
//! function's continuation-passing form (`tauto_nir::cps`), the same tree
//! the JavaScript backend prints.
//!
//! Every computation leaves exactly one value on the operand stack. A
//! function is one code; the body of a `handle` and each of its arms are
//! codes of their own that run in frames sharing the function's slots, so
//! that a continuation is the frames from the `handle`'s body up.

use std::collections::{BTreeMap, BTreeSet, HashMap};
use std::rc::Rc;

use tauto_nir::cps::{self, Cps, CpsPat, PathStep, Prim, Unary};
use tauto_nir::{Arith, Cmp, Package, Quant, Width};

use crate::value::{Step, Value};

/// A constructor: the data type that owns it and its name, and its fields'
/// names in order (`None` for a positional field).
pub struct Ctor {
    pub id: u32,
    pub owner: Rc<str>,
    pub tag: Rc<str>,
    pub names: Vec<Option<Rc<str>>>,
    pub is_struct: bool,
}

impl Ctor {
    pub fn field(&self, name: &str) -> crate::value::R<usize> {
        match self.names.iter().position(|n| n.as_deref() == Some(name)) {
            Some(i) => Ok(i),
            None => name.parse().or_else(|_| {
                crate::value::fail(format!("internal: no field {name} in {}", self.tag))
            }),
        }
    }
}

#[derive(Debug, Clone, Copy)]
pub enum Op {
    /// Pushes a constant.
    Const(u32),
    Unit,
    /// Pushes the value of a slot: through the borrow it holds with
    /// `deref`, a copy with `copy`, moving it out with `take`. An
    /// `indirect` slot holds a borrow of the local's place (a shared `var`,
    /// or a capture of a borrowing closure) and is read through.
    Load {
        slot: u32,
        deref: bool,
        take: bool,
        indirect: bool,
    },
    /// Pops the value into a slot; `shared` puts it in a cell of its own.
    Define {
        slot: u32,
        shared: bool,
    },
    /// Pops the value into the place.
    Assign {
        slot: u32,
        path: u32,
        through: bool,
        indirect: bool,
    },
    /// Pushes a borrow of the place.
    Borrow {
        slot: u32,
        path: u32,
        through: bool,
        indirect: bool,
    },
    Pop,
    Jump(u32),
    /// Pops a `Bool` and jumps when it is false.
    JumpIfNot(u32),
    /// Pops the arguments and the callee below them, and calls it.
    Call {
        argc: u32,
        ticked: bool,
    },
    /// A call of the function itself in return position: the frame is
    /// reused when it is the function's.
    TailSelf {
        inst: u32,
        argc: u32,
    },
    Builtin {
        name: u32,
        argc: u32,
    },
    Prim {
        prim: u32,
        argc: u32,
    },
    Unary(u32),
    Closure(u32),
    Perform {
        op: u32,
        quant: Q,
        argc: u32,
    },
    /// Runs the body of a `handle` in a frame of its own.
    Handle(u32),
    /// The body has its value: the arms answer nothing more.
    Unhandle,
    /// Ends the frame with the value on top.
    Ret,
    /// Ends the function with the value on top.
    Return,
    /// Matches the value on top against the pattern, binding its names;
    /// jumps when it does not fit.
    Test {
        pat: u32,
        fail: u32,
    },
    NoArm,
    /// Counts a step of the budgets in place, or of the host's limit. When
    /// a budget has run out it performs `exceeded`, whose answer the next
    /// op takes; otherwise it skips that op.
    Tick,
    /// Takes the answer of `exceeded`: more steps, or the budget's value.
    TickAnswer,
    /// Runs the body of a `budget` whose steps are on top, in a frame of its
    /// own.
    Budget(u32),
}

/// How an operation resumes.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Q {
    Zero,
    Once,
    Many,
    Direct,
}

pub struct Code {
    pub ops: Vec<Op>,
    /// The slots of the frames of a function or closure.
    pub slots: u32,
    /// The function's parameters' slots.
    pub params: Vec<u32>,
    pub name: Rc<str>,
}

pub enum Pat {
    Wild,
    Bind {
        slot: u32,
        borrow: bool,
    },
    Literal(Value),
    Ctor {
        ctor: u32,
        fields: Vec<Pat>,
    },
    /// `#(…)` on a product: a pattern for each member, in its order.
    Product(Vec<Pat>),
}

pub struct ClosureT {
    pub code: u32,
    /// A capture: the slot outside, whether it is read through, the slot
    /// inside, and how it is taken.
    pub captures: Vec<(u32, bool, u32, Capture)>,
    /// The references it is passed: the slot inside, and the place outside.
    pub refs: Vec<(u32, u32, bool)>,
}

#[derive(Clone, Copy, PartialEq, Eq)]
pub enum Capture {
    Copy,
    Move,
    /// The closure borrows the place: it reads and writes the local itself.
    Alias,
}

/// A local of the code around that a part of a `handle` uses: its slot
/// there, whether it is read through there, and its slot in the part, which
/// holds a borrow of it.
pub type Alias = (u32, bool, u32);

pub struct ArmT {
    pub op: Rc<str>,
    pub pats: Vec<Pat>,
    pub k: Option<u32>,
    pub code: u32,
    pub aliases: Vec<Alias>,
}

pub struct BudgetT {
    pub body: u32,
    pub aliases: Vec<Alias>,
    pub memory: bool,
}

pub struct HandleT {
    pub body: u32,
    pub aliases: Vec<Alias>,
    pub arms: Vec<ArmT>,
}

pub enum PrimOp {
    Arith(Arith, Width),
    FloatArith(Arith),
    Float32Arith(Arith),
    Cmp(Cmp),
    Eq(bool),
    Construct {
        ctor: Rc<Ctor>,
        order: Vec<usize>,
    },
    Product(Vec<(usize, Option<usize>)>),
    Concat,
    TextOfInt,
    TextLen,
    TextCompare,
    Divide {
        modulo: bool,
        width: Width,
    },
    /// `syn_parse` with the parser.
    SynParse(Rc<crate::syntax::SynRt>),
}

pub enum UnaryOp {
    Not,
    Member(usize),
    Field(Step),
    Shown,
    TempRef,
    Deref,
    Inject(u32, u32),
    Remap(Option<u32>, Vec<Option<usize>>),
}

/// The compiled program.
#[derive(Default)]
pub struct Program {
    pub codes: Vec<Code>,
    pub consts: Vec<Value>,
    pub paths: Vec<Vec<Step>>,
    pub names: Vec<Rc<str>>,
    pub prims: Vec<PrimOp>,
    pub unaries: Vec<UnaryOp>,
    pub closures: Vec<ClosureT>,
    pub handles: Vec<HandleT>,
    pub budgets: Vec<BudgetT>,
    pub pats: Vec<Pat>,
    pub ctors: Vec<Rc<Ctor>>,
    ctor_ids: HashMap<(Rc<str>, Rc<str>), u32>,
    /// The runtime syntax parsers, by name, hash and result type.
    parsers: Vec<(String, String, tauto_nir::Ty, Rc<crate::syntax::SynRt>)>,
    /// The code of each function instance.
    pub fns: Vec<u32>,
    pub top: Option<u32>,
}

impl Program {
    /// The constructor `tag` of `owner`, with its fields' names.
    pub fn ctor(
        &mut self,
        owner: &str,
        tag: &str,
        names: &[Option<&str>],
        is_struct: bool,
    ) -> Rc<Ctor> {
        let key: (Rc<str>, Rc<str>) = (Rc::from(owner), Rc::from(tag));
        if let Some(&id) = self.ctor_ids.get(&key) {
            return self.ctors[id as usize].clone();
        }
        let id = self.ctors.len() as u32;
        let ctor = Rc::new(Ctor {
            id,
            owner: key.0.clone(),
            tag: key.1.clone(),
            names: names.iter().map(|n| n.map(Rc::from)).collect(),
            is_struct,
        });
        self.ctors.push(ctor.clone());
        self.ctor_ids.insert(key, id);
        ctor
    }

    fn ctor_id(&mut self, owner: &str, tag: &str) -> u32 {
        let key: (Rc<str>, Rc<str>) = (Rc::from(owner), Rc::from(tag));
        if let Some(&id) = self.ctor_ids.get(&key) {
            return id;
        }
        // Matched before any value of it is made: its names come later.
        self.ctor(owner, tag, &[], false).id
    }

    fn name(&mut self, n: &str) -> u32 {
        if let Some(i) = self.names.iter().position(|m| &**m == n) {
            return i as u32;
        }
        self.names.push(Rc::from(n));
        (self.names.len() - 1) as u32
    }
}

type Rs<T> = Result<T, String>;

/// Compiles the package's functions.
pub fn compile(pkg: &Package) -> Rs<Program> {
    if !pkg.externs.is_empty() {
        return Err("extern functions (the machine has no host bindings)".into());
    }
    let mut p = Program::default();
    // The prelude's data types, so that the builtins make the values the
    // program matches.
    p.ctor("Option", "Some", &[None], false);
    p.ctor("Option", "None", &[], false);
    p.ctor("Result", "Ok", &[None], false);
    p.ctor("Result", "Err", &[None], false);
    p.ctor("Pair", "Pair", &[Some("fst"), Some("snd")], true);
    p.ctor("List", "Cons", &[None, None], false);
    p.ctor("List", "Nil", &[], false);
    for d in &pkg.datas {
        for c in &d.ctors {
            let names: Vec<Option<&str>> = c.fields.iter().map(|f| f.name.as_deref()).collect();
            p.ctor(&d.name, &c.name, &names, d.is_struct);
        }
    }
    for sp in &pkg.syntax_parsers {
        let rt = crate::syntax::prepare(&mut p, pkg, sp)?;
        p.parsers.push((
            sp.name.clone(),
            sp.sha.clone(),
            sp.result.clone(),
            Rc::new(rt),
        ));
    }
    // A function's code is its instance's index; closures and the parts of
    // `handle`s come after.
    for f in &pkg.fns {
        p.codes.push(Code {
            ops: Vec::new(),
            slots: 0,
            params: Vec::new(),
            name: Rc::from(f.source.as_str()),
        });
    }
    for f in &pkg.fns {
        let body = cps::lower(pkg, f, true).map_err(|e| format!("{}: {e}", f.source))?;
        let mut root = Level::default();
        let params: Vec<u32> = f.params.iter().map(|q| root.own(q.local.id)).collect();
        let mut levels = vec![root];
        let mut c = Compiler {
            p: &mut p,
            levels: &mut levels,
            ops: Vec::new(),
        };
        c.expr(&body)?;
        c.ops.push(Op::Ret);
        let ops = std::mem::take(&mut c.ops);
        let code = &mut p.codes[f.id];
        code.ops = ops;
        code.slots = levels[0].slots.len() as u32;
        code.params = params;
        p.fns.push(f.id as u32);
    }
    p.top = pkg.top.map(|t| t as u32);
    Ok(p)
}

/// The slots of a function, a closure, or a part of a `handle`.
#[derive(Default)]
struct Level {
    slots: BTreeMap<u32, u32>,
    /// The locals read through the borrow their slot holds.
    indirect: BTreeSet<u32>,
    /// A part of a `handle`: it borrows the locals of the code around it
    /// that it uses (`aliases`).
    part: bool,
    aliases: Vec<Alias>,
}

impl Level {
    /// A local of this level.
    fn own(&mut self, id: u32) -> u32 {
        let n = self.slots.len() as u32;
        *self.slots.entry(id).or_insert(n)
    }
}

/// The slot of `id` at `levels[at]`: its own, or, in a part, a borrow of
/// the code around's.
fn resolve(levels: &mut [Level], at: usize, id: u32) -> Option<(u32, bool)> {
    if let Some(&s) = levels[at].slots.get(&id) {
        return Some((s, levels[at].indirect.contains(&id)));
    }
    if !levels[at].part || at == 0 {
        return None;
    }
    let (outer, outer_indirect) = resolve(levels, at - 1, id)?;
    let l = &mut levels[at];
    let s = l.own(id);
    l.indirect.insert(id);
    l.aliases.push((outer, outer_indirect, s));
    Some((s, true))
}

struct Compiler<'a> {
    p: &'a mut Program,
    levels: &'a mut Vec<Level>,
    ops: Vec<Op>,
}

fn quant(q: Quant) -> Q {
    match q {
        Quant::Zero => Q::Zero,
        Quant::AtMostOne | Quant::One => Q::Once,
        Quant::Many => Q::Many,
        Quant::Direct => Q::Direct,
    }
}

impl Compiler<'_> {
    /// The slot of a local the code reads or writes, and whether it is
    /// read through.
    fn slot(&mut self, id: u32) -> (u32, bool) {
        let at = self.levels.len() - 1;
        match resolve(self.levels, at, id) {
            Some(s) => s,
            None => (self.levels[at].own(id), false),
        }
    }

    /// The slot of a local the code binds.
    fn own(&mut self, id: u32) -> u32 {
        self.levels.last_mut().unwrap().own(id)
    }

    fn here(&self) -> u32 {
        self.ops.len() as u32
    }

    fn patch(&mut self, at: u32) {
        let to = self.here();
        match &mut self.ops[at as usize] {
            Op::Jump(t) | Op::JumpIfNot(t) => *t = to,
            Op::Test { fail, .. } => *fail = to,
            _ => unreachable!(),
        }
    }

    fn konst(&mut self, v: Value) {
        self.p.consts.push(v);
        self.ops.push(Op::Const((self.p.consts.len() - 1) as u32));
    }

    fn value(&mut self, v: &cps::Value) {
        match v {
            cps::Value::Unit => self.ops.push(Op::Unit),
            cps::Value::Int(n) => self.konst(Value::Int(*n)),
            cps::Value::Float(x) => self.konst(Value::Float(*x)),
            cps::Value::Bool(b) => self.konst(Value::Bool(*b)),
            cps::Value::Text(t) => self.konst(Value::text(t)),
            cps::Value::Fn(i) => self.konst(Value::Fn(*i as u32)),
        }
    }

    fn path(&mut self, path: &[PathStep]) -> u32 {
        let steps = path
            .iter()
            .map(|s| match s {
                PathStep::Name(n) => Step::Name(Rc::from(n.as_str())),
                PathStep::Index(i) => Step::Index(*i),
            })
            .collect();
        self.p.paths.push(steps);
        (self.p.paths.len() - 1) as u32
    }

    fn all(&mut self, es: &[Cps]) -> Rs<u32> {
        for e in es {
            self.expr(e)?;
        }
        Ok(es.len() as u32)
    }

    fn unary(&mut self, u: UnaryOp) {
        self.p.unaries.push(u);
        self.ops.push(Op::Unary((self.p.unaries.len() - 1) as u32));
    }

    fn expr(&mut self, e: &Cps) -> Rs<()> {
        match e {
            Cps::Pure(v) => self.value(v),
            Cps::ReadLocal {
                id, deref, take, ..
            } => {
                let (slot, indirect) = self.slot(*id);
                self.ops.push(Op::Load {
                    slot,
                    deref: *deref,
                    take: *take,
                    indirect,
                });
            }
            Cps::Call {
                callee,
                args,
                ticked,
            } => {
                self.expr(callee)?;
                let argc = self.all(args)?;
                if *ticked {
                    self.ops.push(Op::Tick);
                    self.ops.push(Op::TickAnswer);
                }
                self.ops.push(Op::Call {
                    argc,
                    ticked: false,
                });
            }
            Cps::TailSelfCall { inst, args } => {
                self.konst(Value::Fn(*inst as u32));
                let argc = self.all(args)?;
                self.ops.push(Op::TailSelf {
                    inst: *inst as u32,
                    argc,
                });
            }
            Cps::External { name, .. } => return Err(format!("the extern {name}")),
            Cps::Builtin { name, args } => {
                if !crate::builtins::NAMES.contains(&name.as_str())
                    && !crate::hostcall::NAMES.contains(&name.as_str())
                {
                    return Err(format!("the builtin {name}"));
                }
                let argc = self.all(args)?;
                let name = self.p.name(name);
                self.ops.push(Op::Builtin { name, argc });
            }
            Cps::Prim { op, args } => {
                let prim = match op {
                    Prim::Arith(a, w) => PrimOp::Arith(*a, *w),
                    Prim::FloatArith(a) => PrimOp::FloatArith(*a),
                    Prim::Float32Arith(a) => PrimOp::Float32Arith(*a),
                    Prim::Cmp(c) => PrimOp::Cmp(*c),
                    Prim::Eq { negate } => PrimOp::Eq(*negate),
                    Prim::Construct {
                        ctor,
                        names,
                        order,
                        is_struct,
                        data,
                    } => {
                        let names: Vec<Option<&str>> =
                            order.iter().map(|i| names[*i].as_deref()).collect();
                        let ctor = self.p.ctor(data, ctor, &names, *is_struct);
                        // A constructor matched before it was made has its
                        // names now.
                        if ctor.names.len() != names.len() {
                            let id = ctor.id as usize;
                            let fixed = Rc::new(Ctor {
                                id: ctor.id,
                                owner: ctor.owner.clone(),
                                tag: ctor.tag.clone(),
                                names: names.iter().map(|n| n.map(Rc::from)).collect(),
                                is_struct: *is_struct,
                            });
                            self.p.ctors[id] = fixed.clone();
                            PrimOp::Construct {
                                ctor: fixed,
                                order: order.clone(),
                            }
                        } else {
                            PrimOp::Construct {
                                ctor,
                                order: order.clone(),
                            }
                        }
                    }
                    Prim::Product { picks } => PrimOp::Product(picks.clone()),
                    Prim::Concat => PrimOp::Concat,
                    Prim::TextOfInt => PrimOp::TextOfInt,
                    Prim::TextLen => PrimOp::TextLen,
                    Prim::TextCompare => PrimOp::TextCompare,
                    Prim::Divide { name, width } => PrimOp::Divide {
                        modulo: name == "mod",
                        width: *width,
                    },
                    Prim::SynParse { name, sha, ty } => PrimOp::SynParse(
                        self.p
                            .parsers
                            .iter()
                            .find(|(n, s, t, _)| n == name && s == sha && t == ty)
                            .map(|(.., rt)| rt.clone())
                            .ok_or("a runtime syntax parser without its tables")?,
                    ),
                };
                let argc = self.all(args)?;
                self.p.prims.push(prim);
                self.ops.push(Op::Prim {
                    prim: (self.p.prims.len() - 1) as u32,
                    argc,
                });
            }
            Cps::Map { value, op } => {
                self.expr(value)?;
                let u = match op {
                    Unary::Not => UnaryOp::Not,
                    Unary::Member(i) => UnaryOp::Member(*i),
                    Unary::Field { name, index } => UnaryOp::Field(match index {
                        Some(i) => Step::Index(*i),
                        None => Step::Name(Rc::from(name.as_str())),
                    }),
                    Unary::Shown => UnaryOp::Shown,
                    Unary::TempRef { .. } => UnaryOp::TempRef,
                    Unary::Deref { .. } => UnaryOp::Deref,
                    Unary::Inject { union, variant } => {
                        UnaryOp::Inject(*union as u32, *variant as u32)
                    }
                    Unary::Remap { to, table } => {
                        UnaryOp::Remap(to.map(|t| t as u32), table.clone())
                    }
                };
                self.unary(u);
            }
            Cps::Branch {
                cond,
                then,
                otherwise,
            } => {
                self.expr(cond)?;
                let jump = self.here();
                self.ops.push(Op::JumpIfNot(0));
                self.expr(then)?;
                let end = self.here();
                self.ops.push(Op::Jump(0));
                self.patch(jump);
                self.expr(otherwise)?;
                self.patch(end);
            }
            Cps::Sequence(es) => {
                if es.is_empty() {
                    self.ops.push(Op::Unit);
                }
                for (i, e) in es.iter().enumerate() {
                    if i > 0 {
                        self.ops.push(Op::Pop);
                    }
                    self.expr(e)?;
                }
            }
            Cps::Define {
                id, shared, init, ..
            } => {
                self.expr(init)?;
                let slot = self.own(*id);
                let level = self.levels.last_mut().unwrap();
                if *shared {
                    level.indirect.insert(*id);
                } else {
                    level.indirect.remove(id);
                }
                self.ops.push(Op::Define {
                    slot,
                    shared: *shared,
                });
                self.ops.push(Op::Unit);
            }
            Cps::Assign {
                id,
                path,
                value,
                through_borrow,
            } => {
                self.expr(value)?;
                let (slot, indirect) = self.slot(*id);
                let path = self.path(path);
                self.ops.push(Op::Assign {
                    slot,
                    path,
                    through: *through_borrow,
                    indirect,
                });
                self.ops.push(Op::Unit);
            }
            Cps::While { cond, body, ticked } => {
                let top = self.here();
                self.expr(cond)?;
                let exit = self.here();
                self.ops.push(Op::JumpIfNot(0));
                if *ticked {
                    self.ops.push(Op::Tick);
                    self.ops.push(Op::TickAnswer);
                }
                self.expr(body)?;
                self.ops.push(Op::Pop);
                self.ops.push(Op::Jump(top));
                self.patch(exit);
                self.ops.push(Op::Unit);
            }
            Cps::Return(v) => {
                self.expr(v)?;
                self.ops.push(Op::Return);
            }
            Cps::Match { scrut, arms } => {
                self.expr(scrut)?;
                self.arms(arms)?;
            }
            Cps::Closure(c) => self.closure(c)?,
            Cps::Perform { op, quant: q, args } => {
                let argc = self.all(args)?;
                let op = self.p.name(op);
                self.ops.push(Op::Perform {
                    op,
                    quant: quant(*q),
                    argc,
                });
            }
            Cps::Handle { body, arms, ret } => self.handle(body, arms, ret.as_deref())?,
            Cps::BorrowPlace {
                id,
                path,
                through_borrow,
            } => {
                let (slot, indirect) = self.slot(*id);
                let path = self.path(path);
                self.ops.push(Op::Borrow {
                    slot,
                    path,
                    through: *through_borrow,
                    indirect,
                });
            }
            Cps::Budget {
                memory,
                steps,
                body,
                ..
            } => {
                self.expr(steps)?;
                let (body, aliases) = self.part(|_| Ok(()), |c| c.expr(body))?;
                self.p.budgets.push(BudgetT {
                    body,
                    aliases,
                    memory: *memory,
                });
                self.ops.push(Op::Budget((self.p.budgets.len() - 1) as u32));
            }
        }
        Ok(())
    }

    /// The arms of a `match` whose scrutinee is on top.
    fn arms(&mut self, arms: &[cps::MatchArm]) -> Rs<()> {
        let mut ends = Vec::new();
        for arm in arms {
            let pat = self.pat(&arm.pat);
            let test = self.here();
            self.ops.push(Op::Test { pat, fail: 0 });
            let guard = if arm.guard == Cps::Pure(cps::Value::Bool(true)) {
                None
            } else {
                self.expr(&arm.guard)?;
                let at = self.here();
                self.ops.push(Op::JumpIfNot(0));
                Some(at)
            };
            self.ops.push(Op::Pop);
            self.expr(&arm.body)?;
            ends.push(self.here());
            self.ops.push(Op::Jump(0));
            self.patch(test);
            if let Some(g) = guard {
                // A guard that fails goes on with the next arm; the
                // scrutinee is still on the stack.
                let to = self.here();
                if let Op::JumpIfNot(t) = &mut self.ops[g as usize] {
                    *t = to;
                }
                if let Op::Test { fail, .. } = &mut self.ops[test as usize] {
                    *fail = to;
                }
            }
        }
        self.ops.push(Op::NoArm);
        for e in ends {
            self.patch(e);
        }
        Ok(())
    }

    fn pat(&mut self, p: &CpsPat) -> u32 {
        let pat = self.pat_of(p);
        self.p.pats.push(pat);
        (self.p.pats.len() - 1) as u32
    }

    fn pat_of(&mut self, p: &CpsPat) -> Pat {
        match p {
            CpsPat::Wild => Pat::Wild,
            CpsPat::Bind { id, borrow, .. } => Pat::Bind {
                slot: self.own(*id),
                borrow: *borrow,
            },
            CpsPat::Literal(v) => Pat::Literal(match v {
                cps::Value::Unit => Value::Unit,
                cps::Value::Int(n) => Value::Int(*n),
                cps::Value::Float(x) => Value::Float(*x),
                cps::Value::Bool(b) => Value::Bool(*b),
                cps::Value::Text(t) => Value::text(t),
                cps::Value::Fn(i) => Value::Fn(*i as u32),
            }),
            CpsPat::Product(fields) => {
                Pat::Product(fields.iter().map(|f| self.pat_of(f)).collect())
            }
            CpsPat::Ctor { ctor, fields, data } => Pat::Ctor {
                ctor: self.p.ctor_id(data, ctor),
                fields: fields.iter().map(|f| self.pat_of(f)).collect(),
            },
        }
    }

    /// A new code with slots of its own, borrowing the locals around it
    /// that it uses: the body or an arm of a `handle`. `bind` names the
    /// locals it binds first.
    fn part(
        &mut self,
        bind: impl FnOnce(&mut Compiler) -> Rs<()>,
        f: impl FnOnce(&mut Compiler) -> Rs<()>,
    ) -> Rs<(u32, Vec<Alias>)> {
        let id = self.p.codes.len() as u32;
        self.p.codes.push(Code {
            ops: Vec::new(),
            slots: 0,
            params: Vec::new(),
            name: Rc::from("handle"),
        });
        self.levels.push(Level {
            part: true,
            ..Level::default()
        });
        let mut c = Compiler {
            p: self.p,
            levels: self.levels,
            ops: Vec::new(),
        };
        let done = bind(&mut c).and_then(|()| f(&mut c));
        let mut ops = c.ops;
        let level = self.levels.pop().unwrap();
        done?;
        ops.push(Op::Ret);
        let code = &mut self.p.codes[id as usize];
        code.ops = ops;
        code.slots = level.slots.len() as u32;
        Ok((id, level.aliases))
    }

    fn handle(
        &mut self,
        body: &Cps,
        arms: &[cps::HandlerArm],
        ret: Option<&cps::MatchArm>,
    ) -> Rs<()> {
        let (body, aliases) = self.part(
            |_| Ok(()),
            |c| {
                c.expr(body)?;
                c.ops.push(Op::Unhandle);
                if let Some(ret) = ret {
                    c.arms(std::slice::from_ref(ret))?;
                }
                Ok(())
            },
        )?;
        let mut out = Vec::new();
        for arm in arms {
            if arm.guard != Cps::Pure(cps::Value::Bool(true)) {
                return Err("a guard on a handler arm".into());
            }
            let mut pats = Vec::new();
            let mut k = None;
            let (code, aliases) = self.part(
                |c| {
                    pats = arm.pats.iter().map(|p| c.pat_of(p)).collect();
                    k = arm.k.map(|id| c.own(id));
                    Ok(())
                },
                |c| c.expr(&arm.body),
            )?;
            out.push(ArmT {
                op: Rc::from(arm.op.as_str()),
                pats,
                k,
                code,
                aliases,
            });
        }
        self.p.handles.push(HandleT {
            body,
            aliases,
            arms: out,
        });
        self.ops.push(Op::Handle((self.p.handles.len() - 1) as u32));
        Ok(())
    }

    fn closure(&mut self, c: &cps::Closure) -> Rs<()> {
        let mut inner = Level::default();
        let params: Vec<u32> = c.params.iter().map(|id| inner.own(*id)).collect();
        let mut captures = Vec::new();
        for id in &c.captures {
            let Some((outer, outer_indirect)) = self.find(*id) else {
                continue;
            };
            let slot = inner.own(*id);
            let how = if c.borrowed {
                Capture::Alias
            } else if c.moves.contains(id) {
                Capture::Move
            } else {
                Capture::Copy
            };
            if outer_indirect || how == Capture::Alias {
                inner.indirect.insert(*id);
            }
            captures.push((outer, outer_indirect, slot, how));
        }
        let mut refs = Vec::new();
        for (inner_id, outer_id) in &c.refs {
            let Some((outer, outer_indirect)) = self.find(*outer_id) else {
                return Err("a closure reference to an unknown local".into());
            };
            refs.push((inner.own(*inner_id), outer, outer_indirect));
        }
        let id = self.p.codes.len() as u32;
        self.p.codes.push(Code {
            ops: Vec::new(),
            slots: 0,
            params: Vec::new(),
            name: Rc::from("closure"),
        });
        self.levels.push(inner);
        let mut k = Compiler {
            p: self.p,
            levels: self.levels,
            ops: Vec::new(),
        };
        let done = k.expr(&c.body);
        let mut ops = k.ops;
        let inner = self.levels.pop().unwrap();
        done?;
        ops.push(Op::Ret);
        let code = &mut self.p.codes[id as usize];
        code.ops = ops;
        code.slots = inner.slots.len() as u32;
        code.params = params;
        self.p.closures.push(ClosureT {
            code: id,
            captures,
            refs,
        });
        self.ops
            .push(Op::Closure((self.p.closures.len() - 1) as u32));
        Ok(())
    }

    /// The slot of a local of the code around, if it has one.
    fn find(&mut self, id: u32) -> Option<(u32, bool)> {
        let at = self.levels.len() - 1;
        resolve(self.levels, at, id)
    }
}
