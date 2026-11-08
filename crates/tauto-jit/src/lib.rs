//! Native code, generated with Cranelift, for the functions of a checked
//! program that the bytecode machine may run without its own bytecode
//! (`docs/design/jit.md`).
//!
//! A function has native code when it is of the S tier, has no generics,
//! and holds only fixed-width integers, `Bool` and `Unit` in plain locals:
//! arithmetic, comparisons, `if`, blocks, `while`, `return` and calls of
//! other such functions. Everything else stays in the machine.
//!
//! Native code counts steps of the host's limit where the machine does
//! (before a call marked `tick`, at each turn of a ticked `while`) and ends
//! with the machine's errors. A run that goes deeper than `MAX_DEPTH`
//! calls starts again on a thread with a stack of `DEEP_STACK` bytes; one that
//! goes deeper than that stack holds
//! calls gives up, and the machine runs the call again itself: the code has
//! no effect, so the second run is the first one.
//!
//! Generating and calling machine code needs `unsafe`; this crate is where
//! it stays.

use std::collections::{BTreeSet, HashMap};
use std::rc::Rc;

use cranelift_codegen::ir::{
    self, AbiParam, Block as CBlock, InstBuilder, MemFlagsData, StackSlotData, StackSlotKind,
    UserFuncName, Value as CValue, condcodes::IntCC, types,
};
use cranelift_codegen::settings::{self, Configurable};
use cranelift_frontend::{FunctionBuilder, FunctionBuilderContext, Variable};
use cranelift_jit::{JITBuilder, JITModule};
use cranelift_module::{FuncId, Linkage, Module, default_libcall_names};
use tauto_nir::{
    Arith, Block, Callee, Cmp, Expr, ExprKind, FnInst, InstId, Package, Repr, Stmt, Tick, Tier, Ty,
    Use, Width,
};
use tauto_vm::Value;
use tauto_vm::native::{Answer, Native};

const OK: i64 = 0;
const STEP_LIMIT: i64 = 1;
const TOO_LARGE: i64 = 2;
const DIVISION_BY_ZERO: i64 = 3;
const TOO_DEEP: i64 = 4;

/// How many native calls may be in progress at once.
pub const MAX_DEPTH: i64 = 10_000;

/// The stack of the thread a run that went deeper than `MAX_DEPTH` starts
/// again on, and how many calls it holds.
pub const DEEP_STACK: usize = 4 << 30;
const DEEP_DEPTH: i64 = (DEEP_STACK / 512) as i64;

/// How a value of a type is held in native code.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Rep {
    /// In an `i64`; a `U64` as its bits.
    Int(Width),
    /// `0` or `1` in an `i8`.
    Bool,
    Unit,
}

fn rep(t: &Ty) -> Option<Rep> {
    match t {
        Ty::Int(w) if *w != Width::Nat => Some(Rep::Int(*w)),
        Ty::Bool => Some(Rep::Bool),
        Ty::Unit | Ty::Never => Some(Rep::Unit),
        _ => None,
    }
}

fn clif(r: Rep) -> ir::Type {
    match r {
        Rep::Int(_) => types::I64,
        Rep::Bool | Rep::Unit => types::I8,
    }
}

fn fits(n: i128, w: Width) -> bool {
    match w {
        Width::U64 => u64::try_from(n).is_ok(),
        _ => i64::try_from(n).is_ok(),
    }
}

// ---------------------------------------------------------------------
// Which functions get native code.

fn ok_fn(f: &FnInst, set: &BTreeSet<InstId>) -> bool {
    f.tier == Tier::S
        && f.generics.is_empty()
        && rep(&f.ret).is_some()
        && f.params.iter().all(|p| {
            p.local.repr == Repr::Plain
                && rep(&p.ty).is_some_and(|r| r != Rep::Unit || p.ty == Ty::Unit)
        })
        && ok_expr(&f.body, set)
}

fn ok_block(b: &Block, set: &BTreeSet<InstId>) -> bool {
    b.stmts.iter().all(|s| match s {
        Stmt::Let {
            local, ty, init, ..
        }
        | Stmt::Var {
            local, ty, init, ..
        } => local.repr == Repr::Plain && rep(ty).is_some() && ok_expr(init, set),
        Stmt::Assign { target, value, .. } => {
            target.path.is_empty() && target.local.repr == Repr::Plain && ok_expr(value, set)
        }
        Stmt::Expr(e) => ok_expr(e, set),
        Stmt::While {
            cond, body, tick, ..
        } => *tick != Tick::Budget && ok_expr(cond, set) && ok_block(body, set),
        Stmt::Return { value, .. } => value.as_ref().is_none_or(|e| ok_expr(e, set)),
    }) && b.tail.as_ref().is_none_or(|e| ok_expr(e, set))
}

fn ok_expr(e: &Expr, set: &BTreeSet<InstId>) -> bool {
    let Some(r) = rep(&e.ty) else {
        return false;
    };
    let all = |xs: &[Expr]| xs.iter().all(|x| ok_expr(x, set));
    match &e.kind {
        ExprKind::Unit | ExprKind::Bool(_) => true,
        ExprKind::Int(n) => matches!(r, Rep::Int(w) if fits(*n, w)),
        ExprKind::Read { local, how } => {
            local.repr == Repr::Plain && matches!(how, Use::Move | Use::Copy)
        }
        ExprKind::Call(c) => {
            c.targs.is_empty()
                && c.tick != Tick::Budget
                && all(&c.args)
                && match &c.callee {
                    Callee::Inst(i) => c.tier == Tier::S && set.contains(i),
                    Callee::Builtin(name) => {
                        (name == "div" || name == "mod")
                            && c.args.len() == 2
                            && matches!(r, Rep::Int(_))
                    }
                    _ => false,
                }
        }
        ExprKind::Arith { op, args, width } => {
            *op != Arith::Div && *width != Width::Nat && all(args)
        }
        ExprKind::Cmp { args, .. } => {
            args.len() == 2 && matches!(rep(&args[0].ty), Some(Rep::Int(_))) && all(args)
        }
        ExprKind::Eq { args, .. } => args.len() == 2 && all(args),
        ExprKind::Not(x) => ok_expr(x, set),
        ExprKind::And(a, b) | ExprKind::Or(a, b) => ok_expr(a, set) && ok_expr(b, set),
        ExprKind::If {
            cond,
            then,
            otherwise,
        } => {
            ok_expr(cond, set)
                && ok_expr(then, set)
                && match otherwise {
                    Some(o) => ok_expr(o, set),
                    None => r == Rep::Unit,
                }
        }
        ExprKind::Block(b) => ok_block(b, set),
        _ => false,
    }
}

/// The instances that get native code: the largest set whose members call
/// only members.
fn eligible(pkg: &Package) -> BTreeSet<InstId> {
    let mut set: BTreeSet<InstId> = pkg.fns.iter().map(|f| f.id).collect();
    loop {
        let next: BTreeSet<InstId> = pkg
            .fns
            .iter()
            .filter(|f| set.contains(&f.id) && ok_fn(f, &set))
            .map(|f| f.id)
            .collect();
        if next == set {
            return set;
        }
        set = next;
    }
}

// ---------------------------------------------------------------------
// Code generation.

fn trusted(_: &mut FunctionBuilder) -> MemFlagsData {
    MemFlagsData::trusted()
}

struct Gen<'a, 'b> {
    b: FunctionBuilder<'b>,
    module: &'a mut JITModule,
    ids: &'a HashMap<InstId, FuncId>,
    vars: HashMap<u32, Variable>,
    params: Vec<Variable>,
    this: InstId,
    top: CBlock,
    fuel: CValue,
    out: CValue,
    depth: CValue,
}

impl Gen<'_, '_> {
    fn ptr(&self) -> ir::Type {
        self.module.target_config().pointer_type()
    }

    /// Ends the function with `status` when `cond` holds.
    fn fail_if(&mut self, cond: CValue, status: i64) {
        let fail = self.b.create_block();
        let go = self.b.create_block();
        self.b.ins().brif(cond, fail, &[], go, &[]);
        self.b.switch_to_block(fail);
        let s = self.b.ins().iconst(types::I32, status);
        self.b.ins().return_(&[s]);
        self.b.switch_to_block(go);
    }

    fn tick(&mut self) {
        let f = {
            let m = trusted(&mut self.b);
            self.b.ins().load(types::I64, m, self.fuel, 0)
        };
        let none = self.b.ins().icmp_imm_s(IntCC::Equal, f, 0);
        self.fail_if(none, STEP_LIMIT);
        let f = self.b.ins().iadd_imm_s(f, -1);
        {
            let m = trusted(&mut self.b);
            self.b.ins().store(m, f, self.fuel, 0);
        }
    }

    /// Ends with `TOO_LARGE` when `v` is out of the range of `w`.
    fn range(&mut self, v: CValue, w: Width) {
        let bad = match w {
            Width::W64 | Width::U64 | Width::Nat => return,
            Width::W32 => {
                let lo = self
                    .b
                    .ins()
                    .icmp_imm_s(IntCC::SignedLessThan, v, i32::MIN as i64);
                let hi = self
                    .b
                    .ins()
                    .icmp_imm_s(IntCC::SignedGreaterThan, v, i32::MAX as i64);
                self.b.ins().bor(lo, hi)
            }
            Width::U8 => self
                .b
                .ins()
                .icmp_imm_s(IntCC::UnsignedGreaterThan, v, u8::MAX as i64),
            Width::U32 => self
                .b
                .ins()
                .icmp_imm_s(IntCC::UnsignedGreaterThan, v, u32::MAX as i64),
        };
        self.fail_if(bad, TOO_LARGE);
    }

    fn neg(&mut self, x: CValue, w: Width) -> CValue {
        if w == Width::U64 {
            let bad = self.b.ins().icmp_imm_s(IntCC::NotEqual, x, 0);
            self.fail_if(bad, TOO_LARGE);
            return x;
        }
        let bad = self.b.ins().icmp_imm_s(IntCC::Equal, x, i64::MIN);
        self.fail_if(bad, TOO_LARGE);
        let r = self.b.ins().ineg(x);
        self.range(r, w);
        r
    }

    fn arith(&mut self, op: Arith, x: CValue, y: CValue, w: Width) -> CValue {
        let u = w == Width::U64;
        let (r, of) = match (op, u) {
            (Arith::Add, false) => self.b.ins().sadd_overflow(x, y),
            (Arith::Add, true) => self.b.ins().uadd_overflow(x, y),
            (Arith::Sub, false) => self.b.ins().ssub_overflow(x, y),
            (Arith::Sub, true) => self.b.ins().usub_overflow(x, y),
            (Arith::Mul, false) => self.b.ins().smul_overflow(x, y),
            (Arith::Mul, true) => self.b.ins().umul_overflow(x, y),
            _ => unreachable!("checked by ok_expr"),
        };
        self.fail_if(of, TOO_LARGE);
        self.range(r, w);
        r
    }

    /// `div` / `mod`: truncating, as the machine's `checked_div` / `checked_rem`.
    fn divide(&mut self, modulo: bool, x: CValue, y: CValue, w: Width) -> CValue {
        let zero = self.b.ins().icmp_imm_s(IntCC::Equal, y, 0);
        self.fail_if(zero, DIVISION_BY_ZERO);
        if w == Width::U64 {
            return if modulo {
                self.b.ins().urem(x, y)
            } else {
                self.b.ins().udiv(x, y)
            };
        }
        // By -1 the hardware may trap on `i64::MIN`: negate instead.
        let minus = self.b.ins().icmp_imm_s(IntCC::Equal, y, -1);
        let by_minus = self.b.create_block();
        let other = self.b.create_block();
        let join = self.b.create_block();
        self.b.append_block_param(join, types::I64);
        self.b.ins().brif(minus, by_minus, &[], other, &[]);
        self.b.switch_to_block(by_minus);
        let r = if modulo {
            self.b.ins().iconst(types::I64, 0)
        } else {
            self.neg(x, w)
        };
        self.b.ins().jump(join, &[r.into()]);
        self.b.switch_to_block(other);
        let r = if modulo {
            self.b.ins().srem(x, y)
        } else {
            self.b.ins().sdiv(x, y)
        };
        self.b.ins().jump(join, &[r.into()]);
        self.b.switch_to_block(join);
        let r = self.b.block_params(join)[0];
        self.range(r, w);
        r
    }

    fn dummy(&mut self, t: &Ty) -> CValue {
        let r = rep(t).unwrap_or(Rep::Unit);
        self.b.ins().iconst(clif(r), 0)
    }

    /// The value of `e`, or `None` when control does not come back.
    fn expr(&mut self, e: &Expr) -> Option<CValue> {
        let r = rep(&e.ty).expect("checked by ok_expr");
        Some(match &e.kind {
            ExprKind::Unit => self.b.ins().iconst(types::I8, 0),
            ExprKind::Bool(v) => self.b.ins().iconst(types::I8, *v as i64),
            ExprKind::Int(n) => self.b.ins().iconst(types::I64, *n as i64),
            ExprKind::Read { local, .. } => {
                let v = self.vars[&local.id];
                self.b.use_var(v)
            }
            ExprKind::Arith { op, args, width } => {
                let x = self.expr(&args[0])?;
                if *op == Arith::Neg {
                    self.neg(x, *width)
                } else {
                    let y = self.expr(&args[1])?;
                    self.arith(*op, x, y, *width)
                }
            }
            ExprKind::Cmp { op, args } => {
                let x = self.expr(&args[0])?;
                let y = self.expr(&args[1])?;
                let u = matches!(rep(&args[0].ty), Some(Rep::Int(Width::U64)));
                let cc = match (op, u) {
                    (Cmp::Lt, false) => IntCC::SignedLessThan,
                    (Cmp::Gt, false) => IntCC::SignedGreaterThan,
                    (Cmp::Le, false) => IntCC::SignedLessThanOrEqual,
                    (Cmp::Ge, false) => IntCC::SignedGreaterThanOrEqual,
                    (Cmp::Lt, true) => IntCC::UnsignedLessThan,
                    (Cmp::Gt, true) => IntCC::UnsignedGreaterThan,
                    (Cmp::Le, true) => IntCC::UnsignedLessThanOrEqual,
                    (Cmp::Ge, true) => IntCC::UnsignedGreaterThanOrEqual,
                };
                self.b.ins().icmp(cc, x, y)
            }
            ExprKind::Eq { negate, args } => {
                let x = self.expr(&args[0])?;
                let y = self.expr(&args[1])?;
                let cc = if *negate {
                    IntCC::NotEqual
                } else {
                    IntCC::Equal
                };
                self.b.ins().icmp(cc, x, y)
            }
            ExprKind::Not(x) => {
                let x = self.expr(x)?;
                self.b.ins().bxor_imm_s(x, 1)
            }
            ExprKind::And(a, c) | ExprKind::Or(a, c) => {
                let and = matches!(e.kind, ExprKind::And(..));
                let x = self.expr(a)?;
                let rhs = self.b.create_block();
                let join = self.b.create_block();
                self.b.append_block_param(join, types::I8);
                if and {
                    self.b.ins().brif(x, rhs, &[], join, &[x.into()]);
                } else {
                    self.b.ins().brif(x, join, &[x.into()], rhs, &[]);
                }
                self.b.switch_to_block(rhs);
                if let Some(y) = self.expr(c) {
                    self.b.ins().jump(join, &[y.into()]);
                }
                self.b.switch_to_block(join);
                self.b.block_params(join)[0]
            }
            ExprKind::If {
                cond,
                then,
                otherwise,
            } => {
                let c = self.expr(cond)?;
                let t = self.b.create_block();
                let o = self.b.create_block();
                let join = self.b.create_block();
                self.b.append_block_param(join, clif(r));
                self.b.ins().brif(c, t, &[], o, &[]);
                self.b.switch_to_block(t);
                let mut reached = false;
                if let Some(v) = self.expr(then) {
                    self.b.ins().jump(join, &[v.into()]);
                    reached = true;
                }
                self.b.switch_to_block(o);
                let v = match otherwise {
                    Some(x) => self.expr(x),
                    None => Some(self.b.ins().iconst(types::I8, 0)),
                };
                if let Some(v) = v {
                    self.b.ins().jump(join, &[v.into()]);
                    reached = true;
                }
                self.b.switch_to_block(join);
                if !reached {
                    // No predecessor: end the empty block and stop here.
                    self.b.ins().trap(ir::TrapCode::unwrap_user(1));
                    return None;
                }
                self.b.block_params(join)[0]
            }
            ExprKind::Block(b) => return self.block(b, &e.ty),
            ExprKind::Call(c) => {
                let mut args = Vec::with_capacity(c.args.len());
                for a in &c.args {
                    args.push(self.expr(a)?);
                }
                if c.tick == Tick::Host {
                    self.tick();
                }
                match &c.callee {
                    Callee::Builtin(name) => {
                        let Rep::Int(w) = r else { unreachable!() };
                        self.divide(name == "mod", args[0], args[1], w)
                    }
                    Callee::Inst(i) if c.recur && *i == self.this => {
                        for (p, a) in self.params.clone().into_iter().zip(args) {
                            self.b.def_var(p, a);
                        }
                        self.b.ins().jump(self.top, &[]);
                        return None;
                    }
                    Callee::Inst(i) => {
                        let f = self.module.declare_func_in_func(self.ids[i], self.b.func);
                        let slot = self.b.create_sized_stack_slot(StackSlotData::new(
                            StackSlotKind::ExplicitSlot,
                            8,
                            3,
                        ));
                        let ptr = self.ptr();
                        let out = self.b.ins().stack_addr(ptr, slot, 0);
                        let depth = self.b.ins().iadd_imm_s(self.depth, -1);
                        let mut all = vec![self.fuel, out, depth];
                        all.extend(args);
                        let call = self.b.ins().call(f, &all);
                        let status = self.b.inst_results(call)[0];
                        let fail = self.b.create_block();
                        let go = self.b.create_block();
                        self.b.ins().brif(status, fail, &[], go, &[]);
                        self.b.switch_to_block(fail);
                        self.b.ins().return_(&[status]);
                        self.b.switch_to_block(go);
                        let m = trusted(&mut self.b);
                        let v = self.b.ins().load(types::I64, m, out, 0);
                        match clif(r) {
                            types::I64 => v,
                            t => self.b.ins().ireduce(t, v),
                        }
                    }
                    _ => unreachable!("checked by ok_expr"),
                }
            }
            _ => unreachable!("checked by ok_expr"),
        })
    }

    fn block(&mut self, b: &Block, ty: &Ty) -> Option<CValue> {
        for s in &b.stmts {
            match s {
                Stmt::Let {
                    local, ty, init, ..
                }
                | Stmt::Var {
                    local, ty, init, ..
                } => {
                    let v = self.expr(init)?;
                    let var = self.b.declare_var(clif(rep(ty).expect("checked")));
                    self.b.def_var(var, v);
                    self.vars.insert(local.id, var);
                }
                Stmt::Assign { target, value, .. } => {
                    let v = self.expr(value)?;
                    let var = self.vars[&target.local.id];
                    self.b.def_var(var, v);
                }
                Stmt::Expr(e) => {
                    self.expr(e)?;
                }
                Stmt::While {
                    cond, body, tick, ..
                } => {
                    let head = self.b.create_block();
                    let inner = self.b.create_block();
                    let exit = self.b.create_block();
                    self.b.ins().jump(head, &[]);
                    self.b.switch_to_block(head);
                    let c = self.expr(cond)?;
                    self.b.ins().brif(c, inner, &[], exit, &[]);
                    self.b.switch_to_block(inner);
                    if *tick != Tick::None {
                        self.tick();
                    }
                    if self.block(body, &Ty::Unit).is_some() {
                        self.b.ins().jump(head, &[]);
                    }
                    self.b.switch_to_block(exit);
                }
                Stmt::Return { value, .. } => {
                    let v = match value {
                        Some(e) => self.expr(e)?,
                        None => self.b.ins().iconst(types::I8, 0),
                    };
                    self.ret(v);
                    return None;
                }
            }
        }
        match &b.tail {
            Some(e) => self.expr(e),
            None => Some(self.dummy(ty)),
        }
    }

    fn ret(&mut self, v: CValue) {
        let v = if self.b.func.dfg.value_type(v) == types::I64 {
            v
        } else {
            self.b.ins().uextend(types::I64, v)
        };
        let m = trusted(&mut self.b);
        self.b.ins().store(m, v, self.out, 0);
        let ok = self.b.ins().iconst(types::I32, OK);
        self.b.ins().return_(&[ok]);
    }
}

// ---------------------------------------------------------------------
// The machine's side.

type Entry = unsafe extern "C" fn(*const i64, *mut u64, *mut i64, i64) -> i32;

struct Compiled {
    entry: Entry,
    params: Vec<Rep>,
    ret: Rep,
}

/// The native code of a package. It keeps the code's memory alive.
pub struct Jit {
    _module: JITModule,
    fns: HashMap<u32, Compiled>,
}

/// What a run of native code ended with, as numbers: for a machine that
/// gives its arguments as numbers (`totes/vm/src/native.taut`).
#[derive(Debug, Clone, Copy)]
pub struct Run {
    /// 0 answered, 1 the steps ran out, 2 a number got too large, 3 a
    /// division by zero, 4 the machine runs the call itself.
    pub status: u64,
    /// The steps left.
    pub left: u64,
    /// The answer's magnitude and sign.
    pub mag: u64,
    pub neg: bool,
}

impl Default for Run {
    fn default() -> Self {
        Run {
            status: TOO_DEEP as u64,
            left: 0,
            mag: 0,
            neg: false,
        }
    }
}

impl Jit {
    pub fn has_fn(&self, inst: u32) -> bool {
        self.fns.contains_key(&inst)
    }

    /// What instance `inst` answers: 0 an integer, 1 a `Bool`, 2 `Unit`.
    pub fn kind(&self, inst: u32) -> u64 {
        match self.fns.get(&inst).map(|f| f.ret) {
            Some(Rep::Int(_)) => 0,
            Some(Rep::Bool) => 1,
            _ => 2,
        }
    }

    /// Runs `inst` with arguments given as sign and magnitude.
    pub fn run(&self, inst: u32, args: &[(bool, u64)], fuel: u64) -> Run {
        let Some(f) = self.fns.get(&inst) else {
            return Run::default();
        };
        if args.len() != f.params.len() {
            return Run::default();
        }
        let mut raw = Vec::with_capacity(args.len());
        for (&(neg, mag), r) in args.iter().zip(&f.params) {
            raw.push(match r {
                Rep::Int(Width::U64) if !neg => mag as i64,
                Rep::Int(_) => {
                    let n = if neg { -(mag as i128) } else { mag as i128 };
                    match i64::try_from(n) {
                        Ok(n) => n,
                        Err(_) => return Run::default(),
                    }
                }
                Rep::Bool | Rep::Unit if !neg && mag <= 1 => mag as i64,
                _ => return Run::default(),
            });
        }
        let (status, left, out) = f.raw(&raw, fuel);
        let (neg, mag) = match f.ret {
            Rep::Int(Width::U64) => (false, out as u64),
            Rep::Int(_) => (out < 0, out.unsigned_abs()),
            Rep::Bool => (false, (out != 0) as u64),
            Rep::Unit => (false, 0),
        };
        Run {
            status: status as u64,
            left,
            mag,
            neg,
        }
    }
}

impl Compiled {
    /// Runs the code: the status, the steps left and the answer's bits.
    fn raw(&self, args: &[i64], fuel: u64) -> (i64, u64, i64) {
        assert_eq!(args.len(), self.params.len());
        let entry = self.entry;
        let go = move |args: &[i64], depth: i64| {
            let mut left = fuel;
            let mut out = 0i64;
            // SAFETY: `entry` is the trampoline generated for this instance,
            // which reads `params.len()` arguments from `args` (checked
            // above), the fuel through its pointer and writes one `i64` to
            // `out`; it makes at most `depth` nested calls, which the stack
            // it runs on holds.
            let status = unsafe { entry(args.as_ptr(), &mut left, &mut out, depth) } as i64;
            (status, left, out)
        };
        let first = go(args, MAX_DEPTH);
        if first.0 != TOO_DEEP {
            return first;
        }
        let owned = args.to_vec();
        std::thread::Builder::new()
            .stack_size(DEEP_STACK)
            .spawn(move || go(&owned, DEEP_DEPTH))
            .ok()
            .and_then(|t| t.join().ok())
            .unwrap_or(first)
    }
}

impl Native for Jit {
    fn has(&self, inst: u32) -> bool {
        self.fns.contains_key(&inst)
    }

    fn call(&self, inst: u32, args: &[Value], fuel: &mut u64) -> Answer {
        let Some(f) = self.fns.get(&inst) else {
            return Answer::Fallback;
        };
        if args.len() != f.params.len() {
            return Answer::Fallback;
        }
        let mut raw = Vec::with_capacity(args.len());
        for (a, r) in args.iter().zip(&f.params) {
            raw.push(match (a, r) {
                (Value::Int(n), Rep::Int(Width::U64)) => *n as u64 as i64,
                (Value::Int(n), Rep::Int(_)) => *n as i64,
                (Value::Bool(b), Rep::Bool) => *b as i64,
                (Value::Unit, Rep::Unit) => 0,
                _ => return Answer::Fallback,
            });
        }
        let (status, left, out) = f.raw(&raw, *fuel);
        match status {
            OK => {
                *fuel = left;
                Answer::Done(match f.ret {
                    Rep::Int(Width::U64) => Value::Int(out as u64 as i128),
                    Rep::Int(_) => Value::Int(out as i128),
                    Rep::Bool => Value::Bool(out != 0),
                    Rep::Unit => Value::Unit,
                })
            }
            STEP_LIMIT => {
                *fuel = left;
                Answer::Fail(tauto_rt::messages::STEP_LIMIT)
            }
            TOO_LARGE => Answer::Fail(tauto_vm::value::TOO_LARGE),
            DIVISION_BY_ZERO => Answer::Fail(tauto_rt::messages::DIVISION_BY_ZERO),
            _ => Answer::Fallback,
        }
    }
}

/// Native code for the package's eligible functions, or `None` when there
/// is none or the host has no Cranelift backend.
pub fn compile(pkg: &Package) -> Option<Jit> {
    let set = eligible(pkg);
    if set.is_empty() {
        return None;
    }
    compile_set(pkg, &set).ok()
}

/// The instances `compile` gives native code.
pub fn native_instances(pkg: &Package) -> BTreeSet<InstId> {
    eligible(pkg)
}

fn compile_set(pkg: &Package, set: &BTreeSet<InstId>) -> Result<Jit, String> {
    let mut flags = settings::builder();
    flags
        .set("use_colocated_libcalls", "false")
        .map_err(|e| e.to_string())?;
    flags.set("is_pic", "false").map_err(|e| e.to_string())?;
    flags.set("opt_level", "speed").map_err(|e| e.to_string())?;
    let isa = cranelift_native::builder()
        .map_err(|e| e.to_string())?
        .finish(settings::Flags::new(flags))
        .map_err(|e| e.to_string())?;
    let mut module = JITModule::new(JITBuilder::with_isa(isa, default_libcall_names()));
    let ptr = module.target_config().pointer_type();

    let by_id: HashMap<InstId, &FnInst> = pkg.fns.iter().map(|f| (f.id, f)).collect();
    let mut ids = HashMap::new();
    let mut entries = HashMap::new();
    for &i in set {
        let f = by_id[&i];
        let mut sig = module.make_signature();
        sig.params.push(AbiParam::new(ptr));
        sig.params.push(AbiParam::new(ptr));
        sig.params.push(AbiParam::new(types::I64));
        for p in &f.params {
            sig.params
                .push(AbiParam::new(clif(rep(&p.ty).expect("checked"))));
        }
        sig.returns.push(AbiParam::new(types::I32));
        let id = module
            .declare_function(&format!("f{i}"), Linkage::Local, &sig)
            .map_err(|e| e.to_string())?;
        ids.insert(i, id);
        let mut esig = module.make_signature();
        for _ in 0..3 {
            esig.params.push(AbiParam::new(ptr));
        }
        esig.params.push(AbiParam::new(types::I64));
        esig.returns.push(AbiParam::new(types::I32));
        let eid = module
            .declare_function(&format!("e{i}"), Linkage::Local, &esig)
            .map_err(|e| e.to_string())?;
        entries.insert(i, (eid, esig));
    }

    let mut ctx = module.make_context();
    let mut fctx = FunctionBuilderContext::new();
    for &i in set {
        let f = by_id[&i];
        let id = ids[&i];
        ctx.func.signature = module
            .declarations()
            .get_function_decl(id)
            .signature
            .clone();
        ctx.func.name = UserFuncName::user(0, id.as_u32());
        {
            let mut b = FunctionBuilder::new(&mut ctx.func, &mut fctx);
            let entry = b.create_block();
            b.append_block_params_for_function_params(entry);
            b.switch_to_block(entry);
            let ps = b.block_params(entry).to_vec();
            let (fuel, out, depth) = (ps[0], ps[1], ps[2]);
            let top = b.create_block();
            let mut g = Gen {
                b,
                module: &mut module,
                ids: &ids,
                vars: HashMap::new(),
                params: Vec::new(),
                this: i,
                top,
                fuel,
                out,
                depth,
            };
            let deep = g.b.ins().icmp_imm_s(IntCC::SignedLessThan, depth, 0);
            g.fail_if(deep, TOO_DEEP);
            for (p, v) in f.params.iter().zip(&ps[3..]) {
                let var = g.b.declare_var(clif(rep(&p.ty).expect("checked")));
                g.b.def_var(var, *v);
                g.vars.insert(p.local.id, var);
                g.params.push(var);
            }
            g.b.ins().jump(top, &[]);
            g.b.switch_to_block(top);
            if let Some(v) = g.expr(&f.body) {
                g.ret(v);
            }
            g.b.seal_all_blocks();
            g.b.finalize(module.target_config());
        }
        module
            .define_function(id, &mut ctx)
            .map_err(|e| format!("{e:?}"))?;
        module.clear_context(&mut ctx);

        // The trampoline the machine calls: the arguments from memory.
        let (eid, esig) = &entries[&i];
        ctx.func.signature = esig.clone();
        ctx.func.name = UserFuncName::user(0, eid.as_u32());
        {
            let mut b = FunctionBuilder::new(&mut ctx.func, &mut fctx);
            let entry = b.create_block();
            b.append_block_params_for_function_params(entry);
            b.switch_to_block(entry);
            let ps = b.block_params(entry).to_vec();
            let mut all = vec![ps[1], ps[2], ps[3]];
            for (k, p) in f.params.iter().enumerate() {
                let m = trusted(&mut b);
                let v = b.ins().load(types::I64, m, ps[0], (8 * k) as i32);
                let t = clif(rep(&p.ty).expect("checked"));
                all.push(if t == types::I64 {
                    v
                } else {
                    b.ins().ireduce(t, v)
                });
            }
            let callee = module.declare_func_in_func(id, b.func);
            let call = b.ins().call(callee, &all);
            let s = b.inst_results(call)[0];
            b.ins().return_(&[s]);
            b.seal_all_blocks();
            b.finalize(module.target_config());
        }
        module
            .define_function(*eid, &mut ctx)
            .map_err(|e| format!("{e:?}"))?;
        module.clear_context(&mut ctx);
    }
    module.finalize_definitions().map_err(|e| e.to_string())?;

    let mut fns = HashMap::new();
    for &i in set {
        let f = by_id[&i];
        let code = module.get_finalized_function(entries[&i].0);
        // SAFETY: the trampoline was generated with the signature of `Entry`
        // (three pointers to an `i32`) for this target's calling convention.
        let entry: Entry = unsafe { std::mem::transmute::<*const u8, Entry>(code) };
        fns.insert(
            i as u32,
            Compiled {
                entry,
                params: f
                    .params
                    .iter()
                    .map(|p| rep(&p.ty).expect("checked"))
                    .collect(),
                ret: rep(&f.ret).expect("checked"),
            },
        );
    }
    Ok(Jit {
        _module: module,
        fns,
    })
}

/// Attaches the package's native code to `program`.
pub fn attach(program: &mut tauto_vm::Program, pkg: &Package) {
    program.native = compile(pkg).map(|j| Rc::new(j) as Rc<dyn Native>);
}
