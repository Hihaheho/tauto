//! A compiled program as bytes: what a build writes so that a run need not
//! compile the package again (`tauto-embed`). The bytes hold the program's
//! code and, for calling it from outside, its exported functions and the
//! constructors of each data type of the package.
//!
//! A program that holds what has no form here (a runtime syntax parser, a
//! declaration a macro host made, a constant other than a literal or a
//! function) cannot be written; [`Image::of`] says which.

use std::rc::Rc;

use tauto_nir::{Arith, Cmp, Name, Package, Width};

use crate::code::{
    ArmT, BudgetT, Capture, ClosureT, Code, Ctor, HandleT, Op, Pat, PrimOp, Program, Q, UnaryOp,
};
use crate::value::{Step, Value};

type Rs<T> = Result<T, String>;

/// The format's version: bytes of another version are not read.
const MAGIC: &[u8; 8] = b"TAUTOVM2";

/// A compiled program with what a caller from outside needs of it.
pub struct Image {
    pub program: Program,
    /// Each exported function's name and instance.
    pub exports: Vec<(String, u32)>,
    /// The constructors of each data type of the package, by its index in
    /// `Package::datas`: their ids in the program, when it has them.
    pub datas: Vec<Vec<Option<u32>>>,
}

impl Image {
    /// Compiles `pkg`.
    pub fn of(pkg: &Package) -> Rs<Image> {
        let program = crate::compile(pkg)?;
        let exports = pkg
            .exports
            .iter()
            .map(|e| (e.name.clone(), e.inst as u32))
            .collect();
        let datas = pkg
            .datas
            .iter()
            .map(|d| {
                d.ctors
                    .iter()
                    .map(|c| program.ctor_of(&d.name, &c.name).map(|c| c.id))
                    .collect()
            })
            .collect();
        Ok(Image {
            program,
            exports,
            datas,
        })
    }

    pub fn to_bytes(&self) -> Rs<Vec<u8>> {
        let p = &self.program;
        if !p.declarations.is_empty() {
            return Err("declarations a macro host made".into());
        }
        if !p.parsers.is_empty() {
            return Err("runtime syntax parsers".into());
        }
        let mut w = W(MAGIC.to_vec());
        w.len(self.exports.len());
        for (name, inst) in &self.exports {
            w.str(name);
            w.u(*inst as u64);
        }
        w.len(self.datas.len());
        for d in &self.datas {
            w.len(d.len());
            for c in d {
                w.opt(c.map(u64::from));
            }
        }
        w.len(p.ctors.len());
        for c in &p.ctors {
            w.name(&c.owner);
            w.name(&c.tag);
            w.len(c.names.len());
            for n in &c.names {
                match n {
                    Some(n) => {
                        w.u(1);
                        w.str(n);
                    }
                    None => w.u(0),
                }
            }
            w.bool(c.is_struct);
        }
        w.len(p.codes.len());
        for c in &p.codes {
            w.len(c.ops.len());
            for op in &c.ops {
                w.op(op);
            }
            w.u(c.slots as u64);
            w.us(&c.params);
            w.str(&c.name);
        }
        w.len(p.consts.len());
        for v in &p.consts {
            w.value(v)?;
        }
        w.len(p.paths.len());
        for path in &p.paths {
            w.len(path.len());
            for s in path {
                w.step(s);
            }
        }
        w.len(p.names.len());
        for n in &p.names {
            w.str(n);
        }
        w.len(p.prims.len());
        for prim in &p.prims {
            w.prim(prim)?;
        }
        w.len(p.unaries.len());
        for u in &p.unaries {
            w.unary(u);
        }
        w.len(p.closures.len());
        for c in &p.closures {
            w.u(c.code as u64);
            w.len(c.captures.len());
            for (outside, through, inside, how) in &c.captures {
                w.u(*outside as u64);
                w.bool(*through);
                w.u(*inside as u64);
                w.u(match how {
                    Capture::Copy => 0,
                    Capture::Move => 1,
                    Capture::Alias => 2,
                });
            }
            w.len(c.refs.len());
            for (inside, outside, b) in &c.refs {
                w.u(*inside as u64);
                w.u(*outside as u64);
                w.bool(*b);
            }
        }
        w.len(p.handles.len());
        for h in &p.handles {
            w.u(h.body as u64);
            w.aliases(&h.aliases);
            w.len(h.arms.len());
            for a in &h.arms {
                w.str(&a.op);
                w.len(a.pats.len());
                for pat in &a.pats {
                    w.pat(pat)?;
                }
                w.opt(a.k.map(u64::from));
                w.u(a.code as u64);
                w.aliases(&a.aliases);
            }
        }
        w.len(p.budgets.len());
        for b in &p.budgets {
            w.u(b.body as u64);
            w.aliases(&b.aliases);
            w.bool(b.memory);
        }
        w.len(p.pats.len());
        for pat in &p.pats {
            w.pat(pat)?;
        }
        w.us(&p.fns);
        w.opt(p.top.map(u64::from));
        w.len(p.externs.len());
        for n in &p.externs {
            w.name(n);
        }
        Ok(w.0)
    }

    pub fn from_bytes(bytes: &[u8]) -> Rs<Image> {
        let mut r = R { b: bytes, at: 0 };
        if r.take(MAGIC.len())? != MAGIC {
            return Err("not a program of this version of the machine".into());
        }
        let exports = r.many(|r| Ok((r.str()?.to_string(), r.u32()?)))?;
        let datas = r.many(|r| r.many(|r| Ok(r.opt()?.map(|n| n as u32))))?;
        let mut p = Program::default();
        let n = r.len()?;
        for id in 0..n {
            let owner = r.name()?;
            let tag = r.name()?;
            let names = r.many(|r| {
                Ok(match r.u()? {
                    0 => None,
                    _ => Some(Rc::from(r.str()?)),
                })
            })?;
            let is_struct = r.bool()?;
            p.ctors.push(Rc::new(Ctor {
                id: id as u32,
                owner,
                tag,
                names,
                is_struct,
            }));
        }
        p.codes = r.many(|r| {
            Ok(Code {
                ops: r.many(R::op)?,
                slots: r.u32()?,
                params: r.us()?,
                name: Rc::from(r.str()?),
            })
        })?;
        p.consts = r.many(R::value)?;
        p.paths = r.many(|r| r.many(R::step))?;
        p.names = r.many(|r| Ok(Rc::from(r.str()?)))?;
        let ctors = p.ctors.clone();
        p.prims = r.many(|r| r.prim(&ctors))?;
        p.unaries = r.many(R::unary)?;
        p.closures = r.many(|r| {
            Ok(ClosureT {
                code: r.u32()?,
                captures: r.many(|r| {
                    Ok((
                        r.u32()?,
                        r.bool()?,
                        r.u32()?,
                        match r.u()? {
                            0 => Capture::Copy,
                            1 => Capture::Move,
                            2 => Capture::Alias,
                            n => return Err(format!("capture {n}")),
                        },
                    ))
                })?,
                refs: r.many(|r| Ok((r.u32()?, r.u32()?, r.bool()?)))?,
            })
        })?;
        p.handles = r.many(|r| {
            Ok(HandleT {
                body: r.u32()?,
                aliases: r.aliases()?,
                arms: r.many(|r| {
                    Ok(ArmT {
                        op: Rc::from(r.str()?),
                        pats: r.many(R::pat)?,
                        k: r.opt()?.map(|n| n as u32),
                        code: r.u32()?,
                        aliases: r.aliases()?,
                    })
                })?,
            })
        })?;
        p.budgets = r.many(|r| {
            Ok(BudgetT {
                body: r.u32()?,
                aliases: r.aliases()?,
                memory: r.bool()?,
            })
        })?;
        p.pats = r.many(R::pat)?;
        p.fns = r.us()?;
        p.top = r.opt()?.map(|n| n as u32);
        p.externs = r.many(R::name)?;
        if r.at != bytes.len() {
            return Err("bytes after the program".into());
        }
        Ok(Image {
            program: p,
            exports,
            datas,
        })
    }
}

fn arith(a: Arith) -> u64 {
    match a {
        Arith::Add => 0,
        Arith::Sub => 1,
        Arith::Mul => 2,
        Arith::Neg => 3,
        Arith::Div => 4,
    }
}

fn arith_of(n: u64) -> Rs<Arith> {
    Ok(match n {
        0 => Arith::Add,
        1 => Arith::Sub,
        2 => Arith::Mul,
        3 => Arith::Neg,
        4 => Arith::Div,
        _ => return Err(format!("arith {n}")),
    })
}

fn width(w: Width) -> u64 {
    match w {
        Width::W32 => 0,
        Width::W64 => 1,
        Width::U8 => 2,
        Width::U32 => 3,
        Width::U64 => 4,
        Width::Nat => 5,
    }
}

fn width_of(n: u64) -> Rs<Width> {
    Ok(match n {
        0 => Width::W32,
        1 => Width::W64,
        2 => Width::U8,
        3 => Width::U32,
        4 => Width::U64,
        5 => Width::Nat,
        _ => return Err(format!("width {n}")),
    })
}

fn quant(q: Q) -> u64 {
    match q {
        Q::Zero => 0,
        Q::Once => 1,
        Q::Many => 2,
        Q::Direct => 3,
    }
}

fn quant_of(n: u64) -> Rs<Q> {
    Ok(match n {
        0 => Q::Zero,
        1 => Q::Once,
        2 => Q::Many,
        3 => Q::Direct,
        _ => return Err(format!("quantity {n}")),
    })
}

struct W(Vec<u8>);

impl W {
    /// LEB128.
    fn u(&mut self, mut n: u64) {
        loop {
            let b = (n & 0x7f) as u8;
            n >>= 7;
            if n == 0 {
                self.0.push(b);
                return;
            }
            self.0.push(b | 0x80);
        }
    }
    fn len(&mut self, n: usize) {
        self.u(n as u64);
    }
    fn bool(&mut self, b: bool) {
        self.u(b as u64);
    }
    fn opt(&mut self, n: Option<u64>) {
        match n {
            Some(n) => {
                self.u(1);
                self.u(n);
            }
            None => self.u(0),
        }
    }
    fn str(&mut self, s: &str) {
        self.len(s.len());
        self.0.extend_from_slice(s.as_bytes());
    }
    fn us(&mut self, v: &[u32]) {
        self.len(v.len());
        for n in v {
            self.u(*n as u64);
        }
    }
    /// A name by its spelling, and whether it is the library's: only the
    /// library's names are compared after a program is read (the builtins
    /// find the prelude's constructors by them).
    fn name(&mut self, n: &Name) {
        self.bool(tauto_nir::is_library(n, n.as_str()));
        self.str(n.as_str());
    }
    fn aliases(&mut self, a: &[(u32, bool, u32)]) {
        self.len(a.len());
        for (outside, through, inside) in a {
            self.u(*outside as u64);
            self.bool(*through);
            self.u(*inside as u64);
        }
    }
    fn value(&mut self, v: &Value) -> Rs<()> {
        match v {
            Value::Unit => self.u(0),
            Value::Bool(b) => {
                self.u(1);
                self.bool(*b);
            }
            Value::Int(n) => {
                self.u(2);
                self.0.extend_from_slice(&n.to_le_bytes());
            }
            Value::Float(x) => {
                self.u(3);
                self.0.extend_from_slice(&x.to_le_bytes());
            }
            Value::Text(t) => {
                self.u(4);
                self.str(t);
            }
            Value::Fn(i) => {
                self.u(5);
                self.u(*i as u64);
            }
            _ => return Err("a constant that is not a literal or a function".into()),
        }
        Ok(())
    }
    fn step(&mut self, s: &Step) {
        match s {
            Step::Index(i) => {
                self.u(0);
                self.len(*i);
            }
            Step::Name(n) => {
                self.u(1);
                self.str(n);
            }
            Step::Item(i) => {
                self.u(2);
                self.len(*i);
            }
            Step::Entry(i) => {
                self.u(3);
                self.len(*i);
            }
        }
    }
    fn pat(&mut self, p: &Pat) -> Rs<()> {
        match p {
            Pat::Wild => self.u(0),
            Pat::Bind { slot, borrow } => {
                self.u(1);
                self.u(*slot as u64);
                self.bool(*borrow);
            }
            Pat::Literal(v) => {
                self.u(2);
                self.value(v)?;
            }
            Pat::Ctor { ctor, fields } => {
                self.u(3);
                self.u(*ctor as u64);
                self.len(fields.len());
                for f in fields {
                    self.pat(f)?;
                }
            }
        }
        Ok(())
    }
    fn prim(&mut self, p: &PrimOp) -> Rs<()> {
        match p {
            PrimOp::Arith(a, w) => {
                self.u(0);
                self.u(arith(*a));
                self.u(width(*w));
            }
            PrimOp::FloatArith(a) => {
                self.u(1);
                self.u(arith(*a));
            }
            PrimOp::Float32Arith(a) => {
                self.u(2);
                self.u(arith(*a));
            }
            PrimOp::Cmp(c) => {
                self.u(3);
                self.u(match c {
                    Cmp::Lt => 0,
                    Cmp::Gt => 1,
                    Cmp::Le => 2,
                    Cmp::Ge => 3,
                });
            }
            PrimOp::Eq(b) => {
                self.u(4);
                self.bool(*b);
            }
            PrimOp::Construct { ctor, order } => {
                self.u(5);
                self.u(ctor.id as u64);
                self.len(order.len());
                for i in order {
                    self.len(*i);
                }
            }
            PrimOp::Concat => self.u(7),
            PrimOp::TextOfInt => self.u(8),
            PrimOp::TextLen => self.u(9),
            PrimOp::TextCompare => self.u(10),
            PrimOp::Divide { modulo, width: w } => {
                self.u(11);
                self.bool(*modulo);
                self.u(width(*w));
            }
            PrimOp::SynParse(_) => return Err("runtime syntax parsers".into()),
        }
        Ok(())
    }
    fn unary(&mut self, u: &UnaryOp) {
        match u {
            UnaryOp::Not => self.u(0),
            UnaryOp::Field(s) => {
                self.u(2);
                self.step(s);
            }
            UnaryOp::Shown => self.u(3),
            UnaryOp::TempRef => self.u(4),
            UnaryOp::Deref => self.u(5),
            UnaryOp::Inject(a, b) => {
                self.u(6);
                self.u(*a as u64);
                self.u(*b as u64);
            }
            UnaryOp::Remap(to, table) => {
                self.u(7);
                self.opt(to.map(u64::from));
                self.len(table.len());
                for t in table {
                    self.opt(t.map(|t| t as u64));
                }
            }
        }
    }
    fn op(&mut self, op: &Op) {
        match *op {
            Op::Const(n) => {
                self.u(0);
                self.u(n as u64);
            }
            Op::Unit => self.u(1),
            Op::Load {
                slot,
                deref,
                take,
                indirect,
            } => {
                self.u(2);
                self.u(slot as u64);
                self.bool(deref);
                self.bool(take);
                self.bool(indirect);
            }
            Op::Clear { slot } => {
                self.u(3);
                self.u(slot as u64);
            }
            Op::Define { slot, shared } => {
                self.u(4);
                self.u(slot as u64);
                self.bool(shared);
            }
            Op::Assign {
                slot,
                path,
                through,
                indirect,
            } => {
                self.u(5);
                self.u(slot as u64);
                self.u(path as u64);
                self.bool(through);
                self.bool(indirect);
            }
            Op::Borrow {
                slot,
                path,
                through,
                indirect,
            } => {
                self.u(6);
                self.u(slot as u64);
                self.u(path as u64);
                self.bool(through);
                self.bool(indirect);
            }
            Op::Pop => self.u(7),
            Op::Jump(n) => {
                self.u(8);
                self.u(n as u64);
            }
            Op::JumpIfNot(n) => {
                self.u(9);
                self.u(n as u64);
            }
            Op::Call { argc, ticked } => {
                self.u(10);
                self.u(argc as u64);
                self.bool(ticked);
            }
            Op::TailSelf { inst, argc } => {
                self.u(11);
                self.u(inst as u64);
                self.u(argc as u64);
            }
            Op::Builtin { name, argc } => {
                self.u(12);
                self.u(name as u64);
                self.u(argc as u64);
            }
            Op::Prim { prim, argc } => {
                self.u(13);
                self.u(prim as u64);
                self.u(argc as u64);
            }
            Op::Unary(n) => {
                self.u(14);
                self.u(n as u64);
            }
            Op::Closure(n) => {
                self.u(15);
                self.u(n as u64);
            }
            Op::Perform { op, quant: q, argc } => {
                self.u(16);
                self.u(op as u64);
                self.u(quant(q));
                self.u(argc as u64);
            }
            Op::Handle(n) => {
                self.u(17);
                self.u(n as u64);
            }
            Op::Unhandle => self.u(18),
            Op::Ret => self.u(19),
            Op::Return => self.u(20),
            Op::Test { pat, fail } => {
                self.u(21);
                self.u(pat as u64);
                self.u(fail as u64);
            }
            Op::NoArm => self.u(22),
            Op::Tick => self.u(23),
            Op::TickAnswer => self.u(24),
            Op::Budget(n) => {
                self.u(25);
                self.u(n as u64);
            }
            Op::Extern { index, argc } => {
                self.u(26);
                self.u(index as u64);
                self.u(argc as u64);
            }
        }
    }
}

struct R<'a> {
    b: &'a [u8],
    at: usize,
}

impl<'a> R<'a> {
    fn take(&mut self, n: usize) -> Rs<&'a [u8]> {
        let end = self.at.checked_add(n).filter(|e| *e <= self.b.len());
        let end = end.ok_or("the program's bytes end early")?;
        let out = &self.b[self.at..end];
        self.at = end;
        Ok(out)
    }
    fn u(&mut self) -> Rs<u64> {
        let mut n = 0u64;
        let mut shift = 0;
        loop {
            let b = self.take(1)?[0];
            if shift >= 64 {
                return Err("a number too large".into());
            }
            n |= u64::from(b & 0x7f) << shift;
            if b & 0x80 == 0 {
                return Ok(n);
            }
            shift += 7;
        }
    }
    fn u32(&mut self) -> Rs<u32> {
        u32::try_from(self.u()?).map_err(|_| "a number too large".into())
    }
    fn len(&mut self) -> Rs<usize> {
        usize::try_from(self.u()?).map_err(|_| "a number too large".into())
    }
    fn bool(&mut self) -> Rs<bool> {
        Ok(self.u()? != 0)
    }
    fn opt(&mut self) -> Rs<Option<u64>> {
        Ok(match self.u()? {
            0 => None,
            _ => Some(self.u()?),
        })
    }
    fn str(&mut self) -> Rs<&'a str> {
        let n = self.len()?;
        std::str::from_utf8(self.take(n)?).map_err(|e| e.to_string())
    }
    fn many<T>(&mut self, mut each: impl FnMut(&mut Self) -> Rs<T>) -> Rs<Vec<T>> {
        let n = self.len()?;
        let mut out = Vec::with_capacity(n.min(1 << 16));
        for _ in 0..n {
            out.push(each(self)?);
        }
        Ok(out)
    }
    fn us(&mut self) -> Rs<Vec<u32>> {
        self.many(R::u32)
    }
    fn name(&mut self) -> Rs<Name> {
        let library = self.bool()?;
        let s = self.str()?;
        Ok(if library {
            tauto_nir::library_name(s)
        } else {
            Name::Spelled(s.to_string())
        })
    }
    fn aliases(&mut self) -> Rs<Vec<(u32, bool, u32)>> {
        self.many(|r| Ok((r.u32()?, r.bool()?, r.u32()?)))
    }
    fn value(&mut self) -> Rs<Value> {
        Ok(match self.u()? {
            0 => Value::Unit,
            1 => Value::Bool(self.bool()?),
            2 => Value::Int(i128::from_le_bytes(self.take(16)?.try_into().unwrap())),
            3 => Value::Float(f64::from_le_bytes(self.take(8)?.try_into().unwrap())),
            4 => Value::text(self.str()?),
            5 => Value::Fn(self.u32()?),
            n => return Err(format!("value {n}")),
        })
    }
    fn step(&mut self) -> Rs<Step> {
        Ok(match self.u()? {
            0 => Step::Index(self.len()?),
            1 => Step::Name(Rc::from(self.str()?)),
            2 => Step::Item(self.len()?),
            3 => Step::Entry(self.len()?),
            n => return Err(format!("step {n}")),
        })
    }
    fn pat(&mut self) -> Rs<Pat> {
        Ok(match self.u()? {
            0 => Pat::Wild,
            1 => Pat::Bind {
                slot: self.u32()?,
                borrow: self.bool()?,
            },
            2 => Pat::Literal(self.value()?),
            3 => Pat::Ctor {
                ctor: self.u32()?,
                fields: self.many(R::pat)?,
            },
            n => return Err(format!("pattern {n}")),
        })
    }
    fn prim(&mut self, ctors: &[Rc<Ctor>]) -> Rs<PrimOp> {
        Ok(match self.u()? {
            0 => PrimOp::Arith(arith_of(self.u()?)?, width_of(self.u()?)?),
            1 => PrimOp::FloatArith(arith_of(self.u()?)?),
            2 => PrimOp::Float32Arith(arith_of(self.u()?)?),
            3 => PrimOp::Cmp(match self.u()? {
                0 => Cmp::Lt,
                1 => Cmp::Gt,
                2 => Cmp::Le,
                3 => Cmp::Ge,
                n => return Err(format!("comparison {n}")),
            }),
            4 => PrimOp::Eq(self.bool()?),
            5 => {
                let id = self.len()?;
                let ctor = ctors.get(id).cloned().ok_or("an unknown constructor")?;
                PrimOp::Construct {
                    ctor,
                    order: self.many(R::len)?,
                }
            }
            7 => PrimOp::Concat,
            8 => PrimOp::TextOfInt,
            9 => PrimOp::TextLen,
            10 => PrimOp::TextCompare,
            11 => PrimOp::Divide {
                modulo: self.bool()?,
                width: width_of(self.u()?)?,
            },
            n => return Err(format!("primitive {n}")),
        })
    }
    fn unary(&mut self) -> Rs<UnaryOp> {
        Ok(match self.u()? {
            0 => UnaryOp::Not,
            2 => UnaryOp::Field(self.step()?),
            3 => UnaryOp::Shown,
            4 => UnaryOp::TempRef,
            5 => UnaryOp::Deref,
            6 => UnaryOp::Inject(self.u32()?, self.u32()?),
            7 => UnaryOp::Remap(
                self.opt()?.map(|n| n as u32),
                self.many(|r| Ok(r.opt()?.map(|n| n as usize)))?,
            ),
            n => return Err(format!("unary {n}")),
        })
    }
    fn op(&mut self) -> Rs<Op> {
        Ok(match self.u()? {
            0 => Op::Const(self.u32()?),
            1 => Op::Unit,
            2 => Op::Load {
                slot: self.u32()?,
                deref: self.bool()?,
                take: self.bool()?,
                indirect: self.bool()?,
            },
            3 => Op::Clear { slot: self.u32()? },
            4 => Op::Define {
                slot: self.u32()?,
                shared: self.bool()?,
            },
            5 => Op::Assign {
                slot: self.u32()?,
                path: self.u32()?,
                through: self.bool()?,
                indirect: self.bool()?,
            },
            6 => Op::Borrow {
                slot: self.u32()?,
                path: self.u32()?,
                through: self.bool()?,
                indirect: self.bool()?,
            },
            7 => Op::Pop,
            8 => Op::Jump(self.u32()?),
            9 => Op::JumpIfNot(self.u32()?),
            10 => Op::Call {
                argc: self.u32()?,
                ticked: self.bool()?,
            },
            11 => Op::TailSelf {
                inst: self.u32()?,
                argc: self.u32()?,
            },
            12 => Op::Builtin {
                name: self.u32()?,
                argc: self.u32()?,
            },
            13 => Op::Prim {
                prim: self.u32()?,
                argc: self.u32()?,
            },
            14 => Op::Unary(self.u32()?),
            15 => Op::Closure(self.u32()?),
            16 => Op::Perform {
                op: self.u32()?,
                quant: quant_of(self.u()?)?,
                argc: self.u32()?,
            },
            17 => Op::Handle(self.u32()?),
            18 => Op::Unhandle,
            19 => Op::Ret,
            20 => Op::Return,
            21 => Op::Test {
                pat: self.u32()?,
                fail: self.u32()?,
            },
            22 => Op::NoArm,
            23 => Op::Tick,
            24 => Op::TickAnswer,
            25 => Op::Budget(self.u32()?),
            26 => Op::Extern {
                index: self.u32()?,
                argc: self.u32()?,
            },
            n => return Err(format!("op {n}")),
        })
    }
}
