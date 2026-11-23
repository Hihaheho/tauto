//! A program in continuation-passing style (`tauto_nir::cps`), as the reader
//! of the machine written in Tauto (`totes/vm/src/wire.taut`) takes it:
//! numbers in decimal separated by spaces, each node a tag and then its
//! parts, each list its length and then its items. A text is `t`, its
//! length in bytes, a space and the bytes. The machine compiles it to its
//! own code (`totes/vm/src/compile.taut`). What it cannot be written as is an
//! error naming it.

use std::collections::HashMap;
use std::fmt::Write;
use tauto_nir::Name;

use tauto_nir::cps::{self, Cps, CpsPat, PathStep, Prim, Unary};
use tauto_nir::{Arith, Cmp, Package, Quant, Width};

type Rs<T> = Result<T, String>;

struct Ctor {
    tag: String,
    names: Vec<Option<String>>,
    is_struct: bool,
}

#[derive(Default)]
pub(crate) struct Writer {
    ctors: Vec<Ctor>,
    ids: HashMap<(Name, Name), u32>,
    pub(crate) out: String,
    operation_symbols: HashMap<Name, String>,
    /// Each runtime syntax parser of the package (`syn_parse`), as the machine reads it.
    parsers: Vec<(String, String, tauto_nir::Ty, String)>,
    /// The program makes host values (an `extern` the machine binds): every
    /// local is dropped when its block ends, a move empties its local, and
    /// the machine looks for host values nothing reaches after each
    /// statement (`totes/vm/src/host.taut`).
    hosts: bool,
    /// Locals the writer adds, numbered down from the largest.
    fresh: u32,
}

/// The externs the machine binds, as every runner of the cases does: the
/// case host's probe (`tauto_rt::probe`), a value whose drop is written down
/// by name.
pub const BOUND_EXTERNS: &[&str] = &["Probe::new"];

/// Why a program with another extern is refused: the machine has no binding
/// for it, as the Rust backend refuses an extern its manifest does not bind.
pub fn unbound_extern(name: &str) -> String {
    format!("the extern {name}{UNBOUND}")
}

const UNBOUND: &str = ", which has no binding on the machine";

/// Whether `write` refused the program by a decision of the backend (the
/// secret words, an extern it does not bind), not for a gap of the machine.
pub fn refused(what: &str) -> bool {
    what == SECRET_WORDS || what.ends_with(UNBOUND)
}

/// Why a program that computes on secrets (`Ct::`) is refused: what the
/// machine runs takes a time that depends on the values.
pub const SECRET_WORDS: &str = "secret words, which it cannot run in constant time";

pub fn write(pkg: &Package) -> Rs<String> {
    if let Some(x) = pkg
        .externs
        .iter()
        .find(|x| !BOUND_EXTERNS.contains(&x.name.as_str()))
    {
        return Err(unbound_extern(x.name.as_str()));
    }
    let Some(top) = pkg.top else {
        return Err("a program with no top level".into());
    };
    let mut w = Writer {
        hosts: !pkg.externs.is_empty(),
        ..Writer::default()
    };
    // The prelude's data types first, in the order the machine has them.
    w.ctor(
        &tauto_nir::library_name("Option"),
        &tauto_nir::library_name("Some"),
        &[None],
        false,
    );
    w.ctor(
        &tauto_nir::library_name("Option"),
        &tauto_nir::library_name("None"),
        &[],
        false,
    );
    w.ctor(
        &tauto_nir::library_name("Result"),
        &tauto_nir::library_name("Ok"),
        &[None],
        false,
    );
    w.ctor(
        &tauto_nir::library_name("Result"),
        &tauto_nir::library_name("Err"),
        &[None],
        false,
    );
    w.ctor(
        &tauto_nir::library_name("Pair"),
        &tauto_nir::library_name("Pair::Mk"),
        &[Some("fst"), Some("snd")],
        true,
    );
    w.ctor(
        &tauto_nir::library_name("List"),
        &tauto_nir::library_name("Cons"),
        &[None, None],
        false,
    );
    w.ctor(
        &tauto_nir::library_name("List"),
        &tauto_nir::library_name("Nil"),
        &[],
        false,
    );
    for d in &pkg.datas {
        for c in &d.ctors {
            let names: Vec<Option<&str>> = c.fields.iter().map(|f| f.name.as_deref()).collect();
            w.ctor(&d.name, &c.name, &names, d.is_struct);
        }
    }
    for p in &pkg.syntax_parsers {
        let text = crate::syntax::write(&mut w, pkg, p)?;
        w.parsers
            .push((p.name.clone(), p.sha.clone(), p.result.clone(), text));
    }
    let mut bodies: Vec<Option<(Vec<u32>, Cps)>> = (0..pkg.fns.len()).map(|_| None).collect();
    for f in &pkg.fns {
        let body = cps::lower(pkg, f, true).map_err(|e| format!("{}: {e}", f.source))?;
        bodies[f.id] = Some((f.params.iter().map(|q| q.local.id).collect(), body));
    }
    w.num(bodies.len());
    for b in bodies {
        let (params, body) = b.ok_or("internal: a function with no instance")?;
        w.nums(&params);
        w.expr(&body)?;
    }
    let mut out = std::mem::take(&mut w.out);
    write!(out, " {}", w.ctors.len()).unwrap();
    for c in &w.ctors {
        let named = (c.is_struct || !c.names.is_empty()) && c.names.iter().all(Option::is_some);
        text_out(&mut out, &c.tag);
        write!(out, " {} {}", u8::from(named), c.names.len()).unwrap();
        for n in &c.names {
            text_out(&mut out, n.as_deref().unwrap_or(""));
        }
    }
    write!(out, " {top}").unwrap();
    Ok(out)
}

fn width(w: Width) -> u32 {
    match w {
        Width::W32 => 0,
        Width::W64 => 1,
        Width::U8 => 2,
        Width::U32 => 3,
        Width::U64 => 4,
        Width::Nat => 5,
        Width::Host => 6,
        Width::W8 => 7,
        Width::W16 => 8,
        Width::U16 => 9,
    }
}

fn arith(a: Arith) -> u32 {
    match a {
        Arith::Add => 0,
        Arith::Sub => 1,
        Arith::Mul => 2,
        Arith::Neg => 3,
        Arith::Div => 4,
    }
}

fn text_out(out: &mut String, t: &str) {
    write!(out, " t{} {t}", t.len()).unwrap();
}

impl Writer {
    fn operation(&mut self, operation: &Name) {
        let symbol = match operation {
            Name::Spelled(spelling) => spelling.clone(),
            Name::Global(reference) if tauto_nir::is_library(&operation, operation.as_str()) => {
                reference.display().to_string()
            }
            _ => {
                let next = self.operation_symbols.len();
                self.operation_symbols
                    .entry(operation.clone())
                    .or_insert_with(|| format!("tauto_operation_{next}"))
                    .clone()
            }
        };
        self.text(&symbol);
    }

    pub(crate) fn ctor(
        &mut self,
        owner: &Name,
        tag: &Name,
        names: &[Option<&str>],
        is_struct: bool,
    ) -> u32 {
        let key = (owner.clone(), tag.clone());
        if let Some(&id) = self.ids.get(&key) {
            // A constructor matched before it was made has its names now.
            let c = &mut self.ctors[id as usize];
            if c.names.len() != names.len() {
                c.names = names.iter().map(|n| n.map(String::from)).collect();
                c.is_struct = is_struct;
            }
            return id;
        }
        let id = self.ctors.len() as u32;
        self.ctors.push(Ctor {
            tag: if is_struct {
                tauto_nir::display_name(owner).to_string()
            } else {
                tag.rsplit("::").next().unwrap_or(tag).to_string()
            },
            names: names.iter().map(|n| n.map(String::from)).collect(),
            is_struct,
        });
        self.ids.insert(key, id);
        id
    }

    fn ctor_id(&mut self, owner: &Name, tag: &Name) -> u32 {
        let key = (owner.clone(), tag.clone());
        match self.ids.get(&key) {
            Some(&id) => id,
            None => self.ctor(owner, tag, &[], false),
        }
    }

    pub(crate) fn num(&mut self, n: impl std::fmt::Display) {
        write!(self.out, " {n}").unwrap();
    }

    pub(crate) fn yn(&mut self, b: bool) {
        self.num(u8::from(b));
    }

    pub(crate) fn text(&mut self, t: &str) {
        text_out(&mut self.out, t);
    }

    pub(crate) fn nums(&mut self, ns: &[u32]) {
        self.num(ns.len());
        for n in ns {
            self.num(n);
        }
    }

    fn value(&mut self, v: &cps::Value) {
        match v {
            cps::Value::Declaration(slot) => {
                self.num(6);
                self.num(slot);
            }
            cps::Value::Unit => self.num(0),
            cps::Value::Int(n) => {
                self.num(1);
                self.yn(*n < 0);
                self.num(n.unsigned_abs());
            }
            cps::Value::Float(x) => {
                self.num(2);
                self.num(x.to_bits());
            }
            cps::Value::Bool(b) => {
                self.num(3);
                self.yn(*b);
            }
            cps::Value::Text(t) => {
                self.num(4);
                self.text(t);
            }
            cps::Value::Fn(i) => {
                self.num(5);
                self.num(i);
            }
        }
    }

    fn path(&mut self, path: &[PathStep]) {
        self.num(path.len());
        for s in path {
            match s {
                PathStep::Index(i) => {
                    self.num(0);
                    self.num(i);
                }
                PathStep::Name(n) => {
                    self.num(1);
                    self.text(n);
                }
            }
        }
    }

    fn pat(&mut self, p: &CpsPat) -> Rs<()> {
        match p {
            CpsPat::Wild => self.num(0),
            // Nothing changes what a `&` binding names while it lives, so the
            // machine binds its value: a borrow of a part of a borrow would
            // otherwise lengthen its path at each step of a recursion over a
            // borrowed list, and reading it would walk that path.
            CpsPat::Bind {
                id,
                borrow,
                mutable,
                ..
            } => {
                self.num(1);
                self.num(id);
                self.yn(*borrow && *mutable);
            }
            CpsPat::Literal(v) => {
                self.num(2);
                self.value(v);
            }
            CpsPat::Ctor { ctor, fields, data } => {
                let id = self.ctor_id(data, ctor);
                self.num(3);
                self.num(id);
                self.num(fields.len());
                for f in fields {
                    self.pat(f)?;
                }
            }
            CpsPat::Variant { variant, pat, .. } => {
                self.num(5);
                self.num(variant);
                self.pat(pat)?;
            }
        }
        Ok(())
    }

    fn list(&mut self, es: &[Cps]) -> Rs<()> {
        self.num(es.len());
        es.iter().try_for_each(|e| self.expr(e))
    }

    fn arm(&mut self, arm: &cps::MatchArm) -> Rs<()> {
        self.pat(&arm.pat)?;
        self.expr(&arm.guard)?;
        self.expr(&arm.body)
    }

    fn prim(&mut self, op: &Prim) -> Rs<()> {
        match op {
            Prim::Arith(Arith::Div, _) => return Err("internal: integer `/`".into()),
            Prim::Arith(a, w) => {
                self.num(0);
                self.num(arith(*a));
                self.num(width(*w));
            }
            Prim::FloatArith(a) => {
                self.num(1);
                self.num(arith(*a));
            }
            Prim::Float32Arith(a) => {
                self.num(11);
                self.num(arith(*a));
            }
            Prim::Cmp(c) => {
                self.num(2);
                self.num(match c {
                    Cmp::Lt => 0,
                    Cmp::Le => 1,
                    Cmp::Gt => 2,
                    Cmp::Ge => 3,
                });
            }
            Prim::Eq { negate } => {
                self.num(3);
                self.yn(*negate);
            }
            Prim::Construct {
                ctor,
                names,
                order,
                is_struct,
                data,
                ..
            } => {
                let names: Vec<Option<&str>> = order.iter().map(|i| names[*i].as_deref()).collect();
                let id = self.ctor(data, ctor, &names, *is_struct);
                self.num(4);
                self.num(id);
                self.num(order.len());
                for i in order {
                    self.num(i);
                }
            }
            Prim::Concat => self.num(6),
            Prim::TextOfInt => self.num(7),
            Prim::TextLen => self.num(8),
            Prim::TextCompare => self.num(9),
            Prim::Divide { name, width: w } => {
                self.num(10);
                self.yn(name == "mod");
                self.num(width(*w));
            }
            Prim::SynParse { name, sha, ty } => {
                let Some((.., text)) = self
                    .parsers
                    .iter()
                    .find(|(n, s, t, _)| n == name && s == sha && t == ty)
                else {
                    return Err("a runtime syntax parser without its tables".into());
                };
                let text = text.clone();
                self.num(12);
                self.out.push_str(&text);
            }
        }
        Ok(())
    }

    fn unary(&mut self, op: &Unary) {
        match op {
            Unary::Not => self.num(0),
            Unary::Field { name, index } => {
                self.num(2);
                match index {
                    Some(i) => {
                        self.num(0);
                        self.num(i);
                    }
                    None => {
                        self.num(1);
                        self.text(name);
                    }
                }
            }
            Unary::Shown => self.num(3),
            Unary::TempRef { .. } => self.num(4),
            Unary::Deref { .. } => self.num(5),
            Unary::Inject { union, variant } => {
                self.num(6);
                self.num(union);
                self.num(variant);
            }
            Unary::Remap { to, table } => {
                self.num(7);
                self.yn(to.is_some());
                if let Some(t) = to {
                    self.num(t);
                }
                self.num(table.len());
                for j in table {
                    self.yn(j.is_some());
                    if let Some(j) = j {
                        self.num(j);
                    }
                }
            }
        }
    }

    fn expr(&mut self, e: &Cps) -> Rs<()> {
        match e {
            Cps::Pure(v) => {
                self.num(0);
                self.value(v);
            }
            // A move out of a local that may hold a host value empties it,
            // so the value is dropped by its new owner.
            Cps::ReadLocal {
                id,
                deref: false,
                take: true,
                ..
            } if self.hosts => {
                self.num(19);
                self.num(id);
            }
            Cps::ReadLocal { id, deref, .. } => {
                self.num(1);
                self.num(id);
                self.yn(*deref);
            }
            Cps::Call {
                callee,
                args,
                ticked,
            } => {
                self.num(2);
                self.expr(callee)?;
                self.list(args)?;
                self.yn(*ticked);
            }
            Cps::TailSelfCall { inst, args, ticked } => {
                self.num(3);
                self.num(inst);
                self.list(args)?;
                self.yn(*ticked);
            }
            // The machine refuses the externs it does not bind too
            // (`totes/vm/src/compile.taut`); refusing here as well gives the
            // reason before a program is written.
            Cps::External { name, args } => {
                if !BOUND_EXTERNS.contains(&name.as_str()) {
                    return Err(unbound_extern(name.as_str()));
                }
                self.num(21);
                self.text(name.as_str());
                self.list(args)?;
            }
            Cps::Builtin { name, args } => {
                // `docs/design/secret.md`: the machine's words and numbers
                // promise no constant time, so the secret words are refused.
                if name.starts_with("Ct::") {
                    return Err(SECRET_WORDS.into());
                }
                self.num(4);
                self.text(name);
                self.list(args)?;
            }
            Cps::Prim { op, args } => {
                self.num(5);
                self.prim(op)?;
                self.list(args)?;
            }
            Cps::Map { value, op } => {
                self.num(6);
                self.expr(value)?;
                self.unary(op);
            }
            Cps::Branch {
                cond,
                then,
                otherwise,
            } => {
                self.num(7);
                self.expr(cond)?;
                self.expr(then)?;
                self.expr(otherwise)?;
            }
            Cps::Sequence(es) if self.hosts && es.len() > 1 => {
                // After each statement, a host value nothing reaches any
                // more (a temporary, a continuation no one resumes) is
                // dropped.
                self.num(8);
                self.num(2 * es.len() - 1);
                for (i, e) in es.iter().enumerate() {
                    if i > 0 {
                        self.num(20);
                    }
                    self.expr(e)?;
                }
            }
            Cps::Sequence(es) => {
                self.num(8);
                self.list(es)?;
            }
            Cps::Define {
                id,
                shared,
                init,
                drop,
                ..
            } => {
                self.num(9);
                self.num(id);
                self.yn(*shared);
                self.yn(*drop || self.hosts);
                self.expr(init)?;
            }
            Cps::Assign {
                id,
                path,
                through_borrow,
                value,
            } => {
                self.num(10);
                self.num(id);
                self.path(path);
                self.yn(*through_borrow);
                self.expr(value)?;
            }
            Cps::While { cond, body, ticked } => {
                self.num(11);
                self.expr(cond)?;
                self.expr(body)?;
                self.yn(*ticked);
            }
            Cps::Return(v) => {
                self.num(12);
                self.expr(v)?;
            }
            Cps::Match { scrut, arms } => {
                self.num(13);
                self.expr(scrut)?;
                self.num(arms.len());
                for arm in arms {
                    self.arm(arm)?;
                }
            }
            // A closure that moves locals in empties them once it is made,
            // so what they held is dropped with the closure.
            Cps::Closure(c) if self.hosts && !c.moves.is_empty() => {
                self.fresh += 1;
                let made = u32::MAX - self.fresh;
                self.num(8);
                self.num(c.moves.len() + 2);
                self.num(9);
                self.num(made);
                self.yn(false);
                self.yn(true);
                let mut inner = (**c).clone();
                inner.moves.clear();
                self.expr(&Cps::Closure(Box::new(inner)))?;
                for id in &c.moves {
                    self.num(19);
                    self.num(id);
                }
                self.num(1);
                self.num(made);
                self.yn(false);
            }
            Cps::Closure(c) => {
                self.num(14);
                self.expr(&c.body)?;
                self.nums(&c.params);
                // A borrowing closure reads the locals of the scope it is in
                // without capturing them; the machine's closure is a function
                // of its own, so they are captures too, which shares them.
                let mut caps = c.captures.clone();
                let (mut used, mut bound) = (Vec::new(), c.params.clone());
                bound.extend(c.refs.iter().map(|r| r.0));
                locals(&c.body, &mut used, &mut bound);
                for id in used {
                    if !bound.contains(&id) && !caps.contains(&id) {
                        caps.push(id);
                    }
                }
                self.nums(&caps);
                self.yn(c.borrowed);
                self.num(c.refs.len());
                for (inner, outer) in &c.refs {
                    self.num(inner);
                    self.num(outer);
                }
            }
            Cps::Perform { op, quant, args } => {
                self.num(15);
                self.operation(op);
                self.num(match quant {
                    Quant::Zero => 0,
                    Quant::AtMostOne | Quant::One => 1,
                    Quant::Many => 2,
                    Quant::Direct => 3,
                });
                self.list(args)?;
            }
            Cps::Handle { body, arms, ret } => {
                self.num(16);
                self.expr(body)?;
                self.num(arms.len());
                for a in arms {
                    if a.guard != Cps::Pure(cps::Value::Bool(true)) {
                        return Err("a guard on a handler's arm".into());
                    }
                    self.operation(&a.op);
                    self.num(a.pats.len());
                    for p in &a.pats {
                        self.pat(p)?;
                    }
                    self.num(a.k.map_or(0, |k| k + 1));
                    self.expr(&a.body)?;
                }
                match ret {
                    None => self.num(0),
                    Some(arm) => {
                        self.num(1);
                        self.arm(arm)?;
                    }
                }
            }
            // A `&` borrow of a local that is itself a borrow: nothing writes
            // the place while it lives, so the machine reads the value
            // instead of naming the place again. (A local of its own stays
            // a place, which the machine may have to put in a cell.)
            Cps::BorrowPlace {
                id,
                path,
                through_borrow: true,
                mutable: false,
            } if path.is_empty() => {
                self.num(1);
                self.num(id);
                self.yn(true);
            }
            Cps::BorrowPlace {
                id,
                path,
                through_borrow,
                ..
            } => {
                self.num(17);
                self.num(id);
                self.path(path);
                self.yn(*through_borrow);
            }
            Cps::Budget {
                memory,
                steps,
                body,
                ..
            } => {
                self.num(18);
                self.yn(*memory);
                self.expr(steps)?;
                self.expr(body)?;
            }
        }
        Ok(())
    }
}

/// The most calls that nest, one inside another, that the machine
/// (`totes/vm`, `m_max_frames`) keeps before it stops the run.
pub const MACHINE_MAX_FRAMES: u64 = 1 << 21;

/// The arguments of the machine (`totes/vm`) that runs the program written
/// to `program` with the permissions `flags` (`--allow-…`), at most `steps`
/// steps (`None` for none), what it shows going to `shows` (the standard
/// output when `None`), what it says when the steps run out (`interrupted`,
/// in the language of the user; the English one when `None`), what it says
/// when its calls nest deeper than `MACHINE_MAX_FRAMES` (`too_deep`, likewise),
/// and `args` as the program's own arguments.
///
/// The machine asks its own host for what the program asks of it, so it is
/// given the program's permissions; besides them it may read the program,
/// write the shows and take no step limit of its own, and holds a grant of
/// each kind it uses so that it starts.
pub fn machine_args(
    flags: &[String],
    program: &std::path::Path,
    steps: Option<u64>,
    shows: Option<&std::path::Path>,
    interrupted: Option<&str>,
    too_deep: Option<&str>,
    args: &[String],
) -> Vec<String> {
    let mut out: Vec<String> = flags
        .iter()
        .filter(|f| f.as_str() != "--allow-div")
        .cloned()
        .collect();
    out.push("--allow-div".into());
    out.push(format!("--allow-read={}", program.display()));
    out.push(format!(
        "--allow-write={}",
        shows.unwrap_or(program).display()
    ));
    out.push("--allow-env=TAUTO_VM_NO_SUCH_VARIABLE".into());
    out.push("--allow-net=tauto-vm-no-such-host.invalid".into());
    out.push("--allow-run=tauto-vm-no-such-program".into());
    out.push("--".into());
    out.push(program.display().to_string());
    out.push(steps.map_or("-".into(), |s| s.to_string()));
    out.push(shows.map_or("-".into(), |s| s.display().to_string()));
    out.push(interrupted.unwrap_or("-").to_string());
    out.push(too_deep.unwrap_or("-").to_string());
    out.extend(args.iter().cloned());
    out
}

fn locals(e: &Cps, used: &mut Vec<u32>, bound: &mut Vec<u32>) {
    fn pat(p: &CpsPat, bound: &mut Vec<u32>) {
        match p {
            CpsPat::Bind { id, .. } => bound.push(*id),
            CpsPat::Ctor { fields, .. } => fields.iter().for_each(|f| pat(f, bound)),
            CpsPat::Variant { pat: p, .. } => pat(p, bound),
            CpsPat::Wild | CpsPat::Literal(_) => {}
        }
    }
    let all = |es: &[&Cps], used: &mut Vec<u32>, bound: &mut Vec<u32>| {
        for e in es {
            locals(e, used, bound);
        }
    };
    match e {
        Cps::Pure(_) => {}
        Cps::ReadLocal { id, .. } | Cps::BorrowPlace { id, .. } => used.push(*id),
        Cps::Call { callee, args, .. } => {
            locals(callee, used, bound);
            all(&args.iter().collect::<Vec<_>>(), used, bound);
        }
        Cps::TailSelfCall { args, .. }
        | Cps::External { args, .. }
        | Cps::Builtin { args, .. }
        | Cps::Prim { args, .. }
        | Cps::Perform { args, .. } => all(&args.iter().collect::<Vec<_>>(), used, bound),
        Cps::Sequence(es) => all(&es.iter().collect::<Vec<_>>(), used, bound),
        Cps::Map { value, .. } | Cps::Return(value) => locals(value, used, bound),
        Cps::Branch {
            cond,
            then,
            otherwise,
        } => all(&[cond, then, otherwise], used, bound),
        Cps::Define { id, init, .. } => {
            bound.push(*id);
            locals(init, used, bound);
        }
        Cps::Assign { id, value, .. } => {
            used.push(*id);
            locals(value, used, bound);
        }
        Cps::While { cond, body, .. } => all(&[cond, body], used, bound),
        Cps::Match { scrut, arms } => {
            locals(scrut, used, bound);
            for a in arms {
                pat(&a.pat, bound);
                all(&[&a.guard, &a.body], used, bound);
            }
        }
        Cps::Closure(c) => {
            bound.extend(&c.params);
            used.extend(&c.captures);
            locals(&c.body, used, bound);
        }
        Cps::Handle { body, arms, ret } => {
            locals(body, used, bound);
            for a in arms {
                a.pats.iter().for_each(|p| pat(p, bound));
                bound.extend(a.k);
                all(&[&a.guard, &a.body], used, bound);
            }
            if let Some(a) = ret {
                pat(&a.pat, bound);
                all(&[&a.guard, &a.body], used, bound);
            }
        }
        Cps::Budget { steps, body, .. } => all(&[steps, body], used, bound),
    }
}
