//! A program in continuation-passing style (`tauto_nir::cps`), as the reader
//! of the machine written in Tauto (`totes/vm/src/wire.taut`) takes it:
//! numbers in decimal separated by spaces, each node a tag and then its
//! parts, each list its length and then its items. A text is `t`, its
//! length in bytes, a space and the bytes. The machine compiles it to its
//! own code (`totes/vm/src/compile.taut`). What it cannot be written as is an
//! error naming it.

use std::collections::HashMap;
use std::fmt::Write;

use tauto_nir::cps::{self, Cps, CpsPat, PathStep, Prim, Unary};
use tauto_nir::{Arith, Cmp, Package, Quant, Width};

type Rs<T> = Result<T, String>;

/// A constructor: its data type, its name and its fields' names.
struct Ctor {
    tag: String,
    names: Vec<Option<String>>,
    is_struct: bool,
}

#[derive(Default)]
pub(crate) struct Writer {
    ctors: Vec<Ctor>,
    ids: HashMap<(String, String), u32>,
    pub(crate) out: String,
    /// Each runtime syntax parser of the package (`syn_parse`), as the machine reads it.
    parsers: Vec<(String, String, tauto_nir::Ty, String)>,
}

/// The program of the package.
pub fn write(pkg: &Package) -> Rs<String> {
    if !pkg.externs.is_empty() {
        return Err("extern functions (the machine has no host bindings)".into());
    }
    let Some(top) = pkg.top else {
        return Err("a program with no top level".into());
    };
    let mut w = Writer::default();
    // The prelude's data types first, in the order the machine has them.
    w.ctor("Option", "Some", &[None], false);
    w.ctor("Option", "None", &[], false);
    w.ctor("Result", "Ok", &[None], false);
    w.ctor("Result", "Err", &[None], false);
    w.ctor("Pair", "Pair", &[Some("fst"), Some("snd")], true);
    w.ctor("List", "Cons", &[None, None], false);
    w.ctor("List", "Nil", &[], false);
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
        // Shown by the name written, not by its full name `m.T.C`.
        let tag = c.tag.rsplit('.').next().unwrap_or(&c.tag);
        let tag = tag.strip_prefix(':').unwrap_or(tag);
        let named = (c.is_struct || !c.names.is_empty()) && c.names.iter().all(Option::is_some);
        text_out(&mut out, tag);
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
    pub(crate) fn ctor(
        &mut self,
        owner: &str,
        tag: &str,
        names: &[Option<&str>],
        is_struct: bool,
    ) -> u32 {
        let key = (owner.to_string(), tag.to_string());
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
            tag: tag.to_string(),
            names: names.iter().map(|n| n.map(String::from)).collect(),
            is_struct,
        });
        self.ids.insert(key, id);
        id
    }

    fn ctor_id(&mut self, owner: &str, tag: &str) -> u32 {
        let key = (owner.to_string(), tag.to_string());
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
            CpsPat::Bind { id, borrow, .. } => {
                self.num(1);
                self.num(id);
                self.yn(*borrow);
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
            CpsPat::Product(_) => return Err("a pattern of a product".into()),
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
            Prim::Product { picks } => {
                self.num(5);
                self.num(picks.len());
                for (i, j) in picks {
                    self.num(i);
                    self.yn(j.is_some());
                    if let Some(j) = j {
                        self.num(j);
                    }
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
            Unary::Member(i) => {
                self.num(1);
                self.num(i);
            }
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
            Cps::TailSelfCall { inst, args } => {
                self.num(3);
                self.num(inst);
                self.list(args)?;
            }
            Cps::External { name, .. } => return Err(format!("the extern {name}")),
            Cps::Builtin { name, args } => {
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
            Cps::Sequence(es) => {
                self.num(8);
                self.list(es)?;
            }
            Cps::Define {
                id, shared, init, ..
            } => {
                self.num(9);
                self.num(id);
                self.yn(*shared);
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
                self.text(op);
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
                    self.text(&a.op);
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
            Cps::BorrowPlace {
                id,
                path,
                through_borrow,
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

/// The arguments of the machine (`totes/vm`) that runs the program written
/// to `program` with the permissions `flags` (`--allow-…`), at most `steps`
/// steps (`None` for none), what it shows going to `shows` (the standard
/// output when `None`), and `args` as the program's own arguments.
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
    out.push("--".into());
    out.push(program.display().to_string());
    out.push(steps.map_or("-".into(), |s| s.to_string()));
    out.push(shows.map_or("-".into(), |s| s.display().to_string()));
    out.extend(args.iter().cloned());
    out
}

/// The locals `e` uses, and those it binds.
fn locals(e: &Cps, used: &mut Vec<u32>, bound: &mut Vec<u32>) {
    fn pat(p: &CpsPat, bound: &mut Vec<u32>) {
        match p {
            CpsPat::Bind { id, .. } => bound.push(*id),
            CpsPat::Ctor { fields, .. } | CpsPat::Product(fields) => {
                fields.iter().for_each(|f| pat(f, bound))
            }
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
