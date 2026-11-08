//! Export elaborated declarations for `totes/kernel`. The recording is opt-in;
//! neither the export nor its expected verdicts participate in kernel checking.
use super::*;
use crate::check::{Entry, Kernel, kernel_prelude};
use crate::surface::{Program, Stmt, parse_program_as_written};

/// A sequence of independent-kernel operations and the Rust verdicts for them.
#[derive(Debug)]
pub struct Replay {
    pub input: String,
    pub expected: String,
    /// Operations whose surface input could not be read as a core term.
    pub unread: usize,
    /// The time the Rust core spent in the recorded operations.
    pub time: std::time::Duration,
}

/// A named checker whose independent-kernel declarations are recorded.
pub struct Recorder(Kernel);

impl Recorder {
    pub fn new() -> Result<Self, String> {
        let mut kernel = Kernel::new();
        kernel.core.replay = Some(Vec::new());
        for e in kernel.declare(&kernel_prelude()?, true) {
            if e.failed() {
                return Err(format!("prelude: {}: {:?}", e.name, e.verdict));
            }
        }
        Ok(Self(kernel))
    }

    pub fn declare(&mut self, program: &Program) -> Vec<Entry> {
        self.0.declare_program(program)
    }

    /// Check a theorem's curried statement and body directly, without named
    /// elaboration, so that the replay includes core rejections too.
    pub fn theorem_written(&mut self, source: &str) -> Result<bool, String> {
        let mut p = parse_program_as_written(source)?;
        self.0.resolver.statements(&mut p.stmts);
        let Some(Stmt::Theorem(t)) = p.stmts.first() else {
            return Err("expected a theorem".into());
        };
        let ty = self
            .0
            .telescope(&t.params, &t.ty)
            .map_err(|d| d.message.to_string())?;
        let ty = self.0.shape(&ty).map_err(|d| d.message.to_string())?;
        let body = self
            .0
            .lambda_of(&t.params, t.body.as_ref().ok_or("expected a body")?)
            .map_err(|d| d.message.to_string())?;
        let body = self.0.shape(&body).map_err(|d| d.message.to_string())?;
        Ok(self
            .0
            .core
            .add_decl(&t.name, &ty, Some(&body), false)
            .is_ok())
    }

    /// Read an inductive declaration directly into the independent checker.
    pub fn inductive_written(&mut self, source: &str) -> Result<bool, String> {
        let mut p = parse_program_as_written(source)?;
        self.0.resolver.statements(&mut p.stmts);
        let Some(Stmt::Inductive(i)) = p.stmts.first() else {
            return Err("expected an inductive declaration".into());
        };
        let mut params = Vec::new();
        for (name, domain) in &i.params {
            params.push((
                name.clone(),
                self.0.shape(domain).map_err(|d| d.message.to_string())?,
            ));
        }
        let sort = self.0.shape(&i.sort).map_err(|d| d.message.to_string())?;
        let mut tail = &sort;
        while let TermKind::Pi { result, .. } = &*tail.kind {
            tail = result;
        }
        let out = crate::check::sort_of(tail).ok_or("expected a sort")?;
        let mut ctors = Vec::new();
        for ctor in &i.constructors {
            let mut args = Vec::new();
            for (name, domain) in &ctor.params {
                args.push((
                    name.clone(),
                    self.0.shape(domain).map_err(|d| d.message.to_string())?,
                ));
            }
            let result = self
                .0
                .shape(&ctor.result)
                .map_err(|d| d.message.to_string())?;
            let ty = crate::check::inductive::pi_all(
                &params,
                crate::check::inductive::pi_all(&args, result),
            );
            ctors.push((ctor.name.clone(), ty));
        }
        let spec = FamSpec {
            name: i.name.clone(),
            ty: crate::check::inductive::pi_all(&params, sort),
            ctors,
        };
        Ok(self
            .0
            .core
            .add_inductive(&[spec], params.len(), out)
            .is_ok())
    }

    /// Exercise an explicit eliminator specialization directly, including rejection.
    pub fn recursor_written(&mut self, family: &str, level: u32) -> bool {
        let Some(reference) = self.0.resolver.source_reference(family) else {
            return false;
        };
        self.0
            .core
            .recursor_at(&reference, &crate::check::Level::konst(level))
            .is_ok()
    }

    pub fn finish(mut self) -> Replay {
        let mut input = String::new();
        let mut expected = String::new();
        for (command, good) in self.0.core.replay.take().unwrap_or_default() {
            input.push_str(&command);
            input.push('\n');
            expected.push_str(if good { "accepted\n" } else { "rejected\n" });
        }
        Replay {
            input,
            expected,
            unread: self.0.core.replay_skipped,
            time: self.0.core.replay_time,
        }
    }
}

impl Core {
    pub(super) fn timed<X>(&mut self, f: impl FnOnce(&mut Self) -> X) -> X {
        let start = std::time::Instant::now();
        let x = f(self);
        self.replay_time += start.elapsed();
        x
    }

    pub(super) fn record(&mut self, input: Option<String>, good: bool) {
        if let Some(trace) = &mut self.replay {
            if let Some(input) = input {
                trace.push((input, good));
            } else {
                self.replay_skipped += 1;
            }
        }
    }
}

pub(super) fn term(t: &Tm) -> String {
    match t {
        BVar(i) => format!("b {i}"),
        FVar(x) => format!("f {x}"),
        Sort(s) => format!("s {}", sort(s)),
        Const(n) => format!("c {n}"),
        Pi(_, a, b) => format!("p {} {}", term(a), term(b)),
        Lam(_, b) => format!("l {}", term(b)),
        App(f, a) => format!("a {} {}", term(f), term(a)),
        Lit(n) => {
            let mut n = *n;
            let mut ds = Vec::new();
            while n != 0 {
                ds.push((n & 65535).to_string());
                n >>= 16;
            }
            if ds.is_empty() {
                "n 0".into()
            } else {
                format!("n {} {}", ds.len(), ds.join(" "))
            }
        }
    }
}

fn sort(s: &crate::check::Sort) -> String {
    match s {
        crate::check::Sort::Prop => "P".into(),
        crate::check::Sort::Type(l) => {
            let vars: Vec<_> = l.terms().collect();
            let mut out = format!(
                "T {} {}",
                l.as_const().or(l.constant_floor()).unwrap_or(0),
                vars.len()
            );
            for (v, n) in vars {
                out.push_str(&format!(" {v} {n}"));
            }
            out
        }
    }
}

pub(super) fn encode_decl(
    c: &Core,
    name: &str,
    ty: &T,
    value: Option<&T>,
    transparent: bool,
) -> Option<String> {
    let ty = term(&c.read(ty).ok()?);
    let value = match value {
        None => "0".into(),
        Some(v) => format!("1 {}", term(&c.read(v).ok()?)),
    };
    Some(format!("D {name} {ty} {value} {}", u8::from(transparent)))
}

pub(super) fn encode_inductive(
    c: &Core,
    fams: &[FamSpec],
    np: usize,
    out: &crate::check::Sort,
) -> Option<String> {
    let mut reading = Core::new();
    reading.globals = c.globals.clone();
    reading.names = c.names.clone();
    let mut types = Vec::new();
    for f in fams {
        let ty = reading.read(&f.ty).ok()?;
        types.push(ty.clone());
        reading
            .globals
            .insert(reading.names.register(&f.name), Global { ty, value: None });
    }
    let mut text = format!("I {np} {} {}", sort(out), fams.len());
    for (f, ty) in fams.iter().zip(types) {
        text.push_str(&format!(" {} {} {}", f.name, term(&ty), f.ctors.len()));
        for (name, ty) in &f.ctors {
            text.push_str(&format!(" {name} {}", term(&reading.read(ty).ok()?)));
        }
    }
    Some(text)
}
