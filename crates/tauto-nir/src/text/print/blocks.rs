//! A function in block form as text (`blocks { … }`): the blocks in the
//! order they are numbered, then the regions with the nodes they came from,
//! the places a `match` tests a union's variant, and the bodies of the
//! closures.
//!
//! Every leaf is written on its own, with each local read as `copy plain x#1:
//! T`-style explicit as the text of a lone expression is, so reading a block
//! needs no other block.

use super::*;
use crate::blocks::{BBlock, BlockFn, Edge, EdgeKind, Inst, Region, Shell, Slot, Term, Value};
use crate::decision::Case;

/// `f` with the body `bf` as text: what `parse_blocks` reads.
pub fn print_blocks(pkg: &Package, f: &FnInst, bf: &BlockFn) -> Result<String, String> {
    let mut p = Printer::new(pkg);
    p.head(f);
    p.s(" = blocks {");
    p.indent += 1;
    p.block_fn(bf)?;
    p.indent -= 1;
    p.line();
    p.s("}");
    Ok(p.out)
}

impl Printer<'_> {
    /// A local where it is bound, with no memory of it kept.
    fn binder(&mut self, l: &Local) {
        if l.repr != Repr::Plain {
            self.s(repr_word(l.repr));
            self.s(" ");
        }
        self.local_name(l);
    }

    fn typed_binders(&mut self, ls: &[(Local, Ty)]) {
        self.s("(");
        for (i, (l, t)) in ls.iter().enumerate() {
            if i > 0 {
                self.s(", ");
            }
            self.binder(l);
            self.s(": ");
            self.ty(t);
        }
        self.s(")");
    }

    fn path(&mut self, path: &[usize]) {
        self.s("[");
        for (i, n) in path.iter().enumerate() {
            if i > 0 {
                self.s(", ");
            }
            write!(self.out, "{n}").unwrap();
        }
        self.s("]");
    }

    /// A leaf on its own: the locals it reads that it does not bind itself
    /// are written with their representation and type.
    fn leaf(&mut self, e: &Expr) -> R {
        let mut lone = Printer::new(self.pkg);
        lone.indent = self.indent;
        lone.expr(e)?;
        self.out.push_str(&lone.out);
        Ok(())
    }

    fn value(&mut self, v: &Value) -> R {
        match v {
            Value::Leaf(e) => self.leaf(e),
            Value::Region(r) => {
                write!(self.out, "%{r}").unwrap();
                Ok(())
            }
        }
    }

    fn block_fn(&mut self, bf: &BlockFn) -> R {
        for (i, b) in bf.blocks.iter().enumerate() {
            self.line();
            self.bblock(i, b)?;
        }
        if !bf.regions.is_empty() {
            self.line();
            self.s("regions {");
            self.indent += 1;
            for (i, r) in bf.regions.iter().enumerate() {
                self.line();
                write!(self.out, "region{i} = ").unwrap();
                match r {
                    None => self.s("none"),
                    Some(r) => self.region(r)?,
                }
                self.s(";");
            }
            self.indent -= 1;
            self.line();
            self.s("}");
        }
        for (r, path) in &bf.variants {
            self.line();
            write!(self.out, "variant region{r} ").unwrap();
            self.path(path);
            self.s(";");
        }
        self.line();
        write!(
            self.out,
            "counts opaque {} refutable {};",
            bf.opaque, bf.refutable
        )
        .unwrap();
        for (i, c) in bf.closures.iter().enumerate() {
            self.line();
            write!(self.out, "closure {i} {{").unwrap();
            self.indent += 1;
            self.block_fn(c)?;
            self.indent -= 1;
            self.line();
            self.s("}");
        }
        Ok(())
    }

    fn region(&mut self, r: &Region) -> R {
        match &r.shell {
            Shell::Node(e) => {
                self.s("node ");
                self.leaf(e)?;
            }
            Shell::Block { ty, .. } => {
                self.s("block ");
                self.ty(ty);
            }
            Shell::Call(e) => {
                self.s("call ");
                self.leaf(e)?;
            }
            Shell::While { tick, .. } => {
                self.s("while");
                self.tick(*tick);
            }
        }
        self.s(" slots(");
        for (i, s) in r.slots.iter().enumerate() {
            if i > 0 {
                self.s(", ");
            }
            match s {
                Slot::Operand(v) => {
                    self.s("operand ");
                    self.value(v)?;
                }
                Slot::Body(b) => write!(self.out, "body b{b}").unwrap(),
            }
        }
        self.s(")");
        Ok(())
    }

    fn bblock(&mut self, i: usize, b: &BBlock) -> R {
        write!(self.out, "b{i}").unwrap();
        self.typed_binders(&b.params);
        if let Some(t) = &b.param {
            self.s(" -> ");
            self.ty(t);
        }
        if let Some(o) = b.owner {
            write!(self.out, " owner region{o}").unwrap();
        }
        if let Some(j) = b.join_of {
            write!(self.out, " joins region{j}").unwrap();
        }
        self.s(":");
        self.indent += 1;
        for inst in &b.insts {
            self.line();
            self.block_inst(inst)?;
            self.s(";");
        }
        self.line();
        self.term(&b.term)?;
        self.s(";");
        self.indent -= 1;
        Ok(())
    }

    fn block_inst(&mut self, inst: &Inst) -> R {
        match inst {
            Inst::Let {
                local,
                ty,
                init,
                stack,
                ..
            } => {
                self.s(if *stack { "let stack " } else { "let " });
                self.binder(local);
                self.s(": ");
                self.ty(ty);
                self.s(" := ");
                self.value(init)?;
            }
            Inst::Var {
                local, ty, init, ..
            } => {
                self.s("var ");
                self.binder(local);
                self.s(": ");
                self.ty(ty);
                self.s(" := ");
                self.value(init)?;
            }
            Inst::Assign { target, value, .. } => {
                self.s("set ");
                let mut lone = Printer::new(self.pkg);
                lone.place(target);
                self.out.push_str(&lone.out);
                self.s(" := ");
                self.value(value)?;
            }
            Inst::Eval(v) => {
                self.s("eval ");
                self.value(v)?;
            }
            Inst::Bind {
                local,
                ty,
                path,
                borrow,
            } => {
                self.s("bind ");
                self.binder(local);
                self.s(": ");
                self.ty(ty);
                self.s(if *borrow { " := borrow part " } else { " := part " });
                self.path(path);
            }
            Inst::Unpack { path, last } => {
                self.s("unpack ");
                self.path(path);
                if *last {
                    self.s(" last");
                }
            }
            Inst::End(l) => {
                self.s("end ");
                self.binder(l);
            }
            Inst::Release { path } => {
                self.s("release ");
                self.path(path);
            }
            Inst::Open(r) => write!(self.out, "open region{r}").unwrap(),
            Inst::Close(r, v) => {
                write!(self.out, "close region{r}").unwrap();
                if let Some(v) = v {
                    self.s(" with ");
                    self.value(v)?;
                }
            }
        }
        Ok(())
    }

    fn case(&mut self, c: &Case) {
        match c {
            Case::Ctor { index, arity } => write!(self.out, "ctor({index}, {arity})").unwrap(),
            Case::Int(n) => write!(self.out, "int({n})").unwrap(),
            Case::Nat(n) => write!(self.out, "nat({n})").unwrap(),
            Case::Bool(b) => write!(self.out, "bool({b})").unwrap(),
            Case::Text(s) => write!(self.out, "text({s:?})").unwrap(),
            Case::Variant(i) => write!(self.out, "variant({i})").unwrap(),
        }
    }

    fn edge(&mut self, e: &Edge) {
        self.s(match e.kind {
            EdgeKind::Body => "body",
            EdgeKind::Ret => "ret",
            EdgeKind::Direct => "direct",
            EdgeKind::Abort => "abort",
            EdgeKind::Susp => "susp",
        });
        if let Some(op) = e.op {
            write!(self.out, "({op})").unwrap();
        }
        write!(self.out, " => b{} params", e.entry).unwrap();
        self.typed_binders(&e.params);
        if e.refutable {
            self.s(" refutable");
        }
    }

    fn term(&mut self, t: &Term) -> R {
        match t {
            Term::Jump(b, v) => {
                write!(self.out, "jump b{b}(").unwrap();
                self.value(v)?;
                self.s(")");
            }
            Term::Goto(b) => write!(self.out, "goto b{b}").unwrap(),
            Term::Control {
                region,
                succs,
                join,
            } => {
                write!(self.out, "control region{region} to [").unwrap();
                for (i, b) in succs.iter().enumerate() {
                    if i > 0 {
                        self.s(", ");
                    }
                    write!(self.out, "b{b}").unwrap();
                }
                write!(self.out, "] join b{join}").unwrap();
            }
            Term::Enter {
                region,
                entry,
                join,
                by_ref,
            } => {
                write!(self.out, "enter region{region} at b{entry} join b{join}").unwrap();
                if *by_ref {
                    self.s(" by_ref");
                }
            }
            Term::Test {
                path,
                cases,
                default,
            } => {
                self.s("test ");
                self.path(path);
                self.s(" {");
                for (i, (c, b)) in cases.iter().enumerate() {
                    self.s(if i == 0 { " " } else { ", " });
                    self.case(c);
                    write!(self.out, " => b{b}").unwrap();
                }
                if let Some(d) = default {
                    self.s(if cases.is_empty() { " " } else { ", " });
                    write!(self.out, "_ => b{d}").unwrap();
                }
                self.s(" }");
            }
            Term::Handle {
                region,
                edges,
                join,
            } => {
                write!(self.out, "handle region{region} {{").unwrap();
                self.indent += 1;
                for e in edges {
                    self.line();
                    self.edge(e);
                    self.s(",");
                }
                self.indent -= 1;
                self.line();
                write!(self.out, "}} join b{join}").unwrap();
            }
            Term::Call {
                region,
                abort,
                join,
            } => write!(self.out, "call region{region} to b{join} abort b{abort}").unwrap(),
            Term::Suspend {
                region,
                abort,
                join,
                resumes,
                env,
            } => {
                write!(self.out, "suspend region{region} to b{join} abort b{abort} ").unwrap();
                self.s(match resumes {
                    crate::effects::Resumes::Never => "never",
                    crate::effects::Resumes::Once => "once",
                    crate::effects::Resumes::Many => "many",
                });
                self.s(" env");
                self.typed_binders(env);
            }
            Term::Abort => self.s("abort"),
            Term::Decline => self.s("decline"),
            Term::Branch { value, then, els } => {
                self.s("branch ");
                self.value(value)?;
                write!(self.out, " then b{then}").unwrap();
                if let Some(e) = els {
                    write!(self.out, " else b{e}").unwrap();
                }
            }
            Term::Unreachable => self.s("unreachable"),
            Term::Return { value, cont, .. } => {
                self.s("return");
                if let Some(v) = value {
                    self.s(" ");
                    self.value(v)?;
                }
                write!(self.out, " cont b{cont}").unwrap();
            }
            Term::Done(v) => {
                self.s("done ");
                self.value(v)?;
            }
            Term::Pending => self.s("pending"),
        }
        Ok(())
    }
}
