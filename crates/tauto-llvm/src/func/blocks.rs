//! The control flow of a function, written from its blocks.
//!
//! A function is lowered to the blocks of `tauto_nir::blocks` (`BlockFn`):
//! each block becomes a block of the LLVM function, its instructions
//! (`let`, `var`, an assignment, a pattern's binding, the end of a taken
//! value) are written in order, and its terminator is the branch, the test,
//! the call or the return that ends it. What a region (an `if`, a `match`, a
//! call, a `handle`) makes arrives at the block where its parts meet: from the
//! slot the parts store it in, or, for a call, directly.
//!
//! What stays as the tree reads it: the operands (leaves with no control
//! flow in them) are written by `Fun::expr`, and the part of a `match`
//! that takes a value apart by `Fun::unpack`.

use std::collections::{BTreeSet, HashMap};
use std::rc::Rc;

use tauto_nir::blocks::{
    self as nb, BBlock, BlockFn, BlockId, EdgeKind, Inst, RegionId, Shell, Term, Value,
};

use super::*;

/// A `match` being written: what its blocks need of it.
pub(super) struct MatchCx {
    node: MatchNode,
    /// The scrutinee's address and type.
    root: (String, Ty),
    /// The entry of each arm.
    arms: Vec<BlockId>,
}

impl MatchCx {
    /// Whether the arm takes nothing out of the scrutinee: the `match` is
    /// on a borrow, or the scrutinee is a local the arm binds no owned part
    /// of, which the arm then still owns whole (`ownership`).
    fn lends(&self, arm: usize) -> bool {
        if self.node.by_ref {
            return true;
        }
        let mut binds = Vec::new();
        ownership::bound(&self.node.arms[arm].pat, &mut binds);
        binds.is_empty() && ownership::scrutinee_local(&self.node).is_some()
    }
}

/// A `handle` being written: where the value of its body goes, and what is
/// done once the body has ended.
pub(super) struct HandleCx {
    /// Where the body's value is kept until the body has ended.
    value: String,
    /// The label the end of the body goes to.
    done: String,
    /// The block the code at `done` goes on to: the return arm, or where the
    /// parts of the `handle` meet.
    after: BlockId,
    /// The saved chain of handlers, and the arms put on it.
    saved: String,
    arms: Vec<Val>,
    /// The type of the body's value.
    body_ty: Ty,
    ret: Option<Pat>,
    /// The `handle`'s own type.
    ty: Ty,
    region: RegionId,
    join: BlockId,
}

/// What `Fun` keeps for the blocks it writes.
pub(super) struct Graph {
    pub bf: Rc<BlockFn>,
    /// The type of what each region makes.
    rty: HashMap<RegionId, Ty>,
    labels: HashMap<BlockId, String>,
    /// Where the parts of a region store what it makes.
    rslot: HashMap<RegionId, String>,
    /// What a region has made, as words.
    rval: HashMap<RegionId, Val>,
    matches: HashMap<RegionId, MatchCx>,
    arm_entries: BTreeSet<BlockId>,
    /// What the tests made so far know of the scrutinee's parts, at the
    /// start of each block of a `match`'s decision.
    parts: HashMap<BlockId, Parts>,
    /// The `handle` each block that ends a body jumps out of.
    body_ends: HashMap<BlockId, RegionId>,
    handles: HashMap<RegionId, HandleCx>,
    /// The blocks the code at the end of a body goes before.
    after: HashMap<BlockId, RegionId>,
    /// The paths of the constructors `Unpack` has taken apart in the arm
    /// being written.
    unpacked: Vec<Path>,
}

impl Graph {
    pub fn new(bf: Rc<BlockFn>) -> Graph {
        let mut rty = HashMap::new();
        for b in &bf.blocks {
            if let (Some(r), Some(t)) = (b.join_of, &b.param) {
                rty.insert(r, t.clone());
            }
        }
        for (r, reg) in bf.regions.iter().enumerate() {
            if let Some(Shell::Block { ty, .. }) = reg.as_ref().map(|x| &x.shell) {
                rty.insert(r, ty.clone());
            }
        }
        Graph {
            bf,
            rty,
            labels: HashMap::new(),
            rslot: HashMap::new(),
            rval: HashMap::new(),
            matches: HashMap::new(),
            arm_entries: BTreeSet::new(),
            parts: HashMap::new(),
            body_ends: HashMap::new(),
            handles: HashMap::new(),
            after: HashMap::new(),
            unpacked: Vec::new(),
        }
    }
}

/// The blocks a block goes on to in the function being written. A `handle`'s
/// operation arms are functions of their own; the code that ends its body
/// goes on to its return arm, or to where its parts meet.
fn next(bf: &BlockFn, b: BlockId) -> Vec<BlockId> {
    match &bf.blocks[b].term {
        Term::Jump(to, _) | Term::Goto(to) => vec![*to],
        Term::Branch { then, els, .. } => std::iter::once(*then).chain(*els).collect(),
        Term::Call { join, .. } | Term::Suspend { join, .. } => vec![*join],
        Term::Enter { entry, .. } => vec![*entry],
        Term::Test { cases, default, .. } => cases
            .iter()
            .map(|(_, b)| *b)
            .chain(default.iter().copied())
            .collect(),
        Term::Control {
            region,
            succs,
            join,
        } => {
            let mut v = succs.clone();
            // An `if` without `else`, `&&` and `||` reach their join
            // directly too.
            if let Some(Shell::Node(e)) = bf.regions[*region].as_ref().map(|r| &r.shell) {
                match &e.kind {
                    ExprKind::If { .. } if succs.len() < 2 => v.push(*join),
                    ExprKind::And(..) | ExprKind::Or(..) => v.push(*join),
                    _ => {}
                }
            }
            v
        }
        Term::Handle { edges, join, .. } => {
            let mut v: Vec<BlockId> = edges
                .iter()
                .filter(|e| matches!(e.kind, EdgeKind::Body | EdgeKind::Ret))
                .map(|e| arm_target(bf, e.entry))
                .collect();
            if !edges.iter().any(|e| e.kind == EdgeKind::Ret) {
                v.push(*join);
            }
            v
        }
        Term::Return { .. }
        | Term::Done(_)
        | Term::Abort
        | Term::Unreachable
        | Term::Decline
        | Term::Pending => Vec::new(),
    }
}

/// Where an arm of a `handle` goes on once what it is given is taken: the
/// decision on the arguments (tests, names bound) ends in a `goto` there.
pub(super) fn arm_target(bf: &BlockFn, entry: BlockId) -> BlockId {
    let mut b = entry;
    loop {
        match &bf.blocks[b].term {
            Term::Goto(t) => return *t,
            Term::Test { cases, default, .. } => {
                match cases.first().map(|(_, x)| *x).or(*default) {
                    Some(x) => b = x,
                    None => return b,
                }
            }
            _ => return b,
        }
    }
}

/// The blocks reached from `entry`, each after the blocks that reach it
/// (reverse post-order). A jump to `stop` leaves the graph.
pub(super) fn reachable(bf: &BlockFn, entry: BlockId, stop: Option<BlockId>) -> Vec<BlockId> {
    let succ = |b: BlockId| -> Vec<BlockId> {
        next(bf, b)
            .into_iter()
            .filter(|n| Some(*n) != stop)
            .collect()
    };
    let mut seen = vec![false; bf.blocks.len()];
    let mut post = Vec::new();
    let mut stack = vec![(entry, succ(entry))];
    seen[entry] = true;
    while let Some((b, rest)) = stack.last_mut() {
        match rest.pop() {
            Some(n) if !seen[n] => {
                seen[n] = true;
                let ns = succ(n);
                stack.push((n, ns));
            }
            Some(_) => {}
            None => {
                post.push(*b);
                stack.pop();
            }
        }
    }
    post.reverse();
    post
}

/// Whether any block of the graph from `entry` ends a `handle`.
pub(super) fn has_handle(bf: &BlockFn, entry: BlockId, stop: Option<BlockId>) -> bool {
    reachable(bf, entry, stop)
        .into_iter()
        .any(|b| matches!(bf.blocks[b].term, Term::Handle { .. }))
}

/// The pattern's constructors by path, for the parts of the value it
/// matches.
fn ctors_of(p: &Pat, at: &mut Path, out: &mut HashMap<Path, usize>) {
    match p {
        Pat::Ctor { ctor, fields } => {
            out.insert(at.clone(), ctor.index);
            for (i, f) in fields.iter().enumerate() {
                at.push(i);
                ctors_of(f, at, out);
                at.pop();
            }
        }
        Pat::Variant { pat, .. } => {
            at.push(0);
            ctors_of(pat, at, out);
            at.pop();
        }
        _ => {}
    }
}

/// The sub-pattern of `p` at `path`.
fn pat_at<'a>(p: &'a Pat, path: &[usize]) -> Option<&'a Pat> {
    let Some((first, rest)) = path.split_first() else {
        return Some(p);
    };
    match p {
        Pat::Ctor { fields, .. } => pat_at(fields.get(*first)?, rest),
        Pat::Variant { pat, .. } => pat_at(pat, rest),
        _ => None,
    }
}

impl<'p> Fun<'_, 'p> {
    /// The type of a value of the blocks.
    fn value_ty(&self, v: &Value) -> Ty {
        match v {
            Value::Leaf(e) => e.ty.clone(),
            Value::Region(r) => self.g.rty.get(r).cloned().unwrap_or(Ty::Unit),
        }
    }

    /// The words of a value of the blocks, and its type.
    fn value(&mut self, v: &Value) -> R<(Val, Ty)> {
        match v {
            Value::Leaf(e) => Ok((self.expr(e)?, e.ty.clone())),
            Value::Region(r) => match self.g.rval.get(r) {
                Some(v) => Ok((v.clone(), self.value_ty(&Value::Region(*r)))),
                None => refuse("internal: a region read before it made its value"),
            },
        }
    }

    /// The value of an operand of an operator: the value itself, or the
    /// value a borrow stands for.
    fn operand_value(&mut self, v: &Value) -> R<(Val, Ty)> {
        let (val, t) = self.value(v)?;
        match borrowed(&t) {
            Some(inner) => {
                let inner = inner.clone();
                let p = self.b.ptr(&val[0]);
                let n = self.words(&inner)?;
                Ok((self.b.load(&p, 0, n), inner))
            }
            None => Ok((val, t)),
        }
    }

    /// The slot where the parts of a region store what it makes.
    fn region_slot(&mut self, r: RegionId) -> R<String> {
        if let Some(s) = self.g.rslot.get(&r) {
            return Ok(s.clone());
        }
        let ty = self.g.rty.get(&r).cloned().unwrap_or(Ty::Unit);
        let n = self.words(&ty)?;
        let s = self.b.alloca(n);
        self.g.rslot.insert(r, s.clone());
        Ok(s)
    }

    /// Writes the blocks reached from `entry` as the rest of the function
    /// being written. A jump to `stop` returns its value from the function.
    pub(super) fn emit_graph(&mut self, entry: BlockId, stop: Option<BlockId>) -> R<()> {
        let bf = self.g.bf.clone();
        let order = reachable(&bf, entry, stop);
        for &b in &order {
            let l = self.b.label();
            self.g.labels.insert(b, l);
        }
        for &b in &order {
            // The code that ends a `handle`'s body comes before the block it
            // goes on to.
            if let Some(r) = self.g.after.get(&b).copied() {
                self.end_of_body(r)?;
            }
            if b != entry {
                let l = self.g.labels[&b].clone();
                self.b.start(&l);
            }
            self.block(&bf, b, stop)?;
        }
        Ok(())
    }

    fn label(&self, b: BlockId) -> R<String> {
        match self.g.labels.get(&b) {
            Some(l) => Ok(l.clone()),
            None => refuse("internal: a jump out of the blocks being written"),
        }
    }

    fn block(&mut self, bf: &Rc<BlockFn>, b: BlockId, stop: Option<BlockId>) -> R<()> {
        let blk = &bf.blocks[b];
        if let Some(r) = blk.join_of
            && let Some(slot) = self.g.rslot.get(&r).cloned()
        {
            let ty = self.g.rty.get(&r).cloned().unwrap_or(Ty::Unit);
            let n = self.words(&ty)?;
            let v = self.b.load(&slot, 0, n);
            self.g.rval.insert(r, v);
        }
        if blk.insts.iter().any(|i| matches!(i, Inst::Unpack { .. })) {
            self.g.unpacked.clear();
        }
        for inst in &blk.insts {
            self.inst(bf, b, inst)?;
        }
        self.term(bf, b, blk, stop)
    }

    fn inst(&mut self, bf: &Rc<BlockFn>, b: BlockId, inst: &Inst) -> R<()> {
        match inst {
            Inst::Let {
                local, ty, init, ..
            }
            | Inst::Var {
                local, ty, init, ..
            } => {
                let (v, from) = self.value(init)?;
                self.bind(local, ty, v, &from)
            }
            Inst::Assign { target, value, .. } => {
                if target.path.iter().any(|f| f.indirect == Indirect::Shared) {
                    return refuse("an assignment through a shared field");
                }
                let (v, from) = self.value(value)?;
                let (p, t) = self.place_of(target)?;
                let v = self.coerce(v, &from, &t)?;
                self.b.store(&p, 0, &v);
                Ok(())
            }
            Inst::Eval(v) => {
                self.value(v)?;
                Ok(())
            }
            Inst::Open(_) => Ok(()),
            Inst::Close(r, v) => {
                let ty = self.g.rty.get(r).cloned().unwrap_or(Ty::Unit);
                let val = match v {
                    Some(v) => {
                        let (x, from) = self.value(v)?;
                        self.coerce(x, &from, &ty)?
                    }
                    None => {
                        let n = self.words(&ty)?;
                        vec!["0".to_string(); n]
                    }
                };
                self.g.rval.insert(*r, val);
                Ok(())
            }
            Inst::Bind {
                local, ty, path, ..
            } => self.bind_part(b, local, ty, path),
            Inst::Unpack { path, .. } => self.unpack_at(bf, b, path),
            // A name that was bound for a guard owned nothing; an argument
            // no name takes was ended with the pattern.
            Inst::End(_) | Inst::Release { .. } => Ok(()),
        }
    }

    /// The match a block of a `match` belongs to.
    fn match_of(&self, bf: &BlockFn, b: BlockId) -> Option<RegionId> {
        let mut r = bf.blocks[b].owner;
        while let Some(x) = r {
            if self.g.matches.contains_key(&x) {
                return Some(x);
            }
            // Blocks of a guard are owned by the regions the guard has.
            r = bf
                .blocks
                .iter()
                .find(|c| c.join_of == Some(x))
                .and_then(|c| c.owner);
        }
        None
    }

    /// A local takes the part of the scrutinee at `path`.
    fn bind_part(&mut self, b: BlockId, local: &Local, ty: &Ty, path: &Path) -> R<()> {
        let bf = self.g.bf.clone();
        let Some(r) = self.match_of(&bf, b) else {
            return refuse("internal: a binding outside a match");
        };
        let by_ref = {
            let cx = &self.g.matches[&r];
            let arm = (0..cx.node.arms.len()).find(|i| {
                let mut ps = Vec::new();
                pat_binders(&cx.node.arms[*i].pat, &mut ps);
                ps.iter().any(|l| l.id == local.id)
            });
            match arm {
                Some(a) => cx.lends(a),
                None => cx.node.by_ref,
            }
        };
        let mut parts = self.g.parts.remove(&b).unwrap_or_default();
        if parts.at.is_empty() {
            parts.at.insert(Vec::new(), self.g.matches[&r].root.clone());
        }
        let (p, t) = self.part(&mut parts, path)?;
        self.g.parts.insert(b, parts);
        if local.storage().is_borrow() {
            let w = self.b.word(&p);
            let from = match local.storage() {
                Storage::BorrowMut => Ty::RefMut(Box::new(t.clone())),
                _ => Ty::Ref(Box::new(t.clone())),
            };
            return self.bind(local, ty, vec![w], &from);
        }
        let n = self.words(&t)?;
        let v = self.b.load(&p, 0, n);
        // A `match` on a borrow lends its parts: each name holds a copy. A
        // `match` on a value gives the part to the name, which owns it from
        // the `unpack` that covers it (until then it is shared with the
        // scrutinee, which the name may copy but not move).
        let v = if by_ref { self.dup(v, &t)? } else { v };
        self.bind(local, ty, v, &t)
    }

    /// The constructor at `path` of the scrutinee ends: the names bound to its
    /// parts own them from here.
    fn unpack_at(&mut self, bf: &Rc<BlockFn>, b: BlockId, path: &Path) -> R<()> {
        // A constructor inside one that was taken apart is done with it.
        if self.g.unpacked.iter().any(|p| path.starts_with(p)) {
            return Ok(());
        }
        // The names of an operation arm's pattern were bound with it.
        let Some(r) = self.match_of(bf, b) else {
            return Ok(());
        };
        let (pat, root) = {
            let cx = &self.g.matches[&r];
            let Some(arm) = cx.arms.iter().position(|e| *e == b) else {
                return refuse("internal: an unpack outside the entry of an arm");
            };
            (cx.node.arms[arm].pat.clone(), cx.root.clone())
        };
        let Some(sub) = pat_at(&pat, path) else {
            return refuse("internal: an unpack of a part the pattern does not have");
        };
        let mut parts = Parts::default();
        parts.at.insert(Vec::new(), root);
        ctors_of(&pat, &mut Vec::new(), &mut parts.ctor);
        let (p, t) = self.part(&mut parts, &path.clone())?;
        self.unpack(sub, &p, &t, false, true)?;
        self.g.unpacked.push(path.clone());
        Ok(())
    }

    /// What `pattern` does for a part of a value taken apart, with the names
    /// already bound: the parts nothing names end, and a part that something
    /// else still holds (a box shared with another) is copied by the names.
    fn unpack(&mut self, pat: &Pat, p: &str, t: &Ty, by_ref: bool, owned: bool) -> R<()> {
        match pat {
            Pat::Variant { .. } => refuse("a union"),
            Pat::Wild | Pat::Int(_) | Pat::Nat(_) | Pat::Bool(_) | Pat::Text(_) => {
                if !by_ref && owned {
                    glue::call(self.m, &mut self.b, Glue::Drop, p, t)?;
                }
                Ok(())
            }
            Pat::Bind(local, _) => {
                if local.storage().is_borrow() || !(by_ref || !owned) {
                    return Ok(());
                }
                // The name holds what the part holds: it makes the words its
                // own.
                let (slot, _) = self.slot(local)?;
                let n = self.words(t)?;
                let v = self.b.load(&slot, 0, n);
                let v = self.dup(v, t)?;
                self.b.store(&slot, 0, &v);
                Ok(())
            }
            Pat::Ctor { ctor, fields } => {
                let Some((tagged, cs)) = ctors(layout::shape(self.m.pkg, t)?) else {
                    return refuse(format!("internal: a constructor pattern on a {t:?}"));
                };
                let Some(c) = cs.get(if tagged { ctor.index } else { 0 }) else {
                    return refuse("internal: a pattern of a constructor the type does not have");
                };
                for (i, sub) in fields.iter().enumerate() {
                    let Some(f) = c.fields.get(i) else {
                        return refuse(
                            "internal: a pattern of a field the constructor does not have",
                        );
                    };
                    let at = field_at(self.m, &mut self.b, p, tagged, &c.fields, i)?;
                    let (q, ty) = self.through(at.content.clone(), f.ty.clone())?;
                    let lent = by_ref || borrowed(&f.ty).is_some();
                    match (&at.boxed, f.indirect) {
                        (Some(boxed), Indirect::Shared) if !lent && owned => {
                            let rc = self.b.def(format!("load i64, ptr {boxed}"));
                            let last = self.b.def(format!("icmp eq i64 {rc}, 1"));
                            let (free, keep, done) =
                                (self.b.label(), self.b.label(), self.b.label());
                            self.b.condbr(&last, &free, &keep);
                            self.b.start(&free);
                            self.unpack(sub, &q, &ty, false, true)?;
                            self.b.ins(format!("call void @rt_free(ptr {boxed})"));
                            self.b.br(&done);
                            self.b.start(&keep);
                            let less = self.b.def(format!("sub i64 {rc}, 1"));
                            self.b.ins(format!("store i64 {less}, ptr {boxed}"));
                            self.unpack(sub, &q, &ty, false, false)?;
                            self.b.start(&done);
                        }
                        (Some(boxed), Indirect::Unique) if !lent && owned => {
                            self.unpack(sub, &q, &ty, false, true)?;
                            self.b.ins(format!("call void @rt_free(ptr {boxed})"));
                        }
                        _ => self.unpack(sub, &q, &ty, lent, owned)?,
                    }
                }
                Ok(())
            }
        }
    }

    /// Passes what the tests of a `match` know to the blocks that follow.
    fn pass_parts(&mut self, from: BlockId, to: &[BlockId]) {
        let Some(parts) = self.g.parts.get(&from).cloned() else {
            return;
        };
        for t in to {
            if !self.g.arm_entries.contains(t) {
                self.g.parts.entry(*t).or_insert_with(|| parts.clone());
            }
        }
    }

    /// Stores what a jump gives to the block where the parts of a region
    /// meet, then goes there.
    fn jump(
        &mut self,
        bf: &BlockFn,
        b: BlockId,
        to: BlockId,
        v: &Value,
        stop: Option<BlockId>,
    ) -> R<()> {
        if Some(to) == stop {
            let (x, from) = self.value(v)?;
            let ret = self.ret.clone();
            let x = self.coerce(x, &from, &ret)?;
            self.ret(&x);
            return Ok(());
        }
        // The end of a `handle`'s body.
        if let Some(r) = self.g.body_ends.get(&b).copied()
            && self.g.handles[&r].join == to
        {
            let (x, from) = self.value(v)?;
            let (slot, body_ty, done) = {
                let h = &self.g.handles[&r];
                (h.value.clone(), h.body_ty.clone(), h.done.clone())
            };
            let x = self.coerce(x, &from, &body_ty)?;
            self.b.store(&slot, 0, &x);
            self.b.br(&done);
            return Ok(());
        }
        if let Some(r) = bf.blocks[to].join_of {
            let ty = self.g.rty.get(&r).cloned().unwrap_or(Ty::Unit);
            let slot = self.region_slot(r)?;
            let (x, from) = self.value(v)?;
            let x = self.coerce(x, &from, &ty)?;
            self.b.store(&slot, 0, &x);
        } else {
            self.value(v)?;
        }
        let l = self.label(to)?;
        self.b.br(&l);
        self.pass_parts(b, &[to]);
        Ok(())
    }

    fn term(&mut self, bf: &Rc<BlockFn>, b: BlockId, blk: &BBlock, stop: Option<BlockId>) -> R<()> {
        match &blk.term {
            Term::Jump(to, v) => self.jump(bf, b, *to, v, stop),
            Term::Goto(to) => {
                let l = self.label(*to)?;
                self.b.br(&l);
                self.pass_parts(b, &[*to]);
                Ok(())
            }
            Term::Done(v) => {
                let (x, from) = self.value(v)?;
                let ret = self.ret.clone();
                let x = self.coerce(x, &from, &ret)?;
                self.ret(&x);
                Ok(())
            }
            Term::Return { value, .. } => {
                let ret = self.ret.clone();
                let v = match value {
                    Some(v) => {
                        let (x, from) = self.value(v)?;
                        self.coerce(x, &from, &ret)?
                    }
                    None => Vec::new(),
                };
                self.ret(&v);
                Ok(())
            }
            Term::Decline => refuse("an operation arm whose pattern may not fit"),
            Term::Unreachable => {
                self.fail("no arm matches");
                Ok(())
            }
            Term::Branch { value, then, els } => {
                let (c, _) = self.operand_value(value)?;
                let c = self.b.cond(&c[0]);
                let yes = self.label(*then)?;
                match els {
                    Some(e) => {
                        let no = self.label(*e)?;
                        self.b.condbr(&c, &yes, &no);
                    }
                    None => return refuse("an operation arm whose pattern may not fit"),
                }
                self.pass_parts(b, &[*then]);
                if let Some(e) = els {
                    self.pass_parts(b, &[*e]);
                }
                Ok(())
            }
            Term::Control {
                region,
                succs,
                join,
            } => self.control(bf, b, *region, succs, *join),
            Term::Call { region, join, .. } | Term::Suspend { region, join, .. } => {
                // The abort edge is not written: what stops a run here is
                // what `fail` ends it with.
                let reg = bf.regions[*region].as_ref().expect("a region");
                let Shell::Call(e) = &reg.shell else {
                    return refuse("internal: a call region without its call");
                };
                let v = self.expr(e)?;
                let ty = self.g.rty.get(region).cloned().unwrap_or(Ty::Unit);
                let v = self.coerce(v, &e.ty, &ty)?;
                self.g.rval.insert(*region, v);
                let l = self.label(*join)?;
                self.b.br(&l);
                self.pass_parts(b, &[*join]);
                Ok(())
            }
            Term::Enter {
                region,
                entry,
                join: _,
                by_ref: _,
            } => self.enter_match(bf, b, *region, *entry),
            Term::Test {
                path,
                cases,
                default,
            } => self.test(bf, b, path, cases, default),
            Term::Handle {
                region,
                edges,
                join,
            } => self.handle_term(bf, b, *region, edges, *join),
            Term::Abort | Term::Pending => refuse("internal: a block with no end"),
        }
    }

    fn control(
        &mut self,
        bf: &Rc<BlockFn>,
        b: BlockId,
        region: RegionId,
        succs: &[BlockId],
        join: BlockId,
    ) -> R<()> {
        let reg = bf.regions[region].as_ref().expect("a region");
        let mut to = succs.to_vec();
        to.push(join);
        self.pass_parts(b, &to);
        let operand = |i: usize| match &reg.slots[i] {
            nb::Slot::Operand(v) => v.clone(),
            nb::Slot::Body(_) => unreachable!("an operand comes first"),
        };
        match &reg.shell {
            Shell::While { tick, .. } => {
                if *tick == Tick::Budget {
                    return refuse("a `budget`");
                }
                let head = self.label(succs[0])?;
                self.b.br(&head);
                Ok(())
            }
            Shell::Node(e) => match &e.kind {
                ExprKind::Budget(_) => refuse("a `budget`"),
                ExprKind::And(..) | ExprKind::Or(..) => {
                    let and = matches!(e.kind, ExprKind::And(..));
                    let out = self.region_slot(region)?;
                    let (first, _) = self.operand_value(&operand(0))?;
                    self.b.store(&out, 0, &first);
                    let c = self.b.cond(&first[0]);
                    let (more, done) = (self.label(succs[0])?, self.label(join)?);
                    if and {
                        self.b.condbr(&c, &more, &done);
                    } else {
                        self.b.condbr(&c, &done, &more);
                    }
                    Ok(())
                }
                ExprKind::If { .. } => {
                    self.region_slot(region)?;
                    let (c, _) = self.operand_value(&operand(0))?;
                    let c = self.b.cond(&c[0]);
                    let yes = self.label(succs[0])?;
                    let no = match succs.get(1) {
                        Some(o) => self.label(*o)?,
                        None => self.label(join)?,
                    };
                    self.b.condbr(&c, &yes, &no);
                    Ok(())
                }
                _ => refuse("internal: a control that is not written"),
            },
            _ => refuse("internal: a control that is not written"),
        }
    }

    /// A `match` starts: the scrutinee stays where it is; an arm takes its
    /// parts out of it or borrows them. A copy of a place is a value of its
    /// own.
    fn enter_match(
        &mut self,
        bf: &Rc<BlockFn>,
        b: BlockId,
        region: RegionId,
        entry: BlockId,
    ) -> R<()> {
        let reg = bf.regions[region].as_ref().expect("a region");
        let Shell::Node(Expr {
            kind: ExprKind::Match(m),
            ..
        }) = &reg.shell
        else {
            return refuse("internal: a match without its node");
        };
        let scrut = match &reg.slots[0] {
            nb::Slot::Operand(v) => v.clone(),
            nb::Slot::Body(_) => return refuse("internal: a match without its scrutinee"),
        };
        let mut node = (**m).clone();
        let (p, t) = match &scrut {
            Value::Leaf(e) => {
                node.scrut = e.clone();
                let copied = matches!(
                    &e.kind,
                    ExprKind::Read {
                        how: Use::Clone,
                        ..
                    } | ExprKind::Field {
                        how: Use::Clone,
                        ..
                    } | ExprKind::Deref {
                        how: Use::Clone,
                        ..
                    }
                );
                if copied {
                    let v = self.expr(e)?;
                    (self.temp(&v), e.ty.clone())
                } else {
                    self.place(e)?
                }
            }
            Value::Region(_) => {
                let (v, t) = self.value(&scrut)?;
                (self.temp(&v), t)
            }
        };
        // The entries of the arms, in the order the slots hold them.
        let mut arms = Vec::new();
        let mut guarded = Vec::new();
        let mut at = 1;
        for a in &node.arms {
            if a.guard.is_some() {
                at += 1;
            }
            let nb::Slot::Body(e) = &reg.slots[at] else {
                return refuse("internal: an arm without its entry");
            };
            arms.push(*e);
            guarded.push(a.guard.is_some());
            at += 1;
        }
        let cx = MatchCx {
            node,
            root: (p.clone(), t.clone()),
            arms,
        };
        for (i, g) in guarded.iter().enumerate() {
            if *g && !cx.lends(i) && !self.plain(&t)? {
                return refuse("a guard on a `match` that takes its value apart");
            }
        }
        self.region_slot(region)?;
        self.g.arm_entries.extend(cx.arms.iter().copied());
        self.g.matches.insert(region, cx);
        let mut parts = Parts::default();
        parts.at.insert(Vec::new(), (p, t));
        self.g.parts.insert(entry, parts);
        let l = self.label(entry)?;
        self.b.br(&l);
        let _ = b;
        Ok(())
    }

    /// Tests the part of the scrutinee at `path`: the first case it is goes
    /// on.
    fn test(
        &mut self,
        bf: &Rc<BlockFn>,
        b: BlockId,
        path: &Path,
        cases: &[(Case, BlockId)],
        default: &Option<BlockId>,
    ) -> R<()> {
        let Some(r) = self.match_of(bf, b) else {
            return refuse("internal: a test outside a match");
        };
        let mut parts = self.g.parts.remove(&b).unwrap_or_default();
        if parts.at.is_empty() {
            parts.at.insert(Vec::new(), self.g.matches[&r].root.clone());
        }
        let (p, t) = self.part(&mut parts, path)?;
        let untagged = matches!(layout::shape(self.m.pkg, &t)?, Shape::Pair(..));
        for (case, target) in cases {
            let (yes, no) = (self.label(*target)?, self.b.label());
            let mut inner = parts.clone();
            let want = match case {
                Case::Ctor { .. } if untagged => None,
                Case::Ctor { index, .. } => {
                    inner.ctor.insert(path.clone(), *index);
                    Some(index.to_string())
                }
                Case::Int(n) | Case::Nat(n) => {
                    if !matches!(
                        layout::shape(self.m.pkg, &t)?,
                        Shape::Scalar(Scalar::Int(..))
                    ) {
                        return refuse("a number pattern on a `Nat`");
                    }
                    Some(n.to_string())
                }
                Case::Bool(v) => Some(u8::from(*v).to_string()),
                Case::Variant(_) => return refuse("a union"),
                Case::Text(text) => {
                    let w = self.b.def(format!("load i64, ptr {p}"));
                    let x = self.b.ptr(&w);
                    let c = self.m.string(text);
                    let is = self.b.def(format!(
                        "call i1 @rt_text_is(ptr {x}, ptr {c}, i64 {})",
                        text.len()
                    ));
                    self.b.condbr(&is, &yes, &no);
                    None
                }
            };
            match want {
                Some(want) => {
                    let w = self.b.def(format!("load i64, ptr {p}"));
                    let c = self.b.def(format!("icmp eq i64 {w}, {want}"));
                    self.b.condbr(&c, &yes, &no);
                }
                None if matches!(case, Case::Text(_)) => {}
                None => self.b.br(&yes),
            }
            self.g.parts.entry(*target).or_insert(inner);
            self.b.start(&no);
        }
        match default {
            Some(d) => {
                let l = self.label(*d)?;
                self.b.br(&l);
                self.g.parts.entry(*d).or_insert(parts.clone());
            }
            None => self.fail("no arm matches"),
        }
        self.g.parts.insert(b, parts);
        Ok(())
    }

    /// A `handle`: its operation arms are put on the chain of handlers and
    /// its body runs here; the code that ends the body takes them off again.
    fn handle_term(
        &mut self,
        bf: &Rc<BlockFn>,
        b: BlockId,
        region: RegionId,
        edges: &[nb::Edge],
        join: BlockId,
    ) -> R<()> {
        let reg = bf.regions[region].as_ref().expect("a region");
        let Shell::Node(e) = &reg.shell else {
            return refuse("internal: a handle without its node");
        };
        let ExprKind::Handle(h) = &e.kind else {
            return refuse("internal: a handle without its node");
        };
        if !h.aborts.is_empty() {
            return refuse("a `handle` with an arm that does not resume");
        }
        if !h.susp.is_empty() || h.m || h.kept || h.detached {
            return refuse("a `handle` with an arm that keeps its continuation");
        }
        if !plain(h.body_tier) {
            return refuse("a `handle` whose body may stop");
        }
        let body_entry = edges
            .iter()
            .find(|x| x.kind == EdgeKind::Body)
            .map(|x| x.entry)
            .expect("a body");
        let ret_entry = edges
            .iter()
            .find(|x| x.kind == EdgeKind::Ret)
            .map(|x| x.entry);
        let arm_edges: Vec<&nb::Edge> = edges
            .iter()
            .filter(|x| x.kind == EdgeKind::Direct)
            .collect();
        let mut ops = Vec::new();
        for (a, edge) in h.direct.iter().zip(&arm_edges) {
            if ops.contains(&a.op) {
                return refuse("a `handle` with two arms of an operation");
            }
            ops.push(a.op);
            if a.guard.is_some() || !a.pats.iter().all(|p| self.irrefutable(p)) {
                return refuse("an operation arm whose pattern may not fit");
            }
            let returns = reachable(bf, arm_target(bf, edge.entry), Some(join))
                .into_iter()
                .any(|x| matches!(bf.blocks[x].term, Term::Return { .. }));
            if returns {
                return refuse("an operation arm that returns");
            }
        }
        let saved = self.b.def("load ptr, ptr @rt.ev");
        let mut entries = Vec::new();
        for (a, edge) in h.direct.iter().zip(&arm_edges) {
            let arm = self.arm_fn(h, a, arm_target(bf, edge.entry), join)?;
            // An entry of the chain: the next entry, the operation and the
            // arm.
            let entry = self.b.alloca(3);
            let top = self.b.def("load ptr, ptr @rt.ev");
            let next = self.b.word(&top);
            self.b
                .store(&entry, 0, &[next, a.op.to_string(), arm[0].clone()]);
            self.b.ins(format!("store ptr {entry}, ptr @rt.ev"));
            entries.push(arm);
        }
        // Where the body's value waits for the code that ends the body.
        let n = self.words(&h.body_ty)?;
        let value = self.b.alloca(n);
        let done = self.b.label();
        self.region_slot(region)?;
        let after = ret_entry.map(|e| arm_target(&bf, e)).unwrap_or(join);
        // The blocks of the body that end it.
        for x in reachable(bf, body_entry, Some(join)) {
            if matches!(&bf.blocks[x].term, Term::Jump(t, _) if *t == join) {
                self.g.body_ends.insert(x, region);
            }
        }
        self.g.after.insert(after, region);
        self.g.handles.insert(
            region,
            HandleCx {
                value,
                done,
                after,
                saved,
                arms: entries,
                body_ty: h.body_ty.clone(),
                ret: h.ret.as_ref().map(|r| r.pat.clone()),
                ty: e.ty.clone(),
                region,
                join,
            },
        );
        let l = self.label(body_entry)?;
        self.b.br(&l);
        let _ = b;
        Ok(())
    }

    /// The code that ends the body of a `handle`: it takes its operation
    /// arms off the chain, then goes on with the body's value to the return
    /// arm, or out of the `handle`.
    fn end_of_body(&mut self, r: RegionId) -> R<()> {
        let Some(h) = self.g.handles.remove(&r) else {
            return Ok(());
        };
        self.b.start(&h.done.clone());
        let n = self.words(&h.body_ty)?;
        let v = self.b.load(&h.value, 0, n);
        self.b.ins(format!("store ptr {}, ptr @rt.ev", h.saved));
        for arm in &h.arms {
            let ty = Ty::Fn(Box::new(FnTy {
                params: Vec::new(),
                ret: Ty::Unit,
                kind: Kind::Shared,
                tier: Tier::S,
            }));
            self.drop(arm, &ty)?;
        }
        match &h.ret {
            None => {
                let v = self.coerce(v, &h.body_ty, &h.ty)?;
                let slot = self.region_slot(h.region)?;
                self.b.store(&slot, 0, &v);
            }
            Some(pat) => {
                let p = self.temp(&v);
                self.pattern(pat, &p, &h.body_ty, false, true)?;
            }
        }
        let l = self.label(h.after)?;
        self.b.br(&l);
        Ok(())
    }
}

/// The locals a pattern binds, whatever they own.
fn pat_binders(p: &Pat, out: &mut Vec<Local>) {
    match p {
        Pat::Bind(l, _) => out.push(l.clone()),
        Pat::Ctor { fields, .. } => fields.iter().for_each(|f| pat_binders(f, out)),
        Pat::Variant { pat, .. } => pat_binders(pat, out),
        _ => {}
    }
}

/// The locals a closure reads of the frame it is made in, in the order
/// first read, and whether its body moves each.
pub(super) fn free_locals(c: &ClosureNode, bf: &BlockFn) -> Vec<(Local, bool)> {
    let mut declared: Vec<u32> = c.params.iter().map(|(l, _)| l.id).collect();
    let mut used: Vec<(Local, bool)> = Vec::new();
    for l in &c.clones {
        note(l, false, &mut used);
    }
    collect(bf, &mut declared, &mut used);
    used.into_iter()
        .filter(|(l, _)| !declared.contains(&l.id))
        .collect()
}

fn note(l: &Local, moved: bool, used: &mut Vec<(Local, bool)>) {
    match used.iter_mut().find(|(x, _)| x.id == l.id) {
        Some((_, m)) => *m |= moved,
        None => used.push((l.clone(), moved)),
    }
}

fn collect(f: &BlockFn, declared: &mut Vec<u32>, used: &mut Vec<(Local, bool)>) {
    let leaf = |e: &Expr, declared: &mut Vec<u32>, used: &mut Vec<(Local, bool)>| {
        e.walk(&mut |x| match &x.kind {
            ExprKind::Read { local, how } => note(
                local,
                *how == Use::Move && local.storage() == Storage::Owned,
                used,
            ),
            ExprKind::Match(m) => {
                if !m.by_ref
                    && let ExprKind::Read {
                        local,
                        how: Use::Place,
                    } = &m.scrut.kind
                    && local.storage() == Storage::Owned
                {
                    note(local, true, used);
                }
                for a in &m.arms {
                    let mut ps = Vec::new();
                    pat_binders(&a.pat, &mut ps);
                    declared.extend(ps.iter().map(|l| l.id));
                }
            }
            ExprKind::Ref(p) | ExprKind::RefMut(p) => note(&p.local, false, used),
            ExprKind::Call(call) => {
                if let Callee::Local(l) | Callee::Cont(l) = &call.callee {
                    note(l, false, used);
                }
            }
            ExprKind::Closure(inner) => {
                for l in &inner.clones {
                    note(l, false, used);
                }
                declared.extend(inner.params.iter().map(|(l, _)| l.id));
            }
            _ => {}
        })
    };
    let value = |v: &Value, declared: &mut Vec<u32>, used: &mut Vec<(Local, bool)>| {
        if let Value::Leaf(e) = v {
            leaf(e, declared, used);
        }
    };
    for b in &f.blocks {
        declared.extend(b.params.iter().map(|(l, _)| l.id));
        for inst in &b.insts {
            match inst {
                Inst::Let { local, init, .. } | Inst::Var { local, init, .. } => {
                    declared.push(local.id);
                    value(init, declared, used);
                }
                Inst::Assign {
                    target, value: v, ..
                } => {
                    note(&target.local, false, used);
                    value(v, declared, used);
                }
                Inst::Eval(v) | Inst::Close(_, Some(v)) => value(v, declared, used),
                Inst::Bind { local, .. } => declared.push(local.id),
                Inst::End(_)
                | Inst::Unpack { .. }
                | Inst::Release { .. }
                | Inst::Open(_)
                | Inst::Close(_, None) => {}
            }
        }
        match &b.term {
            Term::Jump(_, v) | Term::Done(v) | Term::Branch { value: v, .. } => {
                value(v, declared, used)
            }
            Term::Return { value: Some(v), .. } => value(v, declared, used),
            _ => {}
        }
    }
    for reg in f.regions.iter().flatten() {
        for s in &reg.slots {
            if let nb::Slot::Operand(v) = s {
                value(v, declared, used);
            }
        }
        match &reg.shell {
            Shell::Node(e) | Shell::Call(e) => {
                leaf(e, declared, used);
                // The scrutinee of a `match` that takes its value apart is
                // moved by an arm that binds an owned part of it.
                if let (ExprKind::Match(m), Some(nb::Slot::Operand(Value::Leaf(s)))) =
                    (&e.kind, reg.slots.first())
                    && !m.by_ref
                    && let ExprKind::Read {
                        local,
                        how: Use::Place,
                    } = &s.kind
                    && local.storage() == Storage::Owned
                {
                    note(local, true, used);
                }
                if let ExprKind::Handle(h) = &e.kind {
                    for a in h.direct.iter().chain(&h.aborts).chain(&h.susp) {
                        for p in &a.pats {
                            let mut ps = Vec::new();
                            pat_binders(p, &mut ps);
                            declared.extend(ps.iter().map(|l| l.id));
                        }
                    }
                }
            }
            Shell::Block { .. } | Shell::While { .. } => {}
        }
    }
    for sub in &f.closures {
        collect(sub, declared, used);
    }
}
