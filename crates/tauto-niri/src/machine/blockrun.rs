//! A function run from its block form (`tauto_nir::blocks`): the machine
//! steps a block's instructions and follows its terminator. What the block
//! form holds is what it runs; the metadata (`regions`' shells) is read
//! only for the node a branch came from (`if`, `&&`, `||`, `while`).
//!
//! A function that holds a `match`, a `handle`, a `budget` or a `suspend`
//! is not run from blocks yet (`supported`): it runs as a tree.

use super::*;
use tauto_nir::decision;
use tauto_nir::blocks::{BlockFn, BlockId, Inst, RegionId, Shell, Slot as RSlot, Term, Value};

/// Where the value of a region waits for the block that reads it: a slot
/// of the frame the function runs in.
const REGION_KEY: u32 = 0xC000_0000;

fn rkey(r: RegionId) -> Key {
    Key::Local(REGION_KEY + r as u32)
}

/// The place a `match` takes apart, and the place by way of the borrow that
/// holds it, and the temporary a scrutinee that is no local is held in.
fn skey(r: RegionId) -> Key {
    Key::Local(REGION_KEY + 0x0100_0000 + r as u32)
}
fn ikey(r: RegionId) -> Key {
    Key::Local(REGION_KEY + 0x0200_0000 + r as u32)
}
fn tkey(r: RegionId) -> Key {
    Key::Local(REGION_KEY + 0x0300_0000 + r as u32)
}

/// What argument `i` of the arm of the `handle` of region `r` is given.
fn argkey(r: RegionId, i: usize) -> Key {
    Key::Local(REGION_KEY + 0x0400_0000 + (r as u32) * 64 + i as u32)
}

/// For each step of `path` below the union tested at a prefix of it, whether
/// it takes the union's payload.
fn blk_steps(f: &BlockFn, r: RegionId, path: &[usize]) -> Vec<bool> {
    (0..path.len())
        .map(|i| path[i] == 0 && f.variants.contains(&(r, path[..i].to_vec())))
        .collect()
}

/// Whether the machine runs `f` from its blocks.
pub(super) fn supported(f: &BlockFn) -> bool {
    f.blocks.iter().all(|b| {
        match &b.term {
                Term::Handle { region, .. } => matches!(
                    &f.regions[*region],
                    Some(r) if matches!(&r.shell, Shell::Node(Expr { kind: ExprKind::Handle(_), .. }))
                ),
                Term::Enter { region, .. } => matches!(
                    &f.regions[*region],
                    Some(r) if matches!(
                        r.slots.first(),
                        Some(RSlot::Operand(Value::Leaf(e))) if !is_control(e)
                    ) | matches!(r.slots.first(), Some(RSlot::Operand(Value::Region(_)))) && matches!(
                        &r.shell,
                        Shell::Node(Expr { kind: ExprKind::Match(_), .. })
                    )
                ),
                Term::Control { region, .. } => matches!(
                    &f.regions[*region],
                    Some(r) if match &r.shell {
                        Shell::Node(e) => matches!(
                            e.kind,
                            ExprKind::If { .. }
                                | ExprKind::And(..)
                                | ExprKind::Or(..)
                                | ExprKind::Budget(_)
                        ),
                        Shell::While { .. } => true,
                        _ => false,
                    }
                ),
                _ => true,
            }
    })
}

impl<'p> M<'p> {
    /// The block form of function `id`, when it runs from blocks.
    pub(super) fn block_fn(&mut self, id: usize) -> Option<&'p BlockFn> {
        if let Some(b) = self.blockfns.get(&id) {
            return *b;
        }
        let f = &self.pkg.fns[id];
        let bf = tauto_nir::blocks::lower_body_for_run(&f.body, f.tier);
        let tiers = tauto_nir::blocks::block_tiers(&bf, f.tier);
        let r: Option<&'p BlockFn> = supported(&bf).then(|| &*Box::leak(Box::new(bf)));
        if let Some(b) = r {
            self.blk_tier.insert(b as *const BlockFn as usize, tiers);
        }
        if std::env::var_os("NIRI_BLOCKS_STATS").is_some() {
            eprintln!("BLOCKFN {}", if r.is_some() { "blocks" } else { "tree" });
        }
        self.blockfns.insert(id, r);
        r
    }

    fn region_val(&self, r: RegionId, fr: &Frame<'p>) -> R<'p, Val<'p>> {
        match fr.borrow_mut().slots.remove(&rkey(r)) {
            Some(Slot::Owned { val, .. }) => Ok(val),
            _ => error(format!("internal: region {r} has no value")),
        }
    }

    fn set_region(&self, r: RegionId, v: Val<'p>, fr: &Frame<'p>) {
        fr.insert(
            rkey(r),
            Slot::Owned {
                name: format!("region{r}"),
                val: v,
            },
        );
    }

    /// The value of `v` now, or the step that makes it (the instruction or
    /// terminator that wanted it is then given it by `apply`).
    fn blk_value(&mut self, v: &'p Value, fr: &Frame<'p>) -> R<'p, Result<Val<'p>, &'p Expr>> {
        match v {
            Value::Region(r) => Ok(Ok(self.region_val(*r, fr)?)),
            Value::Leaf(e) if is_control(e) => Ok(Err(e)),
            Value::Leaf(e) => Ok(Ok(self.eval(e, fr)?)),
        }
    }

    pub(super) fn blk_run(
        &mut self,
        f: &'p BlockFn,
        b: BlockId,
        mut i: usize,
        fr: Frame<'p>,
    ) -> R<'p, Ctl<'p>> {
        self.steps += 1;
        if self.steps > self.opts.steps {
            return unsupported("the step limit");
        }
        let blk = &f.blocks[b];
        while i < blk.insts.len() {
            let inst = &blk.insts[i];
            match inst {
                Inst::Bind { .. } | Inst::Unpack { .. } | Inst::End(_) | Inst::Release { .. } => {
                    self.blk_match_inst(f, blk.owner, blk, i, &fr)?;
                    i += 1;
                    continue;
                }
                _ => {}
            }
            let v = match inst {
                Inst::Open(_) => None,
                Inst::Close(r, None) => {
                    self.set_region(*r, Val::Unit, &fr);
                    None
                }
                Inst::Let { init: v, .. }
                | Inst::Var { init: v, .. }
                | Inst::Assign { value: v, .. }
                | Inst::Eval(v)
                | Inst::Close(_, Some(v)) => Some(v),
                Inst::Bind { .. } | Inst::Unpack { .. } | Inst::End(_) | Inst::Release { .. } => None,
            };
            if let Some(v) = v {
                match self.blk_value(v, &fr)? {
                    Ok(val) => self.blk_finish(inst, val, &fr)?,
                    Err(e) => {
                        self.konts.push(Kont::Blk {
                            f,
                            b,
                            i,
                            fr: fr.clone(),
                        });
                        return Ok(Ctl::Eval(e, fr));
                    }
                }
            }
            i += 1;
        }
        self.blk_term(f, b, fr)
    }

    /// Ends an instruction given the value of its operand.
    pub(super) fn blk_finish(&mut self, inst: &'p Inst, v: Val<'p>, fr: &Frame<'p>) -> R<'p, ()> {
        match inst {
            Inst::Let { local, span, .. } => self.bind(fr, local, v, *span),
            Inst::Var { local, span, .. } => {
                let v = if local.storage() == Storage::SharedVar {
                    Val::Cell(Rc::new(RefCell::new(v)))
                } else {
                    v
                };
                self.bind(fr, local, v, *span)
            }
            Inst::Assign { target, span, .. } => {
                let p = self.place_from(target, fr, *span)?;
                let (old, _, name) = self.at_mut(&p, *span, |x| std::mem::replace(x, v))?;
                if let Some(t) = self.live(&old) {
                    return self.violation(
                        ViolationKind::Leak,
                        *span,
                        Some(self.toks[t].made),
                        name.as_deref().or(Some(&target.local.name)),
                        "an assignment replaces a value that was not dropped",
                    );
                }
                Ok(())
            }
            Inst::Eval(x) => {
                if let Some(t) = self.live(&v) {
                    let at = match x {
                        Value::Leaf(e) => e.span,
                        Value::Region(_) => Span::new(0, 0),
                    };
                    return self.violation(
                        ViolationKind::Leak,
                        at,
                        Some(self.toks[t].made),
                        None,
                        "the value of a statement is dropped by nothing",
                    );
                }
                Ok(())
            }
            Inst::Close(r, _) => {
                self.set_region(*r, v, fr);
                Ok(())
            }
            Inst::Open(_)
            | Inst::Bind { .. }
            | Inst::Unpack { .. }
            | Inst::End(_)
            | Inst::Release { .. } => Ok(()),
        }
    }

    /// The entry of edge `n` of the `handle` that ends block `b`.
    pub(super) fn blk_handle_edge(&self, f: &'p BlockFn, b: BlockId, n: usize) -> BlockId {
        match &f.blocks[b].term {
            Term::Handle { edges, .. } => edges[n].entry,
            _ => unreachable!("a handle"),
        }
    }

    fn region_span(&self, f: &'p BlockFn, r: RegionId) -> Span {
        match f.regions[r].as_ref().map(|x| &x.shell) {
            Some(Shell::Node(e)) => e.span,
            _ => Span::new(0, 0),
        }
    }

    /// A continuation is taken from frame `from` of the stack up: a block in
    /// a body of the tier `S` or `A` is not a point the function may stop
    /// at, so a callee held at a stopping tier that stops under one breaks
    /// the tier it was given.
    pub(super) fn blk_check_stops(&self, from: usize, at: Span) -> R<'p, ()> {
        for k in &self.konts[from..] {
            let (f, b) = match k {
                Kont::Blk { f, b, .. } | Kont::BlkTerm { f, b, .. } => (*f, *b),
                // A call that may abort but not stop.
                Kont::BlkCall { f, b, .. } if matches!(f.blocks[*b].term, Term::Call { .. }) => {
                    (*f, *b)
                }
                _ => continue,
            };
            let t = self
                .blk_tier
                .get(&(f as *const BlockFn as usize))
                .and_then(|v| v.get(b).copied().flatten());
            if let Some(t) = t
                && t < tauto_nir::Tier::O
            {
                return error(format!(
                    "a continuation is taken across a block of tier {t:?}, which cannot stop (at {}..{})",
                    at.start, at.end
                ));
            }
        }
        Ok(())
    }

    /// The locals that an `End` of `f` ends.
    fn blk_ends(&mut self, f: &'p BlockFn) -> Rc<HashSet<u32>> {
        let key = f as *const BlockFn as usize;
        if let Some(s) = self.blk_ended.get(&key) {
            return s.clone();
        }
        let s: HashSet<u32> = f
            .blocks
            .iter()
            .flat_map(|b| &b.insts)
            .filter_map(|i| match i {
                Inst::End(l) => Some(l.id),
                _ => None,
            })
            .collect();
        let s = Rc::new(s);
        self.blk_ended.insert(key, s.clone());
        s
    }

    /// The place the `match` of region `r` takes apart.
    fn blk_scrut(&self, r: RegionId, fr: &Frame<'p>) -> R<'p, PlaceRef<'p>> {
        match fr.borrow().slots.get(&skey(r)) {
            Some(Slot::Owned { val: Val::Ref(p), .. }) => Ok(p.clone()),
            _ => error("internal: a match without its scrutinee"),
        }
    }

    /// Where the value a test, a bind or an unpack names is held, and the
    /// path in it: a `match` holds one scrutinee; an arm of a `handle` holds
    /// each argument it is given, the first step of a path naming it.
    fn blk_target(
        &self,
        f: &'p BlockFn,
        r: RegionId,
        path: &'p [usize],
        fr: &Frame<'p>,
    ) -> R<'p, (PlaceRef<'p>, &'p [usize], usize)> {
        let handle = matches!(
            f.regions[r].as_ref().map(|x| &x.shell),
            Some(Shell::Node(Expr { kind: ExprKind::Handle(_), .. }))
        );
        if handle {
            let Some(i) = path.first() else {
                return error("internal: a path of an arm without its argument");
            };
            let place = PlaceRef {
                root: Root::Slot(fr.clone(), argkey(r, *i)),
                path: Vec::new(),
            };
            Ok((place, &path[1..], 1))
        } else {
            Ok((self.blk_scrut(r, fr)?, path, 0))
        }
    }

    /// Whether an arm that tests the arguments `vals` from `root` is not
    /// declined: the tests are read as the blocks write them, with nothing
    /// bound or taken.
    pub(super) fn blk_arm_applies(
        &self,
        f: &'p BlockFn,
        root: BlockId,
        r: RegionId,
        vals: &[Val<'p>],
        at: Span,
    ) -> R<'p, bool> {
        let mut b = root;
        loop {
            match &f.blocks[b].term {
                Term::Goto(_) => return Ok(true),
                Term::Decline => return Ok(false),
                Term::Test { path, cases, default } => {
                    let Some(v) = path.first().and_then(|i| vals.get(*i)) else {
                        return error("internal: a test of an argument the arm is not given");
                    };
                    let steps = blk_steps(f, r, path);
                    let part = self.val_at(v, &path[1..], &steps[1..], at)?;
                    let mut next = *default;
                    for (c, t) in cases {
                        if self.case_hits(c, &part, at)? {
                            next = Some(*t);
                            break;
                        }
                    }
                    match next {
                        Some(n) => b = n,
                        None => return Ok(false),
                    }
                }
                _ => return error("internal: not a decision of an arm"),
            }
        }
    }

    /// Holds the values an arm is given, for its blocks to take apart.
    pub(super) fn blk_give(&self, r: RegionId, vals: Vec<Val<'p>>, fr: &Frame<'p>) {
        for (i, v) in vals.into_iter().enumerate() {
            fr.insert(
                argkey(r, i),
                Slot::Owned {
                    name: "<argument>".into(),
                    val: v,
                },
            );
        }
    }

    /// The continuation an arm of the `handle` that ends block `b` binds:
    /// the first of its edge's parameters.
    pub(super) fn blk_handle_k(&self, f: &'p BlockFn, b: BlockId, n: usize) -> Option<&'p Local> {
        match &f.blocks[b].term {
            Term::Handle { edges, .. } => edges[n].params.first().map(|(l, _)| l),
            _ => None,
        }
    }

    /// The region of the `handle` that ends block `b`.
    pub(super) fn blk_handle_region(&self, f: &'p BlockFn, b: BlockId) -> RegionId {
        match &f.blocks[b].term {
            Term::Handle { region, .. } => *region,
            _ => unreachable!("a handle"),
        }
    }

    /// The part of `v` at `path` (steps: which of them take a union's
    /// payload).
    fn val_at(&self, v: &Val<'p>, path: &[usize], steps: &[bool], at: Span) -> R<'p, Val<'p>> {
        let mut v = v.clone();
        for (i, idx) in path.iter().enumerate() {
            if matches!(v, Val::Ref(_) | Val::Cell(_)) {
                v = self.value_of(&v, at)?;
            }
            if steps[i] {
                v = match v {
                    Val::Inject(_, x) => *x,
                    Val::Moved(s) => return self.moved_at(s, at),
                    v => return error(format!("internal: a payload of a {}", v.kind())),
                };
            } else {
                while let Val::Inject(_, x) = v {
                    v = *x;
                }
                if matches!(v, Val::Ref(_) | Val::Cell(_)) {
                    v = self.value_of(&v, at)?;
                }
                v = match v {
                    Val::Data(d) => match d.fields.get(*idx) {
                        Some(x) => x.clone(),
                        None => return error("internal: a field out of range"),
                    },
                    Val::Moved(s) => return self.moved_at(s, at),
                    v => return error(format!("internal: a field of a {}", v.kind())),
                };
            }
        }
        Ok(v)
    }

    fn moved_at<T>(&self, s: Span, at: Span) -> R<'p, T> {
        self.violation(
            ViolationKind::UseAfterMove,
            at,
            None,
            None,
            format!("a match on a value moved at {}..{}", s.start, s.end),
        )
    }

    fn case_hits(&self, c: &decision::Case, v: &Val<'p>, at: Span) -> R<'p, bool> {
        use decision::Case;
        let mut v = match v {
            Val::Ref(_) | Val::Cell(_) => self.value_of(v, at)?,
            v => v.clone(),
        };
        if let Case::Ctor { .. } = c {
            while let Val::Inject(_, x) = v {
                v = *x;
            }
        }
        Ok(match (c, &v) {
            (_, Val::Moved(s)) => return self.moved_at(*s, at),
            (Case::Ctor { index, .. }, Val::Data(d)) => d.ctor.index == *index,
            (Case::Variant(i), Val::Inject(j, _)) => i == j,
            (Case::Int(n) | Case::Nat(n), Val::Int(x, _)) => i128::from(*n) == *x,
            (Case::Bool(b), Val::Bool(x)) => b == x,
            (Case::Text(t), Val::Text(x, _)) => **x == **t,
            _ => false,
        })
    }

    /// A `match` is entered: what it takes apart is held, for the tests
    /// and the names bound after.
    fn blk_enter(&mut self, f: &'p BlockFn, region: RegionId, by_ref: bool, fr: &Frame<'p>) -> R<'p, ()> {
        let Some(reg) = &f.regions[region] else {
            return error("internal: a match without its region");
        };
        let Some(RSlot::Operand(sv)) = reg.slots.first() else {
            return error("internal: a match without its scrutinee");
        };
        let at = self.region_span(f, region);
        let held = |p: PlaceRef<'p>| Slot::Owned {
            name: "<scrutinee>".into(),
            val: Val::Ref(p),
        };
        fr.borrow_mut().slots.remove(&ikey(region));
        if by_ref {
            let place = match sv {
                Value::Leaf(e) => self.place_of(e, fr)?,
                Value::Region(rr) => {
                    let v = self.region_val(*rr, fr)?;
                    match v {
                        Val::Ref(p) => p,
                        v => self.temp(v, fr),
                    }
                }
            };
            if let Value::Leaf(e) = sv {
                let local = match &e.kind {
                    ExprKind::Read { local, .. } => Some(local),
                    ExprKind::Ref(p) | ExprKind::RefMut(p) if p.path.is_empty() => Some(&p.local),
                    _ => None,
                };
                let inner = local.filter(|l| l.storage().is_borrow()).and_then(|l| {
                    let (f, k) = self.unalias(fr, Key::Local(l.id)).ok()?;
                    match f.borrow().slots.get(&k) {
                        Some(Slot::Owned { val: Val::Ref(q), .. }) => Some(PlaceRef {
                            root: Root::Via(Rc::new(crate::value::Via {
                                place: q.clone(),
                                kept: RefCell::new(None),
                            })),
                            path: Vec::new(),
                        }),
                        _ => None,
                    }
                });
                if let Some(q) = inner {
                    fr.insert(ikey(region), held(q));
                }
            }
            self.peek(&place, at)?;
            fr.insert(skey(region), held(place));
            return Ok(());
        }
        let local = match sv {
            Value::Leaf(Expr {
                kind: ExprKind::Read { local, how: Use::Move | Use::Place },
                ty,
                ..
            }) if needs_drop(ty) && local.storage() == Storage::Owned => Some(local),
            _ => None,
        };
        let place = match local {
            Some(l) => {
                let p = PlaceRef {
                    root: Root::Slot(fr.clone(), Key::Local(l.id)),
                    path: Vec::new(),
                };
                let v = self.peek(&p, at)?;
                if let Some(s) = self.moved_part(&v) {
                    return self.violation(
                        ViolationKind::UseAfterMove,
                        at,
                        None,
                        Some(&l.name),
                        format!("moved at {}..{}", s.start, s.end),
                    );
                }
                p
            }
            None => {
                let v = match sv {
                    Value::Leaf(e) => self.eval(e, fr)?,
                    Value::Region(rr) => self.region_val(*rr, fr)?,
                };
                fr.insert(
                    tkey(region),
                    Slot::Owned {
                        name: "<scrutinee>".into(),
                        val: v,
                    },
                );
                PlaceRef {
                    root: Root::Slot(fr.clone(), tkey(region)),
                    path: Vec::new(),
                }
            }
        };
        fr.insert(skey(region), held(place));
        Ok(())
    }

    /// A name is bound to a part of the scrutinee, a constructor of it ends,
    /// or a name bound for a guard that failed ends.
    fn blk_match_inst(
        &mut self,
        f: &'p BlockFn,
        owner: Option<RegionId>,
        blk: &'p tauto_nir::blocks::BBlock,
        i: usize,
        fr: &Frame<'p>,
    ) -> R<'p, ()> {
        let inst = &blk.insts[i];
        if let Inst::End(l) = inst {
            // The guard that failed took nothing: what it did to the parts
            // the name held is undone, as it was not run.
            if let Some(saved) = self.blk_saved.remove(&(Rc::as_ptr(fr) as usize, l.id)) {
                for (t, st) in saved {
                    self.toks[t].state = st;
                }
            }
            fr.borrow_mut().slots.remove(&Key::Local(l.id));
            return Ok(());
        }
        let Some(r) = owner else {
            return error("internal: a match instruction outside a match");
        };
        let at = self.region_span(f, r);
        let (path, borrow, last) = match inst {
            Inst::Bind { path, borrow, .. } => (path, *borrow, false),
            Inst::Unpack { path, last } => (path, false, *last),
            Inst::Release { path } => (path, false, false),
            _ => return Ok(()),
        };
        let (place, rest, skip) = self.blk_target(f, r, path, fr)?;
        let steps = blk_steps(f, r, path);
        match inst {
            Inst::Release { .. } => {
                let whole = self.peek(&place, at)?;
                let part = self.val_at(&whole, rest, &steps[skip..], at)?;
                if let Some(t) = self.live(&part) {
                    return self.violation(
                        ViolationKind::Leak,
                        at,
                        Some(self.toks[t].made),
                        None,
                        "a value given to an arm that binds no owned part of it is not dropped",
                    );
                }
                Ok(())
            }
            Inst::Bind { local, ty, path, borrow } => {
                if *borrow {
                    let inner = match fr.borrow().slots.get(&ikey(r)) {
                        Some(Slot::Owned { val: Val::Ref(q), .. }) => Some(q.clone()),
                        _ => None,
                    };
                    let mut q = if path.is_empty() {
                        place.clone()
                    } else {
                        inner.unwrap_or_else(|| place.clone())
                    };
                    for (idx, payload) in path.iter().zip(&steps) {
                        q.path.push(if *payload {
                            FieldRef { name: PAYLOAD.into(), index: None, indirect: tauto_nir::Indirect::None }
                        } else {
                            FieldRef { name: idx.to_string(), index: Some(*idx), indirect: tauto_nir::Indirect::None }
                        });
                    }
                    let v = if is_borrow_ty(ty) || needs_drop(ty) {
                        Val::Ref(q)
                    } else {
                        let x = self.peek(&q, at)?;
                        self.copy_val(&self.value_of(&x, at)?, at, Some(&local.name))?
                    };
                    self.bind(fr, local, v, at)
                } else {
                    let whole = self.peek(&place, at)?;
                    let part = self.val_at(&whole, rest, &steps[skip..], at)?;
                    let v = if needs_drop(ty) {
                        if self.blk_ends(f).contains(&local.id) {
                            let mut toks = Vec::new();
                            part.tokens(&mut |t| toks.push(t));
                            let saved = toks.into_iter().map(|t| (t, self.toks[t].state)).collect();
                            self.blk_saved.insert((Rc::as_ptr(fr) as usize, local.id), saved);
                        }
                        part
                    } else {
                        self.copy_val(&part, at, Some(&local.name))?
                    };
                    self.bind(fr, local, v, at)
                }
            }
            Inst::Unpack { path, last } => {
                let whole = self.peek(&place, at)?;
                let mut node = self.val_at(&whole, rest, &steps[skip..], at)?;
                if matches!(node, Val::Ref(_) | Val::Cell(_)) {
                    node = self.value_of(&node, at)?;
                }
                while let Val::Inject(_, x) = node {
                    node = *x;
                }
                if let Val::Data(d) = &node {
                    if let Some(t) = d.tok {
                        if self.toks[t].state != TokState::Live {
                            return self.violation(
                                ViolationKind::DoubleDrop,
                                at,
                                Some(self.toks[t].made),
                                None,
                                "a match takes apart a value already ended",
                            );
                        }
                        self.toks[t].state = TokState::Consumed(at);
                    }
                    let root_key = match &place.root {
                        Root::Slot(_, k) => Some(*k),
                        _ => None,
                    };
                    for (n, x) in d.fields.iter().enumerate() {
                        let Some(t) = self.live(x) else { continue };
                        let mut child = path.clone();
                        child.push(n);
                        if blk.insts[i + 1..]
                            .iter()
                            .any(|y| matches!(y, Inst::Unpack { path: p, .. } if *p == child))
                        {
                            continue;
                        }
                        let held = fr.borrow().slots.iter().any(|(k, s)| {
                            if Some(*k) == root_key {
                                return false;
                            }
                            let Slot::Owned { val, .. } = s else { return false };
                            let mut hit = false;
                            val.tokens(&mut |u| hit |= u == t);
                            hit
                        });
                        // A part a literal pattern tests is taken by the test.
                        let tested = f.blocks.iter().any(|b| {
                            matches!(&b.term, Term::Test { path: p, .. } if *p == child)
                                && b.owner == Some(r)
                        });
                        if !held && tested {
                            self.release(x.clone(), at, TokState::Consumed(at))?;
                        } else if !held {
                            return self.violation(
                                ViolationKind::Leak,
                                at,
                                Some(self.toks[t].made),
                                None,
                                "a part of the scrutinee that no pattern binds is not dropped",
                            );
                        }
                    }
                }
                if *last {
                    self.at_mut(&place, at, |x| *x = Val::Moved(at))?;
                }
                Ok(())
            }
            _ => Ok(()),
        }
    }

    fn goto(&mut self, f: &'p BlockFn, b: BlockId, fr: Frame<'p>) -> R<'p, Ctl<'p>> {
        Ok(Ctl::Blk(f, b, 0, fr))
    }

    /// Goes to `join` with the value of its region.
    fn jump(&mut self, f: &'p BlockFn, join: BlockId, v: Val<'p>, fr: Frame<'p>) -> R<'p, Ctl<'p>> {
        // The parts of a `handle` and a `budget` end with the value of the
        // part, which the continuation under them takes (their `BlkJoin`
        // gives it to the join).
        if let Some(r) = f.blocks[join].join_of
            && let Some(reg) = &f.regions[r]
            && matches!(
                &reg.shell,
                Shell::Node(Expr { kind: ExprKind::Handle(_) | ExprKind::Budget(_), .. })
            )
        {
            return Ok(Ctl::Value(v));
        }
        self.blk_join(f, join, v, fr)
    }

    /// Goes to `join` with the value of its region.
    pub(super) fn blk_join(
        &mut self,
        f: &'p BlockFn,
        join: BlockId,
        v: Val<'p>,
        fr: Frame<'p>,
    ) -> R<'p, Ctl<'p>> {
        if let Some(r) = f.blocks[join].join_of {
            self.set_region(r, v, &fr);
        }
        self.goto(f, join, fr)
    }

    fn blk_term(&mut self, f: &'p BlockFn, b: BlockId, fr: Frame<'p>) -> R<'p, Ctl<'p>> {
        let term = &f.blocks[b].term;
        // The operand a terminator waits for, if any.
        let operand: Option<&'p Value> = match term {
            Term::Jump(_, v) | Term::Done(v) | Term::Branch { value: v, .. } => Some(v),
            Term::Return { value, .. } => value.as_ref(),
            Term::Control { region, .. } => match &f.regions[*region] {
                Some(r) => match r.slots.first() {
                    Some(RSlot::Operand(v)) => Some(v),
                    _ => None,
                },
                None => None,
            },
            _ => None,
        };
        if let Term::Enter {
            region,
            entry,
            by_ref,
            ..
        } = term
        {
            self.blk_enter(f, *region, *by_ref, &fr)?;
            return self.goto(f, *entry, fr);
        }
        if let Term::Test { path, cases, default } = term {
            let r = f.blocks[b].owner.ok_or(()).or_else(|_| error("internal: a test outside a match"))?;
            let at = self.region_span(f, r);
            let (p, rest, skip) = self.blk_target(f, r, path, &fr)?;
            let whole = self.peek(&p, at)?;
            let part = self.val_at(&whole, rest, &blk_steps(f, r, path)[skip..], at)?;
            for (c, t) in cases {
                if self.case_hits(c, &part, at)? {
                    return self.goto(f, *t, fr);
                }
            }
            return match default {
                Some(d) => self.goto(f, *d, fr),
                None => error("no arm matches"),
            };
        }
        if let Term::Handle { region, edges, join } = term {
            let Some(Shell::Node(Expr { kind: ExprKind::Handle(h), .. })) =
                f.regions[*region].as_ref().map(|r| &r.shell)
            else {
                return error("internal: a handle without its node");
            };
            let id = self.next_handler;
            self.next_handler += 1;
            let body = arm_frame(&fr);
            self.konts.push(Kont::BlkJoin { f, join: *join, fr: fr.clone() });
            self.konts.push(Kont::Handle {
                h,
                fr: fr.clone(),
                body: body.clone(),
                id,
                seg: None,
                blk: Some((f, b)),
            });
            return Ok(Ctl::Blk(f, edges[0].entry, 0, body));
        }
        if let Term::Call { region, .. } | Term::Suspend { region, .. } = term {
            let Some(r) = &f.regions[*region] else {
                return error("internal: a call without its region");
            };
            let Shell::Call(e) = &r.shell else {
                return error("internal: a call region without its call");
            };
            self.konts.push(Kont::BlkCall {
                f,
                b,
                fr: fr.clone(),
            });
            return Ok(Ctl::Eval(e, fr));
        }
        match operand {
            Some(v) => match self.blk_value(v, &fr)? {
                Ok(val) => self.blk_after(f, b, val, fr),
                Err(e) => {
                    self.konts.push(Kont::BlkTerm {
                        f,
                        b,
                        fr: fr.clone(),
                    });
                    Ok(Ctl::Eval(e, fr))
                }
            },
            None => self.blk_after(f, b, Val::Unit, fr),
        }
    }

    /// Goes on from the terminator of `b`, given the value of its operand.
    pub(super) fn blk_after(
        &mut self,
        f: &'p BlockFn,
        b: BlockId,
        v: Val<'p>,
        fr: Frame<'p>,
    ) -> R<'p, Ctl<'p>> {
        match &f.blocks[b].term {
            Term::Jump(t, _) => self.jump(f, *t, v, fr),
            Term::Goto(t) => self.goto(f, *t, fr),
            Term::Done(_) => Ok(Ctl::Value(v)),
            Term::Return { .. } => Err(Stop::Return(v)),
            Term::Branch { then, els, .. } => match v {
                Val::Bool(true) => {
                    // A `while` that counts its steps takes one off every
                    // budget in place before its body.
                    if let Some(r) = f.blocks[b].owner
                        && let Some(Shell::While { tick: Tick::Budget, span }) =
                            f.regions[r].as_ref().map(|x| &x.shell)
                        && let Some(c) = self.tick(Then::Blk(f, *then, fr.clone()), *span)?
                    {
                        return Ok(c);
                    }
                    self.goto(f, *then, fr)
                }
                Val::Bool(false) => match els {
                    Some(e) => self.goto(f, *e, fr),
                    None => error("internal: a guard with no next arm"),
                },
                v => error(format!("internal: a branch on a {}", v.kind())),
            },
            Term::Control {
                region,
                succs,
                join,
            } => {
                let Some(r) = &f.regions[*region] else {
                    return error("internal: a control without its region");
                };
                match &r.shell {
                    Shell::While { .. } => self.goto(f, succs[0], fr),
                    Shell::Node(e) => match (&e.kind, v) {
                        (ExprKind::Budget(bn), v) => {
                            if bn.memory {
                                return unsupported("a memory budget");
                            }
                            let steps = match v {
                                Val::Int(n, _) => u64::try_from(n).unwrap_or(u64::MAX),
                                v => return error(format!("internal: a budget of a {}", v.kind())),
                            };
                            let id = self.next_handler;
                            self.next_handler += 1;
                            self.budgets.insert(id);
                            self.konts.push(Kont::BlkJoin { f, join: *join, fr: fr.clone() });
                            self.konts.push(Kont::Budget {
                                id,
                                left: Rc::new(std::cell::Cell::new(steps)),
                            });
                            self.goto(f, succs[0], fr)
                        }
                        (ExprKind::If { .. }, Val::Bool(true)) => self.goto(f, succs[0], fr),
                        (ExprKind::If { .. }, Val::Bool(false)) => match succs.get(1) {
                            Some(o) => self.goto(f, *o, fr),
                            None => self.jump(f, *join, Val::Unit, fr),
                        },
                        (ExprKind::And(..), Val::Bool(true)) | (ExprKind::Or(..), Val::Bool(false)) => {
                            self.goto(f, succs[0], fr)
                        }
                        (ExprKind::And(..), Val::Bool(false)) => self.jump(f, *join, Val::Bool(false), fr),
                        (ExprKind::Or(..), Val::Bool(true)) => self.jump(f, *join, Val::Bool(true), fr),
                        (_, v) => error(format!("internal: a branch on a {}", v.kind())),
                    },
                    _ => error("internal: a control of another shell"),
                }
            }
            Term::Unreachable => error("no arm matches"),
            Term::Decline => error("an arm's pattern does not match what it is given"),
            _ => error("internal: a terminator the machine does not run"),
        }
    }

    /// A call of a block ended with `v`.
    pub(super) fn blk_call_done(
        &mut self,
        f: &'p BlockFn,
        b: BlockId,
        v: Val<'p>,
        fr: Frame<'p>,
    ) -> R<'p, Ctl<'p>> {
        let (Term::Call { join, .. } | Term::Suspend { join, .. }) = &f.blocks[b].term else {
            return error("internal: not a call");
        };
        self.jump(f, *join, v, fr)
    }

    /// What an abort leaving the call that ends block `b` runs: the drops
    /// of its abort block.
    pub(super) fn blk_cleanup(&mut self, f: &'p BlockFn, b: BlockId, fr: &Frame<'p>) -> R<'p, ()> {
        let (Term::Call { abort, .. } | Term::Suspend { abort, .. }) = &f.blocks[b].term else {
            return error("internal: not a call");
        };
        for inst in &f.blocks[*abort].insts {
            match inst {
                Inst::Eval(Value::Leaf(e)) => {
                    let v = self.eval(e, fr)?;
                    self.blk_finish(inst, v, fr)?;
                }
                Inst::Let { init: Value::Leaf(e), .. } => {
                    let v = self.eval(e, fr)?;
                    self.blk_finish(inst, v, fr)?;
                }
                _ => return error("internal: an abort block that is not straight-line drops"),
            }
        }
        Ok(())
    }
}
