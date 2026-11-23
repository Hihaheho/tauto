//! The walk the static checks share: a state flows along the edges of a
//! function's blocks to a fixed point.
//!
//! A check gives a state, how two states of the same point join, and what a
//! block does to a state (`Analysis::step`). `solve` runs it over the blocks
//! from one entry: each block is run from the join of the states that reach
//! it, again whenever that grows, and once more at the end with `report` set,
//! so a finding is made once, from the state every path has reached. A loop
//! needs no special case.
//!
//! A part of a function that is entered only through one terminator and ends
//! in a jump to its join (the body and the arms of a `handle`, the body of a
//! closure) is solved from its entry up to that join (`stop`), and the state
//! that reaches the join is the result.

use std::collections::BTreeSet;

use super::*;

pub trait Analysis {
    type State: Clone;

    /// Joins `from` into `into` at block `at`; whether `into` grew.
    fn join(&mut self, at: BlockId, into: &mut Self::State, from: &Self::State) -> bool;

    /// Runs the instructions and the terminator of `b` from `st`: the state on
    /// each edge it takes. A path that ends has none. With `report` the
    /// findings of the block are made; the walk to the fixed point runs
    /// without.
    fn step(
        &mut self,
        bf: &BlockFn,
        b: BlockId,
        st: Self::State,
        report: bool,
    ) -> Vec<(BlockId, Self::State)>;
}

/// Runs `a` over the blocks of `bf` from `start` with `init`. The result is
/// the join of the states that reach `stop`, if there is one and a path
/// reaches it.
pub fn solve<A: Analysis>(
    a: &mut A,
    bf: &BlockFn,
    start: BlockId,
    init: A::State,
    stop: Option<BlockId>,
    report: bool,
) -> Option<A::State> {
    let n = bf.blocks.len();
    let mut entry: Vec<Option<A::State>> = vec![None; n];
    let mut exit: Option<A::State> = None;
    let mut queue = BTreeSet::new();
    entry[start] = Some(init);
    queue.insert(start);
    while let Some(b) = queue.pop_first() {
        let Some(st) = entry[b].clone() else { continue };
        for (t, s) in a.step(bf, b, st, false) {
            if Some(t) == stop {
                match &mut exit {
                    None => exit = Some(s),
                    Some(e) => {
                        a.join(t, e, &s);
                    }
                }
                continue;
            }
            match &mut entry[t] {
                None => {
                    entry[t] = Some(s);
                    queue.insert(t);
                }
                Some(e) => {
                    if a.join(t, e, &s) {
                        queue.insert(t);
                    }
                }
            }
        }
    }
    if report {
        for b in 0..n {
            if let Some(st) = entry[b].clone() {
                a.step(bf, b, st, true);
            }
        }
    }
    exit
}

/// The value operands of a region, in the order the node evaluates them.
pub fn operands(bf: &BlockFn, region: RegionId) -> Vec<&Value> {
    bf.regions[region]
        .as_ref()
        .map(|r| {
            r.slots
                .iter()
                .filter_map(|s| match s {
                    Slot::Operand(v) => Some(v),
                    Slot::Body(_) => None,
                })
                .collect()
        })
        .unwrap_or_default()
}

/// The type of the value of a region.
pub fn region_ty(bf: &BlockFn, region: RegionId) -> Ty {
    match bf.regions.get(region).and_then(|r| r.as_ref()).map(|r| &r.shell) {
        Some(Shell::Node(e) | Shell::Call(e)) => e.ty.clone(),
        Some(Shell::Block { ty, .. }) => ty.clone(),
        Some(Shell::While { .. }) => Ty::Unit,
        None => Ty::Never,
    }
}

/// The type of a value.
pub fn value_ty(bf: &BlockFn, v: &Value) -> Ty {
    match v {
        Value::Leaf(e) => e.ty.clone(),
        Value::Region(r) => region_ty(bf, *r),
    }
}

/// Where a value was written.
pub fn value_span(bf: &BlockFn, v: &Value) -> Span {
    match v {
        Value::Leaf(e) => e.span,
        Value::Region(r) => match bf.regions.get(*r).and_then(|r| r.as_ref()).map(|r| &r.shell) {
            Some(Shell::Node(e) | Shell::Call(e)) => e.span,
            Some(Shell::Block { span, .. } | Shell::While { span, .. }) => *span,
            None => Span::new(0, 0),
        },
    }
}

/// The index of the body a closure's leaf was lowered to.
pub fn closure_body(c: &ClosureNode) -> Option<usize> {
    match c.body.kind {
        ExprKind::Int(n) if (CLOSURE_HOLE..CLOSURE_HOLE + (1 << 40)).contains(&n) => {
            Some((n - CLOSURE_HOLE) as usize)
        }
        _ => None,
    }
}

/// Whether the control node of a region goes on to its join without
/// running a part: `&&`, `||` and an `if` with no `else`.
pub fn skips(bf: &BlockFn, region: RegionId) -> bool {
    matches!(
        bf.regions[region].as_ref().map(|r| &r.shell),
        Some(Shell::Node(Expr {
            kind: ExprKind::And(..)
                | ExprKind::Or(..)
                | ExprKind::If {
                    otherwise: None,
                    ..
                },
            ..
        }))
    )
}

/// The locals each region's parts bind (a pattern's names, a handler arm's
/// parameters), which end where the parts meet.
pub fn bound_in(bf: &BlockFn) -> std::collections::HashMap<RegionId, Vec<u32>> {
    let mut out: std::collections::HashMap<RegionId, Vec<u32>> = Default::default();
    for b in &bf.blocks {
        for i in &b.insts {
            if let Inst::Bind { local, .. } = i
                && let Some(r) = b.owner
            {
                out.entry(r).or_default().push(local.id);
            }
        }
        if let Term::Handle { region, edges, .. } = &b.term {
            for e in edges {
                for (l, _) in &e.params {
                    out.entry(*region).or_default().push(l.id);
                }
            }
        }
    }
    out
}
