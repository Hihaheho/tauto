//! Mutation tests: niri must catch what is broken on purpose.
//!
//! Each program that runs clean is changed in one place at a time, and the
//! changed program must stop with the violation the change calls for:
//!
//! - a `drop` removed: a leak (V3, or V4 for a linear value);
//! - a `drop` written twice: the second reads a local already moved (V1) or
//!   drops a token again (V2);
//! - a `Move` read made a `Clone`: the original is left alive (V3), or the
//!   value cannot be cloned (V6);
//! - a `Clone` read made a `Move`: a later read finds it moved (V1);
//! - two statements that show something swapped: the output differs (V8).
//!
//! A change is tried only where the clean run shows it sends an owned value
//! the wrong way, and then it must be caught, with no exception listed by
//! hand. The clean run (`Options::coverage`) records, apart from what the
//! checker reports:
//!
//! - which places it reached: a change in code that never runs cannot be
//!   seen by running;
//! - which moves took a value that owned something, from the frame of a call
//!   (`Run::owned_moves`): a clone of a value that owns nothing, or of one a
//!   closure keeps (the closure drops its copy with it), leaks nothing;
//! - which clones read a place that is used again later
//!   (`Run::clones_read_later`): a move of a value nothing reads again is
//!   not wrong;
//! - which drops dropped a value that owned something (`Run::owned_drops`).
//!
//! The test then says one thing: every change that sends an owned value the
//! wrong way is caught. Without it the checker could catch nothing and every
//! other test would still pass.

mod common;

use std::collections::HashSet;

use tauto_nir::ownership::needs_drop;
use tauto_nir::{Block, Callee, Expr, ExprKind, Package, Stmt, Storage, Use};
use tauto_niri::{Options, Outcome, ViolationKind};

/// Calls `on_expr` on every expression and `on_block` on every block,
/// outer first, in one fixed order.
fn visit(e: &mut Expr, v: &mut dyn Visitor) {
    v.expr(e);
    match &mut e.kind {
        ExprKind::Block(b) => visit_block(b, v),
        ExprKind::If {
            cond,
            then,
            otherwise,
        } => {
            visit(cond, v);
            visit(then, v);
            if let Some(o) = otherwise {
                visit(o, v);
            }
        }
        ExprKind::Match(m) => {
            visit(&mut m.scrut, v);
            for a in &mut m.arms {
                if let Some(g) = &mut a.guard {
                    visit(g, v);
                }
                visit(&mut a.body, v);
            }
        }
        ExprKind::Closure(c) => visit(&mut c.body, v),
        ExprKind::And(a, b) | ExprKind::Or(a, b) => {
            visit(a, v);
            visit(b, v);
        }
        _ => {
            for op in e.operands_mut() {
                visit(op, v);
            }
        }
    }
}

fn visit_block(b: &mut Block, v: &mut dyn Visitor) {
    v.block(b);
    for s in &mut b.stmts {
        match s {
            Stmt::Let { init, .. } | Stmt::Var { init, .. } => visit(init, v),
            Stmt::Assign { value, .. } => visit(value, v),
            Stmt::Expr(e) => visit(e, v),
            Stmt::While { cond, body, .. } => {
                visit(cond, v);
                visit_block(body, v);
            }
            Stmt::Return { value, .. } => {
                if let Some(x) = value {
                    visit(x, v);
                }
            }
        }
    }
    if let Some(t) = &mut b.tail {
        visit(t, v);
    }
}

trait Visitor {
    fn expr(&mut self, _: &mut Expr) {}
    fn block(&mut self, _: &mut Block) {}
}

fn visit_pkg(pkg: &mut Package, v: &mut dyn Visitor) {
    for f in &mut pkg.fns {
        visit(&mut f.body, v);
    }
}

#[derive(Debug, Clone, Copy, PartialEq)]
enum Change {
    RemoveDrop,
    DoubleDrop,
    MoveToClone,
    CloneToMove,
    Swap,
}

impl Change {
    fn expected(self) -> &'static [ViolationKind] {
        use ViolationKind::*;
        match self {
            Change::RemoveDrop => &[Leak, Linear],
            Change::DoubleDrop => &[UseAfterMove, DoubleDrop],
            Change::MoveToClone => &[Leak, UseMark],
            Change::CloneToMove => &[UseAfterMove],
            Change::Swap => &[Output],
        }
    }
}

fn is_drop(e: &Expr) -> bool {
    matches!(&e.kind, ExprKind::Call(c)
        if matches!(&c.callee, Callee::Builtin(n) if n == tauto_nir::builtins::DROP)
            && needs_drop(&c.args[0].ty))
}

fn stmt_expr(s: &Stmt) -> Option<&Expr> {
    match s {
        Stmt::Let { init, .. } | Stmt::Var { init, .. } => Some(init),
        Stmt::Expr(e) => Some(e),
        _ => None,
    }
}

fn shows(e: &Expr) -> bool {
    let mut found = false;
    e.walk(&mut |x| found |= matches!(x.kind, ExprKind::Perform(_)));
    found
}

fn mentions(e: &Expr, ids: &HashSet<u32>) -> bool {
    let mut found = false;
    e.walk(&mut |x| match &x.kind {
        ExprKind::Read { local, .. } => found |= ids.contains(&local.id),
        ExprKind::Ref(p) | ExprKind::RefMut(p) => found |= ids.contains(&p.local.id),
        _ => {}
    });
    found
}

/// The `n`-th site of a change, counted in `visit`'s order: with `apply`,
/// it makes the change there; without, it counts the sites and whether the
/// run reached each.
struct Sites<'a> {
    change: Change,
    visited: &'a HashSet<usize>,
    /// The moves whose value owned something (`Run::owned_moves`): a move
    /// of anything else made a clone changes nothing a run can see.
    owned: &'a HashSet<usize>,
    /// The clones whose place is used again (`Run::clones_read_later`).
    later: &'a HashSet<usize>,
    /// The drops of a value that owned something (`Run::owned_drops`).
    drops: &'a HashSet<usize>,
    /// The sites seen, each with whether it ran.
    seen: Vec<bool>,
    apply: Option<usize>,
    /// Count only whether the run reached a site, not whether the change
    /// there would send an owned value wrong.
    reached_only: bool,
}

impl Sites<'_> {
    fn site(&mut self, ran: bool) -> bool {
        self.seen.push(ran);
        self.apply == Some(self.seen.len() - 1)
    }

    fn ran(&self, e: &Expr) -> bool {
        self.visited.contains(&(e as *const Expr as usize))
    }
}

impl Visitor for Sites<'_> {
    fn expr(&mut self, e: &mut Expr) {
        let to = match (self.change, &e.kind) {
            (
                Change::MoveToClone,
                ExprKind::Read {
                    local,
                    how: Use::Move,
                },
            ) if local.storage() == Storage::Owned && needs_drop(&e.ty) => Use::Clone,
            (
                Change::CloneToMove,
                ExprKind::Read {
                    local,
                    how: Use::Clone,
                },
            ) if local.storage() == Storage::Owned && needs_drop(&e.ty) => Use::Move,
            _ => return,
        };
        let mut ran = self.ran(e);
        let at = e as *const Expr as usize;
        match self.change {
            _ if self.reached_only => {}
            Change::MoveToClone => ran &= self.owned.contains(&at),
            Change::CloneToMove => ran &= self.later.contains(&at),
            _ => {}
        }
        if self.site(ran)
            && let ExprKind::Read { how, .. } = &mut e.kind
        {
            *how = to;
        }
    }

    fn block(&mut self, b: &mut Block) {
        match self.change {
            Change::RemoveDrop | Change::DoubleDrop => {
                let mut i = 0;
                while i < b.stmts.len() {
                    if let Stmt::Expr(e) = &b.stmts[i]
                        && is_drop(e)
                    {
                        let ran = self.ran(e)
                            && (self.reached_only
                                || self.drops.contains(&(e as *const Expr as usize)));
                        if self.site(ran) {
                            if self.change == Change::RemoveDrop {
                                b.stmts.remove(i);
                                continue;
                            }
                            let again = b.stmts[i].clone();
                            b.stmts.insert(i + 1, again);
                            i += 1;
                        }
                    }
                    i += 1;
                }
            }
            Change::Swap => {
                for i in 0..b.stmts.len().saturating_sub(1) {
                    let (Some(x), Some(y)) = (stmt_expr(&b.stmts[i]), stmt_expr(&b.stmts[i + 1]))
                    else {
                        continue;
                    };
                    if !shows(x) || !shows(y) {
                        continue;
                    }
                    let mut first = HashSet::new();
                    if let Stmt::Let { local, .. } | Stmt::Var { local, .. } = &b.stmts[i] {
                        first.insert(local.id);
                    }
                    if mentions(y, &first) {
                        continue;
                    }
                    let ran = self.ran(x) && self.ran(y);
                    if self.site(ran) {
                        b.stmts.swap(i, i + 1);
                    }
                }
            }
            _ => {}
        }
    }
}

#[test]
fn every_change_that_runs_is_caught() {
    let changes = [
        Change::RemoveDrop,
        Change::DoubleDrop,
        Change::MoveToClone,
        Change::CloneToMove,
        Change::Swap,
    ];
    let mut tried = vec![0usize; changes.len()];
    let mut failed = Vec::new();
    for p in common::PROGRAMS.iter().filter(|p| p.known.is_none()) {
        let mut pkg = common::prepared(p.source);
        let clean = tauto_niri::run_with(
            &pkg,
            Options {
                coverage: true,
                ..Options::default()
            },
        );
        assert_eq!(clean.against(p.shown), Outcome::Ok, "{}", p.name);
        for (ci, &change) in changes.iter().enumerate() {
            let mut count = Sites {
                change,
                visited: &clean.visited,
                owned: &clean.owned_moves,
                later: &clean.clones_read_later,
                drops: &clean.owned_drops,
                seen: Vec::new(),
                apply: None,
                reached_only: false,
            };
            visit_pkg(&mut pkg, &mut count);
            for (n, ran) in count.seen.iter().enumerate() {
                if !ran {
                    continue;
                }
                let mut changed = pkg.clone();
                let none = HashSet::new();
                visit_pkg(
                    &mut changed,
                    &mut Sites {
                        change,
                        visited: &none,
                        owned: &none,
                        later: &none,
                        drops: &none,
                        seen: Vec::new(),
                        apply: Some(n),
                        reached_only: false,
                    },
                );
                tried[ci] += 1;
                let outcome = tauto_niri::run(&changed).against(p.shown);
                let caught = matches!(&outcome,
                    Outcome::Violation(v) if change.expected().contains(&v.kind));
                if !caught {
                    failed.push(format!("{} {change:?} #{n}: {outcome:?}", p.name));
                }
            }
        }
    }
    for (c, n) in changes.iter().zip(&tried) {
        assert!(*n > 0, "no site of {c:?} ran in any program");
    }
    assert!(
        failed.is_empty(),
        "changes that send an owned value wrong and niri does not catch:\n{}",
        failed.join("\n")
    );
    eprintln!(
        "changes tried: {:?}",
        changes.iter().zip(tried).collect::<Vec<_>>()
    );
}

/// How a program compiled through LLVM ends under the address sanitizer,
/// which sees a value released twice, used after it is released or never
/// released: `Some(true)` when it is wrong so, or shows something else,
/// `Some(false)` when it ends as it should, `None` when the backend does
/// not write it.
fn llvm_wrong(
    pkg: &Package,
    shown: &[(&str, &str)],
    dir: &std::path::Path,
    n: usize,
) -> Option<bool> {
    use std::process::Command;
    let ir = tauto_llvm::emit_on(pkg, tauto_llvm::Sys::Asan).ok()?;
    let ir = ir.replace(") {\n", ") sanitize_address {\n");
    let ll = dir.join(format!("{n}.ll"));
    let obj = dir.join(format!("{n}.o"));
    let exe = dir.join(format!("{n}.out"));
    std::fs::write(&ll, &ir).ok()?;
    let ok = |c: &mut Command| c.output().map(|o| o.status.success()).unwrap_or(false);
    if !ok(Command::new("clang")
        .args([
            "-O1",
            "-g0",
            "-fsanitize=address",
            "-Wno-override-module",
            "-c",
            "-o",
        ])
        .arg(&obj)
        .arg(&ll))
    {
        return None;
    }
    if !ok(Command::new("cc")
        .args(["-fsanitize=address", "-o"])
        .arg(&exe)
        .arg(&obj))
    {
        return None;
    }
    let run = Command::new(&exe)
        .env(
            "ASAN_OPTIONS",
            "detect_leaks=1:detect_stack_use_after_return=0",
        )
        .output()
        .ok()?;
    for f in [&ll, &obj, &exe] {
        let _ = std::fs::remove_file(f);
    }
    let out = String::from_utf8_lossy(&run.stdout);
    let want: Vec<String> = shown.iter().map(|(k, v)| format!("{k} = {v}")).collect();
    let got: Vec<&str> = out.lines().collect();
    Some(!run.status.success() || got != want.iter().map(String::as_str).collect::<Vec<_>>())
}

/// The changes checked against a second, independent judge: the program
/// compiled through LLVM, whose drops are only the ones NIR writes, run
/// under the address sanitizer. A change the clean run leaves out (at a
/// place the run reached) must not be wrong there: else the record that
/// decides what must be caught would hide a real error. The other way is
/// only counted: the sanitizer does not see a value that uses no memory on
/// the heap (`Nil`), nor one still reachable from a global at the end, so a
/// change niri must catch can look right to it.
#[test]
fn no_change_left_out_is_one_llvm_finds_wrong() {
    if std::process::Command::new("clang")
        .arg("--version")
        .output()
        .is_err()
    {
        eprintln!("no clang: not checked");
        return;
    }
    let dir = std::env::temp_dir().join(format!("niri-oracle-{}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    let changes = [
        Change::RemoveDrop,
        Change::DoubleDrop,
        Change::MoveToClone,
        Change::CloneToMove,
        Change::Swap,
    ];
    let mut disagree = Vec::new();
    let mut counts = std::collections::BTreeMap::<&str, usize>::new();
    let mut k = 0;
    for p in common::PROGRAMS.iter().filter(|p| p.known.is_none()) {
        let mut pkg = common::prepared_mono(p.source);
        let clean = tauto_niri::run_with(
            &pkg,
            Options {
                coverage: true,
                ..Options::default()
            },
        );
        if clean.against(p.shown) != Outcome::Ok {
            continue;
        }
        if llvm_wrong(&pkg, p.shown, &dir, k) != Some(false) {
            *counts.entry("program not run by LLVM").or_default() += 1;
            continue;
        }
        for &change in &changes {
            let mut sites = |reached_only| {
                let mut s = Sites {
                    change,
                    visited: &clean.visited,
                    owned: &clean.owned_moves,
                    later: &clean.clones_read_later,
                    drops: &clean.owned_drops,
                    seen: Vec::new(),
                    apply: None,
                    reached_only,
                };
                visit_pkg(&mut pkg, &mut s);
                s.seen
            };
            let must = sites(false);
            let reached = sites(true);
            for (n, r) in reached.iter().enumerate() {
                if !r {
                    continue;
                }
                let mut changed = pkg.clone();
                let none = HashSet::new();
                visit_pkg(
                    &mut changed,
                    &mut Sites {
                        change,
                        visited: &none,
                        owned: &none,
                        later: &none,
                        drops: &none,
                        seen: Vec::new(),
                        apply: Some(n),
                        reached_only: false,
                    },
                );
                k += 1;
                let Some(wrong) = llvm_wrong(&changed, p.shown, &dir, k) else {
                    *counts.entry("change not run by LLVM").or_default() += 1;
                    continue;
                };
                let key = match (must[n], wrong) {
                    (true, true) => "must be caught, LLVM finds it wrong",
                    (false, false) => "left out, LLVM finds it right",
                    (true, false) => "must be caught, LLVM finds it right",
                    (false, true) => "left out, LLVM finds it wrong",
                };
                *counts.entry(key).or_default() += 1;
                if !must[n] && wrong {
                    disagree.push(format!("{} {change:?} #{n}: {key}", p.name));
                }
            }
        }
    }
    let _ = std::fs::remove_dir_all(&dir);
    eprintln!("{counts:#?}");
    assert!(
        disagree.is_empty(),
        "changes the clean run leaves out but LLVM finds wrong:\n{}",
        disagree.join("\n")
    );
}
