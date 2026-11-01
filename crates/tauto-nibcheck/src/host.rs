//! The standard effects (`std/prelude/Os.taut`): which the host answers at the
//! top level, the permission each needs, and how a backend's program is put
//! inside the prelude's `host_run` that answers them
//! (`docs/design/host-effects.md`).

use crate::surface::{Handler, PRELUDE_BASE, Program, Stmt, SurfaceTerm, TermKind, parse_expr_at};
use std::collections::BTreeSet;

/// The effects the host answers when they reach the top level unanswered.
pub const HOST_EFFECTS: &[&str] = &[
    "stdout",
    "stderr",
    "stdin",
    "argv",
    "exit",
    "stop",
    "wall_clock",
    "monotonic_clock",
    "sleep",
    "wait",
    "random",
    "secure_random",
    "fs_read",
    "fs_write",
    "fs_read_bytes",
    "fs_write_bytes",
    "fs_create_dir",
    "fs_list_dir",
    "fs_remove",
    "fs_temp_dir",
    "proc_run",
    "env",
    "permission",
    "net",
    "net_addr",
    "net_resolve",
    "tcp_listen",
    "tcp_accept",
    "tcp_connect",
    "tcp_read",
    "tcp_write",
    "tcp_shutdown",
    "tcp_close",
    "tcp_unlisten",
    "tls_accept",
    "tls_connect",
    "tls_read",
    "tls_write",
    "tls_shutdown",
    "tls_close",
];

/// The permission (`--allow-<name>`) an effect needs, if any.
pub fn permission(effect: &str) -> Option<&'static str> {
    match effect {
        "fs_read" | "fs_read_bytes" | "fs_list_dir" => Some("read"),
        "fs_write" | "fs_write_bytes" | "fs_create_dir" | "fs_remove" => Some("write"),
        "proc_run" => Some("run"),
        "env" => Some("env"),
        "net" | "net_addr" | "net_resolve" => Some("net"),
        "tcp_listen" | "tcp_accept" | "tcp_connect" | "tcp_read" | "tcp_write" | "tcp_shutdown"
        | "tcp_close" | "tcp_unlisten" => Some("net"),
        "tls_accept" | "tls_connect" | "tls_read" | "tls_write" | "tls_shutdown" | "tls_close" => {
            Some("net")
        }
        _ => None,
    }
}

/// The permissions a run that performs `effects` needs before it starts. A
/// run that makes a temporary directory (`fs_temp_dir`) may read and write
/// under it with no flag, so `read` and `write` are not needed up front: a
/// request outside what the flags cover is still denied when it is made.
pub fn permissions<'e>(effects: impl IntoIterator<Item = &'e String>) -> BTreeSet<&'static str> {
    let effects: Vec<&String> = effects.into_iter().collect();
    let temp = effects.iter().any(|e| e.as_str() == "fs_temp_dir");
    effects
        .into_iter()
        .filter_map(|e| permission(e))
        .filter(|k| !(temp && matches!(*k, "read" | "write")))
        .collect()
}

/// Where the spans of the wrapper start: after the prelude's, before nothing a
/// file can reach.
const WRAPPER_BASE: u32 = PRELUDE_BASE + (1 << 30);

/// The program with its top-level statements in `host_run(() => { … })`, so
/// a backend answers the standard effects with the prelude's handler. The
/// declarations stay at the top level; a function does not see a top-level
/// `let`, so moving the statements does not change what a name means. Each
/// `perform spawn(f)` becomes `perform spawn(() => host_run(f))`: a task runs
/// apart from the handlers around its `spawn`, on a thread of its own where a
/// backend has threads, so the host answers what it asks. Each
/// `perform test(name, body)` puts its body in `host_run` too: the host runs
/// it apart from the program, so a test can `print`. `None` when there
/// is nothing to move.
pub fn wrap(program: &Program) -> Option<Program> {
    let mut program = program.clone();
    for stmt in &mut program.stmts {
        tasks_in_stmt(stmt);
    }
    let program = &program;
    let runs = |s: &Stmt| {
        matches!(
            s,
            Stmt::Let { .. }
                | Stmt::Var { .. }
                | Stmt::Assign { .. }
                | Stmt::While { .. }
                | Stmt::Expr(_)
        )
    };
    if !program.stmts.iter().any(runs) {
        return None;
    }
    // The result is written as `()`: a program that stops (`perform exit(3)`)
    // gives its body the type `Never`, which leaves `host_run`'s `A` open.
    let mut wrapper =
        crate::surface::parse_program_unresolved_at("let _: () := Host::run(() => ())", WRAPPER_BASE)
            .expect("the wrapper parses");
    let Some(Stmt::Let { value: call, .. }) = wrapper.stmts.first_mut() else {
        panic!("the wrapper has the shape it is written with");
    };
    let (items, body): (Vec<Stmt>, Vec<Stmt>) =
        program.stmts.iter().cloned().partition(|s| !runs(s));
    fill(call, body);
    let mut out = program.clone();
    out.stmts = items;
    out.stmts.append(&mut wrapper.stmts);
    Some(out)
}

/// Makes the lambda of the wrapper `{ body; () }`, its `()` the one written.
fn fill(t: &mut crate::surface::SurfaceTerm, body: Vec<Stmt>) {
    let mut kind = (*t.kind).clone();
    match &mut kind {
        TermKind::App { arguments, .. } => fill(&mut arguments[0], body),
        TermKind::Lam { body: unit, .. } => {
            let mut stmts = body;
            stmts.push(Stmt::Expr((**unit).clone()));
            **unit = crate::surface::SurfaceTerm::new(TermKind::Block(stmts), unit.span);
        }
        other => panic!("the wrapper has the shape it is written with: {other:?}"),
    }
    *t = t.with_kind(kind, t.span);
}

/// Puts the body of each `spawn` and `test` in `stmt` in `host_run`.
fn tasks_in_stmt(stmt: &mut Stmt) {
    match stmt {
        Stmt::Let { value, .. } | Stmt::Var { value, .. } | Stmt::Assign { value, .. } => {
            tasks_in(value)
        }
        Stmt::Fn(f) => tasks_in(&mut f.body),
        Stmt::Attributed { stmt, .. } => tasks_in_stmt(stmt),
        Stmt::Mutual { items, .. } | Stmt::Module { items, .. } => {
            items.iter_mut().for_each(tasks_in_stmt)
        }
        Stmt::Instance(i) => i.methods.iter_mut().for_each(|f| tasks_in(&mut f.body)),
        Stmt::While { condition, body } => {
            tasks_in(condition);
            tasks_in(body);
        }
        Stmt::Return(Some(e)) | Stmt::Expr(e) => tasks_in(e),
        _ => {}
    }
}

fn tasks_in(t: &mut SurfaceTerm) {
    let mut kind = (*t.kind).clone();
    match &mut kind {
        TermKind::Perform { effect, args } => {
            args.iter_mut().for_each(tasks_in);
            let body = match (effect.as_str(), args.as_mut_slice()) {
                ("spawn", [f]) | ("test", [_, f]) => Some(f),
                _ => None,
            };
            if let Some(f) = body {
                let mut task = parse_expr_at("() => Host::run(())", WRAPPER_BASE)
                    .expect("the task's wrapper parses");
                put_task(&mut task, f.clone());
                *f = task;
            }
        }
        TermKind::App {
            function,
            arguments,
        } => {
            tasks_in(function);
            arguments.iter_mut().for_each(tasks_in);
        }
        TermKind::Lam { body, .. } => tasks_in(body),
        TermKind::Union(ts) | TermKind::Product(ts) | TermKind::Tuple(ts) => {
            ts.iter_mut().for_each(tasks_in)
        }
        TermKind::Tagged { term, .. } | TermKind::Borrow { term, .. } => tasks_in(term),
        TermKind::If {
            condition,
            then,
            otherwise,
        } => {
            tasks_in(condition);
            tasks_in(then);
            if let Some(o) = otherwise {
                tasks_in(o);
            }
        }
        TermKind::Field { base, .. } | TermKind::Ascribe { term: base, .. } => tasks_in(base),
        TermKind::Block(stmts) => stmts.iter_mut().for_each(tasks_in_stmt),
        TermKind::Handle { body, handlers } => {
            tasks_in(body);
            for h in handlers {
                match h {
                    Handler::Return { body, .. } => tasks_in(body),
                    Handler::Operation { guard, body, .. } => {
                        if let Some(g) = guard {
                            tasks_in(g);
                        }
                        tasks_in(body);
                    }
                }
            }
        }
        TermKind::Budget { steps, body, .. } => {
            tasks_in(steps);
            tasks_in(body);
        }
        TermKind::Match {
            scrutinee, arms, ..
        } => {
            tasks_in(scrutinee);
            for arm in arms {
                if let Some(g) = &mut arm.guard {
                    tasks_in(g);
                }
                tasks_in(&mut arm.body);
            }
        }
        TermKind::Record { fields, .. } => fields.iter_mut().for_each(|(_, v)| tasks_in(v)),
        TermKind::BorrowLam { lam, .. } => tasks_in(lam),
        _ => return,
    }
    if kind != *t.kind {
        *t = t.with_kind(kind, t.span);
    }
}

/// Makes the argument of the task's `host_run` the body `f`.
fn put_task(t: &mut SurfaceTerm, f: SurfaceTerm) {
    let mut kind = (*t.kind).clone();
    match &mut kind {
        TermKind::Lam { body, .. } => put_task(body, f),
        TermKind::App { arguments, .. } => arguments[0] = f,
        other => panic!("the task's wrapper has the shape it is written with: {other:?}"),
    }
    *t = t.with_kind(kind, t.span);
}
