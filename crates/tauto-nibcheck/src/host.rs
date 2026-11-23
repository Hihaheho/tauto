//! The standard effects (`std/builtin/os.taut`): which the host answers at the
//! top level, the permission each needs, and how a backend's program is put
//! under the host's handler that answers them
//! (`docs/design/host-effects.md`).

use crate::surface::{PRELUDE_BASE, Program, Stmt, TermKind};
use std::collections::BTreeSet;

/// The effects the host answers when they reach the top level unanswered.
pub const HOST_EFFECTS: &[&str] = &[
    "ref_new",
    "ref_get",
    "ref_set",
    "weak_of",
    "weak_get",
    "mutex_new",
    "mutex_claim",
    "mutex_take_claimed",
    "mutex_put",
    "mutex_withdraw",
    "atomic_new",
    "atomic_load",
    "atomic_store",
    "atomic_fetch_add",
    "stdout",
    "stderr",
    "stdin_bytes",
    "stdout_flush",
    "shutdown_token",
    "stdin",
    "argv",
    "exit",
    "stop",
    "wall_clock",
    "monotonic_clock",
    "uhost_add",
    "uhost_sub",
    "uhost_mul",
    "uhost_of_u64",
    "host_width",
    "hash_seed",
    "sleep",
    "timer",
    "wait",
    "random",
    "secure_random",
    "fs_read",
    "fs_write",
    "fs_read_bytes",
    "fs_write_bytes",
    "fs_read_under",
    "fs_read_bytes_under",
    "fs_create_dir",
    "fs_list_dir",
    "fs_remove",
    "fs_stat",
    "fs_read_link",
    "fs_write_new",
    "fs_rename",
    "fs_set_mode",
    "fs_lock",
    "fs_unlock",
    "fs_copy",
    "fs_canonicalize",
    "fs_temp_dir",
    "proc_spawn",
    "proc_read",
    "proc_write",
    "proc_close_stdin",
    "proc_wait",
    "proc_close",
    "proc_run",
    "env",
    "environ",
    "permission",
    "net",
    "net_addr",
    "net_resolve",
    "net_open",
    "net_write",
    "net_finish",
    "net_cancel",
    "net_read",
    "net_close",
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
        "fs_read"
        | "fs_read_bytes"
        | "fs_read_under"
        | "fs_read_bytes_under"
        | "fs_list_dir"
        | "fs_stat"
        | "fs_read_link"
        | "fs_canonicalize" => Some("read"),
        "fs_write" | "fs_write_bytes" | "fs_write_new" | "fs_create_dir" | "fs_remove"
        | "fs_rename" | "fs_set_mode" | "fs_lock" => Some("write"),
        "proc_run" | "proc_spawn" => Some("run"),
        "env" | "environ" => Some("env"),
        "net" | "net_addr" | "net_resolve" | "net_open" | "net_write" | "net_finish"
        | "net_cancel" | "net_read" | "net_close" => Some("net"),
        "tcp_listen" | "tcp_accept" | "tcp_connect" | "tcp_read" | "tcp_write" | "tcp_shutdown"
        | "tcp_close" | "tcp_unlisten" => Some("net"),
        "tls_accept" | "tls_connect" | "tls_read" | "tls_write" | "tls_shutdown" | "tls_close" => {
            Some("net")
        }
        _ => None,
    }
}

/// The permissions a run that performs `effects` needs before it starts.
/// `fs_temp_dir` grants nothing up front: a program that makes a temporary
/// directory may still read or write elsewhere, and it is asked for `read`
/// and `write` like any other, so that a request outside the temporary
/// directory is not denied after the run has started.
pub fn permissions<'e>(effects: impl IntoIterator<Item = &'e String>) -> BTreeSet<&'static str> {
    effects
        .into_iter()
        .flat_map(|e| {
            // A copy reads one path and writes another.
            if e.as_str() == "fs_copy" {
                vec!["read", "write"]
            } else {
                permission(e).into_iter().collect()
            }
        })
        .collect()
}

/// Where the spans of the wrapper start: after the prelude's, before nothing a
/// file can reach.
const WRAPPER_BASE: u32 = PRELUDE_BASE + (1 << 30);

/// The program with its top-level statements in `Entry::run(() => { … })`,
/// when the top level performs `main` or `test`: the statements are the
/// module's top level that `Entry::run` evaluates to find the entries and
/// again to call their bodies. The declarations stay at the top level; a
/// function does not see a top-level `let`, so moving the statements does not
/// change what a name means. The host's handler is not written here: the
/// lowering puts it outside the top level and each task
/// (`Lowerer::host_handle`). `None` when there are no entries or nothing to
/// move.
pub fn wrap(program: &Program, entries: bool) -> Option<Program> {
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
    let mut wrapper = tauto_parse::parse_program_unresolved_at(
        if entries {
            "let ^ran: () := Entry::run(() => ())"
        } else {
            return None;
        },
        WRAPPER_BASE,
    )
    .expect("the wrapper parses");
    if tauto_surface::bindings::declared_names(&crate::types::prelude_for(program).stmts)
        .iter()
        .any(|n| n.is_resolved())
    {
        tauto_surface::resolve::Resolver::new(tauto_surface::bindings::library_bindings())
            .statements(&mut wrapper.stmts);
    }
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

fn fill(t: &mut crate::surface::SurfaceTerm, body: Vec<Stmt>) {
    let mut kind = (*t.kind).clone();
    match &mut kind {
        TermKind::App { arguments, .. } => fill(&mut arguments[0], body),
        TermKind::Lam { body: inner, .. } if matches!(&*inner.kind, TermKind::App { arguments, .. } if !arguments.is_empty()) => {
            fill(inner, body)
        }
        TermKind::Lam { body: unit, .. } => {
            let mut stmts = body;
            stmts.push(Stmt::Expr((**unit).clone()));
            **unit = crate::surface::SurfaceTerm::new(TermKind::Block(stmts), unit.span);
        }
        other => panic!("the wrapper has the shape it is written with: {other:?}"),
    }
    *t = t.with_kind(kind, t.span);
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn a_temporary_directory_does_not_stand_in_for_read_or_write() {
        let effects: Vec<String> = ["fs_temp_dir", "fs_read", "fs_write"]
            .into_iter()
            .map(String::from)
            .collect();
        let needed = permissions(effects.iter());
        assert!(needed.contains("read") && needed.contains("write"));
    }
}

/// Whether `effect` is one of the operations on a `Ref` or a `Weak` the
/// host answers (`ref_new`, `ref_get`, `ref_set`, `weak_of`, `weak_get`),
/// or on a `Mutex` or an `Atomic` (`mutex_new`, `atomic_load`, …).
pub fn is_storage_operation(effect: &crate::surface::Name) -> bool {
    [
        "ref_new",
        "ref_get",
        "ref_set",
        "weak_of",
        "weak_get",
        "mutex_new",
        "mutex_claim",
        "mutex_take_claimed",
        "mutex_put",
        "mutex_withdraw",
        "atomic_new",
        "atomic_load",
        "atomic_store",
        "atomic_fetch_add",
    ]
    .iter()
    .any(|op| tauto_surface::bindings::is_library(effect, op))
}
