//! The run-time errors, shared by the runtimes (the bytecode machine
//! `crates/tauto-vm`, the compiled programs) so that they say the same thing.

/// An integer operation overflowed, or a number does not fit the type it is
/// converted to.
pub const TOO_LARGE: &str = "the number is too large";
pub const DIVISION_BY_ZERO: &str = "division by zero";
pub const NO_ARM: &str = "no arm of the match fits";
/// The host's step limit ran out, outside any `budget`.
pub const STEP_LIMIT: &str = "interrupted: the step limit ran out";
/// [`STEP_LIMIT`] in Japanese; `eval-step-limit` of the toolchain's messages
/// says the same in each language.
pub const STEP_LIMIT_JA: &str = "中断: ステップの上限に達した";

/// Whether a run-time error is the host's step limit running out, in any
/// language it is written in.
pub fn is_step_limit(message: &str) -> bool {
    message.starts_with(STEP_LIMIT) || message.starts_with(STEP_LIMIT_JA)
}

/// What a compiled program says when its step limit of `limit` runs out, in
/// the language of the user who runs it: as the tauto command chooses it,
/// `$TAUTO_LANG`, `$LC_ALL`, `$LC_MESSAGES`, `$LANG`, else English. The
/// program carries no other language than these.
pub fn step_limit_ran_out(limit: u64) -> String {
    if japanese() {
        format!(
            "{STEP_LIMIT_JA} （{limit} ステップ。`TAUTO_STEP_LIMIT=N` で増やせる。`--allow-div` で上限をなくせる）"
        )
    } else {
        format!(
            "{STEP_LIMIT} after {limit} steps; `TAUTO_STEP_LIMIT=N` raises it, `--allow-div` lifts it"
        )
    }
}

fn japanese() -> bool {
    let setting = ["TAUTO_LANG", "LC_ALL", "LC_MESSAGES", "LANG"]
        .iter()
        .find_map(|k| std::env::var(k).ok().filter(|v| !v.is_empty()));
    setting.is_some_and(|s| {
        s.split(['_', '-', '.', '@'])
            .next()
            .is_some_and(|l| l.eq_ignore_ascii_case("ja"))
    })
}

/// A wait for a signal that nothing can raise: no other task runs.
pub const DEADLOCK: &str = "deadlock: a wait for a signal that no task can raise";

/// What the host says of an operation nothing handles. It answers
/// `overflow` and `divzero` by stopping the program with what went wrong.
pub fn nothing_handles(effect: &str) -> String {
    match effect {
        "overflow" => TOO_LARGE.into(),
        "divzero" => DIVISION_BY_ZERO.into(),
        _ => format!("nothing handles {effect}"),
    }
}
