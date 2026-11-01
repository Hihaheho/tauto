//! A bytecode machine for checked Tauto programs.
//!
//! `code` compiles each function of the program (`tauto_nir::Package`), in
//! the continuation-passing form the JavaScript backend also prints
//! (`tauto_nir::cps`), to a bytecode; `machine` runs it with its frames on a
//! stack of its own, where an operation's continuation is the frames above
//! its handler. The run's observable behavior is the other backends': what
//! it shows and writes, and the errors it ends with.

pub mod builtins;
pub mod code;
pub mod host;
pub mod hostcall;
pub mod machine;
pub mod syntax;
pub mod value;
pub mod wire;

pub use code::{Program, compile};
pub use host::{Captured, Host, Process};
pub use value::Error;

/// How a run ended.
#[derive(Debug)]
pub enum End {
    /// The top level returned.
    Done,
    /// `exit(code)`.
    Exit(i32),
    /// A run-time error, with its message.
    Error(String),
}

/// Runs the program's top level with at most `steps` steps of the host's
/// limit.
pub fn run(program: &Program, host: &mut dyn Host, steps: u64) -> End {
    let mut m = machine::Machine::new(program, host, steps);
    match m.run_top() {
        Ok(_) => End::Done,
        Err(Error::Exit(code)) => End::Exit(code),
        Err(Error::Runtime(message)) => End::Error(message),
    }
}
