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
pub mod ct;
pub mod host;
pub mod hostcall;
pub mod image;
pub mod machine;
pub mod native;
pub mod syntax;
pub mod value;
pub mod wire;

pub use code::{Program, compile};
pub use host::{Captured, Host, Process};
pub use value::{Error, Value};

#[derive(Debug)]
pub enum End {
    Done,
    Exit(i32),
    Error(String),
}

/// Runs the program's top level with at most `steps` steps of the host's
/// limit.
pub fn run(program: &Program, host: &mut dyn Host, steps: u64) -> End {
    let mut m = machine::Machine::new(program, host, steps);
    tauto_rt::entry::start();
    match m.run_top() {
        Ok(_) => End::Done,
        Err(Error::Exit(code)) => End::Exit(code),
        Err(Error::Runtime(message)) => End::Error(message),
    }
}

/// Calls function instance `inst` of the program (an index of the
/// package's `fns`) with `args`, with at most `steps` steps.
pub fn call(
    program: &Program,
    host: &mut dyn Host,
    inst: u32,
    args: Vec<Value>,
    steps: u64,
) -> Result<value::Value, End> {
    let mut m = machine::Machine::new(program, host, steps);
    match m.run_fn(inst, args) {
        Ok(v) => Ok(v),
        Err(Error::Exit(code)) => Err(End::Exit(code)),
        Err(Error::Runtime(message)) => Err(End::Error(message)),
    }
}

/// What a counted call used: its steps, and the cells it made.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Used {
    pub steps: u64,
    pub cells: i128,
}

/// As `call`, with at most `max_cells` cells made in all, and what the call
/// used whether it answered or not.
pub fn call_counted(
    program: &Program,
    host: &mut dyn Host,
    inst: u32,
    args: Vec<Value>,
    steps: u64,
    max_cells: Option<i128>,
) -> (Result<value::Value, End>, Used) {
    let mut m = machine::Machine::new(program, host, steps);
    m.max_cells = max_cells;
    let ran = match m.run_fn(inst, args) {
        Ok(v) => Ok(v),
        Err(Error::Exit(code)) => Err(End::Exit(code)),
        Err(Error::Runtime(message)) => Err(End::Error(message)),
    };
    let used = Used {
        steps: steps - m.fuel_left(),
        cells: m.cells_made(),
    };
    (ran, used)
}
