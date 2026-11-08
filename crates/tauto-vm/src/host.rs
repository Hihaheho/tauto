//! What the machine asks of the world: where `show` and the program's
//! output go, its arguments, and its permissions. Files, the environment,
//! clocks and randomness are the system's (`tauto_rt::host::System`).

use tauto_rt::permissions::Permissions;

use crate::value::Value;

pub trait Host {
    fn show(&mut self, name: &str, value: &str);
    fn stdout(&mut self, text: &str);
    fn stderr(&mut self, text: &str);
    fn args(&self) -> Vec<String>;
    fn permissions(&mut self) -> &mut Permissions;
    /// Calls extern function `index` of the program (`Program::externs`).
    /// A host that binds none answers that it has none.
    fn call_extern(&mut self, index: u32, args: Vec<Value>) -> Result<Value, String> {
        let _ = (index, args);
        Err("the machine has no host binding for this extern function".into())
    }
}

/// The process's: what the program writes goes to its standard streams.
pub struct Process {
    pub args: Vec<String>,
    pub permissions: Permissions,
}

impl Host for Process {
    fn show(&mut self, name: &str, value: &str) {
        use std::io::Write;
        let mut out = std::io::stdout().lock();
        let _ = writeln!(out, "{name} = {value}");
        let _ = out.flush();
    }

    fn stdout(&mut self, text: &str) {
        use std::io::Write;
        let mut out = std::io::stdout().lock();
        let _ = out.write_all(text.as_bytes());
        let _ = out.flush();
    }

    fn stderr(&mut self, text: &str) {
        use std::io::Write;
        let _ = std::io::stderr().write_all(text.as_bytes());
    }

    fn args(&self) -> Vec<String> {
        self.args.clone()
    }

    fn permissions(&mut self) -> &mut Permissions {
        &mut self.permissions
    }
}

/// A run that keeps what the program shows and writes, as a test reads it.
#[derive(Default)]
pub struct Captured {
    pub shows: Vec<String>,
    pub stdout: String,
    pub stderr: String,
    pub args: Vec<String>,
    pub permissions: Permissions,
}

impl Host for Captured {
    fn show(&mut self, name: &str, value: &str) {
        self.shows.push(format!("{name} = {value}"));
    }

    fn stdout(&mut self, text: &str) {
        self.stdout.push_str(text);
    }

    fn stderr(&mut self, text: &str) {
        self.stderr.push_str(text);
    }

    fn args(&self) -> Vec<String> {
        self.args.clone()
    }

    fn permissions(&mut self) -> &mut Permissions {
        &mut self.permissions
    }
}
