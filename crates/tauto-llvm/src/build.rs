//! The text of one function being written: its instructions in order, the
//! slots of its frame apart at the top, and fresh names.

use std::fmt::Write;

pub struct Body {
    allocas: String,
    text: String,
    next: usize,
    /// Whether the block being written has no last instruction yet.
    open: bool,
}

impl Body {
    pub fn new() -> Body {
        Body {
            allocas: String::new(),
            text: String::new(),
            next: 0,
            open: true,
        }
    }

    pub fn tmp(&mut self) -> String {
        self.next += 1;
        format!("%t{}", self.next)
    }

    pub fn label(&mut self) -> String {
        self.next += 1;
        format!("L{}", self.next)
    }

    /// Writes an instruction. Code after a block's last instruction (what
    /// follows a `return`) is never run: it goes in a block of its own that
    /// nothing jumps to.
    pub fn ins(&mut self, line: impl AsRef<str>) {
        if !self.open {
            let dead = self.label();
            let _ = writeln!(self.text, "{dead}:");
            self.open = true;
        }
        let _ = writeln!(self.text, "  {}", line.as_ref());
    }

    /// Writes an instruction that gives a value, and names the value.
    pub fn def(&mut self, rhs: impl AsRef<str>) -> String {
        let t = self.tmp();
        self.ins(format!("{t} = {}", rhs.as_ref()));
        t
    }

    /// Writes a block's last instruction.
    pub fn end(&mut self, line: impl AsRef<str>) {
        self.ins(line);
        self.open = false;
    }

    pub fn br(&mut self, label: &str) {
        self.end(format!("br label %{label}"));
    }

    pub fn condbr(&mut self, cond: &str, then: &str, otherwise: &str) {
        self.end(format!("br i1 {cond}, label %{then}, label %{otherwise}"));
    }

    /// Starts the block `label`; the block before it goes on into it.
    pub fn start(&mut self, label: &str) {
        if self.open {
            self.br(label);
        }
        let _ = writeln!(self.text, "{label}:");
        self.open = true;
    }

    /// A slot of the frame of `words` words, and its address.
    pub fn alloca(&mut self, words: usize) -> String {
        let p = self.tmp();
        let _ = writeln!(self.allocas, "  {p} = alloca [{} x i64]", words.max(1));
        p
    }

    /// A slot of the frame for a text being built.
    pub fn alloca_buf(&mut self) -> String {
        let p = self.tmp();
        let _ = writeln!(self.allocas, "  {p} = alloca %Buf");
        p
    }

    /// The address `words` words after `p`.
    pub fn gep(&mut self, p: &str, words: usize) -> String {
        if words == 0 {
            p.to_string()
        } else {
            self.def(format!("getelementptr i64, ptr {p}, i64 {words}"))
        }
    }

    pub fn load(&mut self, p: &str, at: usize, words: usize) -> Vec<String> {
        (0..words)
            .map(|i| {
                let q = self.gep(p, at + i);
                self.def(format!("load i64, ptr {q}"))
            })
            .collect()
    }

    pub fn store(&mut self, p: &str, at: usize, vals: &[String]) {
        for (i, v) in vals.iter().enumerate() {
            let q = self.gep(p, at + i);
            self.ins(format!("store i64 {v}, ptr {q}"));
        }
    }

    /// The address a word holds.
    pub fn ptr(&mut self, word: &str) -> String {
        self.def(format!("inttoptr i64 {word} to ptr"))
    }

    /// An address as a word.
    pub fn word(&mut self, ptr: &str) -> String {
        self.def(format!("ptrtoint ptr {ptr} to i64"))
    }

    /// A word that is a `Bool`, as a condition.
    pub fn cond(&mut self, word: &str) -> String {
        self.def(format!("icmp ne i64 {word}, 0"))
    }

    /// A condition as a `Bool`'s word.
    pub fn bool(&mut self, cond: &str) -> String {
        self.def(format!("zext i1 {cond} to i64"))
    }

    /// The function's text: `header` is its `define` line without the brace.
    pub fn finish(self, header: &str) -> String {
        format!(
            "{header} {{\nentry:\n{}  br label %start\nstart:\n{}}}\n\n",
            self.allocas, self.text
        )
    }
}
