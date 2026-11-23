//! Reads a function in block form (`blocks { … }`) as `print_blocks`
//! writes it.

use super::*;
use crate::blocks::{BBlock, BlockFn, Edge, EdgeKind, Inst, Region, Shell, Slot, Term, Value};
use crate::decision::Case;

/// A function written as `fn … = blocks { … }`, read against the package
/// whose data types, operations and functions it names. The function comes
/// back with a unit body: its body is the blocks.
pub fn parse_blocks(pkg: &Package, text: &str) -> Result<(FnInst, BlockFn), ParseError> {
    let toks = lex(text).map_err(|(message, span)| ParseError { message, span })?;
    let mut p = Parser {
        toks,
        at: 0,
        names: HashMap::new(),
        bound: HashMap::new(),
        insts: Vec::new(),
        pkg: pkg.clone(),
    };
    p.expect_word("fn")?;
    let f = p.fn_head()?;
    p.expect("=")?;
    p.expect_word("blocks")?;
    p.expect("{")?;
    let bf = p.block_fn()?;
    if *p.tok() != Tok::End {
        return p.err("expected the end of the function");
    }
    Ok((f, bf))
}

impl Parser {
    /// `b3`.
    fn block_ref(&mut self) -> R<usize> {
        self.numbered("b", "a block: bN")
    }

    /// `region3`.
    fn region_ref(&mut self) -> R<usize> {
        self.numbered("region", "a region: regionN")
    }

    fn numbered(&mut self, prefix: &str, what: &str) -> R<usize> {
        if let Tok::Word(w) = self.tok()
            && let Some(rest) = w.strip_prefix(prefix)
            && let Ok(n) = rest.parse::<usize>()
            && !rest.starts_with('+')
        {
            self.bump();
            return Ok(n);
        }
        self.err(format!("expected {what}"))
    }

    fn is_numbered(&self, prefix: &str) -> bool {
        matches!(self.tok(), Tok::Word(w)
            if w.strip_prefix(prefix).is_some_and(|r| !r.is_empty() && r.bytes().all(|b| b.is_ascii_digit())))
    }

    fn typed_binders(&mut self) -> R<Vec<(Local, Ty)>> {
        self.parens(|p| {
            let l = p.binding()?;
            p.expect(":")?;
            let t = p.ty()?;
            Ok((l, t))
        })
    }

    fn path(&mut self) -> R<Vec<usize>> {
        self.expect("[")?;
        self.until("]", &mut |p| p.number())
    }

    fn value(&mut self) -> R<Value> {
        if self.eat("%") {
            return Ok(Value::Region(self.number()?));
        }
        Ok(Value::Leaf(self.expr()?))
    }

    /// The blocks and the rest of a body, up to the `}` that closes it.
    fn block_fn(&mut self) -> R<BlockFn> {
        let mut f = BlockFn::default();
        loop {
            if self.eat("}") {
                return Ok(f);
            }
            if self.is_numbered("b") {
                let at = self.span();
                let i = self.block_ref()?;
                if i != f.blocks.len() {
                    return Err(ParseError {
                        message: format!("the next block is b{}", f.blocks.len()),
                        span: at,
                    });
                }
                let b = self.bblock()?;
                f.blocks.push(b);
            } else if self.eat_word("regions") {
                self.expect("{")?;
                while !self.eat("}") {
                    let at = self.span();
                    let i = self.region_ref()?;
                    if i != f.regions.len() {
                        return Err(ParseError {
                            message: format!("the next region is region{}", f.regions.len()),
                            span: at,
                        });
                    }
                    self.expect("=")?;
                    let r = if self.eat_word("none") {
                        None
                    } else {
                        Some(self.region()?)
                    };
                    self.expect(";")?;
                    f.regions.push(r);
                }
            } else if self.eat_word("variant") {
                let r = self.region_ref()?;
                let path = self.path()?;
                self.expect(";")?;
                f.variants.insert((r, path));
            } else if self.eat_word("counts") {
                self.expect_word("opaque")?;
                f.opaque = self.number()?;
                self.expect_word("refutable")?;
                f.refutable = self.number()?;
                self.expect(";")?;
            } else if self.eat_word("closure") {
                let at = self.span();
                let i: usize = self.number()?;
                if i != f.closures.len() {
                    return Err(ParseError {
                        message: format!("the next closure is closure {}", f.closures.len()),
                        span: at,
                    });
                }
                self.expect("{")?;
                let c = self.block_fn()?;
                f.closures.push(c);
            } else {
                return self.err("expected a block, `regions`, `variant`, `counts` or `closure`");
            }
        }
    }

    fn region(&mut self) -> R<Region> {
        let start = self.span();
        let shell = if self.eat_word("node") {
            Shell::Node(self.expr()?)
        } else if self.eat_word("block") {
            let ty = self.ty()?;
            Shell::Block {
                ty,
                span: self.since(start),
            }
        } else if self.eat_word("call") {
            Shell::Call(self.expr()?)
        } else if self.eat_word("while") {
            let tick = self.tick()?;
            Shell::While {
                span: self.since(start),
                tick,
            }
        } else {
            return self.err("expected `none`, `node`, `block`, `call` or `while`");
        };
        self.expect_word("slots")?;
        let slots = self.parens(|p| {
            if p.eat_word("operand") {
                Ok(Slot::Operand(p.value()?))
            } else {
                p.expect_word("body")?;
                Ok(Slot::Body(p.block_ref()?))
            }
        })?;
        Ok(Region { shell, slots })
    }

    fn bblock(&mut self) -> R<BBlock> {
        let params = self.typed_binders()?;
        let param = if self.eat("->") {
            Some(self.ty()?)
        } else {
            None
        };
        let owner = if self.eat_word("owner") {
            Some(self.region_ref()?)
        } else {
            None
        };
        let join_of = if self.eat_word("joins") {
            Some(self.region_ref()?)
        } else {
            None
        };
        self.expect(":")?;
        let mut insts = Vec::new();
        loop {
            if let Some(term) = self.term()? {
                self.expect(";")?;
                return Ok(BBlock {
                    param,
                    owner,
                    params,
                    join_of,
                    insts,
                    term,
                });
            }
            let inst = self.block_inst()?;
            self.expect(";")?;
            insts.push(inst);
        }
    }

    fn block_inst(&mut self) -> R<Inst> {
        let start = self.span();
        let Tok::Word(w) = self.tok().clone() else {
            return self.err("expected an instruction or a terminator");
        };
        self.bump();
        Ok(match w.as_str() {
            "let" | "var" => {
                let stack = w == "let" && self.eat_word("stack");
                let local = self.binding()?;
                self.expect(":")?;
                let ty = self.ty()?;
                self.expect(":=")?;
                let init = self.value()?;
                let span = self.since(start);
                if w == "let" {
                    Inst::Let {
                        local,
                        ty,
                        init,
                        span,
                        stack,
                    }
                } else {
                    Inst::Var {
                        local,
                        ty,
                        init,
                        span,
                    }
                }
            }
            "set" => {
                let target = self.place()?;
                self.expect(":=")?;
                let value = self.value()?;
                Inst::Assign {
                    target,
                    value,
                    span: self.since(start),
                }
            }
            "eval" => Inst::Eval(self.value()?),
            "bind" => {
                let local = self.binding()?;
                self.expect(":")?;
                let ty = self.ty()?;
                self.expect(":=")?;
                let borrow = self.eat_word("borrow");
                self.expect_word("part")?;
                let path = self.path()?;
                Inst::Bind {
                    local,
                    ty,
                    path,
                    borrow,
                }
            }
            "unpack" => {
                let path = self.path()?;
                let last = self.eat_word("last");
                Inst::Unpack { path, last }
            }
            "release" => Inst::Release {
                path: self.path()?,
            },
            "end" => Inst::End(self.binding()?),
            "open" => Inst::Open(self.region_ref()?),
            "close" => {
                let r = self.region_ref()?;
                let v = if self.eat_word("with") {
                    Some(self.value()?)
                } else {
                    None
                };
                Inst::Close(r, v)
            }
            _ => {
                self.at -= 1;
                return self.err("expected an instruction or a terminator");
            }
        })
    }

    fn case(&mut self) -> R<Case> {
        let Tok::Word(w) = self.tok().clone() else {
            return self.err("expected a case");
        };
        self.bump();
        self.expect("(")?;
        let c = match w.as_str() {
            "ctor" => {
                let index = self.number()?;
                self.expect(",")?;
                let arity = self.number()?;
                Case::Ctor { index, arity }
            }
            "int" => Case::Int(self.number()?),
            "nat" => Case::Nat(self.number()?),
            "bool" => Case::Bool(self.boolean()?),
            "text" => Case::Text(self.string()?),
            "variant" => Case::Variant(self.number()?),
            _ => {
                self.at -= 2;
                return self.err("expected a case: ctor, int, nat, bool, text or variant");
            }
        };
        self.expect(")")?;
        Ok(c)
    }

    fn edge(&mut self) -> R<Edge> {
        let Tok::Word(w) = self.tok().clone() else {
            return self.err("expected an edge");
        };
        let kind = match w.as_str() {
            "body" => EdgeKind::Body,
            "ret" => EdgeKind::Ret,
            "direct" => EdgeKind::Direct,
            "abort" => EdgeKind::Abort,
            "susp" => EdgeKind::Susp,
            _ => return self.err("expected an edge: body, ret, direct, abort or susp"),
        };
        self.bump();
        let op = if self.eat("(") {
            let o = self.number()?;
            self.expect(")")?;
            Some(o)
        } else {
            None
        };
        self.expect("=>")?;
        let entry = self.block_ref()?;
        self.expect_word("params")?;
        let params = self.typed_binders()?;
        let refutable = self.eat_word("refutable");
        Ok(Edge {
            kind,
            op,
            entry,
            params,
            refutable,
        })
    }

    /// A terminator, or `None` where the word starts an instruction.
    fn term(&mut self) -> R<Option<Term>> {
        let start = self.span();
        let Tok::Word(w) = self.tok().clone() else {
            return Ok(None);
        };
        Ok(Some(match w.as_str() {
            "jump" => {
                self.bump();
                let b = self.block_ref()?;
                self.expect("(")?;
                let v = self.value()?;
                self.expect(")")?;
                Term::Jump(b, v)
            }
            "goto" => {
                self.bump();
                Term::Goto(self.block_ref()?)
            }
            "control" => {
                self.bump();
                let region = self.region_ref()?;
                self.expect_word("to")?;
                self.expect("[")?;
                let succs = self.until("]", &mut |p| p.block_ref())?;
                self.expect_word("join")?;
                let join = self.block_ref()?;
                Term::Control {
                    region,
                    succs,
                    join,
                }
            }
            "enter" => {
                self.bump();
                let region = self.region_ref()?;
                self.expect_word("at")?;
                let entry = self.block_ref()?;
                self.expect_word("join")?;
                let join = self.block_ref()?;
                let by_ref = self.eat_word("by_ref");
                Term::Enter {
                    region,
                    entry,
                    join,
                    by_ref,
                }
            }
            "test" => {
                self.bump();
                let path = self.path()?;
                self.expect("{")?;
                let mut cases = Vec::new();
                let mut default = None;
                while !self.eat("}") {
                    if !cases.is_empty() || default.is_some() {
                        self.expect(",")?;
                    }
                    if self.eat_word("_") {
                        self.expect("=>")?;
                        default = Some(self.block_ref()?);
                    } else {
                        let c = self.case()?;
                        self.expect("=>")?;
                        cases.push((c, self.block_ref()?));
                    }
                }
                Term::Test {
                    path,
                    cases,
                    default,
                }
            }
            "handle" => {
                self.bump();
                let region = self.region_ref()?;
                self.expect("{")?;
                let mut edges = Vec::new();
                while !self.eat("}") {
                    edges.push(self.edge()?);
                    self.expect(",")?;
                }
                self.expect_word("join")?;
                let join = self.block_ref()?;
                Term::Handle {
                    region,
                    edges,
                    join,
                }
            }
            "call" => {
                self.bump();
                let region = self.region_ref()?;
                self.expect_word("to")?;
                let join = self.block_ref()?;
                self.expect_word("abort")?;
                let abort = self.block_ref()?;
                Term::Call {
                    region,
                    abort,
                    join,
                }
            }
            "suspend" => {
                self.bump();
                let region = self.region_ref()?;
                self.expect_word("to")?;
                let join = self.block_ref()?;
                self.expect_word("abort")?;
                let abort = self.block_ref()?;
                let resumes = if self.eat_word("never") {
                    crate::effects::Resumes::Never
                } else if self.eat_word("once") {
                    crate::effects::Resumes::Once
                } else if self.eat_word("many") {
                    crate::effects::Resumes::Many
                } else {
                    return self.err("expected `never`, `once` or `many`");
                };
                self.expect_word("env")?;
                let env = self.typed_binders()?;
                Term::Suspend {
                    region,
                    abort,
                    join,
                    resumes,
                    env,
                }
            }
            "abort" => {
                self.bump();
                Term::Abort
            }
            "decline" => {
                self.bump();
                Term::Decline
            }
            "branch" => {
                self.bump();
                let value = self.value()?;
                self.expect_word("then")?;
                let then = self.block_ref()?;
                let els = if self.eat_word("else") {
                    Some(self.block_ref()?)
                } else {
                    None
                };
                Term::Branch { value, then, els }
            }
            "unreachable" => {
                self.bump();
                Term::Unreachable
            }
            "return" => {
                self.bump();
                let after_value = matches!(self.tok(), Tok::Word(w) if w == "cont")
                    && matches!(&self.toks[self.at + 1].0, Tok::Word(b)
                        if b.strip_prefix('b').is_some_and(|r| !r.is_empty() && r.bytes().all(|c| c.is_ascii_digit())));
                let value = if after_value {
                    None
                } else {
                    Some(self.value()?)
                };
                self.expect_word("cont")?;
                let cont = self.block_ref()?;
                Term::Return {
                    value,
                    span: self.since(start),
                    cont,
                }
            }
            "done" => {
                self.bump();
                Term::Done(self.value()?)
            }
            "pending" => {
                self.bump();
                Term::Pending
            }
            _ => return Ok(None),
        }))
    }
}
