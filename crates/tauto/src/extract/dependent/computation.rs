//! Computations preserve effect requests and their continuations independently
//! of the erased value representation. Handlers consume requests by identity.
use super::*;
use crate::surface::Handler;

pub(super) const REQUEST: &str = "TautoErasedRequest#r0";
pub(super) const HANDLER: &str = "TautoErasedHandler#r0";
pub(super) const HELPERS: &[&str] = &[
    "TautoErasedBind#r0",
    "TautoErasedHandle#r0",
    "TautoErasedDispatch#r0",
    "TautoErasedFinish#r0",
];

pub(super) fn definitions() -> String {
    r#"
fn TautoErasedBind#r0(value: $V, next: $V): $V {
  match value {
    $R(tag, args, continuation) => $R(tag, args, $F(1, (xs: List($V)) => TautoErasedBind#r0(TautoErasedApply#r0(continuation, xs), next)))
    _ => TautoErasedApply#r0(next, [value])
  }
}
fn TautoErasedHandle#r0(value: $V, handlers: List($V), returned: $V): $V {
  match value {
    $R(tag, args, continuation) => {
      let k := $F(1, (xs: List($V)) => TautoErasedHandle#r0(TautoErasedApply#r0(continuation, xs), handlers, returned))
      TautoErasedDispatch#r0(tag, args, k, handlers)
    }
    _ => TautoErasedApply#r0(returned, [value])
  }
}
fn TautoErasedDispatch#r0(tag: nat, args: List($V), continuation: $V, handlers: List($V)): $V {
  match handlers {
    Nil => $R(tag, args, continuation)
    Cons(head, tail) => match head {
      $H(key, body) => if tag == key {
        TautoErasedApply#r0(body, TautoErasedConcat#r0(args, [continuation]))
      } else { TautoErasedDispatch#r0(tag, args, continuation, tail) }
      _ => extract_unreachable()
    }
  }
}
fn TautoErasedFinish#r0(value: $V): $V {
  match value { $R(_, _, _) => extract_unreachable()
    _ => value }
}
"#.replace("$V", VALUE).replace("$R", REQUEST).replace("$F", FUN).replace("$H", HANDLER)
}

impl Eraser<'_> {
    fn bind(
        &mut self,
        value: &str,
        name: &Name,
        body: &str,
        scope: &Scope,
    ) -> Result<String, Message> {
        let next = self.closure_in(&[name.clone()], body, scope)?;
        Ok(format!("TautoErasedBind#r0({value}, {next})"))
    }

    fn requests(&self, term: &SurfaceTerm, scope: &Scope) -> bool {
        match &*term.kind {
            TermKind::Perform { .. } | TermKind::Handle { .. } => true,
            TermKind::Lam { .. } | TermKind::Pi { .. } => false,
            TermKind::App {
                function,
                arguments,
            } => {
                let calls = match &*function.kind {
                    TermKind::Var(name) if !scope.contains(name) => {
                        self.functions.get(name).map_or_else(
                            || {
                                !self.checked.signatures.contains_key(name)
                                    && !self.checked.families.contains_key(name)
                            },
                            |(_, f)| f.effects.as_ref().is_some_and(|r| !r.is_empty()),
                        )
                    }
                    _ => true,
                };
                calls || arguments.iter().any(|arg| self.requests(arg, scope))
            }
            TermKind::Block(stmts)
                if stmts
                    .iter()
                    .any(|s| matches!(s, Stmt::Var { .. } | Stmt::Assign { .. })) =>
            {
                true
            }
            _ => {
                let mut found = false;
                crate::surface::walk::children(&mut term.clone(), &mut |child| {
                    found |= self.requests(child, scope)
                });
                found
            }
        }
    }

    pub(super) fn computation(
        &mut self,
        t: &SurfaceTerm,
        locals: &Scope,
    ) -> Result<String, Message> {
        if !self.requests(t, locals) {
            if let TermKind::Var(name) = &*t.kind
                && let Some(Binding::Mutable { pack, .. }) = locals.bindings.get(name)
            {
                return Ok(pack.replace("$v", &format!("Ref::get({})", self.symbol(name))));
            }
            return self.expr_value(t, locals);
        }
        // Binding forms scope their continuations themselves. For other terms,
        // evaluate their immediate operands from left to right before building
        // the value or making the call.
        match &*t.kind {
            TermKind::Var(name)
                if matches!(locals.bindings.get(name), Some(Binding::Mutable { .. })) =>
            {
                let Some(Binding::Mutable { pack, .. }) = locals.bindings.get(name) else {
                    unreachable!()
                };
                return Ok(pack.replace("$v", &format!("Ref::get({})", self.symbol(name))));
            }
            TermKind::Block(stmts) => return self.sequence(stmts, locals),
            TermKind::Handle { body, handlers } => {
                let value = self.expr(body, locals)?;
                let identity = self.fresh("Result");
                let mut returned = self.closure(&[identity.clone()], &raw(&identity));
                let mut operations = Vec::new();
                for handler in handlers {
                    let mut inner = locals.clone();
                    match handler {
                        Handler::Return { pattern, body } => {
                            let name = self.handler_name(pattern)?;
                            inner.insert(name.clone());
                            let body = self.expr(body, &inner)?;
                            returned = self.closure_in(&[name], &body, &inner)?;
                        }
                        Handler::Operation {
                            effect,
                            patterns,
                            cont,
                            guard,
                            body,
                            ..
                        } => {
                            if guard.is_some() {
                                return Err("dependent extraction: guarded handler".into());
                            }
                            let mut names = patterns
                                .iter()
                                .map(|p| self.handler_name(p))
                                .collect::<Result<Vec<_>, _>>()?;
                            names
                                .push(cont.clone().unwrap_or_else(|| self.fresh("Discard").into()));
                            inner.extend(names.iter().cloned());
                            let body = self.expr(body, &inner)?;
                            let body = self.closure_in(&names, &body, &inner)?;
                            let tag = self.effect_tag(effect);
                            operations.push(format!("{HANDLER}({tag}, {body})"));
                        }
                    }
                }
                return Ok(format!(
                    "TautoErasedHandle#r0({value}, [{}], {returned})",
                    operations.join(", ")
                ));
            }
            _ => {}
        }
        let erased_slots = match &*t.kind {
            TermKind::App {
                function,
                arguments,
            } => match &*function.kind {
                TermKind::Var(name) if !locals.contains(name) => {
                    if let Some(sig) = self.checked.source_call_signature(name) {
                        if sig.result != Role::Value {
                            vec![true; arguments.len()]
                        } else {
                            let roles = self.roles(name)?;
                            let prefix = self
                                .inserted(t.id(), arguments.len(), Some(name))?
                                .map(|p| p.len())
                                .unwrap_or(if arguments.len() == roles.len() {
                                    0
                                } else {
                                    sig.implicit
                                });
                            roles
                                .get(prefix..)
                                .unwrap_or_default()
                                .iter()
                                .map(|r| *r != Role::Value)
                                .collect()
                        }
                    } else {
                        Vec::new()
                    }
                }
                _ => Vec::new(),
            },
            _ => Vec::new(),
        };
        let erase: Vec<_> = match &*t.kind {
            TermKind::App { arguments, .. } => arguments
                .iter()
                .enumerate()
                .map(|(i, arg)| erased_slots.get(i) == Some(&true) && !self.requests(arg, locals))
                .collect(),
            _ => Vec::new(),
        };
        let mut rewritten = t.clone();
        let mut inner = locals.clone();
        let mut operands = Vec::new();
        let mut replace = |term: &mut SurfaceTerm| {
            let name = self.fresh("Operand");
            operands.push((name.clone(), term.clone()));
            *term = SurfaceTerm::var(&name, term.span);
            inner.insert(name.into());
        };
        match std::sync::Arc::make_mut(&mut rewritten.kind) {
            TermKind::App {
                function,
                arguments,
            } => {
                if !matches!(&*function.kind, TermKind::Var(n) if !locals.contains(n)) {
                    replace(function);
                }
                for (index, arg) in arguments.iter_mut().enumerate() {
                    if erase.get(index) == Some(&true) {
                        *arg = SurfaceTerm::var("Type", arg.span);
                    } else {
                        replace(arg);
                    }
                }
            }
            TermKind::Perform { args, .. } => {
                for arg in args {
                    replace(arg);
                }
            }
            TermKind::Match { scrutinee, .. } => replace(scrutinee),
            TermKind::If { condition, .. } => replace(condition),
            TermKind::Field { base, .. } => replace(base),
            TermKind::Ascribe { term, .. } | TermKind::Tagged { term, .. } => replace(term),
            _ => {}
        }
        let mut body = match &*rewritten.kind {
            TermKind::Perform { effect, args } => {
                let tag = self.effect_tag(effect);
                let value = self.fresh("Answer");
                let resume = self.closure(&[value.clone()], &raw(&value));
                format!(
                    "{REQUEST}({tag}, [{}], {resume})",
                    args.iter().map(show).collect::<Vec<_>>().join(", ")
                )
            }
            _ => self.expr_value(&rewritten, &inner)?,
        };
        for (name, operand) in operands.into_iter().rev() {
            let value = self.expr(&operand, locals)?;
            body = self.bind(&value, &name.into(), &body, &inner)?;
        }
        Ok(body)
    }

    fn handler_name(&mut self, pattern: &Pattern) -> Result<Name, Message> {
        match pattern {
            Pattern::Bind(name) => Ok(name.clone()),
            Pattern::Wild => Ok(self.fresh("Discard").into()),
            _ => Err("dependent extraction: handler pattern must bind a value".into()),
        }
    }

    fn sequence(&mut self, stmts: &[Stmt], locals: &Scope) -> Result<String, Message> {
        let Some((first, rest)) = stmts.split_first() else {
            return Ok(ERASED.into());
        };
        match first {
            Stmt::Var {
                name, ty, value, ..
            } => {
                let info = self.checked.local_types.get(name).cloned();
                let repr = if let Some(info) = info {
                    self.boundary(&info)?
                } else if let Some(ty) = ty {
                    self.native_field(ty, &BTreeMap::new())?
                } else {
                    None
                };
                let (native_type, pack, unpack) =
                    repr.unwrap_or_else(|| (VALUE.into(), "$v".into(), "$v".into()));
                let value = self.expr(value, locals)?;
                let initial = self.fresh("Initial");
                let mut inner = locals.clone();
                inner.bindings.insert(
                    name.clone(),
                    Binding::Mutable {
                        ty: native_type,
                        pack,
                        unpack: unpack.clone(),
                    },
                );
                let body = self.sequence(rest, &inner)?;
                let body = format!(
                    "{{ let {} := Ref::new({})\n {body} }}",
                    self.symbol(name),
                    unpack.replace("$v", &initial)
                );
                self.bind(&value, &initial.into(), &body, locals)
            }
            Stmt::Assign {
                name,
                place: None,
                value,
            } if matches!(locals.bindings.get(name), Some(Binding::Mutable { .. })) => {
                let value = self.expr(value, locals)?;
                let assigned = self.fresh("Assigned");
                let body = self.sequence(rest, locals)?;
                let Some(Binding::Mutable { unpack, .. }) = locals.bindings.get(name) else {
                    unreachable!()
                };
                let body = format!(
                    "{{ Ref::set({}, {})\n {body} }}",
                    self.symbol(name),
                    unpack.replace("$v", &assigned)
                );
                self.bind(&value, &assigned.into(), &body, locals)
            }
            Stmt::Let {
                name, ty, value, ..
            } => {
                let mut inner = locals.clone();
                if ty.as_ref().is_some_and(|t| self.prop(t)) {
                    inner.erase(name.clone());
                    let body = self.sequence(rest, &inner)?;
                    if !self.requests(value, locals) {
                        return Ok(body);
                    }
                    let value = self.expr(value, locals)?;
                    let discard = self.fresh("ProofResult");
                    return self.bind(&value, &discard.into(), &body, &inner);
                }
                let value = self.expr(value, locals)?;
                inner.insert(name.clone());
                let body = self.sequence(rest, &inner)?;
                self.bind(&value, name, &body, &inner)
            }
            Stmt::Expr(value) => {
                let value = self.expr(value, locals)?;
                if rest.is_empty() {
                    return Ok(value);
                }
                let discard = self.fresh("Discard");
                let body = self.sequence(rest, locals)?;
                self.bind(&value, &discard.into(), &body, locals)
            }
            _ => Err("dependent extraction: unsupported computation statement".into()),
        }
    }

    pub(super) fn effect_tag(&mut self, effect: &Name) -> usize {
        let next = self.effect_tags.len();
        *self.effect_tags.entry(effect.clone()).or_insert(next)
    }
}
