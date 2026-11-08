//! Selecting references from the finite candidates captured by binding.
use super::*;

impl TypeReport {
    /// Replaces candidates at one checked occurrence and its patterns with
    /// the selected declaration. Descendant expressions are visited separately.
    pub fn resolve_selection_at(&self, term: &mut SurfaceTerm) -> Result<(), Message> {
        let operations = self.operation_facts.as_ref();
        let mut error = None;
        let id = term.id();
        match std::sync::Arc::make_mut(&mut term.kind) {
            TermKind::Var(name) | TermKind::Record { name, .. }
                if matches!(name, Name::Selection(_)) =>
            {
                if let Some(reference) = self.type_references.get(&id) {
                    *name = reference.clone();
                    return Ok(());
                }
                match self.datas.resolve_ctor(name, self.terms.get(&id)) {
                    Ok((owner, index)) => {
                        *name = self.datas.decls[owner].constructors[*index].name.clone()
                    }
                    Err(problem) => {
                        error.get_or_insert(problem);
                    }
                }
            }
            TermKind::Match {
                scrutinee, arms, ..
            } => {
                if let Some(ty) = self.terms.get(&scrutinee.id()) {
                    for arm in arms {
                        if let Err(problem) = pattern(&mut arm.pattern, ty, &self.datas) {
                            error.get_or_insert(problem);
                        }
                    }
                }
            }
            TermKind::Handle { body, handlers } => {
                for handler in handlers {
                    match handler {
                        crate::surface::Handler::Return { pattern: pat, .. } => {
                            if let Some(ty) = self.terms.get(&body.id()) {
                                if let Err(problem) = pattern(pat, ty, &self.datas) {
                                    error.get_or_insert(problem);
                                }
                            }
                        }
                        crate::surface::Handler::Operation { patterns, body, .. } => {
                            if let Some(instance) =
                                operations.and_then(|facts| facts.arm(body.id()))
                            {
                                for (pat, ty) in patterns.iter_mut().zip(&instance.params) {
                                    if let Err(problem) = pattern(pat, ty, &self.datas) {
                                        error.get_or_insert(problem);
                                    }
                                }
                            }
                        }
                    }
                }
            }
            _ => {}
        }
        error.map_or(Ok(()), Err)
    }
}

fn pattern(pattern: &mut Pattern, ty: &super::Ty, datas: &super::Datas) -> Result<(), Message> {
    use super::Ty;
    if let Pattern::Tuple(items) = pattern {
        if super::is_pair_ty(ty.unborrowed()) {
            let types = super::pair_spine(ty.unborrowed());
            for (item, ty) in items.iter_mut().zip(&types) {
                self::pattern(item, ty, datas)?;
            }
        }
        return Ok(());
    }
    if let Pattern::Bind(Name::Selection(selection)) = pattern {
        if let Some(binding) = selection.binding() {
            let name = Name::Selection(selection.clone());
            if !datas.nullary(&name, Some(ty)) {
                *pattern = Pattern::Bind(binding.clone().into());
                return Ok(());
            }
        }
    }
    let name = match pattern {
        Pattern::Bind(name) if datas.has_ctor(name) => name,
        Pattern::Ctor { name, .. } | Pattern::Record { name, .. } => name,
        _ => return Ok(()),
    };
    let (owner, index) = datas.resolve_ctor(name, Some(ty))?;
    let data = &datas.decls[owner];
    *name = if data.is_struct {
        owner.clone()
    } else {
        data.constructors[*index].name.clone()
    };
    let arguments = match ty.unborrowed() {
        Ty::Named(_, args) => args.as_slice(),
        _ => &[],
    };
    let fields = datas.fields(owner, *index, arguments);
    match pattern {
        Pattern::Ctor { args, .. } => {
            for (arg, (_, ty)) in args.iter_mut().zip(&fields) {
                self::pattern(arg, ty, datas)?;
            }
        }
        Pattern::Record {
            fields: patterns, ..
        } => {
            for (label, pattern) in patterns {
                if let Some((_, ty)) = fields
                    .iter()
                    .find(|(name, _)| name.as_deref() == Some(label.as_str()))
                {
                    self::pattern(pattern, ty, datas)?;
                }
            }
        }
        _ => {}
    }
    Ok(())
}
