//! Classes and instances: their declarations are checked here, and each
//! method becomes a function that carries the class as a `where`.

use crate::surface::Name;
use std::collections::{HashMap, HashSet};

use super::{Checker, Kind, Param, ParamId, STRUCTURAL, Scheme, Ty};
use crate::surface::walk;
use crate::surface::{
    ClassDecl, Constraint, FnDecl, InstanceDecl, Program, Stmt, SurfaceTerm, TermKind,
};

pub(super) struct ClassInfo {
    pub decl: ClassDecl,
    pub bound: Kind,
    /// For a class of type constructors, the kind its parameter takes; the
    /// `bound` is what it makes.
    pub arg: Option<Kind>,
    pub in_prelude: bool,
}

pub(super) struct InstanceInfo {
    pub generics: Vec<(Param, Kind)>,
    pub head: Ty,
    /// The `where` of the instance: a class and the generic it constrains.
    pub preds: Vec<(Name, Param)>,
}

/// `C::m@H`: the function an instance of `C` for `H` gives `m`.
pub(super) fn member_fn(class: &ClassDecl, method: &str) -> Name {
    let index = class
        .methods
        .iter()
        .position(|m| m.name.as_str() == method)
        .expect("class method");
    match class.name.as_global() {
        Some(owner) => owner.class_member(index, false, method).into(),
        None => format!("{}::{method}", class.name).into(),
    }
}

pub(super) fn instance_fn(class: &ClassDecl, method: &str, head: &Name) -> Name {
    let member = member_fn(class, method);
    match (member.as_global(), head.as_global()) {
        (Some(member), Some(head)) => member
            .specialize(&format!("head:{:?}", head.id()), format!("{member}@{head}"))
            .into(),
        _ => format!("{member}@{head}").into(),
    }
}

fn mentions(t: &SurfaceTerm, name: &Name) -> bool {
    let mut t = t.clone();
    let mut found = false;
    walk::term(&mut t, &mut |x| {
        if matches!(&*x.kind, TermKind::Var(v) if v == name) {
            found = true;
        }
    });
    found
}

/// `t` with `with` in the place of each `name`; what is put in is not
/// searched again.
pub(super) fn replace(t: &SurfaceTerm, name: &Name, with: &SurfaceTerm) -> SurfaceTerm {
    fn go(t: &mut SurfaceTerm, name: &Name, with: &SurfaceTerm) {
        if matches!(&*t.kind, TermKind::Var(v) if v == name) {
            *t = with.clone();
        } else {
            walk::children(t, &mut |c| go(c, name, with));
        }
    }
    let mut t = t.clone();
    go(&mut t, name, with);
    t
}

/// The type constructor at the head of a type, as the instance table keys it.
fn constructor(t: &Ty, resolved: bool) -> Option<Name> {
    let builtin = |name: &str| {
        if resolved {
            tauto_surface::bindings::library_name(name)
        } else {
            Name::from(name)
        }
    };
    match t {
        Ty::Named(n, _) => Some(n.clone()),
        Ty::Int(_) | Ty::Bool | Ty::Text | Ty::Float | Ty::Float32 | Ty::Decimal | Ty::Unit => {
            Some(builtin(&t.to_string()))
        }
        _ => None,
    }
}

impl Checker {
    /// Checks the declarations of classes and instances, and gives
    /// each method its function. The functions the program's instances
    /// define are returned, to be checked like the program's own.
    pub(super) fn declare_classes(&mut self, program: &Program, prelude: &Program) -> Vec<FnDecl> {
        let own_classes: HashSet<&Name> = program
            .stmts
            .iter()
            .filter_map(|s| match s {
                Stmt::Class(c) => Some(&c.name),
                _ => None,
            })
            .collect();
        let own_types: HashSet<&Name> = program
            .stmts
            .iter()
            .filter_map(|s| match s {
                Stmt::Struct(d) | Stmt::Enum(d) => Some(&d.name),
                _ => None,
            })
            .collect();
        let mut classes: Vec<(&ClassDecl, bool)> = Vec::new();
        for s in &prelude.stmts {
            if let Stmt::Class(c) = s
                && !own_classes.contains(&c.name)
            {
                classes.push((c, true));
            }
        }
        for s in &program.stmts {
            if let Stmt::Class(c) = s {
                classes.push((c, false));
            }
        }
        let mut declared = Vec::new();
        for (c, in_prelude) in classes {
            if self.declare_class(c, in_prelude, &own_types) {
                declared.push(c);
            }
        }
        for s in &program.stmts {
            if let Stmt::Struct(d) | Stmt::Enum(d) = s
                && self.classes.get(&d.name).is_some_and(|c| c.in_prelude)
            {
                self.error(format!("{} is already a class", d.name), d.span);
            }
        }
        // The methods, now that every class is known.
        for c in declared {
            self.declare_methods(c);
        }
        let mut instances: Vec<(&InstanceDecl, bool)> = Vec::new();
        for s in &prelude.stmts {
            if let Stmt::Instance(i) = s
                && !own_classes.contains(&i.class)
            {
                instances.push((i, true));
            }
        }
        for s in &program.stmts {
            if let Stmt::Instance(i) = s {
                instances.push((i, false));
            }
        }
        let mut synthesized = Vec::new();
        for (i, in_prelude) in instances {
            self.declare_instance(i, in_prelude, &own_classes, &own_types, &mut synthesized);
        }
        synthesized
    }

    fn declare_class(
        &mut self,
        c: &ClassDecl,
        in_prelude: bool,
        own_types: &HashSet<&Name>,
    ) -> bool {
        if STRUCTURAL.contains(&c.name.as_str()) {
            self.error(format!("{} is built in", c.name), c.span);
            return false;
        }
        if self.classes.contains_key(&c.name) {
            self.error(format!("class {} is declared twice", c.name), c.span);
            return false;
        }
        if !in_prelude && own_types.contains(&c.name) {
            self.error(format!("{} is already a type", c.name), c.span);
            return false;
        }
        if c.parameters.first().is_some_and(|(_, ty)| {
            !matches!(&*ty.kind, TermKind::Var(name) if name.as_str() == "Type")
                && !c
                    .bound
                    .as_deref()
                    .is_some_and(|bound| Kind::parse_ctor(bound).is_some())
        }) {
            self.error(
                "value-indexed classes require checked dictionary extraction",
                c.span,
            );
            return false;
        }
        if c.arity != 1 {
            self.error(
                format!("class {} takes one parameter, not {}", c.name, c.arity),
                c.span,
            );
            return false;
        }
        let (bound, arg) = match c.bound.as_deref() {
            None => (Kind::Affine, None),
            Some(b) => match (Kind::parse(b), Kind::parse_ctor(b)) {
                (Some(k), _) => (k, None),
                (None, Some((arg, result))) => (result, Some(arg)),
                _ => {
                    self.error(format!("{b} is not a kind"), c.span);
                    return false;
                }
            },
        };
        let mut seen = HashSet::new();
        for m in &c.methods {
            if !seen.insert(m.name.as_str()) {
                self.error(format!("{}::{} is declared twice", c.name, m.name), m.span);
            }
            if !m.where_.is_empty() {
                self.error(
                    format!(
                        "{}.{} has no where: write it outside the class",
                        c.name, m.name
                    ),
                    m.span,
                );
            }
            let mentioned = m
                .param_types
                .iter()
                .flatten()
                .any(|t| mentions(t, &c.param))
                || m.result.as_ref().is_some_and(|r| mentions(r, &c.param));
            if !mentioned {
                self.error(
                    format!("{}::{} does not mention {}", c.name, m.name, c.param),
                    m.span,
                );
            }
        }
        // A law is a statement about the methods, and a method that performs
        // effects has none.
        if !c.laws.is_empty() {
            for m in &c.methods {
                if m.effects.as_ref().is_some_and(|e| !e.is_empty()) {
                    self.error(
                        format!(
                            "{}::{} performs effects, so {} cannot have laws",
                            c.name, m.name, c.name
                        ),
                        m.span,
                    );
                }
            }
        }
        let mut laws = HashSet::new();
        for l in &c.laws {
            if !laws.insert(l.name.as_str()) {
                self.error(format!("{}::{} is declared twice", c.name, l.name), l.span);
            }
        }
        self.classes.insert(
            c.name.clone(),
            ClassInfo {
                decl: c.clone(),
                bound,
                arg,
                in_prelude,
            },
        );
        true
    }

    /// `C::m`: a function over the class's parameter that asks for the class.
    fn declare_methods(&mut self, c: &ClassDecl) {
        let bound = self.classes[&c.name].bound;
        for m in &c.methods {
            let mut f = m.clone();
            f.name = member_fn(c, &m.name);
            f.bounds.resize(f.generics.len(), None);
            let mut generic_types: Vec<_> = f
                .generic_parameters()
                .into_iter()
                .map(|(_, ty)| ty)
                .collect();
            generic_types.insert(0, SurfaceTerm::var("Type", m.span));
            f.generic_types = generic_types;
            f.generics.insert(0, c.param.clone());
            if !f.rows.is_empty() {
                f.rows.insert(0, false);
            }
            f.bounds.insert(
                0,
                Some(match self.classes[&c.name].arg {
                    Some(arg) => format!("({arg})->{bound}").into(),
                    None => bound.to_string().into(),
                }),
            );
            f.where_ = vec![Constraint {
                class: c.name.clone(),
                ty: SurfaceTerm::new(TermKind::Var(c.param.clone()), m.span),
                arguments: Vec::new(),
                span: m.span,
            }];
            let scheme = self.signature(&f);
            self.fns.insert(f.name.clone(), scheme);
        }
    }

    fn declare_instance(
        &mut self,
        i: &InstanceDecl,
        in_prelude: bool,
        own_classes: &HashSet<&Name>,
        own_types: &HashSet<&Name>,
        synthesized: &mut Vec<FnDecl>,
    ) {
        if !i.arguments.is_empty() {
            self.error(
                "value-indexed class instances require checked dictionary extraction",
                i.span,
            );
            return;
        }
        if STRUCTURAL.contains(&i.class.as_str()) {
            self.error(
                format!("{} is structural and has no instances to write", i.class),
                i.span,
            );
            return;
        }
        let Some(class) = self.classes.get(&i.class) else {
            self.error(format!("{} is not a class", i.class), i.span);
            return;
        };
        let (decl, bound, arg) = (class.decl.clone(), class.bound, class.arg);
        let mut generics: Vec<(Param, Kind)> = Vec::new();
        let mut map: HashMap<Name, Ty> = HashMap::new();
        for (n, g) in i.generics.iter().enumerate() {
            let k = i
                .bounds
                .get(n)
                .cloned()
                .flatten()
                .and_then(|b| Kind::parse(&b))
                .unwrap_or(Kind::Affine);
            let param = Param::new(
                ParamId::Instance {
                    class: i.class.clone(),
                    head: i.head.id(),
                    index: n,
                },
                g.clone(),
            );
            generics.push((param.clone(), k));
            map.insert(g.clone(), Ty::Param(param, k));
        }
        // The head: a type with no arguments, or a type constructor applied
        // to distinct generics.
        let shape_ok = match &*i.head.kind {
            TermKind::Var(v) => !i.generics.contains(v),
            TermKind::App {
                function,
                arguments,
            } => {
                matches!(&*function.kind, TermKind::Var(_))
                    && arguments.iter().enumerate().all(|(n, a)| {
                        matches!(&*a.kind, TermKind::Var(g) if i.generics.contains(g)
                            && !arguments[..n].iter().any(|b| b.kind == a.kind))
                    })
            }
            // The product of two distinct generics, `A × B`.
            TermKind::Product(members) => match members.as_slice() {
                [a, b] => matches!((&*a.kind, &*b.kind), (TermKind::Var(x), TermKind::Var(y))
                    if x != y && i.generics.contains(x) && i.generics.contains(y)),
                _ => false,
            },
            _ => false,
        };
        if !shape_ok {
            self.error(
                "an instance head applies a type to distinct generics",
                i.head.span,
            );
            return;
        }
        for (g, _) in &generics {
            if !mentions(&i.head, &g.name) {
                self.error(format!("{g} does not appear in the head"), i.head.span);
                return;
            }
        }
        self.constructor_position = true;
        let head = self.written(&i.head, &map);
        self.constructor_position = false;
        let Some(ctor) = constructor(&head, i.class.is_resolved()) else {
            self.error(
                "an instance head applies a type to distinct generics",
                i.head.span,
            );
            return;
        };
        let missing = match &head {
            Ty::Named(n, args) => self
                .datas
                .decls
                .get(n)
                .map(|d| d.generics.len().saturating_sub(args.len())),
            _ => Some(0),
        };
        match (arg, missing) {
            (Some(arg), Some(1)) => {
                // A type constructor: the head with its last argument.
                let made = super::apply(head.clone(), Ty::Param(Param::kind_witness(arg), arg));
                let shown = self.shown(&made);
                let k = self.datas.kind(&made);
                if !k.fits(bound) {
                    self.error(
                        format!(
                            "{} takes constructors from {arg} to {bound}, and {shown} is {k}",
                            i.class
                        ),
                        i.span,
                    );
                    return;
                }
            }
            (Some(_), _) => {
                let shown = self.shown(&head);
                self.error(
                    format!(
                        "{} takes a type constructor with one argument missing, and {shown} is not one",
                        i.class
                    ),
                    i.span,
                );
                return;
            }
            (None, Some(m)) if m > 0 => {
                let n = constructor(&head, i.class.is_resolved()).unwrap_or_default();
                let want = self.datas.decls[&n].generics.len();
                self.error(format!("{n} takes {want} arguments"), i.head.span);
                return;
            }
            (None, _) => {
                let shown = self.shown(&head);
                let k = self.datas.kind(&head);
                if !k.fits(bound) {
                    self.error(
                        format!("{} takes types up to {bound}, and {shown} is {k}", i.class),
                        i.span,
                    );
                    return;
                }
            }
        }
        let shown = self.shown(&head);
        if !in_prelude && !own_classes.contains(&i.class) && !own_types.contains(&ctor) {
            self.error(
                format!(
                    "{}({ctor}) must be in the tote of {} or of {ctor}",
                    i.class, i.class
                ),
                i.span,
            );
            return;
        }
        let key = (i.class.clone(), ctor.clone());
        if self.instances.contains_key(&key) {
            self.error(
                format!("{} already has an instance for {ctor}", i.class),
                i.span,
            );
            return;
        }
        let mut preds: Vec<(Name, Param)> = Vec::new();
        for c in &i.where_ {
            if !c.arguments.is_empty() {
                self.error(
                    "value-indexed constraints require checked dictionary extraction",
                    c.span,
                );
                continue;
            }
            if !STRUCTURAL.contains(&c.class.as_str()) && !self.classes.contains_key(&c.class) {
                self.error(format!("{} is not a class", c.class), c.span);
                continue;
            }
            match &*c.ty.kind {
                TermKind::Var(g) if i.generics.contains(g) => {
                    let p = (
                        c.class.clone(),
                        generics
                            .iter()
                            .find(|(p, _)| &p.name == g)
                            .unwrap()
                            .0
                            .clone(),
                    );
                    if preds.contains(&p) {
                        self.error(format!("{}({g}) is written twice", c.class), c.span);
                    } else {
                        preds.push(p);
                    }
                }
                _ => self.error("where constrains only generics of the instance", c.span),
            }
        }
        let mut written = HashSet::new();
        for l in &i.laws {
            if !decl.laws.iter().any(|expected| expected.name == l.name) {
                self.error(format!("{} has no law {}", i.class, l.name), l.span);
            } else if !written.insert(l.name.as_str()) {
                self.error(
                    format!("the law {} of the instance is written twice", l.name),
                    l.span,
                );
            }
        }
        // The methods, each as the class gives it with the head in the
        // place of the parameter.
        for expected in &decl.methods {
            let Some(m) = i.methods.iter().find(|m| m.name == expected.name) else {
                self.error(
                    format!(
                        "the instance {}({shown}) does not define {}",
                        i.class, expected.name
                    ),
                    i.span,
                );
                continue;
            };
            let mut f = m.clone();
            f.name = instance_fn(&decl, &m.name, &ctor);
            f.bounds.resize(f.generics.len(), None);
            let mut bounds = i.bounds.clone();
            bounds.resize(i.generics.len(), None);
            bounds.extend(f.bounds.drain(..));
            f.bounds = bounds;
            let mut generic_types: Vec<_> = i
                .generics
                .iter()
                .enumerate()
                .map(|(n, _)| {
                    i.generic_types
                        .get(n)
                        .cloned()
                        .unwrap_or_else(|| SurfaceTerm::var("Type", i.span))
                })
                .collect();
            generic_types.extend(f.generic_parameters().into_iter().map(|(_, ty)| ty));
            f.generic_types = generic_types;
            f.generics.splice(0..0, i.generics.iter().cloned());
            f.where_ = i.where_.clone();
            let scheme = self.signature(&f);
            self.same_signature(i, &f, &scheme, expected, &decl.param, &shown);
            self.fns.insert(f.name.clone(), scheme);
            synthesized.push(f);
        }
        for m in &i.methods {
            if !decl.methods.iter().any(|x| x.name == m.name) {
                self.error(format!("{} has no method {}", i.class, m.name), m.span);
            }
        }
        self.instances.insert(
            key,
            InstanceInfo {
                generics,
                head,
                preds,
            },
        );
    }

    /// The instance's method has the class's signature, the head in the
    /// place of the parameter.
    fn same_signature(
        &mut self,
        i: &InstanceDecl,
        got: &FnDecl,
        scheme: &Scheme,
        expected: &FnDecl,
        param: &Name,
        head: &Ty,
    ) {
        let mut want = expected.clone();
        for t in want.param_types.iter_mut().flatten() {
            *t = replace(t, param, &i.head);
        }
        if let Some(r) = &mut want.result {
            *r = replace(r, param, &i.head);
        }
        want.name = got.name.clone();
        // Compare both signatures over the binders of this method declaration.
        want.body = got.body.clone();
        want.bounds.resize(want.generics.len(), None);
        let mut bounds = i.bounds.clone();
        bounds.resize(i.generics.len(), None);
        bounds.extend(want.bounds.drain(..));
        want.bounds = bounds;
        let mut generic_types: Vec<_> = i
            .generics
            .iter()
            .enumerate()
            .map(|(n, _)| {
                i.generic_types
                    .get(n)
                    .cloned()
                    .unwrap_or_else(|| SurfaceTerm::var("Type", i.span))
            })
            .collect();
        generic_types.extend(want.generic_parameters().into_iter().map(|(_, ty)| ty));
        want.generic_types = generic_types;
        want.generics.splice(0..0, i.generics.iter().cloned());
        want.where_ = i.where_.clone();
        let wanted = self.signature_in(&want, scheme.owner.clone());
        if wanted.ty != scheme.ty || got.borrows != want.borrows {
            let params: Vec<String> = want
                .params
                .iter()
                .enumerate()
                .map(|(n, p)| {
                    let borrow = match want.borrows.get(n).copied().flatten() {
                        Some(true) => "&mut ",
                        Some(false) => "&",
                        None => "",
                    };
                    let ty = match &wanted.ty {
                        Ty::Fn(ps, _, _) => ps
                            .get(n)
                            .map(|t| self.shown(t.unborrowed()).to_string())
                            .unwrap_or_default(),
                        _ => String::new(),
                    };
                    format!("{borrow}{p}: {ty}")
                })
                .collect();
            self.error(
                format!(
                    "{}.{} of {head} takes {}",
                    i.class,
                    expected.name,
                    params.join(", ")
                ),
                got.span,
            );
        }
    }
}

pub(crate) enum Unresolved {
    /// The type is not known by the end of the check.
    Undetermined,
    /// A type parameter that the function does not assume the class of.
    Assumption(String),
    NoInstance(String),
}

impl Checker {
    /// The evidence for `class(t)`: an assumption for
    /// a type parameter, otherwise the instance for the head of the type,
    /// with the evidence for its `where` at the types the head was matched
    /// to. Nothing here makes a type: an unknown type is left as an error.
    pub(super) fn resolve_class(
        &self,
        class: &Name,
        t: &Ty,
        assume: &[(Name, Param)],
    ) -> Result<super::Ev, Unresolved> {
        use super::Ev;
        let t = match self.resolve(t) {
            Ty::Tagged(_, t) | Ty::Borrow(t, _) => *t,
            t => t,
        };
        let shown = || self.shown(&t).to_string();
        if let Ty::Param(n, _) = &t {
            return if assume.iter().any(|(c, g)| c == class && g == n) {
                Ok(Ev::Assume(class.clone(), n.clone()))
            } else {
                Err(Unresolved::Assumption(shown()))
            };
        }
        if matches!(t, Ty::Var(_)) {
            return Err(Unresolved::Undetermined);
        }
        if STRUCTURAL.contains(&class.as_str()) {
            return if self.datas.structural(class, &t, assume) {
                Ok(Ev::Structural)
            } else {
                Err(Unresolved::NoInstance(shown()))
            };
        }
        let Some(ctor) = constructor(&t, class.is_resolved()) else {
            return Err(Unresolved::NoInstance(shown()));
        };
        // A `Pair` is the instance's whichever way it is named: `A × B` is the prelude's.
        let ctor = if super::is_pair_name(&ctor) {
            self.pair_name()
        } else {
            ctor
        };
        let Some(instance) = self.instances.get(&(class.clone(), ctor.clone())) else {
            return Err(if self.has_vars(&t) {
                Unresolved::Undetermined
            } else {
                Unresolved::NoInstance(shown())
            });
        };
        // The head is the constructor over distinct generics, so each
        // argument of `t` is what one generic stands for.
        let mut found: HashMap<&ParamId, Ty> = HashMap::new();
        if let (Ty::Named(_, params), Ty::Named(_, args)) = (&instance.head, &t) {
            for (p, a) in params.iter().zip(args) {
                if let Ty::Param(g, _) = p {
                    found.insert(g.id(), a.clone());
                }
            }
        }
        let args: Vec<Ty> = instance
            .generics
            .iter()
            .map(|(g, _)| found.get(g.id()).cloned().unwrap_or(Ty::Unit))
            .collect();
        let mut subs = Vec::new();
        for (d, g) in &instance.preds {
            let u = found.get(g.id()).cloned().unwrap_or(Ty::Unit);
            subs.push(self.resolve_class(d, &u, assume)?);
        }
        Ok(Ev::Inst(class.clone(), ctor, args, subs))
    }
}
