//! Classes and instances: their declarations are checked here, and each
//! method becomes a function that carries the class as a `where`.

use crate::surface::Name;
use std::collections::{HashMap, HashSet};
use tauto_message::msg;

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
    /// Every class type argument, in order (`C(H₀, H₁, …)`).
    pub heads: Vec<Ty>,
    /// The `where` of the instance: a class and the generics it constrains.
    pub preds: Vec<(Name, Vec<Param>)>,
}

/// Whether a class parameter domain is a native Nib type (or type former), not a value index.
fn is_type_class_param(ty: &SurfaceTerm, class_bound: Option<&str>, first: bool) -> bool {
    matches!(&*ty.kind, TermKind::Var(name) if name.as_str() == "Type")
        || (first && class_bound.is_some_and(|bound| Kind::parse_ctor(bound).is_some()))
}

/// Variables for the class parameters after the first: `C(A, B, C)`'s `B`, `C`.
fn class_tail_vars(
    parameters: &[(Name, SurfaceTerm)],
    span: tauto_parol::Span,
) -> Vec<SurfaceTerm> {
    parameters
        .iter()
        .skip(1)
        .map(|(name, _)| SurfaceTerm::new(TermKind::Var(name.clone()), span))
        .collect()
}

/// Instance table key: one constructor, or every constructor joined when the class has several type arguments.
fn instance_heads_key(heads: &[Ty], resolved: bool) -> Option<Name> {
    let ctors: Option<Vec<Name>> = heads.iter().map(|t| constructor(t, resolved)).collect();
    let ctors = ctors?;
    if ctors.len() == 1 {
        Some(ctors.into_iter().next().unwrap())
    } else {
        Some(Name::from(
            ctors
                .iter()
                .map(|c| c.to_string())
                .collect::<Vec<_>>()
                .join("@"),
        ))
    }
}

/// A type-shaped instance argument (not a value index such as `1` or `"one"`).
/// `_` in a partial application is read as [`TermKind::Other`] `"Wild"`.
fn is_type_instance_arg(t: &SurfaceTerm) -> bool {
    match &*t.kind {
        TermKind::Var(_) | TermKind::Hole(_) => true,
        TermKind::Other(msg) if msg == "Wild" => true,
        TermKind::App {
            function,
            arguments,
        } => {
            matches!(&*function.kind, TermKind::Var(_))
                && arguments.iter().all(is_type_instance_arg)
        }
        TermKind::Pi {
            params,
            result,
            effects: None,
            ..
        } => {
            params
                .iter()
                .all(|(n, p)| n.is_none() && is_type_instance_arg(p))
                && is_type_instance_arg(result)
        }
        _ => false,
    }
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
        (Some(member), None) if is_fn_head(head) => member
            .specialize(&format!("head:{head}"), format!("{member}@{head}"))
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

/// A type of the class's signature as the instance reads it: each class
/// parameter replaced by the instance argument in that place, and a method
/// that is not executable applied to its arguments (`C::child_type(env)`) the
/// type the instance gives it (`Browser`). The body of such a method uses no
/// parameter (`nibcheck-type-method-uses-value`), so the arguments do not
/// change it.
pub(super) fn instance_type(t: &SurfaceTerm, decl: &ClassDecl, i: &InstanceDecl) -> SurfaceTerm {
    let types: Vec<(Name, SurfaceTerm)> = decl
        .methods
        .iter()
        .filter(|m| !super::type_functions::executable(m))
        .filter_map(|m| {
            let given = i.methods.iter().find(|g| g.name == m.name)?;
            Some((member_fn(decl, &m.name), given.body.clone()))
        })
        .collect();
    fn go(t: &mut SurfaceTerm, types: &[(Name, SurfaceTerm)]) {
        let head = match &*t.kind {
            TermKind::App { function, .. } => function.as_ref(),
            _ => &*t,
        };
        if let TermKind::Var(n) = &*head.kind
            && let Some((_, body)) = types.iter().find(|(m, _)| m == n)
        {
            *t = block_value(body);
            return;
        }
        walk::children(t, &mut |c| go(c, types));
    }
    let args: Vec<&SurfaceTerm> = std::iter::once(&i.head).chain(&i.arguments).collect();
    let mut t = t.clone();
    for ((name, _), arg) in decl.parameters.iter().zip(args) {
        t = replace(&t, name, arg);
    }
    go(&mut t, &types);
    t
}

/// A constraint a class method writes, at the instance's head.
fn instance_constraint(c: &Constraint, decl: &ClassDecl, i: &InstanceDecl) -> Constraint {
    Constraint {
        class: c.class.clone(),
        ty: instance_type(&c.ty, decl, i),
        arguments: c
            .arguments
            .iter()
            .map(|a| instance_type(a, decl, i))
            .collect(),
        span: c.span,
    }
}

/// `{ Browser }`, a body, as the term it gives.
fn block_value(body: &SurfaceTerm) -> SurfaceTerm {
    match &*body.kind {
        TermKind::Block(stmts) => match stmts.as_slice() {
            [crate::surface::Stmt::Expr(e)] => block_value(e),
            _ => body.clone(),
        },
        _ => body.clone(),
    }
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
        Ty::Fn(ps, _, _) => Some(fn_head(ps.len())),
        Ty::Int(_) | Ty::Bool | Ty::Text | Ty::Float | Ty::Float32 | Ty::Decimal | Ty::Unit => {
            Some(builtin(&t.to_string()))
        }
        _ => None,
    }
}

/// The head of the instances for functions of `arity` parameters: the
/// function type itself, keyed by its number of parameters. The spelling is
/// one no declaration can have.
pub(super) fn fn_head(arity: usize) -> Name {
    let holes = vec!["_"; arity].join(", ");
    Name::from(format!("({holes}) -> _"))
}

fn is_fn_head(head: &Name) -> bool {
    head.as_global().is_none() && head.as_str().ends_with(") -> _")
}

pub(super) fn head_constructor(t: &Ty, resolved: bool) -> Option<Name> {
    constructor(t, resolved)
}

/// A class method's type, its arguments read by their types: in
/// `fn child_env(env: &mut Env): &mut C::child_type(env)`, `C::child_type(env)`
/// is `C::child_type(Env)`, which an instance for `Env` gives.
fn by_types(t: &SurfaceTerm, decl: &ClassDecl, f: &FnDecl) -> SurfaceTerm {
    let types: Vec<Name> = decl
        .methods
        .iter()
        .filter(|m| !super::type_functions::executable(m))
        .map(|m| member_fn(decl, &m.name))
        .collect();
    let mut t = t.clone();
    walk::term(&mut t, &mut |t| {
        let TermKind::App {
            function,
            arguments,
        } = &*t.kind
        else {
            return;
        };
        if !matches!(&*function.kind, TermKind::Var(n) if types.contains(n)) {
            return;
        }
        let arguments: Vec<SurfaceTerm> = arguments
            .iter()
            .map(|a| match &*a.kind {
                TermKind::Var(x) => f
                    .params
                    .iter()
                    .position(|p| p == x)
                    .and_then(|i| f.param_types.get(i).cloned().flatten())
                    .unwrap_or_else(|| a.clone()),
                _ => a.clone(),
            })
            .collect();
        let function = function.clone();
        *t = t.with_kind(
            TermKind::App {
                function,
                arguments,
            },
            t.span,
        );
    });
    t
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
                self.error(
                    msg!("nibcheck-class-already-class", name = d.name.to_string()),
                    d.span,
                );
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
            self.error(
                msg!("nibcheck-class-built-in", name = c.name.to_string()),
                c.span,
            );
            return false;
        }
        if self.classes.contains_key(&c.name) {
            self.error(
                msg!("nibcheck-class-declared-twice", name = c.name.to_string()),
                c.span,
            );
            return false;
        }
        if !in_prelude && own_types.contains(&c.name) {
            self.error(
                msg!("nibcheck-class-already-type", name = c.name.to_string()),
                c.span,
            );
            return false;
        }
        // Native Nib keeps type (and type-former) parameters only. A value
        // index needs checked dictionary extraction first.
        if c.arity == 0
            || c.parameters
                .iter()
                .enumerate()
                .any(|(i, (_, ty))| !is_type_class_param(ty, c.bound.as_deref(), i == 0))
        {
            self.error(msg!("nibcheck-value-indexed-classes"), c.span);
            return false;
        }
        // `NoBorrow` is a bound of a function's type parameter; a class
        // parameter does not take it. Said once here, the class stays
        // declared without it so its uses read as uses of a class.
        let written = c.bound.as_deref().map(super::without_no_borrow);
        if let Some((_, true)) = written {
            self.error(
                msg!(
                    "nibcheck-class-parameter-no-borrow",
                    class = c.name.to_string()
                ),
                c.span,
            );
        }
        let bound = written.map(|(b, _)| b).unwrap_or(c.bound.clone());
        let (bound, arg) = match bound.as_deref() {
            None => (Kind::Affine, None),
            Some(b) => match (Kind::parse(b), Kind::parse_ctor(b)) {
                (Some(k), _) => (k, None),
                (None, Some((arg, result))) => (result, Some(arg)),
                _ => {
                    self.error(msg!("nibcheck-not-a-kind", name = b.to_string()), c.span);
                    return false;
                }
            },
        };
        let mut seen = HashSet::new();
        for m in &c.methods {
            if !seen.insert(m.name.as_str()) {
                self.error(
                    msg!(
                        "nibcheck-class-member-declared-twice",
                        class = c.name.to_string(),
                        name = m.name.to_string()
                    ),
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
                        msg!(
                            "nibcheck-class-method-performs-effects",
                            class = c.name.to_string(),
                            name = m.name.to_string()
                        ),
                        m.span,
                    );
                }
            }
        }
        let mut laws = HashSet::new();
        for l in &c.laws {
            if !laws.insert(l.name.as_str()) {
                self.error(
                    msg!(
                        "nibcheck-class-member-declared-twice",
                        class = c.name.to_string(),
                        name = l.name.to_string()
                    ),
                    l.span,
                );
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

    /// The classes the `where` of `method` leads to, back to `class`: the
    /// methods passed on the way, `C::m -> D::n -> C`, or `None` when no
    /// `where` leads back.
    fn where_cycle(&self, class: &ClassDecl, method: &FnDecl) -> Option<Vec<String>> {
        fn walk(
            checker: &Checker,
            target: &Name,
            from: &FnDecl,
            owner: &Name,
            path: &mut Vec<String>,
            seen: &mut HashSet<Name>,
        ) -> bool {
            path.push(format!("{owner}::{}", from.name));
            for w in &from.where_ {
                if &w.class == target {
                    path.push(target.to_string());
                    return true;
                }
                if !seen.insert(w.class.clone()) {
                    continue;
                }
                let Some(asked) = checker.classes.get(&w.class) else {
                    continue;
                };
                for held in &asked.decl.methods {
                    if walk(checker, target, held, &w.class, path, seen) {
                        return true;
                    }
                }
            }
            path.pop();
            false
        }
        let mut path = Vec::new();
        walk(
            self,
            &class.name,
            method,
            &class.name,
            &mut path,
            &mut HashSet::new(),
        )
        .then_some(path)
    }

    /// `C::m`: a function over the class's parameters that asks for the class.
    fn declare_methods(&mut self, c: &ClassDecl) {
        let bound = self.classes[&c.name].bound;
        let arg = self.classes[&c.name].arg;
        for m in &c.methods {
            // The evidence a method asks for is a dictionary in the type of
            // the class's own, so the classes traced through method `where`s
            // cannot lead back to the class: the dictionary type is finite.
            if let Some(path) = self.where_cycle(c, m) {
                self.error(
                    msg!(
                        "nibcheck-class-method-where-cycle",
                        path = path.join(" -> ")
                    ),
                    m.span,
                );
            }
            let mut f = m.clone();
            f.name = member_fn(c, &m.name);
            for i in 0..f.param_types.len() {
                if let Some(t) = &f.param_types[i] {
                    f.param_types[i] = Some(by_types(t, c, m));
                }
            }
            f.result = f.result.as_ref().map(|r| by_types(r, c, m));
            f.bounds.resize(f.generics.len(), None);
            let mut generic_types: Vec<_> = f
                .generic_parameters()
                .into_iter()
                .map(|(_, ty)| ty)
                .collect();
            // Every class parameter leads, in order, then the method's own.
            for (i, (name, ty)) in c.parameters.iter().enumerate().rev() {
                let (param_bound, param_arg) = if i == 0 {
                    (bound, arg)
                } else if matches!(&*ty.kind, TermKind::Var(n) if n.as_str() == "Type") {
                    (Kind::Affine, None)
                } else {
                    (bound, None)
                };
                generic_types.insert(0, SurfaceTerm::var("Type", m.span));
                f.generics.insert(0, name.clone());
                if !f.rows.is_empty() {
                    f.rows.insert(0, false);
                }
                f.bounds.insert(
                    0,
                    Some(match param_arg {
                        Some(a) => format!("({a})->{param_bound}").into(),
                        None => param_bound.to_string().into(),
                    }),
                );
            }
            f.generic_types = generic_types;
            // The class's own constraint comes first; the method's follow.
            f.where_.insert(
                0,
                Constraint {
                    class: c.name.clone(),
                    ty: SurfaceTerm::new(TermKind::Var(c.param.clone()), m.span),
                    arguments: class_tail_vars(&c.parameters, m.span),
                    span: m.span,
                },
            );
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
        if STRUCTURAL.contains(&i.class.as_str()) {
            self.error(
                msg!(
                    "nibcheck-class-structural-no-instances",
                    name = i.class.to_string()
                ),
                i.span,
            );
            return;
        }
        let Some(class) = self.classes.get(&i.class) else {
            self.error(
                msg!("nibcheck-not-a-class", name = i.class.to_string()),
                i.span,
            );
            return;
        };
        let (decl, bound, arg) = (class.decl.clone(), class.bound, class.arg);
        let class_args: Vec<&SurfaceTerm> = std::iter::once(&i.head).chain(&i.arguments).collect();
        if class_args.len() != decl.parameters.len() {
            self.error(
                msg!(
                    "nibcheck-class-argument-arity",
                    name = i.class.to_string(),
                    expected = decl.parameters.len().to_string(),
                    count = class_args.len().to_string()
                ),
                i.span,
            );
            return;
        }
        if class_args.iter().any(|a| !is_type_instance_arg(a)) {
            self.error(msg!("nibcheck-value-indexed-instances"), i.span);
            return;
        }
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
            // The product of two distinct generics, `A × B`.
            TermKind::App { .. } if let Some(members) = i.head.product_type_members() => {
                match members.as_slice() {
                    [a, b] => matches!((&*a.kind, &*b.kind), (TermKind::Var(x), TermKind::Var(y))
                    if x != y && i.generics.contains(x) && i.generics.contains(y)),
                    _ => false,
                }
            }
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
            // A function type over distinct generics, `(A, B) -> R`, with no
            // names, borrows or effects written.
            TermKind::Pi {
                params,
                result,
                effects: None,
                ..
            } => {
                let mut all: Vec<&SurfaceTerm> = params
                    .iter()
                    .map(|(n, p)| (n.is_none()).then_some(p))
                    .collect::<Option<_>>()
                    .unwrap_or_default();
                all.push(result);
                all.len() == params.len() + 1
                    && all.iter().enumerate().all(|(n, a)| {
                        matches!(&*a.kind, TermKind::Var(g) if i.generics.contains(g)
                            && !all[..n].iter().any(|b| b.kind == a.kind))
                    })
            }
            _ => false,
        };
        if !shape_ok {
            self.error(
                msg!("nibcheck-instance-head-distinct-generics"),
                i.head.span,
            );
            return;
        }
        for (g, _) in &generics {
            if !class_args.iter().any(|a| mentions(a, &g.name)) {
                self.error(
                    msg!("nibcheck-generic-not-in-head", name = g.to_string()),
                    i.head.span,
                );
                return;
            }
        }
        self.constructor_position = true;
        let mut heads: Vec<Ty> = Vec::new();
        for a in &class_args {
            heads.push(self.written(a, &map));
        }
        self.constructor_position = false;
        let head = heads[0].clone();
        let Some(ctor) = constructor(&head, i.class.is_resolved()) else {
            self.error(
                msg!("nibcheck-instance-head-distinct-generics"),
                i.head.span,
            );
            return;
        };
        let Some(key_ctor) = instance_heads_key(&heads, i.class.is_resolved()) else {
            self.error(
                msg!("nibcheck-instance-head-distinct-generics"),
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
                        msg!(
                            "nibcheck-constructor-kind-mismatch",
                            what = i.class.to_string(),
                            arg = arg.to_string(),
                            result = bound.to_string(),
                            shown = shown.to_string(),
                            kind = k.to_string()
                        ),
                        i.span,
                    );
                    return;
                }
            }
            (Some(_), _) => {
                let shown = self.shown(&head);
                self.error(
                    msg!(
                        "nibcheck-instance-needs-constructor",
                        class = i.class.to_string(),
                        shown = shown.to_string()
                    ),
                    i.span,
                );
                return;
            }
            (None, Some(m)) if m > 0 => {
                let n = constructor(&head, i.class.is_resolved()).unwrap_or_default();
                let want = self.datas.decls[&n].generics.len();
                self.error(
                    msg!(
                        "nibcheck-takes-arguments",
                        name = n.to_string(),
                        count = want.to_string()
                    ),
                    i.head.span,
                );
                return;
            }
            (None, _) => {
                for (n, h) in heads.iter().enumerate() {
                    let shown = self.shown(h);
                    let k = self.datas.kind(h);
                    if !k.fits(bound) {
                        self.error(
                            msg!(
                                "nibcheck-instance-type-kind",
                                class = i.class.to_string(),
                                bound = bound.to_string(),
                                shown = shown.to_string(),
                                kind = k.to_string()
                            ),
                            if n == 0 {
                                i.span
                            } else {
                                i.arguments[n - 1].span
                            },
                        );
                        return;
                    }
                }
            }
        }
        let shown = heads
            .iter()
            .map(|h| self.shown(h).to_string())
            .collect::<Vec<_>>()
            .join(", ");
        let owned_ctor = heads
            .iter()
            .any(|h| constructor(h, i.class.is_resolved()).is_some_and(|c| own_types.contains(&c)));
        if !in_prelude && !own_classes.contains(&i.class) && !owned_ctor {
            self.error(
                msg!(
                    "nibcheck-instance-orphan",
                    class = i.class.to_string(),
                    ctor = ctor.to_string()
                ),
                i.span,
            );
            return;
        }
        let key = (i.class.clone(), key_ctor.clone());
        if self.instances.contains_key(&key) {
            self.error(
                msg!(
                    "nibcheck-instance-duplicate",
                    class = i.class.to_string(),
                    ctor = key_ctor.to_string()
                ),
                i.span,
            );
            return;
        }
        let mut preds: Vec<(Name, Vec<Param>)> = Vec::new();
        for c in &i.where_ {
            let asked = self.classes.get(&c.class).map(|info| info.decl.arity);
            let args: Vec<&SurfaceTerm> = std::iter::once(&c.ty).chain(&c.arguments).collect();
            if let Some(arity) = asked
                && args.len() != arity
            {
                self.error(
                    msg!(
                        "nibcheck-class-argument-arity",
                        name = c.class.to_string(),
                        expected = arity.to_string(),
                        count = args.len().to_string()
                    ),
                    c.span,
                );
                continue;
            }
            if asked.is_none() && !STRUCTURAL.contains(&c.class.as_str()) && !c.arguments.is_empty()
            {
                self.error(msg!("nibcheck-value-indexed-constraints"), c.span);
                continue;
            }
            if !STRUCTURAL.contains(&c.class.as_str()) && !self.classes.contains_key(&c.class) {
                self.error(
                    msg!("nibcheck-not-a-class", name = c.class.to_string()),
                    c.span,
                );
                continue;
            }
            let mut params = Vec::new();
            let mut ok = true;
            for a in &args {
                match &*a.kind {
                    TermKind::Var(g) if i.generics.contains(g) => {
                        params.push(
                            generics
                                .iter()
                                .find(|(p, _)| &p.name == g)
                                .unwrap()
                                .0
                                .clone(),
                        );
                    }
                    _ => {
                        self.error(msg!("nibcheck-where-only-generics-of-instance"), c.span);
                        ok = false;
                        break;
                    }
                }
            }
            if !ok {
                continue;
            }
            let p = (c.class.clone(), params);
            if preds.iter().any(|(cls, ps)| cls == &p.0 && ps == &p.1) {
                self.error(
                    msg!(
                        "nibcheck-predicate-written-twice",
                        class = c.class.to_string(),
                        argument = args
                            .iter()
                            .map(|a| match &*a.kind {
                                TermKind::Var(g) => g.to_string(),
                                _ => "?".into(),
                            })
                            .collect::<Vec<_>>()
                            .join(", ")
                    ),
                    c.span,
                );
            } else {
                preds.push(p);
            }
        }
        let mut written = HashSet::new();
        for l in &i.laws {
            if !decl.laws.iter().any(|expected| expected.name == l.name) {
                self.error(
                    msg!(
                        "nibcheck-instance-no-law",
                        class = i.class.to_string(),
                        name = l.name.to_string()
                    ),
                    l.span,
                );
            } else if !written.insert(l.name.as_str()) {
                self.error(
                    msg!("nibcheck-instance-law-twice", name = l.name.to_string()),
                    l.span,
                );
            }
        }
        // The methods, each as the class gives it with the head in the
        // place of the parameter.
        for expected in &decl.methods {
            let Some(m) = i.methods.iter().find(|m| m.name == expected.name) else {
                self.error(
                    msg!(
                        "nibcheck-instance-missing-method",
                        class = i.class.to_string(),
                        ty = shown.to_string(),
                        name = expected.name.to_string()
                    ),
                    i.span,
                );
                continue;
            };
            // A method that is not executable (`type_functions::executable`)
            // is not run: its body is a type, which the signatures of the
            // other methods read in its place (`same_signature`).
            if !super::type_functions::executable(expected) {
                if let Some(param) = m.params.iter().find(|p| mentions(&m.body, p)) {
                    self.error(
                        msg!(
                            "nibcheck-type-method-uses-value",
                            name = m.name.to_string(),
                            param = param.to_string()
                        ),
                        m.span,
                    );
                } else {
                    // The body is a type over the instance's generics, read
                    // as a native type function's body is
                    // (`type_functions.rs`).
                    let given = self.written(&block_value(&m.body), &map);
                    self.type_methods.insert(
                        (member_fn(&decl, &m.name), key_ctor.clone()),
                        (head.clone(), given),
                    );
                }
                continue;
            }
            let mut f = m.clone();
            f.name = instance_fn(&decl, &m.name, &key_ctor);
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
            f.where_ = i
                .where_
                .iter()
                .cloned()
                .chain(m.where_.iter().cloned())
                .collect();
            let scheme = self.signature(&f);
            self.same_signature(i, &f, &scheme, expected, &decl, &shown);
            self.fns.insert(f.name.clone(), scheme);
            synthesized.push(f);
        }
        for m in &i.methods {
            if !decl.methods.iter().any(|x| x.name == m.name) {
                self.error(
                    msg!(
                        "nibcheck-no-method",
                        owner = i.class.to_string(),
                        name = m.name.to_string()
                    ),
                    m.span,
                );
            }
        }
        self.instances.insert(
            key,
            InstanceInfo {
                generics,
                heads,
                preds,
            },
        );
    }

    /// The instance's method has the class's signature, the heads in the
    /// place of the class parameters.
    fn same_signature(
        &mut self,
        i: &InstanceDecl,
        got: &FnDecl,
        scheme: &Scheme,
        expected: &FnDecl,
        decl: &ClassDecl,
        head: &str,
    ) {
        let mut want = expected.clone();
        for t in want.param_types.iter_mut().flatten() {
            *t = instance_type(t, decl, i);
        }
        if let Some(r) = &mut want.result {
            *r = instance_type(r, decl, i);
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
        want.where_ = i
            .where_
            .iter()
            .cloned()
            .chain(
                expected
                    .where_
                    .iter()
                    .map(|c| instance_constraint(c, decl, i)),
            )
            .collect();
        let wanted = self.signature_in(&want, scheme.owner.clone());
        if wanted.ty != scheme.ty || wanted.preds != scheme.preds || got.borrows != want.borrows {
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
                    format!("{p}: {borrow}{ty}")
                })
                .collect();
            self.error(
                msg!(
                    "nibcheck-instance-method-parameters",
                    class = i.class.to_string(),
                    name = expected.name.to_string(),
                    head = head.to_string(),
                    parameters = params.join(", ")
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
    /// The evidence for `class(t₀, t₁, …)`: an assumption for type
    /// parameters, otherwise the instance for the heads of the types, with
    /// the evidence for its `where` at the types the heads were matched to.
    /// Nothing here makes a type: an unknown type is left as an error.
    pub(super) fn resolve_class(
        &self,
        class: &Name,
        tys: &[Ty],
        assume: &[(Name, Vec<Param>)],
    ) -> Result<super::Ev, Unresolved> {
        use super::Ev;
        let tys: Vec<Ty> = tys
            .iter()
            .map(|t| match self.resolve(t) {
                Ty::Tagged(_, t) | Ty::Borrow(t, _) => *t,
                t => t,
            })
            .collect();
        let shown = || {
            tys.iter()
                .map(|t| self.shown(t).to_string())
                .collect::<Vec<_>>()
                .join(", ")
        };
        if tys.iter().all(|t| matches!(t, Ty::Param(..))) {
            if let Some((_, params)) = assume.iter().find(|(c, ps)| {
                c == class
                    && ps.len() == tys.len()
                    && ps
                        .iter()
                        .zip(&tys)
                        .all(|(p, t)| matches!(t, Ty::Param(n, _) if n == p))
            }) {
                return Ok(Ev::Assume(class.clone(), params.clone()));
            }
            return Err(Unresolved::Assumption(shown()));
        }
        if tys.iter().any(|t| matches!(t, Ty::Var(_))) {
            return Err(Unresolved::Undetermined);
        }
        let Some(t) = tys.first() else {
            return Err(Unresolved::NoInstance(shown()));
        };
        // A union shows the member it holds: the `match` of `Debug(A | B)`
        // has a typed arm for each member, so each needs a head of its own
        // (`docs/design/debug.md`).
        if let (Ty::Union(members), true) = (t, tys.len() == 1)
            && super::debug::is_debug_class(class)
        {
            let mut arms = Vec::new();
            for m in members {
                let m = self.resolve(m);
                let headed = match &m {
                    Ty::Int(_)
                    | Ty::Bool
                    | Ty::Text
                    | Ty::Unit
                    | Ty::Decimal
                    | Ty::Float
                    | Ty::Float32 => true,
                    Ty::Named(..) => true,
                    _ => false,
                };
                if !headed {
                    return Err(if self.has_vars(&m) {
                        Unresolved::Undetermined
                    } else {
                        Unresolved::NoInstance(shown())
                    });
                }
                let ev = self.resolve_class(class, &[m.clone()], assume)?;
                arms.push((m, ev));
            }
            return Ok(Ev::Union(class.clone(), arms));
        }
        if STRUCTURAL.contains(&class.as_str()) {
            return if tys.len() == 1
                && self
                    .datas
                    .structural(class, &self.settled(t), &flatten_assume(assume))
            {
                Ok(Ev::Structural)
            } else {
                Err(Unresolved::NoInstance(shown()))
            };
        }
        let resolved = class.is_resolved();
        let Some(key_ctor) = instance_heads_key(&tys, resolved) else {
            return Err(Unresolved::NoInstance(shown()));
        };
        // A `Pair` is the instance's whichever way it is named: `A × B` is the prelude's.
        let key_ctor = if tys.len() == 1 && super::is_pair_name(&key_ctor) {
            self.pair_name()
        } else {
            key_ctor
        };
        let Some(instance) = self.instances.get(&(class.clone(), key_ctor.clone())) else {
            return Err(if tys.iter().any(|t| self.has_vars(t)) {
                Unresolved::Undetermined
            } else {
                Unresolved::NoInstance(shown())
            });
        };
        // Each head is the constructor over distinct generics, so each
        // argument of `t` is what one generic stands for.
        let mut found: HashMap<&ParamId, Ty> = HashMap::new();
        fn bind<'a>(found: &mut HashMap<&'a ParamId, Ty>, params: &'a [Ty], args: &[Ty]) {
            for (p, a) in params.iter().zip(args) {
                if let Ty::Param(g, _) = p {
                    found.insert(g.id(), a.clone());
                }
            }
        }
        for (inst_ty, got_ty) in instance.heads.iter().zip(&tys) {
            match (inst_ty, got_ty) {
                (Ty::Named(_, params), Ty::Named(_, args)) => bind(&mut found, params, args),
                // A function instance takes a function of its kind whose
                // parameters are owned; a borrowed parameter is not a type a
                // generic stands for.
                (Ty::Fn(params, result, head_kind), Ty::Fn(args, got, kind)) => {
                    let args: Vec<Ty> = args.iter().map(|a| self.resolve(a)).collect();
                    if !(kind == head_kind || (kind.dup() && head_kind.dup()))
                        || args.iter().any(|a| matches!(a, Ty::Borrow(..)))
                    {
                        return Err(Unresolved::NoInstance(shown()));
                    }
                    bind(&mut found, params, &args);
                    bind(
                        &mut found,
                        std::slice::from_ref(&**result),
                        &[self.resolve(got)],
                    );
                }
                _ => {}
            }
        }
        let args: Vec<Ty> = instance
            .generics
            .iter()
            .map(|(g, _)| found.get(g.id()).cloned().unwrap_or(Ty::Unit))
            .collect();
        let mut subs = Vec::new();
        for (d, gs) in &instance.preds {
            let us: Vec<Ty> = gs
                .iter()
                .map(|g| found.get(g.id()).cloned().unwrap_or(Ty::Unit))
                .collect();
            subs.push(self.resolve_class(d, &us, assume)?);
        }
        Ok(Ev::Inst(class.clone(), key_ctor, args, subs))
    }
}

/// Structural predicates still match a single generic; flatten multi-arg assumes to their first.
fn flatten_assume(assume: &[(Name, Vec<Param>)]) -> Vec<(Name, Param)> {
    assume
        .iter()
        .filter_map(|(c, ps)| Some((c.clone(), ps.first()?.clone())))
        .collect()
}
