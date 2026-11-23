//! Binding occurrences to references. Source lookup happens here; an existing
//! reference is copied without consulting its display name.

use std::collections::HashMap;
use std::sync::Arc;

use crate::bindings::Bindings as Declarations;
use crate::identity::{DeclId, EffectUse, Generation, LocalId, LocalRef, Name};
use crate::surface::*;

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
enum Owner {
    Declaration(DeclId),
    Local(LocalId),
    Term(TermId),
    DeclarationTerm(DeclId, u32),
    LocalTerm(LocalId, u32),
}

/// A binding session shared by the proof and executable views of a source.
/// Cloned occurrences receive the same local reference.
#[derive(Clone, Default)]
pub struct Resolver {
    declarations: Declarations,
    locals: crate::identity::ForkedMap<(Owner, u32, String), LocalRef>,
    term_owner: Option<(Owner, u32)>,
    /// Set while a term is read where a type is written (a parameter's type,
    /// a field's type). A name that is a type there means the type, even if a
    /// constructor of the file shares its spelling.
    type_position: bool,
}

type Scope = Vec<(String, Name)>;

impl crate::identity::Detach for Resolver {
    /// A copy whose reservations are its own from now on
    /// ([`crate::bindings::Bindings::detached`]).
    fn detached(&self) -> Self {
        Self {
            declarations: self.declarations.detached(),
            ..self.clone()
        }
    }
}

impl Resolver {
    pub fn new(declarations: Declarations) -> Self {
        Self {
            declarations,
            locals: Default::default(),
            term_owner: None,
            type_position: false,
        }
    }

    pub fn next_revision(&self) -> Self {
        Self {
            declarations: self.declarations.next_revision(),
            locals: self.locals.clone(),
            term_owner: None,
            type_position: false,
        }
    }

    /// Takes in what a copy of this session wrote since it was made, as a
    /// kernel copy declaring other files does ([`Declarations::absorb`]). False
    /// when another copy taken in since wrote the same thing.
    pub fn absorb(&mut self, other: Resolver) -> bool {
        let declarations = self.declarations.absorb(other.declarations);
        let locals = self.locals.absorb(other.locals);
        declarations && locals
    }

    /// Leaves in this copy only what it wrote, for [`Self::absorb`].
    pub fn subtract(&mut self, since: u64, base: &Resolver) {
        self.declarations.subtract(since, &base.declarations);
        self.locals.subtract(since);
    }

    pub fn declarations(&self) -> Declarations {
        self.declarations.clone()
    }

    /// Retains each declaration's source spelling independently of later programs.
    pub fn source_modules(&self, modules: &[String]) {
        let modules: std::collections::HashSet<&str> = modules.iter().map(String::as_str).collect();
        let mut seen = std::collections::HashSet::new();
        for (_, reference) in self.declarations.bindings() {
            if !seen.insert(reference.id()) {
                continue;
            }
            if let Some(offset) = reference
                .display()
                .rmatch_indices("::")
                .find_map(|(at, _)| {
                    modules
                        .contains(&reference.display()[..at])
                        .then_some(at + 2)
                })
            {
                reference.set_source_offset(offset);
            }
        }
    }

    pub fn source_alias(&mut self, spelling: &str, reference: &crate::identity::DeclRef) {
        self.declarations.source_alias(spelling, reference.clone());
    }

    pub fn source_effect_alias(&mut self, spelling: &str, target: &str) {
        if let Some(reference) = self.declarations.effect(target).cloned() {
            self.declarations.effect_alias(spelling, reference);
        }
    }

    /// What `spelling` means now (see [`Declarations::spelling_state`]).
    pub fn spelling_state(&self, spelling: &str) -> crate::bindings::SpellingState {
        self.declarations.spelling_state(spelling)
    }

    pub fn restore_spelling(&mut self, spelling: &str, state: crate::bindings::SpellingState) {
        self.declarations.restore_spelling(spelling, state);
    }

    pub fn reserve_source_declaration(&mut self, spelling: &str, full: &str) {
        self.declarations.reserve_source_declaration(spelling, full);
    }

    pub fn reserve_source_effect(&mut self, spelling: &str, full: &str) {
        self.declarations.reserve_source_effect(spelling, full);
    }

    pub fn source_reference(&self, spelling: &str) -> Option<Name> {
        self.declarations
            .get(spelling)
            .cloned()
            .map(Name::Global)
            .or_else(|| {
                self.declarations
                    .selection(spelling)
                    .filter(|n| matches!(n, Name::Global(_)))
            })
    }

    /// Resolves a generated source identifier in its definition environment.
    /// An unknown identifier remains a distinct, unaccepted declaration.
    pub fn source_name(&mut self, name: &mut Name) {
        self.reference(name, &Vec::new());
    }

    pub fn global(&mut self, name: &Name) -> Name {
        match name {
            Name::Spelled(spelling) => self.declarations.reserve(spelling).into(),
            _ => name.clone(),
        }
    }

    pub fn generated(&mut self, owner: &Name, kind: Generation) -> Name {
        self.declarations.generated(owner, kind).into()
    }

    fn predeclare(&mut self, statements: &mut [Stmt]) {
        for statement in statements.iter() {
            match statement {
                Stmt::Fn(function) => {
                    self.declarations.declare(&function.name);
                }
                Stmt::Theorem(theorem) | Stmt::Def(theorem) => {
                    self.declarations.declare(&theorem.name);
                }
                Stmt::Effect(effect) => {
                    self.declarations.declare_effect(&effect.name);
                }
                Stmt::Class(class) => {
                    self.declarations.declare(&class.name);
                }
                Stmt::Extern { fns, .. } => {
                    for function in fns {
                        self.declarations.declare(&function.name);
                    }
                }
                Stmt::Struct(d) | Stmt::Enum(d) => {
                    self.declarations.declare_type(&d.name);
                }
                Stmt::Inductive(d) => {
                    self.declarations.declare(&d.name);
                }
                _ => {}
            }
        }
        for statement in statements {
            match statement {
                Stmt::Reexport {
                    aliases: Some(aliases),
                    ..
                } => {
                    for alias in aliases {
                        if alias.effect {
                            if let Some(reference) =
                                self.declarations.effect(&alias.target).cloned()
                            {
                                self.declarations.effect_alias(&alias.name, reference);
                            }
                        } else if let Some(reference) =
                            self.declarations.get(&alias.target).cloned()
                        {
                            self.declarations.source_alias(&alias.name, reference);
                        }
                    }
                }
                Stmt::Fn(function) => {
                    if function.decreasing_by.is_some() {
                        self.generated(&function.name, Generation::WellFoundedStep);
                        self.generated(&function.name, Generation::WellFoundedEquation);
                    }
                    if function.opaque {
                        self.generated(&function.name, Generation::OpaqueBody);
                        self.generated(&function.name, Generation::OpaqueEquation);
                    }
                }
                Stmt::Class(class) => {
                    for (index, method) in class.methods.iter().enumerate() {
                        self.declarations
                            .class_member(&class.name, &method.name, index, false);
                    }
                    for (index, law) in class.laws.iter().enumerate() {
                        self.declarations
                            .class_member(&class.name, &law.name, index, true);
                    }
                    self.generated(&class.name, Generation::ClassLaws);
                }
                Stmt::Inductive(d) => {
                    for (index, constructor) in d.constructors.iter_mut().enumerate() {
                        let written = constructor.name.clone();
                        constructor.name =
                            self.declarations
                                .owned_constructor(&d.name, &constructor.name, index);
                        self.declarations.constructor_in(&d.name, &constructor.name);
                        if let Some(spelling) = written.spelling() {
                            self.declarations
                                .constructor_alias(spelling, &constructor.name);
                        }
                    }
                    self.generated(&d.name, Generation::Induction);
                    self.generated(&d.name, Generation::Recursion);
                    self.generated(&d.name, Generation::NoConfusionType);
                    self.generated(&d.name, Generation::NoConfusionDiagonal);
                    self.generated(&d.name, Generation::NoConfusion);
                    self.generated(&d.name, Generation::Equality);
                    self.generated(&d.name, Generation::EqualityReflexivity);
                    self.generated(&d.name, Generation::EqualitySoundness);
                    self.generated(&d.name, Generation::DecidableEquality);
                }
                Stmt::Struct(d) => {
                    let owner = self.declarations.register(&d.name);
                    for (index, constructor) in d.constructors.iter_mut().enumerate() {
                        if matches!(constructor.name, Name::Spelled(_)) {
                            constructor.name = owner.constructor(index, "Mk").into();
                        }
                        self.declarations.constructor_in(&d.name, &constructor.name);
                    }
                    if let [constructor] = d.constructors.as_slice() {
                        self.declarations
                            .constructor_alias(d.name.as_str(), &constructor.name);
                        let leaf = d.name.rsplit("::").next().unwrap();
                        self.declarations
                            .constructor_alias(&format!("{}::{leaf}", d.name), &constructor.name);
                    }
                }
                Stmt::Enum(d) => {
                    for (index, constructor) in d.constructors.iter_mut().enumerate() {
                        let written = constructor.name.clone();
                        constructor.name =
                            self.declarations
                                .owned_constructor(&d.name, &constructor.name, index);
                        self.declarations.constructor_in(&d.name, &constructor.name);
                        if let Some(spelling) = written.spelling() {
                            self.declarations
                                .constructor_alias(spelling, &constructor.name);
                        }
                    }
                }
                Stmt::Mutual { items, .. } | Stmt::Module { items, .. } => self.predeclare(items),
                Stmt::Attributed { stmt, .. } => self.predeclare(std::slice::from_mut(stmt)),
                _ => {}
            }
        }
    }

    /// Reserves the declarations of a source before its quotations are lifted.
    /// This does not resolve bodies or admit declarations to the kernel.
    pub fn reserve_declarations(&mut self, statements: &mut [Stmt]) {
        self.predeclare(statements);
    }

    /// Binds a quotation's definition-site globals. Bindings introduced by the
    /// quotation keep their syntax identities until expansion assigns scopes.
    pub fn quote_globals(&self, statements: &mut [Stmt]) {
        let mut retained: std::collections::HashSet<_> = self
            .declarations
            .bindings()
            .map(|(_, reference)| reference.clone())
            .collect();
        for statement in statements.iter_mut() {
            crate::surface::references::statement(statement, &mut |name| {
                if let Some(reference) = name.as_global() {
                    retained.insert(reference.clone());
                }
            });
        }
        let mut quotation = Self::new(self.declarations.quotation_environment());
        quotation.statements(statements);
        for statement in statements {
            crate::surface::references::statement(statement, &mut |name| {
                let retain = match name {
                    Name::Global(reference) => {
                        retained.contains(reference) || reference.sort().is_some()
                    }
                    Name::Spelled(_) => true,
                    _ => false,
                };
                if !retain {
                    *name = Name::from(name.as_str());
                }
            });
        }
    }

    pub fn statements(&mut self, statements: &mut [Stmt]) {
        self.predeclare(statements);
        let mut scope = Vec::new();
        for statement in statements {
            self.statement(statement, &mut scope, true, None);
        }
    }

    /// Captures constructor candidates in the source file's visible type
    /// environment after generated declarations and models have been named.
    pub fn statements_visible(
        &mut self,
        statements: &mut [Stmt],
        visible: &HashMap<String, String>,
    ) {
        self.statements_visible_among(statements, visible, None);
    }

    /// [`Self::statements_visible`], where `visible` was read before macros
    /// made some declarations: a constructor whose full name is not in
    /// `known`, what the files saw then, is one a macro made since (an `enum`
    /// of `syntax!`), and stays a pattern where its type is reached through
    /// the file's imports (`g::V`, `Str`). The constructors of another file
    /// the file does not import are in `known`, and stay hidden.
    pub fn statements_visible_among(
        &mut self,
        statements: &mut [Stmt],
        visible: &HashMap<String, String>,
        known: Option<&std::collections::HashSet<String>>,
    ) {
        self.predeclare(statements);
        let mut owners = visible
            .values()
            .filter_map(|name| {
                self.source_reference(name)
                    .and_then(|name| name.as_global().cloned())
            })
            .collect();
        fn own_types(
            statements: &[Stmt],
            declarations: &Declarations,
            owners: &mut std::collections::HashSet<crate::identity::DeclRef>,
        ) {
            for statement in statements {
                let name = match statement {
                    Stmt::Struct(data) | Stmt::Enum(data) => Some(&data.name),
                    Stmt::Inductive(data) => Some(&data.name),
                    Stmt::Mutual { items, .. } | Stmt::Module { items, .. } => {
                        own_types(items, declarations, owners);
                        None
                    }
                    Stmt::Attributed { stmt, .. } => {
                        own_types(std::slice::from_ref(stmt), declarations, owners);
                        None
                    }
                    _ => None,
                };
                if let Some(name) = name
                    && let Some(reference) =
                        name.as_global().or_else(|| declarations.get(name.as_str()))
                {
                    owners.insert(reference.clone());
                }
            }
        }
        own_types(statements, &self.declarations, &mut owners);
        if let Some(known) = known {
            let made: Vec<_> = self
                .declarations
                .bindings()
                .filter(|(_, reference)| {
                    let display = reference.display();
                    !known.contains(display)
                        && reference
                            .owner()
                            .is_some_and(|owner| !known.contains(owner.display()))
                })
                .map(|(_, reference)| reference.clone())
                .collect();
            owners.extend(made);
        }
        let candidates = self.declarations.restrict_constructor_owners(&owners);
        let mut scope = Vec::new();
        for statement in statements {
            self.statement(statement, &mut scope, true, None);
        }
        self.declarations.restore_constructor_candidates(candidates);
    }

    /// Binds source syntax in an explicit lexical context. Existing references
    /// are retained, including references whose displays coincide.
    pub fn term_in_context(&mut self, term: &mut SurfaceTerm, context: &[Name]) {
        let mut scope = context
            .iter()
            .map(|name| (name.to_string(), name.clone()))
            .collect();
        self.term(term, &mut scope);
    }

    fn reference(&mut self, name: &mut Name, scope: &Scope) {
        let Name::Spelled(spelling) = name else {
            return;
        };
        *name = scope
            .iter()
            .rev()
            .find(|(text, _)| text == spelling)
            .map(|(_, reference)| reference.clone())
            .or_else(|| {
                self.type_position
                    .then(|| self.declarations.type_named(spelling))
                    .flatten()
                    .map(|reference| Name::Global(reference.clone()))
            })
            .or_else(|| {
                // A constructor is never a type: where one is wanted, the library's type of
                // the name (`Bool`) is meant even when a constructor of the file is called so.
                // The file's own type of that name was found above.
                self.type_position
                    .then(|| crate::bindings::library_type(spelling))
                    .flatten()
                    .map(|reference| Name::Global(reference.clone()))
            })
            .or_else(|| self.declarations.type_constructor_selection(spelling))
            .or_else(|| {
                self.declarations
                    .get(spelling)
                    .filter(|reference| {
                        !self
                            .declarations
                            .is_constructor(&Name::Global((*reference).clone()))
                            && !self
                                .declarations
                                .source_constructor_hides(spelling, reference)
                    })
                    .cloned()
                    .map(Name::Global)
            })
            .or_else(|| self.declarations.selection(spelling))
            .unwrap_or_else(|| self.declarations.reserve(spelling).into());
    }

    /// Reads a term written where a type is wanted. A constructor is never a
    /// type, so a name that is both a type and a constructor (a `struct
    /// Remote` and a variant `Remote`) means the type here, whichever
    /// constructors are known when the type is read.
    fn type_term(&mut self, term: &mut SurfaceTerm, scope: &mut Scope) {
        let outer = std::mem::replace(&mut self.type_position, true);
        self.term(term, scope);
        self.type_position = outer;
    }

    fn declaration(&mut self, name: &mut Name) -> Owner {
        let reference = self.declarations.declare(name);
        *name = reference.clone().into();
        Owner::Declaration(reference.id())
    }

    fn constructor_reference(&mut self, name: &mut Name, scope: &Scope) {
        if let Some(spelling) = name.spelling()
            && let Some(choice) = self.declarations.selection(spelling)
        {
            *name = choice;
            return;
        }
        self.reference(name, scope);
    }

    fn bind(&mut self, name: &mut Name, scope: &mut Scope, owner: Owner, slot: &mut u32) {
        let spelling = name.to_string();
        if let Name::Spelled(_) = name {
            *name = self
                .locals
                .entry((owner, *slot, spelling.clone()))
                .or_insert_with(|| LocalRef::fresh(&spelling))
                .clone()
                .into();
        }
        *slot = slot
            .checked_add(1)
            .expect("too many binders in an occurrence");
        scope.push((spelling, name.clone()));
    }

    pub fn abstract_terms(
        &mut self,
        owner: &Name,
        binders: &mut [Name],
        terms: &mut [SurfaceTerm],
    ) {
        let owner = match self.global(owner) {
            Name::Global(reference) => Owner::Declaration(reference.id()),
            _ => panic!("a declaration owns an abstract term"),
        };
        let mut scope = Vec::new();
        let mut slot = 0;
        for binder in binders {
            self.bind(binder, &mut scope, owner, &mut slot);
        }
        for term in terms {
            self.term(term, &mut scope);
        }
    }

    fn effect_reference(&mut self, name: &mut Name, scope: &Scope) {
        if let Some(spelling) = name.spelling()
            && let Some(reference) = self.declarations.effect(spelling)
        {
            *name = Name::Global(reference.clone());
            return;
        }
        // The library's effect by its full name (a member a set of the
        // library writes): the library's declaration, imported or not.
        if let Some(reference) = name
            .spelling()
            .and_then(|s| s.strip_prefix(crate::surface::qualify::PRELUDE_MODULE))
            .and_then(|s| s.strip_prefix(crate::surface::qualify::SEPARATOR))
            .and_then(crate::bindings::library_effect)
        {
            *name = Name::Global(reference.clone());
            return;
        }
        // An entry of a row names an effect, a row variable, or a parameter;
        // never a constructor. A variant `Div` of an imported enum does not
        // stand for the effect `div` in a row.
        let Name::Spelled(spelling) = name else {
            return;
        };
        *name = scope
            .iter()
            .rev()
            .find(|(text, _)| text == spelling)
            .map(|(_, reference)| reference.clone())
            .or_else(|| {
                self.declarations
                    .get(spelling)
                    .filter(|reference| {
                        !self
                            .declarations
                            .is_constructor(&Name::Global((*reference).clone()))
                    })
                    .cloned()
                    .map(Name::Global)
            })
            .unwrap_or_else(|| self.declarations.reserve(spelling).into());
    }

    fn row(&mut self, row: &mut [Name], scope: &Scope) {
        for entry in row {
            if let Some(mut variable) = entry.row_variable() {
                let written = variable.to_string();
                self.reference(&mut variable, scope);
                if !matches!(variable, Name::Local(_)) {
                    variable = LocalRef::fresh(written).into();
                }
                *entry = variable.in_row();
            } else if let Name::Written(written) = entry {
                // `res(Pos)`, `∀ A. res(A)`: the effect and its argument
                // terms, under the row's parameters.
                let mut inner = scope.clone();
                let parameters: Vec<Name> = written
                    .parameters()
                    .iter()
                    .map(|text| {
                        let reference: Name = LocalRef::fresh(text).into();
                        inner.push((text.to_string(), reference.clone()));
                        reference
                    })
                    .collect();
                let mut effect = Name::from(written.head());
                self.effect_reference(&mut effect, &inner);
                if let Name::Global(effect) = effect {
                    let mut arguments = written.arguments().to_vec();
                    for argument in &mut arguments {
                        self.term(argument, &mut inner);
                    }
                    *entry = Name::Effect(Arc::new(EffectUse::new(
                        effect,
                        arguments,
                        parameters
                            .into_iter()
                            .map(|name| name.as_local().expect("row parameter").clone())
                            .collect(),
                        written.is_universal(),
                        written.display().to_string(),
                    )));
                }
                // An entry whose effect is not declared stays as written:
                // it names no effect, and the checkers report it so.
            } else if let Name::Spelled(_) = entry {
                self.effect_reference(entry, scope);
            }
        }
    }

    fn constraints(&mut self, constraints: &mut [Constraint], scope: &mut Scope) {
        for constraint in constraints {
            self.reference(&mut constraint.class, scope);
            self.term(&mut constraint.ty, scope);
            for arg in &mut constraint.arguments {
                self.term(arg, scope);
            }
        }
    }

    fn function(&mut self, function: &mut FnDecl, outer: &Scope) {
        let owner = match &function.name {
            Name::Local(reference) => Owner::Local(reference.id()),
            _ => self.declaration(&mut function.name),
        };
        self.function_body(function, outer, owner);
    }

    fn function_body(&mut self, function: &mut FnDecl, outer: &Scope, owner: Owner) {
        let previous = self.term_owner.replace((owner, 0));
        let mut scope = outer.clone();
        let mut slot = 0;
        for (index, generic) in function.generics.iter_mut().enumerate() {
            if let Some(ty) = function.generic_types.get_mut(index) {
                self.type_term(ty, &mut scope);
            }
            self.bind(generic, &mut scope, owner, &mut slot);
        }
        for bound in function.bounds.iter_mut().flatten() {
            if let Some(effects) = bound.effects_mut() {
                self.row(effects, &scope);
            }
        }
        for (index, parameter) in function.params.iter_mut().enumerate() {
            if let Some(Some(ty)) = function.param_types.get_mut(index) {
                self.type_term(ty, &mut scope);
            }
            self.bind(parameter, &mut scope, owner, &mut slot);
        }
        if let Some(result) = &mut function.result {
            self.type_term(result, &mut scope);
        }
        if let Some(effects) = &mut function.effects {
            self.row(effects, &scope);
        }
        if let Some(entries) = &mut function.written_effects {
            for entry in entries {
                self.row(std::slice::from_mut(&mut entry.name), &scope);
                if let Some(members) = &mut entry.members {
                    self.row(members, &scope);
                }
            }
        }
        self.constraints(&mut function.where_, &mut scope);
        if let Some(decreasing) = &mut function.decreasing_by {
            self.term(decreasing, &mut scope);
        }
        self.term(&mut function.body, &mut scope);
        self.term_owner = previous;
    }

    fn theorem(&mut self, theorem: &mut TheoremDecl, outer: &Scope) {
        let owner = self.declaration(&mut theorem.name);
        self.theorem_body(theorem, outer, owner);
    }

    fn theorem_body(&mut self, theorem: &mut TheoremDecl, outer: &Scope, owner: Owner) {
        let previous = self.term_owner.replace((owner, 0));
        let mut scope = outer.clone();
        let mut slot = 0;
        for (name, ty) in &mut theorem.params {
            self.term(ty, &mut scope);
            self.bind(name, &mut scope, owner, &mut slot);
        }
        self.term(&mut theorem.ty, &mut scope);
        if let Some(body) = &mut theorem.body {
            self.term(body, &mut scope);
        }
        if let Some(decreasing) = &mut theorem.decreasing_by {
            self.term(decreasing, &mut scope);
        }
        self.term_owner = previous;
    }

    fn data(&mut self, data: &mut DataDecl, outer: &Scope) {
        let owner = self.declaration(&mut data.name);
        let mut scope = outer.clone();
        let mut slot = 0;
        for generic in &mut data.generics {
            self.bind(generic, &mut scope, owner, &mut slot);
        }
        for constructor in &mut data.constructors {
            self.declaration(&mut constructor.name);
            for (_, ty) in &mut constructor.fields {
                self.type_term(ty, &mut scope);
            }
        }
    }

    fn statement(
        &mut self,
        statement: &mut Stmt,
        scope: &mut Scope,
        top: bool,
        site: Option<(Owner, u32)>,
    ) {
        match statement {
            Stmt::Fn(function) => self.function(function, scope),
            Stmt::Theorem(theorem) | Stmt::Def(theorem) => self.theorem(theorem, scope),
            Stmt::Let {
                name, ty, value, ..
            }
            | Stmt::Var {
                name, ty, value, ..
            } => {
                if let Some(ty) = ty {
                    self.type_term(ty, scope);
                }
                self.term(value, scope);
                if top {
                    self.declaration(name);
                } else {
                    let (owner, mut slot) =
                        site.expect("a local statement has a binding occurrence");
                    self.bind(name, scope, owner, &mut slot);
                }
            }
            Stmt::Assign {
                name, place, value, ..
            } => {
                self.reference(name, scope);
                if let Some(place) = place {
                    self.term(place, scope);
                }
                self.term(value, scope);
            }
            Stmt::Struct(data) | Stmt::Enum(data) => self.data(data, scope),
            Stmt::Inductive(data) => {
                let owner = self.declaration(&mut data.name);
                let mut inner = scope.clone();
                inner.push((data.name.to_string(), data.name.clone()));
                let mut slot = 0;
                for (name, ty) in &mut data.params {
                    self.term(ty, &mut inner);
                    self.bind(name, &mut inner, owner, &mut slot);
                }
                self.term(&mut data.sort, &mut inner);
                for constructor in &mut data.constructors {
                    let owner = self.declaration(&mut constructor.name);
                    let mut parameters = inner.clone();
                    let mut slot = 0;
                    for (name, ty) in &mut constructor.params {
                        self.type_term(ty, &mut parameters);
                        self.bind(name, &mut parameters, owner, &mut slot);
                    }
                    self.term(&mut constructor.result, &mut parameters);
                }
            }
            Stmt::Effect(effect) => {
                let reference = self.declarations.declare_effect(&effect.name);
                let owner = Owner::Declaration(reference.id());
                effect.name = reference.into();
                let mut inner = scope.clone();
                let mut slot = 0;
                for name in &mut effect.generics {
                    self.bind(name, &mut inner, owner, &mut slot);
                }
                for (index, ty) in effect.params.iter_mut().enumerate() {
                    if let Some(ty) = ty {
                        self.term(ty, &mut inner);
                    }
                    if let Some(name) = effect.param_names.get_mut(index) {
                        self.bind(name, &mut inner, owner, &mut slot);
                    }
                }
                if let Some(result) = &mut effect.result {
                    self.term(result, &mut inner);
                }
            }
            Stmt::Class(class) => {
                let owner = self.declaration(&mut class.name);
                let mut inner = scope.clone();
                let mut slot = 0;
                for (name, ty) in &mut class.parameters {
                    self.term(ty, &mut inner);
                    self.bind(name, &mut inner, owner, &mut slot);
                }
                if let Some((name, _)) = class.parameters.first() {
                    class.param = name.clone();
                }
                self.constraints(&mut class.parents, &mut inner);
                for (index, method) in class.methods.iter_mut().enumerate() {
                    let label = method.name.to_string();
                    let member = self.declarations.class_member(
                        &class.name,
                        &Name::from(label.as_str()),
                        index,
                        false,
                    );
                    self.function_body(
                        method,
                        &inner,
                        Owner::Declaration(member.as_global().expect("member declaration").id()),
                    );
                    method.name = label.into();
                }
                for (index, law) in class.laws.iter_mut().enumerate() {
                    let label = law.name.to_string();
                    law.theorem.name = self.declarations.class_member(
                        &class.name,
                        &Name::from(label.as_str()),
                        index,
                        true,
                    );
                    self.theorem(&mut law.theorem, &inner);
                    law.name = Name::from(label.as_str());
                    law.theorem.name = label.into();
                }
            }
            Stmt::Instance(instance) => {
                let mut inner = scope.clone();
                let owner = Owner::Term(instance.head.id());
                let mut slot = 0;
                for (index, name) in instance.generics.iter_mut().enumerate() {
                    if let Some(ty) = instance.generic_types.get_mut(index) {
                        self.term(ty, &mut inner);
                    }
                    self.bind(name, &mut inner, owner, &mut slot);
                }
                for bound in instance.bounds.iter_mut().flatten() {
                    if let Some(effects) = bound.effects_mut() {
                        self.row(effects, &inner);
                    }
                }
                self.reference(&mut instance.class, scope);
                // The head is a type: `instance C(Cancelled)` means the type
                // `Cancelled`, not its constructor of the same name.
                self.type_term(&mut instance.head, &mut inner);
                for arg in &mut instance.arguments {
                    self.term(arg, &mut inner);
                }
                self.constraints(&mut instance.where_, &mut inner);
                for method in &mut instance.methods {
                    self.function_body(method, &inner, Owner::Term(method.body.id()));
                    method.name = Name::from(method.name.as_str());
                }
                for law in &mut instance.laws {
                    let label = law.name.to_string();
                    let owner = Owner::Term(law.theorem.ty.id());
                    self.theorem_body(&mut law.theorem, &inner, owner);
                    law.name = Name::from(label.as_str());
                    law.theorem.name = label.into();
                }
            }
            Stmt::Extern {
                fns,
                types,
                instances,
                ..
            } => {
                for function in fns {
                    self.function(function, scope);
                }
                for data in types {
                    self.data(data, scope);
                }
                for instance in instances {
                    self.reference(&mut instance.class, scope);
                    self.term(&mut instance.ty, scope);
                }
            }
            Stmt::Mutual { items, .. } | Stmt::Module { items, .. } => {
                for item in items {
                    self.statement(item, scope, top, site);
                }
            }
            Stmt::Attributed { arg, stmt, .. } => {
                self.term(arg, scope);
                self.statement(stmt, scope, top, site);
            }
            Stmt::While { condition, body } => {
                self.term(condition, scope);
                self.term(body, scope);
            }
            Stmt::For {
                pattern,
                source,
                body,
            } => {
                self.term(source, scope);
                let mut inner = scope.clone();
                let (owner, mut slot) = site.unwrap_or((Owner::Term(body.id()), 0));
                self.pattern(pattern, &mut inner, owner, &mut slot);
                self.term(body, &mut inner);
            }
            Stmt::Loop { body: term }
            | Stmt::Break(Some(term))
            | Stmt::Return(Some(term))
            | Stmt::Expr(term)
            | Stmt::Called { call: term, .. } => self.term(term, scope),
            Stmt::Break(None)
            | Stmt::Continue
            | Stmt::Return(None)
            | Stmt::Reexport { .. }
            | Stmt::Import { .. }
            | Stmt::Syntax { .. }
            | Stmt::Macro { .. }
            | Stmt::Other(..) => {}
        }
    }

    fn pattern(&mut self, pattern: &mut Pattern, scope: &mut Scope, owner: Owner, slot: &mut u32) {
        match pattern {
            Pattern::Bind {
                name: Name::Selection(selection),
                ..
            } if selection.binding().is_some() => {
                scope.push((selection.display().to_string(), selection.clone().into()));
            }
            Pattern::Bind { name: name, .. } if self.declarations.is_constructor(name) => {
                let mut constructor = name.clone();
                self.constructor_reference(&mut constructor, scope);
                if constructor
                    .as_global()
                    .is_some_and(|r| r.is_primitive("true"))
                {
                    *pattern = Pattern::Bool(true);
                } else if constructor
                    .as_global()
                    .is_some_and(|r| r.is_primitive("false"))
                {
                    *pattern = Pattern::Bool(false);
                } else {
                    let candidates = match &constructor {
                        Name::Global(reference) => vec![reference.clone()],
                        Name::Selection(selection) => selection.candidates().to_vec(),
                        _ => unreachable!("a known constructor has declaration candidates"),
                    };
                    let mut local = Name::from(name.as_str());
                    self.bind(&mut local, scope, owner, slot);
                    let selection = crate::identity::Selection::new(name.to_string(), candidates)
                        .with_binding(local.as_local().expect("a pattern binds a local").clone());
                    let reference = Name::Selection(selection);
                    scope.last_mut().expect("the pattern scope").1 = reference.clone();
                    *name = reference;
                }
            }
            Pattern::Bind { name: name, .. } => self.bind(name, scope, owner, slot),
            Pattern::Ctor { name, args } => {
                self.constructor_reference(name, scope);
                for argument in args.iter_mut() {
                    self.pattern(argument, scope, owner, slot);
                }
                if args.is_empty() {
                    if name.as_global().is_some_and(|r| r.is_primitive("true")) {
                        *pattern = Pattern::Bool(true);
                    } else if name.as_global().is_some_and(|r| r.is_primitive("false")) {
                        *pattern = Pattern::Bool(false);
                    }
                }
            }
            Pattern::Record { name, fields } => {
                if name.spelling() != Some(crate::IMPLICITS) {
                    self.constructor_reference(name, scope);
                }
                for (_, field) in fields {
                    self.pattern(field, scope, owner, slot);
                }
            }
            Pattern::Typed { name, ty, .. } => {
                self.term(ty, scope);
                self.bind(name, scope, owner, slot);
            }
            Pattern::Wild
            | Pattern::Int(_)
            | Pattern::Bool(_)
            | Pattern::Text(_)
            | Pattern::Other(_) => {}
        }
    }

    fn term(&mut self, term: &mut SurfaceTerm, scope: &mut Scope) {
        // An occurrence is addressed within its owning declaration, independent
        // of parser allocation and byte offsets in a later source revision.
        let owner = match &mut self.term_owner {
            Some((owner, index)) => {
                let result = match *owner {
                    Owner::Declaration(id) => Owner::DeclarationTerm(id, *index),
                    Owner::Local(id) => Owner::LocalTerm(id, *index),
                    _ => Owner::Term(term.id()),
                };
                *index = index
                    .checked_add(1)
                    .expect("too many terms in a declaration");
                result
            }
            None => Owner::Term(term.id()),
        };
        let mut slot = 0;
        let span = term.span;
        let mut replaced = None;
        match Arc::make_mut(&mut term.kind) {
            TermKind::Var(name) => self.reference(name, scope),
            TermKind::Row(row) => self.row(row, scope),
            TermKind::Pi {
                params,
                result,
                effects,
                ..
            } => {
                let mut inner = scope.clone();
                for (name, ty) in params {
                    self.term(ty, &mut inner);
                    if let Some(name) = name {
                        self.bind(name, &mut inner, owner, &mut slot);
                    }
                }
                self.term(result, &mut inner);
                if let Some(effects) = effects {
                    self.row(effects, &inner);
                }
            }
            TermKind::Lam {
                params,
                types,
                body,
                ..
            } => {
                let mut inner = scope.clone();
                for (index, name) in params.iter_mut().enumerate() {
                    if let Some(Some(ty)) = types.get_mut(index) {
                        self.term(ty, &mut inner);
                    }
                    self.bind(name, &mut inner, owner, &mut slot);
                }
                self.term(body, &mut inner);
            }
            TermKind::Exists {
                binder,
                domain,
                body,
                ..
            } => {
                self.term(domain, scope);
                let mut inner = scope.clone();
                self.bind(binder, &mut inner, owner, &mut slot);
                self.term(body, &mut inner);
            }
            TermKind::Block(statements) => {
                let mut inner = scope.clone();
                for (index, statement) in statements.iter_mut().enumerate() {
                    if let Stmt::Fn(function) = statement {
                        let mut slot =
                            u32::try_from(index).expect("too many statements in a block");
                        self.bind(&mut function.name, &mut inner, owner, &mut slot);
                    }
                }
                for (index, statement) in statements.iter_mut().enumerate() {
                    let index = u32::try_from(index).expect("too many statements in a block");
                    self.statement(statement, &mut inner, false, Some((owner, index)));
                }
            }
            TermKind::Match {
                scrutinee,
                result,
                binder,
                arms,
                ..
            } => {
                self.term(scrutinee, scope);
                if let Some(result) = result {
                    self.term(result, scope);
                }
                let mut common = scope.clone();
                if let Some(binder) = binder {
                    self.bind(binder, &mut common, owner, &mut slot);
                }
                for arm in arms {
                    let mut inner = common.clone();
                    self.pattern(&mut arm.pattern, &mut inner, owner, &mut slot);
                    if let Some(guard) = &mut arm.guard {
                        self.term(guard, &mut inner);
                    }
                    if let Some(goal) = &mut arm.goal {
                        self.term(goal, &mut inner);
                    }
                    self.term(&mut arm.body, &mut inner);
                }
            }
            TermKind::Handle { body, handlers } => {
                self.term(body, scope);
                for handler in handlers {
                    let mut inner = scope.clone();
                    match handler {
                        Handler::Return { pattern, body } => {
                            self.pattern(pattern, &mut inner, owner, &mut slot);
                            self.term(body, &mut inner);
                        }
                        Handler::Operation {
                            effect,
                            instance,
                            patterns,
                            cont,
                            guard,
                            body,
                ..
            } => {
                            self.effect_reference(effect, scope);
                            for name in &mut instance.forall {
                                self.bind(name, &mut inner, owner, &mut slot);
                            }
                            for argument in &mut instance.args {
                                self.term(argument, &mut inner);
                            }
                            for pattern in patterns {
                                self.pattern(pattern, &mut inner, owner, &mut slot);
                            }
                            if let Some(cont) = cont {
                                self.bind(cont, &mut inner, owner, &mut slot);
                            }
                            if let Some(guard) = guard {
                                self.term(guard, &mut inner);
                            }
                            self.term(body, &mut inner);
                        }
                    }
                }
            }
            TermKind::Step(step) => {
                self.term(&mut step.arg, scope);
                if let Some(before) = &mut step.before {
                    self.term(before, scope);
                }
                for arm in &mut step.arms {
                    let mut inner = scope.clone();
                    for (name, ty) in &mut arm.binders {
                        self.term(ty, &mut inner);
                        self.bind(name, &mut inner, owner, &mut slot);
                    }
                    self.term(&mut arm.goal, &mut inner);
                    self.term(&mut arm.body, &mut inner);
                }
            }
            TermKind::Perform { effect, args } => {
                self.effect_reference(effect, scope);
                for argument in args.iter_mut() {
                    self.term(argument, scope);
                }
                replaced = host_budget(effect, args, span);
            }
            TermKind::Record { name, fields, base } => {
                if name.spelling() != Some(crate::IMPLICITS) {
                    self.constructor_reference(name, scope);
                }
                for (_, field) in fields {
                    self.term(field, scope);
                }
                if let Some(base) = base {
                    self.term(base, scope);
                }
            }
            _ => crate::surface::walk::children(term, &mut |child| self.term(child, scope)),
        }
        if let Some(budget) = replaced {
            term.kind = Arc::new(budget);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::span::Span;

    fn identity() -> SurfaceTerm {
        let span = Span { start: 0, end: 0 };
        SurfaceTerm::new(
            TermKind::Lam {
                params: vec![Name::from("x")],
                types: Vec::new(),
                body: Box::new(SurfaceTerm::var("x", span)),
                unused_params: Vec::new()
            },
            span,
        )
    }

    fn parts(term: &SurfaceTerm) -> (&Name, &Name) {
        let TermKind::Lam { params, body, .. } = &*term.kind else {
            panic!("lambda")
        };
        let TermKind::Var(reference) = &*body.kind else {
            panic!("reference")
        };
        (&params[0], reference)
    }

    #[test]
    fn generated_parameters_do_not_reuse_a_source_binder_slot() {
        let mut resolver = Resolver::default();
        let owner = Owner::Local(LocalId::fresh());
        let mut original = Name::from("e");
        let mut generated = Name::from("e@rowop");
        resolver.bind(&mut original, &mut Vec::new(), owner, &mut 0);
        resolver.bind(&mut generated, &mut Vec::new(), owner, &mut 0);
        assert_ne!(original, generated);
        assert_eq!(original.as_str(), "e");
        let mut cloned = Name::from("e");
        resolver.bind(&mut cloned, &mut Vec::new(), owner, &mut 0);
        assert_eq!(original, cloned);
    }

    #[test]
    fn cloned_occurrences_preserve_their_binding() {
        let mut proof = identity();
        let mut executable = proof.clone();
        let mut resolver = Resolver::default();
        resolver.term(&mut proof, &mut Vec::new());
        resolver.term(&mut executable, &mut Vec::new());
        let (binder, reference) = parts(&proof);
        assert!(matches!(binder, Name::Local(_)));
        assert_eq!(binder, reference);
        assert_eq!(parts(&proof), parts(&executable));
    }

    #[test]
    fn equal_spelling_does_not_identify_different_occurrences() {
        let mut first = identity();
        let mut second = identity();
        let mut resolver = Resolver::default();
        resolver.term(&mut first, &mut Vec::new());
        resolver.term(&mut second, &mut Vec::new());
        assert_eq!(parts(&first).0.as_str(), parts(&second).0.as_str());
        assert_ne!(parts(&first).0, parts(&second).0);
    }

    #[test]
    fn local_functions_have_block_owned_references() {
        fn block() -> SurfaceTerm {
            let span = Span::new(0, 1);
            let function = FnDecl {
                name: "f".into(),
                vis: Default::default(),
                generic_types: Vec::new(),
                generics: vec![],
                rows: vec![],
                bounds: vec![],
                bound_spans: vec![],
                params: vec![],
                borrows: vec![],
                param_types: vec![],
                result: None,
                lends: None,
                effects: None,
                written_effects: None,
                row_hole: None,
                where_: vec![],
                span,
                opaque: false,
                ghost: false,
                decreasing_by: None,
                generates: None,
                budget: None,
                body: SurfaceTerm::var("f", span),
                unused: None,
                unused_generics: Vec::new(),
                unused_params: Vec::new()
            };
            SurfaceTerm::new(
                TermKind::Block(vec![
                    Stmt::Expr(SurfaceTerm::var("f", span)),
                    Stmt::Fn(function),
                ]),
                span,
            )
        }
        fn reference(block: &SurfaceTerm) -> &Name {
            let TermKind::Block(statements) = &*block.kind else {
                panic!("block")
            };
            let Stmt::Expr(before) = &statements[0] else {
                panic!("reference")
            };
            let Stmt::Fn(function) = &statements[1] else {
                panic!("function")
            };
            assert!(matches!(&function.name, Name::Local(_)));
            assert!(matches!(&*before.kind, TermKind::Var(name) if name == &function.name));
            assert!(matches!(&*function.body.kind, TermKind::Var(name) if name == &function.name));
            &function.name
        }
        let mut first = block();
        let mut clone = first.clone();
        let mut second = block();
        let mut resolver = Resolver::default();
        for term in [&mut first, &mut clone, &mut second] {
            resolver.term(term, &mut Vec::new());
        }
        assert_eq!(reference(&first), reference(&clone));
        assert_ne!(reference(&first), reference(&second));
    }
}

/// `perform budget(n, f)` and `perform budget_memory(n, f)` of the host: the
/// budget term, when `effect` resolved to the library's operation. Only the
/// resolved declaration decides it: a program's own `effect budget` is an
/// effect of the program, performed as any other, though spelled the same.
/// The host's takes two plain arguments, the most steps or cells and the
/// function of no parameter to run; its body runs where the budget is
/// written, so a written `() => e` is read as `e`, and any other function
/// `f` as the call `f()`.
fn host_budget(effect: &Name, args: &[SurfaceTerm], span: crate::span::Span) -> Option<TermKind> {
    let reference = effect.as_global()?;
    let limit = [BudgetLimit::Steps, BudgetLimit::Memory].into_iter().find(|limit| {
        crate::bindings::library_reference(limit.operation()).as_ref()
            == Some(&Name::Global(reference.clone()))
    })?;
    Some(budget_term(limit, args, span))
}

/// The host's budgets of a program read as written (`parse_program_as_written`),
/// whose names stay spelled: there a `perform` names the library's operation
/// when the program declares no effect under its spelling, which is how such a
/// program's names resolve (`modules::resolve` has already written an effect
/// of a module with its module's path). A program's own `effect budget`
/// keeps its `perform`s its own.
pub fn host_budgets_as_written(stmts: &mut [Stmt]) {
    fn declared(stmts: &[Stmt], spelling: &str) -> bool {
        stmts.iter().any(|s| match s {
            Stmt::Effect(e) => e.name.spelling() == Some(spelling),
            _ => false,
        })
    }
    let limits: Vec<BudgetLimit> = [BudgetLimit::Steps, BudgetLimit::Memory]
        .into_iter()
        .filter(|limit| !declared(stmts, limit.operation()))
        .collect();
    if limits.is_empty() {
        return;
    }
    for statement in stmts.iter_mut() {
        crate::surface::walk::stmt(statement, &mut |t| {
            let TermKind::Perform {
                effect: Name::Spelled(spelling),
                args,
            } = &*t.kind
            else {
                return;
            };
            if let Some(limit) = limits.iter().find(|l| l.operation() == spelling.as_str()) {
                t.kind = Arc::new(budget_term(*limit, args, t.span));
            }
        });
    }
}

fn budget_term(limit: BudgetLimit, args: &[SurfaceTerm], span: crate::span::Span) -> TermKind {
    let plain = |a: &SurfaceTerm| match &*a.kind {
        TermKind::Ascribe { .. } | TermKind::Other(_) => false,
        TermKind::Record { name, .. } => name.spelling() != Some(crate::IMPLICITS),
        _ => true,
    };
    let [steps, f] = args else {
        return budget_refused(limit);
    };
    if !plain(steps) || !plain(f) {
        return budget_refused(limit);
    }
    let body = match &*f.kind {
        TermKind::Lam { params, body, .. } if params.is_empty() => (**body).clone(),
        _ => SurfaceTerm::new(
            TermKind::App {
                function: Box::new(f.clone()),
                arguments: Vec::new(),
            },
            span,
        ),
    };
    TermKind::Budget {
        limit,
        steps: Box::new(steps.clone()),
        body: Box::new(body),
    }
}

fn budget_refused(limit: BudgetLimit) -> TermKind {
    TermKind::Other(format!(
        "`perform {}(n, f)` takes the most {} and the function of no parameter to run",
        limit.operation(),
        match limit {
            BudgetLimit::Steps => "steps",
            BudgetLimit::Memory => "cells",
        }
    ))
}
