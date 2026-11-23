//! Closed nominal boundaries and native data adapters.
use super::*;

impl Eraser<'_> {
    pub(super) fn wrapper(&mut self, name: &Name) -> Result<Option<String>, Message> {
        let (_, f) = self.functions[name].clone();
        let sig = &self.checked.signatures[name];
        if sig.params[..self.arity(name)]
            .iter()
            .any(|r| *r != Role::Value)
        {
            return Ok(None);
        }
        let Some(types) = self.checked.boundary_types.get(name).cloned() else {
            return Ok(None);
        };
        // A value in an implicit telescope is an ordinary argument at the
        // executable boundary. Retain the complete checked source order.
        // Non-closed domains have no BoundaryType and are not exported here.
        let parameters: Vec<_> = f.generics.iter().chain(&f.params).collect();
        if types.len() != parameters.len() + 1 {
            return Ok(None);
        }
        let mut params = Vec::new();
        let mut args = Vec::new();
        for (n, t) in parameters.into_iter().zip(&types) {
            let Some(t) = t else { return Ok(None) };
            let Some((ty, pack, _)) = self.boundary(t)? else {
                return Ok(None);
            };
            params.push(format!("{}: {ty}", self.symbol(n)));
            args.push(pack.replace("$v", &self.symbol(n)));
        }
        let Some(Some(t)) = types.last() else {
            return Ok(None);
        };
        let Some((ty, _, unpack)) = self.boundary(t)? else {
            return Ok(None);
        };
        let target = self.name(name);
        let value = format!("{target}({})", args.join(", "));
        let row = f.effects.as_deref().unwrap_or_default();
        let value = if !row.is_empty() {
            let Some(run) = self.native_computation(row)? else {
                return Ok(None);
            };
            format!("{run}({value})")
        } else if self.computations {
            format!("TautoErasedFinish#r0({value})")
        } else {
            value
        };
        let effects = if row.is_empty() {
            String::new()
        } else {
            format!(
                " ! {{{}}}",
                std::iter::once("div")
                    .chain(
                        row.iter()
                            .map(|name| self.symbol(name))
                            .collect::<Vec<_>>()
                            .iter()
                            .map(String::as_str)
                    )
                    .collect::<Vec<_>>()
                    .join(", ")
            )
        };
        let body = unpack.replace("$v", &value);
        self.exports.insert(name.clone());
        self.total.insert(name.clone());
        Ok(Some(format!(
            "pub fn {}({}): {ty}{effects} {{ {body} }}",
            self.symbol(name),
            params.join(", ")
        )))
    }

    /// Ordinary data keeps its existing Nib representation at the boundary.
    /// Type arguments carry their own bridges, including opaque refinements.
    pub(super) fn native_family(
        &mut self,
        head: &Name,
        arguments: Vec<(String, String, String)>,
    ) -> Result<Option<(String, String, String)>, Message> {
        let Some(decl) = self.declarations.get(head).cloned() else {
            return Ok(None);
        };
        if self.constrained.contains(head) || arguments.len() != decl.params.len() {
            return Ok(None);
        }
        let ty = if arguments.is_empty() {
            self.symbol(head)
        } else {
            format!(
                "{}({})",
                self.symbol(head),
                arguments
                    .iter()
                    .map(|a| a.0.clone())
                    .collect::<Vec<_>>()
                    .join(", ")
            )
        };
        if let Some((pack, unpack)) = self.bridges.get(&ty) {
            return Ok(Some((ty, format!("{pack}($v)"), format!("{unpack}($v)"))));
        }
        if !self.active_bridges.insert(head.into()) {
            return Err("dependent extraction: a native boundary cannot expand a recursively changing type; keep it inside checked code".into());
        }
        let from = self.fresh("PackData");
        let to = self.fresh("UnpackData");
        self.bridges.insert(ty.clone(), (from.clone(), to.clone()));
        let env: BTreeMap<_, _> = decl
            .params
            .iter()
            .map(|(n, _)| n.clone())
            .zip(arguments)
            .collect();
        let mut pack_arms = Vec::new();
        let mut unpack_arms = Vec::new();
        for ctor in &decl.constructors {
            let roles = self.checked.signatures[&ctor.name].params[decl.params.len()..].to_vec();
            let mut names = Vec::new();
            let mut packed = Vec::new();
            let mut unpacked = Vec::new();
            let mut fields = Vec::new();
            for ((field, field_ty), role) in ctor.params.iter().zip(roles) {
                if role != Role::Value {
                    continue;
                }
                let Some((_, pack, unpack)) = self.native_field(field_ty, &env)? else {
                    return Err(msg!(
                        "tauto-extract-dependent-no-native-field",
                        head = head.to_string(),
                        field = field.to_string()
                    ));
                };
                let value = self.fresh("Field");
                packed.push(pack.replace("$v", &value));
                unpacked.push(unpack.replace("$v", &value));
                names.push(value);
                fields.push(field.clone());
            }
            let variant = self.ctor(&ctor.name)?;
            let native = |values: &[String]| {
                if decl.constructors.len() == 1 && !fields.is_empty() {
                    format!(
                        "{} {{ {} }}",
                        self.symbol(head),
                        fields
                            .iter()
                            .zip(values)
                            .map(|(f, v)| format!("{}: {v}", raw(f)))
                            .collect::<Vec<_>>()
                            .join(", ")
                    )
                } else if values.is_empty() {
                    self.symbol(&ctor.name)
                } else {
                    format!("{}({})", self.symbol(&ctor.name), values.join(", "))
                }
            };
            let dynamic = |values: &[String]| {
                if values.is_empty() {
                    variant.clone()
                } else {
                    format!("{variant}({})", values.join(", "))
                }
            };
            pack_arms.push(format!("{} => {}", native(&names), dynamic(&packed)));
            unpack_arms.push(format!("{} => {}", dynamic(&names), native(&unpacked)));
        }
        unpack_arms.push("_ => extract_unreachable()".into());
        self.definitions.push(format!("fn {from}(value: {ty}): {VALUE} {{ match value {{\n{}\n}} }}\nfn {to}(value: {VALUE}): {ty} {{ match value {{\n{}\n}} }}", pack_arms.join("\n"), unpack_arms.join("\n")));
        self.total
            .extend([Name::from(from.clone()), Name::from(to.clone())]);
        self.forbidden.extend([from.clone(), to.clone()]);
        self.active_bridges.remove(head);
        Ok(Some((ty, format!("{from}($v)"), format!("{to}($v)"))))
    }
    pub(super) fn native_field(
        &mut self,
        ty: &SurfaceTerm,
        env: &BTreeMap<Name, (String, String, String)>,
    ) -> Result<Option<(String, String, String)>, Message> {
        if let TermKind::Var(n) = &*ty.kind {
            if let Some(repr) = env.get(n) {
                return Ok(Some(repr.clone()));
            }
            if self.std.of(n) == Some("Int") {
                return self.integer_bridge().map(Some);
            }
            if matches!(
                self.std.of(n),
                Some("Nat" | "Bool" | "Text" | "UHost")
            ) {
                return self.boundary(&crate::check::BoundaryType {
                    id: usize::MAX,
                    ty: ty.clone(),
                    arguments: Vec::new(),
                });
            }
            return self.native_family(n, Vec::new());
        }
        // `@a T`: the native type keeps the label, which the checked value
        // does not carry, so packing takes it off and unpacking puts it on.
        if let TermKind::Tagged { tag, term } = &*ty.kind {
            let Some((inner, pack, unpack)) = self.native_field(term, env)? else {
                return Ok(None);
            };
            return Ok(Some((
                format!("@{tag} ({inner})"),
                format!(
                    "match ($v) {{ @{tag} tauto_label => {} }}",
                    pack.replace("$v", "tauto_label")
                ),
                format!("@{tag} ({unpack})"),
            )));
        }
        if let TermKind::App {
            function,
            arguments,
        } = &*ty.kind
        {
            if head_name(function).and_then(|head| self.std.of(head)) == Some("Quot") {
                return match arguments.first() {
                    Some(value) => self.native_field(value, env),
                    None => Ok(None),
                };
            }
            // `UInt(64)`, `SInt(64)`: a machine word, as the boundary writes it.
            if matches!(
                head_name(function).and_then(|head| self.std.of(head)),
                Some("UInt" | "SInt")
            ) {
                return self.boundary(&crate::check::BoundaryType {
                    id: usize::MAX,
                    ty: ty.clone(),
                    arguments: Vec::new(),
                });
            }
            let mut reprs = Vec::new();
            for argument in arguments {
                let Some(repr) = self.native_field(argument, env)? else {
                    return Ok(None);
                };
                reprs.push(repr);
            }
            return match head_name(function) {
                Some(head) => self.native_family(head, reprs),
                None => Ok(None),
            };
        }
        Ok(None)
    }
    /// The packing and unpacking of the bytes of `Text::Mk(bytes)`: the
    /// field's type as the standard library declares it, `List(Nat)`. The
    /// native `Text` is not a constructor value, so building or taking
    /// apart a text goes through its bytes.
    pub(super) fn text_bytes_bridge(&mut self) -> Result<(String, String), Message> {
        let field = self
            .declarations
            .iter()
            .find(|(name, _)| self.std.of(name) == Some("Text"))
            .and_then(|(_, decl)| match decl.constructors.as_slice() {
                [ctor] => match ctor.params.as_slice() {
                    [(_, ty)] => Some(ty.clone()),
                    _ => None,
                },
                _ => None,
            })
            .ok_or("dependent extraction: the standard library's Text::Mk")?;
        let (_, pack, unpack) = self
            .native_field(&field, &BTreeMap::new())?
            .ok_or("dependent extraction: the bytes of Text::Mk")?;
        Ok((pack, unpack))
    }
    pub(super) fn integer_bridge(&mut self) -> Result<(String, String, String), Message> {
        let info = self
            .checked
            .boundary_types
            .values()
            .flatten()
            .flatten()
            .find(|info| head_name(&info.ty).and_then(|head| self.std.of(head)) == Some("Int"))
            .cloned()
            .ok_or("dependent extraction: missing checked Int boundary")?;
        self.boundary(&info)?
            .ok_or("dependent extraction: Int representation".into())
    }
    pub(super) fn boundary(
        &mut self,
        info: &crate::check::BoundaryType,
    ) -> Result<Option<(String, String, String)>, Message> {
        let t = &info.ty;
        if matches!(&*t.kind, TermKind::Pi { .. }) {
            return Ok(Some(self.opaque_boundary(info.id)));
        }
        if let TermKind::Var(n) = &*t.kind {
            match self.std.of(n) {
                Some("Nat") => {
                    return Ok(Some((
                        "nat".into(),
                        format!("{NAT}($v)"),
                        "TautoErasedGetNat#r0($v)".into(),
                    )));
                }
                Some("Bool") => {
                    return Ok(Some((
                        "Bool".into(),
                        format!("{BOOL}($v)"),
                        "TautoErasedGetBool#r0($v)".into(),
                    )));
                }
                Some("i64") => {
                    return Ok(Some((
                        "i64".into(),
                        "TautoErasedI64#r0($v)".into(),
                        "TautoErasedGetI64#r0($v)".into(),
                    )));
                }
                Some("Text") => {
                    return Ok(Some((
                        "Text".into(),
                        "TautoErasedText#r0($v)".into(),
                        "TautoErasedGetText#r0($v)".into(),
                    )));
                }
                _ => {}
            }
        }
        let Some(head) = head_name(t) else {
            return Ok(None);
        };
        if self.std.of(head) == Some("Quot") {
            return match info.arguments.first() {
                Some(value) => self.boundary(value),
                None => Ok(None),
            };
        }
        // The width of `UInt(w)` and `SInt(w)`, a numeral.
        let width = match &*t.kind {
            TermKind::App { arguments, .. } => match arguments.as_slice() {
                [w] => match &*w.kind {
                    TermKind::Nat(w) => Some(w.as_str()),
                    _ => None,
                },
                _ => None,
            },
            _ => None,
        };
        if self.std.of(head) == Some("SInt") && width == Some("64") {
            return Ok(Some((
                "i64".into(),
                "TautoErasedI64#r0($v)".into(),
                "TautoErasedGetI64#r0($v)".into(),
            )));
        }
        if !self
            .checked
            .families
            .get(head)
            .is_some_and(|f| !f.prop && !f.predicate)
        {
            return Ok(None);
        }
        if self.std.of(head) == Some("Int") {
            let fam = self.checked.families[head].clone();
            let positive = fam
                .ctors
                .iter()
                .find(|c| self.std.of(c) == Some("Int::IntOfNat"))
                .ok_or("dependent boundary: IntOfNat")?
                .clone();
            let negative = fam
                .ctors
                .iter()
                .find(|c| self.std.of(c) == Some("Int::IntNegSucc"))
                .ok_or("dependent boundary: IntNegSucc")?
                .clone();
            let p = self.ctor(&positive)?;
            let n = self.ctor(&negative)?;
            let from = format!("TautoErasedPack{}#r0", info.id);
            let to = format!("TautoErasedUnpack{}#r0", info.id);
            if self.total.insert(from.clone().into()) {
                let (head, positive, negative) = (
                    self.symbol(head),
                    self.symbol(&positive),
                    self.symbol(&negative),
                );
                self.definitions.push(format!("fn {from}(value: {head}): {VALUE} {{ match value {{ {positive}(v) => {p}({NAT}(v))\n {negative}(v) => {n}({NAT}(v)) }} }}\nfn {to}(value: {VALUE}): {head} {{ match value {{ {p}(v) => {positive}(TautoErasedGetNat#r0(v))\n {n}(v) => {negative}(TautoErasedGetNat#r0(v))\n _ => extract_unreachable() }} }}\n"));
                self.total.insert(to.clone().into());
                self.forbidden.extend([from.clone(), to.clone()]);
            }
            return Ok(Some((
                self.symbol(head),
                format!("{from}($v)"),
                format!("{to}($v)"),
            )));
        }
        // `UHost` is the machine word `uhost`, not a struct: its one
        // constructor carries the number, so packing reads the word as a
        // number and unpacking checks nothing (the proof says it fits).
        if self.std.of(head) == Some("UHost") {
            let fam = self.checked.families[head].clone();
            let ctor = fam
                .ctors
                .first()
                .ok_or("dependent boundary: UHost::Mk")?
                .clone();
            let c = self.ctor(&ctor)?;
            let from = format!("TautoErasedPack{}#r0", info.id);
            let to = format!("TautoErasedUnpack{}#r0", info.id);
            if self.total.insert(from.clone().into()) {
                self.definitions.push(format!("fn {from}(value: uhost): {VALUE} {{ {c}({NAT}(Nat::of_u64(U64::of_uhost(value)))) }}\nfn {to}(value: {VALUE}): uhost {{ match value {{ {c}(v) => UHost::of_u64_below(U64::of_nat(TautoErasedGetNat#r0(v)))\n _ => extract_unreachable() }} }}\n"));
                self.total.insert(to.clone().into());
                self.forbidden.extend([from.clone(), to.clone()]);
            }
            return Ok(Some(("uhost".into(), format!("{from}($v)"), format!("{to}($v)"))));
        }
        // `UInt(8)` / `UInt(32)` / `UInt(64)` are machine words, not structs: like `UHost`,
        // each constructor carries the number, and the proof says it fits.
        if let Some((std_name, nib_ty, pack_body, unpack_body)) = match (self.std.of(head), width) {
            (Some("UInt"), Some("8")) => Some((
                "U8",
                "u8",
                "Nat::of_u64(U64::of_u8(value))",
                "U8::of_u64(U64::of_nat(TautoErasedGetNat#r0(v)))",
            )),
            (Some("UInt"), Some("32")) => Some((
                "U32",
                "u32",
                "Nat::of_u64(U64::of_u32(value))",
                "U32::of_u64(U64::of_nat(TautoErasedGetNat#r0(v)))",
            )),
            (Some("UInt"), Some("64")) => Some((
                "U64",
                "u64",
                "Nat::of_u64(value)",
                "U64::of_nat(TautoErasedGetNat#r0(v))",
            )),
            _ => None,
        } {
            let fam = self.checked.families[head].clone();
            let ctor = fam
                .ctors
                .first()
                .ok_or(format!("dependent boundary: {std_name}::Mk"))?
                .clone();
            let c = self.ctor(&ctor)?;
            let from = format!("TautoErasedPack{}#r0", info.id);
            let to = format!("TautoErasedUnpack{}#r0", info.id);
            if self.total.insert(from.clone().into()) {
                self.definitions.push(format!("fn {from}(value: {nib_ty}): {VALUE} {{ {c}({NAT}({pack_body})) }}\nfn {to}(value: {VALUE}): {nib_ty} {{ match value {{ {c}(v) => {unpack_body}\n _ => extract_unreachable() }} }}\n"));
                self.total.insert(to.clone().into());
                self.forbidden.extend([from.clone(), to.clone()]);
            }
            return Ok(Some((
                nib_ty.into(),
                format!("{from}($v)"),
                format!("{to}($v)"),
            )));
        }
        if matches!(self.std.of(head), Some("Option" | "List")) {
            let Some(arg) = info.arguments.first() else {
                return Ok(None);
            };
            let Some((inner, pack, unpack)) = self.boundary(arg)? else {
                return Ok(None);
            };
            let fam = self.checked.families[head].clone();
            let empty = fam
                .ctors
                .iter()
                .find(|c| {
                    self.checked.signatures[*c].params[fam.params..]
                        .iter()
                        .all(|r| *r != Role::Value)
                })
                .ok_or("dependent boundary: empty constructor")?
                .clone();
            let full = fam
                .ctors
                .iter()
                .find(|c| **c != empty)
                .ok_or("dependent boundary: nonempty constructor")?
                .clone();
            let empty_ctor = self.ctor(&empty)?;
            let full_ctor = self.ctor(&full)?;
            let from = format!("TautoErasedPack{}#r0", info.id);
            let to = format!("TautoErasedUnpack{}#r0", info.id);
            let list = self.std.of(head) == Some("List");
            // The family's own constructors, by reference: a program that
            // declares its own `None` or `Nil` must not capture these patterns.
            let (empty_pat, full_pat, source) =
                (self.symbol(&empty), self.symbol(&full), self.symbol(head));
            let tail = if list { ", tail" } else { "" };
            let ty = format!("{source}({inner})");
            if self.total.insert(from.clone().into()) {
                let p = pack.replace("$v", "item");
                let u = unpack.replace("$v", "item");
                let packed_tail = if list {
                    format!(", {from}(tail)")
                } else {
                    String::new()
                };
                let unpacked_tail = if list {
                    format!(", {to}(tail)")
                } else {
                    String::new()
                };
                self.definitions.push(format!("fn {from}(value: {ty}): {VALUE} {{ match value {{ {empty_pat} => {empty_ctor}\n {full_pat}(item{tail}) => {full_ctor}({p}{packed_tail}) }} }}\nfn {to}(value: {VALUE}): {ty} {{ match value {{ {empty_ctor} => {empty_pat}\n {full_ctor}(item{tail}) => {full_pat}({u}{unpacked_tail})\n _ => extract_unreachable() }} }}\n"));
                self.total.insert(to.clone().into());
                self.forbidden.extend([from.clone(), to.clone()]);
            }
            return Ok(Some((ty, format!("{from}($v)"), format!("{to}($v)"))));
        }
        if !self.constrained.contains(head) {
            let mut arguments = Vec::new();
            for arg in &info.arguments {
                let Some(repr) = self.boundary(arg)? else {
                    return Ok(None);
                };
                arguments.push(repr);
            }
            return self.native_family(head, arguments);
        }
        Ok(Some(self.opaque_boundary(info.id)))
    }

    pub(super) fn opaque_boundary(&mut self, key: usize) -> (String, String, String) {
        let n = if let Some(n) = self.opaque.get(&key) {
            n.clone()
        } else {
            let n = self.fresh("Opaque");
            self.opaque.insert(key, n.clone());
            n
        };
        (
            n.clone(),
            "($v).value".into(),
            format!("{n} {{ value: $v }}"),
        )
    }
}

use super::computation::REQUEST;

impl Eraser<'_> {
    pub(super) fn native_effect(&mut self, name: &Name) -> Result<bool, Message> {
        if self.native_effects.contains(name) {
            return Ok(true);
        }
        let Some(types) = self.checked.effect_types.get(name).cloned() else {
            return Ok(false);
        };
        let mut native = Vec::new();
        for ty in types {
            let Some(ty) = ty else {
                return Ok(false);
            };
            let Some(repr) = self.boundary(&ty)? else {
                return Ok(false);
            };
            native.push(repr.0);
        }
        let Some(result) = native.pop() else {
            return Ok(false);
        };
        let params = native
            .iter()
            .enumerate()
            .map(|(i, ty)| format!("arg{i}: {ty}"))
            .collect::<Vec<_>>();
        let resume = self
            .checked
            .effect_resumes
            .get(name)
            .and_then(|r| r.as_ref())
            .map(|r| {
                if r == "direct" {
                    " direct".to_string()
                } else {
                    format!(" resume {r}")
                }
            })
            .unwrap_or_default();
        self.definitions.push(format!(
            "effect {}({}): {result}{resume}",
            self.symbol(name),
            params.join(", ")
        ));
        self.native_effects.insert(name.clone());
        Ok(true)
    }

    pub(super) fn native_computation(&mut self, row: &[Name]) -> Result<Option<String>, Message> {
        for effect in row {
            if !self.native_effect(effect)? {
                return Ok(None);
            }
        }
        let run = self.fresh("Run");
        let mut dispatch = "extract_unreachable()".to_string();
        for effect in row.iter().rev() {
            let types = self.checked.effect_types[effect].clone();
            let mut native = Vec::new();
            for ty in types {
                native.push(self.boundary(&ty.unwrap())?.unwrap());
            }
            let (_, pack, _) = native.pop().unwrap();
            let names: Vec<_> = native.iter().map(|_| self.fresh("Parameter")).collect();
            let args: Vec<_> = native
                .iter()
                .zip(&names)
                .map(|((_, _, unpack), name)| unpack.replace("$v", name))
                .collect();
            let (nil, cons) = self.list_constructors()?;
            let pattern = names
                .iter()
                .rev()
                .fold(nil, |tail, name| format!("{cons}({name}, {tail})"));
            let answer = self.fresh("Answer");
            let packed = pack.replace("$v", &answer);
            let call = format!(
                "{{ let {answer} := perform {}({})\n {run}(TautoErasedApply#r0(continuation, [{packed}])) }}",
                self.symbol(effect),
                args.join(", ")
            );
            let tag = self.effect_tag(effect);
            dispatch = format!(
                "if tag == {tag} {{ match args {{ {pattern} => {call}\n _ => extract_unreachable() }} }} else {{ {dispatch} }}"
            );
        }
        self.definitions.push(format!("fn {run}(value: {VALUE}): {VALUE} ! {{{}}} {{ match value {{ {REQUEST}(tag, args, continuation) => {dispatch}\n _ => value }} }}", std::iter::once("div").chain(row.iter().map(|name| self.symbol(name)).collect::<Vec<_>>().iter().map(String::as_str)).collect::<Vec<_>>().join(", ")));
        self.total.insert(run.clone().into());
        self.forbidden.insert(run.clone());
        Ok(Some(run))
    }

    /// The prelude list's `Nil` and `Cons`, as reference slots.
    fn list_constructors(&self) -> Result<(String, String), Message> {
        let mut nil = None;
        let mut cons = None;
        for family in &self.checked.families {
            if self.std.of(family.0) != Some("List") {
                continue;
            }
            for c in &family.1.ctors {
                match self.std.of(c) {
                    Some("Nil") => nil = Some(self.symbol(c)),
                    Some("Cons") => cons = Some(self.symbol(c)),
                    _ => {}
                }
            }
        }
        nil.zip(cons)
            .ok_or_else(|| "dependent boundary: no list".into())
    }
}
