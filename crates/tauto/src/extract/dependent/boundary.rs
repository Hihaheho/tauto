//! Closed nominal boundaries and native data adapters.
use super::*;

impl Eraser<'_> {
    pub(super) fn wrapper(&mut self, name: &str) -> Result<Option<String>, String> {
        let (_, f) = self.functions[name].clone();
        let sig = &self.checked.signatures[name];
        if !f.generics.is_empty()
            || sig.params[..self.arity(name)]
                .iter()
                .any(|r| *r != Role::Value)
        {
            return Ok(None);
        }
        let Some(types) = self.checked.boundary_types.get(name).cloned() else {
            return Ok(None);
        };
        if types.len() != f.params.len() + 1 {
            return Ok(None);
        }
        let mut params = Vec::new();
        let mut args = Vec::new();
        for (n, t) in f.params.iter().zip(&types) {
            let Some(t) = t else { return Ok(None) };
            let Some((ty, pack, _)) = self.boundary(t)? else {
                return Ok(None);
            };
            params.push(format!("{}: {ty}", raw(n)));
            args.push(pack.replace("$v", &raw(n)));
        }
        let Some(Some(t)) = types.last() else {
            return Ok(None);
        };
        let Some((ty, _, unpack)) = self.boundary(t)? else {
            return Ok(None);
        };
        let target = self.name(name);
        let body = unpack.replace("$v", &format!("{target}({})", args.join(", ")));
        let short = name.rsplit("::").next().unwrap();
        self.exports.insert(name.into());
        self.total.insert(name.into());
        Ok(Some(in_modules_text(
            name,
            &format!(
                "pub fn {}({}): {ty} {{ {body} }}",
                raw(short),
                params.join(", ")
            ),
        )))
    }
    /// Ordinary data keeps its existing Nib representation at the boundary.
    /// Type arguments carry their own bridges, including opaque refinements.
    pub(super) fn native_family(
        &mut self,
        head: &str,
        arguments: Vec<(String, String, String)>,
    ) -> Result<Option<(String, String, String)>, String> {
        let Some(decl) = self.declarations.get(head).cloned() else {
            return Ok(None);
        };
        if self.constrained.contains(head) || arguments.len() != decl.params.len() {
            return Ok(None);
        }
        let ty = if arguments.is_empty() {
            head.to_owned()
        } else {
            format!(
                "{head}({})",
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
                    return Err(format!(
                        "dependent extraction: no native representation for field {head}::{field}"
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
                        "{head} {{ {} }}",
                        fields
                            .iter()
                            .zip(values)
                            .map(|(f, v)| format!("{}: {v}", raw(f)))
                            .collect::<Vec<_>>()
                            .join(", ")
                    )
                } else if values.is_empty() {
                    ctor.name.clone()
                } else {
                    format!("{}({})", ctor.name, values.join(", "))
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
        self.total.extend([from.clone(), to.clone()]);
        self.forbidden.extend([from.clone(), to.clone()]);
        self.active_bridges.remove(head);
        Ok(Some((ty, format!("{from}($v)"), format!("{to}($v)"))))
    }
    pub(super) fn native_field(
        &mut self,
        ty: &SurfaceTerm,
        env: &BTreeMap<String, (String, String, String)>,
    ) -> Result<Option<(String, String, String)>, String> {
        if let TermKind::Var(n) = &*ty.kind {
            if let Some(repr) = env.get(n) {
                return Ok(Some(repr.clone()));
            }
            if self.std.of(n) == Some("Int") {
                return self.integer_bridge().map(Some);
            }
            if matches!(self.std.of(n), Some("Nat" | "Bool" | "I64" | "Text")) {
                return self.boundary(&crate::check::BoundaryType {
                    id: usize::MAX,
                    ty: ty.clone(),
                    arguments: Vec::new(),
                });
            }
            return self.native_family(n, Vec::new());
        }
        if let TermKind::App {
            function,
            arguments,
        } = &*ty.kind
        {
            if self.std.of(head_name(function)) == Some("Quot") {
                return match arguments.first() {
                    Some(value) => self.native_field(value, env),
                    None => Ok(None),
                };
            }
            let mut reprs = Vec::new();
            for argument in arguments {
                let Some(repr) = self.native_field(argument, env)? else {
                    return Ok(None);
                };
                reprs.push(repr);
            }
            return self.native_family(head_name(function), reprs);
        }
        Ok(None)
    }
    pub(super) fn integer_bridge(&mut self) -> Result<(String, String, String), String> {
        let info = self
            .checked
            .boundary_types
            .values()
            .flatten()
            .flatten()
            .find(|info| self.std.of(head_name(&info.ty)) == Some("Int"))
            .cloned()
            .ok_or("dependent extraction: missing checked Int boundary")?;
        self.boundary(&info)?
            .ok_or("dependent extraction: Int representation".into())
    }
    pub(super) fn boundary(
        &mut self,
        info: &crate::check::BoundaryType,
    ) -> Result<Option<(String, String, String)>, String> {
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
                Some("I64" | "i64") => {
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
        let head = head_name(t);
        if self.std.of(head) == Some("Quot") {
            return match info.arguments.first() {
                Some(value) => self.boundary(value),
                None => Ok(None),
            };
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
                .find(|c| self.std.of(c) == Some("IntOfNat"))
                .ok_or("dependent boundary: IntOfNat")?
                .clone();
            let negative = fam
                .ctors
                .iter()
                .find(|c| self.std.of(c) == Some("IntNegSucc"))
                .ok_or("dependent boundary: IntNegSucc")?
                .clone();
            let p = self.ctor(&positive)?;
            let n = self.ctor(&negative)?;
            let from = format!("TautoErasedPack{}#r0", info.id);
            let to = format!("TautoErasedUnpack{}#r0", info.id);
            if self.total.insert(from.clone()) {
                self.definitions.push(format!("fn {from}(value: {head}): {VALUE} {{ match value {{ {positive}(v) => {p}({NAT}(v))\n {negative}(v) => {n}({NAT}(v)) }} }}\nfn {to}(value: {VALUE}): {head} {{ match value {{ {p}(v) => {positive}(TautoErasedGetNat#r0(v))\n {n}(v) => {negative}(TautoErasedGetNat#r0(v))\n _ => extract_unreachable() }} }}\n"));
                self.total.insert(to.clone());
                self.forbidden.extend([from.clone(), to.clone()]);
            }
            return Ok(Some((
                head.to_string(),
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
            let (empty_pat, full_pat, tail, source) = if list {
                ("Nil", "Cons", ", tail", "List")
            } else {
                ("None", "Some", "", "Option")
            };
            let ty = format!("{source}({inner})");
            if self.total.insert(from.clone()) {
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
                self.total.insert(to.clone());
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
