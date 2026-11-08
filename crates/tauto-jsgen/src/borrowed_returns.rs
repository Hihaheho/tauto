//! Borrow-free return values need no traversal to retain escaping host views.
//! Unknown types keep the runtime traversal. Generic data parameters are known
//! borrow-free only after checking every argument at their use site.
use std::collections::BTreeSet;
use tauto_nir::{Package, Ty};

pub(crate) fn needs_export(pkg: &Package, ty: &Ty) -> bool {
    visit(pkg, ty, &BTreeSet::new(), &mut BTreeSet::new(), 128)
}

fn visit(
    pkg: &Package,
    ty: &Ty,
    safe_params: &BTreeSet<String>,
    active: &mut BTreeSet<String>,
    fuel: usize,
) -> bool {
    if fuel == 0 {
        return true;
    }
    match ty {
        Ty::Int(_)
        | Ty::Bool
        | Ty::Text
        | Ty::Unit
        | Ty::Never
        | Ty::Float
        | Ty::Float32
        | Ty::Buf
        | Ty::Shown => false,
        Ty::Ref(_) | Ty::RefMut(_) | Ty::Slice(_) | Ty::Infer | Ty::Std(_, _) | Ty::Fn(_) => true,
        Ty::Param(name) => !safe_params.contains(name),
        Ty::Vec(t)
        | Ty::Array(t)
        | Ty::Option(t)
        | Ty::SharedVar(true, t)
        | Ty::SharedVar(false, t)
        | Ty::Info(t)
        | Ty::BudgetAnswer(t) => visit(pkg, t, safe_params, active, fuel - 1),
        Ty::HashMap(a, b) | Ty::Result(a, b) | Ty::Pair(a, b) => {
            visit(pkg, a, safe_params, active, fuel - 1)
                || visit(pkg, b, safe_params, active, fuel - 1)
        }
        Ty::Data(name, args) => {
            if args
                .iter()
                .any(|arg| visit(pkg, arg, safe_params, active, fuel - 1))
            {
                return true;
            }
            let Some(data) = pkg.datas.iter().find(|data| data.name == *name) else {
                return true;
            };
            if data.view || data.ctors.is_empty() || data.generics.len() != args.len() {
                return true;
            }
            let key = format!("data:{name}");
            if !active.insert(key.clone()) {
                return false;
            }
            // A type already visited in this walk is not visited again: had it
            // needed an export, the walk would have ended there. Keeping it
            // marked makes the walk linear in the types instead of the paths.
            let params = data.generics.iter().cloned().collect();
            data.ctors
                .iter()
                .flat_map(|ctor| &ctor.fields)
                .any(|field| visit(pkg, &field.ty, &params, active, fuel - 1))
        }
        Ty::Union(id) => {
            let Some(union) = pkg.unions.iter().find(|union| union.id == *id) else {
                return true;
            };
            let key = format!("union:{id}");
            if !active.insert(key.clone()) {
                return false;
            }
            let result = union
                .members
                .iter()
                .any(|member| visit(pkg, member, safe_params, active, fuel - 1));
            active.remove(&key);
            result
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use tauto_nir::{CtorDef, DataDef, FieldDef, Indirect, Kind, UnionDef};

    fn recursive() -> Package {
        Package {
            datas: vec![DataDef {
                name: "List".into(),
                generics: vec!["A".into()],
                kind: Kind::Shared,
                is_struct: false,
                clone: true,
                copy: false,
                linear: false,
                view: false,
                host: false,
                ctors: vec![CtorDef {
                    name: "Cons".into(),
                    fields: vec![
                        FieldDef {
                            name: None,
                            ty: Ty::Param("A".into()),
                            indirect: Indirect::None,
                        },
                        FieldDef {
                            name: None,
                            ty: list(Ty::Param("A".into())),
                            indirect: Indirect::Shared,
                        },
                    ],
                }],
            }],
            ..Package::default()
        }
    }
    fn list(ty: Ty) -> Ty {
        Ty::Data("List".into(), vec![ty])
    }

    #[test]
    fn recursive_data_are_traversed_only_when_they_can_contain_borrows() {
        let pkg = recursive();
        assert!(!needs_export(&pkg, &list(Ty::Text)));
        assert!(!needs_export(&pkg, &list(list(Ty::Bool))));
        assert!(needs_export(&pkg, &list(Ty::Ref(Box::new(Ty::Text)))));
        assert!(needs_export(&pkg, &list(Ty::Param("T".into()))));
        assert!(needs_export(&pkg, &Ty::Data("List".into(), vec![])));
        assert!(needs_export(&pkg, &Ty::Data("Unknown".into(), vec![])));
    }

    #[test]
    fn views_unknown_parameters_and_hidden_borrows_stay_conservative() {
        let mut pkg = recursive();
        pkg.datas[0].view = true;
        assert!(needs_export(&pkg, &list(Ty::Text)));
        pkg.datas[0].view = false;
        pkg.datas[0].ctors[0].fields.push(FieldDef {
            name: None,
            ty: Ty::Option(Box::new(Ty::RefMut(Box::new(Ty::Text)))),
            indirect: Indirect::None,
        });
        assert!(needs_export(&pkg, &list(Ty::Text)));
        pkg.datas[0].ctors[0].fields.last_mut().unwrap().ty = Ty::Param("undeclared".into());
        assert!(needs_export(&pkg, &list(Ty::Text)));
        assert!(needs_export(&pkg, &Ty::Infer));
        pkg.datas[0].ctors.clear();
        assert!(needs_export(&pkg, &list(Ty::Text)));
    }

    #[test]
    fn union_members_and_generic_argument_changes_are_checked() {
        let mut pkg = recursive();
        pkg.unions.push(UnionDef {
            id: 0,
            kind: Kind::Shared,
            members: vec![Ty::Text, list(Ty::Text)],
        });
        assert!(!needs_export(&pkg, &Ty::Union(0)));
        pkg.unions[0].members.push(Ty::Ref(Box::new(Ty::Text)));
        assert!(needs_export(&pkg, &Ty::Union(0)));
        pkg.datas[0].ctors[0].fields[1].ty = list(Ty::Ref(Box::new(Ty::Text)));
        assert!(needs_export(&pkg, &list(Ty::Text)));
    }
}
