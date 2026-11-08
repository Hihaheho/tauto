//! Reference slots in compiler-generated syntax. Slots retain already-bound
//! declarations and locals; decoding never consults source visibility or names.
use super::*;
use std::cell::RefCell;

#[derive(Default)]
pub(super) struct References(RefCell<(HashMap<Name, String>, HashMap<String, Name>)>);
impl References {
    pub(super) fn symbol(&self, name: &Name) -> String {
        if let Name::Spelled(generated) = name {
            return raw(generated);
        }
        let mut tables = self.0.borrow_mut();
        if let Some(token) = tables.0.get(name) {
            return token.clone();
        }
        let token = format!("TautoReferenceSlot{}", tables.0.len());
        tables.0.insert(name.clone(), token.clone());
        tables.1.insert(token.clone(), name.clone());
        token
    }
    pub(super) fn decode(&self, name: &mut Name) {
        if let Name::Spelled(token) = name {
            if let Some(reference) = self.0.borrow().1.get(token) {
                *name = reference.clone();
            }
        }
    }
    pub(super) fn term(&self, term: &mut SurfaceTerm) {
        crate::surface::references::term(term, &mut |name| self.decode(name));
    }
    pub(super) fn statements(
        &self,
        text: &str,
    ) -> Result<(Vec<Stmt>, HashMap<String, Name>), Message> {
        let (text, renamed) = legal_names(text);
        let mut program = crate::surface::parse_program_unresolved_at(&text, 0)?;
        if let Some((error, _)) = program.errors.first() {
            return Err(error.clone());
        }
        for statement in &mut program.stmts {
            crate::surface::references::statement(statement, &mut |name| self.decode(name));
        }
        let generated = renamed
            .into_iter()
            .map(|(from, to)| (from, Name::from(to)))
            .collect();
        Ok((program.stmts, generated))
    }
}
impl Eraser<'_> {
    pub(super) fn symbol(&self, name: &Name) -> String {
        self.references.symbol(name)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use tauto_surface::identity::{DeclRef, LocalRef};
    #[test]
    fn slots_keep_equal_display_references_distinct() {
        let references = References::default();
        let names: Vec<Name> = vec![
            DeclRef::fresh("same").into(),
            DeclRef::fresh("same").into(),
            LocalRef::fresh("same").into(),
        ];
        let slots: Vec<_> = names.iter().map(|name| references.symbol(name)).collect();
        assert_eq!(slots.iter().collect::<HashSet<_>>().len(), 3);
        for (slot, expected) in slots.iter().zip(&names) {
            let mut reference = Name::from(slot.clone());
            references.decode(&mut reference);
            assert_eq!(&reference, expected);
        }
    }
}
