//! Declaration and lexical identities shared with the runtime.

use crate::surface::SurfaceTerm;
use std::hash::{Hash, Hasher};
pub use tauto_identity::*;

/// A source reference whose applied effects retain their bound arguments.
pub type Name = tauto_identity::ReferenceName<EffectUse>;

#[derive(Clone, Debug)]
pub struct EffectUse {
    identity: tauto_identity::EffectUse,
    arguments: Vec<SurfaceTerm>,
}

impl EffectUse {
    pub fn new(
        effect: DeclRef,
        arguments: Vec<SurfaceTerm>,
        parameters: Vec<LocalRef>,
        universal: bool,
        display: impl Into<String>,
    ) -> Self {
        let key = crate::bindings::argument_key(&arguments);
        Self {
            identity: tauto_identity::EffectUse::new(effect, key, parameters, universal, display),
            arguments,
        }
    }
    pub fn arguments(&self) -> &[SurfaceTerm] {
        &self.arguments
    }
}
impl std::ops::Deref for EffectUse {
    type Target = tauto_identity::EffectUse;
    fn deref(&self) -> &Self::Target {
        &self.identity
    }
}
impl EffectReference for EffectUse {
    fn display(&self) -> &str {
        self.identity.display()
    }
}
impl PartialEq for EffectUse {
    fn eq(&self, other: &Self) -> bool {
        self.identity == other.identity
    }
}
impl Eq for EffectUse {}
impl Hash for EffectUse {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.identity.hash(state)
    }
}
impl PartialOrd for EffectUse {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}
impl Ord for EffectUse {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.identity.cmp(&other.identity)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::surface::{SurfaceTerm, TermKind};
    use tauto_parol::Span;

    #[test]
    fn applied_effect_retains_argument_identity_despite_equal_display() {
        let effect = DeclRef::fresh("E");
        let a = Name::Global(DeclRef::fresh("T"));
        let b = Name::Global(DeclRef::fresh("T"));
        let application = |name: &Name, display: &str| {
            EffectUse::new(
                effect.clone(),
                vec![SurfaceTerm::var(name, Span::default())],
                vec![],
                false,
                display,
            )
        };
        let first = application(&a, "E(T)");
        let renamed = application(&a, "qualified::E(T)");
        let other = application(&b, "E(T)");
        assert_eq!(first, renamed);
        assert_ne!(first, other);
        assert!(matches!(&*first.arguments()[0].kind, TermKind::Var(n) if n == &a));
    }
}
