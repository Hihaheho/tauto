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
    type Written = WrittenEffect;
    fn display(&self) -> &str {
        self.identity.display()
    }
    fn written_display(written: &WrittenEffect) -> &str {
        &written.display
    }
}

/// An effect applied to arguments as the source writes it (`res(Pos)`,
/// `∀ A. res(A)`), before resolution binds it: the effect's name, the
/// argument terms and the row's parameters, each kept as what it is. The
/// passes before resolution edit the head and the arguments as names and
/// terms, and resolution binds them as such; nothing reads the entry back
/// from its display, which is only what it is shown as.
#[derive(Clone, Debug)]
pub struct WrittenEffect {
    head: String,
    arguments: Vec<SurfaceTerm>,
    parameters: Vec<String>,
    universal: bool,
    display: String,
}

impl WrittenEffect {
    /// `head(arguments…)`, under `∀ parameters.` when `universal`.
    pub fn new(
        head: impl Into<String>,
        arguments: Vec<SurfaceTerm>,
        parameters: Vec<String>,
        universal: bool,
    ) -> Self {
        let mut written = Self {
            head: head.into(),
            arguments,
            parameters,
            universal,
            display: String::new(),
        };
        written.display = written.render();
        written
    }
    pub fn head(&self) -> &str {
        &self.head
    }
    pub fn arguments(&self) -> &[SurfaceTerm] {
        &self.arguments
    }
    pub fn parameters(&self) -> &[String] {
        &self.parameters
    }
    pub fn is_universal(&self) -> bool {
        self.universal
    }
    pub fn display(&self) -> &str {
        &self.display
    }
    /// The entry with its head and its arguments edited.
    pub fn edited(
        &self,
        head: impl FnOnce(&mut String),
        mut argument: impl FnMut(&mut SurfaceTerm),
    ) -> Self {
        let mut out = self.clone();
        head(&mut out.head);
        out.arguments.iter_mut().for_each(&mut argument);
        out.display = out.render();
        out
    }
    fn render(&self) -> String {
        let entry = if self.arguments.is_empty() {
            self.head.clone()
        } else {
            format!(
                "{}({})",
                self.head,
                self.arguments
                    .iter()
                    .map(crate::surface::print::print_term)
                    .collect::<Vec<_>>()
                    .join(", ")
            )
        };
        if self.universal {
            format!("∀ {}. {entry}", self.parameters.join(", "))
        } else {
            entry
        }
    }
}
impl PartialEq for WrittenEffect {
    fn eq(&self, other: &Self) -> bool {
        self.display == other.display
    }
}
impl Eq for WrittenEffect {}
impl Hash for WrittenEffect {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.display.hash(state)
    }
}
impl PartialOrd for WrittenEffect {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}
impl Ord for WrittenEffect {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.display.cmp(&other.display)
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
    use crate::span::Span;
    use crate::surface::{SurfaceTerm, TermKind};

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
