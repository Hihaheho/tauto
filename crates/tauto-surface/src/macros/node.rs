//! A value of a macro's world as plain data: what a macro takes and returns,
//! apart from the evaluator that makes the real values. A syntax's typed
//! tree, a `SynExpr` and a `List(SynStmt)` are all [`Node`]s.

use tauto_parol::Span;

use crate::surface::{SurfaceTerm, TermKind};

/// The constructor's identity and the schema name used to display syntax values.
#[derive(Clone)]
pub struct ConstructorRef {
    reference: crate::identity::Name,
    schema: String,
}

impl ConstructorRef {
    pub fn resolved(reference: crate::identity::Name, schema: String) -> Self {
        Self { reference, schema }
    }
    pub fn reference(&self) -> &crate::identity::Name {
        &self.reference
    }
    pub fn as_str(&self) -> &str {
        &self.schema
    }
}
impl From<crate::identity::Name> for ConstructorRef {
    fn from(reference: crate::identity::Name) -> Self {
        let schema = reference.to_string();
        Self { reference, schema }
    }
}
impl From<&str> for ConstructorRef {
    fn from(schema: &str) -> Self {
        crate::identity::Name::from(schema).into()
    }
}
impl From<String> for ConstructorRef {
    fn from(schema: String) -> Self {
        crate::identity::Name::from(schema).into()
    }
}
impl std::ops::Deref for ConstructorRef {
    type Target = str;
    fn deref(&self) -> &str {
        &self.schema
    }
}
impl std::fmt::Debug for ConstructorRef {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.schema.fmt(f)
    }
}
impl std::fmt::Display for ConstructorRef {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(&self.schema)
    }
}
impl PartialEq for ConstructorRef {
    fn eq(&self, other: &Self) -> bool {
        self.reference == other.reference
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum Node {
    /// A declaration supplied by the expansion host, with no source constructor.
    Declaration(crate::identity::DeclRef),
    /// A constructor reference with labeled or positional fields. Host schema
    /// input may carry a source spelling; evaluator output carries the resolved
    /// reference so transporting a value cannot change its constructor.
    Ctor(ConstructorRef, Vec<(Option<String>, Node)>),
    Text(String),
    Int(i64),
    Bool(bool),
    List(Vec<Node>),
    Option(Option<Box<Node>>),
    /// A `Pair`'s value: `A × B × C` nests to the right, `Pair(a, Pair(b, c))`.
    Pair(Box<(Node, Node)>),
    /// A value filled in where a `quote` has `$`: the term that makes it.
    Splice(Box<SurfaceTerm>),
    /// In a list: a list of the same kind whose items go in here.
    SpliceList(Box<SurfaceTerm>),
}

impl Node {
    pub fn ctor(name: &str, fields: Vec<Node>) -> Node {
        Node::Ctor(name.into(), fields.into_iter().map(|f| (None, f)).collect())
    }

    pub fn text(t: &str) -> Node {
        Node::Text(t.to_string())
    }

    pub fn some(n: Node) -> Node {
        Node::Option(Some(Box::new(n)))
    }

    pub fn none() -> Node {
        Node::Option(None)
    }

    pub fn opt(n: Option<Node>) -> Node {
        Node::Option(n.map(Box::new))
    }

    /// The product of `members` in the order of the declared type, which `×` nests to
    /// the right.
    pub fn product(members: Vec<Node>) -> Node {
        let mut members = members;
        let mut tail = members.pop().expect("a product has members");
        while let Some(head) = members.pop() {
            tail = Node::Pair(Box::new((head, tail)));
        }
        tail
    }

    /// The two members of a `Pair`.
    pub fn pair(&self) -> Option<(&Node, &Node)> {
        match self {
            Node::Pair(p) => Some((&p.0, &p.1)),
            _ => None,
        }
    }

    /// The constructor's name without its type: `Num` of `math.Term.Num`.
    pub fn ctor_name(&self) -> Option<&str> {
        match self {
            Node::Ctor(n, _) => Some(n.rsplit("::").next().unwrap_or(n)),
            _ => None,
        }
    }

    pub fn field(&self, i: usize) -> Option<&Node> {
        match self {
            Node::Ctor(_, fs) => fs.get(i).map(|(_, f)| f),
            _ => None,
        }
    }

    pub fn named(&self, name: &str) -> Option<&Node> {
        match self {
            Node::Ctor(_, fs) => fs
                .iter()
                .find(|(n, _)| n.as_deref() == Some(name))
                .map(|(_, f)| f),
            _ => None,
        }
    }

    pub fn as_text(&self) -> Option<&str> {
        match self {
            Node::Text(t) => Some(t),
            _ => None,
        }
    }

    pub fn as_int(&self) -> Option<i64> {
        match self {
            Node::Int(n) => Some(*n),
            _ => None,
        }
    }

    pub fn as_bool(&self) -> Option<bool> {
        match self {
            Node::Bool(b) => Some(*b),
            _ => None,
        }
    }

    pub fn as_list(&self) -> Option<&[Node]> {
        match self {
            Node::List(v) => Some(v),
            _ => None,
        }
    }

    pub fn as_option(&self) -> Option<Option<&Node>> {
        match self {
            Node::Option(o) => Some(o.as_deref()),
            _ => None,
        }
    }

    /// The value on one line, for comparing it with `totes/macros`:
    /// `Name(a label=b)`, `[a b]`, `Some(a)`, `None`, `<a b>`, `t:HEX`.
    pub fn show(&self) -> String {
        match self {
            Node::Declaration(_) => "<declaration reference>".into(),
            Node::Ctor(name, fs) => {
                let fields: Vec<String> = fs
                    .iter()
                    .map(|(label, f)| match label {
                        Some(l) => format!("{l}={}", f.show()),
                        None => f.show(),
                    })
                    .collect();
                format!("{name}({})", fields.join(" "))
            }
            Node::Text(t) if t.is_empty() => "t:-".into(),
            Node::Text(t) => format!(
                "t:{}",
                t.bytes().map(|b| format!("{b:02x}")).collect::<String>()
            ),
            Node::Int(i) => format!("i:{i}"),
            Node::Bool(b) => b.to_string(),
            Node::List(v) => format!(
                "[{}]",
                v.iter().map(Node::show).collect::<Vec<_>>().join(" ")
            ),
            Node::Option(None) => "None".into(),
            Node::Option(Some(n)) => format!("Some({})", n.show()),
            Node::Pair(p) => format!("<{} {}>", p.0.show(), p.1.show()),
            Node::Splice(_) | Node::SpliceList(_) => "splice".into(),
        }
    }

    /// How many nodes it holds (the output's size, `macro.output_too_large`).
    pub fn size(&self) -> usize {
        1 + match self {
            Node::Ctor(_, fs) => fs.iter().map(|(_, f)| f.size()).sum(),
            Node::List(v) => v.iter().map(Node::size).sum(),
            Node::Option(Some(n)) => n.size(),
            Node::Pair(p) => p.0.size() + p.1.size(),
            _ => 0,
        }
    }

    /// The constructor calls that build this value, in the surface syntax,
    /// all at `span`: a literal's value where it is written.
    pub fn to_term(&self, span: Span) -> SurfaceTerm {
        let var = |n: &str| SurfaceTerm::var(n, span);
        let term = |k: TermKind| SurfaceTerm::new(k, span);
        let app = |f: &str, args: Vec<SurfaceTerm>| {
            term(TermKind::App {
                function: Box::new(var(f)),
                arguments: args,
            })
        };
        match self {
            Node::Declaration(reference) => term(TermKind::Declaration(reference.clone())),
            Node::Splice(t) | Node::SpliceList(t) => (**t).clone(),
            Node::Text(t) => term(TermKind::Text(t.clone())),
            Node::Int(n) => {
                if *n < 0 {
                    app("-", vec![term(TermKind::Nat(n.unsigned_abs().to_string()))])
                } else {
                    term(TermKind::Nat(n.to_string()))
                }
            }
            Node::Bool(b) => term(TermKind::Bool(*b)),
            Node::List(items) => {
                let mut acc = var("List::Nil");
                for item in items.iter().rev() {
                    acc = match item {
                        Node::SpliceList(t) => app("Syn::append", vec![(**t).clone(), acc]),
                        _ => app("List::Cons", vec![item.to_term(span), acc]),
                    };
                }
                acc
            }
            Node::Option(None) => var("Option::None"),
            Node::Option(Some(n)) => app("Option::Some", vec![n.to_term(span)]),
            // `#(a, b, …)`: the members of the `Pair`s nested to the right.
            Node::Pair(_) => {
                let mut members = Vec::new();
                let mut at = self;
                while let Node::Pair(p) = at {
                    members.push(p.0.to_term(span));
                    at = &p.1;
                }
                members.push(at.to_term(span));
                term(TermKind::Tuple(members))
            }
            Node::Ctor(name, fields) => {
                if fields.is_empty() {
                    SurfaceTerm::var(name.reference(), span)
                } else if fields.iter().all(|(n, _)| n.is_some()) {
                    term(TermKind::Record {
                        name: name.reference().clone(),
                        fields: fields
                            .iter()
                            .map(|(n, f)| (n.clone().unwrap_or_default(), f.to_term(span)))
                            .collect(),
                        base: None,
                    })
                } else {
                    term(TermKind::App {
                        function: Box::new(SurfaceTerm::var(name.reference(), span)),
                        arguments: fields.iter().map(|(_, f)| f.to_term(span)).collect(),
                    })
                }
            }
        }
    }
}

impl Node {
    /// Whether the atom `n` is in a `SynExpr` (an `ExAtom` or a `BAtom`).
    pub fn mentions_atom(&self, n: i64) -> bool {
        match self {
            Node::Ctor(name, fs) => {
                let last = name.rsplit("::").next().unwrap_or(name);
                ((last == "ExAtom" || last == "BAtom")
                    && fs.first().and_then(|(_, f)| f.as_int()) == Some(n))
                    || fs.iter().any(|(_, f)| f.mentions_atom(n))
            }
            Node::List(v) => v.iter().any(|x| x.mentions_atom(n)),
            Node::Option(Some(x)) => x.mentions_atom(n),
            Node::Pair(p) => p.0.mentions_atom(n) || p.1.mentions_atom(n),
            _ => false,
        }
    }

    /// The variable `name` of an expression as the atom `atom`, to open the
    /// binder of that name. `None` when the name is also written anywhere but as
    /// a variable (a binder inside may rebind it, and the walk does not guess).
    pub fn open_var(&self, name: &str, atom: i64) -> Option<Node> {
        match self {
            Node::Ctor(ctor, fs) => {
                let last = ctor.rsplit("::").next().unwrap_or(ctor);
                if last == "ExVar"
                    && let Some((_, Node::Ctor(_, id))) = fs.first()
                {
                    if id.iter().any(|(label, value)| {
                        label.as_deref() == Some("declaration")
                            && matches!(value.as_option(), Some(Some(_)))
                    }) {
                        return Some(self.clone());
                    }
                    let named = id
                        .iter()
                        .find(|(n, _)| n.as_deref() == Some("name"))
                        .and_then(|(_, f)| f.as_text());
                    if named == Some(name) {
                        let span = id
                            .iter()
                            .find(|(n, _)| n.as_deref() == Some("span"))?
                            .1
                            .clone();
                        return Some(Node::ctor("SynExpr::ExAtom", vec![Node::Int(atom), span]));
                    }
                    return Some(self.clone());
                }
                if ctor.as_str() == "SynIdent"
                    && fs
                        .iter()
                        .any(|(n, f)| n.as_deref() == Some("name") && f.as_text() == Some(name))
                {
                    return None;
                }
                let mut out = Vec::new();
                for (n, f) in fs {
                    out.push((n.clone(), f.open_var(name, atom)?));
                }
                Some(Node::Ctor(ctor.clone(), out))
            }
            Node::List(v) => Some(Node::List(
                v.iter()
                    .map(|x| x.open_var(name, atom))
                    .collect::<Option<_>>()?,
            )),
            Node::Option(Some(x)) => Some(Node::some(x.open_var(name, atom)?)),
            Node::Pair(p) => Some(Node::Pair(Box::new((
                p.0.open_var(name, atom)?,
                p.1.open_var(name, atom)?,
            )))),
            other => Some(other.clone()),
        }
    }
}

/// The key of a product's member: its label and type (`@name SynIdent`), or its type.
pub fn member_key(label: Option<&str>, ty: &str) -> String {
    match label {
        Some(l) => format!("@{l} {ty}"),
        None => ty.to_string(),
    }
}

pub fn label_of(key: &str) -> Option<&str> {
    key.strip_prefix('@')
        .map(|r| r.split(' ').next().unwrap_or(r))
}

#[cfg(test)]
mod declaration_tests {
    use super::*;

    #[test]
    fn a_schema_name_does_not_replace_the_constructor_reference() {
        let reference: crate::identity::Name =
            crate::identity::DeclRef::fresh("SynIdent::Mk").into();
        let shown = ConstructorRef::resolved(reference.clone(), "SynIdent".into());
        let node = Node::Ctor(shown, vec![]);
        assert_eq!(node.ctor_name(), Some("SynIdent"));
        assert_eq!(node.show(), "SynIdent()");
        assert_eq!(node, Node::Ctor(reference.clone().into(), vec![]));
        let term = node.to_term(Span::default());
        assert!(matches!(&*term.kind, TermKind::Var(name) if name == &reference));
    }

    #[test]
    fn constructor_syntax_retains_identity_for_every_field_shape() {
        use crate::identity::{DeclRef, Name};
        let reference = Name::Global(DeclRef::fresh("same"));
        let other = Name::Global(DeclRef::fresh("same"));
        for fields in [
            vec![],
            vec![(None, Node::Int(1))],
            vec![(Some("value".into()), Node::Int(1))],
        ] {
            let node = Node::Ctor(reference.clone().into(), fields.clone());
            assert_ne!(node, Node::Ctor(other.clone().into(), fields));
            let term = node.to_term(Span::new(0, 0));
            let actual = match &*term.kind {
                TermKind::Var(name) | TermKind::Record { name, .. } => name,
                TermKind::App { function, .. } => match &*function.kind {
                    TermKind::Var(name) => name,
                    _ => panic!("constructor application"),
                },
                _ => panic!("constructor syntax"),
            };
            assert_eq!(actual, &reference);
            assert_ne!(actual, &other);
        }
    }

    #[test]
    fn a_declaration_is_not_reconstructed_from_its_display() {
        let first = Node::Declaration(crate::identity::DeclRef::fresh("same"));
        let second = Node::Declaration(crate::identity::DeclRef::fresh("same"));
        assert_ne!(first, second);
        assert_eq!(first, first.clone());
        assert!(matches!(
            &*first.to_term(Span::new(0, 0)).kind,
            TermKind::Declaration(reference) if first == Node::Declaration(reference.clone())
        ));
    }
}
