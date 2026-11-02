//! A value of a macro's world as plain data: what a macro takes and returns,
//! apart from the evaluator that makes the real values. A syntax's typed
//! tree, a `SynExpr` and a `List(SynStmt)` are all [`Node`]s.

use tauto_parol::Span;

use crate::surface::{SurfaceTerm, TermKind};

#[derive(Debug, Clone, PartialEq)]
pub enum Node {
    /// A struct's value or an enum's variant, by the name `make` takes
    /// (`SynIdent`, `math.Term.Num`), with the names of the fields written
    /// as such. A struct and a record variant name all their fields.
    Ctor(String, Vec<(Option<String>, Node)>),
    Text(String),
    Int(i64),
    Bool(bool),
    List(Vec<Node>),
    Option(Option<Box<Node>>),
    /// A product's value: each member under its key, the member's type as written
    /// with full names and its label (`@name SynIdent`), in the order written.
    Product(Vec<(String, Node)>),
    /// A value filled in where a `quote` has `$`: the term that makes it.
    Splice(Box<SurfaceTerm>),
    /// In a list: a list of the same kind whose items go in here.
    SpliceList(Box<SurfaceTerm>),
}

impl Node {
    pub fn ctor(name: &str, fields: Vec<Node>) -> Node {
        Node::Ctor(
            name.to_string(),
            fields.into_iter().map(|f| (None, f)).collect(),
        )
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

    /// The product of `members`, each `(label, type, value)`, in the order given: the order of
    /// the declared type. A member is also found by its label, or by its type when it has none.
    pub fn product(members: Vec<(Option<&str>, &str, Node)>) -> Node {
        let ms: Vec<(String, Node)> = members
            .into_iter()
            .map(|(l, t, n)| (member_key(l, t), n))
            .collect();
        Node::Product(ms)
    }

    /// The member of a product under `label` (`@label T`), or of type `ty` when
    /// `label` is `None`.
    pub fn member(&self, label: Option<&str>, ty: &str) -> Option<&Node> {
        let Node::Product(ms) = self else {
            return None;
        };
        let key = member_key(label, ty);
        ms.iter().find(|(k, _)| *k == key).map(|(_, n)| n)
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
            Node::Product(ms) => format!(
                "<{}>",
                ms.iter()
                    .map(|(_, n)| n.show())
                    .collect::<Vec<_>>()
                    .join(" ")
            ),
            Node::Splice(_) | Node::SpliceList(_) => "splice".into(),
        }
    }

    /// How many nodes it holds (the output's size, `macro.output_too_large`).
    pub fn size(&self) -> usize {
        1 + match self {
            Node::Ctor(_, fs) => fs.iter().map(|(_, f)| f.size()).sum(),
            Node::List(v) => v.iter().map(Node::size).sum(),
            Node::Option(Some(n)) => n.size(),
            Node::Product(ms) => ms.iter().map(|(_, n)| n.size()).sum(),
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
            // `#(@a x, …)`: the members in the order written, each under its label.
            Node::Product(ms) => {
                let mut members: Vec<SurfaceTerm> = ms
                    .iter()
                    .map(|(k, n)| match label_of(k) {
                        Some(tag) => term(TermKind::Tagged {
                            tag: tag.to_string(),
                            term: Box::new(n.to_term(span)),
                        }),
                        None => n.to_term(span),
                    })
                    .collect();
                match members.len() {
                    0 => var("Tuple"),
                    1 => members.pop().expect("one"),
                    _ => term(TermKind::Tuple(members)),
                }
            }
            Node::Ctor(name, fields) => {
                if fields.is_empty() {
                    var(name)
                } else if fields.iter().all(|(n, _)| n.is_some()) {
                    term(TermKind::Record {
                        name: name.clone(),
                        fields: fields
                            .iter()
                            .map(|(n, f)| (n.clone().unwrap_or_default(), f.to_term(span)))
                            .collect(),
                        base: None,
                    })
                } else {
                    app(name, fields.iter().map(|(_, f)| f.to_term(span)).collect())
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
            Node::Product(ms) => ms.iter().any(|(_, m)| m.mentions_atom(n)),
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
                if ctor == "SynIdent"
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
            Node::Product(ms) => Some(Node::Product(
                ms.iter()
                    .map(|(k, m)| Some((k.clone(), m.open_var(name, atom)?)))
                    .collect::<Option<Vec<_>>>()?,
            )),
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
