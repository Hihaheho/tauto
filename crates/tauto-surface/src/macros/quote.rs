//! `quote { … }` and `quote stmts { … }`
//! as the constructor calls that build the syntax they hold, with the
//! values after `$` put in. The checkers see only those calls.

use tauto_parol::Span;

use super::node::Node;
use super::syn::Lift;
use crate::surface::{Stmt, SurfaceTerm};

pub fn desugar(stmts: bool, body: &[Stmt], span: Span) -> Result<SurfaceTerm, String> {
    let lift = Lift {
        scopes: &[],
        quote: true,
        atoms: None,
        spans: None,
        reflip: None,
    };
    let node = if stmts {
        Node::List(lift.stmt_list(body)?)
    } else if let [Stmt::Expr(only)] = body {
        lift.expr(only)?
    } else {
        Node::ctor(
            "SynExpr::ExBlock",
            vec![
                lift.stmts(body)?,
                Node::Ctor(
                    "SynSpan".into(),
                    vec![(Some("id".into()), Node::Int(i64::from(span.start)))],
                ),
            ],
        )
    };
    Ok(node.to_term(span))
}
