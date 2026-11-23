//! `anf::normalize` leaves every operand of every function an atom or a
//! place, and binds each value once.

use tauto::nir::compile;
use tauto_nir::anf;

fn normalized(source: &str) -> tauto_nir::Package {
    tauto_messages::install();
    let mut pkg = compile(source).unwrap();
    anf::normalize(&mut pkg);
    for f in &pkg.fns {
        anf::check(&f.body).unwrap_or_else(|e| panic!("{}: {e}", f.source));
    }
    pkg
}

#[test]
fn a_long_list_is_one_flat_block() {
    std::thread::Builder::new()
        .stack_size(512 << 20)
        .spawn(long_list)
        .unwrap()
        .join()
        .unwrap();
}

fn long_list() {
    let items: Vec<String> = (0..300).map(|i| i.to_string()).collect();
    let pkg = normalized(&format!(
        "fn main(): List(u64) {{ [{}] }}\nshow(&main())",
        items.join(", ")
    ));
    let mut depth = 0;
    fn blocks(e: &tauto_nir::Expr, d: usize, max: &mut usize) {
        let d = d + matches!(e.kind, tauto_nir::ExprKind::Block(_)) as usize;
        *max = (*max).max(d);
        e.children(&mut |c| blocks(c, d, max));
    }
    for f in &pkg.fns {
        blocks(&f.body, 0, &mut depth);
    }
    assert!(depth < 10, "nested {depth} blocks deep");
}
