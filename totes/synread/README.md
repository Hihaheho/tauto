# synread

Reads a syntax's tables (`.tauto-syntax/<sha256>.tables`) into the parser of `totes/synrun`,
and the values a literal parses to into the `Node` of `totes/macros`.

- `src/tables.taut`: `tb_read` reads the tables (`Tables::read`); `tb_parser_text` writes the parser's
  text (`Tables::runtime_text`) that `syn_read` reads; `tb_node_id` and `tb_nodes` number the schema's
  constructors and say what each is.
- `src/build.taut`: `tb_node` makes a `SynVal` a `Node` (`Builder::node` of the host's reader).
- `src/main.taut`: `synread TABLES_DIR FILE…`, the tote the differential test runs
  (`tools/selfhost-harness/tests/synread.rs`, cases marked `differential = "synread"`).

Holes (`${ e }`, `$name`, `$f(x)`, `$(e)`, …): `src/holes.taut` scans them as the host does, `syn_run_tokens` parses
the tokens, and `tb_embed` reads each hole's expression with the selfhost surface parser and lifts it with
`lf_expr` of `totes/macros`. A path after a hole's name is read as the host reads it, with the Unicode alphabetic and alphanumeric classes (`totes/unicode`).
Lifted expressions name their constructors `SynExpr.ExApp` where the host's value shows `SynExpr::ExApp`.
A span's id is the position in the file: the literal's start and the shifts of an indented block are given in the first line of the input.
