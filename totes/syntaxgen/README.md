# syntaxgen

The program `tauto syntax gen` runs (compiled into `tauto` when it is built, `crates/tauto-cli-totes`) to make the table file of a
grammar. It reads files and writes standard output; the work is done by the
libraries `totes/llkgen` (`llkgen_tables`) and, for a grammar with
`%grammar_type 'lalr(1)'`, `totes/lalrgen` (`lalrgen_tables`), which take the
grammar as a text.

`syntaxgen --gen FILE` reads a grammar from a file and writes its table file.
`tauto syntax gen` runs it as `syntaxgen --allow-read=FILE -- --gen FILE`:
the grammar is written to a temporary file of its own and read permission
covers that file alone. `syntaxgen` with no arguments reads the grammar on standard input
(it then needs `--allow-read`). An error in the grammar is written on
standard error and the program exits with 1.

For development there are the parts of a table file, each the function of
`totes/llkgen` of the same name: `--par FILE…` (`llkgen_model_lines`),
`--scan FILE…` (`llkgen_scan_lines`), `--rx FILE` (`llkgen_rx_trees`),
`syntaxgen TABLE…` (`llkgen_lookahead_lines`), and `--lr FILE`
(`lalrgen_lr_lines`). The tests in
`tools/selfhost-harness/tests/llkgen*.rs` run them.
