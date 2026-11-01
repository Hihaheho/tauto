# The messages of `tauto audit` (its text output; `--json` is not translated).

audit-usage = audit takes only --json
audit-none = none
# Each line of a tote starts with two spaces: FTL drops leading spaces, so
# they are written as a string literal.
audit-externs = {"  "}externs:    { $list }
audit-axioms = {"  "}axioms:     { $list }
audit-effects = {"  "}effects:    { $list }
audit-rust = {"  "}rust:       bridge { $bridge }; crates: { $crates }
audit-javascript = {"  "}javascript: { $list }
audit-granted-nothing = granted nothing
audit-granted = granted { $kinds }
audit-command = {"  "}command:    { $name } ({ $main }; { $granted }) { $about }
audit-not-read = {"  "}not read:   { $list }
