# The messages of `tauto` itself, before a command runs.

no-command = no command { $name }: neither tauto nor this project has one (`tauto --help` lists both)
lang-unknown = unknown language { $lang } (known: { $known })

# The usage of the commands. The syntax itself is in `USAGE` in main.rs.
main-usage = usage:
main-usage-project-command = a command of the project or of a tote it depends on directly
main-usage-offline = never fetch; a locked dependency that is not in the cache is an error
main-usage-lang = the language of the messages (en, ja); else $TAUTO_LANG, `lang` in ~/.config/tauto/config.eure, $LANG

# `tauto try`, `fill`, `expand` and `suggest`.
main-accepted = accepted
main-rejected = rejected
main-suggest-axioms = axioms: { $axioms }
main-suggest-axioms-none = none
main-suggest-remaining-holes = remaining holes: { $holes }
main-suggest-file-status = file status: { $status }
main-expand-needs-by = expand needs --by

# `tauto fmt`.
main-fmt-not-formatted = { $path }: not formatted
main-fmt-fix-outside = { $file }: a fix is outside the file

# `tauto run`.
main-run-tote-no-main = the tote { $name } has no src/main.taut or src/main.tauto
main-run-interrupted = after { $steps } steps; `--steps N` raises it, `--allow-div` lifts it
main-eval-text = text
main-lint-unknown-option = lint: unknown option { $flag }
