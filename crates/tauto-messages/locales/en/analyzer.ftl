# The messages of the analyzer (`tauto-analyzer`): why a hole cannot be
# expanded and why a name cannot be renamed. Names, terms and paths are
# variables, written as they are.

analyzer-not-an-expansion = `{ $text }` is not a way to expand a hole: use `intro`, `match(x)`, `induction(x)` or a tactic `name!(arg)`
analyzer-intro-not-function = the goal `{ $goal }` is not a function type: nothing to introduce
analyzer-match-not-in-scope = `{ $var }` is not a variable in scope at `?{ $hole }`
analyzer-match-not-inductive-var = `{ $var }` : `{ $ty }` is not of an inductive type
analyzer-match-not-inductive = `{ $family }` is not an inductive type
analyzer-tactic-needs-step = `{ $name }!(…)` is a tactic: what its step's arms are is known once the file is checked with it (expand_step)
analyzer-step-arm-reads = arm { $k } of the step reads `{ $line }`
analyzer-file-not-read = the file is not among the files read
analyzer-candidate-not-in-scope = candidate `{ $name }` is not in the loaded scope
analyzer-query-waits-not-file = a query is waiting for something that is not a file
analyzer-fill-no-longer-reads = the file no longer reads with `{ $expr }` for `?{ $name }`: { $error }
analyzer-not-loaded = the program is not loaded
analyzer-no-such-statement = no such statement
analyzer-pinned-field = a field is found by the type of what it is read from
analyzer-pinned-syntax = the names a syntax makes (`name_Rule`) are derived from it
analyzer-pinned-field-pun = the name is also the field's, written once
analyzer-rename-no-name = no name here that this can find the declaration of
analyzer-rename-prelude = `{ $name }` is the prelude's
analyzer-rename-pinned = `{ $name }` is not renamed: { $why }
analyzer-rename-no-name-here = no name here
analyzer-rename-file-without-path = a file without a path
analyzer-rename-broken-file = { $path } does not read as a whole; fix its syntax errors first
analyzer-rename-opaque = `{ $old }` is also written inside a syntax literal or a `quote` in { $path }, where uses are not found
analyzer-rename-unresolved = `{ $old }` is written at { $path }:{ $line } where it does not resolve to a declaration, so it could be a use of this one
analyzer-rename-approximate = `{ $old }` is used in { $path } where only its name says which declaration it is
analyzer-rename-tote-mate = `{ $old }` also appears in { $path }, which is in a tote that sees { $file } without importing it
analyzer-rename-text-changed = the text changed under the rename
analyzer-rename-no-path = no path
analyzer-rename-edited-not-load = the edited file does not load
analyzer-rename-an-edited-not-load = an edited file does not load
analyzer-rename-leaves-syntax-error = the rename would leave { $path } with a syntax error
analyzer-rename-captures = `{ $new_name }` would change what some name in { $path } refers to (it is already in scope there)
analyzer-rename-not-a-name = `{ $name }` is not a name
analyzer-rename-keyword = `{ $name }` is a keyword
analyzer-tokens-unused = the colours of `{ $syntax }` are not those of `{ $function }`, which could not be used: { $why }
analyzer-tokens-outside = it made a range outside the text
