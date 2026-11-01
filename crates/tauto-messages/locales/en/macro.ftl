# Macro expansion (`tauto-macro`). The error code (`macro.unknown`) is
# written before the message, outside it.

macro-reserved = { $name } is the reader's own `{ $name }!`; a macro cannot take its name
macro-duplicate = macro { $name } is declared twice
macro-dollar-outside-quote = $ is written only inside quote
macro-kind-statements = this macro makes statements, and is called where a statement is written
macro-replace-word = `{ $word }` before `{ $kind } { $name }`: an attribute that changes its declaration writes `replace` first
macro-the-declaration = the declaration
macro-replace-other = `replace { $kind } { $name }` names a declaration the attribute is not written before; it is before { $decl }
macro-generates-attribute-kinds = an attribute macro makes only fn, theorem, def, inductive, struct and enum declarations
macro-replace-not-made = the attribute says `replace { $kind } { $name }`, and the macro did not make it
macro-replace-unsaid = the macro makes `{ $kind } { $name }`, the declaration it is given: an attribute that changes its declaration says so with `=> replace { $kind } { $name }`
macro-attribute-list-mismatch = the attribute's list does not match what the macro made
macro-call-list-mismatch = the list of what the call makes does not match what it made

# The function of a macro.
macro-function-undefined = `{ $function }`, the function of macro { $name }, is not defined before this file
macro-function-left-out = `{ $function }`, the function of macro { $name }, is not defined before this file: it does not check ({ $why })
macro-function-not-fn = `{ $function }` is not a function
macro-function-arity = the function of a macro takes the syntax's tree (and, for an attribute macro, the SynStmt it is written before), and `{ $function }` takes { $count }
macro-function-not-start = `{ $function }` takes { $ty }, which is not the tree of a syntax's start symbol
macro-function-not-tree = `{ $function }` takes { $ty }, which is not the tree of a syntax
macro-function-result = `{ $function }` makes { $ty }; a macro makes a SynExpr or a List(SynStmt)
macro-unchecked-effect = `{ $function }` performs an effect that cannot be followed ({ $effect })
macro-row-effect = the function of a macro may perform macro_error, macro_warn, elab and Div, and `{ $function }` performs { $effect }
macro-row-reached = `{ $function }` reaches { $path }, whose row does not check: { $why }
macro-builtin-reached = `{ $function }` reaches { $path }

# Why a function was left out of the library a macro runs in.
macro-left-out-inductive-ctor = { $why }; `{ $name }` is a constructor of an `inductive`, and a macro function is executable code, which uses the constructors of `enum`s (`List`'s `Nil`/`Cons`, `Option`'s `None`/`Some`), not those of an `inductive`
macro-left-out-means = `{ $short }` is `{ $name }`
macro-left-out-builtin = { $why }; in this file { $means }, not the builtin a macro function runs on; write { $builtins } for the builtin
macro-left-out-because = { $why }, because `{ $name }` does not check: { $reason }

# A call.
macro-include-text = `{ $name }!` is read where it is written in a file; a macro cannot make one, and a text read without a file cannot hold one
macro-unknown = there is no macro named `{ $name }`
macro-same-file = macro { $name } is declared in this file; a macro is used in a file after the one that declares it
macro-depth-exceeded = macros expand into macros more than { $depth } deep ({ $chain })
macro-library = the files before this one have errors, so macros do not run ({ $problem })
macro-kind-attribute = macro { $name } is an attribute macro: it is written as `@{ $name }!(…)` on the line before a declaration
macro-kind-not-attribute = macro { $name } is not an attribute macro, and is written with an attribute
macro-kind-attribute-stmts = macro { $name } is an attribute macro, and makes a List(SynStmt)
macro-argument-tactic = macro { $name } is a tactic: it is called as `by { $name }!(…): G {"{"} … {"}"}`
macro-argument-expr = macro { $name } takes an expression, not a syntax literal
macro-argument-literal = macro { $name } takes a syntax literal
macro-input-too-large = the text is more than { $bytes } bytes
macro-syntax-mismatch = macro { $name } reads { $syntax }, and the literal is { $literal }
macro-expand-exceeded = macro { $name } asked to expand more than { $count } expressions
macro-file-budget = the macros of this file took more than { $steps } steps
macro-output-too-large = macro { $name } made more than { $nodes } nodes
macro-proved-untyped = a Proved is for a typed macro in a proof
macro-forbidden-output = a macro may not make { $what }: write it by hand
macro-forbidden-axiom = an axiom
macro-forbidden-extern = an extern
macro-forbidden-import = an import
macro-forbidden-syntax = a syntax
macro-forbidden-macro = a macro
macro-syn-expand = Syn::expand: { $message }
macro-budget = macro { $name } took more than { $steps } steps
macro-memory = macro { $name } made more than { $values } values
macro-not-allowed = macro { $name } called { $builtin }, which a macro may not
macro-runtime = macro { $name }: { $message }

# Typed macros.
macro-nested-typed = a typed macro call is not written inside another's argument
macro-fragment = a typed macro runs on executable code or in a proof; an inductive family is not supported
macro-output-not-check = what the macro made does not check: { $message }
macro-signature-changed = the effects of `{ $name }` are not the same after the macro
macro-ownership-rejected = what the macro made breaks ownership: { $message }
macro-code-no-goal = the expression has no type to show the macro ({ $message })
macro-code-no-type = `{ $name }` has no type
macro-proof-rejected = the proof the macro made is rejected: { $message }
macro-proof-incomplete = the proof the macro made is not complete
macro-dependent-use = the output has the type the call had but is not definitionally equal to it, and a type below depends on that equality ({ $message })
macro-output-rejected = what the macro made is not accepted: { $message }
macro-output-rejected-plain = what the macro made is not accepted
macro-proved-shape = a Proved has a term and a proof
macro-proved-where = a Proved is for a function or a theorem
macro-proof-no-type = the expression has no type
macro-proof-type-unwritable = the type of the expression cannot be written for the kernel
macro-type-changed = the macro changed the type of the expression from { $before } to { $after }
macro-row-grew = the macro added the effect { $effect } to the expression

# `elab_*`.
macro-elab-more-arguments = { $op } takes more arguments
macro-elab-check-kernel = Elab::check is for the kernel's fragment
macro-elab-unknown-op = { $op } is not an operation of the checker

# Steps of a proof.
macro-step-mutual = a step is not written in a `mutual` block
macro-step-fragment = a step is written in a theorem, a `def` or a function of the kernel's language
macro-step-library = the files before this one have errors, so tactics do not run ({ $problem })
macro-step-context = the declaration does not check with the step left out: { $message }
macro-step-no-goal = the step's place has no goal
macro-step-before-mismatch = the goal written is not the goal here: here `{ $here }`, written `{ $written }` ({ $why })
macro-step-holes = the step has { $arms } arm(s), and the tactic left the holes [{ $holes }]; it leaves `?arm1` … `?arm{ $arms }`, each once
macro-step-output-rejected = what the tactic made is not accepted: { $message }
macro-step-hole-no-goal = the hole `?arm{ $k }` the tactic left has no goal
macro-step-arms =
    the tactic leaves { $count } goal(s); the step's arms are:
    { $arms }
macro-step-binders-mismatch = arm { $k }: the tactic adds [{ $added }], and the arm writes [{ $written }]
macro-step-binder-type = arm { $k }: `{ $name }` is a `{ $ty }`, and the arm writes `{ $written }` ({ $why })
macro-step-goal-mismatch = arm { $k }: the tactic leaves `{ $left }`, and the arm writes `{ $written }` ({ $why })
macro-step-not-checked = not checked
macro-step-not-tactic = macro { $name } is not a tactic: its function does not take a ProofStep and make a SynExpr
macro-step-write-before = write the goal the step starts from: `by t!(…): G {"{"} … {"}"}`
macro-step-arm-before = the arm's goal is the goal of the step that proves it; leave out `: …`
