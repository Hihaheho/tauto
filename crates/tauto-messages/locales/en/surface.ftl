# The messages of reading a program (tauto-surface): syntax declarations,
# modules, visibility, effect sets and quotes. `macro.…` codes stay as they are.

surface-tables-missing = the tables of this syntax are missing (grammar { $grammar }…); run `tauto syntax gen`
surface-tables-of-another-grammar = { $path } holds the tables of another grammar; run `tauto syntax gen`
surface-tables-out-of-date = { $path } was made by an older table generator; run `tauto syntax gen --force`
surface-grammar-not-par = the grammar of syntax { $name } is a block named par
surface-syntax-declared-twice = syntax { $name } is declared twice
surface-inductive-syntax-ctor-taken = `{ $ty }::{ $ctor }` is a constructor of `{ $ty }`, and `inductive_syntax!` makes `{ $ty }::I` and `{ $ty }::to_i`; name the rule of the grammar otherwise
surface-inductive-syntax-hole-place = in `{ $ty }`, a hole (`TautoExpr`) is not a whole alternative; in `inductive_syntax!` a hole stands for the non-terminal it is an alternative of
surface-syntax-start-tables = the tables of `{ $name }` for its start symbol `{ $start }` are made for another; run `tauto syntax gen --force`
surface-syntax-error = syntax { $name }: { $error }
surface-syntax-generates-mismatch = syntax { $name }: the list of what it makes does not match what it made
surface-made-not-listed = { $before }; made but not listed: { $items }
surface-listed-not-made = { $before }; listed but not made: { $items }
surface-syntax-with-role = syntax { $name }: `with` registers `fmt` and `tokens`, not `{ $role }`
surface-syntax-registered-twice = syntax { $name }: `{ $role }` is registered twice
surface-not-a-syntax = `{ $name }` is not a syntax
surface-literal-needs-name = a syntax literal needs the syntax's name, as in name`…`; write plaintext`…` for text
surface-effect-set-generic = the effect set { $name } has type parameters; a set of effects takes none yet
surface-effect-set-names-itself = the effect set { $name } names itself: { $path } -> { $name }
surface-module-collides-with-class = module { $module } collides with class { $name }
surface-module-declared-twice = module { $name } is declared twice
surface-dot-names-a-declaration = `.` takes a field; write the name of a declaration with `::`: `{ $name }`
surface-name-of-a-module = { $name } is the name of a module, so `{ $name }.f` would not tell a field from a qualified name; give the local another name
surface-name-shadowed = { $name } names more than one declaration here: { $names }; write the module path (`M::{ $name }`) of the one you mean
surface-name-shadows-outer = { $name } names both { $inner } and a declaration outside every module here; write `{ $inner }` for the module's own, or rename it to use the outer one
surface-name-outer-not-imported = { $name } is read as { $inner }, the module's own; a declaration of that name outside every module is in the program but this file does not import it. If you meant that one, import its file and rename the module's declaration; if you meant { $inner }, write `{ $inner }`
surface-block-indent = macro.block_indent: this line is indented { $lead }, the closing fence { $indent }
surface-extern-rust-path = write extern {"{"} … {"}"}; the rust path goes in Tauto.eure
surface-extern-mix-required-replaceable = an `extern` block cannot mix required host signatures with replaceable Tauto bodies or `struct`/`enum`
surface-ctor-type-name = constructor `{ $name }` has the name of a type; types and constructors share one namespace, so name it otherwise (as `Mk{ $name }`)
surface-extern-inductive-data = `{ $name }` cannot be `inductive` inside `extern`; write an ordinary `struct` or `enum`
surface-extern-open-replaceable = `{ $name }` cannot be `pub(open)` inside a replaceable `extern`: its representation stays inside the block
surface-extern-repr-sealed = `{ $name }` is a replaceable extern type: only functions in its `extern` block may construct it, project its fields, update it, or match on it
surface-extern-partial-bindings = replaceable extern block `{ $block }` has incomplete host bindings: bind every member or none
surface-extern-mixed-backends = replaceable extern block `{ $block }` cannot mix JavaScript bindings with Rust/Wasm bindings for the same representation
surface-class-method-body = a class method is a signature only; write the body on an `instance`, not on the `class`
surface-expected-one-expression = expected one expression
surface-pub-before-statement = { $what }: `pub` and `pub(open)` are written before `fn`, `theorem`, `axiom`, `def`, `inductive`, `struct`, `enum`, `effect` and `class`; `syntax`, `macro` and the other statements are seen from every file
surface-the-file = the file `{ $file }`
surface-the-prelude = the prelude
surface-names-and = { $before } and { $name }
surface-ambiguous = `{ $name }` is ambiguous: it is declared as { $names }; write the full name
surface-ambiguous-prelude = `{ $name }` is ambiguous: it is declared as { $names }; write the full name, or import the file that declares the one meant
surface-ambiguous-imported-prelude = `{ $name }` is ambiguous: it is declared as { $names }, and this file imports both; write the full name, or list after `import { $module }` only what this file uses from it, as in `import { $module } {"{"} … {"}"}`
surface-ambiguous-constructor = `{ $name }` is ambiguous: it is a constructor of more than one type ({ $names }), and the type wanted here does not say which; write it with its type, `T::{ $name }`
surface-ambiguous-language-type = `{ $name }` is ambiguous: it is declared as { $names }; write `std::prelude::{ $name }` for the type, or the other declaration with its type, as in `T::{ $name }`
surface-not-imported = `{ $name }` is declared by `{ $module }`, which this file does not import (what another file or a dependency imports does not reach this one); `import { $spelling }` in this file
surface-ctor-in-std = `{ $name }` is not defined; it is in the standard library: `import { $spelling }`
surface-ctor-not-imported = `{ $name }` is declared by `{ $module }`, which this file does not import (what another file or a dependency imports does not reach this one); `import { $spelling }` in this file
surface-private = `{ $name }` is private to { $file }; write `pub` before its declaration there to use it from another file
surface-private-std = `{ $name }` is not `pub` in the standard library, so only the library's own files use it
surface-sealed-constructor = `{ $name }` is a constructor of `{ $ty }`, which { $file } declares without `pub(open)`: outside that file the type is abstract; use the functions it makes public
surface-sealed-field = `{ $field }` is a field of `{ $ty }`, which { $file } declares without `pub(open)`: outside that file the type is abstract; use the functions it makes public
surface-sealed-perform = `{ $name }` is declared with `pub(handle)` and may only be performed in its declaring scope
surface-sealed-effect = `{ $name }` is an effect { $file } declares without `pub(open)`: only that file may handle it; perform it here, and leave its answer to the handler that file writes
surface-sealed-class = `{ $name }` is a class { $file } declares without `pub(open)`: only that file may write its instances; use the instances that file writes, or ask for `pub(open)` there
surface-private-class-bound = `{ $function }` is `pub`, but its `where` names `{ $name }`, a class this file declares without `pub`: no other file could meet it; write `pub` before the class, or leave the function private
surface-sealed-extern = `{ $name }` is an extern of the tote { $tote }, which only { $tote } may call; call a function { $tote } writes around it
surface-not-a-constructor-of = `{ $name }` is not a constructor of `{ $ty }`, the type of the matched value; it is declared as { $names }
surface-quote-spread-expr = `{ $name }` puts in the values of a list, and is written only where a list goes (the arguments of a call, the parameters of a λ, the arguments of a constructor's pattern, statements)
surface-quote-spread-pattern = `{ $name }` puts in the values of a list, and is written only where a list goes (the arguments of a constructor's pattern)
surface-quote-splice-outside = $ is written only inside quote
surface-quote-in-quote = a quote is not written inside a quote
surface-quote-syntax-literal = a syntax literal is not written inside a quote; call a macro
surface-quote-row = an effect row argument cannot be written in a quote
surface-quote-ascribe = an ascription cannot be written in a quote yet
surface-quote-other = { $what } cannot be written in a quote yet
surface-quote-field-assign = a macro cannot take an assignment to a field (`x.f := v`) yet
surface-quote-deref-assign = a macro cannot take a write through a borrow (`*x := v`) yet
surface-quote-statement = this statement cannot be written in a quote
surface-quote-pattern = pattern { $what } cannot be written in a quote
surface-scope-extrusion = macro.scope_extrusion: the atom { $atom } is used outside the binder it was opened by
surface-bare-kind = the kind `{ $kind }` is written `{ $written }`
surface-old-effect-operation = an effect operation is written `effect ask(question: Text): i64`, with its parameters in parentheses before the result
surface-row-variables = a row has at most one row variable
surface-row-repeats-effect = the effect `{ $name }` is written twice in one set literal
surface-row-variable-in-literal = `{ $name }` is a row variable, not an effect; write it outside the braces, as in `{"{"}trace{"}"} ∪ { $name }`
surface-raw-underscore = `r#_` is not a name: `_` is not written as a raw name
surface-underscore-not-name = `_` is not a name: write a name, and mark it unused with `^name` when it is intentionally unused
surface-unused-marker-wild = `^_` is not allowed: `_` is not a name; write `^name` with a real name
surface-unused-marker-pub = `^` is not written on a `pub` declaration: unused assertions are for bindings this file can verify
surface-unused-marker-not-binding = `^` is written only on a binding name, not on a constructor or a field label in a pattern (`Some(^x)`, `Point {"{"} x: ^y {"}"}`)
surface-unused-marker-record-type = `^` is written only on a field a struct declares, not on a member of a record type
surface-syntax-macro-shape = `{ $macro }` takes a name, a grammar block and, when it registers functions, `with(fmt: f, tokens: g)`
surface-import-not-listed = `{ $name }` comes through `import { $spelling }`, whose list does not write it; write `{ $item }` in its list (`tauto lint --fix` writes the list)
surface-import-listed-unused = `{ $name }` is in the list of `import { $spelling }`, but this file does not use it; take it out of the list (`tauto lint --fix` writes the list)
surface-import-listed-unknown = `{ $name }` is in the list of `import { $spelling }`, but the imported file declares no `{ $name }` for other files
surface-import-misplaced = `import` is written at the top of a file or at the head of the body of a `fn`, `macro fn`, `theorem` or `def` written there, before the body's other statements

surface-break-outside-loop = `break` is written only inside a `loop`, `while` or `for`
surface-continue-outside-loop = `continue` is written only inside a `loop`, `while` or `for`
surface-break-value = `break` takes no value: a loop is `()`; keep the result in a `var` before it
surface-return-in-for = `return` is not written inside a `for`: leave the loop with `break`, or write the rest of the function after it
surface-pair-written = `Pair` is not written by its name: a product is written `A × B` and `#(a, b)`, and taken apart by `#(…)`, by the type of a member or by `.fst` and `.snd`
surface-coerce-twice = a struct has at most one `coerce` field
surface-coerce-not-in-struct = `coerce` is written before a field of a `struct`, not of an `enum`'s constructor or a record type
surface-coerce-level = `coerce({ $word })` is not a level: write `coerce`, `coerce(mut)` or `coerce(owned)`
surface-row-hole-place = `!?` (a row not written yet) is written only after the result of a `fn` with a body, not in a type, an `effect`, an `extern` or a class
surface-unused-effect-marker-place = `^` marks an unused effect only in a function's written row, not in a function type, a row argument or an effect set

surface-single-superclass = a class may declare only one parent class
surface-superclass-argument = the parent class must take the child's single type parameter
surface-unknown-superclass = unknown parent class `{ $name }`
surface-superclass-kind = parent class `{ $name }` must have the same parameter kind and class form
surface-superclass-cycle = the parent classes of `{ $name }` form a cycle

surface-module-duplicate = module `{ $name }` is already declared

surface-module-unknown = no local module named `{ $name }`

surface-module-export = `{ $name }` is not a public member of its module

surface-module-member-private = `{ $name }` is private to its module

surface-module-sealed-handle = `{ $name }` may only be handled in its declaring module

surface-module-export-duplicate = `{ $name }` is re-exported more than once
