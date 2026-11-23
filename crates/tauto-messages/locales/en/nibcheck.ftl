nibcheck-not-a-constructor = { $name } is not a constructor
nibcheck-ambiguous-constructor = ambiguous constructor `{ $name }`: use a type annotation or { $candidates }
nibcheck-no-field = { $name } has no field `{ $field }`
nibcheck-effect-takes-no-type-arguments = `{ $effect }` takes no type arguments
nibcheck-effect-no-type-argument-named = `{ $effect }` has no type argument named `{ $name }`
nibcheck-call-no-type-argument-named = the function has no type argument named `{ $name }`
nibcheck-arm-write-instance = write the instance the arm of `{ $effect }` answers: `{ $effect }<…>(…)`, or { $every } for every one
nibcheck-effect-type-argument-count = `{ $effect }` takes { $expected } type arguments, given { $given }
nibcheck-arm-binds-each-type-argument = an arm for every instance binds each type argument in order: { $every }
nibcheck-typefn-not-transparent = { $name }: native type functions must be transparent and effect-free, with only Type parameters
nibcheck-typefn-duplicate = duplicate native type function declaration `{ $name }`
nibcheck-typefn-body-statements = { $name }: native type function body must be a type expression; statements and general computation require checked type-level evaluation
nibcheck-typefn-body-computation = native type function body must be a type expression; general computation requires checked type-level evaluation
nibcheck-typefn-expansion-limit = native type function expansion limit exceeded
nibcheck-typefn-not-fully-applied = { $name } is not a fully applied native type in a type function
nibcheck-typefn-needs-named-constructor = native type functions require a named type constructor
nibcheck-typefn-not-constructor-with-arguments = { $name } is not a native type constructor with { $count } arguments
nibcheck-typefn-undeclared-effect = effect `{ $effect }` in a native type function is not a declared monomorphic effect
nibcheck-typefn-argument-count = { $name } expects { $expected } explicit type arguments, found { $found }
nibcheck-typefn-recursive = recursive native type function { $name } requires checked type-level evaluation
nibcheck-typefn-used-as-value = { $name } returns a type and cannot be used as an executable value
nibcheck-pattern-field-missing = field `{ $field }` is missing from the pattern

# What the checker of executable code expected a type of.

nibcheck-what-record-constructor = a record constructor
nibcheck-what-constructor = a constructor
nibcheck-what-result-of = the result of `{ $name }`
nibcheck-what-named = `{ $name }`
nibcheck-what-field = field `{ $field }`
nibcheck-what-while-condition = a `while` condition
nibcheck-what-if-condition = an `if` condition
nibcheck-what-returned-value = the returned value
nibcheck-what-argument = an argument
nibcheck-what-product-member = a member of a product
nibcheck-what-ascription = a type ascription
nibcheck-what-arm-goal = the goal of an arm
nibcheck-what-arm-body = the body of an arm
nibcheck-what-match-result = the result of the `match`
nibcheck-what-budget-steps = a budget's steps
nibcheck-what-budget-memory = a budget's memory
nibcheck-what-function-result = the result of a function
nibcheck-what-guard = a guard
nibcheck-what-handler-arm = a handler arm

# A type that does not fit the one expected.

nibcheck-mismatch = { $what }: { $found } does not fit { $expected }
nibcheck-mismatch-lend = { $what }: { $found } does not fit { $expected }: lend it with `&`
nibcheck-mismatch-number = { $what }: expected { $expected }, found { $found }, a different type; for a number the proofs see too, write `{ $checked }` of `std::{ $module }`
nibcheck-mismatch-closure-kind = { $what }: { $found ->
    [affine] an affine
    *[other] a { $found }
  } closure where { $expected } is expected
nibcheck-mismatch-open-product = { $what }: { $found } and { $expected } are matched by the types of their members only where neither mentions a type parameter or an unknown type; write the members in the same order, or tell them apart with tags
nibcheck-mismatch-product-clash = { $what }: two members of a product have the type { $member }, so the members cannot be matched by their types; write the members by position, or tell them apart with tags
nibcheck-forgets-linear-member = { $what }: this forgets the linear member { $member }
nibcheck-not-an-application = { $ty } is not an application of a type constructor
nibcheck-literal-does-not-fit = { $literal } does not fit { $ty }
nibcheck-kind-does-not-fit-bound = { $kind } does not fit { $bound }: { $ty } for a type parameter

# A struct, or a record type, used where a value is written.

nibcheck-record-type-not-a-value = a record type `{"{"} … {"}"}` is not a value: write a record without a name as `#{"{"} … {"}"}`
nibcheck-struct-as-value = `{ $name }` is a struct: write `{ $name } {"{"} field: value {"}"}`

# Names and fields of the checker of executable code.

nibcheck-not-defined = { $name } is not defined
nibcheck-not-a-var = `{ $name }` is not a var
nibcheck-type-declared-twice = type { $name } is declared twice
nibcheck-function-declared-twice = function { $name } is declared twice
nibcheck-not-a-function = { $found } is not a function
nibcheck-no-method = { $owner } has no method { $name }
nibcheck-not-a-struct = { $name } is not a struct
nibcheck-field-given-twice = field `{ $field }` is given twice
nibcheck-field-missing = field `{ $field }` of { $name } is missing
nibcheck-nat-too-large = { $value } is too large
nibcheck-not-a-nat = { $value } is not a Nat
nibcheck-not-an-int = { $value } is not an Int
nibcheck-float-too-large = { $value } is too large for a Float
nibcheck-not-a-var-for-lend = { $what } is not a var: only a var lends `&mut`

# Declarations and types of the checker of executable code.

nibcheck-quote-splice-type = a `$` in an expression of a `quote` takes a SynExpr, a SynIdent or a Judgement, not { $found }
nibcheck-int-literal-no-type = an integer literal has no integer type
nibcheck-closure-returns-borrow = a closure cannot return a borrow
nibcheck-view-type-argument = a type that holds a borrow cannot be a type argument here
nibcheck-generic-effect-argument = a value of { $name }, which may hold a borrow, cannot be an effect argument: write `<{ $name }: NoBorrow>`
nibcheck-rc-linear = `&rc { $ty }` cannot be written: a linear value is used exactly once, and the copies of a `&rc` share it
nibcheck-rc-borrow = `&rc { $ty }` cannot be written: { $ty } holds a borrow, which a box that is kept and returned would outlive
nibcheck-rc-generic-borrow = `&rc { $name }`: { $name } may hold a borrow, which a box that is kept and returned would outlive: write `<{ $name }: Type + NoBorrow>`
nibcheck-rc-mut = { $ty } is shared by its copies: its contents are only borrowed with `&`, never with `&mut`
nibcheck-rc-not-owned = { $what }: { $found } does not fit { $expected }: the copies of a `&rc` share its contents, which are borrowed with `&` and never taken
nibcheck-constructor-kind-mismatch = { $what } takes constructors from { $arg } to { $result }, and { $shown } is { $kind }
nibcheck-type-not-determined = the type { $generics } of `{ $name }` is not determined here: give the value a type, as in `let x: T = ...`
nibcheck-takes-arguments = { $name } takes { $count } arguments
nibcheck-type-constructor-variable-one-argument = { $name } is a type constructor variable and takes one argument
nibcheck-slice-only-borrowed = Slice(A) can only be borrowed
nibcheck-takes-effect-row = { $name } takes an effect row here, as in `{ $name }(!{"{"}a{"}"} ∪ e)`
nibcheck-effect-row-only-to-row-parameter = an effect row is given only to a row parameter, and this one of { $name } is not
nibcheck-not-a-type = not a type
nibcheck-kind-of-function-type = `{ $kind }` is the kind of a function type
nibcheck-not-a-type-of-program = not a type of a program
nibcheck-parameter-has-no-type = a parameter of `{ $name }` has no type
nibcheck-resume-quantity = `resume { $quantity }`: write 0, <=1, 1 or ω
nibcheck-borrow-only-extern-type = only an extern `type` is declared to hold a borrow; a type with fields holds one when a field does
nibcheck-borrow-field = a borrow cannot be a field
nibcheck-declared-shared-holds-itself = declared { $declared } but `{ $name }` holds itself, so it is shared
nibcheck-declared-but-field = declared { $declared } but field { $field } is { $kind }
nibcheck-term-generic-needs-extraction = term generic `{ $name }` requires checked extraction before native compilation
nibcheck-return-needs-mut-parameter = -> { $ty } needs a &mut parameter
nibcheck-return-needs-borrowed-parameter = -> { $ty } needs a borrowed parameter
nibcheck-value-indexed-constraints = value-indexed constraints require checked dictionary extraction
nibcheck-not-a-class = { $name } is not a class
nibcheck-where-only-generics-of-function = where constrains only generics of { $name }
nibcheck-predicate-written-twice = { $class }({ $argument }) is written twice
nibcheck-row-variable-not-declared-type = the row variable `{ $variable }` is not declared; write `{ $name }(!{ $variable })`

# Statements, expressions, patterns and arms of the checker of executable code.

nibcheck-let-mut-borrow-binds-return = `let &mut { $name }` binds what a function returns as `-> &mut A`
nibcheck-let-borrow-binds-return = `let &{ $name }` binds what a function returns as `-> &A`
nibcheck-borrow-cannot-be-stored = a borrow cannot be stored: `{ $name }` would hold { $ty }
nibcheck-var-borrow-binds-view = `{ $name }` is bound as a borrow, but its value holds no borrow
nibcheck-var-cannot-store-borrow = a borrow cannot be stored in `var { $name }`
nibcheck-var-holds-linear = a var cannot hold a linear value: `{ $name }` is { $ty }
nibcheck-view-var-field-assigned = a field of a var that holds a borrow cannot be assigned
nibcheck-assigns-field-of-var = { $target } assigns a field of a `var` or a `&mut` parameter
nibcheck-assign-through-borrow = write `*{ $place } := …` to write through the borrow
nibcheck-deref-needs-mut-borrow = `*{ $place } := …` writes through a `&mut` borrow, and `{ $place }` is not one
nibcheck-deref-outside-assign = a borrow reads as its value; `*` is written only on the left of `:=`
nibcheck-return-outside-function = `return` outside a function
nibcheck-declare-type-at-top-level = declare a type at the top level
nibcheck-declare-extern-at-top-level = declare an `extern` block at the top level
nibcheck-declare-syntax-at-top-level = a syntax or a macro is declared at the top level
nibcheck-not-supported-yet = not supported yet: { $what }
nibcheck-constructor-without-fields = `{ $name }` is a constructor without fields: write `{ $name }`, without `()`
nibcheck-function-argument-count = a function of { $expected } values is given { $given }
nibcheck-cannot-infer-function-type = cannot infer a function type for this call
nibcheck-product-type-as-value = `×` builds a type, not a value: write the product as `#(…)`
nibcheck-no-effect-declared = no effect `{ $effect }` is declared
nibcheck-host-answers = `{ $effect }` is answered by the host that runs the program: no `handle` has an arm for it
nibcheck-effect-value-count = `{ $effect }` takes { $expected } values, given { $given }
nibcheck-budget-arms-differ = budgets answered by one `exceeded` arm give different types
nibcheck-clone-takes-one-borrow = `clone` takes one borrow, `clone(&x)`
nibcheck-clone-takes-borrow = `clone` takes a borrow: write `clone(&x)`
nibcheck-division-operands-unknown = the operands of `/` have no known type: write it
nibcheck-integer-division = integer `/` is a type error: write div(a, b), mod(a, b), or decimal(a) / decimal(b)
nibcheck-operator-other-operands = `{ $op }` takes other operands
nibcheck-operator-not-a-number = `{ $op }` of { $ty }: not a number
nibcheck-label-not-on = the label `@{ $tag }` is not on { $ty }
nibcheck-unit-pattern-mismatch = `#()` does not match { $ty }
nibcheck-pattern-not-supported = this pattern is not supported yet: { $what }
nibcheck-pattern-cannot-match = a pattern of { $pattern } cannot match { $target }
nibcheck-product-pattern-cannot-match = a pattern of a product cannot match { $ty }
nibcheck-product-pattern-members = a pattern of { $count } members cannot match { $ty }
nibcheck-pattern-field-count = { $name } has { $fields } fields, the pattern { $pattern }
nibcheck-match-depends-on-value = the type of this `match` depends on the value `{ $name }`, which only a proof can check
nibcheck-match-not-exhaustive = the `match` does not cover every value
nibcheck-match-literals-need-rest-arm = a `match` on literals ends with a named rest arm (`other => …`)
nibcheck-default-arm-last = the default arm `_ =>` must be the last
nibcheck-default-arm-unreachable = the default arm `_ =>` matches no value
nibcheck-typed-arm-nested = a typed binding `{ $name }: …` stands only as the whole pattern of a `match` arm
nibcheck-typed-arm-not-union = a typed arm narrows a union; this `match` is on { $ty }
nibcheck-typed-arm-unsolved = a typed arm narrows a union whose type is known; this `match` is on { $ty }: write its type (`match x: T {"{"} … {"}"}`)
nibcheck-typed-arm-not-member = { $arm } is neither a member of { $ty } nor a union of its members
nibcheck-typed-arm-type-variable = the member { $member } is a type variable: a typed arm cannot tell its values from the other members'
nibcheck-typed-arm-no-head = the member { $member } has no head a typed arm can test
nibcheck-typed-arm-same-head = { $other } and { $member } have the same head: a typed arm for { $arm } cannot tell their values apart
nibcheck-pattern-on-union = a constructor or a literal does not match the union { $ty }: narrow to a member first, `x: T => match x {"{"} … {"}"}`
nibcheck-match-members-not-covered = the `match` does not cover the members { $members }
nibcheck-arm-told-apart-by-type-arguments = `{ $effect }` is told apart by its type arguments: an arm answers one instance, `{ $effect }<…>(…)`
nibcheck-arm-value-count = `{ $effect }` gives { $expected } values, the arm takes { $given }
nibcheck-direct-arm-must-resume = { $effect } is direct; every path of its arm must end in k(e)
nibcheck-arm-does-not-resume = { $effect } does not resume (`resume 0`): its arm has no `{ $k }`
nibcheck-arm-must-be-generic = the arm of `{ $effect }` must work for whatever type arguments it is performed with: they are chosen where it is performed

nibcheck-operands-differ = `{ $op }` of { $left } and { $right }: the operands differ
nibcheck-operands-differ-labeled = `{ $op }` of { $left } and { $right }: the operands differ; `@{ $tag }` labels only its operand, since it binds tighter than `{ $op }`; to label the result, write `@{ $tag } (a { $op } b)`
nibcheck-not-a-constructor-hint = `{ $name }` is not a constructor; did you mean `{ $hint }`?
nibcheck-not-a-constructor-plain = `{ $name }` is not a constructor

# Classes and instances.

nibcheck-class-already-class = { $name } is already a class
nibcheck-class-built-in = { $name } is built in
nibcheck-class-declared-twice = class { $name } is declared twice
nibcheck-class-already-type = { $name } is already a type
nibcheck-value-indexed-classes = value-indexed classes require checked dictionary extraction
nibcheck-class-parameter-count = class { $name } takes one parameter, not { $count }
nibcheck-class-argument-arity = class { $name } takes { $expected } parameter(s), not { $count }
nibcheck-not-a-kind = { $name } is not a kind
nibcheck-class-parameter-no-borrow = the parameter of class { $class } cannot be bounded by NoBorrow; write `NoBorrow` on the type parameters of its methods and of the functions that use it
nibcheck-class-member-declared-twice = { $class }::{ $name } is declared twice
nibcheck-class-method-where-cycle = the `where` of a method leads back to its own class: { $path }
nibcheck-class-method-performs-effects = { $class }::{ $name } performs effects, so { $class } cannot have laws
nibcheck-value-indexed-instances = value-indexed class instances require checked dictionary extraction
nibcheck-class-structural-no-instances = { $name } is structural and has no instances to write
nibcheck-instance-head-distinct-generics = an instance head applies a type to distinct generics
nibcheck-generic-not-in-head = { $name } does not appear in the head
nibcheck-instance-needs-constructor = { $class } takes a type constructor with one argument missing, and { $shown } is not one
nibcheck-instance-type-kind = { $class } takes types up to { $bound }, and { $shown } is { $kind }
nibcheck-instance-orphan = { $class }({ $ctor }) must be in the tote of { $class } or of { $ctor }
nibcheck-instance-duplicate = { $class } already has an instance for { $ctor }
nibcheck-where-only-generics-of-instance = where constrains only generics of the instance
nibcheck-instance-no-law = { $class } has no law { $name }
nibcheck-instance-law-twice = the law { $name } of the instance is written twice
nibcheck-instance-missing-method = the instance { $class }({ $ty }) does not define { $name }
nibcheck-instance-method-parameters = { $class }.{ $name } of { $head } takes { $parameters }

# Effects indexed by type.

nibcheck-index-entry-binds-each-type-argument = `{ $entry }`: every instance of `{ $head }` binds each type argument in order: `∀ { $want }. { $head }({ $want })`
nibcheck-index-entry-write-forall = `{ $entry }`: write `∀ A. res(A)`
nibcheck-row-write-instance = write the instance of `{ $entry }` the row means: `{ $entry }(…)`, or `∀ { $want }. { $entry }({ $want })` for every one
nibcheck-copied-for-too-many-indices = `{ $name }` is copied for too many indices
nibcheck-index-no-type-found = no type was found
nibcheck-index-generic-not-given = it is the generic `{ $name }`, which is not given
nibcheck-index-arguments-unknown = its type arguments are not known here; annotate them
nibcheck-type-cannot-index-effect = `{ $ty }` cannot index an effect
nibcheck-which-effect-this-is = which `{ $effect }` this is: { $why }
nibcheck-row-around-two-instances = the row around it has two instances of `{ $effect }`; write which with a type annotation
nibcheck-generic-indexes-effect-by-why = `{ $generic }` indexes an effect by `{ $wanted }`: { $why }
nibcheck-generic-indexes-effect-by-unknown = `{ $generic }` indexes an effect by `{ $wanted }`, which is not known here
nibcheck-arguments-rows-name = its arguments' rows name `{ $wanted }` as { $found }; write which with a type annotation
nibcheck-call-row-two-instances = the row around this call has two instances of the effect it indexes by `{ $wanted }`: { $found }; write which with a type annotation
nibcheck-argument-performs-it-as = the argument performs it as { $found }; write which with the result's type

# What a type cannot be cloned for.

nibcheck-type-is-linear = { $ty } is linear
nibcheck-type-has-no-clone = { $ty } has no clone

# Captures and the classes a type needs.

nibcheck-capture-kind-fixed = capture `{ $name }` is inferred as { $kind } after its function kind was fixed; add a type annotation to the captured binding
nibcheck-capture-kind-undetermined = the kind of capture `{ $name }` is not determined; add a type annotation to the captured binding
nibcheck-needs-class = { $what } needs { $class }({ $ty })
nibcheck-needs-class-add-where = { $what } needs { $class }({ $ty }): add where { $class }({ $ty })
nibcheck-class-type-undetermined = the type in { $class }(?) is not determined: a method whose arguments do not tell it names the instance, as in `{ $class }(T)::m(…)`
nibcheck-no-instance = no instance { $class }({ $ty })

# Uses of values: moves, borrows and drops.

nibcheck-lin-not-used = { $name } is not used
nibcheck-lin-arm-captures = arm captures { $what } { $name }
nibcheck-lin-arm-moves-many-times = the arm of { $op } moves { $name }, but it runs many times
nibcheck-lin-borrowed-cannot-move = { $name } is borrowed and cannot be moved
nibcheck-lin-closure-borrows-cannot-store = { $name } borrows { $borrows } and cannot be stored
nibcheck-lin-var-moved-out-of-closure = { $name } is a var and cannot be moved out of a closure
nibcheck-lin-used-after-move = { $name } is used after move
nibcheck-lin-moved-in-loop = { $name } is moved inside a loop and not assigned again before the loop repeats
nibcheck-lin-live-across-many = { $name } is live across { $shown }, which resumes ω
nibcheck-lin-outer-var-across-many = `var { $name }` from outside the handle is used across { $shown }, which resumes ω: each resumption would have its own copy of it
nibcheck-lin-used-some-paths = { $name } is used on some paths only
nibcheck-lin-lend-to-borrowed-parameter = a borrow can only be lent to a borrowed parameter
nibcheck-lin-lent-function-kept = a borrowed function cannot be kept: it can only be called or lent
nibcheck-lin-lent-function-to-generic = a borrowed function can only be lent to a parameter declared as a borrowed function
nibcheck-lin-this-closure-borrows = this closure borrows { $names } and cannot be stored
nibcheck-lin-borrow-effect-argument = a borrow cannot be an effect argument
nibcheck-lin-borrow-returned = a borrow of { $name } cannot be returned
nibcheck-lin-borrow-returned-through = a borrow of { $name } cannot be returned: the value borrows it through { $effect }, whose handle answers with it
nibcheck-lin-borrowed-in-budget = { $name } is borrowed in a budget, whose stopped body may outlive it
nibcheck-lin-destructure = { $name } is { $class }; destructure { $root }
nibcheck-lin-consumes-captured = { $name } consumes a value it captured, so it can be called only once and cannot be lent to a borrowed function parameter
nibcheck-lin-borrowed-after-move = { $name } is borrowed after move
nibcheck-lin-moved-while-borrowed = { $name } is moved while it is borrowed in the same call
nibcheck-lin-borrowed-twice = { $name } is borrowed twice in one call
nibcheck-lin-borrowed-in-argument = { $name } is borrowed again inside an argument while an earlier argument of the call around still borrows it
nibcheck-lin-drops-linear = `_` drops a linear { $ty }

# Classes and the parts of a use diagnostic.

nibcheck-lin-class-shared = shared
nibcheck-lin-class-affine = affine
nibcheck-lin-class-linear = linear
nibcheck-lin-class-var = { $class } var
nibcheck-lin-what-mut-borrow = &mut
nibcheck-lin-what-borrowing-closure = the borrowing closure
nibcheck-lin-live-across-may-not-resume = { $name } is live across { $shown }, which may not resume
nibcheck-lin-live-across-may-not-resume-div = { $name } is live across { $shown }, which may not resume; finish the loop before the arm (in the body), give it fuel so it has no div, or declare the operation resume <=1
nibcheck-lin-borrowed-by-arm = { $name } is borrowed by the arm of { $op }
nibcheck-lin-frozen-by = { $name } is frozen by { $by }
nibcheck-lin-does-not-live-long-enough = { $owner } does not live as long as { $name }, which borrows it
nibcheck-lin-holds-borrow-of = holds a borrow of { $name }
nibcheck-lin-shares-var = shares var { $name }
nibcheck-lin-continuation-only-in-arm = { $name } { $why }, so it may only be called in its arm

# Reference cycles.

nibcheck-cycle-unchecked = { $what } may hold a value that cannot be checked for reference cycles: { $why }
nibcheck-cycle-self = { $what } may hold itself through a closure or a data structure, which is a strong reference cycle{ $path }
nibcheck-cycle-among = strong reference cycle among { $names }{ $path }
nibcheck-type-method-uses-value = the body of `{ $name }` is a type that uses the parameter `{ $param }`: a method that gives a type is read where its instance is known, by the type of its arguments, not by their values
nibcheck-borrows-result-holds-no-borrow = `borrows(…)` is written on a function whose result { $ty } holds no borrow
nibcheck-borrows-not-a-borrowed-parameter = `{ $name }` in `borrows(…)` is not a parameter that lends a borrow
nibcheck-lin-not-in-borrows = the result borrows { $name }, which is not in borrows(…)
nibcheck-let-unknown-prop = `{ $word }` is not a property of `let`; only `let(stack)` is written
nibcheck-stack-var = `{ $name }` is a `var`; only a `let` is written with `stack`
nibcheck-stack-type-param = `let(stack) { $name }` has the type { $ty }, which holds the type parameter `{ $param }`; its size is not known in the frame
nibcheck-stack-recursive = `let(stack) { $name }` has the type { $ty }, which holds itself; its value is not placed in the frame without an allocation
nibcheck-coerce-own-field = `{ $field }` is a field of `{ $ty }`; write `{ $place }.{ $ty }::{ $field }`
nibcheck-coerce-move = `{ $ty }` coerces to `{ $target }` only by { $allowed }; write `coerce(owned)` to move it out
nibcheck-coerce-lend-mut = `{ $ty }` coerces to `{ $target }` only by `&`; write `coerce(mut)` to lend it as `&mut`
nibcheck-coerce-assign = `{ $ty }` coerces to `{ $target }` only by `&`; write `coerce(mut)` to assign its fields
nibcheck-coerce-duplicable = `&{ $ty }` cannot be passed as `&{ $target }`: `{ $target }` is duplicable, so this needs `coerce(owned)`
nibcheck-lin-lending-operation-resumes-once = `{ $name }` answers a value that may hold a mutable borrow, so it resumes at most once: declare it `resume 1` or `resume <=1`
nibcheck-lin-overwrite = { $name } holds a linear value that this write would drop; take it out with `replace` instead
nibcheck-pattern-cannot-match-labelled = a pattern of { $pattern } cannot match { $target }, which is under the label { $label }: write the pattern with the label (`{ $label } { $name }`), or take the label off in the annotation of the value (`match (e: { $pattern }(…))`, as `@a T <: T`)
nibcheck-index-entry-writes-body-row = `{ $entry }` hides what the body performs: write its row, `∀ T. { $head }(() -> T ! {"{"}…{"}"})`
nibcheck-lent-struct-without-owner = struct &{ $name } needs a type { $name } declared in the same module
nibcheck-lent-struct-generics = struct &{ $name } takes the same type parameters as { $name }
nibcheck-lent-struct-field = field { $field } of struct &{ $name } is neither duplicable nor a borrow
nibcheck-lent-struct-without-lend = struct &{ $name } needs an instance of Lend({ $name }) in the same module
nibcheck-export-twice = exports lists `{ $name }` twice
nibcheck-export-unknown = exports names `{ $name }`, which is not a function of the program
nibcheck-export-generic = exports names `{ $name }`, which has generics: a generic function has no code of its own to export
nibcheck-export-unknown-tote = exports names `{ $tote }::*`, but `{ $tote }` is not a tote the program reads (a tote is named as its Tauto.eure `name`, with `-` as written there, not as an import name; the totes read: { $known })
nibcheck-export-ambiguous = exports names `{ $name }`, which is declared by more than one file: write one of { $candidates }
