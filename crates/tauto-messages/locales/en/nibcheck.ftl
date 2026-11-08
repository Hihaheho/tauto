nibcheck-not-a-constructor = { $name } is not a constructor
nibcheck-ambiguous-constructor = ambiguous constructor `{ $name }`: use a type annotation or { $candidates }
nibcheck-no-field = { $name } has no field `{ $field }`
nibcheck-effect-takes-no-type-arguments = `{ $effect }` takes no type arguments
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
nibcheck-mismatch-closure-kind = { $what }: an { $found } closure where { $expected } is expected
nibcheck-mismatch-open-product = { $what }: { $found } and { $expected } are matched by the types of their members only where neither mentions a type parameter or an unknown type; write the members in the same order, or tell them apart with tags
nibcheck-mismatch-product-clash = { $what }: two members of a product have the type { $member }, so the members cannot be matched by their types; write the members by position, or tell them apart with tags
nibcheck-forgets-linear-member = { $what }: this forgets the linear member { $member }
nibcheck-not-an-application = { $ty } is not an application of a type constructor
nibcheck-literal-does-not-fit = { $literal } does not fit { $ty }
nibcheck-kind-does-not-fit-bound = { $kind } does not fit { $bound }: { $ty } for a type parameter
