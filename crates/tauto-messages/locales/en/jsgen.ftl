# The messages of the JavaScript backend (`tauto-jsgen`): why a program
# cannot be written as JavaScript. Names, chunks and types are variables,
# written as they are.

jsgen-unsupported = not supported by the javascript backend: { $what }
jsgen-what-host-type-in-extern = a host type inside another type of an extern signature
jsgen-what-borrowed-host-return = an extern that returns a borrowed host type
jsgen-what-secret-words = secret words, which it cannot run in constant time
jsgen-what-builtin = builtin { $name }
jsgen-what-integer-division = `/` of an integer
jsgen-what-syn-parse-without-tables = Syn::parse without its tables
jsgen-extern-retain-owner = javascript extern { $name } keeps its callbacks, so it needs a host value that owns them
jsgen-extern-retain-callbacks = javascript extern { $name } keeps its callbacks, so each one is passed by value and performs no effect but show
jsgen-export-not-function = javascript export { $name } is not a function of the program without generics
jsgen-export-performs = javascript export { $name } performs { $effect }, which no handler of the instance answers
jsgen-export-signature = javascript export { $name } has { $what } in its signature, which an instance cannot pass
jsgen-what-mutable-borrow = a mutable borrow
jsgen-what-function-by-value = a function taken by value
jsgen-what-borrow = a borrow
jsgen-what-host-type-inside = a host type inside another type
jsgen-what-effectful-function-result = a function result that performs an effect but show
jsgen-chunks-need-modules = the program has javascript chunks; write each of its modules
jsgen-chunk-bad-name = javascript chunk { $chunk } must be a name of letters, digits, `_` and `-`
jsgen-chunk-no-entry = javascript chunk { $chunk } has no entry function
jsgen-chunk-not-function = javascript chunk { $chunk } names { $name }, which is not a function of the program without generics
jsgen-chunk-names-start = javascript chunk { $chunk } names { $name }, which runs when the program starts
jsgen-chunk-entry-twice = { $name } is an entry of both javascript chunks { $other } and { $chunk }
jsgen-declarations-opaque-data = javascript declarations: opaque data type { $name } has no declared JavaScript representation
jsgen-declarations-missing-entry = javascript declarations: missing entry function { $id }
jsgen-declarations-unknown-data = javascript declarations: unknown data type { $name }
jsgen-declarations-type-argument-count = javascript declarations: wrong number of type arguments for { $name }
jsgen-declarations-unknown-union = javascript declarations: unknown union { $id }
jsgen-declarations-unbound-parameter = javascript declarations: unbound type parameter { $name }
jsgen-declarations-function = javascript declarations: functions are supported only as direct extern callback parameters; nested or returned functions use internal runtime calling conventions
jsgen-declarations-standard-type = javascript declarations: standard type { $name } has no declared host representation
jsgen-declarations-internal-type = javascript declarations: internal or unresolved boundary type { $ty }
jsgen-syntax-data-not-retained = runtime syntax data { $data } is not retained
jsgen-syntax-schema-constructor = schema constructor { $data }::{ $ctor }
jsgen-syntax-schema-fields = schema constructor { $data }::{ $ctor } has other fields
jsgen-syntax-expression-hole = a runtime expression hole
jsgen-syntax-no-start-type = a syntax without a start type
