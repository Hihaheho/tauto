# The syntax errors of the parser (tauto-parol).

parse-too-deep = the source nests too deeply
parse-syntax-error = syntax error
parse-unexpected-input = unexpected input
parse-keyword-as-name = `{ $word }` is a keyword and cannot be used as a name; write it as `r#{ $word }`
parse-unexpected = unexpected `{ $found }`
parse-unexpected-line-break = unexpected line break
parse-input-after-end = unexpected input after the end
parse-let-type-eq = this `let` has `=` but no `:=`: in the type `=` is the equality of a proposition, so a binding is written `let x: T := v`
parse-let-pattern = `let` binds a single name and does not take a pattern: write `let x := v` and read the parts with field access (`x.field`), or take the value apart with `match`
