# fluent

Localized messages in the FTL format: reading resources, and formatting a message with
variables, plural categories, selectors, terms and attributes. No dependencies beyond
`std`, and no axioms.

The tauto command is to write its own messages through this tote.

## Use

`src/bundle.taut` is the entry point.

```
fn ftl(): Text {
  "emails = {$count ->
    [0] You have no new email.
    [one] You have one new email.
   *[other] You have {$count} new emails.
}
"
}

format_text(with_resource(bundle_new("en-US"), ftl()), "emails", Cons(arg_num("count", 5), Nil))
// "You have \u{2068}5\u{2069} new emails."
```

| Function | What it does |
| --- | --- |
| `bundle_new(locale)` | An empty bundle for a locale such as `"en-US"`. Placeables are wrapped in U+2068 and U+2069 |
| `bundle_isolating(b, false)` | A bundle that does not wrap placeables |
| `add_resource(b, ftl)` | Adds FTL text; returns `Added::Mk(b, errors)`. The errors are unreadable entries (`Junk(text)`) and names an earlier resource already used (`Duplicate(id)`, the earlier one is kept) |
| `with_resource(b, ftl)` | The bundle of `add_resource` alone |
| `arg_str(name, text)`, `arg_num(name, n)` | The value of the variable `$name` |
| `format(b, id, args)` | `Formatted::Mk(text, errors)`. What is missing is written as `{$name}`, `{id}` or `{-term}` and reported; a text is always returned |
| `format_attr(b, id, attr, args)` | The attribute `id.attr` of a message |
| `format_text(b, id, args)` | The text of `format` alone |
| `has_message(b, id)` | Whether a message exists |
| `error_text(e)` | A description of an error |

What is read:

- Messages `id = …`, terms `-id = …`, attributes `.attr = …`, comments (`#`, `##`, `###`).
- Values are text and placeables `{ … }`. Indented continuation lines are joined with a line
  break; blank lines may come between them. CRLF is read as LF.
- Expressions: strings `"…"` (`\"` and `\\`), numbers `42`, variables `$x`, messages `msg`
  and `msg.attr`, terms `-term` with arguments `-term(case: "object")`.
- Selectors `{ $n -> [one] … *[other] … }`. Keys are names or numbers; exactly one default
  `*`. A selector is a literal, a variable or a term attribute (term attributes cannot be
  placed).
- An unreadable entry is reported as junk, and reading continues at the next entry.

How a value is chosen:

- A number selector matches a key equal to it, and the key naming its plural category. A
  string selector matches the key with the same name. The first matching variant is used,
  else the default.
- When a selector fails (a missing variable, say) the default is used.
- A term sees only the arguments written on it; a message reference sees the same arguments.
- References are followed to depth 1000; a cycle stops there with `TooDeep`.

Plural categories (`src/plural.taut`, integers): `other` only (ja, zh, ko, …), `one` (en,
de, es, …), 0 and 1 as `one` (fr, pt), the Russian kind (ru, uk, hr, …), pl, cs and sk, and
ar. Every other language puts every number in `other`.

## What is proved

No axioms.

- `find_variant_sound` (`proof/select.taut`): the chosen variant is one of the selector's,
  and its key matches the selector.
- `find_variant_none`, `pick_default`: the default is used only when no key matches.
- `exact_number_first`, `exact_string_first`: a first key equal to the selector's number or
  string is chosen whatever the plural category.
- `text_only` (`proof/resolve.taut`): a value without placeables formats to its text, without
  errors.
- `ja_always_other`, `en_other`, `ru_never_other` (`proof/plural.taut`).
- Termination: reading is by the length of the input and resolution by a depth fuel, so both
  stop on every input.
- `examples/`: reading and resolution checked by computation (`Refl`): junk, duplicates,
  cycles, CRLF, escapes, and the plural rules of each language.

```sh
for f in src/*.taut proof/*.taut examples/*.taut; do tauto check "$f"; tauto lint "$f"; done
tauto fmt --check src/*.taut proof/*.taut examples/*.taut
```

## Limitations

- Functions (`NUMBER`, `DATETIME`, user functions). An entry with `NUMBER($n)` is junk.
- Fractions and negative numbers, as literals or arguments; plural rules are for integers.
- `\u` escapes.
