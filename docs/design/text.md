# Templates (`text!`)

A template is fixed text with holes. It is a literal of the syntax `text`
(`std/template.taut`), so a macro receives it as a typed value
([`macro.md`](macro.md)「Typed AST」). `text!` makes a `Text` of it, and other
macros (a logger, an escaping writer) read the same template through the
functions of `std::template`. Examples: [`cases/macro/text.eure`](../../cases/macro/text.eure).

## Syntax

```par
%start Template
%auto_newline_off
%auto_ws_off
%%
Template: { Part };
Part: Fixed | Dollar | TautoExpr;
Fixed: /[^$]+/;
Dollar: '$$';
```

The syntax registers `tokens` (`text_tokens`): fixed text is a string, `$$` an
operator, and holes keep the colours of Tauto.

- A hole is `$` and one postfix expression, or `${ … }`
  ([`macro.md`](macro.md)「Tauto expressions inside a DSL (`${ … }` and `$`)」).
- `$` is the only special character, and `$$` is a dollar. There are no
  escapes: a block literal holds quotes, braces and new lines as written.
- A syntax error in a hole is an error at the hole.

## `text!`

``text!(`Hello, $name! You have ${n + 1} new messages.`)`` is a `Text`.

- The expansion is `Text::concat_all([p1, …, pn])`: a fixed part is its
  literal, and a hole `e` is `ToText::to_text(&e)`. One part is the part
  itself, and no part is `""`.
- Each hole is evaluated once, from left to right, and borrowed, so an affine
  value in a hole is still the caller's after it.
- A hole that is a `Text` literal is fixed text, and adjacent fixed text is
  one part.
- The call of a hole is written at the hole, so an error in it (a type without
  `ToText`) points at the hole in the caller's file.
- The expansion performs nothing; the effects are those of the holes.

## `std::template` for macros

These run when a macro runs; a macro's argument of type `text::Template` is a
template.

| Function | Value |
|---|---|
| `parts(t): List(Part)` | the parts, folded as `text!` folds them |
| `text_with(t, f: SynIdent): SynExpr` | `text!`'s expansion, each hole `e` rendered by `f(&e)` |
| `pattern(t): Text` | the fixed text, `{name}` for a named hole and `{}` for another |
| `each_named(t, f: (SynExpr, SynExpr) -> SynExpr): SynExpr` | the list of `f(name, e)` for the named holes, `name` a literal at the hole |
| `call_at(f: SynIdent, h: Hole): SynExpr` | `f(&e)` written at the hole `h` |

`text!` itself is the function `text(t): SynExpr`.

```nib
pub(open) enum Part { Fixed(Text, SynSpan)  Hole(Hole) }
pub(open) struct Hole { expr: SynExpr, name: Option(Text), span: SynSpan }
```

A hole's name is the last name written in it: the variable (`$user`), the
field (`$(req.path)`) or the label (`$(@ms elapsed(t))`). Other holes have
none. For a labelled hole, `expr` is the value under the label.

## Options

Options are functions called in a hole, as any other expression is:
`$(pad_start(name, 8))`. Each is total and performs nothing; a value that
would be wrong for one is a type that cannot hold it (`hex` takes a `u64`).
Widths are `Nat`s and count characters (code points).

| Function | Value |
|---|---|
| `pad_start(a, width)`, `pad_end(a, width)` | `a`'s text with spaces before or after it, to at least `width` characters |
| `pad_start_with(a, width, fill)`, `pad_end_with(a, width, fill)` | the same with copies of the text `fill`; an empty `fill` adds none |
| `hex(n)`, `hex_upper(n)`, `bin(n)`, `oct(n)` | the `u64` `n` in base 16 (`a`–`f` or `A`–`F`), 2 or 8, without a prefix |
| `zeros(n, width)` | the `i64` `n` with zeros after its sign, to at least `width` characters |
| `signed(n)` | the `i64` `n` with its sign, `+` when it is not negative |
| `grouped(n, sep)` | the `i64` `n` with `sep` between groups of three digits |
| `quoted(t)` | the text `t` as a Tauto literal |
| `join(xs, sep)` | the elements' texts with `sep` between them (`std::builtin::classes`) |

The options other than the paddings and `join` are definitions of the kernel's
fragment, so proofs can state facts about them.

## Open questions

- Options for `Float`.
- A macro reading a hole twice (once for its text, once for a field)
  evaluates it twice; a way to bind the holes once is not provided.
