# `tauto proof`

`tauto proof FILE [NAME] [--format block|node|tree|tree-html|natural|json] [--full] [--output FILE]`
shows the derivations of the file's own theorems (or just `NAME`; duplicate
names are rejected; imported theorems are not shown). Theorems that check
without axioms show only their name; incomplete, failed, unchecked and
axiom-dependent ones say so.

## Derivations

The kernel's final check records, per judgment, context, term, type, rule and
premises. Recording bypasses the proof cache, and the display has no typing
rules of its own. Theorem parameters are the initial context; introductions
show which assumptions they close. Applications have the function and
argument judgments as premises; conversions and universe inclusions keep the
judgment before conversion; `match` and local definitions appear as their
elaborated terms, eliminations as the real eliminator applied to typed
arguments. Holes and references without kernel proofs are open premises, and
everything depending on them is incomplete. If checking fails, the diagnostic
is shown and nothing is reconstructed from syntax.

## Formats

- `natural` (default): numbered mathematical prose in the CLI language:
  assumptions, lemmas used, computations, conclusion.
- `tree`: a Unicode proof tree, premises above the rule line; contexts are
  referenced as numbered `Γ`s.
- `tree-html`: the same tree in HTML.
- `block`: HTML with nested collapsible blocks (premises as typed slots,
  conclusion as output).
- `node`: HTML node graph (premises as input ports wired to the nodes that
  prove them).
- `json`: the full derivation.

HTML is a single self-contained file with no scripts or external resources;
source text is escaped; same types share colours; blocks with open premises
are dashed. Output goes to stdout or to a new `--output` file (never
overwritten). Exit status: 0 ok, 1 check or I/O failure, 2 bad arguments,
3 incomplete; failures of unselected or imported theorems count.

## Natural-language summarization

The display never searches; every sentence comes from a recorded judgment,
and summarizing never changes the verdict.

- Fully annotated applications whose annotation contains no proof steps fold
  into their body. Proposition formation and universe inclusion are not
  restated. Definitional conversions fold into the neighbouring step; a
  conversion closing a goal by computation keeps both ends. Transport along an
  equation is never omitted.
- Congruence, symmetry and transitivity, after checking their endpoints match
  (structurally or definitionally), become an equation chain with reasons;
  intermediate results used elsewhere stay as references.
- Generated eliminators of a single inductive whose parameters, motive, minors,
  indices and target line up become destructuring, case analysis or induction
  (induction whenever the type is recursive). Unreferenced branch locals are
  omitted. Others (e.g. mutual) are shown as applications.
- Constructor applications of propositions show the constructor, data and
  evidence in dependency order.
- References are written where used; implicit arguments without proof content
  are omitted; short single-use proofs are inlined. Results referenced later
  are numbered in order of appearance and shared when context, term and type
  agree (comparing declarations and free locals by ID, up to bound renaming),
  but never across assumption scopes. Generated local names are made
  unambiguous.
- Open goals and what depends on them are never summarized.
- Display queries run on a copy of the checked environment, at most 4096 steps
  each; when a correspondence cannot be confirmed, the raw judgment is shown.

`--full` shows the whole recorded derivation, including parameter
introduction, with every judgment numbered and no summarization. It is the
final check's derivation, not a history of loading or elaboration.

## JSON

Top level: `version` (1), `status` (`ok`, `incomplete`, `failed`), `proofs`:

| Field | Content |
|---|---|
| `name`, `status` | `checked`, `incomplete`, `failed` or `skipped` |
| `parameters`, `implicit` | written parameters, number of leading implicits |
| `goal`, `goal_tree` | conclusion as text and term |
| `axioms`, `uses` | axioms depended on, incomplete declarations used |
| `holes` | `name`, `goal`, `goal_tree`, `context` |
| `error` | reason, or `null` |
| `derivation` | root node, or `null` |

Nodes have `id` (preorder), `rule` (`assumption`, `constant`, `unverified`,
`literal`, `sort`, `formation`, `introduction`, `application`, `conversion`,
`reduction`, `hole`), `complete` (no open leaves; use `status` for
acceptance), `context`, `term`/`term_tree`, `type`/`type_tree`, `introduced`,
`premises`. Bindings have `name`, `type`, `type_tree`. Terms use the
representation of `tauto elaborate --json`. JSON always contains the full
derivation; identifiers are language-independent. If output cannot be built,
the diagnostic goes to stderr with status 1.

## Macro notation

Human formats print an expression macro's original call in place of its
expansion; JSON keeps the expansion. The call is used only when the term
(without positions, up to bound renaming, not up to computation), type
arguments and context match the recorded expansion, the candidate is unique,
and display renaming did not change binders. Calls containing global
references are used only in a context of the original length; calls with only
local references may be used in an extended context if the binders are not
shadowed. Collection stops at the theorem's parameters; macro calls produced
by expansions and statement macros are not restored. Otherwise the plain term
is printed.

## Editor hover

`tauto lsp` shows the `natural` proof under the signature when hovering a
theorem's keyword, name or a reference to it, preserving layout and not
interpreting it as Markdown. It uses the snapshot including unsaved edits,
caches per theorem until the open files change, and falls back to the
signature on failure.
