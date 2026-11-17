# Generated sections

A generated section is text of a document that a producer computes from the
code. The document holds it between two markers; one path rewrites every
section from its producer, or checks that each is what its producer gives.
The text around the markers is the document's own and is never rewritten.

## Markers

A destination holds each section registered for it once, its markers each
a line of its own:

- in Markdown, `<!-- generated: ID -->` and `<!-- end generated: ID -->`;
- in LaTeX, `% generated: ID` and `% end generated: ID`.

The lines between the markers are the section. A marker without its
partner, a section opened inside another, a section appearing twice and
markers naming a section registered for no producer there each fail the
rewrite and the check, with the file and the marker's line; a section
registered for the destination with no markers fails with the file. A
destination's sections are registered in one format, or the run fails.

## The registry

[`dev/generated-sections.mts`](../dev/generated-sections.mts) registers
each section: its identity, its destination file, its format (Markdown or
LaTeX) and its producer, a function from the code's export to the
section's text. Each producer's export is computed once per run.

| Section | Destination | Producer |
| --- | --- | --- |
| `paper-arithmetic-rules` | [Tolerant frames](drafts/tolerant-frames-note/note.tex), the rows of the display "Arithmetic steps" | the paper's rule rows |
| `arithmetic-rules` | [ARITHMETIC.md](ARITHMETIC.md#linear-facts), "Bounded bitwise operands" | the rules as `math` blocks, each preceded by a comment carrying the rule's JSON |

## The arithmetic rules' export

`verifier --export rules arithmetic` prints `ArithmeticRules.rules` as JSON,
the one statement of the rules every section is rendered from:

- `statement` and `soundness`: the names of the soundness statement
  (`ArithmeticRules.ArithRule.Sound`) and of its proof over every rule
  (`ArithmeticRules.rules_sound`);
- `rules`, in the paper's order, each with `name` (the paper's; the
  triples of one rule share it), `declaration` and `proof` (the Lean
  declarations that state and prove it), `op` (the calculus's operator),
  `left` (a domain: `safeInteger` or `number`), `right` (`{"operand":
  domain}` or `{"constant": {symbol, lower, upper, normalisation}}`, the
  bounds `null` where absent, the normalisation `identity` or
  `shiftCount`), `premises` and `conclusion` (linear facts, each `terms`, a
  list of `{var, coef}` with `var` one of `left`, `right` and `result`, and
  `bound`), and `result` (a domain). A coefficient is `{lit, byConstant,
  byPower}`, the value `lit + byConstant·k + byPower·2^k` at the normalised
  constant `k`.

The reader in `dev/generated-sections.mts` requires every field and
refuses an unknown one.

## The renderer

One renderer sets a rule in three notations, from the same facts:

- the paper's rows: `\textsc{Name} & \hoare{P}{y=x op c}{Q}`, the triples
  of one rule side by side;
- ARITHMETIC.md's inference rules, `int(a)`, `K ⊢ b = d` and the premises
  over `K ⊢ r ← a op b ⊣ int(r), …`;
- a page of the rules, drawn as `dev/record-render.mts` draws the rules of
  a commit record, with each rule's declarations.

A fact `Σ aᵢ·vᵢ ≤ b` is set with its positive terms on the left and its
negative terms and bound on the right, `-b ≤ N` where it has no positive
term, and `P < 2^p` for a bound `2^p − 1`. Two facts bounding each other
are an equality, and two facts sharing a side no other fact names a chain
`A ≤ X ≤ B`.

## Checking and rewriting

- `node dev/generated-sections.mts --check` writes nothing and fails
  with the first lines where a section differs from what its producer
  gives; it is a fast check of `test-all.sh`.
- `make generate-sections` rewrites every section from its producer,
  after building the verifier.
- `make rules-page` writes the rules' page to `$TMPDIR/arithmetic-rules.html`
  (`RULES_PAGE=F` to `F`) and opens it; it runs
  `node dev/generated-sections.mts --page F`.

## Adding a section

A new section registers its identity, destination, format and producer in
the registry, and its destination gains the two markers; the markers, the
check and the rewrite are shared. A producer reading another datum of the
code adds that datum's export to the verifier and a reader beside the
arithmetic rules' one.
