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
| `arithmetic-rules` | [ARITHMETIC.md](ARITHMETIC.md#linear-facts), "Arithmetic rules" | the rules as `math` blocks, each preceded by a comment naming the rule's declarations |

## The arithmetic rules' export

`verifier --export rules arithmetic` prints `ArithmeticRules.rules` as a
Markdown document that reads on its own, the one statement of the rules
every section is rendered from:

- a title and a sentence naming the rules, the soundness statement
  (`ArithmeticRules.ArithRule.Sound`) and its proof over every rule
  (`ArithmeticRules.rules_sound`);
- for each rule, in the paper's order, a section headed by its name (the
  paper's; the triples of one rule share it), with its operator in the
  calculus and the Lean declarations that state and prove it;
- a table of the rule's variables, `left`, `right` and `result`, each with
  its role (an operand, a constant read as itself or as a shift count, or
  the result) and its sort (`Num` or `SafeInt`), both computed in Lean
  from the rule's domains (`ArithRule.variables`): a constant is a
  `SafeInt`, as the rule's soundness reads it;
- for a rule with a constant, a sentence with its bounds and how the rule
  reads it;
- the premises and the conclusion, each fact a line
  `(coefficient)·variable + … ≤ bound`, a coefficient written in the
  rule's constant `k` as read: `2^k - 1`, `-1`, `k`.

The reader in `dev/generated-sections.mts` reads exactly that form, line
by line, and refuses any other line.

## The renderer

One renderer sets a rule in three notations, from the same facts:

- the paper's rows, one per triple: the rule's name on its first triple,
  the operands' sorts as the export states them, then
  `\hoare{P}{y=x op c}{Q}`;
- ARITHMETIC.md's inference rules, `int(a)`, `K ⊢ b = d` and the premises
  over `K ⊢ r ← a op b ⊣ int(r), …`, the rule's name followed by the
  operands' sorts;
- a page of the rules, drawn as `dev/record-render.mts` draws the rules of
  a commit record, the sorts first among the premises, with each rule's
  declarations.

A variable's letter follows from its role and sort as the export states
them, one convention for every rule: $`a`$ and $`b`$ for the first and
the second operand of `SafeInt`, $`x`$ for an operand of `Num`, $`d`$ for
a constant read as a shift count and $`c`$ for another, and $`y`$ for the
result ($`r`$ in ARITHMETIC.md).

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
