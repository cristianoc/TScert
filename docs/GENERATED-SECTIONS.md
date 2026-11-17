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
| `paper-arithmetic-rules` | [Tolerant frames](drafts/tolerant-frames-note/note.tex), the rows of the display "Arithmetic steps" | the paper's rule rows of the display `arithmetic` |
| `paper-string-rules` | [Tolerant frames](drafts/tolerant-frames-note/note.tex), the rows of the string steps | the paper's rule rows of the display `strings` |
| `paper-view-rules` | [Tolerant frames](drafts/tolerant-frames-note/note.tex), the rows of "The typed array's steps" | the paper's rule rows of the display `views`, with their effects |
| `paper-library-rules` | [Tolerant frames](drafts/tolerant-frames-note/note.tex), the rows of "Library functions" | the paper's rule rows of the display `library` |
| `arithmetic-rules` | [ARITHMETIC.md](ARITHMETIC.md#linear-facts), "Arithmetic rules" | the rules of the display `arithmetic` as `math` blocks, each preceded by a comment naming the rule's declaration and evidence |
| `string-rules` | [ARITHMETIC.md](ARITHMETIC.md#linear-facts), "The steps stating them" | the rules of the display `strings`, alike |
| `view-rules` | [SOURCE-CONTRACTS.md](SOURCE-CONTRACTS.md#the-standard-librarys-typed-arrays), "The three steps' rules" | the rules of the display `views`, alike, with their effects |
| `library-rules` | [SOURCE-CONTRACTS.md](SOURCE-CONTRACTS.md#the-notes-library-functions), "The note's library functions" | the rules of the display `library`, alike |

## The step rules' export

`verifier --export rules arithmetic` prints `ArithmeticRules.rules` as a
Markdown document that reads on its own, the one statement of the rules
every section is rendered from:

- a title and a sentence naming the rules, the soundness statement
  (`ArithmeticRules.ArithRule.Sound`) and its proof over every proved rule
  (`ArithmeticRules.rules_sound`);
- for each rule, in the paper's order, a section headed by its name (the
  paper's; the triples of one rule share it), with its operation (a
  binary operator of the calculus, `strLength`, `strRead`, `viewLength`,
  `viewRead`, `viewWrite`, a library call `call m,…` of the methods it
  holds of, marked `(indexed)` where its argument is a position, or
  `construct`), its display (`arithmetic`, `strings`, `views` or
  `library`), the Lean declaration that states it and its evidence: the
  declaration of its proof, or the native contracts it is assumed of, and
  the lemmas of the Lean model the entry names (`The Lean model proves …`);
- a table of the rule's variables, `left`, `right`, `third` and `result`,
  each with its role (an operand, an index, a written value, a library
  function's argument, a constant read as itself or as a shift count, or
  the result) and its sort (`Num`, `SafeInt`, `String`, `Array`,
  `TypedArray` or `Value`), both computed in Lean
  from the rule's domains (`ArithRule.variables`): a constant is a
  `SafeInt`, as the rule's soundness reads it;
- for a rule with a constant, a sentence with its bounds and how the rule
  reads it;
- the premises and the conclusion, each fact a line
  `(coefficient)·term + … ≤ bound`, a term a variable or its length
  `|variable|`, a coefficient written in the rule's constant `k` as read:
  `2^k - 1`, `-1`, `k`;
- the conclusion's atoms, `x[i] ≐ y`, `x[i] ≐ conv(v)` (the value
  converted to the typed array's format), `kept x ≠ i` (every other
  index of `x` reads what it read) and `F ⇒ G` (where one fact holds, the
  other does), and the effect, entries `region: change` in the grammar of
  the paper's effects, followed by `The result is allocated.` where the
  result is a fresh allocation.

The reader in `dev/generated-sections.mts` reads exactly that form, line
by line, and refuses any other line.

## The renderer

One renderer sets a rule in three notations, from the same facts:

- the paper's rows of a display, one per triple: the rule's name on its
  first triple, the operands' sorts as the export states them, then
  `\hoare{P}{s}{Q}`, the step `s` in mathematics (`y=x op c`) in the
  display `arithmetic`, `·` in the display `library`, whose rows are
  headed by the call (`\code{r = s.charCodeAt(i)}`, several methods one
  below the other), and in code (`\code{y = s.length}`) in the others,
  and the effect in the display `views`;
- the implementation's inference rules, `int(a)`, `K ⊢ b = d` and the
  premises over `K ⊢ r ← a op b ⊣ int(r), …`, the rule's name followed by
  the operands' sorts and, in the display `views`, the effect;
- a page of the rules, drawn as `dev/record-render.mts` draws the rules of
  a commit record, the sorts first among the premises, with each rule's
  declaration and evidence.

A display without an effect column holds rules of the empty effect alone,
which its text states; a rule with an effect there fails the run.

A variable's letter follows from its role and sort as the export states
them, one convention for every rule: $`a`$ and $`b`$ for the first and
the second operand of `SafeInt`, $`x`$ for an operand of `Num`, $`s`$ and
$`s'`$ for operands of `String`, $`b`$ for a `TypedArray`, $`\mathit{xs}`$
for an `Array`, $`v`$ for any value, $`i`$ for an index, $`v`$ for a
written value, $`a`$ and $`b`$ for a library function's arguments of
`SafeInt`, $`n`$ for one of `Num` and $`u`$ for one of `String`, $`d`$ for
a constant read as a shift count and $`c`$ for another, and $`y`$ for the
result ($`r`$ in the display `library` and in the implementation's
documents). A length is $`|x|`$ in the paper and the
implementation's term of the sort in its documents:
$`\mathrm{strLength}(s)`$ of a string, $`\mathrm{view}(b)`$ of a typed
array.

A fact `Σ aᵢ·tᵢ ≤ b` over the integers is set with its positive terms on
the left and its negative terms and bound on the right, `-b ≤ N` where it
has no positive term, `P ≤ N`, `P < N` and `P + c ≤ N` for the bounds `0`,
`−1` and `−c`, the result's term `y < E` at the bound `−1`, and `P < B` for
a bound `B − 1` where the notation names `B` (the paper's largest array
length, $`2^{32}-1`$) or writes it from a power of two ($`2^{53}-1`$
excepted). A literal from $`2^{16}`$ with no such form is written in
hexadecimal. Two facts bounding each other are an equality, and facts
sharing sides a chain `A ≤ X ≤ … ≤ B` where no other fact bounds a shared
side from below.

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
step rules' one.
