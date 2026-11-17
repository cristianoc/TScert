# Arithmetic rules stated once

The arithmetic rules of [Tolerant frames](tolerant-frames-note/note.tex)
(§6, "Arithmetic steps") as one Lean datum per rule, which the
implementation's producer (A) and the paper's derivation (B) both
instantiate, and from which the paper's rule rows and
[ARITHMETIC.md](../ARITHMETIC.md)'s rules are generated and checked. The
first rules are Shr, Mask (two triples), Shl and Or; the datum's interface
also states Add, Sub and Scale, which migrate after them.

## The existing mechanisms this extends

- **Integer facts** ([DESIGN.md](../DESIGN.md#general-mechanisms)): linear
  facts over value, length and path terms, decided by linear certificates,
  owned by [ARITHMETIC.md](../ARITHMETIC.md#linear-facts).
  - A: `IndexWrites.linearAtoms` reads both operands as linear forms
    (`operandForm`, which requires a safe integer), then states each
    operation's facts: sums, differences and constant products by
    `resultForm`, `>>` and `&` by `bitAtoms` under the premises its `match`
    states (`0 ≤ cb < 32`, `0 ≤ cb < 2^31`, `smallOperand`), comparisons by
    `compareAtoms`. `linearAtoms_holds` proves the emitted atoms;
    `bitAtoms_holds` rests on `SafeIntegers.shr_safe` and `bitAnd_safe`.
  - B: `ParityDerivations` reads operands by `Operand.form` and
    `Operand.premise` (safe integers), states the facts by `resultForm`,
    `shrFacts` and `maskFacts`, and derives them by
    `Derivation.integerOperation`, `.shiftRight` and `.mask`, each taking
    the operation's evidence (`dop`), its operands' and its constant's.
  - `Bridges/ParityArithmeticBridges` proves that A's atoms and B's
    conclusions hold at the same states (`shrAtoms_iff`, `maskAtoms_iff`).

  This design keeps the mechanism and states each rule once, as a datum
  both sides instantiate.
- **Text produced from code**: no mechanism generates documentation. Three
  come near: commit records rendered by `dev/record-render.mts` (a fixed
  format with a renderer, written by hand); `tests/json-field-names.mts`
  (one fact compared in two places, nothing generated); `tests/docs.mts`
  (links, anchors, math and the annotation inventory). The generated
  sections below are a new mechanism, owned by a new document and listed
  among the general mechanisms.

## The rule datum

`Semantics/ArithmeticRules.lean`, in the shared model. An `ArithRule`
states, for one numeric operation producing linear facts:

- its paper name and its place in the paper's order (presentation only);
- the operator, the calculus's `Arith`;
- each operand's domain: a safe integer, or any Number (Mask's range rule
  reads `x` as any Number);
- the constant operand, where there is one, and its binding: a literal or a
  value known to be constant; its side condition (`0 ≤ m < 2^31`); its
  normalisation (a shift count `d' = ToUint32(d) mod 32`, as `arithBits`
  reads it);
- the premises, linear facts over the operands' terms, whose coefficients
  are computed from the bound constant (`2^{d'}`);
- the result's definedness (a safe integer) and the conclusion, linear
  facts over the result's and the operands' terms.

`rules` lists the paper's rules. Each is stated at the generality its
semantics allows; the list is the rules themselves, not a list standing
for a property. Comparisons, with their conditional Boolean facts, and the
sum past the safe integers, with its disjunction, keep their present forms.

One soundness statement covers every rule: for operand values in their
domains meeting the premises, the calculus's result (`arithBits`, through
`ToInt32`) is defined and meets the conclusion. Its instances for Shr and
Mask where `0 ≤ x < 2^31` are today's `shr_safe` and `bitAnd_safe`; the
general forms, Shl and Or are new proofs.

The four rules, as approved (`d' = ToUint32(d) mod 32`, `0 ≤ m < 2^31`):

| Rule | Domain and premises | Conclusion |
| --- | --- | --- |
| Shr | `x` a safe integer, `-2^31 ≤ x < 2^31` | `2^{d'}·y ≤ x ≤ 2^{d'}·y + 2^{d'} − 1` |
| Mask (range) | `x` any Number | `0 ≤ y ≤ m` |
| Mask (bound) | `x` a safe integer, `0 ≤ x` | `y ≤ x` |
| Shl | `x` a safe integer, `-2^31 ≤ 2^{d'}·x < 2^31` | `y = 2^{d'}·x` |
| Or | `x`, `x'` safe integers, `0 ≤ x < 2^31`, `0 ≤ x' < 2^31` | `x ≤ y`, `x' ≤ y`, `y ≤ x + x'` |

## A and B from the datum

- **A**: `linearAtoms` reads each operand only in the form its rule's
  domain asks (a linear form for a safe integer, nothing for any Number),
  and for each rule of the operator emits the conclusion, instantiated at
  the step's slots, where the instantiated premises are entailed
  (`entailsKnown`). The emitted atoms are proved by the soundness statement
  through `linearAtoms_holds`; `bitAtoms` and its inline premises are
  deleted.
- **B**: one constructor, `Derivation.arith`, taking a rule of `rules`,
  the operation's evidence, the operands' and constant's evidence its
  domains ask, and a derivation of each instantiated premise, and
  concluding the instantiated conclusion; sound by the same statement.
  `shiftRight`, `mask`, `shrFacts` and `maskFacts` are deleted.
- **What is shared, and what is not**: A and B instantiate the same
  domains, side conditions, premises and conclusions, through one
  substitution of the datum's terms by a step's slots (A) or a two-state's
  terms (B), with one interpretation lemma. They establish premises
  differently: A by entailment from the knowledge at the step, B by
  derivations. So A applies a rule only where B can derive its premises
  (A to B), and B derives a rule's conclusion wherever its premises are
  derivable, which A matches only where its entailment finds them (B to A,
  partial, as [the basis](implementation-and-paper-rules.md) states for
  every rule). The bridge lemmas for Shr and Mask become instances of the
  interpretation lemma and are deleted.

## Generated sections

A new mechanism, owned by a new document, `docs/GENERATED-SECTIONS.md`,
and listed in [DESIGN.md](../DESIGN.md#general-mechanisms):

- **A registry**, `tools/generated-sections.mts`: each section's identity,
  destination file, output format (Markdown or LaTeX) and producer. A
  destination holds each registered section once, between
  `<!-- generated: <id> -->` and `<!-- end generated: <id> -->` (`%`
  comments in LaTeX); a missing, duplicate, nested or unmatched marker
  fails.
- **One producer per datum**: the verifier exports the datum as JSON
  (`verifier --export rules arithmetic`), every semantic field and the
  names of the Lean declarations that state and prove each rule. Nothing
  else states the rules.
- **One renderer**, in TypeScript, from that JSON to each format: the
  paper's rule rows (LaTeX, the paper's notation), ARITHMETIC.md's rules
  (Markdown with `math` blocks GitHub renders, in that document's
  notation, each preceded by a comment carrying the rule's JSON), and a
  page for the rules, as `dev/record-render.mts` renders commit records.
- **One generation path**, used both to check and to rewrite:
  `node tools/generated-sections.mts --check`, a fast check in
  `test-all.sh`, writes nothing and fails with the difference;
  `make generate-sections` rewrites every section and leaves the text
  around it as it is.

A later generated section registers its producer and its destinations;
the markers, the check, the rewrite and the renderer are shared.

## The text around the rules

- **The paper**: the rows of the "Arithmetic steps" display become a
  generated section; the paragraph that introduces them states each rule's
  operand domains as the rows do (Mask's range rule for any Number), and
  its status tag names the soundness statement's declarations.
- **ARITHMETIC.md**: the section "Bounded bitwise operands" holds the
  generated rules; its prose explains them and names the declarations that
  state and prove them now.

## Cases

- `bounds-pattern-shift-or-refused` (P21) becomes verified at the read,
  renamed to drop `-refused`.
- Negative cases, run under Node, where the program is unsafe:
  `8388608 << 8` is `-2147483648`, read as an index below 0; an or whose
  result read as an index of a 256-entry table exceeds it
  (`(1 << 8) | 0` read in `table[...]` of length 256 gives `undefined`).
- Cases for the generalised Shr and Mask: a negative operand of `>>`
  bounding an index after an offset; a fractional or large operand of `&`
  giving a bounded index.

## Order

1. The datum, its JSON export and the soundness statement, for the four
   rules.
2. A and B from the datum; the bridge lemmas replaced; the cases.
3. The generated-sections mechanism: registry, renderer, check, rewrite,
   its document and DESIGN.md entry; the paper's rows and ARITHMETIC.md's
   rules generated; the rules page.
4. Add, Sub and Scale into the datum.
