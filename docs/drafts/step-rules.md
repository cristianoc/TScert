# String and typed-array steps stated once

Paper I's rows for the string steps (Str-Length, Str-Read, Concat) and the
typed array's steps (View-Length, View-Read, View-Write, View-Write-Any),
generated from Lean as the arithmetic rows are, with the matching rules of
the implementation's documentation.

## The existing mechanism this extends

The arithmetic rules' datum (`Semantics/ArithmeticRules.lean`,
[ARITHMETIC.md](../ARITHMETIC.md#linear-facts), "Arithmetic rules") and the
[generated sections](../GENERATED-SECTIONS.md). A rule there is an operator
of the calculus's `binop`, operands with a sort and a role, linear premises
and conclusions over the operands' values, and one soundness statement
against `arithBits`. The pass applies it through `IndexWrites.ruleAtoms`,
the paper's derivation through `Derivation.arith`, and
`Bridges.ruleAtoms_agree` relates the two. The verifier exports the rules as
Markdown; `dev/generated-sections.mts` renders the paper's rows, ARITHMETIC.md's
blocks and a page.

This design extends that datum and its export; it adds no second mechanism.

## What the seven rows state, and where Lean states them

| Row | The paper | The pass (A) | The derivation (B) |
| --- | --- | --- | --- |
| Str-Length | `{true} y = s.length {y = |s|}` | `linearAtoms` on `lenOf` of a string slot: `int(y)`, `y = strLength(s)` | `Derivation.stringLengthRead`: `lengthReadFacts`, `y` a safe integer and `y = |s|` |
| Str-Read | `{0 ≤ i < |s| ∧ i < N} y = s[i] {|y| = 1}` | none: no producer states a code unit's length | `Derivation.stringRead`: `stringIndexFacts` (`0 ≤ i`, `i + 1 ≤ |s|`, `i ≤ 2^32 − 2`) give `unitFacts` (`|y| = 1`) |
| Concat | `{true} y = s + s' {|y| = |s| + |s'|}` | `concatAtoms`, where both operands are string slots | `Derivation.stringConcat`: premises `0 ≤ |s|` and `0 ≤ |s'|` give `concatFacts` |
| View-Length | `{true} y = b.length {y = |b|} : ∅` | the native contract of `length` on a typed array | none |
| View-Read | `{0 ≤ i < |b|} y = b[i] {b[i] ≐ y} : ∅` | the native contract of the element read | none |
| View-Write | `{0 ≤ i < |b|} b[i] = v {b[i] ≐ conv_t(v) ∧ Q_{≠i}} : {values: grow}` | `ViewWrite` (`Semantics/ElementWrites.lean`), `ExactWrite` for a format storing the value unchanged | none |
| View-Write-Any | `{true} b[i] = v {true} : {values: grow}` | `ViewWrite` | none |

Differences between Lean and the paper's rows, left as they are:

- **Concat.** B's constructor takes `0 ≤ |s|` and `0 ≤ |s'|` as premises; the
  row's precondition is `true` (a string's length is non-negative by the
  term's definition).
- **Str-Read.** B states `i ≤ 2^32 − 2` where the row states `i < N`,
  `N = 2^32 − 1`: the same bound. A states nothing of a code unit's length.
- **Str-Length.** B also states `y` a safe integer, which the row's
  `y = slen(s)` implies by the meaning of a defined term.
- **View rules.** The paper's status tag reads them as assumed contracts of
  the host. B has no rule for them, and A reads them through the native
  contracts and `ViewWrite`/`ExactWrite`, not as linear rules of a step.

## Decisions

- **The view rules stay assumed** (the owner's decision). Their datum
  entries state the trust in place of a proof: each names the native
  contract it rests on, and the export and the rendered rows show it as
  assumed.
- **The string rules are proved**, against the calculus's string
  operations: a string's length (`strLengthOf`), its element read
  (`codeUnitAt`) and the concatenation `binop .add` gives two strings.
- **The datum states the paper's rows; the pass's and the derivation's
  string rules stay as they are** (the owner: change neither side). Each is
  related to its datum entry by a theorem: the derivation's conclusion is
  the entry's conclusion substituted, under premises that entail the
  entry's (B's Concat takes two more); the pass's atoms on a string's length
  read and on a concatenation are the entry's conclusion substituted. The
  differences are recorded in [B against the paper](b-against-the-paper.md).
- **The pass gains no Str-Read producer.** A producer is added where a
  refusal of a program calls for it (CLAUDE.md, "deciding what a refusal
  calls for"); no case shows a refusal on a code unit's length, and the
  datum's entry and the derivation's rule state the row without it.
- **The derivation gains no view rules**: the view rules are assumed, and an
  assumed contract is read where the pass reads it, at the native's call.

## The generalisation the datum needs

## The generalisation the datum needs

1. **Terms by measure.** A fact's term is a variable with a measure: its
   value, its string length (`strLength`), its typed array's length
   (`view`) or its array's length. Lean keeps the three length terms
   distinct; the paper's renderer writes each as `|x|` (`\len`), the
   variable's sort, stated in the row's sort column, telling them apart.
   ARITHMETIC.md keeps the implementation's names.
2. **Sorts.** `Num`, `SafeInt`, `String`, `Array` and `TypedArray`, with
   the format `t` of a typed array a parameter of the rule.
3. **The step.** An operation beside `binop`: a string's length read and
   element read, a typed array's length read, element read and element
   write. A proved rule's soundness is stated over the operation's values:
   for operand values in their sorts meeting the premises, the value the
   calculus's operation gives (`binop`, `strLengthOf`, `codeUnitAt`) lies in
   the result's sort and meets the conclusion; `arithBits` is its instance
   for `binop` on numbers. An assumed rule has no such statement and names
   its contract.
4. **Conclusions beyond linear facts.** An element atom `b[i] ≐ y` and
   `b[i] ≐ conv_t(v)`, and the frame `Q_{≠i}`, each an atom of the
   assertion language with its own interpretation.
5. **Effects.** Each rule's effect (`∅`, `{values: grow}`), exported and
   rendered in the effect column.

## Decided above

The open decisions of the first version (the view rules' soundness, B's
view rules and A's Str-Read) are settled under "Decisions".
