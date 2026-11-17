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
| Str-Length | `{true} y = s.length {y = slen(s)}` | `linearAtoms` on `lenOf` of a string slot: `int(y)`, `y = strLength(s)` | `Derivation.stringLengthRead`: `lengthReadFacts`, `y` a safe integer and `y = |s|` |
| Str-Read | `{0 ≤ i < slen(s) ∧ i < N} y = s[i] {slen(y) = 1}` | none: no producer states a code unit's length | `Derivation.stringRead`: `stringIndexFacts` (`0 ≤ i`, `i + 1 ≤ |s|`, `i ≤ 2^32 − 2`) give `unitFacts` (`|y| = 1`) |
| Concat | `{true} y = s + s' {slen(y) = slen(s) + slen(s')}` | `concatAtoms`, where both operands are string slots | `Derivation.stringConcat`: premises `0 ≤ |s|` and `0 ≤ |s'|` give `concatFacts` |
| View-Length | `{true} y = b.length {y = view(b)} : ∅` | the native contract of `length` on a typed array | none |
| View-Read | `{0 ≤ i < view(b)} y = b[i] {b[i] ≐ y} : ∅` | the native contract of the element read | none |
| View-Write | `{0 ≤ i < view(b)} b[i] = v {b[i] ≐ conv_t(v) ∧ Q_{≠i}} : {values: grow}` | `ViewWrite` (`Semantics/ElementWrites.lean`), `ExactWrite` for a format storing the value unchanged | none |
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

## The generalisation the datum needs

1. **Terms by measure.** A fact's term is a variable with a measure: its
   value, its string length (`strLength`), its typed array's length
   (`view`) or its array's length. Lean keeps the three length terms
   distinct; the paper's renderer writes each as `|x|` (`\len`), the
   variable's sort, stated in the row's sort column, telling them apart.
   ARITHMETIC.md keeps the implementation's names.
2. **Sorts.** `Num`, `SafeInt`, `String`, `Array` and `TypedArray`, with
   the format `t` of a typed array a parameter of the rule.
3. **The step.** An operation of the calculus beside `binop`: a string's
   length read, a string's element read, a typed array's length read,
   element read and element write. The soundness statement becomes one over
   the step's relation (`Step` from the entry heap and environment to the
   result and the exit heap), of which `arithBits` is the instance for
   `binop`.
4. **Conclusions beyond linear facts.** An element atom `b[i] ≐ y` and
   `b[i] ≐ conv_t(v)`, and the frame `Q_{≠i}`, each an atom of the
   assertion language with its own interpretation.
5. **Effects.** Each rule's effect (`∅`, `{values: grow}`), exported and
   rendered in the effect column.

## Open decisions

- **The view rules' soundness.** Proving View-Read, View-Write and
  View-Write-Any against the calculus's typed-array model turns assumed
  contracts into theorems; stating them in the datum without proofs keeps
  them assumed. The paper's status tag follows either choice.
- **B's view rules.** B has none; the datum's rule would be applied by a
  new `Derivation` constructor for steps of the view operations, and A's
  native contracts related to it by a bridge theorem.
- **A's Str-Read.** A has no producer for it: either A gains one from the
  datum, or the row stays B's only, as the parity table states.
