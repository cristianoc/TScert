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
- **The pass gains no Str-Read producer in this work.** The census orders
  the work on the pass's producers (CLAUDE.md, "choosing the gap cases to
  work on"), and no case or census reason asks for a code unit's length;
  the datum's entry and the derivation's rule state the row.
- **The derivation gains no view rules in this work.** The datum states the
  view rules as assumed contracts, naming them; a derivation rule
  conditional on those contracts is possible and outside this work.

## The datum, generalised

The arithmetic datum's types, extended to state every row of the three
displays; each extension is the general form of what it states.

1. **Operations.** A rule's operation is one of the calculus's steps that
   give a value of their operands: a binary operator (`binop`, the
   arithmetic rows and Concat), a string's length read (`strLengthOf`), a
   string's element read (`codeUnitAt`), and a typed array's length read,
   element read and element write (`%ByteLength%`, `%ByteAt%`,
   `%ByteSet%`). An operation has up to three operands (`left`, `right`,
   `third`: the written value of an element write) and a result.
2. **Sorts.** An operand or the result is `Num`, `SafeInt`, `String`,
   `Array` or `TypedArray`. A `String` is a string whose UTF-16 length is
   at most `M` (`strLengthOf` is defined), a `TypedArray` one of format `t`,
   a parameter of the rule. A constant is a `SafeInt`.
3. **Terms by measure.** A fact's term is a variable's value or its length,
   `|x|`: the string's UTF-16 length, the typed array's fixed length, or the
   array's spine length, as the variable's sort says. Lean keeps the three
   length terms distinct; the paper's rows write each as `|x|`, the sort
   column telling them apart; ARITHMETIC.md keeps the implementation's
   names.
4. **Atoms beyond linear facts.** A conclusion may state an element atom,
   `b[i] ≐ y` or `b[i] ≐ conv_t(v)`, `conv_t` the format's conversion
   (`ViewFormat.conv`) and `≐` the model's equality of numbers, and the frame
   `Q_{≠i}`: every other index of the collection reads after the step what
   it read before. The frame is the rule's local postcondition; the effect
   (below) bounds what other typed arrays over the same bytes read.
5. **Effects.** Each rule states its effect in the grammar of Paper I's
   effects: `∅`, or entries `r : δ` with `r` among `st`, `vw`, `val`,
   `π.spine`, `π.cells`, `π.f`, `π.fields` and `δ` among `keep`, `init`,
   `scalar`, `grow`, `any`.
6. **Trust.** A rule is proved, its soundness a theorem whose term the
   export checks against its entry, or assumed, naming the native contracts
   it rests on (`%ByteLength%`, `%ByteAt%`, `%ByteSet%`, the latter through
   `ViewWrite` and `ViewAssign`/`WriteAt`, which state the conversion at the
   view's format for any number).
7. **Soundness.** For a proved rule, one statement by its operation, over
   successful evaluation: for operand values in their sorts meeting the
   premises, where the operation gives a value (Concat: `binop .add` of two
   strings gives one only where the sum of their lengths is at most `M`;
   the step throws otherwise, and the row's postcondition is for a normal
   return), that value lies in the result's sort and meets the conclusion.
   Str-Length connects the string's measure to the numeric result, a safe
   integer; Str-Read takes a `SafeInt` index below `|s|` and `N`, where
   `codeUnitAt` gives a string of UTF-16 length one, the model's surrogate
   replacement included. `arithBits` is the binary operator's instance on
   numbers.

## The bridges

The derivation's string constructors and the pass's atoms stay as they
are. The existing bridges (`concatAtoms_iff`, `lengthReadAtoms_iff`) are
extended to the datum's entries: each states that, for the operands' sorts
with their measures defined and the operation's evidence, the entry's
substituted premises are entailed by the constructor's (B's Concat adds two,
`0 ≤ |s|` and `0 ≤ |s'|`, which its operands' defined lengths give), and the
entry's substituted conclusion holds where the constructor's or the pass's
atoms do, Str-Length's `safeFact` included. The pass's theorem is stated
of the `linearAtoms` branch itself.

## The renderer

The export carries every field above. The renderer writes the paper's three
displays (the arithmetic steps, the string steps, the typed array's steps)
as generated sections, each row with its sort column, its triple and, for
the typed array's steps, its effect column, and the implementation's
documentation's matching sections (ARITHMETIC.md for strings,
SOURCE-CONTRACTS.md for the typed array's natives), and marks an assumed
rule with its contracts. In a display with an effect column, a rule's sorts
take a row of their own above its triple, so that the rows fit the page.

