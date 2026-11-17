# Implementation rules, paper rules, and their correspondence

The basis of the work that relates the verifier to the paper
[Tolerant frames](tolerant-frames-note/note.tex). Its status is the row
"Implementation rules and paper rules" of [WORK.md](../../WORK.md#status).

## Three things

**A. The implementation rules.** The rules acceptance applies: the
deciders of the single pass, each with its own soundness theorem, which
the acceptance theorem `PassUnit.mode8Accepted_sound` reads. They are
implicit to different degrees: a rule is stated by its code, and its
documentation ([PROGRAM-TYPING.md](../PROGRAM-TYPING.md),
[FOOTPRINTS.md](../FOOTPRINTS.md), [ARITHMETIC.md](../ARITHMETIC.md) and
the comments of the deciders) states it as far as it does.

**B. The paper rules.** The Lean statements of the paper's definitions and
rules: explicit, documented, and close to the paper, though not equal to
it. Acceptance does not apply them; the paper's status tags cite them.

**C. The correspondence between A and B.** Partial. For a rule of A, the
rule of B it agrees with, how far, and where they differ, is to be
studied.

## The first item: B

Clarity on B, in three parts:

1. **Where it lives.** The Lean modules, definitions and theorems that are
   B, and what each states.
2. **How far it matches the paper.** For each definition and rule of the
   paper: the statement of B that is it, and whether it is equal, narrower
   or broader, with the difference stated; or that B has none.
3. **How to make it identifiable.** A refactoring that places B where the
   source tree shows it as B, apart from A, and states what of B other
   code reads.
