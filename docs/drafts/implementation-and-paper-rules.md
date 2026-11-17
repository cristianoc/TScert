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

**B. The paper rules.** The definitions and rules of the paper. Their
formalisation in Lean is a first infrastructure: statements of part of
the paper, equal to it in places and narrower in others, which the
paper's status tags cite and acceptance does not apply. It may be brought
to exact correspondence with the paper, or deleted.

**The shared model.** Worlds, admissible transitions, heaps, regions,
changes, effects, support, respect and the frame theorem: definitions
both A and the formalisation of B read.

**Separable.** The formalisation of B is deletable without touching A:
A imports the shared model only; the formalisation imports the shared
model and A; the existing bridges between A and B belong to the
formalisation.

**C. The correspondence between A and B.** Partial. For a rule of A, the
rule of B it agrees with, how far, and where they differ, is to be
studied, first where pretext's functions rely on it. It has two
directions:

- **from A to B:** what A accepts is derivable by B's rules;
- **from B to A:** what B derives, A accepts.

Each is explored informally first: by examples and by reading the two
side by side, not by a theorem.

## The first item: B

Clarity on B, in three parts:

1. **Where it lives.** The Lean modules, definitions and theorems that are
   B, and what each states.
2. **How far it matches the paper.** For each definition and rule of the
   paper: the statement of B that is it, and whether it is equal, narrower
   or broader, with the difference stated; or that B has none.
3. **How to make it identifiable and separable.** A refactoring that places
   the formalisation of B in its own part of the source tree, moves what A
   reads of it into the shared model, and leaves no import from A into
   it.

## Where C is met

A new pretext case meets C. Supporting a pattern of
[Tolerant frames II](tolerant-frames-2-note/note.tex) starts with its
derivation in the paper; whether A accepts the program is then a question
of C, from B to A. Where A does not accept it, the way forward is decided
with the owner: bring the aspects of A and B involved closer together, or
another route.
