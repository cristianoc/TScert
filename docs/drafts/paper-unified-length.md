# Unified lengths in the paper grammar

The existing mechanism is the shared partial readers `lengthOf`, `viewLengthOf`
and `strLengthOf`. B reuses them; A's `HeapKnowledge.Term.Kind` and its meaning
remain unchanged. The specification is the terms paragraph of
[Tolerant frames](tolerant-frames-note/note.tex).

## Meaning and syntax

[LengthReading.lean](../../lean/Verification/Paper/TolerantFrames/LengthReading.lean)
selects the reader from the runtime value: a plain object uses its array-spine
reader, a view descriptor its fixed-length reader, and a string its UTF-16
reader. A plain object without an array spine has undefined length. Selection
precedes reading, so a malformed view cannot fall back to an array. Callable
objects and other values have undefined length. No world is consulted.

Both grammars have canonical `Term.lengthPath`, `Term.lengthElement` and
`BodyTerm.lengthProject`. Element/project suffixes may be empty; body length
projection is unshifted. The older explicitly sorted readers remain auxiliary
encodings. [PaperTermForms.lean](../../lean/Verification/Paper/TolerantFrames/PaperTermForms.lean)
checks the paper's term forms recursively through indices, bounds, free body
terms, old, quantifiers, implications and modalities. This is a term-form
predicate, separate from scope, declared-region admission and receiver typing.

## Sound transport and qualified bridges

Renaming, lexical scope, two-state admission and program-map agreement include
the new constructors. Old reads the entire term and nested index at entry.
The complete modality-free all-keep support and heap-only world independence
include canonical lengths. Current-state selected-path substitution, recursive
integer definedness/consequence and body instantiation preserve their meaning.
Instantiation also preserves the paper-term predicate.

Every defined length is between zero and M; array lengths retain the stronger
N bound. `Derivation.canonicalLengthRange` integrates the common bound through
the existing derivation soundness mechanism. This is not complete Definition 23
integration or automatic proof-search completeness.

[LengthBridges.lean](../../lean/Verification/Paper/TolerantFrames/LengthBridges.lean)
proves equality of canonical and sorted Option results with explicit successful
receiver/element/suffix reads and runtime-category evidence. The final reader
may be undefined. These are not unconditional equivalences or proofs that a
declaration selects a runtime category. Old sorted exactness/growth theorems
remain restricted to their explicitly sorted syntax.

## Remaining correspondence boundaries

Inst and Prefix cover canonical lengths, including empty element suffixes.
Their element-free receiver interpretation remains an owner decision. Empty
also needs the paper's declared collection-path restriction connected to runtime
receiver semantics: unified length definedness alone includes strings.
Mixed array/string support unions require the separate region-admission
decision described in [correspondence obligations](paper-alignment-obligations.md).
No support table or mathematical statement is changed to resolve those items.
The owning status and exact validation are in [WORK](../../WORK.md#status) and
the [validation record](paper-alignment-validation.md).
