# Arithmetic rules from actual primitive execution

The existing mechanisms are shared SafeIntegers, arithV, Steps and B's
PrimitiveRun/Triple/Effects. Extend these; no numeric evaluator or native
contract is introduced. The current paper is the arithmetic paragraph of
[tolerant-frames-note/note.tex](tolerant-frames-note/note.tex).

A known pure reduction to a valid source value determines every completed
primitive run by deterministic prefix cancellation. It cannot raise, its heap
is unchanged, and its result binding is exact. The command triple chooses the
positive restricted world corresponding to the actual primitive count. The
computed result relation is about the entry environment/state; no arbitrary
semantic predicate is assumed to survive budget restriction. Empty effects
follow from the unchanged heap.

For Mask, a nonnegative signed-31-bit mask bounds intAnd at every signed first
operand, including negative ToInt32 results. Encoding gives a safe nonnegative
result no greater than the mask. For nonnegative safe input x, use the existing
small-input theorem below 2^31; above it, the result is already less than x.
For Or, natural bitwise inclusion gives both lower bounds, binary division
proves the sum upper bound, and bit-width preservation keeps the result below
2^31. The exact arithV rule connects these integer results to command execution.

Result-name freshness is needed when expressing an entry operand in the
current environment: fresh binding leaves its value unchanged. Add syntax
corollaries through safeIntOfBits_complete, retaining signed-zero distinction.
The general semantic command rules and those current-state corollaries are
separate from the old restricted finite Parity certificates.

Astra independently reviewed the numerical and pure-execution prototypes before
integration. It found no soundness blocker and required the entry/current and
freshness distinction to stay explicit. Shift-count normalization for every
paper integer constant remains separate; SafeInt count alone is narrower.
