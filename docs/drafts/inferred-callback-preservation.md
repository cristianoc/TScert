# Inferred callback preservation

[Read the paper (PDF)](inferred-callback-preservation-note/inferred-callback-preservation.pdf) ·
[LaTeX source](inferred-callback-preservation-note/note.tex)

The paper specifies how the experimental source checker infers effect
requirements for preserving heap-dependent refinements across callback
invocations. It gives rules for selecting and retaining facts, replaying
the producer, checking the caller, and forwarding a requirement. Its
pseudocode follows the executable Lean implementation.

The source regression tests nonempty requirements inferred from
`InferPreserves<T>`. It exercises captures, ordinary callback arguments,
direct forwarding, and module boundaries. The paper includes a reduced
Pretext example with parallel arrays and an adapting visitor. Its guarded
raw walker infers a length-preservation requirement. A direct cache write
satisfies the requirement. An append through the same array is rejected,
and the prototype cannot check the fresh-array append or the adapting
closure with its existing rules. The paper states the source soundness
target as a conjecture.

- [Producer](../../lean/Verification/Source/Claims/CallbackInferencePlan.lean)
- [Provenance and escape scan](../../lean/Verification/Source/Claims/CallbackOrigins.lean)
- [Closure effects](../../lean/Verification/Source/Claims/CallbackEffectInference.lean)
- [Interface consumer](../../lean/Verification/Source/Claims/CallbackInterfaceCheck.lean)
- [Source regression](../../tests/callback-preservation.mts)
- [Lean controls](../../lean/Verification/Tests/CallbackPreservationControls.lean)
