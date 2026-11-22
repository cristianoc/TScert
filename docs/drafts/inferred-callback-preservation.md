# Inferred callback preservation

[Read the paper (PDF)](inferred-callback-preservation-note/inferred-callback-preservation.pdf) ·
[LaTeX source](inferred-callback-preservation-note/note.tex)

## The existing mechanism this extends

`writeInterface` replays the marked declaration using supports found by
its annotation-driven walk. `check` resolves the supplied literal and
checks its effect against those demands. For a cursor walk that calls its
visitor just before reading `xs[c.i]`, the demand includes the length of
`xs`. A literal that pops from `xs` fails that check. An empty literal
passes it, but the walk's declaration alone cannot be used with an
arbitrary callback of the same TypeScript arrow type.

The direct caller now plans both declarations in one frozen store.
`certifyLinked` reads the successful publication and caller scan, checks
the source identity and the actual module slot, and builds the ordinary
expression certificates up to the direct call with that slot masked.
`TailSite.safe` applies the empty literal's operational preservation
proof through the producer's dispatch and the caller's direct return.
The worker may mark this caller verified without a separate unconditional
verdict for the producer. Selecting the entire file still reports the
producer independently.

### What this duplicates

The caller reads the same code inference and origin computation used by
the interface scan to construct its dependent prefix certificate. It has
no second implementation of effect inference, origin transfer, subtype
checking or program execution. The source linkage uses the ordinary
receiverless code from `FilePlans.moduleCodes` and the ordered capture
rows from `FilePlans.captures`. It resolves local names to the file
front's declaration indices. The model's ordinary module closure and
capture operations evaluate that checked layout. The
executable restriction and its proof are in
[CallbackLinkedEntry](../../lean/Verification/Source/Claims/CallbackLinkedEntry.lean).

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
