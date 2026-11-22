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

The implementation PR reports callback checks as experimental.
The [soundness companion](https://github.com/cristianoc/TScert/pull/337)
adds the verified worker, which reuses one frozen type store. `certifyProducer` verifies the
producer under its inferred callback requirements. `certifySourceProducer`
checks the fixed signature and actual module binding at publication.
`certifyModuleCaller` reads that publication and verifies the caller.
The paper's fresh-array collector verifies. Its aliasing variant is
refused at its callback.

### What this duplicates

The caller's certificate uses the ordinary code inference and origin
computation. Source linkage uses the receiverless code from
`FilePlans.moduleCodes` and the ordered capture rows from `FilePlans.captures`.
The assertion projection checks the paths to every original caller
assertion with an opaque producer capture. It runs the ordinary graph
checker on that projection. The producer's body is used to certify its
publication, and the caller's check consumes the published contract.

The paper's **Restrictions checked by the worker** section names the
executable scope checks in Lean. Other cases, including the Pretext
adapter and cross-module verification, are described with their
experimental source results.

- [Worker scope and routing](../../lean/Verification/Source/RequestCli.lean)
- [Producer](../../lean/Verification/Source/Claims/CallbackInferencePlan.lean)
- [Provenance and escape scan](../../lean/Verification/Source/Claims/CallbackOrigins.lean)
- [Closure effects](../../lean/Verification/Source/Claims/CallbackEffectInference.lean)
- [Interface consumer](../../lean/Verification/Source/Claims/CallbackInterfaceCheck.lean)
- [Source regression](../../tests/callback-preservation.mts)
- [Lean controls](../../lean/Verification/Tests/CallbackPreservationControls.lean)
