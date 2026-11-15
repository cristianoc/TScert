# Effects of commands

## The existing mechanism this extends

This design extends the following mechanisms:

| Concern | Lean definitions | Owning document |
|---|---|---|
| Effects and their action | `Footprints.Footprint`, `Region.mem`, `Change.Holds`, `Post`; `TolerantFrames.Action` | [Footprints](../FOOTPRINTS.md) |
| Entry-relative composition | `RebaseEvidence`, `RebaseOk`, `rebaseAll`, `Post.compose_at` | [Footprints](../FOOTPRINTS.md), [the note](tolerant-frames-note/note.tex), Seq-Eff and Fresh-Eff |
| Callable guarantees | `CallEffects.Effect`, `ExitSpec`, `PromiseWith`, `Effect.within` | [Source contracts](../SOURCE-CONTRACTS.md) |
| Checked consequences | `Parity.Formula`, `TwoState`, `OperationPost`, `checkDerivation` | [The note](tolerant-frames-note/note.tex), Entry and Frame |
| Recorded visits and graph composition | `SinglePass.VisitRecord`, `StepGrades`, `recordsAdmit`, `SinglePassClose.run_rebound_of_records` | [Source elaboration](../SOURCE-ELABORATION.md) |
| Typed-array writes | `Kinds.ViewWrite.frame_iff`, `ViewAssign`, `ExactWrite` | [Footprints](../FOOTPRINTS.md), View-Write in the note |

The target has one effect representation and one interpretation: each completion has a finite list of region/change entries and a conjunction of two-state postconditions. A checked command supplies this information before comparison with an enclosing bound.

The declarations below are **proposed interfaces and proof obligations**, not compiled Lean. Existing theorem names above identify available foundations; statements marked NEW require proofs.

## Representation

### Regions and closed effects

Reuse `Footprints.Footprint := List (Region × Change)` and its heap-only interpretation. The stated region language contains:

- The three class regions: values, arrays and views.
- A store, store-plus-cells, or field at a path rooted at a call position.
- The own value locations of such a path, subject to the expressiveness issue below.

Call position `0` is the receiver; position `i + 1` is argument `i`. Frame paths refer to the entry. Postconditions distinguish entry and exit explicitly; exit position `0` is the returned or thrown value.

The note’s `π[*]` expands to the store entry and its element-cell entry, with the same change. Existing `pathElems` alone denotes only the cells. Selector unions expand to entries for their constituent classes. Internal `.all` expands to the three classes on allocated locations.

**An expressiveness correction is necessary.** Today `receiverOwn` selects all own value locations, including fields not enumerated by a structural contract. A finite list of named `π.f` regions cannot generally express that set. Enumerating declared fields requires a proof that they exhaust the runtime own locations.

The smallest exact extension is a region `π.own`, restricted to value locations, with the existing meaning of `.inCls (.pathOwn …) .values`. Add this general region to the note. If the stated language must contain *only* the regions currently printed there, arbitrary `receiverOwn` contracts cannot be translated exactly; some contracts must instead be widened or refused. That is a semantic change, not a serialization refactor.

```lean
-- CHANGED from { value, store }.
structure Footprints.Closed where
  value : Change
  array : Change
  view  : Change

-- CHANGED: one entry per disjoint content category.
def Closed.fp (c : Closed) : Footprint :=
  [(.cls .values, c.value),
   (.cls .arrays, c.array),
   (.cls .views,  c.view)]

-- NEW: exact normalization for class-only effects.
def Footprint.closed? : Footprint → Option Closed

-- NEW: conservative class bound for any effect.
def Footprint.close : Footprint → Closed

-- NEW; quantified over well-formed admissible states.
theorem closed?_sound
    (hc : Φ.closed? = some c) :
    Action Φ ρ s s' ↔ Action c.fp ρ s s'

theorem close_sound :
    Action Φ ρ s s' → Action Φ.close.fp ρ s s'
```

These are three **components**, each holding a change, not three possible effects. Normalize changes according to their action on each category. In particular, the existing value normalization sends `grow` to `scalar`; store normalization sends `init` and `scalar` to `keep`. Prove the corresponding view normalization against the tagged representation.

`Closed` remains a computational projection for class-only joins, widening and fast support checks. A general effect is never reconstructed from its closed projection. `closed?` gives equivalence; `close` gives only inclusion.

For old closed effects, the exact embedding is `⟨value, store, store⟩`.

### Exit specifications and postconditions

```lean
-- CHANGED from List HeapKnowledge.IndexFact.
structure CallEffects.ExitSpec where
  frame   : Footprints.Footprint
  ensures : List Parity.Formula

-- CHANGED: replaces closed, onThrow, receiverStore, receiverOwn,
-- receiverGrows, elementWrite and the separate regions field.
structure CallEffects.Effect where
  exits    : Exits ExitSpec
  promise  : Option TypePromise
  requires : Option ElemPred
  pre      : List HeapKnowledge.IndexFact

-- NEW: all formulas in ensures hold in the same two-state interpretation.
def ExitSpec.Holds
    (arena : AssertionArena) (q : ExitSpec) (s : TwoState) : Prop :=
  EffectAction q.frame s.beforeEnv s.before s.after ∧
  ∀ F ∈ q.ensures, Parity.Holds arena s F

-- CHANGED from the normal-only frame.
def Effect.within
    (e : Effect) (c : Completion) (ρ : Env) (h h' : Heap) : Prop :=
  Footprints.Post (e.exits.get c).frame ρ h h'
```

`fresh`, `freshObject`, `elements` and the old `ensures` become normal postconditions. `promise` retains its role in the result contract; preconditions remain preconditions.

Use the existing assertion arena and two-state formulas. Factor their foundational syntax and interpretation below `CallEffects`: importing the current `ParityDerivations` directly into `CallEffects` would create a dependency cycle through its call-specific operational posts.

The postcondition language must express the guarantees being removed:

- Freshness of the result’s store or own locations.
- Conditional element predicates.
- Append contents and length, including the correspondence with actual arguments.
- View update contents, conversion, invalid-index behavior and unchanged receiver indices.

Extend the shared assertion language with the required store observations and update expressions. Give these expressions ordinary equality, definedness and quantification semantics. Do not introduce a postcondition constructor whose only meaning is “the old `elementWrite` variant holds.”

`ViewAssign` and `ExactWrite` remain useful semantic lemmas. The latter follows from the general assignment post under its format, index and value premises. `Kinds.ViewWrite.frame_iff` supplies the independent `{views: grow}` frame.

An exact primitive post is exact about the observations specified by that operation. It is not necessarily a strongest postcondition describing the entire heap. At a host call, the post is the assumed contract’s guarantee.

### JSON

The serialized form of an effect is [the serialized effect](#the-serialized-effect).

## Command summaries and composition

A local summary is attached to the successful checking visit that establishes it. Its construction receives the checked rule, entry knowledge and selected contracts, but no enclosing effect bound.

```lean
-- NEW.
abbrev CommandSummary := Exits ExitSpec

-- NEW: evidence tied to the particular checked visit and its entry.
structure LocalCertificate (v : CheckedVisit) where
  summary : CommandSummary
  sound   : LocalSummarySound v summary

-- CHANGED from StepGrades' lists of Closed alternatives.
structure VisitRecord where
  label       : Nat
  certificate : LocalCertificate checkedVisit
  -- Existing identity/context data ties checkedVisit to this visit.

-- NEW: computation from checked local information.
def summarizeStep :
    CheckedVisit → Except LocatedError (LocalCertificate checkedVisit)

-- NEW: certified entry-relative composition.
def composeSummary :
    CommandSummary → CommandSummary → CompositionEvidence →
    Except LocatedError CommandSummary

-- NEW: finite graph summary, including loop certificates.
def summarizeBody :
    CheckedGraph → VisitRecords → CompositionEvidence →
    Except LocatedError CommandSummary

-- NEW: a separate comparison, after inference.
def checkBound :
    AssertionContext → CommandSummary → CommandSummary →
    BoundEvidence → Bool
```

`CheckedVisit`, `CompositionEvidence`, `LocalSummarySound` and `BoundEvidence` above are interface parameters: they package the existing checked step, rebasing evidence and checked derivations, rather than a second checking pass.

The obligations are:

```lean
-- NEW.
theorem summarizeStep_sound
    (h : summarizeStep v = .ok cert) :
    LocalSummarySound v cert.summary

theorem composeSummary_sound
    (ha : CommandSummarySound a A)
    (hb : CommandSummarySound b B)
    (hev : CompositionEvidence.Valid ev)
    (h : composeSummary A B ev = .ok C) :
    CommandSummarySound (sequence a b) C

theorem summarizeBody_sound
    (hv : RecordsSound graph records)
    (hev : CompositionEvidence.Valid ev)
    (h : summarizeBody graph records ev = .ok S) :
    CommandSummarySound graph S

theorem checkBound_sound
    (hc : checkBound K inferred stated ev = true) :
    SummaryEntails K inferred stated

-- CHANGED from admission of closed grades.
theorem recordsAdmit_sound :
    RecordsSound graph records →
    recordsAdmit records bound evidence = true →
    GraphWithin graph bound

-- CHANGED conclusion: both entry-relative exit specifications.
theorem run_rebound_of_records :
    SuccessfulCheckedRun run →
    RecordsSound run.graph run.records →
    BodySummarySound run run.summary
```

`CommandSummarySound` says: every finite completion on the deterministic execution justified by the checked command satisfies that completion’s action and postconditions. It includes the existing safety obligations. It changes neither reduction nor `Safe`.

Composition follows the control-flow exits:

| Composite exit | Contributing executions |
|---|---|
| Sequence, normal | First normal, then second normal |
| Sequence, exceptional | First exceptional; or first normal, then second exceptional |
| Handler, normal | Protected command normal; or protected command exceptional, then handler normal |
| Handler, exceptional | Protected command exceptional, then handler exceptional |

Rebase each later frame to the composite entry and apply `Post.compose_at`. Join alternative executions by an upper bound. Keep the intermediate state explicit in the semantic proof; derive exported postconditions through checked consequences. Conjoining two posts while identifying their different `old` states is unsound.

Fresh-Eff is part of rebasing. It removes a store entry only when that store lies beyond the composite entry mark. It does not erase old cells reached through a fresh array, or the class-wide view effect of writing through a fresh view.

A loop certificate establishes:

1. Each recorded prefix is bounded relative to the iteration entry.
2. The back edge preserves the invariant and transports names.
3. Iteration effects compose into the chosen loop summary.
4. Every normal and exceptional departure has the corresponding entry-relative summary.

Rigid class effects provide a terminating widening. Regional precision requires checked path stability or rebasing evidence. A body’s final postcondition alone cannot justify facts used inside the loop.

The function’s inferred **mutation effect** is its body frame, rebased to the call positions. Exported postconditions are checked consequences in the interface scope. Fresh-result and returned-callable obligations remain independently established.

## Replacing the deciders

| Decider | Present decision | General replacement |
|---|---|---|
| `Synthesis.wrote`, `throwWrites` | Accumulate value/store grades; classify unbounded throws; widen receiver and element-write cases | Propose per-exit entries for each operation, compose along control flow, and rebase using provenance. Acceptance uses the checked visits’ summaries. An exceptional path includes its entire preceding prefix. |
| `PassProposals` | Stand-ins, recursion assumptions and memo entries carry `(Closed, onThrow)` | Carry complete exit summaries. A recursive proposal is accepted only when each body exit entails its assumed specification. Widen frames by region inclusion; weaken proposed posts when necessary. Memo keys include both exits, posts and referenced assertions. |
| `GraphCode.selectedWithinAt` | Compare the coarse footprint; separately allow receiver-own changes or a fresh receiver store | Instantiate the selected exit’s entries, rebase to the enclosing entry, discharge empty old regions by freshness, then check entry-wise coverage and change inclusion. No receiver-specific exemption remains. |
| `PromiseCalls.keepsHeap` | Empty coarse footprint and neither receiver exception | Check that the instantiated frame is included in the empty effect. Prove that success gives entry-heap prefix preservation. |
| `PromiseCalls.effectKept` | Select growth, receiver, argument-region and element-write branches | For each fact, check support/respect against every applicable effect entry, or derive it from Entry and the exact post. Apply independently to each completion. |

Entry-wise inclusion is a sound finite check, not a complete decision procedure for semantic implication. It uses category information, region containment, stability, separation and freshness evidence. Unknown containment fails or widens conservatively.

### Exact elaboration versus changed decisions

| Old field | Exact interpretation |
|---|---|
| `closed` | Three class entries, copying the old store grade to arrays and views |
| `regions` | Each argument path’s store at `any` |
| `receiverStore` | Receiver store at `any`, when `receiverOwn` does not take precedence |
| `receiverOwn` | Receiver own **value** locations at `any`; preserve its present precedence |
| `onThrow = true` | Exceptional frame equals the old frame; exceptional posts are empty |
| `onThrow = false` | Exceptional top and true |
| `ensures`, `fresh`, `freshObject`, `elements` | Corresponding normal postconditions |
| `receiverGrows` | Its complete growth and append guarantee, including preservation outside the receiver store |
| `elementWrite` | Its world-aware view frame plus its assignment/conversion postconditions |

The first six rows admit exact frame elaboration. The last two do **not** elaborate to entries alone.

Preserve simultaneous guarantees as conjunctions. Adding a tighter frame’s entries to a wider frame does not intersect the two effects: list concatenation permits either entry’s change.

Semantic equivalence does not establish identical verifier verdicts. The general checks can recognize preservation that today’s branches discard. Separating array and view effects, precise exceptional composition, general freshness elimination and consuming exact posts can genuinely change inferred effects and verdicts. Such changes require separate validation.

## Smallest buildable migration

**Order decided on 2026-11-15.** The decisions this section assigns to step 4
(the exceptional frame at throws, freshness, fact survival at calls, the
effect proposals, the assumptions of recursion) move onto the per-exit form
before step 3, so that the serialized format never carries or imitates the
fields they read. Step 3 then changes the format, and what remains of step 4
is the deletion of those fields and composition used by acceptance.

There are four integration steps. The first three preserve the interpretation of existing contracts; the fourth activates the general command analysis. Exact verdict preservation must be proved for each claimed refactor, rather than inferred from equivalent specifications.

### 1. Establish the common semantics behind the existing wire

**Files:** `Semantics/ClosedFootprints.lean`, `Footprints.lean`, `FootprintRebase.lean`, foundational `Parity*.lean`, `CallEffects.lean`, `ElementWrites.lean`; their proof dependents.

Introduce three-component `Closed`, the internal exit summaries, postcondition elaboration and the dependency split. The decoder continues accepting only the current JSON shape and elaborates it immediately.

**Obligations:** old/new contract equivalence on admissible states; closed normalization; substitution and scope preservation; complete append and view-post translations. Exceptional top equivalence is stated on admissible transitions, not arbitrary heap pairs.

**Gate:** Lean build and axiom check; targeted contract, receiver, regional and view cases; `make test` before committing.

**Verdicts:** unchanged. No precision improvement is activated.

### 2. Move consumers and record independent summaries

**Files:** `Programs/ExpressionEffects.lean`, `GraphCode.lean`, `PromiseCalls.lean`, `SinglePass.lean`, `SinglePassClose.lean`, argument-region modules; `Source/Lowering/Synthesis.lean`, `Source/Claims/PassProposals.lean` and their callers.

Consumers read the list representation. Add bound-independent local certificates and prove their connection to existing recorded grades. Implement the general inclusion and consequence checks.

Move an existing decider in this step only with an equivalence theorem over the old representable domain. A decider whose general replacement changes results belongs in step 4. Do not preserve its behavior by recognizing the old flags’ encoded pattern.

**Obligations:** decider equivalences where claimed; local certificate soundness; recorded-visit identity; both-exit transport; unchanged exhaustive certification and acceptance theorem.

**Gate:** Lean build; affected cases and forced-proposal controls; `make test` before committing.

**Verdicts:** unchanged for migrated acceptance paths. General machinery may be proved before its acceptance integration.

### 3. Change the serialized shape once

**Files:** `Source/EffectJson.lean`; effect-bearing fragment, claim and evidence readers/writers; all affected `tools/*.mts`, particularly declaration types, type mappings, compiler API, intrinsic/library declarations, host families and claim text; fixtures and field-name controls.

Switch every producer and consumer together. TypeScript produces explicit exit specifications equivalent to the preceding elaboration. Update every mapping, substitution, overload, equality and digest operation. Regenerate fixtures.

Remove the old wire decoder and its elaboration immediately. There is one accepted shape and no compatibility mode. Lean’s evidence/diagnostic JSON serializers also change; TypeScript is the front-end producer.

**Obligations:** encode/decode agreement; exact field and scope checks; mapping preservation of both exits and every post; contract equivalence with the preceding step.

**Gate:** TypeScript strict check, unchecked-source check, JSON field-name check, malformed-fragment controls and `make test`.

**Verdicts:** unchanged for equivalent current inputs. Old serialized documents are refused.

### 4. Integrate command composition and delete superseded decisions

**Files:** the consumer files from step 2; `Programs` local-certificate and composition modules; `Source/Claims/PassUnit*`; `Tests/AxiomCheck.lean`; affected cases and owning documentation.

Use the recorded local summaries for sequence, handler, loop and function inference. Replace the remaining flag-shaped decisions with the general checks. Connect the resulting certificates through `FunctionPlan.certify` to `PassUnit.mode8Accepted_sound`.

Delete `elementWrite` and `stores/assign/exact` metadata variants; `onThrow`, `receiverStore`, `receiverOwn`, `receiverGrows`; separate argument-region lists; `(Closed, Bool)` stand-ins; superseded `wrote`/`throwWrites` effect inference and preservation branches. Keep semantic view-update and append lemmas used by the common postcondition interpretation.

**Obligations:** composition and loop soundness; prefix certificates; checked recursive assumptions; inferred/stated implication; the exact CLI acceptance theorem covering every unit member.

**Gate:** Lean and TypeScript checks, forced-proposal and forged-fragment controls, targeted positive and unsafe negative cases, then `make test`. Run the prescribed pretext tier for affected arithmetic capability.

**Verdicts:** may change. Report each change against its cause; a reclassified expectation is not evidence of a closed goal.

A wholly verdict-preserving migration to the more general analysis is not guaranteed. Steps 1–3 isolate representation changes; step 4 owns the semantic integration.

## Changing the effect type

The effect type changes from its fields to its two exits by moving every
reader onto the exits first and changing the representation last. The
existing mechanisms are `Effect.schema` and `ExitSpec.Holds` for the
meaning, `FrameChecks` for frames, Entry and consequence for
postconditions, and `CommandComposition` for sequencing and rebasing.

### Readers and where each goes

| Kind of reader | Readers | Destination |
|---|---|---|
| Frame | `ExpressionEffects`, `GraphCode`, `ArgumentRegionCertificates`, regional preservation in `PromiseCalls` | the selected completion's frame, through `includedIn`, `boundBelow`, `keepsHeap` and rebasing evidence |
| Postcondition | freshness, elements, growth, append, exact write, index facts | Entry and consequence from the selected exit's `ensures`; a frame proves none of these |
| Scope and body | `below`, `belowRow`, `codeConditions`, `PassUnitCodes`, `PassUnitRealize`, `VariadicTyping` | scoped schemas, and certificates establishing every exported postcondition |
| Operation on effects | `drop`, `meet`, `covers`, `withoutActuals` | schema transformations with their entailment, substitution or conjunction theorems |
| Constructor and proposal | library contracts, `Lowering/Synthesis`, `ExitProposals`, `PassProposals` | both exits built directly; inference proposes them and body certification proves them |
| Serialization | `EffectJson`, writers of requests and claims, `Lowering/Types`, the TypeScript mappings and declarations, fixtures | one wire transaction |

A semantic reader does not recover an old field from a constructor's
pattern. `drop` belongs with substitution and consequence, `withoutActuals`
with forgetting, `meet` with conjunction and its independence condition,
`below` and `belowRow` with scope and body obligations; `codeConditions`
stays a check of code built on these, each exported postcondition of each
exit among those a run establishes, a membership whose consequence is proved
once (`Exits.exitPost_of_established`) and proves both exits of a body; `covers` is sufficient entailment of
both exits with variance of the result and the precondition. None of them
needs an inverse of the elaboration. `meet` is the conjunction of the two
schemas on each exit (`Exits.meet`, exact by `Exits.exitPost_meet`): where
the two frames state the same entries beside their class entries, its frame
is the meet of their class bounds with those entries (`frameMeet?`, exact by
`post_frameMeet`), so coverage reads the met closed bound; otherwise its
frame is the first's and the second's is a postcondition `.transition`.
Two signatures conjoin where their promise and preconditions are the same
(`Effect.sameResult`), and the conjunction is used through coverage
(`Effect.meetCovers`), which also checks what the conjunction's proof
reads of the two schemas: canonical transports on both, and the second's
exits reading the exit through its heap alone, so that its guarantee holds
at the first run's worlds (`Exits.exitHeapOnly`, `Exits.independent`).

Two questions about a frame's change have two projections. A conservative
reader of a call's change reads the closed bound above the frame
(`Effect.changeBound`, the frame's `Footprint.close`: every change the frame
admits is within it, `Effect.within_changeBound`); whether a frame admits
every change, which an async code's signature must, is decided by its class
bound being `⊤` (`Effect.admitsAll`, sufficient: `Effect.within_of_admitsAll`).
The class bound alone is no upper bound: entries over other regions add
changes it does not state.

Binding is the exact substitution where it is defined (`Exits.drop`), and
otherwise the total weakening `Exits.dropWeak`: the frame substituted, or its
closed bound where it names a saved position; the postconditions that
substitute, the others forgotten. Its exits follow from the schema's at the
longer call on both exits (`Exits.exitPost_dropWeak`) and equal the exact
substitution where that is defined (`Exits.dropWeak_of_drop`). A bound
signature is the target's exits weakened so, its promise counted after the
saved actuals and its preconditions (`Effect.drop`); binding keeps a
signature whose promise is about an actual past the saved ones and that
states no precondition (`Effect.keeps`).

A postcondition is read from the normal exit's postconditions by its
formula: a fresh result store (`freshStore 0`, `ExitSchema.freshResult`), a
fresh result object (`freshObject 0`, `ExitSchema.freshObjectResult`), the
receiver's elements where the result is `true` (`elementsWhen 0 true 1 R`,
`ExitSchema.elementsWhenTrue`) and the index facts at the exit
(`fact after 0 F`, `ExitSchema.facts`). The consequence a call draws from
each is its formula's meaning at the call (`Effect.callPost_fresh`,
`callPost_freshObject`, `callPost_elements`, `callPost_ensures`), read from
the exit's postconditions held at the call (`Effect.callPost_holds`). In
coverage a target's postcondition is implied by one of the source's
(`postImplies`, proved by `postImplies_sound`): the same formula, or the
receiver's elements at a predicate at most the target's (`ElemPred.le`).

### The eleven commits

Each is a green, buildable step.

1. The scope declarations move below callable and body typing (below),
   names and definitions unchanged; a signature's exits at a prefix of the
   actuals carry to the longer call by scope congruence.
2. `SafePostExcV.bind`, the bind induction keeping the thrown value in the
   exceptional clause, and its one-step `bind_value` specialization.
3. The semantic composition foundation (`Consequence`, `Rebases`,
   `Post.compose_rebases`) below body typing, and `Exits.compose_entry`
   (below); the rest body's invocation uses it in place of the round trip
   through the heap postconditions.
4. The schema operations with their semantic theorems, one operation per
   commit; each old operation is kept with a proved relationship to the new
   one until its readers move.
5. The frame deciders: the shared `FrameChecks` interfaces, then
   `ExpressionEffects` and `GraphCode`, then `ArgumentRegionCertificates`,
   then `PromiseCalls`.
6. The remaining Entry readers, then `below`, `belowRow` and body
   certification (`PassUnitCodes`, `PassUnitRealize`).
7. The proposals: `ExitProposals`, then `PassProposals`, `Synthesis` and the
   readers of requests and diagnostics. The exceptional prefix is kept
   through sequence and handlers.
8. The constructors, by semantic family: builders of schemas, each equal to
   today's elaboration.
9. The old wire as a datatype, with a decoder elaborating it into exits and
   a partial encoder writing only the effects it represents exactly;
   serialization goes through it while the representation is unchanged.
10. The pivot: `Effect` stores `exits`, `promise`, `requires` and `pre`;
    `schema` is a projection; the old fields and the proofs only the
    elaboration needs are deleted. A property every elaboration has and a
    decision reads is a check where the decision is made: a conjunction's
    independence and canonical transports (`Effect.meetCovers`), a rest
    body's exceptional exit stating no postcondition
    (`ProgramTyping.exportsEstablished`, `Exits.AllocStable`); a bound
    signature's exits are arena-free by construction
    (`Exits.dropWeak_arenaFree`).
11. The serialized shape changes once, across Lean, TypeScript and
    fixtures ([the serialized effect](#the-serialized-effect)); the old wire
    datatype and its encoder are deleted.

The walk bounds the prefix before an escaping throw by the normal bound
($`\Phi \sqsubseteq \Psi`$), a sufficient instance of Seq-Eff; tracking
the prefix's own effect, which a pure prefix may need where the declared
normal bound exceeds the exceptional one, is composition work after the
pivot.

The decisions the general checks make are not those of the old fields in
every case: after the representation forgets a distinction (with a normal
frame of top, `onThrow` changes no schema while `covers` distinguishes the
two), the decision follows the schema. A commit that changes a decision
lists each changed verdict with its cause.

### Exit composition for rest bodies

A body with a rest parameter runs after the allocation of its rest array.
Its exits, stated at the heap after that allocation, are carried to the
invocation's entry by composition: the frame by Seq-Eff and Fresh-Eff
rebasing, the postconditions by consequence.

```lean
theorem Exits.compose_entry
    (h₁ : EffectAction Φ (callEnv r args) s₀ s₁)
    (hr : Rebases Φ Ψ (callEnv r args) s₀.h
      (x.get c).frame (callEnv r args) s₁.h)
    (hle : Footprint.le cl (Φ ++ Ψ) (y.get c).frame = true)
    (hcl : ClassOk cl (callEnv r args) s₀.h)
    (hq : ∀ u z,
      (∀ F ∈ (x.get c).ensures, Holds AssertionArena.empty
        (callState r args z s₁.h.length s₁ u)
        (instantiateFormula (x.callInstantiation args.length) F)) →
      ∀ F ∈ (y.get c).ensures, Holds AssertionArena.empty
        (callState r args z s₀.h.length s₀ u)
        (instantiateFormula (y.callInstantiation args.length) F))
    (h₂ : x.exitPost c r args s₁ s₂ v) :
    y.exitPost c r args s₀ s₂ v
```

The frame follows from `Post.compose_rebases`, admissibility by
transitivity, and the postconditions from `hq`. A checked instance of `hq`
uses the consequence machinery of `ThenEvidence.sound`; there is one
rebasing relation. For the rest allocation the prefix changes no old
location; fresh-result guarantees are lowered from the allocation heap's
mark to the invocation's mark, a fresh entry of the rest store is
discharged, old cells reached through that store are kept, and the
allocation's exceptional exit meets the invocation's exceptional guarantee.
`Exits.exitPost_entry` covers equal entry heaps only.

### Declarations below typing

`ParityDerivations` depends on `ProgramTyping` through `ParityEvidence` and
`ParityAssertions`, and `ProgramTyping` on `VariadicTyping` and
`TypingBasics`; the scope theorems the typing of bodies needs sit below
both:

- `Scope`, `Scope.count`, `Path.scoped`, `Witness.scoped`,
  `StepVar.scoped`, `OperationPostF.scoped`, `FormulaF.scoped`;
- substitution and scoping of assertions: `substCheck` and what its
  soundness needs, `scopedAt`, `sat_scoped_congr`, congruence of region
  roots and `effectScoped`;
- `TwoState.AgreeBelow` and the congruence theorems of `FormulaScopes`, over
  `ExitSchemas` and the assertion semantics;
- `Effect.summary_scoped` and its corollaries for interfaces, above
  `EffectSignatures`;
- `Consequence`, `Rebases`, `Post.compose_rebases` and the composition
  interface.

Derivation checking, the framing of graphs and the integration of command
bodies stay above typing.

## The serialized effect

Every document that carries a callable's effect (the Fragment's declaration
document, the request's types tables, the claims document, module
interfaces, diagnostics) writes it in one shape: the effect's two exits,
its promise and its preconditions, as `CallEffects.Effect` stores them.
[The request protocol](../REQUEST-PROTOCOL.md#the-serialized-effect) owns
its grammar, positions and order; this section states the design around it.

### What the decoder establishes and what consumers check

The decoder establishes the protocol's reading: the exact syntax, no
assertion-arena node, primitive literals and the nesting limit
([reading](../REQUEST-PROTOCOL.md#reading)). Scope depends on the callable's
arity, which the effect alone does not state: the consumers check it at the
callable's arity, before certification (`Effect.belowRow`, where an actual
is truncated, and the arity instantiation of a rest schema at the expanded
actuals). The decoder does not establish what a consumer checks: canonical
transports (`shift = 1`) where `covers`, `meetCovers` and `belowRow` use the
completion lemmas, the second exit's independence of the world where a
conjunction is used (`Exits.exitHeapOnly`, which refuses a certified stable
image), and the stability of a rest allocation at both exits where a body
is composed (`exportsEstablished`, `framesAtLocation`); a `stable` slot is
an obligation `HoldsAt` states, not evidence of one. A decoded native
contract is trusted as the library model's contract is: decoding certifies
no body and proves no contract.

### Builders and identity

The front end states an effect through its builders (`tools/type-graph.mts`),
never as a literal object. `EffectOptions` is an authoring type, never
serialized; a footprint effect (`footprintEffect`) is the exits the old
fields stated: the closed bound's three class entries, the receiver's own
locations (else its store) at `any`, then the normal postconditions in
their order (fresh store, fresh object, elements where the result is
`true`, the facts after, the receiver's growth and append, the element
write's postconditions), and the exceptional exit the same frame where the
options state throws, `⊤` otherwise, with no postcondition. An exact element
write states its range's facts among its preconditions, and the builder
refuses one that does not. `withPromise` keeps every other field;
`withConditions` adds a declaration's `@requires` as preconditions and its
`@ensures` as normal `fact after 0` postconditions.

One serializer writes an effect's text (`effectText`): every object's keys
in code point order and every list in its order. Type identity and the
comparison of effects (`sameEffect`, and the test for the ordinary effect)
compare that text: it identifies the syntax, so two effects of one meaning
written differently are two types.

### Statements and proposals

A declaration's statement (`Modifies<P, T>`, `Fresh<T>`) is serialized as
its exits (`statedExits`): the closed frame with its store regions at `any`,
`freshStore 0` for a fresh result, and on a throw the same frame or `⊤` as
`onThrow` states; an absent statement is `null`. The claims document states
a function's proposed exits (`exits`) and its returned function's
(`resultExits`), and an established interface entry the same two. The pass
keeps a statement and a claim in their closed form, which it reads from
the exits with the exits checked to be exactly that form's
(`StatedEffect.ofExits`, `classOfExits`); a throw flag at the frame `⊤`,
which states no exit of its own, reads as unset. A returned callable's
proposal is its normal bound, an exceptional `⊤` and no postcondition, and
certification establishes every exit guarantee a signature advertises.

### Codec theorems

Serialization is defined on effects of the serialization predicate
(`EffectCodec.Serializable`): arena-free formulas, primitive literals and
the nesting limit; every integer is written, a safe one as a number and any
other as its decimal string. Its subtype (`EffectCodec.SerializableEffect`) has a total encoder, and a
writer that can refuse writes through it (`EffectJson.effectJson`). Every
writer of a document holding effects (the claims document, module
interfaces, diagnostics and observations, the CLI's printed documents)
writes it through `EffectCodec.document`: each effect in it reads back as
one, or the whole document is refused, naming the effect's place. The
encoder writes `null` at an assertion reference and at a term literal,
which the decoder refuses, so no object that is not an effect is written
where an effect is.

- **Encoding then decoding** returns every serializable effect
  (`EffectCodec.decode_encode`).
- **A decoded effect** is serializable, and decoding then encoding writes
  the document read, up to the order of object members
  (`EffectCodec.decode_sound`).
- **Encoding keeps** both exits' frames, every formula, the promise and the
  preconditions: two serializable effects of one writing are one effect
  (`EffectCodec.encode_injective`).

These are codec theorems; scope and certification are proved where they are
checked.

### Controls

The controls of forged documents go through the verifier's command line
(`tests/single-pass-controls.mts`, the controls named "forged effect"): a
field no effect has at depth, an assertion reference, a transport's
override that is no pair, a second tag, an integer written as a string in
the safe range, a statement stating a postcondition, an exact write without
its range among its preconditions, symbol identities across two documents'
orders and undeclared ones, and a key stated twice, once escaped. The
codec's examples (`Source/EffectCodec.lean`) hold what no read document
reaches: the serialization predicate of an effect in memory and the
refusal of a document the verifier writes. The consumers' controls
(`Tests/EffectCodecControls.lean`) decode documents in the grammar and
apply the consuming check: a noncanonical transport at coverage, a
certified stable image of a second signature at a conjunction, an
exceptional postcondition and a frame reading through a path where a body
is composed across its rest allocation, and entry and exit positions past
a callable's arity at its scope.

## Parallel implementation

After the foundational interfaces in step 1 are fixed, two implementers can work on disjoint files:

| Implementer | Exclusive work |
|---|---|
| A | `Semantics` effect algebra, postcondition interpretation, rebasing/composition proofs and new command-summary modules |
| B | `Programs` deciders and visit integration; `Source/Lowering/Synthesis.lean` and `Source/Claims/PassProposals.lean`, against those fixed interfaces |

`CallEffects.lean`, foundational `Parity*.lean` and shared certificate types need one owner. Their interface changes precede consumer integration.

The wire transaction is sequential and has one owner across Lean, TypeScript and fixtures. Final acceptance integration follows the composition proofs. Parallel preparation does not split the format change across buildable commits.

## Corrections to the note and limits

The note states each point this design relies on
([the note](../REFERENCES.md#the-tolerant-frames-note)):

1. **Top includes views.** The note's store class contains view stores, so
   its `⊤` is the three classes the model's `⊤` is.
2. **Own regions.** The note's regions include `π.own`, every field
   location of the object a path reads, the model's own-value region.
3. **Seq-Eff's rebasing premise is the note's definition.** `Rebases`
   admits coverage absorbed by an entry of the frame so far at `any`; such
   a rebasing gives the note's direct coverage of the later frame by the
   union of the frame so far and the rebased frame (`Rebases.covers`), so
   `Post.compose_rebases` is Seq-Eff over the printed definition
   "Rebasing".
4. **Both exits compose.** A throw of the first command, a throw of the
   second after a return of the first, and a caught throw contributing to
   the handler's exit.
5. **Effects bound change; postconditions state values.** Growth does not
   imply an append's contents; `{views: grow}` does not determine the
   receiver's converted element.
6. **The mark and `old` are distinct.** Freshness reads the invocation's
   mark, and `old` the command's entry.
7. **Rebasing widens to a class at any path depth.** The note's rebasing
   tag states it.
8. **A derived effect is an upper bound.** Finite stated effects and
   finite postcondition lists need not express strongest command
   summaries; loop widening and checked consequence are part of inference.

Reduction remains deterministic. Host-dependent operations are host values meeting stated contracts. Region interpretation remains heap-only, connected to world kinds by the existing correspondence theorems.
