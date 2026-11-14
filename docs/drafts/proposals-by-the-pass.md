# Proposals by the pass

## The existing mechanism this extends

This design extends the step-frame rule of [footprints](../FOOTPRINTS.md#argument-path-store-regions) and `ArgumentRegionGraph.stepWithin`: a step's local effect, rebased to the function's entry, lies within the function's frame. Its composition theorem is `nodeWithin_of_step` (`lean/Verification/Programs/ArgumentRegionGraph.lean:154`). The front's proposals are owned by [the front](../SINGLE-PASS-FRONT.md); the form-based decisions this replaces are inventoried in [on-demand processing, section 9](on-demand-processing.md#proposal-c2).

**Proposed implementation:** one checked traversal produces the unwritten interface from its steps and finalizes the obligations that depend on that interface. Written components remain obligations. The same step implementation serves both inference and checking. One-traversal feasibility is a conjecture subject to the experiment of section 8.

References abbreviate `lean/Verification/Programs/` as **P/**, `lean/Verification/Semantics/` as **S/**, and `lean/Verification/Source/` as **F/**. "Proved" identifies an existing theorem; "proposed" identifies this design.

## 1. What the pass knows today

The closed-footprint check is a predicate against a supplied bound. `footprintCheck` combines preservation, write checks, the selected derivation's effect, empty contexts and types, exceptional preservation, freshness at returns and scope (`P/SinglePass.lean:1405`). `visitStep` obtains the checked step and applies that predicate (`:2646–2693`). Each of its disjuncts is a rule's own grade below the bound and a side condition the bound does not enter: an inspection or an unreachable type keeps everything, a typed field write is within `⟨any, keep⟩`, an element write within `⟨any, keep⟩` or `⟨any, grow⟩`, an element write at a run-time index within `⟨any, grow⟩`, an initializing write within `⟨init, keep⟩`, a call within its selected signature's footprint, with its receiver's own change, or `top` where the signature excepts its receiver's store and the receiver is not fresh (`P/ExpressionEffects.lean`, `fieldWriteWithin`, `elemWriteWithin`, `elemVarWriteWithin`, `initWriteWithin`; `P/GraphCode.lean:330`, `selectedWithinAt`).

`Stepped.stepEffect` holds `HeapExpressionRules.StepEvidence`, an evidential description of the step; it is not itself a joinable footprint (`P/SinglePass.lean:1758`). The regional checker exposes a joinable `StepEffect`: slot interpretation, normal frame and raised frame (`P/ArgumentRegionGraph.lean:43`).

That extraction depends partly on the proposed bound. `stepEffects` obtains alternatives from `closedStep Φ`, the selected call and an element-write frame; `closedStep Φ` returns the bound whose check succeeded (`P/ArgumentRegionCertificates.lean:33,185`). Running this extractor at `top` and joining its answers therefore computes no useful footprint.

**Proved: on the direct route a step's local effect is read off its evidence.** Every disjunct of `footprintCheck` that reads the bound has the form $`g \sqsubseteq \Phi`$ for a closed footprint $`g`$ the step's own rule grants: a typed field write ⟨any, keep⟩, an element write ⟨any, keep⟩ or ⟨any, grow⟩, an element write at a run-time index ⟨any, grow⟩, an initializing write ⟨init, keep⟩, a call its selected signature's footprint joined with its receiver's own change, or `top` where the signature excepts its receiver's store and the receiver is not fresh; an inspection or an empty type keeps everything. `stepGrades` lists these grades once per step and `footprintCheck_eq_admits` (`P/SinglePass.lean`) proves the check at every bound equal to `admits` of them; `writeWithin_eq_grades`, `initWriteWithin_eq_grades` (`P/ExpressionEffects.lean`) and `selectedWithinAt_eq_grades` (`P/GraphCode.lean`) prove the disjuncts. A walk with `grading` reports each visited step's grades (`SinglePass.walkGrades`), and the front's proposal reads them off the run that settles the member's loop heads (`PassProposals.settledInterface`).

**The direct walk's transfers read no bound.** The bound enters a walk at two places: each step's footprint check (`boundOk`, a gate that stops the walk), and the region with no normal return (`deadRegion`), which reads only whether the bound bounds throws. Entry, step and exit transfers read neither.

**The regional route reads the bound in its transfers.** `checkClosedNode` has the same disjunct forms as `footprintCheck`. `cellsKept` reads the frames `stepEffects` gives, and `closedStep Φ` gives the bound itself as the step's frame (`P/ArgumentRegionCertificates.lean`): which cells a step keeps, the regional state carried to its successors, depends on $`\Phi`$. A footprint the regional route establishes is therefore checked by a regional walk at that footprint; a walk at another bound is another walk. Replacing `closedStep Φ`'s frame by the step's least grade would make this transfer bound-free, at the cost of `stepEffects_ok` for that frame, and changes which cells are kept (more are kept), so verdicts can change.

The interface has distinct components:

- **Normal footprint:** the join of the entry-rebased effects of the steps outside the region from which no normal return is possible. Under a footprint without `onThrow`, the steps of that region are exempt (`deadRegion`, `GraphCode.deadNode`); under one with `onThrow` there is no such region.
- **Exceptional guarantee:** `onThrow` states that the footprint also bounds an escaping throw. A throw a live handler catches is held to the footprint as well: on the direct route a step whose caught throw is unbounded admits no bound below `top` (`footprintCheck`'s throw conjunct), and the regional check reads every step with a handler as throwing (`checkNode`'s `thr`, `P/ArgumentRegionCertificates.lean:718`).
- **Fresh result:** every normal return establishes freshness; `outFreshOf` computes the current evidence (`P/SinglePass.lean:2499`). This component combines by conjunction.
- **Returned callable:** its effect comes from the checked type of the returned value. Its invocation effect is separate from the producer's execution effect. `resultWithFootprint` strengthens the result contract and the function's returns establish it (`F/Lowering/Types.lean:771`).

The new traversal retains separate normal and exceptional accumulators, return types and freshness evidence. It projects these into the existing interface fields at finalization.

## 2. The lattice and rebasing

The "twelve footprints" are the normalized closed domain: four value changes, `keep ≤ init ≤ scalar ≤ any`, times three store changes, `keep ≤ grow ≤ any`. `Closed.le` applies exactly these normalizations (`S/ClosedFootprints.lean:22–39`). Its longest strict ascending chain has five increases; twelve elements do not imply that three iterations suffice.

The semantic language is larger: a footprint is a finite list of region/change pairs, including parameter paths and class regions (`S/Footprints.lean:310,498`). Finite unions are expressible there. The exported regional representation is narrower: closed components plus argument-path store regions (`S/StoreRegions.lean:9,32`; `P/ArgumentRegionGraph.lean:62`). Every join has a sound representation through widening, although that representation need not preserve its precision.

The single composition rule is:

```math
\Phi_f=\bigsqcup_{s\text{ in }f}\alpha_f\!\left(\mathrm{rebase}_{e_s}(\Phi_s)\right).
```

Here rebasing uses established entry origins and freshness; $`\alpha_f`$ expresses the result in the interface language: the least closed footprint whose frame includes it, as `Footprint.le` reads inclusion. A proven stable parameter path remains that path. Locations proved absent from the entry heap disappear. Any remaining unrepresentable region widens to its class, retaining its change grade.

This is the note's **Seq-Eff/Fresh-Eff** rule ([the Tolerant frames note](../REFERENCES.md#the-tolerant-frames-note)), including its qualification that fresh array stores disappear while their cells may widen to their class. Freshness of a local variable alone does not erase every location reachable through it.

The implementation already has this mechanism: `rebaseAll`, `rebase_sound` and `Post.compose_at` (`S/FootprintRebase.lean:116,134,161,248`). Unresolved roots become `all`; an enclosing `inCls` retains the class restriction. Preserve that evidence-based behavior for every step.

For termination, inferred parameter paths use a finite vocabulary fixed from the lowered unit and consumed contracts. Rebasing outside that vocabulary widens to a class. Arbitrarily growing paths would invalidate a finite-height argument.

## 3. Calls and recursion

On-demand processing establishes each acyclic callee's interface before its caller consumes it. The caller's step includes all work represented by its lowered operation and evidence, including argument-pack construction. Reading only the callee's declared mutation effect is insufficient.

Let $`T_f(I)`$ be the interface obtained by running the pass's steps with self-calls reading $`I`$. Iterate:

```math
I_0=\bot,\qquad I_{n+1}=I_n\sqcup T_f(I_n),
\qquad T_f(I_n)\sqsubseteq I_n\ \Longrightarrow\ \text{finalize}.
```

Written components stay fixed. Unwritten footprints start at `keep/keep`; the exceptional guarantee starts bounded and can weaken. Returned-callable components participate wherever represented. Freshness, if inferred, uses the reverse Boolean order.

Each unstable successful round strictly increases the finite product lattice, so its height bounds the rounds. Calling the result the **least** fixed point additionally requires monotonicity of $`T_f`$; that property is unproved for the proposed driver. A located typing failure remains a failure, rather than evidence for a smaller effect.

Self-recursion today uses three source walks and reads its own returned-callable footprint at `top` (`F/Claims/FragmentFront.lean`, `declarationWalks`). The lattice measure replaces that numerical cutoff.

Mutual recursion follows the agreed first-version policy: another member's unwritten components are read at unrestricted changes, unbounded throws and no freshness or returned-callable strengthening. Each member establishes the consumed view through its own check; there is no joint iteration ([on-demand processing, decisions](on-demand-processing.md#8-decisions)).

## 4. One traversal and its cost

The proposed run performs typing, step checking, edge checking and effect accumulation together. It retains the evidence needed to discharge final interface-dependent obligations. Finalization checks the accumulated frame, written bounds, return contracts and regional provenance against those retained results. It performs no second transfer traversal.

A function's inferred footprint then bounds its collected effects by construction. This does not discharge unrelated obligations, nor justify regional facts assumed during collection. Regional preservation depends on `Φ` through `cellsKept`, and path stability depends on the regional contract (`P/ArgumentRegionCertificates.lean:255`; `P/ArgumentRegionGraph.lean:73`). Collection must retain those dependencies and validate them against the final interface.

Self-recursive rounds and loop-invariant refinement can require repeated transfers. "One traversal" means one final checked traversal after those inputs stabilize.

**What one run being both proposal and check needs.** Three things, none of which is in the code:

1. *The result contract.* A returned function's footprint is part of the plan's result type: the producer's claims at the returns and the goal the returns are checked at are computed from it. Installing it changes the claims, so the run at the installed interface is a different run. Carrying the component open needs claims that hold the result's footprint as a variable to close at the end; claims are types of the frozen store, which has no such variable. Where the installed result type equals the one the run had (a function returning no function, or one whose returned footprint is `top`), no rerun is needed for it.
2. *One plan.* The proposal's runs are over the plans built for the proposal (`planOf`, its own frozen store); the check's over the unit's plans. A fused theorem needs both to be one value, which a unit planned in its own check (the file worker's `PreparedFile.plan`) makes possible.
3. *The theorem.* For the direct route: a walk with no bound accepted, every recorded step's grades admitted at $`\Phi`$ (and the region with no normal return where $`\Phi`$ states no throw bound), gives the walk at $`\Phi`$ with the same record, by induction over `drive` (the transfers read no bound); then lifted through `passMember` and the settling runs, whose intermediate runs at $`\Phi`$ may stop where the open runs passed, so the lift is over the last run with the settled candidates (`Recandidated`), and through a planning premise for the proposal's plans in `Mode8Accepted`.

Two runs remain: the proposal's (settling runs at the open footprint, plus the regional walk at `top` where the direct footprint is more than keep/keep) and the check's at the proposal.

Each graph run is counted by kind with its inputs' digest ([on-demand processing, graph runs by kind](on-demand-processing.md#graph-runs-by-kind)): on pretext the proposals' regional route (the walk at `top`, its tables and its local effects) is the largest share of the cost proposals add, and the check's runs that repeat or only re-bound a proposal's are a smaller one.

## 5. The proof boundary

The existing theorem establishes a **given** interface. `RequestSafe` includes safety, closed footprint and freshness, postconditions, regional bounds and assertions (`F/Claims/PassUnit.lean:113`). `passGroupMode8_safe` derives unit safety from accepted member runs (`F/Claims/PassUnitInferred.lean:317`).

An exploratory pass followed by the existing checking pass keeps that semantic proof path, at the cost of two transfers. A single-traversal implementation needs an additional theorem, with the following proposed statement:

```math
\mathrm{inferCheck}(r)=\mathrm{ok}(I,w)
\quad\Longrightarrow\quad
\mathrm{RequestSafe}(\mathrm{install}(r,I)).
```

Its premises include the existing store, instance and read-summary soundness conditions. `install` fills only unwritten components and preserves written contracts and program identity. The proof combines checked step effects, rebasing and composition, and final return checks. It reuses existing semantic lemmas; its exact executable acceptance premise requires new proof plumbing.

`Recandidated` permits changing only request candidates (`F/Claims/PassUnitInferred.lean:19`). It does not justify changing footprints or result contracts. Interface installation needs its own theorem, and the accepted-plan path must consume that theorem's result. The headline acceptance invariant retains its meaning.

This design preserves the semantic property, and claims no unchanged proof for a fused run.

## 6. What disappears

`declarationWalks` as an effect-analysis traversal, its `returnedFootprint` collection, and the effect-grading state and operations in `Synthesis`: `valueChange`, `storeChange`, `throwWrites`, `wrote`, `callChange`, `targetWrite`, and the corresponding construct grades (`F/Claims/FragmentFront.lean`, `returnedFootprint`, `declarationWalks`; `F/Lowering/Synthesis.lean:99,1823–1851`). Function literals obtain effects through their own checked bodies before their grading machinery can go (`F/Lowering/Synthesis.lean`, the function literal's effect).

In the C2 inventory ([on-demand processing, section 9](on-demand-processing.md#proposal-c2)):

- The **generic/rest exclusion** goes.
- The **three-walk self-recursion row** becomes the pass-step fixed point.
- The **`returnedFootprint` return-shape row** goes with the source-return walk.
- The **`resultWithFootprint`/`keepingType` shape gates** require general interface-component filling that preserves every existing contract. Their removal is part of that implementation, not a consequence of joining effects alone.
- Written effects use the same run, with those components fixed and unwritten components collected.

Async's explicit language restriction and stand-in controls retain their stated purposes. Ordinary and generic slot representation and the C3 publication and realization restrictions are separate obligations ([on-demand processing, section 9](on-demand-processing.md#publication-and-realization-c3)).

`Synthesis` remains responsible for the types and lowered input the pass requires. Removing grading requires separating effect holes from ordinary type synthesis, including nested callable types.

## 7. The common mechanism and implementation order

**What the front proposes about a body is computed using the pass's entry, step, merge and edge operations on that body.**

Effects accumulate upward. Loop-head candidates weaken within a finite vocabulary and must hold on every incoming edge. Regional origins and freshness meet across incoming states and require the same edge validation. These are different fixed-point domains over shared transfers.

Order: **step effects and rebasing; regional inference; loop-head inference**. Regional state flows through `regionalAt` (`P/SinglePass.lean:2792`); `RegionInference`'s claimed-certificate iteration is replaced by those checked transfers (`F/Claims/RegionInference.lean:94`). `HeadInference.walk`'s context interpreter (`F/Claims/HeadInference.lean:1193`) is replaced by a finite-vocabulary design of its own, which retains a final ordinary pass; sharing transfers applies to it directly, and eliminating its final run requires the same evidence-finalization argument proposed here.

## 8. Feasibility experiment and unresolved risks

Reading establishes the explicit regional effect mechanism and the bound-dependent closed checks. It does not establish that every checked step admits a sufficiently precise bound-independent extractor, that interface constraints avoid retyping, or that the fused run saves CPU.

The smallest experiment instruments the pass to collect effects and retained obligations, then compares its finalized interface against an ordinary checking run as a temporary oracle. It uses the nine cases [on-demand processing, section 9](on-demand-processing.md#proposal-c2) records: the six positive patterns `generic-graph-bodies`, `generic-structural-bounds`, `generic-promise-resolution`, `generic-promise-associated-result`, `generic-promise-bounded-result`, `module-functions`, and the three `invalid-generic-promise-bounded-*` negatives.

It inspects the binder-typed field-writing `set` and the rest caller `spread`/`discard`, then every function in those fixtures. The gate is six preserved positive verdicts, three preserved negative verdicts at their intended obligations, and no inferred footprint refused by the oracle. The forced footprint, returned-callable and regional-proposal controls stay.

It records the local effect, rebasing evidence, exported join, transfer count and finalization cost. Any final obligation requiring changed transfer state identifies the precise obstruction to fusion.
