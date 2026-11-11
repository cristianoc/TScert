# Draft: tolerant frames in the indexed model

The Lean reading of the working note "Tolerant frames" (11 November 2026),
the proof organisation of the [single forward pass](single-pass.md)'s
soundness theorem. Its definitions and theorems are in
`lean/Verification/Semantics/TolerantFrames.lean` and
`lean/Verification/Programs/TolerantFramesRuns.lean`, namespace
`Verification.TolerantFrames`. Each claim below is labelled **proved** (with
its Lean name) or **not proved**.

## The existing mechanism this extends

[Footprints](../FOOTPRINTS.md#changes-and-footprints): a footprint is a list
of regions with changes, its meaning $`\mathrm{Post}\ \Phi\ \rho\ h\ h'`$
relating the heap its regions are read at to a later heap, and the
stability check accepts a fact under a footprint when each footprint entry
changes the fact's support within its tolerance or is apart from it
([the stable set for density](../FOOTPRINTS.md#the-stable-set-for-density),
[index facts](../FOOTPRINTS.md#index-facts)). The modality below quantifies
over the transitions those footprints bound; its atom theorems are the
existing support and stability lemmas (`stable_sound`, `holdsAt_kept`,
`stableDenseClosed_sound`) stated against that quantifier.

## States and admissible transitions

A state $`s=(n,W,h)`$ is a budget $`n>0`$, a world $`W`$ at $`n`$ with
$`\mathrm{WorldAdm}\ W`$, and a heap with $`\mathrm{HeapOk}\ n\ W\ h`$
(`IndexedHeap`). The admissible transition is

```math
s \to s' \iff n' \le n \;\wedge\; \mathrm{WExt}\,(\mathrm{trunc}_{n'}\,W)\,W'
```

(`Admissible`). Proved:

- reflexivity and transitivity through the intermediate world
  (`Admissible.refl`, `Admissible.trans`);
- heap growth, $`|h|\le|h'|`$, from the heap's length being the world's
  (`Admissible.length_le`);
- a location whose contract admits the single value $`v`$ holds $`v`$ in
  every reachable state (`Admissible.stable_value`), and a path through such
  locations reads its value there (`Admissible.stablePath`,
  `Admissible.readPath`).

**Budget zero.** States have positive budget throughout. At budget zero
$`\mathrm{Safe}\ \Xi\ T\ 0\ W\ h\ t`$ holds for every term (`safe_zero`),
so an execution that has used its budget carries no obligation, and every
assertion is read where single-value contracts determine contents.

## Adequacy

A run of $`k`$ steps that a safety derivation covers, from a state with
$`k<n`$, ends in a state an admissible transition reaches, the derivation
continuing there; its intermediate worlds are the derivation's, matched to
the run by determinism of the step relation (proved: `run` for
`SafePostExc`, `safe_run` for `Safe`). On each exit the endpoint carries the
exit's postcondition: a value meets its type and $`Q`$ (`run_normal`), a
raise is a throw of the exception family and meets $`R`$ (`run_throw`). For
a closed footprint $`c`$ stated on both exits, as the expression effect rules
state it, each exit is an action of $`c`$ (`action_normal`,
`action_throw`). The graph machine is deterministic (`transition_det`), and
a graph run that `SafeGraph` covers with budget left ends in an admissible
state, `SafeGraph` continuing there (`graph_run`).

One expression end to end, proved: a typed field write
(`ExpressionEffects.fieldWriteWithin` with $`\{\mathsf{values}:\mathsf{any},\ \mathsf{stores}:\mathsf{keep}\}`$),
safe at $`s`$, run to a value or a raise with budget left, ends in a state
an action of that effect reaches, where every bound $`y\le|x|`$ that held at
$`s`$ holds (`field_write_keeps_bound`).

## The modality

```math
\mathrm{Action}_\Phi^\rho\ s\ s' \iff s\to s' \wedge \mathrm{Post}\ \Phi\ \rho\ h\ h'
\qquad
\rho,m,s\models\Box_\Phi F \iff \forall s'.\ \mathrm{Action}_\Phi^\rho\ s\ s' \Rightarrow \rho,m,s'\models F
```

(`Action`, `Box`): the name valuation $`\rho`$ and the entry mark $`m`$ are
fixed across it. An assertion $`g`$ is invariant when every admissible
transition keeps it (`Invariant`); this is $`g\vdash\Box_\top g`$ for
$`\top=\{\mathsf{values}:\mathsf{any},\ \mathsf{stores}:\mathsf{any}\}`$
(proved: `invariant_iff_top`). An effect is rigid at $`\rho`$ when its
action is transitive (`Rigid`). The laws, proved:

| Law | Statement | Lean |
| --- | --- | --- |
| (a) | $`\Box_\Phi F\vdash F`$ | `box_elim` |
| (b) | $`\Box_\Phi(F\wedge G)\dashv\vdash\Box_\Phi F\wedge\Box_\Phi G`$; $`F\vdash G`$ gives $`\Box_\Phi F\vdash\Box_\Phi G`$ | `box_and`, `box_mono` |
| (c) | actions of $`\Phi`$ from $`s`$ are actions of $`\Psi`$ gives $`\Box_\Psi F\vdash\Box_\Phi F`$ at $`s`$ | `box_anti` |
| (d) | $`g`$ invariant gives $`g\vee\Box_\Phi F\vdash\Box_\Phi(g\vee F)`$ | `box_or` |
| (e) | $`\Phi`$ rigid gives $`\Box_\Phi F\vdash\Box_\Phi\Box_\Phi F`$ | `box_idem` |

Inclusion of actions, proved: a footprint within another by
`Footprint.le cl`, from a state where the class evidence `cl` holds
(`action_le`); a closed footprint within another, from every state
(`action_le_closed`).

Rigidity, proved: every closed footprint is rigid (`closed_rigid`, from
`Closed.Holds.trans_on`); the store of $`x`$ with the cells it lists, both
at $`\mathsf{any}`$, is not, by a three-location witness in which a first
action makes the store list an old cell and a second changes that cell
(`elems_not_rigid`). A stable path is rigid under every effect: its value is
read in every state an action reaches (`stable_rigid`), and the path's
stability is invariant (`stableAt_invariant`), so the witness of
$`\mathrm{rigid}(\pi)`$ is a fact of the world. Freshness of a store against
the entry mark reads no heap and is invariant (`fresh_invariant`).

## Entering the modality

The tolerant frame theorem, proved: a fact kind whose support the effect
respects under separation knowledge $`K`$ holding at $`s`$ enters
$`\Box_\Phi`$ (`tolerant_frame`), and an index fact a closed footprint's
change keeps enters its modality (`kept_box`). The atoms, proved, with
$`G=\{\mathsf{values}:\mathsf{any},\ \mathsf{stores}:\mathsf{grow}\}`$:

```math
y\le|x| \;\vdash\; \Box_G\,(y\le|x|)
\qquad
\mathrm{dense}(x,k) \;\vdash\; \Box_G\,\mathrm{dense}(x,k)
```

(`grow`, `dense`), for variables $`x`$, $`y`$ and a fixed prefix $`k`$.
Along a stable path $`p`$, $`y\le|x.p|\vdash\Box_G(y\le|x.p|)`$
(`grow_path`): the note's (Rigid) with (Grow), the rigidity supplied by the
world.

## What the model requires beyond the note

- **Admissibility needs no frame assumption.** Reflexivity, transitivity,
  heap growth and single-valued locations follow from the indexed model at
  positive budget (proved, above); an object's keys and their locations are
  part of the object value, which no transition changes.
- **The class of a location's contents is not fixed by admissibility.** A
  contract may admit both a store and another value, so an effect stated by
  class, such as $`\{\mathsf{values}:\mathsf{any}\}`$, bounds a write only
  where typing gives the class of what is written over; the field write's
  judgment obtains it from a type of source values
  (`ExpressionEffects.field_write_within_exc`).
- **Antitonicity is relative to the start state.** Inclusion of
  footprints whose regions are read through class evidence holds where that
  evidence holds (`action_le`); law (c) for those footprints is
  $`K\wedge\Box_\Psi F\vdash\Box_\Phi F`$.
- **Rigidity is a property of the effect and of the state.** Closed
  footprints are rigid at every state; a store region at a path composes
  only where the path resolves to the same store in both heaps
  (`ArgumentStoreRegionsWithin.trans`'s premise), and element regions at
  $`\mathsf{any}`$ are not rigid (proved).
- **Allocated cells are not a consequence of admissibility.** A store whose
  contract admits it may list a cell beyond the heap; the support of
  $`\mathrm{apart}(x,y)`$ needs every listed cell allocated, a well-formedness
  condition the contracts or the steps must supply (not proved here).
- **An action from a run needs the effect judgment.** Safety alone gives an
  admissible endpoint; the footprint comes from a postcondition relative
  to the run's first heap, on each exit (`action_normal`, `action_throw`).
  A graph run's footprint is the graph code's node judgments composed
  (`Post.compose_at`; not connected to `graph_run` here).
