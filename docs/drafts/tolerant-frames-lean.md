# Draft: tolerant frames in the indexed model

The Lean reading of the working note "Tolerant frames" (11 November 2026),
the proof organisation of the [single forward pass](single-pass.md)'s
soundness theorem. Its definitions and theorems are in
`lean/Verification/Semantics/TolerantFrames.lean` and
`lean/Verification/Programs/TolerantFramesRuns.lean` (and the modules each section names), namespace
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
raise is a throw of the exception family and meets $`R`$ (`run_throw`). Each exit has its own footprint and post: a judgment whose normal exit meets
$`c_n`$ and $`Q_n`$ from the run's first heap, and whose exceptional exit
meets $`c_e`$ and $`Q_e`$, gives on the normal exit an action of $`c_n`$ with
the residual budget $`n'+k=n`$, the value's type and $`Q_n`$
(`action_normal`), and on the exceptional exit an action of $`c_e`$ with the
raised value $`e`$ closed, of the exception family, and $`Q_e`$
(`action_throw`). A normal-only judgment leaves the exceptional exit at
$`\top`$ (`action_throw_top`). The graph machine is deterministic
(`transition_det`); a graph run that `SafeGraph` covers with budget left ends
in an admissible state (`graph_run`).

One expression end to end, proved: a typed field write
(`ExpressionEffects.fieldWriteWithin` with $`\{\mathsf{values}:\mathsf{any},\ \mathsf{stores}:\mathsf{keep}\}`$),
safe at $`s`$, run with budget left to a value or a raise, ends in a state an
action of that effect reaches, with the residual budget, the result's type or
the raised value's family, and every bound $`y\le|x|`$ that held at $`s`$
(`field_write_keeps_bound`).

## Graph safety and transfer

`SafeGraph` is established from node obligations (proved: `graph_safe`,
`graph_safe_at`). The invariant `GraphInv` states, at positive budget only: at
`.at l ρ` the node assertion $`\mathrm{pre}_l`$; at a partially evaluated
`.eval` its node's local safety `SafePostExc` from the node's entry state
$`s_0`$, the current world reached from $`s_0`$ (`Reach`) and the node's
exit obligations; at `.done` the result type and the normal exit post
$`Q_{\mathrm{res}}`$ of the heap; at `.raised` a closed value of the exception
family and the exceptional exit post $`R_{\mathrm{res}}`$. One transition from
the invariant is `graph_step`; `graph_safe` iterates it. Its premises are

- `NodesChecked`: from every state where $`\mathrm{pre}_l\ \rho`$ holds, node
  $`l`$ exists, is locally safe with exit footprints $`c_n, c_e`$ and posts
  $`Q_n, Q_e`$, and meets its `NodeObligations`;
- `AdminClosed`: each $`\mathrm{pre}_l`$ survives an admissible transition
  that keeps the heap (the world truncated by entering a node).

`NodeObligations` are, per exit: the shape a continuation needs to take a
transition (a Boolean at a branch), required at every budget so that a
successor exists at budget one; the normal target (`NormalTarget`: the
target's assertion at `mapEnv θ (push v ρ)` or `mapEnv θ ρ`, the branch's by
the observed Boolean, the result type and $`Q_{\mathrm{res}}`$ at `ret`), from an action of $`c_n`$,
the value, its type one level above (`Above`) and $`Q_n`$; and the raise
target (`RaiseTarget`: the handler's assertion with $`e`$ bound, or the
exception family and $`R_{\mathrm{res}}`$ when it escapes), from an action of $`c_e`$, $`e`$ closed,
its family above, and $`Q_e`$. Entering a node and each continuation or
handler transition spend one level; no obligation is read at budget zero.

TRANSFER (proved: `transfer`) builds `NodeObligations` from the shape, the
retained index facts $`K_n`$, $`K_e`$ under $`\Box_{c_n}`$, $`\Box_{c_e}`$ at
$`s_0`$, and the per-exit target entailment, which receives the retained
facts transported (`Transported`): each $`F\in K`$ holds as $`F'`$ at every
target environment $`\rho'`$ under every renaming $`g`$ with
$`F.\mathrm{mapM}\ g = F'`$ and $`\rho'(g\,i)=\rho\,i`$ on $`F`$'s slots
(`transported_of`, from `holdsAt_mapM`); `mapEnv_slot` and
`mapEnv_push_slot` give the slot condition for an edge mapping with and
without the exit's value bound. The continuations `branchBind` and `tagBind`
are outside this statement (`ShapeOk` is false there).

The note's loop `for (j = from; j < to; j++) out[j] = xs[j]`, head facts
$`0\le j`$ and $`\mathit{to}\le|\mathit{xs}|`$, `out` possibly `xs`, proved at
two edges:

- the aliasing element write: its local judgment within
  $`G=\{\mathsf{values}:\mathsf{any},\ \mathsf{stores}:\mathsf{grow}\}`$
  (`grow_write_judgment`, from `ExpressionEffects.write_within_exc`, which
  covers an element write at a run-time index whatever array it writes), and
  its obligations toward the increment, $`\mathit{to}\le|\mathit{xs}|`$ by
  (Grow) and $`0\le j`$ reading no heap (`loop_write_obligations`);
- the back edge with a changed head valuation: after $`j'=j+1`$, the
  head's slot 0 holds $`j'`$, $`\mathit{to}\le|\mathit{xs}|`$ is retained under
  the increment's empty effect and renamed from slots 2, 3 to 1, 2, and
  $`0\le j'`$ follows from $`0\le j`$ and the increment's post
  (`loop_back_edge`).

Two graphs with an actual throw instantiate `graph_safe`
(`lean/Verification/Programs/TolerantFramesExamples.lean`, proved): in
`handledGraph` node 0 throws `null` to a handler node returning the value it
receives, the raise target the handler's assertion with the thrown value
bound (`handled_safe`); in `escapingGraph` the throw escapes, the raise target
the graph's exception family (`escaping_safe`), and a run to the raised state
raises `null` (`escaping_raised`, from `invocation_raised`).

The increment's local judgment, proved (`increment_judgment`): with slot 1
holding a non-negative integer $`j`$ below the integer slot 2 holds (the
guard's $`j<\mathit{to}`$), `j + 1` takes one step to the double of
$`j+1`$, a safe integer (`SafeIntegers.add_safe`), keeping the heap; its post
is the one `loop_back_edge` takes. The increment node is then checked in the
form `NodesChecked` asks, its judgment and its back edge's obligations
together (`increment_checked`). The loop's initialisation, guard and read
nodes are not proved: a closed instance of `graph_safe` for the loop needs
their judgments (the comparison `j < to` as a Boolean, the read
$`\mathit{xs}[j]`$ within the array's store contract) and a concrete world
for $`\mathit{xs}`$ and $`\mathit{out}`$. Both edges take the escaping
throw's obligation from the node's exception family one level up (`hΞ`).

## One action per invocation

Module `lean/Verification/Programs/TolerantFramesInvocation.lean`. A graph
run from a state `GraphInv` describes, with budget left, ends in a state it
describes, reached by an admissible transition (proved: `graph_inv_run`, each
transition the one `graph_step` supplies, by `transition_det`). So a run of
an invocation from a node entry whose assertion holds ends, at `.done v`, with
$`v`$ of the result type and $`Q_{\mathrm{res}}`$ of the heap
(`invocation_done`), and at `.raised e` with $`e`$ closed, of the exception
family, and $`R_{\mathrm{res}}`$ (`invocation_raised`). Where
$`Q_{\mathrm{res}}`$ bounds the heap by $`c_n`$ from the entry heap, the run is
one action of $`c_n`$ from the entry state, at every name valuation
(`invocation_action`; `invocation_throw_action` for $`c_e`$ and
$`R_{\mathrm{res}}`$), and a fact under $`\Box_{c_n}`$ at the entry holds at the
exit (`invocation_box`): a callee's invocation is the action a caller's
`transfer` consumes. Effects are required at the exits only.

The node assertions carry the bound so far from the fixed invocation entry
heap $`h_0`$, and each exit composes the node's effect onto it, proved:

- a closed node effect $`c_n\le c`$ (`bound_step`, from
  `Closed.Holds.trans_on`), the handler's exceptional effect alike;
- the fresh-store exemption: a node effect within $`c`$ on the locations below
  $`|h_0|`$ only (`bound_step_fresh`);
- the administrative transitions keep the heap, so the bound conjoined to the
  node assertions keeps `AdminClosed` (`adminClosed_bound`);
- a regional node effect $`\Psi`$ at the node's positions, rebased to the
  entry values: an action of $`\Phi_q`$ from the invocation's entry where
  $`\Phi_p\mathbin{+\!\!+}\mathrm{rebase}(\Psi)\le_{cl}\Phi_q`$ with
  $`\mathrm{ClassOk}\ cl`$ at the invocation's entry heap (`action_compose_at`,
  the lift of `Post.compose_at`); the rebasing evidence holds wherever each
  position's value is read from an entry position along a stable path of the
  entry world (`rebaseOk_stable`).

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

Rigidity on a domain, proved. $`\Phi`$ is rigid on $`D`$ at $`\rho`$ when its
action is transitive from every state where $`D`$ holds (`RigidOn`); then
$`D\wedge\Box_\Phi F\vdash\Box_\Phi\Box_\Phi F`$ (`box_idem_on`), and an invariant
$`D`$ holds at every state an action reaches (`rigidOn_domain`), so
idempotence iterates. A store region at a path,
$`\{x.p.k:\delta\}`$, is rigid on the domain of the path's stability,
$`\mathrm{StableAt}\ x\ p\ v`$, whatever $`\delta`$ (`path_rigid_on`): the region
reads the same locations at every heap where the path reads $`v`$
(`path_mem_eq`), and changes compose (`Change.Holds.trans`).

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

(`grow`, `dense`), for variables $`x`$, $`y`$ and a fixed prefix $`k`$. Density here is physical presence of the first $`k`$ store entries: it states neither that the listed cells are allocated nor anything of the elements' contents.
Along a stable path $`p`$, $`y\le|x.p|\vdash\Box_G(y\le|x.p|)`$
(`grow_path`): the note's (Rigid) with (Grow), the rigidity supplied by the
world. $`y\le|x.p|`$ is the pass's linear index fact over the value of $`y`$
and the length term at $`x`$'s path $`p`$ (proved: `pathLowerBound_iff`), so
(Grow) at a rigid path holds of that fact (`grow_path_fact`). That
`StableAt` follows from the pass's own path-preservation evidence is not
connected.

## The facts a step is not handed

The pass stores facts over names and hands a step's rule the facts over the
names its expression mentions (`SinglePass.materialize`); `applyDelta`
removes a handed fact the rule's output lost and keeps every other stored
fact. Module `lean/Verification/Programs/TolerantFramesNamed.lean`.

A named fact $`a`$ is read at a name valuation $`\eta`$ (each name its value)
and a heap, with each name for a slot (`AtomHolds`); a separation fact
relates its subject's fields to its partners' at names. Its meaning needs no
slot. $`\mathrm{Named}\ S\ \eta`$ holds at a state when every fact of $`S`$
holds at $`\eta`$ and the state's heap. Proved:

- every named fact survives an extension of the heap (`atomHolds_extend`), a
  fact reading no heap holds in every heap (`atomHolds_heapFree`), where
  $`a.\mathrm{heapFree}`$ is exactly the pass's handler filter: values, alias
  links, separation, and index facts with $`\mathrm{envOnly}`$; a fact reads
  only its names' values (`atomHolds_congr`), so naming a step's result $`r`$,
  fresh for $`S`$, keeps $`S`$ (`named_set`);
- (Keep) for $`c\le\{\mathsf{values}:\mathsf{keep},\ \mathsf{stores}:\mathsf{keep}\}`$,
  $`\mathrm{Named}\ S\ \eta\vdash\Box_c\,\mathrm{Named}\ S\ \eta`$
  (`named_keep_box`); for $`S`$ heap-free,
  $`\mathrm{Named}\ S\ \eta\vdash\Box_\Phi\,\mathrm{Named}\ S\ \eta`$ for every
  $`\Phi`$ (`named_any_box`); a footprint within such a $`c`$ by class evidence
  $`cl`$ keeps $`S`$ from a state where $`\mathrm{ClassOk}\ cl`$ holds at the
  action's source heap (`named_le_box`), the evidence of a density fact
  holding at the heap the density holds at (`dense_class_at`);
- the step, both exits: a judgment whose normal exit is within such a
  $`c_n`$, run to a value with budget left, ends in an action of $`c_n`$ with
  the residual budget, the value's type, the exact post and
  $`\mathrm{Named}\ S\ \eta[r\mapsto v]`$ (`preserving_normal`); a throw ends in
  an action of $`\top`$ with the raised value closed and of the exception
  family and the heap-free part of $`S`$ (`preserving_throw`);
- the preserving judgments: an inspection (`inspection_keeps`, from
  `inspect_frame`), a call `keepsCall` accepts (`keepsCall_keeps`, from
  `selectedCall_sound` at the empty footprint) and a call `freshCall` accepts
  (`freshCall_keeps`, from `keepsHeap_prefix`) have their normal exit within
  $`\{\mathsf{values}:\mathsf{keep},\ \mathsf{stores}:\mathsf{keep}\}`$. At a
  node whose step `keepsCall` accepts, both exits together
  (`keepsCall_frame`): the normal return exposes the rule's output
  $`\mathrm{shift}\ k`$ for the handed facts $`k`$ and every fact of $`S`$,
  handed or not, at $`\eta[r\mapsto v]`$; the throw exposes the heap-free
  facts of $`S`$.

A fact whose names hold no slot is kept under $`\eta`$, not at the positional
environment: `Transported` states only facts over slots, so a slotless fact
holds in the named invariant and enters no target assertion until a slot
holds its names.

Every `preserving` case of the pass has its normal exit within
$`\{\mathsf{values}:\mathsf{keep},\ \mathsf{stores}:\mathsf{keep}\}`$: the four
call layers through `keepsHeap` (proved for `keepsCall` and `freshCall`;
`elementsCall` and `requiresCall` test the same `keepsHeap` of the selected
effect), and the other step kinds through their terms (proved for
inspections; the term shapes `created`, the reads and `knownValue` require are
not connected here). The frame consumes no class evidence: `keepsHeap`
compares closed footprints. Two conditions are outside it: the result's name
is fresh for the store (a premise, `hr`), and the output the pass applies is
the checked rule's (`Checker.select` agreeing with `run`).

### The preserving steps through their checked rules

Module `lean/Verification/Programs/TolerantFramesSteps.lean`. The pass frames
a step (`applyDelta … true`) when it is preserving: a call its own predicates
find keeping the heap (`callKeepsHeap`, `SinglePass.lean` lines 1289–1296), or
a step of a kind other than `ordinary`, `written` and `boundedWrite`
(`kindPreserving`, lines 1307–1309); `passPreserving` is their disjunction.
$`\mathrm{KeepsPost}`$ is the normal exit within
$`\{\mathsf{values}:\mathsf{keep},\ \mathsf{stores}:\mathsf{keep}\}`$. Proved:

- the base rule (`checkStepUsing`) of each preserving kind fixes the term's
  shape (`base_shape`): `pure` and `reading` an inspection by their checked
  purity, the four reads `.readAt f (.var i)` with $`i`$ a slot holding a value
  (for `linkedRead`, an object by the link fact), `knownValue` a slot,
  `allocated` an allocation or merge of slots, `created` a graph closure's
  creation, which allocates its two frames (`created_keeps`); so each keeps the
  heap (`base_keeps`, with `pure_inspect`);
- the calls: `elementsCall` and a `requiresCall` whose selected signature keeps
  the heap (`elementsCall_keeps`, `requiresCall_keeps`, from `selected_sound`,
  `requiresTree_sound` and `keepsHeap_prefix`), and with `freshCall_keeps`,
  `keepsCall_keeps` every call the pass frames (`callKeepsHeap_keeps`);
- the production checker accepts a preserving kind only where its base rule or
  `elementsCall` does (`ordinary_run_base`: every other call layer reads an
  `ordinary` step, the rest map the base's output), and a qualified body's
  checker only where its base rule does (`withSubtyping_run_base`); so every
  step the pass classifies preserving keeps the heap (`passPreserving_keeps`);
- both exits (`preserving_step_frame` for any checker given $`\mathrm{KeepsPost}`$,
  `pass_preserving_frame` at `Checker.ordinary`): from `run`'s output
  $`\mathit{out}`$ over the handed facts, a normal return is an action of
  $`\{\mathsf{values}:\mathsf{keep},\ \mathsf{stores}:\mathsf{keep}\}`$ with
  $`n'+k=n`$, the result's type, $`\mathit{out}`$ at $`\mathrm{push}\ v\ \rho`$ and
  $`\mathrm{Named}\ S\ \eta[r\mapsto v]`$; a throw is an action of $`\top`$ with
  the raised value closed and of the exception family and the heap-free part
  of $`S`$.

`ownCall` and `ensuresCall` steps are not preserving: the first only
excludes `keepsCall` (line 1296), the second is an `ordinary` step taking the
writing path.

The theorems above take the output of a checker's `run` (`hr`); the pass's
own conditions discharge it ([the selected output](#the-selected-output-under-the-passs-tree-check)).

### The selected output under the pass's tree check

Module `lean/Verification/Programs/TolerantFramesSelect.lean`. The pass takes a
step's output from `Checker.select` of the step's evidence (`SinglePass.lean`
1302 for a direct call, 1313 for a searched step, 1390 over every fact for a
writing step), and checks the step's derivation once (1318–1333) where its
checker's `select` checks nothing:

```
let tree := match effect with
  | .slicedRead _ _ _ e _ => some e
  | _ => effect.proof?
if let some p := (if selectChecks then none else tree) then
  if !checkTreeUsing G images p codes sums then
    if requiresTree G images kE codes sums p then preconditioned := some p
    else refuse
```

`passTree` is that `tree`, and `passTreeOk G images k codes sums e` that
condition at knowledge $`k`$. `passSteps` is the base checker whose `run` is
`Checker.steps`' `select` (`checkStepResult … (tree := false)`) where
`passTreeOk` holds; `ordinaryOver b` is `Checker.ordinary`'s layers over a base
$`b`$ (`Checker.ordinary = ordinaryOver (Checker.steps …)`, by definition);
`passOrdinary = ordinaryOver passSteps`. Proved:

- `requiresTree` roots at a call: the claimed term of its tree is an
  `invoke` or a `construct` (`requiresApp_term`, `requiresTree_term`); no kind
  but `ordinary` accepts such a term at `select` (`select_call_none`); the
  pass's tree is claimed at the step's term (`select_claim_term`);
- where `checkTreeUsing` accepts the tree, the base's `select` has `run`'s
  value for every kind but `typedRead` (`select_value_eq`);
- (`passSteps_value`) the base's `select` with `passTreeOk` gives one of:
  `checkStepUsing … = some out`; an `ordinary` step whose tree only
  `requiresTree` accepts, $`\mathit{out}=\mathrm{ordinaryOutput}\ k`$; or
  `typedRead`'s optional-field branch with its tree accepted with the codes.
  Each is sound (`passSteps_sound`): the first by `checkStep_sound`, the
  second by `requiresTree_sound`'s typing with the output's facts holding of
  every heap, the third by `optionalRead_sound` with the codes;
- (`ordinary_select_eq`) $`\mathrm{passTreeOk}\ k\ e \Rightarrow
  \mathrm{ordinary.select}\ j\ k\ e = \mathrm{passOrdinary.run}\ j\ k\ e`$:
  every layer reads its base at the same step; so the pass's selected output
  is `passOrdinary`'s `run` (`select_run`) and sound (`ordinary_select_sound`),
  and every theorem stated for a checker's `run` (`judgment_with_output`,
  `write_judgment`, `top_judgment`, `writing_frame`'s premise,
  `preserving_step_frame`) holds of it at `passOrdinary`;
- a qualified body's `select` is its `run` (`withSubtyping_select`);
- the preserving steps at the selected output: `ordinaryOver b` accepts a
  preserving kind only where $`b`$ or `elementsCall` does
  (`ordinaryOver_run_base`); `passSteps` keeps the heap at a preserving kind
  (`passSteps_keeps`); so `passPreserving_keeps_select`,
  `pass_preserving_frame_select` and `preserving_judgment_select` are
  `passPreserving_keeps`, `pass_preserving_frame` and `preserving_judgment`
  from the pass's conditions;
- a tree `checkTreeUsing` accepts passes the check at every knowledge
  (`passTreeOk_of_tree`).

The pass's checker (`SinglePass.PassChecker`, `SinglePass.lean` 819–840) is
`ordinary` (`Checker.ordinary`, whose `select` takes a derivation as given,
the pass checking its tree) or `qualified` (`Checker.withSubtyping`, whose
`select` is its `run`). The pass's tree check at the step's facts
$`k_E`$ (lines 1325–1333) is `passTreeCheck`: refused, or accepted with the
tree only `requiresTree` accepted (`preconditioned`); before a writing step's
`select` over every fact $`k_E'`$ that tree is checked again at $`k_E'`$
(lines 1386–1388, `passWholeCheck`). `passRunChecker` is `passOrdinary` for
the ordinary checker and the qualified body's checker itself. Proved:

- `passTreeCheck` accepting gives `passTreeOk` at $`k_E`$
  (`passTreeCheck_ok`), and with `passWholeCheck` at $`k_E'`$
  (`passWholeCheck_ok`), for the ordinary checker;
- (`pass_select_run`) where the checker's `select` checks nothing,
  `passTreeOk` at $`k`$, $`\mathrm{select}\ j\ k\ e=\mathit{out}\Rightarrow
  \mathrm{passRunChecker.run}\ j\ k\ e=\mathit{out}`$; so the output the pass
  applies over the step's facts (lines 1302 for a direct call, 1313 for a
  searched step, both `select` of the step's evidence) is its checker's `run`
  (`pass_select_narrow`), and the output over every fact (line 1390) too
  (`pass_select_whole`); it is sound (`pass_select_sound`);
- the preserving steps at either checker: `passPreserving_keeps_pass`,
  `pass_preserving_frame_pass`, `preserving_judgment_pass`.

**Where `run` and the pass differ**: `typedRead`'s optional-field branch.
`run` checks its tree with no codes (`fun _ => false`), the pass with the
codes, so `run` rejects a tree whose check consults a code entry. The output
is sound with the codes (`passSteps_sound`); `run` and the pass differ,
safety does not.

### The writing steps

Module `lean/Verification/Programs/TolerantFramesWrites.lean`. A step the pass
does not frame reads every fact (line 1322) and the store keeps what its rule's
output states. A named fact $`a`$ is kept by a closed effect $`c`$ when it reads
no heap or is an index fact $`c`$'s change keeps (`Atom.keptBy`). Proved:

- (Keep by atom) a kept fact survives every action of its effect
  (`atom_kept`), so $`\mathrm{Named}\ S\ \eta\vdash\Box_c\,\mathrm{Named}\ S\ \eta`$
  for $`S`$ kept by $`c`$ (`named_kept_box`); a length lower bound over names
  is kept by $`\{\mathsf{values}:\mathsf{any},\ \mathsf{stores}:\mathsf{grow}\}`$
  and by $`\{\mathsf{values}:\mathsf{any},\ \mathsf{stores}:\mathsf{keep}\}`$
  (`lowerBound_keptBy_grow`, `lowerBound_keptBy_field`);
- a run only grows the heap: a normal-only judgment holds on both exits with
  each exit's heap at least as long (`safePost_grow`);
- the judgments, in the form `NodesChecked` takes, each with `run`'s output
  $`\mathit{out}`$ on the normal exit (`judgment_with_output`): a write the
  pass's footprint check admits within $`c`$ (`write_judgment`, from
  `writeWithin`, line 1360), a typed field write within
  $`\{\mathsf{values}:\mathsf{any},\ \mathsf{stores}:\mathsf{keep}\}`$
  (`field_write_judgment`), an element write within
  $`\{\mathsf{values}:\mathsf{any},\ \mathsf{stores}:\mathsf{grow}\}`$
  (`element_write_judgment`), a step the pass frames, an allocation among them,
  normal exit within $`\{\mathsf{values}:\mathsf{keep},\ \mathsf{stores}:\mathsf{keep}\}`$
  and throw within $`\top`$ (`preserving_judgment`), and an ordinary call or
  expression within $`\top`$ on both exits (`top_judgment`);
- both exits (`writing_frame`): from such a judgment, a normal return is an
  action of $`c_n`$ with $`n'+k=n`$, the type, the post and the named facts
  $`c_n`$ keeps at $`\eta[r\mapsto v]`$; a throw an action of $`c_e`$ with the
  raised value closed and of the family and the named facts $`c_e`$ keeps.

`written` and `boundedWrite` acceptance does not imply `writeWithin` or
`fieldWriteWithin`; the effect a writing step has is what the pass's footprint
check gives ([the footprint check](#the-footprint-check-at-a-node)); the element facts
an effect keeps are [below](#element-facts-under-an-effect).

### Element facts under an effect

Module `lean/Verification/Programs/TolerantFramesElems.lean`.
`Atom.keptByElems c` extends `Atom.keptBy c` by two cases: an index atom whose
fact $`c`$'s change keeps as a quantified element fact
(`IndexFact.everyKept`: stores kept, no number changed, its length path, stop
and body terms kept), and an elements atom (`.elem`, `ElemsAt`: every present
element of the store meets the predicate) under
$`\{\mathsf{values}:\mathsf{keep},\ \mathsf{stores}:\mathsf{keep}\}`$. Proved:

- `keptBy_keptByElems`: it decides at least what `keptBy` decides;
- `atom_keptByElems`, `named_keptByElems_box`: a fact it keeps survives every
  action of $`c`$, so $`\mathrm{Named}\ S\ \eta\vdash\Box_c\,\mathrm{Named}\ S\ \eta`$
  for $`S`$ kept by $`c`$;
- `every_keptBy_init`: a quantified element fact over a slot's store with a
  slot's value as its stop and a body of kept terms is kept by the
  initialisation write's $`\{\mathsf{values}:\mathsf{init},\ \mathsf{stores}:\mathsf{keep}\}`$
  (`initEffect`); `elem_keptByElems_empty`: an elements atom by
  $`\{\mathsf{values}:\mathsf{keep},\ \mathsf{stores}:\mathsf{keep}\}`$.

A dense prefix is kept by $`\{\mathsf{values}:\mathsf{any},\ \mathsf{stores}:\mathsf{grow}\}`$
(`dense`); it is a semantic atom, not one of the pass's atoms. Under
$`\{\mathsf{values}:\mathsf{any},\ \mathsf{stores}:\mathsf{grow}\}`$ and
$`\{\mathsf{values}:\mathsf{any},\ \mathsf{stores}:\mathsf{keep}\}`$ neither
element fact is kept by its effect alone: a `grow` change admits a fresh store
entry, a `values: any` change any element value (observed in the definitions
of `Change.Holds`; no counter-model is formalized). The element writes and
field writes keep them through their rules' outputs (`IndexWrites.writeAtoms`,
`HeapExpressionRules.fieldEvery`), which read the written location and value.

### The footprint check at a node

Module `lean/Verification/Programs/TolerantFramesFootprint.lean`. Where the
invocation states a bound $`\Phi`$ (`SinglePass.lean` 1416–1451), the pass
evaluates at a node with sequent $`j`$, step knowledge $`k_S`$ (`stepK`), step
derivation $`d`$ (`stepDeriv`) and fresh receiver slots $`F`$:
`passWrites` (`writes`, 1431–1432: `writeWithin` or `initWriteWithin` at
$`\Phi`$), `passDerivChecked` (`derivChecked`, 1427–1430: $`d`$ claimed at the
node's term, its tree accepted by `checkTreeUsing` or by `requiresTree` at
$`k_S`$), `passWithin` (`within`, 1433–1435: an inspection, `passWrites`,
`selectedWithinAt Φ F d` with `passDerivChecked`, or a type no value has) and
`passThrows` (`throws`, 1443–1446, its first disjunct, which bounds no
throw, left out). Proved, for $`\mathrm{FreshOk}\ F\ b\ \rho`$ and
`DerivContext` (below):

- `pass_within_normal`: `passWithin` ⟹ the normal exit is within $`\Phi`$ on
  the locations below $`b`$ from the node's entry heap:
  $`\Phi.\mathrm{HoldsOn}\ (\cdot < b)\ h\ h'`$; `pass_within_throw`:
  `passThrows` ⟹ the throw is too;
- relative to the invocation's entry $`h_0`$ with $`b=|h_0|`$:
  $`\Phi.\mathrm{Holds}\ h_0\ h \wedge \Phi.\mathrm{HoldsOn}\ (\cdot<|h_0|)\ h\ h'
  \Rightarrow \Phi.\mathrm{Holds}\ h_0\ h'`$ (`pass_within_entry`, from
  `Closed.Holds.trans_on`), the composition `bound_step` and
  `action_compose_at` carry along the invocation;
- `pass_write_judgment`: `passWrites` ⟹ the step's judgment within $`\Phi`$ on
  the whole heap, both exits, with its rule's output: `write_judgment`'s
  `writeWithin` premise discharged at $`c=\Phi`$, the initialisation write
  included.

**`DerivContext`** (a named hypothesis, where `selectedWithinAt` holds): the
claim of $`d`$ is at the node's context. `passDerivChecked` compares the
claim's term only (`SinglePass.lean` 1428); the selected signature's
soundness (`selected_sound`, `requiresTree_sound`) is stated at the claim's
context. A conjunct `(claim deriv).context == c.context` there discharges it.

What the check does not give:

1. **The effect is the invocation's bound, not the step's.** The check
   establishes $`\Phi`$ (below $`b`$), so the per-step effect a writing step's
   judgment has is $`\Phi`$; a fact $`\Phi`$ does not tolerate is kept across
   a writing step only through the rule's output over every fact. A per-step
   effect tighter than the bound (a field write's
   $`\{\mathsf{values}:\mathsf{any},\ \mathsf{stores}:\mathsf{keep}\}`$, an
   element write's $`\{\mathsf{values}:\mathsf{any},\ \mathsf{stores}:\mathsf{grow}\}`$)
   would need the pass to evaluate `fieldWriteWithin` or `writeWithin` at that
   effect for the step, beside the bound check.
2. Where no bound is stated (`bound = none`) the pass checks no footprint; a
   writing step's judgment is then `top_judgment`'s.
3. `FreshOk F b ρ`, the receiver slots the pass records fresh (`entry.fresh`)
   holding stores allocated at or after the invocation's entry, is a premise:
   the pass's freshness tracking is not connected.

**The facts a writing step is not handed.** A step that may write
materializes every fact (`materialize … true`, `SinglePass.lean` 1370), and a
fact naming a name no slot holds fails to rename and is not among `pairs`.
Before the step's delta the pass removes each such fact that reads the heap
and keeps the heap-free ones (lines 1375–1380, the handler's filter): a
writing step's effect does not tolerate a heap fact it is not handed (a cell
fact over a name fails after an action of $`\top`$, proved:
`slotless_not_framed`).

## Allocated cells and separation

Module `lean/Verification/Semantics/TolerantFramesCells.lean`. A root's
allocated cells, $`\mathrm{cells}(x)`$ read at the heap, is
`HeapKnowledge.ElementsBelow` of the store $`x`$'s store location holds:
every listed cell below the heap's length (`RootCells`). It is not kept by
admissibility: in a world whose locations admit every value, a transition may
replace a store by one listing a cell past the heap (proved:
`rootCells_not_invariant`). It follows from a fact of the world instead:
$`x`$'s store location has a contract every store of which lists only cells of
its world (`StoreCells`, `CellsCtr`). Proved:

- every tuple contract lists cells of its world (`listT_cells`): a required,
  optional or rest position each states a lookup of its cell; so a location
  whose contract's stores meet a tuple contract establishes
  $`\mathrm{StoreCells}`$ (`cellsCtr_of_listT`, `storeCells_of_listT`);
- $`\mathrm{StoreCells}\ x`$ is invariant (`storeCells_invariant`: the
  contract persists, restricted, along every admissible transition), and
  gives $`\mathrm{cells}(x)`$ at the state, the heap meeting the contract one
  level down (`rootCells_of_storeCells`), so
  $`\mathrm{StoreCells}\ x\vdash\Box_\Phi\,\mathrm{cells}(x)`$ for every
  $`\Phi`$ (`rootCells_box`). No step needs to preserve the cells: the world
  fact covers every state reached.

A built-in array's store location has such a contract, proved
(`storeCells_of_arrayInvariant`, `TolerantFramesWrites.lean`): the array
invariant (`PositiveGraphs.arrayInvariant`) gives the store field a location
whose contract's stores are `builtinStoreT`, a tuple contract. What is not
connected: that a slot whose type has the `.list` clause meets the array
invariant (`builtinInvariant` applies it to records, dictionaries and
`source` clauses where the graph states the built-ins), and that `StableAt`
follows from the pass's path-preservation evidence. A root whose store location
admits any value carries no allocated-cell fact, and a step writing a store
that lists a cell past the heap there (a store value the program holds, not
an allocation, which reserves fresh cells: `elemSlots_above`) breaks it.

Separation, proved:

- allocation: a store whose location and cells are at or past $`b`$ is apart
  from a store whose location and cells are below $`b`$ (`alloc_apart`);
  freshness against the entry mark (`FreshAt`) is the location half;

The third atom, (Apart, one-sided), proved (`apart_grow_keep`), with
$`\Phi_x=\{\mathsf{values}:\mathsf{any},\ x.\mathsf{store}:\mathsf{grow}\}`$
(`growOne`) and $`y`$ an array object:

```math
\mathrm{apart}(x,y)\wedge\mathrm{cells}(y)\;\vdash\;\Box_{\Phi_x}\,\mathrm{apart}(x,y)
```

$`y`$'s store location is not $`x`$'s, so it is kept (`growOne_keeps_store`),
and $`x`$'s store gains only cells at or past the heap's end, beyond $`y`$'s
allocated cells and store location. Both stores growing is not covered: their
new cells may coincide.

## The pass's named state

Module `lean/Verification/Programs/TolerantFramesState.lean`. The pass's state
at a point (`SinglePass.State`, `SinglePass.lean` lines 165–170) is its slots'
names $`N`$, a store $`S`$ of facts over names (`Store`, lines 88–162) and the
names $`F`$ holding stores the invocation allocated; the walk keeps the
implications $`I`$ over names beside it (lines 961, 1767). The store's facts
are its live set's and those its index by name lists
($`\mathrm{all}(S)`$, `storeAll`).

**Meaning** (`StateHolds G st I start entry`), at the slot environment
$`\rho`$, the invocation's mark $`m`$ and the state $`s`$:

```math
\exists \eta.\;
(\forall i\,x.\ N[i]=x \Rightarrow \rho\,i=\eta\,x) \;\wedge\;
\mathrm{Named}\ \mathrm{all}(S)\ \eta \;\wedge\;
\mathrm{ImpliesOk}\ I\ \eta \;\wedge\;
(\forall x\in F.\ \mathrm{FreshAt}\ m\ (\eta\,x)) \;\wedge\;
(\forall q\,x.\ \mathit{start}[q]=x \Rightarrow \eta\,x=\mathit{entry}\ q)
```

$`\mathrm{ImpliesOk}`$ is `PromiseCalls.ImpliesOk` at the names: where the
test's name holds `true`, the target's value has the type. The valuation is
existential per state: a loop head's names denote new values on each visit,
and a name no slot holds denotes some value.

**Well-formedness** (`StateWF st next`, with $`\mathit{next}`$ the pass's next
fresh name), separate from the meaning:

| Conjunct | States | Kept by |
| --- | --- | --- |
| `store` | the store's well-formedness `StoreWF`: live facts canonical (`Atom.canon`); each fact the index lists under a name live, mentioning that name, listed there once | every insertion and removal (proved: `addRaw_wf`, `remove_wf`, `addBound_wf`, `add_wf`) |
| `below` | every name of the slots, the facts and $`F`$ is below $`\mathit{next}`$, so a result name is fresh (proved: `StateWF.fresh_result`) | construction (the counter only grows); not proved |
| `freshHeld` | every fresh name is held by a slot | edges (line 1758 filters the names an edge drops); a merge keeps a predecessor's name beside its fresh renames (lines 1142–1146), held or not; freshness reads no heap, so the meaning does not need it |

Soundness reads `below` (through `fresh_result`) and `store` (through
`removedLeave`).

**The store's laws**, proved from the lemmas of `Std.HashSet` and
`Std.HashMap` (the store's live facts and its index by name, `SinglePass.lean`
88–92): an insertion adds only its key or its list (`keys_insert`,
`vals_insert`), an erasure adds nothing (`keys_erase`), a list found under a
name is among the index's lists (`findD_vals`, `mem_valsOf`).

Proved, per fact and per store operation:

- `atomHolds_canon`: $`a.\mathrm{canon}`$ holds iff $`a`$ does;
  `atomHolds_rename`: a fact renamed by $`f`$ holds at $`\rho`$ where
  $`f\,x=i \Rightarrow \rho\,i=\eta\,x`$;
- adding a holding fact and removing any fact keep every
  fact of the store holding (`addRaw_ok`, `remove_ok`), a stronger bound
  replacing weaker ones (`addBound_ok`), a length fact added with the linear
  facts it means (`add_ok`, from `HeapKnowledge.atomLinear_holds`).

### The unit's entry

Module `lean/Verification/Programs/TolerantFramesEntry.lean`. The pass checks
the unit's entry before its walk (`SinglePass.entryRefusal`), and the start's
state is the head entry (`SinglePass.headEntry`) of its given invariant
(`startGiven`: the written assertion with the request's entry index facts
and separation, then the supplied facts, as `SinglePass.run` builds it) over
the start's names $`0,\dots,|\mathit{inputs}|-1`$. Proved:

- `entryRefusal_ok`: an accepted check gives the start's claim at the
  inputs, no given implication, the promised input at each slot named after
  it, each input's entry value at its own slot, and `entryKnows` of the
  written and supplied facts;
- `startGiven_holds`: from `EnvOk` at the inputs, the entry separation and
  the entry index facts, the given invariant holds at $`\rho`$
  (`entryKnows_sound`, `union_holds`);
- `headEntry_start_names`: each start slot is named by itself;
  `headStore_ok`: the head's store holds and is well-formed;
- (`entry_stateHolds`) $`\mathrm{entryRefusal}=\mathrm{none}\wedge
  \mathrm{EnvOk}\ \mathit{inputs}\ \rho \wedge \rho\models S_{\mathrm{entry}}
  \wedge \rho,h\models I_{\mathrm{entry}} \Rightarrow
  \mathrm{StateHolds}\ \mathit{st}_0\ \mathit{imp}_0\ [0,\dots]\ \rho`$ at $`\rho`$:
  the start's state holds, each start name holding its entry value, its store
  well-formed.

The start's names are $`0,\dots,w-1`$ in `run` (its `fresh` is 0 when they
are drawn), and the request's inputs are the start's context by the check.

### Materialization

Module `lean/Verification/Programs/TolerantFramesMaterialize.lean`.

`materialize` is `materializeFrom` at its selected facts (`materialize_eq`,
by definition): every live fact with `whole` (`selectedAtoms_whole`), else the
facts its worklist collects. Proved:

- the slot table maps each name to a slot holding it (`slotTable_get`); so
  each renamed fact holds at $`\rho`$ (`table_named`);
- the alias links between slots holding one name hold (`aliasLinksOf_holds`);
- the facts derived for names no slot holds, restated through read links and
  eliminated, hold at $`\eta`$ (`derivedOf_holds`, from `restateReads_holds`,
  `restateStores_holds`, `eliminateIndices_holds`);
- `ofAtoms` of holding facts at slots holds, its separation read at depth
  $`d`$ (`ofAtoms_holds`); a knowledge's facts hold as `atomsOf` lists them
  (`atomsOf_holds`);
- (`materializeFrom_holds`) where every selected fact holds at $`\eta`$ and
  each slot holds its name's value, the knowledge holds at $`\rho`$; each pair
  is a selected fact and its image under the table (`materializeFrom_pairs`).

From the state's meaning: the whole materialization holds
(`stateHolds_materialize_whole`); the selective one holds
(`stateHolds_materialize`), its facts drawn from the index by name; and the step's knowledge
$`k_E`$ and $`k_E'`$ (`kE` of `SinglePass.run`, over the step's facts and over every fact), each `expandLinks` at the
node's context, hold together where the environment meets that context
(`stateHolds_stepKnowledge`).

The selective worklist (`SinglePass.selectFrom`, `SinglePass.lean`
330–347) is rounds (`selectRound`) structural on a fuel of the store's size;
every fact it returns is listed by `Store.about` of some name (proved:
`selectRound_about`, `selectFrom_about`, `selectedFromIndex`).

### A step's delta

Module `lean/Verification/Programs/TolerantFramesDelta.lean`. `applyDelta`
(`SinglePass.lean` lines 373–403) is three loops (`applyDelta_eq`, by
definition): `deltaRemove` removes each handed fact whose image over the
pushed slots the output lost, `deltaAdd` adds each output fact not among the
images, renamed by `back`, and `deltaRestate` restates each added linear fact
over a read's name over the read's path. The pass's `back` (lines 1316–1317,
1331–1332) is `passBack`: slot 0 the result's name, a slot the table's
inverse gives its name, else the slot's name. Proved:

- `deltaRemove_sub`: the removal loop keeps only facts the store held;
  `deltaAdd_ok`: the facts added hold where the output holds at the pushed
  slots $`\rho'`$ and $`\mathit{back}\ i = x \Rightarrow \eta'\,x=\rho'\,i`$;
  `deltaRestate_ok`: the restated facts hold (`restateReads_holds`, the read
  links being the store's);
- (`applyDelta_ok`) where the facts the removal loop keeps hold at
  $`\eta'`$, every fact of the resulting store holds; (`applyDelta_preserving`)
  so where every fact of the store holds after the step;
- `passBack_ok`: the pass's renaming meets that condition at
  $`\rho'=\mathrm{push}\ v\ \rho`$ where $`\eta'`$ names the result $`v`$ and
  agrees with $`\eta`$ on the slots' names (`inverse_get`: the inverse sends a
  slot to a name the table sends to it).

The state after a step, proved:

- (`stateHolds_after`) from the state's valuation $`\eta`$ before the step
  and a valuation $`\eta'`$ agreeing with it on every name of the slots, the
  fresh names, the start names and the implications and naming the result,
  with the facts the removal loop keeps holding at $`\eta'`$ after an
  admissible transition and the output at the pushed slots, the pushed state
  holds at $`\mathrm{push}\ v\ \rho`$ (implications carried by
  admissibility of every type's meaning, `impliesOk_admissible`);
- a preserving step with a fresh result name (line 1309):
  $`\eta'=\eta[r\mapsto v]`$ with $`r`$ new (`ResultFresh`), from the frame's
  $`\mathrm{Named}\ \mathrm{all}(S)\ \eta[r\mapsto v]`$, which
  `pass_preserving_frame_select` gives with `StateWF.fresh_result`
  (`stateHolds_fresh_result`);
- a read of a slot keeping its name (line 1307): $`\eta'=\eta`$, the result
  slot $`i`$'s value (`stateHolds_reused_name`);
- a copy (lines 1203–1220): no step, the store unchanged, slot 0 named as
  slot $`i`$ (`stateHolds_copy`).

The writing case, proved (`applyDelta_writing`, module
`lean/Verification/Programs/TolerantFramesStore.lean`): for a well-formed
store, where every stored fact either holds after the step or is handed to
the rule (a pair $`(x,b)`$ with $`x`$ renamed to $`b`$ by a table whose slots
hold their names' values), every fact of the resulting store holds: a kept
handed fact's image is in the output, which holds at the pushed slots, and
reads back through the shift (`rename_succ_total`) and the table
(`atomHolds_rename_rev`) to the fact at $`\eta'`$. A handed fact whose image
the output lost leaves the store (`removedLeave`): `Store.remove` erases a
canonical fact from the live set and from each of its names' lists, which
hold it once, and no other list holds it (`remove_absent`), and the loop keeps
the store well-formed (`deltaRemove_wf`). The facts that hold after a writing
step are those its effect keeps (`writing_frame`, `Atom.keptByElems`). The
pass removes before the delta the heap facts it does not hand the step
(`Store.dropHeap` of the handed set, [the facts a writing step is not
handed](#the-footprint-check-at-a-node)): after it every fact is handed or
reads no heap and the store stays well-formed (`dropHeap_cover`), so where
the heap-free facts hold after the step, the output holds at the pushed
slots and `back` names each slot's value, every fact of the resulting store
holds (`applyDelta_dropHeap`).

### What the named state's proofs do not cover

The pass's operations are top-level functions of `SinglePass.lean`
(`headEntry`, `mergeState`, `checkedStep`, `edgeStoreOf`, `edgeTransfer`,
`Store.drop`, `Store.dropHeap`); the footprint, return and regional checks
and the edges' type, head and assertion checks are inline in `run`. Not
proved:

1. the merge (`mergeState`): every predecessor's `StateHolds` implies the
   merged state's, at predecessor-specific valuations extended to the fresh
   names; its equalities are proved (below), its met store, weakest bounds,
   entailed and guarded facts, fresh intersection and implications are not;
2. the head entry of a loop head other than the start, and an edge's store
   and transfer (`edgeStoreOf`, `edgeTransfer`);
3. `Store.drop`: its soundness is the materialization's elimination
   (`derivedOf_holds`) plus the alias restatement;
4. `checkedStep` as a whole: the theorems of the selected output, the
   preserving steps and the delta take its conditions as the definitions
   that mirror its code (`passTreeCheck`, `passWholeCheck`, `passWithin`,
   `passThrows`, `handedSet`), equal by unfolding, with no theorem about
   `checkedStep` itself;
5. `StateWF.below` maintained by the operations.

**A merge's equalities**, module
`lean/Verification/Programs/TolerantFramesMerge.lean`. At a merge
(`SinglePass.mergeState`) a predecessor renaming its name $`x`$ to fresh
names $`\varphi_1,\dots`$ states each $`\varphi`$ equal to $`x`$ where a slot
keeps $`x`$, and consecutive fresh names equal (`mergeEqual`, the merge's
`equal`; `mergeEqAtoms`, its `eqAtoms`): by an alias link, and by
$`\varphi-x\le 0`$, $`x-\varphi\le 0`$ where the predecessor's unconditional
facts make $`x`$ an integer (`Store.integral`). Proved:

- `index_safeInt`: the bits `indexOfBits` reads as $`i`$ are a safe integer
  $`i`$ ($`\pm 0`$, or `bitsOfNat i` by the uniqueness of a normal double's
  scaled value, `lex_scaled`);
- `integral_int`: where every fact of a store holds at $`\eta`$, a name
  `Store.integral` accepts holds a safe integer at $`\eta`$ (an `int`,
  `index`, length, bound or linear fact over its value);
- (`mergeEqual_holds`) where every fact of the predecessor's store holds at
  $`\eta`$, and $`\eta'`$ holds at each fresh name of $`x`$ the value $`\eta`$
  holds at $`x`$ and agrees with $`\eta`$ at every renamed name, every equality
  the merge states for that predecessor holds at $`\eta'`$.

`mergeEqual` is the merge's local `equal` with its `eqAtoms` unfolded (equal
by unfolding the `let`s); the merge theorem reads it there.

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
  condition a fact of the world supplies (`StoreCells`, above).
- **An action from a run needs the effect judgment.** Safety alone gives an
  admissible endpoint; the footprint comes from a postcondition relative
  to the run's first heap, on each exit (`action_normal`, `action_throw`).
  A graph run's footprint is the node judgments composed from the
  invocation entry and stated as the graph's exit posts (`invocation_action`).

## Leg 9: the step theorem about `checkedStep`

Modules `lean/Verification/Programs/TolerantFramesStepLink.lean` and
`lean/Verification/Programs/TolerantFramesStepLinkSound.lean`.

**`checkedStep` read as its conditions** (proved: `checkedStep_ok`, by
unfolding the pass's own function). An accepted step of node $`l`$ from the
entry state $`\mathit{st}_0`$ with result $`r`$ is

- a copy (`copiedOf`): the term is a slot $`i`$ whose context type is the
  claim's, $`r=\mathit{st}_0.\mathrm{names}[i]`$, the store unchanged, the
  answers unchanged; or
- a step (`StepAccepted`) at evidence $`e`$, with $`\mathit{sums}_0`$ the read
  summaries after the direct call (if any) and $`\mathit{sums}`$ those after
  the search (if any), the final answers: the output
  $`\mathit{out}=\mathrm{select}\ j\ k_E\ e\ \mathit{sums}`$ at the step's
  facts $`k_E`$ (`kOf`); the tree check
  $`\mathrm{passTreeCheck}\ k_E\ \mathit{sums}\ e=\mathrm{some}\ \mathit{pre}`$;
  the result $`(r,\mathit{fresh}')=\mathrm{resultOf}`$ (a slot's read keeps
  its name, else the fresh name); where
  $`\mathrm{passPreserving}\ j\ k_E\ e\ \mathit{sums}_0`$, the store
  $`\mathrm{applyDelta}\ \mathit{st}_0.\mathrm{store}\ \mathit{pairs}\ \mathit{out}`$
  with `passBack`; otherwise `passWholeCheck` at every fact $`k_W`$, the output
  $`\mathit{out}'=\mathrm{select}\ j\ k_W\ e\ \mathit{sums}`$ and the store
  $`\mathrm{applyDelta}\ (\mathit{st}_0.\mathrm{store}.\mathrm{dropHeap}\ (\mathrm{handedSet}\ \mathit{pairs}_W))\ \mathit{pairs}_W\ \mathit{out}'`$.

The call layers' test reads $`\mathit{sums}_0`$ and the selection
$`\mathit{sums}`$ (`SinglePass.lean` 1251, 1285): the preserving judgment is
stated at both (`passPreserving_keeps_two`, `preserving_judgment_two`).

**The step theorem** (proved: `checkedStep_sound`). Premises:
`checkedStep … = (ok st, _, ans)`;
$`\mathrm{StateHolds}\ \mathit{st}_0\ I\ \mathit{start}\ E`$ at $`\rho,m,s`$;
`StoreWF` of the entry's store; every name of the entry state, its start names
and its implications below the fresh counter (`NamesBelow`); the entry's names
no wider than the context; `EnvOk` of the context at $`\rho`$; `CodesSound`;
the incoming summaries checked. Conclusion: the outgoing summaries are checked;
`st.stepK` holds at $`\rho`$; $`r`$ is an entry name with the counter kept, or
the counter with the counter advanced; and for closed effects $`c_n,c_e`$
(`StepExits`):

- the local judgment of the node's term with normal post
  $`c_n\wedge\mathit{st}.\mathrm{stepOut}`$ at $`\mathrm{push}\ v\ \rho`$ and
  exceptional post $`c_e`$;
- a run with budget left to a value $`v`$: an action of $`c_n`$, $`n'+k=n`$,
  $`v`$ of the claim's type, `st.stepOut` at $`\mathrm{push}\ v\ \rho`$, and
  $`\mathrm{StateHolds}\ \langle r::\mathit{st}_0.\mathrm{names},\ \mathit{st}.\mathrm{store},\ \mathit{st}_0.\mathrm{fresh}\rangle`$
  at $`\mathrm{push}\ v\ \rho`$ (`stateHolds_pushed`, `preserving_store`,
  `writing_store`);
- a raise of $`x`$: an action of $`c_e`$, $`x`$ closed and of the exception
  family, and $`\mathrm{StateHolds}\ \langle\mathit{st}_0.\mathrm{names},\ \mathit{st}_0.\mathrm{store}.\mathrm{dropHeap}\ \bot,\ \mathit{st}_0.\mathrm{fresh}\rangle`$
  at $`\rho`$ (`stateHolds_throw`), the store a handler edge starts from.

The effects are $`c_n=\{\mathsf{values}:\mathsf{keep},\ \mathsf{stores}:\mathsf{keep}\}`$,
$`c_e=\top`$ at a preserving step, $`c_n=c_e=\top`$ at a writing step, and
$`c_n=c_e=\{\mathsf{values}:\mathsf{keep},\ \mathsf{stores}:\mathsf{keep}\}`$
at a copy.

Named hypotheses of the step theorem:

- `DirectKeepsSummaries`, `SearchKeepsSummaries`: `directCall` and
  `expressionEffectUsing` keep every summary of the answers' table checked
  (`checkReadSummary`). `summaryUsing` checks a summary before appending it
  (`CertificateProducer.lean` 625–651); no theorem states it of the search.
- `NamesBelow` and the width of the entry's names: invariants of the pass's
  states (`StateWF.below` with the start names and implications), not proved
  maintained.

The theorem gives no effect tighter than $`\top`$ at a writing step; the
footprint check gives the bound's.

## Leg 9: an edge's store and transfer

Module `lean/Verification/Programs/TolerantFramesEdge.lean`. The state's
meaning is existential in the name valuation $`\eta`$; an edge renames
slots, never names, so every operation of an edge keeps the facts holding at
the exit's $`\eta`$. Proved:

- `drop_ok`: `Store.drop` of any names keeps every fact holding at
  $`\eta`$ (the removed facts leave; a separation with fewer partners, a fact
  restated through an alias link, a derived linear fact each hold);
- `edgeStore_observed`, `edgeStore_promote`: the observation's facts at slot 0
  (`observeTyped` under the edge's context, `withElements`) and a branch's
  promoted truthiness (`promoteTruthy`) added by the delta keep the state
  holding, the delta's renaming reading back each slot's name
  (`edgeBack_ok`);
- `edgeTransfer_ok`: where each target slot is named by the name of the
  source slot the mapping reads (`MapNamesSound`) and a fresh result holds a
  store at or past the mark, the target's state (mapped names, dropped store,
  kept fresh names, implications naming no dropped name) holds at
  $`\mathrm{mapEnv}\ \theta\ \rho_x`$;
- `edge_normal_sound`: from the step's normal exit
  (`checkedStep_sound`) and the observation of its value (`ObservedOk`: a
  branch-binding's observation holds of $`v`$, a branch's answer is $`v`$'s
  truthiness), the state `edgeTransfer` builds from `edgeStoreOf` holds at
  $`\mathrm{mapEnv}\ \theta\ (\mathrm{push}\ v\ \rho)`$ on a pushed edge and at
  $`\mathrm{mapEnv}\ \theta\ \rho`$ on an unpushed one;
- `edge_handler_sound`: from the step's throw state, the thrown value at a
  name above every name, the handler's state at
  $`\mathrm{mapEnv}\ \theta\ (\mathrm{push}\ e\ \rho)`$;
- `freshImpl_ok`: where the step's yields hold of its value
  (`PromiseCalls.YieldsOk`), the implications a pushed edge states of its
  result hold (`stateHolds_addImplies` adds them).

**Interface between the head entry and the edge check.** An edge into a loop
head with given invariant $`\mathit{req}`$ over context $`\Delta`$
establishes (`EdgeEstablishes`) $`\mathit{req}`$ at
$`\mathrm{mapEnv}\ \theta\ \rho_x`$ and $`\Delta`$'s types there. Proved
(`head_query_sound`): the head query `checkIn` accepting, with the edge's
facts holding at $`\rho_x`$ and typed by the edge's context, gives the first
conjunct from the second.

Named hypotheses: `MapNamesSound` (`mapNames` reads the mapping's ordered
suffix by `orderedSuffix`, a `while` loop, which no proof unfolds; the
identity mapping is proved, `mapNamesSound_none`); the result's freshness
where `outFresh`; the step's yields (`YieldsOk`, which `yieldFollows_sound`
gives where `yieldFollows` accepts them; the pass does not evaluate
`yieldFollows`); the target's types at the mapped environment (the edge's type
check through `subtypeUsing`).
