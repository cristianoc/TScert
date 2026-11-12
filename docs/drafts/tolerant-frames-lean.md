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
$`\Phi`$), `passDerivChecked` (`derivChecked`: $`d`$ claimed at the
node's term and context, its tree accepted by `checkTreeUsing` or by `requiresTree` at
$`k_S`$), `passWithin` (`within`, 1433–1435: an inspection, `passWrites`,
`selectedWithinAt Φ F d` with `passDerivChecked`, or a type no value has) and
`passThrows` (`throws`, 1443–1446, its first disjunct, which bounds no
throw, left out). Proved, for $`\mathrm{FreshOk}\ F\ b\ \rho`$:

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

**The derivation's context.** `passDerivChecked`, as `footprintCheck`'s
`derivChecked`, compares the claim of $`d`$ with the node's term and context;
the selected signature's soundness (`selected_sound`, `requiresTree_sound`)
is stated at the claim's context, so it holds at the node's.

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
| `below` | every name of the slots, the facts and $`F`$ is below $`\mathit{next}`$, so a result name is fresh (proved: `StateWF.fresh_result`) | each store operation (proved: the store operations' table below) |
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

### A merge's equalities

Module `lean/Verification/Programs/TolerantFramesMerge.lean`. At a merge
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

## The step

Modules `lean/Verification/Programs/TolerantFramesStepLink.lean`,
`TolerantFramesStepLinkSound.lean` and `TolerantFramesStepLinkReturns.lean`.

**A step's conditions** (proved: `checkedStep_ok`, by unfolding the pass's
function). An accepted step of node $`l`$ from the entry state
$`\mathit{st}_0`$ with result $`r`$ is

- a copy (`copiedOf`): the term is a slot $`i`$ whose context type is the
  claim's, $`r=\mathit{st}_0.\mathrm{names}[i]`$, the store and the answers
  unchanged; or
- a step (`StepAccepted`) at evidence $`e`$, the call layers reading the
  summaries $`\mathit{sums}_0`$ of the answers after the direct call and the
  selection those, $`\mathit{sums}`$, after the search: the output
  $`\mathit{out}=\mathrm{select}\ j\ k_E\ e\ \mathit{sums}`$ at the step's
  facts $`k_E`$ (`kOf`); the tree check
  $`\mathrm{passTreeCheck}\ k_E\ \mathit{sums}\ e=\mathrm{some}\ \mathit{pre}`$;
  the result $`(r,\mathit{fresh}')=\mathrm{resultOf}`$; where
  $`\mathrm{passPreserving}\ j\ k_E\ e\ \mathit{sums}_0`$, the store
  $`\mathrm{applyDelta}\ \mathit{st}_0.\mathrm{store}\ \mathit{pairs}\ \mathit{out}`$;
  otherwise `passWholeCheck` at every fact $`k_W`$, the output
  $`\mathit{out}'=\mathrm{select}\ j\ k_W\ e\ \mathit{sums}`$ and the store
  $`\mathrm{applyDelta}\ (\mathit{st}_0.\mathrm{store}.\mathrm{dropHeap}\ (\mathrm{handedSet}\ \mathit{pairs}_W))\ \mathit{pairs}_W\ \mathit{out}'`$.

`StepChecked` is these conditions at some evidence and some answers whose
summaries are checked where the entry's are: the searches
(`directCall`, `expressionEffectUsing`) are oracles, and the evidence they
return is what `select` and the tree check read. Proved:
`stepChecked_of_step`, an accepted `checkedStep` is `StepChecked` under
`DirectKeepsSummaries` and `SearchKeepsSummaries` (each search keeps the
answers' summary table checked).

**The step theorem** (proved: `stepChecked_parts`, `stepChecked_sound`;
`checkedStep_parts`, `checkedStep_sound` are them at `stepChecked_of_step`).
Premises: `StepChecked`;
$`\mathrm{StateHolds}\ \mathit{st}_0\ I\ \mathit{start}\ E`$ at $`\rho,m,s`$;
`StoreWF` of the entry's store; every name of the entry state, its start
names and its implications below the fresh counter (`NamesBelow`); the
entry's names no wider than the context; `EnvOk` of the context at
$`\rho`$; `CodesSound`; the entry's summaries checked. Conclusion: the
final summaries checked; `st.stepK` holds at $`\rho`$; $`r`$ an entry name
with the counter kept, or the counter with the counter advanced; and for
closed effects $`c_n,c_e`$ (`StepParts`, `StepExits`):

- the local judgment of the node's term with normal post
  $`c_n\wedge\mathit{st}.\mathrm{stepOut}`$ at $`\mathrm{push}\ v\ \rho`$ and
  exceptional post $`c_e`$;
- a run with budget left to a value $`v`$: an action of $`c_n`$, $`v`$ of
  the claim's type, `st.stepOut` at $`\mathrm{push}\ v\ \rho`$, and
  $`\mathrm{StateHolds}\ \langle r::\mathit{st}_0.\mathrm{names},\ \mathit{st}.\mathrm{store},\ \mathit{st}_0.\mathrm{fresh}\rangle`$
  at $`\mathrm{push}\ v\ \rho`$;
- a raise of $`x`$: an action of $`c_e`$, $`x`$ closed and of the exception
  family, and $`\mathrm{StateHolds}\ \langle\mathit{st}_0.\mathrm{names},\ \mathit{st}_0.\mathrm{store}.\mathrm{dropHeap}\ \bot,\ \mathit{st}_0.\mathrm{fresh}\rangle`$
  at $`\rho`$, the store a handler edge starts from.

The effects are $`c_n=\{\mathsf{values}:\mathsf{keep},\ \mathsf{stores}:\mathsf{keep}\}`$,
$`c_e=\top`$ at a preserving step, $`c_n=c_e=\top`$ at a writing step, and
$`c_n=c_e=\{\mathsf{values}:\mathsf{keep},\ \mathsf{stores}:\mathsf{keep}\}`$
at a copy. The footprint check gives a writing step's bound.

**Returns, footprints and reads at a step** (proved):

- `plain_return`, `returnCheck_plain`: the plain goal's check gives a
  returned value of the claim's type the goal's type;
- `pass_return_ensures`, `returnCheck_ensures`, `passTracked_names`: where
  `returnCheck` refuses nothing, the state after the step gives `ensures`
  at the result and the invocation's entry values;
- `footprintCheck_sound`, `footprint_exits`, `pass_footprint_exits`: where
  `footprintCheck` accepts the node, the receiver slots it records fresh
  hold stores allocated at or past the mark (`FreshOk`, `freshOk_recv`),
  and each run with budget left keeps the bound $`\Phi`$ from the
  invocation's entry heap to the heap of its normal exit, and of its throw
  where a live handler catches it or the bound covers throws;
- `typedRead_optional_sound`: at a read of a field the slot's type states
  optional, the output `readFrame k i fld true` holds after the read;
- `namesBelow_step`, `width_step`: the state after the step is below the
  next counter, given its store's facts are, and no wider than the pushed
  context.

## The edge

Modules `lean/Verification/Programs/TolerantFramesEdge.lean`,
`TolerantFramesNodeEdges.lean`, `TolerantFramesNodeWalk.lean`,
`TolerantFramesNodeAsserted.lean` and `TolerantFramesComposeEdges.lean`.
An edge renames slots, never names, so every operation of an edge keeps the
facts holding at the exit's valuation $`\eta`$. Proved:

- `drop_ok`: `Store.drop` of any names keeps every fact holding;
- `edgeStore_observed`, `edgeStore_promote`, `edgeBack_ok`: the
  observation's facts at slot 0 and a branch's promoted truthiness, added by
  the delta, keep the state holding;
- `edgeTransfer_ok`: where each target slot is named by the name of the
  source slot the mapping reads (`MapNamesSound`), the target's state
  (mapped names, dropped store, kept fresh names, implications naming no
  dropped name) holds at $`\mathrm{mapEnv}\ \theta\ \rho_x`$;
- `edge_normal_sound`, `edge_handler_sound`: from the step's normal exit and
  the observation of its value, or from its throw state, the state
  `edgeTransfer` builds from `edgeStoreOf` holds at the target's
  environment; `freshImpl_ok`: where the step's yields hold of its value
  (`YieldsOk`), the implications a pushed edge states of its result hold;
- `exitDelivers_of_edge`, `handlerDelivers_of_edge`: an edge into a node
  other than a loop head delivers that state with its implications, where
  the walk records it among the target's incoming states;
  `exitDelivers_head`: an edge into a loop head establishes
  `HeadEstablishes` (`headEstablishes_of_edge`): the given facts by the head
  query (`head_query_sound` over the edge's materialized store), the given
  implications by an implication the edge carries with a type within the
  given one, the given inputs and the promised input by the slot-name
  checks;
- `edgeEvidenceChecked_env`, `checkedEdge_env`: where `edgeEvidenceChecked`
  accepts the edge search's evidence, the edge's facts holding and its
  context typing the source environment, the target's context types the
  mapped environment (the `htc` premise of the exit lemmas);
- `assertion_query_sound`: the check on an edge into a node stating an
  assertion gives the assertion at the target's environment;
- `edgeStoreOf_wf`, `edgeTransfer_wf`, `edgeTransfer_width` (under
  `MapNamesLength`), `edgeStoreOf_below`, `edgeTransfer_below`: the
  target's state well-formed, of the mapping's width and below the counter.

`ofNode_flags`: an exit of `Exit.ofNode` observes only where it pushes and
promotes only where it does not, the premises `hpo` and `hpp` of the exit
lemmas.

## The store operations

Modules `lean/Verification/Programs/TolerantFramesStoreOps*.lean` and
`TolerantFramesMergeBelow.lean`. Each operation against the conjuncts of
`StateWF`: `StoreWF`, the slot and fresh names below the counter, the facts'
names below the counter (`FactsBelow`). Every cell is proved.

| Operation | `StoreWF` | names, fresh below | facts below |
| --- | --- | --- | --- |
| `Store.addRaw`, `remove`, `addBound`, `add` | `addRaw_wf`, `remove_wf`, `addBound_wf`, `add_wf` | unchanged | `addRaw_below`, `remove_below`, `addBound_below`, `add_below`, for a fact below |
| `applyDelta` | `applyDelta_wf` | slot 0 the result name | `applyDelta_below`, where `back` renames below the counter (`BackBelow`) |
| `Store.dropHeap` | `dropHeap_cover` | unchanged | `dropHeap_below` |
| `Store.drop` | `drop_wf` | unchanged | `drop_below` (the eliminations name their inputs' names: `eliminateIndices_named`) |
| `edgeStoreOf` | `edgeStoreOf_wf` | — | `edgeStoreOf_below` |
| `edgeTransfer` | `edgeTransfer_wf` | `edgeTransfer_below` | `edgeTransfer_below` |
| `mergeState` | `mergeState_wf` | `mergeState_wf` | `mergeState_below` |
| `headEntry` | `headStore_ok` | `headEntry_below` | `headEntry_below` |

`freshHeld` (every fresh name held by a slot) does not hold of a merge: a
predecessor's fresh name stays beside its fresh renames (`mergeFresh`) when
no slot of the merge holds it. No proof reads it.

## The merge

Modules `lean/Verification/Programs/TolerantFramesMergeMirror.lean` to
`TolerantFramesMergeChecked.lean`.

**The merge in parts.** `SinglePass.mergeState` is the composition of its
parts, by unfolding (proved: `mergeState_state`, `mergeState_implies`,
`mergeState_fresh`): the names and renamings (`mergeSlots`), the
restatements (`mergeVariants`), the common facts (`mergeCommon`), the
restated facts every predecessor states (`mergeMeet`), the names renamed
away forgotten (`mergeMet0`, `Store.drop`), the differences (`mergeDiffs`),
the weakest bounds (`mergeBounds`), the entailed bounds (`mergeEntailed`),
the guarded join (`mergeGuarded`, `mergeAddGuarded`), the fresh names
(`mergeFresh`) and the implications (`mergeImplies`).

**The path's valuation.** On the path through predecessor $`p`$, whose state
holds at $`\eta`$ and slot environment $`\rho`$, the merge's valuation is

```math
\eta'(y) = \begin{cases} \eta(y) & y < \mathit{fresh} \\ \rho(i) & \text{for a slot } i \text{ the merge names } y \\ \eta(y) & \text{otherwise} \end{cases}
```

(`mVal`). Proved: the first loop's invariant (`mergeSlots_inv`), one value
per merged name (`slots_same`), each slot its merged name's value
(`mergeVal_slots`), a fresh rename of $`x`$ the value of $`x`$
(`mergeVal_rename`).

**The merged store on the path** (proved): the common facts are live facts
of every predecessor (`mergeCommon_live`); $`p`$'s restatements hold
(`OnPath.variants_ok`), so the met store and each difference hold
(`OnPath.met0_ok`, `OnPath.diffs_ok`); a weakest bound holds
(`OnPath.bounds_ok`); an entailed bound holds where it passes the check
below (`OnPath.entailed_ok_checked`); the guarded facts hold
(`OnPath.guarded_ok` with `guardedHolds_of_path`: each fact the join keeps
passes `indicesCheckWith` against every predecessor's view, among them
$`p`$'s, through `guardReads_path`, `lowerRead_holds`, `lowerGuards_holds`,
`check_holds`, `OnPath.projection_holds`); the fresh names hold fresh
stores (`OnPath.fresh_ok`).

**The entailed bounds' check.** A term denotes what its kind reads of the
value its path reads from its slot (`termValue`); no term is defined at
every valuation (`termValue_value_undef`, `termValue_length_num`). The
merge adds an entailed bound only where every view passes
`SinglePass.entailDefinedCheck q a F`: $`q`$'s store holds $`a`$ as a live
fact, or every term of $`F`$ is one `termDefined` accepts over the facts the
entailment reads, `q.store.linearNear a.names`. Proved:
`checked_bound_holds`, `mergeEntailed_inv` (the merge's own check is the
premise the bound's holding reads).

**The facts near a merge's names.** `linearNearFuel s names limit fuel` is
`Store.linearNear`'s search by structural recursion on `fuel` (default
`s.size + 1`): each round (`nearRound`) reads every frontier name's facts and
keeps an unconditional index fact not kept yet while fewer than `limit` are
listed (`nearStep`); the rounds run while the frontier is non-empty
(`nearLoop`). Proved: `linearNearFuel_sound`, every fact it lists is an
unconditional `index` fact of the store, at any fuel;
`linearNearSound_of_eq`: `LinearNearFuelEq` (the pass's `linearNear` is
`linearNearFuel` at fuel `s.size + 1`) gives `LinearNearSound`.

**The joined implications.** The pass records each edge into a merge as
$`(\Gamma_e, \mathit{atSlots}, m)`$: the source's context, the implications
the edge carries restated at the source's slots (`atSlotsOf`), the edge's
mapping. The merge keeps a joined implication $`x`$
(`CertificateProducer.meetImplications`) only where every incoming edge
passes

```math
\mathrm{impliesCheck}\ G\ \Gamma_e\ \mathit{atSlots}\ m\ [x] = \mathit{true}
```

(`joinedChecked`). Proved: `atSlots_ok`; `meetImplications_ok_of_check`:
for a recorded edge whose context types the source environment $`\rho_s`$,
where the edge's implications hold, the kept implications hold at
$`\mathrm{mapEnv}\ m\ \rho_s`$; `mergeImplies_ok_of_check`: the merge's
implications then hold at its valuation.

**(Merge)**, proved (`mergeState_holdsAt_checked`, `mergeState_holds_checked`
its existential form): for predecessors `preds`, $`p`$ below their number,
the merge's first fresh name $`\mathit{fresh}`$,

```math
\begin{aligned}
&\forall q\in\mathit{preds}.\ |q.\mathit{names}| = |\mathit{context}| \wedge \mathrm{StoreWF}\ q.\mathit{store} \wedge \mathrm{StateBelow}\ q\ \mathit{fresh}
\ \wedge\ \forall x\in\mathit{start}.\ x<\mathit{fresh}
\\ &\wedge\ \mathrm{LinearNearFuelEq}
\ \wedge\ \mathrm{ImpliesOk}\ (\mathrm{joinedChecked}\ \mathit{edgesIn})\ \rho
\ \wedge\ \mathrm{StateHoldsAt}\ \mathit{preds}[p]\ \eta\ \rho
\\ &\Rightarrow\ \mathrm{StateHoldsAt}\ (\mathrm{mergeState}\ \dots).\mathit{state}\ (\mathrm{mergeState}\ \dots).\mathit{implies}\ \eta'\ \rho
\end{aligned}
```

**(Merge below)**, proved (`mergeState_below`, with `mergeState_wf`): a
non-empty list of predecessors of the context's width, well-formed and below
$`\mathit{fresh}`$, gives a merged state below its next fresh name.

## The head

Module `lean/Verification/Programs/TolerantFramesMergeHead.lean`. A loop head
enters with `SinglePass.headEntry g false`: slot $`i`$ named by the start
name a given input `(i, q)` names, else by the promised input's start name
where the slot is among its slots, else by $`\mathit{fresh}+i`$; the store
is the given facts $`g`$ renamed to those names; the next fresh name
$`\mathit{fresh}+\mathit{width}`$. Its valuation (`headVal`) gives a start
name `startNames[q]` the entry value $`\rho_0(q)`$ and $`\mathit{fresh}+i`$
the value of slot $`i`$.

**What an edge establishes at a head** (`HeadEstablishes`), at the head's
environment $`\rho'`$ and the state $`s`$: $`g`$ holds at $`\rho', s.h`$; the
given implications hold; for each given input $`(j,q)`$,
$`\rho'(j)=\rho_0(q)`$; for each promised-input slot $`j`$,
$`\rho'(j)=\rho_0(q)`$ for the start name $`q`$ the promised input is.
Proved:

- `headEntry_holds`: start names distinct and below $`\mathit{fresh}`$ ∧ the
  promised input a start name ∧ `HeadEstablishes` ⟹ the head's state with
  its implications holds at $`\rho'`$, its store well-formed;
- `headsEntered_of_recorded`: a walk recording each edge state into a head
  as the head's entry enters its heads (`HeadsEntered`).

**The start.** The pass enters the start with `headEntry g true` (each slot
named by its own start name) where no edge enters it, and with
`headEntry g false` as any head where one does; `g` is `startGiven`, the
written assertion with the entry index facts and separation and the
supplied facts. Proved: `entryRefusal_ok`, `startGiven_holds`,
`entry_stateHolds`; `start_passPreT` (no edge into the start) and
`start_entered_passPreT` (an edge into it, the counter at or past the
inputs' width): where `entryRefusal` accepts, the start's typed assertion
holds at every entry meeting the inputs, the separation and the index facts.

## The walk

Modules `lean/Verification/Programs/TolerantFramesMergeGraph.lean`,
`TolerantFramesNodeSound.lean`, `TolerantFramesNodeWalk.lean`,
`TolerantFramesWalkReassignNodes.lean` and
`TolerantFramesWalkReassignWalk.lean`.

**The node assertion.** A walk (`Walk`) records the visited labels, each
visited node's entry state and implications, and the states with
implications edges carry into each node. At label $`l`$,
$`\mathrm{passPreT}\ l = \mathrm{passPre}\ l\wedge\mathrm{EnvOk}\ (\mathit{ctx}\ l)`$:
$`l`$ visited, its entry state holding with the start names at the entry
values, its context typing the environment; $`\mathrm{edgePreT}\ t`$: an
edge state into $`t`$ holds and $`t`$'s context types the environment.
Proved: `passPre_adminClosed`, `passPreT_adminClosed` (the assertions
survive the administrative steps), `nodeObligations_mono`.

**The walk's construction** (`Traversed`): every node an edge state enters
is visited; a node with no given facts and one incoming state enters with
it; with several, with `mergeState` of them over its context, merge edges
and fresh counter, each incoming state of the context's width, well-formed
and below the counter, the start names below it. `MergesSound`:
`LinearNearFuelEq`, and at each merge the kept joined implications
(`joinedChecked`) wherever an edge state into it holds. Proved:

- (`entries_of_traversed`) `Traversed` ∧ `HeadsEntered` ∧ `MergesSound` ⟹
  `EntriesFromEdges`: a node's entry state holds wherever an edge state into
  it holds (a head by `HeadsEntered`, one incoming state as it is, several by
  `mergeState_holds_checked`);
- (`run_sound_of_walk_typed`) `Traversed` ∧ `StepEdgesSoundT` ∧
  `HeadsEntered` ∧ `MergesSound` ∧ `passPreT` at the start ⟹ `SafeGraph`
  from the start, by `graph_safe_at`. `StepEdgesSoundT`: from `passPreT` at
  every visited node, the node's local judgment and every exit an
  `edgePreT` of its target.

**A node of the walk.** `NodeRan` holds the pass's values and checks at a
visited node: the node and its claim, the label's context the claim's, the
entry state, `checkedStep`'s equation, the store well-formed, `NamesBelow`,
the width, the entry's summaries checked. `NodeChecked` is `NodeRan` with
`StepChecked` in place of the step's equation (`NodeRan.checked`, under
`DirectKeepsSummaries` and `SearchKeepsSummaries`). `NodeMeaning`, about a
node's values and the written assertions `stated`, is what they mean at a
graph: the entry state holding where `passPreT` does (`entered`), the
claim's type giving each continuation's shape (`shape`) and a return's
result type (`ret`), each normal exit and the handler delivering the
target's typed and written assertion (`exits`, `handler`, at `edgePreA`).
`NodeAccepted` is `NodeRan` with these fields at `edgePreT`. Proved:

- `nodeObligations_of_parts`: the step's parts and the meaning give the
  node's `NodeObligations`;
- `stepEdgesSound_of`: `NodeAccepted` at every visited label ∧ `CodesSound`
  ∧ `DirectKeepsSummaries` ∧ `SearchKeepsSummaries` ⟹ `StepEdgesSoundT`;
- `stepEdgesSound_of_checked`: `NodeChecked` with its `NodeMeaning` at every
  visited label ∧ `CodesSound` ⟹ `StepEdgesSoundA` (`StepEdgesSoundT` with
  the targets' `edgePreA`), with the exception family `excOf G` and no heap
  post.

**Every continuation.** `ShapeOk` asks a Boolean at a `branch` and a
`branchBind`, nothing at a `tagBind`; `NormalTarget` at `branchBind y n` is
the arm of the Boolean at the pushed environment, at `tagBind tg y n` the
arm of `tagHoldsIn h tg v`, as `Transition.yesBind`, `noBind` and `tagBind`
take them. `graph_step`, `normalTarget_of_exits` (each exit observing what
its arm tests: `ofNode_flags`, `tagHolds_of_heap`), `nodeObligations_mono`
and `nodeShape_of` (the shape check `passShapeCheck`: a Boolean type at a
`branch`, `onlyBoolean` at a `branchBind`) are proved at every
continuation.

**What `Traversed` requires of the traversal**, stated for the driver's
walk: every cycle of reached nodes passes through a node `isHead` marks
(`HeadsCutCycles`), which `loopHeads` gives where it marks every target of a
retreating edge of a complete depth-first walk (every cycle of a graph
contains a retreating edge of any complete depth-first walk, a standard fact
of depth-first search, not proved here); and a node other than a head
processed after every edge into it from a reached node (the in-degree
order), so that a merge's incoming list is complete.

## The guarantee

Modules `lean/Verification/Programs/TolerantFramesGuaranteeRuns.lean`,
`TolerantFramesGuarantee.lean`, `TolerantFramesGuaranteeWalk.lean`,
`TolerantFramesNodeBound.lean`, `TolerantFramesNodeReturns.lean`,
`TolerantFramesNodeAsserts.lean`, `TolerantFramesNodeGoals.lean`,
`TolerantFramesNodeCallFresh.lean`, `TolerantFramesRegionalNode.lean` and
`TolerantFramesRegionalRuns.lean`.

**Run properties.** A property of the graph machine's states
(`StateKeeps X Q R`) is $`X`$ at a node entry, at each node's exits the
target's $`X`$ (`EvalKeeps`), $`Q`$ at `.done v` and $`R`$ at `.raised`. A
node keeps it (`NodesKeep P pre X Q R`) when from every state where its
assertion and $`X`$ hold every run of its term meets its exit's obligation;
it holds at every stronger assertion (`nodesKeep_anti`). Proved:
`keeps_step`, `keeps_postExc` (`NodesChecked` ∧ `AdminClosed` ∧
`NodesKeep` ⟹ $`\mathrm{SafePostExc}\ \Xi\ T\ Q\ R`$), `reached_pre`.

**The node assertion** every field reads:

```math
\mathrm{passPreU}\ l\ \rho\ m\ s \iff \mathrm{passPreT}\ l\ \rho\ m\ s \wedge \mathrm{AssertsAt}\ \mathit{stated}\ l\ \rho\ s \wedge \mathrm{StableNow}\ \mathit{fields}\ \rho_0\ h_0\ s.W
```

the typed assertion, the label's written assertion (`passPreA`), and the
regional bound's traversed fields of the entry values fixed in the current
world (none without a regional bound, `regionFields`). Proved:
`passPreU_adminClosed`; (`nodesChecked_of_walk`) `WalkSound` (`Traversed`,
`StepEdgesSoundA`, `HeadsEntered`, `MergesSound`) ⟹ `NodesChecked` at
`passPreU` (`nodesChecked_of_walkA`, and `nodesChecked_stable`: a property
every admissible transition keeps joins the obligations). The written
assertion reaches every entry by the edges, since the entry state does not
entail every written fact (a fact with a slot no name holds is not added,
`Store.addBound` skips a bound for one of the same normal form, a
separation fact carries no level bound): `assertsAt_of_edge`
(`assertion_query_sound`), `assertsAt_of_head`, `assertsAt_start`,
`exitDeliversA_of`.

**The fields.** `GraphGuarantee` is the unit lane's record field by field
(`GraphGuarantee.toTarget`, `transitions_of_reachesIn`). `PassWalkSound`
holds `WalkSound` at every entry value and mark; the start's `passPreA` at
every entry meeting the inputs, the separation and the index facts
(`entered`); the traversed fields fixed at such an entry (`stable`); the
per-node hypotheses; each assertion of the request the written assertion at
its label (`labelled`). Proved: (`run_guarantee`) `PassWalkSound` at
`reassign G η` for every admitted $`\eta`$ ⟹ `GraphGuarantee`, each field
at `passPreU`:

| Field | By | Per-node hypothesis |
| --- | --- | --- |
| `safe` | `graph_safe_at` | none |
| `bounded` | `keeps_postExc` | `FootprintKept`: `NodesKeep` at `passPreT` with $`X`$ the label in the region `dead` or $`\Phi`$ from $`h_0`$, $`Q`$ $`\Phi`$ with the value fresh where `fresh`, $`R`$ $`\Phi`$ where `onThrow` |
| `ensured` | `keeps_postExc` | `ReturnsEnsured`: `NodesKeep` at `passPreT` with $`Q`$ `EnsuresAt ensures h (push v ρ0)` |
| `regionally` | `keeps_postExc` | `RegionsKeptS`: `NodesKeep` at `passPreS` (`passPreT` and `StableNow`) with the regional facts $`X`$, holding at the start, and $`Q`$, $`R`$ `ArgumentStoreRegionsWithin Φ regions ρ0 h0` |
| `asserted` | `reached_pre`, `holds_of_assertsAt` | `labelled` |

**The per-node hypotheses from the pass's checks**, proved over
`NodeAccepted`:

- (`footprintKept_of`) `NodeAccepted` at mark $`|h_0|`$ ∧ `BoundChecked`
  (`deadNode` inside `dead`, `footprintCheck` outside it) ∧
  `CallFreshBelow` at every visited node ∧ `CodesSound` ∧
  `DirectKeepsSummaries` ∧ `SearchKeepsSummaries` ⟹ `FootprintKept`;
  `CallFreshBelow`: where `outFresh` reads a fresh result off the
  derivation's selected effect, every run within the budget returns a store
  allocated at or past the mark; (`callFresh_of_checked`) the derivation
  passing `passDerivChecked` gives it, the mark at most the heap's length;
- (`returnsEnsured_of`) `NodeAccepted` ∧ `ReturnChecked` at every visited
  node ∧ `CodesSound` ∧ `DirectKeepsSummaries` ∧ `SearchKeepsSummaries` ⟹
  `ReturnsEnsured`;
- (`goalHolds_of_return`) `returnCheck` accepting ∧ `SubtypeAnswersSound`
  (an accepted `subtypeUsing` answer an inclusion of meanings) ∧ the
  promised input the start name of the goal's slot ∧ the state after the
  step holding at $`\mathrm{push}\ v\ \rho`$ ∧ `YieldsOk` of the return's
  yields ⟹ a guard's or an assertion's goal of the returned value
  (`returnOk_of_check`, `passHeld_argument`, `goalHolds_at`);
- (`regionsKept_of`) `RegionNodeOk` at every visited node ⟹ `RegionsKeptS`
  with $`X`$ the regions within and the graph's tables holding
  (`RegionX`); `RegionNodeOk.ofCheck`: the check `run` makes over the
  node's tables (`checkNode_sound`), their agreement with the graph's
  (`TablesAgree`, `checkNode_mono`, `meet_sub`), `RegionalTyped` (the
  evidence's `ExpressionOk`) and the evidence's entry
  (`regionNodeEntry_of`); `regionalTyped_of_tree`: the step's derivation
  claimed at the node's term and context with its tree accepted
  (`regionalDerivChecked`) gives `RegionalTyped`; `regionX_start`.

## The reassignment

Modules `lean/Verification/Programs/TolerantFramesWalkReassign*.lean`.

**How the proved checker covers every assignment.** Its rules' soundness
theorems are stated for every graph at the graph's own assignment; its
acceptance at `G` is its acceptance at `reassign G η`
(`Parametricity.accept_reassign`); so one check gives safety at every
$`\eta`$. A qualified body's subtyping (`BodySubtyping`) is sound at the
graph's own assignment only; `RequestJson.verify_qualified_safe_at` gives
safety at an admitted instance `assign η source.binders As` from the lexical
body check.

**The same route for the pass.** Every theorem above is stated for every
graph. Proved, the pass's functions at a reassigned graph, the answers
carried by `Answered.reassign`: `codesSound_reassign`,
`Parametricity.summariesSound_reassign`, `footprintCheck_reassign`,
`subtypeSearch_reassign`, `subtypeUsing_reassign`, `returnCheck_reassign`,
`edgeStoreOf_reassign`, `entryRefusal_reassign`, `mergeState_reassign`
(each equal at `reassign G η`), `directCall_reassign` (through
`forIn_map_state`), `ordinarySelect_reassign`, `headQuery_reassign`,
`assertionQuery_reassign`, `edgeEvidenceChecked_reassign`.

**The searches as oracles.** `PassCheckerReassign pc pc'`: `pc'` checks the
tree where `pc` does and its `select` has the same value as `pc`'s at `G`.
Proved:

```math
\mathrm{StepAccepted}\ G\ I\ pc\ \dots\ e\ \dots\ st\ \wedge\ \mathrm{PassCheckerReassign}\ pc\ pc'\ \Longrightarrow\ \mathrm{StepAccepted}\ (\mathrm{reassign}\ G\ \eta)\ (I.\mathrm{reassign}\ \eta)\ pc'\ \dots\ e\ \dots\ st
```

(`stepAccepted_reassign`), and with it `stepChecked_reassign`,
`nodeChecked_reassign` (a node checked at `G` is checked at
`reassign G η`, the answers reassigned); `passCheckerReassign_ordinary`;
`passCheckerReassign_qualified`, `passCheckerReassign_lexical` (a qualified
body's checker at each instance its scheme admits within its bounds);
`scope_reassign` (a checker's scope, `CheckerScope`, gives the checker at
each admitted assignment); `Traversed.reassign`; `StartEntered.entered`.

## The graph theorem

Modules `lean/Verification/Programs/TolerantFramesGuaranteeTarget.lean` (the
unit lane's definitions, copied from `PassUnit.lean` at c99647d3 on
`engine-proof-unit`) and `TolerantFramesRunSound.lean`.

`RunWalk G I c`, what the driver records of an accepted call: a walk, the
label contexts, each merge's edges and counter, the loop heads, the written
assertions by label (`stated`); every visited node `NodeChecked` at `G`;
`Traversed`; each edge state into a head the head's entry; `StartEntered`
(`entryRefusal` accepting with the start's written assertion, the start's
entry `headEntry` over `startGiven` as the start or as any head, its
context the inputs).

**(`run_sound`)**, proved:

```math
\mathrm{RunTraversed} \wedge \mathrm{NodesMean} \wedge \mathrm{LinearNearFuelEq} \wedge \mathrm{MergesImpliesHold} \wedge \mathrm{FootprintsKept} \wedge \mathrm{ReturnsKept} \wedge \mathrm{RegionsHeld} \wedge \mathrm{AssertionsLabelled} \Longrightarrow \mathrm{RunSound}
```

`RunSound` is the unit lane's statement: for an accepted `RunCall`, under
its `CheckerScope`, with `CodesSound` and `SummariesSound` of the summaries
it leaves and the regions' entry fields check, `GraphGuarantee` of its
options at its inputs. The proof carries each checked node to every
admitted assignment (`scope_reassign`, `nodeChecked_reassign`), gives the
node obligations there (`stepEdgesSound_of_checked`), the heads entered
(`headsEntered_of_recorded`), the start's typed and written assertion
(`StartEntered.entered`), the traversed fields at the start
(`checkEntryFields_sound` from the call's premise, `checkEntryFields_reassign`),
the walk's construction (`Traversed.reassign`), and assembles the guarantee
(`run_guarantee`, `GraphGuarantee.toTarget`). Each premise is a definition
of `TolerantFramesRunSound.lean`, quantified over every call the premises of
`RunSound` hold of and every walk it records.

## Open premises

The hypotheses of `run_sound`, each with what discharges it and the theorem
that consumes it. Pass changes are named by the pass lane's items; the pass
lane (`engine-pass`) is at 7fd1fedb, where D1 (the edge evidence), D2 (the
yields), D3 (the joined implications), D4 (a fresh result off a checked
derivation) and the entailed bounds' check have arrived.

| Premise | Discharged by | Consumed by |
| --- | --- | --- |
| `RunTraversed` | a pass change: the driver on fuel returning a `Walk` (not arrived), then a proof `run_traversed` composing: `NodeRan.checked` at each visited node, under `DirectKeepsSummaries` and `SearchKeepsSummaries` (pass change D6, a `summaries_sound` field of `Answered`, not arrived) and the entry's summaries among the final ones (`RunKeepsSummaries`, the same driver); `NamesBelow` and the width at each entry (proofs to write along the walk from `namesBelow_step`, `edgeTransfer_below`, `mergeState_below`, `headEntry_below`); `Traversed`'s fields (the in-degree order and `HeadsCutCycles`: `loopHeads` on fuel, a pass change not arrived, and the depth-first fact, a proof to write; `width` under `MapNamesLength`, pass change D7, `mapNames` on fuel, not arrived; `wf`, `below` proved per edge); the heads' records, `stated` and `StartEntered`, read off the driver | `run_sound` (the walk, the checked nodes, `Traversed.reassign`, `headsEntered_of_recorded`, `StartEntered.entered`) |
| `NodesMean` | per field: `entered`, the entry state where the node assertion holds, read off the driver; `shape`, `nodeShape_of` given `passShapeCheck` at the node (a pass change: the Boolean tests at a `branch` and at a `branchBind`, D9, not arrived); `ret`, `returnCheck_plain` at a plain goal, `goalHolds_of_return` at a guard or an assertion goal under `SubtypeAnswersSound` (D5, not arrived) and `YieldsOk` (from D2's `checkedYields` through `yieldFollows_sound`, a proof to write), a proof to write restating `ret` at the state after the step; `exits`, `exitDelivers_of_edge`, `exitDelivers_head` with `exitDeliversA_of`, `assertsAt_of_edge`, `assertsAt_of_head`, under `MapNamesSound` (D7, not arrived), `YieldsOk` (as above), the result's freshness (`callFresh_of_checked`, D4 arrived, a proof to write at the edge), the target's types (`checkedEdge_env`, D1 arrived; an edge accepted by subtype answers alone, D5) and a given implication's type (D5); `handler`, `handlerDelivers_of_edge` with the written assertion | `stepEdgesSound_of_checked` |
| `LinearNearFuelEq` | a pass change: `Store.linearNear` on fuel `s.size + 1` as `linearNearFuel` (not arrived) | `mergeState_holdsAt_checked`, through `MergesSound` |
| `MergesImpliesHold` | a proof to write: the walk records, for each state into a merge, its edge among `edgesIn` with the source's context typing the source environment and the carried implications holding there, then `meetImplications_ok_of_check` (the merge's per-edge check is the pass's, `joinedChecked`) | `entries_of_traversed`, through `MergesSound` |
| `FootprintsKept` | `footprintKept_of`, over `NodeAccepted`, under `BoundChecked` and `CallFreshBelow`; proofs to write: `BoundChecked` over the pass's `outFresh` with the call disjunct behind `derivChecked` (D4, arrived; `passOutFreshChecked`), `CallFreshBelow` from `callFresh_of_checked` (the mark at most the heap's length at a node entry), and the theorem over `NodeChecked` at the reassigned graph (`stepChecked_parts` in place of `checkedStep_parts`) | `run_guarantee` (`bounded`) |
| `ReturnsKept` | `returnsEnsured_of`, over `NodeAccepted`, under `ReturnChecked`; a proof to write: the same over `NodeChecked` | `run_guarantee` (`ensured`) |
| `RegionsHeld` | `regionsKept_of` from `RegionNodeOk` at every visited node (`RegionNodeOk.ofCheck`); left: `RegionalTyped` (`regionalTyped_of_tree` given `regionalDerivChecked` of the step's derivation at the regional check, a pass change D11, not arrived; a step with no derivation, a proof to write), `TablesAgree` at every visited node (the meet over every predecessor, from the in-degree order of `RunTraversed`) | `run_guarantee` (`regionally`) |
| `AssertionsLabelled` | a pass change D10: `run` refuses a repeated assertion label or joins the assertions a label states (`byLabel` keeps the first; not arrived) | `run_guarantee` (`asserted`) |

## Leg 17a: the per-node hypotheses from the pass's checks

Modules `lean/Verification/Programs/TolerantFramesNodeBound.lean` (the
values `run` reads at the footprint check), `TolerantFramesNodeCallFresh.lean`,
`TolerantFramesNodeReturns.lean` and `TolerantFramesComposeRunSound.lean`.

**The footprint check at a checked node.** `BoundChecked r Φ dead ret exc`
is `run`'s check at a node `r : NodeChecked` under the bound
$`(\Phi, \mathit{ret}, \mathit{exc})`$: inside `dead`, `deadNode` and
$`\mathit{exc}=\mathit{false}`$; outside it, `footprintCheck` at the step's
values with `outFresh` as `run` computes it (`passOutFreshChecked`: a copy
of a slot holding a fresh name, or a call stating a fresh result, its
operands selected, whose derivation `derivChecked` accepts). Proved:

- `passOutFreshChecked_cases`: the call disjunct gives `passCallFresh` and
  `passDerivChecked` at the node's sequent, the premises of
  `callFresh_of_checked`;
- (`footprintKept_of`) every visited node checked, its entry state holding
  where `passPreT` does at mark $`|h_0|`$, and `BoundChecked` ∧ `CodesSound`
  ⟹ `FootprintKept`; outside `dead` the heap $`h`$ is within $`\Phi`$ from
  $`h_0`$, so $`|h_0| \le |h|`$ (`Post`'s first conjunct), the mark
  premise of `callFresh_of_checked`;
- `BoundChecked.reassign`, `passOutFreshChecked_reassign`: the check at `G`
  is the check at `reassign G η`.

**The return check at a checked node.** `ReturnChecked r goal ensures`:
at a return, `returnCheck` at the step's values refuses nothing. Proved:
(`returnsEnsured_of`) every visited node checked, its entry state holding
where `passPreT` does, and `ReturnChecked` ∧ `CodesSound` ⟹
`ReturnsEnsured`; `ReturnChecked.reassign`.

**The graph theorem from the checks.** `BoundsChecked` (under the call's
bound, some region `dead` with `BoundChecked` at every visited node of the
walk, at `G`) and `ReturnsChecked` (where the call states `ensures`,
`ReturnChecked` at every visited node) are the driver's checks at the nodes
it visits. Proved: `footprintsKept_of_checked` (`NodesMean` ∧
`BoundsChecked` ⟹ `FootprintsKept`), `returnsKept_of_checked`
(`NodesMean` ∧ `ReturnsChecked` ⟹ `ReturnsKept`), and

```math
\mathrm{RunTraversedA} \wedge \mathrm{NodesMean} \wedge \mathrm{LinearNearFuelEq} \wedge \mathrm{MergeExitsJoined} \wedge \mathrm{BoundsChecked} \wedge \mathrm{ReturnsChecked} \wedge \mathrm{RegionsHeld} \wedge \mathrm{AssertionsLabelled} \Longrightarrow \mathrm{RunSound}
```

(`run_sound_17a`). `BoundChecked` over `NodeAccepted`, the mirror
`passOutFresh` and `CallFreshBelow` are replaced by these.

**The merges' joined implications at the exits** (module
`TolerantFramesNodeJoined.lean`). The walk side's `joinedAt` and
`ExitsJoined` (Leg 18b) state the obligation. Proved: (`joinedAt_of_exit`)
an edge recorded into $`t`$ as
$`(\Gamma_e, \mathrm{atSlotsOf}\ \mathit{names}\ \mathit{carried}, m)`$,
its source environment $`\rho_s`$ typed by $`\Gamma_e`$, its slots holding
$`\mathit{names}`$' values at $`\eta`$, the carried implications holding at
$`\eta`$ ⟹ `joinedAt` at $`\mathrm{mapEnv}\ m\ \rho_s`$. `ExitsJoined` is
discharged per exit by it, given the driver's record of the edge and
$`\Gamma_e`$ typing the source environment: at a handler edge $`\Gamma_e`$
is the node's context; at a normal edge it is the context as the step's
yields refine it, typed where the kept yields hold of the step's value.

**The kept yields at the values the step returns** (module
`TolerantFramesNodeYields.lean`). `run` keeps a step's yields where
`checkedYields` accepts them: outside a call at a promise signature, those
`yieldFollows` accepts of the node's term. `NodeMeaning`'s `ret` and
`exits` are stated for every value of the claim's type; a guard's goal and
the implications a pushed edge states of its result hold only of the
values the step returns, so `NodeYielded` restates them there, with the
yields `ys` read at the implications `xs`. Proved:

- `SafePostExc.conj_post`: a run safe with postconditions $`Q, R`$ and
  safe with a value property $`T'`$ is safe with $`T'`$, $`Q`$ and $`R`$;
- `checkedYields_follows`: outside a promise call, every kept yield passes
  `yieldFollows`;
- (`stepYields_judgment`) the yields passing `yieldFollows` ∧ the context
  typing $`\rho`$ ∧ `ImpliesOk xs` ∧ the step's links holding ∧ the step's
  judgment ⟹ the judgment with each value meeting the claim's type and
  `YieldsOk ys` (`yieldFollows_sound`);
- `nodeObligations_of_partsY`, (`stepEdgesSound_of_yields`) `NodeChecked`
  ∧ `NodeMeaning` (entry, shapes, handler) ∧ `ExitsJoined` (handler) ∧
  `NodeYielded` (the yields accepted, `xs` holding at the entry, the return's
  goal and each exit from the state after the step and the yields at the
  value) at every visited label ∧ `CodesSound` ⟹ `StepEdgesSoundAt`
  at `edgePreAJ`;
- `exitDeliversY_of_edge`: `exitDelivers_of_edge` with the yields read at
  the step's value and the target's types from the edge's check where they
  hold, so an exit's `YieldsOk` premise and a refined context's typing come
  from the state after the step.

`NodeYielded.ret` is `goalHolds_of_return`'s premises with the yields at
the value (its yields `passReturnYields entry ys`).

**A copy's regional evidence** (module `TolerantFramesRegionalRuns.lean`).
Proved: (`regionalTyped_copy`) a term that is a slot whose context type is
the claim's, with no derivation and no step evidence, gives the regional
evidence's context the node's and `RegionalTyped`: the term's value is the
slot's, of the claim's type, with no yields and no output facts.

Premises this leg discharges / leaves:

- discharges `FootprintsKept` (into `BoundsChecked`, a record of the
  driver's walk) and `CallFreshBelow`;
- discharges `ReturnsKept` (into `ReturnsChecked`, a record of the
  driver's walk);
- leaves `BoundsChecked` and `ReturnsChecked` to the driver on fuel
  (`RunTraversedA`'s walk records them).
- leaves `ExitsJoined`
  per exit to `joinedAt_of_exit` with the driver's record and the typing of
  the refined context.
- discharges the yields premise of the exits and the return (`YieldsOk`
  at every value) into `NodeYielded`, whose `follows` field is
  `checkedYields_follows` outside a promise call; leaves: a promise call's
  kept yields (`checkedYields`' promise branch keeps them by
  `promiseYields` and the output, where `promiseCall_sound` needs the
  derivation's tree, which `run` checks of the step's evidence, not of
  `stepDeriv`: a pass change), `xs` holding at the entry (`slotImplOf`
  over the state's implications, a proof to write), the head edge's
  version of `exitDeliversY_of_edge`, and the walk's predicates over
  `StepEdgesSoundAt` at `edgePreAJ`.
- discharges `RegionalTyped` at a copy (`regionalTyped_copy`, where the
  copy's `stepDeriv` and `stepEffect` are none, which `StepChecked`'s copy
  case does not yet state); leaves `RegionalTyped` at a step with step
  evidence alone (the rule's judgment at every state where the evidence's
  facts hold) and with a derivation (D11, `regionalTyped_of_tree`).

## Leg 17b: the walk side of the graph theorem

Modules `lean/Verification/Programs/TolerantFramesMergeExits.lean` and
`TolerantFramesMergeNearRounds.lean`.

**A merge's joined implications come with the exit into it.** The pass
records each edge into a merge as $`(\Gamma_e, \mathrm{atSlotsOf}\ \mathit{names}\ \mathit{carried}, m)`$
beside the state `edgeTransfer` carries, whose implications are
$`\mathit{carried}`$ and whose names are `mapNames names m`
(`MergeEdgeRecorded`, what `RunWalk` records of it). A kept joined
implication holds at the target environment $`\mathrm{mapEnv}\ m\ \rho_s`$
of an exit whose source environment $`\rho_s`$ meets $`\Gamma_e`$ and whose
carried implications hold at the source's valuation (proved:
`joined_of_exit`, from `meetImplications_ok_of_check` and `atSlots_ok`).
The edge state's meaning (`StateHolds`) reads names, facts and
implications, not types, and the merge keeps an implication whose target
slot's source type is within it (`impliesFollows`, its second disjunct)
without the edge stating it. So `MergesImpliesHold`, the joined
implications wherever an edge state into the merge holds (`edgePre`), is
stronger than the pass establishes (observed from the definitions, no
counterexample built): the joined implications are delivered by the exit.
An exit into a merge delivers

```math
\mathrm{edgePreJ}\ t\ \rho\ m\ s \iff \mathrm{edgePre}\ t\ \rho\ m\ s \wedge (t \text{ a merge} \Rightarrow \mathrm{ImpliesOk}\ (\mathrm{joinedChecked}\ (\mathit{ctx}\ t)\ (\mathit{edgesIn}\ t))\ \rho)
```

and the entries follow from it. Proved: `entry_of_edge` (the entry state
where an edge state holds with, at a merge, the joined implications; from
`Traversed`, `HeadsEntered`, `LinearNearFuelEq`), `entries_of_traversed`
by it, `entries_of_traversedJ` (`edgePreJ` ⟹ `passPre`).

**The rounds of the search near a merge's names.** Over a store with
`StoreWF` (each fact an `about` list holds is live), more fuel than
$`|s| + 1`$ returns the same facts:

```math
\mathrm{StoreWF}\ s \Rightarrow \mathrm{linearNearFuel}\ s\ \mathit{names}\ \mathit{limit}\ (|s| + 1 + k) = \mathrm{linearNearFuel}\ s\ \mathit{names}\ \mathit{limit}
```

(proved: `linearNearFuel_rounds`). The search's invariant `NearInv` (each
listed fact kept, listed facts distinct and live) bounds the listed facts
by $`|s|`$ (`NearInv.out_le`); a round leaving a non-empty next frontier
lists one more (`nearRound_progress`); so the loop has ended once its fuel
exceeds the facts left unlisted (`nearLoop_stable`).

Premises this leg discharges / leaves:

- `MergesImpliesHold`: left, and replaced in the decomposition by what the
  exits deliver: `NodeMeaning`'s exits and handler into a merge deliver
  `edgePreJ` (per edge, `joined_of_exit` at the exit's source environment,
  the per-node side), the walk records `MergeEdgeRecorded`; then
  `entries_of_traversedJ` takes the place of `MergesSound`'s second
  conjunct. `run_sound`'s statement is unchanged until the per-node side's
  exits deliver `edgePreJ`.
- `LinearNearFuelEq`: the rounds bound discharged (`linearNearFuel_rounds`);
  left: the equation of the pass's `while` loop with `linearNearFuel`, and
  the terms an entailment reads named by the facts it reads.

## Leg 18b: the driver's record read as the walk

Modules `lean/Verification/Programs/TolerantFramesMergeWritten.lean` and
`TolerantFramesDriverWalk.lean`.

**The written facts at an entry.** At a node other than a loop head the
pass adds its written assertion's facts to the state it enters with (the
single incoming state or the merge), each atom renamed from its slot to the
name the slot holds, an atom with a slot no name holds left out
(`withWritten`), and records that state as the label's entry. So the
record's entry is not the single incoming state or the merge where the
label states an assertion, and `Traversed`'s `single` and `merge` fields do
not hold of it. `TraversedA` states the walk's construction over entries
`base` before the addition (`Traversed` of the walk with entries `base`),
each label's entry being `base t` at a head and
`withWritten (stated t) (base t)` elsewhere. Proved: `withWritten_holds`
(the state with the facts added holds where the state and the written
assertion hold), `withWritten_wf`, `TraversedA.reassign`; `entry_of_edgeA`:

```math
\mathrm{TraversedA} \wedge \mathrm{HeadsEntered} \wedge \mathrm{LinearNearFuelEq} \wedge \mathrm{edgePre}\ t\ \rho\ m\ s \wedge \mathrm{AssertsAt}\ \mathit{stated}\ t\ \rho\ s \wedge (t \text{ a merge} \Rightarrow \mathrm{ImpliesOk}\ (\mathrm{joinedChecked}\ \dots)\ \rho) \Longrightarrow \mathrm{passPre}\ t\ \rho\ m\ s
```

and with it `passPreA_of_edgeAJ`: `edgePreAJ` (`edgePreA` with, at a merge,
the joined implications) gives `passPreA`.

**The driver.** `SinglePass.drive` visits the queue's first node on fuel.
Proved: a drive that returns made its visits, each from the queue's first
node over the rest of the queue, until the queue is empty (`Drives`,
`drives_of_drive`, `Drives.queue`); a property every visit keeps holds of
its result (`Drives.inv`); an accepted call either stopped with an accepted
outcome or returned a record visiting at least the nodes the start
reaches, its answers the call's (`walk_of_accepts'`, from `run` being the
record's `Walk.outcome`); with `WalkStopsRefuse` (a stopped walk is never
accepted), the latter (`walk_of_accepts`).

**The record as the proof's walk** (`ofPass`, with the loop heads
`passHeads`, the start and `loopHeads`' targets as `runWalk` marks them): a
label visited where its record says so; its recorded entry state and
implications; into a node other than a head, the states and implications
the processed edges carried; into a head, its own entry where a processed
edge enters it, so each edge state into a head is the head's entry by
construction (proved: `ofPass_heads`). The label contexts, written
assertions, merge edges and merge counters are the call's and the record's
(`passCtx`, `passStated`, `passEdgesIn`, `passFresh`). `RecordSound`, what
the record must give: every visited node `NodeChecked`, `TraversedA`, the
start entered. Proved: (`run_traversedA`) `WalkStopsRefuse` ∧
`RecordsSound` ⟹ `RunTraversedA`, the driver's walk `RunWalkA` (`RunWalk`
with `TraversedA`) of every accepted call.

**A merge's joined implications on the exits.** The pass keeps a joined
implication at a merge only where every incoming edge passes
`PromiseCalls.impliesCheck` over the edge's context $`\Gamma_e`$ as the
source's yields refine it, its implications at the source's slots and its
mapping (`joinedChecked`). That check gives the kept implications at the
target environment $`\mathrm{mapEnv}\ m\ \rho_s`$ of an exit whose source
environment $`\rho_s`$ meets $`\Gamma_e`$ and whose carried implications
hold (`joined_of_exit`). It does not give `edgePreJ` at an edge state alone:
the edge state's meaning reads names, facts and implications, and the
check reads $`\Gamma_e`$'s types at the source, which no edge state and no
target type states (the merge's own context types the target, not the
source's refined context). So the joined implications are an obligation of
the exit, stated beside the exits' other obligations: `joinedAt` (at a
merge, the kept implications at the environment) and `ExitsJoined` (each
normal exit and the handler of a node delivering `joinedAt` of its
target). `NodeMeaningAt pre` is a node's meaning with its exits and handler
delivering `pre`, `NodeMeaning` the one at `edgePreA`;
`StepEdgesSoundAt pre` is `StepEdgesSoundA` at `pre`. Proved:
`stepEdgesSound_of_checkedAt` (`NodeChecked` with `NodeMeaningAt pre` at
every visited node ∧ `CodesSound` ⟹ `StepEdgesSoundAt pre`),
`NodeMeaning.withJoined` (`NodeMeaning` ∧ `ExitsJoined` ⟹
`NodeMeaningAt edgePreAJ`), `nodesChecked_of_walkJ`:

```math
\mathrm{TraversedA} \wedge \mathrm{StepEdgesSoundAt}\ \mathrm{edgePreAJ} \wedge \mathrm{HeadsEntered} \wedge \mathrm{LinearNearFuelEq} \Longrightarrow \mathrm{NodesChecked}\ \mathrm{passPreA}
```

`PassWalkSound`'s walk field is `NodesChecked` at `passPreA` at every entry
value and mark; `nodesChecked_of_walk` gives it at `passPreU`.

**(`run_sound`, restated)**, proved:

```math
\mathrm{RunTraversedA} \wedge \mathrm{NodesMean} \wedge \mathrm{LinearNearFuelEq} \wedge \mathrm{MergeExitsJoined} \wedge \mathrm{FootprintsKept} \wedge \mathrm{ReturnsKept} \wedge \mathrm{RegionsHeld} \wedge \mathrm{AssertionsLabelled} \Longrightarrow \mathrm{RunSound}
```

`RunWalkA` is `RunWalk` with `TraversedA`; `MergeExitsJoined`: at every
admitted reassigned graph, every visited node of the walk meets
`ExitsJoined` (the per-node side's route: `joined_of_exit` at the exit,
given the walk's `MergeEdgeRecorded` and the source environment meeting the
edge's refined context). Every other premise is the one of the earlier
statement, over `RunWalkA`.

**The loop heads cut every cycle.** Module
`lean/Verification/Programs/TolerantFramesDriverHeads.lean`.
`SinglePass.loopHeads` is a `while` loop over the marks, the node states (0
new, 1 on the stack, 2 done) and a stack of frames, each a node with its
successors not yet examined. `dfsStep` is one round of it over functions in
place of arrays, `dfsLoop` the rounds on fuel, `dfsInit` the start;
`LoopHeadsFuelEq` (named hypothesis) is the equation of the pass's loop with
them: it ends at a fuel where the mirror's stack is empty, with the
mirror's marks and states. `HeadsCutCycles succ n reached heads`: no path of
edges from a reached node to a successor below $`n`$ that is no head
(`NonHeadEdge`) returns to its node. With ghost finishing times $`f`$ below
a counter, the rounds keep `DfsInv`: the done nodes are those with a time;
each done node's successors below $`n`$ are heads or done at an earlier
time; each frame's examined successors are heads, done, or nodes of frames
above it (`FramesOk`); a node in state 1 is a frame's node and every
frame's node is in state 1, the frames' nodes distinct. Proved:
`dfsStep_inv`, `dfsLoop_inv`, `dfsInit_inv`; (`dfs_cuts`) on an empty
stack every reached node is done, so each non-head edge between reached
nodes goes to an earlier time ($`f(b) < f(a)`$, `Path.rank_lt`) and no such
path is a cycle; `loopHeads_cuts` (under `LoopHeadsFuelEq`, the marks
`loopHeads` returns cut every cycle of the nodes it reaches);
`HeadsCutCycles.mono`; `passHeads_cuts` (the call's heads, the start
marked besides). No depth-first path theorem is used.

**(`run_sound_18b`)**, proved (`run_sound` with `run_traversedA`):

```math
\mathrm{WalkStopsRefuse} \wedge \mathrm{RecordsSound} \wedge \mathrm{NodesMean} \wedge \mathrm{LinearNearFuelEq} \wedge \mathrm{MergeExitsJoined} \wedge \mathrm{FootprintsKept} \wedge \mathrm{ReturnsKept} \wedge \mathrm{RegionsHeld} \wedge \mathrm{AssertionsLabelled} \Longrightarrow \mathrm{RunSound}
```

**What the record lacks for `RecordsSound`** (pass changes, each a field
or a definition the proof reads):

- `runWalk`'s visit and setup as top-level functions (the visit is a local
  `fun` of `runWalk`, which no statement can name), so that each visit's
  effect on the record is a theorem over the visit and `Drives.inv` carries
  it to the walk's end;
- per label, the fresh counter the step starts from, the answers it starts
  from and its `Stepped` result (`NodeChecked`'s `fresh`, `answers`, `st`),
  and the counter on entry (the start's `StartEntered` counter);
- the loop heads (`isHead`) in the record, or exposed by the setup
  (`passHeads` restates them);
- a stop type without acceptance (`WalkStopsRefuse` by its type);
- `loopHeads` on fuel as `dfsLoop` (`LoopHeadsFuelEq` by construction);
- `Store.linearNear` on fuel as `linearNearFuel` (`LinearNearFuelEq`).

Premises this leg discharges / leaves:

- `RunTraversed`: restated as `RunTraversedA` (the record's entries hold
  the written facts, which `Traversed` did not state) and reduced by
  `run_traversedA` to `WalkStopsRefuse` and `RecordsSound`; the heads'
  records discharged by the reading (`ofPass_heads`). Left: `RecordsSound`
  (each visited node `NodeChecked`, `TraversedA`, `StartEntered`, read off
  the visit once it is a function), `WalkStopsRefuse`.
- `HeadsCutCycles`: discharged under `LoopHeadsFuelEq` (`passHeads_cuts`),
  for the proof of `TraversedA`'s merges; left: the in-degree order (a
  node other than a head visited after every edge into it from a reached
  node) and `TablesAgree` from it, both over the visit.
- `MergesImpliesHold`: replaced by `MergeExitsJoined`, the exits into a
  merge delivering its joined implications (`ExitsJoined`, the per-node
  side's, by `joined_of_exit` at the source environment meeting the edge's
  refined context); the pass's per-edge check does not give them at an
  edge state alone.
- `LinearNearFuelEq`, `RunKeepsSummaries`: left (`Store.linearNear` is a
  `while` loop; the answers are threaded by the visit).
