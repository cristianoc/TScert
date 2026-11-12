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

## Leg 8: the merge

Modules `lean/Verification/Programs/TolerantFramesMergeMirror.lean`,
`TolerantFramesMergeNames.lean`, `TolerantFramesMergeMeet.lean`,
`TolerantFramesMergeJoin.lean`, `TolerantFramesMergeHolds.lean` and
`TolerantFramesStoreOpsDrop.lean`.

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

(`mergeVal`). Proved: the first loop's invariant (`mergeSlots_inv`: a slot
keeps the predecessors' common name or takes the fresh name of their names'
vector, distinct vectors distinct fresh names, each renaming sends a name to
fresh names of slots where the predecessor holds it); two slots with one
merged name hold one value (`slots_same`); each slot holds its merged name's
value under $`\eta'`$ (`mergeVal_slots`); a fresh name $`\varphi`$ that $`p`$
renames $`x`$ to has $`\eta'(\varphi)=\eta(x)`$ (`mergeVal_rename`), and a
renamed name is below $`\mathit{fresh}`$ (`rename_key_below`).

**Forgetting names**, proved: `Store.drop` keeps every fact holding
(`drop_ok`: removed facts leave, a separation fact keeps its partners outside
the dropped names, a fact restated through an alias link holds by the link,
`keptAliasOf_eq`, the derived facts by `eliminateIndices_holds`,
`restateReads_holds`, `restateStores_holds` over facts of the store,
`dropDerived_holds`) and keeps the store well-formed (`drop_wf`).

**The merged store**, proved on the path through $`p`$ at $`\eta'`$:

- the common facts are live facts of every predecessor (`mergeCommon_live`);
- $`p`$'s restatements hold (`OnPath.variants_ok`: `renameEach_holds`, and
  `mergeEqual_holds`), so the met store holds (`OnPath.met0_ok`) and so does
  each fact $`p`$ states beyond it (`OnPath.diffs_ok`);
- a weakest bound: each predecessor's map holds a bound of the form that is
  one of its facts (`boundsOf_get`), the bound added is at least each
  (`weakestStep_cases`), and a weakened bound in normal form holds
  (`linear_weaken`, `normalize_vars`): `OnPath.bounds_ok`;
- an entailed bound: `Store.holds` is sound for an unconditional linear fact
  whose terms are defined (`holds_sound`), and `entailsKnown_sound` over the
  facts `linearNear` lists: `OnPath.entailed_ok`;
- the guarded facts renamed by the merge's names: `OnPath.guarded_ok`;
- each part as a property of stores closed under the facts it adds
  (`mergeMeet_inv`, `mergeBounds_inv`, `mergeEntailed_inv`,
  `mergeAddGuarded_inv`), instantiated at holding (`OnPath.store_ok`) and at
  well-formedness.

**(Merge)**, proved (`mergeState_holdsAt`, `mergeState_holds` its
existential form): for predecessors `preds`, $`p`$ below their number, the
merge's first fresh name $`\mathit{fresh}`$,

```math
\begin{aligned}
&\forall q\in\mathit{preds}.\ |q.\mathit{names}| = |\mathit{context}| \wedge \mathrm{StoreWF}\ q.\mathit{store} \wedge \mathrm{StateBelow}\ q\ \mathit{fresh}
\\ &\wedge\ \forall x\in\mathit{start}.\ x<\mathit{fresh}
\ \wedge\ \mathrm{LinearNearSound} \wedge \mathrm{EntailedDefined}_\eta \wedge \mathrm{GuardedHolds}
\\ &\wedge\ \mathrm{ImpliesOk}\ (\mathrm{meetImplications}\ \mathit{edgesIn})\ \rho
\ \wedge\ \mathrm{StateHoldsAt}\ \mathit{preds}[p]\ \eta\ \rho
\\ &\Rightarrow\ \mathrm{StateHoldsAt}\ (\mathrm{mergeState}\ \dots).\mathit{state}\ (\mathrm{mergeState}\ \dots).\mathit{implies}\ \eta'\ \rho
\end{aligned}
```

where $`\mathrm{StateHoldsAt}`$ is $`\mathrm{StateHolds}`$ at a given
valuation (`stateHolds_iff`) and $`\mathrm{StateBelow}`$ is the type of
`StateWF.below`. The implications hold where the edges' joined implications
hold at the slots (`mergeImplies_ok`); the fresh names hold fresh stores
(`OnPath.fresh_ok`). The merged store is well-formed, the next fresh name is
at least $`\mathit{fresh}`$, and the merged names and fresh names are below
it (`mergeState_wf`, for a non-empty list of predecessors).

**Named hypotheses of (Merge):**

1. `LinearNearSound`: every fact `Store.linearNear` lists is an `index` fact
   of its store. Its search is a `while` loop, which Lean does not unfold; a
   fuel bound, as `selectFrom` has, makes it provable.
2. `EntailedDefined`: an entailed bound's terms have integer values at
   $`\eta'`$. `Linear.Known.entails` reads an undefined term as 0, and the
   merge checks no definedness; a `termDefined` check per view, as
   `IndexWrites`' rules make, discharges it.
3. `GuardedHolds`: the guarded join's facts hold at $`\rho`$. Its tagged
   candidates are checked against every view by `indicesCheckWith`; its
   joined facts are `CertificateProducer.joinGuarded`'s, a search function
   with no soundness theorem.
4. `hI`: the edges' implications joined at the slots
   (`CertificateProducer.meetImplications`) hold at $`\rho`$, an obligation on
   the edges.

Not proved: the merged facts' names below the next fresh name (the names of
`eliminateIndices`' output); `StateWF.freshHeld` of the merged state, which
does not hold in general: a predecessor's fresh name stays beside its fresh
renames (`mergeFresh`) when no slot of the merge holds it.

## Leg 8: the graph invariant

Module `lean/Verification/Programs/TolerantFramesMergeGraph.lean`. A walk of
the pass (`Walk`) records the labels it visits, each visited node's entry
state and implications, and the states with implications that edges carry
into each node. The pass's node assertion at label $`l`$ (`passPre`) is: $`l`$
is visited and its entry state holds (`StateHolds`), the start names holding
the invocation's entry values. Proved:

- `passPre_adminClosed`: the node assertions survive the administrative
  steps (`AdminClosed`): a state's meaning reads the heap, and the world only
  through the implications' types, which admissibility keeps;
- `nodeObligations_mono`: node obligations are monotone in the node
  assertions;
- (`run_sound_of_traversed`) `StepEdgesSound` ∧ `EntriesFromEdges` ⟹ for
  every label $`l`$ and state where `passPre` holds, `SafeGraph` from
  $`(l,\rho)`$, by `graph_safe_at`;
- (`entries_of_traversed`) `Traversed` ∧ `HeadsEntered` ∧ `MergesSound` ⟹
  `EntriesFromEdges`: a head by `HeadsEntered`, one incoming state as it is,
  several by `mergeState_holds`;
- `run_sound_of_walk`, the two composed; `start_passPre`: the start's
  assertion holds at every entry meeting the inputs, the entry separation and
  the entry index facts, where the walk enters the start with its head entry
  and `entryRefusal` accepts (`entry_stateHolds`).

The conclusion is the `safe` field of the unit lane's `GraphGuarantee` at the
start (on branch `engine-proof-unit`, `PassUnit.lean`), for the main graph;
its `bounded`, `ensured`, `regionally` and `asserted` fields are not
addressed here.

**`Traversed`** (the walk's construction, as `run`'s driver builds it): every
node an edge state enters is visited; a node with no given facts and one
incoming state enters with it and its implications; with several, with
`mergeState` of them over its context, merge edges and fresh counter, each
incoming state of the context's width, with a well-formed store and names
below the counter, the start names below it.

**The premises of `run_sound_of_walk`:**

| Premise | Status |
| --- | --- |
| `Traversed` | needs a pass change: `run`'s driver is `while true`, which Lean does not unfold; a fuel-structured driver returning the walk, and a theorem that acceptance gives `Traversed` |
| `StepEdgesSound` | named hypothesis: the per-node step theorems (proved for the step kinds above, from `checkedStep`'s conditions taken as hypotheses) and the edge theorems (`edgeStoreOf`, `edgeTransfer`, the edges' checks; the other lane), including the walk's order: an edge's state is among those its target entered with |
| `HeadsEntered` | a head's state holds where an edge state into it does | step-and-edge lane: `headEstablishes_of_edge`, `headsEntered_of_recorded`; the start: pass change D8 arrived (a start an edge enters is entered as any loop head, `run` at 0f8d18ce), so `StartNotReentered` is replaced by `headEstablishes_of_edge` at the start once `run_traversed` records its entry; not yet stated |
| `MergesSound` | named hypotheses `LinearNearSound`, `EntailedDefined`, `GuardedHolds`, the edges' joined implications (Leg 8: the merge) |
| `Traversed.width`, `.wf`, `.below` at merges | not proved: the edge operations' maintenance of the target's width, `StoreWF` and `StateBelow` |

## Leg 8: the head entry

Module `lean/Verification/Programs/TolerantFramesMergeHead.lean`. A loop
head other than the start enters with `SinglePass.headEntry g false`: slot
$`i`$ named by the start name a given input `(i, q)` names, else by the
promised input's start name where the slot is among the promised input's
slots, else by the fresh name $`\mathit{fresh}+i`$; the store is the given
facts $`g`$ renamed from slots to those names; the given implications
renamed alike; the next fresh name $`\mathit{fresh}+\mathit{width}`$. Its
valuation (`headVal`) gives a start name `startNames[q]` the entry value
$`\rho_0(q)`$ and any other name $`\mathit{fresh}+i`$ the value of slot $`i`$.

### Interface between the head entry and the edge check

`EdgeEstablishes G g implies startNames argName argSlots inputSlots ρ0 ρ' s`,
at the head's environment $`\rho'`$ (the edge's mapping applied to the
source's slots, with the exit's value bound where the edge pushes it) and
the state $`s`$ the edge reaches:

1. `facts`: $`\rho', s.h \models g`$ (`HeapKnowledge.Holds`), the head's given
   facts at its slots;
2. `implies`: the head's given implications hold at $`\rho'`$
   (`PromiseCalls.ImpliesOk`);
3. `inputs`: for each given input $`(j,q)`$ with `startNames[q] = x`,
   $`\rho'(j)=\rho_0(q)`$;
4. `arg`: for each promised-input slot $`j`$, where `argName = a` and
   `startNames[q] = a`, $`\rho'(j)=\rho_0(q)`$.

These are what the edge into a head checks (`SinglePass.lean`, the edge loop
of `run`: the given implications, the inputs' values, the promised input, and
`KnowledgeExpand.checkIn` of the given facts over the edge's materialized
store), stated at the target environment; the edge lane proves that the
checks and the source's holding state give them.

Proved:

- (`headEntry_holds`) start names distinct and below $`\mathit{fresh}`$ ∧
  the promised input a start name ∧ `EdgeEstablishes` at $`\rho'`$ ⟹ the
  head's state with its implications holds at $`\rho'`$ (`StateHolds`, at
  `headVal`) ∧ its store is well-formed; `headEntry_slots`: each slot holds
  its name's value under `headVal`;
- (`headsEntered_of`) a walk entering each head with its head entry, every
  edge state into a head establishing it (`EdgeEstablishes`) ⟹
  `HeadsEntered`.

Not proved: the start as a loop head with edges into it
(`headEntry … true`, its names the start names themselves).

## Leg 8: the store operations and well-formedness

Module `lean/Verification/Programs/TolerantFramesStoreOpsBelow.lean` and the
modules above. The store operations the pass uses, by function of
`SinglePass.lean`, and the well-formedness conjuncts of `StateWF`: `store`
(`StoreWF`), the slot and fresh names below the counter (`below`, names), the
facts' names below the counter (`below`, facts), `freshHeld`.

| Operation | `StoreWF` | names, fresh below | facts below | `freshHeld` |
| --- | --- | --- | --- | --- |
| `Store.addRaw`, `remove`, `addBound`, `add` | proved (`addRaw_wf`, `remove_wf`, `addBound_wf`, `add_wf`) | no names change | proved for a fact below (`addRaw_below`, `remove_below`, `addBound_below`, `add_below`) | no names change |
| `applyDelta` | removal loop proved (`deltaRemove_wf`); additions by `add_wf`; the loops as a whole not stated | slot 0 named by the result name | not proved: the names `back` gives | not stated |
| `Store.dropHeap` | proved (`dropHeap_cover`) | no names change | removals only, not stated | no names change |
| `Store.drop` | proved (`drop_wf`) | no names change | not proved: the names of `eliminateIndices`' output | no names change |
| `edgeStoreOf` | handler: `dropHeap`; observed: `applyDelta`; as those | — | as those | — |
| `edgeTransfer` | through `Store.drop` | not proved: `mapNames`' output | not proved | the fresh names filtered by the dropped names; not proved |
| `mergeState` | proved (`mergeState_wf`) | proved (`mergeState_wf`) | not proved: through `Store.drop` | does not hold in general |
| `headEntry` | proved (`headStore_ok`, `headEntry_holds`) | not stated | not proved: the renamed facts' names | no fresh names |

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

## Leg 9: returns and footprints at a step

Module `lean/Verification/Programs/TolerantFramesStepLinkReturns.lean`.
Proved:

- `plain_return`: the plain goal's check (`c.type == R || c.type.isEmpty`)
  gives a returned value of the claim's type the goal's type;
- `pass_return_ensures`: where `returnEntails` accepts the output's facts over
  the result and the tracked slots, each tracked slot holding the name of the
  start's input it tracks, the state after the step (`checkedStep_sound`) gives
  `ensures` at the result and the invocation's entry values
  (`GraphCode.returnEntails_sound`, the context at the pushed slots
  `setsCtx_push_ok`);
- `pass_footprint_exits`: where `within` and `throws` hold at the node, a
  bound $`\Phi`$ from the invocation's entry $`h_0`$ to the node's entry heap
  and the node's local safety give $`\Phi`$ from $`h_0`$ to the heap of each
  exit, normal and exceptional (`pass_within_normal`, `pass_within_throw`,
  `pass_within_entry`).

Named hypotheses: `FreshOk F |h_0| ρ` for the receiver slots the pass records
fresh, and `DerivContext` (the context conjunct of `derivChecked`); a
closed return's result freshness (`returns`, line 1628: `outFresh`, read off
the step's derivation's selected effect, whose tree `outFresh` does not
check); the guard and assertion goals (`ControlFlow.goal_return` needs the
step's yields, which the pass takes from `nodeYields` unchecked). The
regional checks (`ArgumentRegionGraph.checkNode` over the tables `run`
builds inline, lines 1741–1791) are not connected.

## Leg 9: the searches the pass relies on

Each producer the pass runs, where its result is used, and the check that
validates it before the pass relies on it (`SinglePass.lean` lines at 16720b68).

| Producer | Result used at | Validated by |
| --- | --- | --- |
| `expressionEffectUsing` (1259) | the step's evidence `effect` (1268, 1341) | `select` with the tree check (`pass_select_sound`, `checkedStep_sound`) |
| `expressionEffectUsing` (1259) | the derivation `deriv` (1318): `outFresh` (1590–1594) | relied on unchecked: the claim's term compared, the tree not; change: `outFresh` behind `derivChecked` |
| `expressionEffectUsing` (1259) | `deriv` at the footprint (1607–1614) | `derivChecked` (`pass_within_normal`) with `DerivContext` |
| `directCall` (1248) | the step's evidence `.ordinary e` (1256–1258) | `select` with the tree check (`checkedStep_ok`) |
| `nodeYields` (1651, 1714, 1856) | the promise return (1690–1705), the edges' refined contexts (1873–1881, 1967, 1987), the result's implications (1917–1919) | relied on unchecked; change: keep the yields `PromiseCalls.yieldFollows` accepts (`yieldFollows_sound`, `PromiseCalls.lean` 728) |
| `edgeUsing` (1842, 1881, 1908) | an edge's types accepted where its value is some (1847, 1914) | relied on unchecked: the edge evidence is not checked; change: check it with the certificate checker's target check (`ControlFlow.target_sound`, `ControlFlow.lean` 892) |
| `subtypeUsing`, cached (1702, 1829, 1901, 1932) | a slot's type, a promise, an implication accepted where its value is some | `subtypeSearch_sound` (`CertificateProducer.lean` 441) where the cache holds only `subtypeSearch`'s answers (its one writer, 607); the cache's content is not stated of `Answered`; change: test `answers.proved.contains (A, B)` (`Answered.proved_sound`) |
| `meetImplications` (1154) | a merge's implications (1525) | relied on unchecked; change: check each on every incoming edge (`PromiseCalls.impliesCheck_sound`, `PromiseCalls.lean` 167) |
| `summaryUsing`, through the search (the table at 1251, 1285, 1335) | the read summaries every tree check reads | each summary checked before it is appended (`CertificateProducer.lean` 642); the table's soundness is not stated of `Answered` (`DirectKeepsSummaries`, `SearchKeepsSummaries`); change: a `summaries_sound` field of `Answered`, as `proved_sound` |
| `mapNames` (958) | the target's names on every edge | relied on unproved: `orderedSuffix` is a `while` loop (`MapNamesSound`); change: structural recursion, as `selectFrom` |

## Leg 10: the guarantee's fields from the walk

Modules `lean/Verification/Programs/TolerantFramesGuaranteeRuns.lean` and
`lean/Verification/Programs/TolerantFramesGuarantee.lean`.

**Run properties beside the graph invariant.** A property of the graph
machine's states (`StateKeeps X Q R`) is, at a node entry $`(l,\rho)`$ in heap
$`h`$, a property $`X\ l\ \rho\ h`$; inside a node, that every run of its term
with budget left meets the obligation of the exit it reaches (`EvalKeeps`:
$`X`$ at the target's environment, `ContKeeps` and `HandlerKeeps`); at the
ends, $`Q\ h\ v`$ at `.done v` and $`R\ h`$ at `.raised`. A node keeps it
(`NodesKeep P pre X Q R`) when from every state where its assertion and
$`X`$ hold, every run of its term meets its exit's obligation. Proved:

- `keeps_step`: one transition from a state the graph invariant describes
  keeps `StateKeeps`;
- `keeps_postExc`: `NodesChecked` ∧ `AdminClosed` ∧ `NodesKeep` ⟹ the term
  simulating (`GraphCode.Sim`) a state the invariant and the run property
  describe satisfies $`\mathrm{SafePostExc}\ \Xi\ T\ Q\ R`$;
- `reached_pre`: a graph run from a node entry whose assertion holds, with
  budget left, to the entry of $`l'`$ ends where $`l'`$'s assertion holds.

**The guarantee.** `GraphGuarantee` is the unit lane's record field by field
(its reachability `ReachesIn` read as `Transitions`, the same constructors).
`WalkSound` bundles the safety proof's walk predicates (`Traversed`,
`StepEdgesSoundT` with exit posts $`\top`$, `HeadsEntered`, `MergesSound`);
`nodesChecked_of_walk` gives `NodesChecked` for `passPreT` (Leg 11) from them. Each
field, proved from `WalkSound` and one per-node hypothesis, at the start
entered at `envOf L d` with mark $`|h|`$:

| Field | Theorem | Per-node hypothesis | $`X`$, $`Q`$, $`R`$ |
| --- | --- | --- | --- |
| `safe` | `run_sound_of_walk` | none | — |
| `bounded` | `bounded_of_walk` | `FootprintKept` | `BoundX`: the label in the region `dead` or $`\Phi.\mathrm{Holds}\ h_0\ h`$; `BoundQ`: $`\Phi`$ from $`h_0`$, the value fresh at $`\lvert h_0\rvert`$ where `fresh`; `BoundR`: $`\Phi`$ where `onThrow` |
| `ensured` | `ensured_of_walk` | `ReturnsEnsured` | $`\top`$; `EnsuresQ`: `EnsuresAt ensures h (push v ρ0)`; $`\top`$ |
| `regionally` | `regionally_of_walk` | `RegionsKept` (its facts $`X`$ holding at the start) | $`X`$; `RegionQ`, `RegionR`: `ArgumentStoreRegionsWithin Φ regions ρ0 h0` |
| `asserted` | `asserted_of_walk` | `AssertionsHeld` | — |

The per-node hypotheses, exactly (`pre` = `passPreT G w startNames ρ0 ctx`, each
hypothesis taking the contexts `ctx`):

- `FootprintKept P G w startNames ρ0 Φ h₀ dead fresh onThrow` =
  `NodesKeep P pre (BoundX Φ h₀ dead) (BoundQ Φ h₀ fresh) (BoundR Φ h₀ onThrow) |h₀|`:
  outside the region `dead`, `pass_footprint_exits` gives $`\Phi`$ from
  $`h_0`$ on each exit of a run (its premises `FreshOk` from the state's
  fresh names at mark $`\lvert h_0\rvert`$, `DerivContext`); at a return
  where `fresh`, the result's freshness (`returns`, `outFresh`); inside
  `dead`, `deadNode`'s no-return and exit closure, as `GraphCode.bounded_step`
  proves them for the checker;
- `ReturnsEnsured P G w startNames ρ0 ens m` =
  `NodesKeep P pre ⊤ (EnsuresQ ens ρ0) ⊤ m`: at a `ret` node,
  `pass_return_ensures` from the state `checkedStep_sound` gives after the
  step; at every other continuation the obligation is $`\top`$;
- `RegionsKept P G w startNames ρ0 X Φ regions h₀ exc` =
  `NodesKeep P pre X (RegionQ …) (RegionR …) |h₀|`, $`X`$ the regional facts
  the pass's tables (`regionIn`, `ArgumentRegionGraph.checkNode`) state, and
  $`X`$ at the start from `checkEntryFields`;
- `AssertionsHeld G w startNames ρ0 assertions m`: each stated
  $`(l,K)`$ holds at $`\rho, s.h`$ wherever `passPre l ρ m s` holds: at a node
  other than a head the pass adds $`K`$'s facts to the entry state after the
  edges check it, at a head $`K`$ is part of the given facts.

**`run_guarantee`**, proved: $`\forall\eta.\ \mathrm{admits}\ \eta\Rightarrow\exists\ w\ \mathit{given}\ \mathit{ctx}\ \mathit{edgesIn}\ \mathit{fresh}.\ \mathrm{PassWalkSound}\ (\mathrm{reassign}\ G\ \eta)\ \dots`$
⟹ `GraphGuarantee G admits P start goal inputs sep idx assertions bound ensures regional`.
`PassWalkSound` holds `WalkSound` at every entry value $`\rho_0`$ and mark,
the start entered at every entry meeting the inputs, the separation and the
index facts (`entered`, which `start_passPreT` gives from `entryRefusal`'s
acceptance, the walk's start entry and the start's context the inputs), and the four per-node hypotheses
for the options the call states. The unit lane's `RunSound` is then
`run_guarantee` composed with `run_traversed` (an accepted call yields a walk
with `PassWalkSound` at every admitted assignment), which needs the driver on
fuel.

**The head's interface.** The edge lane's `EdgeEstablishes` (the given
facts and the head's types at $`\mathrm{mapEnv}\ \theta\ \rho`$,
`head_query_sound`) and the merge line's `HeadEstablishes` (facts, given
implications, given inputs, promised input) are connected by the step lane's
`headEstablishes_of_edge` (Leg 11), which proves `HeadEstablishes` from the
pass's checks on the edge. The merge line's `drop_ok` and `keepFirst_mem` are
named `drop_holds` and `keepFirst_sub`, the edge lane keeping its copies
under the original names.

## Leg 10: the edge operations and well-formedness

Module `lean/Verification/Programs/TolerantFramesStoreOpsEdge.lean`. Proved:

- `deltaAdd_wf`, `deltaRestate_wf`, `applyDelta_wf`: `applyDelta`'s loops
  only add and remove facts, so the delta keeps a store well-formed;
- `edgeStoreOf_wf`: an edge's store is well-formed where the entry store and
  the output store are (a handler's by `dropHeap_cover`, an observation's
  and a promotion's by `applyDelta_wf`);
- `edgeTransfer_wf`: the target's store, the edge's store without the
  dropped names, is well-formed (`drop_wf`);
- `edgeTransfer_width`: under `MapNamesLength` (`mapNames names (some
  slots)` has one name per slot where every slot reads a source slot, a
  premise: `orderedSuffix` is a `while` loop), the target has as many names
  as the mapping has slots, and the identity mapping as many as the source
  (`mapNames_none`).

`StateWF` has the conjuncts `store` and `below`. A merge keeps a
predecessor's fresh name beside its renames where no merged slot holds it
(`mergeFresh`); what holds of every state's fresh names is that they are
below the counter, the third part of `below` (`mergeState_wf` for a merge),
and no proof reads more.

The facts' names below the counter through `Store.drop`, the delta, an
edge's store and transfer and `headEntry`: Leg 12.

## Leg 10: the start as a loop head

`SinglePass.run` makes the start a head (`isHead`, line 1403) and enters it
with `headEntry g true`: slot $`i`$ named by the start name
$`\mathit{startNames}[i]`$, whatever the given inputs. The state's meaning
pins a start name to the entry value ($`\eta(\mathit{startNames}[q])=\rho_0(q)`$),
so the start's state holds at $`\rho'`$ only where $`\rho'(i)=\rho_0(i)`$ at
every slot. An edge into the start checks the given facts, the given
implications, the given inputs and the promised input (lines 1937–1953),
and no equality of a slot not among the given inputs with its entry value.
So `HeadsEntered` at the start does not follow from the edge check where an
edge enters the start and changes a slot's value: the start's facts over
start names, and the input tracking a return's `ensures` reads
(`startNames[q]` in `entry.names`, line 1672), would then be read of the
entry values while the slots hold others. Observed in the code; no source
reaching it is demonstrated. The pass change that closes it: where an edge
enters the start, enter it as any head (`headEntry g false`, fresh names
for the slots outside the given inputs), or check every start-named slot
on each edge into the start as the given inputs are checked. Until then
`HeadsEntered` at the start is the named premise `StartNotReentered`: no
edge enters the start, or each edge into it keeps every slot's entry value.

## Leg 10: what the driver must record

`run_traversed` (an accepted call yields a walk with `PassWalkSound`) needs
`run`'s driver on fuel; `run` is a `while true` loop, as `loopHeads` is. Its
record `Walk` must contain, per label: whether it was visited, its entry
state and implications (after the head entry, the single state or the
merge, and the written assertion's facts added at a node other than a head),
the states with implications every processed edge carried into it, the
merge's context, edges and fresh counter, and, per edge, the edge's mapping,
whether it pushed, and the source's state after the step. `Traversed.merge`
asks the merge's incoming list to be complete: every edge into a non-head
node from a reached node is processed before the node. That rests on the
in-degree order, which is sound where every cycle of reached nodes passes
through a head (`HeadsCutCycles`: removing the edges into heads leaves the
reached graph acyclic), which `loopHeads` gives where it marks every
retreating edge's target of a complete depth-first walk; `loopHeads` is a
`while` loop, so this needs it on fuel too.

## Open premises of the graph-level proof

The current list. `run_guarantee` proves the unit lane's `GraphGuarantee`
from `PassWalkSound` at every admitted assignment (at the typed assertions,
Leg 12); each premise below is a part of it or of `run_traversed`.

| Premise | Statement | Status |
| --- | --- | --- |
| `run_traversed` | an accepted `run` yields a walk, contexts, merge edges and counters with `Traversed`, `NodeAccepted` at every visited node, and each edge into a head recorded as the head's entry (`headsEntered_of_recorded`) | needs pass change: the driver on fuel returning `Walk` (not arrived) |
| the reassignment | the walk predicates at `reassign G η` for every admitted `η` | the node runs carried: `nodeRan_reassign` under `CheckedStepReassign`, and `run_guarantee_of_run` from one run at `G` (Leg 13); `CheckedStepReassign` lacks the invariance of `directCall`, the search `expressionEffectUsing` and the checker's `select`, and for a qualified body a `BodySubtyping (reassign G η)` at the scope's admitted `η`; the meaning of each node at `reassign G η` is `run_traversed`'s at that graph (`hwalk`) |
| `HeadsCutCycles` | every cycle of reached nodes contains a head | needs pass change: `loopHeads` on fuel (not arrived) |
| `StepEdgesSoundT` | per node, from `passPreT`, the local judgment and every exit a holding edge state into its target | step-and-edge lane: `stepEdgesSound_of` from `NodeAccepted`, `CodesSound`, `DirectKeepsSummaries`, `SearchKeepsSummaries` |
| `HeadsEntered` | a head's state holds where an edge state into it does | step-and-edge lane: `headEstablishes_of_edge`, `headsEntered_of_recorded`; the start: pass change D8 arrived (a start an edge enters is entered as any loop head, `run` at 0f8d18ce), so `StartNotReentered` is replaced by `headEstablishes_of_edge` at the start once `run_traversed` records its entry; not yet stated |
| `MergesSound`: `LinearNearSound` | every fact `linearNear` returns is stored | needs pass change: `linearNear` on fuel (not arrived) |
| `MergesSound`: `EntailedDefined` | the terms of an entailed bound are defined on each path | needs pass change: the `termDefined` check at merges (not arrived) |
| `MergesSound`: `GuardedHolds` | the guarded join's facts hold on each path | needs pass change: the recheck of guarded joins (not arrived) |
| `MergesSound`: the joined implications | `ImpliesOk` of `meetImplications` at the merge's environment | needs pass change D3: on each incoming edge, each met implication established by `impliesCheck` from the implications the edge carries (`impliesCheck_sound`); this is the check's specification (not arrived) |
| `Traversed.width` | the incoming states have the context's width | `edgeTransfer_width` under `MapNamesLength`; `MapNamesLength` needs pass change D7 (`mapNames` on fuel, not arrived) |
| `Traversed.wf` | the incoming stores are well-formed | proved from the step's output store well-formed (`edgeStoreOf_wf`, `edgeTransfer_wf`) |
| `Traversed.below` | the incoming states below the merge's counter | proved from the step's output below the counter and a positive counter (`edgeStoreOf_below`, `edgeTransfer_below`, Leg 12); the step's output facts: `applyDelta_below` with `passBack_below` |
| a merge's facts below its counter | the met store's facts below the merge's next name | other: not proved (Leg 12's table) |
| `entered` | the start's typed state holds at every entry meeting the inputs | `start_passPreT`, given `entryRefusal`'s acceptance, the walk's start entry and the start's context the inputs (`StartContext`) |
| `FootprintKept` | the footprint check keeps the bound at each node | step-and-edge lane: `footprintCheck_sound`, `footprint_exits`; composition into `NodesKeep` not stated |
| `ReturnsEnsured` | the return check establishes `ensures` | step-and-edge lane: `pass_return_ensures`; at the start, `StartNotReentered` |
| `RegionsKept` | the regional check keeps its facts per node | step-and-edge lane: `ArgumentRegionGraph.checkNode`'s soundness from a node's own typing and the tables' agreement, not proved |
| `AssertionsHeld` | each stated assertion holds where `passPreT` at its label does | other: the node assertion carries the walk's entry, to which the pass adds the written assertion's facts at a node other than a head; `run_traversed` records the entry after that addition, and at a head the written assertion is part of the given facts |
| `ShapeOk` at a branch | the claim's type at a branch is Boolean | needs pass change: no check of the pass states it |
| `RunKeepsSummaries` | the answers' summaries a call starts from are among those it leaves | needs pass change: the driver on fuel; per step `DirectKeepsSummaries`, `SearchKeepsSummaries`, which pass change D6 (a `summaries_sound` field) makes structural |
| unchecked searches | edge evidence, yields, `outFresh`, the subtype cache | edge evidence: pass change D1 arrived (`checkMappedUsing` or `checkObservedUsing` of the search's evidence, `run` at 9e925a2e), which discharges `htc` through `checkMapped_sound`, `checkObserved_sound` once `run_traversed` records the check; not yet stated; yields, `outFresh`, the subtype cache: pass changes D2, D4, D5 (not arrived) |

## Leg 11: one obligation per node

Modules `lean/Verification/Programs/TolerantFramesNodeSound.lean`,
`TolerantFramesNodeEdges.lean` and `TolerantFramesNodeWalk.lean`.

**The typed node assertion.** A node's step needs its context's types at
its environment (the `EnvOk` premise of `checkedStep_parts`), which no state
carries: the pass checks them on every edge into the node. `StepEdgesSound`
(Leg 8: the graph invariant) reads a node's assertion as `passPre` alone, and
no node's step is provable from it. The typed assertions are
$`\mathrm{passPreT}\ l = \mathrm{passPre}\ l\wedge\mathrm{EnvOk}\ (\mathit{ctx}\ l)`$
and $`\mathrm{edgePreT}\ t = \mathrm{edgePre}\ t\wedge\mathrm{EnvOk}\ (\mathit{ctx}\ t)`$,
and `StepEdgesSoundT` is `StepEdgesSound` at them. Proved:

- `run_sound_of_walk_typed`: `Traversed` ∧ `StepEdgesSoundT` ∧
  `HeadsEntered` ∧ `MergesSound` ∧ `passPreT` at the start ⟹ `SafeGraph`
  from the start; its entry premise is the untyped `EntriesFromEdges`, since
  an edge's types are the target's (`passPreT_adminClosed`: types survive an
  admissible transition, `envOk_admissible`);
- `headsEntered_of_recorded`: a walk recording, as each edge's state into a
  head, the head's entry state and implications enters its heads.

**The node's obligations from the step** (proved:
`nodeObligations_of_parts`). `checkedStep_parts` states the step theorem's
exits in parts (`StepParts`): the local judgment, the state after the step
after every run to a value whose endpoint is an action of the normal effect
with the rule's output, and the throw state after every action of the
exceptional effect. With the normal post extended by the run that reaches the
value (`safePostExc_trace`), these give `NodeObligations` at the node, the
exception family `excOf G`, the claim's type, where the claim's type gives
each value its continuation's shape, each normal exit's target obligation
follows from the state after the step at the pushed environment, and each
throw's from the throw state.

**A node's exits** (proved):

- `normalTarget_of_exits`: every normal exit of `Exit.ofNode` delivering
  (`ExitDelivers`: the state after the step, the pushed environment's types
  and the exit's observation give the target's assertion) gives the normal
  target of a `bind`, `effect` and `branch` (the yes edge at `true`, its
  promoted truthiness `true`), and of a return where the claim's type gives
  the result type (`plain_return` for a plain goal);
- `exitDelivers_of_edge`, `handlerDelivers_of_edge`: an edge into a node
  other than a loop head delivers the state `edgeTransfer` builds from
  `edgeStoreOf` with the implications `implies ++ freshImplOf …`
  (`normal_edge_delivers`, `handler_edge_delivers`,
  `stateHolds_freshImpl`), where the walk records it among the target's
  incoming states;
- `exitDelivers_head`: an edge into a loop head establishes each field of
  `HeadEstablishes` (`headEstablishes_of_edge`): `facts` by the head query
  (`head_query_sound` over the edge's materialized store,
  `edgeStore_normal`), `implies` by an implication the edge carries at the
  mapped slots' names with a type within the given one, `inputs` and `arg`
  by the slot-name checks with the start names' entry values; the head's
  entry then holds (`headEntry_holds`). The checks bind where the edge is
  not vacuous; a vacuous edge has no environment meeting its context.

`EdgeEstablishes` of Leg 9 is the `facts` field of `HeadEstablishes` with the
target's types: `HeadEstablishes` is the interface.

**Every node of the pass delivers** (proved: `stepEdgesSound_of`). Premises:
`NodeAccepted` at every visited label, `CodesSound`, `DirectKeepsSummaries`,
`SearchKeepsSummaries`. Conclusion: `StepEdgesSoundT` with the exception
family `excOf G`, the result type `Tres` and no heap post. `NodeAccepted l`
holds the values `SinglePass.run` computes at $`l`$ and the checks it passes
there, by the pass's functions (the driver is a `while` loop no proof
unfolds): the node and its claim, the label's context the claim's; the
step's entry state (the walk's entry, the node's stated assertion joined),
holding where the node's assertion holds (`stated`); `checkedStep`
accepting, with the store well-formed, the names below the counter
(`NamesBelow`), the width, the incoming summary table checked; the claim's
type giving each continuation's shape and a return's result type; each normal
exit delivering and the handler delivering (`exits`, `handler`, discharged
by the exit lemmas above from the edge's checks).

Named hypotheses and what discharges them:

| Hypothesis | Discharged by |
| --- | --- |
| `NodeAccepted` as a whole | the pass's driver on fuel returning a `Walk` (queued in the pass lane), with the extractions `edgeCheck`, `returnCheck` |
| `stated` | proved where the node states no assertion (the entry is the walk's); otherwise the stated assertion carried in the node assertion |
| `sums`, `DirectKeepsSummaries`, `SearchKeepsSummaries` | the summary table's soundness as an invariant field of `Answered` (queued) |
| `below` (`NamesBelow`), `width` | the maintenance of the state's names by the step, the edge and `mapNames` |
| `shape` at a branch | the claim's type Boolean at a branch: no check of the pass states it; `branchBind` and `tagBind` are outside `NodeObligations` (`ShapeOk`) |
| `ret` beyond a plain goal | the guard and assertion goals, under `YieldsOk` |
| `MapNamesSound` | `mapNames` on fuel (queued) |
| `YieldsOk` (`hY`) | yields kept only where `yieldFollows` accepts (queued) |
| the result's freshness (`hfo`) | `outFresh` behind `derivChecked` (queued) |
| the target's types (`htc`), a given implication's type within (`himp`) | edge evidence checked; the subtype cache's soundness (queued) |
| the walk's records (`hrec`, `hrecHead`, `hentry`) | the driver returning a `Walk` (queued) |

## Leg 11: the footprint and return checks at a node

Module `lean/Verification/Programs/TolerantFramesStepLinkReturns.lean`, over
the pass's functions `SinglePass.footprintCheck` and `SinglePass.returnCheck`.
Proved:

- `footprintCheck_sound`, by unfolding: at the node's sequent, `within`
  (`passWithin`), `throws` (`passThrows`) where a live handler catches the
  throw or the bound covers throws, a return's freshness where the bound
  requires a fresh result, and the term's scope. The derivation check
  (`passDerivChecked`) states the claim at the node's term and context, as
  `footprintCheck`'s `derivChecked` does;
- `footprint_exits`: where `footprintCheck` accepts the node, the fresh
  receiver slots hold stores allocated at or past the invocation's entry
  $`h_0`$ (`FreshOk`), and the node's local safety and $`\Phi`$ from $`h_0`$ to
  its entry heap hold, each run with budget left keeps $`\Phi`$ from $`h_0`$ to
  the heap of its normal exit, and of its throw where a live handler catches
  it or the bound covers throws: the per-node form the `bounded` field
  composes along a run;
- `returnCheck_plain`: where `returnCheck` refuses nothing at a plain goal,
  a returned value of the claim's type is of the goal's (`GoalHolds`), which
  is `NodeAccepted.ret` at a plain goal.

Named hypotheses: `FreshOk` of the receiver slots the pass records fresh;
the guard and assertion goals of `returnCheck` (the yields' soundness,
`YieldsOk`, and the subtype cache's).

The regional check (`ArgumentRegionGraph.checkNode` over the tables `run`
builds per node) has a soundness theorem only for a whole certified graph
(`ArgumentRegionGraph.checkNodes_sound`, whose premise is the certificate
checker's acceptance, `checkGraphUsing`); the pass supplies a node's typing
by its step, and its tables per node (`sparse` over the node and its
targets), so the per-node regional statement needs `checkNode`'s soundness
from the node's own typing and the agreement of each node's tables with its
targets' (`regionIn`'s meet).

## Leg 11: the names after a step, and the hypotheses of pure functions

Module `lean/Verification/Programs/TolerantFramesNodeWalk.lean`. Proved:

- `namesBelow_step`: where the entry's names, start names and implications
  are below the counter and the result is an entry name with the counter
  kept or the counter with the counter advanced (`checkedStep_parts`), the
  state after the step is below the next counter, given its store's facts
  are;
- `width_step`: the pushed names no wider than the pushed context.

Not proved, with the function each needs:

- the store's facts after a step below the next counter: the names
  `applyDelta` reads back (`passBack`), and after an edge, the names of
  `Store.drop`'s derived facts (`HeapKnowledge.eliminateIndices`' output);
- `MapNamesSound` for a mapping other than the identity: `mapNames` reads the
  ordered suffix by `orderedSuffix`, a `while` loop;
- `DirectKeepsSummaries`, `SearchKeepsSummaries`: the table's one writer is
  `summaryUsing` (`CertificateProducer.lean` 646), which appends a summary
  `checkReadSummaryResult` accepts; a proof through `directCall` and
  `expressionEffectUsing` is an invariant of every `SearchM` function they
  run, which a `summaries_sound` field of `Answered` (as `proved_sound`)
  makes structural;
- the result's freshness where `outFresh`: read off the step's derivation's
  selected effect, whose tree `outFresh` does not check (`run`, the
  definition of `outFresh`).

## Leg 11: `typedRead`'s optional-field branch

Module `lean/Verification/Programs/TolerantFramesSelect.lean`. Proved
(`typedRead_optional_sound`): where the pass's tree check accepts the read's
derivation with the codes, at a read of a field the slot's type states
optional, the output `readFrame k i fld true` holds after the read. The
checker's `run` checks this tree with no codes; the pass's selection reaches
the branch by `passSteps_value`'s third case, and `passSteps_sound` consumes
it through `typedRead_optional_sound` alone.

## Leg 12: the facts' names below the counter

Modules `lean/Verification/Programs/TolerantFramesStoreOpsNames.lean` (the
eliminations and renamings) and `TolerantFramesStoreOpsBelowNames.lean` (the
store operations).

**The eliminations name their inputs' names** (proved). A name an index atom
states is a slot of its fact or its condition (`NamedIn`).

- `termDefined_named`: a term `termDefined as` accepts is rooted at a name
  an atom of `as` states;
- `eliminateLinear_named`, `eliminateIndices_named`: every name of the
  output of `eliminateLinear D as` and `eliminateIndices D as` is a name of
  `as`: a derived linear fact keeps only terms `termDefined as` accepts, under
  the condition of an atom of `as`; `releasePast` restates a disjunct;
- `restateReads_named`, `restateStores_named`: every name of their output is
  a name of their input atoms or the cell of one of their links
  (`liftDropped` and `liftPath` root a term at a read's cell);
- `atom_rename_names`: a fact renamed by $`f`$ names only $`f`$'s images of its
  names.

**The store operations against the well-formedness conjuncts.** `StoreWF`,
the slot and fresh names below the counter, the facts' names below the
counter (`FactsBelow`); every cell proved, or stated with what it lacks.

| Operation | `StoreWF` | names, fresh below | facts below |
| --- | --- | --- | --- |
| `Store.addRaw`, `remove`, `addBound`, `add` | `addRaw_wf`, `remove_wf`, `addBound_wf`, `add_wf` | unchanged | `addRaw_below`, `remove_below`, `addBound_below`, `add_below`, for a fact below |
| `applyDelta` | `applyDelta_wf` | slot 0 the result name | `applyDelta_below`, where `back` renames below the counter (`BackBelow`) |
| `Store.dropHeap` | `dropHeap_cover` | unchanged | `dropHeap_below` |
| `Store.drop` | `drop_wf` | unchanged | `drop_below` |
| `edgeStoreOf` | `edgeStoreOf_wf` | — | `edgeStoreOf_below`: the delta's `back` reads `materialize`'s table, whose keys are the state's slot names (`slotTable_keys`, `materialize_table_keys`, `inverse_keys`, `back_below`) |
| `edgeTransfer` | `edgeTransfer_wf` | `edgeTransfer_below`: a target name is a source name or $`0`$ (`mapNames_mem`), so below a positive counter; the fresh names are the entry's and the result | `edgeTransfer_below` (`drop_below`) |
| `mergeState` | `mergeState_wf` | `mergeState_wf` | not proved: the met store's and the joins' facts are predecessor facts renamed by the merge's renaming (`rename_key_below` gives the renamed names below the merge's counter) and `Store.drop`'s output; the composition through `mergeState`'s loops is not stated |
| `headEntry` | `headStore_ok` | `headEntry_below` | `headEntry_below`: the store's facts are renamed to the slots' names; premise: each slot's own name `i + base` below the counter, automatic at a head other than the start ($`\mathit{base}=\mathit{fresh}`$, counter $`\mathit{fresh}+w`$), at the start $`i+\mathit{startNames}[0]<\mathit{fresh}`$ |
| the step (`checkedStep`'s output store) | the step-and-edge lane (`NamesBelow`) | the step-and-edge lane | the step-and-edge lane |

`Traversed.below` (each state into a merge below the merge's counter) is
then `edgeTransfer_below` over `edgeStoreOf_below` at the source's step
output, given the step's output below the counter (`NamesBelow` after the
step) and a positive counter.

## Leg 12: the guarantee at the typed assertions

Module `lean/Verification/Programs/TolerantFramesGuarantee.lean`. The walk
predicates of `run_guarantee` are the typed ones (Leg 11): `WalkSound.steps`
is `StepEdgesSoundT`, `nodesChecked_of_walk` gives `NodesChecked` for
`passPreT`, and the four per-node hypotheses (`FootprintKept`,
`ReturnsEnsured`, `RegionsKept`, `AssertionsHeld`) are stated from `passPreT`
at the contexts `ctx`. `run_guarantee`'s `safe` field is
`run_sound_of_walk_typed`. `PassWalkSound.entered` gives `passPreT` at the
start, which `start_passPreT` proves from `start_passPre` where the start's
context is the inputs (the unit lane's `StartContext`).

## Leg 12: the reassignment link

Module `lean/Verification/Programs/TolerantFramesWalkReassign.lean`.

**How the proved checker covers every assignment.** Its rules' soundness
theorems are stated for every graph, at the graph's own assignment
(`ControlFlow.accepted_inputs_safe` at any `G`); its acceptance at `G` is its
acceptance at `reassign G η` (`Parametricity.accept_reassign`: each checker
equal at the reassigned graph, by `rfl` where it unfolds and by a lemma for
the recursive ones: `checkTree_reassign`, `checkStep_reassign`,
`checkTarget_reassign`, `yieldFollows_reassign`, `checkReturn_reassign` and
the rest of `Parametricity.lean`); so one check gives safety at every `η`
(`Parametricity.accepted_at`). A qualified body is not covered that way: its
subtyping (`BodySubtyping`) is sound at the graph's own assignment only, and
`RequestJson.verify_qualified_safe_at` gives safety at an admitted instance
`assign η source.binders As` from the lexical body check and the descriptor
capabilities.

**The same route for the pass.** The step-and-edge lane's theorems
(`checkedStep_sound`, `stepEdgesSound_of`, `headEstablishes_of_edge`) and this
lane's (`mergeState_holds`, the store operations) are stated for every graph.
So the walk predicates at `reassign G η` follow from an accepted run at
`reassign G η` with the reassigned arguments, and `run_guarantee`'s premise
from the equation

```math
\mathrm{run}\ (\mathrm{reassign}\ G\ \eta)\ (I.\mathrm{reassign}\ \eta)\ \dots\ (a.\mathrm{reassign}\ \eta)\ =_{\mathrm{outcome}}\ \mathrm{run}\ G\ I\ \dots\ a
```

(`run_reassign`, not proved). Proved: the arguments at the reassigned graph
exist and keep their soundness: `codesSound_reassign` (a code table sound at
`G` is sound at every reassignment), `Answered.reassign` (the cached answers,
their proved inclusions holding at every assignment),
`Parametricity.summariesSound_reassign`. Observed: `mergeState`,
`entryRefusal` and `edgeStoreOf` are equal at the reassigned graph by `rfl`;
`footprintCheck` and `returnCheck` are not (they call the tree check, which
`checkTree_reassign` covers by a lemma). What `run_reassign` needs:

- the driver on fuel (a `while` loop is a `partial` definition: no equation
  unfolds it);
- an invariance lemma for each pass function that is not `rfl`:
  `footprintCheck`, `returnCheck`, `checkedStep` and the searches it runs
  (their results are data the run carries, so each search must return the
  same at the reassigned graph), the edge checks, the head query;
- for a qualified checker, `PassChecker.qualified`'s subtyping at
  `reassign G η`: a `BodySubtyping (reassign G η)` exists only where the
  body's check is sound at `η`, which the lexical body check gives at
  `q.Admits η` (`verify_qualified_safe_at`'s route). This is the one rule
  whose soundness is not uniform in `η`.

Until then the link is `run_guarantee`'s premise as stated: `PassWalkSound` at
`reassign G η` for every admitted `η`.

## Leg 12: the loop heads and the order

What `run_traversed` needs of the traversal, stated for the driver's
`Walk`:

- `HeadsCutCycles`: every cycle of reached nodes passes through a node
  `isHead` marks. `loopHeads` marks every target of a retreating edge of the
  depth-first walk it runs, and every cycle of a graph contains a retreating
  edge of any complete depth-first walk (a standard fact of depth-first
  search, not proved here); the theorem needs `loopHeads` as a
  function a proof unfolds (on fuel) and its walk complete over the reached
  nodes;
- the in-degree order: a node other than a head is processed after every
  edge into it from a reached node is processed. The driver must record,
  per label, the list of incoming states in processing order and the
  processed flag of each edge, so that `Traversed.merge` (the merge's list
  complete) follows from the in-degree counter reaching zero, which counts
  the edges into the node from reached nodes outside the edges into heads.

## Leg 13: the pass's checks at a reassignment

Modules `lean/Verification/Programs/TolerantFramesWalkReassignChecks.lean`
and `TolerantFramesWalkReassignNodes.lean`.

**Invariant functions** (proved). Each is the same function at
`reassign G η` with the image check `images.reassign η`, the answers
carried by `Answered.reassign` where it threads them:

- `footprintCheck_reassign`: `footprintCheck` is equal;
- `subtypeSearch_reassign`: the subtype search, through its instance
  proposals (`instantiationUsing_reassign`, `rowInstances_reassign`, over
  `unifiedInstance_reassign`, `matchedInstance_reassign`, `matchRow_reassign`,
  `matchSig_reassign`, `matchRest_reassign`, `searchReads_reassign`,
  `searchFree_reassign`) and `Parametricity.compareUsing_reassign`;
- `subtypeUsing_reassign`: an answered subtype request returns the same
  result, its answers reassigned;
- `returnCheck_reassign`: the return check's refusal and queried count are
  equal, its answers reassigned (the promise's fold by `foldl_map_state`);
- `edgeStoreOf_reassign`, `entryRefusal_reassign`: equal by unfolding.

**A node's run and its meaning.** `NodeAccepted` splits into `NodeRan`,
the pass's values and checks at a node (the step's equation, the store
well-formed, the names below the counter, the width, the summary table
checked), and `NodeMeaning`, the fields that read the graph's meaning (the
stated assertion, the shapes, the return type, the exits, the handler);
`NodeAccepted.ran`, `NodeAccepted.meaning` and `NodeAccepted.ofRan` convert.
A meaning field holds at a graph by the theorems that give it at every graph
from the checks there (`exitDelivers_of_edge`, `exitDelivers_head`,
`handlerDelivers_of_edge`, `returnCheck_plain`); it is not carried from
`G`, whose meaning is read at another assignment.

- `nodeRan_reassign`: `CheckedStepReassign` ⟹ every `NodeRan` at `G` is a
  `NodeRan` at `reassign G η`, the answers reassigned, the table checked by
  `Parametricity.summariesSound_reassign`;
- `nodeAccepted_reassign`: with the reassigned run's `NodeMeaning`, an
  accepted node at `G` is accepted at `reassign G η`;
- `run_guarantee_of_run`: `NodeRan` at every visited node of one run at
  `G` ∧ for every admitted `η` a checker `pc'` with `CheckedStepReassign` ∧
  `hwalk` (the nodes' runs at `reassign G η` give `PassWalkSound` there) ⟹
  `GraphGuarantee`.

**Named hypothesis `CheckedStepReassign`**: `checkedStep` at
`reassign G η` with the checker `pc'` returns what it returns at `G`, its
answers reassigned. The functions `checkedStep` calls whose invariance is
not proved: `directCall` (its `for` loops thread the answers through
`subtypeUsing`, whose invariance is proved), the search
`expressionEffectUsing`, the checker's `select` at the reassigned graph; for
a qualified body, `pc'` needs a `BodySubtyping (reassign G η)`, which exists
where the body's check is sound at `η` (the scope `q.Admits η`, as
`verify_qualified_safe_at`). The head query of an edge into a loop head is
not equal by unfolding (`withTypedCells`, `withTypedLinks`, `ctxOf`); its
invariance lemma is not stated.

**`hwalk`** is `run_traversed`'s statement at `reassign G η`: its proof is
uniform in the graph, and the edge and merge functions it reads are equal
at the reassigned graph (`mergeState` by unfolding, `edgeStoreOf_reassign`).


## Leg 14b: the footprint check kept along a run

Module `lean/Verification/Programs/TolerantFramesNodeBound.lean`. Under
`bound = some (Φ, ret, exc)` and the region `dead`, `run` checks at each
node (`BoundChecked`): at a node of `dead`, `GraphCode.deadNode` with
`exc = false`; outside it, `footprintCheck` at the step's values, which
`passRecvFresh`, `passDerivOf`, `passLiveHandler` and `passOutFresh`
restate from `run`'s bindings (`F`, `deriv`, `liveHandler`, `outFresh`);
`run` reads the region as an array, `deadAt_toList` gives the list. Proved:

- `freshOk_recv`: the receiver slots `passRecvFresh` lists hold stores
  allocated at or past the mark (`GraphCode.FreshOk`), from the entry
  state's fresh names: the `FreshOk` premise of `footprint_exits`;
- `copyFresh`: a copy of a slot holding a fresh name returns a fresh store;
- (`footprintKept_of`) `NodeAccepted` at mark $`|h_0|`$ ∧ `BoundChecked`
  ∧ `CallFreshOk` at every visited node ∧ `CodesSound` ∧
  `DirectKeepsSummaries` ∧ `SearchKeepsSummaries` ⟹ `FootprintKept`.
  Outside `dead`, from $`\Phi`$ between $`h_0`$ and the entry heap,
  `footprint_exits` gives $`\Phi`$ on each normal exit and on a throw where
  the handler is live or the bound covers throws; a return where `ret`
  is fresh by `passOutFresh` (`copyFresh`, or `CallFreshOk`). Inside
  `dead`, an empty result type admits no normal exit (the value's type from
  the step's exits), a continuation into `dead` reaches a node of `dead`,
  and a throw reaches a handler of `dead` or escapes with no throw bound.

Named hypothesis `CallFreshOk`: where `outFresh` reads a fresh result off
the derivation's selected effect (`passCallFresh`), the returned value's
store is allocated at or past the mark; the pass does not check that
derivation's tree there (pass change D4).

## Leg 14b: the return check kept along a run

Module `lean/Verification/Programs/TolerantFramesNodeReturns.lean`.
`ReturnChecked` is `returnCheck` refusing nothing at a node whose
continuation is a return, at the step's output store and result. Proved:

- `returnCheck_ensures`, by unfolding: where `returnCheck` refuses nothing,
  `ensures` is empty, the claim's type or a context slot's is empty, or
  `returnEntails` accepts the output's facts over the result and the
  tracked inputs (`passTracked`, `returnCheck`'s `tracked`);
- `passTracked_names`: each tracked slot holds the start name of the input
  it tracks, the premise `htr` of `pass_return_ensures`;
- (`returnsEnsured_of`) `NodeAccepted` ∧ `ReturnChecked` at every visited
  node ∧ `CodesSound` ∧ `DirectKeepsSummaries` ∧ `SearchKeepsSummaries` ⟹
  `ReturnsEnsured`: the state after the step at the pushed environment
  (the step's normal exit) gives `ensures` by `pass_return_ensures`; an
  empty result type admits no value, an empty context type no
  environment.

The guard and assertion goals are not composed here: `NodeAccepted.ret`
states the goal of every value of the claim's type, while a guard's goal
reads the promised argument (`GoalHolds (.guards T _) a`), which only the
state after the step determines (the argument's slots, named by
`argName`, refined by the step's yields). Their proof needs `ret` read at
that state, as `ControlFlow.goal_return` reads `ReturnOk`, `YieldsOk` and
`ArgumentsOk`, with the subtype answers' soundness (pass change D5) for
`returnCheck`'s `subtypeUsing`.

## Leg 14b: a written assertion on its edges and in the entry state

Module `lean/Verification/Programs/TolerantFramesNodeAsserted.lean`.
Proved (`assertion_query_sound`): the check `run` makes on every edge into
a node other than a head that states an assertion `req` (`checkIn` of `req`
over the edge's materialized facts with the typed cells and links of the
edge's context $`\Gamma_e`$, under the edge's observation where it has one,
`assertionSource`) gives `req` at the target's environment
$`\mathrm{mapEnv}\ \theta\ \rho`$, where the edge's facts hold at
$`\rho`$, $`\Gamma_e`$ types $`\rho`$ (on a refined edge context, the
step's yields: `YieldsOk`), the observation holds of the result and the
target's context types the mapped environment.

`AssertionsHeld` reads the assertion from the node's entry state
(`passPreT`), into which `run` adds each written fact renamed to the
slots' names (`Store.add`). That state does not entail every written
fact: a fact one of whose slots has no name is not added (its renaming is
`none`); `Store.addBound` does not add a linear bound when the store has a
bound of the same normal form at least as strong, though the normal form
may drop a term (`x - x`) whose value the skipped fact requires defined;
and a separation fact's atoms carry no level bound. Observed in the code;
no source reaching these is demonstrated. So `AssertionsHeld` is a named
hypothesis of this leg. The edge check above is the obligation that gives
the assertion at every entry: a node assertion that states, beside
`passPreT`, the stated assertions at the label, with every edge into the
label establishing them (`assertion_query_sound` at a node other than a
head, `head_query_sound` at a head, whose given facts include the written
assertion), carries them to every reached entry as `reached_pre` carries
`passPreT`.

## Leg 14b: the edge evidence checked, and a start an edge enters

Module `lean/Verification/Programs/TolerantFramesComposeEdges.lean`.

**D1, the edge evidence.** Proved: (`edgeEvidenceChecked_env`) where
`edgeEvidenceChecked` accepts the search's evidence at the edge's context
$`\Gamma`$ and the target's $`\Delta`$, over the fields, optional fields
and cells read off the edge's facts $`k`$, with $`k`$ holding at
$`\rho`$, $`\Gamma`$ typing $`\rho`$ and the observation holding of slot
0, $`\Delta`$ types $`\mathrm{mapEnv}\ \theta\ \rho`$: an unsatisfiable
context meets no environment, `checkMapped_sound` gives `MappedCovers`
and `checkObserved_sound` `ObservedCovers`, each read at the environment
(`MappedCovers.env`, `ObservedCovers.env` with `readFields_holds`,
`optionalFields_holds`, `aliasCells_holds`), as `ControlFlow.target_sound`
and `branch_target_sound` read them for the checker; `checkedEdge_env` is
the same for `checkedEdge`'s accepted result. This is the `htc` premise
of `exitDelivers_of_edge` and `exitDelivers_head` on an edge `run` accepts
by its search, at each context `run` searches from: the edge's own (its
facts the materialized edge store, expanded, which `edgeStore_normal`
gives), the yields' refinement and the mixed one (their typing at
$`\rho`$ the step's yields, `YieldsOk`, pass change D2). An edge accepted
by subtype answers alone reads the subtype cache (pass change D5).

**D8, the start an edge enters.** `run` enters it with `headEntry g
false`, as any head, and checks each edge into it as an edge into a head,
so `exitDelivers_head` covers those edges with the start's given facts
`startGiven …`. Proved (`start_entered_passPreT`): with that entry,
`entryRefusal` accepting, the counter at or past the inputs' width and the
entry meeting the inputs, the separation and the index facts, the start's
typed assertion holds at the entry values (`headEntry_holds` from
`HeadEstablishes` at the entry: the given facts by `startGiven_holds`, no
given implication, each given input and the promised input at its own
slot). `StartNotReentered` is then not a premise: `PassWalkSound.entered`
is `start_passPreT` at a start no edge enters and `start_entered_passPreT`
at one an edge enters, and `HeadsEntered` at the start is
`headsEntered_of_recorded` as at any head.

## Leg 14b: the shape of a branch's value

Module `lean/Verification/Programs/TolerantFramesComposeShape.lean`.
`NodeAccepted.shape` asks every value of the claim's type to have its
continuation's shape (`ShapeOk`): a Boolean at a branch. Neither the
graph's well-formedness nor the lowering gives it, since the claims are
the producer's; the proved checker tests it of a branch's evidence
(`ControlFlow.checkNodeResult` at `.branch`, `decide (expand G (result c)
= [.bool])`), and `run` makes no such test. The check the pass needs is
that test at a branch node (`passShapeCheck`). Proved: `branchShape_of`,
the test gives `true` or `false` of every value (`represents_raw` at the
Boolean clause); `nodeShape_of`, `passShapeCheck` gives `shape` at every
continuation.

`ShapeOk` and `NormalTarget` are `False` at `branchBind` and `tagBind`:
the node obligations admit no node with those continuations, so a unit
with one is outside `stepEdgesSound_of`. The checker covers them by
`onlyBoolean` at `branchBind` and the tag's observation at `tagBind`
(`ContinuationOk`, `BranchTargetOk`); `NodeObligations` would take the
same.

## Leg 14b: the regional check of one node

Module `lean/Verification/Programs/TolerantFramesRegionalNode.lean`. Proved:

- (`checkNode_sound`) `checkNode` accepting node $`l`$ at its evidence
  $`c`$ ∧ `ExpressionOk G c node.expression` ∧ `SummariesSound` ⟹
  `NodeWithinAt` (the node's conjunct of `NodesWithin`): the core of
  `checkNodes_sound`, its typing premise the node's own instead of the
  whole graph's acceptance (`graph_node`); `nodesWithin_of` assembles it;
- (`checkNode_mono`) the check over the node's tables holds over the
  graph's where they agree (`TablesAgree`): equal at the node, and at each
  target of its continuation and handler the graph's entry within the
  node's, in each of the four tables (every target check is an `all` over
  the target's entry: `checkEdges_mono`, `checkHandler_mono`,
  `edgesFresh_mono`, `handlerFresh_mono`, `edgesFields_mono`,
  `handlerFields_mono`);
- (`meet_sub`) the meet of the established entries is within each, the
  agreement at a target other than a head, once the meet is over every
  predecessor's entry (the in-degree order, `run_traversed`).

The graph's tables are then, at each label, the entry `run` checks the node
at (the regions' inputs at the start, a head's given facts, the meet of
the entries the edges into it establish, with the kept cells and fields).
What `RegionsKept` still needs, beyond `NodeWithinAt` at every visited
node:

1. `ExpressionOk G cEv node.expression` at the evidence `run` checks
   (`⟨ordinaryEv, some ⟨c.context, node.expression, c.type⟩, [], kHere,
   stepEffect, …⟩`): it quantifies over every environment meeting the
   evidence's context and its facts `kHere` (materialized from the entry
   state), while the step theorem gives the node's judgment from the entry
   state holding; and the evidence's context is its derivation's claim,
   which `run` does not compare with the node's at this check. A named
   hypothesis (`RegionalTyped`), discharged by the derivation's tree check
   at the node's context, as `footprintCheck`'s `derivChecked`;
2. the composition along a run: `NodesKeep` with $`X`$ the graph's tables
   holding (`LabelHolds`) and the regions within, as
   `ArgumentRegionGraph.bounded_step` composes `NodesWithin` for the
   checker from `StateOk`, here from `passPreT` and the step's judgment,
   with `StableNow` at the entry world carried in $`X`$.
   Not proved here.

## Leg 14b: premises this leg discharges and leaves

Discharges:

- `FootprintKept`: `footprintKept_of`, from `NodeAccepted`, `BoundChecked`
  and `CallFreshOk` at every visited node; its `FreshOk` of the receiver
  slots from the entry state's fresh names (`freshOk_recv`);
- `ReturnsEnsured`: `returnsEnsured_of`, from `NodeAccepted` and
  `ReturnChecked` at every visited node;
- the edge lemmas' target types (`htc`) on an edge accepted by the edge
  search: `checkedEdge_env` (D1), given the edge's facts holding and its
  context typing the source environment;
- `StartNotReentered`: `start_entered_passPreT` at a start an edge enters
  (D8), with `exitDelivers_head` and `headsEntered_of_recorded` at the start
  as at any head;
- `shape` at a branch: `nodeShape_of`, given the check `passShapeCheck`
  (needs a pass change: the checker's Boolean test at a branch node).

Leaves:

- `CallFreshOk`: a call's fresh result read off the derivation's selected
  effect (pass change D4);
- `AssertionsHeld` from `passPreT`: the entry state does not entail every
  written fact (Leg 14b: a written assertion on its edges and in the entry
  state); the edge's check gives it (`assertion_query_sound`), carried by a
  node assertion stating the assertions;
- `RegionsKept`: `RegionalTyped` (the evidence's `ExpressionOk`), the
  graph's tables' agreement with each node's through the in-degree order,
  and the composition along a run;
- the guard and assertion goals of `NodeAccepted.ret`: `ret` read at the
  state after the step, `YieldsOk`, the subtype answers (D5);
- `branchBind` and `tagBind` continuations: outside the node obligations;
- `htc` on an edge accepted by subtype answers alone (D5), and at the
  yields' refined and mixed contexts (`YieldsOk`, D2).

## Leg 15b: node obligations at every continuation

Modules `lean/Verification/Programs/TolerantFramesNodeBinds.lean` and
`TolerantFramesNodeBindsExits.lean`.

The lowering emits no `branch` continuation: every two-way dispatch of a
source is a `branchBind` (a condition whose claim type is Boolean) or a
`tagBind` (a condition by truthiness, a `typeof` or equality guard, `?.`
and `??`, a default for `undefined`, a read before initialization, an
`Array.isArray` test, a `__proto__` key), at 19 sites of
`Source/Lowering` (`Control.lean`, `Atoms.lean`, `Execution.lean`,
`Bindings.lean`, `Flow.lean`). `ShapeOk` and `NormalTarget` are `False` at
both, so `NodeObligations` covers no unit with a condition.

`ShapeOk'` and `NormalTarget'` extend them: at `branchBind y n` the value
is `true` or `false` and the arm it selects holds at
$`\mathrm{mapEnv}\ \theta\ (\mathrm{push}\ v\ \rho)`$; at `tagBind tg y n`
any value, and the arm of `tagHoldsIn h tg v` in the heap of the state
reached holds at the pushed environment, as `Transition.yesBind`, `noBind`
and `tagBind` take them. `NodeObligations'`, `EvalOk'`, `GraphInv'` and
`NodesChecked'` are the existing definitions over them. Proved:

- `shapeOk'_eq`, `normalTarget'_eq`: on the other four continuations they
  are `ShapeOk` and `NormalTarget`; `nodeObligations'_of`,
  `nodesChecked'_of`: every `NodeObligations` is a `NodeObligations'`;
- `graph_step'`, `graph_safe'`, `graph_safe_at'`, `graph_inv_run'`,
  `reached_pre'`, `transfer'`: the graph theorems over `NodesChecked'`;
- `nodeShape'_of`: the shape check `passShapeCheck'` (the proved
  checker's `onlyBoolean` at a `branchBind`, nothing at a `tagBind`) gives
  `ShapeOk'`;
- `ofNode_flags`: an exit of `Exit.ofNode` observes only where it pushes
  and promotes only where it does not, the premises `hpo` and `hpp` of
  `exitDelivers_of_edge` and `exitDelivers_head`, which therefore deliver
  the exits of both continuations as they stand (the observation's facts
  by `edgeStore_observed`);
- `normalTarget'_of_exits`: from every exit delivering, the normal target
  at every continuation; a `branchBind`'s exits observe `.boolean`, a
  `tagBind`'s observe `.tag tg q`, which `tagHolds_of_heap` gives from the
  answer in the heap;
- `nodeObligations'_of_parts`, `NodeAccepted'` (`NodeAccepted` with
  `ShapeOk'`, `NodeAccepted.toPrime`), `stepEdgesSound'_of`,
  `StepEdgesSoundT'`, `stepEdgesSoundT'_of`, `run_sound_of_walk_typed'`.

The rest of the guarantee (`nodesChecked_of_walk`, `keeps_step`,
`keeps_postExc`, `reached_pre` and the fields of `TolerantFramesGuarantee`)
is generic in the node obligations: replacing `ShapeOk` and `NormalTarget`
in `TolerantFramesRuns.lean` by `ShapeOk'` and `NormalTarget'` adds the two
cases of `graph_step'` to `graph_step`, the two of `normalTarget'_of_exits`
to `normalTarget_of_exits`, the two of `nodeObligations'_mono` to
`nodeObligations_mono` and the `branchBind` case of `nodeShape'_of` to
`nodeShape_of`; no other proof unfolds either definition.

## Leg 15b: the regional check kept along a run

Module `lean/Verification/Programs/TolerantFramesRegionalRuns.lean`. The
regional facts at a node entry are `RegionX`: the regions within $`\Phi`$
from the invocation's entry heap $`h_0`$ at the entry values
$`\rho_0`$, and the graph's tables at the label holding (`LabelHolds`), as
`ArgumentRegionGraph.bounded_step` carries them for the certificate
checker.

A node's regional obligation (`NodeWithinAt`) reads, beside these, the
regions' single-field paths of $`\rho_0`$ fixed in the current world
(`StableNow`), a property of the world that `RegionsKept`'s facts $`X`$
(of the environment and heap) cannot state. The node assertion carries
it: `passPreS` is `passPreT` and `StableNow` at the state's world, and
`RegionsKeptS` is `RegionsKept` at `passPreS`. Proved:

- `stableNow_admissible`: an admissible transition keeps `StableNow`;
  `nodesChecked_stable`: a property every admissible transition keeps
  joins the node obligations' targets;
- (`regionally_of_walk_stable`) `WalkSound` ∧ `RegionsKeptS` ∧ `passPreT`
  at the start ∧ `StableNow` at the start's world ∧ $`X`$ at the start ⟹
  the run within the regional bound, the conclusion of
  `regionally_of_walk`;
- (`regionsKept_of`) `RegionNodeOk` at every visited node ⟹
  `RegionsKeptS` with $`X`$ = `RegionX`: the node's obligation at the entry
  state gives the regions within and the targets' tables on every normal
  exit (`checkEdges_sound`, `edgesFresh_holds`, `edgesFields_holds`,
  `contKeeps_regionX` at every continuation, `branchBind` and `tagBind`
  included), and on a throw the handler's tables or, escaping, the regions
  within where the bound covers throws;
- `RegionNodeOk.ofCheck`: the check `run` makes over the node's tables,
  their agreement with the graph's (`TablesAgree`, `checkNode_mono`),
  `RegionalTyped` and the evidence's entry give `RegionNodeOk`;
- `regionNodeEntry_of`: the evidence's entry (its context, no
  implications, its facts the materialized entry state) holds where the
  node assertion does, given the evidence's context is the node's;
- (`regionalTyped_of_tree`) `regionalDerivChecked` (the step's derivation
  claimed at the node's term and context, its tree accepted) ⟹ the
  evidence's context is the node's and `RegionalTyped`;
- `regionX_start`: the start's facts from the start's table
  (`checkEntry`, no fresh value, cell or field).

What the pass needs for these premises:

- `StableNow` at the start's world: `checkEntryFields_sound` from
  `ArgumentPathTracking.checkEntryFields G inputs regions`, which the
  certificate checker's `goto_bounded` makes and `run` does not
  (needs pass change);
- `RegionalTyped` and the context agreement: `regionalDerivChecked` of the
  step's derivation at the regional check, the conjuncts `derivChecked`
  makes in `footprintCheck` (needs pass change: `run`'s regional check
  reads `stepDeriv` unchecked); a step without a derivation (a copy, step
  evidence alone) needs its own typing argument;
- `TablesAgree` at every visited node: the graph's tables the meet of the
  established entries over every predecessor (`meet_sub`), the in-degree
  order of `run_traversed`.

The guarantee's `regions` field (`PassWalkSound.regions`) reads
`RegionsKept` at `passPreT`; `regionally_of_walk_stable` is its form at
`passPreS`, which the fold replaces it by.

## Leg 15b: the written assertions in the node assertion

Module `lean/Verification/Programs/TolerantFramesNodeAsserts.lean`. `run`
reads the request's assertions by label (`stated`, `byLabel`). The node
assertion `passPreA` is `passPreT` and the label's written assertion
holding (`AssertsAt stated`); `edgePreA` is `edgePreT` and the target's.
Proved:

- `passPreA_adminClosed`; (`nodesChecked_of_walkA`) `Traversed` ∧
  `StepEdgesSoundA` (`StepEdgesSoundT` with the targets' `edgePreA`) ∧
  `HeadsEntered` ∧ `MergesSound` ⟹ `NodesChecked` at `passPreA`;
  (`asserted_of_walkA`) the written assertion holds at every node entry a
  run from the start reaches with budget left;
- `holds_of_assertsAt`: where every `(l, k)` of the request is `stated l`,
  `AssertsAt` gives `AssertionsHeld`'s conclusion;
- (`assertsAt_of_edge`) on an edge into a node other than a loop head, the
  edge's assertion check gives the target's written assertion
  (`assertion_query_sound`), its facts by `edgeFacts_holds` (the edge's
  materialized store, `edgeStore_normal`, `stateHolds_materialize`);
- (`assertsAt_of_head`) on an edge into a loop head, `HeadEstablishes`
  gives the head's given facts, the written assertion with the claims'
  index facts (`holds_of_indices_append`);
- (`assertsAt_start`) at the start, `entryRefusal`'s entailment of the
  written facts (`entryRefusal_ok`, `entryKnows_sound`);
- `exitDeliversA_of`: an exit delivering `edgePreT` and the target's
  written assertion delivers `edgePreA`.

The change to the walk modules: `WalkSound.steps` at `StepEdgesSoundA`,
`PassWalkSound.entered` at `passPreA` (`start_passPreT` with
`assertsAt_start`), `AssertionsHeld` at `passPreA` (true by its
definition), the field `asserted` of `run_guarantee` from
`asserted_of_walkA`; `NodeAccepted.exits` and `exitDelivers_head` then
deliver `edgePreA` through `exitDeliversA_of` with the three lemmas above.

The three facts the entry state does not entail (Leg 14b: a written
assertion on its edges and in the entry state) leave the entry state
weaker than the written assertion: the step reads fewer facts and refuses
more. With the written assertion stated in the node assertion they are
only a proof inconvenience:

- an atom whose renaming is `none` names a slot no name holds; the edge
  check reads the written atom at the target's slots, independently of the
  renaming;
- `Store.addBound` skipping a bound for an equal-or-stronger one of the
  same normal form keeps a bound the step reads in place of the written
  one; the written one, with the definedness of the terms its normal form
  drops, is the edge check's;
- a separation fact's atoms carry no level bound in the state; the written
  separation is read from the edge check.

`byLabel` keeps the first assertion a request states at a label, so a
request stating two at one label has the second checked on no edge, while
`GraphGuarantee.asserted` states every pair of `assertions`. `run` accepting
such a request states an assertion no check established (observed in the
code; no request with a repeated label is demonstrated). Needs pass change:
`run` refuses a repeated label, or joins the assertions a label states;
`holds_of_assertsAt`'s premise then holds.

## Leg 15b: a guard's and an assertion's goal at a return

Module `lean/Verification/Programs/TolerantFramesNodeGoals.lean`.
`NodeAccepted.ret` gives the goal from the value alone; a type guard's
goal (`x is T`) and an assertion function's (`asserts x is T`) read the
promised argument $`a`$, the entry value of the goal's slot. Its
state-dependent form, at the state after the step $`s'`$ and the pushed
environment $`\mathrm{push}\ v\ \rho`$, is the conclusion of
`goalHolds_of_return`: `GoalHolds G goal a` of $`v`$ at $`s'`$.

`returnCheck` checks the promise as the certificate checker's
`checkReturnResult` does: `returnGuard_of_check` and
`returnAssert_of_check` read its code (the answer's type Boolean, or
`undefined`; the answer `true` impossible, or the type empty; or a slot of
`passHeld`, the entry's slots holding `argName`, whose type refined by the
yields at the entry's slots, `passReturnYields`, a subtype answer places
within the promise, `returnWithin`, `returnWithin_sound`). Proved:

- (`returnOk_of_check`) `returnCheck` accepting ∧ `SubtypeAnswersSound`
  ⟹ `ControlFlow.ReturnOk G goal c.context c.type (passReturnYields …)
  (passHeld …)`, or the goal is plain;
- (`passHeld_argument`) the entry state holding ∧ `argName` the start name
  of the goal's slot ⟹ every slot of `passHeld` reads the promised
  argument (`ArgumentsOk`; `slot_start`);
- `goalHolds_at`: `ControlFlow.goal_return` at the state's own level;
- (`goalHolds_of_return`) `returnCheck` accepting ∧ `SubtypeAnswersSound`
  ∧ `argName = goal.slot.bind (startNames[·]?)` ∧ the state after the step
  holding at $`\mathrm{push}\ v\ \rho`$ ∧ the pushed context typing it ∧
  `YieldsOk` of `passReturnYields` at $`\rho`$ and $`v`$ ∧ a plain goal's
  result type containing the claim's ⟹ `GoalHolds G goal a v` at $`s'`$.

Named hypotheses: `SubtypeAnswersSound` (an accepted `subtypeUsing`
answer, from any table, an inclusion of meanings: pass change D5);
`YieldsOk` of the step's yields (pass change D2). The plain goal's premise
is `NodeAccepted.ret` at a plain goal (`plain_return`).

## Leg 15b: a call's fresh result behind its derivation's check

Module `lean/Verification/Programs/TolerantFramesNodeCallFresh.lean`.
`passOutFreshChecked` is `run`'s `outFresh` with its call disjunct
(`passCallFresh`) behind `passDerivChecked`, the check pass change D4
adds; `passOutFresh_of_checked` gives the existing `outFresh` from it.
`CallFreshBelow` is `CallFreshOk` over the runs within the state's budget,
the runs `footprintKept_of` reads (`EvalKeeps`). Proved:

- (`callFresh_of_checked`) `passCallFresh` ∧ `passDerivChecked` at the
  node's sequent ∧ `CodesSound` ∧ `SummariesSound` ∧ the mark at most the
  heap's length ∧ the context typing the environment ∧ the step's
  knowledge holding ⟹ every run of the node's term within the budget to a
  value returns a store allocated at or past the mark: the selected
  effect's `post` (`selected_sound`, or `requiresTree_sound`) states the
  result fresh at the heap's length (`Effect.post`'s `fresh` conjunct),
  `FreshAt.lower` at the mark.

`CallFreshOk` quantifies over runs of every length, which the step's
judgment at the state's budget does not bound; the fold restates it as
`CallFreshBelow`, which `footprintKept_of`'s consumption (`hcf … k …`,
`k` below the budget) already meets.

## Leg 15b: premises this leg discharges and leaves

Discharges:

- the node obligations at `branchBind` and `tagBind`: `NodeObligations'`,
  `graph_safe'`, `normalTarget'_of_exits`, `stepEdgesSound'_of`; the
  edge lemmas cover both continuations as they stand (`ofNode_flags`);
  the shape at a `branchBind` from `passShapeCheck'` (needs the pass's
  `onlyBoolean` test there, beside Leg 14b's `branch` test);
- `RegionsKept`: `regionsKept_of` and `regionally_of_walk_stable` at the
  assertion fixing the traversed fields (`passPreS`), from `RegionNodeOk`
  at every visited node (`RegionNodeOk.ofCheck`);
- `AssertionsHeld`: by `passPreA`, every edge establishing the written
  assertion (`assertsAt_of_edge`, `assertsAt_of_head`, `assertsAt_start`),
  `asserted_of_walkA`;
- the guard and assertion goals of `NodeAccepted.ret`:
  `goalHolds_of_return`, under `SubtypeAnswersSound` (D5) and `YieldsOk`
  (D2);
- `CallFreshOk` within the budget: `callFresh_of_checked` under D4.

Leaves:

- the fold of `ShapeOk'`, `NormalTarget'` into `TolerantFramesRuns.lean`
  (the two cases each of `graph_step`, `normalTarget_of_exits`,
  `nodeObligations_mono`, `nodeShape_of`), of `passPreS` and `passPreA`
  into `WalkSound`, `PassWalkSound` and `run_guarantee`, and of
  `CallFreshBelow` into `footprintKept_of`;
- pass changes: `onlyBoolean` at a `branchBind`; `checkEntryFields G
  inputs regions` under a regional check (`StableNow` at the start);
  `regionalDerivChecked` of the step's derivation at the regional check
  (`RegionalTyped`); a repeated assertion label refused or joined
  (`byLabel` checks the first); D2, D4, D5;
- `RegionalTyped` at a node whose step has no derivation (a copy, step
  evidence alone); `TablesAgree` at every visited node (the meet over
  every predecessor, `run_traversed`'s order); the mark at most the
  heap's length at a node entry (`callFresh_of_checked`'s `hm`).
