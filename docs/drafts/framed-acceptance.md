# Draft: accepting a unit through the read-only frame

A design for the step from the read-only frame rule, proved at the paper's
executions, to a unit's accepted verdict. It adds one constructor of
`FunctionPlan`, a framed plan, with its branch in `FunctionPlan.certify`,
and the theorem that the pass's check of a framed plan gives
`PassUnit.FramedRequestSafe` at a frame built from the request itself, so
that `SourceClaimJson.PassUnit.mode8Accepted_sound` covers a unit accepted
that way under the client obligation $`\Theta_C`$ of
[Trust](readonly-handles.md#trust). It is stated for every function a
component exports, every call inside the component whose run may reach
code outside it, and every fact the graph carries across a call, with the
restrictions of the language it needs stated and enforced
([restrictions](#restrictions)).
[P22's walker](../../pipeline/examples/bounds-pattern-unreachable-field.ts)
and pretext's walkers are its tests ([Tests](#tests)); the first buildable
milestone is the bound route for P22 ([milestones](#milestones)).

Base: branch `p22-accept` at `c05b844db`. Notation is that of
[Read-only frames](readonly-frames-note/note.tex) and of
[read-only handles](readonly-handles.md#the-rule): a component $`C`$, its
region $`R_C`$, its protocol $`\Psi_C`$, the client obligation
$`\Theta_C`$, the action $`h\xrightarrow{\Phi}_\rho h'`$ of an effect and
$`\Phi\oplus_C\Psi`$. Each claim is labelled **proved** (a Lean name at
the base), **to be proved** (its plan and the proved results it reuses),
**trust** (an assumption about code outside the analyzed sources), or
**observed** (a run, under Node 26.13.0 or of a Lean file at the base,
listed in [Runs](#runs)).

## The existing mechanism this extends

Three mechanisms, each kept, each changed at one place.

1. **The graph's transfer at a call** ([footprints](../FOOTPRINTS.md#a-calls-effect-at-the-caller),
   rule Frame of [Tolerant frames](tolerant-frames-note/note.tex)). At a
   call node the pass keeps a fact of the caller where its support
   respects the callee's effect read at the caller's slots, $`\Phi`$
   (`PromiseCalls.callerFrame`): `callKept`, `callGrown`, `frameKeeps`,
   each sound from the heap relation the callee's semantic type gives at
   its return (`callerFrame_post`), and at a handler from the exceptional
   effect where the callee states one (`callExc`). This design changes one
   predicate: at a *framed call* of the request's main graph a support may
   instead pass the read-only frame's check, whose soundness is a return
   premise the execution discharges
   ([the graph at framed returns](#the-graph-at-framed-returns)). The
   ordinary graph theorem is its instance with no framed call.
2. **The read-only frame rule** ([the rule](readonly-frames-note/note.tex),
   [read-only handles](readonly-handles.md#what-the-lean-states)), with its
   consequence over the paper's executions (proved: `exec_rely`,
   `ClientFrame.call_rely`), its premise checked at a frame of $`C`$'s code
   (proved: `ClientFrame.framed_at_call`, `ClientFrame.framed_at_innermost`,
   `frameCheck_sound`) and the flow of sites (proved: `FFlow.check_sound`,
   `fitsAt_reached`). This design generalizes the rule's premise from a
   call of outside code to a call whose run may reach outside code, a
   function of $`C`$ among them ([the transfer](#the-transfer-at-a-call)),
   states one notion of charges with one local lemma at the base of any
   call ([charges](#charges)), indexes certificates by the calls an
   execution makes ([certificates](#certificates)), and records each
   entry's incoming crossing in the history, as the note's Appendix A states
   it ([the history](#the-history-of-a-program)).
3. **The acceptance path** (CLAUDE.md, "Acceptance/soundness invariant").
   `CertifiedPlan.framed`, `PassUnit.FramedRequestSafe` and `MemberSafe`'s
   branch reading it exist (proved: `framed_callSafe`,
   `callSafe_of_member`); no `FunctionPlan` certifies to a framed plan.
   This design adds `FunctionPlan.framed`, its branch of `certify`, the
   constructor `MemberAccepted.framed`, and `framed_requestSafe`, at a frame
   whose calls are the actual calls of the request's code entered from
   outside code in programs ([the frame of a request](#the-frame-of-a-request)).

## Findings this design closes

Each finding is a property of the base or of an earlier version of this
draft, verified by a run or by reading the Lean named, with the section
that closes it.

**The first two rounds** (gaps of the proved results; vacuity of `enters`
and of the flow; the guarantee's return; the entering step and the joined
protocol; a redirected path; charges tied to the lowered code; callers and
the callback's type; `callParts`' universe; local storage; the start's
length and totality; `PublicCall`'s world and closures; the codes and the
sixth clause; $`W_c`$ at P22's cursor; `Cert.own`'s entering edge; a
writable prefix; the guarantee's proof; verdicts reading a framed arrow):
each is closed in the section that now owns it, as the third round
records (Astra and Fable found none of them reopened, Fable's table).

**The third round.**

- **The prologue** (Astra 1): a receiverless module function runs its
  prologue on tables extended past the request's, so the realized term is
  no `gotoOf r.program …` (Astra's Lean check). Closed by a simulation
  ([realization](#realization)).
- **The program's history protected nothing** (Astra 2, Fable F2): the
  frame's crossings were all `.outOf`, so no location was protected along a
  program (`NoProt.lean`: `ex_noProt`, `rowAt_vacuous`), `project` was
  false (`project_false`), and keeping $`\Theta_C`$ before the call
  constrained no step. Closed: `chk` records each entry's arguments
  crossing in at the actual invocation ([the history](#the-history-of-a-program);
  `Round4.lean`: `cross_into_prot`, `truncate_after_cross`).
- **Storage reached through another closure's capture** (Astra 3, Fable
  F4): `local_reach` and $`W_c`$ admitted a capture slot's site but not what
  it reaches (`nested-capture.mjs`, `undefined`; `boxed-capture.mjs`,
  `NaN`). Closed by one closure of sites through contents and captures,
  used in the lemma, $`\Psi_C`$ and $`W_c`$ ([charges](#charges)).
- **Stores checked at one root** (Astra 4, Fable F1, milestone 4): a store
  keeping $`I`$ at the written root breaks it at another root sharing the
  support (`shared-support.mjs`, `NaN`). Stated as open for milestone 4
  with the fix ([the guarantee route](#the-guarantee-route)).
- **Allocation origin** (Astra 5): a flow giving an allocation the site
  `none` passes `FFlow.check`, `marksB` and `entryB` (`AstraR3.lean`,
  `(true, true, true, none)`), so `Held` read the proposal. Closed: sites
  are the lowering's numbering, checked (`Round4.lean`, `allocSomeB` false
  on that flow; [the binding checks](#the-binding-checks)).
- **$`\Theta_C`$ with path keys** (Astra 6, Fable F5): `@clients` admits path
  keys per exported type. Closed by a restriction, stated and enforced
  ([restrictions](#restrictions)).
- **The realm's intrinsics** (milestone 1's first check): P22's `walk`
  captures `[[Array.prototype]]` beside `%ElementAt%`, an object of the
  realm, so an empty initial heap holds no value for that slot. Closed: an
  initial configuration starts from the realm's heap, and the restriction
  admits its intrinsic objects ([initialization](#initialization),
  [restrictions](#restrictions)).
- **The initialization** (Fable F3): the base realizes module closures as
  finite unfoldings (`ModuleClosures.lean`), so an initialization holding
  "the module closures" is undefined where module functions name each
  other; `PublicCall` read the frame it defines; the program-level lemmas
  were stated over `Reached`. Closed in [initialization](#initialization)
  and [the calls the claim is about](#the-calls-the-claim-is-about).
- **Framed units by form** (Fable F6): the public call was the invocation
  of a module closure. Closed: the notion is an entering step of the
  request's code, with a realization per kind of unit, and the kinds
  without one are a restriction ([restrictions](#restrictions)).
- **Smaller points** (Fable F7): `writeKeeps` names an existing function
  (renamed `storeKeepsInv`); the outgoing crossings' type; the world of the
  start; `Inv` after an incoming crossing. Closed where each is named.

**The fourth round.**

- **Sites under the realization** (Astra 1, Fable N1): with a numbering per
  code, the same body allocation gets two sites in the request's tables and
  in the realized ones (Astra's check: `some 6` and `some 8`; Fable's
  `RealizedCode.lean`: `(some 0, none)`), on P22's own `const c = { i: 0 }`.
  Closed: one canonical site per body allocation, keyed by the body, and
  `chk` invariant under the realization ([realization](#realization);
  `Round5.lean`, `body_prefix`).
- **`approx_stable`** (Astra 2, Fable N2): false where an outside slot
  varies with the depth (`ApproxStable.lean`). Closed by a restriction,
  every outside slot an audited realm value constant in the depth, which
  P22's elaborated layout meets (measured, `layout.out` and the probe's
  module code), and the stability lemma under it (`PassUnit.approx_stable`;
  [initialization](#initialization), [restrictions](#restrictions)).
- **Coverage from each actual invocation** (Astra 3, Fable N5): the
  theorem from an actual public invocation to the request's claim was
  missing; the client's scope is one binder under the whole `letE`; a rest
  parameter's spine is built before the depth increases. Closed by
  `publicCall_safe` ([the calls the claim is about](#the-calls-the-claim-is-about)).
- **Write coverage of a residual redex** (Astra 4): a writing redex reached
  after its receiver is evaluated needs an invariant linking it to its
  source write. Closed by charging a write at every site of its kinds and
  the residual invariant `WOk` ([charges](#charges)).
- **Crossings beyond the entry** (Astra 5): stated as the subset milestone
  1 implements ([the history](#the-history-of-a-program)).
- **The entry crossing falsifies `ActualCrossings`** (Fable N3,
  `IncomingCrossings.lean`). Closed: the lemmas restated over the
  crossings with the incoming ones, and `crossOk_incoming`
  ([the history](#the-history-of-a-program)).
- **`paramTypes` of a shared code** (Fable N4, `EnteredTables.lean`). Closed
  by the meet over the functions sharing a code
  ([the history](#the-history-of-a-program)).
- **`writesIn` is partial** (Fable N6, `WritesInOpaque.lean`). Closed by a
  total definition (`writesK`).
- **Smaller points** (Fable N6): `FrameSpec` named the probe's structure
  (renamed `FramedSpec`); `entry_slot_holds_O_tokens` is the second
  review's check (`CodeClause.lean`), to be moved into the build;
  `PublicCall` stated with `KStep` and the depth; the typed program is a
  part of $`\Theta_C`$'s row ([trust](#proved-to-be-proved-trust)).

## Definitions

A state is a configuration of the paper's executions with its history,
$`s=(x,g)`$ (`Conf × Ghost`); $`\delta(s)`$ is the number of calls of
$`C`$ active at it (`depthC`).

- **A call state** of a frame $`f`$: $`f`$, a frame of $`C`$'s code with
  environment $`\rho_f`$, is the innermost frame of $`s_0`$'s term, and
  its term is a call whose callee, receiver and arguments are values. The
  pass's call nodes have this form (`call_local_sound`).
- **The call's segment**: the steps from $`s_0`$ to the first later state
  $`s_1`$ at which $`f`$ is innermost again, its term a value (a normal
  return) or a throw (an exceptional return), the *resumption*. Along it
  $`\delta\ge\delta(s_0)`$.
- **The steps at the caller's depth** in a segment: steps from states with
  $`\delta=\delta(s_0)`$, each of $`C`$'s code or of outside code. Every
  deeper step is inside a call of $`C`$ entered from outside code, a
  member's call.
- **The segment's codes** $`\mathrm{seg}(c)`$ of a call node $`c`$: the
  least set of codes of the flow holding each code whose token the
  callee's set at $`c`$ holds, and closed under the same at every call
  node of its members and under the tokens of the closure arguments of
  every native step model its members call (`segCodes`, computed, and
  `segClosedB`, its closure decided, sound by `segClosedB_sound`,
  `ReadOnlyCharges.lean`). At a
  call of a parameter holding what outside code may supply it holds every
  code whose token lies in $`O`$ (`entry_slot_holds_O_tokens`).
- **The closure of sites** $`\overline{S}`$ of a set $`S`$ of sites and
  tokens (`capClose`, computed, and `capClosedB`, its closure decided,
  sound by `capClosedB_sound`): the least superset of $`S`$ closed under
  the heap of sites' contents (each site's `contents`) and under captures
  (for each code token in it, the sites and tokens of that code's capture
  slots at every context, `captureSites`).
- **A framed call**: a call node of the request's main graph whose
  callee's set holds outside storage, or such that some code of
  $`\mathrm{seg}(c)`$ has a node whose callee's set holds it (`reachesOut`,
  decided). The calculus has no implicit call (an arithmetic of a
  non-primitive throws, `arithThrow`), so each run of outside code starts
  at an `invoke` or `construct` step.
- **The effects at a call.** $`\Phi`$ is the callee's effect read at the
  caller's slots; $`\Phi^{e}`$ is $`\Phi`$ where the callee's type states
  an exceptional bound and $`\top`$ otherwise; $`\Phi_\star`$ is $`\Phi`$ at
  a normal return and $`\Phi^{e}`$ at an exceptional one.

## Charges

**The charges of a set of codes** $`\mathrm{Ch}(M)`$: the kinds the writes
of the node expressions of the codes of $`M`$ may change, each field write
under a key $`k`$ at `roleKinds (slotBound k)` and each element store at
the element kind (`writesK`, `codeKinds`, `codesKinds`,
`ReadOnlyCharges.lean`), the native step models' codes among them. A
protocol from charges $`K`$ and a held set $`H`$ (`probeProtocol`) changes a
part by $`\mathsf{any}`$ where its kind is in $`K`$, and keeps it at a local
site outside $`H`$ and at every other kind: a write is charged at every site
its kind may have, and the precision on local storage is $`H`$'s, from the
local lemma below. The verifier computes the charges from the lowered node
expressions the flow holds, which the binding checks make the request's
lowered codes; nothing is discharged as fresh.

**The local lemma, at the base of any call** (`local_reach`, proved,
`ReadOnlyLocalReach.lean`). Let a run start at a heap $`h_0`$ and a term
$`u_0`$ (a call entered from outside code, or a call node $`c`$ of a frame
$`f`$, its term in its evaluation context), and let $`L`$ be a set of sites
such that every location one step reaches from a value $`u_0`$ holds, or
from a value the code of such a value holds (the captures and node
expressions of every closure, the parts of every bound function), is of a
site of $`L`$, and every location of $`h_0`$ of a site of $`L`$ holds such
a value (`DeepIn`, `HeapDeep`). Then a step of the run changes a location
$`l<|h_0|`$ only where its site is in $`L`$. Proof: reading every tag's
code as outside code (`allC`), the base's no-forgery (`step_noForge`)
holds of every step, so what the run's term reaches it reached at $`h_0`$
or allocated (`valRun_noForge`); the changed location is one step from a
value of the step's term (`step_reach`); so, being old, it is reached from
$`u_0`$'s values at $`h_0`$, and the reach stays among $`L`$'s sites
(`reach_deep`). A step of the run is then within the protocol from its
code's charges and $`L`$ (`stepWithin_reach`, with `stepWithin_charged`).

The flow gives both premises (`deepIn_of_vj`, `heapDeep_of_heapInv`,
proved) for a set $`L`$ that holds the sets of $`u_0`$'s values, is closed
under the heap of sites' contents, and is closed under captures
(`CapClosed`: for each code whose token it holds, the sites of each
capture slot at the code's entry at the layout of its closures), where the
closures of $`C`$'s code in $`h_0`$ and among $`u_0`$'s values have their
codes' layouts (`LayDeep`) and the node expressions of the flow's codes
hold no located value (`CodesLowered`: their values are spines with no
cell; decided by `codesLoweredB`, sound by `codesLoweredB_sound`,
`ReadOnlyLayouts.lean`). A capture's sites
are its slot's at its closure's code's entry (`VJ.capC`), a node
expression of a closure of $`C`$'s code holds no location
(`CodesLowered`) and one of outside code is lowered (`lowered_vals_all`), and the
code of a bound function or of a closure of outside code holds values
meeting its own set (`VJ.boundPart`, `VJ.capOut`). The closure of sites
$`\overline{S}`$ is closed under both, its closure under captures read
through each code's layout `lay` (`tokenCaps`), the layout of a code's
first entry (`layAt`, as the flow reads a code's proposals); its check
gives `CapClosed` at those layouts where every code's tokens are sites
(`capClosed_of_lay`, with `tokensSomeB`, proved). At the frame of a plan the
start premises of `lay_reached` and `wok_reached` come from the program
(`FramedSpec.lay_start`, `FramedSpec.wok_start`, proved,
`FramedRealize.lean`: along the public call and its realization,
`entry_run`, the request's run is the realized code's below the prologue
in a context, `EvalCtx.layP_hole`, `EvalCtx.wok_hole`), and an initial
configuration meets both where the initialization's node expressions and
the realm do and the client is lowered source (`initial_starts`, proved,
its premise the client's `LoweredSrc`, which `Initial` states,
`initial_lowered`).

The layouts are a run invariant (`layouts_reached`, proved,
`ReadOnlyLayouts.lean`): every closure a term or a heap holds or creates,
in the code of its values and runs included, has at its code, tag and
layout what `layQ` decides, a closure of $`C`$'s code its code's layout
(`layP`, `HeapLay`); every step keeps it (`step_layP`: a step builds its
result from the term's subterms, the code of the closures it calls and the
heap's values, and allocating a closure keeps its layout), so it holds at
every reached state from calls meeting it (`ClientFrame.lay_reached`) and
at every public call from initial configurations meeting it
(`FrameCore.lay_program`); an initial configuration does where the
initialization's node expressions do and the client is lowered source,
which creates closures of outside code only (`lay_initial`). A value
meeting it has `LayDeep` (`layDeep_of_layP`), and the premises of the local
lemma follow from the checks (`heapDeep_of_checks`, `deepIn_of_checks`).

Its two instances, each reading a closure:

- **The protocol** $`\Psi_C`$, at a member's call entered from outside
  code (the receiver and arguments meet $`O`$):
  $`\mathrm{Ch}(\text{all codes of }C)`$ at every part but a local part
  whose site is outside $`\overline{\bigcup_m\mathrm{captureSites}(m)\cup O}`$,
  which is $`\mathsf{keep}`$. The wire's proposal is checked to be at least
  this.
- **The depth charges** of a call node $`c`$: $`L(c)`$ is
  $`\overline{\mathrm{sites}(\text{callee})\cup\mathrm{sites}(\text{receiver})\cup\mathrm{sites}(\text{arguments})}`$
  (`callReach`), and $`W_c`$ is $`\mathrm{Ch}(\text{all codes of }C)`$ at
  every part but a local part whose site is outside $`L(c)`$, which is
  $`\mathsf{keep}`$ (`depthCharges`). Every frame of $`C`$'s code runs a
  code of the flow (`Fits.frameC`), so its charges are among them.
  `nested-capture.mjs` (`undefined`): the wrapper captures `bump`, `bump`
  captures `holder`, the changed field is at `holder.child`'s site; it is in
  $`L(c)`$ through the wrapper's capture of `bump`'s token, `bump`'s
  capture of `holder` and `holder`'s contents, so charged.
  `boxed-capture.mjs` (`NaN`): `k`, handed out and back, captures a box
  holding the cursor; outside storage is in $`L(c)`$, so its contents
  $`O`$, `k`'s token among them, its capture's site and the box's contents
  are, so the cursor is charged.
  At P22's `visit(c.i)` the argument is a number, the receiver
  `undefined`, and the callee's set holds outside storage and `walk`'s
  token, whose captures are module closures; the cursor's site is in no
  capture slot and in no site's contents (it is stored nowhere), so it is
  outside $`L(c)`$ and $`W_c`$ keeps it (observed, the flow probe).
- **The call's protocol** $`\Psi_c=\Psi_j\sqcup W_c`$ with
  $`\Psi_j=\Psi_C\sqcup\Theta_C`$.

**A step's changes are its code's charges** (`step_kind_charged`, proved,
`ReadOnlyWriteKinds.lean`): at a step from a term meeting the residual
invariant, with valid references, every old location the step changes has
a kind among the charges of the innermost frame's code.

- **The residual invariant** (`WOk`, kept by every step, `step_wok`): at
  every run of graph code in the term, `frame E K t …`, the writes its
  running term may still perform are among its code's
  (`writesK t ⊆ codeKinds E`), and the slots of a run, the captures of a
  closure and the parts of a bound function perform none, with a heap of
  such values (`HeapW`). A step's writes are among those of the term it
  steps from; an entered node instantiates its code's expression with
  plain values (`instantiate_wok`); a value performs no write
  (`writesK_val`). It holds at every reached state from calls meeting it
  (`ClientFrame.wok_reached`), and lowered code meets it (`lowered_wok`,
  proved); at a call the claim is about the term is the request's run,
  whose code is lowered, at slots and a heap of plain values, which every
  step of a program from an initial configuration keeps (`wok_program`,
  proved, `ReadOnlyLocalReach.lean`: `wok_ex` along a public call, from
  initial configurations meeting it; an initial configuration's term does,
  `wok_initial`, its heap the realm's, of plain values).
- **The active redex's writes** (`active_writes`): the writes of the term
  the next step reduces are among the charges of the innermost frame's
  code.
- `step_writes_active` (proved, `ReadOnlyStepWrites.lean`) locates the
  changed location at the active redex, a writing redex at it
  (`WriteRedex`), and `slotKind_sound` (proved) puts its kind among that
  redex's writes: a slot under $`k`$ has a role of `slotBound k`
  (`field_bound`), a spine's listed cell is an element cell. The
  invocation changes no old location.
- At a charged part whose site, where local, the held set holds, the
  protocol from charges is $`\mathsf{any}`$ (`probeProtocol_charged`).

A step from a term meeting the residual invariant whose innermost frame's
code's charges are among $`K`$, each changed old local location's site
held, is `StepWithin` the protocol from $`K`$ and the held set
(`stepWithin_charged`, proved). So **within a call** (`within_charges`):
every step of $`C`$'s code inside a member's call from $`a`$ is
`StepWithin Ψ_C |h_a|`, and every step of $`C`$'s code at the caller's
depth in a segment from $`s_0`$ is `StepWithin W_c |h₀|`. Its core is
proved at a run of the calculus (`stepWithin_reach`: `local_reach` gives
the held sites), with the frame's code's charges among every code's
(`Fits.frameIn`, `frameKinds_flow`: the innermost frame of a fitting term
runs a code the flow proposes for). Its instance at a call (`within_run`,
proved, `ReadOnlySegment.lean`) reads the call's run as the run of the
call's term $`u_0`$ in its evaluation context until it returns
(`hole_run`, by `EvalCtx.steps_inv`), so the local lemma's base is
$`u_0`$'s values, the callee, the receiver and the arguments: a step of
$`C`$'s code, or of no frame, of that run is within the protocol from
every code's charges and a set $`T`$ passing the closure check that holds
their sets. The innermost frame inside the call's term is the whole
term's (`activeFrame_ctx`, `activeFrame_hole`), so it runs a code of the
flow (`Fits.frameIn_hole`); the residual invariant and the references
pass from the whole term to the call's term (`EvalCtx.wok_hole`,
`EvalCtx.refs_hole`, `wok_steps`). Its two instances are $`W_c`$ at
$`T=L(c)`$ (`within_depth`) and $`\Psi_C`$ at the closure of the capture
sites and $`O`$ (`within_member`); `framed_transfer`'s segment
(`CallState`, `Inside`) supplies the context and the run.

## The transfer at a call

**Framed transfer.** For a fact with support $`S`$:

```math
\frac{s_0\ \text{reached, a call state of}\ f\qquad s_0\to^{*}s_1\ \text{its segment, every step keeping}\ \Theta_C\qquad h_0\xrightarrow{\Phi_\star}_{\rho_f}h_1\qquad \mathrm{Framed}(\Phi_\star,\Psi_c,S,\rho_f,s_0)}{\mathrm{Supported}(S,\rho_f,h_0,h_1)}\ \textsf{(Framed transfer)}
```

with `Supported` the relation of
[footprints](../FOOTPRINTS.md#support-and-respect): each location
$`l<|h_0|`$ of each $`(r:\delta)\in S`$, read at $`(\rho_f,h_0)`$, changes
within $`\delta`$. The argument: the segment's steps at the caller's depth
of $`C`$'s code change each $`l<|h_0|`$ within $`W_c`$; each maximal run of
outside code at that depth changes $`R_C`$ within $`\Psi_j`$, its member
calls by their certificates ((L2)); $`R_C`$ grows inside the call ((L3)),
so the segment changes each $`l\in R_C(s_0)`$ within $`\Psi_c`$; with
$`\Phi_\star`$ bounding every other location the segment is an action of
$`\Phi_\star\oplus_C\Psi_c`$, and `Framed` gives `Supported`.

Lean (proved, `ReadOnlyTransfer.lean`, in `ClientFrame`), at the claim's
top frame $`f`$ with code `E, K`, slots `L`, default `d`, continuation `k`,
handler `x` and tag `comp`:

```lean
theorem framed_transfer (hc : fr.ChkSound) (hi : fr.StartInv)
    (certs : fr.TraceCerts Ψj G) (hΘ : ∀ p, (fr.Θ p).le (Ψj p) = true)
    (hW : ∀ p, (Ψj p).le (Ψc p) = true) {a e : Conf × Ghost (fr.F.at fr.C)} {n : Nat}
    (ha : fr.Reached a) (hcall : CallState fr.F fr.C E K L d k x comp a.1.t)
    (hex : Ex fr.KStep (fun s => Inside fr.F fr.C E K L d k x comp s.1.t) n a e)
    (hres : Resumes fr.F fr.C E K L d k x comp e.1.t) (hown : fr.SegWithin Ψc E K L d k x comp a)
    (hΦ : TolerantFrames.Action Φ ρ a.1.s e.1.s) (hfr : Framed Φ Ψc S ρ (lift fr.F fr.C none a.1 a.2)) :
    Footprints.Supported S ρ a.1.s.h e.1.s.h
```

`CallState`: $`f`$ at the top of the term, of $`C`$'s code, its running
term a call of values. `Inside`: $`f`$ at the top, its running term not
returned (a value or a throw, `Returned`). `Resumes`: $`f`$ at the top,
its running term returned. `SegWithin Ψc`: every step of $`C`$'s code at
the call's depth from a state of the segment is `StepWithin Ψc |h₀|`. The
proof:

- **The segment as a run** (`seg_run`, proved, by the strong induction of
  `decompose` at the caller's depth). An execution from depth $`d>0`$ to
  $`d`$ whose states keep at least $`d`$ calls active is a
  `RunSeq … d d`: a step of $`C`$'s code at $`d`$ is a checked step at
  $`d`$ (not an exit, the next state being at $`d`$), a step of outside
  code at $`d`$ an inner run of one outside step, and an entry with the
  execution up to the first state at $`d`$ again an inner run of one
  member call (`callRun_trace`). Its bound (`seg_bound`) is
  `RunSeq.within` at $`d_i=d`$, the inner runs by `Run.bound` at
  $`\Psi_j`$ lifted to $`\Psi_c`$.
- **The depth.** A call state and a resumption are at depth 1
  (`CallState.depth`, `Resumes.depth`, `depthC_frame_val`), a state inside
  at least 1 (`Inside.depth`, `depthC_frame`).
- **The action**, as in `readOnly_rule` (`Leads.of_bound`), then
  `supported_of_framed` (`transfer_at`).
- **The saved environment.** A step of $`f`$ whose term has not returned
  is a step of its term (`frameC_shape`, proved), so every state of the
  segment is $`f`$ around a term the call's term reaches
  (`FrameCore.inside_run`, proved): $`\rho_f`$ is the same at every state.
- **The own steps** (`segWithin_of_run`, proved): `SegWithin` at the
  protocol from every code's charges and a set $`T`$ passing the closure
  check ($`W_c`$ at $`T=L(c)`$), by `within_run` at each own step. The
  call's run in its context is the frame's term's (`FrameCore.inside_run`)
  over the segment's heaps (`inside_prefix`), heaps of values by the flow
  (`fitsAt_reached`); the residual invariant, the layouts and the heap's
  flow at the call state by `wok_reached`, `lay_reached` and
  `fitsAt_reached`; the old locations' sites kept (`ex_sites`); and at one
  call of $`C`$ a step of $`C`$'s code has its innermost frame of $`C`$'s
  code (`activeFrame_runsC`: every frame on the path inside $`f`$ is of
  $`C`$'s code where the path has one block of $`C`$, `blocks_one_all`, and
  the innermost frame's tag is on the path, `innermost_tag`). Its premise
  at the call: the callee's, receiver's and arguments' sets are within
  $`T`$, each meeting layout provenance (`hroots`).

### An exceptional return

A framed node's kept facts are added at its normal exit alone
(`SinglePass.keptStep`, `keptDone_thrown`): its handler reads the store
the call's step leaves, with no fact kept, whatever the callee states of
its exceptional exit, and the claim's return premise at an exceptional
return is `True` (`framed_requestSafe`'s `RetE`). So a read in the handler
that needs a fact over the cursor is refused, `0 <= c.i` included
(observed: the reviews' `s14_throw_exit_onthrow`, `t6`, `k1`, each safe
and refused; `u29`, unsafe under Node, refused). $`\mathrm{Ch}`$ charges
a write at both exits.

### A call of the component's own code

A wrapper, a function of $`C`$ calling the client at its own call site, is
the callee of a framed call, and the transfer covers it: its own steps at
the walker's depth by $`W_c`$, its calls of the client by $`\Psi_j`$
(`wrapper.mjs`, `nested-capture.mjs`). $`\Theta_C`$ binds the client a
wrapper calls as it binds one an entry calls (`ClientFrame.Keeps`).

The note's rule reads, with the generalized premise:

```math
\frac{c:\Phi\mid\Phi^{e}\qquad c\ \text{a call inside a call of}\ C\ \text{whose run may reach code outside}\ C\qquad W_c\ \text{bounds its steps of}\ C\text{'s code at the caller's depth}\qquad \text{(S)}\quad\text{(K)}}{c:\ \Phi\oplus_C(\Psi_C\sqcup\Theta_C\sqcup W_c)\ \mid\ \Phi^{e}\oplus_C(\Psi_C\sqcup\Theta_C\sqcup W_c)}
```

The note's section "The rule" and Appendix A take this statement when it is
built.

### The check at a call

At a framed call node $`l`$ of code $`m`$, for each fact the ordinary
transfer drops, the pass runs the frame's check of its support for every
context of $`m`$ and every node $`l'`$ of $`m`$ with $`l`$'s continuation
and handler, and keeps the fact where all pass: `ClientFrame.framed_at_innermost`
(proved) gives `Framed` at some such context and node.

- **Keys.** A part's key is the key the world records in the location's
  role (`keyAt`, `St.part`), fixed along admissible transitions
  (`keyAt_kept`). A region's keys (`regionKeys`) are the key its form fixes,
  or none where its bound holds no field or cell; every location of a
  region has one of them (`regionKeys_sound`, proved), and a region given
  sites has finitely many (`regionKeys_of_sites`). A write at the key `k`
  charges the kinds of a slot under `k` at `k` (`writesK`, `slotKey`,
  `slotKind_sound`).
- **A region with no sites.** `frameCheckAt` refuses a region with no
  computed sites (`fields`, `pathFields`, `cls`, `all`).

### Protection

Milestone 1 reads every region unprotected (`prot` false), which loses
precision only. Milestone 2 reads a region protected where its slot holds
the value of a path of reads from an entry parameter at a read-only
position, and the locations the path and the region's prefix pass are
kept, with its witness from the entering step's crossing ([the protected reading](#milestone-2-the-protected-reading)).
`prefix.mjs` (`undefined`): a writable prefix is read unprotected.

## Certificates

A member's certificate states, of each actual call of a code from a
reached state, the bound and the guarantees over the call's trace: its
entering step and every own step after it.

```lean
def Entering (Adm) (m : Option Code) (a a₁ : Conf × Ghost (F.at C)) : Prop :=
  Adm a ∧ XStep F C c Θ chk a a₁ ∧ entered c a₁.1.t = m ∧ δ F C c a₁ = δ F C c a + 1

def OwnAfter (a a₁ y z : Conf × Ghost (F.at C)) : Prop :=
  (∃ n, Ex (XStep F C c Θ chk) (QCall F C c (δ F C c a)) n a₁ y) ∧ XStep F C c Θ chk y z ∧
    δ F C c y = δ F C c a + 1 ∧ ¬ Outside F C c y.1

structure Cert (Adm) (Ψ : Protocol (F.at C)) (G : (St (F.at C) → Prop) → Prop) (m : Option Code) where
  enterWithin : ∀ a a₁, Entering Adm m a a₁ →
    StepWithin Ψ a.1.s.h.length (lift F C c a.1 a.2) (lift F C c a₁.1 a₁.2)
  own : ∀ a a₁ y z, Entering Adm m a a₁ → OwnAfter a a₁ y z →
    StepWithin Ψ a.1.s.h.length (lift F C c y.1 y.2) (lift F C c z.1 z.2)
  enterKeeps : ∀ I, G I → ∀ a a₁, Entering Adm m a a₁ →
    I (lift F C c a.1 a.2) → I (lift F C c a₁.1 a₁.2)
  tolerant : ∀ I, G I → ∀ a a₁ y z, Entering Adm m a a₁ → OwnAfter a a₁ y z →
    I (lift F C c y.1 y.2) → I (lift F C c z.1 z.2)
```

Every field reads the actual entering edge (`keep_rejects`: a body step
`c.i++` of an existing cursor is outside `keep`). Lean (proved,
`ReadOnlyTraceCert.lean`): the structure is `TraceCert`, with
`Entering` and `OwnAfter` as above; its member is `traceMember`, whose call
is a `MemberRun.Own` run whose own steps are within $`\Psi`$ below the
entry's heap and keep each invariant of $`G`$ (`ownQ`), bounded by
`MemberRun.within` and keeping invariants by `RunSeq.keeps`; and
`decompose_trace` is `decompose` over trace certificates, the entering
step prepended, each own step's property read from the certificate of the
code its call entered at the call's entry (`exec_bound_trace`,
`callRun_trace`). Certificates are at $`\Psi_j`$. Well-formedness alone
does not bound an entering step: a step of outside code that evaluates a
write just before a run of $`C`$ not yet entered, at a pending position,
changes the heap and enters the call (`enterWrite_step`, counter-model,
`ReadOnlyTransfer.lean`), and neither $`\Theta_C`$ (read at steps of kind
`outside`) nor $`C`$'s checks bound it. The reached states meet a
stronger invariant (`wfS`, `ReadOnlyPending.lean`): along the evaluation
path every other position is free of runs, but a binding's body, which
may be a run not yet entered when its head is a value, a throw of a value
or a literal of values (the rest binding of `graphEntry`). Every step
keeps it, and a step that changes the heap changes only the innermost
entry of the path, at its tag (`step_wfS`, proved); it holds at the
frame's starts, the request's run (`FramedSpec.wfS_start`, proved), so at
every reached state (`ClientFrame.reached_wfS`, proved).

`cert_of_charges` (proved, `ReadOnlyMemberCert.lean`) gives the
certificate of every code at $`\Psi_j=\Psi_C`$ (`componentProtocol`) and
$`G=\emptyset`$. An entering step keeps the heap (`enter_keeps_heap`), so
`enterWithin` holds at every protocol; it pushes a run of $`C`$'s code
in an evaluation context whose frames hold the calls active before it,
its top segment outside $`C`$ (`enter_ctx`). While the call is active the
state is that context around a run its hole reached (`hole_ex`: a
context steps only where its hole steps or throws, `EvalCtx.step_hole`,
and a value or a throw at the hole holds the context's calls,
`ctx_val_tags`), and at one call more than the context a step of $`C`$'s
code has every frame of the run on $`C`$'s code (`hole_runsC`), so `own`
follows from `within_member` at the entered run, its base heap the entry's.
Its premises besides the reached-state invariants: the closure check of
the capture sites and $`O`$, and `hroots`, the values of each run an
entering step pushes meeting that closure in depth (`cert_of_deep`;
`cert_of_charges` reads them as values meeting sets within it).

`hroots` holds where no code of $`C`$ collects a rest
([restrictions](#restrictions); `ClientFrame.entry_roots`, proved,
`ReadOnlyEnterRoots.lean`). The term before the step is the context of the
pushed run around a term stepping to it (`step_hole_inv`: the positions off
the evaluation path are free of runs). That term is a call of graph code, a
binding whose body is the run, or a frame of the run's code. A frame's step
to its code's next node keeps the calls of $`C`$ active (`depthC_ctx`). A
binding's body that is a run not yet entered runs outside code
(`noPend_reached`): such a run is a graph call's rest binding, of a closure
collecting a rest, and every closure of $`C`$'s code has its code's layout
(`layQ_noRest`). So the step is a call of a closure of $`C`$'s code from a
position of outside code (`depth_push`, `fits_ctx`); the call's fit gives
its callee, receiver and actuals sets within $`O`$, and the run's values
are theirs and the values its callee holds (`deep_entry`), within the
closure in depth (`deepIn_of_checks`).

## Re-entry

A callback re-entering $`C`$ creates calls of $`C`$ deeper than the
claim's main frame. The claim reads of such a call its effect on $`R_C`$
(the certificate, from $`\mathrm{Ch}`$, no fact), its progress (the
callback's arrow, part of $`\Theta_C`$, [callers and
callbacks](#callers-and-callbacks)), and none of its facts: the clauses
read assertions at states whose whole term runs the claim's graph
(`AssertedAt`) and posts at the claim's exit. A re-entry records its
arguments' incoming crossing ([the history](#the-history-of-a-program)),
which only adds to the protection; no fact of the re-entered call reads a
witness, so the claim needs witnesses only at its main frame.

## The guarantee route

Milestone 4. The return premise holds the kept invariants
($`I_{\mathit{root}}(\rho,h_0)\Rightarrow I_{\mathit{root}}(\rho,h_1)`$,
[the graph at framed returns](#the-graph-at-framed-returns)), discharged by
`framed_guarantee` (to be proved) with `SupportAt.outside` and
`invIn_of_installs` (proved), over path facts (`pathSupportB`; stable under
allocation, `pathFact_alloc`), (O) covering protected released storage
(`protectedInto_released`; `released_prot_inR`), the invariant at the
entry from `invariant-requires` (`invariant_of_entry`), and `hnew` by
`supp_split`.

**Open for milestone 4: a store checked at one root** (Astra 4, Fable F1).
Each store into a candidate's possible support is checked to keep the
invariant at the root it writes (`storeKeepsInv`, renamed from
`writeKeeps`, which names another function at the base). A store keeping
$`I`$ at its root breaks it at another root whose support holds the written
location: `shared-support.mjs` (`NaN`: `view` shares `xs` between two
handles, `truncate(b)` keeps $`I(b)`$ and breaks $`I(a)`$) and Astra's
`install(a)` writing a counter `b` shares. The fix this design takes for
milestone 4: **disjoint supports**, a check of (O) refusing a store that
makes a location of a candidate's support reachable from a second root of
its handle's sites (by sites, `supportShareB`), with the invariant
`SupportDisjoint` (each support location on the support of one root) kept
by the checked stores; then a store's check at its written root is its
check at every root whose support it may change. `view` in
`shared-support.mjs` is refused. A store's check quantifying over every
root by sites is the alternative where sharing is wanted. Neither is
needed by milestone 1.

## The history of a program

`chk` gives, at each step of $`C`$'s code, the sites of what it allocates
(the canonical sites, [the binding checks](#the-binding-checks)), the key
`none`, and its crossings: the actual crossings out (`actualXs` at the
type $`\top_{w}`$, a writable type, so an outgoing crossing reaches nothing
read-only and adds nothing to $`E`$), and, **at an entering step**, the
arguments of the call the step reduces (the active redex, `invoke` or
`construct`, in a frame of outside code), the first of them as many as the
function's parameters, crossing in at the entered code's parameter types
(`FramedSpec.entryXs`). No code of $`C`$ collects a rest
([restrictions](#restrictions)), so each such argument is the value of its
parameter.

- **The types of a shared code** (`sharedParamTypes`): the entered code is
  its tables (`entered`), which two functions of $`C`$ may share with
  different declared types (`EnteredTables.lean`). A parameter's crossing
  type is the meet of the declared types of every function of $`C`$ whose
  realized code is the entered code: read-only at a position only where
  every one declares it read-only, by position
  ([the crossings an entering step records](#the-crossings-an-entering-step-records),
  piece 0 of milestone 2).
- **The subset milestone 1 implements.** The note counts a callback's
  result and a caught value as incoming crossings too. Milestone 1 records
  the entering step's alone: with fewer recorded crossings fewer locations
  are protected, so the obligation is weaker and the claim about more
  executions; milestone 2 reads protection from the entering step's
  crossings alone. Milestone 4 records the others at their declared types.
- **The checks at the new crossings** (`ReadOnlyIncoming.lean`, proved).
  The base's `chkSound_of_sites`, `chkSound_of_escape` and
  `chkSound_of_flow` read `ActualCrossings T`, every crossing `.outOf`
  (`IncomingCrossings.lean`: `not_actualCrossings_of_into`). Their
  restatements `chkSound_of_escapeIn`, `chkSound_of_sitesIn` and
  `chkSound_of_flowIn` read `ActualCrossingsIn T inc`: the crossings
  `inc ++ actualXs`, which the framed frame meets with `inc` its entering
  step's crossings (`FramedSpec.actualCrossingsIn`, each `.into`,
  `FramedSpec.entryXs_into`). `gives` and `stores` keep their proofs, which
  read the outgoing part (`pkgProps_actualIn`). `PkgProps.crossOk` at an
  incoming crossing is `crossOk_incoming`: its value is a root of outside
  code at the state before the step, which meets $`O`$ there
  (`sitesAt_reached`, from `fitsAt_reached` and `fits_roots`); the step's
  allocation keeps the site of every location the value reaches; so by
  `crossOk_of_sites` it reaches no local, internal or exposed location. A
  value holding no location crosses alike (`crossOk_noLeaves`). The premise
  `IncomingRoots` (each incoming value a root of outside code before its
  step, or a value holding no location) is, for the framed frame,
  `entryXs_roots` (proved, `FramedHistory.lean`). A root is an object, a
  spine or a view spine (`vals_located`, proved), so an entering step whose
  argument is a number crosses a value that is no root (`num_not_root`,
  proved): the premise reads such a value by its holding no location. Each
  crossing is an argument of the active redex in a frame of outside code:
  an object, a spine or a view spine there is a value at a position of
  outside code of the term (`active_vals`, `redex_arg_root`,
  `ReadOnlyLocalReach.lean`), any other value reaches no location.
- **`Inv` after an incoming crossing** is `pkg_step_inv` (proved) at the
  history's crossings, which reads every crossing alike: a crossing changes
  no site or key (`crosses_site`), steps the history by `HStep.cross`
  (`crosses_hsteps`) and adds to $`E`$ only exposed locations
  (`crosses_covers`).

Observed (`Round4.lean`): `cross_into_prot`; at the base (`NoProt.lean`)
with `.outOf` crossings alone nothing is protected.

## Initialization

The base realizes a module function as a closure term whose linked slots
hold the other functions' closures one unfolding less, `null` at depth
$`0`$, and whose outside slots hold a value per depth (`approxEnv`,
`Slot.outside`, `PassUnitRealize.lean`; `ModuleClosures.lean`). An outside
slot varying with the depth makes every unfolding different
(`ApproxStable.lean`). Under the restriction that every outside slot holds
an audited realm value, the same value at every depth, and with an acyclic
name graph ranked by a height (`StableLayout`: each linked slot names a
function of smaller height), a function's closure is the same at every
depth from its height on (proved, `PassUnit.approx_stable`); a function
with no linked slot has height `0`, one unfolding at every depth.

**The initialization** of $`C`$: `initC`, a code of $`C`$ (tagged
$`c_C`$) whose node expression allocates, in reverse topological order of
the name graph, each module function's closure at its stable unfolding
(`makeAt (.graph …)`, its linked captures the closures already allocated,
its outside captures the slots holding the realm's identities), and returns the array of the exported
ones. Its order names each module function once, by name (`initOrder`):
two module functions of one code are two closures of that code. Its
allocations are at canonical sites.

**An initial configuration** of a program over $`C`$: the realm's heap
$`h_R`$, holding the intrinsic objects the outside slots of $`C`$'s module
functions name (`Array.prototype`), a world at which it is typed, and the
closed term
`letE (gotoOf initC 0 Lr .undef c_C) client`, `Lr` the realm's
identities ([the initialization in the flow](#the-initialization-in-the-flow)), whose `client` is lowered
source of outside code (`LoweredSrc`, holding no closure,
`loweredSrc_no_closure`) scoped at one binder (`Scoped 1 client`, its
variable `0` the exports' array; the whole `letE` is `Scoped 0`).

**The scope of the claim** (a stated limit; proved of the definition,
`FramedSpec.Initial`, `initial_lowered`): the realm's heap holds one
location per realm value $`C`$'s module functions read (`componentInit`:
for P22, `%ElementAt%` and `[[Array.prototype]]`, an object with no
field), and the client holds no located value (`LoweredSrc`) and reads
one variable, the exports. So a program the framed claim is about reaches
the exports, what its client allocates, and the calculus's operations
(element reads and writes, lengths, arithmetic, literals, calls of the
exports' and its own closures). A client calling a native (`xs.push`,
`Math.max`, a `Map`, any method of a realm object) runs no program the
claim is about: covering it takes an initial heap holding the whole
audited realm, each native with its step model or contract, bound for the
client.

**P22's layout** (measured, `layout.py` on P22's `fragment.json`, and the
module code the flow probe reads): one function, `walk`; no module
initialization statement (`init: []`); no imported module; two outside
slots, the intrinsic `%ElementAt%` the read `xs[c.i]!` lowers to, an
audited native with a step model, and `[[Array.prototype]]`, the realm's
array prototype every unit that uses arrays sees (`Elaboration.lean`), an
intrinsic object of $`h_R`$. `walk` names no function of its module. So
P22 meets the restriction and its `initC` allocates one closure.

### The initialization in the flow

**Both premises on the initial configurations read the initialization's
code at the flow** (proved, `FramedStarts.lean`). An initial
configuration's term runs `initC` at $`c_C`$, a tag of $`C`$
(`init_ofC`). Code provenance at an entry (`InitialEntry`) holds only
where `initC` is a code the flow proposes for (`initialEntry_code`), and
the fit (`InitialFits`) only where the flow has a proposal for it, the
rule `gotoC` being the only rule fitting a run of $`C`$'s code
(`initialFits_code`).

**A closure whose code names a signature at a capture** is created by no
lowered code (proved, `capSig_not_lowered`): `Lowered`'s clause for a
closure of $`C`$'s code requires `SelfFn` at every context of the created
code, only the closure's own slot naming a signature at its entry. P22's
`walk` is such a code (measured): its entry names `%ElementAt%`'s
signature at its capture slot `4`, the seed `componentCodes` gives a
module function's sibling slot of a native (`sibSig`), by which its read
`xs[c.i]!` is a known call (`Fits.invokeC`). So `initC` is no lowered
code, and the flow's checks read of its codes what their consumers need,
the two rules below. `Fits.makeGraphC` reads `CapFn` at the instantiated
captures, which a capture holding a closure of the named signature meets.

**The design.** The initialization is a code of $`C`$ the flow proposes
for, reading the realm's values from its slots, and two rules read what
their consumers need:

- **The initial configuration** is
  `letE (.goto initE initK 0 Lr .undef c_C) client`, `Lr` the realm's
  identities in `componentInit`'s order (`FramedSpec.initL`, the
  identity `j` the realm's object at its location `j`, `realmValueAt`).
  `initE`'s captures of realm values are the variables of the slots
  holding them (at node `k`, the slot `k + j` of the realm value `j`, past
  the `k` closures bound before it); `initB` checks them so (a capture
  naming no module function a slot of an identity, `k ≤ v < k + |Lr|`;
  `Lr`'s length the realm's, its identity `j` at location `j`).
- **The flow proposes for `initC`** (`componentCodes`'s `init`: one more
  code of $`C`$, a unit entered at `entryCx` at its node `0` with no
  closure of its own, each slot holding a realm value seeded with that
  value's signature where it is a native's closure, as a module
  function's sibling slots are; its returns reach $`O`$, as a unit's do).
  `FFlow.check`, `codesCoverB` and `marksB` then cover it.
- **The open fit of a closure creation reads the creating node's
  signatures** (`OFits.makeGraphC`, decided by `graphSites` with
  `ocapFnB`, proved `ocapFnB_sound`): `CapFn` read on the open term
  (`OCapFn`): each slot naming a signature at the created code's entry,
  at every context, is the closure's own slot, or the slot of a capture
  that is a slot of the node naming the same signature ($`\varphi`$).
  Instantiation keeps it (`OCapFn.inst`, in `ofits_sound`: the
  instantiated capture is the environment's value at that slot, a closure
  of the signature by `EnvFn`), giving `Fits.makeGraphC`'s `CapFn`.
  `SelfFn` is the case of no capture naming a signature
  (`SelfFn.ocapFn`).
- **The flow's codes hold no located value** (`CodesLowered`, as its one
  consumer reads it, `goodIn_vals_vj`: the values of each node expression
  of a code the flow proposes for are spines with no cell, as lowered
  code's are, `lowered_vals_all`), decided by `codesLoweredB` over that
  property (`codesLoweredB_sound`). `Lowered` is the condition on outside
  code (`LoweredSrc.lowered`) and on the code of a closure a term creates
  (`Fits.makeGraphC`), which `walk`'s code meets.
- **The checks `frameFlowB` adds** (`initFlowB`, `realmSlotB`,
  controls in `Tests/FramedBindingControls.lean`), the premises of the
  two rules the initial term fits by: `initC`'s proposal at `entryCx`,
  its return set within $`O`$ (the exports' array reaches the client); at
  each slot of the entry the realm identity it holds meeting the slot's
  set (an identity is an object with no field, which holds no location;
  for a native's closure, with no capture and its code holding no value,
  its token in the set, the native's proposal at `entryCx`, open where its
  token lies in $`O`$, only its own slot naming a signature at its entry,
  and the slot naming none or its signature, `EnvFn`; no slot past `Lr`
  naming one); every code `initE` and `Lr` hold at a tag of $`C`$ a code
  of the flow and every such code carrying a tag of $`C`$ (provenance and
  outside source); each value of the realm's heap a primitive
  (`primVal`); and each identity meeting layout provenance, the residual
  invariant and free of runs.
- **What they give** (proved, `FramedInitial.lean`). `InitialFits`
  (`FramedSpec.initialFits`): the `letE` by `Fits.letE` at the set
  $`O`$, the run by `gotoC` at `initC`'s proposal (its slots by the checks
  above, the default `undefined` a primitive), the client by
  `fits_lowered` (`LoweredSrc.lowered`, its variable `0` bound to
  $`O`$), the realm's heap by `VJ.prim`. `InitialEntry`
  (`FramedSpec.initialEntry`): provenance
  (`initC` and the natives' codes are flow codes; the client creates only
  closures of outside code, `LoweredSrc`), the discipline (`wf` of the
  term, the realm's heap free of runs, primitives), outside code lowered
  source (the client; no value of the realm is code) and closed values
  (`Lr` closed, `Scoped 1 client`, primitives).

**A linked capture fits at the creation's value** (proved, the rule
`Fits.frameC`'s value clause at `FnTm`, and `CodeChk`'s): a module
function's capture slot of another module function names that
function's signature (`sibSig`, by which its call is a known call), and
the initialization's slot binding that function's closure names it too,
as the value of a node creating a closure of $`C`$'s code names the
signature of the code it creates (`vfnB`, `creationIx`). So `initC`'s
creation of a closure capturing another module function's closure meets
its open fit (`OCapFn`). Module functions naming each other in a cycle
are refused at their gate ([Restrictions](#restrictions)): `initC`
creates each closure after those it names.

**At P22** (measured): the component's checks pass, `initC` among the
flow's codes, `initFlowB` among them; `initC`'s proposal returns within
$`O`$; its slot `0` (`[[Array.prototype]]`) holds outside storage, its
slot `1` names `%ElementAt%`'s signature and holds the native's token,
which lies outside $`O`$. The restrictions hold.

## The frame of a request

### The frame's core

```lean
/-- What the obligation, the history and the steps read: the family, the
component, the type view, the client obligation and the checks' data. -/
structure FrameCore (τ : Type) where
  fam : NumberedFamily
  C : Nat
  view : ViewOver τ
  Θ : Protocol (fam.family.at C)
  chk : Heap → Tm → Heap → Tm → CheckData (fam.family.at C) view.view
```

`KStep`, `next` and `Keeps` read a `FrameCore`; `ClientFrame` extends it
with `codes`, `start` and `enters`, so `PublicCall` is defined over the
core before the frame.

### Realization

A unit's **realization** relates the code an entering step enters to the
request: `RealizeSim r` (new), a simulation between configurations running
the entered code and configurations running `gotoOf r.program …`, relating
states with the same heap and world and histories equal but for the depth
of $`A`$ (the same sites, keys, $`E`$, $`B`$ and protected set), frames at
the same labels with environments related by the realization's slot map,
and keeping the step kinds, roots and crossings. For a receiverless module
function the entered code is the request's tables extended by the
prologue (`PassUnit.dropReceiver`; `Step.frameEffect` carries both tables
into the body), and `prologue_sim` (proved, `FramedRealize.lean`) relates
a state of the extended tables at a body label $`l<|\mathrm{r.program}|`$
to the request's state at $`l`$: the prologue's node is past the body, no
body node's target reaches it (`bodyTargetsB`, decided), so the two codes
agree on the body (`BodyAgree`, `realized_agree`) and each body step in the
extended tables is the same step in the request's, on the same heap, to
related terms (`TabRel`: a run at a body label, a frame at a body node with
the same running term, or the same term; `tabRel_step`, `tabRel_steps`,
`ReadOnlyRealize.lean`), and where one takes no step the other takes none
(`tabRel_stuck`); the prologue's own two steps (`prologue_steps`: its node
evaluates `undefined`, its continuation maps the slots past the receiver)
reach the realized code's run at the request's start, related to the
request's.

**One site per body allocation.** Allocation sites are keyed by the body:
`bodyOf m` is the request's tables for a realized code (the first
$`|\mathrm{r.program}|`$ entries of its tables, `Round5.lean`, `body_prefix`)
and `m` for any other code; the canonical numbering of an allocation
occurrence is that of `(bodyOf m, continuation and handler, kind)` (`canonSite`).
So the same body allocation, P22's `const c = { i: 0 }` among them, has one
site in both codes, and `chk_sim` states that `chk` gives related steps
the same allocation sites, keys and crossings: in any context, related
runs allocate at the same site (`chk_site_sim`, from `stepSite_tabRel` and
`allocB_realized`), keys are `none` in both, and a step of related runs
crosses out the same values (`chk_actual_sim`: related runs hold the same
values, `vals_tabRel`, `vals_ctx`, `actualXs_congr`), and an entering
step's crossings in agree (`chk_entry_sim`): `entryXs` reads the active
frame's tag and redex and the calls of $`C`$ active, which depend only on
the tags of the paths in the context (`path_ctx`, `depthC_ctx`), the same
for related runs (`tabRel_tags`); the code entered differs only where the
realized code's frame continues at its own node, a step keeping the calls
active (`frame_goto_tags`), so an entering step on neither side. Together
`chk_sim` (proved, `FramedRealize.lean`): in any context, related steps have
the same checks' data. The flow holds both codes
(`codesCoverB`), its proposals for the realized code at body labels equal
to the request's (`realizedFlowB`, decided), so `Fits`, `Provenance` and
the frame check read the same proposal in either code; re-entered calls of
the function run the realized code inside the isolated execution at the
same sites.

**`RealizedAt r a₁ a₂ L d`** (new): `a₁` runs the realized code from its
`graphEntry` state, the execution from `a₁` to `a₂` consists of the
prologue's steps, and `a₂`'s innermost run is the realized code at
`r.start` with slots `L` and default `d`, related by `prologue_sim` to
`gotoOf r.program r.start L d r.comp`. Other kinds of unit (a method, a
function a binding holds) have no realization here: a restriction.

### The calls the claim is about

**A public call** (`PublicCall core r x₀ n x a₁`, new, over a
`FrameCore`): `x₀` is an initial configuration; `Ex core.KStep (fun _ =>
True) n (x₀, bareStart) x` is an execution of actual steps (`AStep`: each
configuration's world admissible, its heap typed, the world `Keeps` reads)
each keeping $`\Theta_C`$ at the threaded history; and `x → a₁` is an
entering step (`Entering`: the active frame of `x` outside $`C`$, `a₁`
running the code of $`r`$'s realization, one more call of $`C`$ active).
The entering step records the arguments' incoming crossing.

**The claim's entry** is the state of the realization after the
prologue: `a₂`, related by `RealizeSim r` to `(⟨n₂, W₂, h₂⟩, gotoOf
r.program r.start L d r.comp)`, the history $`g_2`$ the program's at `a₂`.
**Isolation** (`isolate`, proved, `ReadOnlyIsolate.lean`): from `a₂` to
the call's return the execution is `K[t]` with `K` the client's context,
every step a step of `t` in `K`, until `t` takes no step (a value or a
throw). A term whose innermost run is a run not yet entered is that run in
an evaluation context (`innermostGoto_ctx`; `EvalCtx`,
`Semantics/EvalContexts.lean`: a congruence position of a step rule, its
earlier positions values, nested, a frame's running term among them); a
step of the hole is a step of the context (`EvalCtx.step`), and by
determinism an execution from `K[t]` is an execution of `t` in `K` or
reaches a `K[t₁]` whose `t₁` takes no step (`EvalCtx.steps_inv`).

```lean
def FramedSpec.frame (spec : FramedSpec ι) (r : SourceRequest σ ι) : ClientFrame (Ty ι) where
  toFrameCore := spec.core r
  enters k W h t := ∃ x₀ n x a₁ a₂ L d, PublicCall (spec.core r) r x₀ n x a₁ ∧
    RealizedAt r a₁ a₂ L d ∧ a₂.1.s.n = k ∧ a₂.1.s.W ≍ W ∧ h = a₂.1.s.h ∧
    t = gotoOf r.program r.start L d r.comp
  start k W h t g :=
    (∃ x₀ n x a₁ a₂ L d, PublicCall (spec.core r) r x₀ n x a₁ ∧ RealizedAt r a₁ a₂ L d ∧
      a₂.1.s.n = k ∧ a₂.1.s.W ≍ W ∧ h = a₂.1.s.h ∧ t = gotoOf r.program r.start L d r.comp ∧
      g = { a₂.2 with A := [a₂.2.Prot] }) ∨
    ((¬ ∃ x₀ n x a₁ a₂ L d, PublicCall (spec.core r) r x₀ n x a₁ ∧ RealizedAt r a₁ a₂ L d ∧
        a₂.1.s.n = k ∧ a₂.1.s.W ≍ W ∧ h = a₂.1.s.h ∧ t = gotoOf r.program r.start L d r.comp) ∧
      g = bareStart (spec.core r).F (spec.core r).C t)
```

`enters` reads the world: `ClientFrame.enters` takes `k` and `W`, and the
six clauses pass the world they quantify, so each clause is read at the
program's world at the entry (Fable F7). The start is the program's
history at the entry truncated to its one set, with no second crossing:
the crossing was recorded at the entering step. It holds one set, the one
call of $`C`$ the isolated `goto` holds (`startFix_startInv_len`), and the
same protection (`truncate_prot`, `truncate_after_cross`). The start is
total.

- **The projection** (`project`, to be proved): along the isolated
  execution, the isolated history and the program's history protect the
  same locations, have the same sites, keys and exposed set, and differ in
  depth by the calls of $`C`$ active below the entry: each history step
  acts alike on every set of a uniform history (`HStep.uniform`, proved),
  and the isolated execution ends before the call's own exit pops. So
  `Keeps` at each isolated step is `Keeps` at the program's step, at the
  same world: the isolated executions keeping $`\Theta_C`$ are the
  program's. `NoProt.lean`'s `project_false` was about a program history
  without the entry crossing.
- **The obligation reads no proposal** (`keeps_canonical`, to be proved):
  $`\Theta_C`$ is a change per kind (the restriction on `@clients`); the
  marks a flow gives expose no site and a local location is reached by no
  outside root (`MarksOk`), and an outside step changes only locations its
  roots reach (`step_reach`, proved), so `Keeps` is "every changed
  location the history protects changes within $`\Theta_C`$ at its kind";
  the protected set is built from the entries' arguments at their
  declared types and from `Held`, which reads whether a location's site is
  `some`, which the canonical allocation sites decide from the lowering.
- **The flow along a program** (proved, `FramedStarts.lean`): the
  program's frame (`progFrame`, the plan's core and codes, its calls the
  initial configurations, its start the history before any entry) reaches
  the program's states, so `fitsAt_reached`, `chkSound_of_sitesIn` and
  `reached_ok` read them: every state fits $`O`$ at a position of outside
  code and its heap meets the flow (`progOk_ex`, from initial
  configurations fitting it, `InitialFits`), (S), (K) and (O) hold at
  every step of $`C`$'s code, the initialization's and earlier calls'
  included (`progFrame_chkSound`), and every state meets the invariants of
  states (`reached_ok` at `progFrame`, from initial configurations that
  are entries, `InitialEntry`). Then the frame's entries fit
  (`entryFits`, its slots those `graphEntry` and the prologue fill, at the
  realized code's proposal, the request's at its body labels), its starts
  meet the invariants of states (`startInv`), and `ChkSound` holds for the
  frame (`chkSound`).
- **An inhabitant.** Milestone 1's first check builds one public call of
  P22's `walk` from an initial configuration of a client program.

**The headline's reading** of "keeping $`\Theta_C`$": each step of outside
code, from the program's start through the call, changes the locations the
program's history protects within $`\Theta_C`$, the history protecting what
each active entry's arguments reach read-only at their declared types, and
what $`C`$ holds of them after an outermost return (`B`).

**Coverage, from each actual invocation** (`publicCall_safe`, to be
proved): for every program from an initial configuration and every state
`x` of its execution, along steps keeping $`\Theta_C`$, at which outside
code invokes the closure of $`r`$'s function with values `L₀`, `d₀`
meeting the request's entry contracts at `x`'s world, the program's
execution from `x` until the call returns or throws is safe (each state a
value, a throw, or a step at an admissible world with a typed heap, the
call's context `K` waiting), along each continuation keeping
$`\Theta_C`$, and the call's footprint, postcondition and regional clauses
hold between `x`'s heap and the return's. Plan: the invocation's steps up
to the entering step (a rest spine's `letE` among them) are steps of
outside code in `K`, safe by the closure's realization; the entering step
`x → a₁` makes `PublicCall` hold by its definition; the prologue's steps
are safe and reach `a₂` (`prologue_sim`); `RealizedAt r a₁ a₂ L d` and the
execution give `enters` at `a₂`'s world and `start` at the program's
history truncated; `FramedRequestSafe r (spec.frame r)` gives the isolated
clauses; `isolate` and `RealizeSim` carry each to the program's execution
in `K`. The entry contracts at `a₂` are the invocation's at `L₀`, `d₀`
through `graphEntry`'s slot map (`entryHolds_realized`, to be proved, as
the module realization's `approx_envOk` does for an ordinary row). This is
the direction the headline promises: every actual public call is covered.

**`PublicCall` with `KStep` and the depth**: its execution is of
`core.KStep` (actual steps, the history `next`, `Keeps`), and its entering
step is a `KStep` raising $`\delta`$ by one; `PkgProps` at that step is
`progFrame_chkSound`'s conclusion, never a premise of the definition.

### The binding checks

Decided by the verifier from the request, the fragment's components and
the lowered code, each with a forged-fragment control. The checks over a
finite flow are `ReadOnlyBinding.lean` and `FramedBinding.lean`, each with
its soundness lemma (proved) and its forged flows refused in
`Tests/FramedBindingControls.lean`; the forged fragments through the
pipeline come with the producer's framed plans.

- **codes** (`codesCoverB`, `codesCoverB_sound`): the flow holds, at its
  entry context, a proposal for each code of $`C`$ by content (module
functions of one code, arity and number of captures are one code of the
flow, with one proposal, one site per body allocation and one closure
token, `componentCodes`): each module
  function's realized code (the prologue's extension included) and its
  request's code (`requestCode`, the tables the claim's term runs), its
  closures' codes, the codes of its requests' codes, and `initC`. The
  frame's `codes` are these. A frame of a code with no proposal allocates
  at outside storage (`allocOf`).
- **allocation sites** (`allocB`): each allocation occurrence of a code of
  $`C`$ has the canonical site of `(bodyOf m, continuation and handler,
  kind)`, a `some` site, and the flow's allocation tables equal
  that numbering. Its first half is `allocSomeB` (`allocSomeB_sound`: every
  proposal allocates at `some` sites at every node key, so a step of a
  covered code of $`C`$ allocates at a `some` site, `stepSite_some`;
  `Round4.lean`: false on `AstraR3.lean`'s flow, which `FFlow.check`,
  `marksB` and `entryB` pass); its second half is `allocCanonB`
  (`allocCanonB_sound`, `ReadOnlyBinding.lean`): the canonical site of an
  occurrence is, from a base, two numbers per element of the bodies'
  occurrences (`allocOccs`, each body with each of its node keys, in
  order), the object's then the array's (`canonSite`, injective on the
  occurrences, `canonSite_inj`), and the flow's sites number so at every
  node key of a code that its body has. `allocB` (`FramedBinding.lean`)
  is both, at the body `bodyOf r` (the request's code for the realized
  code, every other code itself); `allocB_realized` gives the realized
  code and its request's the same allocation sites at every node key of
  the request's program.
  `realizedFlowB` (`realizedFlowB_sound`,
  by `agreeB_sound`) makes a realized code's proposals at body labels the
  request's: at every context of the realized code, the request's code
  has a proposal with the same slots, value sets, signatures and outside
  calls at each body label, the same allocation sites at each body node's
  continuation and handler, and the same return set.
- **the component** (`compB`, `compB_sound`, `FramedBinding.lean`): the
  request's tag, which the lowering assigns (`componentAt` at its name), is
  $`C`$, so the claim's frames run $`C`$'s code; the family's nesting is
  the fragment's components', read by the producer.
- **the entry** (`entryB`, `entryFnB`, `entryFnB_sound`): at the realized
  code's entry, its slots naming signatures only at the sibling slots and
  the closure's own slot.
- **the inputs**: `paramTypes`, computed from the requests.
- **the body's targets** (`bodyTargetsB`, `bodyTargetsB_sound`,
  `FramedRealize.lean`): every continuation and handler of the request's
  program targets one of its labels, and its start is one, so the
  realized code and the request's agree on the body (`realized_agree`).
- **codes holding no located value, and layouts** (`codesLoweredB`,
  `tokensSomeB`, `ReadOnlyLayouts.lean`): every node expression of a code
  of the flow holds no located value, every context has a `some` token,
  and every closure of $`C`$'s code the initialization's and the flow's
  node expressions and the realm's identities create or are has its
  code's layout `lay` (`layP (layQ F lay)`).
- **$`\Theta_C`$** (`clientsB`, `clientsB_sound`, `FramedBinding.lean`):
  the rows of $`C`$'s exported types state class keys only
  (`clientsByKindB`), and the plan's $`\Theta_C`$ by kind is, at every
  kind, the join of the stated rows' changes at that kind (`rowsAt`), read
  from the declaration document; so the frame's $`\Theta_C`$ is the rows'
  at every part (`FramedSpec.theta_rows`).
- **the read-only types** (`readOnlyB`, `FramedSpec.readOnly_declared`):
  every type the frame's view reads read-only is an input of the member
  whose parameter's declared shape is read-only throughout.
- **the framed nodes** (`FramedSpec.framed_nodes`): the plan's framed
  nodes are the realized code's framed call nodes in the flow
  (`framedCallNodes`).
- **the protocol** (`protocolAtLeastB`, `protocolAtLeastB_sound`,
  `ReadOnlyBinding.lean`): the wire's $`\Psi_C`$ at least $`\Psi_C`$ as
  defined, at every part of $`U`$ at the key `none` (`partsU`).
- **the restrictions** below.

### The plan

```lean
inductive FunctionPlan (σ ι : Type) [Labels ι] [StoreView σ ι] where
  | graph (name : String) (namePos : Span) (request : SourceRequest σ ι)
  | framed (name : String) (namePos : Span) (request : SourceRequest σ ι) (spec : FramedSpec ι)

def FunctionPlan.certify : FunctionPlan σ ι → Except String (CertifiedPlan σ ι)
  | .graph name pos request => pure (.graph name pos request)
  | .framed name pos request spec => pure (.framed name pos request spec)
```

`CertifiedPlan.framed` carries the proposals, and `MemberSafe` reads a
framed plan's claim at the frame they define, `FramedRequestSafe r
(spec.frame r)`: the frame holds the checks' data, which reads the
crossings of a step classically, so the executable boundary carries the
proposals and the claim the frame (`Plans.lean`).

`FramedSpec ι` (`FramedSpec.lean`) holds the proposals: $`C`$, the types
a crossing reads read-only (the member's inputs whose declared shapes are
read-only throughout, `readOnlyInputs`), the type outgoing values cross
at, the realm's heap, the initialization's code and its order (`initOrder`,
the module functions by name) and the function's arity;
and what the check reads: the component's tags, the marks of its flow's
sites (`O`), the flow the solver proposes at those marks (`checked`, each
module function's request code beside its realized code), each code's
layout, the natives' codes, the component family the declaration document
describes and the checked file's functions, the component's module
functions' codes, names, arities and slot names, its entries, the wire's
$`\Theta_C`$ by kind (`theta`) and $`\Psi_C`$ by numbered site and kind
(`psi`), $`\Psi_C`$ as defined at the flow's sites (`psiDef`), the
refusal of the checks that read the component alone with the evaluation
it is (`componentRefusal`), and each framed call node of the main graph with
the supports its frame keeps. The family is the numbered family of the one
component $`C`$, each site marked by the flow (`oneComponent`);
$`\Theta_C`$ is the wire's change per kind (`protocolOfKinds`); the finite
flow (`fflow`, which the binding checks decide; `flow` is the flow it
stands for) is `checked` with its sites renamed into the family's (`FFlow.mapSites`). From them and the request:

- `realizedCode r`: the request's node lists behind the receiver's
  prologue (`dropReceiver`'s lists over $`|\mathrm{r.inputs}|`$ slots);
- `view`: a type is read-only where the proposals name it, and a type's
  children are itself, so a read-only type is read-only throughout
  (`ro_of_readOnlyShape` checks the names against the declared shape);
- `chk r`: the flow's site of a step's fresh locations (`stepSite`), no
  keys, and the crossings: at an entering step of the realized code its
  first `arity` arguments into $`C`$ at their declared types (`entryXs`),
  and every value reaching outside code out of $`C`$ (`actualXs`);
- `Initial x₀`: the realm's heap, and `letE (goto initE initK 0 [] undefined C) client`
  with `client` lowered outside source whose one free variable is the
  exports;
- `RealizedAt r a₁ a₂ L d`: `a₁`'s innermost run is the realized code at
  the prologue's label, and `a₂` is the first state after it, along steps
  keeping $`\Theta_C`$, whose innermost run is the realized code at
  `r.start`, with slots `L`, default `d` and the request's tag. The label
  makes the realization the prologue's two steps (`prologue_det`): a run
  of the realized code entered at a body label could reach its start
  inside a frame of $`C`$'s code, where the fit bounds its returns by a
  set of $`C`$'s, not by $`O`$; `publicCall_safe` reads that every closure
  of the realized code enters at the prologue's label;
- `frame r`: its core `(fam, C, view, Θ_C, chk r)`, its codes those the
  flow holds, its entries `EntryAt`, the realizations of the public calls
  of the realized code (`FrameCore.PublicCall`, `ReadOnlyPublic.lean`) at
  the program's world and heap, its term `gotoOf r.program r.start L d
  r.comp`, and its start as stated above (total, by cases).

`MemberAccepted.framed` holds a framed plan at the member
(`FramedPlanAt`) and `FramedAccepted f r spec`: its code requests accepted
in order by the ordinary pass (`CodesAccepted`, ordinary checker, from the
empty table), the read summaries their runs leave checked
(`summariesChecked`), each stated region meeting its entry conditions, its
main graph over the codes' table accepted by the pass's framed mode at its
bound and stated regions (`RunCall.AcceptsFramed` at the framed nodes `F`
keeping the supports `S`), its read summaries checked, and the checks at
its request; the returns `framedRet S` hold at the executions the claim
is about (`FramedReturnsReachedW`, `framedReturns_reached`, from the
checks). `framedReturns_of_main` gives `FramedReturnsGuarantee` from the
framed run by `RunSoundFramed` (`run_sound_framed`), and
`framedRun_of_returnsW` the main graph's five clauses of
`FramedRequestSafe r (spec.frame r)`. `framed_requestSafe` (under `RunSound`,
`RunKeepsSummaries` and the request over the file's store) and
`member_safe`'s framed branch are proved from it. `passMember`
checks a framed plan (`framedRun`, [what the pass
checks](#what-the-pass-checks)) and accepts it where every check passes
(`framedRun_sound`). **The codes are checked by the ordinary pass**,
so a code's closure meets its ordinary arrow, and **the sixth clause** of
`FramedRequestSafe` is proved from each code's guarantee
(`codesAccepted_guarantees`) by `framedCode_of_guarantee`: the graph's
safety read on the term that runs it (`GraphCode.safe_of_sim`), its
assertions at every state reached (`assertedAt_of_graph`), along every set
of executions (`SafeUnder.of_safe`)
(`returned-closure.mjs`'s closure, whose fact needs a frame, is refused at
its read). `view`: `ViewOver (Ty ι)` with `RO` the type reader's read-only
throughout, a read-only type's children read-only by construction
(`ro_child` by definition), agreeing with
`ComponentChecks.readOnlyShape` on the declared shape
(`ro_of_readOnlyShape`, to be proved). `PlanAt` stays the graph plans'
(`RowRealized` reads it); `FramedPlanAt` is new. `OverStore` reads every
plan, a graph plan or a framed plan (`FunctionPlan.parts`), and the plan
transforms change a plan's request alone, of either kind
(`FunctionPlan.mapRequest`): a framed plan's request takes the given head
facts and the inferred candidates as a graph plan's does, and
`Recandidated` relates each plan to the one at its index with other
candidates (`framedRequestSafe_recandidated`: the frame and the framed
claim read no candidate).

### What the pass checks

The executable check (`FramedFlow.lean`, `FramedNodeChecks.lean`,
`Json.lean`): `framedCallNodes`, the call nodes of the member's code framed
at some context of the flow; `callEffectAt`, the callee's stated effect at
the caller's slots; at each framed node $`l`$ of the request's code
`framedNodeOkB`: the call's operands read from slots (`atomCallB`), the
node's set $`T_l`$, the closure of the operand slots' sets at every context
and node sharing the call's continuation and handler (`nodeSet`), checked
closed (`capClosedB`), and each kept support passing `frameCheckAt` at
$`\Psi_c(l)=\Theta_C\sqcup\Psi_C\sqcup W(T_l)`$ (`nodeProtocol`) and
the callee's stated effect there (`supportKeptB`). The producer keeps, of
each node's entry supports (in the pass's slot numbering), those
`supportKeptB` passes (`framedNodeKeeps`), the check the pass runs on the
plan. `passMember`'s framed branch (`FilePlans.framedRun`) reads first the
refusal of the checks that read the component alone
(`componentBindingRefusal`, `FramedComponentChecks.lean`), evaluated once
per component and shared by its plans, each carrying the evaluation with
its value (`FramedSpec.componentRefusal`, a value with the equation that
it is `componentBindingRefusal` at the plan's fields): `noRestB`,
`FFlow.check`, `marksB`, `codesCoverB` over every module function's
realized and request codes, `allocB` (`allocSomeB`, and `allocCanonB` at
the bodies `moduleBody`, a module function's realized code's its
request's, from three sites per code), `initB` (in the initialization's
order, which names each module function once, each node allocating a
closure of the code of the function the order names there, each linked
capture the slot holding the closure its name names, allocated earlier,
every other capture a realm identity, the last node the entries' array)
and `frameFlowB` at the frame's sites. Then, per request, the binding
checks that read it (`FramedSpec.bindingChecks`, run by
`FilePlans.framedChecks`, decided as `FramedSpec.bindingB`): `entryB`,
`codesCoverB` at `requestCode r`, `entryFnB`, `clientsB` (the wire's
$`\Theta_C`$ by kind against the `@clients` rows, `rowsAt`),
`protocolAtLeastB` (the wire's $`\Psi_C`$ against `psiDef`, at the flow's
sites), `readOnlyB` and the framed call nodes the flow's; then the main
graph walked with those nodes framed (`passMemberGraph`), settled; then
the checks the returns read at the request (`FramedSpec.requestB`,
`FramedNodeChecks.lean`): its tag `C` (`compB`), its node expressions
source terms (`sourceTermsB`), $`\Theta_C`$ keeping every part
(`thetaKeepB`), its start a label of its program, `realizedFlowB` at the
frame's flow, and `framedNodesAt` (`framedNodeOkB` at each framed node) at
the frame's flow, a failure's text naming the node and the check
(`framedNodesWhy`). It refuses at the first that fails, and otherwise
accepts: its walk is the direct one, its walks run with no fallback
(`passMemberGraph`'s `fallback`), settled at candidates (`framedSettle`),
and `FramedAccepted` holds at the request with them (`framedRun_sound`,
through `passMemberGraph_accepted`'s `GraphAccepted` and `MainAcceptedAt`
at the framed nodes, the fallback excluded). The verdict line of its group
names the components (`acceptedUnderClientTrust`,
`FilePlans.clientComponents`), and the acceptance is a print site of
`Mode8Accepted` (`Mode8Accepted.framed`: the plans with the member's plan
the framed plan, `framedPlan_overStore`).
The component's checks include
`frameFlowB` at the frame's flow (`FramedFrameFlow.lean`: `FFlow.check`,
`marksB`, `tokensSomeB`, `codesLoweredB`, the closure of the capture
sites and $`O`$ checked closed, the initialization's node expressions and
the realm's identities free of runs, and with the realm's values meeting
`layP` and `WOk`, decided by `wokB`, the realm's values primitives, and
the initialization in the flow, `initFlowB`), the flow the frame reads with its tags decided (`frameFlowOf`,
`framePkg`), equal to the frame's (`frame_transport`). Each binding
check has a control forging its document, its flow, its initialization,
its plan or its family (`tests/single-pass-control-inputs.mts`,
`tests/single-pass-controls.mts`).

The producer (`FilePlans.framedPlan`, `RequestCli.framedVerdict`) forms a
framed plan for a member of a group the pass refused whose code calls. It
reads the file's framed component (`FramedComponent`,
`PreparedFile.framedComponent`), prepared once per file on the first
refused unit that reads it and kept beside the file's other prepared data
(`PreparedFile.framed`): the module, where it is its family's outermost
component and imports no other module's value (a located refusal
otherwise), its module functions (every function a module binding holds,
each planned alone, its closure collecting a rest where its source
declares one), the restrictions below, its flow solved once
(`framedComponentFlow`), $`\Psi_C`$ as defined at its flow's sites, its
initialization and the checks that read the component alone. Per member:
its framed call nodes and each node's entry supports the check passes,
observed in the walk. Its document is the producer's inputs alone: the
component, the entries, $`\Theta_C`$ by kind, $`\Psi_C`$ by numbered site
and kind, and each framed call node with its supports (`framedDocument`).
The decoder (`FramedSpec.decode`) reads the component's flow and refuses a
document whose fields, entries or nodes disagree with it; the supports are
checked by `framedNodesAt` after the walk;
`inputDigest` hashes the document. The framed plan's refusal follows the
group's ordinary refusal; the verdict is the ordinary plan's.

`MemberAccepted.framed`, beside `ordinary`'s premises over the request
(its codes by the ordinary pass): the checks that read the component
alone (`FramedAccepted.component`: `componentBindingRefusal` at the
plan's fields refuses nothing, which `componentBindingRefusal_none`
reads as `FFlow.check (remark F)`, `marksB`, `codesCoverB`, `allocSomeB`,
`allocCanonB`, `noRestB`, `initB` and `frameFlowB`, each passing); the
binding checks that read the request (`FramedAccepted.binding`,
`FramedSpec.bindingB` at the member's name, read by `FramedSpec.bindingB_iff`,
`FramedSpec.theta_rows`, `FramedSpec.readOnly_declared`,
`FramedSpec.framed_nodes` and `FramedSpec.entry_checked`); the main graph
accepted by the framed run (`RunCall.AcceptsFramed`) at the plan's framed
nodes; the checks at the request (`FramedAccepted.request`,
`FramedSpec.requestB` at `callEffects`). The premises on the initial configurations
(`InitialFits`, `InitialEntry`) are read from the component's checks
(`FramedSpec.initialFits`, `FramedSpec.initialEntry`).

## Restrictions

Each is chosen by the behaviour it excludes, enters
[SOURCE-FRAGMENT](../SOURCE-FRAGMENT.md) in the commit that enforces it,
is enforced at the plan (a located refusal of the framed plan, the unit
then checked by an ordinary plan), and has a control.

- **Framed units are realized units.** A framed plan's request is a module
  function of $`C`$ with a realization (`RealizeSim`). The excluded
  behaviour: a fact a method or a function a binding holds keeps across a
  call of outside code by the frame, whose entering step no realization
  relates to its request. Refusal: "a framed plan needs a realized entry";
  control: a method whose walker fact needs the frame, refused, its
  ordinary plan's refusal at the call.
- **No cycle of names.** No module functions of a framed plan's component
  name each other in a cycle. Excluded: two module functions whose
  closures capture each other, which `initC`, creating each closure after
  those it names, does not create; the note creates them as one group
  (conj.). Refusal: "a framed plan's module function X names the module
  function Y, which names it back, a cycle of names"; control:
  `bounds-pattern-framed-cycle-refused`.
- **Outside slots are audited realm values.** Every outside slot of a
  module function of a framed plan's component holds an audited realm
  value, the same at every depth: a native with a step model (P22's
  `%ElementAt%`) or an intrinsic object of the realm's heap (P22's
  `[[Array.prototype]]`). Both are decided by name: a native with a step
  model is a name `hostModel?` maps to a code, today `%ElementAt%` alone;
  an intrinsic object is a slot name of the form `[[…]]`
  (`intrinsicName`), modelled as an object with no field
  (`realmValueAt`), the import gate admitting a name starting with `%` or
  bracketed (`prepareFramedComponent`). The decision is the audit's list
  of realm values, by their names. Excluded: an import of another module's value, a module
  constant or cell, a host value, whose unfolding varies with the depth
  (`ApproxStable.lean`) and which `initC` does not initialize. Control: a
  framed walker whose module imports a function of another module, or
  reads a module `let` cell, refused. Pretext's walkers import; they wait
  for the initialization of imports.
- **`@clients` by kind.** A component's `@clients` rows state class keys
  only (or none, read-only). Excluded: a path key such as
  `"this.items[*]": "extend"`, whose part needs the declaration's sites.
  Control: a framed walker in a component whose exported type states a path
  key, refused.
- **A client obligation keeping every part.** A framed plan's
  $`\Theta_C`$ keeps every part (`thetaKeepB`, checked at the request,
  `FramedSpec.requestB`; `thetaKeepB_sound`): the component's `@clients`
  rows state no change. Excluded: outside code changing storage the
  component reaches read-only, such as `{ spines: "grow" }`, for which the
  returns at reached executions read $`\Theta_C`$ within the component's
  protocol (`hΘ` of `ret_reachedW_spec`) and the frame's guarantee route
  is milestone 4's. Refusal: "framed plan: the request check of its
  client obligation keeping every part (thetaKeepB) fails"; control: a
  framed walker in a component whose exported type states
  `@clients { spines: "grow" }`, refused, its ordinary plan's refusal at
  the call (`bounds-pattern-framed-clients-change-refused`), and the Lean
  control in `Tests/FramedBindingControls.lean`.
- **No rest in a framed component.** No code of a framed plan's component
  collects a rest: every layout of its flow's codes has none (`noRestB`,
  `ReadOnlyEnterRoots.lean`; with layout provenance every closure of
  $`C`$'s code has its code's layout, `layQ_noRest`). Excluded: a call
  from outside code of a closure of $`C`$'s code with a rest, which enters
  $`C`$ at the step of its rest's binding (`letV`), two steps after the
  call; that state's fit gives the run's slots their sets as lower bounds
  alone, and the entering step's crossings (`FramedSpec.entryXs`) read a
  call's arguments. Refusal: "framed plan: the binding check of no code
  collecting a rest (noRestB) fails", the first of the component's binding
  checks; a module function's closure collects a rest where its source
  declares one, of any type. Control: a framed walker beside a module
  function with a rest parameter, refused, its ordinary plan's refusal at
  the call (`bounds-pattern-framed-rest-refused`).
- **Exports are module functions.** Every module function of a framed
  plan's module has closure code, and every export of its component is a
  module function. Excluded: an exported class, another exported value, a
  module function declaring `this`, which the initialization (`initC`,
  whose last node is the array of the exports' closures) does not create.
  Refusals: "a framed plan's component exports X, which is no module
  function", "a framed plan's module function X has no closure code";
  control: a framed walker beside an exported class, refused
  (`bounds-pattern-framed-export-class-refused`).

## Callers and callbacks

### The callback's type

By the owner's decision of 2026-11-19, a callback into a framed component
meeting its arrow type, and a client program's executions typed at their
worlds, are parts of the client obligation. The row of $`\Theta_C`$
([Trust](readonly-handles.md#trust)) reads:

> Code outside $`C`$ keeps $`\Theta_C`$ at each of its steps on the storage
> the row protects; a function value it passes to $`C`$ at a function type
> meets that type: called by $`C`$, its run, its calls of $`C`$ included, is
> safe and within its stated effect; and every configuration of the
> program, the client's own code included, has an admissible world typing
> its heap (`AStep`, the configurations of `PublicCall`).

The theorem reads the row's callback clause as `FramedSpec.CallbacksWithin`,
a premise of `MemberSafe`'s framed branch: a call at a framed node of the
request's code (a call whose callee may be a value of outside code,
`framedCallNodes`) whose callee's type states an effect, from a reached
state entering it to the state it returns to with a value, changes the
heap within that effect at the node's slots. It says nothing of a throw.

The continuation after a failed return premise is outside the claim
(`RunSoundFramed` claims progress on paths whose framed returns meet their
premise; `ret_reachedW` establishes it before the continuation).

### Verdicts that read a framed member's arrow

- **The component's own linking supplies it** (a sibling slot, a unit's
  own slot, a module binding): the reading unit's ordinary plan reads the
  member's ordinary claim, which is refused, so the reading unit is
  refused ("a unit it depends on is refused"), and its framed plan reads
  the member's call as a known call checked by that claim.
  A module's interface does not establish a framed member
  (`establishVerdict`: its entry's `established` is null), and an
  importer of it is checked as an importer of any member its interface
  does not establish: verified at the member's declared type, its line
  naming no dependency on it (observed: the first review's importer of a
  framed walker and of a walker refused outright, both verified with
  `depends: []`).
- **An input supplies it** (`apply.mjs`'s `apply(f, h, visit)`): the
  ordinary verdict is conditional on its inputs meeting their types
  (`EntryHolds`). The caller row is restated with a reading in the
  definitions: a value of a framed component meets its declared type along
  the executions keeping that component's $`\Theta_C`$ at the program's
  history. In `apply.mjs` the handle `prepare` returned crosses into
  $`C`$ at `walk`'s read-only handle parameter when `walk` is entered (from
  `apply` outside $`C`$; or at `apply`'s own entry when `apply` is in
  $`C`$), so the history protects its array and the client's visitor,
  shortening it, breaks $`\Theta_C`$. The verdict line of such a unit is
  unchanged; the trust surface's caller row names $`\Theta_C`$.

The verdict line of a group with a framed member accepted lists its
components (`"acceptedUnderClientTrust": [C]`), the pipeline's outcome
`accepted only under client trust Θ_C (component C)`. Milestone 5 brings the
obligation-relative arrow $`[\![T]\!]^{\Theta}`$ and its linking theorem,
for units of the first kind.

## The theorems

### The graph at framed returns

`RunSoundFramed ι` (proved, `run_sound_framed`) replaces `Target.RunSound`: an accepted
framed run of the claim's main graph gives each of its five clauses as
safety at framed returns of the term that runs the graph
(`FramedReturnsGuarantee r F Ret RetE`), where every evaluation of a framed
node $`l`$, from its entry $`(\rho,h)`$ to its return $`(v,h')`$, meets

```math
\mathrm{Ret}_l(\rho,h,h')\iff\bigl(\forall S\in S_l.\ \mathrm{Supported}(S,\rho,h,h')\bigr)\wedge\bigl(\forall (I,\mathit{root})\in G_l.\ I_{\mathit{root}}(\rho,h)\Rightarrow I_{\mathit{root}}(\rho,h')\bigr)
```

and $`\mathrm{Ret}^{e}_l`$ alike at a throw. **Safety at framed returns**
(`SafeRet`, `Semantics/SafeRet.lean`) is `SafePostExcW` with a state
property `J` at every state, its run followed past a step leaving a framed
node only where the return meets $`\mathrm{Ret}`$ (the node's term a
value) or $`\mathrm{Ret}^{e}`$ (a throw), at the node's environment, the
heap it was entered at and the heap it leaves at. The evaluation pending is
threaded along: a step from `goto … l …` to a `frame` with $`F(l)`$ records
$`l`$ and the heap (`framedPend`), a step within the frame keeps it, any
other step clears it (`RetAt` reads it at the leaving step).

```lean
def SafeRet (J : Heap → Tm → Prop) (Ξ T : Fam) (Q : WPost) (R : WExc) (F : Nat → Bool)
    (Ret RetE : Nat → Env → Heap → Heap → Prop) :
    (n : Nat) → WorldT n → Option (Nat × Heap) → Heap → Tm → Prop
```

`Target.RunSound` is the instance with no framed node: `SafeRet.of_safe`
(ordinary safety with `J` along the run is `SafeRet` at every framed set)
and `SafeRet.erase` (with no framed node, `SafeRet` is ordinary safety),
both proved; at the claim, `framedReturns_of_requestSafe` (proved): a
request safe for every execution meets `FramedReturnsGuarantee` with no
framed node, whatever the returns.

**The graph theorem at framed returns is the graph theorem, generalized
once.** The composition of node obligations into the graph's safety reads
a node's exits through one structure, `NodeObligations`; its version under
return premises, `NodeObligationsR` (each exit's target required where the
exit's heap meets $`R_n`$, or $`R_e`$ at a throw), is the only place a
framed node differs (`SinglePass/GraphSafety.lean`). The graph machine's
safety at framed returns `SafeGraphRet Ξ P T F Ret RetE` threads the pending
evaluation as `SafeRet` does (`enterPend`, `pendG`, `RetAtG`), and
`NodesCheckedR P pre F Ret RetE` gives a framed node $`l`$ entered at
$`h_0`$ the premises $`\mathrm{Ret}_l(\rho,h_0,\cdot)`$ and
$`\mathrm{Ret}^{e}_l(\rho,h_0,\cdot)`$. Proved, each with the ordinary
statement as its instance with no framed node (`toR`, `toPlain`,
`SafeGraphRet.erase`, `SafeRet.erase`), the ordinary proof deleted:

- `graph_stepR`, `graph_safeR`, `graph_safe_atR` (instances `graph_step`,
  `graph_safe`, `graph_safe_at`);
- `keeps_stepR`, `keeps_postExcR` over `NodesKeepR` (instances
  `keeps_step`, `keeps_postExc`), the latter with a state property `J` the
  invariant gives, which carries the assertions clause;
- `safeRet_of_sim`, `sim_pend`, `sim_retAt`: the term that runs graph code
  is safe at framed returns as the graph machine is;
- the walk's steps: `nodeObligationsR_marked`, `nodeObligationsR_mono`,
  `nodesCheckedR_stable`, `nodesChecked_of_walkJR` from
  `StepEdgesSoundMarkedR`, `nodesChecked_of_walkR` (instances the ordinary
  ones).

The size of the generalization, measured: the declarations between the
node obligations and `run_sound_single_pass` that read them are 25, 638
lines in 12 files of the 26.6K lines of `TolerantFrames*` and
`SinglePass/` (a Lean dependency walk from `run_sound_single_pass` to
`NodeObligations`: 30 theorems and 8 definitions, structure projections
included). Below `StepEdgesSoundMarked` nothing is restated: a framed
node's delivery enters as its obligations under its returns.

The framed node's delivery is `stepEdgesSound_of_yieldsR`: at a framed
node $`l`$ entered at $`h`$, an exit whose heap $`h'`$ meets
$`\mathrm{Ret}_l(\rho,h,h')`$ holds each index fact of the step's input
whose produced support (read with no stable key) lies in a support of
$`S_l`$ (`framedKept_holds`, in place of `callerFrame_post`), which the
node's exits read beside the step's output (`NodeYieldedR` at `framedK`).
`run_guaranteeR` gives the five clauses on the term that runs the graph
(`GraphGuaranteeR`) from a walk at framed returns (`PassWalkSoundR`), by
`safeRet_of_sim` and `keeps_postExcR`; `run_sound_checkedR` and
`run_sound_framed` give `RunSoundFramed` over the pass's framed mode
`RunCall.AcceptsFramed`: the call's walk accepted, each visited node's
exits delivering with `framedK`.

**The walk at framed nodes.** A call of the pass names its framed nodes
with the supports their returns keep (`RunCall.framed`, the walk's
`framed`; `framedAt`). At a framed node the exits read the step with the
facts its return keeps added to the store after the step, over the names
after it (`keptStep`, `keepStore`, `keptDone`); the label's record keeps
the step itself. A call is accepted in the ordinary mode where its walk is
accepted with no framed node (`RunCall.Accepts`: `AcceptsWalk` and
`framed = []`), which is the premise of `RunSound`; the walk's records
cover every accepted walk (`RunTraversedA`, `RecordsChecked` and
`RunPremises` read `AcceptsWalk`). The exits' records are checked at the
exits' step (`ExitsYield` at `keptStep`, the trace and the site's facts at
`keptDone`), whose store holds where the state after the step and
`framedK` hold (`stateHolds_keep`, `keptHolds_of_framedK`); so each node
delivers with its exits reading `framedK` at the call's framed nodes
(`NodesYield`, `nodeYieldedR_of_checks`), and a call whose walk is accepted
is accepted in the framed mode at its own framed nodes
(`acceptsFramed_of_walk`, `acceptsFramed_of_acceptedWalk`). With no framed
node the exits' step is the step and `NodeYieldedR` gives `NodeYielded`
(`NodeYieldedR.toPlain`), which `run_sound_checked` reads.

### The returns, at reached executions

The frame's executions are of actual steps (`KStep`), and the client
obligation is read at each configuration's world, whose kinds the
protocol reads (`St.part`). A step clause reading the obligation at a world
unrelated to the configuration admits steps that break it at the
configuration's world (`rowAt_reads_world`, proved, a counter-model: one
transition keeps a protocol at a world where the location is a field and
breaks it at one where it has no kind), so the returns are stated at the
worlds of the safety derivation: `FramedReturnsReachedW r fr F Ret RetE`,
an invariant of the history, the pending framed evaluation, the world and
the state, holding at every call the claim is about, on which every step
keeping $`\Theta_C`$ at the state's world, to a world and heap the step's
safety admits, meets the returns (`RetAt`) and leaves a state meeting it
where its term is valid there. `framedRun_of_returnsW` (proved, by
`SafeRet.underW`) gives the main graph's five clauses from it and the
guarantee.

Lean (proved, `FramedReturns.lean`):

- `ret_reachedW`: `FramedReturnsReachedW r fr F (framedRet S) (fun _ _ _ _ => True)`
  from the request's node expressions being source terms, the calls at
  positive budgets of admissible worlds typing their heaps with slots of
  values, and `FramedNodeTransfer` at the request's code and tag: along
  every execution of the frame from a reached state entering a framed node
  $`l`$ to a state whose node's term is a value, every support of $`S_l`$
  is supported from the entry's heap to that state's. The invariant
  (`RetInv`) is the frame's reached configuration at the world, the
  request's code at the top of the term with slots of values (`TopRuns`),
  and the pending evaluation the execution from its node's entry
  (`PendFrom`); the step leaving a frame keeps the heap
  (`frame_val_heap`), so $`\mathrm{Ret}_l`$ is read at the resumption.
- `nodeTransfer_of_transfer`: `FramedNodeTransfer` by `framed_transfer`
  at each framed node, its operands read from the slots (`atomCallB`,
  decided; P22's nodes 10 and 13 are such calls), so the node's entry is
  a call state (`atomCall_inst`) and its evaluation to a value the call's
  segment to its resumption; its premises: `ChkSound`, `StartInv`, the
  request's tag of $`C`$, trace certificates at $`\Psi_j`$ with
  $`\Theta_C\sqsubseteq\Psi_j\sqsubseteq\Psi_c(l)`$, `SegWithin`
  $`\Psi_c(l)`$ at the node's entry, `Framed` $`\Phi_l`$
  $`\Psi_c(l)`$ of each support at the node's entry (the pass's check,
  by `ClientFrame.framed_at_innermost`), and the callee's
  effect $`\Phi_l`$ bounding the heap along the call (the callback's
  arrow, part of $`\Theta_C`$).
- `own_of_run`: that `SegWithin` premise by `segWithin_of_run` at each
  node's set $`T_l`$, from `hroots` at the node's entry.
- `own_of_fit`: that premise from the frame's fit. The fit of a frame
  records its node through its continuation and handler alone (`NodeOf`),
  so it gives each slot value the slot's set at some node $`l'`$ sharing
  $`l`$'s continuation and handler, at some context; where $`T_l`$ holds
  the sets of the operand slots (`atomSlots`) at every such node and
  context (`hslots`), each operand meets a set within $`T_l`$ (`atom_vj`,
  a constant every set), and so each value of the call's term meets
  $`T_l`$ in depth (`deepIn_of_checks`, `DeepIn.held`), the premise of
  `segWithin_of_deep` (`within_deep`, `ReadOnlySegment.lean`).
- `framed_of_check`: the `Framed` premise from the pass's check of each
  support at every context of the code and every node with $`l`$'s
  continuation and handler (`frameCheckAt`, each region at its keys, no
  protection), by `ClientFrame.framed_at_innermost`, where the separation the
  check reads holds at the node's entry.
- `ret_reachedW_of_checks`: `ret_reachedW` with its transfer premise
  assembled from `nodeTransfer_of_transfer`, `own_of_fit` and
  `framed_of_check`. Its premises besides the checks (`atomCallB`,
  `hslots`, the closure check of each $`T_l`$, $`W_c(T_l)\sqsubseteq\Psi_c(l)`$,
  the frame check): the spec's (`hsrc`, `hty`, `hvals`, `ChkSound`,
  `StartInv`, `Facts`, `FlowSites`, `EntryFits`, the residual
  invariant and layout provenance at the starts, `tokensSomeB`,
  `codesLoweredB`), the trace certificates at $`\Psi_j`$ with
  $`\Theta_C\sqsubseteq\Psi_j\sqsubseteq\Psi_c(l)`$,
  the separation the frame check reads at each framed node's entry, and
  the callee's effect bounding the heap along the call (part of
  $`\Theta_C`$).
- `ret_reachedW_of_charges`: `ret_reachedW_of_checks` at the
  certificates `cert_of_charges` gives, $`\Psi_j=\Psi_C`$; in place of the
  certificates it reads the reached-term invariant at the starts, the
  closure check of the capture sites and $`O`$, `hroots`
  ([certificates](#certificates)) and
  $`\Theta_C\sqsubseteq\Psi_C\sqsubseteq\Psi_c(l)`$.
- `ret_reachedW_of_entries`: `ret_reachedW_of_charges` with `hroots`
  given by `entry_roots` at `cert_of_deep`; in its place it reads `noRestB`
  and that no run of $`C`$'s code waits as a binding's body at the starts
  (`NoPend`).
- `ret_reachedW_frame`: `ret_reachedW_of_entries` at `spec.frame r` and a
  flow whose `Flow` is the spec's. The facts of the spec discharge the
  reached-term invariants at the frame's calls (`wfS_start`,
  `noPend_start`), the flow's sites (`flowSites`), and layout provenance
  and the residual invariant at the calls (`lay_start`, `wok_start`, from
  the initial configurations meeting them). Its premises:
  - *checks the pass runs*: the program's source terms (`hsrc`),
    `FFlow.check` (`Facts`, `FFlow.check_sound`), `tokensSomeB`,
    `codesLoweredB`, the request's tag (`compB`), `atomCallB` at the framed
    nodes, the closure check of each $`T_l`$ and of the capture sites and
    $`O`$, $`W_c(T_l)\sqsubseteq\Psi_c(l)`$, `hslots` and the frame check
    at every node sharing $`l`$'s continuation and handler and every
    context, `noRestB`, $`\Theta_C\sqsubseteq\Psi_C`$ (`clientsB`,
    `protocolAtLeastB`) and $`\Psi_C\sqsubseteq\Psi_c(l)`$;
  - *the trust* of $`\Theta_C`$: the callee's effect $`\Phi_l`$ bounding
    the heap along each framed call (`hΦ`, the callback's arrow);
  - *the initial configurations*: layout provenance and the residual
    invariant (`initial_starts`, from checks of the initialization's node
    expressions, the realm's heap, and the client's lowered source, which
    `Initial` states, `initial_lowered`);
  - *invariants of the frame*: `ChkSound`, `StartInv`, `EntryFits`,
    `hvals` and the separation the frame check reads at each
    framed node's entry (`hq`), which `ret_reachedW_public` discharges.

- `ret_reachedW_spec` (proved, `FramedReturns.lean`): `ret_reachedW_frame`
  at the plan's flow (`spec.fflow`) and layouts (`spec.lay`), the hashing
  of the plan's sites its instance: `hty` by `call_typed` (an entry is a
  configuration, whose budget is positive, world admissible and heap
  typed); the initial configurations by `initial_lay` from layout
  provenance and the residual invariant of the initialization's node
  expressions and of the realm's heap; `noRestB` from the component's
  binding checks (`componentBindingRefusal_none`). Its other premises are
  `ret_reachedW_frame`'s.
- `framedReturns_reached` (proved, `FramedReached.lean`):
  `ret_reachedW_public` with every premise that is a check read from the
  pass's: the component's at the frame's flow (`frameFlowB_sound`,
  `frameFlow_checks`), the request's (`framedNodesAt_sound`,
  `framedNodes_frame`, `compB_sound`), $`T_l`$ and $`\Psi_c(l)`$ as the
  check defines them (`nodeSetOf`, `nodeProtocolOf`, `nodeProtocolOf_ge`
  giving `hle` and `hW`), `hΘ` by `thetaKeepB_sound`, the separation by
  `classQuery_sound`, `hΦ` from the callback row
  (`FramedSpec.CallbacksWithin` at `callEffects`), the checks of the
  program's starts by `FramedSpec.starts_checks` (`marksB` and
  `realizedFlowB` at the frame's flow, the start a label, the
  initialization free of runs); the two premises on the initial
  configurations, `InitialFits` and `InitialEntry`, from the component's
  checks (`FramedSpec.initialFits`, `FramedSpec.initialEntry`,
  `FramedInitial.lean`; [the initialization in the flow](#the-initialization-in-the-flow)).
- `ret_reachedW_public` (proved, `FramedStarts.lean`): `ret_reachedW_spec`
  with the frame's invariants read along the program. The program's
  states (`ProgOk`: `wfS`, a heap free of runs, layout provenance,
  `NoPend`, the fit) are kept by every step (`progOk_ex`) from the
  initial configurations (`progOk_initial`). At an entry the entering
  step pushes the realized code's run at a position of outside code
  (`enter_hole_out`), the realization is the prologue (`prologue_det`),
  so the run fits $`O`$ there at a proposal that is the request's at its
  body labels (`entry_hole`, `realizedFlowB_sound`): every entry fits
  (`entryFits`), its slots are values (`slotVals`), and the checks give
  (S), (K) and (O) (`chkSound`, by `chkSound_of_sitesIn`). The program's
  history meets the invariants of states at the program's frame
  (`progFrame`, its calls the initial configurations, its start the
  history before any entry; `progFrame_chkSound`, `reached_ok`), and its
  truncation keeps them: the request's run at the top holds no root of
  outside code, and the protected set, the sites and the heap are the
  program's (`startInv`). The
  pass's frame check reads `classQuery`, sound at every state. Its
  premises besides `ret_reachedW_spec`'s checks and trust: the request's
  start a body label, `realizedFlowB` and `marksB` at `spec.fflow`, the
  initialization's node expressions free of runs, and two named check
  premises on the initial configurations, the fit of the flow
  (`InitialFits`) and the premises of an entry (`InitialEntry`).

With no framed node the returns hold of every frame
(`framedReturnsReachedW_none`, proved).

### The framed claim, from the check

```lean
theorem framed_requestSafe {f : FilePlans} {r : Req f} {spec : FramedSpec _}
    (hrun : RunSound (EquationStore.CheckedLabel f.F.equations f.F.primitive))
    (hkeep : RunKeepsSummaries (EquationStore.CheckedLabel f.F.equations f.F.primitive))
    (htypes : r.types = f.F.store) (hacc : FramedAccepted f r spec) :
    FramedRequestSafe r (spec.frame r)
```

Proved: the sixth clause by `codesAccepted_guarantees` and
`framedCode_of_guarantee`; the five main-graph clauses by
`framedRun_of_returnsW` from the plan's framed nodes and returns, the
guarantee and the reached returns: at each call and history the frame
starts from, `SafeRet.underW` (proved, by induction on the budget) reads the
returns at each step keeping $`\Theta_C`$ from the invariant, and claims
nothing past a step breaking it. The guarantee is `framedReturns_of_main`'s,
from the framed main run `FramedAccepted` holds; the returns are
`framedReturns_reached`'s.

### The headline

`member_safe` gains the framed branch, `passMember_sound` shows `passGroup`
makes a framed member `MemberAccepted.framed`, and the executable path is
`FilePlans.passMember`'s framed branch. `mode8Accepted_sound` keeps its
statement:

```lean
theorem mode8Accepted_sound {f : FilePlans} {i : Nat} (h : Mode8Accepted f i) : PassUnitSafe f i
```

- **Premise** `Mode8Accepted f i`: the exact CLI condition, at the print
  sites `main`, `freshModule` and `framed` (a group accepted at a member's
  framed plan, `PreparedFile.framedVerdict`); a group with a framed member
  is printed accepted under client trust at its components.
- **Conclusion** `PassUnitSafe f i`: every member is `MemberSafe`: a graph
  plan's request `RequestSafe`; a framed plan's `FramedRequestSafe r
  (spec.frame r)`, that is: at each entry of $`r`$'s realized code from
  outside code in a program from an initial configuration, at the
  program's world, every step of outside code keeping $`\Theta_C`$ at the
  program's history up to the entry (as [read above](#the-calls-the-claim-is-about)),
  from the request's entry contracts and along each continuation keeping
  $`\Theta_C`$, every state is a value, a throw or takes a step with an
  admissible world and a typed heap, and the footprint, postcondition,
  regional and assertion clauses hold; and each code's requirements hold
  at every call of it. No proposal narrows the calls.

The commit that builds it records `Theorem modified (mode8Accepted_sound)`
with this conclusion and the readings of `MemberSafe`, `FramedRequestSafe`
(its sixth clause, `enters` with the world) and `ClientFrame`.

## Proved, to be proved, trust

**Proved at the base**, reused: `FFlow.check_sound`, `fitsAt_reached`
(its proof), `fits_step`, `fits_roots`, `fits_graphEntry`, `fits_lowered`,
`chkSound_of_sites`, `sitesSound_of_fits`, `ClientFrame.framed_at_innermost`,
`frameCheck_sound`, `framed_of_sites`, `regionSites_sound`, `reach_sites`,
`regionKeys_sound`, `grows_of_start`, `HStep.uniform`, `call_segment`,
`decompose`, `Run.bound`, `MemberRun.within`, `RBoundBelow.trans`,
`RBound.mono`, `RBoundBelow.mono`, `StepWithin.mono`, `approx_stable`,
`step?_sound` and `linked` (`Tests/FramedLinkedCall.lean`, the first check),
`InR.mono`, `FrameCore.PublicCall.ex`, `FramedSpec.frame` (its
`start_total`), `framed_requestSafe` from `FramedAccepted` (its codes'
clause by `framedCode_of_guarantee`), `member_safe`'s framed branch,
`OverStore` over framed plans, `framedRequestSafe_recandidated`,
`SafeRet.underW`, `SafeRet.of_safe`, `SafeRet.erase`, `framedRun_of_returnsW`,
`framedReturns_of_requestSafe`, `framedReturnsReachedW_none`, `isolate`
(`innermostGoto_ctx`, `EvalCtx.step`, `EvalCtx.steps_inv`), `assertedAt_of_graph` (by `sim_reaches`, a path of the
term that runs a graph is a graph path), `pkg_step_ok`, `stepWithin_of_check`, `readOnly_rule`,
`supported_of_framed`, `step_changes`, `step_reach`, `stepAt_site`,
`Fits.innermost`, `XStep.inv`, `Ex.inv`, `kstep_xstep`, `reached_ok`,
`sim_step_back`, `asserted_of_reach`, `framed_callSafe`,
`call_local_sound`, `callKept_sound`, `callGrown_sound`,
`callEntry_holds`, `codesAccepted_guarantees`, `run_sound_single_pass`,
`crosses_hsteps`, `crosses_covers`; `crossOk_incoming`, `sitesAt_reached`,
`pkgProps_actualIn`, `chkSound_of_escapeIn`, `chkSound_of_sitesIn`,
`chkSound_of_flowIn` (`ReadOnlyIncoming.lean`),
`FramedSpec.actualCrossingsIn`, `FramedSpec.entryXs_into`
(`FramedHistory.lean`); `capClosedB_sound`, `segClosedB_sound`
(`ReadOnlyCharges.lean`); `codesCoverB_sound`, `allocSomeB_sound`,
`allocOf_some`, `stepSite_some`, `entryFnB_sound`, `agreeB_sound`
(`ReadOnlyBinding.lean`), `realizedFlowB_sound` (`FramedBinding.lean`);
`step_writes_active`, `Fits.active`, `write_site`
(`ReadOnlyStepWrites.lean`); `crossOk_noLeaves`, `vals_located`,
`num_not_root` (`ReadOnlyIncoming.lean`); `protocolAtLeastB_sound`
(`ReadOnlyBinding.lean`), `clientsB_sound` (`FramedBinding.lean`);
`canonSite_inj`, `allocCanonB_sound`, `allocCanon_same`
(`ReadOnlyBinding.lean`), `allocB_realized`, `compB_sound`
(`FramedBinding.lean`); `step_wok`, `subst_wok`, `instantiate_wok`,
`active_writes`, `slotKind_sound`, `step_kind_charged`,
`probeProtocol_charged`, `stepWithin_charged`, `ClientFrame.wok_reached`,
`lowered_wok` (`ReadOnlyWriteKinds.lean`); `graph_stepR`, `graph_safeR`,
`SafeGraphRet.erase` (`SinglePass/GraphSafety.lean`), `keeps_stepR`,
`keeps_postExcR`, `safeRet_of_sim` (`TolerantFramesGuaranteeRuns.lean`),
`nodesChecked_of_walkJR`, `nodesChecked_of_walkR`; `framedKept_holds`,
`stepEdgesSound_of_yieldsR`, `run_sound_checkedR`
(`TolerantFramesComposeYields.lean`), `nodeObligationsR_of_partsY`
(`TolerantFramesNodeYields.lean`), `run_guaranteeR`
(`TolerantFramesGuaranteeWalk.lean`), `run_sound_framed`,
`acceptsFramed_of_acceptedWalk` (`TolerantFramesSinglePassSound.lean`);
the walk at framed nodes: `keepStore_ok`, `stateHolds_keep`,
`keepStore_wf` (`TolerantFramesEntry.lean`), `keepStore_below`
(`TolerantFramesStoreOpsBelowNames.lean`), `keptHolds_of_framedK`,
`NodeYieldedR.toPlain`, `nodeYieldedR_of_checks`, `nodesYield_of`,
`acceptsFramed_of_walk` (`TolerantFramesComposeYields.lean`),
`exitsYield_of_checks` at the exits' step (`TolerantFramesExitsYield.lean`);
`framedReturns_of_guaranteeR`, `framedFootprint_of_bound`,
`framedReturns_of_main` (`PassUnitSafe.lean`); `local_reach`,
`valRun_noForge`, `reach_deep`, `stepWithin_reach`, `lowered_vals_all`,
`deepIn_of_vj`, `heapDeep_of_heapInv`, `Fits.frameIn`, `frameKinds_flow`,
`wok_program`, `wok_initial`, `active_vals`, `redex_arg_root`
(`ReadOnlyLocalReach.lean`), `FramedSpec.entryXs_roots`
(`FramedHistory.lean`); `step_layP`, `layDeep_of_layP`, `layouts_reached`
(`ClientFrame.lay_reached`, `FrameCore.lay_program`, `lay_initial`),
`capClosed_of_lay`, `codesLoweredB_sound`, `tokensSomeB_sound`,
`heapDeep_of_checks`, `deepIn_of_checks` (`ReadOnlyLayouts.lean`);
`activeFrame_ctx`, `activeFrame_hole`, `Fits.frameIn_hole`, `hole_run`,
`valRun_of_steps`, `EvalCtx.refs_hole`, `EvalCtx.wok_hole`, `wok_steps`,
`within_run`, `within_depth`, `within_member` (`ReadOnlySegment.lean`);
`tabRel_step`, `tabRel_steps`, `tabRel_stuck`, `activeFrame_snd`,
`stepSite_tabRel`, `vals_tabRel`, `vals_ctx`, `actualXs_congr`
(`ReadOnlyRealize.lean`), `bodyTargetsB_sound`, `realized_agree`,
`prologue_steps`, `prologue_sim`, `chk_site_sim`, `chk_actual_sim`,
`chk_entry_sim`, `chk_sim` (`FramedRealize.lean`), `path_ctx`,
`depthC_ctx`, `tabRel_tags`, `entered_frame`, `frame_goto_tags`
(`ReadOnlyRealize.lean`), `entry_run`, `lay_start`, `wok_start`,
`initial_starts`, `flowSites` (`FramedRealize.lean`), `EvalCtx.layP_hole`
(`ReadOnlySegment.lean`); `RunSeq.within` (`ReadOnlyCert.lean`); `RunSeq.mono`,
`RunSeq.keeps`, `traceMember`, `decompose_trace`, `exec_bound_trace`,
`callRun_trace` (`ReadOnlyTraceCert.lean`); `seg_run`, `seg_bound`,
`transfer_at`, `Leads.of_bound`, `frameC_shape`, `FrameCore.inside_run`,
`CallState.depth`, `Inside.depth`, `Resumes.depth`, `framed_transfer`,
`innermost_tag`, `blocks_one_all`, `activeFrame_runsC`, `inside_prefix`,
`ex_sites`, `segWithin_of_run` (`ReadOnlyTransfer.lean`); `SafeRet.underW`,
`framedRun_of_returnsW`, `rowAt_reads_world`, `TopRuns.step`,
`frame_val_heap`, `frame_to_frame`, `retInv_step`, `ret_reachedW`,
`atomCall_inst`, `nodeTransfer_of_transfer`, `own_of_run`, `atom_vj`,
`own_of_fit`, `frame_rootsOk`, `framed_of_check`, `ret_reachedW_of_checks`
(`FramedReturns.lean`); `within_deep`, `DeepIn.held`
(`ReadOnlySegment.lean`); `segWithin_of_deep`, `enterWrite_step`
(`ReadOnlyTransfer.lean`); `wfS_of_free`, `wfS_wf`, `step_wfS`
(`ReadOnlyPending.lean`); `EvalCtx.raises_hole`, `EvalCtx.step_hole`,
`ctx_val_tags` (`ReadOnlyEnter.lean`); `enter_keeps_heap`, `enter_ctx`,
`hole_ex`, `hole_runsC`, `ClientFrame.reached_wfS`,
`ClientFrame.cert_of_charges` (`ReadOnlyMemberCert.lean`);
`ClientFrame.cert_of_deep` (`ReadOnlyMemberCert.lean`);
`EvalCtx.free_hole`, `EvalCtx.not_free`, `noRun`, `list_hole_inv`,
`step_hole_inv`, `EvalCtx.wfS_hole`, `noRestB`, `layQ_noRest`, `NoPend`,
`noPend_goto`, `noPend_step`, `PathAt.keep`, `fits_ctx`, `depth_push`,
`deep_entry`, `ClientFrame.noPend_reached`, `ClientFrame.entry_roots`
(`ReadOnlyEnterRoots.lean`); `FramedSpec.wfS_start`,
`FramedSpec.noPend_start` (`FramedRealize.lean`); `ret_reachedW_of_charges`,
`ret_reachedW_of_entries`, `ret_reachedW_frame`, `ret_reachedW_spec` (`FramedReturns.lean`); `call_typed`, `initial_lay`, `initial_lowered` (`FramedRealize.lean`, `FramedSpec.lean`); `innermostGoto_ctx_goto`, `innermostGoto_ctx_frame`, `enter_hole_out`, `loweredSrc_free`, `noPend_letGoto`, `progOk_step`, `progOk_ex`, `progOk_initial`, `prologue_det`, `entry_hole`, `entryFits`, `slotVals`, `noKeys`, `chkSound`, `progFrame_chkSound`, `startInv`, `ret_reachedW_public`, `init_ofC`, `initialEntry_code`, `initialFits_code`, `capSig_not_lowered` (`FramedStarts.lean`); `OCapFn.inst`, `SelfFn.ocapFn` (`ReadOnlyFitsCheck.lean`), `ocapFnB_sound` (`ReadOnlyFitsDecide.lean`); `prov_mono`, `prov_loweredSrc`, `instantiate_of_scoped`, `realmSlot_vj`, `realmSlot_scoped`, `init_fits`, `FramedSpec.frameFlow_checks`, `FramedSpec.init_checks`, `FramedSpec.initialFits`, `FramedSpec.initialEntry`, `FramedSpec.codeOk_ok` (`FramedInitial.lean`); `framedReturns_reached` (`FramedReached.lean`); `passMemberGraph_accepted`, `framedSettle_ok`, `framedRun_sound`, `passMember_sound`'s framed branch (`PassUnitMemberRun.lean`); `overStore_withPlan`, `framedPlan_overStore`, `mode8Accepted_sound`'s framed case (`PassUnitRun.lean`); `preparedMode8_overStore` (`PassUnitInterfaces.lean`); `entryXs_root` (`FramedHistory.lean`).

**Observed at the base** (to be moved into the build): `truncate_prot`,
`truncate_uniform`; `startFix_startInv_len`, `keep_rejects`,
`released_prot_inR`, `loweredSrc_no_closure`, `gotoOf_start_ne`;
`cross_into_prot`, `truncate_after_cross`, `allocSomeB`'s value on
`AstraR3.lean`'s flow; `body_prefix` (`Round5.lean`); `entry_slot_holds_O_tokens` (the second
review's `CodeClause.lean`).

**To be proved, milestone 1**: `publicCall_safe`, `entryHolds_realized`,
`project`, `keeps_canonical`, `ro_of_readOnlyShape`.

**To be proved, milestone 2**: the theorems of
[the protected reading](#the-theorem-chain).

**To be proved, milestone 4**: `framed_guarantee`, `pathFact_alloc`, `tolerant_of_storeKeepsInv` with
disjoint supports (`supportShareB`, `SupportDisjoint`),
`pathSupport_stays`, `protectedInto_of_supp`, `protectedInto_released`,
`supp_split`, `hnew_of_paths`, `invariant_of_entry`.

**Trust**, rows of the [trust surface](../DESIGN.md#trust-surface):

- the client obligation $`\Theta_C`$, stated in the component's API
  (owner-approved), with its three parts (owner's decision of 2026-11-19):
  code outside $`C`$ keeps $`\Theta_C`$ at each of its steps; a function
  value it passes to $`C`$ at a function type meets that type, its calls of
  $`C`$ included; and the program's executions are typed at their worlds
  (`AStep`: every configuration of the program, the client's own code
  included, has an admissible world typing its heap);
- the caller row, restated: a value of a framed component meets its
  declared type along the executions keeping that component's
  $`\Theta_C`$ at the program's history;
- *Clients* (Assumption "Clients"): outside code enters $`C`$ only through
  its interface (`Provenance`), is lowered source of the calculus
  (`Source`), closed (`ClosedAt`), well formed (`Discipline`);
- the request's entry contracts at a public call (the existing rows on
  exported preconditions and handle parameters);
- a native's step model performs its model's steps, where the flow reads
  one;
- the binding of the plan to the checked file (executable, unproved, the
  front end's trust): `PreparedFile.prepareFramedComponent`,
  `FramedComponent.of`, `componentInit`, `framedComponentFlow` and
  `FramedSpec.decode` build the plan's realm, initialization, flow and
  family from the file's fragment and declaration document. Proved of the
  checks the plan carries: its $`\Theta_C`$ is the family's `@clients`
  rows' (`FramedSpec.theta_rows`), its read-only types the member's
  declared read-only parameters (`FramedSpec.readOnly_declared`), its
  framed nodes the flow's (`FramedSpec.framed_nodes`), its entry the
  checked flow's (`FramedSpec.entry_checked`) and its tag $`C`$
  (`compB_sound`).

## Milestone 2: the protected reading

The frame's check reads a region as protected where
[the decision](#the-decision) holds, so that the pass applies the frame's
check of [Read-only frames](readonly-frames-note/note.tex) §4.1, within
the [restrictions](#restrictions-of-the-protected-reading) below:
the pass's check of each framed node (`framedNodesAt`) and the producer's
supports (`FilePlans.framedSupports`) read `FramedSpec.protAt`, and the
returns at reached executions discharge its witnesses
(`framedReturns_reached`, `FramedSpec.prot_witness`). Every Lean name
below is proved. The pieces are in [commit order](#the-pieces-in-commit-order).

### The existing mechanism this extends

The frame's check at a framed call node has the protected reading as a
parameter. `frameCheck` (`ReadOnlyChecks.lean`) takes `prot : Region →
Bool` and reads it in its second line: a part of a site of $`O`$ meets the
callee's effect where its region is not read as protected
(`Part.mayOut`). `frameCheck_sound` is sound where every lent location of
a region read as protected is protected (`hprot`), and `prot_of_witness`
discharges that from a live history witness (`Witness`); `framed_of_sites`,
`framed_of_frame` and `ClientFrame.framed_at_innermost`
(`ReadOnlyCallFrame.lean`) carry the witness premise to a reached state.
The history records the witness: an entering step of a public call pushes
the call's set and then crosses each argument in at a type
(`Ghost.stepAt` at kind `enter`, `FramedSpec.entryXs`), a crossing in adds
what it reaches read-only to every set (`Ghost.cross`, `Ghost.incoming`),
and every step inside the call grows the history (`XStep.grows`,
`Ex.grows`), along which a witness stays live (`Witness.grow`).

The code passes `prot` false at each reader: `framed_of_check`
(`FramedReturns.lean`, its last argument to `framed_at_innermost`),
`supportKeptB` and `supportFailure` (`FramedNodeChecks.lean`) and
`framedSupportsAt` (`FramedFlow.lean`). The milestone gives them a decided
`prot` and proves the witness premise. It adds no rule and no trust; it
changes the types an entering step's crossings are recorded at to the
meet the draft's [history of a program](#the-history-of-a-program) states
(piece 0).

Three proved mechanisms are reused as they stand:

- **Witness growth**, from `ClientFrame.witness_reached`. Its premise
  `StartsEntry` reads a start equal to `entryStart`; the framed spec's
  start is the program's history at the entry truncated to one set
  (`FramedSpec.truncate`, `FramedSpec.frame`), so the premise fails at the
  framed spec. The argument does not need it: a witness at the start grows
  to every reached state with the call active (`Witness.grow`,
  `Ex.grows`, `ex_depth`, `ex_xstep`). The route keeps the witness
  interface and replaces `entryStart_witness` by a witness at the
  truncated start, built from the entering step's crossing. Proving the
  protected set directly reaches the same set but bypasses `Witness`,
  which `framed_of_sites` and its callers read; the witness costs one
  existential and keeps their statements.
- **The charges of a step** (`step_kind_charged`, `frameKinds_flow`,
  `probeProtocol_charged`, `componentProtocol`): a step of $`C`$'s code
  changes an old location only at a kind and key the flow's charges hold.
  They keep the locations a path passes.
- **The top of the request's run** (`TopRuns.step`, `FramedReturns.lean`):
  every step of the frame keeps the request's graph code at the top of the
  term. Its case analysis carries the slot-copy invariant.

One mechanism is new: a must-analysis of the paths of entry values that
slots hold, with its decided check, an instance of the pattern of a
computed proposal and a proved check (`capClose`, `capClosedB`). The flow
cannot serve: it records the sites a slot's value may reach, which do not
identify the value.

### The rule as the paper states it

At a call node $`l`$, for each $`(r:\delta)`$ of the support and each part
$`p=(s,\kappa,k)`$ of $`r`$ at $`l`$, the frame's check requires
$`\Psi(p)\sqsubseteq\delta`$ always, and $`\gamma\sqsubseteq\delta`$ for
each $`(r':\gamma)\in\Phi`$ not apart from $`r`$ where $`s\in O`$ and
$`r`$ is not read as protected. A region is read as protected when each of
its locations of a site of $`O`$ has a crossing in of the active call that
reached it read-only (§4.1, after Definition "The marks of a flow"); a
location is reached read-only from a crossing at $`T`$ when a chain of
field and element reads from the value to it has a prefix ending at a
read-only position (§2, "Crossing"). Section 1's module reads
`const w = h.widths` and keeps $`i<\mathit{len}(w)`$ across the visit, the
spine of `w` reached read-only from the crossing of `h` at `H`
(Example "The module above", `ex:ro`). Example "A member writing another
key" (`ex:rokey`) is accepted: both regions of $`h.\mathit{flags}`$ are
read as protected and $`\Psi_C\sqcup\Theta_C=\mathsf{keep}`$ at their
parts. Example "A member writing the same key" (`ex:rosamekey`) is
refused by the first line, whatever the reading: $`\Psi_C`$ is
$`\mathsf{any}`$ at $`(s,\mathsf{F},\mathtt{flags})`$.

In the model, a region $`r`$ is read as protected at a state `st` with
environment $`\rho`$ when every location $`\ell`$ of $`r`$
(`r.mem ρ st.s.h ℓ`) with `st.g.Lent ℓ` has `Witness view 1 st ℓ`: a
crossing into $`C`$ at a type $`T`$ of a value $`v`$ at a heap $`h`$
reached $`\ell`$ read-only (`ReachRO`) while $`\ell`$ was lent, and the
history has grown inside the call since (`Grows 1`). This is the premise
`framed_of_sites` reads.

### The crossings an entering step records

The view reads a type read-only by membership in `spec.readOnly`
(`FramedSpec.view`). Recording the $`j`$-th argument at `r.inputs[j]`, the
request's declared type, would widen the recorded protection beyond
Assumption "Clients" in two ways:

- a function of $`C`$ whose realized code is the request's enters the same
  code (`entered`), its arguments then recorded at the request's types,
  read-only where the request declares read-only and the other function
  writable (`walk(xs: readonly number[])` and `walkAgain(xs: number[])`
  of one body);
- a writable parameter whose calculus type equals a read-only one's (`W =
  { flags: number[] }` beside `H = { readonly flags: readonly number[] }`,
  equal once `readonly` is erased) is recorded at a type the view reads
  read-only.

Either way the history would protect storage the client may change, and
the headline's
hypothesis (each outside step keeps $`\Theta_C`$ at the history) stronger
than Assumption "Clients". The recorded crossings are the paper's:

- **The read-only positions** `roPos j` (`FramedSpec.roPositions`, a
  field of the plan the decoder computes as `readOnlyPositions` and
  `roPositionsB` checks; it is on no document): position $`j`$ is
  read-only where it is below the arity and the member and every module
  function of $`C`$ whose code in `codes` is the request's realized code
  declare it read-only throughout (`declaredReadOnly`: `memberShapes`,
  `shapeReadOnly`). This is the meet of the draft's `sharedParamTypes`,
  by position. The meet reads the module functions `names` lists; the
  component's restriction that no module function creates a closure
  leaves the natives' models as the only other closures of $`C`$'s code,
  and a model's code equal to a request's realized code is not read.
- **The recorded type** (`entryTy`): `entryXs` records argument $`j`$ at
  `r.inputs[j]` where `roPos j`, and at `spec.outType` otherwise, the
  writable type the outgoing crossings use; `readOnlyB` states that
  `spec.readOnly` holds exactly the inputs at the read-only positions
  (`readOnlyInputs`) and not `spec.outType`. A writable position is then
  recorded at a type no view reads read-only, whatever its calculus type
  equals.

`FramedSpec.readOnly_declared` states: every crossing an entering step
records at a type the view reads read-only is the argument at a position
$`j`$ below the arity, at `r.inputs[j]`, which the member and every module
function sharing the realized code declare read-only
(`FramedSpec.roPositionsB_sound`). The proofs reading `entryXs`
(`entryXs_into`, `entryXs_root`, `chk_entry_sim`) read only its direction
and values, which are unchanged.

### The decision

**Paths of entry values** (`FramedPaths.lean`). A path $`\pi`$ is a list
of keys, each read by the calculus's `readAt f`: an own field, or the key
read from the `[[proto]]` field's value, or `undefined` where neither is
present (`ReadKey`, mirroring `Step.readField`, `Step.readProto` and
`Step.readMissing`). `Reads h v π u` states that the reads of $`\pi`$
from $`v`$ at the heap $`h`$ give $`u`$; `undefined` reaches nothing. An
element read (`elemAt`) reads a cell its index selects, which no
proposal can name: a slot bound to one has no copy entry. Each location a
read passes is named with the value holding it and its **step**, the
region that location is a member of at the holding value: `field 0 f` for
an own field, `field 0 [[proto]]` for the prototype field (`KeyLoc`,
`ReadsAt`; `keySteps f`, `pathSteps π`). A step fixes the location's
kinds and key (`Region.bound_sound`, `regionKeys_sound`), so its parts are
read at the step, at any site.

**The slot copies** $`\mathit{cp}`$ (`FramedCopies.lean`; a table of
entries per label, `CopyTable`): $`(i,j,\pi)\in\mathit{cp}(l)`$ states
that at every run of $`m`$ at label $`l`$ reached from the request's start
with slots `L₀`, while the locations the reads of $`\pi`$ from
`envOf L₀ d₀ j` read at $`h_0`$ keep their contents, slot $`i`$ holds the
value `u` with `Reads h₀ (envOf L₀ d₀ j) π u`. `copiesB Pe Pk start arity
cp` decides it:

- each entry of $`\mathit{cp}(\mathit{start})`$ is $`(j,j,[])`$ with
  $`j`$ below the arity;
- for each node $`l`$ and each edge from it (`nodeEdges`: the targets of
  its continuation, `bind`, `effect`, `branch`, `branchBind` and
  `tagBind`, and its handler), each $`(i',j,\pi)`$ of the target's label
  has the slot the edge reads for $`i'`$ (`srcOf` of the target's
  mapping, over `L`, or over `v :: L` for a bound edge, `envMap_src`)
  either a slot $`i`$ of `L` with $`(i,j,\pi)\in\mathit{cp}(l)`$, or the
  bound value `v` of a `bind` or `tagBind` edge of a node whose expression
  is `.var i` or `readAt f (.var i)`, with $`(i,j,\pi_0)\in\mathit{cp}(l)`$
  and $`\pi`$ respectively $`\pi_0`$ or $`\pi_0`$ followed by $`f`$
  (`boundEntryB`). A handler's bound value, a branch's Boolean and every
  other bound value have no entry.

The proposal `copiesOf` (unproved: a must-analysis intersecting along the
edges from the start's diagonal, paths at most a bound long) is used where
`copiesB` passes, and the empty table, which passes, otherwise. `const g =
h` binds `.var`, so `g`'s slot gets `(j, [])`; `const w = h.widths` binds
`readAt "widths" (.var h)`, so `w`'s slot gets `(j, [widths])`; `h = w`
maps `h`'s slot from `w`'s, whose entry names the other parameter.

**A region read as protected** (`FramedReading.lean`). A region $`r`$
names a slot (`regionSlot`: $`x`$ of `field x k`, `path x p k`, `spine x
p`, `cells x` and `pathCells x p`; that of $`r`$ for `inCls r c`; none for
`fields`, `pathFields`, `cls` and `all`, which `frameCheckAt` refuses) and
the steps of the locations its membership reads from the slot's value
(`regionSteps`: `field 0 f` for each own field of its path, and for cells
the spine they are read from, `field 0 []` and `spine 0 []`).

At a framed node $`l`$ of the request's code $`m`$, with $`\Psi_C`$ =
`componentProtocol F lay`, $`r`$ is **read as protected**
(`protRegionB Ψ_C cp arity roPos m l r`) when $`\Psi_C`$ keeps the parts of
$`r`$'s steps (`stepsKeptB`) and at every node $`l'`$ sharing $`l`$'s
continuation and handler (`sharingNodes m l`) some
$`(\mathrm{slot}(r),j,\pi)\in\mathit{cp}(l')`$ has:

- **(C) a read-only position**: `roPos j`, $`j`$ below the arity;
- **(P) the path kept**: $`\Psi_C`$ keeps the parts of the path's steps
  (`stepsKeptB Ψ_C (pathSteps π)`).

A step's parts are those at a kind its bound holds and a key of the step,
at the site `none` (`stepKeptB`); $`\Psi_C`$ is the same at every site but
a local one, and no location a crossing in reaches is of a local site
(the entering step's `CrossOk`). $`\Theta_C`$ keeps every part
(`thetaKeepB`, checked at every framed plan), so $`(\Psi_C\sqcup\Theta_C)
(p)=\mathsf{keep}`$ exactly where $`\Psi_C(p)=\mathsf{keep}`$, which holds
at a part of no local site exactly where no write of $`C`$'s code or
native step model is charged at its kind and key (`probeProtocol`). With
the plan's view a read-only type is read-only at every path
(`TypeView.roPath_iff`, `ro_at`), so a prefix ending at a read-only
position is the whole path from the parameter.

### The theorem chain

Each step is **to be proved** unless marked proved, its plan from the
proved results named.

0. **The recorded crossings** (proved; `FramedSpec.lean`,
   `PassUnitMember.lean`). `roPositionsB_sound`: where the binding checks pass, `roPos j` holds
   exactly when every function of $`C`$ sharing the realized code declares
   position $`j`$ read-only; `readOnly_declared` restated as above.
1. **The history at the start** (proved; `ReadOnlyCallFrame.lean`,
   `FramedSpec.lean`). `crosses_witness`: after a sequence of crossings
   from a uniform history with $`d\ge 1`$ sets, a released or outside
   location an incoming crossing reaches read-only has `Witness view d`,
   of which `entryStart_witness` is an instance; `FramedSpec.truncate_prot`
   (`(truncate g).Prot ℓ ↔ g.Prot ℓ`) and `FramedSpec.truncate_grows`
   (`Grows 1 g (truncate g)` where $`1\le\lvert g.A\rvert`$).
2. **Witness growth from a start** (proved; `ReadOnlyCallFrame.lean`).
   `ClientFrame.grows_of_start`: at a call of the frame whose term's top
   is a run of $`C`$'s code (`TopC`) and whose start meets `StartInv`, the
   history grows at depth `1` from the start's to every state reached with
   the call active (`ex_depth`, `ex_xstep`, `Ex.grows`);
   `witness_of_start` carries a witness along it (`Witness.grow`), and
   `witness_reached` is its instance at `entryStart`.
3. **The entry's slots** (proved; `FramedProtection.lean`).
   `enter_call`: an entering step from a term with no pending binding of
   $`C`$'s runs is, in an evaluation context, a call or a `new` of a
   closure of the pushed run's code from a position of outside code (the
   term's active frame and redex, `activeFrame_pathAt`), keeping the heap,
   the run's slots `recv :: parameters n args ++ caps ++ [self]`;
   `FramedSpec.prologue_run` (the prologue's two steps, as
   `prologue_det`); `FramedSpec.enter_args`: at `spec.EntryAt r k W h t
   a₂`, `t = gotoOf r.program r.start L d r.comp`, the heap is the
   entering state's, and for $`j`$ below the arity `envOf L d j` is
   `undefined` or the crossing `⟨.into, entryTy r j, envOf L d j⟩` the
   entering step records. The closure's arity is the plan's by a new
   binding check, `arityB` (the realized code's layout has the plan's
   arity, and the arity is at most the inputs'), read through layout
   provenance at the program's state.
4. **The start's protection** (proved; `FramedSpec.start_protects`). At
   such an entry, from a configuration at it, for $`j`$ below the arity
   with `roPos j`, every location `envOf L d j` reaches in `h` is
   allocated, of no local or internal site at the truncated start (the
   entering step's `CrossOk`), `RowProtects` there (exposed and in `E` by
   `Ghost.crosses_covers`, or released or outside and protected), and has
   `Witness view 1` there where it is released or outside storage
   (`crosses_witness` at the entering step's history, read-only since
   `readOnlyB` puts the input at a read-only position in `spec.readOnly`;
   `Ex.grows` over the prologue at the program's frame,
   `progFrame_chkSound`, `reached_ok`; `truncate_grows`).
5. **Paths and regions** (proved; `FramedPaths.lean`). `readKey_reach`,
   `reads_reach`: a read's value is reached from the value read
   (`ValReach`: the value itself, or the contents of a location a path
   from it reaches), or is `undefined`; `keyLoc_reach`, `readsAt_reach`:
   a location a path reads is in a value reached, a member of a step of
   the path there; `readKey_congr`, `reads_congr`: at a heap agreeing
   with $`h_0`$ on the locations a read reads at $`h_0`$, the read is
   $`h_0`$'s; `reads_snoc`, `readsAt_snoc`: a path extended by one read.
   The prefix of a region is stated by the locations its membership reads
   from its slot's value (`RegionReadsAt`: its path's own fields,
   `OwnAt`, and for cells the spine they are read from, `SpineAt`), with
   their steps (`regionSteps`); `region_reach`: at a heap agreeing with
   $`h_0`$ on those, every location of the region is reached from the
   slot's value at $`h_0`$; `regionReadsAt_reach`, `spineAt_mem`: each
   read location is a member of a step of the region in a value reached.
6. **A kept location** (proved; `FramedKept.lean`).
   `ClientFrame.kept_step`: a step of the frame from a reached state whose
   term holds no write outside every frame keeps the contents of an old
   location the history protects (`RowProtects`) where
   $`\Psi_C`$ keeps its kind and key (read at site `none`, where
   `componentProtocol` is `any` exactly at a charged kind and key): a step
   of outside code by the client obligation (`Row`, $`\Theta_C`$ keeping
   every part); a step of $`C`$'s code by `step_kind_charged`, its frame
   the path's innermost (`activeFrame_tag_ne`), its kinds within
   `flowKinds` (`frameKinds_flow`), and `probeProtocol_charged`; a step
   changing the calls of $`C`$ active keeps the heap
   (`depth_of_heap_ne`). `ClientFrame.kept_along`: from a call's start at
   a run of $`C`$'s code meeting `StartInv`, a set of locations allocated
   and protected at the start, at kinds and keys $`\Psi_C`$ keeps, holds
   the start's contents at every state of the execution, the protection
   kept by the growth of the history (`XStep.grows`), the sites by
   `next_site` and the kinds and keys by `kindAt_kept`, `keyAt_kept`.
   The protection at the start is `start_protects` (step 4).
7. **Slot copies** (proved; `FramedCopies.lean`). `CopyInv` at a term
   of the request's run, for a set `K` of locations: a `goto` at label
   $`l`$ with slots of values holding $`\mathit{cp}(l)`$'s entries whose
   reads read only locations of `K` (`SlotsHold`, `EntryKept`); a frame
   of a node $`l'`$ with its continuation and handler, its slots holding
   $`\mathit{cp}(l')`$'s entries and its term what its expression makes
   it (`TermHolds`: the slot's value for `.var i`, a `Stage` of the read
   for `readAt f (.var i)`, read at $`h_0`$ where its locations are in
   `K`); or a term taking no step. `copyInv_step`: every step of the term
   at a heap agreeing with $`h_0`$ on `K` and holding values keeps it,
   by the step rules of `goto` and `frame` (`edge_holds`,
   `copiesB_node`, `reads_snoc`, `readsAt_of_keyLoc`); `copiesB_start`:
   the start's diagonal holds; `copies_along`: along an execution whose
   stepping states agree with $`h_0`$ on `K`. A research `#guard` checks
   the proposal at a walker reading `const w = h.widths` (retired in
   piece 9).
8. **The path and prefix unchanged** (proved; `FramedReading.lean`).
   `stepKeptB` decides (P) at a step: every part a location of the step
   may have, at a kind of its bound and a key of the step, at the site
   `none`, is kept by $`\Psi_C`$; `stepKept_part`: then $`\Psi_C`$ keeps
   each such location's part (`Region.bound_sound`, `regionKeys_sound`).
   `ClientFrame.region_reached`: from a call's start at a run of the code
   meeting `StartInv`, whose slots below the arity at read-only positions
   reach only protected locations (step 4), along an execution to a frame
   of the code, some node $`l''`$ with the frame's continuation and handler
   has, for each entry $`(i,j,\pi)`$ of its table with $`j`$ read-only and
   `stepsKeptB` at `pathSteps π`, every location of a region of slot
   $`i`$ with `stepsKeptB` at its `regionSteps`, at the frame's slots and
   heap, reached from argument $`j`$ at $`h_0`$. The set the arguments at
   read-only positions reach at kept parts holds its contents along the
   call (`kept_along`), so the copies hold (`copies_along`) and the
   region's read locations are unchanged (`region_reach`).
9. **The witness at a framed node** (proved; `FramedReading.lean`).
   `ClientFrame.prot_witness`: at a frame of the code entering node $`l`$,
   reached from a call's start whose read-only arguments reach only
   protected locations, witnessed where released or outside storage,
   every released or outside location of a region `protRegionB` reads as
   protected at $`l`$ is reached from the argument at $`h_0`$
   (`region_reached`), so witnessed at the start and, the history growing
   inside the call, at the frame's state (`witness_of_start`, `ex_sites`).
   `FramedSpec.prot_witness`: the same at the plan's frame, the start's
   protection by `start_protects`, at a checked table; `copiesOf_sound`:
   the proposal's table is checked.
10. **The returns with protection** (proved; `FramedReturns.lean`,
    `FramedStarts.lean`). `ClientFrame.ProtWitness`: at every reached
    state entering a framed node $`l`$, each lent location of a region
    `prot l` reads as protected has a live witness at depth `1`;
    `framed_of_check` takes `prot : Nat → Region → Bool` and that premise,
    its check at `prot l`; `ret_reachedW_of_checks`,
    `ret_reachedW_of_charges`, `ret_reachedW_of_entries`,
    `ret_reachedW_frame`, `ret_reachedW_spec` and `ret_reachedW_public`
    carry both. `framedReturns_reached` (`FramedReached.lean`) reads them at
    the pass's checks, discharging the premise by
    `FramedSpec.prot_witness` at `protRegionB`. The headline
    `PassUnit.mode8Accepted_sound` and its premise `Mode8Accepted` are
    unchanged.

### The pieces in commit order

Each piece is one commit with its record. Sizes are lines of Lean,
estimated from the proved lemmas each mirrors.

| # | Piece | Proves | Size | Tests |
| --- | --- | --- | --- | --- |
| 0 | The recorded crossings at the read-only positions | `roPositions`, `roPositionsB`, `entryXs` at `outType` off them, chain 0 | 150–250 | `lake build`; `node tests/json-field-names.mts` (no document changes: the decoder computes `roPositions`); `node pipeline/run-cases.mts framed`, `readonly-frame`, `bounds-pattern` unchanged; the shared-code twins below as cases, refused as before |
| 1 | The history at the start and witness growth | chain 1 and 2, `entryStart_witness` and `witness_reached` as instances | 100–150 | `lake build` of the two modules |
| 2 | The entry's slots and the start's witness | chain 3 and 4 | 250–350 | `lake build` |
| 3 | Paths and regions | `Reads`, `pathParts`, `prefixRegions`, chain 5 | 300–400 | `lake build` |
| 4 | Kept locations | chain 6 | 200–300 | `lake build` |
| 5 | Slot copies | `entryCopies`, `copiesB`, `copiesOf`, chain 7 | 450–600 | `lake build`; a research `#guard` that `copiesOf` of the alias case's walker gives `w`'s slot `(0, [field widths])` at the visit, retired in piece 9 |
| 6 | The path and prefix unchanged | chain 8 | 200–300 | `lake build` |
| 7 | The decision and its witness | `protRegionB`, chain 9 | 150–250 | `lake build` |
| 8 | Protection threaded, read nowhere | chain 10 at `prot` false at every reader | 100–150 | `lake build`; `run-cases.mts readonly-frame`, `framed`, `bounds-pattern`, every expectation unchanged |
| 9 | Protection read | `protRegionB` at `supportKeptB`, `supportFailure`, `framedNodeOkB`, `framedNodesAt`, `framedNodesWhy` and `framedSupportsAt`; the cases and controls below | 50–100, the cases and controls | the cases below; `node tests/node-runs.mts`; `make test-checks` for the controls; `run-cases.mts readonly-frame`, `framed`, `bounds-pattern`; `make test` before the merge |

Lean in all: 1950–2850 lines. Pieces 1 to 8 change no acceptance; piece 0
changes the recorded history and no verdict; piece 9 changes acceptance.

### Tests

Each walker reads `h.flags[i]!` (or the region named) across `visit(i)`
under the invariant `h.flags.length === n`, with `n = h.flags.length`;
`H = { readonly flags: readonly number[] }`, `W = { flags: number[] }`.
A visitor states `{ values: "keep"; spines: "any" }`, so only protection
keeps a spine fact (`{ values: "any"; spines: "any" }` is refused at the
gate). Each negative's program is unsafe under Node: the named client
makes the walker read past the array (`NaN`), run by
`tests/node-runs.mts` (observed under Node 26.13.0 for the reassigned,
shared-code and depth-two programs as JavaScript transcriptions: `NaN`;
the alias program returns its widths).

| Case | Outcome | Shows |
| --- | --- | --- |
| `readonly-frame-other-key` (`ex:rokey`) | accepted under client trust | protection at keyed parts; (P) at `flags` with `rename` charged at `label` |
| `invalid-readonly-frame-same-key` (`ex:rosamekey`) | negative, kept | the protocol at `flags`, whatever the reading |
| `readonly-frame-param-protected` | accepted under client trust | `walk(h: H, visit)`: the spine of `h.flags` read protected |
| `invalid-readonly-frame-param-writable` | negative | `walk(h: W, visit)`: no read-only position; the client pops `h.flags` |
| `invalid-readonly-frame-param-partly-readonly` | negative | `h: { readonly flags: number[] }`: the field read-only, its array writable, so the type is not read-only throughout (the plan's view); the client pops `h.flags` |
| `readonly-frame-param-positions` / `invalid-readonly-frame-param-positions` | accepted under client trust / negative | `walk(h: H, w: W, visit)`, `H` and `W` equal once `readonly` is erased: the fact over `h.flags` kept, the fact over `w.flags` dropped; the client pops `w.flags` |
| `readonly-frame-shared-code` / `invalid-readonly-frame-shared-code` | accepted under client trust / negative | two exported walkers of one body: both `xs: readonly number[]`, accepted; one `xs: number[]`, position 0 not read-only in the meet, both refused; the client calls the writable twin and pops its array |
| `readonly-frame-local-alias` | accepted under client trust | Section 1's `const w = h.widths` (`ex:ro`): `w`'s slot holds `(0, [widths])` |
| `readonly-frame-param-copy` | accepted under client trust | `const g = h`: `g`'s slot a copy |
| `invalid-readonly-frame-param-reassigned` | negative | `walk(h: H, w: W, visit)` with `h = w` before the loop: `h`'s slot names `w`; the client pops `w.flags` |
| `readonly-frame-depth-two` / `invalid-readonly-frame-depth-two` | accepted under client trust / negative | `h.inner.flags` with `H2 = { readonly inner: H }`: kept; with a member `swap(h)` writing `inner` (charged at `inner`), (P) fails at the path's first field; a visitor calling `swap(h)` makes the walker read past the new array |
| `readonly-frame-cells` | gap | an element fact `forall k in items: … items[k] < widths.length` over the cells of `items = h.items` across a visitor stating `{ values: "any"; spines: "keep" }`: the fact's support names a region of a class, which the frame's check gives no sites (`regionSites`), so the node drops it before any reading |
| `readonly-frame-handler` | gap | `try { visit(i) } catch { s += h.flags[i]!; }`: the copies hold across `frameHandle`'s bound slot, but the framed returns claim a support at a normal return only (`RetAt`), so the catch block lacks the fact |

Controls:

- **Mutation controls** (`tests/single-pass-mutations.mts`,
  `tests/single-pass-controls.mts`): `fr-protected`, a verifier whose
  `protRegionB` reads every region as protected, accepts
  `invalid-readonly-frame-param-reassigned`; `fr-ro-sharing`, one whose
  `sharingReadOnlyB` passes, so a position reads the member's own shape
  alone, accepts `invalid-readonly-frame-shared-code`'s `walk`. Each shows
  the check is what refuses.
- **(P) at a region's prefix** (`Tests/FramedBindingControls.lean`): no
  support the pass derives names a spine without its field region, whose
  own check refuses first, and a forced support omitting the field leaves
  the fact unsupported, so the walk refuses before the node's check; the
  decision is shown at `protRegionB` itself: with slot 7 copying a
  read-only argument, `spine 7 ["flags"]` is read as protected at a
  protocol keeping every part and unprotected at one charging the field
  `flags`, and a copy along `flags` is unprotected there too.

### Restrictions of the protected reading

Where the note's rule is wider, the code reads a region unprotected and
keeps the frame's check; each is sound and gives up acceptance only.

- **Read-only positions** (`readOnlyPositions`): a parameter is read-only
  where its declared shape is read-only throughout; the note's "a prefix
  ending at a read-only position" is read at the whole parameter.
- **Copies** (`copiesB`): a slot holds a copy along own and prototype key
  reads at most `copyBound` (4) long; an element read gives none.
- **Sites** (`stepKeptB`): (P) is decided at the site `none`, so for every
  site but a local one.
- **Witnesses**: only an entry's arguments witness protection; a callback's
  result and a caught value protect nothing.
- **Callees** (`calleeArgB`): a node's regions are read as protected only
  where its callee is an argument's own value at every sharing node, a
  function the client passes; a callee read from storage may be a native.
- **Natives the realm does not model** (`nativeSites`, `nativeProtocol`):
  the framed realm models `[[Array.prototype]]` with no fields, so a call
  of C's code whose callee may be outside code and is no argument's own
  value (`a.pop()`, `a.fill(1)`, `out.push(x)`) is charged `any` at every
  part its callee, receiver and actuals may reach, in every framed node's
  protocol and in (P). The note charges each native's stated effect at its
  receivers' parts, which is narrower: Section 1's printed module, whose
  `prepare` fills the array `walk` reads, is refused here
  (`readonly-frame-local-alias` is the module without `prepare` and with a
  sum in place of `push`). The Lean model runs no such native, so these
  charges are read by the checks and by no theorem of the model: the
  theorems hold of any protocol joined to $`\Psi_C`$
  (`nodeProtocolOf_ge`, `protRegionB_mono`).
- **Exports** (`tools/components.mts`): a module exporting a value binding
  that names one of its functions or classes (`export const g = f`) has an
  unknown interface, and no framed plan reads it.

### What milestone 2 trusts

No trust row is added. A unit accepted through a protected region relies
on $`\Theta_C`$ (the row owner-approved on 2026-11-19) at storage the
history protects: a client keeps the row at what an entry's argument
reaches read-only at its declared type, through its own writable alias
too (Assumption "Clients"; Example "Storage passed in read-only"). With
piece 0 the history protects what a crossing reaches only at a position
every function sharing the entered code declares read-only, so the
headline's hypothesis is Assumption "Clients" at the declared types.
The read-only positions are read from the family's declared shapes, part
of the binding of the plan to the checked file (an existing row), with
`roPositionsB_sound` proved of it.

## Milestone 3: the contexts of known calls

A module function that is no entry is checked at the flow's contexts of
its known calls, as [Read-only frames](readonly-frames-note/note.tex)
states it in (B1) and (B4), with the argument of its item "(B1), (B4) at
known calls". The test is the note's Example "A walker that is no entry"
(`bounds-pattern-framed-inner-walker`): `walk` is internal, and the
export `countLines` calls it with an arrow of its own.

### The existing mechanism this extends

Four mechanisms, each kept, each changed at one place.

1. **The flow of sites** ([Read-only frames](readonly-frames-note/note.tex)
   §3, Theorem "Flow"; `FFlow.check_sound`). Its contexts already give a
   code one proposal per known call site (`solveStart`, `invokeSites`).
   Two of its rules decide inner-walker before any context is read:
   - **A closure a node expression creates** is lowered code
     (`Lowered`, the note's "The code of every closure created is
     lowered"): its token in $`O`$, its code open, its capture slots
     holding $`O`$. The check reads it at `initC`'s creation of every
     module function whose code creates a closure (`lowB`). A proposal
     holding the tokens of the entries alone in $`O`$ fails it at
     `initC`'s node creating that module function's closure (observed,
     the cause of the gate "No closure creation"): the check is right and
     such a proposal incomplete. The solver proposes each lowered
     closure's token in $`O`$ and its capture slots grown with $`O`$ at
     every context (`SolveCode.lowered`); the proposal is untrusted, and
     `FFlow.check` reads it as any other.
   - **The value of a closure creation names the signature of its
     code** (the note, "Signatures"). Read so, `initC`'s slot holding
     `walk`'s closure names `walk`'s signature, and `countLines`'s
     capture of `walk`, which names it, meets its open fit; a creation's
     value naming no signature fails it (the cause of the gate "No linked
     capture"). The rule `Fits.frameC` reads a node value naming
     $`\sigma`$ as a term computing a closure of $`\sigma`$ (`FnTm`: a
     closure of $`\sigma`$, or its creation), kept by every step
     (`FnTm.step`), so the value it returns is one (`FnTm.fnIs`);
     `CodeChk` and its decision `vfnB` admit a creation of $`C`$'s code
     at its own signature, and the solver carries it (`creationIx`).
     Module functions naming each other in a cycle stay refused: `initC`
     creates each closure after those it names, and the note's creation
     of a group is conj.
2. **The framed call nodes** ((B1); `framedCallNodes`). A call is framed
   where its callee set holds $`\circ`$ or its segment reaches outside
   code. The note adds a callee that is a slot naming no signature and
   holding a token (`outsideCalleeAt`): a closure of $`C`$ that the call
   reads by no specification. A native's slot names its step model's
   signature, so a native call is not framed by this clause.
   Framing more nodes is sound: the framed walk is proved for any set of
   framed nodes whose checks pass.
3. **The binding checks** ((B4); `FramedSpec.bindingChecks`). The open
   entry `entryB` is read where $`f`$ is an entry or its token lies in
   $`O`$. Where $`f`$ is no entry and its token lies outside $`O`$ (`innerB`,
   the plan's `inner` tied to the checked file), `entryB` is not read;
   after the walk, a check of the request (`requestB`) reads the realized
   code's returns within $`O`$ at every context (`retsInB`, a gate
   narrower than the note's (B4), which states none);
   and no region is read as protected (`protAt` false): no argument of a
   known call crosses in. (B2)'s sets and the frame's check at each framed
   node already read every context of the code (`operandSets`,
   `framedNodesAt`), a superset of the contexts at which $`f`$ is checked:
   the extra context $`0`$ of a code no caller enters holds empty sets.
4. **The calls the claim is about** ([the frame of a
   request](#the-calls-the-claim-is-about); `FramedSpec.frame`). The
   frame's entries are realized public calls (`PublicCall`: an entering
   step from outside code). For a function that is no entry with its token
   outside $`O`$, outside code holds no closure of it (Theorem "Flow"), so
   no public call of it exists and that claim says nothing. Its frame's
   entries are every call of its realized code a program makes
   (`FramedSpec.Called`: a step keeping the obligation into the closure's
   entry, from any code), from an initial configuration along steps keeping
   $`\Theta_C`$.

### The theorem

`mode8Accepted_sound` is unchanged in statement. Its framed branch,
`FramedRequestSafe r (spec.frame r)`, reads the frame, whose entries are
`EntryAt`, now over `Called`:

```math
\mathrm{Called}(x_0,n,x,a_1) \iff \mathrm{Initial}(x_0) \wedge x_0 \to^{n} x \wedge x \to a_1 \wedge (\neg\mathit{inner} \Rightarrow \mathrm{Entering}(x,a_1))
```

with $`\to`$ a step keeping $`\Theta_C`$. At `inner` false it is
`PublicCall`, and the frame is milestone 2's. At `inner` true it is every
call. The proof reads the entry's fit from the program's flow at every
reached state (`progOk_ex`, `fits_ctx`), as for a public call: the
realized code's run fits at the context of its frame (`Fits.gotoC`),
whatever code made the call (`entry_hole`). A public call puts the run at
a position of outside code, so its returns lie within $`O`$
(`enter_hole_out`); a call from $`C`$'s code puts it in a frame of $`C`$,
and the returns lie within $`O`$ by `retsInB` (`RetsIn`). The witnesses of
milestone 2 read the entering step's crossings (`enter_args`), at `inner`
false; at `inner` true no region is read as protected
(`ProtWitness.none`). The rest of `framedReturns_reached` reads the
entry's fit and its reach alone (`Called.ex`).

So the note's headline (B5) at the contexts of known calls is proved,
under the code's gates: the verdict of $`f`$ covers every call of $`f`$'s
code in every program the claim is about, the context of each call one of
the flow's contexts of $`f`$'s code.

### A call of the component's own closure

(B1) bounds a framed call of a closure of $`C`$ by the charges of its
segment. The check reads one bound at each framed node $`l`$
(`FramedSpec.boundAt`, `callBound`):

1. **A call of an argument's own value at an entry** (`clientCallee`: a
   request checked at its entry, the callee an argument's own value,
   `calleeArgB`): the callee's stated effect $`\Phi`$, by the callback row
   of $`\Theta_C`$, "a function value outside code passes at a function
   type meets that type" (`CallbacksWithin`). The argument may also be a
   closure of $`C`$ that $`C`$'s own code passes to the entry (an exported
   walker called by the component with an arrow of its own), which the
   row covers too. The frame's check reads
   $`\Psi_c(l)`$ at a part that may lie in $`R_C`$ and $`\Phi`$ at one that
   may lie outside it (`frameCheckAt`).
2. **Any other call, where no node of the flow may call outside code**
   (`noOutB`: `CodeFlow.out` false at every node of every code at every
   context): the segment's charges. The segment changes every location
   below the call's heap within $`\Psi_c(l)`$, in $`R_C`$ or not, and the
   check reads $`\Psi_c(l)`$ at every part (`frameCheckOwnAt`).
3. **Any other call**: the top effect, the frame's check of 1 at
   $`\Phi = \top`$ (`Closed.top`), its action holding of every admissible
   transition (`action_top`).

A mixed segment, the component's code calling outside code
(`bounds-pattern-framed-mixed-local`, `u-q1-through`), is bound 3: the
charges bound $`R_C`$, the top effect every other location.

**The existing mechanisms this extends.**

1. **Whether a run at a node may call outside code** (`CodeFlow.out`,
   `Fits.outCall`): a frame whose next step calls outside code fits at a
   node whose `out` holds, the callee set holding $`\circ`$ only there
   (`outB`).
2. **The transfer at a call** (`transfer_at`, `seg_bound`): own steps of
   $`C`$'s code at the caller's depth within $`\Psi_c`$, runs of outside
   code bounded by $`\Theta_C`$, both on $`R_C`$; every other location
   within $`\Phi`$ (`Leads.of_bound`).
3. **The own steps within the charges** (`within_run`, `stepWithin_reach`,
   `stepWithin_charged`): a step whose innermost frame runs $`C`$'s code
   changes a location below the call's heap only where the step charges
   its part and the call's values reach its site.

**Bound 2, proved** (`ClientFrame.segAll_of_deep`, `all_of_fit`,
`supported_of_own`, `nodeTransfer_of_transfer`):

- *No outside run.* A frame or a run of outside code fits only at a
  position that may call outside code (`Fits.frameOut`, `Fits.gotoOut`;
  the call of a closure of outside code reads the premise of
  `Fits.invoke`). Where every node's `out` is false, every frame inside
  the top frame's running term runs $`C`$'s code (`Fits.innermostC`), at
  every state of the segment (`fitsAt_reached`).
- *The charges at every location.* Each step of the segment changes every
  location below the call's heap within the protocol from the flow's
  charges and the node's set (`within_deep_all`, `stepAll_reach`,
  `stepAll_charged`: the argument of `within_run`, which reads no
  location's membership in $`R_C`$); the steps compose (`AllBelow.trans`),
  the marks fixing each location's part (`kept_of_kstep`).
- *The check.* $`\Psi_c(l)`$ within each region's change at every part a
  location of the region may have (`frameCheckOwnAt`,
  `ownFramed_of_sites`) gives each support supported.

**The segment's code as lowered.** Bound 2 reads the segment's codes as
the flow lowers them. A lowering is faithful where the unit holding the
code is accepted: a template literal of an object lowers to an addition,
which calls no code, and under Node the conversion calls the object's
`toString` (`invalid-bounds-pattern-framed-template`). A verdict reading
bound 2 at a node rests on the verdict of each module function holding a
code the node's call runs (`FramedComponent.segOwners`, over `segRun`: a
known call enters its signature's code, any other call each code whose
token its callee's set holds, a native step model the codes its own nodes
call), on the verdict line's `depends`; a code of the segment that is
neither a native step model nor of a module function refuses the plan.
The pipeline decides dependencies by what each unit reaches through them
(`verify-source.mts`), so a cycle is decided together: a unit refused of
its own, or with no verdict, refuses every unit reaching it, naming the
dependency on a shortest path and that unit's refusal; otherwise a unit
reaching one accepted under client trust is accepted under the client
obligation, and one reaching none is verified.

**Proof scope.** Bound 2's condition is the flow's, at every node: a
component one of whose nodes may call outside code bounds each call of a
function the client does not pass by the top effect. (B1)'s notion is the
segment's (`reachesOut` over `segCodes`); reading it at the segment needs
the callee sets of a fitting term tied to the flow's `callSets` along the
segment, which is not proved.

### What milestone 3 trusts

The callback row ranges over the calls whose callee is an argument's own
value in a function checked at its entry (`clientCallee`), whoever passes
it: outside code, or $`C`$'s own code calling the entry with a closure of
its own. Any other call of a closure of $`C`$ (a function checked at the
contexts of its known calls, or a callee read otherwise) is bounded by its
segment's charges (bound 2) or by the top effect (bound 3), with no
assumption about that closure.

### Tests

| Case | Outcome | Shows |
| --- | --- | --- |
| `bounds-pattern-framed-inner-walker` (Example "A walker that is no entry") | gap: `walk` refused by its dependency on `countLines` | the visit's callee the arrow's token alone, bound 2 keeping the cursor; `countLines` refused at its call of `walk`, whose arrow writes the captured `stats` (cause not established; a caller whose arrow writes nothing is accepted) |
| `bounds-pattern-framed-known-calls` | gap: `walk` refused by its dependency on `total` | the cursor its caller's, outside the visit's reach at the known call, kept by bound 2; exported, `walk` is refused at the visit (observed); `total` refused at its call of `walk`, its arrow writing the captured `seen` (cause not established) |
| `invalid-bounds-pattern-framed-known-calls` | negative | the arrow moves the caller's cursor, charged at its site; `total([1, 2])` reads past the array (`NaN` under Node) |
| `bounds-pattern-framed-arrow-exceeds` | gap: `walk` refused by its dependency on `countLines` | the arrow writes beyond its type's effect; bound 2 keeps the walker's array and cursor; `countLines` refused at its call of `walk` |
| `bounds-pattern-framed-made-visitor` | `walk` and `total` accepted under client trust | bound 2 at an arrow `mk` makes: `walk` rests on `mk`, verified, `total` on `walk` |
| `invalid-bounds-pattern-framed-template` | negative | bound 2 at an arrow whose template literal lowers to an addition; `walk` refused by its dependency on `total`; `NaN` under Node |
| `invalid-bounds-pattern-framed-construct` | negative | the arrow constructs a client's class: bound 3, the client's array may shrink; `NaN` under Node |
| `bounds-pattern-framed-mixed-local` | `walk` accepted under client trust | a mixed segment, bound 3: the walker's own array and cursor lie in $`R_C`$, kept by the charges |
| `invalid-bounds-pattern-framed-mixed` | negative | the same over the client's array, which the top effect may shrink; `NaN` under Node |
| `bounds-pattern-framed-closure` | accepted under client trust | a closure a module function creates and calls |
| `bounds-pattern-framed-shared-helper` | both walkers accepted under client trust, the helper verified | a module function naming another |
| `bounds-pattern-unreachable-handle` | accepted under client trust | a known call of a module function after a framed visit |
| `bounds-pattern-framed-cycle-refused` | gap | the gate on a cycle of names |
| `bounds-pattern-framed-returns-local-refused` | gap | the request check of the returns within $`O`$ (`retsInB`), at a walker returning an object it allocates |

## Outside slots and the initialization, shared with verification

A design, for the owner's review, of how the framed plan reads what a
module function of $`C`$ captures from outside its code (a native, an
intrinsic object, an import, a module cell or constant) and the program
state a client starts from. The framed plan reads each outside slot at the
kind and the contract the ordinary pass reads it at, and adds only the set
of sites its value may be; it reads a call of a native at the native's
stated footprint and by the frame's check, the native's own steps charged
to $`C`$ at the parts its receiver and actuals reach, under two trust rows
on standard natives the owner approved on 2026-11-21; and it states its claim over every initial configuration that
fits the flow, is an entry and meets the outside contracts, a premise in
place of a constructed initialization term. Base: `single-pass` at
`0f2e13844`. Notation is that of the sections above. Each Lean name is
labelled as above: **proved** at the base, **to be proved**, or **trust**.

### The existing mechanism this extends

1. **Outside slots by kind** ([H5b](../SINGLE-PASS-THEOREM.md), section 4,
   "H5b, the outside contracts"; `PassUnitInterfaces.lean`). A module
   function is a `ModuleCode` whose slots are linked (another function of
   the module) or outside (a value per depth). An outside slot's kind
   (`OutsideKind`) is an import read at an established entry
   (`established`), an import read at its declaration (`declared`), an
   import stand-in (`standIn`), a host value (`host`) or a module constant
   or cell (`moduleCell`), and `KindMet` states that every value such a
   slot holds at depth $`i`$ meets the slot's type at every budget
   $`j\le i`$ in every world. `outsideContracts_of_kinds` (proved) gives
   `OutsideContracts` from the five; `established_met` (proved) discharges
   the established kind from the entries' modules; `init_asserted`
   (proved, `PassUnitInit.lean`) gives the `:init` request's assertions at
   its finish states, and the module cell's kind is the conjectured H5b.
   `[[Array.prototype]]` is such a slot, typed at `ArrayProto`
   (`Elaboration.lean`, the input slot `[[Array.prototype]]`), its
   methods' contracts the overlay of `tools/array-prototype.mts`, trusted by
   the row "`Array.prototype` meets `ArrayProto`"
   ([trust surface](../DESIGN.md#trust-surface)); the intrinsics
   (`%ElementAt%`) are typed at the signatures of `tools/intrinsics.mts`,
   trusted by the row "The intrinsics meet their signatures".
2. **A call's effect at the caller**
   ([footprints](../FOOTPRINTS.md#a-calls-effect-at-the-caller)). At a
   call of a callee whose type states a footprint, the pass reads the
   footprint at the caller's slots, $`\Phi`$ (`PromiseCalls.callerFrame`),
   a region at a position the call passes no slot at widening to every
   allocated location, and the callee's semantic type gives that the heap
   from the call to its return is an action of $`\Phi`$ (proved:
   `callerFrame_post`). Each native states its footprint
   ([natives](../FOOTPRINTS.md#natives)), its callback's included, at its
   normal return.
3. **The module's unfoldings** (`PassUnitRealize.lean`). A module's
   functions are realized as their closures unfolded $`n`$ times
   (`approxEnv`, `approx`): a linked slot holds the named function's
   closure one unfolding less, `null` at depth $`0`$, an outside slot its
   value at that depth, and a run of at most $`n`$ steps calls through at
   most $`n`$ closures. `captures_envOk` and `approx_captures_envOk`
   (proved) give a realized function's captures their types at every
   budget up to the depth (`EnvOk`), names that call each other included:
   no order of creation is read.
4. **The frame's flow, charges and executions**, kept as they are: the
   flow of sites and its rule for a call whose callee set holds $`\circ`$
   (Read-only frames §4, Theorem "Flow"; `FFlow.check_sound`,
   `fitsAt_reached`), the charges $`\mathrm{Ch}`$, $`\Psi_C`$ and $`W_c`$
   ([charges](#charges)), the selection of a framed call's bound
   ([a call of the component's own closure](#a-call-of-the-components-own-closure),
   `callBound`), protection ([milestone 2](#milestone-2-the-protected-reading)),
   the history and its crossings ([the history](#the-history-of-a-program)),
   $`\Theta_C`$, and the calls the claim is about (`FramedSpec.Called`,
   `EntryAt`) with their two premises on initial configurations,
   `InitialFits` and `InitialEntry` (`FramedSpec.lean`).

**What the framed plan duplicates.** Each concern below has one mechanism
in the ordinary pass and a second in the framed plan; this design deletes
the second.

- *What an outside slot holds*: ordinary, any value meeting the slot's type
  by its kind; framed, one value per slot name (`realmValueAt`), the names
  admitted by spelling (`hostModel?`, `intrinsicName`, the import gate's
  `%` and `[[…]]`), every other slot refused (`framedRestriction`,
  `PreparedFile.prepareFramedComponent`).
- *`[[Array.prototype]]`*: ordinary, a value meeting `ArrayProto`; framed,
  an object with no field, so no theorem connects a framed unit's array
  natives to their contracts.
- *Natives*: ordinary, each call at its stated footprint; framed, `%ElementAt%`
  as a code of $`C`$ (`hostModel?`, a step model tagged $`C`$) and every
  other native call charged `any` at every part its operands may reach
  (`nativeSites`, `nativeProtocol`).
- *Module functions naming each other*: ordinary, unfoldings at any graph
  of names; framed, closures allocated once in an order where each comes
  after those it names (`initC`, `namingOrder`, `approx_stable` under
  `StableLayout`), a cycle refused.
- *Module cells and constants, imports, several modules*: ordinary, the
  kinds `moduleCell`, `established` and `declared`; framed, refused.
- *The initialization*: ordinary, the `:init` request, checked as a unit;
  framed, a constructed term (`initC`, `componentInit`) whose execution the
  claim starts from (`FramedSpec.Initial`).

A third native model, the read-only handles' family checks
(`ComponentChecks.lean`, `Call.native` and `nativeParts`), is read by no
acceptance; it is outside this change, with its row in
[WORK.md](../../WORK.md#status).
### Two trust rows on standard natives

Approved by the owner on 2026-11-21, rows of the
[trust surface](../DESIGN.md#trust-surface) once piece 2 lands, stated of
every *standard native*: a function the realm defines whose contract is an
`ArrayProto` member, an intrinsic's signature, a stated library type's
member or a host contract.

- **(a) Throws.** A standard native's writes before it throws are within
  its normal-return footprint $`\Phi_c`$: the heap from its call to its
  throw, as to its return, is an action of $`\Phi_c`$.
- **(b) Retention.** A standard native stores its arguments only into what
  its receiver and arguments reach, or into its result, and calls out only
  through the function arguments it is given. Each store of its run is so,
  not only its net change.

With (a) a native call's exceptional edge reads $`\Phi_c`$, not
$`\top`$; with (b) a native's run reaches only its operands, so its call
gives nothing to $`O`$ but through a function argument of outside code.

### The algorithm

**Per component, once.**

1. **The layout.** The module functions of $`C`$'s modules, each a
   `ModuleCode` with its slots and its kinds table, as the ordinary pass
   lays them out (`ModuleLayout`'s `code`, the front's `kinds`). The
   framed plan reads them from the plan; no slot is decided by its name.
2. **The sites of a slot.** The flow gives each capture slot of a module
   function's code at its entry the set of sites its value may be, by the
   slot's kind (`OutsideKind`) or link:
   - a linked slot naming the function $`g`$, and a slot of kind
     `established` whose entry is a module function $`g`$ of $`C`$ (its
     value is $`g`$'s module value, `HoldsModuleValue`): the token of
     $`g`$'s code, the slot naming $`g`$'s signature;
   - a slot of kind `moduleCell`, a `const`'s or a `let`'s binding: the
     cell, captured as that cell, its site the allocation site of the
     binding in its module's `:init` code, of kind cell and key `value`;
   - a slot of kind `established` of another component, `declared`,
     `standIn` or `host` (a native, an intrinsic object, a declared
     global such as `Infinity`): $`\{\circ\}`$, storage of code outside
     $`C`$, naming no signature.
3. **The codes** $`M_C`$: the module functions' codes, the closures they
   create, and each module's `:init` request code, a code of $`C`$ entered
   once at context $`0`$, its import slots at the sets of step 2. No
   native is a code of $`M_C`$. The `:init` codes are read by the flow and
   by no charge: they run before any entry and no closure of them exists,
   so no step of a member's call or of a segment runs them, and
   $`\Psi_C`$ keeps the cell of a `const`.
4. **A call of a native.** A call node of a code of $`M_C`$ calls a native
   where its callee's value is read from an outside slot of kind `host`
   or `declared`, or through one: a member of such a value, read directly
   or through a receiver whose type's prototype is that slot's contract
   (an array's prototype is the value of `[[Array.prototype]]`, the array
   invariant). The code's request decides it from the callee's expression
   (`nativeAt`), and `nativeAt_sound` (to be proved) states the property:
   at a reached state in a frame of the code at the node, under
   $`\mathrm{SlotsMet}`$ and the array invariant, the callee is a closure
   of the realm's code. Its footprint $`\Phi_c`$ is the native's stated
   footprint read at the caller's slots, the $`\Phi`$ `callerFrame` reads
   there. Every node sharing a native call's continuation and handler calls
   a native (`nativeKeysB`, a check): a frame records its node by its key
   alone.
5. **The flow at a call of a native.** With $`L_n(c)`$ the closure of the
   receiver's and the actuals' sets, $`\overline{S_r\cup\bigcup\bar S}`$
   (the callee's set left out, by (b)): its result is in
   $`L_n(c)`$ or the sites of its node's key; every site of $`L_n(c)`$
   stores $`L_n(c)`$ and those sites; every code whose token $`L_n(c)`$
   holds is entered at $`L_n(c)`$ (a callback); and where $`L_n(c)`$ holds
   $`\circ`$, a function argument of outside code, $`L_n(c)`$ enters
   $`O`$ (`Fits.native`, a rule of the flow; `FFlow.check` decides it as
   any rule). A native allocates at its node's key, the sites of $`C`$'s
   frame that called it (`stepSite` reading that frame, Read-only frames'
   "Marks": "a native call's included").
6. **The charges.** $`\mathrm{Ch}(M)`$, for a set $`M`$ of codes of
   $`M_C`$ other than the `:init` codes, is the charges of the writes of the
   codes of $`M`$ (`writesK`, `codeKinds`), and, at each call of a native
   $`c`$ of a code of $`M`$, $`\mathsf{any}`$ at every part of a site of
   $`L_n(c)`$ (`nativeReach`): by (b) a native's own steps change only
   locations its operands reach. $`\Psi_C`$ and $`W_c`$ read
   $`\mathrm{Ch}`$ as [charges](#charges) states; the protocol from
   charges (`probeProtocol`) joins the native reach, which is at sites
   (`chargesProtocol`).
7. **The codes the charges come from** (Fable S4). $`\Psi_C`$'s native
   reach, and whether a node calls a native, are read from each code's
   ordinary request. A code of $`M_C`$ with a call of a native is read so
   only where the unit holding it is accepted and on the verdict line's
   `depends`, as a segment's codes are
   ([a call of the component's own closure](#a-call-of-the-components-own-closure));
   at any other code each of its calls of a native is charged
   $`\mathsf{any}`$ at every part (`nativeTop`), a stated precision limit.
8. **The other gates** stay as [restrictions](#restrictions) states them
   but three: the cycle of names, the audited realm values and the one
   module (with the package's) are deleted. One is added (Fable S3): a
   closure of $`C`$ a native is passed, a token of $`C`$ in $`L_n(c)`$,
   has a code with no framed node and an ordinary verdict (`callbackB`);
   otherwise the plan is refused, located at the call. Reading a framed
   closure at an arrow relative to the client obligation is milestone 5,
   not built.

**Per unit.** (B1) to (B5) of Read-only frames, (B1) reading a call of a
native as a framed call: its run runs code outside $`C`$, the realm's. At
a call of a native a fact is kept where the ordinary pass keeps it at
$`\Phi_c`$ (`callKept`, `frameKeeps`) or where the frame's check keeps it
at $`\Psi_c`$ and $`\Phi_c`$, on both exits (by (a), $`\Phi_c`$ bounds
the exceptional one). The segment's codes $`\mathrm{seg}(c)`$ are closed
under the calls of their members and under the callbacks of their calls
of natives.

**At P22.** `walk`'s slots are `[[Array.prototype]]` (kind `host`, type
`ArrayProto`, sites $`\{\circ\}`$) and `%ElementAt%` (kind `host`, its
intrinsic signature, sites $`\{\circ\}`$). Node 10, `xs[c.i]!`, calls the
native `%ElementAt%`, $`\Phi_c=\mathsf{keep}`$, $`L_n(c)`$ the closure of
`xs`'s set; node 13, `visit(c.i)`, is framed. The cursor's site is in no
$`L_n`$, so the cursor facts are kept at both, as at the base (observed,
[runs](#runs)). Pretext's typed-array reads (`%ByteAt%`, `%ByteLength%`,
read by `line-break.ts`) and writes (`%ByteSet%`) are intrinsics of kind
`host` at their [byte-read signatures](../SOURCE-CONTRACTS.md), their
trust the row on the overlay's typed arrays: each a call of a native,
`%ByteSet%` charged at its view's reach, no name of them read.

### Natives

**A native run.** At a call of a native $`c`$ from a frame $`f`$ of
$`C`$'s code, the *native run* is the execution from the call state to the
first state at which $`f`$ is innermost again with its term returned or
thrown. A native's closure is the realm's code: a closure tagged with the
realm's component $`R`$, apart from $`C`$ and from the client's code (an
initial configuration's `Entry` states it, below).

- **Whose steps** (Fable S2). A step whose active frame is $`R`$'s, and
  whose innermost frame outside $`R`$ on the path is $`C`$'s, is $`C`$'s:
  the native's own step (`NativeStep`). A step whose active frame is the
  client's code is a client step wherever it runs, inside a native's run
  included, and keeps $`\Theta_C`$ (`ClientStep`; `FrameCore.Keeps` at
  client steps). A native the client calls takes client steps. So
  $`C`$'s charges hold the native's own writes and no callback's effect.
- **The native's own steps** (`nativeStep_within`, to be proved): from a
  reached state, each changes only locations of sites of $`L_n(c)`$ or of
  its node's key, by (b) and no-forgery (`valRun_noForge`: what the
  native's run holds it reached from its operands or its closure, its
  closure's captures realm storage it does not write by (b)); so each is
  `StepWithin` the native reach of $`c`$.
- **In a segment and in a member's call.** `RunSeq` gains a native step
  as one more kind of step at the run's depth (`RunSeq.native`), bounded
  by the native reach; a client step inside a native run is an outside
  step, a call of $`C`$ from it a member's call. `seg_run`, `seg_bound`,
  `ClientFrame.cert_of_charges` and `segWithin_of_run` read it, so a
  native's steps at the caller's depth are within $`W_c`$ and those inside
  a member's call within $`\Psi_C`$.
- **The frame's check at a call of a native.** `framed_transfer` at
  $`\Phi_\star=\Phi_c`$ at both exits, by `callerFrame_post` at the
  callee's type for a normal return and by (a) at a throw; the callee's
  value meets that type by `nativeAt_sound` and its contract
  (`SlotsMet`, the trust rows). Every other location changes within
  $`\Phi_c`$ as for any framed call.
- **In the flow.** A native's frames fit at $`L_n(c)`$ (`Fits.native`);
  `fits_step` at a native's step reads (b) and no-forgery. (S), (K) and
  (O) hold at each step of $`C`$'s code inside a native run, as anywhere.

**Natives that call back** (the audit's first open point).

- *A function of outside code* (`[c.i].forEach(visit)`): $`L_n(c)`$ holds
  $`\circ`$, so the operands enter $`O`$; `visit`'s steps are client steps
  keeping $`\Theta_C`$, its effect bounded by its type by the callback
  row, restated (below) for a function a native $`C`$ calls is passed.
- *A closure of the component* (`xs.map(f)`): `f`'s code is in $`\mathrm{seg}(c)`$
  and entered at $`L_n(c)`$; its steps are $`C`$'s code, within $`W_c`$ at
  the caller's depth, `f` given out only where $`L_n(c)`$ holds
  $`\circ`$. The native's footprint reads `f` at its arrow type, which
  `f`'s ordinary verdict establishes: the gate `callbackB` (step 8) admits
  such an `f` only where its code has no framed node and its unit is
  accepted by its ordinary plan, on the verdict line's `depends`.

**Precision of the native reach.** A native whose footprint is bounded by
class (`pop`, `shift`, `splice`, `unshift`, `sort`, and the natives taking
callbacks; [natives](../FOOTPRINTS.md#natives)) changes every value part at
every site under the ordinary pass's $`\Phi_c`$, at a receiver that is not
fresh. Under the framed plan the native's own steps are charged at
$`L_n(c)`$ alone. The ordinary pass refuses
`walk(xs) { const c = { i: 0 }, out = [1, 2]; while (c.i < xs.length) { out.pop(); s += xs[c.i]!; c.i++ } }`
at the read, `0 <= c.i` lost at `out.pop()` (observed: the review's probe
`ord-pop-local.ts`, "No rule derives this invoke at number"); the frame's
check at `out.pop()` keeps it, the cursor's site outside
$`L_n(c)=\overline{\{\mathit{out}\}}`$ and local, so $`W_c`$ keeps its part.
The same walker with `visit(c.i)` before the pop is kept at both calls. A
fact over storage $`L_n(c)`$ reaches is lost at `any`, whatever the
footprint states of the region, a stated limit: reading the footprint's
kinds at each step needs a per-step form of the footprint, which no row
states.

### The initialization as a premise

**The initial configurations** are every configuration $`x_0`$, at the
history before any entry, that fits the flow, is an entry, and meets the
outside contracts:

```math
\mathrm{Initial}(x_0) \iff \mathrm{Fits}_F(x_0, g_\varnothing) \wedge \mathrm{Entry}(x_0) \wedge \mathrm{SlotsMet}(x_0)
```

- $`\mathrm{Fits}_F(x_0,g_\varnothing)`$ is the frame's fit
  (`ClientFrame.FitsAt`, what `InitialFits` states of each initial
  configuration): $`x_0`$'s term fits $`O`$ at a position of outside code
  and its heap meets the flow's $`H`$;
- $`\mathrm{Entry}(x_0)`$ is the frame's `Entry` (what `InitialEntry`
  states): code provenance, the call discipline, closed values, every
  closure of the client's code lowered source (`LoweredSrc`) and every
  closure of the realm's code ($`R`$) lowered code of the calculus
  meeting (a) and (b);
- $`\mathrm{SlotsMet}(x_0)`$: every closure of a module function in
  $`x_0`$'s term or heap is an unfolding $`\mathrm{approx}\ \mathit{code}\
  i\ u`$ of the plan's layout at a depth $`i`$ at least $`x_0`$'s budget,
  and each of its outside captures meets the capture's type at every
  budget up to $`i`$, at every world admissible for $`x_0`$'s heap and
  every extension of one (Fable S5). `KindMet` states every world
  (`PassUnitInterfaces.lean`); for a cell holding a reference, whose
  meaning depends on the world, every world may hold of no value
  ([H5b](../SINGLE-PASS-THEOREM.md), the last sentence of its `moduleCell`
  item), so $`\mathrm{SlotsMet}`$ reads the worlds of $`x_0`$, which every
  later state's world extends.

So `InitialFits` and `InitialEntry` hold by definition, and
`FramedSpec.Initial`'s term, the realm's heap, `initE`, `initK`, `initL`
and `initOrder` leave `FramedSpec`. The claim quantifies over a heap the
client may have built, holding natives, `Array.prototype` and the client's
own closures, and over a client holding any values that meet $`O`$; the
stated limit of [initialization](#initialization) ("a client calling a
native runs no program the claim is about") is deleted with the term.

**The claim is not vacuous** (Fable S5). A premise can be unsatisfiable,
so the design states its inhabitance: `initial_inhabited` (to be proved),
$`\exists x_0,\ \mathrm{Initial}(x_0)`$ for P22's plan, with a public call
of `walk` from it (`PublicCall`). The witness is
`Tests/FramedLinkedCall.lean`'s configuration, retargeted: its realm
values replaced by a closure of the realm's code meeting `%ElementAt%`'s
signature (its step model's code, tagged $`R`$) and an object meeting
`ArrayProto` at P22's budget, and `walk`'s closure, the client and the
26 steps to the request's entry kept. That object needs a value of each
`ArrayProto` member the meaning reads; where the meaning admits no value
the calculus can build, the inhabitance fails and the design is wrong, so
piece 2 starts with it.

**The instances.** That a program's state after its modules' evaluation is
an initial configuration is discharged per kind of slot by the mechanisms
that discharge it for the ordinary pass:

- *`host`, `declared` and `standIn` slots*: the slot's contract by its
  trust row or stated footprint (`KindMet` at the kind), "`Array.prototype`
  meets `ArrayProto`", "The intrinsics meet their signatures" and the
  overlay's typed arrays among them; their sites $`\{\circ\}`$ hold of
  every value outside code may hold.
- *`established` slots*: `established_met` (proved); the value is the
  entry's module value, a closure of that module function's code, whose
  token step 2 gives the slot where the module is $`C`$'s.
- *`moduleCell` slots*: the slot's contract is the conjectured H5b for
  `moduleCell`, owned by [H5b](../SINGLE-PASS-THEOREM.md), from the
  `:init` request's acceptance (`init_asserted`), read at the worlds of
  $`x_0`$; its site is the binding's in the `:init` code, a code of
  $`M_C`$.
- *Linked slots*: the unfolding (`approxEnv`); a slot naming a signature
  holds a closure of it at every depth but $`0`$, where it holds `null`
  (`EnvFnAt`, below).
- *The fit and the entry*: the flow theorem along the initialization.
  Every module's `:init` code is a code of $`M_C`$, so a run of it from a
  configuration that fits ends in one that fits (`fitsAt_reached`).
  `initial_of_inits` (to be proved): from a configuration before any
  module runs (its cells holding the uninitialized value, which meets
  every set; its module functions' closures unfoldings), every execution
  that runs each `:init` code exactly once, in any order, ending at the
  client's first step, reaches an initial configuration. No order is
  constructed or read.
- *The natives as the realm's code*: the Clients row (Assumption
  "Clients" of Read-only frames) reads outside code as lowered source; the
  design extends its scope to the natives, which it reads as the realm's
  code, lowered calculus code meeting their contracts and (a) and (b).

**Several modules and mutual imports** (the e2 finding,
`noMutualImportOrder` on `e2-astra`). Read-only frames' (A1) admits
modules that import each other, and the order its (A2) states, "a module
after the modules it imports", is met by no order of two such modules.
The premise reads no order: whatever order ECMA-262 runs a cycle's modules
in, a completed evaluation reaches an initial configuration by
`initial_of_inits`. An evaluation that throws, as `cell-left.ts` reading
`cell-right.ts`'s cell during its initialization does (a `ReferenceError`
under Node), ends before the client's first step, so no program the claim
is about starts from it; a cycle whose functions read each other's cells
only when called after the evaluation completes is such a program. Whether
the `:init` postcondition of a module holds after a cycle that read
another module's cell is H5b's statement, shared with the ordinary pass:
its item (a) reads the importer's `:init` at the imported cells'
contracts, and a read of an uninitialized cell throws.

**Module functions run during the initialization** (the second open
point). A module's statements may call its module functions
(`const table = build()`). Those runs are runs of codes of $`M_C`$ inside
the `:init` code's run, before $`x_0`$: their safety is the `:init` unit's
and the called functions' units' (the ordinary pass), what they leave in
the heap fits the flow by `initial_of_inits`, and the claim starts at
$`x_0`$. A framed unit's claim is about calls entered after $`x_0`$.

**`entryHolds_realized`** (the third open point; "to be proved, milestone
1", in no Lean file): the request's entry contracts at the claim's entry,
from the invocation's. Restated as `entryHolds_of_slots` (to be proved):
the parameters' contracts are the invocation's actuals at their declared
types (the existing row on exported preconditions and handle parameters),
through `graphEntry`'s slot map; each outside capture's is
$`\mathrm{SlotsMet}`$'s, read by `captures_envOk`'s outside case at the
entry's world, an extension of $`x_0`$'s; a linked capture's is the named
function's code's requirement, which the codes' clause of
`FramedRequestSafe` gives at every call of it
(`codesAccepted_guarantees`).

**`EnvFn` at an unfolding.** At depth $`0`$ a linked capture is `null`, so
a slot naming a signature holds a closure of that signature or, in an
unfolding, `null` (`EnvFnAt`, the flow's `EnvFn` with that case). A call
of `null` takes no step, and a configuration of budget $`n`$ calls through
at most $`n`$ closures from closures unfolded at least $`n`$ times
(`unfold_budget`, to be proved, the frame's form of `approxEnv`'s
docstring), so no execution of the claim calls one. Two module functions
naming each other are unfoldings of each other: the cycle gate goes.

### The theorem chain

`SourceClaimJson.PassUnit.mode8Accepted_sound` keeps its statement; its
framed branch reads the frame at the new initial configurations, so the
commit that builds it records `Theorem modified (mode8Accepted_sound)`
with the readings of `FramedSpec.Initial`, `FrameCore.Keeps` and
`MemberSafe`'s framed branch.

1. `FramedSpec.Initial` (modified): the three conjuncts above;
   `FramedSpec.SlotsMet` (new), over the plan's layout (`FramedSpec.layout`,
   the `ModuleCode`s and kinds of the plan's component), at the worlds of
   $`x_0`$.
2. `FramedSpec.initialFits`, `FramedSpec.initialEntry` (modified, proved
   by definition); `initial_inhabited` (new, to be proved).
3. `NativeStep`, `ClientStep` (new), `FrameCore.Keeps` (modified: the
   obligation at client steps), with `project` and `keeps_canonical`
   (to be proved, milestone 1) restated over client steps.
4. `nativeAt_sound` (new, to be proved): a node `nativeAt` decides calls
   a closure of the realm's code.
5. `nativeStep_within` (new, to be proved): a native's own step changes
   only locations of its call's native reach, from (b) and
   `valRun_noForge`.
6. `RunSeq.native` (new constructor), `seg_run`, `seg_bound`,
   `segWithin_of_run`, `ClientFrame.cert_of_charges` (modified, to be
   proved again with native steps), `framed_transfer` (statement kept) at
   a call of a native at $`\Phi_c`$, its throw by (a).
7. `nativeKeysB`, `nativeKeysB_sound`, `callbackB`, `callbackB_sound`
   (new): every node of a native call's key calls a native; a closure of
   $`C`$ a native is passed has a code with no framed node.
8. `Fits.native` (new rule), `fits_step` (proof modified at a native's
   step); `EnvFnAt`, `unfold_budget` (new, to be proved); `fitsAt_reached`
   reads `EnvFnAt` (a slot holding `null` is never called).
9. `entryHolds_of_slots` (new, to be proved), replacing
   `entryHolds_realized`; `publicCall_safe` (to be proved, milestone 1)
   reads it.
10. `initial_of_inits` (new, to be proved): the instance, over every order
    of the `:init` runs, each exactly once.
11. `framedReturns_reached`, `framed_requestSafe`, `member_safe`'s framed
    branch and `mode8Accepted_sound`'s framed case: proofs re-threaded,
    statements as above.

### The charges of a term, exhaustively

`writesK` (`ReadOnlyCharges.lean`) ends with `| _ => []`, so a new
constructor of `Tm` would be read as writing nothing. Its last case is
replaced by the constructors that write nothing, listed:

```lean
  | .var _ | .nul | .undef | .tru | .fls | .num _ | .str _ | .bigint _ | .sym _
  | .objAt .. | .arr _ | .viewSpine .. | .goto .. | .frame .. => []
```

A value, a variable and a spine perform no write; a run (`goto`, `frame`)
is evaluated in its own frame, whose code's charges are read there. A new
constructor then fails to compile until its writes are stated.

### The pieces in commit order

Each piece is one commit with its record. Sizes are lines of Lean added,
estimated from the proved lemmas each mirrors, and lines deleted, counted at
the base.

| # | Piece | Proves | Added | Deleted | Changes verdicts |
| --- | --- | --- | --- | --- | --- |
| 0 | `writesK` exhaustive | none: the proofs over `writesK` unchanged | 5–10 | 1 | no |
| 1 | Client steps and native steps, read at no call of a native | chain 3, 6 at a plan with no call of a native, 7 | 400–600 | — | no |
| 2 | The initialization as a premise, and natives by their footprints | first `initial_inhabited` (chain 2), then chain 1, 4, 5, 6, 8 at natives, 9, 11; `chargesProtocol`, `nativeTop` | 900–1350 | about 1450 (the [deletion list](#what-the-change-deletes): the initialization, the realm and the natives' models) | yes: P22 kept, the probes below accepted |
| 3 | Outside slots of every kind and several modules | step 2's sites; the `:init` codes in $`M_C`$; chain 10 | 400–600 | about 120 (the gates) | yes: cells, imports and package components |
| 4 | Unfoldings at a cycle of names | chain 8's `EnvFnAt` | 150–250 | about 60 (`namingOrder`, `closable`, `StableLayout`, `PassUnit.approx_stable`) | yes: the cycle case |
| 5 | Read-only frames and the trust surface | the [paper proposal](readonly-frames-note/proposal-shared-slots.diff), applied once the owner approves it, its statuses at the pieces' Lean names; rows (a) and (b) in DESIGN.md | — | — | no |

Lean in all: 1855–2810 lines added, about 1630 deleted. The initialization
and the natives are one piece: a native's bound reads the callee's
contract, which $`\mathrm{SlotsMet}`$ states and the realm's heap, holding
one value per name, does not.

### Tests

Every current framed and read-only-frame case keeps its verdict or gains
one; the cases are those `node pipeline/run-cases.mts framed`,
`readonly-frame` and `bounds-pattern` run. Each negative's program is run
under Node by `tests/node-runs.mts`. Ten `readonly-frame-*` examples call
natives (`readonly-frame-walker`, `-two-walkers`, `-install-copy`,
`-own-map`, `-own-map-get`, `-library-calls`, `-confined-closure`,
`-released-store`, `-restored`, `-guarantee`) under the family checks
(`ComponentChecks.lean`), whose outcome no acceptance reads; their
expected outcomes are the family's and do not move.

| Case | Outcome | Shows |
| --- | --- | --- |
| `bounds-pattern-unreachable-field` (P22) | accepted under client trust, kept | `%ElementAt%` by its intrinsic contract, nodes 10 and 13 framed |
| every other `bounds-pattern-framed-*`, `readonly-frame-*`, `invalid-readonly-frame-*` case | kept | the frame's checks unchanged at a component calling no native but `%ElementAt%` |
| `readonly-frame-printed-module` (new; Section 1's printed module) | accepted under client trust | `fill` and `push` charged at their operands' reach; `w`'s spine read as protected |
| `readonly-frame-push-local` (new; `walk` alone, `out.push`, `visit: () => void`) | accepted under client trust | the same without `prepare` |
| `readonly-frame-push-visitor` (new; the visitor `{ values: "keep"; spines: "any" }`) | accepted under client trust | the same at a stated visitor |
| `readonly-frame-prepare-fill` (new; `prepare` by `new Array(n).fill(1)`) | accepted under client trust | `fill` charged at its fresh array's sites |
| `readonly-frame-prepare-loop` (new; `prepare` by a loop of `push`) | accepted under client trust | `push` charged at a local array's sites |
| `bounds-pattern-framed-pop-local` (new; the review's `ord-pop-local.ts`) | accepted under client trust | `out.pop()` framed, the cursor outside its reach |
| `bounds-pattern-framed-unrelated-natives` (new; a cursor-field walker calling `pop` and `sort` on an array it allocates, beside `visit`) | accepted under client trust | the cursor outside both natives' reach |
| `bounds-pattern-framed-native-callback` (new; the review's `native-callback.ts`, `[c.i].forEach(visit)`) | accepted under client trust | the callback's steps client steps, the cursor outside the native's reach |
| `invalid-bounds-pattern-framed-callback-throws` (new; a callback the native calls after the walker's `pop` of the client's array throws, the walker catching it and reading on) | negative | (a) bounds the pop's writes before the throw by its footprint, which changes the spine; `NaN` under Node |
| `invalid-readonly-frame-native-protected` (new; a member popping the protected array, called by the visitor, which catches the member's exception) | negative | the member's native reach holds the protected spine, (P) fails; `NaN` under Node |
| `bounds-pattern-framed-callback-gate` (new; `xs.map(f)` with `f` a closure of $`C`$ holding a framed call) | gap: refused at `callbackB` | the gate of Fable S3 |
| `bounds-pattern-framed-map-callback` (new; `xs.map(f)` with `f` a closure of $`C`$ with no framed call) | accepted under client trust | `f` entered at the native's reach, on `depends` |
| `bounds-pattern-framed-refused-member-native` (new; a member refused by its ordinary plan holding `a.pop()` beside P22's walker) | gap: refused at the visit | its native charged at every part (`nativeTop`): the cursor facts kept, `c.i < xs.length` lost at the spine of $`\circ`$ |
| `invalid-readonly-frame-walker-pops` | negative, kept | `w.flags.pop()` charged at the spine of $`\circ`$: (P) fails at `h.flags` |
| `invalid-readonly-frame-trim` | negative, kept | `trim`'s `pop` charged at the spine of $`\circ`$ |
| `invalid-readonly-frame-member-pop`, `-member-push`, `-member-shift`, `-member-splice` (new) | negative | a member's native at its parameter's reach, of $`\circ`$ |
| `invalid-readonly-frame-pops-no-visit` (new) | negative | the frame's check at `w.flags.pop()`: `w`'s reach holds `h.flags`'s sites |
| `invalid-readonly-frame-alias-export` | negative, kept | the interface gate, unchanged |
| `bounds-pattern-framed-cycle` (from `bounds-pattern-framed-cycle-refused`) | accepted under client trust | P22 beside `even` and `odd` naming each other, unfoldings |
| `bounds-pattern-framed-cell` (from `bounds-pattern-framed-cell-refused`) | accepted under client trust | a `let` cell a member writes, at its `:init` site, local, charged at its part |
| `invalid-bounds-pattern-framed-cell` (new) | negative | a walker over a module cell's array, which a member replaces (`data = []`): the cell's part is charged `any`; a visitor calling the member makes the walker read past the array, `NaN` under Node |
| `bounds-pattern-framed-cell-init` (new; a cell a module function writes during the initialization, then only read) | accepted under client trust | the `:init` code's write charged nowhere, `Ψ_C` keeping the cell |
| `invalid-bounds-pattern-framed-cell-init` (new; the same cell written again by a member the visitor calls) | negative | the member's write charged; `NaN` under Node |
| `bounds-pattern-framed-import` (new; the walker importing from two modules, one of its package at an `established` entry and one at its declaration) | accepted under client trust | the token at the first, $`\circ`$ at the second |
| `bounds-pattern-framed-mutual-imports` (new; two modules of the package importing each other, each reading the other's cell only when called) | accepted under client trust | no order read |
| `bounds-pattern-framed-mutual-imports-throw` (new; `cell-left.ts` and `cell-right.ts` with the walker) | the ordinary verdicts of the pair | the evaluation that throws starts no program |

Controls:

- **A native key shared with a call of outside code**
  (`Tests/FramedBindingControls.lean`): `nativeKeysB` refuses a flow whose
  native call shares its continuation and handler with a call of a
  parameter.
- **A native key's footprint forged** (`tests/single-pass-control-inputs.mts`,
  `framed-native-footprint`): a plan whose call of `pop` states
  $`\mathsf{keep}`$ at the receiver is refused at the frame's check of its
  node, which reads the footprint from the code's request.
- **Native reach dropped** (a mutation control, `fr-native-reach`): a
  verifier whose `nativeReach` is empty accepts
  `invalid-readonly-frame-walker-pops`, so the native's charge is what
  refuses it.
- **The inhabitance** (`Tests/FramedLinkedCall.lean`, retargeted):
  `initial_inhabited` for P22's plan, built with the library.

### What the change deletes

Each item with what replaces it. Files and line counts at the base.

**The constructed initialization and the realm.**

- `ComponentInit`, `componentInit`, `realmValueAt`, `namingOrder`, and
  their readers in `FramedCheck.lean` (`initOrder`, the realm's fields in
  the framed component), about 95 lines: replaced by the plan's layout and
  $`\mathrm{SlotsMet}`$.
- `FramedSpec.Initial`'s term and the fields `realm`, `initE`, `initK`,
  `initL`, `initOrder` (`FramedSpec.lean`; their readers in
  `PassUnitMember.lean`, `Elaboration.lean`, `FramedRealize.lean`,
  `FramedReturns.lean`, `FramedStarts.lean`), with their wire: the framed
  document's fields and `FramedSpec.decode`'s reading of them, and their
  names in `tests/json-field-names.mts`'s comparison: replaced by
  [the initial configurations](#the-initialization-as-a-premise).
- `initB` (`FramedComponentChecks.lean`, and its name in the docstring of
  `Json.lean`'s framed run), `initFlowB`, `realmSlotB` and the realm's
  checks in `frameFlowB` and `wokB` (`FramedFrameFlow.lean`): replaced by
  nothing; what they checked of one term is the premise.
- `FramedInitial.lean` (342 lines): `realmSlot_vj`, `realmSlot_scoped`,
  `init_fits`, `FramedSpec.frameFlow_checks`, `FramedSpec.init_checks`,
  `FramedSpec.initialFits`, `FramedSpec.codeOk_ok`,
  `FramedSpec.initialEntry`; replaced by the two premises holding by
  definition. Its general lemmas `prov_mono`, `codePart_prov`,
  `prov_loweredSrc`, `instantiate_of_scoped` move to their reader if one
  remains, and go otherwise.
- `FramedStarts.lean`: `init_ofC`, `initialEntry_code`, `initialFits_code`,
  `capSig_not_lowered` (the initialization as a code of the flow) go;
  `progOk_initial`, `progFrame_starts`, `progFrame_entryFits` are restated
  at the new `Initial`.
- `FramedRealize.lean`: `initial_starts`, `initial_lowered`,
  `initial_lay` restated at the new `Initial`; `ReadOnlyLayouts.lean`'s
  `lay_initial` and `ReadOnlyLocalReach.lean`'s `wok_initial` read an
  initial configuration's `Entry` in place of `letE (goto initC …)
  client`.
- `FlowProbe.lean`'s `componentCodes`' `init` argument (the
  initialization's code seeded with the realm's signatures) and `sibSig`
  at a native's slot: replaced by the `:init` request codes and the sites
  of step 2.
- `Tests/FramedLinkedCall.lean`'s initialization (`initC` allocating
  `walk`'s closure from the realm's heap): replaced by the witness of
  `initial_inhabited`; the file, its 26 steps and its import in
  `Tests/AxiomCheck.lean` stay, retargeted.
- `Tests/FramedBindingControls.lean`'s controls of the initialization and
  the realm (`initCode`, the init nodes running a write or holding a run, a
  realm identity without its layout, a realm value no primitive, the
  `initFlowB` and `realmSlotB` cases): about 60 lines.
- The forced control `framed-init-exports`
  (`tests/single-pass-control-inputs.mts`); `framed-doc-component`'s
  comment names the frame's flow.

**The natives' second model.**

- `hostModel?` (`FlowProbe.lean`) and its readers in `FramedCheck.lean`
  (`framedRestriction`, `realmValueAt`): replaced by each native's stated
  footprint and the native reach.
- `nativeSites`, `nativeProtocol` and their join in `nodeProtocol`
  (`FramedNodeChecks.lean`), their readers in `FramedCheck.lean`, and
  `protRegionB`'s join with them (`FramedSpec.protAt`): replaced by the
  native reach in $`\mathrm{Ch}`$, which leaves out the callee's set.
- `calleeArgB` as a condition of protection (`FramedSpec.protAt` and its
  readers in `FramedCheck.lean`; the restriction "Callees" of
  [restrictions of the protected reading](#restrictions-of-the-protected-reading)):
  its reason, a native read from storage whose steps no charge bounds, is
  answered by the native reach, and at a part of a site of $`O`$, where
  protection is read, $`W_c`$ is within $`\Psi_C`$
  ($`\mathrm{seg}(c)`$ is a set of codes of $`C`$). `calleeArgB` stays in
  `clientCallee`, the selection of a framed call's bound.
- `segCodes`' `host` argument (`ReadOnlyCharges.lean`), replaced by the
  callbacks of calls of natives (`Fits.native`'s entries).
- The restriction "Natives the realm does not model" of [restrictions of
  the protected reading](#restrictions-of-the-protected-reading), with its
  sentence in [SOURCE-FRAGMENT](../SOURCE-FRAGMENT.md) ("a call of C's
  code whose callee may be outside code …, is charged `any`").
- The trust row "a native's step model performs its model's steps" of
  [proved, to be proved, trust](#proved-to-be-proved-trust), and the row
  "the binding of the plan to the checked file" there naming
  `componentInit` and the realm: the first replaced by the ordinary pass's
  rows with (a) and (b), the second restated without them.

**The restrictions that become unnecessary**, each with its row in
[SOURCE-FRAGMENT](../SOURCE-FRAGMENT.md) and its refusal in
`framedRestriction` or `prepareFramedComponent`:

- "No cycle of names" (`bounds-pattern-framed-cycle-refused`, renamed
  `bounds-pattern-framed-cycle`, positive): replaced by the unfoldings.
- "Outside slots are audited realm values" (`intrinsicName`, the import
  gate admitting `%…` and `[[…]]` in `RequestCli.lean`;
  `bounds-pattern-framed-cell-refused`, renamed `bounds-pattern-framed-cell`,
  positive): replaced by outside slots by kind.
- "A framed unit whose outermost component is a package" and the one
  module of `prepareFramedComponent` (`comp.kind != .module`): replaced by
  the layout of the component's modules.
- `PassUnit.approx_stable` and `StableLayout` (`PassUnitRealize.lean`,
  read by no other proof; `Semantics/Tower.lean`'s `approx_stable` is
  another lemma and stays): replaced by the unfoldings at every depth.
- `closable` (`FlowProbe.lean`): the module functions on no cycle of
  names; every module function's closure is a value.

**The draft's sections and findings.** In this draft, when the pieces
land: [initialization](#initialization) and [the initialization in the
flow](#the-initialization-in-the-flow) are replaced by [the initialization
as a premise](#the-initialization-as-a-premise); the restrictions "No cycle
of names" and "Outside slots are audited realm values" leave
[restrictions](#restrictions); "The realm's intrinsics" and
"`approx_stable`" leave [findings](#findings-this-design-closes); the
first check's linked call in [milestones](#milestones) and [runs](#runs)
is restated as the inhabitance; `entryHolds_realized` leaves "To be
proved, milestone 1", replaced by `entryHolds_of_slots`. In
[read-only handles](readonly-handles.md#trust), the reading of the rule
"at its audited effect" by a step model is replaced by the native's stated
footprint and its reach.

**E2's draft** (`e2-astra`, `26237698b`, unmerged): its section
"Initialization of an import-closed component" and `noMutualImportOrder`
are replaced by [several modules and mutual imports](#the-initialization-as-a-premise),
which reads no order; its fixture's program (`cell-left.ts`,
`cell-right.ts`) becomes the case `bounds-pattern-framed-mutual-imports-throw`.
The branch is not merged.

### The ordinary side's lists of special cases

The audit found lists standing for a property on the ordinary side. This
change touches none of them: the framed plan reads a native call's
footprint as the ordinary request types it, whatever produced the type.
Each is separate work, with its row in [WORK.md](../../WORK.md#status):

- *Native methods by name in the front's proposals*:
  `HeadInference.lean`'s `resized` (`push`, `pop`, `shift`, `unshift`,
  `splice`), `touched` (those and `fill`, `copyWithin`) and `Ctx.pushed`
  (`push`); `Synthesis.lean`'s first-use freshness (`map`, `flatMap`),
  `generalArrayUse` (19 read-only methods) and the evolving writes (`push`,
  `unshift`). Each is a native's footprint or result freshness the
  contract states: row "Native footprints read by name in proposals".
- *Native results by name in the arithmetic rules*: `ArithmeticRules.lean`'s
  rules over `.call ["charCodeAt"]`, `["indexOf", "lastIndexOf"]`,
  `["slice"]` and the others, each with its `trust := .assumed [...]` by
  contract name: row "Library rules keyed by method names".
- *Built-in keys by name*: `Fragment.lean`'s `functionKeys`,
  `typedArrayKeys` and `inKeyRefusal`'s `arrayKeys` and `regexpKeys`, and
  `SourceTypes.prototypeNames`: row "Built-in prototype keys as one table".

### What the change trusts

- **Added**: rows (a) and (b) on standard natives, owner-approved on
  2026-11-21.
- **Restated**: the callback row of $`\Theta_C`$ reads "a function value
  outside code passes to $`C`$ at a function type meets that type, called
  by $`C`$ or by a native $`C`$ calls", and Assumption "Clients" reads
  the natives as the realm's code, lowered calculus code meeting their
  contracts, (a) and (b). The client obligation reads the client's steps
  wherever they run, and not a native's own steps.
- **Kept**: the rows the ordinary pass relies on for the same slots,
  "`Array.prototype` meets `ArrayProto`", "The intrinsics meet their
  signatures", the overlay's typed arrays, the declared imports' and host
  values' rows, the stand-ins' footprints, and H5b for module cells (its
  conjecture shared, not restated).
- **Deleted**: "a native's step model performs its model's steps".

## Milestones

1. **The bound route for P22** ($`G_C=\emptyset`$, `prot` false, the
   entering step's crossings alone). **Its first check**, before the
   theorems: one actual linked call of P22's `walk`, from an initial
   configuration (`initC` allocating `walk`'s closure, its outside slot the
   native `%ElementAt%`) through the entering step and the prologue to the
   request's entry related by `prologue_sim`, continued past the body's
   allocation `const c = { i: 0 }`, with the cursor's site the same in the
   realized and the request's code (`chk_sim` at that step); and, on the
   flow probe with `probeProtocol` replaced by $`\Psi_C`$ and $`W_c`$ as
   defined here (`writesK`), the cursor fact `c.i < xs.length` kept at
   `visit(c.i)` under $`\Psi_c`$, and `nested-capture.mjs`'s fact dropped
   at `wrapper()`. Then the lemmas listed for milestone 1, the restrictions
   with their controls, the plan, the headline, and the refusal of units
   whose linking reads a framed member.
2. **The protected reading of Read-only frames §4.1**, from the entering
   step's crossings ([the protected reading](#milestone-2-the-protected-reading)),
   its pieces in [commit order](#the-pieces-in-commit-order).
3. **The contexts of known calls** of Read-only frames (B1) and (B4)
   ([milestone 3](#milestone-3-the-contexts-of-known-calls)).
4. **The guarantee route**, with disjoint supports and the remaining
   incoming crossings (callback results, caught values).
5. **The obligation-relative arrow**: framed callers and importers.
6. **Keys**: `@clients` path keys. Parts are at field keys, a location's
   key the one its role in the world records ([the check at a call](#the-check-at-a-call),
   `keyAt`, `regionKeys_sound`); the initialization of imports is the shared model's (branch
   `shared-slots`).
7. **Outside slots and the initialization shared with verification**
   ([the design](#outside-slots-and-the-initialization-shared-with-verification)),
   its pieces in [commit order](#the-pieces-in-commit-order-1).

**Milestone 1 is specified to build**: each lemma it lists has its
statement and plan, each definition it reads is given (the canonical
sites, `RealizedAt`, `writesK`, `ActualCrossingsIn`, `PublicCall` over the
core), its restrictions are stated with their refusals and controls,
and P22's layout meets them (measured).

**The first check** (observed, [Runs](#runs)):

- *The linked call* (`Tests/FramedLinkedCall.lean`): from the realm's heap
  and `letE (gotoOf initC 0 [] .undef c_C) client`, 26 steps of the
  calculus (`linked`, proved from `step?_sound`): the initialization
  allocates `walk`'s closure and the exports' array; the client builds
  `xs` and a visitor and invokes the closure, the entering step raising
  the calls of $`C`$ active from 0 to 1, the entered slots the receiver,
  the two parameters, the two outside captures and the closure; the
  prologue reaches the realized code at `r.start` with the slots past the
  receiver, its first 33 entries the request's tables; from there the
  realized run is the request's run on the realized tables at the same
  heap for 26 steps, past `const c = { i: 0 }`, whose site is the same in
  both codes at the numbering keyed by `bodyOf` and two sites at a
  numbering per code.
- *The flow probe* at $`\Psi_c`$ (`componentProtocol`, `depthCharges`):
  at P22's `visit(c.i)` the call is framed, $`\mathrm{seg}(c)`$ is
  `walk` and `%ElementAt%`, $`L(c)`$ is outside storage, the two released
  sites of $`O`$ and `%ElementAt%`'s token, and the cursor's local site lies
  outside it: `c.i < xs.length` and `0 <= c.i` are kept. At
  `nested-capture.mjs`'s `wrapper()` (its TypeScript form) the call is
  framed through $`\mathrm{seg}(c)`$, the sites of `holder` and
  `holder.child` are in $`L(c)`$, and the field kind is charged `any` by
  `bump`'s write: both facts are dropped.

## Tests

- **P22**, `bounds-pattern-unreachable-field` (positive, accepted under
  client trust): the first check above.
- **Kept negative**: `invalid-bounds-pattern-cursor-given`.
- **Two module functions of one code**, `bounds-pattern-framed-shared-code`
  (positive, each walker accepted under client trust): P22's walker twice
  under two names; with a helper both call,
  `bounds-pattern-framed-shared-helper` (positive, both walkers accepted
  under client trust, the helper verified).
- **The restrictions' gates**: `bounds-pattern-framed-cycle-refused` and
  the rows of
  [SOURCE-FRAGMENT](../SOURCE-FRAGMENT.md).
- **New cases**: `throw.mjs`'s walker (negative at the handler read) and a
  variant reading only `0 <= c.i` (positive); a wrapper calling the client,
  the walker keeping its cursor (positive); a wrapper given the cursor,
  `nested-capture.mjs` and `boxed-capture.mjs` (negative); a client
  shortening the array through a wrapper (negative); `capture.mjs`
  (negative); `returned-closure.mjs` (refused at its closure's read);
  `dependent.mjs`'s `total` and a recursive walker (refused at the read of
  the framed member); the restrictions' controls.
- **Controls** (forged fragments): a flow omitting the walker's code
  (`codesCoverB`); an allocation site `none` (`allocB`, `AstraR3.lean`'s
  flow); a signature at a non-sibling entry slot (`entryFnB`); a realized
  code's proposal other than its request's at a body label
  (`realizedFlowB`); the four as forged flows in
  `Tests/FramedBindingControls.lean`; a wire
  $`\Theta_C`$ other than the source's and a row stating a path key
  (`clientsB`) and a $`\Psi_C`$ below its definition
  (`protocolAtLeastB`), there too; a check passing at one node of a call's continuation and
  handler and failing at another; a region `.all` at a protocol changing a
  part.
- **Pretext's walkers**: cursor bounds at local sites, measured by the
  probe at its own protocol (raw 8/8, complex 3/4 contexts); widths facts,
  at keyed parts, once the frame reads the shared model of outside slots
  ([the plan](../../WORK.md#status)); the layout functions at milestone 5.

## Open points for review

1. **Milestone 4's disjoint supports** are a design to review.

## Runs

Node 26.13.0, each printing the value shown; the files are in the reviews'
scratch directories (`framed-review/`, `round2/fable/`, `round3/`,
`round3/review/fable/`, `round4/`, `round4/review/fable/`, `round5/`, `verify3/`, `verify4/`), outside the repository:

- `throw.mjs`: `{ s: NaN, i: 2 }`; `wrapper.mjs`: `NaN`, `NaN`;
  `redirect.mjs`: `NaN`; `capture.mjs`: `NaN`; `prefix.mjs`: `undefined`;
  `install.mjs`: `true false`; `forged-flow.mjs`, `dependent.mjs`,
  `apply.mjs`: `NaN`; `returned-closure.mjs`: `NaN` at a later heap;
  `o-callee.mjs`: `walk` at the walker's depth;
- P22's layout (`round5/layout.py` on its `fragment.json`, `layout.out`):
  one function, no initialization statement, no import, the declared value
  `%ElementAt%`;
- the first check: `Tests/FramedLinkedCall.lean` (the linked call, built
  with the library); the flow probe (`TSCERT_FLOW_PROBE=only`,
  `TSCERT_FRAME_PROBE` at the call's offset) on the run directories of
  P22 and of `nested-capture.mjs`'s TypeScript form (`m1-build/`);
- the walk at framed nodes on P22's run directory
  (`TSCERT_OBSERVE=framed=13;node:10`, `m1-build/obs-f13.out`): node 13
  (`visit(c.i)`) framed, keeping the produced support of each of its 15
  entry index facts; the ordinary walk refuses node 10 (`xs[c.i]`), and the
  framed walk's entry of node 10 holds `c.i + 1 <= xs.length` and
  `0 <= c.i` and passes it, then refuses the edge from node 6 (the write
  of `c.i++`) into the loop head 2, which lacks the head's candidate
  `c.i <= 0`, a fact of the loop's first entry that the back edge does not
  establish (`c.i` is 1 there). Settled as the member's run settles
  (`inferredNext`: the candidate left out, the framed node's supports
  taken again), the framed walk is accepted (`m1-build/obs-a4-2.out`):
  node 13 keeps the supports of its 17 entry facts, among them
  `0 <= c.i` (the written invariant, the cursor's field at `keep`),
  `c.i < xs.length` (the loop's test, the field at `keep` and `xs`'s
  spine at `grow`) and `c.i <= 2^32 - 2` (from the test and the length
  bound); node 10's entry holds the first two and decides `xs[c.i]`, and
  `c.i++` from the third meets the head's `c.i <= 2^53 - 1`;
- the framed check on P22's run directory (`TSCERT_FRAMED`,
  `m1-build/framed-a4-2.out`), the supports decided from the flow: the
  framed call nodes are 13 (`visit(c.i)`) and 10 (`xs[c.i]`, the call of
  `%ElementAt%`, whose callee's set holds outside storage); at node 13,
  at $`\Psi_c`$ and the visitor's stated effect read at the caller's
  slots (values `any`, spines and views `grow`), the frame keeps 15 of the
  17 entry supports and drops the two facts over the length read before
  the call (`v = xs.length` and `xs.length <= v`), which the spines'
  growth breaks; at node 10 (effect `keep`) it keeps all 15; settled,
  the main graph's walk with both framed is accepted;
- P22 through the pipeline (`verify-source.mts`, `m1-build/f2/p22-flip.out`):
  its framed plan formed and decoded, its binding checks passing, the
  initialization a code of the flow, its framed call nodes 10 and 13, its
  framed walk accepted after the head's `c.i <= 0` is left out, direct;
  `walk@1190` accepted only under client trust Θ_C (component 0);
- `nested-capture.mjs`: `undefined`, a wrapper's captured closure writes
  storage its own capture reaches; `boxed-capture.mjs`: `NaN`, a handed-out
  closure capturing a box holding the cursor, called at the walker's
  depth; `shared-support.mjs`: `NaN`, a store keeping the invariant at its
  root breaks it at another sharing the support.

Lean files checked with `lake env lean` at the base, standard axioms only:
`Vacuous.lean`, `EmptyFlow.lean`, `NoSites.lean`, `CodeClause.lean`,
`StartLen.lean`, `NoProt.lean`, `ModuleClosures.lean`, `AstraR3.lean`,
`ApproxStable.lean`, `EnteredTables.lean`, `IncomingCrossings.lean`,
`RealizedCode.lean`, `WritesInOpaque.lean`, `AstraR4.lean` (the reviews'),
and `Truncate.lean`, `Round3.lean`, `Round4.lean`, `Round5.lean`:

```lean
theorem cross_into_prot {P : Package} (g : Ghost P) (tv : TypeView) (T : tv.Ty) (h : Heap) (v : Val) (l : Nat)
    (hA : g.A ≠ []) (hr : ReachRO tv P.ofC T h v l) (hl : g.Lent l) :
    (g.cross tv .into T h v).Prot l
theorem truncate_after_cross {P : Package} (g : Ghost P) (l : Nat) (hp : g.Prot l) :
    ({ g with A := [g.Prot] } : Ghost P).Prot l
example : (F.check, F.marksB, allocSomeB F) = (true, true, false)   -- AstraR3.lean's flow
theorem startFix_startInv_len … :
    (Ghost.crosses tv h xs { g₀ with A := [g₀.Prot] }).A.length = depthC F C none (.goto E K l L d comp)
theorem keep_rejects (b : Nat) (x y : Tm) (hne : y ≠ x) : ¬ Footprints.Change.keep.Holds b x y
theorem released_prot_inR … (hr : g.origin l = some .released) (hp : g.Prot l) : g.InR l
theorem loweredSrc_no_closure … : ¬ LoweredSrc ofC (.objAt fs c i)
theorem gotoOf_start_ne … (hs : s ≠ s') : gotoOf P s L d c ≠ gotoOf Q s' L' d' c'
theorem truncate_prot (g : Ghost P) (l : Nat) : ({ g with A := [g.Prot] } : Ghost P).Prot l ↔ g.Prot l
```
