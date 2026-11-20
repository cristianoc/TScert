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
[P22's walker](../../pipeline/examples/bounds-pattern-unreachable-field-refused.ts)
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
   (proved: `ClientFrame.framed_at_call`, `framed_at_innermost_keys`,
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
- **Stores checked at one root** (Astra 4, Fable F1, milestone 2): a store
  keeping $`I`$ at the written root breaks it at another root sharing the
  support (`shared-support.mjs`, `NaN`). Stated as open for milestone 2
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
  P22's extracted layout meets (measured, `layout.out` and the probe's
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
codes' layouts (`LayDeep`) and the flow's codes are lowered
(`CodesLowered`, decided by `codesLoweredB`, sound by
`codesLoweredB_sound`, `ReadOnlyLayouts.lean`). A capture's sites
are its slot's at its closure's code's entry (`VJ.capC`), a node
expression of a closure holds no location (`lowered_vals_all`), and the
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

At an exceptional return the transfer reads $`\Phi^{e}`$, $`\top`$ where the
callee states no exceptional bound
([exceptional footprints](../SOURCE-ELABORATION.md#exceptional-footprints)):
in `throw.mjs` the fact `c.i < xs.length` is lost at the handler and
`0 <= c.i` kept. $`\mathrm{Ch}`$ charges a write at both exits.

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
and handler, and keeps the fact where all pass: `framed_at_innermost_keys`
(proved) gives `Framed` at some such context and node.

- **Keys.** Every location has the key `none` (`NoKeys`, `reached_key`,
  proved); `ComponentChecks.Ctx.boundAt` joins every entry of a site and
  kind at `none`, so `noKeys` is sound for `Framed`.
- **The part universe.** The check at a universe (`frameCheckAtU`,
  `ReadOnlyCover.lean`) reads a region with no sites at the parts of
  $`U=(\mathrm{sites}(F)\cup\{\mathsf{none}\})\times\mathrm{kinds}\times\{\mathsf{none}\}`$
  (`flowSites`); `framed_of_cover` (proved) gives `Framed` from it where
  every location's site is in $`U`$, which `sites_in_flow` (proved) gives
  at every reached state from starts whose sites are the flow's: a step's
  fresh locations take the allocation sites of the innermost frame's
  proposal or outside storage (`stepSite_mem`), and the canonical
  allocation sites are the flow's ([the binding checks](#the-binding-checks)).
  At the base `callParts` reads such a region at `[]` (`NoSites.lean`).

### Protection

Milestone 1 reads every region unprotected (`prot` false), which loses
precision only. Milestone 2 reads a region protected where its root slot
is a value copy of an entry parameter's slot (`entryRootB`,
`copies_sound`), the parameter's declared type is read-only at every
position the path passes (so every location on it is reached read-only by
the entry's recorded crossing and stays in $`R_C`$), and each part the
path passes before its last location is $`\mathsf{keep}`$ under $`\Psi_j`$;
then `witness_of_path` (to be proved, induction on the path, each location
in $`R_C`$ changing within $`\mathsf{keep}`$) and `witness_reached` give
the witness. `prefix.mjs` (`undefined`): a writable prefix is read
unprotected.

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

Milestone 2. The return premise holds the kept invariants
($`I_{\mathit{root}}(\rho,h_0)\Rightarrow I_{\mathit{root}}(\rho,h_1)`$,
[the graph at framed returns](#the-graph-at-framed-returns)), discharged by
`framed_guarantee` (to be proved) with `SupportAt.outside` and
`invIn_of_installs` (proved), over path facts (`pathSupportB`; stable under
allocation, `pathFact_alloc`), (O) covering protected released storage
(`protectedInto_released`; `released_prot_inR`), the invariant at the
entry from `invariant-requires` (`invariant_of_entry`), and `hnew` by
`supp_split`.

**Open for milestone 2: a store checked at one root** (Astra 4, Fable F1).
Each store into a candidate's possible support is checked to keep the
invariant at the root it writes (`storeKeepsInv`, renamed from
`writeKeeps`, which names another function at the base). A store keeping
$`I`$ at its root breaks it at another root whose support holds the written
location: `shared-support.mjs` (`NaN`: `view` shares `xs` between two
handles, `truncate(b)` keeps $`I(b)`$ and breaks $`I(a)`$) and Astra's
`install(a)` writing a counter `b` shares. The fix this design takes for
milestone 2: **disjoint supports**, a check of (O) refusing a store that
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
  every one declares it read-only.
- **The subset milestone 1 implements.** The note counts a callback's
  result and a caught value as incoming crossings too. Milestone 1 records
  the entering step's alone: with fewer recorded crossings fewer locations
  are protected, so the obligation is weaker and the claim about more
  executions; milestone 1 reads no protection (`prot` false). Milestone 2
  records the others at their declared types.
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
its outside captures the natives), and returns the array of the exported
ones. Its order names each module function once, by name (`initOrder`):
two module functions of one code are two closures of that code. Its
allocations are at canonical sites.

**An initial configuration** of a program over $`C`$: the realm's heap
$`h_R`$, holding the intrinsic objects the outside slots of $`C`$'s module
functions name (`Array.prototype`), a world at which it is typed, and the
closed term
`letE (gotoOf initC 0 [] .undef c_C) client`, whose `client` is lowered
source of outside code (`LoweredSrc`, holding no closure,
`loweredSrc_no_closure`) scoped at one binder (`Scoped 1 client`, its
variable `0` the exports' array; the whole `letE` is `Scoped 0`).

**P22's layout** (measured, `layout.py` on P22's `fragment.json`, and the
module code the flow probe reads): one function, `walk`; no module
initialization statement (`init: []`); no imported module; two outside
slots, the intrinsic `%ElementAt%` the read `xs[c.i]!` lowers to, an
audited native with a step model, and `[[Array.prototype]]`, the realm's
array prototype every unit that uses arrays sees (`Extraction.lean`), an
intrinsic object of $`h_R`$. `walk` names no function of its module. So
P22 meets the restriction and its `initC` allocates one closure.

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
- **The flow along a program** (to be proved over `ProgReached core x₀`,
  the states of executions from initial configurations, by the proofs of
  `fitsAt_reached`, `chkSound_of_sites`, `sitesSound_of_fits`, `XStep.inv`
  and `Ex.inv` with the start predicate generalized from `fr.Call` to an
  initial configuration): `fits_program` (every state fits $`O`$ at a
  position of outside code and its heap meets the flow; at $`x_0`$ the
  initialization by its code's check and `client` by `fits_lowered`,
  proved), `chkSound_program` ((S), (K) and (O) at every step of $`C`$'s
  code, the initialization's and earlier calls' included),
  `inv_program` (`Inv` at the empty heap, kept by every step,
  `pkg_step_inv` at an entry). Then `entryFits_public` (the isolated start
  fits, its slots those `graphEntry` and the prologue fill, related by
  `prologue_sim`), `startInv_public` and `ChkSound` for the frame.
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
`chkSound_program`'s conclusion, never a premise of the definition.

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
- **lowered codes and layouts** (`codesLoweredB`, `tokensSomeB`,
  `ReadOnlyLayouts.lean`): every code of the flow is lowered, every context
  has a `some` token, and every closure of $`C`$'s code the initialization's
  and the flow's node expressions create has its code's layout `lay`
  (`layP (layQ F lay)`).
- **$`\Theta_C`$** (`clientsB`, `clientsB_sound`, `FramedBinding.lean`):
  the rows of $`C`$'s exported types state class keys only
  (`clientsByKindB`), and the plan's $`\Theta_C`$ is, at every part of
  $`U`$ at the key `none`, the join of the stated rows' changes at the
  part's kind (`rowsTheta`), read from the declaration document.
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
- `RealizedAt r a₁ a₂ L d`: `a₁` runs the realized code, and `a₂` is the
  first state after it, along steps keeping $`\Theta_C`$, whose innermost
  run is the realized code at `r.start`, with slots `L`, default `d` and
  the request's tag;
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
keeping the supports `S`), its read summaries checked, and the field
`FramedObligations r spec F S`: the returns `framedRet S` hold at the
executions the claim is about (`FramedReturnsReachedW`, by `ret_reachedW`,
from the check). `framedReturns_of_main` gives `FramedReturnsGuarantee` from the
framed run by `RunSoundFramed` (`run_sound_framed`), and
`framedRun_of_returnsW` the main graph's five clauses of
`FramedRequestSafe r (spec.frame r)`. `framed_requestSafe` (under `RunSound`,
`RunKeepsSummaries` and the request over the file's store) and
`member_safe`'s framed branch are proved from it; a field leaves the
structure in the commit that proves it from the check. `passMember`
checks a framed plan and refuses it (`framedRefusal`, [what the pass
checks](#what-the-pass-checks)) until none is left. **The codes are checked by the ordinary pass**,
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

The executable check (`FramedFlow.lean`, `Json.lean`): `framedCallNodes`,
the call nodes of the member's code framed at some context of the flow;
`callEffectAt`, the callee's stated effect at the caller's slots;
`framedSupportsAt`, the entry supports (in the pass's slot numbering)
passing `frameCheckAt` at $`\Psi_c = \Psi_C \sqcup \Theta_C \sqcup W_c`$
at every context and every node of the call's continuation and handler
that may call outside code. `passMember`'s framed branch
(`FilePlans.framedRefusal`) reads first the refusal of the checks that
read the component alone (`componentBindingRefusal`,
`FramedComponentChecks.lean`), evaluated once per component and shared
by its plans, each carrying the evaluation with its value
(`FramedSpec.componentRefusal`, a value with the equation that it is
`componentBindingRefusal` at the plan's fields): `noRestB`, `FFlow.check`,
`marksB`, `codesCoverB` over every module function's realized and request
codes, `allocB` (`allocSomeB`, and `allocCanonB` at the bodies
`moduleBody`, a module function's realized code's its request's, from
three sites per code), `initB` (in the initialization's order, which
names each module function once, each node allocating a closure of the
code of the function the order names there, each linked capture the slot holding the closure its name names,
allocated earlier, every other capture a realm identity, the last node the
entries' array), and (S), (K), (O) at the component's bodies
(`componentFrameDiags`). Then, per request: `entryB`, `compB`,
`codesCoverB` at `requestCode r`, `entryFnB`, `realizedFlowB`, `clientsB`
(the wire's $`\Theta_C`$ against the `@clients` rows, `rowsTheta`),
`protocolAtLeastB` (the wire's $`\Psi_C`$ against `psiDef`, both at the
flow's sites) and `readOnlyB`; the framed call nodes recomputed and each
kept support passing the check at the wire's protocols; then the main
graph walked with those nodes framed (`passMemberGraph`), settled; it
refuses at the first that fails, and otherwise at
`FramedObligations.reached`, which no check establishes. Each binding
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
document whose fields, entries, nodes or supports disagree with it;
`inputDigest` hashes the document. The framed plan's refusal follows the
group's ordinary refusal; the verdict is the ordinary plan's.

`MemberAccepted.framed`, beside `ordinary`'s premises over the request
(its codes by the ordinary pass): the checks that read the component
alone (`FramedAccepted.component`: `componentBindingRefusal` at the
plan's fields refuses nothing, which `componentBindingRefusal_none`
reads as `FFlow.check (remark F)`, `marksB`, `codesCoverB`, `allocSomeB`,
`allocCanonB`, `noRestB`, `initB` and (S), (K), (O) over every body of the
component, each passing); the binding checks that read the request; $`\Psi_C`$ as defined; at each framed call node $`c`$ of the
main graph, $`W_c`$ computed and the supports kept by the check at
$`\Psi_c`$, at $`\Phi`$ and $`\Phi^{e}`$; the main graph accepted by the
framed run (`RunCall.AcceptsFramed`).

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
- **Acyclic module names.** A framed plan's component has an acyclic name
  graph among its module functions. Excluded: two module functions naming
  each other, whose closures have no finite initialization at the base.
  Control: a framed walker in a module with two mutually naming functions,
  refused.
- **Outside slots are audited realm values.** Every outside slot of a
  module function of a framed plan's component holds an audited realm
  value, the same at every depth: a native with a step model (P22's
  `%ElementAt%`) or an intrinsic object of the realm's heap (P22's
  `[[Array.prototype]]`). Excluded: an import of another module's value, a module
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

The continuation after a failed return premise is outside the claim
(`RunSoundFramed` claims progress on paths whose framed returns meet their
premise; `ret_reachedW` establishes it before the continuation).

### Verdicts that read a framed member's arrow

- **The component's own linking supplies it** (a sibling slot, a unit's
  own slot, a module binding): refused at that read, located there
  (`dependent.mjs`'s `total`, a recursive walker); importers refused by
  `establishVerdict`.
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

The verdict line of a group with a framed member is
`accept under client trust Θ_C (component C)`. Milestone 3 brings the
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
  by `framed_at_innermost_keys` and `framed_of_cover`), and the callee's
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
  continuation and handler (`frameCheckAt`, keys `noKeys`, no
  protection), by `framed_at_innermost_keys`, where the separation the
  check reads holds at the node's entry.
- `ret_reachedW_of_checks`: `ret_reachedW` with its transfer premise
  assembled from `nodeTransfer_of_transfer`, `own_of_fit` and
  `framed_of_check`. Its premises besides the checks (`atomCallB`,
  `hslots`, the closure check of each $`T_l`$, $`W_c(T_l)\sqsubseteq\Psi_c(l)`$,
  the frame check): the spec's (`hsrc`, `hty`, `hvals`, `ChkSound`,
  `StartInv`, `Facts`, `FlowSites`, `EntryFits`, `NoKeys`, the residual
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
  - *invariants of the frame to be proved*: `ChkSound` and `StartInv`
    (`chkSound_program`, `startInv_public`), `EntryFits`
    (`entryFits_public`), `NoKeys` at the starts, `hvals` (from
    `EntryAt`), and the separation the frame check reads at each framed
    node's entry (`hq`).

- `ret_reachedW_spec` (proved, `FramedReturns.lean`): `ret_reachedW_frame`
  at the plan's flow (`spec.fflow`) and layouts (`spec.lay`), the hashing
  of the plan's sites its instance: `hty` by `call_typed` (an entry is a
  configuration, whose budget is positive, world admissible and heap
  typed); the initial configurations by `initial_lay` from layout
  provenance and the residual invariant of the initialization's node
  expressions and of the realm's heap; `noRestB` from the component's
  binding checks (`componentBindingRefusal_none`). Its other premises are
  `ret_reachedW_frame`'s.

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
`framedRun_of_returnsW` from `FramedObligations`' framed nodes and returns,
the guarantee and the reached returns: at each call and history the frame
starts from, `SafeRet.underW` (proved, by induction on the budget) reads the
returns at each step keeping $`\Theta_C`$ from the invariant, and claims
nothing past a step breaking it. The guarantee is `framedReturns_of_main`'s,
from the framed main run `FramedAccepted` holds; the returns are
`FramedObligations.reached`, which leaves the structure when `ret_reachedW`
gives it.

### The headline

`member_safe` gains the framed branch, `passMember_sound` shows `passGroup`
makes a framed member `MemberAccepted.framed`, and the executable path is
`FilePlans.passMember`'s framed branch. `mode8Accepted_sound` keeps its
statement:

```lean
theorem mode8Accepted_sound {f : FilePlans} {i : Nat} (h : Mode8Accepted f i) : PassUnitSafe f i
```

- **Premise** `Mode8Accepted f i`: unchanged, the exact CLI condition; a
  group with a framed member is printed
  `accept under client trust Θ_C (component C)`.
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
`chkSound_of_sites`, `sitesSound_of_fits`, `framed_at_innermost_keys`,
`frameCheck_sound`, `framed_of_sites`, `regionSites_sound`, `reach_sites`,
`reached_key`, `witness_along`, `HStep.uniform`, `call_segment`,
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
`lowered_wok` (`ReadOnlyWriteKinds.lean`); `framed_of_cover`,
`framed_of_frame_cover`, `stepSite_mem`, `sites_in_flow`
(`ReadOnlyCover.lean`); `graph_stepR`, `graph_safeR`,
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
`ret_reachedW_of_entries`, `ret_reachedW_frame`, `ret_reachedW_spec` (`FramedReturns.lean`); `call_typed`, `initial_lay`, `initial_lowered` (`FramedRealize.lean`, `FramedSpec.lean`).

**Observed at the base** (to be moved into the build): `truncate_prot`,
`truncate_uniform`; `startFix_startInv_len`, `keep_rejects`,
`released_prot_inR`, `loweredSrc_no_closure`, `gotoOf_start_ne`;
`cross_into_prot`, `truncate_after_cross`, `allocSomeB`'s value on
`AstraR3.lean`'s flow; `body_prefix` (`Round5.lean`); `entry_slot_holds_O_tokens` (the second
review's `CodeClause.lean`).

**To be proved, milestone 1**: `publicCall_safe`, `entryHolds_realized`,
`project`, `keeps_canonical`,
`fits_program`, `chkSound_program`, `inv_program`, `entryFits_public`,
`startInv_public`, `ret_reachedW_spec`'s premises to be proved (`hvals`
from `EntryAt`, `NoKeys` at the starts, the frame check's separation at
each framed node's entry), its premises that are checks connected to the
checks the pass runs (`FFlow.check` at `spec.fflow` from the component's
check at `spec.checked`, `compB`, `tokensSomeB`, `codesLoweredB`,
`atomCallB` at the framed nodes, the closure checks, `hslots` and
`hcheck` from `framedSupportsAt`, the protocol orders, the layout
provenance and residual invariant of the initialization and the realm),
each field of `FramedObligations` from the check,
`ro_of_readOnlyShape`, `passMember_sound`'s
framed branch.

**To be proved, milestone 2**: `copies_sound`, `witness_of_path`,
`framed_guarantee`, `pathFact_alloc`, `tolerant_of_storeKeepsInv` with
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
  one.

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
2. **Protection and the guarantee route**, with disjoint supports and the
   remaining incoming crossings (callback results, caught values).
3. **The obligation-relative arrow**: framed callers and importers.
4. **Keys**: parts at field keys (pretext's `prepared.widths`), `@clients`
   path keys, and the initialization of imports.

**Milestone 1 is specified to build**: each lemma it lists has its
statement and plan, each definition it reads is given (the canonical
sites, `RealizedAt`, `writesK`, `ActualCrossingsIn`, `PublicCall` over the
core), its five restrictions are stated with their refusals and controls,
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

- **P22**, `bounds-pattern-unreachable-field-refused` (a gap, positive at
  milestone 1, renamed with its outcome): the first check above.
- **Kept negative**: `invalid-bounds-pattern-cursor-given`.
- **Two module functions of one code**,
  `bounds-pattern-framed-shared-code-refused` (a gap at P22's line): P22's
  walker twice under two names beside a module function both call.
- **New cases**: `throw.mjs`'s walker (negative at the handler read) and a
  variant reading only `0 <= c.i` (positive); a wrapper calling the client,
  the walker keeping its cursor (positive); a wrapper given the cursor,
  `nested-capture.mjs` and `boxed-capture.mjs` (negative); a client
  shortening the array through a wrapper (negative); `capture.mjs`
  (negative); `returned-closure.mjs` (refused at its closure's read);
  `dependent.mjs`'s `total` and a recursive walker (refused at the read of
  the framed member); the five restrictions' controls.
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
  probe at its own protocol (raw 8/8, complex 3/4 contexts); widths facts
  at milestone 4; the layout functions at milestone 3.

## Open points for review

1. **Milestone 2's disjoint supports** are a design to review.

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
- P22 through the pipeline (`verify-source.mts`, `m1-build/a5-p22-4.out`):
  its framed plan formed and decoded, its binding checks passing, its
  framed call nodes 10 and 13, its framed walk accepted after the head's
  `c.i <= 0` is left out; refused at `FramedObligations.reached`;
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
