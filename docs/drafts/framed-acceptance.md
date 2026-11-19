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
code outside it, and every fact the graph carries across a call.
[P22's walker](../../pipeline/examples/bounds-pattern-unreachable-field-refused.ts)
and pretext's walkers are its tests ([Tests](#tests)); the first buildable
milestone is the bound route for P22 ([milestones](#milestones)).

Base: branch `p22-accept` at `f96ecd5e4`. Notation is that of
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
   predicate: at a *framed call* a support may instead pass the read-only
   frame's check, whose soundness is a return premise the execution
   discharges ([the graph at framed returns](#the-graph-at-framed-returns)).
   The ordinary graph theorem is its instance with no framed call.
2. **The read-only frame rule** ([the rule](readonly-frames-note/note.tex),
   [read-only handles](readonly-handles.md#what-the-lean-states)), with its
   consequence over the paper's executions (proved: `exec_rely`,
   `ClientFrame.call_rely`), its premise checked at a frame of $`C`$'s code
   (proved: `ClientFrame.framed_at_call`, `framed_at_innermost_keys`,
   `frameCheck_sound`) and the flow of sites (proved: `FFlow.check_sound`,
   `fitsAt_reached`). This design generalizes the rule's premise from a
   call of outside code to a call whose run may reach outside code, a
   function of $`C`$ among them ([the transfer](#the-transfer-at-a-call)),
   states one notion of charges for the members' certificates and for a
   call's own steps ([charges](#charges)), and indexes certificates by the
   calls an execution makes ([certificates](#certificates)).
3. **The acceptance path** (CLAUDE.md, "Acceptance/soundness invariant").
   `CertifiedPlan.framed`, `PassUnit.FramedRequestSafe` and `MemberSafe`'s
   branch reading it exist (proved: `framed_callSafe`,
   `callSafe_of_member`); no `FunctionPlan` certifies to a framed plan.
   This design adds `FunctionPlan.framed`, its branch of `certify`, the
   constructor `MemberAccepted.framed`, and `framed_requestSafe`, at a frame
   whose calls are the actual public calls of programs
   ([the frame of a request](#the-frame-of-a-request)).

## Findings this design closes

Each finding below is a property of the base or of the previous version of
this draft, verified by a run or by reading the Lean named, with the
section that closes it. A premise moves into a theorem to be proved, a
decided check, a restriction, or a row of trust.

- **Gaps of the proved results** (from a review of an earlier acceptance
  design): (1) `framed_at_call` gives `Framed` before the invocation and
  `call_rely` reads it after it ([the transfer](#the-transfer-at-a-call));
  (2) a callback may shorten an array and throw, the segment being read at
  one effect, observed `throw.mjs` ([an exceptional return](#an-exceptional-return));
  (3) a re-entered member's fresh arguments have no witness
  ([re-entry](#re-entry)); (4) `Cert.tolerant` ranges over every
  `PkgStep` ([certificates](#certificates)); (5) the guarantee route's
  `hsup` and `hnew` ([the guarantee route](#the-guarantee-route)).
- **Vacuity** (Astra 1, Fable 1). `FramedRequestSafe r fr` holds of every
  request at a frame whose `enters` admits no call (observed:
  `Vacuous.lean`); an empty flow passes `FFlow.check` and `marksB` and
  admits no `EntryShape` (observed: `EmptyFlow.lean`); a flow omitting the
  walker's code keeps a fact across a call that breaks it (observed:
  `forged-flow.mjs`, `NaN`); a heap value of a private closure makes
  `EntryShape` false at every term (Astra, checked in Lean). Closed by the
  frame built from the request, its calls defined by program executions,
  and the binding checks ([the frame of a request](#the-frame-of-a-request)).
- **The guarantee's return** (Astra 2): `Supported` cannot state an
  invariant kept across a replacing write (an equal-length array
  installed: the invariant holds, the field's `grow` bound fails). Closed
  by an invariant return premise ([the graph at framed returns](#the-graph-at-framed-returns),
  [the guarantee route](#the-guarantee-route)).
- **The entering step and the joined protocol** (Astra 3, Fable 7): a
  certificate's `tolerant` started after the entering step, which pushes
  the history; `Run.bound` needs $`\Theta_C\sqsubseteq\Psi`$ at the
  certificates' protocol. Closed in [certificates](#certificates).
- **Witnesses for locations a region comes to include** (Astra 4): a
  `scalar` write can redirect a path so that a region includes a location
  the entry never reached. Closed in [protection](#protection).
- **Charges tied to the lowered code** (Astra 5, Fable 9.3–9.4): the wire's
  write list has no correspondence theorem, `allocAt` numbers allocations
  within one reduction, the `π.out` filter can select no node at a
  wrapper's call. Closed in [charges](#charges) and
  [the check at a call](#the-check-at-a-call).
- **Callers, importers and the callback's type** (Fable 2, 3, Astra 6): a
  unit calling a framed unit is accepted with no trust stated (observed:
  `dependent.mjs`, `NaN`); the callback's arrow is assumed unconditionally;
  continuing past a failed return premise is unsafe (Astra, a callback
  emptying `[7]`). Closed in [callers and callbacks](#callers-and-callbacks).
- **`callParts`' universe** (Fable 4): a region with no sites gets no part
  and `frameCheck` passes on it vacuously (observed: `NoSites.lean`).
  Closed in [the check at a call](#the-check-at-a-call).
- **Local storage in the certificate** (Fable 6): uncharged local parts
  need a lemma. Closed in [charges](#charges), observed `capture.mjs`.
- **Generality** (Fable 5): one notion of charges for $`W_c`$ and
  $`\Psi_C`$; `RunSound` an instance; the top-frame scope stated; keys.
  Closed in [charges](#charges), [the graph at framed returns](#the-graph-at-framed-returns)
  and [scope](#scope).
- **Build interfaces** (Astra 7, Fable 9): `OverStore` reads graph plans
  alone; `FirstKept` and each exit's environment at a return; the
  direction of `asserted_of_reach`; `ViewOver (Ty ι)`; the guarantee's
  entry; the pretext measurements. Closed in [the plan](#the-plan),
  [the theorems](#the-theorems), [the guarantee route](#the-guarantee-route)
  and [tests](#tests).

## Definitions

A state is a configuration of the paper's executions with its history,
$`s=(x,g)`$ (`Conf × Ghost`); $`\delta(s)`$ is the number of calls of
$`C`$ active at it (`depthC`).

- **A call state** of a frame $`f`$: $`f`$, a frame of $`C`$'s code with
  environment $`\rho_f`$, is the innermost frame of $`s_0`$'s term, and
  its term is a call whose callee, receiver and arguments are values. The
  pass's call nodes have this form (`call_local_sound`, a call node is one
  sequent whose parts are values).
- **The call's segment**: the steps from $`s_0`$ to the first later state
  $`s_1`$ at which $`f`$ is innermost again, its term a value (a normal
  return) or a throw (an exceptional return), the *resumption*. Along it
  $`\delta\ge\delta(s_0)`$.
- **The steps at the caller's depth** in a segment: steps from states with
  $`\delta=\delta(s_0)`$, each of $`C`$'s code (the invocation, the body
  of a callee of $`C`$'s code) or of outside code. Every deeper step is
  inside a call of $`C`$ entered from outside code, a member's call.
- **The segment's codes** $`\mathrm{seg}(c)`$ of a call node $`c`$: the
  least set of codes of the flow holding each code whose token the
  callee's set at $`c`$ holds, and closed under the same at every call
  node of its members (`segCodes`, decided over the flow's slots and
  tokens, every context). **A framed call**: a call node whose callee's
  set holds outside storage, or such that some code of $`\mathrm{seg}(c)`$
  has a node whose callee's set holds it (`reachesOut`, decided). A native
  without a step model is outside code (`Fits.invoke`); the calculus has
  no implicit call (an arithmetic of a non-primitive throws,
  `arithThrow`), so each run of outside code starts at an `invoke` or
  `construct` step.
- **The effects at a call.** $`\Phi`$ is the callee's effect read at the
  caller's slots; $`\Phi^{e}`$ is $`\Phi`$ where the callee's type states
  an exceptional bound (`onThrow`, `callExc`) and $`\top`$ otherwise;
  $`\Phi_\star`$ is $`\Phi`$ at a normal return and $`\Phi^{e}`$ at an
  exceptional one.

## Charges

One notion of charges serves the members' certificates and a call's own
steps.

**The charges of a set of codes** $`\mathrm{Ch}(M)`$: the protocol joining,
for each node of each code of $`M`$ at each of its contexts, each write of
the node's expression, at the parts of its receiver's sites at that node
and context and the kinds its form writes (`writesIn` over the flow's
nodes, the function the frame probe uses: an element write at the spine's
sites and the element kind, a write at a key at the receiver's sites
under that key), at $`\mathsf{any}`$; and each native step model's writes
at its receivers' parts. It is computed by the verifier from the lowered
node expressions the flow holds, which [the binding
checks](#the-binding-checks) make the request's lowered codes; no write
list of the wire is read, and no write is discharged as fresh.

- **The protocol** $`\Psi_C`$: $`\mathrm{Ch}(\text{all codes of }C)`$ at
  every part, except a part of a local site that no capture slot of any
  code may hold, through the heap of sites' contents (`captureSites`
  closed under `contents`), which is $`\mathsf{keep}`$. The proposed
  $`\Psi_C`$ on the wire is checked to be at least this
  (`protocolDiags` restated over $`\mathrm{Ch}`$).
- **The depth charges** of a call node $`c`$: $`W_c=\mathrm{Ch}(\mathrm{seg}(c))`$
  at every part, local parts included: a code the call runs at the
  caller's depth may hold the caller's local storage through an argument
  of a call by name or a closure of the caller's frame (observed:
  `wrapper.mjs`, a wrapper writing the walker's cursor, `NaN`).
- **The call's protocol** $`\Psi_c=\Psi_j\sqcup W_c`$ with
  $`\Psi_j=\Psi_C\sqcup\Theta_C`$, the joined protocol.

The difference between the two bases is one lemma.

- **Local storage at a member's call** (`local_unreached`, to be proved):
  in a call of $`C`$ entered from outside code at a state $`a`$, a step of
  $`C`$'s code changes no location $`l<|h_a|`$ of a local site that no
  capture slot may hold. Plan: by induction along the call, every value
  its frames hold is (i) a value outside code supplied (it meets $`O`$,
  which holds no local site, `Flow.Facts.noLocal`), (ii) read from storage
  of a site that is not local, which references no local site
  (`LocalHeld`, `FFlow.marks_of_marksFrom`), (iii) a capture of a closure
  of $`C`$ (its slots' sites), (iv) allocated in the call, at least
  $`|h_a|`$, or (v) computed from such; by `reach_sites` (proved) a
  location such a value reaches is of a site in the closure of those
  sets, so a pre-entry local location it reaches is of a captured site.
  Observed (`capture.mjs`, `NaN`): a closure of $`C`$ capturing the
  walker's cursor, given to the visitor and called, writes the cursor in a
  member's call; its site is a capture slot's, charged.
- **A step's changes are its charged writes** (`stepWrites_sound`, to be
  proved): every location $`l<|h|`$ a step of $`C`$'s code from a reached
  state changes is written by a write of the instantiated node expression
  of the code and node the frame fits at (`Fits.innermost`,
  `fitsAt_reached`, proved), and $`l`$'s part is among that write's
  charged parts. Plan: `step_changes` (proved) locates the changed slot or
  cell among the stepped term's references; by cases on the writing steps
  of `Step` (`writeAt`, `setElem`, a native's step model), the redex is a
  subterm of the node expression after substitution, so its write is one
  `writesIn` lists (`writesIn_sound`, to be proved by induction on the
  expression, as `syn_sound` is); the receiver meets its set (`Fits`), so
  $`l`$'s site is one of its sites (`reach_sites`); the kind is the
  world's at $`l`$ (`kindAt`). The invocation changes no old location.

So **within a call** (`within_charges`, to be proved, from the two lemmas
and `stepWithin_of_check`, proved): every step of $`C`$'s code inside a
member's call from $`a`$ is `StepWithin Ψ_C |h_a|`, and every step of
$`C`$'s code at the caller's depth in a segment from $`s_0`$ is
`StepWithin W_c |h₀|`, its frame running a code of $`\mathrm{seg}(c)`$
(`segFrames`, to be proved: every frame at the caller's depth above $`f`$
is pushed by a call step of such a frame or of $`f`$'s call, whose callee
meets the callee's set at its node, and a closure of $`C`$ in a set holds
its code's token there, `FnsIn`). No freshness is read, so no
per-activation allocation record is needed.

## The transfer at a call

**Framed transfer.** For a fact with support $`S`$:

```math
\frac{s_0\ \text{reached, a call state of}\ f\qquad s_0\to^{*}s_1\ \text{its segment, every step keeping}\ \Theta_C\qquad h_0\xrightarrow{\Phi_\star}_{\rho_f}h_1\qquad \mathrm{Framed}(\Phi_\star,\Psi_c,S,\rho_f,s_0)}{\mathrm{Supported}(S,\rho_f,h_0,h_1)}\ \textsf{(Framed transfer)}
```

with $`h_0,h_1`$ the heaps of $`s_0,s_1`$ and `Supported` the relation of
[footprints](../FOOTPRINTS.md#support-and-respect): each location
$`l<|h_0|`$ of each $`(r:\delta)\in S`$, read at $`(\rho_f,h_0)`$, changes
within $`\delta`$.

The argument: the segment's steps at the caller's depth of $`C`$'s code
change each $`l<|h_0|`$ within $`W_c`$ ([charges](#charges)); each maximal
run of outside code at that depth changes $`R_C`$ within $`\Psi_j`$, its
member calls by their certificates at $`\Psi_j`$ ((L2)); $`R_C`$ grows
inside the call ((L3)), so the segment changes each $`l\in R_C(s_0)`$,
$`l<|h_0|`$, within $`\Psi_c`$; with $`\Phi_\star`$ bounding every other
location the segment is an action of $`\Phi_\star\oplus_C\Psi_c`$, and
`Framed` gives `Supported`.

Lean (to be proved, `ReadOnlyTransfer.lean`, in `ClientFrame`):

```lean
theorem framed_transfer (hc : fr.ChkSound) (hi : fr.StartInv)
    (certs : fr.Certs (Ψ ⊔ fr.Θ) G) (hW : ∀ p, ((Ψ ⊔ fr.Θ) p).le (Ψc p) = true)
    {a e : Conf × Ghost (fr.F.at fr.C)} {E K t L d k x comp} {n : Nat}
    (ha : fr.Reached a) (hcall : CallState a.1.t (.frame E K t L d k x comp))
    (hex : Ex fr.KStep (Inside a.1.t) n a e) (hres : Resumes a.1.t e.1.t)
    (hown : SegWithin fr Ψc a)
    (hΦ : TolerantFrames.Action Φ (envOf L d) a.1.s e.1.s)
    (hfr : Framed Φ Ψc S (envOf L d) (lift fr.F fr.C none a.1 a.2)) :
    Footprints.Supported S (envOf L d) a.1.s.h e.1.s.h
```

`CallState`, `Inside`, `Resumes` (over `path`, `ReadOnlySteps.lean`) and
`SegWithin` (every step of $`C`$'s code at the call's depth in the segment
is `StepWithin Ψc |h₀|`) are new. Plan:

- **The segment as a run.** `MemberRun.Own` (proved) takes a depth
  parameter $`d'`$ for its own steps; the member's call is $`d'=d+1`$, the
  segment $`d'=d`$; `MemberRun.within` (proved) is the one bound for both.
  `seg_run` (to be proved): the segment is one, its inner runs the
  maximal `QRun d` pieces (`call_segment`, `decompose`'s first conjunct at
  `off = 0`, proved), each from a reached state that is `Ok d`
  (`Reached.xstep`, `reached_ok`, proved).
- **The protocols.** Certificates and runs are at $`\Psi_j`$, so
  `Run.bound` (proved) has its premise $`\Theta_C\sqsubseteq\Psi_j`$;
  `RBound.mono` (to be proved, from `Change.Holds.mono`) lifts each run's
  bound to $`\Psi_c\sqsupseteq\Psi_j`$.
- **The action**, as in `readOnly_rule` (proved): `RBoundBelow.all` and
  `hΦ` give `OAction Φ Ψc`; `supported_of_framed` (proved) gives
  `Supported`.
- **The invocation** is a checked step at depth $`d`$ (`ChkSound`): marks
  kept, the history grown, `Ok d` after it (`pkg_step_ok`, proved); its
  fresh locations lie outside `Framed`'s domain; `SegWithin` holds of it
  (it changes no old location).
- **The saved environment.** The claim reads facts at the top frame of
  each claim ([scope](#scope)), whose term is `.frame E K t L d k x comp`;
  every step of the segment is `frameC` of its running term, so `L`, `d`,
  `k`, `x` are kept (`frameC_shape`, to be proved by cases on `Step`).

`hown` comes from `within_charges` and the decided check that $`W_c`$ lies
within $`\Psi_c`$; `certs` from [certificates](#certificates).

### An exceptional return

At an exceptional return the transfer reads $`\Phi^{e}`$, which is
$`\top`$ where the callee states no exceptional bound
([exceptional footprints](../SOURCE-ELABORATION.md#exceptional-footprints)).
The check at a handler's facts runs at $`\Phi^{e}`$, so it keeps a fact
only where its support lies in $`R_C`$ at parts $`\Psi_c`$ allows: in
`throw.mjs` the fact `c.i < xs.length` is lost at the handler and
`0 <= c.i` kept. $`\mathrm{Ch}`$ charges a write at both exits, so the
outside runs' bound is the same at both returns.

### A call of the component's own code

A wrapper, a function of $`C`$ that calls the client at its own call
site, is the callee of a framed call by the definition, and the transfer
covers it: its own steps at the walker's depth are bounded by $`W_c`$,
its calls of the client by $`\Psi_j`$. `wrapper.mjs` shows both
obligations: a wrapper writing the walker's cursor (charged by $`W_c`$,
the fact fails) and a client shortening the walker's array through the
wrapper (outside storage off $`R_C`$, bounded by the wrapper's effect at
the walker's slots, $`\top`$; the fact fails). Astra's run of a wrapper
that calls a no-op client and then increments the walker's cursor through
a closure of the walker's frame is covered the same way: the write is a
write of a code of $`\mathrm{seg}(c)`$, charged at the cursor's site,
since $`\mathrm{Ch}`$ discharges nothing.

The obligation $`\Theta_C`$ binds the client the wrapper calls as it binds
one an entry calls: `ClientFrame.Keeps` constrains every step of outside
code keeping the number of calls of $`C`$ active, wherever the call came
from, against the protection of the history at that step.

The note's rule reads, with the generalized premise:

```math
\frac{c:\Phi\mid\Phi^{e}\qquad c\ \text{a call inside a call of}\ C\ \text{whose run may reach code outside}\ C\qquad W_c\ \text{bounds its steps of}\ C\text{'s code at the caller's depth}\qquad \text{(S)}\quad\text{(K)}}{c:\ \Phi\oplus_C(\Psi_C\sqcup\Theta_C\sqcup W_c)\ \mid\ \Phi^{e}\oplus_C(\Psi_C\sqcup\Theta_C\sqcup W_c)}
```

At a call of outside code alone $`\mathrm{seg}(c)=\emptyset`$,
$`W_c=\mathsf{keep}`$ and the rule is the note's. The note's section "The
rule" and Appendix A take this statement when it is built.

### The check at a call

At a framed call node $`l`$ of code $`m`$, for each fact the ordinary
transfer drops, the pass runs the frame's check of its support for
**every** context of $`m`$ and **every** node $`l'`$ of $`m`$ with $`l`$'s
continuation and handler, and keeps the fact where all pass.
`framed_at_innermost_keys` (proved) gives `Framed` at some such context
and node at every reached state whose innermost frame is a frame of
$`m`$, whatever the callee; the conjunction covers it. The `π.out` filter
of `framed_at_call` is not applied: at a wrapper's call it can select no
node.

- **Keys.** Every location has the key `none` (`NoKeys`, `reached_key`,
  proved); a protocol entry at `none` is read through
  `ComponentChecks.Ctx.boundAt`, which joins every entry of the site and
  kind and the client change, so `noKeys` is sound for `Framed`.
- **The part universe** (Fable 4). `callParts` gives a region with no
  sites (`.fields`, `.pathFields`, `.cls`, `.all`) the full part set
  $`U=(\mathrm{sites}(F)\cup\{\mathsf{none}\})\times\mathrm{kinds}\times\{\mathsf{none}\}`$,
  a finite list, with `regionSites` returning `some U` for it, so
  `frameCheckAt`'s `isSome` conjunct holds of every region. Its cover
  premise is `sites_in_flow` (to be proved): every location of a reached
  state has its site among the flow's sites or `none`, by induction along
  the execution (`stepAt_site`, proved: a step's fresh locations get
  `stepSite`, a site of the flow's allocation tables, or `none` at a step
  of outside code; the start's sites are those the threaded history gave,
  [the frame](#the-frame-of-a-request)). `framed_of_cover` (to be proved,
  the cover generalization of `framed_of_sites`) gives `Framed` from it.
  Observed (`NoSites.lean`): at the base `callParts` gives `[]` and
  `frameCheck` passes on `.all` at every protocol; with $`U`$ the check at
  `.all` requires $`\Psi_c(p)\sqsubseteq\delta`$ at every part and every
  entry of $`\Phi_\star`$ within $`\delta`$.

### Protection

A region is read protected (`prot`) where its every location at the call
was reached, read-only, at the entry from an entry argument at its
parameter's type: then `witness_reached` gives each such location a live
witness at the call. A region comes to include a location the entry did
not reach where a write on its path changes a reference: Astra's
counter-model replaces `root.p` (`undefined` at the entry) by an existing
`child` within `scalar`, and `Region.path 0 ["p"] "i"` then includes
`child.i`. So `prot` requires the path's references fixed since the entry:

- **its root** is the entry's argument: the region's root slot at node
  $`l`$ carries the parameter's slot from the request's start along every
  graph path (`entryRootB`, decided over the edges' `mapIdx`; its
  soundness `entryRoot_sound`, to be proved by induction on graph paths
  with `carriesB_sound`, proved);
- **each part its path passes before the last location** is
  $`\mathsf{keep}`$ under $`\Psi_j`$ and under $`\mathrm{Ch}`$ of the
  unit's own codes (the unit's steps between the entry and the call are
  steps of $`C`$'s code at depth $`1`$, `within_charges` at the unit's own
  call).

Then `witness_of_path` (to be proved, induction on the path): each
location the path passes at the call is the one it passed at the entry,
every step between changing it within $`\mathsf{keep}`$; so the last is
reached at the entry by a read-only path, and `witness_reached` applies.
Every other region is read unprotected, which loses precision only
(`frameCheck` checks both $`\Psi_c`$ and $`\Phi_\star`$ at a lent part).
The history records no crossing into $`C`$ after the entry (`actualXs`), so
no location becomes protected later.

## Certificates

A member's certificate states, of each actual call of a code from a
reached state, the bound and the guarantees over every step of that call's
trace, the entering step and the exit included.

```lean
/-- The trace of a call of `m` from `a`: its entering step `a → a₁`, then
the execution from `a₁` while the call is active, to `y`. -/
def CallTrace (Adm) (m : Option Code) (a y : Conf × Ghost (F.at C)) : Prop :=
  ∃ a₁ n, Adm a ∧ XStep F C c Θ chk a a₁ ∧ entered c a₁.1.t = m ∧ δ F C c a₁ = δ F C c a + 1 ∧
    Ex (XStep F C c Θ chk) (QCall F C c (δ F C c a)) n a₁ y

structure Cert (Adm) (Ψ : Protocol (F.at C)) (G : (St (F.at C) → Prop) → Prop) (m : Option Code) where
  /-- every own step of the call (the entering step, its steps of C's code at
  its depth, its exit) is within Ψ below the entry's length -/
  own : ∀ a y z, (y = a ∨ CallTrace Adm m a y) → XStep F C c Θ chk y z →
    OwnStep a y z → StepWithin Ψ a.1.s.h.length (lift F C c y.1 y.2) (lift F C c z.1 z.2)
  /-- every own step keeps each invariant of G -/
  tolerant : ∀ I, G I → ∀ a y z, (y = a ∨ CallTrace Adm m a y) → XStep F C c Θ chk y z →
    OwnStep a y z → I (lift F C c y.1 y.2) → I (lift F C c z.1 z.2)
```

`OwnStep a y z`: the step from `y` is the entering step (`y = a`) or a
step at the call's depth $`\delta(a)+1`$ of $`C`$'s code (the exit among
them). The entering step pushes the history, so an invariant that reads
the history's depth fails `tolerant` there (Astra's counter-model: "the
stack has its pre-call length and the cell is false" holds before and
fails after the entry, and the earlier statement kept it vacuously).

- **`Member` over the trace.** `Member.Call d Inner st st'` becomes a
  trace of the call with its inner segments: the steps of `MemberRun.Own`
  are the trace's own steps, each `Inner` segment the trace's maximal run
  of outside code one call deeper, so `Cert.own` and `Cert.tolerant` are
  read on the steps the run consists of. `decompose` (proved) is restated
  with this `Member.Call`; its induction is the same, prepending the
  entering step as it does now.
- **The joined protocol.** Certificates are at $`\Psi_j=\Psi_C\sqcup\Theta_C`$,
  the protocol their inner runs are bounded at, so `Run.bound`'s
  $`\Theta_C\sqsubseteq\Psi_j`$ holds; Astra's separating instance
  ($`\Theta=\mathsf{any}`$, $`\Psi=\mathsf{keep}`$, $`\Psi_c=\mathsf{any}`$)
  does not arise.
- **From the charges** (`cert_of_charges`, to be proved): `own` from
  `within_charges` ($`\Psi_C\sqsubseteq\Psi_j`$; the entering step changes
  no old location); the same certificate for every code $`m`$, since
  $`\mathrm{Ch}`$ charges every write of every code. `tolerant`: vacuous at
  $`G=\emptyset`$; for the guarantee route, from `keeps_of_charges`
  (proved) at each own step and from the invariant reading the heap, the
  sites and the keys alone (`HeapOnly I`, a condition on $`G_C`$'s
  candidates), so the entering and exiting steps, which change the
  history and allocate, keep it.

## Re-entry

A callback re-entering $`C`$ creates calls of $`C`$ deeper than the
claim's top frame. The claim reads three things of such a call, none a
fact of it:

1. its effect on $`R_C`$: the certificate, from $`\mathrm{Ch}`$, which
   reads the lowered writes and the flow (an element write is charged
   $`\mathsf{any}`$ whatever its index);
2. its progress and typed heap inside the callback's run: the callback's
   semantic type ([callers and callbacks](#callers-and-callbacks));
3. its facts: read by no clause of the claim. The clauses read a stated
   assertion at a state whose whole term runs the claim's graph at its
   label (`AssertedAt`: `t' = gotoOf P l L' d' c'`) and the posts at the
   claim's exit; the graph's facts are delivered at the claim's top
   frame. A re-entered call's frames lie inside a callback's run inside
   that frame.

So the witnesses the claim needs are those of its own top frame, from its
own entry ([protection](#protection)). This holds while the charges read
no fact and the history records no crossing into $`C`$ after the entry,
both properties of this design.

## The guarantee route

The bound route ($`G_C=\emptyset`$) reads no ownership. The guarantee
route keeps $`I\in G_C`$ across a framed call where `Supported` cannot
state it: an installed array of equal length keeps
`flags.length === widths.length` while the field `widths` changes
identity, beyond `grow` (Astra: `Change.grow.Holds` is false between two
distinct object identities; observed under Node, the invariant true and the
field changed). So the graph's return premise at a framed call includes,
for each invariant $`(I,\mathit{root})`$ the frame keeps there, the
invariant itself ([the graph at framed returns](#the-graph-at-framed-returns)):
$`I_{\mathit{root}}(\rho,h_0)\Rightarrow I_{\mathit{root}}(\rho,h_1)`$.
It is discharged by `framed_guarantee` (to be proved), the guarantee
analogue of `framed_transfer`: along the segment `InvIn I supp` holds at
every state; at an outside step by `SupportAt.outside` (proved), whose
`keeps` and `stays` hold of a path support (below) whose parts
$`\Theta_C`$ tolerates (decided by `SupportParts` over the support's
parts); at an own step by `invIn_of_installs` (proved), with $`I`$ after
the step from `keeps_of_charges` (proved), and `hsup`, `hnew` from:

- **A path support.** $`\mathrm{supp}(I)`$ at a state is the set of
  locations on a fixed finite set of field paths $`\Pi`$ from the root
  (`PathSupport`). `Ctx.supportOf` falls back to the whole reachable
  storage where a fact gives no paths (Astra: `factPaths (.element 0 1 2)`
  is `none`); a candidate whose support is that fallback is not in
  $`G_C`$ (decided, `pathSupportB`), so the route applies to path
  supports, and a fact of the fallback form takes the bound route.
- **A new location is reached through a write** (`supp_split`, to be
  proved, from `follows_split`, proved): for a step $`t\to t'`$ and
  $`l\in\mathrm{supp}_{t'}`$, $`l\in\mathrm{supp}_t`$, or the path to $`l`$
  has a first location $`w`$ the step changed, $`w\in\mathrm{supp}_t`$,
  and $`l`$ is reached from $`w`$'s new value.
- **Every write the support reads is classified** (`protectedInto_of_supp`,
  to be proved, giving `hsup`): $`w\in\mathrm{supp}_t\subseteq R_C(t)`$,
  so $`w`$ is local (its part in `Ctx.supportOf`, by `stepWrites_sound`
  and `pathSites`, so `cx.supported`; `protectedInto_local`, proved),
  exposed (`protectedInto_exposed`, proved) or outside storage protected
  at the entry (the receiver's tokens hold the component's token for a
  value entering from outside, from the entry's supplied slots). No
  released location lies in $`R_C`$: no crossing into $`C`$ after the
  entry is recorded.
- **`hnew`** (`hnew_of_paths`, to be proved): by `supp_split`, a new
  location is reached from a value of a classified store whose (O) check
  passed, the disjunct `invIn_of_installs` takes.

**At the entry**: the invariant holds of the entry's handle argument by
`EntryHolds` (the request's input at the handle type means its
representation meeting `@invariant`, the row on handle parameters), and
its support lies in $`R_C`$ by the entry's crossing at the read-only
handle type. Observed (`redirect.mjs`, `NaN`): a re-entered member storing
the client's writable array in the handle's field; the store is into
$`\mathrm{supp}_t`$, classified, and (O) refuses it (`installIncoming`).

## The frame of a request

The claim's calls and its frame are fixed by the request and the
program's semantics; the wire's proposals are checked against them.

### The calls the claim is about

**A public call** of the request $`r`$ (`PublicCall r h L d`, new, read
from no wire datum): there is a program, an initial configuration
$`x_0`$, and an execution from $`x_0`$, every step of which keeps
$`\Theta_C`$ at the history threaded from $`x_0`$, to a state whose active
frame is outside $`C`$ and whose next step invokes $`r`$'s module closure
with arguments `L` and receiver `d`, the heap being `h`. An initial
configuration: an empty heap, a term that is outside code's lowered
source (`LoweredSrc`, closed) with $`C`$'s module closures as values,
$`C`$'s module initialization run first as $`C`$'s code. Its history is
`bareStart`.

```lean
def FrameSpec.frame (spec : FrameSpec ι) (r : SourceRequest σ ι) : ClientFrame (Ty ι) where
  enters h t := ∃ L d, t = gotoOf r.program r.start L d r.comp ∧ PublicCall r h L d
  start k W h t g := ∃ L d g₀, t = gotoOf r.program r.start L d r.comp ∧ ThreadedAt r h L d g₀ ∧
    g = Ghost.crosses tv h (inputsAt r L d) ({ g₀ with A := [g₀.Prot] }.enter)
  ...
```

`ThreadedAt r h L d g₀`: $`g_0`$ is the history threaded along such an
execution at the invoking state. The start truncates the history to one
set, which keeps every protection (observed: `Truncate.lean`,
`truncate_prot`, `truncate_uniform`), pushes the call's set and lets the
arguments cross in at the request's input types (`inputsAt`: `r.inputs`
at the entry's slots, read from the request). `start_total` holds with
`bareStart` at a state no execution reaches.

So `enters` is the set of the request's actual public calls: no proposal
narrows it (the vacuity of `Vacuous.lean` needs an `enters` admitting no
call), and the conclusion of `mode8Accepted_sound` holds of each public
call of each program whose clients keep $`\Theta_C`$ up to and through the
call. A call inside a callback, at a depth above zero, is a public call
too.

**What the flow gives at a public call** (to be proved), replacing the
premise `EntryShape` (whose clause on every heap value fails for a
private closure in the heap, Astra):

- `fits_program`: from an initial configuration meeting the flow
  (`initFits`, decided: the module closures in the term meet $`O`$ with
  their captures at their codes' capture slots; the heap is empty), every
  state of every execution fits $`O`$ at a position of outside code and
  its heap meets the flow at the threaded history (the proof of
  `fitsAt_reached`, proved, from this start: `fits_step` keeps a fitting
  term, `HeapInv.set`, `HeapInv.fresh` the heap, `stepAt_site` the fresh
  sites). A private closure held in $`C`$'s storage meets its site's
  contents; no clause asks it to be one $`C`$ gave out.
- `entryFits_public`: at a public call the claim's start fits: the invoked
  closure meets $`O`$ (`fits_roots`, proved), so its token is in $`O`$ and
  its code is open at its entry context, whose slots hold the arguments
  (`fits_graphEntry`, proved), and the heap meets the flow at the
  truncated history (the sites unchanged). This is `EntryFits`; with
  `Flow.Facts` (`FFlow.check_sound`), `FlowSites` and `ActualCrossings`
  (by `chk`) it gives `ChkSound` (`chkSound_of_sites`,
  `sitesSound_of_fits`, proved).
- `startInv_public`: the invariants of states hold along the execution
  from $`x_0`$ (`Inv` at the empty heap; `XStep.inv`, `Ex.inv`, proved),
  and the start meets `StartInv` (one set; `enter` and the crossings keep
  `Inv`, `crosses_uniform`, proved).
- `witness_public`: an entry argument reaches its locations read-only at
  the start's crossing, so `entryStart_prot`'s proof (proved) gives them
  protected at the start and `witness_along` (proved) at every later state
  of the call; `witness_reached` is restated at this start.

### The binding checks

Decided by the verifier from the request, the fragment's components and
the lowered code, each with a forged-fragment control:

- **codes**: the flow holds, at its entry context and at every context the
  check quantifies over, a proposal for each code of $`C`$ by content: the
  request's program and its codes, every module function of $`C`$'s
  modules and their closures' codes, and each module's initialization
  (`codesCoverB`). The frame's `codes` are these codes, computed from the
  request and the module realization, never from the wire. A flow omitting
  the walker's code (`forged-flow.mjs`) fails it.
- **the component**: $`C`$ is `componentAt` of the request's place (the
  outermost component of the family the request's tag runs in), and the
  family's tags of $`C`$ are those the lowering assigns to $`C`$'s modules
  (`compB`).
- **the entry**: `entryB` at the request's own code and start
  (`(r.program, r.start)` at `entryCx`), its slots naming signatures only
  at the sibling slots, each the module closure's signature (`entryFnB`).
- **the inputs**: `args` are `inputsAt r`, computed; the wire carries no
  entry types.
- **$`\Theta_C`$**: the component's `@clients` read from the source's
  declaration document, equal to the wire's (`clientsB`); the verdict line
  prints it.
- **the protocol**: the wire's $`\Psi_C`$ at least $`\mathrm{Ch}`$ as
  defined in [charges](#charges), at every part of $`U`$.

### The plan

```lean
inductive FunctionPlan (σ ι : Type) [Labels ι] [StoreView σ ι] where
  | graph (name : String) (namePos : Span) (request : SourceRequest σ ι)
  | framed (name : String) (namePos : Span) (request : SourceRequest σ ι) (spec : FrameSpec ι)

def FunctionPlan.certify : FunctionPlan σ ι → Except String (CertifiedPlan σ ι)
  | .graph name pos request => pure (.graph name pos request)
  | .framed name pos request spec => pure (.framed name pos request (spec.frame request))
```

`FunctionPlan.over` maps the request and the spec. `FrameSpec ι` holds the
proposals alone: the family's numbering, the finite flow (`FFlow`, its
marks the ones it gives, `FFlow.MarksFrom`), the proposed $`\Psi_C`$ and
$`\Theta_C`$ (checked as above), and for each framed call node the
supports and the invariants kept at its continuation and handler.
`spec.frame request` takes `codes`, `C`, `enters`, `start` and the inputs
from the request. Its `view` is `ViewOver (Ty ι)` with `RO T` the type
reader's "read-only throughout" of `T`, and
`child T a := if RO T then T.readonlyChild a else T.child a`, a read-only
type's every child read-only by construction, so `ro_child` holds by
definition; unions, generics and recursive types are read by the type
reader's own `child`, and a type it cannot decide is not read-only. `chk`
is the flow's `stepSite` for fresh locations, the key `none`, and
`actualXs`, so `FlowSites`, `NoKeys` and `ActualCrossings` hold by
definition.

`PlanAt` and `OverStore` (`PassUnitPlans.lean`) are restated over both
constructors (`PlanAt f i name pos r` holds of a graph or a framed plan
with request `r`; `over_types` per constructor), so `hover` types at a
framed plan.

### What the pass checks

`MemberAccepted.framed`, beside `ordinary`'s premises over the request:

- `FFlow.check (remark F)`, `marksB`, `initFits`, and the binding checks;
- (S), (K), (O) over every body of the component (`ComponentChecks`), (S)
  the restriction *No suspension*;
- $`\Psi_C\sqsupseteq\mathrm{Ch}`$; at each framed call node $`c`$,
  $`W_c=\mathrm{Ch}(\mathrm{seg}(c))`$ computed and the supports kept by
  the check at $`\Psi_c`$ ([the check at a call](#the-check-at-a-call)),
  at $`\Phi`$ for the continuation's facts and $`\Phi^{e}`$ for the
  handler's;
- the request's main graph and each of its codes' graphs accepted by the
  framed run with those supports kept (`RunCall.AcceptsFramed`).

## Callers and callbacks

### The callback's type

The graph reads a callee value at its arrow's ordinary semantic type
(`call_local_sound`): its call is safe from every heap, its calls back
into $`C`$ included. A client callback that calls a framed member of
$`C`$ meets that only where the member is safe on executions breaking
$`\Theta_C`$, which no framed claim proves. The design states it as trust,
one row of its own:

> **Callbacks into a framed component.** A function value that code
> outside a component $`C`$ whose API states the read-only row passes to
> $`C`$ at a function type meets that type: called by $`C`$, its run,
> its calls of $`C`$ included, is safe and within its stated effect.

Each framed claim proves the member's safety along the executions keeping
$`\Theta_C`$, the only ones it is about; the row is stronger. Its
replacement by a derivation is milestone 3: the arrow
$`[\![T]\!]^{\Theta}`$ whose call is `SafeUnder fr.Keeps` from every
reached state, read for outside callees and framed members alike, with
`call_local_sound_under` giving `SafeUnder` from it.

**The continuation after a failed return premise** is outside the claim:
a callback emptying the walker's `[7]` and returning normally makes the
next read `undefined` (Astra, observed). `RunSoundFramed` claims progress
at the states of the paths whose framed returns meet their premise, and
`framed_requestSafe` establishes the premise (`ret_reached`) before it
follows the continuation; after a step that broke $`\Theta_C`$ the claim
states nothing (`SafeUnder`).

### Callers inside the component and importers

`dependent.mjs` (observed `NaN`): an ordinary unit `total` calling a framed
`walk` is accepted with no trust stated, its graph reading `walk` at its
ordinary arrow, which `FramedRequestSafe` does not give. The design:

- **A unit whose graph reads a framed member** (through a sibling slot,
  `SourceRequest.siblings`, or any value whose type the graph reads from a
  framed member's signature) is refused at that read, located there
  ("calls a function accepted under client trust", a check of
  `passMember`), until the obligation-relative arrow exists. No ordinary
  verdict rests on a framed claim; `total` is refused.
- **The verdict line** of a group with a framed member is
  `accept under client trust Θ_C (component C)`, naming $`\Theta_C`$ and
  $`C`$.
- **Importers**: `FilePlans.establishVerdict` refuses to establish a
  framed group (`MemberSettle.lean`), so a module importing a framed unit
  is refused at the import; the interface document carries no framed
  arrow.
- With the obligation-relative arrow (milestone 3), a unit reading a
  framed member at $`[\![T]\!]^{\Theta}`$ certifies to a framed plan with
  the same frame, its label propagated along `depends`, and the interface
  carries $`\Theta_C`$ with the arrow. Pretext's layout functions, which
  call the walkers, need that milestone.

## Scope

- **Frames.** The transfer is applied at the top frame of each claim: the
  request's graph and each of its codes' graphs (each code's clause runs
  its own graph as the whole term). A framed call in another function is
  that function's unit's. So every call node of every graph the plan
  checks is covered.
- **Keys.** The check reads every location at the key `none`: one protocol
  entry bounds every field of a site's records. Facts that need two fields
  of one record told apart (pretext's `prepared.widths` beside the `stats`
  writes) are outside this design's precision; they are refused, located
  at the part that fails.
- **Charges discharge nothing as fresh**: a write to storage the writing
  frame allocated is charged at its site, so a fact about another location
  of that site is lost.

## The theorems

### The graph at framed returns

`RunSoundFramed ι` (to be proved) replaces `Target.RunSound`: for an
accepted run whose framed call nodes $`l`$ keep supports $`S_l`$,
$`S^{e}_l`$ and invariants $`G_l`$, $`G^{e}_l`$, each field of
`GraphGuarantee` holds along the graph paths whose every evaluation of a
framed node, from its entry $`(\rho,h)`$ to its return $`(v,h')`$, meets

```math
\mathrm{Ret}_l(\rho,h,h')\iff\bigl(\forall S\in S_l.\ \mathrm{Supported}(S,\rho,h,h')\bigr)\wedge\bigl(\forall (I,\mathit{root})\in G_l.\ I_{\mathit{root}}(\rho,h)\Rightarrow I_{\mathit{root}}(\rho,h')\bigr)
```

and $`\mathrm{Ret}^{e}_l`$ alike at an exceptional return; its states past
an evaluation that fails it are outside the claim. `Target.RunSound` is
the instance with no framed node (`runSound_of_framed`, to be proved:
$`\mathrm{Ret}`$ is vacuous), and `run_sound_single_pass` is proved through
it.

The node delivery reads $`\mathrm{Ret}`$ in place of `callerFrame_post`
for the kept supports (`callKept_sound`, `callGrown_sound`, `frameKeeps`,
proved, read `Supported` through `Footprints.frame_step`), and the kept
invariants as known after the call; the rest of the call's delivery is as
at an ordinary call: the support's condition `FirstKept` read from the
callee's post (`callEntry_holds`'s premise `hstable`), the continuation's
facts at `push v ρ` through the continuation's mapping, the handler's at
the thrown value through the handler's. The graph state carries the
pending framed node's entry (`SafeGraphRet`, a `SafeGraph` with that
datum, as `SafeUnder` is a `SafePostExcW` with a ghost).

### The returns, at reached executions

`ret_reached` (to be proved): at every evaluation of a framed node of a
claim's top graph from a reached call state $`s_0`$ to its resumption
$`s_1`$, along steps keeping $`\Theta_C`$, with the callee's post at
$`s_1`$ (`callPost`, or `callExc` at a throw), $`\mathrm{Ret}_l`$ or
$`\mathrm{Ret}^{e}_l`$ holds. The node's entry heap is $`s_0`$'s: the
`goto` at $`l`$ enters its frame (`gotoEnter`, no heap change) and the
call's parts are values, so the frame's term is the call and the first
step of the segment is the invocation. Plan: `framed_transfer` and
`framed_guarantee`, with `ChkSound` and `StartInv` from [the
frame](#the-frame-of-a-request), `certs` from `cert_of_charges`, `hown`
from `within_charges`, `Framed` from `framed_at_innermost_keys`,
`framed_of_cover` and `classQuery_sound` (proved), and the witnesses of
[protection](#protection).

### The framed claim, from the check

```lean
theorem framed_requestSafe {f : FilePlans} {r : Req f} {spec : FrameSpec _}
    (hrun : RunSoundFramed (EquationStore.CheckedLabel f.F.equations f.F.primitive))
    (hkeep : RunKeepsSummaries (EquationStore.CheckedLabel f.F.equations f.F.primitive))
    (htypes : r.types = f.F.store) (hacc : FramedAccepted f r spec) :
    FramedRequestSafe r (spec.frame r)
```

Plan, for each of the six clauses, by induction on the budget, the
invariant at a state being: it is reached from the clause's start
(`Reached`, with the execution), its term simulates a graph state of the
claim's graph (`GraphCode.Sim`, with the pending framed call state), and
that graph state is on a $`\mathrm{Ret}`$-path of `RunSoundFramed`. A step
breaking $`\Theta_C`$ ends the obligation; any other is a `KStep`, mapped
to a transition by `sim_step_back` (proved); at a framed node's return
`ret_reached` gives $`\mathrm{Ret}`$ and the path stays a
$`\mathrm{Ret}`$-path. The assertions: a term state `gotoOf P l L' d' c'`
reached from the start is simulated by the graph state
`.at l (envOf L' d')` reached on a $`\mathrm{Ret}`$-path (`sim_step_back`
along the execution), at which `RunSoundFramed`'s `asserted` gives
`Holds` (`assertedAt_of_graph`, to be proved, the converse direction of
`asserted_of_reach`, proved). The executions are built from the start
without assuming the clause (`framed_reaches`, which assumes it, is not
used).

### The headline

`member_safe` gains the branch `framed … => ⟨_, _, hplan, rfl,
framed_requestSafe hrunF hkeep (hover j name pos r hplan) hacc⟩`, and
`passMember_sound` (H3) shows `passGroup` accepting a group makes a
framed member `MemberAccepted.framed`; the executable path is
`FilePlans.passMember`'s framed branch, which runs the checks above.
`mode8Accepted_sound` keeps its statement:

```lean
theorem mode8Accepted_sound {f : FilePlans} {i : Nat} (h : Mode8Accepted f i) : PassUnitSafe f i
```

- **Premise** `Mode8Accepted f i`: unchanged, the exact CLI condition at
  either print site; a group with a framed member reaches it printed
  `accept under client trust Θ_C (component C)`.
- **Conclusion** `PassUnitSafe f i`: every member of the group is
  `MemberSafe`: a graph plan's request `RequestSafe`, a framed plan's
  `FramedRequestSafe r (spec.frame r)`, that is: at each public call of
  $`r`$ in a program whose outside code keeps $`\Theta_C`$ up to the call,
  from the request's entry contracts, along each continuation keeping
  $`\Theta_C`$, every state is a value, a throw or takes a step with an
  admissible world and a typed heap, and the footprint, postcondition,
  regional and assertion clauses hold. The calls are the program's, so no
  proposal narrows the conclusion.

The commit that builds it records `Theorem modified (mode8Accepted_sound)`
with this conclusion and `MemberSafe`'s reading.

## Proved, to be proved, trust

**Proved at the base**, reused: `FFlow.check_sound`, `fitsAt_reached`
(its proof), `fits_step`, `fits_roots`, `fits_graphEntry`,
`chkSound_of_sites`, `sitesSound_of_fits`, `framed_at_innermost_keys`,
`frameCheck_sound`, `framed_of_sites`, `regionSites_sound`, `reach_sites`,
`reached_key`, `witness_along`, `entryStart_prot`, `crosses_uniform`,
`call_segment`, `decompose`, `Run.bound`, `Run.keeps`,
`MemberRun.within`, `RBoundBelow.trans`, `InR.mono`, `pkg_step_ok`,
`stepWithin_of_check`, `keeps_of_charges`, `readOnly_rule`,
`supported_of_framed`, `invIn_of_installs`, `installs_checked`,
`protectedInto_local`, `protectedInto_exposed`, `SupportAt.outside`,
`follows_split`, `step_changes`, `stepAt_site`, `Fits.innermost`,
`XStep.inv`, `Ex.inv`, `kstep_xstep`, `reached_ok`, `sim_step_back`,
`asserted_of_reach`, `framed_callSafe`, `call_local_sound`,
`callKept_sound`, `callGrown_sound`, `callEntry_holds`, `carriesB_sound`,
`run_sound_single_pass`.

**Observed at the base** (`Truncate.lean`): `truncate_prot`,
`truncate_uniform`, to be moved into the build.

**To be proved**: `local_unreached`, `stepWrites_sound`,
`writesIn_sound`, `within_charges`, `segFrames`, `framed_transfer`,
`seg_run`, `MemberRun.Own` at a depth parameter, `RBound.mono`,
`frameC_shape`, `sites_in_flow`, `framed_of_cover`, `entryRoot_sound`,
`witness_of_path`, the trace-indexed `Cert` and `Member.Call` with
`decompose` restated, `cert_of_charges`, `fits_program`,
`entryFits_public`, `startInv_public`, `witness_public`,
`RunSoundFramed`, `runSound_of_framed`, `ret_reached`,
`assertedAt_of_graph`, `framed_requestSafe`, `PlanAt`/`OverStore` over
both constructors, `member_safe`'s and `passMember_sound`'s framed
branches; for the guarantee route `framed_guarantee`, `supp_split`,
`protectedInto_of_supp`, `hnew_of_paths`.

**Trust**, rows of the [trust surface](../DESIGN.md#trust-surface):

- the client obligation $`\Theta_C`$ (`ClientFrame.Keeps`, `Row`),
  stated in the component's API (owner-approved);
- *Clients* (Read-only frames, Assumption "Clients"): outside code enters
  $`C`$ only through its interface (`Provenance`), and a program's
  outside code is lowered source of the calculus (`Source`, `LoweredSrc`),
  closed (`ClosedAt`), in a well-formed configuration (`Discipline`), as
  the initial configurations of `PublicCall` are;
- **Callbacks into a framed component** (the row above);
- the request's entry contracts at a public call (the existing rows on
  exported preconditions and handle parameters);
- a native's step model performs its model's steps (the `%ElementAt%`
  row), where the flow reads one.

## Milestones

Each is stated generally and buildable on the one before.

1. **The bound route for P22** ($`G_C=\emptyset`$): the charges and their
   lemmas (`local_unreached`, `stepWrites_sound`, `within_charges`,
   `segFrames`), the trace-indexed certificates, the general
   `framed_transfer` at every framed call, the check at a call over $`U`$,
   the frame of a request with `PublicCall` and the binding checks
   (`fits_program`, `entryFits_public`), `RunSoundFramed` with supports
   only, `framed_requestSafe`, the plan and the headline, the refusal of
   readers of framed members. `prot` is false at every region in this
   milestone; P22 reads none.
2. **Protection and the guarantee route**: `entryRoot_sound`,
   `witness_of_path`; `framed_guarantee` with path supports.
3. **The obligation-relative arrow**: $`[\![T]\!]^{\Theta}`$ replacing the
   callback row, framed callers and importers, the label along `depends`.
4. **Keys**: parts at field keys, for facts such as pretext's
   `prepared.widths`.

## Tests

- **P22**, `bounds-pattern-unreachable-field-refused` (a gap, positive at
  milestone 1, renamed with its outcome). `visit(c.i)` is a framed call
  of outside code, $`W_c=\mathsf{keep}`$. The cursor's site is local and
  in no capture slot, so $`\Psi_C`$ is $`\mathsf{keep}`$ there, though
  `walk`'s own `c.i++` is charged at it in $`\mathrm{Ch}`$; `xs`'s spine
  is outside storage, off $`R_C`$, bounded by the visitor's
  $`\mathsf{grow}`$. `c.i < xs.length` and `0 <= c.i` pass (measured by
  the frame probe, [read-only handles](readonly-handles.md#deciding-the-flow)).
- **Kept negative**: `invalid-bounds-pattern-cursor-given`.
- **New cases**: `throw.mjs`'s walker (negative at the handler read) and
  its variant reading only `0 <= c.i` there (positive); a wrapper calling
  the client, the walker keeping its local cursor (positive); a wrapper
  writing the cursor, and a wrapper incrementing it through a capture
  (negative); a client shortening the array through a wrapper (negative);
  `capture.mjs`'s walker (negative); `dependent.mjs`'s `total` (refused at
  its read of `walk`).
- **Controls** (forged fragments against the verifier): a flow omitting
  the walker's code (`codesCoverB`); a flow whose entry context names a
  signature at a non-sibling slot (`entryFnB`); a wire $`\Theta_C`$ other
  than the source's (`clientsB`); a $`\Psi_C`$ below $`\mathrm{Ch}`$; a
  framed call whose check passes at one node of the call's continuation
  and handler and fails at another (the fact dropped); a region `.all` at
  a protocol changing a part (the fact dropped, `NoSites.lean`'s case).
- **Pretext's walkers**: their cursor bounds at local sites, measured by
  the probe at the direct-call obligation (the raw walker's two
  segment-index bounds and grapheme-index lower bound at 8/8 contexts, the
  complex walker's segment-index bounds at 3/4), across the wrapper
  `onLine`; the `prepared.widths` facts need milestone 4, and the layout
  functions calling the walkers milestone 3.

## Open points for review

1. **`PublicCall`'s initial configurations**: the module initialization as
   $`C`$'s code before the client's top level, and `initFits` at it, are
   stated over a program realization the calculus has for one module
   (`PassUnitFile`, the module realization); a package of modules needs
   their initialization order.
2. **`stepWrites_sound`** rests on the node expression's writes being the
   only writing redexes of a frame's steps, natives' step models included;
   a native without a step model is outside code, which `Fits.invoke`
   states.
3. **The local rule's sources**: `local_unreached` reads captures of
   closures of $`C`$ only; a bound function's parts and a closure of
   outside code's captures reach no local site (`CodeNoLocal`), a reading
   of the value judgment for the proof to confirm.
4. **The callback row** is a new trust row, stronger than each framed
   claim; it is for the owner, until milestone 3 replaces it.
5. **`RunSoundFramed`'s size**: threading $`\mathrm{Ret}`$ through the
   graph theorem touches the call node's delivery and the path predicate,
   a reading of `run_sound_pass`'s structure, not yet a build.

## Runs

Node 26.13.0, each printing the value shown; sources below, and
`forged-flow.mjs` and `dependent.mjs` as the second review gives them:

- `throw.mjs`: `{ s: NaN, i: 2 }`, a visitor shortens `xs` and throws, the
  handler reads `xs[c.i]`;
- `wrapper.mjs`: `NaN`, `NaN`, a client shortens `xs` through a wrapper; a
  wrapper writes the walker's cursor;
- `redirect.mjs`: `NaN`, a re-entered member installs the client's array
  in a handle's field, the client shortens it;
- `capture.mjs`: `NaN`, a closure of $`C`$ capturing the walker's cursor,
  given to the visitor and called, writes the cursor;
- `forged-flow.mjs`: `NaN`, the cursor given to the visitor;
- `dependent.mjs`: `NaN`, an ordinary caller of a framed walker, the
  client shortening a `readonly number[]` it passed.

Lean files checked with `lake env lean` at the base, standard axioms only:
`Vacuous.lean` (every request is `FramedRequestSafe` at a frame admitting
no call), `EmptyFlow.lean` (an empty flow passes `FFlow.check` and
`marksB`, and admits no `EntryShape`), `NoSites.lean` (`callParts` gives
`[]` for `.all` and `frameCheck` passes on it), `Truncate.lean` (a history
truncated to its one set protects what it protected, and is uniform).

```js
// capture.mjs
function walk(xs, visit) {
  const c = { i: 0 }; let s = 0;
  const bump = () => { c.i += 5; };
  while (c.i < xs.length) { visit(bump); s += xs[c.i]; c.i++; }
  return s;
}
console.log(walk([1, 2, 3], (f) => f()));
```

```js
// throw.mjs
function walk(xs, visit) {
  const c = { i: 0 }; let s = 0;
  while (c.i < xs.length) { try { visit(c.i); } catch { s += xs[c.i]; } c.i++; }
  return { s, i: c.i };
}
const xs = [1, 2, 3];
console.log(walk(xs, (i) => { if (i === 1) { xs.length = 0; throw new Error("stop"); } }));
```

```js
// wrapper.mjs
function walk(xs, onLine) {
  const c = { i: 0 }; let s = 0;
  while (c.i < xs.length) { onLine(c.i); s += xs[c.i]; c.i++; }
  return s;
}
function layout(xs, user) { return walk(xs, (i) => user(i)); }
const xs = [1, 2, 3];
console.log(layout(xs, (i) => { if (i === 1) xs.length = 1; }));
function walk2(xs, onLine) {
  const c = { i: 0 }; let s = 0;
  while (c.i < xs.length) { onLine(c); s += xs[c.i]; c.i++; }
  return s;
}
function layout2(xs, user) { return walk2(xs, (c) => { user(); c.i = c.i + 5; }); }
console.log(layout2([1, 2, 3], () => {}));
```

```js
// redirect.mjs
function prepare(n) { return { buf: new Array(n).fill(1), n }; }   // invariant: buf.length === n
function rebind(h, arr) { if (arr.length === h.n) h.buf = arr; }
function walk(h, visit) {
  let s = 0;
  for (let i = 0; i < h.n; i++) { visit(); s += h.buf[i]; }
  return s;
}
const h = prepare(3), mine = [5, 5, 5];
let first = true;
console.log(walk(h, () => { if (first) { first = false; rebind(h, mine); } else { mine.length = 0; } }));
```

```lean
-- Truncate.lean
theorem truncate_prot {P : Package} (g : Ghost P) (l : Nat) :
    ({ g with A := [g.Prot] } : Ghost P).Prot l ↔ g.Prot l
theorem truncate_uniform {P : Package} (g : Ghost P) : ({ g with A := [g.Prot] } : Ghost P).Uniform
```
