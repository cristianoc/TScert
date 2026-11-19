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

Base: branch `p22-accept` at `cc69530a2`. Notation is that of
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
   call ([charges](#charges)), and indexes certificates by the calls an
   execution makes ([certificates](#certificates)).
3. **The acceptance path** (CLAUDE.md, "Acceptance/soundness invariant").
   `CertifiedPlan.framed`, `PassUnit.FramedRequestSafe` and `MemberSafe`'s
   branch reading it exist (proved: `framed_callSafe`,
   `callSafe_of_member`); no `FunctionPlan` certifies to a framed plan.
   This design adds `FunctionPlan.framed`, its branch of `certify`, the
   constructor `MemberAccepted.framed`, and `framed_requestSafe`, at a frame
   whose calls are the actual public calls of programs
   ([the frame of a request](#the-frame-of-a-request)).

## Findings this design closes

Each finding is a property of the base or of an earlier version of this
draft, verified by a run or by reading the Lean named, with the section
that closes it. A premise moves into a theorem to be proved, a decided
check, a restriction, or a row of trust.

**The first round.**

- **Gaps of the proved results**: (1) `framed_at_call` gives `Framed`
  before the invocation and `call_rely` reads it after it
  ([the transfer](#the-transfer-at-a-call)); (2) a callback may shorten an
  array and throw (`throw.mjs`, [an exceptional return](#an-exceptional-return));
  (3) a re-entered member's fresh arguments have no witness
  ([re-entry](#re-entry)); (4) `Cert.tolerant` ranges over every `PkgStep`
  ([certificates](#certificates)); (5) the guarantee route's `hsup` and
  `hnew` ([the guarantee route](#the-guarantee-route)).
- **Vacuity** (Astra 1, Fable 1): every request is `FramedRequestSafe` at a
  frame admitting no call (`Vacuous.lean`); an empty flow passes the flow
  checks (`EmptyFlow.lean`); a flow omitting the walker's code keeps a
  broken fact (`forged-flow.mjs`). Closed by the frame of a request.
- **The guarantee's return** (Astra 2), **the entering step and the joined
  protocol** (Astra 3, Fable 7), **a redirected path** (Astra 4),
  **charges tied to the lowered code** (Astra 5), **callers and the
  callback's type** (Fable 2, 3, Astra 6, `dependent.mjs`), **`callParts`'
  universe** (Fable 4, `NoSites.lean`), **local storage** (Fable 6),
  **generality** (Fable 5), **build interfaces** (Astra 7, Fable 9):
  closed in the sections below, as the second round refines them.

**The second round.**

- **The start** (Astra 1, Fable N4): the start with `enter` holds two sets
  where the entry's `goto` holds one call of $`C`$, so it meets no
  `StartInv` (`StartLen.lean`), and it was not total. Closed: the start has
  no `enter`, and a `bareStart` branch at every other state
  ([the calls the claim is about](#the-calls-the-claim-is-about);
  `Round3.lean`, `startFix_startInv_len`).
- **`PublicCall`** (Astra 2, Fable N5): no world; an initial configuration
  holding closures, which lowered source cannot hold (`Round3.lean`,
  `loweredSrc_no_closure`); the raw actuals where `graphEntry` builds the
  slots, runs a prologue and allocates a rest; protection read from the
  proposal; the client term's fit; units that are no module closure.
  Closed in [the calls the claim is about](#the-calls-the-claim-is-about).
- **The codes and the sixth clause** (Astra 3, Fable N1, N3): a frame
  admitting only the main entry makes the code clause vacuous
  (`CodeClause.lean`, `codeClause_vacuous`; `Round3.lean`,
  `gotoOf_start_ne`), and a code checked by a framed run gives its closure
  no ordinary arrow (`returned-closure.mjs`, `NaN`). Closed: the codes are
  checked by the ordinary pass, and the sixth clause is the ordinary one
  ([the plan](#the-plan)).
- **$`W_c`$ refuses P22** (Astra 4, Fable N2): the callee's set at
  `visit(c.i)` holds `walk`'s own token (Astra's probe run, node 13, the
  callee slot `[none, some 2, some 33]`, `walk`'s token `some 2`;
  `CodeClause.lean`, `entry_slot_holds_O_tokens`), so $`W_c`$ charged
  `c.i++` at the cursor; and a closure of $`C`$ handed out runs at the
  caller's depth (`o-callee.mjs`). Closed by one local lemma at the base
  of any call ([charges](#charges)).
- **`Cert.own` at `y = a`, the inner depth** (Astra 5): the entering case
  carried no entering edge, so it ranged over a body step such as
  `c.i++` (`Round3.lean`, `keep_rejects`); a segment's inner runs are at
  the caller's depth. Closed in [certificates](#certificates) and
  [the transfer](#the-transfer-at-a-call).
- **A writable prefix** (Astra 6): `keep` at a part outside $`R_C`$ bounds
  no outside write (`prefix.mjs`, `undefined`). Closed in
  [protection](#protection).
- **The guarantee's proof** (Astra 7): charges at `any` cannot tell an
  invariant-keeping store from a breaking one (`install.mjs`,
  `true false`); a released location an entry crossing protects is in
  $`R_C`$ (`Round3.lean`, `released_prot_inR`); a heap-only predicate is not
  stable under allocation; `EntryHolds` holds no `@invariant` conjunct.
  Closed in [the guarantee route](#the-guarantee-route).
- **Verdicts reading a framed member's arrow** (Astra 8, Fable N6, N7): an
  ordinary unit given a framed member as a value (`apply.mjs`, `NaN`), a
  recursive walker, the callback row. Closed in
  [callers and callbacks](#callers-and-callbacks), with the owner's
  decision of 2026-11-19.
- **Smaller points** (Fable N7, Astra's remaining interfaces):
  `MemberRun.Own`'s status, natives with step models in
  $`\mathrm{seg}(c)`$, the kind in `stepWrites_sound`, `SafeGraphRet`, the
  type view of declared shapes, `RowRealized`. Closed where each is named.

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
  node of its members and under the tokens of the closure arguments of
  every native step model its members call (`segCodes`, decided over the
  flow's slots and tokens, every context). At a call of a parameter
  holding what outside code may supply, the callee's set holds the token of
  every code whose token lies in $`O`$ (`Supplied`; `entry_slot_holds_O_tokens`),
  so $`\mathrm{seg}(c)`$ holds those codes: a closure of $`C`$ handed out
  may be the callee, and it runs at the caller's depth (`o-callee.mjs`).
- **A framed call**: a call node of the request's main graph whose
  callee's set holds outside storage, or such that some code of
  $`\mathrm{seg}(c)`$ has a node whose callee's set holds it
  (`reachesOut`, decided). A native without a step model is outside code
  (`Fits.invoke`); the calculus has no implicit call (an arithmetic of a
  non-primitive throws, `arithThrow`), so each run of outside code starts
  at an `invoke` or `construct` step.
- **The effects at a call.** $`\Phi`$ is the callee's effect read at the
  caller's slots; $`\Phi^{e}`$ is $`\Phi`$ where the callee's type states
  an exceptional bound (`onThrow`, `callExc`) and $`\top`$ otherwise;
  $`\Phi_\star`$ is $`\Phi`$ at a normal return and $`\Phi^{e}`$ at an
  exceptional one.

## Charges

One notion of charges, read at a base, serves the members' certificates
and a call's own steps.

**The charges of a set of codes** $`\mathrm{Ch}(M)`$: the protocol joining,
for each node of each code of $`M`$ at each of its contexts, each write of
the node's expression, at the parts of its receiver's sites at that node
and context and the kinds its form writes (`writesIn` over the flow's
nodes, the function the frame probe uses: an element write at the spine's
sites and the element kind, a write at a key at the receiver's sites
under that key, `roleKinds (slotBound k)`), at $`\mathsf{any}`$; and each
native step model's writes at its receivers' parts. The verifier computes
it from the lowered node expressions the flow holds, which [the binding
checks](#the-binding-checks) make the request's lowered codes; no write
list of the wire is read, and no write is discharged as fresh.

**The local lemma, at the base of any call** (`local_reach`, to be
proved). Let a call start at a state $`s_0`$ (an entry from outside code,
or a call node $`c`$ of a frame $`f`$) and let
$`L(s_0)=\mathrm{close}(\mathrm{sites}(\text{callee's captures},\text{receiver},\text{arguments}))`$,
the sites of what the call passes, closed under the heap of sites'
contents. Then a step of the call's run changes a location $`l<|h_0|`$ of
a local site $`\sigma`$ only where $`\sigma\in L(s_0)`$ or $`\sigma`$ is a
capture slot's site of a code the run executes. Plan: by induction along
the run, every value its frames hold is (i) a value the call passed or the
caller's captures, (ii) a value outside code supplied, meeting $`O`$, which
holds no local site (`Flow.Facts.noLocal`), (iii) read from storage of a
site that is not local, which references no local site (`LocalHeld`,
`FFlow.marks_of_marksFrom`), (iv) a capture of a closure of $`C`$, (v)
allocated in the run, at least $`|h_0|`$, or (vi) computed from such; by
`reach_sites` (proved) a location such a value reaches is of a site of the
closure of those sets. A bound function's parts and a closure of outside
code's captures reach no local site (`CodeNoLocal`, proved), so they add
no source.

Its two instances:

- **The protocol** $`\Psi_C`$, at a member's call entered from outside
  code: the receiver and arguments meet $`O`$, so the sources are capture
  slots. $`\Psi_C`$ is $`\mathrm{Ch}(\text{all codes of }C)`$ at every part
  but a local part whose site no capture slot of any code holds (closed
  under contents), which is $`\mathsf{keep}`$. The wire's proposal is
  checked to be at least $`\Psi_C`$ as so defined (`protocolDiags` over
  $`\mathrm{Ch}`$). Observed (`capture.mjs`, `NaN`): a closure capturing
  the walker's cursor, handed to the visitor and called, writes the cursor
  in a member's call; its site is a capture slot's, charged.
- **The depth charges** of a call node $`c`$: $`W_c`$ is
  $`\mathrm{Ch}(\mathrm{seg}(c))`$ at every part but a local part whose site
  is neither in $`L(c)`$ (the sites of what $`c`$ passes and of its
  callee's captures) nor a capture slot's site of a code of
  $`\mathrm{seg}(c)`$, which is $`\mathsf{keep}`$. A wrapper given the
  walker's cursor as an argument (`wrapper.mjs`, `onLine(c)`) is charged at
  the cursor; at P22's `visit(c.i)` the argument is a number, the receiver
  `undefined`, and no capture slot holds the cursor's site (measured by the
  frame probe, [read-only handles](readonly-handles.md#deciding-the-flow)),
  so $`W_c`$ keeps the cursor though `walk`'s `c.i++` is a write of a code
  of $`\mathrm{seg}(c)`$.
- **The call's protocol** $`\Psi_c=\Psi_j\sqcup W_c`$ with
  $`\Psi_j=\Psi_C\sqcup\Theta_C`$, the joined protocol.

**A step's changes are its charged writes** (`stepWrites_sound`, to be
proved): every location $`l<|h|`$ a step of $`C`$'s code from a reached
state changes is written by a write of the instantiated node expression of
the code and node the frame fits at (`Fits.innermost`, `fitsAt_reached`,
proved), and $`l`$'s part is among that write's charged parts. Plan:
`step_changes` (proved) locates the changed slot or cell among the stepped
term's references; by cases on the writing steps of `Step` (`writeAt`,
`setElem`, a native's step model), the redex is a subterm of the node
expression after substitution, so its write is one `writesIn` lists
(`writesIn_sound`, to be proved by induction on the expression, as
`syn_sound` is); the receiver meets its set (`Fits`), so $`l`$'s site is
one of its sites (`reach_sites`); the world's kind at $`l`$ is among
`roleKinds (slotBound k)` (`slotKind_sound`, to be proved from the world's
roles: a field location of a key is a field or cell role, a spine location
the spine role). The invocation changes no old location.

So **within a call** (`within_charges`, to be proved, from `local_reach`,
`stepWrites_sound` and `stepWithin_of_check`, proved): every step of
$`C`$'s code inside a member's call from $`a`$ is `StepWithin Ψ_C |h_a|`,
and every step of $`C`$'s code at the caller's depth in a segment from
$`s_0`$ is `StepWithin W_c |h₀|`, its frame running a code of
$`\mathrm{seg}(c)`$ (`segFrames`, to be proved: every frame at the
caller's depth above $`f`$ is pushed by a call step of such a frame or of
$`f`$'s call, whose callee meets the callee's set at its node, and a
closure of $`C`$ in a set holds its code's token there, `FnsIn`).

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

- **The segment as a run.** `MemberRun.Own` (proved, own steps at depth
  $`d`$ and inner runs at $`d+1`$) is generalized, to be proved, to
  `RunSeq R Inner d dᵢ q`: own steps at depth $`d`$, inner runs from
  states with at least $`d_i`$ calls active, each `Ok dᵢ`;
  `MemberRun.within` becomes `RunSeq.within` with its inner premise at
  `Ok dᵢ`. A member's call is $`d_i=d+1`$; a segment is $`d_i=d`$, its
  inner runs of outside code being at the caller's depth (at a top-level
  member's direct callback, depth $`1`$, Astra 5). `seg_run` (to be
  proved): the segment is a `RunSeq … d d`, its inner runs the maximal
  `QRun d` pieces (`call_segment`, `decompose`'s first conjunct at
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
- **The saved environment.** The framed calls are those of the claim's
  main graph, whose frame is the claim's term, `.frame E K t L d k x comp`;
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
obligations: a wrapper given the walker's cursor and writing it (the
cursor's site is in $`L(c)`$, charged; the fact fails) and a client
shortening the walker's array through the wrapper (outside storage off
$`R_C`$, bounded by the wrapper's effect at the walker's slots, $`\top`$;
the fact fails). A wrapper that increments the walker's cursor through a
closure of the walker's frame passed to it is charged the same way: the
closure is an argument, its captures' sites are in $`L(c)`$.

$`\Theta_C`$ binds the client the wrapper calls as it binds one an entry
calls: `ClientFrame.Keeps` constrains every step of outside code keeping
the number of calls of $`C`$ active, wherever the call came from, against
the protection of the history at that step.

The note's rule reads, with the generalized premise:

```math
\frac{c:\Phi\mid\Phi^{e}\qquad c\ \text{a call inside a call of}\ C\ \text{whose run may reach code outside}\ C\qquad W_c\ \text{bounds its steps of}\ C\text{'s code at the caller's depth}\qquad \text{(S)}\quad\text{(K)}}{c:\ \Phi\oplus_C(\Psi_C\sqcup\Theta_C\sqcup W_c)\ \mid\ \Phi^{e}\oplus_C(\Psi_C\sqcup\Theta_C\sqcup W_c)}
```

The note's section "The rule" and Appendix A take this statement when it is
built.

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
- **The part universe.** `callParts` gives a region with no sites
  (`.fields`, `.pathFields`, `.cls`, `.all`) the full part set
  $`U=(\mathrm{sites}(F)\cup\{\mathsf{none}\})\times\mathrm{kinds}\times\{\mathsf{none}\}`$,
  a finite list, with `regionSites` returning `some U` for it, so
  `frameCheckAt`'s `isSome` conjunct holds of every region. Its cover
  premise is `sites_in_flow` (to be proved): every location of a reached
  state has its site among the flow's sites or `none`, by induction along
  the execution (`stepAt_site`, proved: a step's fresh locations get
  `stepSite`, a site of the flow's allocation tables, or `none` at a step
  of outside code; the start's sites are those the threaded history gave).
  `framed_of_cover` (to be proved, the cover generalization of
  `framed_of_sites`) gives `Framed` from it. Observed (`NoSites.lean`): at
  the base `callParts` gives `[]` and `frameCheck` passes on `.all` at
  every protocol; with $`U`$ the check at `.all` requires
  $`\Psi_c(p)\sqsubseteq\delta`$ at every part and every entry of
  $`\Phi_\star`$ within $`\delta`$.

### Protection

A region is read protected (`prot`) where its every location at the call
was reached, read-only, at the entry from an entry argument at its
parameter's type: then `witness_reached` gives each such location a live
witness at the call. A region comes to include a location the entry did
not reach where a step on its path changes a reference: a component
write (Astra's first counter-model, `root.p` replaced within `scalar`) or
an outside write to a writable prefix (`prefix.mjs`: a callback replaces a
writable `root.box`, and the guarded read reaches the client's own
emptied array, `undefined`). So `prot` requires:

- **its root** is the entry's argument, equal in value: the region's root
  slot at node $`l`$ is a copy of the parameter's slot from the request's
  start along every graph path (`entryRootB`, decided over the edges'
  `mapIdx`; `copies_sound`, to be proved: a slot an edge maps from a source
  slot holds that slot's value, by `mapEnv`'s definition, which gives
  equality where `carriesB_sound` gives inclusion of sites);
- **the whole path is read-only from the root**: the parameter's declared
  type is read-only at every position the path passes, so every location
  on it is reached read-only by the entry's crossing, protected from the
  entry, and stays in $`R_C`$ (`InR.mono`);
- **each part the path passes before its last location is
  $`\mathsf{keep}`$ under $`\Psi_j`$** and under $`\mathrm{Ch}`$ of the
  unit's own codes.

Then `witness_of_path` (to be proved, induction on the path): each
location on the path is in $`R_C`$ at every state from the entry to the
call, so every step between changes it within $`\Psi_j`$ (a step of
outside code by (L1), one of $`C`$'s by `within_charges`), that is within
$`\mathsf{keep}`$; so the path at the call is the path at the entry, its
last location reached at the entry by a read-only path, and
`witness_reached` applies. In `prefix.mjs` `box` is writable, so the region
is read unprotected and the fact is lost. Every other region is read
unprotected, which loses precision only.

## Certificates

A member's certificate states, of each actual call of a code from a
reached state, the bound and the guarantees over the call's trace: its
entering step and every own step after it.

```lean
/-- The entering step of a call of `m` from `a`. -/
def Entering (Adm) (m : Option Code) (a a₁ : Conf × Ghost (F.at C)) : Prop :=
  Adm a ∧ XStep F C c Θ chk a a₁ ∧ entered c a₁.1.t = m ∧ δ F C c a₁ = δ F C c a + 1

/-- An own step of that call after its entering step: the call active from
`a₁` to `y`, the step from `y` one of `C`'s code at the call's depth (its
exit among them). -/
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

Every field reads the actual entering edge: no field ranges over a step
of no call (Astra 5: with `y = a` and no entering edge, `own` asked
`keep` of a body step `c.i++` of an existing cursor, which `keep`
rejects, `keep_rejects`). The entering step pushes the history, so an
invariant reading the history's depth fails `enterKeeps` (Astra's first
counter-model).

- **`Member` over the trace.** `Member.Call d Inner st st'` becomes a
  trace of the call with its inner segments: the steps of `RunSeq … (d+1)
  (d+1)` are the trace's own steps, each `Inner` segment the trace's
  maximal run of outside code one call deeper, so the fields are read on
  the steps the run consists of. `decompose` (proved) is restated with
  this `Member.Call`; its induction is the same, prepending the entering
  step.
- **The joined protocol.** Certificates are at $`\Psi_j=\Psi_C\sqcup\Theta_C`$,
  so `Run.bound`'s premise $`\Theta_C\sqsubseteq\Psi_j`$ holds.
- **From the charges** (`cert_of_charges`, to be proved): `enterWithin`
  (the entering step changes no old location) and `own` from
  `within_charges` ($`\Psi_C\sqsubseteq\Psi_j`$); the same certificate for
  every code $`m`$, since $`\mathrm{Ch}`$ charges every write of every code.
  `enterKeeps` and `tolerant`: vacuous at $`G=\emptyset`$; for the
  guarantee route, [the guarantee route](#the-guarantee-route).

## Re-entry

A callback re-entering $`C`$ creates calls of $`C`$ deeper than the
claim's main frame. The claim reads three things of such a call, none a
framed fact of it:

1. its effect on $`R_C`$: the certificate, from $`\mathrm{Ch}`$, which
   reads the lowered writes and the flow (an element write is charged
   $`\mathsf{any}`$ whatever its index);
2. its progress and typed heap inside the callback's run: the callback's
   semantic type, part of $`\Theta_C`$ ([callers and callbacks](#callers-and-callbacks));
3. its facts: read by no clause of the claim. The clauses read a stated
   assertion at a state whose whole term runs the claim's graph at its
   label (`AssertedAt`: `t' = gotoOf P l L' d' c'`) and the posts at the
   claim's exit; the graph's facts are delivered at the claim's main
   frame. A re-entered call's frames lie inside a callback's run inside
   that frame.

So the witnesses the claim needs are those of its main frame, from its own
entry ([protection](#protection)). This holds while the charges read no
fact, the guarantee's tolerance reads only facts no framed transfer
established (below), and the history records no crossing into $`C`$ after
the entry.

## The guarantee route

The bound route ($`G_C=\emptyset`$) reads no ownership. The guarantee
route keeps $`I\in G_C`$ across a framed call where `Supported` cannot
state it: an installed array of equal length keeps
`flags.length === widths.length` while the field `widths` changes
identity, beyond `grow`. So the graph's return premise at a framed call
includes, for each invariant $`(I,\mathit{root})`$ the frame keeps there,
$`I_{\mathit{root}}(\rho,h_0)\Rightarrow I_{\mathit{root}}(\rho,h_1)`$
([the graph at framed returns](#the-graph-at-framed-returns)), discharged
by `framed_guarantee` (to be proved): along the segment `InvIn I supp`
holds at every state, at an outside step by `SupportAt.outside` (proved),
at a step of $`C`$'s code by `invIn_of_installs` (proved), each with the
premises below.

- **The invariant language.** $`G_C`$'s candidates are path facts over a
  root: the type invariants whose support is a fixed finite set of field
  paths $`\Pi`$ from the root (`PathSupport`; `pathSupportB` decides it, and
  `Ctx.supportOf`'s whole-reach fallback, Astra's `factPaths (.element 0 1 2)
  = none`, is not a candidate). A path fact reads only locations on its
  paths, so an allocation, which changes no old location, keeps it
  (`pathFact_alloc`, to be proved; a heap-only predicate such as
  `h.length = 0` is no path fact).
- **A store's tolerance is its checked post** (`tolerant`). Charges at
  `any` cannot tell `widths = [9]` from `widths = []` with `flags = [0]`
  (`install.mjs`, `true false`). So each write of $`C`$'s code into a
  candidate's possible support is a **Check**: at the write's node, the
  graph's knowledge after the write implies $`I`$ at the written root, the
  store's guard and the value's facts (a `slice`'s fresh result, its
  length) included (`writeKeeps`, a check of the member's graph). Its
  soundness reads the member's facts at the write, at every call of the
  member, re-entered ones included; so the check uses only facts no framed
  transfer established on the path from the member's entry to the write
  (`framedFreeB`, decided over the graph: no framed call node lies on a
  path to the write whose kept supports the implication reads). Such facts
  hold at every call by the member's graph theorem along paths with no
  framed return (`RunSoundFramed` with $`\mathrm{Ret}`$ unused), so no
  witness of a re-entered call is read ([re-entry](#re-entry)).
  `tolerant_of_writeKeeps` (to be proved) gives `tolerant`, and
  `invIn_of_installs` takes $`I`$ after the step from it.
- **`SupportAt.keeps` and `.stays`**: at an outside step, every location on
  the paths is in $`R_C`$ and changes within $`\Theta_C`$ (L1); the support's
  parts tolerating $`\Theta_C`$ (`SupportParts`, decided) gives `keeps`,
  and paths whose every passed part is $`\mathsf{keep}`$ under $`\Theta_C`$
  read the same locations after the step, which gives `stays`
  (`pathSupport_stays`, to be proved).
- **`hsup`** (`protectedInto_of_supp`, to be proved): a store into
  $`w\in\mathrm{supp}_t\subseteq R_C(t)`$ is classified by (O): $`w`$ local
  (its part in `Ctx.supportOf`, so `cx.supported`; `protectedInto_local`,
  proved), exposed (`protectedInto_exposed`, proved), released and
  protected, or outside storage protected. A released location an entry
  crossing reached read-only is in $`R_C`$ (`released_prot_inR`), so (O)
  covers it: `protectedInto`'s released clause holds there, since a
  crossing into $`C`$ reached it (not `unreached`) and it came back into
  $`C`$ (`mayComeBack`) (`protectedInto_released`, to be proved from the
  flow at the entry's supplied slots); protected outside storage by the
  first disjunct, the receiver's tokens holding the component's token for
  a value entering from outside.
- **`hnew`** (`hnew_of_paths`, to be proved): by `supp_split` (to be
  proved, from `follows_split`, proved) a new location on a path is
  reached from the value of a store into a location of $`\mathrm{supp}_t`$,
  classified, whose (O) check passed, the disjunct `invIn_of_installs`
  takes.
- **At the entry.** `EntryHolds` holds no `@invariant` conjunct; the
  handle's invariant reaches the request as its precondition from
  `invariant-requires` (the entry's index facts, `r.entryIndices`) or, for
  an outside caller, from the row on handle parameters, which the lowering
  states as the same precondition. `invariant_of_entry` (to be proved):
  each invariant of $`G_C`$ at an entry parameter of its handle type is
  among the request's entry index facts, so it holds at a public call;
  its support lies in $`R_C`$ by the entry's crossing at the read-only
  handle type.

Observed (`redirect.mjs`, `NaN`): a re-entered member storing the
client's writable array in the handle's field; the store is into
$`\mathrm{supp}_t`$, classified, and (O) refuses it (`installIncoming`).

## The frame of a request

The claim's calls and its frame are fixed by the request, the module
realization and the calculus; the wire's proposals are checked against
them.

### The calls the claim is about

**An initial configuration** of a program over $`C`$: a configuration
$`x_0`$ (`Conf`: a world, a heap typed by it, a term valid at it) whose
heap is empty and whose term is
`letE (gotoOf initC 0 [] .undef c_C) client`, with `initC` the lowered
initialization of $`C`$'s modules (its code one of $`C`$'s, tagged
$`c_C`$), whose value holds the module closures it allocates, and
`client` closed lowered source of outside code (`LoweredSrc`) whose
variable `0` names that value. Lowered source holds no closure value
(`loweredSrc_no_closure`) and an empty heap holds no identity, so the
closures are made by the initialization's steps, a transition of the
calculus from source and an empty heap.

**A public call** of the request $`r`$ (`PublicCall r x`, new): $`x`$ is a
configuration of an execution `Ex fr.KStep (fun _ => True) n (x₀, bareStart) (x, g₀)`
from an initial configuration, every step an actual step (`AStep`: each
configuration's world admissible and its heap typed by it, the world the
obligation's `Keeps` reads, as in `ClientFrame.KStep`), keeping
$`\Theta_C`$ at the threaded history; $`x`$'s active frame is outside
$`C`$ and its next step invokes the module closure of $`r`$'s function.

**The claim's entry of a public call** (`realize_public`, to be proved):
from such an $`x`$ the execution reaches, in steps of the invocation and
of $`C`$'s code at depth one more, a configuration $`x'`$ whose innermost
run is `gotoOf r.program r.start L d r.comp`, where `L` and `d` are the
slots `graphEntry` builds (Astra's reduction: the receiver, the argument,
the closure itself, default `.nul`), then the prologue of a receiverless
module function (`PassUnit.dropReceiver`, the realization's
`PassUnitRealize`), and a rest function's spine allocated before its body.
The plan follows `graphEntry`'s equations (`Calculus.lean`) and the
realization's prologue lemma; the steps' worlds are the execution's.

**Isolation** (`isolate`, to be proved): from $`x'`$ to the call's return,
the execution is `K[t]` for the client's evaluation context `K` and the
isolated term `t`, every step a step of `t` in `K` (`Step`'s congruences);
so the isolated execution from `(h', gotoOf …)` has the same heaps,
worlds and steps, and the same steps of outside code, until the isolated
term is a value or a throw.

```lean
def FrameSpec.frame (spec : FrameSpec ι) (r : SourceRequest σ ι) : ClientFrame (Ty ι) where
  enters h t := ∃ x x' L d, PublicCall r x ∧ RealizedAt r x x' L d ∧ h = x'.s.h ∧
    t = gotoOf r.program r.start L d r.comp
  start k W h t g :=
    (∃ x x' L d g₀, PublicCall r x ∧ RealizedAt r x x' L d ∧ ThreadedAt x' g₀ ∧ h = x'.s.h ∧
      t = gotoOf r.program r.start L d r.comp ∧
      g = Ghost.crosses tv h (inputsAt r L d) { g₀ with A := [g₀.Prot] }) ∨
    ((¬ ∃ x x' L d, PublicCall r x ∧ RealizedAt r x x' L d ∧ h = x'.s.h ∧
        t = gotoOf r.program r.start L d r.comp) ∧ g = bareStart fr.F fr.C t)
  ...
```

`ThreadedAt x' g₀`: $`g_0`$ is the history threaded to $`x'`$, the entry's
own `enter` and the prologue's steps included. The start truncates that
history to its one set and lets the arguments cross in at the request's
input types (`inputsAt`: `r.inputs` at the entry's slots), so it holds one
set, the one call of $`C`$ the isolated `goto` holds
(`startFix_startInv_len`), and protects every location the program's
history protected (`truncate_prot`). The start is total: every other state
has `bareStart`.

- **The projection** (`project`, to be proved): along the isolated
  execution, the isolated history and the program's history protect the
  same locations, have the same sites, keys and exposed set, and differ in
  their depth by the number of calls of $`C`$ active below $`x'`$: each
  `HStep` acts alike on every set of a uniform history (`HStep.uniform`,
  proved), and the isolated execution ends before the call's own exit
  pops. So `Keeps` at each isolated step is `Keeps` at the program's step,
  and the isolated executions are the program's.
- **The obligation reads no proposal** (`keeps_canonical`, to be proved).
  $`\Theta_C`$ is a function of a part's kind alone (`@clients` states a
  change per kind: values, spines, fields), so its reading needs no site
  numbering; `RowProtects` reads the marks only through `Lent` and
  `exposed`, and at the marks a flow gives (`MarksFrom`) no site is exposed
  and a local location is reached by no outside root (`MarksOk`), so at an
  outside step, which changes only locations its roots reach
  (`step_reach`, proved), `Keeps` is "every changed location the history
  protects changes within $`\Theta_C`$ at its kind". The protected set is
  built from the entries' arguments at their input types and from
  `Held`, which reads whether a location's site is `some` (every
  allocation of $`C`$'s code gets one, `stepSite`) — neither depends on
  the proposal. So two proposals passing the checks give the same public
  calls.
- **The flow at a public call** (to be proved), replacing `EntryShape`:
  `fits_program`: from an initial configuration every state fits $`O`$ at
  a position of outside code and its heap meets the flow at the threaded
  history (the proof of `fitsAt_reached`, proved, from this start:
  `fits_step`, `HeapInv.set`, `HeapInv.fresh`, `stepAt_site`); at
  $`x_0`$ the initialization fits by its code's check and `client` by
  `fits_lowered` (proved: lowered code instantiated at an environment of
  $`O`$ fits $`O`$), once the initialization's value meets $`O`$, which
  `initB` decides (the value's closures' tokens in $`O`$, their captures at
  their codes' capture slots). A private closure held in $`C`$'s storage
  meets its site's contents; no clause asks it to be one $`C`$ gave out.
  `entryFits_public`: the isolated start fits, its slots those
  `graphEntry` and the prologue fill (`fits_graphEntry`, proved, and the
  prologue's node), so `EntryFits` holds, and with `Flow.Facts`,
  `FlowSites` and `ActualCrossings` (by `chk`) `ChkSound`
  (`chkSound_of_sites`, `sitesSound_of_fits`, proved). `startInv_public`:
  `Inv` along the execution (`Inv` at the empty heap; `XStep.inv`,
  `Ex.inv`, proved), kept by truncation and the crossings
  (`truncate_uniform`, `crosses_uniform`), with the length of
  `startFix_startInv_len`. `witness_public`: the arguments' crossing at the
  start protects what they reach read-only (`entryStart_prot`'s proof), and
  `witness_along` (proved) keeps it live along the call.
- **Which units are framed.** A public call invokes a module closure, so a
  framed plan is a module function's: an export or a function the module
  names. A method, or a function a binding holds, is checked by an
  ordinary plan.

### The binding checks

Decided by the verifier from the request, the fragment's components and
the lowered code, each with a forged-fragment control:

- **codes** (`codesCoverB`): the flow holds, at its entry context and at
  every context the check quantifies over, a proposal for each code of
  $`C`$ by content: the request's program and its codes, every module
  function of $`C`$'s modules and their closures' codes, and each module's
  initialization. The frame's `codes` are these, computed from the request
  and the module realization. A flow omitting the walker's code
  (`forged-flow.mjs`) fails it.
- **the component** (`compB`): $`C`$ is `componentAt` of the request's
  place, and the family's tags of $`C`$ are those the lowering assigns to
  $`C`$'s modules.
- **the entry** (`entryB`, `entryFnB`): at the request's own code and
  start, its slots naming signatures only at the sibling slots, each the
  module closure's signature; **the initialization** (`initB`).
- **the inputs**: `inputsAt r`, computed; the wire carries no entry types.
- **$`\Theta_C`$** (`clientsB`): the change per kind of the component's
  `@clients`, read from the source's declaration document, equal to the
  wire's; the verdict line prints it.
- **the protocol**: the wire's $`\Psi_C`$ at least $`\Psi_C`$ as defined in
  [charges](#charges), at every part of $`U`$, the uncaptured local parts
  at $`\mathsf{keep}`$.

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
$`\Theta_C`$, and for each framed call node of the main graph the supports
and invariants kept at its continuation and handler.

**The codes are checked by the ordinary pass.** A code's graph (a closure
the request creates) keeps no framed support: it is accepted as at the
base (`CodesAccepted`, `c.passChecker = .ordinary`), so its closure meets
its ordinary arrow (`CodesSound`) where the main graph creates, calls or
returns it. A code whose fact needs a frame is refused at its call node.
`returned-closure.mjs` (`NaN`): a returned closure whose call relies on a
frame; with its code ordinary, its fact across its visitor is dropped and
the read refused. **The sixth clause** of `FramedRequestSafe` is the
ordinary code clause of `RequestSafe` (each code's requirements at every
call meeting its entry contracts, frame-free), proved by
`codesAccepted_guarantees` (proved) as in `ordinary_requestSafe`; the
definition of `FramedRequestSafe` changes to read it, so the clause is
about every call of each code (`codeClause_vacuous` no longer applies).

`spec.frame request` takes `codes`, `C`, `enters`, `start` and the inputs
from the request. Its `view` is `ViewOver (Ty ι)` with `RO T` the type
reader's "read-only throughout" of `T`, `child T a := if RO T then
T.readonlyChild a else T.child a`, a read-only type's every child read-only
by construction, so `ro_child` holds by definition. A type is read by the
type reader that reads the API's declared shapes, so `RO` agrees with
`ComponentChecks.readOnlyShape` on the declared shape
(`ro_of_readOnlyShape`, to be proved by induction on the shape over the
type reader's `child`); a type it cannot decide is not read-only. `chk` is
the flow's `stepSite` for fresh locations, the key `none`, and `actualXs`,
so `FlowSites`, `NoKeys` and `ActualCrossings` hold by definition.

`PlanAt` stays the graph plans' (`RowRealized` reads it, and its proof
calls `requestSafe_of_member`, an ordinary claim); `FramedPlanAt` is new,
and `OverStore` reads both (`over_types` per constructor), so `hover`
types at a framed plan while a framed plan realizes no row.

### What the pass checks

`MemberAccepted.framed`, beside `ordinary`'s premises over the request
(its codes by the ordinary pass):

- `FFlow.check (remark F)`, `marksB`, `initB`, and the binding checks;
- (S), (K), (O) over every body of the component (`ComponentChecks`), (S)
  the restriction *No suspension*;
- $`\Psi_C`$ as defined; at each framed call node $`c`$ of the main graph,
  $`W_c`$ computed and the supports kept by the check at $`\Psi_c`$
  ([the check at a call](#the-check-at-a-call)), at $`\Phi`$ for the
  continuation's facts and $`\Phi^{e}`$ for the handler's;
- the main graph accepted by the framed run with those supports kept
  (`RunCall.AcceptsFramed`).

## Callers and callbacks

### The callback's type

The graph reads a callee value at its arrow's ordinary semantic type
(`call_local_sound`): its call is safe from every heap, its calls back
into $`C`$ included. By the owner's decision of 2026-11-19, a callback
into a framed component meeting its arrow type is part of the client
obligation: clients respect the API's types. The row of $`\Theta_C`$
([Trust](readonly-handles.md#trust)) reads, with it:

> Code outside $`C`$ keeps $`\Theta_C`$ at each of its steps on the storage
> the row protects, and a function value it passes to $`C`$ at a function
> type meets that type: called by $`C`$, its run, its calls of $`C`$
> included, is safe and within its stated effect.

**The continuation after a failed return premise** is outside the claim:
a callback emptying the walker's `[7]` and returning normally makes the
next read `undefined` (Astra). `RunSoundFramed` claims progress at the
states of the paths whose framed returns meet their premise, and
`framed_requestSafe` establishes the premise (`ret_reached`) before it
follows the continuation; after a step that broke $`\Theta_C`$ the claim
states nothing (`SafeUnder`).

### Verdicts that read a framed member's arrow

A framed member meets its ordinary arrow only along executions keeping
$`\Theta_C`$. A verdict reads that arrow in one of two ways, and the design
decides each by who supplies the arrow:

- **The component's own linking supplies it**: a unit whose graph reads a
  framed member through a sibling slot, its own slot (a recursive walker,
  whose `EntryHolds` holds that slot at the ordinary arrow), or a module
  binding holding it. The arrow is a premise the pass must discharge, and
  no ordinary theorem gives it: the unit is **refused** at that read,
  located there ("reads a function accepted under client trust",
  `passMember`). `dependent.mjs`'s `total` is refused. A framed plan
  realizes no row of a module's interface, `establishVerdict` refuses to
  establish a framed group (`MemberSettle.lean`), so an importer is
  refused at the import.
- **An input supplies it**: a unit taking a function at a parameter
  (`apply(f, h, visit)` in `apply.mjs`). Its ordinary verdict is
  conditional on its inputs meeting their types (`EntryHolds`, the row on
  exported preconditions); the unit cannot tell a framed member from any
  other function, and refusing it would refuse every higher-order unit,
  each safe for every input meeting its type. The program of `apply.mjs`
  passes `walk` with a visitor shortening the array of a handle `prepare`
  gave it at its read-only handle type, a client breaking $`\Theta_C`$, so
  `walk` does not
  meet its arrow there and `apply`'s premise is false. The verdict is
  **labelled** by that row, which the trust surface restates: a value of a
  framed component meets its declared type along the executions in which
  its holders keep that component's $`\Theta_C`$. The verdict line of such a
  unit is unchanged; the trust surface's caller row names $`\Theta_C`$.

The **verdict line** of a group with a framed member is
`accept under client trust Θ_C (component C)`. With the
obligation-relative arrow (milestone 3, $`[\![T]\!]^{\Theta}`$, its call
`SafeUnder fr.Keeps` from every reached state, `call_local_sound_under`
giving `SafeUnder` from it, and its linking theorem for the module's
rows), a unit of the first kind certifies to a framed plan with the same
frame, its label propagated along `depends`, and the interface carries
$`\Theta_C`$ with the arrow. Pretext's layout functions, which call the
walkers, need that milestone.

## Scope

- **Frames.** The transfer is applied at the framed calls of the
  request's main graph, whose frame is the claim's term; a code's graph is
  checked by the ordinary pass. A framed call in another function is that
  function's unit's.
- **Keys.** The check reads every location at the key `none`: one protocol
  entry bounds every field of a site's records. Facts that need two fields
  of one record told apart (pretext's `prepared.widths` beside the `stats`
  writes) are outside this design's precision; they are refused, located
  at the part that fails.
- **Charges discharge nothing as fresh**: a write to storage the writing
  frame allocated is charged at its site, so a fact about another location
  of that site is lost, but at an uncaptured local site outside $`L(c)`$.

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

and $`\mathrm{Ret}^{e}_l`$ alike at an exceptional return. `Target.RunSound`
is the instance with no framed node (`runSound_of_framed`, to be proved:
$`\mathrm{Ret}`$ is vacuous), and `run_sound_single_pass` is proved through
it. The paths are those of `SafeGraphRet`:

```lean
/-- `SafeGraph` with the pending framed node's entry: a state `.eval t ρ k x`
of a framed node `l` carries its entry heap `h₀`; a transition from it to
its successor at a return `v` or a throw is followed only where `Ret l ρ h₀
h'` (or `RetE`) holds; every other transition as in `SafeGraph`. -/
def SafeGraphRet (Ξ : Fam) (P : Program) (T : Fam) (F : Nat → Bool) (Ret RetE : Nat → Env → Heap → Heap → Prop) :
    (n : Nat) → WorldT n → Heap → State × Option (Nat × Heap) → Prop
```

The node delivery reads $`\mathrm{Ret}`$ in place of `callerFrame_post` for
the kept supports (`callKept_sound`, `callGrown_sound`, `frameKeeps`,
proved, read `Supported` through `Footprints.frame_step`), and the kept
invariants as known after the call; the rest of the call's delivery is as
at an ordinary call: `FirstKept` read from the callee's post
(`callEntry_holds`'s premise `hstable`), the continuation's facts at
`push v ρ` through the continuation's mapping, the handler's at the
thrown value through the handler's.

### The returns, at reached executions

`ret_reached` (to be proved): at every evaluation of a framed node of the
claim's main graph from a reached call state $`s_0`$ to its resumption
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

Plan. The sixth clause by `codesAccepted_guarantees` (above). Each of the
other five by induction on the budget, the invariant at a state being: it
is reached from the clause's start (`Reached`, with the execution), its
term simulates a state of `SafeGraphRet` over the claim's graph
(`GraphCode.Sim` with the pending framed call's entry), and that state is
on a $`\mathrm{Ret}`$-path of `RunSoundFramed`. Progress and the typed heap
at each state come from `SafeGraphRet` through the simulation. A step
breaking $`\Theta_C`$ ends the obligation; any other is a `KStep`, mapped to
a transition by `sim_step_back` (proved); at a framed node's return
`ret_reached` gives $`\mathrm{Ret}`$ and the path stays a
$`\mathrm{Ret}`$-path. The assertions: a term state `gotoOf P l L' d' c'`
reached from the start is simulated by `.at l (envOf L' d')` reached on a
$`\mathrm{Ret}`$-path, at which `RunSoundFramed`'s `asserted` gives `Holds`
(`assertedAt_of_graph`, to be proved, the converse direction of
`asserted_of_reach`, proved). The executions are built from the start
without assuming the clause.

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
  regional and assertion clauses hold; and each code's requirements hold at
  every call of it. The calls are the program's, so no proposal narrows
  the conclusion.

The commit that builds it records `Theorem modified (mode8Accepted_sound)`
with this conclusion, and `MemberSafe`'s and `FramedRequestSafe`'s
readings.

## Proved, to be proved, trust

**Proved at the base**, reused: `FFlow.check_sound`, `fitsAt_reached`
(its proof), `fits_step`, `fits_roots`, `fits_graphEntry`, `fits_lowered`,
`chkSound_of_sites`, `sitesSound_of_fits`, `framed_at_innermost_keys`,
`frameCheck_sound`, `framed_of_sites`, `regionSites_sound`, `reach_sites`,
`reached_key`, `witness_along`, `entryStart_prot`, `crosses_uniform`,
`HStep.uniform`, `call_segment`, `decompose`, `Run.bound`, `Run.keeps`,
`MemberRun.within`, `RBoundBelow.trans`, `InR.mono`, `pkg_step_ok`,
`stepWithin_of_check`, `keeps_of_charges`, `readOnly_rule`,
`supported_of_framed`, `invIn_of_installs`, `installs_checked`,
`protectedInto_local`, `protectedInto_exposed`, `SupportAt.outside`,
`follows_split`, `step_changes`, `step_reach`, `stepAt_site`,
`Fits.innermost`, `XStep.inv`, `Ex.inv`, `kstep_xstep`, `reached_ok`,
`sim_step_back`, `asserted_of_reach`, `framed_callSafe`,
`call_local_sound`, `callKept_sound`, `callGrown_sound`,
`callEntry_holds`, `carriesB_sound`, `codesAccepted_guarantees`,
`run_sound_single_pass`.

**Observed at the base** (to be moved into the build): `truncate_prot`,
`truncate_uniform` (`Truncate.lean`); `startFix_startInv_len`,
`keep_rejects`, `released_prot_inR`, `loweredSrc_no_closure`,
`gotoOf_start_ne` (`Round3.lean`).

**To be proved**, milestone 1: `local_reach`, `stepWrites_sound`,
`writesIn_sound`, `slotKind_sound`, `within_charges`, `segFrames`,
`framed_transfer`, `seg_run`, `RunSeq.within`, `RBound.mono`,
`frameC_shape`, `sites_in_flow`, `framed_of_cover`, the trace-indexed
`Cert` and `Member.Call` with `decompose` restated, `cert_of_charges`,
`realize_public`, `isolate`, `project`, `keeps_canonical`, `fits_program`,
`entryFits_public`, `startInv_public`, `RunSoundFramed` with
`SafeGraphRet`, `runSound_of_framed`, `ret_reached`, `assertedAt_of_graph`,
`framed_requestSafe`, `ro_of_readOnlyShape`, `FramedPlanAt` and
`OverStore`, `member_safe`'s and `passMember_sound`'s framed branches.
Milestone 2: `witness_public`, `copies_sound`, `witness_of_path`,
`framed_guarantee`, `pathFact_alloc`, `tolerant_of_writeKeeps`,
`pathSupport_stays`, `protectedInto_of_supp`, `protectedInto_released`,
`supp_split`, `hnew_of_paths`, `invariant_of_entry`.

**Trust**, rows of the [trust surface](../DESIGN.md#trust-surface):

- the client obligation $`\Theta_C`$, stated in the component's API
  (owner-approved), with its two parts (owner's decision of 2026-11-19):
  code outside $`C`$ keeps $`\Theta_C`$ at each of its steps
  (`ClientFrame.Keeps`, `Row`), and a function value it passes to $`C`$ at a
  function type meets that type, its calls of $`C`$ included; clients
  respect the API's types, so a program's executions are typed at their
  worlds (`AStep`, the configurations of `PublicCall`);
- the caller row, restated: a value of a framed component meets its
  declared type along the executions in which its holders keep that
  component's $`\Theta_C`$;
- *Clients* (Read-only frames, Assumption "Clients"): outside code enters
  $`C`$ only through its interface (`Provenance`), and a program's outside
  code is lowered source of the calculus (`Source`, `LoweredSrc`), closed
  (`ClosedAt`), in a well-formed configuration (`Discipline`), as the
  initial configurations of `PublicCall` are;
- the request's entry contracts at a public call (the existing rows on
  exported preconditions and handle parameters);
- a native's step model performs its model's steps (the `%ElementAt%`
  row), where the flow reads one.

## Milestones

Each is stated generally and buildable on the one before.

1. **The bound route for P22** ($`G_C=\emptyset`$, `prot` false at every
   region). **Its first check**, before the theorems: one actual linked
   call of P22's `walk`, from an initial configuration of a client program
   through the invocation of `walk`'s module closure to the request's
   entry with `graphEntry`'s slots, the world and the threaded history
   (the instance of `realize_public` and `startFix_startInv_len` at P22),
   and, on the flow probe, the cursor fact `c.i < xs.length` kept at
   `visit(c.i)` under the final $`\Psi_c=\Psi_j\sqcup W_c`$, with $`W_c`$
   and $`\Psi_C`$ computed as in [charges](#charges) (the probe's protocol,
   `probeProtocol`, replaced by them). Then the charges and their lemmas,
   the trace-indexed certificates, `framed_transfer`, the check at a call
   over $`U`$, the frame of a request with `PublicCall`, the binding checks,
   `RunSoundFramed` with supports only, `framed_requestSafe`, the plan with
   its codes by the ordinary pass, the headline, and the refusal of units
   whose linking reads a framed member.
2. **Protection and the guarantee route**: `witness_public`,
   `witness_of_path`; `framed_guarantee` with path facts and checked
   stores.
3. **The obligation-relative arrow**: $`[\![T]\!]^{\Theta}`$, framed callers
   and importers, the label along `depends`.
4. **Keys**: parts at field keys, for facts such as pretext's
   `prepared.widths`.

## Tests

- **P22**, `bounds-pattern-unreachable-field-refused` (a gap, positive at
  milestone 1, renamed with its outcome). `visit(c.i)` is a framed call;
  $`\mathrm{seg}(c)`$ holds `walk`'s code (its token lies in $`O`$), and
  $`W_c`$ is $`\mathsf{keep}`$ at the cursor's part, its site neither in
  $`L(c)`$ nor a capture slot's; $`\Psi_C`$ is $`\mathsf{keep}`$ there by
  the same lemma. `xs`'s spine is outside storage, off $`R_C`$, bounded by
  the visitor's $`\mathsf{grow}`$. That `c.i < xs.length` and `0 <= c.i`
  pass under the final $`\Psi_c`$ is milestone 1's first check; the probe
  measured them at its own protocol.
- **Kept negative**: `invalid-bounds-pattern-cursor-given`.
- **New cases**: `throw.mjs`'s walker (negative at the handler read) and
  its variant reading only `0 <= c.i` there (positive); a wrapper calling
  the client, the walker keeping its local cursor (positive); a wrapper
  given the cursor and writing it, and one given a closure of the walker
  that increments it (negative); a client shortening the array through a
  wrapper (negative); `capture.mjs`'s walker (negative);
  `returned-closure.mjs`'s `make` (refused at its closure's read);
  `dependent.mjs`'s `total` and a recursive walker (refused at the read of
  the framed member); `prefix.mjs`'s walker (refused: its region is read
  unprotected).
- **Controls** (forged fragments against the verifier): a flow omitting
  the walker's code (`codesCoverB`); a flow whose entry context names a
  signature at a non-sibling slot (`entryFnB`); a wire $`\Theta_C`$ other
  than the source's (`clientsB`); a $`\Psi_C`$ below its definition; a
  framed call whose check passes at one node of the call's continuation
  and handler and fails at another (the fact dropped); a region `.all` at a
  protocol changing a part (the fact dropped).
- **Pretext's walkers**: their cursor bounds at local sites, measured by
  the probe at the direct-call obligation (the raw walker's two
  segment-index bounds and grapheme-index lower bound at 8/8 contexts, the
  complex walker's segment-index bounds at 3/4), across the wrapper
  `onLine`; the `prepared.widths` facts need milestone 4, and the layout
  functions calling the walkers milestone 3.

## Open points for review

1. **The initialization of a package**: `initC` is one code of $`C`$'s
   module initialization; a package of several modules needs their
   initialization order in it, which the module realization
   (`PassUnitRealize`) states for one module.
2. **`stepWrites_sound`** rests on the node expression's writes being the
   only writing redexes of a frame's steps, natives' step models included.
3. **`local_reach`'s sources**: a bound function's parts and a closure of
   outside code's captures are excluded by `CodeNoLocal`, a reading of the
   value judgment for the proof to confirm.
4. **`keeps_canonical`** needs $`\Theta_C`$ a function of the kind alone;
   an `@clients` stating changes per site would need its site naming from
   the declaration.
5. **`framedFreeB`** (milestone 2) bounds what the guarantee's checked
   stores may read; whether pretext's stores need facts a framed transfer
   gave is not measured.
6. **`RunSoundFramed`'s size**: threading $`\mathrm{Ret}`$ through the
   graph theorem touches the call node's delivery and the path predicate,
   a reading of `run_sound_pass`'s structure, not yet a build.

## Runs

Node 26.13.0, each printing the value shown; the files are in the
reviews' scratch directories (`framed-review/`, `round2/fable/`,
`round3/`), outside the repository:

- `throw.mjs`: `{ s: NaN, i: 2 }`, a visitor shortens `xs` and throws, the
  handler reads `xs[c.i]`;
- `wrapper.mjs`: `NaN`, `NaN`, a client shortens `xs` through a wrapper; a
  wrapper writes the walker's cursor;
- `redirect.mjs`: `NaN`, a re-entered member installs the client's array
  in a handle's field, the client shortens it;
- `capture.mjs`: `NaN`, a closure of $`C`$ capturing the walker's cursor,
  given to the visitor and called, writes the cursor;
- `prefix.mjs`: `undefined`, a callback redirects a writable prefix and a
  second empties the client's array the path now reaches;
- `install.mjs`: `true false`, two replacements of `widths` at the same
  charge, one keeping the invariant;
- `forged-flow.mjs`, `dependent.mjs`, `apply.mjs`, `returned-closure.mjs`,
  `o-callee.mjs`: as the second review reports them (`NaN`; `NaN`; `NaN`;
  `NaN` at a later heap; `walk` running at the walker's depth).

Lean files checked with `lake env lean` at the base, standard axioms only:
`Vacuous.lean`, `EmptyFlow.lean`, `NoSites.lean` (first review),
`CodeClause.lean`, `StartLen.lean` (second review), `Truncate.lean` and
`Round3.lean`:

```lean
theorem startFix_startInv_len {F : Family} {C : Nat} {tv : TypeView} (h : Heap) (xs : List (Crossing tv))
    (g₀ : Ghost (F.at C)) {E K l L d comp} (hc : F.ofC C comp = true) :
    (Ghost.crosses tv h xs { g₀ with A := [g₀.Prot] }).A.length = depthC F C none (.goto E K l L d comp)
theorem keep_rejects (b : Nat) (x y : Tm) (hne : y ≠ x) : ¬ Footprints.Change.keep.Holds b x y
theorem released_prot_inR {P : Package} (g : Ghost P) (l : Nat) (hr : g.origin l = some .released)
    (hp : g.Prot l) : g.InR l
theorem loweredSrc_no_closure (ofC : ComponentTag → Bool) (fs : List (PropKey × Nat)) (c : CallCode) (i : Nat) :
    ¬ LoweredSrc ofC (.objAt fs c i)
theorem gotoOf_start_ne (P Q : ControlFlow.Program) {s s' : Nat} (hs : s ≠ s') (L L' : List Tm) (d d' : Tm)
    (c c' : ComponentTag) : gotoOf P s L d c ≠ gotoOf Q s' L' d' c'
theorem truncate_prot {P : Package} (g : Ghost P) (l : Nat) :
    ({ g with A := [g.Prot] } : Ghost P).Prot l ↔ g.Prot l
theorem truncate_uniform {P : Package} (g : Ghost P) : ({ g with A := [g.Prot] } : Ghost P).Uniform
```
