# Draft: accepting a unit through the read-only frame

A design for the step from the read-only frame rule, proved at the paper's
executions, to a unit's accepted verdict. It adds one constructor of
`FunctionPlan`, a framed plan, with its branch in `FunctionPlan.certify`, and
the theorem that the pass's check of a framed plan gives
`PassUnit.FramedRequestSafe`, so that `SourceClaimJson.PassUnit.mode8Accepted_sound`
covers a unit accepted that way under the client obligation $`\Theta_C`$ of
[Trust](readonly-handles.md#trust). The design is stated for every function
a component exports, every call inside the component that may run code
outside it, and every fact the graph carries across a call.
[P22's walker](../../pipeline/examples/bounds-pattern-unreachable-field-refused.ts)
and pretext's walkers are its tests ([Tests](#tests)).

Base: branch `p22-accept` at `4c1d35f60`. Notation is that of
[Read-only frames](readonly-frames-note/note.tex) and of
[read-only handles](readonly-handles.md#the-rule): a component $`C`$, its
region $`R_C`$, its protocol $`\Psi_C`$, the client obligation $`\Theta_C`$,
the action $`h\xrightarrow{\Phi}_\rho h'`$ of an effect and
$`\Phi\oplus_C\Psi`$. Each claim is labelled **proved** (with its Lean
name, at this base), **to be proved** (with its proof plan and the proved
results it reuses), **trust** (an assumption about code outside the analyzed
sources), or **observed** (a program run under Node 26.13.0, sources in
[Counter-models](#counter-models)).

## The existing mechanism this extends

Three mechanisms, each kept, each changed at one place.

1. **The graph's transfer at a call** ([footprints](../FOOTPRINTS.md#a-calls-effect-at-the-caller),
   rule Frame of [Tolerant frames](tolerant-frames-note/note.tex)). At a
   call node the pass keeps a fact of the caller where the fact's support
   respects the callee's effect read at the caller's slots, $`\Phi`$
   (`PromiseCalls.callerFrame`): the terms it keeps (`callKept`,
   `callKept_sound`), the terms it grows (`callGrown`, `callGrown_sound`)
   and the index facts it keeps (`frameKeeps`), each sound from the heap
   relation $`h\xrightarrow{\Phi}_\rho h'`$ that the callee's semantic type
   gives at its return (`callerFrame_post`), and at a handler from the
   exceptional effect where the callee states one (`callExc`). This design
   changes one predicate: at a *framed call* the support may instead pass
   the read-only frame's check, whose soundness is the support's
   preservation between the call's heap and the return's heap, read from
   the execution ([the transfer at a call](#the-transfer-at-a-call)).
2. **The read-only frame rule** ([the rule](readonly-frames-note/note.tex),
   [read-only handles](readonly-handles.md#what-the-lean-states)): the
   rule's consequence over the paper's executions (proved: `exec_rely`,
   `ClientFrame.call_rely`), its premise checked at a frame of $`C`$'s code
   (proved: `ClientFrame.framed_at_call`, `frameCheck_sound`), the flow of
   sites and its check (proved: `FFlow.check_sound`,
   `ClientFrame.chkSound_of_flow`). This design generalizes the rule's
   premise from a call of outside code to a call of any code that may run
   outside code, a function of $`C`$ among them
   ([wrappers](#a-call-of-the-components-own-code)), restates the members'
   certificates over the calls an execution makes
   ([certificates](#certificates-over-the-calls-an-execution-makes)), and
   states the transfer from the call's own state.
3. **The acceptance path** (CLAUDE.md, "Acceptance/soundness invariant").
   `CertifiedPlan.framed`, `PassUnit.FramedRequestSafe` and `MemberSafe`'s
   branch reading it exist (proved: `framed_callSafe`,
   `callSafe_of_member`); no `FunctionPlan` certifies to a framed plan. This
   design adds `FunctionPlan.framed`, its branch of `certify`, a
   constructor `MemberAccepted.framed` for what the pass checks of it, and
   the theorem `framed_requestSafe` from that check to
   `FramedRequestSafe` ([the theorems](#the-theorems)).

No new judgment form and no new modality. The graph theorem is restated
once, relative to the returns of the framed calls
([the graph at assumed returns](#the-graph-at-assumed-returns)).

## The five gaps

Five gaps lie between the proved results and an accepted verdict, as an
independent review of an acceptance design (Astra, kept outside the
repository) named them. Each is restated at the level of the note,
verified against the Lean at the base, and closed in the section named.

1. **The transfer across the call.** `ClientFrame.framed_at_call` gives
   `Framed` at a reached state whose innermost frame is a frame of $`C`$'s
   code about to call outside code (`ReadOnlyCallFrame.lean`, the
   statement's `ht` and `hcall`). `ClientFrame.call_rely` reads `Framed` at
   the first state of its segment, and that segment's states at depth
   $`d`$ run outside code (its premise `hex` at the predicate
   $`\neg(\delta=d\wedge\neg\mathrm{Outside})`$). The two states differ by
   the step that invokes the callee, so no proved theorem connects them.
   Verified by reading both statements: **a gap**. Closed by the transfer
   stated from the call's own state ([the transfer](#the-transfer-at-a-call)).
2. **A throw from the callback.** `call_rely` takes the action of one
   effect $`\Phi`$ over the whole segment, whichever exit ends it. A
   callee whose stated effect bounds its normal return alone can shorten an
   array and throw. Observed (`throw.mjs`): the walker's handler reads
   `xs[1]` of an emptied array, `{ s: NaN, i: 2 }`. **A gap.** Closed by
   reading the exceptional exit at $`\Phi^{e}`$
   ([an exceptional return](#an-exceptional-return)).
3. **Re-entry with fresh storage.** `witness_reached` witnesses the
   locations the unit's entry arguments reach read-only; a callback's fresh
   array passed read-only to a re-entered member has no witness, since the
   history records no crossing into $`C`$ after the entry (`actualXs`,
   `ReadOnlyCrossings.lean`). **Not a gap of this design**: no fact of a
   re-entered call is read by the unit's claim, and the members'
   certificates read no fact ([re-entry](#re-entry)).
4. **`Cert.tolerant` over every `PkgStep`.** The field quantifies over
   every `R.Rel d t t'` at `R = StepRel.checked`, and `PkgStep`'s fields
   (`ReadOnlyChecks.lean`, `PkgStep`) constrain allocation, the history,
   crossings and stores into local storage, never which old location a step
   changes; so a nonempty guarantee family asks a property of steps no code
   makes. Likewise `Cert.ofBody` asks its bound of every `MemberRunOf`
   between a call's two endpoints, whose intermediate steps the endpoints do
   not determine. Verified by reading the definitions: **a gap**. Closed by
   certificates indexed by the call's trace
   ([certificates](#certificates-over-the-calls-an-execution-makes)).
5. **(O) needs `hsup` and `hnew`.** `invIn_of_installs` holds given
   `hnew` (each location the support reads after a step was read before,
   is in $`R_C`$, or is reached through a stored value (O) checked), and
   `installs_checked` given `hsup` (each store the support may read is one
   (O) classifies). Neither is proved. **A gap of the guarantee route**;
   the bound route reads neither. Closed by
   [the guarantee route](#the-guarantee-route).

The review's other findings are read as follows: the check at the call's
label ([the check at a call](#the-check-at-a-call)); `NoKeys` sound for
`Framed`, the protocol at `none` joining every key
([the check](#the-check-at-a-call)); the proof direction of
`framed_reaches` ([the framed claim](#the-framed-claim-from-the-check));
the marks and bindings at the acceptance family (the marks the flow gives,
`FFlow.MarksFrom`, below).

## Definitions

Let a state be a configuration of the paper's executions with its history,
$`s=(x,g)`$ (`Conf × Ghost`), and $`\delta(s)`$ the number of calls of
$`C`$ active at it (`depthC`).

- **A call state.** $`s_0`$ is a call state of a frame $`f`$ when $`f`$,
  a frame of $`C`$'s code with environment $`\rho_f`$, is the innermost
  frame of $`s_0`$'s term and its term is a call whose callee, receiver
  and arguments are values (`invoke` or `construct`). The pass's call
  nodes have this form: a node expression that is a call is checked as one
  sequent whose parts are values (`call_local_sound`, `LocalUsing … (.app e)`).
- **The call's segment** from $`s_0`$: the steps until the first later
  state $`s_1`$ at which $`f`$ is the innermost frame again, its term a
  value (a normal return) or a throw (an exceptional return), $`s_1`$ the
  *resumption*. Every state between has the call's run inside $`f`$'s
  term, so $`\delta\ge\delta(s_0)`$ along it.
- **The steps at the caller's depth.** A step of the segment from a state
  $`s`$ with $`\delta(s)=\delta(s_0)`$ is a step of $`C`$'s code (the
  invocation, and the body of a callee that is $`C`$'s own code) or a step
  of outside code (`stepKind`). Every step at a greater depth is inside a
  call of $`C`$ entered from outside code, a member's call.
- **A framed call.** A call node of a code of $`C`$ at which the flow
  (`Flow.code`, [the sites of a term](readonly-handles.md#the-sites-of-a-term))
  lets the callee's run reach outside code: its callee's set holds outside
  storage (`CodeFlow.out`, `FnsIn.notOut`), or holds the token of a code
  of $`C`$ that reaches such a node by the flow's known calls and calls of
  closures of $`C`$'s code, transitively (`reachesOut`, to be defined over
  `FFlow` as `callsOut` is). A native with no step model is outside code
  (`Fits.invoke`); the calculus has no implicit call (an arithmetic of a
  non-primitive throws, `arithThrow`), so every run of outside code starts
  at an `invoke` or `construct` step.
- **The depth charges of a call** $`W_c`$: the protocol, part by part,
  joining the charge of each write of each code of $`C`$ the callee's run
  may execute at the caller's depth (the codes whose tokens the callee's
  set holds, closed under their known calls and calls of closures of
  $`C`$'s code), at the parts of its receiver's sites, discharging only a
  write every location of whose receiver the write's own frame allocated.
  The protocol's own discharge of a write through a confined closure of an
  enclosing frame (*Fresh storage* of
  [read-only handles](readonly-handles.md#what-the-lean-states)) is not
  applied: that frame may be $`f`$ or below it, its storage older than
  $`s_0`$. For a callee that is outside code alone, $`W_c`$ is
  $`\mathsf{keep}`$ at every part: the invocation writes nothing.
- **The call's protocol** $`\Psi_c=\Psi_C\sqcup\Theta_C\sqcup W_c`$.
- **The effects at a call.** $`\Phi`$ is the callee's effect read at the
  caller's slots (`callerFrame eff t`); $`\Phi^{e}`$ is $`\Phi`$ where the
  callee's type states an exceptional bound (`onThrow`, `callExc`) and
  $`\top`$ otherwise.

## The transfer at a call

**Framed transfer.** For a fact with support $`S`$:

```math
\frac{s_0\ \text{reached, a call state of}\ f\qquad s_0\to^{*}s_1\ \text{its segment, every step keeping}\ \Theta_C\qquad h_0\xrightarrow{\Phi_\star}_{\rho_f}h_1\qquad \mathrm{Framed}(\Phi_\star,\Psi_c,S,\rho_f,s_0)}{\mathrm{Supported}(S,\rho_f,h_0,h_1)}\ \textsf{(Framed transfer)}
```

with $`h_0,h_1`$ the heaps of $`s_0,s_1`$, $`\Phi_\star=\Phi`$ at a
normal return and $`\Phi^{e}`$ at an exceptional one, and `Supported` the
support relation of [footprints](../FOOTPRINTS.md#support-and-respect):
each location $`l<|h_0|`$ of each $`(r:\delta)\in S`$, read at
$`(\rho_f,h_0)`$, changes within $`\delta`$. So every fact the support
supports holds at $`(\rho_f,h_1)`$ where it held at $`(\rho_f,h_0)`$.

The argument, at the note's level:

1. The segment's steps at the caller's depth that run $`C`$'s code change
   each location $`l<|h_0|`$ of $`R_C`$ within $`W_c\sqcup\Psi_C`$ at its
   part: each is a write of a code $`W_c`$ joins (a step's changes are its
   writes, below), charged at its receiver's parts or to storage its own
   frame allocated, which is at least $`|h_0|`$ since that frame is pushed
   after $`s_0`$.
2. Each maximal run of outside code at the caller's depth, from a state
   whose active frame is outside $`C`$ to the next state of $`C`$'s code at
   that depth, changes $`R_C`$ within $`\Psi_C\sqcup\Theta_C`$ and keeps the
   invariants of states: (L2) at the paper's executions.
3. $`R_C`$ only grows inside the call (L3), so the bounds compose: the
   segment changes each $`l\in R_C(s_0)`$, $`l<|h_0|`$, within $`\Psi_c`$.
4. With $`h_0\xrightarrow{\Phi_\star}h_1`$ bounding every other location,
   the segment is an action of $`\Phi_\star\oplus_C\Psi_c`$ from $`s_0`$,
   and `Framed` gives `Supported` location by location.

Lean (to be proved, `ReadOnlyTransfer.lean`, namespace
`TolerantFrames.ReadOnly.ClientFrame`):

```lean
theorem framed_transfer (hc : fr.ChkSound) (hi : fr.StartInv) (certs : fr.Certs Ψ G)
    (hΘ : ∀ p, (fr.Θ p).le (Ψc p) = true) (hΨ : ∀ p, (Ψ p).le (Ψc p) = true)
    {a e : Conf × Ghost (fr.F.at fr.C)} {E K t L d k x comp} {n : Nat}
    (ha : fr.Reached a) (hcall : CallState a.1.t (.frame E K t L d k x comp))
    (hex : Ex fr.KStep (Inside a.1.t) n a e) (hres : Resumes a.1.t e.1.t)
    (hown : ∀ y z, OnSegment a y → fr.KStep y z → δ fr.F fr.C none y = δ fr.F fr.C none a →
      ¬ Outside fr.F fr.C none y.1 →
      StepWithin Ψc a.1.s.h.length (lift fr.F fr.C none y.1 y.2) (lift fr.F fr.C none z.1 z.2))
    (hΦ : TolerantFrames.Action Φ (envOf L d) a.1.s e.1.s)
    (hfr : Framed Φ Ψc S (envOf L d) (lift fr.F fr.C none a.1 a.2)) :
    Footprints.Supported S (envOf L d) a.1.s.h e.1.s.h
```

`CallState`, `Inside` (a state whose path extends the call state's by the
callee's run) and `Resumes` (the call state's frame innermost again, its
term a value or a throw) are new definitions over `path`
(`ReadOnlySteps.lean`). Proof plan:

- **The segment as a run** (`SegRun`, new): an inductive of steps of
  $`C`$'s code at depth $`d`$ meeting a property, and runs of outside code
  at depth $`d`$ (`Run Θ Ψ G k d`), as `MemberRun.Own` is at depth
  $`d+1`$. `seg_run`: the segment is one, its runs the maximal `QRun d`
  pieces, by `call_segment` and `decompose`'s first conjunct at `off = 0`
  (proved), each piece starting at a reached state (`Reached.xstep`,
  proved) that is `Ok d` (`reached_ok`, proved).
- **Its bound** (`SegRun.within`, new): `RBoundBelow Ψc d |h₀|`, by
  induction as `MemberRun.within` (proved): an own step by `hown` and
  `pkg_step_ok` (proved), a run by `Run.bound` (proved) and
  `RBound.mono` (new, from `Change.Holds.mono`), composed by
  `RBoundBelow.trans` (proved), the region growing by `InR.mono` (proved).
  Below `|h₀|` is all of `Framed`'s domain, which reads locations of the
  call state's heap only.
- **The action** (as `readOnly_rule`, proved): `RBoundBelow.all` and `hΦ`
  give `OAction Φ Ψc` from the lifted call state; `supported_of_framed`
  (proved) gives `Supported`.
- **The saved environment.** At the unit's top frame (the only frames
  whose facts the claim reads, [re-entry](#re-entry)) the frame is the
  term itself, `.frame E K t L d k x comp`, and every step of the segment
  is `frameC` of its running term, until the term is a value or a throw:
  `L` and `d` are the frame's own fields, unchanged (`frameC_shape`, new,
  by cases on `Step` at a frame). The `frameBind` or `frameHandle` step
  after $`s_1`$ is the graph's transition to the continuation or the
  handler at `push v (envOf L d)`.
- **Allocation and crossings at the invocation.** The invocation is a
  step of $`C`$'s code at depth $`d`$ (`stepKind … = .body`): a checked
  step (`ChkSound`), so `pkg_step_ok` (proved) gives the marks kept, the
  history growing at depth $`d`$ (its crossings out add to $`E`$ only) and
  `Ok d` after it; its fresh locations are at least $`|h_0|`$, outside
  `Framed`'s domain. `hown` holds of it: it writes nothing (below).

`hown` is discharged from the pass's check of $`W_c`$ by the step
interpretation:

- **A step's changes are its writes** (`stepWrites_sound`, to be proved):
  every location below the heap's length that a step of $`C`$'s code from a
  reached state changes is written by the step's redex, at a location
  whose site and kind are among the parts of the write's receiver's set at
  the redex's node and context. Plan: `step_changes` (proved: an old
  location a step changes is a slot of an object or an element cell of a
  spine the stepped term references), by cases on the writing steps of
  `Step` (`writeAt`, `setElem`, a native's step model), with the redex's
  fit (`Fits.innermost`, `fitsAt_reached`, proved) giving the receiver's
  sites and `regionSites_sound`'s argument (proved) the location's site.
  The invocation steps (`invoke`, `construct` of a closure) change no old
  location.
- **Own-frame freshness** (`ownFresh_sound`, to be proved): a write whose
  receiver the check classifies as allocated by its own frame writes a
  location allocated after that frame was pushed. Plan: the classification
  is a flow fact of the frame's slots; along the located steps
  (`Located`, `step_lift`, proved) a frame's allocations are numbered
  within it (`allocAt`).
- **The check of $`W_c`$** (`segWithin_of_check`, to be proved, from the
  two above and `stepWithin_of_check`, proved): where every charge
  $`W_c`$ joins is within $`\Psi_c`$, every step of $`C`$'s code at the
  caller's depth in the segment is `StepWithin Ψc |h₀|`. The steps at the
  caller's depth in the segment run the codes $`W_c`$ joins: the flow's
  fit at each reached state names the code each frame runs, and a frame at
  the caller's depth above $`f`$ is pushed by a call of the callee's run.

### An exceptional return

At an exceptional return the transfer reads $`\Phi^{e}`$. The graph reads
a call's handler at `callExc`, which bounds the heap by the callee's
footprint only where it states `onThrow`
([exceptional footprints](../SOURCE-ELABORATION.md#exceptional-footprints)),
and by nothing otherwise: the frame's check at a handler's facts runs at
$`\Phi^{e}=\top`$ there, and keeps only facts whose support lies in
$`R_C`$ at parts $`\Psi_c`$ allows. So in `throw.mjs` the fact
`c.i < xs.length` is lost at the handler (`xs` is outside storage, $`\top`$
shortens it) and `0 <= c.i` is kept (`c` is local). $`\Psi_C`$ joins every
member's normal and exceptional exits (the charges are of writes, each at
both exits), so the outside runs' bound is the same at both returns.

A callback that never returns has no resumption, so no transfer is read;
every state of its run still takes a step with an admissible world and a
typed heap, given by the callee's semantic type at the call
(`call_local_sound`, proved), which the graph theorem below reads
unchanged.

### A call of the component's own code

The package flow of pretext finds the walkers' `onLine` always a closure of
the package ([read-only handles](readonly-handles.md#deciding-the-flow),
measured there): a function of $`C`$ that calls the client's visitor at
its own call site, a *wrapper*. The design settles it as follows.

- **The obligation covers each step of client code, whoever called it.**
  `ClientFrame.Keeps` constrains every step whose active frame runs no code
  of $`C`$ and keeps the number of calls of $`C`$ active (`stepKind …
  = .outside`). A client visitor that a wrapper calls is such a step's
  code, at the wrapper's depth; the protection it reads is the history's at
  that step, which the wrapper's crossings out (its arguments to the
  client) extend by exposed locations only. So $`\Theta_C`$ binds the
  client on $`R_C`$ alike whether an entry or a wrapper calls it.
- **The walker's fact across the wrapper's call** is the transfer above
  at the walker's call of the wrapper, a framed call by the definition
  (the wrapper's code reaches a node calling outside code). The wrapper's
  own steps run at the walker's depth, in the same call of $`C`$; they
  are bounded by $`W_c`$, the charges of the wrapper's writes, those
  through closures the walker's frame created included. Observed
  (`wrapper.mjs`): a wrapper given the walker's cursor and writing it
  makes the walker read past the end (`NaN`); $`W_c`$ charges that write at
  the cursor's site, and the fact fails. A client shortening the walker's
  array through the wrapper makes the walker read past the end too
  (`NaN`): the array is outside storage given writable, off $`R_C`$, and
  $`\Phi`$, the wrapper's effect at the walker's slots, bounds it, $`\top`$
  where the wrapper calls a client of no stated effect.
- **Preconditions of a re-entered member** are the obligation of its
  caller, outside code: the client's call is one of the calls its type
  describes, covered by the callback's semantic type (trust, below), not
  by a check of $`C`$.

The note's rule reads, with this premise:

```math
\frac{c:\Phi\mid\Phi^{e}\qquad c\ \text{a call, inside a call of}\ C,\ \text{whose run may run code outside}\ C\qquad W_c\ \text{bounds its steps of}\ C\text{'s code at the caller's depth}\qquad \text{(S)}\quad\text{(K)}}{c:\ \Phi\oplus_C(\Psi_C\sqcup\Theta_C\sqcup W_c)\ \mid\ \Phi^{e}\oplus_C(\Psi_C\sqcup\Theta_C\sqcup W_c)}
```

At a call of outside code $`W_c=\mathsf{keep}`$ and the rule is the note's.
The note's section "The rule" and Appendix A take this statement when it is
built, with the paper's Lean (`readOnly_rule`) stated over `SegRun`.

### The check at a call

At a framed call node $`l`$ of code $`m`$, for each fact the existing
transfer drops, the pass runs `frameCheckAt q Ψc Φ⋆ S Fl.H (π.env l')
noKeys prot` for **every** context $`c`$ of $`m`$ and **every** node $`l'`$
of $`m`$ whose continuation and handler are $`l`$'s and which may call
outside code (`π.out l'`), and keeps the fact where all pass. This is the
conjunction `framed_at_call` (proved) requires: it gives `Framed` at some
context and some such node, which the frame's term does not name. A frame
of a wrapper's call is read the same way through `framed_at_innermost_keys`
(proved), at every node of $`m`$ with $`l`$'s continuation and handler.

- **Keys.** The checks give every location the key `none` (`NoKeys`,
  `reached_key`, proved), and a protocol entry at `none` joins every key
  of a site's records, so `noKeys` is sound for `Framed`
  (`ComponentChecks.Ctx.boundAt` joins, at the key `none`, every entry of
  the site and kind and the client change).
- **A region the flow gives no sites** (a value's fields by enumeration,
  a class, every location) is read at every part: the check requires
  $`\Psi_c(p)\sqsubseteq\delta`$ at every part $`p`$ and
  $`\gamma\sqsubseteq\delta`$ for every entry of $`\Phi_\star`$. `callParts`
  returns the full part set for it, and `framed_of_sites`'s cover premise
  holds of the full set trivially (to be proved, `framed_of_cover`, a
  generalization of `framed_of_sites`).
- **Protection** (`prot`) is read for a region only where its locations
  are reached at the entry's heap, read-only, from an entry argument at
  its parameter's type, and every part on the path to them preserves
  references under $`\Psi_C\sqcup\Theta_C`$ (*Reference-preserving
  protocol*). Then each such location has a live witness at the call:
  `witness_reached` (proved) at the location the entry reached, which the
  region names at the call because every reference on its path is
  preserved (`witness_of_path`, to be proved by induction on the path,
  each step by the bound of every step of $`C`$'s code between the entry
  and the call within $`\Psi_C`$ below the entry's length and of every
  outside run within $`\Psi_C\sqcup\Theta_C`$). Every other region is read
  unprotected. The history records no crossing into $`C`$ after the entry
  (`actualXs`), so no location becomes protected later, and a region read
  unprotected loses only precision.

## Certificates over the calls an execution makes

A member's certificate states, of each actual call of a code from a
reached state, what the pass's charges establish of that call's own steps.

```lean
structure Cert (Adm : Conf × Ghost (F.at C) → Prop) (Ψ : Protocol (F.at C))
    (G : (St (F.at C) → Prop) → Prop) (m : Option Code) where
  eff : Protocol (F.at C)
  within : ∀ p, (eff p).le (Ψ p) = true
  own : ∀ a a₁ b y z n, Adm a → XStep F C c Θ chk a a₁ → entered c a₁.1.t = m →
    δ F C c a₁ = δ F C c a + 1 → Ex (XStep F C c Θ chk) (QCall F C c (δ F C c a)) n a₁ y →
    XStep F C c Θ chk y z → δ F C c y = δ F C c a + 1 → ¬ Outside F C c y.1 →
    StepWithin eff a.1.s.h.length (lift F C c y.1 y.2) (lift F C c z.1 z.2)
  tolerant : ∀ I, G I → ∀ a a₁ y z n, Adm a → XStep F C c Θ chk a a₁ → entered c a₁.1.t = m →
    δ F C c a₁ = δ F C c a + 1 → Ex (XStep F C c Θ chk) (QCall F C c (δ F C c a)) n a₁ y →
    XStep F C c Θ chk y z → δ F C c y = δ F C c a + 1 → ¬ Outside F C c y.1 →
    Ok (δ F C c a + 1) (lift F C c y.1 y.2) → I (lift F C c y.1 y.2) → I (lift F C c z.1 z.2)
```

`own` and `tolerant` read one step of the call's own trace: the trace
from the call's entry $`a_1`$, made by the execution, every state of which
the call leaves active (`QCall`), to a step at the call's own depth of
$`C`$'s code, its exit among them. The steps belong to one execution, and
the step's frame was pushed after the call's entry. This replaces
`Cert.certified` and `Cert.tolerant` (`ReadOnlyExec.lean`), which quantify
over every `MemberRunOf` and every `PkgStep` (gap 4).

- **`decompose` restated** (to be proved, the same induction): its second
  conjunct builds the member's call as `MemberRun.Own` over the trace's
  steps, each own step meeting `StepWithin eff |h(a)|` by `own`, its runs
  one call deeper by the induction; `MemberRun.within` (proved) gives the
  member's bound, and `MemberRun.keeps` with `tolerant` its invariants.
  `Cert.member`, `exec_bound`, `exec_keeps`, `exec_rely` and `call_rely`
  keep their statements, read at the new `Cert`.
- **The certificate from the charges** (`cert_of_charges`, to be proved):
  `eff := Ψ_C`; `own` from `stepWrites_sound`, `stepWithin_of_check`
  (proved) at the protocol's charges (`ComponentChecks.protocolDiags` with
  no failure), and the *Fresh storage* discharge read at the call: a
  receiver allocated by the write's frame or, through a closure confined
  to its frames, by an enclosing frame, was allocated after the call's
  entry, since outside code holds no confined closure and the call's
  frames are pushed after its entry (`fresh_within_call`, to be proved, by
  `ownFresh_sound` and the flow's confinement of such closures). The
  certificate is the same for every code $`m`$: $`\Psi_C`$ charges every
  write of every code of $`C`$, so no member, entry label, argument or
  capture of the suspended context is identified.
- **`tolerant` from the guarantee's check**: at $`G=\emptyset`$ (the
  bound route) it is vacuous; for the guarantee route, from
  `keeps_of_charges` (proved) and `stepWrites_sound`, each step being an
  actual step of the call ([the guarantee route](#the-guarantee-route)).

The review's counter-model (a member writing nothing, a guarantee that a
local cell is zero, an abstract `PkgStep` changing it) is excluded: the
new `tolerant` quantifies over the member's own actual steps, and a
member writing nothing has steps that change no old location
(`stepWrites_sound`).

## Re-entry

A callback that re-enters $`C`$ with fresh storage creates calls of
$`C`$ deeper than the unit's call. Three things the unit's claim reads of
such a call, each without a fact of it:

1. **Its effect on $`R_C`$** is the certificate's, from the protocol's
   charges, which read the flow and the writes, not the graph's facts
   ([certificates](#certificates-over-the-calls-an-execution-makes)).
   A charge does not depend on a fact: an element's write is charged
   $`\mathsf{grow}`$ whatever its index, a `length` write
   $`\mathsf{any}`$ (`ComponentChecks`, *Charges*).
2. **Its progress and typed heap** inside the callback's run are given by
   the callee's semantic type at the unit's call (`call_local_sound`): the
   callback, an entry argument or a value the graph types, meets its arrow
   at every world, its calls of $`C`$ included.
3. **Its facts** are read by no clause of the unit's claim. The six
   clauses of `FramedRequestSafe` read a stated assertion at a state whose
   whole term runs the unit's graph at its label (`AssertedAt`:
   `t' = gotoOf P l L' d' c'`), the codes' assertions at their own graphs'
   top labels, and the posts at the unit's own exit; the graph's delivery
   at each node is read at the unit's top frame. A re-entered call's
   frames lie inside a callback's run inside the unit's frame, never the
   whole term.

So the witnesses the unit's claim needs are those of its own frames, whose
protected regions are reached by its entry arguments (`witness_reached`).
The draft keeps this as a property of the design, enforced by two
restrictions: the protocol's and the guarantee's checks read charges only,
and the history records no crossing into $`C`$ after the entry. A design
whose certificates read a member's framed facts would need, at a
re-entry, the entry's crossing of the member's arguments at their
parameter types in `chk` (the `enter` transition of `Ghost.stepAt` already
lets a step's crossings cross after the push) and the witness from it.

## The guarantee route

The bound route ($`G_C=\emptyset`$) reads no ownership: $`R_C`$ grows by
the marks and the history alone (`InR.mono`). The guarantee route keeps an
invariant $`I\in G_C`$ whose support lies in $`R_C`$ (`InvIn`) at every
resumption, and needs, at each step of $`C`$'s code, `hnew` of
`InvIn.of_step` and `hsup` of `installs_checked`. Both follow from three
facts about a support given by paths.

- **A path support.** $`\mathrm{supp}(I)`$ at a state is the set of
  locations on a fixed finite set of field paths $`\Pi`$ from the
  invariant's root (`PathSupport`, new): $`l\in\mathrm{supp}_t`$ iff
  $`h_t\vdash r\xrightarrow{\pi'}l`$ for a prefix $`\pi'`$ of some
  $`\pi\in\Pi`$. The supports `Ctx.supportOf` computes are of this form,
  paths read from a record of the candidate's first keys.
- **A new location is reached through a write** (`supp_split`, to be
  proved, from `follows_split`, proved): for a step $`t\to t'`$ and
  $`l\in\mathrm{supp}_{t'}`$, either $`l\in\mathrm{supp}_t`$, or the path
  to $`l`$ at $`t'`$ has a first location $`w`$ the step changed, with
  $`w\in\mathrm{supp}_t`$ (its prefix is unchanged) and $`l`$ reached from
  the value stored at $`w`$ by the rest of the path.
- **Every write the support reads is classified** (`protectedInto_of_supp`,
  to be proved, giving `hsup`): $`w\in\mathrm{supp}_t\subseteq R_C(t)`$
  by `InvIn` at $`t`$, so its mark is local or exposed, or it is outside
  storage protected at the entry. A local $`w`$: its part is in
  `Ctx.supportOf` (the static support covers the semantic one, by
  `stepWrites_sound` at the write's receiver and the support's paths
  read through the flow's contents, `pathSites`), so `cx.supported` holds
  (`protectedInto_local`, proved). An exposed $`w`$:
  `protectedInto_exposed` (proved). Protected outside storage: the
  receiver's set holds the entry's supplied sites, so the receiver's
  tokens hold the component's token for a value entering from outside
  (`protectedInto`'s first disjunct; to be proved from `EntryShape`'s
  `Supplied` slots). A released $`w`$ never lies in $`R_C`$: no crossing
  into $`C`$ after the entry is recorded and the entry history holds no
  released location (`entryStart_site`, proved), so none is protected.
- **`hnew`** (`hnew_of_paths`, to be proved): by `supp_split`, a new
  $`l`$ is reached from a value stored at a classified write, so it is
  among that store's value's reachable sites, whose (O) check passed
  (`installBad … = []`), the disjunct `invIn_of_installs` (proved) takes.

With the three, `invIn_of_installs` gives `InvIn` after every step of
$`C`$'s code, `SupportAt.outside` (proved) after every outside step, and
induction along the execution gives it at every resumption, exceptional
ones included. The review's counter-model, observed (`redirect.mjs`): a
re-entered member stores the client's writable array of the right length
in the handle's field, and the walker reads past its end after the client
shortens it (`NaN`); the store is into $`\mathrm{supp}_t`$, classified,
and (O) refuses it (`installIncoming`: a value entering from outside other
than read-only).

## The plan and its check

### The plan

```lean
inductive FunctionPlan (σ ι : Type) [Labels ι] [StoreView σ ι] where
  | graph (name : String) (namePos : Span) (request : SourceRequest σ ι)
  | framed (name : String) (namePos : Span) (request : SourceRequest σ ι) (spec : FrameSpec ι)

def FunctionPlan.certify : FunctionPlan σ ι → Except String (CertifiedPlan σ ι)
  | .graph name pos request => pure (.graph name pos request)
  | .framed name pos request spec => pure (.framed name pos request spec.frame)
```

`FunctionPlan.over` maps `spec` with the request. The exhaustive match
makes the new constructor a compile error until its branch exists;
`certify` converts it alone, no `Option` or projection discarding a plan.

`FrameSpec ι` is the wire's description of the unit's component, decoded
like every document (one declared type, every field required):

- the family of components with its sites numbered (`NumberedFamily`),
  the component $`C`$, and $`\Theta_C`$ (`@clients`, read-only by
  default);
- the finite flow (`FFlow`) of $`C`$'s codes, its marks the ones it gives
  (`FFlow.MarksFrom`: a site of $`O`$ released, every other local; the
  acceptance family is this one, so the cursor's site is local and the
  bindings check runs at it);
- the proposed protocol $`\Psi_C`$, a change per part;
- the entry's parameters with their declared types (`args`);
- for each framed call node, its depth charges $`W_c`$ and the supports
  the frame keeps at its continuation and at its handler.

`FrameSpec.frame : ClientFrame (Ty ι)` builds the frame the claim reads:
`codes` the flow's codes; `view` the read-only types of `Ty ι`; `chk` the
flow's sites of each step's fresh locations (`stepSite`), the key `none`,
and the step's actual crossings (`actualXs`); `start` the entry history at
`args` (`StartsEntry`); `enters` the calls at the module's closures
(`ReadOnlyFitsEntry`, the sibling slots) meeting `EntryShape` at the flow.
Its `chk` gives `FlowSites` and `NoKeys` by definition and
`ActualCrossings` by `actualXs`.

### What the pass checks

`MemberAccepted.framed`, beside `ordinary`'s premises over the request
(its codes accepted, its main graph accepted by the framed run, its read
summaries checked):

- `FFlow.check (remark F) = true`, `FFlow.entryB`, `FFlow.marksB`
  (decided; sound by `FFlow.check_sound`, `FFlow.marks_of_marksFrom`);
- (S), (K) and (O) over every body of the component with no failure
  (`ComponentChecks`), (S) the restriction *No suspension*;
- the protocol: every charge of every write of $`C`$'s code within
  $`\Psi_C`$ (`protocolDiags`), and $`\Theta_C\sqsubseteq\Psi_c`$;
- at each framed call node: every charge $`W_c`$ joins within $`\Psi_c`$,
  and each kept support passing the check of
  [the check at a call](#the-check-at-a-call), at $`\Phi`$ for the
  continuation's facts and $`\Phi^{e}`$ for the handler's;
- the main graph accepted by the pass run with those supports kept at
  the framed nodes (`RunCall.AcceptsFramed`, the pass's transfer with
  `callerFrameKeeps` extended by the kept supports).

## The theorems

### The graph at assumed returns

The graph theorem, relative to the returns of the framed calls
(`RunSoundFramed ι`, to be proved, beside `Target.RunSound`): for an
accepted run whose framed call nodes keep the supports $`S_l`$ at their
continuations and $`S^{e}_l`$ at their handlers, each field of
`GraphGuarantee` holds along the graph paths whose every evaluation of a
framed node $`l`$, from its entry $`(\rho,h)`$ to its return
$`(v,h')`$, meets

```math
\mathrm{Ret}_l(\rho,h,h')\iff\forall S\in S_l.\ \mathrm{Supported}(S,\rho,h,h')\qquad\mathrm{Ret}^{e}_l(\rho,h,h')\iff\forall S\in S^{e}_l.\ \mathrm{Supported}(S,\rho,h,h')
```

at a normal and an exceptional return. Paths that break it are cut: their
later states are outside the claim. Progress at every state, the states
inside a call included, is unconditional, as in `SafeGraph`.

Proof plan: the proof of `run_sound_single_pass` (proved), with the
call node's delivery (`callEntry_holds`, `callKept_sound`,
`callGrown_sound` and the index facts' `frameKeeps`, proved) taking, at a
framed node, `Supported` from $`\mathrm{Ret}_l`$ in place of
`callerFrame_post`; `Footprints.frame_step` reads its heap relation only
through `Supported`. The graph state carries the pending framed node's
entry, so $`\mathrm{Ret}_l`$ is read at the evaluation's end
(`SafeGraphRet`, a `SafeGraph` with that ghost, as `SafeUnder` is a
`SafePostExcW` with one). Size: every lemma between the node delivery and
`run_sound_pass` takes the hypothesis; none changes its argument.

### The returns, at reached executions

`ret_reached` (to be proved): at every reached evaluation of a framed node
of the unit's graph, a reached call state $`s_0`$ at the unit's top frame
to its resumption $`s_1`$ along steps keeping $`\Theta_C`$, with the
callee's post at $`s_1`$ ($`h_0\xrightarrow{\Phi}h_1`$ from `callPost`,
or $`\Phi^{e}`$ from `callExc`), $`\mathrm{Ret}_l`$ or
$`\mathrm{Ret}^{e}_l`$ holds. Plan: `framed_transfer` with
`ChkSound` (`chkSound_of_flow`, proved, from the checks above and
`EntryShape` at `enters`), `StartInv` (`startInv_of_entry`, proved),
`certs` (`cert_of_charges`), `hown` (`segWithin_of_check`), `Framed` from
`framed_at_call` or `framed_at_innermost_keys` with `frameCheck_sound`,
`regionSites_sound`, `classQuery_sound` (proved) and the witnesses
(`witness_of_path`).

### The framed claim, from the check

`framed_requestSafe` (to be proved):

```lean
theorem framed_requestSafe {f : FilePlans} {r : Req f} {spec : FrameSpec _}
    (hrun : RunSoundFramed (EquationStore.CheckedLabel f.F.equations f.F.primitive))
    (hkeep : RunKeepsSummaries (EquationStore.CheckedLabel f.F.equations f.F.primitive))
    (htypes : r.types = f.F.store) (hacc : FramedAccepted f r spec) :
    FramedRequestSafe r spec.frame
```

Proof plan, for each of the six clauses: by induction on the budget, the
invariant at each state being that it is reached from the clause's entry
(`ClientFrame.Reached`, with the execution from the entry), that its term
simulates a graph state of the unit's program (`GraphCode.Sim`, the
pending framed node's call state with it), and that the graph state is
safe along $`\mathrm{Ret}`$-paths (`RunSoundFramed`). A step from such a
state either breaks the obligation, after which `SafeUnder` asks nothing,
or is a `KStep` (`safeUnder_kstep`'s converse direction:
`sim_step_back`, proved, maps it to a transition); at a framed node's
return the execution so far is a reached segment, so `ret_reached` gives
$`\mathrm{Ret}`$ and the graph path stays a $`\mathrm{Ret}`$-path.
`AssertedAt` at a `gotoOf` state is the graph's assertion at that label
(`asserted_of_reach`, proved, read in this direction). This builds the
reached executions from the clause's entry without assuming the clause,
the direction the review found missing in `framed_reaches` (which assumes
`FramedAssertionsClause`; it stays the converse).

### The headline

`member_safe` gains the branch:

```lean
  | framed name pos r spec .. hplan .. hacc =>
    exact ⟨_, _, hplan, rfl, framed_requestSafe hrunF hkeep (hover j name pos r hplan) hacc⟩
```

and `passMember_sound` (H3) shows `passGroup` accepting a group makes a
framed member `MemberAccepted.framed`. `mode8Accepted_sound` keeps its
statement:

```lean
theorem mode8Accepted_sound {f : FilePlans} {i : Nat} (h : Mode8Accepted f i) : PassUnitSafe f i
```

- **Premise** (`Mode8Accepted f i`): unchanged, the exact CLI condition
  at either print site; a group with a framed member reaches it with its
  verdict printed `accept under client trust` (`CertifiedPlan.clientTrust`).
- **Conclusion** (`PassUnitSafe f i`): every member $`j`$ of $`i`$'s group
  is `MemberSafe f j`: its plan certifies (`FunctionPlan.certify`) to a
  graph plan whose request is `RequestSafe`, or to a framed plan whose
  request is `FramedRequestSafe r spec.frame`. For a framed member that
  is: from every call meeting the frame's entry premises
  (`ClientFrame.Call`) and the request's entry contracts, along every
  execution each of whose steps of code outside $`C`$ keeps $`\Theta_C`$,
  every state is a value, a throw or takes a step with an admissible world
  and a typed heap, and the footprint, postcondition, regional and
  assertion clauses hold, as `RequestSafe` states them. Where the
  obligation is met, it is `RequestSafe` at every call (`framed_callSafe`,
  proved).

Its premise and conclusion are reviewed again, as a change of the accepted
plan type requires; the record of the commit that builds it states
`Theorem modified (mode8Accepted_sound)` with this conclusion.

## Proved, to be proved, trust

**Proved at the base**, reused: `FFlow.check_sound`,
`ClientFrame.chkSound_of_flow`, `startInv_of_entry`, `entryStart_site`,
`ClientFrame.framed_at_call`, `framed_at_innermost_keys`,
`frameCheck_sound`, `framed_of_sites`, `regionSites_sound`, `reached_key`,
`witness_reached`, `call_segment`, `call_premises`, `decompose` (its
induction), `Run.bound`, `Run.keeps`, `MemberRun.within`,
`RBoundBelow.trans`, `InR.mono`, `pkg_step_ok`, `stepWithin_of_check`,
`keeps_of_charges`, `readOnly_rule`, `supported_of_framed`,
`invIn_of_installs`, `installs_checked`, `protectedInto_local`,
`protectedInto_exposed`, `SupportAt.outside`, `follows_split`,
`step_changes`, `step_lift`, `Fits.innermost`, `fitsAt_reached`,
`kstep_xstep`, `reached_ok`, `sim_step_back`, `asserted_of_reach`,
`framed_callSafe`, `call_local_sound`, `callKept_sound`,
`callGrown_sound`, `run_sound_single_pass`.

**To be proved**, each with its plan above: `framed_transfer`,
`SegRun.within`, `seg_run`, `RBound.mono`, `frameC_shape`,
`stepWrites_sound`, `ownFresh_sound`, `fresh_within_call`,
`segWithin_of_check`, `framed_of_cover`, `witness_of_path`, the new
`Cert` with `decompose` restated, `cert_of_charges`, `RunSoundFramed`,
`ret_reached`, `framed_requestSafe`, `member_safe`'s and
`passMember_sound`'s framed branches; for the guarantee route
`supp_split`, `protectedInto_of_supp`, `hnew_of_paths`. The order of the
build: the bound route first ($`G_C=\emptyset`$, which P22 and the
walkers' cursor facts read), then the guarantee route.

**Trust**, each a row of the [trust surface](../DESIGN.md#trust-surface):

- the client obligation $`\Theta_C`$ (`ClientFrame.Keeps`, `Row`), stated
  in the component's API, owner-approved;
- *Clients* (Read-only frames, Assumption "Clients"): outside code enters
  $`C`$ only through its interface, so every code tagged with $`C`$ is
  $`C`$'s (`Provenance`), and every closure of $`C`$ that outside code
  holds at an entry is one $`C`$ gave out (`EntryShape`, `GivenOut`),
  premises of `ClientFrame.Call`; that a sequence of entries each checked
  against one flow discharges `EntryShape` at each is conjectured;
- the callback's semantic type at the call: an outside value passed at an
  arrow type meets it (the existing rows on exported preconditions and on
  a callback's stated effect);
- a native's step model performs its model's steps (the `%ElementAt%`
  row), where a flow reads one.

## Tests

- **P22**, `bounds-pattern-unreachable-field-refused`: a gap, positive
  once built, renamed with its outcome. `walk`'s call `visit(c.i)` is a
  framed call of outside code ($`W_c=\mathsf{keep}`$). The cursor's site is
  local and captured by no closure, so $`\Psi_C`$ keeps `c.i` ($`\Psi_C`$
  charges nothing at it: `walk`'s write `c.i++` is to storage its own
  frame allocated); `xs`'s spine is outside storage given writable, off
  $`R_C`$, bounded by the visitor's $`\mathsf{grow}`$. `c.i < xs.length`
  and `0 <= c.i` pass the check (measured by the frame probe,
  [read-only handles](readonly-handles.md#deciding-the-flow)).
- **Kept negative**: `invalid-bounds-pattern-cursor-given` (the cursor
  given to the visitor: its site in $`O`$, released, off $`R_C`$).
- **New cases** (from [Counter-models](#counter-models)): a visitor that
  shortens and throws, the walker's handler reading at the index
  (negative, refused at the handler's read); the same walker reading at
  the handler only `0 <= c.i` (positive); a wrapper calling the client,
  the walker keeping its local cursor's bounds (positive); a wrapper
  writing the walker's cursor (negative, refused: $`W_c`$ charges the
  cursor's site); a client shortening the array through a wrapper
  (negative).
- **Controls** (forged fragments and forced proposals against the
  verifier): a flow proposing the cursor's site outside every capture
  slot where a closure captures it (refused by `FFlow.check`); a protocol
  proposing $`\mathsf{keep}`$ at a part a member writes (refused by
  `protocolDiags`); a $`W_c`$ omitting a wrapper's write (refused by the
  depth charges' check); a frame check passing at the call's node and
  failing at another node of the same continuation and handler (the fact
  dropped).
- **Pretext's walkers**: `walkPreparedLinesRaw` and
  `walkPreparedComplexLines` at the package, their `onLine` a wrapper.
  Their cursor bounds are read at local sites (measured to pass at every
  context, by the probe at the direct-call obligation); the facts on
  `prepared.widths` need keys beside `none` and the protected region of
  an entry argument read-only, both read by this design's check and
  neither required by the P22 case.

## Open points for review

1. **The callback's semantic type as a premise.** The framed claim
   assumes an outside callback meets its arrow unconditionally, its calls
   back into $`C`$ included, while what it proves of $`C`$'s entries holds
   only along executions keeping $`\Theta_C`$. Composing the claim of a
   client that re-enters $`C`$ with $`C`$'s framed claim needs a semantic
   type read under the obligation. Whether the existing callback row
   covers this, or a row of its own is needed, is for the owner.
2. **$`W_c`$ at a wrapper.** Its soundness rests on own-frame freshness
   being decided per frame and on the codes it joins covering every frame
   at the caller's depth in the segment (`segWithin_of_check`); a
   recursion back into the walker's code at the caller's depth writes the
   walker's site again, charged there.
3. **The conjunctive check** over every node with the call's continuation
   and handler: sound by `framed_at_call`'s existential; two nodes of one
   code sharing both are rare and lose the fact. The located labels
   (`ReadOnlyLocated.lean`) would name the node exactly at the cost of
   carrying them through `fitsAt_reached`.
4. **`EntryShape` at every call** is a premise of the claim, narrowing
   the calls it is about; its discharge from earlier entries is
   conjectured.
5. **`RunSoundFramed`'s size**: threading $`\mathrm{Ret}`$ through the
   graph theorem's proof is stated as touching only the call node's
   delivery; that is a reading of `run_sound_pass`'s structure, not yet a
   build.

## Counter-models

Each runs under `node` (observed, Node 26.13.0); the claimed outcome is
printed after it.

```js
// throw.mjs: { s: NaN, i: 2 }
function walk(xs, visit) {
  const c = { i: 0 }; let s = 0;
  while (c.i < xs.length) { try { visit(c.i); } catch { s += xs[c.i]; } c.i++; }
  return { s, i: c.i };
}
const xs = [1, 2, 3];
console.log(walk(xs, (i) => { if (i === 1) { xs.length = 0; throw new Error("stop"); } }));
```

```js
// wrapper.mjs: "client shortens xs: NaN", "wrapper writes cursor: NaN"
function walk(xs, onLine) {
  const c = { i: 0 }; let s = 0;
  while (c.i < xs.length) { onLine(c.i); s += xs[c.i]; c.i++; }
  return s;
}
function layout(xs, user) { return walk(xs, (i) => user(i)); }
const xs = [1, 2, 3];
console.log("client shortens xs:", layout(xs, (i) => { if (i === 1) xs.length = 1; }));
function walk2(xs, onLine) {
  const c = { i: 0 }; let s = 0;
  while (c.i < xs.length) { onLine(c); s += xs[c.i]; c.i++; }
  return s;
}
function layout2(xs, user) { return walk2(xs, (c) => { user(); c.i = c.i + 5; }); }
console.log("wrapper writes cursor:", layout2([1, 2, 3], () => {}));
```

```js
// redirect.mjs: NaN
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
