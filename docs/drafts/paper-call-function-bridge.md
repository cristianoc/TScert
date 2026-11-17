# Call and function-body correspondence

## The existing mechanism this extends

The owner of the specification is the first paper's Call and Fun rules in
[tolerant-frames-note/note.tex](tolerant-frames-note/note.tex). B already has
actual shared-calculus primitive execution, four-exit command execution,
world-valid triples, effects, and semantic/capture-avoiding assertion and
postcondition renaming. Those mechanisms are extended; no new evaluator or
heap/world model is proposed. Existing CommandSummary signature transport
accepts a supplied summary and is not an implementation of Fun.

## Displayed Call

First prove naturality of the existing primitive execution relation. Rename
command arguments and operations structurally and prove the executed shared
term equals the original at the pulled-back environment. Aliasing actual
arguments is permitted. A bound result needs the precise freshness condition:
only its formal result name maps to its actual result name. This makes fresh
binding commute with environment pullback; injectivity of argument renaming
is not required.

Transport the formal primitive triple along this execution correspondence.
The chosen exit world is retained. Actual output environment validity follows
from the original valid environment and the formal result's validity; it must
not be inferred merely from validity at names in the image of the renaming.
Transport normal and exceptional effects through the existing footprint rename
semantics. Provide the Call instance for the actual operation, not a supplied
summary or a theorem whose premise is the desired renamed call contract.
The existing first-order renaming equivalences identify semantic transport
with actual syntax. Declared-region admission transport remains a distinct
obligation where its source/current type contexts differ.

## Function-body realization

Fun requires a new operational correspondence between B Command bodies and
shared callable graph code. Prove lowering and execution inversion for normal
fallthrough (undefined), returned values and throws; reject a break escaping
the function boundary. Preserve heaps, frozen function entry, source/root
validity and shared reduction counts. A supplied sound-body summary would
leave precisely this obligation unproved. Recursive invocation uses induction
on actual shared reduction count: an invocation costs a shared step, whereas
some B administrative command constructors cost zero.

The body effect is restricted below the invocation-entry mark. Rest-array
allocation must occur after that mark, with proved length, density and element
readings from actual allocation. A known dense literal-length spread requires
actual element reads. Neither rest nor spread is represented by an assumed
unexecuted list.

## Freshness polarity to investigate

The paper permits arbitrary postcondition implication and says specifications
state freshness only of the result. Positive result freshness is preserved when
a callee's mark is lowered to an earlier caller mark. That fact alone does not
justify arbitrary implication: fresh(y) implies false can change truth when
the mark is lowered. This refutes a naive unchanged-Q mark substitution, not the complete Fun
rule: the displayed Call explicitly assumes mark independence, and its text
requires freshness rebasing separately. Before requesting a paper decision, establish the exact
operational instance and scope, or prove that the stated premises preclude it.
Do not add a polarity restriction or silently rebase arbitrary Q.

Astra independently read the exact Call/Fun premises and designed this order
on 2026-11-17. It identified the execution correspondence, actual-environment
validity and freshness/mark questions as separate proof obligations.

## Scope and declaration transport

A total naming map is an implementation device, not an extra Call premise.
Extend a finite input assignment with the fresh result, send unused names to a
non-result default, and prove the constructed map has the required result
fiber. Complete scoped AST rename-agreement proves unused images irrelevant;
old uses input scope, the result is current-only, logical maps lift together,
and both inner and outer regional effects participate. The displayed callee
is fixed. A final scoped corollary must assemble precondition dependence,
postcondition/effect scopes and declared-region admission; the raw total-map
transport alone is not labelled a complete finite substitution rule.

Program-only renaming must also preserve both scope and static admission.
Logical binders leave program names unchanged. Their declaration shift commutes
with program renaming of the shared even/odd root encoding. This extends the
existing scope and DeclaredPaths pullback mechanisms, without inferring object
or collection types from equality at one heap.

## Administrative reductions and raw completion

Astra reviewed these foundations before implementation. Shared graph code has
dispatch/invocation reductions in addition to the primitive reductions B counts.
For syntactic assertions, same-heap positive world truncation preserves truth:
project any higher-budget future to budget one, keeping the exact footprint
postcondition, and use induction on the assertion body. This is not arbitrary-
world independence, nor a theorem for arbitrary semantic predicates such as
budget greater than one. Full two-state transport preserves frozen anchors;
transition atoms require an exit budget below the truncated entry, or explicit
admissibility of both pairs. Implications follow by equivalence, not assumed
monotonicity.

After compiler inversion relates primitive count p to shared count N for the
same body segment, with p≤N<S.n, apply the body Triple at the original entry
budget and restrict its chosen exit from S.n-p to S.n-N. Exact syntactic
current-state transport requires the original entry/exit pair admissible; both
versions of each transition atom then have the same heap predicate. This
retains the original entry anchor and needs no arbitrary postcondition
monotonicity. Source/context validity survives the exit restriction. Only
same-heap administrative steps can be erased this way. Rest prologue allocation
changes the heap and can be observed even by quantifiers omitting the rest name;
it needs a separate operational proof. Begin with fixed-arity bodies.

Raw B completion should use shared isVal while ValidContext and ExitValid retain
source-value and world-reference guarantees. Otherwise an unspecified native
returning an internal machine value may complete graph code but disappear from
B's raw runs, making a body Triple vacuous. Broadening raw executions strengthens
Triple obligations; it supplies no source guarantee for arbitrary NativeCode.
Typed/host contracts still supply source guarantees. Return/Throw rules use
Argument.valid; actual Call validity recovers both source and references of a
bound result from the formal exit context. A and the shared calculus are unchanged.

## Outer lexical bindings remain in scope

Astra identified an admission defect before the fixed-arity body bridge: a choice
or handler join could forget an original input name, then a sequence could bind
that numeric name again. The named environment would overwrite an immutable
parameter. Require each join output to retain its input scope, then derive input
scope preservation and avoidance by structural induction. Shadowing remains
possible after alpha-renaming to a distinct identity. Keep raw execution general;
this is an admission correction. A caught name is local to its handler and is
excluded from the joined output, including when another branch reuses that raw
numeric slot. This follows the existing locality documented by the judgment.

## Fixed finite slot layout for command graphs

The next operational construction uses the existing graph envMap mechanism.
Choose B above every program name occurring anywhere in the command (bind and
catch names included). Slots 0 through B-1 retain those named values. Three
extra slots hold viewRead/viewWrite/viewLength and a fourth the exit payload; the symbolic host template is
var B, var (B+1), var (B+2). Every edge carries B+4 slots. A binding x maps its
output slot x to the newly pushed result (index zero), and every other slot i
to its previous index i+1. Perform uses effect with the complete identity map.
Catch uses the same replacement map on the actual raised value. Reconstruct
the total B environment using the original environment beyond B; finite command
scope ensures no command reads or binds those fallback names.

First prove replacement/identity envMap equations, named-environment agreement
and unchanged host slots. Native code slots must hold machine values when the
shared graph dispatch requires value environments. This is an explicit
representability condition of the function embedding, not a native safety or
contract assumption. The shared graph-entry/capture construction and its
reference/scoping validity still require proofs.

Compile explicit throw as an actual shared throw expression with its current
handler. Shared Raises.throwV requires a source value, whereas B's broadened
raw throw grammar admits any machine value. Therefore the required terminal
graph-to-B inversion may be general, but a forward simulation of every raw B
throw would be false for an internal spine. Do not implement catch as an
unconditional bind/jump, which would invent a shared catch of that stuck throw.
Any forward theorem must state its source-value condition. This distinction
strengthens, rather than weakens, the body Triple obligation.

Astra independently designed this finite layout and identified the raw throw
asymmetry. These are the next compiler obligations, not implemented Fun premises.

## Structured command continuations

The concrete next bridge extends Executes with a small control machine, not a
second heap semantics. Its stack has sequence, loop and catch frames. Running
a primitive uses an actual PrimitiveRun and its reduction count. Unfolding a
sequence/choice/loop/handler or propagating an exit is administrative and costs
zero in B's count. Return/throw arguments retain their raw isVal premises.
The four exits and frozen function entry are unchanged.

Interpret a stack structurally as the rest of the computation. A normal exit
through a sequence frame executes its second command; an abrupt exit skips it.
A normal exit through a loop frame executes the remaining loop, a break becomes
normal, and return/throw propagate. A catch frame binds an actual thrown value
and executes its handler; every other exit propagates. Each case then interprets
the shorter stack. This interpretation may reference Executes of the remaining
loop, so the definition itself recurses only on stack length.

Backward preservation of that interpretation by each control transition proves
that a finite terminating machine run gives the existing structured Executes,
with exactly its primitive count. A separate CPS graph construction must
produce concrete finite nodes/labels and relate each graph transition to these
control configurations (possibly several zero-cost administrative steps).
Actual graph dispatch consumes shared budget, so finite loops with no primitive
steps are handled by induction on the shared run, not by decreasing B's count.
Normal/return/throw/break exits must retain their source environment until the
compiler proof identifies the corresponding sink; a ret discards its frame.
No supplied command summary is part of this bridge.


## Implemented generated-command inversion

The finite offset compiler, front normalization, all concatenation lookups and
Origin/Routes evidence are generated internally. Root sink origins constrain
actual expressions, so metadata alone cannot justify a return or throw. Local
node inversion preserves the real heap and target map and retains the named
environment at the sink. The whole proof inducts on actual shared count;
enter/leave overhead decreases the suffix count even when primitive weight is
zero. Actual shared value and exceptional Steps yield the existing structured
Executes with p≤N. Native host code is required to be machine values for this
representation, not assumed safe merely from that fact. Full callable frame
setup, physical-budget postcondition transfer, Fun and rest remain separate.

## Native method elaboration is an execution obligation

A literal array has no push property/prototype in its raw B allocation. Ordinary
method lookup therefore obtains undefined, and invoking it is stuck. A scalar
string's readAt method lookup is also stuck. An assumed partial Triple at those
terms would not establish that the paper's native operation is represented.

Extend the existing invoke/named-environment mechanism with explicit resolved
native calls: invoke the supplied callee value with the receiver separate from
positional arguments. Ordinary user-method/property lookup remains separate.
The declared host identity and receiver sort select the native; a spelling such
as push alone is insufficient. The callee slot participates in scopes, renaming
and finite frame bounds, preserving the existing three typed-array captures.
Shared graph entry puts the receiver in slot 0; the paper's explicit method
receiver is not duplicated in the positional argument list. Ambient contracts
must supply receiver-compatible callability/availability/safety and exact
outcomes/effects, not merely SourceVal or isFun. Construct-only or incompatible
receivers show why those weaker conditions are insufficient. No real native
library implementation or new global axiom is proposed. Astra independently
confirmed this source-model obstruction and the explicit-callee design.


## Fixed-arity callable entry

The existing generated compiler and real `CallArguments.graphEntry` are joined
by an appended adapter, preserving every original body label. The modules are
[CallableEntryLayout](../../lean/Verification/Paper/TolerantFrames/CallableEntryLayout.lean),
[CallableEntryCode](../../lean/Verification/Paper/TolerantFrames/CallableEntryCode.lean)
and [CallableEntryCorrectness](../../lean/Verification/Paper/TolerantFrames/CallableEntryCorrectness.lean).

A finite source-selector list identifies receiver, parameter, capture, self or
undefined for each logical name. Parameter selection reuses actual padding and
discarding of already evaluated extras. Finite indices supply capture/parameter
bounds. The bind adapter receives [undefined, receiver, parameters, captures,
self], then maps the source prefix, three captured host values and undefined
payload into the existing canonical frame. The actual self comes from the last
invocation slot; no cyclic capture construction is used. Unused logical inputs
beyond the body frame remain in the restored outer environment.

The raw prefix consists of exactly three heap-preserving shared reductions:
callGraph, gotoEnter and frameBind. `CodeAgrees` requires exact lookup equality
at generated body nodes; extra adapter labels need no fabricated Origin. The
existing inversion proof is generalised once, retaining its original API as a
corollary. Every actual completed invocation yields N=3+q and structured body
execution with primitive p≤q<N, the same final heap and the same exit. Escaping
break remains distinct even though its sink returns undefined.

Machine values suffice for raw inversion. The separate entry-context theorem
requires source/world-valid receiver, arguments and self, and each capture
selected as a program input. Host-only slots have no program-root obligation.
Self's reference validity can nevertheless constrain references inside its
captures. CallableReferences derives it from actual identity/own-field roles
and capture references: generated symbolic expressions contain no heap references.
It assumes no callable behavior or desired function specification.
The heap and entry mark coincide with invocation's; no native availability or
safety follows.

This constructs an already represented graph callable and its raw invocation
bridge. The specification transport below excludes escaping break by the body's
false break obligation and preserves old across budget choices. Function
allocation/typing, recursive discharge and rest allocation/spread remain separate.
The design uses the existing graph/frame mechanism and was independently checked
against the actual shared call ABI before implementation.


## Scoped body specifications at actual invocation exits

[CallableEntrySpecification](../../lean/Verification/Paper/TolerantFrames/CallableEntrySpecification.lean)
uses the displayed body's Triple and Effects as premises, rather than a supplied
callable summary. ResultPost binds an arbitrary returned value in the current
phase only; fallthrough uses undefined. Return obligations freeze the same
original function entry used by normal and exceptional postconditions. The body
break obligation is false. An actual value or throw completion of the graph
therefore has a source/world-valid result or exception and its respective full
syntactic postcondition and regional effect.

Apply the body proof at the original entry S, obtaining a chosen exit of budget
S.n-p. Restrict this exit to positive budget S.n-N for the actual shared count
N<S.n. Full syntactic current-state equivalence handles implication, modalities,
transition atoms and both binders without changing the old anchor or mark.
[PostconditionEnvironmentScope](../../lean/Verification/Paper/TolerantFrames/PostconditionEnvironmentScope.lean)
uses the existing program renaming/agreement theorems to remove body locals:
normal posts read entry scope Γ and current scope Γ plus result, exceptional
posts read Γ in both phases. WellScoped implies all input names are preserved.
Effects keep their original entry environment; caller renaming is not inferred.

[CallableReferences](../../lean/Verification/Paper/TolerantFrames/CallableReferences.lean)
proves symbolic code has no embedded references. Generated self's reference
validity follows from actual object roles and captures; the combined entry
context theorem also needs source-valid receiver, arguments and selected program
captures. Host-only captures require raw machine-value representability for
execution inversion. Neither role validity nor machine values imply native safety.

These theorems transport proved body premises for a fixed-arity represented
callable. They do not discharge recursive uses of its own specification,
allocate/type the function, compare its finite decoded environment with a caller
under separate phase scopes, rebase the caller mark, or allocate rest/spread.
Thus they are not labelled the full Fun rule. Astra independently checked the
transport design against the actual completed-execution semantics.


## Separate phase environments and bounded recursive proofs

[PostconditionValuationScope](../../lean/Verification/Paper/TolerantFrames/PostconditionValuationScope.lean)
extends the existing scope-agreement proof jointly to program and logical
valuations. Entry/current scopes are independent and corresponding IndexedHeaps
remain identical, including worlds and budgets. Old selects entry agreement;
boxes compare the same future states; transitions use entry names; binders lift
logical agreement. This supplies the environment transport needed by actual calls.

[BoundedCommands](../../lean/Verification/Paper/TolerantFrames/BoundedCommands.lean)
adds n<N to completed-run premises while retaining n<S.n and the original entry
state. Full triples/effects are equivalent to all such bounds. Sequence, choice,
handlers and loop invariants compose at a fixed bound; sequence/handler/loop
postconditions are state assertions, which can capture fixed function-entry
parameters. Loop induction uses finite execution evidence, since iterations can
cost zero. [BoundedFrameRules](../../lean/Verification/Paper/TolerantFrames/BoundedFrameRules.lean)
provides Entry, Frame, Frame+ and the displayed modal Loop at the same bound.
[BoundedEffects](../../lean/Verification/Paper/TolerantFrames/BoundedEffects.lean)
composes sequence/handlers/loops for one common rigid footprint on both exits,
using actual chosen admissible worlds through the final component and restoring
the original footprint valuation. This is a sufficient mechanism for relative
body proofs, not the general exceptional/rebased Seq-Eff rule.

[RecursiveFunctions](../../lean/Verification/Paper/TolerantFrames/RecursiveFunctions.lean)
proves actual count induction for a concrete represented callable. Its relative
body proof may use that callable's specification only at counts k<N, and must
construct TripleBelow/EffectsBelow N. Real invocation inversion gives body p<N;
full postcondition exit truncation retains the original entry budget/old anchor.
FunctionEntryPre freezes symbolic entry by equalities reflexively true at each
actual valid P-entry; it imposes no new restriction on such calls. Normal and
exceptional invocation specifications follow for every actual count by strong
induction. This is a theorem schema with a genuine relative body-proof obligation,
not a supplied compiler summary or an unrestricted self triple.

[RecursiveCallRules](../../lean/Verification/Paper/TolerantFrames/RecursiveCallRules.lean)
connects the restricted hypothesis to actual PrimitiveRun: direct-call code is
exactly invocation of the concrete callable with its evaluated arguments. The
oracle is used at that primitive's actual count below N. P depends on input scope
and is mark-independent; Q/Qe have separate phase scopes and semantic mark
independence; both effects have input scope. Decoded-entry validity, machine
captures and equality of decoded/caller inputs are explicit encoding premises.
The whole output environment is recovered from original caller validity plus
admissibility, then a valid normal result is bound. Break/return obligations are
arbitrary because a primitive call cannot produce those command exits.

[MarkIndependence](../../lean/Verification/Paper/TolerantFrames/MarkIndependence.lean)
distinguishes semantic independence from a recursive no-freshness sufficient
check, traversing old, modalities, implication and both binders. The latter is
not a characterization. No arbitrary freshness postcondition is silently moved
to an earlier caller mark.

The recursive primitive rule is identity-aligned: arbitrary actuals still need
the existing scoped renaming layer connected to it. A relative body proof must
actually be constructed from the command/primitive rules in each application.
Function allocation/type membership, deriving capture/layout premises from
source typing, freshness rebasing, and rest/spread remain separate. These
results do not certify all recursive programs or establish a complete Fun rule.


## Rest allocation and the old anchor

The rest extension has a source-level anchor obstruction, independently reviewed
by Astra. Let F be the closed assertion ∃v.(v∈object ∧ len(v)=0). A valid heap
containing the function but no array/view spines makes F false; the empty rest
array makes it true after prologue allocation. Thus old(F) distinguishes the
invocation entry from the body entry after that allocation. It mentions neither
rest nor result and is mark-independent, with no freshness-region admission issue.

The paper says old selects the entry of the command whose triple contains it,
and in Fun says old in Q/Qe refers to body entry. Those anchors coincide in the
fixed-arity nonallocating adapter and differ for rest. Excluding the rest name
from the exported member does not prove allocation invariance of quantification.
The qualification matters: an unrestricted ordinary body triple from true alone
would not prove old(F); this obstructs the rest extension using its stated
rest-entry facts, whose incorporation into the body premise needs clarification.

An owner decision is pending: freeze exported old before rest allocation and
state the body premise with that anchor, or retain post-prologue body old with
explicit anchor translation/distinct call-specification semantics. The paper is
unchanged, and no rest/Fun gap is counted closed by this observation.
