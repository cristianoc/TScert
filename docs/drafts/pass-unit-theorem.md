# Draft: the single pass's unit theorem

What mode 8 (`verifier --verify-units 8`, [the single pass](single-pass.md))
proves of a unit it prints accepted, above the graph: from the pass
accepting each request of the unit's group to the safety of every function
of the unit. The graph-level part, that an accepted call of the pass
guarantees its graph, is [the tolerant-frames development](tolerant-frames-lean.md)'s;
this draft states the interface it is to meet (`RunSound`).

## The existing mechanism this extends

The acceptance theorem of the proved checker,
`SourceClaimJson.checkUnitJson_safe`
([what "verified" means](../DESIGN.md#what-verified-means)): a unit's
accepted verdict implies, for every function of the unit, safety of its
extracted graph at every admitted assignment, from every environment meeting
its inputs, with its footprint, fresh result, postcondition, regional bound
and stated assertions (`RequestsSafe`). Its premise is the exact condition
under which the CLI prints the verdict, and its plans cross the exhaustive
conversion to `CertifiedPlan`. The theorem here has the same conclusion
without the certificate, and its premise is mode 8's exact condition.

Two mechanisms of [the general mechanisms](../DESIGN.md#general-mechanisms)
bear on what the conclusion assumes: a unit's inputs include the values of
the functions it calls, at the effects
[inferred call effects](../SOURCE-ELABORATION.md#inferred-call-effects-elaboration-and-certification)
propose and each callee's own unit establishes; and code of another module
enters through [certified imports](../SOURCE-CONTRACTS.md#certified-imports).

The Lean modules are
[PassUnit](../../lean/Verification/Source/Claims/PassUnit.lean) (definitions),
[PassUnitCodes](../../lean/Verification/Source/Claims/PassUnitCodes.lean) (the code table),
[PassUnitPlans](../../lean/Verification/Source/Claims/PassUnitPlans.lean) (construction facts of the plans),
[PassUnitMember](../../lean/Verification/Source/Claims/PassUnitMember.lean) (the wrapper's checks),
[PassUnitSafe](../../lean/Verification/Source/Claims/PassUnitSafe.lean) and
[PassUnitHeadline](../../lean/Verification/Source/Claims/PassUnitHeadline.lean) (the theorems),
[PassUnitLink](../../lean/Verification/Source/Claims/PassUnitLink.lean) (the closure and the linking induction),
[PassUnitRealize](../../lean/Verification/Source/Claims/PassUnitRealize.lean) (the module's environment) and
[PassUnitFile](../../lean/Verification/Source/Claims/PassUnitFile.lean) (the file-level theorem).

## 1. The statement

### Definitions

Throughout, $`G`$ is a request's normal graph, $`\eta`$ an assignment of its
type parameters, $`G\eta`$ the graph reassigned at it, $`n`$ a step budget,
$`W`$ a world of budget $`n`$, $`h`$ a heap and $`\rho`$ an environment.

**Entry.** A request $`r`$ with inputs $`\Gamma`$, entry separation $`S`$
and entry index facts $`X`$ is entered at $`(\rho, n, W, h)`$ when

```math
\mathrm{Entry}_{G\eta}(\Gamma, S, X; \rho, n, W, h) \iff
  \rho \models_{n,W}^{G\eta} \Gamma \;\wedge\; \rho \models S \;\wedge\; \rho, h \models X
  \;\wedge\; \mathrm{WorldAdm}(W) \;\wedge\; \mathrm{HeapOk}_n(W, h)
```

(`EntryHolds`; $`\rho \models_{n,W}^{G} \Gamma`$ is `EnvOk`).

**Reachability.** $`P \vdash (h, s) \to^k (h', s')`$: the graph machine of
program $`P`$ goes from state $`s`$ on heap $`h`$ to $`s'`$ on $`h'`$ in $`k`$
transitions (`ReachesIn`).

**A safe request** (`RequestSafe`). For a request $`r`$ with program
$`P`$, start $`\ell_0`$, goal $`R`$, admitted assignments $`\mathrm{Adm}_r`$
(all of them for an unqualified body, its source signature's instances for a
qualified one), and $`\mathrm{run}(L, d)`$ the term running $`P`$ from
$`\ell_0`$ with frame $`L`$ and receiver $`d`$, $`r`$ is safe when, for every
$`\eta`$:

1. *safety*: $`\eta \in \mathrm{Adm}_r`$ and $`\mathrm{Entry}_{G\eta}(\Gamma, S, X; \rho, n, W, h)`$
   imply $`\mathrm{SafeGraph}_{n,W}(P, R; h, \ell_0\,\rho)`$ (`SafeClause`);
2. *footprint*: where $`r`$ claims a footprint $`\Phi \ne \top`$, a footprint
   on a throw, or a fresh result, $`\mathrm{run}(L, d)`$ from such an entry,
   with $`L`$ and $`d`$ values, is safe, returns with $`\Phi(h, h')`$ and,
   where fresh, a value whose store is at or above $`|h|`$, and throws with
   $`\Phi(h, h')`$ where it claims the throw (`FootprintClause`);
3. *postcondition*: where $`r`$ states facts $`E \ne []`$ at its returns,
   every return of $`\mathrm{run}(L, d)`$ with value $`v`$ and heap $`h'`$
   meets $`E`$ at $`v`$ and the inputs' entry values (`EnsuresClause`);
4. *regions*: where $`r`$ states a regional bound $`(\Phi, \mathcal R)`$,
   $`\mathrm{run}(L, d)`$ changes no location of $`h`$ outside $`\Phi`$ but
   the stores $`\mathcal R`$ selects at entry, on a throw too where its
   stated effect bounds one (`RegionalClause`);
5. *assertions*: for each stated assertion $`(\ell, K)`$ of $`P`$, each
   admitted $`\eta`$, entry and $`j < n`$, $`P \vdash (h, \ell_0\,\rho) \to^j (h', \ell\,\rho')`$
   implies $`\rho', h' \models K`$ (`AssertionsClause`);
6. *code assertions*: the same for each code request's requirements, from
   every frame meeting the code's signature (`CodeAssertionsClause`).

Conjuncts 1–4 are `RequestsSafe`'s semantic conjuncts. Conjuncts 5 and 6
replace its certificate-relative `RequestAssertionsEntailed` by validity at
the reached states: they state the assertion of the program, not of a
certificate.

**A safe member and unit.**

```math
\mathrm{MemberSafe}(f, i) \iff \exists\, p\, c.\; f.\mathrm{plans}[i] = \mathrm{ok}\ p \;\wedge\;
  \mathrm{certify}(p) = \mathrm{ok}\ c \;\wedge\;
  \begin{cases} \mathrm{RequestSafe}(r) & c = \mathrm{graph}(\_, \_, r) \end{cases}
```

```math
\mathrm{PassUnitSafe}(f, i) \iff \forall j \in f.\mathrm{group}(i).\; \mathrm{MemberSafe}(f, j)
```

The match is over every constructor of `CertifiedPlan`: a new constructor is
a compile error there, and no plan variant is filtered out.

### The headline

**Theorem** `passUnit_safe` (proved under hypotheses H1–H4 of section 2). Let
$`f' = f.\mathrm{withHeadFacts}(\mathit{givenLines}, \mathrm{false})`$. Then

```math
\begin{aligned}
&\mathrm{fragmentPlans}(\mathit{ast}, \mathit{key}, \mathit{budget}, \mathit{sel}, \mathit{standIns}, \mathit{force}) = \mathrm{ok}\ f
  \;\wedge\; i \in f.\mathrm{selected}(\mathit{sel}) \\
&\wedge\; (f'.\mathrm{passGroup}(\mathit{fuel}, f.\mathrm{group}(i), \ldots)).2 = \mathrm{ok}\ \mathit{deps}
  \;\Longrightarrow\; \mathrm{PassUnitSafe}(f', i)
\end{aligned}
```

The premise is the condition under which mode 8 prints the unit's line
`"accepted": true` (`Source/RequestCli.lean`, the mode 8 branch), every
argument of `passGroup` free: the CLI's comparison, observation, repetition,
counting and given-file inputs range over all their values.

## 2. The hypotheses

**H1 `RunSound`** (the graph lane's target). For every call $`c`$ of
`SinglePass.run` (`RunCall`: every argument it takes) over $`G`$ and image
check $`I`$, every $`\mathit{after}`$, assignment set $`A`$ and inputs
$`\Gamma`$:

```math
\begin{aligned}
&c \text{ accepts leaving } \mathit{after}
 \;\wedge\; \mathrm{Scope}(c.\mathrm{checker}, A)
 \;\wedge\; c.\mathrm{claims}[c.\mathrm{start}].\mathrm{context} = \Gamma \\
&\wedge\; \mathrm{CodesSound}(G, c.\mathrm{codes})
 \;\wedge\; \mathrm{SummariesSound}(G, I, \mathit{after}.\mathrm{summaries})
 \;\wedge\; \mathrm{entryFields}(G, \Gamma, \mathcal R) \text{ for } c\text{'s regions } \mathcal R \\
&\Longrightarrow\; \mathrm{GraphGuarantee}_G(A, P, \ell_0, R, \Gamma, S, X, \mathit{assertions}, \mathit{bound}, E, \mathit{regional})
\end{aligned}
```

$`\mathrm{Scope}`$ (`CheckerScope`) relates the ordinary checker to every
assignment and a qualified body's checker to its admitted instances.
`GraphGuarantee` is conjuncts 1–5 of `RequestSafe` for the call's own
arguments: conjunct 2 where $`\mathit{bound} = (\Phi, \mathit{fresh}, \mathit{onThrow})`$,
conjunct 4 where $`\mathit{regional} = (\Phi, \mathcal R, \mathit{exc})`$, conjuncts 2–4
for the term running any node lists whose graph is $`P`$. Every argument
not named in the premise is a free proposal: the pool, candidates, cuts,
given implications, arguments and inputs, known evidence, cached answers and
reference. A sound `run` therefore checks at its start whatever it installs
there (the entry gap of the proof plan), validates every cached answer it
uses and records every read summary it relies on.

**H2 `RunKeepsSummaries`** (graph lane). Every read summary of the answers a
call starts from is among those it leaves. The wrapper checks only the last
run's summaries; the code runs before it rely on theirs.

**H3 `PassGroupChecks`** (wrapper, section 3). `passGroup` accepting a group
makes every member `MemberAccepted`. A statement about the actual function.

**H4 `FragmentStartContexts`** (extraction). In mode 8's plans, each
request's start claim states its inputs and each code request's its frame
(`StartContexts`). Neither the pass nor `passGroup` checks it, and `run`
receives no inputs.

## 3. The wrapper

`MemberAccepted` states what `passGroup` checks of a member, each check as
the exact call or condition the code makes:

- the plan is a graph request (`PlanAt`);
- the declared effect's conditions (`declaredEffect`: async at `top`, an
  async unit promising no fresh result, the claim within the stated effect);
- unqualified: each stated region's entry conditions (not async, not fresh,
  `checkEntryFields`); each code request's conditions and run, in order,
  against the table of those before it (`CodesAccepted`); the main graph's
  run at its bound and regions, or the bound refused and the regional
  fallback with no region, followed by the stated regions' run
  (`MainAccepted`); each final run's read summaries checked;
- qualified: footprint `top` on normal return alone, no postcondition,
  regions or codes, one run at the body's checker over its own graph and
  image check, its read summaries checked.

What each establishes, all proved:

- the code table: `codesAccepted_sound` (H1, H2): accepted code runs extend
  a sound table to a sound one, the counterpart of `GraphCode.extendTable_sound`.
  Its step, `codeSpec_of_guarantee`, is `GraphCode.codeChecked_sound`'s
  argument with the run's guarantee in place of `checkEntryUsing` and the
  effect's three cases (`top`, pure, bounded) read from `codeBound` in place
  of `effectChecked`. The premise that changes is the certificate check;
  the summaries are the final ones the wrapper checks (H2 carries them back).
- each code's guarantee, for its assertions: `codesAccepted_guarantees`;
- the main graph: `main_guarantee` (H1); the footprint by the bound, by the
  graph's purity (`footprint_of_bound`, the pure shortcut proved from safety
  as the old checker's) or by the regional fallback (`footprint_of_fallback`);
- read summaries: `summaries_of_checked`, at the frozen store's image check
  because every plan is over that store (`fragmentPlans_overStore`,
  `withHeadFacts_overStore`);
- qualified bodies: `qualified_requestSafe`, the conclusion at the body's
  admitted instances (`CheckerScope.qualified`), the scope of
  `checkRequests_safe_at`;
- a member: `member_safe`; the unit: `passUnit_safe`.

Two checks establish nothing `RequestSafe` states. The expression
obligations (`ExpressionClaims.checkAllResult`) compare claims and have no
soundness theorem in either headline. The declared effect's conditions give
the async property `checkRequests_async` states, outside `RequestsSafe`.

### H3 and the repairs it needs

`passGroup` is one `Id.run` block; each member's outcome is a local of its
loop, with early returns, a `for` with `break` over the codes, and the
diagnostics interleaved. No theorem can name the member's outcome, so H3 is
not proved. H3 holds of `passGroup` once two repairs are made, and is then
provable by unfolding:

- **R1, the structure.** Extract `passMember : FilePlans → … → Nat → MemberRun`,
  a pure function returning the request, the code runs with their answers,
  the main runs taken and their summaries' checks, and make `passGroup` its
  fold plus the rendering of lines. H3 is then a lemma per field.
- **R2, the fallback's summaries.** After the regional fallback, where the
  unit states regions, the regions' run starts from the answers before the
  fallback and only its summaries are checked: the fallback run's summaries,
  on which its footprint rests, are never checked. `MainAccepted.fallback`
  requires them checked; the repair checks them, or starts the regions' run
  from the fallback's answers so H2 carries them.
- **R3, an observed code run.** A code run returning `.observed` breaks the
  loop with no refusal, and the main graph runs over a table without that
  code and the ones after it. The code runs pass no observation, so this
  needs `run` to observe only when asked; the repair refuses there.

## 4. Dependencies and linking

`RequestSafe` is local: its entry premise $`\rho \models \Gamma`$ includes the
slots holding the values of the functions the unit calls, at the types its
callers read for them: the footprints `declarationEffects` proposes, a
recursive function's self-assumption, the module values the
initialization's walk types. A caller's theorem holds of the program once
those values meet those types.

### The closure

A verdict line of mode 8 names a unit, its group's members and, accepted,
its dependencies (`FilePlans.dependencies`): the groups its members reach
outside the group. Mode 8 plans no module run (`fragmentPlans_modules`,
proved), so every dependency is a unit of the file. The closure of a file's
verdicts $`V`$ (unit $`\mapsto`$ accepted dependencies, or refused) is

```math
\mathrm{ClosedIn}(V, S) \iff \forall u \in S.\; \exists\, D.\; V(u) = \mathrm{accepted}(D) \wedge D \subseteq S
```

`closedUnits` computes it: the accepted units, shrunk while a remaining unit
has a dependency outside, kept where the result is closed; a dependency
with no verdict refuses its dependents. `closedUnits_closed` (proved): its
result is closed. `fileVerdicts` is the verdicts mode 8's loop prints, and
`closedUnits_safe` (proved, under H1–H4): every closed unit is a selected
unit whose group `passGroup` accepts, so every member of its group is safe.
The agreement tool's `closed` (`dev/single-pass-agreement.mts`) is this
fixpoint, but it treats a dependency with no verdict as closed.

### The induction

Let $`M(u, n)`$ be the interface of unit $`u`$ at budget $`n`$: the value
the module's environment holds for each member meets, in every world of
budget $`n`$, the type its callers read (`MeetsAt`).

**Theorem** `link` (proved). For a set $`S`$ closed under $`\mathrm{deps}`$,

```math
\frac{\forall u.\; M(u, 0) \qquad
  \forall u \in S.\; \forall n.\; (\forall m \le n.\; M(u, m)) \wedge (\forall d \in \mathrm{deps}(u).\; \forall m \le n.\; M(d, m)) \Rightarrow M(u, n+1)}
 {\forall n.\; \forall u \in S.\; M(u, n)}
```

by induction on $`n`$. Recursion needs no order on units: a unit's own
group and every cycle of groups are covered because the step from $`n`$ to
$`n + 1`$ reads interfaces at budgets up to $`n`$ only. `closedUnits_linked`
(proved) instantiates it at `closedUnits`, each unit depending on itself
(its group's members) and on its printed dependencies.

**Theorem** `envOk_of_linked` (proved). Where each slot a link names holds
its callee's module value at the type its interface states, that interface
holds at budget $`n`$, and every other slot meets its type,
$`\rho \models_{n,W} \Gamma`$. So `RequestSafe`'s entry premise reduces to
the unit's own parameters once its callees are linked.

### H5: the realization

The step premise of `link` at a closed unit is that the unit's value meets
its interface one budget up. It is proved for the module's environment
defined below, from the units' own `RequestSafe`, under two hypotheses
about the file's layout and its outside slots (H5a, H5b).

**The module's code.** A module function's code (`ModuleCode`) is graph
code (arity $`a`$, node lists $`E, K`$, start $`\ell_0`$, kind) with, per
capture $`k`$ in frame order after the receiver and the parameters, a type
$`C_k`$ and a slot $`s_k`$: $`\mathrm{linked}(d)`$, the value of the file's
function $`d`$, or $`\mathrm{outside}(v)`$, a value from outside the file's
functions (an import, a host value, a module constant or cell).

**The module's environment** (`approxEnv`, `approx`). The value of $`u`$
unfolded $`n`$ times is its closure over its slots, each linked one
holding its callee unfolded $`n - 1`$ times:

```math
\mathrm{env}_0(u) = \mathtt{null} \qquad
\mathrm{env}_{n+1}(u) = \mathrm{closure}_u\big(s_1[\mathrm{env}_n], \ldots, s_m[\mathrm{env}_n]\big) \qquad
\mathrm{approx}_n(u) = \mathrm{env}_{n+1}(u)
```

with $`\mathrm{linked}(d)[e] = e(d)`$ and $`\mathrm{outside}(v)[e] = v`$. A
closure holds its captured values, so a cycle of functions has no finite
closure; the depth-$`n`$ unfolding is the environment a run of at most
$`n`$ steps sees, since each call spends a step.

**Realized** (`Realizes`). A unit $`u`$ of a set $`S`$ is realized when its
interface $`I_u`$ presents one clause of signatures $`L`$ and variadic
signatures $`S_v`$ which its code offers at its captures' types
(`CodeOffers`) with its kind (`KindOffers`); it has one slot per capture;
each linked slot $`\mathrm{linked}(d)`$ has type $`I_d`$ with $`d \in S`$
(the slot agreement); and each outside slot's value meets its type at every
budget in every world.

**Theorem** `closure_meets_below` (proved). Graph code of fixed arity
offering the signatures of $`F`$, whose captured values meet their types at
every budget $`j < n`$ in every world, meets $`F`$ at $`n`$ in every world:
every call of a closure runs its code below the budget of the call. It is
`offers_self`'s induction with the self entry replaced by captures given
below the budget.

**Theorem** `unitSpec_of_requestSafe` (proved). Where a unit request $`r`$
is a code $`c`$'s (`UnitIsCode`: unqualified, inputs $`c`$'s frame, program
$`c`$'s node lists, start and goal $`c`$'s, no entry separation, $`c`$'s
precondition as entry facts, $`c`$'s footprint, fresh and throw flags) and
$`c`$ meets the code conditions (`codeConditions`),

```math
\mathrm{RequestSafe}(r) \;\Longrightarrow\; \forall \eta.\; \mathrm{GraphCodeSpec}_{G\eta}(c)
```

It shares its argument with the code requests' `codeSpec_of_guarantee`
through `codeSpec_of_clauses` (proved): safety from the frame and the bound,
by the bound, the graph's purity or the top footprint.

**Theorem** `approx_meets` (proved). If every unit of $`S`$ is realized
against $`S`$ and every outside value is a closed value,

```math
\forall n.\; \forall u \in S.\; \forall m \le n.\; \forall W \in \mathrm{World}_m.\;
  \mathrm{approx}_n(u) \in ⟦I_u⟧_{m,W}
```

by induction on $`n`$ with `closure_meets_below`; recursion and cycles of
units go through because the captured values are one unfolding below.
`approx_captures_envOk` (proved): the values the depth-$`n`$ environment
captures for $`u \in S`$ meet $`u`$'s capture types at $`n`$, the module
part of $`u`$'s entry premise. `approx_link` (proved) restates
`approx_meets` as `link`'s interface.

**H5a, the module's layout** (`ModuleLayout`, the extraction's frame
layout). For each closed unit $`u`$: its code, interface and slots as
above, its interface one clause, one slot per capture, the slot agreement,
and each signature $`p`$ of its interface realized by a member $`j`$ of its
group (`RowRealized`): $`j`$'s plan is a request that is the code of $`u`$
at $`p`$ and meets the code conditions. It is a statement about the
extraction (the slot table `ordinarySlots` builds, `withStandIns`,
`withNeverImports`, the frame `extractMember` lays out), not proved: every
function on that path is a `do` block over the front with no theorem about
its frame, and part of it is decidable at the verdict (see 6.3).

**H5b, the outside contracts** (`OutsideContracts`). Every value a closed
unit's outside slot holds meets the slot's type at every budget. It is the
trusted boundary of section 5, slot by slot: an import's declared contract
or an import stand-in's footprint, a host value's contract, and a module
constant's or cell's type, which the initialization's request would have to
establish as a postcondition on the module's cells (`withInitTypes`
proposes these types; the `:init` request states no such postcondition). A
function stand-in fixes a linked slot's type, $`I_u`$, which $`u`$'s own
unit establishes: it needs no hypothesis. With no import, no host value and
no module constant, no slot is outside and H5b holds vacuously.

**What H5a excludes.** A unit realized through `RowRealized` has fixed
arity, no rest, an unqualified (non-generic) request, and signatures meeting
the code conditions: no postcondition, stated region, precondition, element
promise, fresh object, receiver growth or element write. A closed unit
outside these has no layout and `passFile_safe` says nothing of its value;
its members stay safe locally (`passUnit_safe`).

## 5. The boundaries that stay trusted

Each enters the headline at a named place:

- **Parser fidelity**: `ast`, the premise of `fragmentPlans`. The theorem
  is about the plans of that document.
- **Annotation interpretation**: each request's inputs, result, claimed
  footprint, regions and postcondition, read from the declarations; they are
  $`\Gamma`$, $`R`$ and the claims `RequestSafe` states.
- **Source-to-graph lowering**: each request's program $`P`$. `RequestSafe`
  is about $`P`$'s runs. In particular, at a test whose context type answers
  it (`Answers`, `Source/Lowering/Execution.lean`, the expression dispatch),
  the lowering emits the selected arm alone. The decision is proved sound,
  `TypingBasics.answers_sound`: every value of the type answers the test as
  decided. What stays trusted is that the tested value at that point of the
  source run has the context type, which needs a source semantics to state.
- **Sparse handler placement**: which nodes the lowering gives a handler;
  the graph's handler edges are $`P`$'s.
- **Host and declaration-only import contracts**: the types of the slots
  holding host values and imports, assumed in $`\rho \models \Gamma`$ and
  never discharged by linking; imported footprints (`standIns.imports`)
  enter the front as written.
- **Stand-ins**: a function stand-in fixes the footprint its callers read;
  its own unit checks it, so it is discharged by H5 for a closed unit. An
  import stand-in is an assumed contract, as above.
- **Proposals of the walk**: the candidates, given implications, arguments
  and inputs, known evidence and cached answers are arguments H1 quantifies
  over; no proposal is trusted.
- **Compiled replacements**: the proofs are about the logical definitions;
  the verifier runs the pass's `implemented_by` replacements
  (`SinglePass.timedKind`, `clock`, `same`, `oneObject`, `Store.diff`), which
  no theorem relates to their definitions.

The hypotheses are listed with their owners in section 6.
