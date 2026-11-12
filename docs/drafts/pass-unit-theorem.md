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
[PassUnitFile](../../lean/Verification/Source/Claims/PassUnitFile.lean) (the file-level theorem) and
[PassUnitModules](../../lean/Verification/Source/Claims/PassUnitModules.lean) (linking modules) and
[PassUnitObligations](../../lean/Verification/Source/Claims/PassUnitObligations.lean) (expression obligations, async members) and
[PassUnitInterfaces](../../lean/Verification/Source/Claims/PassUnitInterfaces.lean) (outside slots by kind, module interfaces, the command line's condition) and
[PassUnitSignatures](../../lean/Verification/Source/Claims/PassUnitSignatures.lean) (signature agreement from a store map) and
[PassUnitCross](../../lean/Verification/Source/Claims/PassUnitCross.lean) (the cross-module theorem) and
[PassUnitWrapper](../../lean/Verification/Source/Claims/PassUnitWrapper.lean) (the wrapper's lemmas) and
[PassUnitMemberRun](../../lean/Verification/Source/Claims/PassUnitMemberRun.lean) (what an accepted member run establishes) and
[PassUnitVerdict](../../lean/Verification/Source/Claims/PassUnitVerdict.lean) (the headline at mode 8's verdict) and
[PassUnitInit](../../lean/Verification/Source/Claims/PassUnitInit.lean) (the initialization's assertions), over
[StoreMaps](../../lean/Verification/Types/StoreMaps.lean) (one type's meaning in two stores) and
[StoreMapsCheck](../../lean/Verification/Types/StoreMapsCheck.lean) (the store-map check) and
[StoreMapsBuiltins](../../lean/Verification/Types/StoreMapsBuiltins.lean) (store maps and the built-ins).

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

**Theorem** `passUnit_safe` (proved under hypotheses H1–H3 of section 2). Let
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

### The final statement

**Theorem** `passUnitVerdict_safe` (proved under H1 and H2,
[PassUnitVerdict](../../lean/Verification/Source/Claims/PassUnitVerdict.lean)). With
$`f = \mathrm{preparedMode8}(\mathit{force}, \mathit{givenLines}, f_0)`$, the
plans with the given head facts, and the false start fact where
`TSCERT_FORCE` names `start-facts`:

```math
\begin{aligned}
&\big(\exists\, \mathit{est}.\; \mathrm{fragmentPlansFromInterfaces}(\mathit{ast}, \ldots, \mathit{est}) = \mathrm{ok}\ f_0
 \;\vee\; \exists\, \mathit{ms}\, \mathit{ns}.\; \mathrm{fragmentPlansWithModules}(\mathit{ast}, \ldots) = \mathrm{ok}\ (f_0, \mathit{ms}, \mathit{ns})\big) \\
&\wedge\; (f.\mathrm{passGroup}(\mathit{fuel}, f.\mathrm{group}(i), \ldots, \mathit{observe} = \mathrm{none}, \ldots)).2 = \mathrm{ok}\ \mathit{deps}
 \;\Longrightarrow\; \forall j \in f.\mathrm{group}(i).\; \mathrm{MemberSafe}(f, j)
\end{aligned}
```

`passUnitCli_safe` states the same for every value of $`\mathit{observe}`$,
under H1–H3; H3 at $`\mathit{observe} = \mathrm{none}`$ is proved
(`passGroupChecks_unobserved passMember_sound`, section 3), so
`passUnitVerdict_safe` has H1 and H2 as its only hypotheses.

The premise is the condition under which `verifyUnitsFile` prints unit
$`i`$'s line `"accepted": true` in mode 8 with `TSCERT_OBSERVE` unset, with
an interface file (`--verify-interface-stage`) or without; every other
argument is free: the comparison, node, repetition, given lines and counting
inputs, the modules' check and the interface file's entries. With
`TSCERT_OBSERVE` set, the observation rerun's outcome replaces a refusal
(section 3), and the verdict is outside the theorem. Its
conclusion is `checkUnitJson_safe`'s for a file's unit: every member's plan
crosses the exhaustive certification and its request is safe
(`RequestSafe`). With the file-level part (`passFile_safe_kinds`) every
closed unit's value meets its interface, and with `crossModule_safe` an
importer's units meet theirs, their imports discharged by their modules'
checks (section 7).

### The hypotheses, by level and class

Each level's theorem adds hypotheses to the one below it:

- **Unit**, `passUnitVerdict_safe`: H1, H2 (`passUnitCli_safe`, for every
  `observe`: H1, H2, H3).
- **File**, `passFile_safe_kinds`: H1–H3, `ReceiverDropSound`, the layout (H5a `ModuleLayout`),
  the established slots (`EstablishedSlots`) and the four outside kinds met
  (`KindMet` for `declared`, `standIn`, `host`, `moduleCell`).
- **Cross-module**, `crossModule_safe`: H1–H3, `ReceiverDropSound`, the importer's layout, the
  publication order (`ReadsEarlier`), each published entry's step
  (`EstablishedStep`) and layout (`StepLayouts`), the chosen slots
  (`ChosenSlots`), each established slot reading an entry of the order, and
  the other three outside kinds; with `established_of_provenance` the steps
  follow from `InterfaceProvenance` and `EstablishProvenance`.

**(i) The graph lane** (about `SinglePass.run`, section 2):

- **H1 `RunSound`**: for every call $`c`$ over $`G`$ and image check $`I`$,
  every $`\mathit{after}`$ and every assignment set $`A`$, $`c`$ accepting
  leaving $`\mathit{after}`$, $`\mathrm{Scope}(c.\mathrm{passChecker}, A)`$,
  $`\mathrm{CodesSound}(G, c.\mathrm{codes})`$,
  $`\mathrm{SummariesSound}(G, I, \mathit{after}.\mathrm{summaries})`$ and
  $`c`$'s region entry fields imply
  $`\mathrm{GraphGuarantee}_G(A, c.P, c.\mathrm{start}, c.\mathrm{goal}, c.\mathrm{inputs}, c.S, c.X, c.\mathit{assertions}, c.\mathit{bound}, c.E, c.\mathit{regional})`$.
- **H2 `RunKeepsSummaries`**: for every call $`c`$, every summary of
  $`c.\mathrm{answers}`$ is a summary of the answers $`c`$ returns.
- **`ReceiverDropSound`** (a lemma about the graph machine): for a request
  $`r`$ with no receiver slot and a code $`c`$ with
  $`\mathrm{UnitIsReceiverless}(r, c)`$ and $`\mathrm{codeConditions}(c)`$,
  $`\mathrm{RequestSafe}(r) \Rightarrow \forall \eta.\; \mathrm{GraphCodeSpec}_{G\eta}(\mathrm{dropReceiver}(c))`$
  (section 4, "H5: the realization").

**(ii) The wrapper lane** (lemmas about the actual functions, each a
statement for every value of every argument):

- `passGroup_members`: $`(f.\mathrm{passGroup}(\mathit{fuel}, g, \ldots)).2 = \mathrm{ok}\ d \Rightarrow \forall j \in g.\; (f.\mathrm{passMember}(\mathit{fuel}, \ldots, j)).\mathrm{accepted}`$,
  and `passMember_sound`: $`(f.\mathrm{passMember}(\ldots, j)).\mathrm{accepted} \Rightarrow \mathrm{MemberAccepted}(f, j)`$;
  both proved, `passMember_sound` at `observe = none`; together H3 on the
  command's verdict path (`passGroupChecks_unobserved`, section 3).
- `EstablishProvenance`: $`\mathrm{establishModules}(\mathit{needs}, \ldots, \mathit{incoming}, \mathit{prepare}, \mathit{check}) = \mathrm{ok}\ (\mathit{est}, \ldots) \Rightarrow \forall e \in \mathit{est}.\; e \in \mathit{incoming} \vee \mathrm{EstablishedStep}(e)`$,
  after R1's repair of `establishModules` (a per-module step and its fold).
- **The publication order**: for the components `interfaceComponents`
  returns and the entries `establishModules` publishes along them,
  `ReadsEarlier`: each module's reads are entries published at an earlier
  position. A lemma about the fold of `fragmentPlansWithModules` and of
  the interface stage's component order, of `published_holds`' form.
- **The layout check** (H5a): a decidable check at the verdict building
  each closed unit's `ModuleCode` from its plan (one clause, one slot per
  capture, the slot agreement, each signature realized by a member's
  request, `RowRealized`), with a soundness lemma giving `ModuleLayout`;
  run at each module's step it gives `StepLayouts`.
- **The `:init` postcondition** (section 4, H5b): `KindMet` for
  `moduleCell`, a named hypothesis; `init_asserted` (proved) gives the
  stated facts at the init graph's finish states.
- **The signature-agreement check** (section 7): the interface entry
  carries its rows $`(G_s, I_s)`$; `interfaceFile` publishes it where
  $`\mathrm{matchStores}(G_m, G_s, \ldots, I_u, I_s)`$ accepts
  (`EstablishedStep` states it); the importer refuses a slot whose
  $`\mathrm{matchStores}(G_s, G, \ldots, I_s, A)`$ refuses (`ModuleLayout`
  states the slot's type is that $`A`$), and a module's step refuses its own
  read the same way (section 7, "A module's own reads"); a published
  module's store states the built-ins (section 7, "Built-ins in one graph
  only"). Then `ChosenSlots`' agreement is `signatureAgrees_of_checks`
  (proved).

**(iii) Trusted boundaries**, each with why no Lean theorem states it today
and what would close it:

- **Parser fidelity** (`ast`): the TypeScript parse and the front's
  document are produced outside Lean, from TypeScript's compiler; closing
  it needs a TypeScript syntax in Lean and a proof (or a checked
  translation validation) of the parser's output against it.
- **Annotation interpretation** (each request's $`\Gamma`$, $`R`$,
  footprints, regions, pre- and postconditions): the meaning of a
  TypeScript type annotation has no definition in Lean; closing it needs a
  semantics of TypeScript's types and a theorem that the type reader's
  lowering represents each annotation's whole contract.
- **Source-to-graph lowering** (each request's program $`P`$, sparse
  handler placement, the context type at a test, that a budget-$`n`$ source
  run sees the depth-$`n`$ environment): there is no source semantics in
  Lean to relate $`P`$'s runs to; closing it needs one, and a simulation
  theorem for `extractMember`.
- **Declaration-only import contracts** (kind `declared`): the imported
  code is outside the checked fragment; closing it needs the import's
  implementation checked as a module (kind `established`), or a reviewed
  contract ([certified imports](../SOURCE-CONTRACTS.md#certified-imports)).
- **Host contracts** (kind `host`, the intrinsics' declarations): the host
  is native code; closing it needs a model of each host function
  ([prototype contracts](../SOURCE-CONTRACTS.md#prototype-contracts)) or a
  run-time check at the boundary.
- **The stage store's replay** (`InterfaceProvenance`): the importer reads
  an interface file another process wrote; closing it needs the importer to
  recompute the interface (`fragmentPlansWithModules`, then the hypothesis
  is `EstablishProvenance` alone) or a signed record of the computation.
- **Compiled replacements** (`implemented_by`, section 5): the compiled code
  is not the definitions the proofs are about; closing it needs each
  replacement's equality to its definition proved (`@[csimp]`) or the
  replacement removed.

The stand-in kind is vacuous with no `TSCERT_STANDINS`
(`standIns_vacuous`, proved), so it is a measurement aid, not a boundary.

**(iv) Exclusions of the linking**, each a change of the proved side
(other lanes' modules), stated as a request with the theorem it enables
(section 4 states how each case is excluded):

- **Element preconditions**: `GraphCodeSpec` (`TypingBasics`) gains a
  premise $`\mathrm{ElemsAt}(e.\mathrm{requires})`$ at entry, and
  `codeConditions` stops excluding `Effect.requires`; with an entry fact of
  the request stating it, `unitSpec_of_requestSafe` and `approx_meets`
  then cover a unit with an element precondition.
- **Postconditions**: `Effect.below` admits `ensures` facts over slots up
  to the arity plus one, `Effect.post` reads them (`post_args` for a
  nonempty `ensures`), and `codeSpec_of_clauses` carries `EnsuresClause`
  into that post; then `unitSpec_of_requestSafe` covers `@ensures`.
- **Stated regions**: `GraphCodeSpec`'s frame condition is the regional
  one (`ArgumentStoreRegionsWithin`) where the effect states regions, and
  `Effect.below` admits them; `codeSpec_of_clauses` carries
  `RegionalClause` into it.
- **A rest parameter**: `CodeOffers` over variadic signatures with the
  packed rest frame (`codeFrame` with the row's rest),
  `closure_meets_below` over them, and `RowRealized` per variadic row; then
  `approx_meets` covers a unit with a rest parameter.
- **Type parameters**: a relation between a body's admitted instances
  (`qualified_requestSafe`'s scope) and its scheme's bounded, allowed
  substitutions (`schemeSemWithArgs`), and `approx_meets` stated per
  instance; then a generic module function's value meets its scheme.

Against `checkUnitJson_safe` with the old module theorem, clause by clause:
its premise is the CLI's exact condition, as there; the certificate's
acceptance has no counterpart, since no certificate is built; safety,
footprint and fresh result, postcondition and regions are the same
statements from the same entry; assertions hold at the reached states
in place of being entailed by a certificate; the module values are
discharged by linking (the old theorem assumes them in
$`\rho \models \Gamma`$); an imported module's functions are discharged
through its interface under `InterfaceProvenance`, where the old module case
checks each certified import's restricted document in the same process;
async holds of the member and its codes (`member_async`, `codes_async`), as
`checkRequests_async` states outside `RequestsSafe`.

## 2. The hypotheses

**H1 `RunSound`** (the graph lane's target). For every call $`c`$ of
`SinglePass.run` (`RunCall`: every argument it takes) over $`G`$ and image
check $`I`$, every $`\mathit{after}`$ and assignment set $`A`$, with
$`\Gamma = c.\mathrm{inputs}`$:

```math
\begin{aligned}
&c \text{ accepts leaving } \mathit{after}
 \;\wedge\; \mathrm{Scope}(c.\mathrm{passChecker}, A)
 \;\wedge\; \mathrm{CodesSound}(G, c.\mathrm{codes}) \\
&\wedge\; \mathrm{SummariesSound}(G, I, \mathit{after}.\mathrm{summaries})
 \;\wedge\; \mathrm{entryFields}(G, \Gamma, \mathcal R) \text{ for } c\text{'s regions } \mathcal R \\
&\Longrightarrow\; \mathrm{GraphGuarantee}_G(A, P, \ell_0, R, \Gamma, S, X, \mathit{assertions}, \mathit{bound}, E, \mathit{regional})
\end{aligned}
```

$`\mathrm{Scope}`$ (`CheckerScope`) relates the pass checker
(`SinglePass.PassChecker`) `.ordinary` to every assignment and
`.qualified` at a body's subtyping to that body's admitted instances. The
call's inputs $`c.\mathrm{inputs}`$ are an argument of `run`, which checks
the start claim's context against them (`SinglePass.entryRefusal`).
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

The wrapper gives each run the inputs the theorem's entry premise names:
the request's inputs for its own graph (`MainCall`), each code request's
frame for that code's (`CodeRunAccepted`). No hypothesis about the plans'
start claims is needed.

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

Two checks establish nothing `RequestSafe` states: the expression
obligations and the declared effect's async condition (section 8).

### H3 and the repairs it needs

`passMember` is a pure function returning the member's run (`MemberRun`:
the request's own refusal, the qualified run, the code runs, the main
runs, the summaries' and obligations' checks, the outcome), and
`passGroup` is its fold with the lines rendered. H3 splits in two:

- `passGroup_members` (proved): $`(f.\mathrm{passGroup}(\ldots)).2 = \mathrm{ok}\ d \Rightarrow \forall j \in g.\; \exists m.\; f.\mathrm{passMember}(\ldots, j) = \mathrm{ok}\ m \wedge m.\mathrm{accepted}`$.
- `passMember_sound` (proved, PassUnitMemberRun): `PassMemberSound`, at
  `observe = none`,
  $`f.\mathrm{passMember}(\ldots, \mathrm{none}, \ldots, j) = \mathrm{ok}\ m \wedge m.\mathrm{accepted} \Rightarrow \mathrm{MemberAccepted}(f, j)`$.
  The proof follows the function's steps, each `let` of its body
  extracted as a local definition (`extract_lets`) and each branch split
  where it is reached, so no step unfolds the whole body (the module
  checks in about 10 s, measured 2026-11-12). A code run's request is
  `codeRequest r q` (`q.asRequest r.toRequest`), whose inputs and entry
  facts are `codeFrame` and `codeEntryIndices` by definition; code
  conditions and `codeBound` are written inline, equal by unfolding; the
  table the main run reads is `admits` of the accepted codes
  (`codesInOrder_accepted`: every run `codesInOrder` returns accepted makes
  the codes `CodesAccepted` and the table every code's entry), equal to
  `admits (r.codes.map entry)`. The obligations' check and the two
  refusals no clause names (`no node to observe`, the repeated runs'
  `notHandled`) only refuse.

`passGroupChecks_unobserved passMember_sound` is H3 on the command's
verdict path. With an observation asked (`TSCERT_OBSERVE`), a refused
outcome is replaced by the outcome of an observation rerun, which nothing
keeps from being accepted; H3 for every `observe` needs the wrapper to keep
the refusal there (the rerun's outcome used only where it is not
accepted), a request of the pass lane.

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
`closedUnits_safe` (proved, under H1–H3): every closed unit is a selected
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

with $`\mathrm{linked}(d)[e] = e(d)`$ and $`\mathrm{outside}(v)[e] = v_n`$:
an outside slot holds one value per depth, an import's being its own
module's environment at that depth. A
closure holds its captured values, so a cycle of functions has no finite
closure; the depth-$`n`$ unfolding is the environment a run of at most
$`n`$ steps sees, since each call spends a step.

**Realized** (`Realizes`). A unit $`u`$ of a set $`S`$ is realized when its
interface $`I_u`$ presents one clause of signatures $`L`$ and variadic
signatures $`S_v`$ which its code offers at its captures' types
(`CodeOffers`) with its kind (`KindOffers`); it has one slot per capture;
each linked slot $`\mathrm{linked}(d)`$ has type $`I_d`$ with $`d \in S`$
(the slot agreement); and each outside slot's value at depth $`i`$ meets
its type at every budget $`j \le i`$ in every world.

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

**A function declared without `this`.** Every call of a closure enters
its code with the receiver in slot 0 (`graphEntry`; a plain call passes
`undefined`), and the request of a function declared without `this` has
no receiver slot: its inputs are $`\mathit{params} \mathbin{+\!\!+} C`$
(`extractNormalizedFn`). Its module code is
$`\mathrm{dropReceiver}(c)`$: the request's node lists with one node
appended, at which the code starts, evaluating `undefined` and continuing
at the request's start with the slots $`1, \ldots, a + |C| + 1`$ of the
frame (the parameters, the captures, the closure). `UnitIsReceiverless`
$`(r, c)`$ states the request is $`c`$'s behind that prologue: unqualified,
no rest, $`r.\mathrm{inputs} = c.\mathrm{row.arguments.take}(a) \mathbin{+\!\!+} C`$,
its program, start and goal $`c`$'s at that frame (a promise's parameter
unshifted, `receiverlessGoal`), no entry separation, its entry facts implied
by $`c`$'s at every frame with a receiver in front, and $`c`$'s footprint,
fresh and throw flags. `ReceiverDropSound` (a named hypothesis, section 1)
gives $`\mathrm{GraphCodeSpec}(\mathrm{dropReceiver}(c))`$ from
$`\mathrm{RequestSafe}(r)`$: the prologue's two transitions lead from
$`\mathit{recv} :: L`$ to the request's start at $`L`$, and every later
transition is one of the request's program.

**H5a, the module's layout** (`ModuleLayout`, the extraction's frame
layout). A set $`D`$ of functions laid out, holding every closed unit and
every member of its group (a mutually recursive group's non-leaders
included), and for each $`x \in D`$: its code, interface and slots as above,
its interface one clause, one slot per capture, each linked slot's callee
in $`D`$ at its interface, and each signature $`p`$ of its interface
realized (`RowRealized`) by a member $`j`$ of the group of some closed
unit: $`j`$'s plan is a request that is a code $`e`$'s (`CodeOf`:
`UnitIsCode` with $`e`$ the module code, or `UnitIsReceiverless` with
$`\mathrm{dropReceiver}(e)`$ the module code) meeting the code conditions.
The realizing member is any member of any closed group: a member of its own
group, or, for an overload, of the group whose request is at that
signature. Linking is per function within and across groups: the
environment (`approxEnv`) is indexed by function, its captured values one
unfolding below, so `approx_meets` covers every $`x \in D`$; the verdicts'
closure (`closedUnits`) is per group. `layout_realizes` (proved under
`ReceiverDropSound`) gives every $`x \in D`$ realized from its members'
safety (`rowRealized_spec`). H5a is a statement about the extraction (the
slot table `ordinarySlots` builds, `withStandIns`, `withNeverImports`, the
frame `extractMember` lays out), not proved: every function on that path is
a `do` block over the front with no theorem about its frame; part of it is
decidable at the verdict (the layout check).

**The layout check against real units** (measured by the front lane on
206 units of the pipeline's cases, 2026-11-12, with the previous layout:
one member per unit, rows realized by the unit's own group, a receiver
slot required): 30 refused, every one a unit another unit of its file
calls. Against the restated layout, argued from the refusal kinds (not
rerun): 26 refused at "no receiver slot" are admitted under
`ReceiverDropSound` where their entry facts are empty (the check's
sufficient case of `UnitIsReceiverless.indices`); the mutually recursive
unit (`even@210`, whose group's non-leader `odd@302` it captures) is
admitted, `odd` laid out in $`D`$; an overload is admitted where each
overload signature's row is realized by the member whose request is at it
with the same node lists, decided per row; the 4 generic functions stay
refused (type parameters, below).

**H5b, the outside contracts** (`OutsideContracts`). Every value a closed
unit's outside slot holds at depth $`i`$ meets the slot's type at every
budget $`j \le i`$. It splits by the kind of the slot (`OutsideKind`, a
table `kinds` the layout states), and `outsideContracts_of_kinds` (proved)
gives `OutsideContracts` from the five kinds met (`KindMet`):

- **An import with a body, read at an established entry** (`established`):
  no hypothesis of its own; `established_met` (proved) discharges it from
  the entry's module (section 7).
- **A declaration-only import, or an import read at its declared type**
  (`declared`): its contract is the declaration as the front reads it (the
  importer's `declarations` entry of that name, lowered by the type reader
  as for any declared value) and states that the value meets that type at
  every budget. A trusted boundary, unchanged from the proved checker's
  ([certified imports](../SOURCE-CONTRACTS.md#certified-imports)).
- **An import stand-in** (`standIn`, `TSCERT_STANDINS`, a measurement aid):
  its contract is the written footprint. `standIns_vacuous` (proved): with
  no stand-in slot, as with no stand-in file, it holds.
- **A host value** (`host`): its host contract, a trusted boundary.
- **A module constant or cell** (`moduleCell`): the initialization's
  obligation. The lemma the wrapper lane would provide:

```math
\mathrm{passGroup}(\texttt{:init}) \text{ accepts} \;\Longrightarrow\;
  \forall \text{ cell } c \text{ of type } C_c.\; \forall n\, W.\; h_{\mathrm{after\ init}}(c) \in ⟦C_c⟧_{n,W}
```

  The `:init` request's assertions at its finish nodes give, by
  `init_asserted` (proved, from `RequestSafe`'s assertions clause), their
  facts $`K`$ at every state reached there within the budget, from every
  entry and admitted assignment:

```math
(l, K) \in r.\mathrm{assertions} \wedge \mathrm{RequestSafe}(r) \wedge \mathrm{Entry}(\rho, n, W, h)
\wedge j < n \wedge P \vdash (h, \ell_0\,\rho) \to^j (h', l\,\rho') \Longrightarrow \rho', h' \models K
```

  The slot's contract is a type, and an assertion's facts are no type
  labels (`HeapKnowledge.Knowledge`: cells, values, links, separation,
  elements, indices), so `KindMet` for `moduleCell` stays a named
  hypothesis. It follows from three statements: (a) the pass checks typed
  assertions $`(l, s, A)`$, and the guarantee gives
  $`\rho'(s) \in ⟦A⟧`$ at every reached state (the graph lane:
  `GraphGuarantee`'s assertions conjunct for typed assertions), the
  `:init` request stating, per module constant, its walk type met with its
  annotation, per early cell its storage contract; (b) the slot's value at
  each depth is slot $`s`$'s value at a reached finish state (the
  extraction); (c) a cell's later writes keep it, each unit's write being
  checked at the contract. A cell holds a reference, whose meaning depends
  on the world, so (a) gives it at the worlds the run reaches, and
  `KindMet`'s every world needs the meaning's world independence for the
  slot's type, or `OutsideContracts` stated at the worlds extending the
  initialization's.

`passFile_safe_kinds` (proved) is `passFile_safe` with H5b replaced by
these: `EstablishedSlots` and four `KindMet` premises.

**What H5a excludes, and what each needs.** A function realized through
`RowRealized` has fixed arity, no rest, an unqualified request, and
signatures meeting the code conditions (`codeConditions`) and the code
specification's own condition `Effect.below` (inside `GraphCodeSpec`). A
closed unit outside these stays safe locally (`passUnit_safe`);
`passFile_safe` says nothing of its value. Each case against the actual
definitions:

- *a precondition on the call's values* (`@requires`, the effect's `pre`
  index facts): admitted. `codeConditions` does not exclude it,
  `UnitIsCode.indices` takes it as the request's entry facts
  (`codeEntryIndices`), `GraphCodeSpec` assumes it at entry (`PreAt`), and
  `codeSpec_of_clauses` discharges the entry from it
  (`codeEntryIndices_holds`); the caller's call rule establishes it at the
  call. An element predicate on the receiver (`Effect.requires`, an
  `ElemPred`) is excluded by `codeConditions`; lifting it needs an
  `ElemsAt` premise in `GraphCodeSpec` (`TypingBasics`) and an entry fact
  of the request stating it, neither of which exists.
- *a postcondition* (`@ensures`): excluded by `Effect.below`
  (`e.ensures.isEmpty`), which `GraphCodeSpec` requires of every
  signature. `EnsuresClause` gives the returns' facts; lifting needs
  `Effect.below` to admit `ensures` facts at slots up to the arity plus one
  (`CallEffects`), the post of `GraphCodeSpec` to read them
  (`Effect.post`, which `post_args` relates to the frame only for an empty
  `ensures`), and `codeSpec_of_clauses` to carry `EnsuresClause` into that
  post.
- *stated regions*: excluded by `Effect.below` (`e.regions.isEmpty`).
  `RegionalClause` gives the bound; lifting needs the specification's frame
  condition to be the regional one (`ArgumentStoreRegionsWithin`) in place
  of the footprint, in `GraphCodeSpec`.
- *a rest parameter*: `RowRealized` fixes `e.store = none` and
  `closure_meets_below` is stated for `CodeOffers … false L S []`, no
  variadic signature realized. Lifting needs `CodeOffers` over the variadic
  signatures $`S_v`$ with the packed rest frame (`codeFrame` with the row's
  rest), `closure_meets_below` extended to them, and `RowRealized` per
  variadic row.
- *type parameters*: the interface is a scheme; `RequestSafe` holds at the
  admitted instances (`qualified_requestSafe`), and `approx_meets` must be
  stated per instance $`\eta \in \mathrm{Adm}`$ against $`I_u\eta`$: a
  scheme row's meaning (`schemeSemWithArgs`) asks the value to meet every
  bounded instance at once, so the step needs the instances' safety for one
  code, which `qualified_requestSafe` gives for the body's own admitted
  instances; what is missing is the relation between the body's admitted
  instances and the scheme's bounded, allowed substitutions.

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

The hypotheses are listed with their owners in section 1.

## 6. The file-level theorem

### The statement

**Theorem** `passFile_safe` (proved under H1–H3, H5a, H5b). Let
$`f' = f.\mathrm{withHeadFacts}(\mathit{givenLines}, \mathrm{false})`$,
$`V = \mathrm{fileVerdicts}(f, \ldots)`$ the verdicts mode 8's loop prints
and $`S = \mathrm{closedUnits}(V)`$. Then

```math
\begin{aligned}
&\mathrm{fragmentPlans}(\ldots) = \mathrm{ok}\ f \;\wedge\; \mathrm{ModuleLayout}(f', S) \;\wedge\; \mathrm{OutsideContracts}
 \;\Longrightarrow\; \forall u \in S. \\
&\quad \exists i \in f.\mathrm{selected}.\; \mathrm{unitId}(i) = u \wedge \mathrm{PassUnitSafe}(f', i) \\
&\quad \wedge\; \forall n.\; \forall m \le n.\; \forall W.\; \mathrm{approx}_n(u) \in ⟦I_u⟧_{m,W} \\
&\quad \wedge\; \forall n.\; \forall W.\; \text{the values } \mathrm{env} \text{ captures for } u \models_{n,W} C_u
\end{aligned}
```

Every member of each closed unit's group is safe from every entry meeting
its inputs; each closed function's value in the module's environment meets
the arrow its callers read, its effect included, at every budget; and its
module slots are met by that environment. This statement, with
`passUnit_safe` for a unit's line alone, takes the place of
`checkUnitJson_safe` for mode 8.

### The hypotheses and who discharges them

Section 1 lists them by class ("The hypotheses, by level and class").

### The lemma the wrapper lane provides

With `passMember f fuel compare debugNode repeats given observe counting j`
the pure function a member's checks become, and `.accepted` its verdict:

```math
\begin{aligned}
&\texttt{passGroup\_members}:\; (f.\mathrm{passGroup}(\mathit{fuel}, g, \ldots)).2 = \mathrm{ok}\ d
  \;\Longrightarrow\; \forall j \in g.\; (f.\mathrm{passMember}(\mathit{fuel}, \ldots, j)).\mathrm{accepted} \\
&\texttt{passMember\_sound}:\; (f.\mathrm{passMember}(\mathit{fuel}, \ldots, j)).\mathrm{accepted}
  \;\Longrightarrow\; \mathrm{MemberAccepted}(f, j)
\end{aligned}
```

for every value of every argument. `MemberAccepted` is the inductive of
section 3 as written in `PassUnitMember`, its clauses the exact calls:
`PlanAt`, `declaredEffect`, the region entry conditions, `CodesAccepted`
(each code run accepted, R3: a run returning an observation refuses) and
`MainAccepted` (R2: in the fallback, the fallback run's own summaries
checked, which `MainAccepted.fallback` requires), or the qualified case.

The comparison with `checkUnitJson_safe` is in section 1, under the final
statement.

## 7. Module interfaces

### The existing mechanism

A module's interface is the result of the canonical component computation,
`establishModules`, over the modules' components (`interfaceComponents`:
the strongly connected components of the import graph in dependency order,
members by location). Each module is planned by `fragmentPlansCore` with
the entries established before it as its imports' footprints, prepared
(its given head facts), its reached groups checked by `check`, and a
function's entry $`((\ell, n), (\Phi, t, \Phi_r), u)`$ added where its group
$`u`$ is in the fixpoint `ok`: accepted with every dependency in `ok` or
established before. An importer reads an entry at its declared type with
that footprint (`importedArrow`), after the declaration-identity and
signature-agreement checks. [Module interfaces](module-interfaces.md) owns
the computation and its wire.

### What is within Lean and what is trusted

Within Lean: the component computation (`establishModules`, run by
`RequestCli.interfaceFile` on a component's request), its encoding
(`encodeInterfaces`), the importer's decoding against its own fragment's
module documents (`decodeInterfaces`), the importer's plans from the
decoded entries (`fragmentPlansFromInterfaces`) and the same computation in
one invocation (`fragmentPlansWithModules`). Trusted: the stage store's
replay. The importer is a separate process that reads an interface file; that
the file is the output of `interfaceFile` at the request its key names is
the store's guarantee (`pipeline/module-interfaces.mts`), exercised by the
forged-interface control. The theorem takes it as one hypothesis.

**`InterfaceProvenance`** (trusted boundary, the stage store). Every entry
$`e`$ the importer decodes was published by `establishModules` at mode 8's
prepare and check: for some modules, incoming entries $`\mathit{inc}`$ with
$`e \notin \mathit{inc}`$ and result $`\mathit{est}'`$ with $`e \in \mathit{est}'`$.

**`EstablishProvenance`** (under hypothesis; the wrapper lane, about
`establishModules` as H3 is about `passGroup`). Every entry
`establishModules` returns was given to it or satisfies `EstablishedStep`:
its module $`m`$ is planned by `fragmentPlansCore` over its document at its
names; its footprint is the one the module's claim of that function
states; its unit is in a set `ok` of wire identities, each a leader of the
prepared plans whose group `check` accepts with every dependency in `ok` or
established before. `establishModules` is a `for` loop with `continue`
over an `Except` block; the same repair as R1 (a pure per-module step and
its fold) makes it a lemma per field.

### The theorems

**Theorem** `step_units_safe` (proved under H1–H3). For a step of mode 8's
interface computation, every unit of its `ok` is a selected unit of the
module's prepared plans whose group is safe (`PassUnitSafe`): the check is
`passGroup`, the plans are over their store (`fragmentPlansCore_overStore`,
at every argument of the core planner), so `passGroupOver_safe` applies.

**Theorem** `passPlans_safe` (proved). `passFile_safe`'s conclusion for any
plans over their store and any set $`S`$ of units each a selected unit whose
group is safe: with a layout of $`S`$ and its outside contracts, every
$`u \in S`$ has $`\mathrm{approx}_n(u) \in ⟦I_u⟧_{m,W}`$ for $`m \le n`$.
A module's step is this at its `ok`.

**Theorem** `entry_met` (proved). Let `EntryRealized`$`(e)`$ be the module
side of an entry: its plans over their store, a set $`S_m`$ of safe
selected units containing $`e`$'s unit $`u`$, a layout of $`S_m`$ and its
outside contracts. If an importer's slot of type $`A`$ holds at depth $`i`$
the value $`\mathrm{approx}_i(u)`$ of $`u`$'s module (`HoldsModuleValue`)
and the stores agree on the signature (`SignatureAgrees`:
$`w \in ⟦I_u⟧^{G_m}_{j,W} \Rightarrow w \in ⟦A⟧^{G}_{j,W}`$), then
$`\forall i.\; \forall j \le i.\; \forall W.\; v_i \in ⟦A⟧_{j,W}`$.
`established_met` (proved) lifts it to every slot of kind `established`
(`EstablishedSlots`).

**Theorem** `entryRealized_of_step` (proved under H1–H3). A step of mode
8's interface computation (`fragmentPlansCore` over the module's document,
mode 8's prepare `mode8Prepare` and check `mode8Check`, its accepted set
$`\mathit{ok}`$) and a layout of the module at units of $`\mathit{ok}`$
(`StepLayout`: a set $`S_m`$ of units whose wire identities are in
$`\mathit{ok}`$, holding the entry's unit, a `ModuleLayout` of $`S_m`$ and
its `OutsideContracts`) give `EntryRealized`$`(e)`$: the safety of $`S_m`$
is `step_units_safe`, the wire identity being injective
(`moduleUnitId_inj`). `realized_of_established` (proved) gives a
realization of every entry `EstablishedStep` states, under `StepLayouts`
(H5a at the module, for every step publishing $`e`$, a layout whose
realization satisfies a predicate $`\mathit{Chosen}`$, the realization the
importers' slots read).

**Theorem** `established_of_provenance` (proved under
`InterfaceProvenance` and `EstablishProvenance`). Every entry of the
interface file an importer reads is published by a step of mode 8's
interface computation: `establishModules` returned it and it was not among
the incoming entries.

**Theorem** `entries_realized` (proved under H1–H3). Over an order of
modules in which each reads only entries published before it
(`ReadsEarlier`), where each module's entries are published by steps of
mode 8's interface computation and laid out (`StepLayouts`) once the
entries it reads are realized, every published entry has a realization
$`\mathit{Chosen}`$ names. By `linkModules`, `Holds`$`(e)`$ being
$`\exists\, \mathit{src}.\; \mathit{Chosen}(e, \mathit{src})`$.

**Theorem** `crossModule_safe` (proved under H1–H3, the importer's layout,
the modules' `StepLayouts`, the publication order, and the per-kind
contracts of the other outside slots). For plans over their store and a set
$`S`$ of units each a selected unit whose group is safe, whose established
slots read entries published along the order and hold, at each depth, the
value of every chosen realization at a type the stores agree on
(`ChosenSlots`), every $`u \in S`$ meets its interface:

```math
\forall n.\; \forall m \le n.\; \forall W.\; \mathrm{approx}_n(u) \in ⟦I_u⟧_{m,W}
\qquad\text{and}\qquad
\forall n\, W.\; \text{the values } \mathrm{env} \text{ captures for } u \models_{n,W} C_u
```

`passUnitCli_safe` gives each importer unit's safety from its verdict line;
`crossModule_safe` adds its value's interface, the imports discharged
through their modules' own checks.

### Signature agreement across two stores

`SignatureAgrees` relates two frozen equation stores, the module's and the
importer's, each with its own labels (`Lab f`, trees over its own head
numbering). Their meanings are related by a store map.

**Store map** (`StoreMaps.StoreMap`). A label map $`\varphi : \iota \to \kappa`$
from graph $`G`$ to graph $`H`$ and a region $`D`$ of $`G`$'s labels, with
$`\varphi`$ injective on $`D`$, $`D`$ closed under what each of its rows reads
(`PositiveRules.reads`), its meet parts, its schemes' binders and bound
binders, and holding the built-ins' types, such that for every $`l \in D`$:

- $`H.\mathrm{kind}(\varphi\,l) = G.\mathrm{kind}(l)`$ (parameter kinds, so
  value, pack and packed binders);
- the clauses are related both ways (`RowsRel`): each clause $`c`$ of $`l`$
  has a clause $`c'`$ of $`\varphi\,l`$, and each $`c'`$ a $`c`$, with
  $`c' = c.\mathrm{map}\,\sigma`$ for an operand map $`\sigma`$ such that
  $`\sigma S`$ and $`\varphi S`$ have the same members for each operand $`S`$
  of $`c`$ and for $`[]`$ (`ClauseRel`, `Equiv`): the same constructor, the
  same keys, literals, flags and effects, every operand a union of the same
  labels renamed, in any order;
- a scheme $`s`$ of $`l`$ is $`\varphi\,l`$'s with binders renamed by
  $`\varphi`$ and every operand (signatures, bounds' types, variadic
  signatures) by such a $`\sigma`$, qualification and construct flag kept
  (`mapSchemeWith`); no scheme maps to no scheme;
- a meet $`(p, cs)`$ of $`l`$ is $`(\varphi\,p, cs')`$ with $`cs`$ and $`cs'`$
  related, and the further meet parameters are the renamed ones, as sets;
- the built-ins are related (same keys, prototype and `unknown` types of the
  renamed labels); the domain admits the image scheme's substitutions as the
  scheme's (`ordinary_allowed`: two ordinary domains do); the image's
  assignment gives $`\varphi\,l`$ the family $`G`$'s gives $`l`$.

**Theorem** `StoreMap.meaning_eq` (proved). For every type $`A`$ of labels
of $`D`$, at every budget $`n`$ and world $`W`$,

```math
⟦A.\mathrm{map}\,\varphi⟧^{H}_{n,W} = ⟦A⟧^{G}_{n,W}
```

and `meaning_eq_of_mem`: the same for any union with the members of
$`A.\mathrm{map}\,\varphi`$. Both directions hold. The proof is by induction
on the approximation index of the guarded fixed point over pairs of
assignments related by $`\varphi`$ (`Related`:
$`\theta(\varphi\,p) = \eta(p)`$ on $`D`$), each step reading related rows
(`layer_eq`); a scheme's reassignment keeps the pair related
(`related_assign`, from injectivity). The constructors covered are every
clause constructor (`Clause.map` is the whole syntax), parameter rows of
every kind, schemes with bounds, variadic signatures, qualification and
construct signatures, meets, argument packs, and the built-ins' array
invariant and exception family. Arrows keep their effect under
`Contract.map`, so footprints, throw footprints, fresh results,
preconditions and postconditions are carried as they are: the map relates
types, and an arrow's effect is part of its clause.

**Theorem** `signatureAgrees_of_storeMap` (proved). A store map from the
entry's module graph to the importer's graph whose region holds the
interface $`I_u`$, and a slot type with the members of $`\varphi(I_u)`$,
give `SignatureAgrees`.

### Where signature agreement is decided

**What the importer reads.** An interface entry
$`((\ell, n), (\Phi, t, \Phi_r), u)`$ carries the established footprint,
throw flag, result footprint and unit, and no type (`encodeInterfaces`,
`decodeInterfaces`). The importer's slot of the import is
`importedArrow` over its own declaration type $`U`$ of the name (the
`imported` entry of its equation front): $`U`$'s one arrow, each parameter
and the result spelled as claims of the importer's labels (`graphClaim`),
the entry's footprint, lowered by `moduleArrow` into the importer's store.
So the slot's type $`A`$ is a type of the importer's frozen store
$`G = \mathrm{graphOf}(f)`$. The module's interface $`I_u`$ is
`moduleArrow` over its unit's own signature (`ordinarySlots`), a type of
the module's frozen store $`G_m = \mathrm{graphOf}(f_m)`$. The two
lowerings share their input text only: `eligibleRead` requires the
importer's and the module's readings of the declaration equal, recursively
over the declarations they reach (`sameReading`), and the same
precondition and postcondition.

**A two-store question.** `SignatureAgrees` is the inclusion
$`⟦I_u⟧^{G_m}_{j,W} \subseteq ⟦A⟧^{G}_{j,W}`$, and the module's theorem
(`interface_entry_meets`) is about $`G_m`$'s labels, so the question
relates two stores whatever the importer re-interns: a type decoded into
the importer's store is a type of $`G`$, and relating it to $`I_u`$ is again
a statement across $`G_m`$ and $`G`$. Two routes decide it without a
theorem about the lowering:

- **One invocation** (`fragmentPlansWithModules`, where `establishModules`
  plans the module in the importer's process). The check
  $`\mathrm{matchStores}(G_m, G, \mathit{canon}, \mathit{fuel}, I_u, A)`$
  accepting gives `StoreMapAgrees` (`storeMapAgrees_of_check`, proved).
- **An interface file.** The entry carries a graph $`G_s`$ and a type
  $`I_s`$ of it: the module's rows on the region its own check found. The
  module's check $`\mathrm{matchStores}(G_m, G_s, \ldots, I_u, I_s)`$ and
  the importer's $`\mathrm{matchStores}(G_s, G, \ldots, I_s, A)`$ accepting
  give `SignatureAgrees` (`signatureAgrees_of_checks`, proved): the meanings
  are equal along both maps. The module's check runs on the decoded
  rows, so no theorem about the encoder or the decoder is needed.

**The store-map check** (`StoreMapsCheck.matchStores`). A worklist from
the roots, structural on its fuel, proposes a label map: clauses paired by
their skeleton (each operand replaced by its size, so constructor, keys,
literals, flags and effects), union members by the shape of their rows.
The proposal is not relied on. The check then requires, of every label
$`i`$ of the map's domain, with operands mapped by
$`\sigma S = \mathit{canon}(S.\mathrm{map}\,\varphi)`$: $`\varphi\,i`$'s
kind; a scheme mapped to $`\varphi\,i`$'s with no resolution and its
binders mapped; a meet mapped to $`\varphi\,i`$'s; the further meet
parameters renamed as sets; a clause row's clauses and $`\varphi\,i`$'s
related both ways; its reads and meet parts mapped; an inverse map
returning $`i`$; the built-ins related and mapped; the root mapped and the
image root of the root's renamed members.

**Theorem** `matchStores_sound` (proved). For $`\mathit{canon}`$ keeping
members and graphs whose environments agree (both empty, as every frozen
store's, `graphOf_env`),

```math
\mathrm{matchStores}(G, H, \mathit{canon}, \mathit{fuel}, I, A) = \mathrm{some}\ \mathit{mp}
\;\Longrightarrow\; \exists\, m : \mathrm{StoreMap}(G, H).\;
  I \subseteq m.D \;\wedge\; \mathrm{members}(A) = \mathrm{members}(I.\mathrm{map}\, m.\varphi)
```

Its cost, for $`s`$ the reachable rows' total size and $`k`$ the largest
number of clauses of a row, is $`O(s \cdot k)`$ hash-map operations and
clause comparisons. It is incomplete for unions with two members of one row
shape to depth two (the proposal pairs members by their row's shape and the
shapes of their operands' members, as sets), or rows with two clauses of
one skeleton, which the proposal pairs in the wrong order; for a qualified
scheme (nonempty resolution, whose domains it does not relate); and for an
image operand outside $`\mathit{canon}`$'s form.

**Built-ins in one graph only.** Every arrow, method and constructor
signature reads the graph's exception family (`excOf`: `builtinExc` at the
built-in values, the $`\Xi`$ of `semWithArgs`), the values a call may throw,
and that family is the built-ins' array invariant where the graph states
them and only the store being a list where it states none
(`builtinInvariant`). So for $`G_m`$ without built-ins and $`G`$ with them,
and any arrow type $`F`$ of a region of both,
$`⟦F⟧^{G_m}_{n,W} \not\subseteq ⟦F⟧^{G}_{n,W}`$ in general: a closure that throws
an array whose store holds a value outside $`G`$'s `unknown` type, or whose
prototype is not $`G`$'s, meets the first and not the second.
[StoreMapsBuiltins](../../lean/Verification/Types/StoreMapsBuiltins.lean)
states the store maps' side, all proved:

- `StoreMap.excOf_eq`: along a store map $`m : G \to H`$,
  $`\mathrm{excOf}(H) = \mathrm{excOf}(G)`$;
- `StoreMap.builtins_isSome`: a store map relates a graph stating built-ins
  only to one stating them, and `matchStores_none_of_builtins`: the check
  returns none where exactly one of the two graphs states them;
- `matchStores_sound_builtins`: where $`G`$ states the built-ins $`r`$ and
  the check accepts, $`H`$ states built-ins $`r'`$ with
  $`r'.\mathrm{keys} = r.\mathrm{keys}`$, its prototype and `unknown`
  types the renamed ones, those types in the map's region, and
  $`\mathrm{excOf}(H) = \mathrm{excOf}(G)`$, besides `matchStores_sound`'s
  conclusion.

The three reads the front lane lost (`certified-mts-value-import`
`doubled@259`, `default-import-value-import` `twice@275` and `scaled@346`)
and pretext's `missing` (from `checked.ts`) are arrows from a module whose
store states no built-ins to an importer whose store does: the check
refuses them (`matchStores_none_of_builtins`), and no sound extension of it
admits them, since the module's theorem gives its functions' throws in the
weaker family only. What admits them is the module's theorem at the
importer's family: the module's frozen store states the built-ins (the
standard ones, as the importer's: the same keys, prototype and `unknown`
types) whenever its interface is published, so its units are checked
against the same exception family; then `matchStores_sound_builtins`
applies with the check unchanged. A module with no arrays throws no array,
so its checks hold at the stronger family (not measured).

**A module's own reads.** `crossModule_safe` needs each module's own
established slots met (`StepLayouts`' outside contracts hold of the
module's layout, its established kind among them), so a module's reads of
entries published before it need the same check as an importer's: at each
step of the interface computation, for each capture of the module's plans
read at an entry $`e`$ published earlier,
$`\mathrm{matchStores}(G_s(e), G_m, \mathit{canon}, \mathit{fuel}, I_s(e), A)`$
accepts, with $`G_s(e)`$ and $`I_s(e)`$ the rows table and interface type
of $`e`$ in the file the step reads, $`G_m`$ the module's frozen store and
$`A`$ the capture's type in it; a refused check refuses the units reading
the slot at `signature rows differ`. Then the module's established slots
are `signatureAgrees_of_checks` at that check and its own publication
check.

**The request to the wrapper lane** (the smallest change making signature
agreement checked):

1. `encodeInterfaces` writes, per established entry, `interface` (the
   trees of $`I_u`$'s labels) and `rows` (for each label of the map the
   module's check found, its row as trees, with the built-ins), and
   `decodeInterfaces` reads them as $`G_s = \mathrm{NormalGraph.ofRowMap}`$
   over a map from trees to rows and $`I_s`$.
2. `interfaceFile` publishes an entry only where
   $`\mathrm{matchStores}(G_m, G_s, \ldots, I_u, I_s)`$ accepts, with
   $`G_m`$ the step's prepared plans' graph and $`I_u`$ the unit's slot
   there; `EstablishedStep` gains that clause (`EstablishProvenance`).
3. The importer, after `fragmentPlansFromInterfaces`, runs
   $`\mathrm{matchStores}(G_s, \mathrm{graphOf}(f), \ldots, I_s, A)`$ for
   each import slot read at an entry, $`A`$ the slot's type in its
   frozen store; a refused check refuses the units reading the slot, with
   the located reason `signature rows differ`. `ModuleLayout` (H5a) states
   that the slot's capture type is that $`A`$.

With these, `ChosenSlots`' agreement is `signatureAgrees_of_checks` at the
two accepted checks, and `StoreMapAgrees` is no hypothesis.

## 8. Expression obligations and async members

### Expression obligations

A member's expression claims are sequents $`\Gamma \vdash t : A`$ at source
positions (`ExpressionClaims.Required`), the types claimed for the unit's
expressions; `passGroup` checks them against evidence, the member's code
table and the read summaries its last run left (`checkAllResult`).

**Theorem** `obligations_sound` (proved). Where the check accepts, the table
is sound and the summaries are sound, every obligation holds semantically:

```math
\forall (\Gamma \vdash t : A) \in \mathit{rs}.\; \forall n\, W\, h\, \rho.\;
  \rho \models_{n,W} \Gamma \wedge \mathrm{WorldAdm}(W) \wedge \mathrm{HeapOk}_n(W, h)
  \;\Longrightarrow\; \mathrm{Safe}_{n,W}(A;\, h,\, t\rho)
```

by `checkTreeUsing_sound` and the typing's soundness. A member's table is
sound by `codesAccepted_sound` and its last run's summaries by
`summaries_of_checked`; the remaining step is a clause of `MemberAccepted`
recording the obligations' check, which `MemberAccepted` does not state;
`passMember_sound`'s proof reads the check's acceptance from the outcome
(`hobl`), where such a clause would take it. The
old headline states no such clause: its `RequestsSafe` has no conjunct for
obligations. The theorem says what a claimed expression type means for the
term the obligation states; that the term is the source expression at that
position is the lowering's boundary.

### Async members

**Theorem** `member_async` (proved). An async member `passGroup` accepts
claims the footprint letting every location change:
$`\mathrm{MemberAccepted}(f, j) \wedge r.\mathrm{async} \Rightarrow r.\mathrm{footprint} = \top`$,
from the declared effect's condition. It is the member half of
`checkRequests_async`, which the old checker states outside `RequestsSafe`.

**Theorem** `codes_async` (proved). Each code request of an accepted member
meets the same condition,
$`q.\mathrm{async} \Rightarrow q.\mathrm{footprint} = \top`$, from the
condition `passGroup` checks before each code's run (`CodeRunAccepted`):
the other half of `checkRequests_async`.

The async property stays outside `RequestSafe`: it constrains how a claim is
read against the source (an async body runs after its call returns its
promise), which is the lowering's boundary, not a property of the graph's
runs. Both headlines state it as a separate consequence.
