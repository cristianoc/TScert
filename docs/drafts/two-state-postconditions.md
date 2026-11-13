# Two-state postconditions

A postcondition such as `lists.widths.length === old(lists.widths.length) + n`
relates the state a function starts in and the state it returns in. This
draft states the definition, how the Lean represents it, the rules that
read it, and which statements it changes.

## The existing mechanism this extends

- **Postconditions** ([postconditions](../ARITHMETIC.md#postconditions)): a
  signature's `Effect.ensures` lists index facts at the return's positions
  (`0` the result, $`i+1`$ the call's position $`i`$), read in the heap a
  normal return leaves (`Effect.post`). A unit states them at its entry
  frame (`PassUnit.EnsuresClause`) and the pass proves them at each return
  by entailment from the facts there (`GraphCode.returnEntails`).
- **The pass's named state**
  ([the pass's named state](../SINGLE-PASS-PROOF.md#the-passs-named-state)):
  the facts the walk keeps, over names, kept across steps by the frame
  checks (`Term.keptBy`, `IndexFact.keptBy`).
- **The entry check** (`SinglePass.entryRefusal`, `ControlFlow.entryKnows`):
  the start's given facts, written and proposed, entailed by the request's
  entry facts.
- **Exact changes across a step**: the push rule and the write at the
  length, each a relation between a length before and after a step.

Each is extended, none replaced: the entry state is a parameter of the
satisfaction all of them read, `old` is one more form of term, and the
exact changes are instances of one composition.

## The definition

The note "Tolerant frames", section 6, "Triples": the posts of a triple
are two-state; in them $`\mathrm{old}(e)`$ denotes the value of $`e`$ in the
environment and heap the command started in. That state is a whole state,
fixed for the run. An assertion that reads only the entry state is
invariant under every step (its support is empty, section 5). Rule Call
instantiates a callee's two-state post with the caller's state just before
the call as the callee's entry. A precondition is one-state.

## The representation

**The entry state** $`\varepsilon=\langle\varepsilon.\mathrm{env},\varepsilon.\mathrm{heap}\rangle`$
(`HeapKnowledge.EntryState`) is a parameter of every satisfaction relation:
$`\varepsilon;\rho,h\models F`$ (`IndexFact.HoldsAt ε F ρ h`), knowledge
(`HeapKnowledge.Holds k ε ρ h`), the named facts, the pass's state
(`StateHolds … start ε`) and the walk's node and edge assertions. One
$`\varepsilon`$ serves every node of a run; a step's or a check's obligation
holds for every $`\varepsilon`$.

**Terms.** A term is $`t=\langle k,s,p\rangle`$ (kind, slot, path) or its
entry form $`\mathrm{old}(t)`$ (`Term.atEntry`):

```math
[\![t]\!]_{\varepsilon,\rho,h}=\mathrm{kind}_k\,h\,(\mathrm{read}_h\,(\rho\,s)\,p)
\qquad
[\![\mathrm{old}(t)]\!]_{\varepsilon,\rho,h}=[\![t]\!]_{\varepsilon,\varepsilon.\mathrm{env},\varepsilon.\mathrm{heap}}
```

(`termValue`, `termAt`). Every fact form whose terms are terms (linear
facts, a quantified fact's bound and free body terms) admits entry terms.
Invariance (proved, `termValue_entry_invariant`):
$`[\![\mathrm{old}(t)]\!]_{\varepsilon,\rho,h}=[\![\mathrm{old}(t)]\!]_{\varepsilon,\rho',h'}`$.

**Two renamings.** Within one invocation the entry is fixed: renaming the
current slots (reassignment, the pass's names, a push past the result)
leaves every entry term as it is (`Term.mapM`, `IndexFact.mapM`). A change
of frame translates both environments, each by its own map:

```math
\mathrm{reframe}\,f\,g\,F = F[\,s\mapsto f\,s\ \text{(current)},\ \ s\mapsto g\,s\ \text{(entry)}\,]
```

(`IndexFact.reframe`, `mapEntry`; proved `holdsAt_reframe`: where $`f`$ and
$`g`$ carry each slot's value to its image and the entry heaps agree, the
translated fact holds exactly where the source does). A function declared
without `this` reads its row's postcondition past the receiver in both
states (`IndexFact.pastReceiver`: current $`0\mapsto 0`$, $`1\mapsto\bot`$,
$`i+1\mapsto i`$; entry $`0\mapsto\bot`$, $`p+1\mapsto p`$; proved
`holdsAt_pastReceiver`), and a row naming the receiver in either state has
no receiverless request (`not_receiverless_of_oldReceiver`).

**The start.** At the start the current state is the entry state, and
$`\varepsilon=\langle\rho,h\rangle\Rightarrow(\varepsilon;\rho,h\models F\iff\varepsilon;\rho,h\models F[\mathrm{old}(t):=t])`$
(proved, `IndexFact.holdsAt_toNow`, every fact form); for a term,
$`\varepsilon=\langle\rho,h\rangle\wedge[\![t]\!]\ \text{defined}\Rightarrow[\![t]\!]=[\![\mathrm{old}(t)]\!]`$
(proved, `IndexFact.identity_holds`). The post needs that identity where it
reads the term. For each occurrence of an entry term in a post fact, by
structural recursion over every form of fact (`SinglePass.startIdentities`),
the statements of the identity are, strongest first, the identity itself
and the identity under each guard the occurrence is read beneath, a guard on
an input read at the start at that input:

```math
\mathrm{ids}(A\lor B)=\mathrm{ids}(A)\cup\mathrm{ids}(B)\qquad
\mathrm{ids}(g_{x}\lor B)=\{\,c\cdot(g_{x}\lor I)\mid c\cdot I\in\mathrm{ids}(B)\,\}
```

The start knows, of each occurrence, the first statement the entry facts
entail (`SinglePass.startOldFacts`). Where none is entailed, an occurrence
read in every state the post holds in (one beneath no disjunction's arm and
no guard on the result) is proposed in its weakest statement, which the
entry check refuses; any other gives the start no identity for it, and the
post is established at the return from the facts there.

**A return.** `EnsuresAt ens ε h' (push v ρ0)`: each fact at the result
pushed onto the inputs' entry values, its entry terms at $`\varepsilon`$. The
return check entails the postcondition from the facts at the return
(`returnEntails`, proved `returnEntails_sound`).

**A precondition** is read at the callee's entry, where $`\mathrm{old}(t)`$
is $`t`$: every check of it reads $`F[\mathrm{old}(t):=t]`$
(`Effect.below`, `preconditionHolds`, the unit's entry facts; proved
`Effect.pre_toNow`).

**A call** (rule Call). The callee's post is read at
$`\langle\mathrm{callEnv}\,r\,\mathit{args},h_{\mathrm{before}}\rangle`$
(`Effect.post`). Its facts naming no entry term join the caller's facts at
the return's slots (`ensuresAtoms`). Its other facts naming an entry term,
under a disjunction, a guard or a quantifier, compose form by form
(`HeapKnowledge.Composer.fact`, proved `Composer.fact_holds`). Its linear
facts naming an entry term form a relation between the caller's states before and after the call,
over variables $`\mathrm{before}(t)`$ and $`\mathrm{after}(t)`$
(`StepVar`, `callRelation`):

```math
\mathrm{old}(\langle k,p,q\rangle)\mapsto\mathrm{before}(\langle k,\sigma_p,q\rangle)\qquad
\langle k,j,q\rangle\mapsto\mathrm{after}(\langle k,\tau_j,q\rangle)
```

with $`\sigma_p`$ the caller's slot holding position $`p`$ (the receiver
where it is a slot, each actual) and $`\tau_j`$ the return's slot. A position the call passes nothing at holds
`undefined`, and every post fact reads it as `undefined`, by structural
recursion over every form (`Composer.fact`): a term reading it denotes no
integer, so a linear fact, a quantified fact's bound or body atom naming one
never holds and is $`0\le -1`$; an atom reading it as a number, an array or
an index never holds; a guard reading it with the empty path reads
`undefined`, and with a path reads nothing; a disjunction with an arm that
never holds is its other arm:

```math
\frac{\mathrm{old}(m)\le 0\ \lor\ r\le 0\qquad [\![m]\!]=\mathtt{undefined}}{r\le 0}
```

A region or store separation reading it, and an element fact whose value
is it, state nothing after the call. A before-variable is a logical name
inside one composition, no slot of any environment. The caller's facts
after the call are composed, all at the caller's own fixed
$`\varepsilon`$:

```math
\frac{B\ \text{held before}\qquad \mathrm{kept}(t)=t'\Rightarrow [\![t]\!]_{\mathrm{before}}=[\![t']\!]_{\mathrm{after}}\qquad R\ \text{holds of the step}}
{\mathrm{eliminate}_{\mathrm{before}(\cdot)}\big(B[t\mapsto\mathrm{after}(t')\ \text{kept},\ t\mapsto\mathrm{before}(t)\ \text{else}]\ \cup\ R\big)\ \text{held after}}\ \textsf{compose}
```

where elimination substitutes a before-variable the relation defines
($`b+\mathit{rest}\le k`$ and $`-b-\mathit{rest}\le -k`$ give
$`b=k-\mathit{rest}`$) and eliminates any other by Fourier–Motzkin, and each
resulting fact names after-terms alone, each defined after the step
(`HeapKnowledge.compose`, proved `compose_holds`; `ensuresComposed`,
proved `ensuresComposed_holds` from `callRelation_holds` and
`callKept_sound`). For $`|x|_{\mathrm{after}}=\mathrm{old}(|x|)+n`$:
$`b=|x|_{\mathrm{after}}-n`$, so a fact $`a-|x|\le 0`$ before the call
becomes $`a-|x|+n\le 0`$ after it.

A relation's fact holds where its before-terms denote integers; a relation
states the before-terms it defines (`StepRelation.definedBefore`). A fact
that holds defines its terms (`IndexFact.defines`, proved
`defines_holds`, every form: a linear fact's terms, an `int` atom's value, a
`length` atom's length and value, an element's index, a quantified fact's
bound), so a call's relation defines every term its facts name, before the
call and after it, and every fact of it composes, whether or not the
caller's facts before the call name its before-terms. Two equalities through
one entry value compose into an equality after the call:
$`|y|_{\mathrm{after}}=b+1,\ r=b\ \vdash\ |y|_{\mathrm{after}}=r+1`$.

The push rule ($`|x|_{\mathrm{after}}=|x|_{\mathrm{before}}+\mathit{count}`$)
and the write at the length ($`|x|_{\mathrm{after}}=|x|_{\mathrm{before}}+1`$)
are the same composition at the relation `IndexWrites.lengthGrowth`
(`linearAppendKept`, `writeCarried`).

**Entry allocation before a call** (`Effect.post_prefix`): a post read at
the heap after an administrative allocation is read at the call's entry,
the heap before it, where its entry terms denote the same at both
(`Effect.EntryAgrees`, read through `holdsAt_congr_entryTerms`); a code
row states no postcondition (`Effect.below`), so at its one use it holds
vacuously (`entryAgrees_of_nil`).

**Module rows** carry the postcondition as stated; `Effect.belowRow` bounds
its current positions by the result, the receiver and the code's
parameters and its entry positions by the receiver and the parameters.

**The wire.** A linear term is `{"kind", "slot", "path"}`, an entry term
also `"atEntry": true`, its slot a call position. The front end writes it
for `old(P)` and `old(P.length)` in `@ensures` (at the call's position of
the root parameter), in a loop invariant (at the input position of a
parameter of the function the loop is in) and in `@requires` (read as the
term itself).

## The statements whose meaning changed

The statements of `run_sound_single_pass`, `mode8Accepted_sound` and
`crossModule_safe` are the same; these definitions on their paths read the
entry state, and where no fact names an entry term their meaning is the
one-state meaning:

- `termValue`, `termValuation`, `IndexFact.HoldsAt`, `IndexHolds`,
  `HeapKnowledge.Holds`: satisfaction at $`\varepsilon`$.
- `StateHolds`, the walk's node and edge assertions (`passPre` and its
  variants), `EntryHolds`: at the run's $`\varepsilon`$, the start names at
  $`\varepsilon.\mathrm{env}`$.
- `GraphCode.EnsuresAt`, `GraphGuarantee.ensured` and `asserted`: the post
  at the run's entry.
- `PassUnit.EnsuresClause`, `AssertionsClause`, `CodeAssertionsClause`:
  $`\varepsilon=\langle\mathrm{envOf}\,L\,d,h\rangle`$.
- `CallEffects.Effect.Requires`: at
  $`\langle\mathrm{callEnv}\,r\,\mathit{args},h\rangle`$; `Effect.post`: its
  facts at $`\langle\mathrm{callEnv}\,r\,\mathit{args},\mathit{before}\rangle`$.
  So every callable's specification (`meaning` of an arrow) and the
  module's realization (`RowSpec`, `Realizes`) change with them.
- `PassUnit.UnitIsReceiverless.ensures`: the request's post is the row's
  read past the receiver in both states (`pastReceiver`).
- Executable checks: `entryKnows` (reads `toNow`), `startOldFacts`,
  `Effect.below` and `belowRow`, `preconditionHolds`, `ensuresAtoms`,
  `ensuresComposed`, `linearAppendKept`, `atLengthAtoms`.

## The named hypotheses

- `ReceiverDropSound` (of `crossModule_safe`):
  $`\forall\,r\,c,\ \mathrm{RequestSafe}\,r\wedge\mathrm{UnitIsReceiverless}\,r\,c\wedge\mathrm{rowConditions}\,c\Rightarrow\forall\eta,\ \mathrm{RowSpec}\,(\mathrm{reassign}\,G\,\eta)\,(\mathrm{dropReceiver}\,c)\,(\mathrm{receiverSeparation}\,r.\mathrm{entrySeparation})`$,
  with `UnitIsReceiverless.ensures` stating
  `row.ensures.mapM pastReceiver = some r.ensures`. By
  `holdsAt_pastReceiver`, the request's post at its entry
  $`\langle\mathrm{envOf}\,L\,d,h\rangle`$ and return holds exactly where the
  row's does at $`\langle\mathrm{envOf}\,(\mathit{recv}::L)\,d,h\rangle`$: the
  hypothesis's postcondition part is the faithful translation; the
  hypothesis itself (the prologue's two transitions) is unproved.
- `RunSound` (H1), `RunKeepsSummaries` (H2), `ModuleLayout`,
  `InterfaceProvenance`, `EstablishProvenance`: their statements are the
  same; the specifications they reference read the entry state as above.
- `StartWrittenImpliesStated` quantifies every $`\varepsilon`$; accepted
  setup discharges it.

## Limits

Required by the definition:

- A linear fact holds only where each of its terms denotes an integer, an
  entry term at the entry state included.
- A precondition is one-state; an entry term in it is its term.

Restrictions of the language, documented in
[ARITHMETIC.md](../ARITHMETIC.md#two-state-postconditions):

- `old` applies to the clause grammar's terms, `old(P)` and
  `old(P.length)`, with a parameter as root; not to arbitrary source
  expressions.
- An exceptional postcondition is the frame alone (`Effect.excPost`).
- Code rows (local functions) state no postcondition (`Effect.below`), and
  a row's postcondition names the result, the receiver and the code's
  parameters (`belowRow`).

## What the rules do not derive

[Two-state postconditions](../ARITHMETIC.md#two-state-postconditions) states
each consequence the composition loses with its smallest example (a bound
that is no term, bounds from the composition's facts alone, body atoms one
at a time, a value no slot holds, separations at an absent position) and
the start's identities the language cannot state.

**Implemented scope: definedness of an entry term is an obligation the
function's stated entry facts discharge.** It does not follow from the
input types in the present model, because a value meets its type only to
the depth of the budget: `recT`'s field contracts agree only below the
level and `HeapOk` constrains a location only below it, while `EntryHolds`
holds at every budget. The counter-model and the intended design (the
finite field-and-store shape a type demands in the unindexed structural
part of heap well-formedness) are stated
[there](../ARITHMETIC.md#two-state-postconditions).
