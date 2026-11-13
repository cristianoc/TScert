# Two-state postconditions

A postcondition such as `lists.widths.length === old(lists.widths.length) + n`
relates the state a function starts in and the state it returns in. This
draft states the definition, how the Lean represents it, and which
statements it changes.

## The existing mechanism this extends

- **Postconditions** ([postconditions](../ARITHMETIC.md#postconditions)): a
  signature's `Effect.ensures` lists index facts at the return's positions
  (`0` the result, $`i+1`$ the call's position $`i`$), read in the heap a
  normal return leaves (`Effect.post`). A unit states them at its entry
  frame (`PassUnit.EnsuresClause`) and the pass proves them at each return
  by entailment from the facts there (`GraphCode.returnEntails`).
- **The pass's named state**
  ([the pass's named state](../SINGLE-PASS-PROOF.md#the-passs-named-state)):
  the facts the walk keeps, over names, with the start names pinned to the
  invocation's entry values, kept across steps by the frame checks
  (`Term.keptBy`, `IndexFact.keptBy`) and across a throw where they read no
  heap (`Atom.heapFree`).
- **The entry check** (`SinglePass.entryRefusal`, `ControlFlow.entryKnows`):
  the start's given facts, written and proposed, entailed by the request's
  entry facts.

Each is extended, none replaced: the entry state is a parameter of the
satisfaction all three read, and `old` is one more form of term.

## The definition

The note "Tolerant frames", section 6, "Triples": the posts of a triple
are two-state; in them $`\mathrm{old}(e)`$ denotes the value of $`e`$ in the
environment and heap the command started in. That state is a whole state,
fixed for the run. An assertion that reads only the entry state is
invariant under every step: no step changes a past state (its support is
empty, section 5). Rule Call instantiates a callee's two-state post with
the caller's state at the call as the callee's entry.

## The representation

**The entry state** $`\varepsilon=\langle\varepsilon.\mathrm{env},\varepsilon.\mathrm{heap}\rangle`$
(`HeapKnowledge.EntryState`) is a parameter of every satisfaction relation:
$`\varepsilon;\rho,h\models F`$ (`IndexFact.HoldsAt ε F ρ h`), knowledge
(`HeapKnowledge.Holds k ε ρ h`), the named facts (`AtomHolds`, `Named`,
`StoreOk`), the pass's state (`StateHolds … start ε`, its start names
holding $`\varepsilon.\mathrm{env}\,q`$) and the walk's node and edge
assertions (`passPre`, `passPreT`, `passPreA`, `passPreU`, …). One
$`\varepsilon`$ serves every node of a run. A step's, a node's or a check's
obligation (`Checker.sound`, `ExpressionOk`, `NodeWithin`, `StepOk`, the
entailments between knowledges) holds for every $`\varepsilon`$.

**Terms.** A term is $`t=\langle k,s,p\rangle`$ (kind, slot, path) or its
entry form $`\mathrm{old}(t)`$ (`Term.atEntry`):

```math
[\![t]\!]_{\varepsilon,\rho,h}=\mathrm{kind}_k\,h\,(\mathrm{read}_h\,(\rho\,s)\,p)
\qquad
[\![\mathrm{old}(t)]\!]_{\varepsilon,\rho,h}=[\![t]\!]_{\varepsilon,\varepsilon.\mathrm{env},\varepsilon.\mathrm{heap}}
```

(`termValue`, `termAt`). The slot of $`\mathrm{old}(t)`$ is a position of
the entry environment; renamings of the current slots leave it as it is
(`Term.mapM`), and it is no current slot of the fact (`Term.slots`,
`IndexFact.entrySlots`). Every fact form whose terms are terms (linear
facts, a quantified fact's bound and free body terms) admits entry terms.

**Invariance** (proved, `termValue_entry_invariant`):
$`[\![\mathrm{old}(t)]\!]_{\varepsilon,\rho,h}=[\![\mathrm{old}(t)]\!]_{\varepsilon,\rho',h'}`$
for all $`\rho,h,\rho',h'`$. So an entry term is kept by every change
(`Term.keptBy`, `termValue_kept`, `termValue_grown`, `termValue_viewFramed`,
`termValue_storeGrown`) and reads no current heap (`Term.envOnly`,
`termValue_envOnly`): a fact all of whose heap reads are under $`\mathrm{old}`$
crosses every step and every handler edge (`IndexFact.holdsAt_envOnly`).

**The start.** At the start the current state is the entry state:
$`\varepsilon=\langle\rho,h\rangle`$, and then
$`\varepsilon;\rho,h\models F \iff \varepsilon;\rho,h\models F[\mathrm{old}(t):=t]`$
(proved, `IndexFact.holdsAt_toNow`, `HeapKnowledge.holds_toNow`). The pass
proposes, for each entry term $`\mathrm{old}(t)`$ the postcondition names,
the facts $`t-\mathrm{old}(t)\le 0`$ and $`\mathrm{old}(t)-t\le 0`$ among the
start's (`SinglePass.startOldFacts`, `withStartOld`); the entry check reads
the start's facts at the entry state itself (`entryKnows` checks
`Knowledge.toNow`), where they are $`t-t\le 0`$, entailed where the entry
facts state $`t`$ defined. A proposal: nothing about it is trusted.

**A return.** `EnsuresAt ens ε h' (push v ρ0)`: each fact at the result
pushed onto the inputs' entry values, its entry terms at $`\varepsilon`$. The
return check entails the postcondition from the facts at the return
(`returnEntails`, proved `returnEntails_sound`); the renaming to the
return's slots leaves its entry terms as they are, and the walk's facts read
the same $`\varepsilon`$. `EnsuresClause` states it with
$`\varepsilon=\langle\mathrm{envOf}\,L\,d,h\rangle`$, the run's own entry.

**A call** (rule Call). A callee's post is read with the caller's state at
the call as the callee's entry: $`\langle\mathrm{callEnv}\,r\,\mathit{args},h_{\mathrm{before}}\rangle`$
(`Effect.post`); its precondition is one-state (`Effect.below` admits no
entry term in it), read at $`\langle\mathrm{callEnv}\,r\,\mathit{args},h\rangle`$.
The caller adds the callee's post facts naming no entry term to its facts
(`PromiseCalls.ensuresAtoms`); a fact naming one is not added. Stating it
with the step's own before and after is open work (below).

**Module rows** carry the postcondition as stated: `Effect.belowRow`
bounds its entry slots by the positions the code binds, and
`ensures_take`, `ensures_frame` read it at the call's and at the frame's
entry, which agree there (`callEnv_take`, `callEnv_frame`). Entry
allocation before a call (`Effect.post_prefix`) admits a post naming no
entry term.

**The wire.** A linear term is `{"kind", "slot", "path"}`, an entry term also
`"atEntry": true` (`EffectJson`, `LinearTerm` in
`tools/declaration-types.mts`); the front end writes none.

## What changed in which statements

- Satisfaction of every fact, knowledge and walk assertion takes
  $`\varepsilon`$; `GraphGuarantee`, `EntryHolds`, `EnsuresClause`,
  `AssertionsClause` and `CodeAssertionsClause` instantiate it with the
  run's entry. The statements of `run_sound_single_pass`,
  `mode8Accepted_sound` and `crossModule_safe` are the same; where no fact
  names an entry term their meaning is the one-state meaning.
- `Effect.Requires` reads the precondition at the callee's entry
  $`\langle\mathrm{callEnv}\,r\,\mathit{args},h\rangle`$, `Effect.post` the
  post's facts at $`\langle\mathrm{callEnv}\,r\,\mathit{args},\mathit{before}\rangle`$.
- `ControlFlow.entryKnows_sound` concludes the start's knowledge at
  $`\langle\rho,h\rangle`$.

## Open work

- **Rule Call in the caller's facts.** A callee's post fact naming
  $`\mathrm{old}(t)`$ relates the caller's terms before and after the call.
  It is dropped at the call. Stating it needs the step's before-terms in the
  after-state's facts: an exact change substituted into the before-facts,
  as `linearAppendKept` does for a push.
- **The front end** parses `old(…)` in `@ensures` and writes
  `"atEntry": true`; no pipeline case exercises an entry term.
