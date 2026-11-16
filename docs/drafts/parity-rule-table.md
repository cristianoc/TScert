# The note against the implementation, rule by rule

A map: for each rule of the note
[Tolerant frames](tolerant-frames-note/note.tex) in scope, the Lean
statement and the mechanism the pass's acceptance applies. Read by
gpt-6-astra from the sources at commit `81d7f232` on 2026-11-15, with no
build or suite run; "proved" names a proof declaration read in the source.
The goal is the [parity skill](../../.claude/skills/parity/SKILL.md#the-goal)'s:
each rule of the note is the rule acceptance applies. The work list is in
[WORK.md](../../WORK.md#status) and
[the note's rules at acceptance](rules-at-acceptance.md).

A mechanism is **separate** when acceptance applies its own decision,
proved sound by its own theorem, and that decision establishes no
derivation in the note's checker (`checkDerivation`, `checkScoped`). A
separate mechanism is sound by its theorem and does not meet the goal: each
row whose mechanism is separate, or absent, is work.

## The rules

| Rule | Lean statement | Mechanism acceptance applies |
|---|---|---|
| Entry | `CommandSummary.Sound` and `ExitSpec.facts` state a command's exit postconditions together with its transition `tr` | `HeapKnowledge.Entry`, `entry_sound` at a call (`PromiseCalls.callEntry`) and a push (`appendEntry`); separate: `PromiseCalls.withEnsures`, `Composer.fact` |
| Frame | `Derivation.frame`: elimination of the modality, with checked substitution and transport | separate: `effectKept`, `frameKeeps`, `IndexFact.keeps`; at a handler edge `edgeStoreOf` keeps no heap fact |
| Frame+ | `Derivation.framePlus`, with certified rigidity on an invariant domain | none: acceptance keeps no fact under the modality |
| Loop | `LoopEvidence.prefix_sound`, `frame_at_head`, `frame_at_exit`, `reliance_at_prefix`: the parts of the rule, with the note's agreement of valuations at a prefix | separate: `headExit` checks supplied head facts, closed by induction over the graph |
| Call | `call_exits_exact`, the schema's instantiation, substitution and transport of the mark: instantiation per exit, rest actuals included | Call itself, at the selected signature; the facts a caller derives from it go through the separate Entry and Frame mechanisms above |
| Alloc | `alloc_post`, with the typed allocation and separation lemmas, for the ordinary empty array | separate: `IndexWrites.regionAtoms`, `Checker.emptyArrays` |
| Seq-Eff | `Post.compose_rebases`, `ThenEvidence.sound`, `CommandSummary.seq_sound`, `CommandSummary.handle_sound`: composition relative to the entry, on both exits | separate: `footprintCheck` and `StepGrades.admits`, over closed bounds along the walk |
| Fresh-Eff | `rebaseAll_fresh_eff`, `Post.fresh_eff`, `ThenEvidence.into_fresh`: rebasing erases the fresh spine's entry alone | separate: the fresh positions' projection in `StepCertificate.grades` and `Footprint.boundBelow`, and the regional checks |
| Conj | `SafePostExcV.cross_independent`, `PromiseWith.conj`, `Exits.exitPost_meet`, with the world-independence condition | Conj itself: `Effect.meetCovers` checks the rule's conditions |
| Grow | `Derivation.grow` | separate: support, and the preservation deciders of writes and calls |
| Dense | `Derivation.dense`, for a prefix bounded by a variable | separate: the density and type checks and the callback contracts |
| Sep | `RawDerivation.sep`, through `tolerantFrame`, for linear length atoms | separate: `frameKeeps` and the separation queries |
| Every | `RawDerivation.everyFrame`, through support and respect, for ordinary arrays and the represented scalar predicates | separate: `everyKept`, `writeAtoms`, and the append and write rules |
| Init | `RawDerivation.init`, through support and respect, for linear atoms at a path | separate: the kept terms and the initialization checks |
| Rigid | `Derivation.rigidSubst`: capture-avoiding substitution under the fresh-variable and effect condition | separate: recognition of stable fields and paths; no producer introduces rigidity into the checker from the typing certificates |
| View | `RawDerivation.view`, through invariant support, for facts over variables and view lengths | separate: the preservation of view lengths |
| Write-In | `Derivation.writeIn` with `Bridges.lengthsKept_of_run`: the exact length equation | separate: `keepsLengths`, `boundedLength_sound` |
| Write-End | `Derivation.writeEnd`: the growth of the length | separate: `atLengthAtoms` and the write rules |
| Push | `Derivation.pushPost`: the growth of the length, from `ReceiverAppends` | separate: `statesAppend`, the append rules and the Entry mechanisms |
| Add, Sub, Scale | `Derivation.integerOperation`: safe operands, multiplication by a constant, a safe result | separate: `linearAtoms`, `smallOperand`; the arithmetic bridges relate the two representations |
| Shr, Mask | `Derivation.shiftRight`, `Derivation.mask`: the displayed ranges and inequalities, known constants included | separate: `bitAtoms` |
| String length successor | `Derivation.lengthSuccessor`: a safe result or 2⁵³ | separate: `stringLengthPlusOne`, `pastSafeAtoms` |
| Str-Length, Concat | `stringLengthRead`, `stringConcat`: the equations; bridges relate them to the producers' facts | separate: those producers |
| Str-Read | `Derivation.stringRead`: a result of length one, under the index bounds; no producer of the pass emits it | none |
| View-Length, View-Read, View-Write | the tagged view model and the native contracts, which the selected call's check reads | separate: `exactWriteOf` reads the exact write of an integer whose format is unchanged; no derivation consumes the exact postconditions |
| Transfer (§7) | `checkScoped_sound`: the entailment of the checked sequent; `transfer`, for closed exit effects | separate: `exitStep`, `edgeStoreOf`, `edgeTransfer`, `assertionExit`, `headExit` and the merge checks |

## Rules applied through a separate mechanism

Acceptance applies Call and Conj themselves, each with the consequences it
recognizes. It applies every other rule in scope through a separate
mechanism: Entry, Frame, Frame+, Loop, Alloc, Seq-Eff, Fresh-Eff, the seven
atom axioms (Grow, Dense, Sep, Every, Init, Rigid, View), Transfer (§7),
the arithmetic rules, and the exact updates of a write.

## Statements weaker than the note

- **Write-End.** The note concludes `x[i] ≐ v` and the extension of
  density; `Derivation.writeEnd` concludes the growth of the length.
- **Push.** The note concludes `y = |x|`; `Derivation.pushPost` concludes
  the growth of the length.
- **Str-Read.** The note reads the UTF-16 code unit at `i`;
  `Derivation.stringRead` concludes a result of length one.

The atom axioms hold for narrower atoms than the note's "an atom": Sep and
Init for linear atoms, Every for the represented scalar predicates. A
structural derivation schema over every relevant atom form is what extends
them.

## Fixtures related to loops

Each fixture below needs more than rule Loop with its frame.

| Fixture | What its source requires |
|---|---|
| `bounds-pattern-grow-upper-refused` | `paths`: separation of an allocation through stable paths; `straight`: transfer without a loop |
| `bounds-pattern-fresh-field-write-refused` | preservation by support across a field write, usable as a loop frame, of a quantified fact over a typed array that also reads another array's length; `everyFrame` gives part of it |
| `written-ensures-push-refused` | an inferred invariant of a counter and a length, the exact Push consequence, arithmetic, and reasoning at the loop's exit |
| `bounds-pattern-postfix-prefix-refused` | extension of a changing quantified prefix across a view write, a fact of the invariant |
| `blocker-for-of-fresh-record` | the separation of a replacement record, which the note places outside its established derivations |
