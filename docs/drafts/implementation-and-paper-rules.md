# Implementation rules, paper rules, and their correspondence

The basis of the work that relates the verifier to the paper
[Tolerant frames](tolerant-frames-note/note.tex). Its status is the row
"Implementation rules and paper rules" of [WORK.md](../../WORK.md#status).

## Three things

**A. The implementation rules.** The rules acceptance applies: the
deciders of the single pass, each with its own soundness theorem, which
the acceptance theorem `PassUnit.mode8Accepted_sound` reads. They are
implicit to different degrees: a rule is stated by its code, and its
documentation ([PROGRAM-TYPING.md](../PROGRAM-TYPING.md),
[FOOTPRINTS.md](../FOOTPRINTS.md), [ARITHMETIC.md](../ARITHMETIC.md) and
the comments of the deciders) states it as far as it does.

**B. The paper rules.** The definitions and rules of the paper. Their
formalisation in Lean is a first infrastructure: statements of part of
the paper, equal to it in places and narrower in others, which the
paper's status tags cite and acceptance does not apply. It may be brought
to exact correspondence with the paper, or deleted.

**The shared model.** Worlds, admissible transitions, heaps, regions,
changes, effects, support, respect and the frame theorem: definitions
both A and the formalisation of B read.

**Separable.** The formalisation of B is deletable without touching A:
A imports the shared model only; the formalisation imports the shared
model and A; the existing bridges between A and B belong to the
formalisation.

**C. The correspondence between A and B.** Partial. For a rule of A, the
rule of B it agrees with, how far, and where they differ, is to be
studied, first where pretext's functions rely on it. It has two
directions:

- **from A to B:** what A accepts is derivable by B's rules;
- **from B to A:** what B derives, A accepts.

Each is explored informally first: by examples and by reading the two
side by side, not by a theorem.

## The first item: B

Clarity on B, in three parts:

1. **Where it lives.** The Lean modules, definitions and theorems that are
   B, and what each states.
2. **How far it matches the paper.** For each definition and rule of the
   paper: the statement of B that is it, and whether it is equal, narrower
   or broader, with the difference stated; or that B has none.
3. **How to make it identifiable and separable.** A refactoring that places
   the formalisation of B in its own part of the source tree, moves what A
   reads of it into the shared model, and leaves no import from A into
   it.

## Where B lives

The formalisation of B is the modules of
[lean/Verification/Paper/TolerantFrames](../../lean/Verification/Paper/TolerantFrames):
19 modules, about 8,600 lines and 1,989 declarations (counted 2026-11-17),
with [their own axiom check](../../lean/Verification/Paper/TolerantFrames/Tests/AxiomCheck.lean).
No module outside them imports one of them. Each module's header states
what it proves; the modules fall in four groups.

**The assertion language and its derivations** (the paper's §4–§6; the
design [parity-interfaces.md](parity-interfaces.md), I4 and I5):

- `ParityAssertions`: the assertion language as one acyclic arena of
  nodes, its satisfaction $`\rho, m, h \models F`$ at a name valuation, an
  entry mark and an indexed state, and the modality read through the
  effect action.
- `ParityEvidence`: substitution, the transport of freshness between
  marks, the meaning of a rigid path, and support contexts throughout a
  modality, with the tolerant frame theorem over the arena
  (`Parity.tolerant_frame`, `atom_frame`, `RigidityEvidence.sound`).
- `ParityDerivations`: two-state formulas and the checked derivation
  `Derivation`, whose constructors are the paper's rule schemas that read
  no region membership (the connectives, guards, witnesses, substitution,
  the laws of the modality, (Grow), (Dense), Frame, Frame⁺, linear
  arithmetic and the arithmetic of bound facts); the untrusted
  `RawDerivation` its checker reads, and `Derivation.sound`. It holds half
  of B's declarations (1,027).
- `Tests/ParityDerivationTests`: the paper's derivations encoded as raw
  derivations and checked.

**Command summaries** (the paper's §3, "The effect of a command", and the
rules Entry, Frame, Seq-Eff, Loop and Call of §6):

- `CommandSummaries`: a command's summary, a frame and two-state
  postconditions per exit, its soundness for the command's runs, and
  weakening by checked consequence.
- `CommandComposition`: rebasing, one exit followed by another, and the
  soundness of sequence, choice, a handler and a join.
- `CommandLoops`: the prefix summary of a loop and the rule Loop
  (`LoopEvidence.loop_sound`).
- `CommandBodies`: a function body's summary read at a call's positions,
  stating the signature's summary.

**The paper's rules in the indexed model, and its examples**:

- `Instances`: an effect that is not rigid, and length lower bounds.
- `ModelRules`: (View), (Init), Call, Alloc, Seq-Eff and Fresh-Eff, with
  the counter-model where a statement needs a premise
  (`apart_not_kept_fresh`).
- `KindsModelRules`: witnesses of (View), Alloc and the view write over
  kinded worlds.
- `ModelLoop`: the paper's loop as a graph of six nodes, a closed instance
  of graph safety (`loop_safe`).
- `Examples`: two graphs with throws.
- `NamedCounterexample`: a named fact a writing step does not keep.

**Bridges** from A's rules to the paper's, under
[Bridges](../../lean/Verification/Paper/TolerantFrames/Bridges):

- `ExitProposals`: the front's class-level summaries as instances of the
  command-summary rules, sound for runs.
- `Grow`: (Grow) at a variable and along a rigid path, a typed field
  write keeping every length lower bound, and the loop's back edge.
- `ModelTyped`: stable paths and class evidence from a typed environment.
- `ParityArithmeticBridges`: the pass's arithmetic atoms read as the
  conclusions of the derivation rules.
- `Transfer`: a node's exit obligations along each exit, which graph
  safety composes.

**What B reads from outside it.** The command-summary and derivation
modules import the shared model alone (`Semantics/`). The bridges, and
`Examples`, `ModelRules` and `NamedCounterexample` outside `Bridges/`, also
import A: `Programs.IndexWrites`, `Programs.SinglePass.GraphSafety`,
`Programs.TolerantFramesInvocation`, `Programs.TolerantFramesNamed`,
`Programs.TolerantFramesWrites` and `Source.Lowering.ExitProposals`.
`ParityAssertions` and `KindsModelRules` read the kinds development
(`Semantics.AdmissibleCells`, `Semantics.KindsNatives`,
`Semantics.ViewSpines`), which lies outside `Paper/` and outside the
import closure of the acceptance theorem's module.

**What the paper cites.** The paper's status tags cite 164 Lean names
(counted 2026-11-17, each resolved to the module declaring it). 39 are
declarations of B; 120 are declarations of A or of the shared model, among
them the laws of the modality (`box_elim` … `box_idem`, in
`Semantics.IndexedStates`), the frame theorem (`frame_step`,
`respect_sound`, in `Semantics.Support`) and graph safety (`graph_safe`);
5 name declarations on both sides (`transfer`, `seq_eff`, `grow`, `cells`,
`ConditionOnActions`).

## Where C is met

A new pretext case meets C. Supporting a pattern of
[Tolerant frames II](tolerant-frames-2-note/note.tex) starts with its
derivation in the paper; whether A accepts the program is then a question
of C, from B to A. Where A does not accept it, the way forward is decided
with the owner: bring the aspects of A and B involved closer together, or
another route.
