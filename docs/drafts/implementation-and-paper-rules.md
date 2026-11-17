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
with [its own axiom check](../../lean/Verification/Paper/TolerantFrames/Tests/AxiomCheck.lean).
No module outside them imports one of them. Each module's header states what it proves. The general assertion, command
and semantic layers are described below; the original certificate and bridge
modules fall in four groups.

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

## General semantic rules

[SemanticRules.lean](../../lean/Verification/Paper/TolerantFrames/SemanticRules.lean)
extends the existing indexed-state modality and support domain with arbitrary
assertions. Semantic respect is distinct from its sufficient pairwise check.
It states the general tolerant frame theorem, weakest stable strengthening,
freshness against any region below the mark, prefix reliance, and Conj retaining
the first derivation's result family. Valid environment roots and the invocation
mark are explicit context obligations. [Correspondence obligations](paper-alignment-obligations.md)
distinguishes this layer from finite certificates and automatic proof search.

The general assertion interpreter is
[Assertions.lean](../../lean/Verification/Paper/TolerantFrames/Assertions.lean).
Its recursive expressions cover the full term and body forms, linear bounds,
unrestricted disjunction, optional equality, ordinary/view elements and
separation’s defined-nonarray cases. The original arena remains the restricted
serialized certificate language. The general syntax does not change A’s shared
schemas or acceptance. Semantic implication/quantification and the value-family
write principles are in
[Consequences.lean](../../lean/Verification/Paper/TolerantFrames/Consequences.lean);
these ingredients do not establish complete postcondition syntax, general
two-state substitution, structural supports, or command-level native rules.

## Renaming, replacement and quantified rules

[Renaming.lean](../../lean/Verification/Paper/TolerantFrames/Renaming.lean)
proves complete simultaneous variable renaming for the general syntax. Images
may alias; existential binders lift the map. Identity/composition and context
validity are proved semantically.
[RenamingAdmission.lean](../../lean/Verification/Paper/TolerantFrames/RenamingAdmission.lean)
preserves declared region admission under type pullback, including shifted
binder declarations. Runtime equality is not used to infer declared types.

[PathReplacement.lean](../../lean/Verification/Paper/TolerantFrames/PathReplacement.lean)
and [ModalReplacement.lean](../../lean/Verification/Paper/TolerantFrames/ModalReplacement.lean)
state selected occurrence replacement with intact suffixes. Variable-only
positions require variable-only output. Local replacement leaves boxes
unchanged; changing a box transports its regional effect and body using future
equality, derived from equality and rigidity of the two selected paths.
Unrelated paths need no rigidity. Derivation constructors enforce input/output
region admission. These are current-state rules; complete mixed old/current
postcondition substitution is a separate obligation.

[QuantifiedRules.lean](../../lean/Verification/Paper/TolerantFrames/QuantifiedRules.lean)
instantiates a full body into actual assertion syntax at an arbitrary linear
index. It retains partial definedness, shifted elements, fields and body
connectives. Its Empty theorem derives collection entries from defined array
or view length and valid root references; density is not a premise. General
Inst, Prefix and Empty constructors are part of the sound derivation system.

## General supports, witnesses and arithmetic

[AllSupport.lean](../../lean/Verification/Paper/TolerantFrames/AllSupport.lean)
proves the exact support `{val:keep, st:keep}` for every assertion without a
modality. Partial element projections, holes, optional fields, separation,
freshness and existential witnesses are included. This is forward preservation
under allocation; allocation may introduce new witnesses, so equivalence is
not claimed. The structural support table and its polarity/omission conditions
are separate obligations.

[Existentials.lean](../../lean/Verification/Paper/TolerantFrames/Existentials.lean)
scopes logical witness introduction and elimination to the current state.
Opening an existential extends the exit environment only. Inherited premises
and the conclusion remove that fresh binder from their current valuation;
old assertions keep the entry environment. The finite derivation system also
contains old monotonicity, proved at the diagonal entry pair, and the all
frame rule by the paper’s sufficient respect check.

[Arithmetic.lean](../../lean/Verification/Paper/TolerantFrames/Arithmetic.lean)
states integer consequence from a finite list of inequalities, fixing literal
values and requiring every goal term to occur in a premise or be literal.
Recursively mentioned element-index terms count, and zero coefficients retain
definedness obligations. Length ranges cover ordinary, view and string
readings, including projected elements. These are current-state arithmetic
rules, without a claim of complete automatic search or mixed-state syntax.

[LiteralEquality.lean](../../lean/Verification/Paper/TolerantFrames/LiteralEquality.lean)
proves the owner-corrected numeric clause of Definition 23: value equality
implies integer equality; the reverse gives the same stored value at a nonzero
integer and the disjunction of both stored zeros at zero. All three finite
derivation rules are sound. Stored equality and A's numeric semantics are
unchanged. [Obstructions.lean](../../lean/Verification/Paper/TolerantFrames/Obstructions.lean)
records why the former unconditional reverse clause fails.

[PathSupports.lean](../../lean/Verification/Paper/TolerantFrames/PathSupports.lean)
states raw reads with intermediate grow and a chosen last tolerance. A
transition-local condition handles omitted fields at any path prefix;
reinstating them at keep and restricting regions permits reuse of the shared
traversal proof. Equality, contents, optional equality and full separation
have their exact successful-read supports. Optional equality preserves a
strict receiver and permits only its final field absent.

[FreshnessCounterexample.lean](../../lean/Verification/Paper/TolerantFrames/FreshnessCounterexample.lean)
proves that failed nullable prefixes invalidate the paper's general freshness
support: a nullish intermediate can become an old object under grow, changing
an empty fresh region to one below the mark. The concrete six-location states
have valid contexts, an admissible transition and admitted regions/support;
this is not a full source EnvTyping or execution proof. The paper's freshness
statement remains unchanged, with the owner decision tracked in WORK.

## First-order two-state postconditions

[PostconditionSyntax.lean](../../lean/Verification/Paper/TolerantFrames/PostconditionSyntax.lean)
interprets first-order syntax in the existing semantic postcondition target.
Program names, logical integer indices and logical values have separate
namespaces; quantifier bodies are syntax rather than arbitrary predicates.
Logical integers can exceed the safe-number range. Ordinary reads use the
current focus, `old(t)` reads the entire term at frozen entry, and modalities
advance focus without changing that entry. Universal source-value quantification requires current heap validity.
Entry heap validity and fine world-role validity are not inferred.

[PostconditionScope.lean](../../lean/Verification/Paper/TolerantFrames/PostconditionScope.lean)
proves logical valuation agreement through all terms, bodies, assertions,
quantifiers and regional actions. Closed admitted formulas do not depend on
unused logical slots. Entry and current program scopes are separate: a result
name available only at exit cannot be read under `old`.
[PostconditionAdmission.lean](../../lean/Verification/Paper/TolerantFrames/PostconditionAdmission.lean)
adds declared-region admission using the existing seven-form judgment and
excludes raw nested-old forms. Program and logical-value roots reuse shared
region semantics through a disjoint encoding. Value binder lifting shifts only
logical roots and reserves the fresh witness as undeclared; it does not infer entry heap validity or fine world-role validity for
universally quantified values; current heap validity is part of their domain.

[PostconditionRenaming.lean](../../lean/Verification/Paper/TolerantFrames/PostconditionRenaming.lean)
proves total semantic transport with independent maps for the three namespaces.
Only the bound namespace lifts at a binder. Both entry/current program
valuations and all modal effects participate; heaps and invocation mark stay
fixed. This is not yet a theorem preserving scope/static admission under
transformed declarations, or general path/term substitution.

[PostconditionExamples.lean](../../lean/Verification/Paper/TolerantFrames/PostconditionExamples.lean)
encodes Q_< and Q_≠i as actual syntax, sharing each quantified index and value
between old/current reads. Successful element readings are proved source values,
including holes. The full Push and converted View-Write formulas are equivalent
to their exact semantic relations under entry/current admissibility and the stated receiver/index/conversion
premises. These are interpretation bridges, not native execution proofs.

[IndexInstantiation.lean](../../lean/Verification/Paper/TolerantFrames/IndexInstantiation.lean)
expresses a defined frozen instance with the existing grammar: defined(t) and
forall j, j=t implies Q(j), with the term shifted below the binder. It proves
this evaluates t once and keeps the resulting integer through Q's old/modal
parts. A conditional obstruction shows unrestricted textual substitution is
false if the term reads zero at entry and one currently. It does not itself
construct a valid/admissible execution or prove admission of the particular
textual formula. The paper's index-at-term sentence does not specify this
choice; the owner clarification is tracked in WORK, and the auxiliary frozen
construction is not inserted as a claimed Definition 23 derivation rule.

## Heap-only logical values and further support proofs

[HeapValidity.lean](../../lean/Verification/Paper/TolerantFrames/HeapValidity.lean)
implements the owner's world-independent quantification decision. Identities
are allocated; ordinary slots/elements contain source values; array-spine slots
and view descriptors select matching heap shapes. This erases fine world roles,
not heap/world semantics. World-valid program roots imply heap-valid logical
roots; the converse is not assumed. Command ValidContext, ExitValid and triples
retain their world-role meanings. Logical support and consequence use the larger
HeapContext, so an existential can open a heap-valid logical value safely.

[WorldIndependence.lean](../../lean/Verification/Paper/TolerantFrames/WorldIndependence.lean)
proves the entire modality-free assertion grammar reads only environment, mark
and heap, including existential binders. The first-order version allows old
terms, quantified values/indices and arbitrary implication, with fixed entry and
current heaps. It supplies the actual Independent premise of Conj. Transition
atoms and boxes are excluded because their semantics reads worlds. Universal
postcondition values use the current heap domain; existential assertions use
their focus, including entry under old. A current witness need not exist at entry.
The actual AST law forall u, exists v, v=u is proved for that common current
domain. Evaluated universal instantiation fixes one successfully read Value
throughout Q. Full syntactic substitution is a separate obligation.

[PostconditionExamples.lean](../../lean/Verification/Paper/TolerantFrames/PostconditionExamples.lean)
now states its Q_<, Q_≠i, Push and View interpretation equivalences on admissible
entry/current pairs. A successful old element reading is source-valued and
heap-valid at entry (including undef at holes), and admissibility transports the
same value into the current universal domain. These are not arbitrary-pair
interpretation equivalences or native execution proofs.

[PathTermSupports.lean](../../lean/Verification/Paper/TolerantFrames/PathTermSupports.lean),
[ElementSupports.lean](../../lean/Verification/Paper/TolerantFrames/ElementSupports.lean)
and [AtomSupports.lean](../../lean/Verification/Paper/TolerantFrames/AtomSupports.lean)
prove the path-reading, numeric element-term, element-atom and density support
rows, retaining arbitrary exactly supported indices/bounds, holes and view
readings. [EverySupports.lean](../../lean/Verification/Paper/TolerantFrames/EverySupports.lean)
handles the paper table's restricted body grammar: the unshifted numeric element
and free exactly supported terms. Its ordinary-array condition is explicit; a
bridge from declared receiver typing is separate. Other body terms have no
support from this definition, as the paper states.

[PolaritySupports.lean](../../lean/Verification/Paper/TolerantFrames/PolaritySupports.lean)
separates semantic growth tolerance from a sufficient certificate. The tolerance
criterion constrains actual successful readings at admissible transitions; it is
independent of the support predicate. Integer-domain monotonicity is sufficient
when the actual readings lie in that domain; it is not identified with maximal
physical growth tolerance. Zero coefficients retain their syntactic terms and
nested index dependencies. Canonical/maximal annotation selection is not proved.
[BelowMark.lean](../../lean/Verification/Paper/TolerantFrames/BelowMark.lean)
proves invocation-entry bounds for immutable descriptor regions, with heap-valid
witnesses and world-valid sufficient corollaries. Spine cell sets are excluded
because growth can add new cells. The fresh-versus-below-mark disjointness proof
uses these bounds without conflating invocation entry and command entry.

## Commands, scope and transfer

[Commands.lean](../../lean/Verification/Paper/TolerantFrames/Commands.lean)
interprets named steps and command control flow through the shared calculus.
Runs have heaps, environments and normal/break/return/throw exits. Triples
supply admissible exit worlds and preserve valid environments and result
values. Return freezes the function’s entry for old; Conj transports only the
second normal/exceptional postcondition to the first proof’s world. An own
field read does not use the shared calculus’s prototype extension on absence.
Native typed-array code is an explicit parameter; selecting it proves no
native contract.

[CommandRules.lean](../../lean/Verification/Paper/TolerantFrames/CommandRules.lean)
and [Loops.lean](../../lean/Verification/Paper/TolerantFrames/Loops.lean)
state general partial-correctness rules. The loop theorem is induction on
execution with actual abrupt exits, not a supplied prefix summary.
[Scopes.lean](../../lean/Verification/Paper/TolerantFrames/Scopes.lean)
derives frame transport from noncapture.
[Admission.lean](../../lean/Verification/Paper/TolerantFrames/Admission.lean)
states the seven paper region forms, declared path conditions and lexical
scope/freshness conditions; raw shared implementation helpers are not extra
paper region forms. Complete admission/typing/substitution bridges remain
separate proof obligations.

[Derivations.lean](../../lean/Verification/Paper/TolerantFrames/Derivations.lean)
is explicitly a sound subcalculus of Definition 23, without an arbitrary
semantic-entailment constructor. [Transfer.lean](../../lean/Verification/Paper/TolerantFrames/Transfer.lean)
assembles Check and connects node triples and effects to regional transfer
with arbitrary knowledge. It does not infer prefix safety from endpoints.
[AliasExample.lean](../../lean/Verification/Paper/TolerantFrames/AliasExample.lean)
encodes the actual loop, both tests and the throw, with scopes, full head
bounds and arithmetic obligations proved. It does not claim a closed
execution/graph proof or use the older six-node graph as that example.

## How far B matches the paper

Every item is compared in [B against the paper](b-against-the-paper.md).
The original source audit found 13 equal, 35 narrower and 2 different
statements, 26 absent and 13 assumed host contracts among its 89 items.
The reconciled table counts exact imported shared theorems and new general
statements, distinguishes semantic rules from certificate coverage, and keeps
unproved syntax, support, primitive, derivation and example bridges explicit.
The owning completion status is exclusively [WORK.md](../../WORK.md#status).

## Where C is met

A new pretext case meets C. Supporting a pattern of
[Tolerant frames II](tolerant-frames-2-note/note.tex) starts with its
derivation in the paper; whether A accepts the program is then a question
of C, from B to A. Where A does not accept it, the way forward is decided
with the owner: bring the aspects of A and B involved closer together, or
another route.
