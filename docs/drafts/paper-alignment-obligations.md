# Correspondence obligations for Tolerant frames

## The existing mechanism this extends

The shared semantics already defines heaps, worlds, admissible transitions,
regions, effects, support domains and the modality. The paper modules import
that semantics. The finite `Parity` arena, derivations and raw checker are
proof-certificate infrastructure, described in [the basis](implementation-and-paper-rules.md).
This work extends those semantic mechanisms to the language and rules of
[the paper](tolerant-frames-note/note.tex). It does not migrate acceptance.
The source audit is [B against the paper](b-against-the-paper.md); the owning
status is [WORK.md](../../WORK.md#status).

The implementation branch starts at the fetched `origin/single-pass` commit
`ba681dfdab8ab41c7d73f3c573f449ab90fedab7`, verified against both the local
checkout and remote tracking reference on 2026-11-17.

## What correspondence requires

For each definition, compare its quantified domain and meaning. For each
rule, compare every premise and conclusion, including definedness, scope,
marks, worlds, exceptional exits and semantic side conditions. A theorem with
a stronger premise is not the displayed rule. A theorem establishing only a
consequence of the displayed postcondition is not the whole postcondition.
Imported shared theorems count when their statements are the exact notion.

Three different obligations must be kept separate:

- The semantic language and rules describe all the forms of the paper.
- A finite certificate has a sound interpretation in those rules.
- Automatic search attempts to find certificates. Search completeness is not
  required, and does not follow from certificate soundness.

A finite checker may reject a valid entailment. Its accepted certificates
must not define the meaning or coverage of a general paper rule. Conversely,
a semantic proof of an entailment is not automatically a derivation in the
particular calculus of Definition 23. General logical derivations and the
serialized `Parity` checker have separately stated proof scopes.

## Renaming is not arbitrary path substitution

A variable renaming is total over every assertion constructor and lifts beneath
logical binders. All occurrences in terms, bodies, witnesses, regions and modal
effects must participate. Actual-variable images may alias. Declared-type
admission follows from a declaration pullback, not heap equality.

The paper’s path-replacement rule concerns selected occurring paths. A bare
variable slot in density, apartness or an equality witness cannot silently
become a field path: the output must still belong to the grammar. Prefix
replacement retains the entire suffix. Beneath a binder the selected free
paths shift. An unchanged box requires no rigidity; a changed effect/body
requires equality at all admissible future states, which equality plus rigidity
of the two selected paths supplies. General mixed old/current postcondition
substitution must respect each phase’s environment and the frozen function
entry; a current-state replacement theorem is not that theorem.

## Numeric literal equality obstruction

Definition 23 says that equality of a path to a safe-integer literal and
term equality with that integer imply each other. Shared integer reading
maps both IEEE zero representations to the integer zero. B’s value equality
in `Atom.equal` compares the stored values, which distinguish their bits.
[The proved countermodel](../../lean/Verification/Paper/TolerantFrames/Obstructions.lean)
has every variable hold `-0`, in any indexed heap at mark zero. Both integer
inequalities defining `x = 0` hold; `x ≐ +0` fails. All roots are valid source
values and no heap location is used.

This is a correspondence obstruction to the bridge under B’s current equality
interpretation, not a counterexample to integer arithmetic. Changing literal
equality alone also requires checking Guard, contents/literal membership and
replacement soundness: those notions currently share raw value identity.
An alternative paper statement needs an owner decision. The unrestricted
bridge cannot be counted as proved under either an added nonzero premise or
a new axiom. Independent support and integer-consequence proofs do not depend
on resolving this item.

## Quantified-index instantiation across phases

Definition 23 says: “A postcondition quantified over indices is instantiated
at a term.” Its wording does not specify freezing or textual substitution.
A logical index is fixed across states. Thus forall j, old(j=0) implies j=0
is true. If a term reads zero at entry and one currently, textual replacement
gives old(t=0) implies t=0, which is false even with both readings defined and
without modalities. [The conditional obstruction and frozen construction](../../lean/Verification/Paper/TolerantFrames/IndexInstantiation.lean)
formalise this distinction. The conditional theorem assumes those evaluations;
it is not reported as a constructed valid/admissible execution countermodel.

A defined frozen instance is expressible in the existing first-order grammar:
defined(t) and forall j, j=t implies Q(j), where t is shifted below the index
binder and appears only in the current-state guard. Its proved interpretation
evaluates t once and gives Q that integer as a logical value. It is an auxiliary
semantic result pending clarification of the paper sentence, not evidence for
unrestricted textual substitution or an extra Definition 23 rule. A source
term under a modality requires the same distinction between rigid logical
values and heap readings at each future state.

## State and command obligations

The shared `IndexedHeap` contains the heap, world, budget and heap invariants.
The paper also requires valid environment roots and an invocation mark no
larger than the heap. These are explicit context obligations; they must not
be inferred from the existence of an indexed heap. The surrounding type
system supplies variable types. Logical values must be source values rather
than internal spine contents or executable terms.

Command execution records heaps, environments and control exits. A proof of a
triple supplies an admissible exit world. Two proofs can supply different
worlds. Conj therefore retains the first world and transports the second
normal and exceptional postconditions by independence. The compatibility
premise of the shared safety theorem combines an additional result family;
retaining its first family discharges that premise by projection. It is not
a missing premise of the displayed paper rule.

Break and return have obligations from their enclosing loop and function.
An `old` in a return obligation refers to the function entry, which must be
frozen independently of each local command entry. Sequence preserves the
invocation mark. Frame scope includes the effect appearing beneath a box;
a binding cannot capture a variable of the frame. Freshness disjointness
requires an actual proof that the other region is below the invocation mark.

A completed-run triple states partial correctness and endpoint
admissibility. Prefix reliance needs bounds for each intermediate primitive
and callback prefix. It cannot be deduced from an endpoint effect alone.

## Primitive and host obligations

Push includes the appended-element equality and the universal kept-prefix
postcondition. View-Write uses the converted value and the universal
other-index postcondition. A theorem about a family of present readings is
an ingredient, not the full rule for a quantified body which might read no
element. Free terms and bounds must be preserved wherever a rule relies on
that preservation.

Native contracts are explicit parameters to soundness statements. Providing
code for a native operation does not prove its contract, and no result in B
certifies the actual native library. Write-End and Str-Read require exactly
the postconditions in the current paper; their future-work conjectures are
not extra premises or conclusions of those rules.

## Review and validation obligations

Every new module belongs to the Paper axiom check. No module outside
`Verification.Paper` may import a module inside it. A-to-B bridges stay on
B's side. The acceptance theorem, acceptance decisions and trust surface of
A are preserved. Any necessary shared assertion change requires an explicit
impact analysis and regressions; new B syntax may instead interpret the
existing shared heap/world/region semantics without changing shared schemas.

Focused Lean builds establish that proofs typecheck. The axiom checks
establish their axiom dependencies. Neither establishes paper correspondence:
independent review must inspect the statements against the paper and report
its actual scope. The full repository checks, regression cases and docs
checks provide their separate validation evidence.
