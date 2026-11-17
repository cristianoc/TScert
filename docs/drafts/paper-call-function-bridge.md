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
