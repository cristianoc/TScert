# The single pass's controls

The [single pass](SINGLE-PASS.md) has boundaries no proof covers: what the
parser writes, what the type computation proposes, what the interface
stages publish, and how the trusted contracts read. This document lists
each boundary and the controls that guard it.

**Evidence labels.** **Measured** gives the command, the commit or branch
and the date. **Cited** names inspected code. **Conjectured** marks a claim
not checked.

## The mechanism

The controls are those of [the stage store's controls](STAGE-STORE.md#controls):
each feeds the verifier an input no case makes (a forged document, a forced
proposal, a mutation of the pass) and requires its refusal; each registers
with `control(…)`, runs in a pool of control processes, and every operation
it runs replays from the stage store. They are
`tests/single-pass-controls.mts`, run by `test-all.sh` as the suite
"Single-pass controls". A control checks its case through the pipeline,
then runs the pass over the case's fragment under a forced proposal
(`TSCERT_FORCE`), over a forged fragment, or with a mutation verifier of the
pass (`tests/single-pass-mutations.mts`). The forced proposals are one list,
`tests/single-pass-control-inputs.mts`: each entry names a case, a unit and
a force; a positive entry's unit is accepted unforced, with every unit it
depends on, and every entry's unit is refused under its force.

## Coverage

Measured: `node tests/single-pass-controls.mts`, branch engine-cleanup,
2026-11-12: 163 controls, every one passing, 19 s.

| Boundary | Controls | Gap |
| --- | --- | --- |
| The parser's fragment: its shape | Malformed bodies, graph labels, claim-shaped annotations, unexamined fields at the root and on nodes, overload units at another function's code, unbound names, deferred mapped types, a regex shape no declaration lists, a family guard's call without its domain: each refused by the fragment's decoder or the front. | An assignment to an unbound name is refused with no span. |
| The parser's fragment: its contracts (`requires`, `ensures`, loop invariants, statements, store regions) | False postconditions (3), a removed quantified precondition, a false loop-cell invariant, a closure's removed precondition, fresh results, moved, rebased and path regions, an old array at a slot's join, a generic closure's statement, a method's dropped statement, a callee's store separation removed: each refused at its unit. | none |
| The parser's fragment: its declarations | The Promise tag (renamed, dropped, on another prototype, a base or a callable one, PromiseLike in `then`, an allocation keyed by it, the native contract without it), a generic member's result, a union host's member effects, an array's `toJSON`, stable keys and stable links, written applications' arguments, scopes and references, binder roles, an unguarded alias, guard domains, a guard's promise, another import closure: each refused. | none ([declarations by identity](#declarations-by-identity)) |
| The parser's fragment: reserved names | Each write form renamed to `stack` refused at the write's span; a member renamed `stack` accepted, the reservation the parser's alone. | none |
| The type computation's proposals | 106 forced proposals ([below](#forced-proposals)), each a positive unit accepted unforced and refused forced, or a negative one refused both ways. | none |
| Loop-head facts | The `head-*` forces, each stating a false fact among a loop head's proposals, refused at an edge into the head ([loop heads' proposals](SINGLE-PASS.md#loop-heads-proposals)). | A unit whose loop head needs a fact the walk does not propose is refused: a loss of coverage. |
| The start's entry | `start-facts` (returntype-guard `isName@125`); the mutation `sp-entry` accepts it, so this control catches a pass without its entry check. | none |
| The pass's checks (mutations) | `sp-entry` caught by the `start-facts` control; `sp-footprint` caught by three negative cases. | `sp-edge-evidence` flips no unit of the cases probed; the edge evidence is the pass's own ([below](#the-passs-own-evidence)), so no force of it is kept. `checkedEdge`, `checkedStep` and `returnCheck` have no mutation: their results carry the pass's answers, and a mutation must build that structure. |
| Module interfaces and the stage store | A module's document leaving out a function an import reaches (the imported function, or one its code calls): each unit reading the import refused at its read, `unbound name <name> in <module>, read through the import '<local>'`, on the interface path and the one-process path; a forged interface row refused by the store-map check; a module's store stating no built-ins; rows of another signature; a forged stored interface recomputed; an interface stale for an edited module refused; forced and selected requests keyed apart; own-file and reordered requests reach the same keys; an importer's forced execution prints one payload; a timed-out or failed component unpublished; cold and warm runs agree, the interface stages replay warm, an importer's edit executes its stages and replays the module's interface, to a cold run's outcome; the pass's exit without a complete refusal, injected into the verifier `VERIFIER` names, a tool failure. | none |
| Native and host contracts | Every negative case `tests/node-runs.mts` runs under Node refused, but one reviewed acceptance (invalid-native-promise-invariant-result `widen@89`, a valid instance the pass checks: `make<unknown>` at the expected result `Box<unknown>`); the stand-in host's reading rules, a declared-optional method, the string-tagged family, the compiler enums through an audited and a mismatched installation, nested installations. | `exhausted` at a written obligation is reported `unsupported` (`pipeline/verify-source.mts`). |
| The lowering | The malformed bodies above; the front's refusal of a form it does not handle is a refusal (two `jsDoc` forms). | 996 refusals of the cases name a node and a Lean term, no span (`expression at node N`, measured 2026-11-12). |

## Declarations by identity

The code names each declaration it reads by its identity (its module, name
and span, the `target` of a reference), and the front reads the definition
of that identity. So a tampered declaration list changes what the pass
accepts for a unit only through the identities the unit reads:

- An identity the document has no definition of: the unit is refused at
  its annotation (`the declarations required by this unit cannot be
  interpreted: reference has no declaration equation`), the first half of
  the control "forged declarations: another import closure". A unit reading
  no declaration (`identity`) has a verdict independent of the list, its
  second half.
- A definition's content under its own identity: the document is the front's
  statement of what TypeScript resolved, and it carries no hash
  ([AGENTS](../AGENTS.md), "Wire formats"); nothing can check content
  against anything but the code that reads it. Content the code contradicts
  is refused by the controls of the declarations above (a generic member's
  result, member effects, the Promise tag); content no code contradicts is
  the trusted front's, a review obligation.

## Forced proposals

A force (`TSCERT_FORCE=<force>`, comma-separated) makes the walk or the
loop-head inference state something false. The pass checks every proposal
at its node, so each forced unit is refused. Each force is described beside
the rule it contradicts, in [the walk's rules](SINGLE-PASS-FRONT.md) or
[loop heads' proposals](SINGLE-PASS.md#loop-heads-proposals); the list of
forced units is `tests/single-pass-control-inputs.mts`. Among them:

- `literals` (every function literal at keep/keep), `callees` (every
  function of the file without a written footprint at keep/keep),
  `throws` (every function at keep/keep bounding its throws), `imports`
  (every imported function a module establishes keeping values and stores
  and bounding its throws), `results`, `defaults`, `schemes`, `binds`,
  `steps`, `no-return`: footprints a unit's own check refuses;
- `elements` (every element read without `undefined`), `objects` (every
  object literal at its expected type), `spreads` (every spread with every
  key its operand's type states, optional ones as present, the copy at its
  own keys exactly), `keys` (a keyed read of an object at the first name
  its key may spell alone), `instances` (a call's instance kept at the one
  its actuals give where the type expected of its value does not admit
  that instance's result), `arms` (a call of a union of callables at its
  first arm's signature), `offers`, `callbacks`, `captures`, `cells`,
  `early`, `fresh`: types at a point;
- `stale` (a binding a function literal assigns kept narrowed across a
  call), `guards` (each guard's and family guard's true answer stated on
  its false edge too), `reads` (a member read's receiver held without
  `null` and `undefined` at every later statement), `paths` (each narrowed
  member path kept narrowed at every later statement), `loops` (each path
  narrowed before a loop kept at its head, its body and its exit, whatever
  ends it), `decided` (every test's `false` answer unreached), `finally`
  (a finalizer's shared entry its statement's normal completion alone),
  `never` (every call's statement completing at no value), `meets` (a type
  parameter's value dropped from `a ?? b`'s left operand), `implications`
  (every constant's initializer narrowing every other binding where the
  constant is tested `true`): narrowings;
- `head-entry`, `head-entails`, `head-counters`, `head-every` and the other
  `head-*` forces: loop-head proposals;
- `start-facts`: a false fact at every start, refused by the entry check;
- `preparation-limit`: the file worker's preparation held past every
  stage's limit, so no unit has a verdict and each is recorded with the
  timeout (the control `worker preparation over its limit`);
- `point@<start>-<end>` (`Synthesis.forcedPoint`): at the expression of
  that source span alone, the first of its type's members, else `true`
  (`false` for `true`), the walk going on with the computed type. Thirteen
  such entries guard points no other force reaches (nullish-member-reads
  `size@534`, error-subclass
  `omitted@902`, logical-narrowing-past-reads `untested@879`,
  blocker-module-assignment, invalid-field-test-disjunction `either@238`,
  blocker-function-member-read `runs@561`, field-contents-exclusion,
  enum-reverse-keys `openName@708`, negated-disjunction-test).

A control's acceptance counts only with every unit it depends on accepted:
a run with named units checks only those, a dependency's footprint among
its proposals.

## The pass's own evidence

The edge search's evidence, the step's derivations and the facts at a
point are computed by the pass and checked by it; no input states them.
Whatever they are, a unit mode 8 accepts is safe (`mode8Accepted_sound`,
[the unit theorem](SINGLE-PASS-THEOREM.md#the-final-statement)). A forged
reading of a native at a call or a read, which no source states since
TypeScript rejects the program, is a proposal of the type computation,
which the pass checks at its node; the forces `instances`, `guards`,
`elements`, `objects` and `optional-reads` show each such check is reached.
What stays trusted is the native's declaration itself, which the negative
cases and the Node counterexamples guard.
