# Draft: shallow and deep function coverage

The census of `tools/` measures two things per function. **Shallow
verified:** the function's own unit checks against the signatures, with
their claimed effects, of the code it reads. **Deep verified:** the
function is shallow verified, and so is every unit it reaches,
transitively, across files. Deep is the release metric of
[function coverage](../DESIGN.md#function-coverage-and-release-thresholds);
shallow is reported beside it. Claims are labelled **proved** (with the
Lean name), **cited** (with the document and its scope) or **conjectured**.

## The existing mechanism this extends

A unit is already checked against the signatures of the code it reads,
never against that code itself.

- **Module functions within one document.** `extractPlans`
  (`Claims/Extraction.lean`) reads the whole Fragment and claims once (the
  equations, the module environment `moduleFunctions`, `moduleConstants`,
  `classSelves`, the generic instances, `checkInitializationOrder`), then
  extracts each unit, a function or the module's initialization. Each unit
  reads every module function `g` at `moduleArrow g (footprintOf g)
  (onThrowOf g)`: its annotated signature with the footprint and on-throw
  flag `g`'s claim states, extended by a rest of `unknown` because its code
  discards further actuals. `checkDocument` accepts only when every unit's
  request is certified from that unit's own code, so the assumptions the
  units make of each other are discharged in one call.
  `checkDocument_safe` (proved) gives each request's safety under `EnvOk`
  of its inputs. Composing the units into one module execution is
  [module composition](../../WORK.md#module-composition) (open, a review
  obligation).
- **The module import assumption.** An import of a program function is
  read at its declaration's ordinary signature, its
  [statement](../SOURCE-ELABORATION.md#stated-effects) included; the
  importer verifies relative to it whether or not the exporting module's
  run certifies it
  ([imported values](../SOURCE-CONTRACTS.md#imported-ambient-and-global-values);
  cited).
- **Certified imports.** A
  [certified import](../SOURCE-CONTRACTS.md#certified-imports) is read at
  its unit's signature with the effect its module run's claims state; that
  module run is checked as a document of its own (`checkModules`). A read a
  plan, a search or a module run refuses is withdrawn and the importer
  proposed again (cited).
- **Effects and footprints.** What a footprint guarantees is
  [FOOTPRINTS](../FOOTPRINTS.md); a footprint holds on a throw only where
  the effect states `onThrow`
  ([exceptional footprints](../SOURCE-ELABORATION.md#exceptional-footprints)).
  This design adds no effect language and no interface: a unit's
  assumptions are the claims of its document.

**What changes.** The unit stays the unit; the claims document stays the
file's. Today one acceptance covers a whole document, and the census makes
a document per function (a slice holding its same-file closure), so each
body is checked once per slice that reaches it (21,284 s CPU for `tools/`
at 883614a0, measured). The design accepts each unit on its own, over one
front per file, and the census composes the units' results along their
dependencies.

## 1. Units

A **unit** is a set of plans certified together:

- a **group**: the functions of the checked file that reach each other
  through their mentions, a strongly connected component of the file's
  mention graph (§2), one function where it reaches no other that reaches
  it back. Its members are certified simultaneously by one check, each
  member's request discharged, since recursive calls are justified only
  by a simultaneous argument;
- the module's **initialization**, its top-level code, constants, cells,
  classes with their members and enums, in source order, is a member of
  the group its mentions place it in, usually a group of its own;
- a **module run**: the document of a module the checked file reads a
  certified import from, checked whole as today (`checkDocument`).

Executable code the function count does not cover (closures, functions a
module binding holds, class members, callbacks, parameter defaults) is
code of the unit that creates it: a closure is checked in its function's
plan, a class member and a binding-held function in the initialization's.
Its certification is that unit's.

## 2. The file front and per-unit extraction

`extractPlans` splits in two:

```
fileFront   : (ast claims : Json) → fileKey → qualified → Except String Front
extractUnit : Front → UnitId → Except String (EquationStore.State × List (FunctionPlan …))
```

`fileFront` is the shared part of today's `extractPlans`: the equations
(`equationFront`), the module environment, the generic instances, the
initialization's claims and `checkInitializationOrder`, and the unit
graph. `extractUnit` extracts the members of one group from the front's
store, threading a store only through that group's members, and returns
the store it ends with, which `freezePlans` freezes: a unit's extraction
sees what the front computed and nothing another unit's extraction added.
Every input a unit's extraction reads beside its own bodies and claims is
a field of `Front`. `extractPlans`, which a module run's check uses, is
the front followed by every unit's extraction in turn.

A failure of the front refuses every unit of the file. A failure of a
member's extraction (missing claims, a refused scheme, a lowering refusal)
refuses its group alone, located.

**The mention graph.** A unit's edges come from every name its members'
code mentions, bound or not (`stmtNames` over the bodies, parameter
defaults and nested closures included):

- the name of a module function, generic ones included: that function's
  group;
- the name of a module constant, cell, class, enum or generic class, or a
  name the parser makes for a class's parts or its self binding: the
  initialization;
- the local name of a qualified read: the module runs of the file;
- for the initialization, every module function its statements name.

Mentions over-approximate reads, as `checkInitializationOrder` already
relies on. A function value that reaches a unit as an input (a callback, a
field) is created by code of a unit that mentions it, so the owner of its
code is in the closure of whatever unit created it. A unit's
**dependencies** are the groups its edges reach outside its own group,
the initialization included, and the module runs its members name.

## 3. Search, check and the headline theorem

- `--units ast claims` prints the file's units: each group's members, the
  initialization's place, the module runs.
- `--produce-unit ast claims snapshot evidence unit depth` (search,
  untrusted): the front, `extractUnit`, freeze, search; for a module run,
  today's `produceRunJson`.
- `--check-unit ast claims snapshot evidence unit` (check): `planImports`,
  the front, `extractUnit`, freeze, the exhaustive `certifyPlans` into
  `CertifiedPlan`, decode, `checkRequests`; for a module run,
  `checkDocument` of that run. On success it prints `accept`, then
  `depends:` and the unit's dependencies as the front computed them.

The headline theorem is `checkUnitJson_safe`:

```
theorem checkUnitJson_safe
    (h : checkUnitJson ast claims fileKey evidence budget unit = .ok deps) :
  ∃ p front, planImports ast claims = .ok p ∧
    fileFront p.ast p.claims fileKey budget p.qualified = .ok front ∧
    deps = front.dependencies unit ∧ UnitSafe front unit evidence budget
```

`UnitSafe` is today's `DocumentSafe` for the unit's plans: they crossed
`certifyPlans`, every certified request is safe at every admitted
assignment of its parameter rows under `EnvOk` of its inputs (parameters,
the front's module values with their claimed effects, qualified reads,
imported, ambient and host values), and stays within its footprint where
it claims one, also on a throw where it claims `onThrow`. For a module run
it is `DocumentSafe` of that run. The premise is the exact CLI success of
`--check-unit`. `checkJson`, `checkJson_safe`, `--check-source-claims`
and `--produce-source-claims` are deleted: one acceptance path, one
headline theorem, which `AxiomCheck.lean` checks.

That `front.dependencies` includes every unit a unit's code reaches by
name is a reviewed property of the mention scan, stated in the trust
surface beside source extraction; that the printed list is `deps` is the
CLI's serialization.

**A file's outcome.** `verify-source` checks every unit of the file; the
file is verified when every unit is accepted. A case's expectation is
unchanged.

**Certified imports and withdrawal.** A qualified read stays eligible as
`planImports` decides. A module run is a unit named by its location
within one (Fragment, claims) pair, whose `planImports` fixes its
document and claims; its dependencies are the other module runs and, for
deep status, its module's own census units (§4). The withdrawal loop stays
per file: a read is withdrawn when the plan refuses it, when its module
run's search or check fails, or when a unit's search or check refusal
names it, and the file is then proposed, searched and checked again. The
checks run inside that loop, and every check of a verdict is of the last
round's (Fragment, claims) pair.

## 4. Shallow and deep

**A unit's own result:** accepted (its check printed `accept`);
unsupported (the gate, the lowering, the producer, the front or its
extraction refused it, located); unverified or exhausted (search or
check); error (a tool failure or a timeout).

**Shallow verified:** a census function whose group's own result is
accepted. Its check assumes every module value at its signature with its
claimed effect, every import at its ordinary or certified signature, and
every external value at its declared or modelled contract.

**Deep verified:** shallow verified, and every unit of its dependency
closure is accepted. The closure follows the `depends` lists of accepted
checks; its own file's initialization; and, across files, each import of
a census-directory function to that function's group, of any other value
to its module's initialization, and, for every census-directory module
loaded with the file (an import of any kind, a side-effect import, a
re-export, transitively), that module's initialization. A unit not
accepted, a mention the census cannot resolve to a unit, or a unit outside
the census blocks deep status; the census names the first such unit,
breadth-first, as the **deep blocker**, with its own result.

Deep status states that every obligation of the closure has an accepted
check. Each check gives the safety of its unit conditional on its inputs
meeting their contracts (`EnvOk`); combining the checks into the safety of
the composed execution, recursive groups and initialization included, is
[module composition](../../WORK.md#module-composition), open. A group
checked together supplies the certificates that argument needs, not the
argument.

**What blocks deep status, by assumption:**

| Assumption of a unit's check | Certificate it needs | Blocks deep when |
| --- | --- | --- |
| a same-file function at its claimed signature and effect | that function's group, same front | its group is not accepted |
| a module constant, cell or class at its claimed contract | the initialization | the initialization is not accepted |
| a certified import | its module run, same pair | the module run is not accepted |
| an import of the census directory at its ordinary signature | the declaration's group in its own file | that group is not deep-accepted along the closure |
| a value outside the census directory (package, `.d.ts`, host) | the [trust surface](../DESIGN.md#trust-surface) | never: an external assumption of stated scope |

Two readings of one same-file signature are one claim of one front, so a
same-file edge needs no interface comparison. An import read at its
ordinary signature relies on the parser reading the declaration alike in
both files, the import assumption's existing review obligation; a
certified import's two readings are compared structurally, as today.

**The counts.** Shallow and deep each count census functions; a group
counts each member. If every unit of the closure of a set of functions is
accepted, every function of the set is deep verified, by definition. That
says nothing of code outside the census directory's units, and leaves
source correspondence, module composition and host assumptions as they
are (cited: the theorem's scope above).

**Exceptions.** A footprint certified for normal return gives no
preservation on a throw; a caller that catches is checked against the
heap its callee's `onThrow`, or its absence, allows. Guards and
fresh-result promises are normal-return guarantees.

**Initialization.** A function mentioning a module constant, cell, class
or enum depends on the initialization, whose acceptance (its order check
`checkInitializationOrder` included) its deep status requires. A cell read
before initialization throws the checked access's `ReferenceError`
([module cells](../SOURCE-ELABORATION.md#module-cells); cited).

## 5. The census

The census checks the directory's files themselves, with no slices: each
file is parsed once and has one front; its units are its functions, its
recursive groups and its initialization; each unit has its own search and
check; deep status comes from the `depends` closure. `make census
FILES=… FUNCTIONS=…` selects units, with their dependency closure where
deep status is wanted.

**Refused functions: the absent-function boundary.** The parser leaves a
module run's function out where its gate refuses it, with the reason
([certified imports, failure boundary](../SOURCE-CONTRACTS.md#certified-imports)).
For the checked file, the census uses the same boundary with the
function's signature kept:

- the parser takes the file's **absent** functions as an input, extends
  that set to the recursive groups of the source's mention graph (a
  refused member refuses its group), and reads each absent function as it
  reads an ambient `declare function`: a value at its declared signature,
  read under the import assumption, its body neither scanned nor lowered,
  so its callers are checked against that signature and are not left out
  with it;
- every scan of the source over binding facts (`eval`, `arguments`, the
  writes of a function's binding) still reads the absent bodies;
- the fragment lists each absent function with its reason (`absent`, as a
  module's does).

A parse, control-flow lowering or proposal refusal located inside a
function of the file makes that function absent, its reason the refusal,
and the file is parsed again; each round adds a group, so the rounds end
within the number of functions plus one. A refusal located outside every
function, or in an absent function's signature, refuses every unit of the
file. An absent function's own result is its refusal; its callers depend
on it by name, so it blocks their deep status.

**The record.** Outcomes are keyed by unit identity (file, then the
function's name or the initialization). Per file: its rounds with the
functions each made absent; per unit its members, own result, `depends`
and stage invocations. Per census function: its unit, its own result and,
computed from the record alone with no verification run, its deep status
and deep blocker. Statement coverage classifies each statement by the
unit that owns it (a statement of the module's top-level code by the
initialization) under shallow and under deep. `report` prints shallow and
deep counts and statement coverage by each, and their movement between
two records; `refusals` groups the units whose own result is a refusal by
its first blocker, weighted as today, and lists for each function blocked
only by a dependency the unit blocking it.

**Cross-file edges.** The census resolves each import of a file to the
census-directory declaration it binds (a named, default or namespace
import, the last reaching every unit of the module, and a side-effect
import or re-export the module's initialization), syntactically and
over-approximately: every import a unit's members mention, and every
module the file loads for its initialization. A mention the census cannot
resolve to a unit blocks deep status.

## 6. Cases and controls

- A pipeline case whose functions verify only through each other's
  claimed effects, and its negative where a callee's code exceeds the
  footprint a caller relies on.
- A control forging one group's claims: the forged unit refused, the
  others of the file accepted, and the forged unit reported as the deep
  blocker of each unit depending on it.
- A control showing a recursive group refused as one unit when one
  member's request is not certified.
- A control showing a unit's evidence checked against another unit
  refused.

## 7. Cost

Each body is searched and checked once per round of its file; parsing,
lowering and proposing run once per round per file. That is a scheduling
objective, not a guarantee: the withdrawal loop and the census's rounds
repeat the file's front stages, and the front's decoding and equations are
repeated by every unit's search and check (measured per unit once
implemented).
