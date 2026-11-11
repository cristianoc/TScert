# Draft: module interfaces

A module's interface is what an importer reads of the module beyond the
declared types: for each function of the module an import resolves to, the
footprint, on-throw flag and returned footprint its module's check
established, or the ordinary effect. It is computed by the module's own
mode-8 run, stored once by the content of everything it was computed from,
and read by every importer in place of planning, walking and checking the
module again ([imports](single-pass.md#9-the-claims-free-front), "Imports").

## The existing mechanism this extends

[The stage store](../STAGE-STORE.md): a stage's result is an entry keyed by
the SHA-256 of the stage, its implementation and its complete input
description ([keys](../STAGE-STORE.md#keys)), and a later run whose key
matches replays the entry instead of executing the stage, across runs,
checkouts and worktrees. Replaying a check trusts the store's binding of
results to exact inputs and the integrity of what it stores
([replay and trust](../STAGE-STORE.md#replay-and-trust)), nothing more.

A module interface is the output of one more process stage of that
mechanism, keyed and replayed as every stage is; it adds no second cache.
What is new is only which part of a mode-8 run is its own stage: the
importer's invocation computes its modules' footprints
(`fragmentPlansWithModules`) inside its own stage, so that work is keyed by
the importer's inputs and is of no use to another importer.

## What an entry contains

For a module `M` at its content:

- for each function of `M` an import can resolve to (`eligibleRead`: no
  binders, rest, receiver or guard, a binding no code of `M` writes), by
  name and name position, one of:
  - `established`: the footprint, on-throw flag and returned footprint its
    walk proposed, at which its group and every group it depends on were
    accepted;
  - `ordinary`: proposed the ordinary effect, resting on a refused group,
    or not walked (async, generic, of a written effect);
- the key of the entry of each module `M`'s reads resolve to, the
  dependencies the established footprints rest on.

The importer's own checks stay with the importer: the resolution of each
import to a unit (`importerReads`, `eligibleRead` with `sameReading`, which
compare the importer's declarations with `M`'s; 0.04 s for
`prepareRichInline`), and the reading of each import at its declared type,
at the entry's footprint.

## Its key, and why it is complete

The key is the SHA-256 of:

1. the stage and its implementation, as for any process stage: the
   verifier's executable with its libraries and the stage runner;
2. the mode (8, the pass; 9, the referee's search and check), the fuel and
   search budget, and the environment the mode reads that changes a
   proposal or a check (`TSCERT_FORCE`, `TSCERT_ALL_CUTS`);
3. `M`'s document as an importer's fragment lists it (`Fragment.ModuleAst`:
   location, `sourceSha256`, declarations, initialization, functions and
   the functions left out);
4. the given file's lines of `M`'s units (`module:<location>#<unit>`), the
   loop heads' facts its checks read;
5. for each module `M`'s reads resolve to, the key of its entry.

Every input `M`'s plans and checks read is one of these: its code and
declarations (3), the footprints of its imports (5, transitively, so the
keys form a Merkle tree over the import graph), its loop heads' facts (4),
and the code that computes and checks (1, 2). A change of any of them
changes the key: an edit of `M` changes (3) of `M` and so (5) of every
module that reads `M`; an edit of a module `M` does not read leaves `M`'s
key as it is. The modules on a cycle of reads are planned together, their
reads of each other at the ordinary effect, and keyed by their documents
together.

## Who writes it and who reads it

The module's own mode-8 run writes it: the run that checks `M`'s file
plans and checks every group of `M`, and writes, for the accepted groups,
the footprints they were accepted at, and `ordinary` for the others. A run
writing an entry has executed the check an importer would run; nothing is
written as established for a group the check refused or did not run.

Every importer's run reads it: each import its selected units read
resolves to a unit of `M` (importer-side), and its footprint is the
entry's. Reading an entry rests on the check having accepted the module
unit, as reading a footprint established in the same invocation does;
replay adds only the store's existing trust in its binding of results to
exact inputs. Trust does not widen: an entry states no footprint the
module's check did not accept at exactly these inputs.

Where no entry exists for a key, the importer runs the module's stage
first (the store executes it and publishes its entry), then reads it: the
cost is paid once per module content, by whichever run needs it first.

## Expected cost

Measured 2026-11-11 (perf gate, CPU of the verifier process, best of 3,
mode 8 with the gate's stand-ins): `prepareRichInline` 5794 to 7146 ms over two measurements, of which
the modules' least fronts 0.23 s, least walks 0.77 s, plans 1.73 s and 115
groups checked 2.24 s; the verifier of f894d34a, which plans no module,
2188 ms. `measureAnalysis` 1275 ms (934). `buildEngineProfile` reads no
module's footprint (142 ms, 143).

With the entries in the store, an importer's run plans no module: its cost
is f894d34a's plus the reads' resolution and the entries' reads, expected
about 2.25 s for `prepareRichInline` and 0.95 s for `measureAnalysis`
(conjectured from the parts above), the precision of the established
footprints kept (`prepareRichInline` verified with no stand-in). The
modules' own runs pay the rest once per content, where a census already
runs each of them.

## Decisions

- The interface is a stage of the stage store, the module's own mode-8 run
  computing it, so its entries are shared by every importer and every
  checkout through the existing mechanism.
- The key is complete by construction: the module's document, its loop
  heads' given lines and its imports' entry keys, beside the
  implementation and the mode's inputs.
- An entry states only what the module's check accepted at those inputs;
  an importer reads it as it reads a footprint established in its own
  invocation, so no trust is added beyond replaying a check.
