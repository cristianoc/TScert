# Dossier: facts about locations a call cannot reach

The evidence for a design round on pattern P22 of
[Tolerant frames in practice](tolerant-frames-patterns-note/note.tex), "a fact about a
location a callback cannot reach", and on the patterns of that paper that
share its structure. It proposes no design. Each claim is labelled:

- **observed**, with the command or the file and line it was read from;
- **cited**, with the document and the scope of what it states;
- **conjectured**.

Pretext is the fork's `tscert-bounds` branch at `6837e821`; "upstream" is
chenglou/pretext at `0d102a5`, the fork's base; file names are under `src/`. TScert is `single-pass` at `ac7ec4f9`. The rules cited are those of
[Tolerant frames](tolerant-frames-note/note.tex).
The check command is
`TSCERT_STEP_LIMIT=300 node dev/check-functions.mts <pretext checkout> <file> <functions>`,
written below as `check <file> <functions>`.

## 1. P22's two forms

*Tolerant frames in practice* states P22 as a fact about a location "the caller allocated and
never handed to the callback, nor made reachable from what the callback
holds", which "keeps its contents across the call" (cited: *Tolerant frames in practice*, §P22,
"What an extension must provide"). Its program is the case
`bounds-pattern-unreachable-field`, at the base commit:
a walker holds its index in a field `c.i` of a cursor it allocates and calls a
visitor typed `(w: number) => Modifies<{ values: "any"; spines: "grow" }, void>`,
which receives only a number.

**Observed** (`node pipeline/run-cases.mts bounds-pattern-unreachable-field bounds-pattern-visitor`,
6 of 6 as expected): the case is a named gap, refused at the read `xs[c.i]!`
with "The callee requires 0 <= c.i && c.i + 1 <= xs.length, which the facts
here do not establish" (its expectation, `pipeline/cases.mts:2889`). Its
neighbours: `bounds-pattern-visitor` and `bounds-pattern-visitor-handle`
verify; `invalid-bounds-pattern-visitor-handle` is refused (a negative case,
unsafe under Node).

### (a) The cursor

A location the caller allocates, never stores where the callback can read
it, and passes only to its own helpers.

- `walkPreparedLinesRaw` (`line-break.ts:290–322`) allocates
  `cursor: LayoutCursor` at line 296, passes it to
  `normalizePreparedLineStart` (line 298) and `stepPreparedSimpleLineGeometry`
  (line 316), and calls `onLine?.(…)` at line 319 with five numbers, three of
  them read from the cursor's fields (observed, source).
- `onLine`'s type is `InternalLineVisitor`, stated
  `Modifies<{ values: "any"; spines: "grow" }, void>` (`line-break.ts:116–122`;
  observed). Its class entry `values: any` covers every field location of
  the entry heap, the cursor's included (cited: *Tolerant frames*, §3, "Regions":
  $`\mathsf{values}`$ denotes every location of class value).

### (b) The handle

The prepared handle the user creates with `prepare()`,
`prepareWithSegments()` or `prepareRichInline()` and passes back.

**Upstream's handles are opaque.** At `0d102a5` (chenglou/pretext, the
fork's base; `git show 0d102a5:src/…` in the checkout; observed):

- `layout.ts:40–46`: `declare const preparedTextBrand: unique symbol` and
  `export type PreparedText = { readonly [preparedTextBrand]: true }`, under
  the comment "Keep the compact height-prediction handle opaque so the public
  API does not accidentally calcify around the current parallel-array
  representation".
- `layout.ts:53–57`: `PreparedTextWithSegments = PreparedText & { readonly segments: readonly string[]; readonly kinds: readonly SegmentBreakKind[]; readonly widths: ArrayLike<number> }`.
- `layout.ts:154–156`: `getInternalPrepared` returns `prepared as InternalPreparedText`.
- `rich-inline.ts:53` and `81–83`: `declare const preparedRichInlineBrand: unique symbol`
  and `export type PreparedRichInline = { readonly [preparedRichInlineBrand]: true }`;
  `InternalPreparedRichInline = PreparedRichInline & { data: …; onlyItem: …; … }`
  (line 136); `getInternalPreparedRichInline` returns
  `prepared as InternalPreparedRichInline` (lines 182–184).
- `README.md:32` and `139`: `prepare()` "return[s] an opaque handle", "an
  opaque value to pass to `layout()`".

So upstream exposes no writable representation of any handle: the two
prepared handles are branded, `PreparedTextWithSegments`'s three fields are
read-only views. (The coordinator's brief states that upstream's
`PreparedRichInline` is `InternalPreparedRichInline` with plain fields; at
`0d102a5` it is branded, and the plain form at `rich-inline.ts:79` and `132`
is the fork's: observed.)

**The fork's rewrite.** Commit `2b11a4c` ("Rewrites under which TScert
verifies all of src/") replaces both brands with the records:
`export type PreparedText = PreparedLineData`,
`export type PreparedRichInline = InternalPreparedRichInline`, each accessor
returning its argument, and drops `readonly widths: ArrayLike<number>` from
`PreparedTextWithSegments` (observed: `git show 2b11a4c -- src/layout.ts`).
Its reasons, from the rewrite list of cristianoc/pretext#1, "Handle types",
which TScert issue #94 points to (cited, read with `gh pr view 1 -R cristianoc/pretext`):

- "A brand is a field no handle has; the downcast back to the record relies
  on every handle coming from preparation, which TScert cannot check. The
  structural type states the record, so a handle is checked like any
  argument."
- Gap workaround: with `readonly widths: ArrayLike<number>`,
  `{ ...prepared, segments, kinds }` "is not derived at the return type".
- The case it names, `blocker-pretext-opaque-handle-cast`, is a gap: a
  branded handle cast with `as` to its internal record, refused with "no
  claim of the handle meets the internal type's fields" (cited:
  `pipeline/cases.mts:113`). Observed: `node pipeline/run-cases.mts
  blocker-pretext-opaque-handle-cast sealed-handle`, 11 of 11 as expected,
  that case a gap and `sealed-handle`, `sealed-handle-value-import` and
  `sealed-handle-intersection-representation` verified.

**What TScert reads of an opaque handle today.** A brand with no
`@representation` is refused at the cast (above). A brand stating
`@representation T` is a **sealed handle**: "`H` means `T`: its equation is
the reference to `T`, and the members `H` declares, a brand no value holds,
are no requirement", so a cast out holds of every value of `H` (cited:
[a handle means its representation](../PROGRAM-TYPING.md#a-handle-means-its-representation),
rule `handle-meaning`). Its invariant is assumed at each function taking
it and established at each call and return (cited:
[type invariants](../ARITHMETIC.md#type-invariants)); a caller outside the
analysed sources is assumed to pass a value of `T` meeting it (cited:
[trust surface](../DESIGN.md#trust-surface), line 539).

**Form (b) with the opaque type restored.** Observed with a probe of
upstream's shape, a sealed handle
`/** @invariant this.flags.length === this.widths.length @representation Rep */ type Handle = { readonly [brand]: true }`,
`Rep = { widths: number[]; flags: Uint8Array }`, an opener cast
`h as Handle & Rep`, `last(h: Handle)` reading `flags[widths.length - 1]!`,
and `walk(h: Handle, visit)` calling `visit(0)` (a number only) then
`last(h)`, run by `node pipeline/verify-source.mts` (files placed in
`pipeline/examples/` for the run and removed):

- visitor stated `{ values: "any"; spines: "grow" }`: unverified, at
  `last(h)`: "The callee requires view(h.flags) <= h.widths.length &&
  h.widths.length <= view(h.flags), which the facts here do not establish";
- visitor stated `{}`: verified (`open`, `last`, `walk`).

So TScert refuses form (b) at an opaque handle as it does at the record:
the handle means its representation, the visitor's stated effect covers
every location of class value and lets every spine grow, and no assumption
states that external code holding a value at an opaque or read-only type
writes none of its locations. Under upstream's types, a user callback
reaches a `PreparedText` or `PreparedRichInline` only at a branded type,
and a `PreparedTextWithSegments` at read-only fields; that it then writes
none of its locations is what the types say to TypeScript code, and is no
statement of TScert's model or trust surface (observed: the rows at
[trust surface](../DESIGN.md#trust-surface) lines 537–539, 570 and 573
state preconditions, invariants at calls, plain data, and the preservation
of function fields and prototypes; none states it).

**The fork's form.** `PreparedText` is `PreparedLineData` (`layout.ts:43`),
`PreparedRichInline` is `InternalPreparedRichInline` (`rich-inline.ts:79`),
and the accessors return their arguments (`layout.ts:146–148`,
`rich-inline.ts:178–180`; observed). There a user callback that captures
the handle can write its fields and arrays at their declared types
(conjectured of any callback; no pretext code does it), and
`walkPreparedLinesRaw` passes the same handle to the stepper after the
visit (line 316, reached again after line 319; observed). The visitor can
break a relation of the handle's lengths within its stated effect:
`invalid-bounds-pattern-visitor-handle` pushes onto `widths` and `last(h)`
reads past `flags`, which Node runs to `undefined` (cited: the case's header
and `pipeline/cases.mts:2886`; refused, observed above). The fork's only
statement about it is the comment `// contract on callers:` (§3).

### Re-observation at `walkPreparedLinesRaw`

*Tolerant frames in practice* states that at `aa8f7cc2` the call at line 316 is refused with the
stated effect and accepted with the empty one (cited: §P22). At `6837e821`
every read the stepper makes is rewritten (`?? missing()` or a guarded
throw), and with no edit **observed**: `check line-break.ts
walkPreparedLinesRaw,walkPreparedComplexLines,countSteppedLines,countPreparedLines`
gives all four verified (30 s). The refusal appears once an obligation
crosses the visit. Copies of the checkout in the scratchpad, each edited as
the row says (all edits in `line-break.ts`):

- **E0** (common to all rows): the stepper states
  `@requires safeInteger(cursor.segmentIndex) && 0 <= cursor.segmentIndex && cursor.segmentIndex < prepared.widths.length`
  and `@ensures safeInteger(cursor.segmentIndex) && 0 <= cursor.segmentIndex`,
  and reads `widths[start]!` in place of `widths[start] ?? missing()`; the
  walker's two loops state
  `@invariant safeInteger(cursor.segmentIndex) && 0 <= cursor.segmentIndex && safeInteger(segmentCount) && segmentCount === prepared.widths.length`
  and the same over `startSegmentIndex`.
- **stats**: lines 317–318 (`stats.lineCount++`, the write of
  `stats.maxLineWidth`) removed.
- **stable**: `widths` declared `/** @stable */ readonly widths: number[]`.
- **effect**: `InternalLineVisitor`'s statement, `{ values: "any"; spines: "grow" }`
  or `{}` (the empty effect).

| Variant | Effect | `walkPreparedLinesRaw` (observed) |
| --- | --- | --- |
| E0 | stated | refused at the back edge after `onLine?.(…)` (line 321 in the copy): lacks `safeInteger(cursor.segmentIndex)`, `0 <= cursor.segmentIndex` and both directions of `segmentCount === prepared.widths.length` |
| E0 | empty | refused at the same edge, lacking the same four facts |
| E0, stats | stated | refused, lacking the same four facts |
| E0, stats | empty | refused, lacking only `segmentCount === prepared.widths.length`; the cursor's two facts are established |
| E0, stats, stable | stated | refused, lacking the cursor's two facts and `prepared.widths.length <= segmentCount`; `segmentCount <= prepared.widths.length` is established |
| E0, stats, stable | **empty** | **verified** |

The stepper verifies under E0 in every row (observed). Read as attributions
(conjectured where a row differs from another in one edit only, observed
for the differences themselves):

1. The visitor's `values: any` removes the facts about the fresh cursor's
   field (form (a)): the last two rows differ in the effect alone.
2. The visitor's `spines: grow` removes the upper bound
   `|prepared.widths| <= segmentCount` and keeps the lower bound (form (b));
   the lower bound is *Tolerant frames*' (Grow) at a rigid path, (Rigid).
3. The two field writes to `stats`, a parameter the walker does not
   allocate, remove the facts about the fresh cursor's field, with no
   callback involved: rows 2 and 4 differ in them alone.
4. Without `@stable`, `segmentCount === prepared.widths.length` is lost at a
   step other than the visit, under the empty effect (row 4); the candidates
   are the stepper's call, whose inferred effect covers the handle's field
   locations though the stepper writes only `cursor`'s fields, and the write
   `cursor.segmentIndex = startSegmentIndex` (conjectured; not separated by
   a further run).

## 2. Every site in pretext's implementation

Each row is a function that holds a fact about a location across a call of a
callback, a visitor, or a function whose effect is stated or inferred wider
than the locations it can write. "Lost" names the locations whose facts the
call's effect covers. Source rows are observed from the files; "Result" is
`check` at `6837e821` with no edit (observed: `line-break.ts` above;
`check layout.ts walkLineRanges,layoutWithLines,measureLineStats,stepNextLine,layoutNextLine,layoutNextLineRange`,
all six verified; `check rich-inline.ts walkRichInlineLineRanges,measureRichInlineStats,layoutNextRichInlineLineRange,prepareRichInline`,
three verified and `prepareRichInline` refused at its first call of
`measureAnalysis`, line 212, on `analysis.flags.length <= analysis.starts.length`,
a precondition with no callback between). Every bound obligation in these
functions is rewritten, so a verified row shows that the rewrites hold, and
the P1 sites are the rewrites a restoration would reach (cited: the case
`bounds-pattern-visitor-refused`'s header counts 48 in the three
`line-break.ts` walkers and 2 in `prepareRichInline`).

### Form (a): a location the caller allocates (6 sites)

| Site | Lost locations | Allocated by | Can the callee reach them? | Result |
| --- | --- | --- | --- | --- |
| `walkPreparedLinesRaw`, `line-break.ts:296–319`: `onLine` (319), the stepper (316), `normalizePreparedLineStart` (298), `stats` writes (317–318) | `cursor.segmentIndex`, `cursor.graphemeIndex` | the walker, line 296 | `onLine`: no, it receives five numbers. The two helpers: yes, `cursor` is their argument, and they write only its fields (observed, `line-break.ts:255–288`, `1105–1182`) | verified, rewritten; refused once restored (§1) |
| `countSteppedLines`, `line-break.ts:398–420`: `normalizePreparedLineStart` (403), the stepper (406), `walkPreparedComplexLines` (410, `onLine` undefined, `stats` null) | `cursor`'s fields; facts about `segmentFlags`, a local read before the loop | the function, line 401 | yes, by argument; the callees write the cursor and nothing else of the caller's (conjectured for `walkPreparedComplexLines`, whose `onLine` is `undefined` here) | verified, rewritten (line 407) |
| `walkPreparedComplexLines`, `line-break.ts:469–1101`: `onLine` (1097), `normalizePreparedLineStart` (1099), `stats` writes (1093–1096) | `cursor`'s fields, across iterations | its caller (`walkPreparedLinesRaw` 296, `countSteppedLines` 401, `stepPreparedLineGeometryFromStart`'s callers) | `onLine`: no. The locals destructured from `prepared` at 477–488 are variables, kept by every effect | verified, rewritten (37 lines of its body carry `missing()`) |
| `stepNextLine`, `layout.ts:279–295` | `lineEnd`, `lineStart` fields between the two helper calls | `layoutNextLine` and `layoutNextLineRange`, `layout.ts:305–306`, `325–326` | yes, by argument | verified |
| `layoutNextRichInlineLineRange`, `rich-inline.ts:1213–1235` | `lineEnd`'s fields across `normalizePreparedLineStart` and `stepPreparedLineGeometryFromStart` | the function, line 1223 | yes, by argument | verified |
| `prepareRichInline`, `rich-inline.ts:363–370` | `own`'s arrays, read at `own.segmentFlags[i] ?? missing()` (370) after both helper calls (364) | `measureAnalysis`, its fresh result `own` (362); the cursor `start` (363) | the helpers receive `own` and `start` and write only `start` (conjectured from their source) | refused at line 212 (unrelated); the two P1 sites are rewritten |

The `stats` objects: `measureLineStats` (`layout.ts:261`) and
`measureRichInlineStats` (`rich-inline.ts:1376`) allocate `stats` and pass
it to `walkPreparedLinesRaw`, whose default (`line-break.ts:294`) allocates
one where the caller passes none. The walkers write its fields
(`line-break.ts:317–318`, `1093–1096`). It holds no bound; row 3 of §1
shows its writes removing the fresh cursor's facts.

### Form (b): a handle the callback may reach (5 sites)

| Site | Lost locations | Allocated by | Can the callee reach them? | Result |
| --- | --- | --- | --- | --- |
| `walkPreparedLinesRaw`, `line-break.ts:316` after `319` | `prepared.widths` (field), the spine of `widths`, the relation of `segmentFlags`'s and `widths`'s lengths | `prepare()` / `prepareWithSegments()` (`layout.ts:131`, `137`), or `prepareRichInline` | `onLine` from `walkLineRanges`: the user's callback, by a capture; from `layoutWithLines` (`layout.ts:338–349`): pretext's lambda captures the handle and reads `prepared.segments` through `createLayoutLine` | verified, rewritten; refused once restored (§1) |
| `walkPreparedComplexLines`, `line-break.ts:1099` after `1097` | the handle's fields and arrays, read again by `normalizePreparedLineStart(prepared, cursor)` | as above | as above | verified, rewritten |
| `walkLineRanges`, `layout.ts:237–255` | none held; passes the handle and its lambda to the walker | the user | the user's `onLine`, by a capture | verified |
| `walkRichInlineLineRanges`, `rich-inline.ts:1352–1367` | `flow`'s fields read by `createOnlyItemLine` / `createLine` inside the lambda after each step, and `flow.data` passed to the walker | `prepareRichInline` | the lambda captures `flow`; the user's `onLine` may capture the handle (`getInternalPreparedRichInline` returns its argument, line 178–180) | verified |
| `layoutWithLines`, `layout.ts:335–351` | the handle, read by its own lambda; `lines`, fresh, pushed by the lambda | the user; `lines` at 336 | the lambda reaches both by capture; its effect is `InternalLineVisitor`'s statement | verified |

The column "Can the callee reach them?" is the fork's. Under upstream's
types the user's `onLine` reaches each of these handles only at a branded
type (`PreparedText`, `PreparedRichInline`) or through read-only fields
(`PreparedTextWithSegments`), and pretext's own lambdas, which TScert
checks, reach them at their internal records (observed: `0d102a5`'s
declarations, §1 (b)). The user's callback then writes the handle only by
going outside its exported types; which assumption would say it does not is
an open question (§7).

### Calls whose stated effect exceeds what they write (1 site)

`measureAnalysis` (`prepare.ts:357–695`) allocates
`scriptRuns` (line 424) and calls `spaceSharesScriptRun` (501) and
`getUnspacedGraphemes` (520), stated
`Modifies<{ values: "any"; spines: "grow"; "runs.openBrackets[*]": "any" }, …>`
(lines 183, 222, 258), which write only `runs`' fields and the spine of
`runs.openBrackets` (conjectured from their source). The loop keeps the
lower bounds `to <= flags.length` and the like by stating the separations
`flags !== scriptRuns.openBrackets` in its invariant (lines 452–453).
Verified (observed: `check prepare.ts measureAnalysis`, 9 s). *Tolerant frames in practice*' P4
is the same pattern, whose separations at paths do not hold on the entry
edge in its smaller program (cited: §P4).

### Instances in TScert's own code

- `typeText` writes `state.printable`, and the guarded fields of `atom`,
  "parsed data `state` does not reach", are read into constants before it
  (cited: [source rewrites](../SOURCE-REWRITES.md), lines 1480–1495).
- `familyTable` avoids `snapshot.map(g => g.arm())`, since "establishing
  that this particular callback cannot reach the private snapshot requires
  information beyond its callable contract" (cited: the same, 3660–3675).
- `Gate`'s members: "Showing that a call whose footprint lets spines change
  beyond `grow` cannot reach a given local array" is deferred (cited:
  [method effects](method-effects.md), lines 284–292, D5).

## 3. What the API exposes

**Entries** (observed, `package.json` `exports`, the same at `0d102a5` and
`6837e821`): `.` (`dist/layout.js`, from `layout.ts`) and `./rich-inline`
(from `rich-inline.ts`).

**Exported functions taking a callback** (observed): `walkLineRanges`
(`layout.ts:237`; upstream `242`) and `walkRichInlineLineRanges`
(`rich-inline.ts:1352`; upstream `1241`). Upstream types each `onLine` as
`(line: …) => void` (`layout.ts:245`, `rich-inline.ts:1244`); the fork
states `Modifies<{ values: "any"; spines: "grow" }, void>`. No other
exported function takes a function (observed: a search of `src/` for
function-typed parameters finds these two and the internal
`InternalLineVisitor`). The handle each takes beside the callback:
`walkLineRanges` a `PreparedText`, `walkRichInlineLineRanges` a
`PreparedRichInline`.

**Handles a user holds, under upstream's types** (observed, `0d102a5`):

| Handle | Its exported type | Made by | Taken by |
| --- | --- | --- | --- |
| `PreparedText` | branded, `{ readonly [preparedTextBrand]: true }` (`layout.ts:44–46`) | `prepare` | `layout`, `walkLineRanges` (with `onLine`), `measureLineStats`, `measureNaturalWidth`, `layoutNextLineRange` |
| `PreparedTextWithSegments` | `PreparedText & { readonly segments; readonly kinds; readonly widths: ArrayLike<number> }` (`layout.ts:53–57`) | `prepareWithSegments` | the above, and `materializeLineRange`, `layoutNextLine`, `layoutWithLines` |
| `PreparedRichInline` | branded, `{ readonly [preparedRichInlineBrand]: true }` (`rich-inline.ts:81–83`) | `prepareRichInline` | `layoutNextRichInlineLineRange`, `materializeRichInlineLineRange`, `walkRichInlineLineRanges` (with `onLine`), `measureRichInlineStats` |

**A writable alias of a handle.** No exported function of `0d102a5`
returns a handle's array or record at a writable type: the results are
`LayoutResult`, `LineStats`, `RichInlineStats`, `number`, and
`LayoutLine`, `LayoutLineRange`, `LayoutLinesResult`, `RichInlineLine`,
`RichInlineLineRange`, whose fields are numbers, strings, and cursors and
fragments each function allocates (observed: the exported signatures,
`git show 0d102a5:src/layout.ts`, `…:src/rich-inline.ts`; that the cursors
and fragments are fresh, observed for `createLayoutLineRange`,
`layout.ts:195–212` at `6837e821`, and `createOnlyItemLine`,
`rich-inline.ts:1024–1035`; conjectured for `createLine`). The read-only
`widths` of `PreparedTextWithSegments` is the walkers' own array: upstream's
`prepareWithSegments` writes `prepared.kinds = kinds` and returns the
prepared record itself (observed: `git show 2b11a4c -- src/layout.ts`, its
removed lines). Pretext writes no handle's array after preparation
(conjectured). The callback's arguments hold no handle (observed, the same
functions). So under upstream's types the user's callback reaches a handle
only by capturing the value the user holds, at its exported type.

**Handles whose type exposes their representation** are, in the fork,
both: `PreparedText = PreparedLineData` (`layout.ts:43`) and
`PreparedRichInline = InternalPreparedRichInline` (`rich-inline.ts:79`,
fields `data`, `onlyItem`, `wholeWidth`, … at 132–170), and
`PreparedTextWithSegments` keeps `widths` writable through
`PreparedLineData` (observed). Upstream exposes no handle's representation
(above).

**The markers** (observed, fork only, both identical but for the function):

> contract on callers: onLine changes no typed array and shortens no array; it may change any value and grow any array. Assumed, not checked outside pretext.

It states the callback's closed footprint, `{ values: any, spines: grow }`.
It assumes the trust row "A caller outside the analyzed sources passes, for a
parameter of an exported function whose type states a callback's effect, a
function within that effect" (cited: [DESIGN.md](../DESIGN.md#trust-surface),
line 538). A conforming function "respects its contract across every future
heap, callback effects included" (cited: the same, line 570); its contract
is that footprint, which covers every location of the handle.

**What a user callback reaches** (conjectured, from the source): its
arguments, fresh per line and holding no handle (above); whatever it
captures, a handle the user holds included; and pretext's module state
through the exported functions it may call, among them `clearCache` and
`setLocale` (`layout.ts:355–367`) and the `textSources` `WeakMap`
(`rich-inline.ts:1259`). The marker allows it to change any value location
of all of these and grow any array, a handle's included, whether the
handle's type is the record (fork) or branded (upstream).

## 4. Other patterns of *Tolerant frames in practice* with shared structure

The parts: **(i)** a fact lost across a call or a write whose effect is
stated by kind of location rather than by what the step can reach;
**(ii)** an invariant of a handle or an object across calls; **(iii)**
ownership, freshness or confinement; **(iv)** a contract on callers.

- **P1** (Summary only): a visitor of unknown effect between reads; verifies
  once the visitor's type states `{ values: any; spines: grow }`, by (Grow).
  Shares (i) and (iv): the Summary says P1's effect "is assumed" of "a
  callback that the application passes to a public function". P22 is what
  blocks it in `line-break.ts`.
- **P2** (Summary only): growth by a known count across a callee. A
  postcondition carries the fact. Shares none.
- **P3**: a quantified fact over `widths` across `fragment.width = s`, a
  field of a fresh object. Shares (i) and (iii): "A quantified fact is kept
  across a write to a field of a fresh object"; *Tolerant frames*' Theorem "Tolerant
  frame" keeps it by the kinds (a field location is no element cell). §1
  row 3 is the same loss at a write to a parameter's field.
- **P4**: separations at paths across `measure(i, lists)`, stated
  `{ values: "any"; spines: "keep"; "p.widths[*]": "any" }`. Shares (i) and
  (iii): "a new array is apart from the arrays reached through fields of the
  variables in scope", Rule Alloc. Pretext's `measureAnalysis` (§2) is its
  site.
- **P5**: the contents of a generated table. Shares none: the fact comes
  from what the generator wrote.
- **P6**: a quantified fact across `touch(c)`, stated `{ values: "any" }`,
  which writes only `c.value`. Shares (i): "The effects a program can state
  name only `values`, `spines` and `p[*]`"; "For a callee that writes a field
  of an object it receives, neither paper has a rule". The stepper and
  `normalizePreparedLineStart`, which write only the cursor (§2), are callees
  of this shape.
- **P7**: facts over a local closure's captures. Shares (iii): what a
  function literal reaches is its parameters and its captures; "Facts about
  the variables a function literal captures are known at the literal's
  entry". The converse of P22: P7 needs the facts a closure's captures carry
  in, P22 the locations a callback's captures leave out.
- **P9, P10, P11, P12, P13, P17, P19, P21**: arithmetic, terms, string reads,
  relations of arrays, a paired index, indexed paths, sums, shifts. Share
  none (their entries name no call, write effect or handle; P13 and P17 pass
  objects to a callee, and the obligation is the callee's own).
- **P14**: length contracts of natives. Shares (iv) only as trust of external
  code: "Facts about code outside the analysed files" (Summary).
- **P15**: a module constant array's length. Shares (ii): "a fact about a
  module array that every step of every function keeps". A module binding is
  reachable by every function of the module, and no step writes the array.
- **P16**: a module cell initialised at first use. Shares (ii): "a fact about
  the contents of a module cell that every write to the cell keeps".
- **P18**: a type invariant of `Prepared` across `step(c)`, stated
  `{ values: "any" }`, which writes only `c.segment`. Shares (i) and (ii):
  "a guard read through two or more fields is kept by no step that changes
  the heap"; the extension is (Rigid), the fields being `@stable`.
- **P20**: a type invariant of a value read back from a `Map`. Shares (ii):
  "a rule that gives the type invariant of a value read from a `Map` when
  every write to that `Map` stores a value that meets the invariant".

## 5. The existing mechanisms that touch this

- **Stated effects** ([SOURCE-ELABORATION.md](../SOURCE-ELABORATION.md#stated-effects); cited).
  Gives: a closed footprint by class, `values` and `spines`, `onThrow`, a
  fresh result, and spine regions `"x[*]"`, `"x.f[*]"` on a function
  declaration's parameters. Falls short: a quoted key `"x.f"`, `"x.*"` is
  refused ("the regions it names are proved in the model … and are not read
  from the source"); a region on any signature but a function declaration's
  is refused (`invalid-modifies-region-callback`), so a callback type states
  only a class footprint. No form names "what the arguments reach".
- **Inferred effects** ([inferred call effects](../SOURCE-ELABORATION.md#inferred-call-effects-elaboration-and-certification),
  [the checked callback contract](../FOOTPRINTS.md#the-checked-callback-contract); cited).
  Gives: a per-exit summary proposed at the class level (`ClassSummary`),
  projected into a closed footprint and certified node by node. Falls short:
  the projection is closed, so a helper writing only its argument's fields
  is read at `values: any` (§1, attribution 4, conjectured).
- **Tolerant frames, the five kinds, support and respect**
  (*Tolerant frames* §§2, 5; [support and respect](../FOOTPRINTS.md#support-and-respect); cited).
  Gives: kinds F, C, E, S, I; class regions and regions at a path
  ($`\pi.f`$, $`\pi.\mathsf{fields}`$, $`\pi.\mathsf{cells}`$,
  $`\pi.\mathsf{spine}`$); a fact survives where each effect entry is within
  its support's change or disjoint from it. Falls short: a class region
  $`\mathsf{values}`$ overlaps every field location, so the cursor's field is
  covered; disjointness evidence is by kind, separation facts and freshness.
- **Fresh-Eff, Alloc and freshness marks** (*Tolerant frames*, rules Alloc and
  Fresh-Eff, Example "Freshness bounds effects, not facts";
  [fresh array storage](../FOOTPRINTS.md#fresh-array-storage); separation
  queries "by freshness", [separation queries](../FOOTPRINTS.md#separation-queries); cited).
  Gives: a body's changes to locations at or above its own mark are no part
  of its effect to its callers; $`\mathrm{fresh}(r)`$ is disjoint from any
  region below the mark. Falls short: the callback's entries are class
  regions, and the caller's fresh cursor lies below the callback's mark;
  *Tolerant frames* says freshness "does not put any fact under a modality".
- **Separation facts and allocation** ([separation facts](../PROGRAM-TYPING.md#separation-facts),
  [heap-freshness draft](heap-freshness.md); cited). Gives: "the field
  locations of two objects differ", stated at an allocation, read by writes.
  The rules `call-fresh` (a call allocating its result, `freshObject`, an
  intrinsic's declaration only) and `call-own` (a call changing only its
  receiver, `receiverFields`, the array iterator's step)
  ([PROGRAM-TYPING.md](../PROGRAM-TYPING.md), lines 4733–4790) keep facts
  about fields a separation fact keeps apart. Falls short: a code definition
  never states `freshObject`, and `call-own` applies to a receiver's fields,
  not to an argument's.
- **Argument-path spine regions and rebasing**
  ([argument-path spine regions](../FOOTPRINTS.md#argument-path-spine-regions),
  [deferred: extra precision](../FOOTPRINTS.md#deferred-extra-precision); cited).
  Gives: regions rooted at call positions and paths of `@stable` fields,
  composed by `Post.compose_at`, certified by the regional graph check; the
  deferred section names "footprints over regions rooted at a call's operands
  (`fields(x)`, `spine(x)`, `cells(x)`)" with "the regional lemmas proved".
  Falls short: "a field of a position's own value … and own locations,
  without a link, rebase to all"; regions are spines only in the source.
- **Type invariants and sealed handles**
  ([type invariants](../ARITHMETIC.md#type-invariants); cited). Gives: an
  invariant assumed of each value a body receives and established at each
  call and return; kept "between boundaries" by frame conditions. Falls
  short: a call with `values: any` keeps no invariant over fields of a
  non-`@stable` record (P18; `invalid-bounds-pattern-visitor-handle`), and
  the fork's handles state none. A sealed handle "means" its representation
  (rule `handle-meaning`), so its brand bounds no write: the probe of §1 (b)
  is refused at the opaque type as at the record. A brand with no
  `@representation` is refused at the cast out
  (`blocker-pretext-opaque-handle-cast`, a gap; observed, §1 (b)).
- **Footprints** ([FOOTPRINTS.md](../FOOTPRINTS.md); cited) is the mechanism
  [DESIGN.md](../DESIGN.md#general-mechanisms) names for "a fact a construct
  relies on while other code runs": the fact, its stable operations as closed
  footprints, the checked contract, the construct's rule. Its footprints are
  closed.
- **Contracts on callers and the trust surface**
  ([trust surface](../DESIGN.md#trust-surface), lines 537–539, 570, 573; cited).
  Gives: exported preconditions and type invariants, callbacks within their
  stated effect, sealed handles' representations, all assumed of callers
  outside the analysed sources; "External code preserves every
  effect-bearing contract of the program's values it holds", which names
  function fields, members and prototypes. Falls short: no row states that
  external code holding a program value at an opaque or read-only type
  writes none of its locations, nor that a callback leaves a handle's
  invariant or fields unchanged.
- **Effect variables** (*Tolerant frames*, Future work, "A callback that writes what
  it captured", and Limits, "Effects are closed"; cited): "A specification
  that gives each call the effect of its own callback needs an effect
  variable".
- **The draft "Keeping contract facts across calls"**
  ([keeping-contract-facts-across-calls.md](keeping-contract-facts-across-calls.md); cited)
  proposes write regions naming module cells, argument own locations and
  checked paths, and "Give `onLine` an explicit effect-qualified callback
  contract … admit captured output accumulation through certified separated
  regions".

## 6. Constraints any design must meet

From [CLAUDE.md](../../CLAUDE.md) (cited):

- **General statements**: a definition is stated over every expression,
  write, call and effect; a list of supported cases is a defect; a Lean
  notion and *Tolerant frames* state the same definition.
- **Designs start from an existing mechanism**: a draft opens with "The
  existing mechanism this extends", citing its owner; [footprints](../FOOTPRINTS.md)
  for a fact a construct relies on across code.
- **Never erase a contract**: annotation lowering represents the whole
  contract or refuses it; a native or external callback is audited for every
  callback it runs.
- **Trust stated**: a new assumption is a row of the trust surface, an
  external code assumption reviewed by the owner; standard-object
  non-tampering is approved by policy, any other kind goes to the owner.
- **The acceptance/soundness invariant**: an accepted verdict implies the
  modelled safety of every function of the unit, through
  `FunctionPlan.certify` and `SourceClaimJson.PassUnit.mode8Accepted_sound`;
  the front's proposals are untrusted until certified.
- **Annotation translation does not strengthen an ordinary arrow**; inferred
  effects need the definition's check before an application consumes them
  ([inferred call effects](../SOURCE-ELABORATION.md#inferred-call-effects-elaboration-and-certification)).

From the owner (cited: the coordinator's brief for this revision): a handle
meant to be encapsulated stays encapsulated, so the design does not solve a
problem the fork's rewrite created. Upstream's handles are branded or
read-only (§1 (b), §3); the fork's writable handle types come from
`2b11a4c`.

From *Tolerant frames* (cited): its subtitle and abstract, "fact preservation
without ownership": "TypeScript programs are not written against an
ownership discipline, and TScert imposes none". Assertions "describe the
whole heap. They can be duplicated, and holding one confers no permission to
write". Its relation to separation logic: "no separating conjunction and no
resource model".

## 7. Open questions

Form (b) under upstream's types is a question of encapsulation: the user's
callback holds the handle only at a branded or read-only type (§3). The
questions are those it raises, beside those of form (a).

1. What is the semantic notion of "a location a call can reach": the
   locations reachable through references from its callee value's
   captures, its receiver and arguments at the call, the module bindings its
   code names, and what it allocates? Does the model's (W3) "valid
   references" with (T3) give a theorem that a run reads and writes only
   locations so reachable, or allocated during it, and is that theorem in
   Lean?
2. For a callback passed as a parameter, whose captures are unknown, what
   bounds its reach over a location the caller allocated: its type, or the
   caller's knowledge that the location was allocated after the callback
   value existed and never published?
3. Which steps publish a location (a store into an older location, an
   argument, a capture, a return, a throw), and how is "never published"
   stated and checked along a graph, loops and handlers included?
4. Is the bound on the callee's side (an effect over what its inputs reach)
   or on the caller's side (a frame rule for locations the callee cannot
   reach), and how does it compose with Seq-Eff, rebasing and Fresh-Eff?
5. What must TScert support for upstream's opaque handles: a
   `unique symbol` brand, the identity cast out
   (`prepared as InternalPreparedText`), the cast in at preparation, the
   spread `{ ...prepared, segments, kinds }` at a type with a read-only
   `ArrayLike<number>` view, and a brand with no `@representation`
   (`blocker-pretext-opaque-handle-cast`)? Does a sealed handle, which means
   its representation, carry encapsulation at all, or does encapsulation need
   a reading in which the brand stands for locations external code does not
   write?
6. How is "external code honours an opaque or read-only type" stated: as a
   trust row beside lines 537–539, 570 and 573 of the
   [trust surface](../DESIGN.md#trust-surface), as a statement in *Tolerant frames*'
   model (a class of locations, a region, a part of the world, or a contract
   on the locations a brand covers), or both, with the Lean and the note
   stating one definition? Where is it checked of the program's own code
   (pretext's lambdas reach the handles at their internal records), and
   where only assumed of external code?
7. How does that statement meet the callback's stated effect: does a
   conforming function's footprint `{ values: any, spines: grow }` range over
   the handle's locations, or only over locations external code may write?
8. Should a field-only effect (P6), the freshness separation at a write to
   another object's field (§1, attribution 3; P3) and the guard through
   `@stable` fields (P18) be instances of the mechanism of form (a), or of
   the existing support and respect with more disjointness evidence?
9. How is the mechanism stated in *Tolerant frames*' language (regions, effects,
   supports), so that the Lean definition and the note's are one?
10. What does `Modifies` gain, if anything: a region form for callbacks,
    or none, the bound read from elsewhere?
11. Does the mechanism cover natives' callbacks (`map`, `forEachChild`) and
    pretext's own lambdas, which capture both the handle and the user's
    callback (`walkLineRanges`, `walkRichInlineLineRanges`)?
12. Does it subsume *Tolerant frames*' effect variables
    ($`\forall\varepsilon.\ \Phi\cup\varepsilon`$), or does each need the other?
13. Where does acceptance read it: which premise of `mode8Accepted_sound`,
    which certificate, and which controls (forged fragments, forced
    proposals) and Node-run negatives show its refusals?
14. What does it cost in the pass's time per call site, against the
    performance goal of no function over 1 s?
