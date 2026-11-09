/* The checked-bounds deep dive: how TScert checks array bounds with linear
 * arithmetic, inferred loop invariants, contracts at function and type
 * boundaries and frame conditions between them, all rechecked by a proved
 * checker; with its outcome on pretext and what remains. Measured at
 * TScert f868f344 and pretext tscert-bounds 86a93c0; chain 1's remaining
 * sites observed at TScert d36212f9 and pretext aaa11c50, with preconditions
 * and loop invariants added, on 2026-11-09. Built with the deck kit
 * (`make deck NAME=checked-bounds`).
 * Build: make deck NAME=checked-bounds SINCE=e0979e83. */
import { bullets, card, cards, code, columns, cover, inline, panel, para, point, rules, slide, stat, statement, status, table, type Deck, type Slide } from "../../../dev/deck.mts";

/** Prose with `code` in backticks, as the kit's `inline` reads it. */
const t = inline;
/** The strength of a claim, in its status pair's colour (STYLE.md, "The voice"). */
const proved = status("ok", "proved"), measured = status("neutral", "measured"), trusted = status("trust", "trusted");
const proposed = status("gap", "proposed"), observed = status("neutral", "observed"), cited = status("neutral", "cited");


const slides: Slide[] = [
  cover("cover", {
    label: "TScert · checked array bounds",
    title: "Proving array bounds in TypeScript",
    text: t("TScert checks safety claims about TypeScript programs. Integer linear arithmetic relates indices to array lengths. An untrusted producer proposes types and loop invariants; untrusted proof search constructs certificates; a checker proved sound in Lean validates them. Source translation and library contracts remain trusted. The case study is pretext, a text-layout library: which array-bound checks can verification discharge, and which proof obligations remain?"),
  }),
  slide("problem", {
    label: "The obligation", note: `Node 26.13.0 · ${observed}`,
    title: t("`number[]` and `number` do not establish a bound"), gap: 22,
    body: columns([
      code(["function at(xs: number[], i: number): number {", "  return xs[i]!", "}", "", "at([10, 20, 30], 1)    // 20", "at([10, 20, 30], 3)    // undefined", "at([10, 20, 30], 1.5)  // undefined"]),
      bullets([
        point("Assertion", t("`!` removes `undefined` from the static type; it performs no run-time check.")),
        point("Proof obligation", t("`i` is a safe integer and `0 ≤ i < xs.length`, under an array contract that makes the element present.")),
        point("Case study", t("pretext’s checked rewrite, verified by TScert, turns each of 501 bounds into a run-time check: a read `xs[i] ?? missing()`, where `missing` throws, a guarded write, or an explicit `undefined` test.")),
        point("Experiment", "replace those checks with assertions and contracts, and measure what verifies."),
      ], 26),
    ], [46, 54]),
  }),
  slide("arithmetic", {
    label: "Arithmetic model", note: t("the rules ") + proved + t(" against Lean’s model of IEEE doubles"),
    title: "Integer reasoning over exact JavaScript arithmetic", gap: 22,
    body: rules(["Σᵢ cᵢ·tᵢ ≤ d        Σᵢ cᵢ·tᵢ ≠ d        (cᵢ, d integers)"]) +
      bullets([
        point("Safe integers", t("a numeric term denotes an integer only within ±(2⁵³ − 1). Fractions, infinities and NaN denote nothing, so no fact about them holds.")),
        point("Exact addition", t("`r = a + b` holds when the operands are safe integers and the known facts bound the sum within that range; there the double sum is exact. A string’s length plus one may reach 2⁵³; a typed array built at that length throws, so one that is built has the exact sum.")),
        point("Terms", t("values, field paths `p.f.g`, array lengths (at most 2³² − 1) and typed-array lengths; a constant whose type is one integer literal denotes it. A term is partial: where its path meets no object, it denotes nothing.")),
        point("Branch facts", t("on safe integers `<` and `===` are integer order and equality: the true branch of `i < n` gives i ≤ n − 1, the false branch n ≤ i.")),
      ], 26),
  }),
  slide("inferred", {
    label: "Loop invariants and certificates", note: t("inference and proof search ") + proposed + t(" · checker ") + proved,
    title: "Check initialization and preservation of loop invariants", gap: 22,
    body: columns([
      code(["let s = 0", "for (let j = 0; j < xs.length; j++)", "  s = s + xs[j]!"]) +
        table(["Obligation", "Fact"], [
          ["Initialization", "j = 0"],
          ["Loop invariant", "j is a safe integer; 0 ≤ j ≤ xs.length"],
          ["Body entry", "0 ≤ j < xs.length"],
          ["Back edge", "j + 1 ≤ xs.length; the increment is exact"],
        ], [40, 60]),
      bullets([
        point("Inference", "the producer proposes types and facts at program points, loop invariants included."),
        point("Proof search", "untrusted search constructs certificates for the proposed claims."),
        point("Checking", "the checker validates initialization and preservation on every incoming edge."),
        point("Arithmetic", "certificates use nonnegative linear combinations, integer rounding and disequalities; search uses Fourier–Motzkin elimination."),
      ], 26),
    ], [46, 54]),
  }),
  slide("requires", {
    label: "Function contracts", note: t("schematic, after pretext’s `classifySegmentUnit` · the call rule ") + proved,
    title: "Callers establish the precondition", gap: 22,
    body: code(["/** @requires safeInteger(i) && 0 <= i && i + 1 < breaks.length */", "function nextFlag(breaks: Uint8Array, i: number): number {", "  return breaks[i + 1]!", "}"]) +
      bullets([
        point("Body", "verification assumes the precondition and proves the read in bounds."),
        point("Analyzed callers", "each call must establish the precondition of its evaluated arguments; a call that cannot is unverified."),
        point("Clause language", t("conjunctions of `safeInteger` and linear comparisons over parameters, field paths and lengths, optionally under null guards `p.f === null || …`. A clause runs no code.")),
        point("Trusted boundary", t("callers outside the analyzed sources are " + "trusted" + " to meet exported preconditions.")),
      ], 26),
  }),
  slide("kinds", {
    label: "Contract support", note: t("C is a clause of the shared language"),
    title: "Preconditions, postconditions and invariants", gap: 22,
    body: table(["Contract", "Support"], [
      ["Precondition", status("ok", "written") + t(" as `@requires C`; checked at analyzed calls, assumed by the body")],
      ["Postcondition", status("ok", "written") + t(" as `@ensures C`; checked at every normal return, held by the variable a call’s result is assigned to")],
      ["Type invariant", status("ok", "written") + t(" as `@invariant C` on a type; obligations at function boundaries")],
      ["Loop invariant", status("ok", "written") + t(" as `@invariant C` before a loop, or inferred; checked on every edge into the head")],
    ], [24, 76]) +
      para(t("Clauses are linear relations over values, field paths and lengths, under null guards; quantified clauses `forall i in xs: B` over an array’s elements; and `a !== b` of two arrays (slide 10). A heap change preserves no quantified fact: a stated limit."), 26),
  }),
  slide("invariants", {
    label: "Type invariants", note: t("an opaque-type regression example, after pretext’s handle · the boundary rules ") + proved,
    title: "Type invariants become preconditions and postconditions", gap: 22,
    body: columns([
      code(["/** @invariant this.segmentFlags.length", " *     === this.widths.length", " *  @representation PreparedLineBreakData */", "export type PreparedText = {", "  readonly [preparedTextBrand]: true", "}"]),
      bullets([
        point("Representation invariant", t("`PreparedText` is opaque; `@representation` names its underlying record. The invariant equates two array lengths.")),
        point("Precondition", "for a parameter without a default argument, callers establish the invariant and the body assumes it."),
        point("Postcondition", "every normal return establishes result invariants and restores those of parameters never reassigned."),
        point("Casts", "a cast checks the representation type; the invariant needs proof at a call or return."),
        point("Preservation", "across calls, keeping the equality needs a frame condition that protects the field references and the lengths (slide 8)."),
      ], 25),
    ], [46, 54]),
  }),
  slide("preservation", {
    label: "Frame conditions", note: t("the preservation rules ") + proved,
    title: "A fact survives a step that leaves its locations unchanged", gap: 22,
    body: para(t("A fact over the heap reads particular locations: fields, variables, array elements and lengths. An operation’s frame condition, its frame, bounds what it may change in each class of location: `values` (fields and variables) and `stores` (an array’s elements and length), each kept (`keep`), changed keeping every element present (`grow`), or changed freely (`any`). The producer proposes a function’s frame from its body and the checker certifies it; a signature may also state it (slide 10)."), 26) +
      table(["Operation", "Facts kept"], [
        ["Write a numeric field", "array lengths; facts about that field restated from the written value"],
        [t("Write `xs[k]` below the length"), "the length"],
        [t("`out.push(v)`"), t("lower bounds on `out.length`; the lengths of arrays older than a literal `out`")],
        ["Call", "the facts whose locations the callee’s frame keeps"],
        ["Any step", t("a typed array’s length: fixed for its life (" + "trusted" + ")")],
      ], [38, 62]) +
      para("These rules concern normal returns; a throw carries a frame only where one is stated for it.", 24),
  }),
  slide("frame-cost", {
    label: "pretext · invariants across calls", note: t("the owner’s measurement, ") + cited + t(" from the draft on keeping contract facts across calls · the frames for `??=` and `Map.set` ") + proved,
    title: "A coarse frame loses the facts a return must restore", gap: 22,
    body: columns([
      code(["// Schematic proof obligations", "// Entry:", "//   prepared.segmentFlags.length", "//     === prepared.widths.length", "callWithCoarseFrame()", "// The equality is no longer established;", "// it is required again at every normal return."]),
      bullets([
        point("Cited", t("with type invariants, a pretext target (`2b11a4c` without its bound rewrites) has 137 functions accepted, against 148 without them.")),
        point("Return obligation", "a parameter never reassigned must satisfy its invariant at every normal return."),
        point("Coarse frame", t("a call at `values: \"any\"` may replace the array a field holds, so the checker drops the equality even where every array keeps its length.")),
        point("Coarse calls", t("in that target: `Map.set` on module caches, `getEngineProfile`, `onLine` callbacks, measurement helpers.")),
        point("Finer frames", t("a call filling a cache by `??=`, and `Map.set`, keep every length and every field’s array (cases `lazy-cache-keeps-facts`, `map-insert-keeps-paths`); frames for callbacks and measurement helpers are ") + proposed + "."),
        point("Default argument", t("`start = TEXT_START_CURSOR` receives no invariant precondition; an obligation on default values is ") + proposed + "."),
      ], 24),
    ], [44, 56]),
  }),
  slide("argument-store", {
    label: "Frames naming one array", note: t("the case `stated-local-runs` · the rules ") + proved + t(" · their use in pretext ") + proposed,
    title: "A frame naming one array keeps the lengths of the others", gap: 22,
    body: columns([
      code(["type Runs = { /** @stable */", "  readonly openBrackets: number[] };", "", "function readRuns(runs: Runs): Modifies<", "    { values: \"any\";", "      \"runs.openBrackets[*]\": \"any\" }, void> {", "  runs.openBrackets.splice(0, 1);", "}", "", "export function measure(flags: number[]): number {", "  const runs: Runs = { openBrackets: [] };", "  let sum = 0;", "  for (let i = 0; i < flags.length; i++) {", "    readRuns(runs); sum += flags[i]!; }", "  return sum;", "}"]),
      bullets([
        point("Stated frame", t("`Modifies<P, T>`, read by TypeScript as `T`. `P` lets `readRuns` change any value and, through the region `\"runs.openBrackets[*]\"`, the array `runs.openBrackets` holds at the call; `stores` left out, every other array is kept. The checker certifies the body against `P`.")),
        point("@stable", t("a `readonly` field holding what its object literal put there for the record’s life: the region names one array across every call.")),
        point("Separation", t("the literal’s `[]` is a new array, so it is not `flags`: the loop keeps `i < flags.length` across each call, and `flags[i]!` is in bounds. A record from a caller needs the precondition `flags !== runs.openBrackets`: distinct arrays. Of typed arrays it is refused; two views may share a buffer.")),
        point("Alias", t("a caller passing one array as both is refused at that precondition; under Node that call returns `NaN` (`invalid-stated-alias`).")),
        point("pretext", t("`readScriptRuns` splices pretext’s `runs.openBrackets`, and `measureAnalysis` builds its `ScriptRuns` literal before its loop: this shape, no frame stated (slide 13).")),
      ], 24),
    ], [46, 54]),
  }),
  slide("trust", {
    label: "Soundness and trust", note: t("a conditional safety theorem ") + proved + t(" · explicit assumptions ") + trusted,
    title: "What certificate acceptance guarantees", gap: 20,
    body: columns([
      para("The Lean theorem connects acceptance to modeled safety for every function in the checked unit, assuming input types, preconditions, separation requirements and environment contracts. Normal returns satisfy the checked postconditions. Exceptions and divergence are permitted.", 26) +
        bullets([
          point("Untrusted inference", "the producer proposes types and loop invariants."),
          point("Untrusted proof search", "search constructs certificates from the proposed claims; the checker validates them."),
        ], 26),
      bullets([
        point("Trusted computing base", "source and annotation translation; correspondence with JavaScript; Lean’s kernel, compiler and executed checker."),
        point("Environment assumptions", "native contracts; standard-object behavior; external callers satisfying exported contracts; typed arrays backed by fixed-size buffers that are never detached."),
      ], 26),
    ], [50, 50]),
  }),
  slide("pretext", {
    label: "pretext", note: t("measured at TScert `f868f344`, pretext `tscert-bounds` `86a93c0` · ") + measured,
    title: "Bound checks leave pretext one chain at a time", gap: 22,
    body: cards([
      stat("210 / 210", "pretext functions verify on the rewrite as it stands.", "ok"),
      stat("54 / 501", "bound rewrites restored to pretext’s own reads; 447 remain.", "ok"),
      stat("7 / 67", t("restored in chain 1: `analyzeText` through `prepare.ts`."), "gap"),
    ], 3) +
      para(t("A chain is a function that builds a structure and every function reading it. Its rewrites are restored together, each read replaced by an assertion and the contracts that prove it in bounds, and every pretext function keeps verifying. In chain 1, `analyzeText` and `segmentAtLineBreaks` state that `texts`, `starts` and `flags` have one length."), 25) +
      para(t("One class stays checked (" + "observed" + " under Node): a line range kept from a longer text, materialized on a shorter one, reads past a segment’s graphemes; original pretext returns wrong text, or `NaN` offsets in rich inline text. No annotation makes it safe; the code needs an index check."), 25),
  }),
  slide("remains", {
    label: "Remaining obligations", note: t("TScert `d36212f9`, pretext `aaa11c50` with preconditions and loop invariants added, 2026-11-09 · ") + observed + t(" · the capabilities ") + proposed,
    title: "What the remaining reads of chain 1 need", gap: 22,
    body: para(t("With preconditions and loop invariants written and no frame stated, restoring a site verifies 6 of the 26 in `measureAnalysis`’s helpers inside their own functions: 3 in `getFollowingSpaceTail`, 3 in `getJoinedNarrowing`. The other 20 are refused at a typing claim or a loop head, causes not established. `measureAnalysis` (33 sites) is refused with none restored, at its call of `addIdeographicSpaceHangs` after its loop."), 25) +
      table(["Capability needed", "Where chain 1 needs it"], [
        [t("the frame of slide 10 on `readScriptRuns`, and on the two functions passing their `runs` on to it: a region passed on to another function’s region is outside what the checker certifies"), t("`measureAnalysis`, whose loop calls `spaceSharesScriptRun` and `getUnspacedGraphemes`, each calling `readScriptRuns`")],
        [t("string lengths of `replace` and `slice` results: library contracts, an assumption about the standard library for the owner to decide (") + trusted + ")", t("`mapSourceLineBreaks` and `segmentAtLineBreaks`’ break reads, which need `breaks.length >= normalized.length + 1`")],
        [t("a string’s element read below its length, typed as a string"), t("`normalized[i]!`")],
      ], [52, 48]),
  }),
  statement("moral", {
    label: "The takeaway",
    title: "Contracts state the obligations at boundaries; certificates discharge them; frame conditions carry facts between.",
    text: "Where the checker accepts, a bound check becomes a proof, under the trust the deck states. Where no annotation can make code safe, the analysis reports the site.",
  }),
];

const deck: Deck = {
  title: "Proving array bounds in TypeScript",
  slides,
  sections: [
    { description: "The obligation an asserted read leaves.", start: "cover" },
    { description: "Linear arithmetic, inference and contracts.", start: "arithmetic" },
    { description: "Invariants and frame conditions.", start: "invariants" },
    { description: "Soundness, the outcome on pretext, what remains.", start: "trust" },
  ],
};
export default deck;
