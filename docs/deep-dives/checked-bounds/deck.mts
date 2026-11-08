/* The checked-bounds deep dive: how TScert checks array bounds with linear
 * arithmetic, inferred loop invariants, contracts at function and type
 * boundaries and frame conditions between them, all rechecked by a proved
 * checker; with its outcome on pretext and what remains. Branch
 * bound-annotations-opus, measured at 5701f1e9. Built with the deck kit
 * (`make deck NAME=checked-bounds`). */
import { bullets, card, cards, code, columns, cover, inline, panel, para, point, rules, slide, stat, statement, status, table, type Deck, type Slide } from "../../../dev/deck.mts";

/** Prose with `code` in backticks, as the kit's `inline` reads it. */
const t = inline;
/** The strength of a claim, in its status pair's colour (STYLE.md, "The voice"). */
const proved = status("ok", "proved"), measured = status("neutral", "measured"), trusted = status("trust", "trusted");
const proposed = status("gap", "proposed"), observed = status("neutral", "observed");


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
        point("Case study", t("pretext’s checked rewrite, verified by TScert, turns each bound into a run-time check: 376 checked reads, 55 guarded writes, 70 explicit `undefined` checks.")),
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
        point("Exact addition", t("`r = a + b` holds when the operands are safe integers and the known facts bound the sum within that range; there the double sum is exact.")),
        point("Terms", t("values, field paths `p.f.g`, array lengths (at most 2³² − 1) and typed-array lengths. A term is partial: where its path meets no object, it denotes nothing.")),
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
      ["Postcondition", status("gap", "partial") + ": result facts from native specifications and type invariants; no written postcondition syntax"],
      ["Type invariant", status("ok", "written") + t(" as `@invariant C` on a type; obligations at function boundaries")],
      ["Loop invariant", status("ok", "written") + t(" as `@invariant C` before a loop, or inferred; checked on every edge into the head")],
    ], [24, 76]) +
      para(t("Clauses are linear relations over values, field paths and lengths, under null guards, and quantified clauses `forall i in xs: B` over an array’s elements. A heap change preserves no quantified fact: a stated limit."), 26),
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
        point("Preservation", "across calls, keeping the equality needs a frame condition that protects the field references and the lengths."),
      ], 25),
    ], [46, 54]),
  }),
  slide("preservation", {
    label: "Frame conditions", note: t("the preservation rules ") + proved,
    title: "Mutations preserve facts through checked effects", gap: 22,
    body: para(t("A fact over the heap reads particular locations. TScert’s footprint mechanism, its frame conditions, checks whether an operation leaves those locations unchanged, or changes them in a way that preserves the inequality."), 26) +
      table(["Operation", "Preservation"], [
        ["Write a numeric field", "array lengths preserved; facts about that field restated from the written value"],
        [t("Write `xs[k]` below the length"), "the length preserved"],
        [t("`out.push(v)`"), t("lower bounds on `out.length` preserved; upper bounds dropped")],
        ["Call with a checked frame condition", "facts whose locations its frame protects"],
        ["Any step", t("a typed array’s length: fixed for its life (" + "trusted" + ")")],
      ], [38, 62]) +
      para("These rules concern normal returns; a throw carries a frame condition only where one is stated for it.", 24),
  }),
  slide("frame-cost", {
    label: "pretext · invariant verification", note: t("the bounds target with and without the invariants, at one TScert commit · ") + measured,
    title: "Coarse frame conditions prevent proving return obligations", gap: 22,
    body: columns([
      code(["// Schematic proof obligations", "// Entry:", "//   prepared.segmentFlags.length", "//     === prepared.widths.length", "callWithCoarseFrame()", "// The equality is no longer established;", "// it is required again at every normal return."]),
      bullets([
        point("Measured", t("length invariants on `PreparedLineBreakData`: 137 functions verified against 144 without them; 9 lost, 2 gained.")),
        point("Return obligation", "a parameter never reassigned must satisfy its invariant at every normal return."),
        point("Frame condition", "the calls may change field references, so the checker drops the equality even where array lengths are preserved."),
        point("Recorded calls", t("`Map.set` on module caches, `getEngineProfile`, `onLine` callbacks, measurement helpers.")),
        point("Default argument", t("`start = TEXT_START_CURSOR` receives no invariant precondition.")),
        point("Proposed", "more precise modifies clauses; proof obligations for supplied and default argument values."),
      ], 25),
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
    label: "pretext", note: t("measured at TScert `4775efde`, each stage limited to 300 s · ") + measured,
    title: "149 of 211 functions verified without bound checks", gap: 22,
    body: cards([
      stat("149 / 211", "shallow: each function’s own unit accepted, its callees read at their contracts.", "ok"),
      stat("130 / 211", "deep: every unit it depends on accepted too, module initialization included.", "ok"),
      stat("3 sites", "unsafe within pretext’s own contract, marked in the code as described exceptions.", "neg"),
    ], 3) +
      para(t("The target: pretext’s checked rewrite with its 501 bound checks reverted and arithmetic annotations added. The unsafe class (" + "observed" + " under Node): a line range kept from a longer text, materialized on a shorter one, reads past a segment’s graphemes; original pretext returns wrong text, or `NaN` offsets in rich inline text. No annotation makes it safe; the code needs an index check."), 25),
  }),
  slide("remains", {
    label: "Remaining obligations", note: `the 62 unverified functions, classed by their first refusal · estimates`,
    title: "Element bounds need more than a quantified clause", gap: 22,
    body: table(["Capability needed", "Functions"], [
      ["type invariants across calls with coarse frame conditions", "11"],
      ["element facts of typed arrays, whose writes the model does not track", "11"],
      ["generated tables: checked decoding, strides, bit arithmetic", "10"],
      [t("string lengths as terms (`text.codePointAt(i)!`)"), "6"],
      ["lengths of the elements of arrays of arrays", "3"],
      ["element writes; key-adding writes; facts at edges, cause unknown", "3; 2; 3"],
      ["other element and index reads, not yet classified", "13"],
    ], [80, 20]) +
      para(t("Quantified clauses gained one function: the other element-bound functions also write their arrays, and a heap change preserves no quantified fact. Keeping one across an element write is a design choice; extending it across `push` needs an append relation in that native contract, new trust."), 25),
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
