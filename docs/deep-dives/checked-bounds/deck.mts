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
    title: "From type safety to checked array bounds",
    text: t("TScert checks safety claims about TypeScript programs. Linear arithmetic over integers extends those claims to relations between indices and array lengths. An untrusted producer proposes invariants and certificates; a checker proved sound in Lean validates them under explicit assumptions. The case study is pretext, a text-layout library: which run-time bound checks can proofs replace, and which obligations remain?"),
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
    label: "Inference and certificates", note: t("producer ") + proposed + t(" · checker ") + proved,
    title: "Infer loop invariants; check every incoming edge", gap: 22,
    body: columns([
      code(["let s = 0", "for (let j = 0; j < xs.length; j++)", "  s = s + xs[j]!"]) +
        table(["Obligation", "Fact"], [
          ["Initialization", "j = 0"],
          ["Loop invariant", "j a safe integer, 0 ≤ j ≤ |xs|"],
          ["Body entry", "0 ≤ j < |xs|"],
          ["Back edge", "j + 1 ≤ |xs|; the increment is exact"],
        ], [40, 60]),
      bullets([
        point("Untrusted inference", "the producer proposes facts at each program point, loop invariants included."),
        point("Proved checking", "the checker validates establishment and preservation on every incoming edge."),
        point("Linear certificates", "each step is a nonnegative combination of known facts, rounded over the integers; ≠ with a bound gives a strict bound. Fourier–Motzkin elimination removes variables that go out of scope."),
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
      ["Type invariant", status("ok", "written") + t(" as `@invariant C`; obligations at function boundaries")],
      ["Loop invariant", status("gap", "inferred") + ": checked on incoming edges; no written loop-invariant syntax"],
    ], [24, 76]) +
      para(t("The clause language expresses scalar linear relations. Quantified bounds over array elements and written loop invariants are " + "proposed" + " extensions."), 26),
  }),
  slide("invariants", {
    label: "Type invariants", note: t("pretext’s handle type, annotated as in TScert’s regression case; the measured target does not use it · the boundary checks ") + proved,
    title: "Re-establish the invariant at function boundaries", gap: 22,
    body: columns([
      code(["/** @invariant this.segmentFlags.length", " *     === this.widths.length", " *  @representation PreparedLineBreakData */", "export type PreparedText = {", "  readonly [preparedTextBrand]: true", "}"]),
      bullets([
        point("Meaning", t("the symbol property brands an opaque handle; `@representation` names the record behind it.")),
        point("Entry and return", "callers establish parameter invariants; bodies establish result invariants, and restore those of parameters never reassigned."),
        point("Casts", "a cast into the handle checks the representation type; the invariant is checked at the boundary that requires it."),
        point("Between boundaries", "each fact needs a preservation argument (next slide)."),
      ], 26),
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
  slide("trust", {
    label: "Soundness and trust", title: "What an accepted certificate guarantees", gap: 20,
    body: columns([
      panel(`Proved in Lean: ${proved}`, para("Acceptance implies modeled safety for every function of the accepted unit, given its input types, entry facts, separation requirements and environment contracts; each normal return meets the checked result facts. Safety admits exceptions and divergence.", 26)) +
        panel(`Untrusted: ${proposed}`, para("The producer’s proposed types, invariants and certificates.", 26)),
      panel(`Trusted computing base: ${trusted}`, bullets([
        "Source and annotation translation; the model’s correspondence with JavaScript.",
        "Lean’s kernel and compiler, and the executed checker.",
        "Native contracts and the standard-object assumptions.",
        "External callers meeting exported contracts, a stand-in until applications are analyzed too.",
        "Typed arrays over fixed-size, never-detached buffers.",
      ], 26)),
    ], [50, 50]),
  }),
  slide("pretext", {
    label: "pretext", note: t("measured at TScert `5701f1e9`, each stage limited to 300 s · ") + measured,
    title: "148 of 211 functions verified without bound checks", gap: 22,
    body: cards([
      stat("148 / 211", "shallow: each function’s own unit accepted, its callees read at their contracts.", "ok"),
      stat("129 / 211", "deep: every unit it depends on accepted too, module initialization included.", "ok"),
      stat("3 sites", "unsafe within pretext’s own contract, marked in the code as described exceptions.", "neg"),
    ], 3) +
      para(t("The target: pretext’s checked rewrite with its 501 bound checks reverted and arithmetic annotations added. The unsafe class (" + "observed" + " under Node): a line range kept from a longer text, materialized on a shorter one, reads past a segment’s graphemes; original pretext returns wrong text, or `NaN` offsets in rich inline text. No annotation makes it safe; the code needs an index check."), 25),
  }),
  slide("remains", {
    label: "Remaining obligations", note: `by hand, over the 63 unverified functions · estimates`,
    title: "Element bounds are the largest gap", gap: 22,
    body: table(["Capability needed", "Functions, estimated"], [
      [t("quantified bounds over array elements: every `xs[i] ≤ ys.length`"), "about 25"],
      ["contract facts kept across calls and parameter defaults", "about 11"],
      ["string lengths as terms", "7"],
      ["indices from shifts and products (non-linear)", "7"],
      ["facts about library results", "4"],
      ["calls in loops; run-time keys; unclassified", "4; 2; 3"],
    ], [72, 28]) +
      para(t("The estimates overlap: they are not a partition of the 63. Element bounds, call frames and string lengths have " + "proposed" + " designs; their gains are not yet measured."), 25),
  }),
  statement("moral", {
    label: "The takeaway",
    title: "Contracts state the obligations at boundaries; certificates discharge them; frame conditions carry facts between.",
    text: "Where the checker accepts, a bound check becomes a proof, under the trust the deck states. Where no annotation can make code safe, the analysis reports the site.",
  }),
];

const deck: Deck = {
  title: "From type safety to checked facts",
  slides,
  sections: [
    { description: "The obligation an asserted read leaves.", start: "cover" },
    { description: "Linear arithmetic, inference and contracts.", start: "arithmetic" },
    { description: "Invariants and frame conditions.", start: "invariants" },
    { description: "Soundness, the outcome on pretext, what remains.", start: "trust" },
  ],
};
export default deck;
