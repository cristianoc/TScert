/* The checked-bounds deep dive: how TScert checks array bounds with linear
 * arithmetic, inferred loop invariants, contracts at function and type
 * boundaries and frame conditions between them, all rechecked by a proved
 * checker; with its outcome on pretext and what remains. Measured at
 * TScert 787770a1 and pretext tscert-bounds ba09794f; the optional-callback
 * verdicts observed at TScert 0a5e9cab on 2026-11-10; the string reads chain 1
 * needs observed at TScert d36212f9 and pretext aaa11c50 on 2026-11-09;
 * the coarse-frame measurement cited from its draft. Built with the deck kit
 * (`make deck NAME=checked-bounds`).
 * Build: make deck NAME=checked-bounds SINCE=e0979e83. */
import { bullets, card, cards, code, columns, cover, esc, inline, panel, para, point, rules, slide, stat, statement, status, table, type Deck, type Slide } from "../../../dev/deck.mts";
import { LIGHT as K } from "../../../dev/style-tokens.mts";

/** Prose with `code` in backticks, as the kit's `inline` reads it. */
const t = inline;
/** The strength of a claim, in its status pair's colour (STYLE.md, "The voice"). */
const proved = status("ok", "proved"), measured = status("neutral", "measured"), trusted = status("trust", "trusted");
const proposed = status("gap", "proposed"), observed = status("neutral", "observed"), cited = status("neutral", "cited");
const open = status("gap", "open");


/* Heap pictures: inline SVG in the shared colours. An array store is a row
 * of cells (STYLE.md, "Roles": a value is `--neutral`); a store a step may
 * change freely sits in a dashed `--neg` region; a cell a growing step may
 * add is dashed `--ok`; a fact kept is `--ok`, a fact lost `--neg`. Labels
 * are in the code typeface at 26 px, captions in the text typeface. */
const MONO_F = "'Source Code Pro', Menlo, monospace", SANS_F = "Inter, 'Helvetica Neue', Arial, sans-serif";
/** Text: runs of [text, colour], in the code typeface unless `sans`. */
const label = (x: number, y: number, runs: [string, string][], o: { sans?: boolean; size?: number; anchor?: string; bold?: boolean } = {}): string =>
  `<text x="${x}" y="${y}" font-family="${o.sans ? SANS_F : MONO_F}" font-size="${o.size ?? 26}" text-anchor="${o.anchor ?? "start"}"${o.bold ? ' font-weight="600"' : ""}>` +
  runs.map(([t, c]) => `<tspan fill="${c}">${esc(t)}</tspan>`).join("") + `</text>`;
const ink = (x: number, y: number, t: string, o: { sans?: boolean; size?: number; anchor?: string; bold?: boolean; fill?: string } = {}): string =>
  label(x, y, [[t, o.fill ?? K.ink]], o);
/** A store's cells from x: `n` cells, of which those from `added` on are a
 * growth's dashed new cells, each `fill` coloured. */
const cells = (x: number, y: number, n: number, o: { added?: number; fill?: string; w?: number; h?: number } = {}): string => {
  const w = o.w ?? 52, h = o.h ?? 44;
  return Array.from({ length: n }, (_, i) => {
    const isNew = o.added !== undefined && i >= o.added;
    return `<rect x="${x + i * w}" y="${y}" width="${w}" height="${h}" fill="${isNew ? K["ok-bg"] : o.fill ?? K["neutral-bg"]}" stroke="${isNew ? K.ok : K.neutral}" stroke-width="2"${isNew ? ' stroke-dasharray="6 4"' : ""}/>`;
  }).join("");
};
const arrow = (x1: number, y1: number, x2: number, y2: number): string => {
  const a = Math.atan2(y2 - y1, x2 - x1), l = 14, s = 0.45;
  const p = (r: number, d: number): string => `${x2 - l * Math.cos(a + d * s) * r},${y2 - l * Math.sin(a + d * s) * r}`;
  return `<line x1="${x1}" y1="${y1}" x2="${x2 - 10 * Math.cos(a)}" y2="${y2 - 10 * Math.sin(a)}" stroke="${K.ink}" stroke-width="3"/>` +
    `<polygon points="${x2},${y2} ${p(1, 1)} ${p(1, -1)}" fill="${K.ink}"/>`;
};
const box = (x: number, y: number, w: number, h: number, o: { fill?: string; stroke?: string; dash?: boolean; r?: number } = {}): string =>
  `<rect x="${x}" y="${y}" width="${w}" height="${h}" rx="${o.r ?? 12}" fill="${o.fill ?? "none"}" stroke="${o.stroke ?? K.rule}" stroke-width="${o.dash ? 3 : 2}"${o.dash ? ' stroke-dasharray="10 6"' : ""}/>`;
/** Two panels side by side, each with its heading. */
const panels = (h: number, a: [string, string], b: [string, string]): string =>
  `<svg width="1664" height="${h}" viewBox="0 0 1664 ${h}" xmlns="http://www.w3.org/2000/svg">` +
  [a, b].map(([head, body], i) => box(i * 852, 0, 812, h, { fill: K.surface, r: 16 }) + ink(i * 852 + 32, 46, head, { sans: true, size: 28, bold: true }) + body).join("") + `</svg>`;
/** A record holding a `@stable` field that points to a store. */
const record = (ox: number, y: number, name: string, field: string): string =>
  box(ox + 32, y, 340, 96, { fill: K["neutral-bg"], stroke: K.neutral }) + ink(ox + 50, y + 38, name, { bold: true }) +
  label(ox + 50, y + 78, [[field, K.ink], [" @stable", K.muted]]);

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
    label: "Candidates, loop invariants and certificates", note: t("inference and proof search ") + proposed + t(" · checker ") + proved,
    title: "Keep the candidate facts every incoming edge establishes", gap: 22,
    body: columns([
      code(["let s = 0", "for (let j = 0; j < xs.length; j++)", "  s = s + xs[j]!"]) +
        table(["Obligation", "Fact"], [
          ["Initialization", "j = 0"],
          ["Loop invariant", "j is a safe integer; 0 ≤ j ≤ xs.length"],
          ["Body entry", "0 ≤ j < xs.length"],
          ["Back edge", "j + 1 ≤ xs.length; the increment is exact"],
        ], [40, 60]),
      bullets([
        point("Candidates", "the producer proposes types, and at each statement entry candidate facts: bounds, linear facts and facts that two arrays are distinct (slide 10), a loop head’s invariant among them."),
        point("Proof search", "untrusted search keeps at each entry the candidates every edge into it establishes, an edge being one step of control flow that reaches the entry: it drops each candidate an edge does not establish and searches again, at most once per candidate, and constructs certificates."),
        point("Checking", t("the checker validates each entry’s facts on every incoming edge, and that they include the entry’s required facts: its bindings’ types and contents, and a written `@invariant`.")),
        point("Arithmetic", "certificates use nonnegative linear combinations, integer rounding and disequalities; search uses Fourier–Motzkin elimination."),
        point("Diagnostics", "a refused function lists where the producer’s proposal drops a fact and what dropped it (a statement’s change, a call’s frame, slide 8), and each candidate the search left out, with the edge that does not establish it."),
      ], 24),
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
      ["Loop invariant", status("ok", "written") + t(" as `@invariant C` before a loop, required on every edge into the head; or inferred, a candidate kept where every such edge establishes it")],
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
    body: para(t("A fact over the heap reads particular locations: fields, variables, array elements and lengths. An operation’s frame condition, its frame, bounds what it may change in each class of location: `values` (fields and variables) and `stores` (an array’s elements and length), each kept (`keep`), changed keeping every element present and the array no shorter (`grow`), or changed freely (`any`). The producer proposes a function’s frame from its body and the checker certifies it; a signature may also state it (slide 10)."), 26) +
      table(["Operation", "Facts kept"], [
        ["Write a numeric field", "array lengths; facts about that field restated from the written value"],
        [t("Write `xs[k]` below the length"), "the length"],
        [t("Write `xs[k]` at any index"), "lower bounds of every length (slide 12)"],
        [t("`out.push(v)`"), t("lower bounds on `out.length`; the lengths of arrays older than a literal `out`")],
        ["Call", t("the facts whose locations the callee’s frame keeps; at `stores: \"grow\"`, lower bounds of lengths")],
        ["Any step", t("a typed array’s length: fixed for its life (" + "trusted" + ")")],
      ], [38, 62]) +
      para("These rules concern normal returns; a throw carries a frame only where one is stated for it.", 24),
  }),
  slide("frame-cost", {
    label: "pretext · invariants across calls", note: t("a measurement ") + cited + t(" from the draft on keeping contract facts across calls · the frames for `??=` and `Map.set` ") + proved,
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
    label: "Frames naming one array", note: t("the case `stated-local-runs` · the rules ") + proved + t(" · in pretext ") + observed,
    title: "A frame naming one array keeps the lengths of the others", gap: 22,
    body: columns([
      code(["type Runs = { /** @stable */", "  readonly openBrackets: number[] };", "", "function readRuns(runs: Runs): Modifies<", "    { values: \"any\";", "      \"runs.openBrackets[*]\": \"any\" }, void> {", "  runs.openBrackets.splice(0, 1);", "}", "", "export function measure(flags: number[]): number {", "  const runs: Runs = { openBrackets: [] };", "  let sum = 0;", "  for (let i = 0; i < flags.length; i++) {", "    readRuns(runs); sum += flags[i]!; }", "  return sum;", "}"]),
      bullets([
        point("Stated frame", t("`Modifies<P, T>`, read by TypeScript as `T`. `P` lets `readRuns` change any value and, through the region `\"runs.openBrackets[*]\"`, the array `runs.openBrackets` holds at the call; `stores` left out, every other array is kept. The checker certifies the body against `P`.")),
        point("@stable", t("a `readonly` field holding what its object literal put there for the record’s life: the region names one array across every call.")),
        point("Separation", t("the literal’s `[]` is a new array, so it is not `flags`: the loop keeps `i < flags.length` across each call, and `flags[i]!` is in bounds. A record from a caller needs the precondition `flags !== runs.openBrackets`: distinct arrays. Of typed arrays it is refused; two views may share a buffer.")),
        point("Alias", t("a caller passing one array as both is refused at that precondition; under Node that call returns `NaN` (`invalid-stated-alias`).")),
        point("In pretext", t("a helper splices a bracket stack held by a record that its caller builds before a loop over other arrays: this shape.")),
      ], 24),
    ], [46, 54]),
  }),
  slide("one-array-heap", {
    label: "Frames naming one array · the heap", note: t("the frame of `readRuns` on slide 10 · the rules ") + proved,
    title: "The region changes freely; every other store is kept", gap: 22,
    body: panels(400, ["At the call readRuns(runs)", (() => {
      const o = 0;
      return ink(o + 32, 126, "flags") + cells(o + 140, 94, 5) + ink(o + 420, 126, "length 5", { fill: K.muted }) +
        record(o, 196, "runs", "openBrackets") + arrow(o + 372, 270, o + 478, 270) + cells(o + 480, 248, 3) +
        box(o + 464, 228, 188, 84, { stroke: K.neg, dash: true, r: 8 }) + ink(o + 464, 216, "region: any change", { fill: K.neg, size: 24 }) +
        label(o + 32, 366, [["i < flags.length", K.neutral]]);
    })()], ["After the call", (() => {
      const o = 852;
      return ink(o + 32, 126, "flags") + cells(o + 140, 94, 5) + ink(o + 420, 126, "length 5, kept", { fill: K.ok }) +
        record(o, 196, "runs", "openBrackets") + arrow(o + 372, 270, o + 478, 270) + cells(o + 480, 248, 2, { fill: K["principled-bg"] }) +
        box(o + 464, 228, 188, 84, { stroke: K.neg, dash: true, r: 8 }) + ink(o + 464, 216, "spliced: shorter", { fill: K.neg, size: 24 }) +
        label(o + 32, 366, [["i < flags.length", K.ok], ["  kept", K.ok]]);
    })()]) +
      para(t("A store is an array’s elements and length. The frame names the store `runs.openBrackets` holds at the call; `@stable` fixes which store that is. `flags !== runs.openBrackets` places `flags` outside the region, and the frame keeps every store outside it, so `i < flags.length` holds after the call."), 26),
  }),
  slide("growth", {
    label: "Growth", note: t("the cases `stated-grow-keeps-lengths`, `invalid-stated-grow-upper-bound` · the rules ") + proved + t(" · native contracts ") + trusted,
    title: "Growth keeps the lower bounds of lengths", gap: 22,
    body: columns([
      code(["function add(xs: number[]): Modifies<", "    { values: \"any\"; stores: \"grow\" }, void> {", "  xs.push(1);", "}", "", "/** @requires safeInteger(i) && 0 <= i", " *    && i < xs.length */", "export function get(xs: number[], i: number): number {", "  add(xs);", "  return xs[i]!;      // verified", "}"]),
      bullets([
        point("Growth", t("`stores: \"grow\"` states that every array keeps each element present and gets no shorter, within the maximum length 2³² − 1.")),
        point("Lower bound", t("`i < xs.length`, read i − xs.length ≤ −1: a fact whose length terms all have coefficients ≤ 0. Growth keeps it.")),
        point("Upper bound", t("`xs.length <= ys.length` is dropped: `add(xs)` may lengthen `xs` (slide 13).")),
        point("Where it applies", t("a call stated `stores: \"grow\"`; `push`; an element write `out[j] = v` at any index.")),
        point("Natives", t("a native contract at `store: grow` (`push`, `sort`, a typed array’s `fill`) also states that its arrays get no shorter: ") + trusted + t(", argued from ECMA-262.")),
      ], 26),
    ], [52, 48]),
  }),
  slide("growth-heap", {
    label: "Growth · the heap", note: t("`add(xs)` of slide 12, stated `stores: \"grow\"` · the rules ") + proved,
    title: "A store that grows keeps lower bounds and loses upper ones", gap: 22,
    body: panels(440, ["Lower bound: kept", (() => {
      const o = 0, mark = (y: number): string => `<rect x="${o + 92 + 2 * 52}" y="${y - 48}" width="52" height="44" fill="${K["principled-bg"]}" stroke="${K.neutral}" stroke-width="2"/>` + ink(o + 222, y + 30, "xs[i]", { anchor: "middle" });
      return ink(o + 32, 90, "before", { sans: true, fill: K.muted }) + ink(o + 32, 140, "xs") + cells(o + 92, 108, 4) + ink(o + 316, 140, "length 4", { fill: K.muted }) + mark(156) +
        ink(o + 32, 260, "after add(xs)", { sans: true, fill: K.muted }) + ink(o + 32, 310, "xs") + cells(o + 92, 278, 5, { added: 4 }) + ink(o + 368, 310, "length 5", { fill: K.muted }) + mark(326) +
        label(o + 32, 412, [["i < xs.length", K.ok], ["  holds before and after", K.ok]]);
    })()], ["Upper bound: lost", (() => {
      const o = 852, end = o + 92 + 4 * 52;
      return ink(o + 32, 90, "before", { sans: true, fill: K.muted }) + ink(o + 32, 140, "xs") + cells(o + 92, 108, 4) + ink(o + 32, 192, "ys") + cells(o + 92, 160, 4) +
        ink(o + 420, 166, "4 <= 4", { fill: K.muted }) +
        ink(o + 32, 260, "after add(xs)", { sans: true, fill: K.muted }) + ink(o + 32, 310, "xs") + cells(o + 92, 278, 5, { added: 4 }) + ink(o + 32, 362, "ys") + cells(o + 92, 330, 4) +
        `<line x1="${end}" y1="270" x2="${end}" y2="384" stroke="${K.neg}" stroke-width="3" stroke-dasharray="8 5"/>` + ink(o + 420, 336, "5 <= 4 fails", { fill: K.neg }) +
        label(o + 32, 412, [["xs.length <= ys.length", K.neg], ["  lost", K.neg]]);
    })()]) +
      para(t("A growing step leaves the store no shorter: `i` stays below the length, and the length may pass any bound above it."), 26),
  }),
  slide("separation", {
    label: "Separation across calls", note: t("after the case `stated-region-nullable-apart` · the rules ") + proved + t(" · in pretext ") + observed,
    title: "A guarded separation keeps a length across a regional call", gap: 22,
    body: columns([
      code(["type Runs = { /** @stable */ readonly open: number[] };", "function step(runs: Runs | null, out: number[]):", "    Modifies<{ values: \"any\"; stores: \"grow\";", "      \"runs.open[*]\": \"any\" }, void> {", "  if (runs !== null) runs.open.pop(); out.push(1);", "}", "/** @requires safeInteger(to) && 0 <= to && to <= xs.length */", "export function f(xs: number[], out: number[],", "    to: number, use: boolean): number {", "  const runs: Runs = { open: [] };", "  const chosen = use ? runs : null;", "  let s = 0;", "  /** @invariant safeInteger(i) && safeInteger(to) && 0 <= i", "   *    && to <= xs.length", "   *  @invariant chosen === null || xs !== chosen.open */", "  for (let i = 0; i < to; i++) {", "    step(chosen, out); s += xs[i]!; }", "  return s;", "}"]),
      bullets([
        point("Regional growth", t("`step` may change the array `runs.open` holds, its region, and may grow every other array: a lower bound of the length of an array apart from the region survives the call.")),
        point("Guarded separation", t("`chosen === null || xs !== chosen.open`: where `chosen` is `null` the region selects no array, elsewhere `xs` is another array, so `to <= xs.length` survives `step(chosen, out)`. The producer proposes separations through copies, conditional declarations and joins of control flow; the checker checks each on every edge.")),
        point("Writes", t("a separation read through a `@stable` field also survives element and field writes: the field holds its array for the record’s life.")),
        point("In pretext", t("a measuring loop passes its record or `null` to a helper stating such a region; its loop invariant states this guarded separation.")),
      ], 24),
    ], [60, 40]),
  }),
  slide("separation-heap", {
    label: "Separation across calls · the heap", note: t("`step(chosen, out)` of slide 14 · the rules ") + proved,
    title: "Either way, xs lies outside the region", gap: 22,
    body: panels(470, ["chosen holds runs", (() => {
      const o = 0;
      return ink(o + 32, 122, "xs") + cells(o + 92, 90, 5) + cells(o + 352, 90, 1, { added: 0 }) + ink(o + 430, 122, "outside: at most grows", { fill: K.ok, size: 24 }) +
        record(o, 186, "runs", "open") + arrow(o + 372, 258, o + 478, 258) + cells(o + 480, 236, 3) +
        box(o + 464, 216, 188, 84, { stroke: K.neg, dash: true, r: 8 }) + ink(o + 464, 204, "region: any change", { fill: K.neg, size: 24 }) +
        ink(o + 32, 340, "chosen") + arrow(o + 140, 330, o + 200, 284) +
        label(o + 32, 404, [["chosen === null || ", K.muted], ["xs !== chosen.open", K.ok]]) +
        label(o + 32, 446, [["to <= xs.length", K.ok], ["  kept", K.ok]]);
    })()], ["chosen is null", (() => {
      const o = 852;
      return ink(o + 32, 122, "xs") + cells(o + 92, 90, 5) + cells(o + 352, 90, 1, { added: 0 }) + ink(o + 430, 122, "outside: at most grows", { fill: K.ok, size: 24 }) +
        record(o, 186, "runs", "open") + arrow(o + 372, 258, o + 478, 258) + cells(o + 480, 236, 3) + cells(o + 636, 236, 1, { added: 0 }) +
        ink(o + 32, 340, "chosen = null") + ink(o + 300, 340, "the region selects no store", { fill: K.muted, size: 24 }) +
        label(o + 32, 404, [["chosen === null", K.ok], [" || xs !== chosen.open", K.muted]]) +
        label(o + 32, 446, [["to <= xs.length", K.ok], ["  kept", K.ok]]);
    })()]) +
      para(t("The guarded separation holds in both cases by a different disjunct, and in both `xs` is a store the frame lets only grow."), 26),
  }),
  slide("trust", {
    label: "Soundness and trust", note: t("a conditional safety theorem ") + proved + t(" · explicit assumptions ") + trusted,
    title: "What certificate acceptance guarantees", gap: 20,
    body: columns([
      para("The Lean theorem connects acceptance to modeled safety for every function the checker accepts, assuming input types, preconditions, separation requirements and environment contracts. Normal returns satisfy the checked postconditions. Exceptions and divergence are permitted.", 26) +
        bullets([
          point("Untrusted inference", "the producer proposes types, loop invariants and candidate facts."),
          point("Untrusted proof search", "search constructs certificates from the proposed claims; the checker validates them."),
        ], 24),
      bullets([
        point("What acceptance states", t("the program meets each statement entry’s required facts (its bindings’ types and contents, a written `@invariant`) and every precondition, postcondition, stated frame and expression claim. A fact the producer supplies at an entry is a candidate, outside what acceptance states.")),
        point("Trusted computing base", "source and annotation translation; correspondence with JavaScript; Lean’s kernel, compiler and executed checker."),
        point("Environment assumptions", t("native contracts, a native stated at `store: grow` leaving every array no shorter; standard-object behavior; external callers satisfying exported contracts; typed arrays backed by fixed-size buffers that are never detached.")),
      ], 24),
    ], [50, 50]),
  }),
  slide("pretext", {
    label: "pretext", note: t("measured at TScert `787770a1`, pretext `tscert-bounds` `ba09794f` · ") + measured,
    title: "Bound checks leave pretext one chain at a time", gap: 22,
    body: cards([
      stat("12 / 12", t("source files outside `src/generated` have every function verified on the rewrite as it stands. The two generated data files do not: one is refused before proof search, one exceeds the time limit."), "ok"),
      stat("66 / 501", "run-time bound checks replaced by pretext’s own reads, each proved in bounds; 436 checks remain.", "ok"),
      stat("1", "check added, where no rule yet carries a fact across a call (slide 19).", "gap"),
    ], 3) +
      para(t("A chain is a function that builds a structure and every function reading it. Its rewrites are restored together, each read replaced by an assertion and the contracts that prove it in bounds, and every function that verified keeps verifying. In the first chain, the functions that segment a text state that its three segment arrays have one length, and the function measuring a range of segments requires the range’s end at most each length: lower bounds, which growth keeps."), 25) +
      para(t("One class stays checked (" + "observed" + " under Node): a line range kept from a longer text, materialized on a shorter one, reads past a segment’s graphemes; original pretext returns wrong text, or `NaN` offsets in rich inline text. No annotation makes it safe; the code needs an index check."), 25),
  }),
  slide("remains", {
    label: "Remaining obligations", note: t("each seen in pretext at `ba09794f`, TScert `787770a1` · ") + observed + t(" · each capability ") + open,
    title: "Facts no rule carries yet", gap: 22,
    body: table(["A read needs", "Why no rule carries it"], [
      [t("a fact kept across a call of a function with an optional callback that the call does not pass"), t("a function has one frame for every call, and an unknown callback may change any array (slide 19)")],
      [t("an upper bound of a length kept across a call, such as `a.length <= b.length`"), t("growth keeps lower bounds only (slide 13); keeping an upper bound needs a frame stating that the array is unchanged")],
      [t("a fact known only through a Boolean binding: `i > lo` through `const inside = i > lo && …`, tested later"), t("a test of a binding gives facts about that binding, not about the comparison it was computed from")],
      [t("the length of a string a library function returns, such as `replace` or `slice`"), t("a library contract: an assumption about the standard library, ") + trusted + t(" once stated")],
      [t("a string’s element read below its length, typed as a string"), t("no rule types a string’s element read by its bound yet")],
    ], [50, 50], { compact: true }),
  }),
  slide("visitor", {
    label: "Optional callbacks", note: t("three variants ") + observed + t(" at TScert `7b6e476a`, 2026-11-10 · a frame that depends on the callback ") + open,
    title: "A callback left out still costs the call its frame", gap: 22,
    body: columns([
      code(["type Visitor = (i: number) => void;", "", "function walk(n: number, onItem?: Visitor): number {", "  let s = 0;", "  for (let i = 0; i < n; i++) {", "    s += i;", "    onItem?.(i);", "  }", "  return s;", "}", "", "/** @requires safeInteger(i) && 0 <= i", " *    && i < xs.length */", "export function get(xs: number[], i: number): number {", "  const n = walk(3);   // no visitor passed", "  return xs[i]! + n;   // refused", "}"]),
      bullets([
        point("One frame per function", t("`walk`’s frame is inferred once, for every call. An unknown callback may change any array, so the frame is `stores: \"any\"`.")),
        point("The caller pays", t("`get` is refused although `walk(3)` runs no callback: the call drops `i < xs.length`.")),
        point("A frame on the callback’s type", t("with `Visitor` stated `stores: \"grow\"`, `get` verifies; a public function handing its own caller’s callback to `walk` is then refused.")),
        point("A run-time check", t("`if (i >= xs.length) throw …` after the call verifies. It never fires; it stands in for the proof.")),
        point("In pretext", "one such check stands before a call in a loop that also calls a line walker without its optional visitor."),
      ], 26),
    ], [54, 46]),
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
