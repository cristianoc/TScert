#!/usr/bin/env node
/**
 * Runnable Node reproductions for:
 *
 * 1. The two upstream Pretext bounds bugs (`// bounds bug:` in
 *    `dev/paper-rules/pretext/src/`):
 *    - `line-text.ts` (`getGraphemeStart`): `ends[graphemeIndex - 1]!` returns
 *      `undefined` (typed as `number`) when a line range kept from a longer
 *      text is materialized on a shorter text past a segment's last grapheme,
 *      returning the entire segment from `buildRangeText` and `NaN` source
 *      offsets in `rich-inline.ts`.
 *    - `measurement.ts` (`getCanvasFont`): `families[...]` returns `undefined`
 *      when `families` lists fewer generic families than `genericKeywords`,
 *      inserting `"undefined"` as a CSS font family name.
 *
 * 2. Separately, the two `#365` public-API cursor boundary validations
 *    (`// boundary check:` in `layout.ts` `stepNextLine` and `rich-inline.ts`
 *    `layoutNextRichInlineLineRange`): pragmatic runtime checks validating
 *    caller-supplied cursors at public streaming entry points (not upstream
 *    bugs on Pretext-produced cursors).
 *
 * Execution provenance:
 * - `line-text.ts`, `layout.ts`, `line-break.ts`, and `rich-inline.ts` are
 *   loaded directly from `dev/paper-rules/pretext/src/` under Node via
 *   `registerHooks` (`.js` -> `.ts` resolution inside that directory) with no
 *   browser DOM or Canvas mocks.
 * - Upstream buggy behavior for `getGraphemeStart` is reproduced by an
 *   extracted mirror of the upstream expression (`ends[graphemeIndex - 1]!`)
 *   fed the real `Int32Array` from Pretext's `getGraphemeEnds`, alongside the
 *   downstream `slice` and `getSourceOffset` arithmetic.
 * - `getCanvasFont` is unexported in `measurement.ts`, so both its upstream
 *   buggy body and its fixed body are exercised through extracted mirrors.
 * - Both `#365` boundary checks call the real exported `layoutNextLineRange`,
 *   `layoutNextLine`, and `layoutNextRichInlineLineRange`, and contrast them
 *   against calling the real exported `normalizePreparedLineStart` +
 *   `stepPreparedLineGeometryFromStart` directly (without the boundary check).
 */
import assert from "node:assert/strict";
import { existsSync, readFileSync } from "node:fs";
import { registerHooks } from "node:module";
import { dirname, resolve } from "node:path";
import { fileURLToPath, pathToFileURL } from "node:url";

// --- Local structural types matching Pretext's runtime shapes ---

type LayoutCursor = {
  segmentIndex: number;
  graphemeIndex: number;
};

type LayoutLineRange = {
  width: number;
  start: LayoutCursor;
  end: LayoutCursor;
};

type LayoutLine = {
  text: string;
  width: number;
  start: LayoutCursor;
  end: LayoutCursor;
};

type PreparedTextWithSegments = {
  widths: number[];
  segmentFlags: Uint8Array;
  simpleLineWalkFastPath: boolean;
  simpleLineCountFastPath: boolean;
  breakableFitAdvances: (number[] | null)[];
  breakableLineStartExtras: (number[] | null)[] | null;
  lineStartExtras: number[] | null;
  lineEndTrims: number[] | null;
  overflowLineEndTrims: number[] | null;
  letterSpacing: number;
  discretionaryHyphenWidth: number;
  discretionaryHyphenContexts: number[] | null;
  tabStopAdvance: number;
  minimumTabAdvance: number;
  readonly segments: readonly string[];
  readonly kinds: readonly string[];
};

type RichInlineCursor = {
  itemIndex: number;
  segmentIndex: number;
  graphemeIndex: number;
};

type RichInlineFragmentRange = {
  itemIndex: number;
  gapBefore: number;
  gapItemIndex: number;
  occupiedWidth: number;
  start: LayoutCursor;
  end: LayoutCursor;
};

type RichInlineLineRange = {
  fragments: RichInlineFragmentRange[];
  width: number;
  end: RichInlineCursor;
};

type RichInlineFragment = {
  itemIndex: number;
  text: string;
  gapBefore: number;
  gapItemIndex: number;
  occupiedWidth: number;
  sourceStart: number;
  sourceEnd: number;
};

type RichInlineLine = {
  fragments: RichInlineFragment[];
  width: number;
  end: RichInlineCursor;
};

type PreparedRichInline = {
  data: PreparedTextWithSegments;
  onlyItem: number;
  wholeWidth: number | null;
  wholeStart: number;
  wholeEnd: number;
  itemSegments: number[];
  segmentItems: Int32Array | null;
  gapSegments: Uint8Array | null;
  plainWidths: boolean;
  sourceStarts: number[] | null;
  sourceEnds: number[] | null;
  sourceUnits: (number[] | null)[] | null;
  text: string;
};

type LineTextModule = {
  getGraphemeEnds(prepared: PreparedTextWithSegments, segmentIndex: number): Int32Array;
  getGraphemeStart(prepared: PreparedTextWithSegments, segmentIndex: number, graphemeIndex: number): number;
  buildRangeText(
    prepared: PreparedTextWithSegments,
    startSegmentIndex: number,
    startGraphemeIndex: number,
    endSegmentIndex: number,
    endGraphemeIndex: number,
  ): string;
};

type LineBreakModule = {
  normalizePreparedLineStart(prepared: PreparedTextWithSegments, cursor: LayoutCursor): boolean;
  stepPreparedLineGeometryFromStart(
    prepared: PreparedTextWithSegments,
    cursor: LayoutCursor,
    maxWidth: number,
  ): number | null;
};

type LayoutModule = {
  layoutNextLine(
    prepared: PreparedTextWithSegments,
    maxWidth: number,
    start?: LayoutCursor,
  ): LayoutLine | null;
  layoutNextLineRange(
    prepared: PreparedTextWithSegments,
    maxWidth: number,
    start?: LayoutCursor,
  ): LayoutLineRange | null;
  materializeLineRange(prepared: PreparedTextWithSegments, line: LayoutLineRange): LayoutLine;
};

type RichInlineModule = {
  layoutNextRichInlineLineRange(
    prepared: PreparedRichInline,
    maxWidth: number,
    start?: RichInlineCursor,
  ): RichInlineLineRange | null;
  materializeRichInlineLineRange(prepared: PreparedRichInline, line: RichInlineLineRange): RichInlineLine;
};

// --- Direct loader for dev/paper-rules/pretext/src/*.ts ---

const repoRoot = resolve(import.meta.dirname, "..");
const pretextSrcDir = resolve(repoRoot, "dev/paper-rules/pretext/src");
const pretextSrcPrefix = `${pathToFileURL(pretextSrcDir).href}/`;

registerHooks({
  resolve(specifier, context, nextResolve) {
    if (
      specifier.startsWith(".") &&
      specifier.endsWith(".js") &&
      context.parentURL !== undefined &&
      context.parentURL.startsWith(pretextSrcPrefix)
    ) {
      const tsPath = resolve(dirname(fileURLToPath(context.parentURL)), `${specifier.slice(0, -3)}.ts`);
      if (existsSync(tsPath)) {
        return { url: pathToFileURL(tsPath).href, format: "module-typescript", shortCircuit: true };
      }
    }
    return nextResolve(specifier, context);
  },
  load(url, context, nextLoad) {
    if (url.startsWith(pretextSrcPrefix) && url.endsWith(".ts")) {
      return {
        format: "module-typescript",
        source: readFileSync(fileURLToPath(url), "utf8"),
        shortCircuit: true,
      };
    }
    return nextLoad(url, context);
  },
});

function requireModuleRecord(raw: unknown, label: string): Record<string, unknown> {
  if (typeof raw !== "object" || raw === null) {
    throw new TypeError(`${label}: expected module namespace object`);
  }
  return raw as Record<string, unknown>; // asserted: checked non-null object above
}

function requireFunctionExport<F>(mod: Record<string, unknown>, name: string, label: string): F {
  const value = mod[name];
  if (typeof value !== "function") {
    throw new TypeError(`${label}: expected function export "${name}"`);
  }
  return value as F; // asserted: runtime typeof === "function" check on loaded Pretext module export
}

async function importPretextModule(file: string): Promise<Record<string, unknown>> {
  const url = pathToFileURL(resolve(pretextSrcDir, file)).href;
  const raw: unknown = await import(url);
  return requireModuleRecord(raw, file);
}

async function loadPretextModules(): Promise<{
  lineText: LineTextModule;
  lineBreak: LineBreakModule;
  layout: LayoutModule;
  richInline: RichInlineModule;
}> {
  const lineTextRec = await importPretextModule("line-text.ts");
  const lineBreakRec = await importPretextModule("line-break.ts");
  const layoutRec = await importPretextModule("layout.ts");
  const richInlineRec = await importPretextModule("rich-inline.ts");

  return {
    lineText: {
      getGraphemeEnds: requireFunctionExport<LineTextModule["getGraphemeEnds"]>(
        lineTextRec,
        "getGraphemeEnds",
        "line-text.ts",
      ),
      getGraphemeStart: requireFunctionExport<LineTextModule["getGraphemeStart"]>(
        lineTextRec,
        "getGraphemeStart",
        "line-text.ts",
      ),
      buildRangeText: requireFunctionExport<LineTextModule["buildRangeText"]>(
        lineTextRec,
        "buildRangeText",
        "line-text.ts",
      ),
    },
    lineBreak: {
      normalizePreparedLineStart: requireFunctionExport<LineBreakModule["normalizePreparedLineStart"]>(
        lineBreakRec,
        "normalizePreparedLineStart",
        "line-break.ts",
      ),
      stepPreparedLineGeometryFromStart: requireFunctionExport<LineBreakModule["stepPreparedLineGeometryFromStart"]>(
        lineBreakRec,
        "stepPreparedLineGeometryFromStart",
        "line-break.ts",
      ),
    },
    layout: {
      layoutNextLine: requireFunctionExport<LayoutModule["layoutNextLine"]>(
        layoutRec,
        "layoutNextLine",
        "layout.ts",
      ),
      layoutNextLineRange: requireFunctionExport<LayoutModule["layoutNextLineRange"]>(
        layoutRec,
        "layoutNextLineRange",
        "layout.ts",
      ),
      materializeLineRange: requireFunctionExport<LayoutModule["materializeLineRange"]>(
        layoutRec,
        "materializeLineRange",
        "layout.ts",
      ),
    },
    richInline: {
      layoutNextRichInlineLineRange: requireFunctionExport<RichInlineModule["layoutNextRichInlineLineRange"]>(
        richInlineRec,
        "layoutNextRichInlineLineRange",
        "rich-inline.ts",
      ),
      materializeRichInlineLineRange: requireFunctionExport<RichInlineModule["materializeRichInlineLineRange"]>(
        richInlineRec,
        "materializeRichInlineLineRange",
        "rich-inline.ts",
      ),
    },
  };
}

// --- Plain Pretext handle builders (single ASCII TEXT segment, kind = 0) ---

function makeSingleWordPrepared(word: string, advancePerGrapheme: number): PreparedTextWithSegments {
  const graphemeCount = word.length;
  const advances = graphemeCount > 1 ? Array.from({ length: graphemeCount }, () => advancePerGrapheme) : null;
  return {
    widths: [graphemeCount * advancePerGrapheme],
    segmentFlags: new Uint8Array([0]), // TEXT = 0 in analysis.ts
    simpleLineWalkFastPath: true,
    simpleLineCountFastPath: true,
    breakableFitAdvances: [advances],
    breakableLineStartExtras: null,
    lineStartExtras: null,
    lineEndTrims: null,
    overflowLineEndTrims: null,
    letterSpacing: 0,
    discretionaryHyphenWidth: 0,
    discretionaryHyphenContexts: null,
    tabStopAdvance: 0,
    minimumTabAdvance: 0,
    segments: [word],
    kinds: ["text"],
  };
}

function makeSingleItemRichInline(word: string, advancePerGrapheme: number): PreparedRichInline {
  const data = makeSingleWordPrepared(word, advancePerGrapheme);
  return {
    data,
    onlyItem: 0,
    wholeWidth: word.length * advancePerGrapheme,
    wholeStart: 0,
    wholeEnd: 1,
    itemSegments: [0, 1],
    segmentItems: null,
    gapSegments: null,
    plainWidths: true,
    sourceStarts: [0],
    sourceEnds: [word.length],
    sourceUnits: null,
    text: word,
  };
}

// --- Extracted mirrors of upstream buggy expressions ---

/**
 * Extracted mirror of upstream `getGraphemeStart` (`line-text.ts` before the
 * `// bounds bug:` fix):
 *   const end = ends[graphemeIndex - 1]!
 *   return end === 0 ? ends.length : end
 *
 * Returns `number | undefined` honestly here; upstream typed it as `number` via `!`.
 */
function upstreamGetGraphemeStartFromEnds(ends: Int32Array, graphemeIndex: number): number | undefined {
  if (graphemeIndex <= 0) return 0;
  const end = ends[graphemeIndex - 1];
  return end === 0 ? ends.length : end;
}

const GENERIC_KEYWORDS: readonly string[] = ["serif", "sans-serif", "cursive", "fantasy", "monospace"];
const FONT_SIZE_RE = /\dpx(?:\s*\/\s*\S+)?\s+/;
const GENERIC_REPLACE_RE =
  /("[^"]*"|'[^']*')|(^|,)(\s*)(serif|sans-serif|cursive|fantasy|monospace)(?=\s*(?:,|$))/gi;

/**
 * Replaces matches of `GENERIC_REPLACE_RE` using `matchAll` (equivalent to
 * `String.prototype.replace` with capture groups, without the `...args: any[]`
 * signature of `String.prototype.replace` in `lib.es5.d.ts`).
 */
function replaceGenericMatches(
  tail: string,
  replacer: (
    item: string,
    quoted: string | undefined,
    separator: string | undefined,
    space: string | undefined,
    keyword: string | undefined,
  ) => string,
): string {
  let out = "";
  let cursor = 0;
  for (const match of tail.matchAll(GENERIC_REPLACE_RE)) {
    const index = match.index;
    out += tail.slice(cursor, index);
    out += replacer(match[0], match[1], match[2], match[3], match[4]);
    cursor = index + match[0].length;
  }
  return out + tail.slice(cursor);
}

/**
 * Extracted mirror of upstream `getCanvasFont` (`measurement.ts`, unexported,
 * before the `// bounds bug:` fix):
 *   const named = families[genericKeywords.indexOf(keyword.toLowerCase())]!
 *   return named === '' ? item : separator + space + named
 */
function upstreamGetCanvasFont(font: string, families: readonly string[]): string {
  const size = FONT_SIZE_RE.exec(font);
  if (size === null) return font;
  const start = size.index + size[0].length;
  return (
    font.slice(0, start) +
    replaceGenericMatches(font.slice(start), (item, quoted, separator, space, keyword) => {
      if (quoted !== undefined || separator === undefined || space === undefined || keyword === undefined) {
        return item;
      }
      const named = families[GENERIC_KEYWORDS.indexOf(keyword.toLowerCase())];
      // Upstream did `named === '' ? item : separator + space + named`, coercing `undefined` to `"undefined"`.
      return named === "" ? item : separator + space + String(named);
    })
  );
}

/**
 * Extracted mirror of fixed `getCanvasFont` (`dev/paper-rules/pretext/src/measurement.ts`,
 * unexported):
 *   const named = families[genericKeywords.indexOf(keyword.toLowerCase())] ?? ''
 *   return named === '' ? item : separator + space + named
 */
function fixedGetCanvasFont(font: string, families: readonly string[]): string {
  const size = FONT_SIZE_RE.exec(font);
  if (size === null) return font;
  const start = size.index + size[0].length;
  return (
    font.slice(0, start) +
    replaceGenericMatches(font.slice(start), (item, quoted, separator, space, keyword) => {
      if (quoted !== undefined || separator === undefined || space === undefined || keyword === undefined) {
        return item;
      }
      const named = families[GENERIC_KEYWORDS.indexOf(keyword.toLowerCase())] ?? "";
      return named === "" ? item : separator + space + named;
    })
  );
}

// --- Section 1: Upstream Pretext bounds bugs (`// bounds bug:`) ---

function runUpstreamBug1(
  lineText: LineTextModule,
  layout: LayoutModule,
  richInline: RichInlineModule,
): void {
  console.log("=== UPSTREAM BUG 1 (`// bounds bug:`): line-text.ts getGraphemeStart ===");

  // Produce genuine Pretext line ranges from a longer text ("abcdefgh", 8 graphemes x 10px = 80px).
  const longer = makeSingleWordPrepared("abcdefgh", 10);
  const line1At50 = layout.layoutNextLineRange(longer, 50);
  assert.notEqual(line1At50, null);
  assert.deepEqual(line1At50?.end, { segmentIndex: 0, graphemeIndex: 5 });

  const tailRangeFromLonger = layout.layoutNextLineRange(longer, 50, line1At50?.end);
  if (tailRangeFromLonger === null) assert.fail("expected second line range from longer text");
  assert.deepEqual(tailRangeFromLonger.start, { segmentIndex: 0, graphemeIndex: 5 });
  assert.deepEqual(tailRangeFromLonger.end, { segmentIndex: 1, graphemeIndex: 0 });

  // Also produce an intra-segment range [0,5) -> [0,7) at maxWidth 20px.
  const midRangeFromLonger = layout.layoutNextLineRange(longer, 20, line1At50?.end);
  assert.notEqual(midRangeFromLonger, null);
  assert.deepEqual(midRangeFromLonger?.start, { segmentIndex: 0, graphemeIndex: 5 });
  assert.deepEqual(midRangeFromLonger?.end, { segmentIndex: 0, graphemeIndex: 7 });

  // Re-prepare a shorter text ("hi", 2 graphemes) and materialize the stale ranges from `longer`.
  const shorter = makeSingleWordPrepared("hi", 10);
  const shorterRich = makeSingleItemRichInline("hi", 10);
  const realEnds = lineText.getGraphemeEnds(shorter, 0);
  assert.deepEqual(Array.from(realEnds), [1, 2]);

  // 1a. Upstream mirror vs. real fixed `getGraphemeStart` on graphemeIndex 5 (past "hi"'s 2 graphemes).
  const upstreamStart = upstreamGetGraphemeStartFromEnds(realEnds, 5);
  const upstreamEnd = upstreamGetGraphemeStartFromEnds(realEnds, 7);
  assert.equal(upstreamStart, undefined, "upstream reads ends[4] -> undefined");
  assert.equal(upstreamEnd, undefined, "upstream reads ends[6] -> undefined");

  const fixedStart = lineText.getGraphemeStart(shorter, 0, 5);
  const fixedEnd = lineText.getGraphemeStart(shorter, 0, 7);
  assert.equal(fixedStart, 2, "fixed getGraphemeStart clamps to ends.length (2)");
  assert.equal(fixedEnd, 2, "fixed getGraphemeStart clamps to ends.length (2)");

  // 1b. Downstream effect in `buildRangeText` / `materializeLineRange`:
  // Upstream slices `"hi".slice(undefined)` -> `"hi"` (whole segment instead of `""`).
  const upstreamTailText = shorter.segments[0]?.slice(upstreamStart);
  const upstreamMidText = shorter.segments[0]?.slice(upstreamStart, upstreamEnd);
  assert.equal(upstreamTailText, "hi", "upstream slice(undefined) returns full segment");
  assert.equal(upstreamMidText, "hi", "upstream slice(undefined, undefined) returns full segment");

  const fixedTailText = lineText.buildRangeText(shorter, 0, 5, 1, 0);
  const fixedMidText = lineText.buildRangeText(shorter, 0, 5, 0, 7);
  const fixedMaterialized = layout.materializeLineRange(shorter, tailRangeFromLonger);
  assert.equal(fixedTailText, "");
  assert.equal(fixedMidText, "");
  assert.equal(fixedMaterialized.text, "");

  // 1c. Downstream effect in `rich-inline.ts` (`materializeRichInlineLineRange`):
  // Upstream computes `sourceStarts[0] + undefined` -> `NaN`, and `(undefined - 1) + 1` -> `NaN`.
  const sourceStartBase = 0;
  const upstreamSourceStart = sourceStartBase + Number(upstreamStart);
  const upstreamSourceEnd = sourceStartBase + (Number(upstreamEnd) - 1) + 1;
  assert.ok(Number.isNaN(upstreamSourceStart), "upstream sourceStart becomes NaN");
  assert.ok(Number.isNaN(upstreamSourceEnd), "upstream sourceEnd becomes NaN");

  const richMidRangeFromLonger: RichInlineLineRange = {
    fragments: [
      {
        itemIndex: 0,
        gapBefore: 0,
        gapItemIndex: -1,
        occupiedWidth: 20,
        start: { segmentIndex: 0, graphemeIndex: 5 },
        end: { segmentIndex: 0, graphemeIndex: 7 },
      },
    ],
    width: 20,
    end: { itemIndex: 0, segmentIndex: 0, graphemeIndex: 7 },
  };
  const fixedRichLine = richInline.materializeRichInlineLineRange(shorterRich, richMidRangeFromLonger);
  assert.equal(fixedRichLine.fragments.length, 1);
  const fixedFrag = fixedRichLine.fragments[0];
  assert.notEqual(fixedFrag, undefined);
  assert.equal(fixedFrag?.text, "");
  assert.equal(fixedFrag?.sourceStart, 2);
  assert.equal(fixedFrag?.sourceEnd, 2);

  console.log(
    `  [upstream mirror on real getGraphemeEnds([1,2])] getGraphemeStart(shorter, 0, 5) = ${String(upstreamStart)} -> slice = ${JSON.stringify(upstreamTailText)}, rich-inline sourceStart/End = ${String(upstreamSourceStart)}/${String(upstreamSourceEnd)}`,
  );
  console.log(
    `  [real Pretext fixed] getGraphemeStart(shorter, 0, 5) = ${fixedStart} -> materializeLineRange.text = ${JSON.stringify(fixedMaterialized.text)}, materializeRichInlineLineRange = { text: ${JSON.stringify(fixedFrag?.text)}, sourceStart: ${fixedFrag?.sourceStart}, sourceEnd: ${fixedFrag?.sourceEnd} }`,
  );
}

function runUpstreamBug2(): void {
  console.log("=== UPSTREAM BUG 2 (`// bounds bug:`): measurement.ts getCanvasFont (extracted mirror; unexported) ===");

  // Profile lists only 2 generic families (`serif`, `sans-serif`), fewer than `genericKeywords` (5).
  const shortFamilies: readonly string[] = ['"Georgia"', '"Helvetica"'];

  const upstreamMono = upstreamGetCanvasFont("16px monospace", shortFamilies);
  const upstreamList = upstreamGetCanvasFont("16px serif, monospace", shortFamilies);
  assert.equal(upstreamMono, "16px undefined");
  assert.equal(upstreamList, '16px "Georgia", undefined');

  const fixedMono = fixedGetCanvasFont("16px monospace", shortFamilies);
  const fixedList = fixedGetCanvasFont("16px serif, monospace", shortFamilies);
  const fixedQuoted = fixedGetCanvasFont('16px "monospace", serif', shortFamilies);
  assert.equal(fixedMono, "16px monospace");
  assert.equal(fixedList, '16px "Georgia", monospace');
  assert.equal(fixedQuoted, '16px "monospace", "Georgia"');

  console.log(
    `  [upstream mirror] getCanvasFont("16px serif, monospace", ['"Georgia"', '"Helvetica"']) = ${JSON.stringify(upstreamList)}`,
  );
  console.log(
    `  [fixed mirror]    getCanvasFont("16px serif, monospace", ['"Georgia"', '"Helvetica"']) = ${JSON.stringify(fixedList)}`,
  );
}

// --- Section 2: Public API boundary checks (`// boundary check:`, #365) ---
// These validate caller-supplied cursors at public streaming APIs. They are NOT
// upstream bugs on Pretext-produced cursors (which preserve segment/grapheme invariants).

function runBoundaryCheckLayout(layout: LayoutModule, lineBreak: LineBreakModule): void {
  console.log("=== PUBLIC API BOUNDARY CHECK (#365, `// boundary check:`): layout.ts stepNextLine ===");

  const twoGrapheme = makeSingleWordPrepared("hi", 10);
  const oneGrapheme = makeSingleWordPrepared("a", 10); // breakableFitAdvances: [null]

  // Without the boundary check, passing an invalid caller cursor straight to the
  // real line-break steppers returns NaN width (fitAdvances[5] is undefined).
  const uncheckedCursor: LayoutCursor = { segmentIndex: 0, graphemeIndex: 5 };
  assert.equal(lineBreak.normalizePreparedLineStart(twoGrapheme, uncheckedCursor), true);
  const uncheckedWidth = lineBreak.stepPreparedLineGeometryFromStart(twoGrapheme, uncheckedCursor, 50);
  assert.ok(
    typeof uncheckedWidth === "number" && Number.isNaN(uncheckedWidth),
    "real line-break steppers without boundary check yield NaN on graphemeIndex 5",
  );

  // With the real `#365` boundary check in `layout.ts` (`stepNextLine`):
  assert.throws(
    () => layout.layoutNextLineRange(twoGrapheme, 50, { segmentIndex: -1, graphemeIndex: 0 }),
    /RangeError: cursor segment index out of range/,
  );
  assert.throws(
    () => layout.layoutNextLineRange(twoGrapheme, 50, { segmentIndex: 0.5, graphemeIndex: 0 }),
    /RangeError: cursor segment index out of range/,
  );
  assert.throws(
    () => layout.layoutNextLineRange(twoGrapheme, 50, { segmentIndex: 0, graphemeIndex: -1 }),
    /RangeError: cursor grapheme index out of range/,
  );
  assert.throws(
    () => layout.layoutNextLineRange(twoGrapheme, 50, { segmentIndex: 0, graphemeIndex: 5 }),
    /RangeError: cursor grapheme index out of range/,
  );
  assert.throws(
    () => layout.layoutNextLine(oneGrapheme, 50, { segmentIndex: 0, graphemeIndex: 1 }),
    /RangeError: cursor grapheme index out of range/,
  );

  // Valid caller cursors still succeed cleanly: past-end returns null; in-range returns a line.
  assert.equal(layout.layoutNextLineRange(twoGrapheme, 50, { segmentIndex: 1, graphemeIndex: 0 }), null);
  assert.equal(layout.layoutNextLineRange(twoGrapheme, 50, { segmentIndex: 1, graphemeIndex: 5 }), null);
  const validLine = layout.layoutNextLine(twoGrapheme, 50, { segmentIndex: 0, graphemeIndex: 1 });
  assert.equal(validLine?.text, "i");
  assert.equal(validLine?.width, 10);

  console.log(
    `  [real line-break without boundary check] stepPreparedLineGeometryFromStart({segmentIndex:0, graphemeIndex:5}) = ${String(uncheckedWidth)}`,
  );
  console.log(
    `  [real layout.ts with #365 boundary check] invalid cursors (-1, 0.5, graphemeIndex 5, null advances) throw RangeError; valid {0,1} -> ${JSON.stringify(validLine?.text)} (width ${validLine?.width}), past-end -> null`,
  );
}

function runBoundaryCheckRichInline(richInline: RichInlineModule, lineBreak: LineBreakModule): void {
  console.log(
    "=== PUBLIC API BOUNDARY CHECK (#365, `// boundary check:`): rich-inline.ts layoutNextRichInlineLineRange ===",
  );

  const twoGraphemeRich = makeSingleItemRichInline("hi", 10);
  const oneGraphemeRich = makeSingleItemRichInline("a", 10); // breakableFitAdvances: [null]

  // Without the boundary check, forwarding `{segmentIndex: 0, graphemeIndex: 5}` to
  // the real line-break steppers yields NaN width.
  const uncheckedCursor: LayoutCursor = { segmentIndex: 0, graphemeIndex: 5 };
  assert.equal(lineBreak.normalizePreparedLineStart(twoGraphemeRich.data, uncheckedCursor), true);
  const uncheckedWidth = lineBreak.stepPreparedLineGeometryFromStart(twoGraphemeRich.data, uncheckedCursor, 50);
  assert.ok(
    typeof uncheckedWidth === "number" && Number.isNaN(uncheckedWidth),
    "real line-break steppers without boundary check yield NaN on graphemeIndex 5",
  );

  // With the real `#365` boundary check in `rich-inline.ts` (`layoutNextRichInlineLineRange`):
  assert.throws(
    () =>
      richInline.layoutNextRichInlineLineRange(twoGraphemeRich, 50, {
        itemIndex: -1,
        segmentIndex: 0,
        graphemeIndex: 0,
      }),
    /RangeError: cursor item index out of range/,
  );
  assert.throws(
    () =>
      richInline.layoutNextRichInlineLineRange(twoGraphemeRich, 50, {
        itemIndex: 0.5,
        segmentIndex: 0,
        graphemeIndex: 0,
      }),
    /RangeError: cursor item index out of range/,
  );
  assert.throws(
    () =>
      richInline.layoutNextRichInlineLineRange(twoGraphemeRich, 50, {
        itemIndex: 1,
        segmentIndex: -1,
        graphemeIndex: 0,
      }),
    /RangeError: cursor segment index out of range/,
  );
  assert.throws(
    () =>
      richInline.layoutNextRichInlineLineRange(twoGraphemeRich, 50, {
        itemIndex: 0,
        segmentIndex: -1,
        graphemeIndex: 0,
      }),
    /RangeError: cursor segment index out of range/,
  );
  assert.throws(
    () =>
      richInline.layoutNextRichInlineLineRange(twoGraphemeRich, 50, {
        itemIndex: 0,
        segmentIndex: 0.5,
        graphemeIndex: 0,
      }),
    /RangeError: cursor segment index out of range/,
  );
  assert.throws(
    () =>
      richInline.layoutNextRichInlineLineRange(twoGraphemeRich, 50, {
        itemIndex: 0,
        segmentIndex: 0,
        graphemeIndex: -1,
      }),
    /RangeError: cursor grapheme index out of range/,
  );
  assert.throws(
    () =>
      richInline.layoutNextRichInlineLineRange(twoGraphemeRich, 50, {
        itemIndex: 0,
        segmentIndex: 0,
        graphemeIndex: 5,
      }),
    /RangeError: cursor grapheme index out of range/,
  );
  assert.throws(
    () =>
      richInline.layoutNextRichInlineLineRange(oneGraphemeRich, 50, {
        itemIndex: 0,
        segmentIndex: 0,
        graphemeIndex: 1,
      }),
    /RangeError: cursor grapheme index out of range/,
  );

  // Valid caller cursors still succeed cleanly: start returns the line; past-end returns null.
  const validRange = richInline.layoutNextRichInlineLineRange(twoGraphemeRich, 50, {
    itemIndex: 0,
    segmentIndex: 0,
    graphemeIndex: 0,
  });
  assert.notEqual(validRange, null);
  assert.equal(validRange?.width, 20);
  assert.equal(
    richInline.layoutNextRichInlineLineRange(twoGraphemeRich, 50, {
      itemIndex: 1,
      segmentIndex: 0,
      graphemeIndex: 0,
    }),
    null,
  );

  console.log(
    `  [real line-break without boundary check] stepPreparedLineGeometryFromStart({segmentIndex:0, graphemeIndex:5}) = ${String(uncheckedWidth)}`,
  );
  console.log(
    `  [real rich-inline.ts with #365 boundary check] invalid cursors (-1, 0.5, graphemeIndex 5, null advances) throw RangeError; valid {0,0,0} -> width ${validRange?.width}, past-end -> null`,
  );
}

async function main(): Promise<void> {
  const { lineText, lineBreak, layout, richInline } = await loadPretextModules();
  runUpstreamBug1(lineText, layout, richInline);
  runUpstreamBug2();
  runBoundaryCheckLayout(layout, lineBreak);
  runBoundaryCheckRichInline(richInline, lineBreak);
  console.log("pretext-bug-repros: all 2 upstream bug repros and 2 #365 public API boundary checks passed.");
}

await main();
