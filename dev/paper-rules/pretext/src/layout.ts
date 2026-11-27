// Prepare text with engine segmentation rules and cached Canvas measurements, then
// lay it out with arithmetic. Preparation touches the DOM in three places: the emoji
// correction's span, read once per font where Canvas measures an emoji wider than its
// font size; the page's `<html lang>`, unless setLocale() gave a language; and, without
// OffscreenCanvas, a canvas element never attached. Layout itself does no measurement
// or string work.
// Rich APIs add source cursors and text materialization.
// Browser measurement limitations are documented in README.md and PLATFORM_BUGS.md.
// Based on Sebastian Markbage's text-layout research (github.com/chenglou/text-layout).

import { missing } from './checked.js'
import { clearWordSegmenter } from './line-breaks.js'
import {
  analyzeText,
  KIND_BITS,
  SEGMENT_KINDS,
  type SegmentBreakKind,
  type WhiteSpaceMode,
  type WordBreakMode as AnalysisWordBreakMode,
} from './analysis.js'
import {
  clearMeasurementCaches,
  getEngineProfile,
  getPreparationLanguage,
  readLetterSpacing,
  setLocaleLanguage,
} from './measurement.js'
import { measureAnalysis } from './prepare.js'
import {
  countPreparedLines,
  normalizeMaxWidth,
  normalizePreparedLineStart,
  stepPreparedLineGeometryFromStart,
  walkPreparedLinesRaw,
  type PreparedLineBreakData,
  type PreparedLineData,
} from './line-break.js'
import { buildLineTextFromRange } from './line-text.js'

// --- Public types ---

// The compact height-prediction handle: the line walkers' parallel arrays, which are internal.
export type PreparedText = PreparedLineData

// The handle that also keeps each segment's text, which the functions that return
// line text need (layoutWithLines(), layoutNextLine() and materializeLineRange()),
// and its kind, for the app's own rendering. Its type shows those two read-only, beside
// the line walkers' storage, which changes with engine fixes (RESEARCH.md, Decisions Log,
// 2026-10-06).
export type PreparedTextWithSegments = PreparedText & {
  readonly segments: readonly string[] // Each segment's text, e.g. ['hello', ' ', 'world']
  readonly kinds: readonly SegmentBreakKind[] // What each segment is, e.g. ['text', 'space', 'text']
}

// What a handle holds: the line walkers' data. getInternalPrepared() reads a public handle as it.
type InternalPreparedText = PreparedText & PreparedLineBreakData

export type LayoutCursor = {
  segmentIndex: number // Segment index in `segments`
  graphemeIndex: number // Grapheme index within that segment; `0` at segment boundaries
}

export type LayoutResult = {
  lineCount: number // Number of wrapped lines, e.g. 3
  height: number // Total block height, e.g. lineCount * lineHeight = 57
}

export type LineStats = {
  lineCount: number
  maxLineWidth: number
}

export type LayoutLine = {
  text: string // Full text content of this line, e.g. 'hello world'
  width: number // Measured width of this line, e.g. 87.5, leaving out spaces and tabs that hang past its end
  start: LayoutCursor // Inclusive start cursor in prepared segments/graphemes
  end: LayoutCursor // Exclusive end cursor in prepared segments/graphemes
}

export type LayoutLineRange = {
  width: number // Measured width of this line, e.g. 87.5, leaving out spaces and tabs that hang past its end
  start: LayoutCursor // Inclusive start cursor in prepared segments/graphemes
  end: LayoutCursor // Exclusive end cursor in prepared segments/graphemes
}

export type LayoutLinesResult = LayoutResult & {
  lines: LayoutLine[] // Per-line text/width pairs for custom rendering
}

export type WordBreakMode = AnalysisWordBreakMode

export type PrepareOptions = {
  whiteSpace?: WhiteSpaceMode
  wordBreak?: WordBreakMode
  letterSpacing?: number
}

// --- Public API ---

/** @requires segments === null || segments.length === 0 */
function prepareInternal(
  text: string,
  font: string,
  segments: string[] | null,
  options?: PrepareOptions,
): PreparedText {
  const wordBreak = options?.wordBreak ?? 'normal'
  const engineProfile = getEngineProfile()
  const letterSpacing = readLetterSpacing(options?.letterSpacing, engineProfile)
  // One language read: break rules and measurement both follow it.
  const language = getPreparationLanguage(engineProfile)
  const analysis = analyzeText(text, engineProfile, options?.whiteSpace, wordBreak, language)
  // PAPER: workaround (call-ensures-arg-locals): `from` and `to` must be locals so `measureAnalysis`'s `@ensures` (`to - from`) substitutes at the call site
  const from = 0
  const to = analysis.flags.length
  // PAPER: workaround (callee-spine-framing): re-establish `segments.length === 0` after `analyzeText` (whose unannotated transitive callees such as `getGeckoLineBreaks` / `removeItemsSkippableSegmentBreaks` infer `spines: "grow"` and clobber `segments.length`, failing `measureAnalysis`'s `@requires` with `node-typing claim`)
  if (segments !== null && segments.length !== 0) throw new RangeError('segments')
  const prepared = measureAnalysis(analysis, from, to, font, segments, letterSpacing, engineProfile, language, true, null, 0)
  // PAPER: workaround (object-literal-field-locals): copy fields into locals and rebuild object explicitly so `PreparedLineData` invariant sees local length/forall facts (direct return, `{ ...prepared }`, and inline `prepared.<field>` all fail `binding-annotation` / `ensures`)
  const widths = prepared.widths
  const segmentFlags = prepared.segmentFlags
  const breakableFitAdvances = prepared.breakableFitAdvances
  const breakableLineStartExtras = prepared.breakableLineStartExtras
  const lineStartExtras = prepared.lineStartExtras
  const lineEndTrims = prepared.lineEndTrims
  const overflowLineEndTrims = prepared.overflowLineEndTrims
  const result: PreparedText = {
    widths,
    segmentFlags,
    simpleLineWalkFastPath: prepared.simpleLineWalkFastPath,
    simpleLineCountFastPath: prepared.simpleLineCountFastPath,
    breakableFitAdvances,
    breakableLineStartExtras,
    lineStartExtras,
    lineEndTrims,
    overflowLineEndTrims,
    letterSpacing: prepared.letterSpacing,
    discretionaryHyphenWidth: prepared.discretionaryHyphenWidth,
    discretionaryHyphenContexts: prepared.discretionaryHyphenContexts,
    tabStopAdvance: prepared.tabStopAdvance,
    minimumTabAdvance: prepared.minimumTabAdvance,
  }
  return result
}

// Prepare text for layout. Segments the text, measures each segment via canvas,
// and stores the widths for fast relayout at any width. Call once per text block
// (e.g. when a comment first appears). The result is width-independent — the
// same PreparedText can be laid out at any maxWidth and lineHeight via layout().
//
// Steps:
//   1. Normalize white space as white-space: normal or pre-wrap does
//   2. Find break opportunities with the engine's own line-break scan
//   3. Split the text into segments between them ("better." as one unit)
//   4. Measure each segment via canvas measureText, cache by (segment, font).
//      WebKit measures a word with the space after it
//   5. Measure where each text segment of two or more graphemes can break under
//      overflow-wrap: break-word: by graphemes, pairs or prefixes, per engine
//   6. Correct emoji canvas inflation (probed once per font)
//   7. Record what changes at a line's edges: Blink's halts of CJK punctuation,
//      U+3000 hangs, and how much narrower a soft hyphen's neighbors measure joined
export function prepare(text: string, font: string, options?: PrepareOptions): PreparedText {
  return prepareInternal(text, font, null, options) as PreparedText
}

// Rich variant used by callers that need enough information to render the
// laid-out lines themselves.
export function prepareWithSegments(text: string, font: string, options?: PrepareOptions): PreparedTextWithSegments {
  const segments: string[] = []
  const prepared = prepareInternal(text, font, segments, options)
  // Each segment's kind by name, from its flags.
  const kinds: SegmentBreakKind[] = []
  /** @invariant prepared.segmentFlags.length === prepared.widths.length && prepared.breakableFitAdvances.length === prepared.widths.length && prepared.widths !== kinds
   *  @invariant prepared.lineStartExtras === null || prepared.widths.length <= prepared.lineStartExtras.length
   *  @invariant prepared.lineEndTrims === null || prepared.widths.length <= prepared.lineEndTrims.length
   *  @invariant prepared.overflowLineEndTrims === null || prepared.widths.length <= prepared.overflowLineEndTrims.length
   *  @invariant prepared.breakableLineStartExtras === null || prepared.widths.length <= prepared.breakableLineStartExtras.length
   *  @invariant forall i in prepared.breakableFitAdvances: prepared.breakableFitAdvances[i] === null || 1 <= prepared.breakableFitAdvances[i].length
   *  @invariant prepared.breakableLineStartExtras === null || forall i in prepared.breakableFitAdvances: prepared.breakableFitAdvances[i] === null || prepared.breakableLineStartExtras[i] === null || prepared.breakableFitAdvances[i].length <= prepared.breakableLineStartExtras[i].length
   *  @invariant prepared.items === undefined || prepared.items.hyphenWidths === null || prepared.widths.length <= prepared.items.hyphenWidths.length
   *  @invariant prepared.items === undefined || prepared.items.hyphenRooms === null || prepared.widths.length < prepared.items.hyphenRooms.length
   *  @invariant prepared.items === undefined || prepared.items.itemEndHalts === null || prepared.widths.length <= prepared.items.itemEndHalts.length
   *  @invariant prepared.items === undefined || prepared.items.openingEdges === null || prepared.widths.length <= prepared.items.openingEdges.length */
  for (let i = 0; i < prepared.segmentFlags.length; i++) kinds.push(SEGMENT_KINDS[prepared.segmentFlags[i]! & KIND_BITS] ?? missing())
  return { ...prepared, segments, kinds }
}

function getInternalPrepared(prepared: PreparedText): InternalPreparedText {
  return prepared
}

// Layout prepared text at a given max width and caller-provided lineHeight.
// Pure arithmetic on cached widths — no canvas calls, no DOM reads, no string
// operations, and no per-line allocations. Call on every resize. Lines break
// where the engine's page breaks them, under the CSS the README lists
// (README.md, Caveats).
export function layout(prepared: PreparedText, maxWidth: number, lineHeight: number): LayoutResult {
  // The resize hot path counts the same lines as `layoutWithLines()` without
  // building line ranges or text.
  const lineCount = countPreparedLines(getInternalPrepared(prepared), normalizeMaxWidth(maxWidth))
  return { lineCount, height: lineCount * lineHeight }
}

// Reported widths are clamped at zero wherever a line is built. A line's
// advance can be negative: the rest of a word after an emergency break can
// hold only invisible characters and the word's kerning with a following
// space, and letter spacing can be strongly negative. Line breaking keeps the
// signed advance.
function createLayoutLine(
  prepared: PreparedTextWithSegments,
  width: number,
  startSegmentIndex: number,
  startGraphemeIndex: number,
  endSegmentIndex: number,
  endGraphemeIndex: number,
): Effects<{ "@state": "any" }, LayoutLine> {   // PAPER: annotation
  return {
    text: buildLineTextFromRange(
      prepared,
      startSegmentIndex,
      startGraphemeIndex,
      endSegmentIndex,
      endGraphemeIndex,
    ),
    width: Math.max(0, width),
    start: {
      segmentIndex: startSegmentIndex,
      graphemeIndex: startGraphemeIndex,
    },
    end: {
      segmentIndex: endSegmentIndex,
      graphemeIndex: endGraphemeIndex,
    },
  }
}

function createLayoutLineRange(
  width: number,
  startSegmentIndex: number,
  startGraphemeIndex: number,
  endSegmentIndex: number,
  endGraphemeIndex: number,
): Modifies<{}, LayoutLineRange> {   // PAPER: annotation
  return {
    width: Math.max(0, width),
    start: {
      segmentIndex: startSegmentIndex,
      graphemeIndex: startGraphemeIndex,
    },
    end: {
      segmentIndex: endSegmentIndex,
      graphemeIndex: endGraphemeIndex,
    },
  }
}

export function materializeLineRange(
  prepared: PreparedTextWithSegments,
  line: LayoutLineRange,
): LayoutLine {
  return createLayoutLine(
    prepared,
    line.width,
    line.start.segmentIndex,
    line.start.graphemeIndex,
    line.end.segmentIndex,
    line.end.graphemeIndex,
  )
}

// Batch low-level line-range pass. This is the non-materializing counterpart
// to layoutWithLines(), useful for shrinkwrap and other aggregate stats work.
// It, measureLineStats(), measureNaturalWidth() and layoutNextLineRange() return
// widths and cursors and no text, from the line-break data layout() reads, so they
// take a prepare() handle as well (RESEARCH.md, Decisions Log, 2026-10-06).
// PAPER: onLine's effect is the effect variable E: a caller states it as the instance, and
// the bound requires it to keep every location the handle reaches and allows any other change.
export function walkLineRanges<E extends AtMost<{ "prepared.**": "keep"; else: "any" }>>(
  prepared: PreparedText,
  maxWidth: number,
  onLine: (line: LayoutLineRange) => Modifies<E, void>,   // PAPER
): number {
  return walkPreparedLinesRaw<E>(   // PAPER: forwards E
    getInternalPrepared(prepared),
    normalizeMaxWidth(maxWidth),
    (width, startSegmentIndex, startGraphemeIndex, endSegmentIndex, endGraphemeIndex) => {
      onLine(createLayoutLineRange(
        width,
        startSegmentIndex,
        startGraphemeIndex,
        endSegmentIndex,
        endGraphemeIndex,
      ))
    },
  )
}

export function measureLineStats(
  prepared: PreparedText,
  maxWidth: number,
): LineStats {
  const stats = { lineCount: 0, maxLineWidth: 0 }
  walkPreparedLinesRaw(getInternalPrepared(prepared), normalizeMaxWidth(maxWidth), undefined, stats)
  return stats
}

// Intrinsic-width helper for rich/userland layout work. This asks "how wide is
// the prepared text when container width is not the thing forcing wraps?".
// Explicit hard breaks still count, so this returns the widest forced line.
export function measureNaturalWidth(prepared: PreparedText): number {
  return measureLineStats(prepared, Number.POSITIVE_INFINITY).maxLineWidth
}

// Where a line stream starts without a `start`: the text's first line.
const TEXT_START_CURSOR: LayoutCursor = { segmentIndex: 0, graphemeIndex: 0 }

// Steps one streamed line from `start` into the result's cursors: the
// normalized line start and the line end. Returns the reported width, or null
// after the last line.
function stepNextLine(
  prepared: PreparedText,
  maxWidth: number,
  start: LayoutCursor,
  lineStart: LayoutCursor,
  lineEnd: LayoutCursor,
): number | null {
  const internal = getInternalPrepared(prepared)
  lineEnd.segmentIndex = start.segmentIndex
  lineEnd.graphemeIndex = start.graphemeIndex
  // boundary check: validates caller-supplied LayoutCursor (segmentIndex, graphemeIndex,
  // and breakableFitAdvances bounds) at the public streaming API boundary (#365).
  if (!(Number.isSafeInteger(lineEnd.segmentIndex) && 0 <= lineEnd.segmentIndex)) throw new RangeError('cursor segment index out of range')
  if (!(Number.isSafeInteger(lineEnd.graphemeIndex) && 0 <= lineEnd.graphemeIndex)) throw new RangeError('cursor grapheme index out of range')
  if (lineEnd.graphemeIndex > 0) {
    if (lineEnd.segmentIndex >= internal.widths.length || lineEnd.segmentIndex >= internal.breakableFitAdvances.length) return null
    const advances = internal.breakableFitAdvances[lineEnd.segmentIndex]
    if (advances === undefined || advances === null || lineEnd.graphemeIndex >= advances.length) throw new RangeError('cursor grapheme index out of range')
  }
  if (!normalizePreparedLineStart(internal, lineEnd)) return null

  // PAPER: workaround (object-disjointness-requires): copy lineStart fields through locals and write after step because `@requires` only supports `!==` on arrays (`lineStart !== lineEnd` is rejected), so writing `lineStart.*` before `stepPreparedLineGeometryFromStart` clobbers `lineEnd` bounds
  const lineStartSegmentIndex = lineEnd.segmentIndex
  const lineStartGraphemeIndex = lineEnd.graphemeIndex
  const width = stepPreparedLineGeometryFromStart(internal, lineEnd, maxWidth)
  lineStart.segmentIndex = lineStartSegmentIndex
  lineStart.graphemeIndex = lineStartGraphemeIndex
  return width === null ? null : Math.max(0, width)
}

// The line streams take the width before the cursor, as layoutNextRichInlineLineRange()
// does, and start at the text's first line without one: pass each line's `end` back
// for the next.
export function layoutNextLine(
  prepared: PreparedTextWithSegments,
  maxWidth: number,
  start: LayoutCursor = TEXT_START_CURSOR,
): LayoutLine | null {
  const lineStart = { segmentIndex: 0, graphemeIndex: 0 }
  const end = { segmentIndex: 0, graphemeIndex: 0 }
  const width = stepNextLine(prepared, maxWidth, start, lineStart, end)
  if (width === null) return null

  const text = buildLineTextFromRange(
    prepared,
    lineStart.segmentIndex,
    lineStart.graphemeIndex,
    end.segmentIndex,
    end.graphemeIndex,
  )
  return { text, width, start: lineStart, end }
}

export function layoutNextLineRange(
  prepared: PreparedText,
  maxWidth: number,
  start: LayoutCursor = TEXT_START_CURSOR,
): LayoutLineRange | null {
  const lineStart = { segmentIndex: 0, graphemeIndex: 0 }
  const end = { segmentIndex: 0, graphemeIndex: 0 }
  const width = stepNextLine(prepared, maxWidth, start, lineStart, end)
  return width === null ? null : { width, start: lineStart, end }
}

// Rich layout API for callers that want the actual line contents and widths.
// Caller still supplies lineHeight at layout time. Mirrors layout()'s break
// decisions, but keeps extra per-line bookkeeping so it should stay off the
// resize hot path.
export function layoutWithLines(prepared: PreparedTextWithSegments, maxWidth: number, lineHeight: number): LayoutLinesResult {
  const lines: LayoutLine[] = []
  const lineCount = walkPreparedLinesRaw<{ "lines[*]": "extend"; "@state": "any" }>(   // PAPER: the visitor's instance
    getInternalPrepared(prepared),
    normalizeMaxWidth(maxWidth),
    (width, startSegmentIndex, startGraphemeIndex, endSegmentIndex, endGraphemeIndex) => {
      lines.push(createLayoutLine(
        prepared,
        width,
        startSegmentIndex,
        startGraphemeIndex,
        endSegmentIndex,
        endGraphemeIndex,
      ))
    },
  )

  return { lineCount, height: lineCount * lineHeight, lines }
}

export function clearCache(): void {
  clearWordSegmenter()
  clearMeasurementCaches()
}

// Sets the language later preparation breaks and measures under in place of
// `<html lang>`, which a worker doesn't have; an empty one is a page's without a
// language. Without a locale, preparation reads `<html lang>` again. Prepared
// handles keep theirs (RESEARCH.md, Decisions Log, 2026-09-26).
export function setLocale(locale?: string): void {
  setLocaleLanguage(locale)
  clearCache()
}
