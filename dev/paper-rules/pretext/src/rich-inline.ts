import { missing } from './checked.js'
import type { LayoutCursor, WordBreakMode } from './layout.js'
import {
  alignToSource,
  analyzeText,
  isCollapsibleSpaceCode,
  DROPPED,
  HARD_BREAK,
  KIND_BITS,
  OBJECT,
  PRESERVED_SPACE,
  RETURNABLE,
  SOFT_HYPHEN,
  SPACE,
  SPACED,
  TAB,
  TEXT,
  UNBROKEN,
  ZERO_WIDTH_BREAK,
  ZERO_WIDTH_GLUE,
  type ParagraphItems,
  type TextAnalysis,
  type WhiteSpaceMode,
} from './analysis.js'
import { buildLineTextFromRange, buildRangeText, getGraphemeStart, type PreparedSegments } from './line-text.js'
import {
  getItemTabAdvance,
  normalizeMaxWidth,
  normalizePreparedLineStart,
  stepPreparedLineGeometryFromStart,
  walkPreparedLinesRaw,
  type ParagraphSegmentData,
  type PreparedLineData,
} from './line-break.js'
import { getEngineProfile, getFontMeasurement, getPreparationLanguage, getSpaceWidth, readLetterSpacing, zeros, type EngineProfile } from './measurement.js'
import { measureAnalysis, measureParagraphAnalysis } from './prepare.js'

// Helper for rich-text inline flow under `white-space: normal` or `pre-wrap`: one paragraph's text
// broken across its items, as a browser lays out the text of an inline formatting context across
// its spans. The items' texts join into the paragraph's text, an atomic item or a box as one
// U+FFFC, which is analyzed once, as prepare() analyzes a text, with a segment starting wherever an
// item does. Each item's segments are measured in its font, and the text walkers lay the paragraph
// out. So:
// - white space collapses across item boundaries, and under pre-wrap preserved spaces hang
//   across them, tab stops count from the line's start, and hard breaks end lines
// - break opportunities across item boundaries are the engine's: from the text the items join in
//   Blink and Gecko, and in WebKit from each item's own text and the last two characters before
//   it, under the paragraph's word-break; a run that continues across items wraps together
// - atomic inline boxes like pills, and boxes the app sizes and paints, such as images, are one
//   segment each, which a line can break before and after
// - an item's extra horizontal chrome, such as padding and borders, is part of its width on
//   every line the item reaches
// A line's fragments are its segments cut where the item changes.

const PRESERVED_WHITE_SPACE = 1 << PRESERVED_SPACE | 1 << TAB

export type RichInlineItem = {
  text: string // Raw author text, including any leading/trailing collapsible spaces
  font: string // Canvas font shorthand used to prepare and measure this item
  letterSpacing?: number // Extra horizontal spacing between graphemes, in CSS px
  break?: 'normal' | 'never' // `never` keeps the item atomic, like a pill or mention chip
  extraWidth?: number // Caller-owned horizontal chrome, e.g. padding + border width
  width?: never // A RichInlineBox's
}

// An object inside a line that the app sizes and paints, such as an image, a custom emoji, a formula
// or a badge: an atomic inline with no text, as an <img> or an empty inline-block is, which a line
// can break before and after. An item without text is one.
export type RichInlineBox = {
  width: number // The room it takes on the line, in CSS px, at least 0 and final: its element's margin box
  text?: never
}

// How the paragraph the items make wraps, one setting for all of them, as CSS on the
// element that holds the spans sets it.
export type RichInlineOptions = {
  whiteSpace?: WhiteSpaceMode // `pre-wrap`: CSS `white-space: pre-wrap`, as prepare() takes it
  wordBreak?: WordBreakMode // `keep-all`: CSS `word-break: keep-all`, as prepare() takes it
}

export type PreparedRichInline = InternalPreparedRichInline

// A place in the paragraph: an item, and a segment and grapheme of that item's part of the
// paragraph's text, whose segments no app sees. What a line or a fragment range gives is for
// passing back. A materialized fragment's type has no cursors (RESEARCH.md, Decisions Log,
// 2026-10-10): its place in its item's text is its sourceStart and sourceEnd, and the line to
// pass back is the range it was materialized from.
export type RichInlineCursor = {
  itemIndex: number // Index into the items prepareRichInline() took
  segmentIndex: number
  graphemeIndex: number
}

export type RichInlineFragment = {
  itemIndex: number // Index into the items prepareRichInline() took
  text: string // Text slice for this fragment
  gapBefore: number // Collapsed inter-item gap paid before this fragment on this line
  gapItemIndex: number // Item whose collapsed whitespace made gapBefore, or -1 when no gap precedes this fragment on this line
  occupiedWidth: number // Text width plus the item's extraWidth contribution
  sourceStart: number // Where the fragment starts in its item's `text`, in UTF-16 units
  sourceEnd: number // Where it ends there
}

export type RichInlineFragmentRange = {
  itemIndex: number // Index into the items prepareRichInline() took
  gapBefore: number // Collapsed inter-item gap paid before this fragment on this line
  gapItemIndex: number // Item whose collapsed whitespace made gapBefore, or -1 when no gap precedes this fragment on this line
  occupiedWidth: number // Text width plus the item's extraWidth contribution
  start: LayoutCursor // Start cursor within the item's part of the paragraph
  end: LayoutCursor // End cursor within the item's part of the paragraph
}

// A materialized fragment as materializeRichInlineLineRange() builds it: with its range's
// cursors, which are off its type only (RESEARCH.md, Decisions Log, 2026-10-10).
type InternalRichInlineFragment = RichInlineFragment & RichInlineFragmentRange

export type RichInlineLine = {
  fragments: RichInlineFragment[]
  width: number
  end: RichInlineCursor
}

export type RichInlineLineRange = {
  fragments: RichInlineFragmentRange[]
  width: number
  end: RichInlineCursor
}

export type RichInlineStats = {
  lineCount: number
  maxLineWidth: number
}

/** @invariant this.data.segmentFlags.length === this.data.widths.length
 *  @invariant this.data.breakableFitAdvances.length === this.data.widths.length
 *  @invariant this.data.lineStartExtras === null || this.data.widths.length <= this.data.lineStartExtras.length
 *  @invariant this.data.lineEndTrims === null || this.data.widths.length <= this.data.lineEndTrims.length
 *  @invariant this.data.overflowLineEndTrims === null || this.data.widths.length <= this.data.overflowLineEndTrims.length
 *  @invariant this.data.breakableLineStartExtras === null || this.data.widths.length <= this.data.breakableLineStartExtras.length
 *  @invariant forall i in this.data.breakableFitAdvances: this.data.breakableFitAdvances[i] === null || 1 <= this.data.breakableFitAdvances[i].length
 *  @invariant this.data.breakableLineStartExtras === null || forall i in this.data.breakableFitAdvances: this.data.breakableFitAdvances[i] === null || this.data.breakableLineStartExtras[i] === null || this.data.breakableFitAdvances[i].length <= this.data.breakableLineStartExtras[i].length
 *  @invariant this.data.items === undefined || this.data.items.hyphenWidths === null || this.data.widths.length <= this.data.items.hyphenWidths.length
 *  @invariant this.data.items === undefined || this.data.items.hyphenRooms === null || this.data.widths.length < this.data.items.hyphenRooms.length
 *  @invariant this.data.items === undefined || this.data.items.itemEndHalts === null || this.data.widths.length <= this.data.items.itemEndHalts.length
 *  @invariant this.data.items === undefined || this.data.items.openingEdges === null || this.data.widths.length <= this.data.items.openingEdges.length
 *  @invariant this.data.items === undefined || this.data.items.insideExtras === null || this.data.widths.length <= this.data.items.insideExtras.length
 *  @invariant this.data.items === undefined || this.data.items.fillExtras === null || this.data.widths.length <= this.data.items.fillExtras.length
 *  @invariant 1 <= this.itemSegments.length
 *  @invariant this.segmentItems === null || this.segmentItems.length === this.data.widths.length
 *  @invariant this.gapSegments === null || this.gapSegments.length === this.data.widths.length
 *  @invariant this.segmentItems === null || forall k in this.segmentItems: safeInteger(this.segmentItems[k]) && 0 <= this.segmentItems[k] && this.segmentItems[k] + 1 < this.itemSegments.length
 */
type InternalPreparedRichInline = {
  // The paragraph's handle, which the text walkers lay out. A paragraph of one text item that isn't
  // atomic and has no extraWidth is that text's own handle, as prepareWithSegments() makes it. Its
  // letterSpacing is the one its text items share, atomic ones aside; where they differ it is 0,
  // and each segment's width and advances hold its item's letter spacing after every grapheme.
  data: PreparedSegments
  // The only item with segments, where it has no extraWidth, so that every line is one fragment
  // of it, as wide as the line; else -1.
  onlyItem: number
  // The paragraph's line where nothing wraps it, which is its only one at any width it fits:
  // its width, null where it has no line or several, as with a hard break, and its start and end
  // segments (findWholeLine).
  wholeWidth: number | null
  wholeStart: number
  wholeEnd: number
  // Per item, its first segment in the paragraph, then the segment count: an item's segments are
  // those up to the next item's first.
  itemSegments: Dense<number[]>
  // Per segment of a paragraph that isn't one text's handle, its item, and 1 where it is a
  // collapsed space at its item's start or end, which is the gap before the next fragment on its
  // line, else 0: a line's fragments are cut by them, with no search (createLine). Null for a
  // paragraph that is one text's handle.
  segmentItems: Int32Array | null
  gapSegments: Uint8Array | null
  // Whether each segment of such a paragraph is as wide on a line as its width, but the one a line
  // starts with or ends inside (createLine): no letter spacing the handle adds after a segment's
  // graphemes, no mark halted at its item's end, and no tab, whose advance depends on where the
  // line reaches it.
  plainWidths: boolean
  // Per segment, where its text starts and ends in its item's text, and, for a segment whose text
  // isn't one stretch of its item's, as where white space inside it was removed, where each of
  // its units is there, else null (null too where no segment has any). A paragraph that is one
  // text's handle finds them when a line is first materialized, from `text`, its item's; a
  // frozen one keeps them beside the handle, and these stay null (textSources).
  sourceStarts: Dense<number[]> | null
  sourceEnds: Dense<number[]> | null
  sourceUnits: Dense<(Dense<number[]> | null)[]> | null
  text: string
}

const RICH_INLINE_START_CURSOR: RichInlineCursor = {
  itemIndex: 0,
  segmentIndex: 0,
  graphemeIndex: 0,
}

function getInternalPreparedRichInline(prepared: PreparedRichInline): InternalPreparedRichInline {
  return prepared
}

export function prepareRichInline(items: Array<RichInlineItem | RichInlineBox>, options?: RichInlineOptions): PreparedRichInline {
  const whiteSpace = options?.whiteSpace ?? 'normal'
  const wordBreak = options?.wordBreak ?? 'normal'
  const preserve = (options?.whiteSpace ?? 'normal') === 'pre-wrap'
  // One language read for the paragraph's analysis and every item's measurement.
  const profile = getEngineProfile()
  const language = getPreparationLanguage(profile)
  // Whether a line can end before preserved white space that starts an item: WebKit finds a soft
  // wrap opportunity next to every white-space item (isAtSoftWrapOpportunity,
  // InlineFormattingUtils.cpp:406-418), which is part of how it finds breaks between inline items,
  // so the profile's scan names it.
  const whiteSpaceItemBreaks = profile.lineBreakScan === 'webkit'

  // A paragraph of one styled run that isn't atomic and has no extraWidth is the most common one,
  // and is that run's text: its handle is the one prepareWithSegments() makes, laid out as
  // layout()'s walkers lay it out. So is a paragraph whose other items are empty, which are
  // dropped (below).
  const itemCount = items.length
  if (itemCount === 0) {
    const emptySegments: Dense<string[]> = []
    const emptyWidths: Dense<number[]> = []
    const emptyAdvances: Dense<(number[] | null)[]> = []
    const emptyItemSegments: Dense<number[]> = [0]
    const emptySourceStarts: Dense<number[]> = []
    const emptySourceEnds: Dense<number[]> = []
    const emptySegmentData: ParagraphSegmentData = {
      hyphenWidths: null, tabStopAdvances: null, minimumTabAdvances: null,
      itemEndHalts: null, hyphenRooms: null,
      insideExtras: null, fillExtras: null, openingEdges: null,
      emptyObjectSpaces: null, emptyObjectReturns: null, hangEnds: null,
    }
    const emptyData: PreparedSegments = {
      widths: emptyWidths,
      segmentFlags: new Uint8Array(0),
      simpleLineWalkFastPath: true,
      simpleLineCountFastPath: false,
      breakableFitAdvances: emptyAdvances,
      letterSpacing: 0,
      discretionaryHyphenWidth: 0,
      discretionaryHyphenContexts: null,
      breakableLineStartExtras: null,
      lineStartExtras: null,
      lineEndTrims: null,
      overflowLineEndTrims: null,
      tabStopAdvance: 0,
      minimumTabAdvance: 0,
      items: emptySegmentData,
      segments: emptySegments,
    }
    return findWholeLine({
      data: emptyData, onlyItem: -1, wholeWidth: null, wholeStart: 0, wholeEnd: 0,
      itemSegments: emptyItemSegments, segmentItems: new Int32Array(0), gapSegments: new Uint8Array(0),
      plainWidths: true, sourceStarts: emptySourceStarts, sourceEnds: emptySourceEnds, sourceUnits: null, text: '',
    })
  }
  let onlyIndex: SafeInt = -1
  /** @invariant safeInteger(itemCount) && 0 < itemCount && itemCount === items.length && safeInteger(index) && 0 <= index && index <= itemCount && safeInteger(onlyIndex) && -1 <= onlyIndex && onlyIndex < itemCount */
  for (let index = 0; index < itemCount; index++) {
    if (items[index]!.text === '') continue
    if (onlyIndex >= 0) {
      onlyIndex = -1
      break
    }
    onlyIndex = index
  }
  const only = onlyIndex < 0 ? undefined : items[onlyIndex]
  if (onlyIndex >= 0 && only !== undefined && only.text !== undefined && only.break !== 'never' && (only.extraWidth ?? 0) === 0) {
    const analysis = analyzeText(only.text, profile, whiteSpace, wordBreak, language)
    const singleSegCount = analysis.flags.length
    const itemSegments: Dense<number[]> = []
    padItemSegments(itemSegments, onlyIndex, 0)
    padItemSegments(itemSegments, itemCount, singleSegCount)
    const segments: Dense<string[]> = []
    const data = prepareSingleSegments(analysis, singleSegCount, only.font, segments, readLetterSpacing(only.letterSpacing, profile), profile, language)
    return findWholeLine({
      data, onlyItem: onlyIndex, wholeWidth: null, wholeStart: 0, wholeEnd: 0, itemSegments, segmentItems: null, gapSegments: null, plainWidths: false,
      sourceStarts: null, sourceEnds: null, sourceUnits: null, text: only.text,
    })
  }

  // The paragraph's text: the items' texts joined, an atomic item or a box as one U+FFFC. An atomic
  // item's own white space is none of the paragraph's: its inline-block lays its text out as a
  // paragraph of its own, whose lines drop white space at their start and end. Blink puts the box in
  // the outer paragraph as one U+FFFC (inline_node.cc:408-422) and removes its own paragraph's
  // leading and trailing spaces (inline_items_builder.cc:869-871, ExitBlock at 1622-1629); WebKit's
  // atomic inline box is one item of the outer line (InlineItemsBuilder.cpp:1073-1074), and its own
  // lines collapse leading white space (Line::appendText, InlineLine.cpp:348-373) and remove
  // trailing (InlineLineBuilder.cpp:646); Gecko's text run stops at the box
  // (BuildTextRunsScanner::ScanFrame, nsTextFrame.cpp:2248-2254), and its own lines skip leading
  // white space (nsTextFrame.cpp:10935-10944) and trim trailing (nsBlockFrame.cpp:5844). So an
  // atomic item of only white space is still an object, as wide as its extraWidth. An item whose
  // text is empty, atomic or not, is dropped, with no fragment and no width: apps empty a run to
  // hide it (RESEARCH.md, Objects Inside A Line).
  let source = ''
  const starts: Dense<number[]> = []
  const atomic: Dense<boolean[]> = []
  // Whether an item is an object or has extraWidth, so that a line of it alone isn't its text's.
  let paddedOrObject = false
  // How many text items have extraWidth: each may get one segment more than the analysis gives it,
  // the start edge of its opening (below).
  let padded = 0
  // The letter spacing the text items that aren't atomic share, and whether two of them differ: the
  // walkers take one for the handle, so where items differ, each segment's width holds its own.
  let sharedSpacing: number | null = null
  let spacingsDiffer = false
  // Whether an item may make a line narrower: under a negative letter spacing or extraWidth.
  let mayNarrow = false
  // PAPER: workaround (coarse-effect framing in loop): pre-measure atomic items before the main loop because measureAtomicItem calls analyzeText (coarse effects)
  let atomicMeasures: Dense<(AtomicMeasure | null)[]> | null = null
  /** @invariant safeInteger(padded) && 0 <= padded && safeInteger(index) && 0 <= index && index <= items.length && 0 < items.length && starts.length === index && atomic.length === index && items !== starts && items !== atomic && starts !== atomic
   *  @invariant atomicMeasures === null || atomicMeasures.length === items.length && atomicMeasures !== items && atomicMeasures !== starts && atomicMeasures !== atomic */
  for (let index = 0; index < items.length; index++) {
    const item = items[index]!
    starts.push(source.length)
    if (item.text === undefined) {
      // A width that isn't finite would give lines of width NaN or Infinity, and Chrome breaks lines
      // around a negative one otherwise than a negative extraWidth does (RESEARCH.md, Objects Inside
      // A Line), so Pretext refuses both.
      if (!Number.isFinite(item.width) || item.width < 0) throw new RangeError(`Item ${index} has no text, so it's a box, whose width must be a finite number of CSS px, at least 0, not ${item.width}`)
      atomic.push(true)
      source += '￼'
      paddedOrObject = true
      continue
    }
    const isAtomic = (item.break ?? 'normal') === 'never' && item.text !== ''
    atomic.push(isAtomic)
    if (isAtomic) {
      source += '￼'
      const measured = measureAtomicItem(item, profile, wordBreak, language)
      const measures = atomicMeasures ?? (atomicMeasures = new Array<AtomicMeasure | null>(items.length).fill(null))
      measures[index] = measured
    } else {
      source += item.text
      if (item.text !== '') {
        const letterSpacing = readLetterSpacing(item.letterSpacing, profile)
        if (sharedSpacing !== null && sharedSpacing !== letterSpacing) spacingsDiffer = true
        sharedSpacing ??= letterSpacing
        if (letterSpacing < 0) mayNarrow = true
      }
    }
    if (isAtomic || (item.extraWidth ?? 0) !== 0) paddedOrObject = true
    if (!isAtomic && (item.extraWidth ?? 0) !== 0) padded++
    if ((item.extraWidth ?? 0) < 0) mayNarrow = true
  }
  const paragraph: ParagraphItems = { items, starts, atomic, ownSegmentBreaks: !profile.transformsSegmentBreaksAcrossItems, sourceOffsets: null }
  const analysis = analyzeText(source, profile, whiteSpace, wordBreak, language, paragraph)
  const offsets = paragraph.sourceOffsets
  if (offsets === undefined || offsets === null) throw new RangeError('missing value')
  const count: SafeInt = analysis.flags.length

  // The paragraph's lists, which each item's measurement adds its segments to (measureAnalysis).
  const widths: Dense<number[]> = []
  const flags = new Uint8Array(count + padded)
  const breakableFitAdvances: Dense<(number[] | null)[]> = []
  const segments: Dense<string[]> = []
  const sourceStarts: Dense<number[]> = []
  const sourceEnds: Dense<number[]> = []
  // PAPER: workaround (sparse arrays / Map conversion): collect sparse sourceUnits in Map and materialize after the main loop
  const sourceUnitsMap = new Map<number, Dense<number[]>>()
  let hasSourceUnits = false
  const itemSegments: Dense<number[]> = []
  // What only some segments have, each made whole at the first one that does: a zero or a null for
  // every segment the paragraph can have, `flags.length` of them, which is more than it has where
  // a padded item gets no start edge, and the segment's value stored at its index. Chrome 154,
  // Firefox 156 and Safari 27 prepare CJK styled paragraphs again up to 8% faster with the lists
  // made whole than with each filled by a call and a push a segment (RESEARCH.md, Keeping Work
  // Bounded, JavaScript Engines, under A paragraph's sparse lists made whole).
  // PAPER: workaround (sparse arrays / Map conversion): collect sparse breakableLineStartExtras in Map and validate/materialize after the main loop so sparse writes do not clobber breakableFitAdvances invariants
  const breakableLineStartExtrasMap = new Map<number, number[]>()
  let hasBreakableLineStartExtras = false
  let lineStartExtras: Dense<number[]> | null = null
  let lineEndTrims: Dense<number[]> | null = null
  let overflowLineEndTrims: Dense<number[]> | null = null
  let itemEndHalts: Dense<number[]> | null = null
  // A line returns from a soft hyphen whose hyphen doesn't fit on a handle with soft-hyphen
  // contexts, which an item's measurement makes for text with one.
  let discretionaryHyphenContexts: Dense<number[]> | null = null
  let insideExtras: Dense<number[]> | null = null
  let fillExtras: Dense<number[]> | null = null
  let openingEdges: Dense<number[]> | null = null
  // Each text item's hyphen width, tab stop advance and least tab advance, and whether two items
  // differ in one, in a paragraph whose text has what reads them: a soft hyphen or, preserved, a
  // tab (ParagraphSegmentData). Another paragraph keeps none, and its handle's own are 0.
  const readsItemFonts = source.includes('\u00AD') || (preserve && source.includes('\t'))
  const hyphenWidths: Dense<number[]> = zeros(readsItemFonts ? items.length : 0)
  const tabStopAdvances: Dense<number[]> = zeros(readsItemFonts ? items.length : 0)
  const minimumTabAdvances: Dense<number[]> = zeros(readsItemFonts ? items.length : 0)
  let hasFirstTextItem = false
  let firstHyphenWidth = 0
  let firstTabStopAdvance = 0
  let firstMinimumTabAdvance = 0
  let fontsDiffer = false
  let simple = !analysis.hasUnbroken
  // Whether a segment got no break before it here (below), an item's start edge or white space that
  // goes on from the item before, in a paragraph whose analysis found none, so its other segments
  // aren't marked as breaks to return to.
  let marksReturnable = false
  // Where the item at hand starts among the paragraph's segments.
  let itemStart = 0
  // Whether the paragraph holds an object of width 0.
  let hasEmptyObject = false

  let segs: SafeInt = 0
  /** @invariant safeInteger(from) && safeInteger(segs) && 0 <= from && from <= count && count <= analysis.flags.length && count <= analysis.starts.length && count <= analysis.texts.length && segs === widths.length && widths.length === breakableFitAdvances.length && segs + count <= flags.length + from
   *  @invariant 0 < items.length && starts.length === items.length && itemSegments.length <= items.length
   *  @invariant readsItemFonts === false || hyphenWidths.length === items.length
   *  @invariant readsItemFonts === false || tabStopAdvances.length === items.length
   *  @invariant readsItemFonts === false || minimumTabAdvances.length === items.length
   *  @invariant widths !== breakableFitAdvances && widths !== analysis.flags && widths !== analysis.starts && widths !== analysis.texts && widths !== itemSegments && widths !== segments && widths !== sourceStarts && widths !== sourceEnds && widths !== starts && widths !== hyphenWidths && widths !== tabStopAdvances && widths !== minimumTabAdvances
   *  @invariant breakableFitAdvances !== analysis.flags && breakableFitAdvances !== analysis.starts && breakableFitAdvances !== analysis.texts && breakableFitAdvances !== itemSegments && breakableFitAdvances !== segments && breakableFitAdvances !== sourceStarts && breakableFitAdvances !== sourceEnds && breakableFitAdvances !== starts && breakableFitAdvances !== hyphenWidths && breakableFitAdvances !== tabStopAdvances && breakableFitAdvances !== minimumTabAdvances
   *  @invariant itemSegments !== segments && itemSegments !== sourceStarts && itemSegments !== sourceEnds && itemSegments !== starts && itemSegments !== hyphenWidths && itemSegments !== tabStopAdvances && itemSegments !== minimumTabAdvances
   *  @invariant lineStartExtras === null || flags.length <= lineStartExtras.length && lineStartExtras !== widths && lineStartExtras !== itemSegments && lineStartExtras !== breakableFitAdvances
   *  @invariant lineEndTrims === null || flags.length <= lineEndTrims.length && lineEndTrims !== widths && lineEndTrims !== itemSegments && lineEndTrims !== breakableFitAdvances
   *  @invariant overflowLineEndTrims === null || flags.length <= overflowLineEndTrims.length && overflowLineEndTrims !== widths && overflowLineEndTrims !== itemSegments && overflowLineEndTrims !== breakableFitAdvances
   *  @invariant itemEndHalts === null || flags.length <= itemEndHalts.length && itemEndHalts !== widths && itemEndHalts !== itemSegments && itemEndHalts !== breakableFitAdvances
   *  @invariant openingEdges === null || flags.length <= openingEdges.length && openingEdges !== widths && openingEdges !== itemSegments && openingEdges !== breakableFitAdvances
   *  @invariant discretionaryHyphenContexts === null || flags.length <= discretionaryHyphenContexts.length && discretionaryHyphenContexts !== widths && discretionaryHyphenContexts !== breakableFitAdvances && discretionaryHyphenContexts !== itemSegments
   *  @invariant insideExtras === null || flags.length <= insideExtras.length && insideExtras !== widths && insideExtras !== itemSegments && insideExtras !== breakableFitAdvances
   *  @invariant fillExtras === null || flags.length <= fillExtras.length && fillExtras !== widths && fillExtras !== itemSegments && fillExtras !== breakableFitAdvances
   *  @invariant forall i in breakableFitAdvances: breakableFitAdvances[i] === null || 1 <= breakableFitAdvances[i].length */   // PAPER: annotation
  for (let from: SafeInt = 0; from < count;) {
    // The item this segment starts in, and the segments that start in it.
    const offset = offsets[analysis.starts[from]!]
    if (offset === undefined) throw new RangeError('missing value')
    const index = findItemIndex(starts, itemSegments.length === 0 ? 0 : itemSegments.length - 1, offset, starts.length)
    const item = items[index]!
    padItemSegments(itemSegments, index, widths.length)
    const itemEnd = index + 1 < starts.length ? starts[index + 1]! : source.length
    const to = findItemEnd(analysis, offsets, from, count, itemEnd)

    const measuredAtomic = atomicMeasures !== null ? (atomicMeasures[index] ?? null) : null
    if (measuredAtomic !== null || item.text === undefined) {
      // PAPER: workaround (Linear.elimSteps cap of 64): advance `from` before itemStart/widths.push/segs++ so projecting out old `from` stays under 64 pairs and preserves `segs + (count - from) <= flags.length`
      from = to
      // One object: a box's width, or the width of the item's text on a line of its own, laid out
      // in normal white space, as a chip's box with `white-space: nowrap` collapses its own, plus
      // its extraWidth: all three browsers lay out a pre-wrap paragraph of 15px Helvetica Neue with
      // the 12px chip ` @bob ` 6.6px narrower than the chip's text with its spaces. It is prepared
      // without emergency breaks, as it is only laid out whole.
      let width = 0
      let text = ''
      let textStart = 0
      let textEnd = 0
      if (item.text === undefined) {
        width = item.width
      } else if (measuredAtomic !== null) {
        width = measuredAtomic.width
        text = measuredAtomic.text
        textStart = measuredAtomic.textStart
        textEnd = measuredAtomic.textEnd
      }
      // Gecko places an object of width 0 otherwise than the simple walker does (walkPreparedComplexLines).
      if (width === 0) {
        simple = false
        hasEmptyObject = true
      }
      itemStart = widths.length
      flags[widths.length] = OBJECT
      widths.push(width)
      segs++
      segments.push(text)
      breakableFitAdvances.push(null)
      sourceStarts.push(textStart)
      sourceEnds.push(textEnd)
      continue
    }

    const letterSpacing = readLetterSpacing(item.letterSpacing, profile)
    if (to === from + 1 && (analysis.flags[from]! & KIND_BITS) === SPACE && analysis.texts[from] === ' ') {
      const spaceFlags = analysis.flags[from]!
      // PAPER: workaround (Linear.elimSteps cap of 64): advance `from` before reading `widths.length` (`itemStart`) or writing `flags` so projecting out old `from` stays under 64 pairs
      from = to
      itemStart = widths.length
      // An item of only collapsible white space, as between two styled words: its one space, as
      // measureAnalysis() measures one.
      if (letterSpacing !== 0) simple = false
      flags[widths.length] = SPACE | (spaceFlags & (UNBROKEN | RETURNABLE)) | (letterSpacing !== 0 ? SPACED : 0)
      widths.push(getSpaceWidth(getFontMeasurement(item.font, language, letterSpacing !== 0)) + (spacingsDiffer ? letterSpacing : 0))
      segs++
      segments.push(' ')
      breakableFitAdvances.push(null)
      sourceStarts.push(offset - starts[index]!)
      sourceEnds.push(offset + 1 - starts[index]!)
      continue
    }
    const previousItemStart = itemStart
    itemStart = widths.length
    // Every line the item reaches pays its extraWidth, as its fragment on that line paints it
    // (box-decoration-break: clone). The first of its segments whose width a line counts, after
    // the collapsed space before its text, holds it for a line that comes into the item or starts
    // with it, and a line that starts later in the item pays it there (ParagraphSegmentData). An
    // item that opens with preserved white space, a hard break or a zero-width space, which a line
    // can end with after content that fills it, gets a start edge of its own before them: an empty
    // segment as wide as the extraWidth, which fits by the edges the engine fits where a line takes
    // the item's opening and no more of it (getOpeningFit), and no break comes before it, as none
    // comes before white space, a hard break or a zero-width space in the text (UAX #14 LB6, LB7),
    // but after an object in Blink and Gecko, and before a zero-width space after an object or
    // white space, where the browsers break.
    const extraWidth = item.extraWidth ?? 0
    let first = to
    if (extraWidth !== 0) {
      first = findFirstContent(analysis.flags, from, to)
      const firstKind = first < to ? analysis.flags[first]! & KIND_BITS : TEXT
      if (firstKind === PRESERVED_SPACE || firstKind === TAB || firstKind === HARD_BREAK || (firstKind === ZERO_WIDTH_BREAK && first === from)) {
        const at = segs
        if (at + (count - from) >= flags.length) throw new RangeError('index')   // PAPER: workaround (accumulated segment count bound): SinglePass does not track opening-edge count <= padded across the outer loop
        const afterObject = at > 0 && (flags[at - 1]! & KIND_BITS) === OBJECT
        // Whether the item follows preserved spaces that follow text in their own text item. Blink
        // ends a text item at each character it makes a control item (IsControlItemCharacter,
        // inline_items_builder.cc:177-184; AppendPreserveWhitespace, :1082-1126): a run of preserved
        // tabs (:1098-1110), a line feed, whose forced break the spaces after it follow as a text item
        // of their own (:1084-1097, 1023-1033), and a lone CR or FF (:1119-1125), which the analysis
        // takes as a line feed. So spaces after a tab or a hard break, which is a line feed in the
        // one profile that reads this, follow no text. A ZWNJ, the other such character, starts a
        // text item and is text in it (:1112-1118), as it is here. An item of only spaces after its
        // own start edge follows none either. Blink also ends a text item where a bidi run ends
        // inside it (InlineItem::SetBidiLevel, inline_item.cc:207-236), which no profile resolves:
        // the premise is that the spaces are at the level of the text before them, and its gap is
        // spaces after right-to-left text (ENGINE_FOLLOWUPS.md, Rich-inline item edges).
        const afterTextSpaces = at - 1 > previousItemStart && ((flags[at - 1] ?? missing()) & KIND_BITS) === PRESERVED_SPACE && (1 << ((flags[at - 2] ?? missing()) & KIND_BITS) & (1 << TAB | 1 << HARD_BREAK)) === 0 &&
          (openingEdges === null || openingEdges[at - 2] === 0)
        const fit = getOpeningFit(analysis.flags, from, to, extraWidth, afterTextSpaces, profile)
        // In WebKit a break comes before white space that starts an item (whiteSpaceItemBreaks), and
        // none before a hard break, after an object too (nextWrapOpportunity,
        // InlineFormattingUtils.cpp:469-475).
        const breaksBefore = at === 0 || (firstKind === ZERO_WIDTH_BREAK ? afterObject || (1 << (flags[at - 1]! & KIND_BITS) & (1 << SPACE | PRESERVED_WHITE_SPACE)) !== 0
          : whiteSpaceItemBreaks ? firstKind !== HARD_BREAK : afterObject)
        // A line that takes the opening paints the whole edge, whatever of it the line fitted
        // (ParagraphSegmentData, openingEdges). An opening no edge of which is fitted takes no room
        // among the white space around it, which hangs past it. Else it is an object, whose line-end
        // trim is what the line doesn't fit: the white space after it stays on its line, as the line
        // keeps the opening it took.
        flags[at] = fit === 0 ? PRESERVED_SPACE : breaksBefore ? OBJECT : OBJECT | UNBROKEN
        widths.push(extraWidth)
        segs++
        openingEdges ??= zeroList(flags.length)
        openingEdges[at] = extraWidth
        if (!breaksBefore && !analysis.hasUnbroken) marksReturnable = true
        // Where the engine ends a line inside the preserved spaces before a padded hard break that
        // doesn't fit (hardBreakItemRetreat), those spaces get an advance each, as text a line can
        // end inside has.
        if (firstKind === HARD_BREAK && !breaksBefore && at > 0 && profile.hardBreakItemRetreat !== 'item' && (flags[at - 1]! & KIND_BITS) === PRESERVED_SPACE) {
          const prevSegment = segments[at - 1] ?? missing()
          if (prevSegment !== '') {
            const spaces = prevSegment.length
            const advances = equalAdvances(widths[at - 1]!, spaces)
            const idx = at - 1
            if (hasBreakableLineStartExtras) breakableLineStartExtrasMap.delete(idx)
            breakableFitAdvances[idx] = advances
          }
        }
        // The simple walkers take every boundary for a break and a line-end trim out of the line's width.
        simple = false
        segments.push('')
        breakableFitAdvances.push(null)
        // The edge comes before the item's segments, so before the space or soft hyphens that lead them.
        sourceStarts.push(offset - starts[index]!)
        sourceEnds.push(offset - starts[index]!)
        if (fit !== 0 && fit !== extraWidth) {
          lineEndTrims ??= zeroList(flags.length)
          lineEndTrims[at] = extraWidth - fit
        }
        first = from - 1
      }
    }
    // An item that is one segment holding all of its text, as a styled word, is measured by the
    // item's own string, not the equal slice of the paragraph's text: a font's widths are kept by
    // text, and a string the caller hands in again keeps its hash, where the slice is hashed anew
    // at every preparation.
    if (to === from + 1 && analysis.texts[from] === item.text) {
      analysis.texts[from] = item.text
    }
    // The item's segments, measured in its font onto the end of the paragraph's lists; `sub` holds
    // what else measurement gives them, from the item's first segment.
    const itemAt = segs
    const sub = measureParagraphAnalysis(analysis, from, to, item.font, letterSpacing, profile, language, widths, flags, breakableFitAdvances, itemAt)
    simple &&= sub.simpleLineCountFastPath
    /** @invariant safeInteger(i) && safeInteger(from) && safeInteger(to) && safeInteger(itemAt) && safeInteger(segs) && safeInteger(index) && 0 <= from && from <= i && i <= to && to <= count && count <= analysis.flags.length && count <= analysis.starts.length && count <= analysis.texts.length && 0 <= itemAt && segs === itemAt && 0 <= index && index < items.length && widths.length === itemAt + (to - from) && breakableFitAdvances.length === widths.length && widths.length + count <= flags.length + to
     *  @invariant 0 < items.length && starts.length === items.length && itemSegments.length <= items.length
     *  @invariant readsItemFonts === false || hyphenWidths.length === items.length
     *  @invariant readsItemFonts === false || tabStopAdvances.length === items.length
     *  @invariant readsItemFonts === false || minimumTabAdvances.length === items.length
     *  @invariant sub.lineStartExtras === null || to - from <= sub.lineStartExtras.length
     *  @invariant sub.lineEndTrims === null || to - from <= sub.lineEndTrims.length
     *  @invariant sub.overflowLineEndTrims === null || to - from <= sub.overflowLineEndTrims.length
     *  @invariant widths !== breakableFitAdvances && widths !== analysis.flags && widths !== analysis.starts && widths !== analysis.texts && widths !== itemSegments && widths !== segments && widths !== sourceStarts && widths !== sourceEnds && widths !== starts && widths !== hyphenWidths && widths !== tabStopAdvances && widths !== minimumTabAdvances
     *  @invariant breakableFitAdvances !== analysis.flags && breakableFitAdvances !== analysis.starts && breakableFitAdvances !== analysis.texts && breakableFitAdvances !== itemSegments && breakableFitAdvances !== segments && breakableFitAdvances !== sourceStarts && breakableFitAdvances !== sourceEnds && breakableFitAdvances !== starts && breakableFitAdvances !== hyphenWidths && breakableFitAdvances !== tabStopAdvances && breakableFitAdvances !== minimumTabAdvances
     *  @invariant itemSegments !== segments && itemSegments !== sourceStarts && itemSegments !== sourceEnds && itemSegments !== starts && itemSegments !== hyphenWidths && itemSegments !== tabStopAdvances && itemSegments !== minimumTabAdvances
     *  @invariant lineStartExtras === null || flags.length <= lineStartExtras.length && lineStartExtras !== widths && lineStartExtras !== itemSegments && lineStartExtras !== breakableFitAdvances
     *  @invariant lineEndTrims === null || flags.length <= lineEndTrims.length && lineEndTrims !== widths && lineEndTrims !== itemSegments && lineEndTrims !== breakableFitAdvances
     *  @invariant overflowLineEndTrims === null || flags.length <= overflowLineEndTrims.length && overflowLineEndTrims !== widths && overflowLineEndTrims !== itemSegments && overflowLineEndTrims !== breakableFitAdvances
     *  @invariant itemEndHalts === null || flags.length <= itemEndHalts.length && itemEndHalts !== widths && itemEndHalts !== itemSegments && itemEndHalts !== breakableFitAdvances
     *  @invariant openingEdges === null || flags.length <= openingEdges.length && openingEdges !== widths && openingEdges !== itemSegments && openingEdges !== breakableFitAdvances
     *  @invariant discretionaryHyphenContexts === null || flags.length <= discretionaryHyphenContexts.length && discretionaryHyphenContexts !== widths && discretionaryHyphenContexts !== breakableFitAdvances && discretionaryHyphenContexts !== itemSegments
     *  @invariant insideExtras === null || flags.length <= insideExtras.length && insideExtras !== widths && insideExtras !== itemSegments && insideExtras !== breakableFitAdvances
     *  @invariant fillExtras === null || flags.length <= fillExtras.length && fillExtras !== widths && fillExtras !== itemSegments && fillExtras !== breakableFitAdvances
     *  @invariant forall k in breakableFitAdvances: breakableFitAdvances[k] === null || 1 <= breakableFitAdvances[k].length */   // PAPER: annotation
    for (let i = from; i < to; i++) {
      const s = i - from
      const at = itemAt + s
      const spaced = spacingsDiffer && (flags[at]! & SPACED) !== 0
      const holdsExtra = i === first
      if (spaced || holdsExtra) {
        const origAdvances = breakableFitAdvances[at] ?? null
        if (origAdvances !== null) {
          // The cached advances are shared by every occurrence of this text.
          const advances = adjustRichAdvances(origAdvances, spaced, holdsExtra, letterSpacing, extraWidth)
          breakableFitAdvances[at] = advances
        }
        if (spaced) {
          widths[at] = widths[at]! + letterSpacing
        }
        if (holdsExtra) {
          widths[at] = widths[at]! + extraWidth
        }
      }
      // No break comes before white space (UAX #14 LB7), so none inside a run of preserved spaces
      // and tabs that goes on from the item before, but in WebKit (whiteSpaceItemBreaks).
      if (s === 0 && at > 0 && !whiteSpaceItemBreaks && (1 << (flags[at]! & KIND_BITS) & PRESERVED_WHITE_SPACE) !== 0 && (1 << (flags[at - 1]! & KIND_BITS) & PRESERVED_WHITE_SPACE) !== 0) {
        flags[at] = flags[at]! | UNBROKEN
        if (!analysis.hasUnbroken) marksReturnable = true
      }
      const normalizedStart = analysis.starts[i]!
      const normalizedEnd = i + 1 < count ? analysis.starts[i + 1]! : analysis.normalized.length
      const sourceEnd = (offsets[normalizedEnd - 1] ?? missing()) + 1
      // Where the segment's text ends in the normalized text.
      let textEnd = normalizedEnd
      sourceStarts.push((offsets[normalizedStart] ?? missing()) - starts[index]!)
      if (sourceEnd > itemEnd) {
        // The Gecko analysis keeps the soft hyphens and bidi controls Firefox's text run drops with
        // the segment before them, across items: the segment's text here is its own item's part, and
        // the rest, which paints nothing, is in no fragment.
        textEnd = trimTextEnd(offsets, textEnd, itemEnd)
        segments.push(analysis.normalized.slice(normalizedStart, textEnd))
        sourceEnds.push(itemEnd - starts[index]!)
      } else {
        segments.push(analysis.texts[i]!)
        // CRLF is one line feed, which ends with the item where the next item holds the line feed.
        sourceEnds.push((preserve && sourceEnd < itemEnd && source.charCodeAt(sourceEnd - 1) === 0x0D && source.charCodeAt(sourceEnd) === 0x0A ? sourceEnd + 1 : sourceEnd) - starts[index]!)
      }
      const units = getSourceUnits(offsets, normalizedStart, textEnd, starts[index]!)
      if (units !== null) {
        hasSourceUnits = true
        sourceUnitsMap.set(at, units)
      }
      const subStartExtras = sub.breakableLineStartExtras
      if (subStartExtras !== null) {
        const subStartExtra = subStartExtras[s] ?? null
        if (subStartExtra !== null) {
          hasBreakableLineStartExtras = true
          breakableLineStartExtrasMap.set(at, subStartExtra)
        }
      }
      const startExtra = (sub.lineStartExtras === null ? 0 : sub.lineStartExtras[s]!) + (i > first ? extraWidth : 0)
      if (startExtra !== 0) {
        lineStartExtras ??= zeroList(flags.length)
        lineStartExtras[at] = startExtra
      }
      if (sub.lineEndTrims !== null) {
        const endTrim = sub.lineEndTrims[s]!
        if (endTrim !== 0) {
          lineEndTrims ??= zeroList(flags.length)
          lineEndTrims[at] = endTrim
        }
        // A closing mark that ends its item, halted at a line's end, stays halted where the line
        // goes on. Blink breaks an item's text that doesn't fit its line, and where the text fits
        // with its last mark halted, which it tries where a break comes right after the mark, that
        // is the item's result, and the line takes what follows after it
        // (ShapingLineBreaker::ShapeLine, shaping_line_breaker.cc:342-363; LineBreaker::BreakText,
        // line_breaker.cc:1736-1758): in 16px Hiragino Sans, Chrome 154 lays out `文字」` and a span
        // `i` as one 43.81px line at 44-47px. A run of U+3000 that ends the item has a line-end
        // trim too, its hang, which is no halt. An item with extraWidth keeps the halt at a line's
        // end only. Blink fits its text before its end edge: where the text fits there the mark
        // stays whole though the edge overflows, so Chrome leaves the mark of a span `文字」` with
        // 4px of padding on each side whole at 52-55px and wraps the `i` after it, and where it
        // doesn't the mark is halted and the line goes on, as at 51.81-51.94px, where the `i`
        // fits after it. The extraWidth doesn't split the end edge off, so the line can't tell
        // the two and takes the first for both. Its gap is what follows such a mark and is
        // narrower than the halt less that edge, which wraps where Chrome keeps it
        // (ENGINE_FOLLOWUPS.md, Rich-inline item edges). The walkers that take every boundary for
        // a break end the line after a trimmed segment, so the paragraph isn't theirs.
        if (endTrim !== 0 && i === to - 1 && to < count && extraWidth === 0 && !analysis.texts[i]!.endsWith('\u3000')) {
          itemEndHalts ??= zeroList(flags.length)
          itemEndHalts[at] = endTrim
          simple = false
        }
      }
      if (sub.overflowLineEndTrims !== null) {
        const retryTrim = sub.overflowLineEndTrims[s]!
        if (retryTrim !== 0) {
          overflowLineEndTrims ??= zeroList(flags.length)
          overflowLineEndTrims[at] = retryTrim
        }
        // Where no break comes after the mark, as before a period or a no-break space that starts
        // the next item, Blink halts it only on a line it lays out again with a break after every
        // grapheme (HandleOverflow, line_breaker.cc:4259-4264), and there too the halted text is the
        // item's result and the line goes on: Chrome 154 lays out `文字」`, a span `.` and `字` as
        // `文` / `字」.` / `字` at 28.5-31.75px, where their text in one node ends the second line
        // after the mark.
        if (retryTrim !== 0 && i === to - 1 && to < count && extraWidth === 0) {
          itemEndHalts ??= zeroList(flags.length)
          itemEndHalts[at] = retryTrim
          simple = false
        }
      }
      const subContexts = sub.discretionaryHyphenContexts
      if (subContexts !== null) {
        discretionaryHyphenContexts ??= zeroList(flags.length)
        const discretionaryHyphenContextsValue = subContexts[s]
        if (discretionaryHyphenContextsValue === undefined) throw new RangeError('missing value')
        discretionaryHyphenContexts[at] = discretionaryHyphenContextsValue
      }
      if (i >= first && first < to) {
        insideExtras ??= zeroList(flags.length)
        insideExtras[at] = extraWidth
      }
      if (i > first && first < to) {
        fillExtras ??= zeroList(flags.length)
        fillExtras[at] = extraWidth
      }
    }
    // PAPER: workaround (dense-write ordering): update item font tables after the inner loop to keep sub field facts intact across inner loop
    if (readsItemFonts) {
      // The gap before the hyphen is the letter spacing after the grapheme before it.
      const hw = spacingsDiffer ? sub.discretionaryHyphenWidth - letterSpacing : sub.discretionaryHyphenWidth
      const ts = sub.tabStopAdvance
      const mt = sub.minimumTabAdvance
      hyphenWidths[index] = hw
      tabStopAdvances[index] = ts
      minimumTabAdvances[index] = mt
      if (!hasFirstTextItem) {
        hasFirstTextItem = true
        firstHyphenWidth = hw
        firstTabStopAdvance = ts
        firstMinimumTabAdvance = mt
      } else if (hw !== firstHyphenWidth || ts !== firstTabStopAdvance || mt !== firstMinimumTabAdvance) {
        fontsDiffer = true
      }
    }
    segs = widths.length
    from = to
  }
  const segmentCount: SafeInt = widths.length
  padItemSegments(itemSegments, items.length, segmentCount)

  let onlyItem: SafeInt = -1
  /** @invariant safeInteger(segmentCount) && 0 < items.length && starts.length === items.length && itemSegments.length === items.length + 1 && widths.length === segmentCount && breakableFitAdvances.length === segmentCount && segmentCount <= flags.length
   *  @invariant readsItemFonts === false || hyphenWidths.length === items.length
   *  @invariant readsItemFonts === false || tabStopAdvances.length === items.length
   *  @invariant readsItemFonts === false || minimumTabAdvances.length === items.length
   *  @invariant lineStartExtras === null || segmentCount <= lineStartExtras.length
   *  @invariant lineEndTrims === null || segmentCount <= lineEndTrims.length
   *  @invariant overflowLineEndTrims === null || segmentCount <= overflowLineEndTrims.length
   *  @invariant itemEndHalts === null || segmentCount <= itemEndHalts.length
   *  @invariant openingEdges === null || segmentCount <= openingEdges.length
   *  @invariant insideExtras === null || segmentCount <= insideExtras.length
   *  @invariant fillExtras === null || segmentCount <= fillExtras.length
   *  @invariant forall i in breakableFitAdvances: breakableFitAdvances[i] === null || 1 <= breakableFitAdvances[i].length */   // PAPER: annotation
  for (let index = 0; index < items.length && !paddedOrObject; index++) {
    if (itemSegments[index] === itemSegments[index + 1]) continue
    if (onlyItem >= 0) {
      onlyItem = -1
      break
    }
    onlyItem = index
  }

  const segmentFlags = segmentCount === flags.length ? flags : flags.subarray(0, segmentCount)
  // A paragraph whose lines return from an unfit hyphen marks every break the scan gives before
  // text, so its walk records each as the line's latest break (pendingBreakSegmentIndex in
  // walkPreparedComplexLines). The return itself reads no mark, as a text's doesn't; what the marks
  // still decide is where the Gecko profile ends a line that an object of width 0 sticks out of
  // (ENGINE_FOLLOWUPS.md, Rich-inline item edges).
  const doMarksReturnable = marksReturnable || (discretionaryHyphenContexts !== null && !analysis.hasUnbroken)
  const gapSegments = new Uint8Array(segmentCount)
  // Each item is a text frame: a zero-width space after preserved spaces of its own item ends
  // the run of them that hangs (ParagraphSegmentData, hangEnds).
  const trackHangEnds = preserve && profile.hangsSpacesPerTextFrame && source.includes('\u200B')
  const hangBuf = new Uint8Array(trackHangEnds ? segmentCount : 0)
  let hasHangEnds = false
  let itemIndex: SafeInt = 0
  let prevItemIndex = -1
  /** @invariant safeInteger(segmentCount) && safeInteger(itemIndex) && 0 <= itemIndex && itemIndex < items.length && starts.length === items.length && itemSegments.length === items.length + 1 && segmentFlags.length === segmentCount && gapSegments.length === segmentCount && widths.length === segmentCount && breakableFitAdvances.length === segmentCount
   *  @invariant trackHangEnds === false || hangBuf.length === segmentCount
   *  @invariant readsItemFonts === false || hyphenWidths.length === items.length
   *  @invariant readsItemFonts === false || tabStopAdvances.length === items.length
   *  @invariant readsItemFonts === false || minimumTabAdvances.length === items.length
   *  @invariant lineStartExtras === null || segmentCount <= lineStartExtras.length
   *  @invariant lineEndTrims === null || segmentCount <= lineEndTrims.length
   *  @invariant overflowLineEndTrims === null || segmentCount <= overflowLineEndTrims.length
   *  @invariant itemEndHalts === null || segmentCount <= itemEndHalts.length
   *  @invariant openingEdges === null || segmentCount <= openingEdges.length
   *  @invariant insideExtras === null || segmentCount <= insideExtras.length
   *  @invariant fillExtras === null || segmentCount <= fillExtras.length
   *  @invariant forall j in breakableFitAdvances: breakableFitAdvances[j] === null || 1 <= breakableFitAdvances[j].length */   // PAPER: annotation
  for (let i = 0; i < segmentCount; i++) {
    if (doMarksReturnable && (segmentFlags[i]! & UNBROKEN) === 0) segmentFlags[i] = segmentFlags[i]! | RETURNABLE
    itemIndex = findItemIndex(itemSegments, itemIndex, i, items.length)
    if ((i === itemSegments[itemIndex]! || i === itemSegments[itemIndex + 1]! - 1) && (segmentFlags[i]! & KIND_BITS) === SPACE && (segments[i] ?? missing()).length === 1) gapSegments[i] = 1
    if (trackHangEnds && i > 0 && itemIndex === prevItemIndex && (segmentFlags[i]! & (KIND_BITS | DROPPED)) === ZERO_WIDTH_BREAK && (segmentFlags[i - 1]! & KIND_BITS) === PRESERVED_SPACE) {
      hangBuf[i] = 1
      hasHangEnds = true
    }
    prevItemIndex = itemIndex
  }
  const hangEnds = hasHangEnds ? hangBuf : null

  if (items.length > 2147483647) throw new RangeError('Too many rich-text inline items')
  const segmentItems = new Int32Array(segmentCount)
  let segItemIdx: SafeInt = 0
  let segIdx: SafeInt = 0
  /** @invariant safeInteger(segmentCount) && safeInteger(segIdx) && safeInteger(segItemIdx) && 0 <= segIdx && segIdx <= segmentCount && 0 <= segItemIdx && segItemIdx < items.length && items.length <= 2147483647 && starts.length === items.length && itemSegments.length === items.length + 1 && segmentFlags.length === segmentCount && segmentItems.length === segmentCount && gapSegments.length === segmentCount && widths.length === segmentCount && breakableFitAdvances.length === segmentCount
   *  @invariant readsItemFonts === false || hyphenWidths.length === items.length
   *  @invariant readsItemFonts === false || tabStopAdvances.length === items.length
   *  @invariant readsItemFonts === false || minimumTabAdvances.length === items.length
   *  @invariant lineStartExtras === null || segmentCount <= lineStartExtras.length
   *  @invariant lineEndTrims === null || segmentCount <= lineEndTrims.length
   *  @invariant overflowLineEndTrims === null || segmentCount <= overflowLineEndTrims.length
   *  @invariant itemEndHalts === null || segmentCount <= itemEndHalts.length
   *  @invariant openingEdges === null || segmentCount <= openingEdges.length
   *  @invariant insideExtras === null || segmentCount <= insideExtras.length
   *  @invariant fillExtras === null || segmentCount <= fillExtras.length
   *  @invariant forall j in breakableFitAdvances: breakableFitAdvances[j] === null || 1 <= breakableFitAdvances[j].length
   *  @invariant forall k < segIdx of segmentItems: safeInteger(segmentItems[k]) && 0 <= segmentItems[k] && segmentItems[k] + 1 < itemSegments.length */   // PAPER: annotation
  while (segIdx < segmentCount) {
    segItemIdx = findItemIndex(itemSegments, segItemIdx, segIdx, items.length)
    const nextSeg: SafeInt = segIdx + 1
    segmentItems[segIdx] = segItemIdx
    segIdx = nextSeg
  }

  const segmentHyphenWidths = readsItemFonts && fontsDiffer ? buildSegmentNumbers(hyphenWidths, itemSegments, segmentItems) : null
  const segmentTabStopAdvances = readsItemFonts && fontsDiffer ? buildSegmentNumbers(tabStopAdvances, itemSegments, segmentItems) : null
  const segmentMinimumTabAdvances = readsItemFonts && fontsDiffer ? buildSegmentNumbers(minimumTabAdvances, itemSegments, segmentItems) : null
  const hyphenRooms = readsItemFonts && discretionaryHyphenContexts !== null && profile.unfitHyphenRetreat === 'reduced-width' ? getHyphenRooms(hyphenWidths, itemSegments, segmentItems) : null
  const sourceUnits = hasSourceUnits ? materializeIndexedMap(sourceUnitsMap, flags.length) : null
  const breakableLineStartExtras = hasBreakableLineStartExtras ? checkBreakableLineStartExtras(breakableFitAdvances, breakableLineStartExtrasMap, segmentCount) : null
  const segmentData: ParagraphSegmentData = {
    hyphenWidths: segmentHyphenWidths, tabStopAdvances: segmentTabStopAdvances, minimumTabAdvances: segmentMinimumTabAdvances,
    itemEndHalts,
    hyphenRooms,
    insideExtras, fillExtras, openingEdges,
    emptyObjectSpaces: null, emptyObjectReturns: null, hangEnds,
  }
  // The properties measureAnalysis() gives a text's handle, in its order, then the paragraph's own.
  const data: PreparedSegments = {
    widths,
    segmentFlags,
    simpleLineWalkFastPath: simple,
    simpleLineCountFastPath: false,
    breakableFitAdvances,
    letterSpacing: spacingsDiffer || sharedSpacing === null ? 0 : sharedSpacing,
    discretionaryHyphenWidth: firstHyphenWidth,
    discretionaryHyphenContexts,
    breakableLineStartExtras,
    lineStartExtras,
    lineEndTrims,
    overflowLineEndTrims,
    tabStopAdvance: firstTabStopAdvance,
    minimumTabAdvance: firstMinimumTabAdvance,
    items: segmentData,
    segments,
  }
  if (hasEmptyObject && profile.emptyAtomicAlwaysFits) {
    const emptyFacts = setEmptyObjectFacts(data, items, itemSegments, segmentItems, source, starts)
    segmentData.emptyObjectSpaces = emptyFacts.spaces
    segmentData.emptyObjectReturns = emptyFacts.returns
  }
  const flow: InternalPreparedRichInline = {
    data, onlyItem, wholeWidth: null, wholeStart: 0, wholeEnd: 0, itemSegments, segmentItems, gapSegments,
    plainWidths: data.letterSpacing === 0 && itemEndHalts === null && !(preserve && source.includes('\t')),
    sourceStarts, sourceEnds, sourceUnits, text: '',
  }
  return mayNarrow && onlyItem < 0 && narrowsLine(data, itemSegments) ? flow : findWholeLine(flow)
}

// Per segment, the room a line that ends at the break before it leaves for a hyphen, where the line
// returns there from a soft hyphen whose hyphen doesn't fit, with a last entry for the break at the
// paragraph's end. Blink breaks a text item again against the width less the item's own hyphen
// where the hyphen of the soft hyphen it ends at overflows (LineBreaker::BreakText,
// line_breaker.cc:1705-1719), so a break inside the item that holds the soft hyphen leaves room
// for that item's hyphen. Where none in the item does, the line goes back over the items before it
// to the latest break that fits, with no room (HandleOverflow, :4105-4112), so the break before an
// item's first segment leaves none. The premise is that a break inside an item is returned to from
// a soft hyphen of that item: for one inside an earlier item Blink asks only that the line fit
// (:4138-4158), and this leaves room for that item's hyphen (ENGINE_FOLLOWUPS.md, Rich-inline item
// edges).
// PAPER: workaround (SinglePass CFG scaling): extracted from prepareRichInline to keep CFG verification under 60s
/** @requires _itemSegments.length <= table.length + 1
 *  @requires forall k in segmentItems: safeInteger(segmentItems[k]) && 0 <= segmentItems[k] && segmentItems[k] + 1 < _itemSegments.length
 *  @ensures result.length === segmentItems.length */
function buildSegmentNumbers(table: Dense<number[]>, _itemSegments: Dense<number[]>, segmentItems: Int32Array): Modifies<{}, Fresh<number[]>> {   // PAPER: annotation
  const out: number[] = []
  const n = segmentItems.length
  let i = 0
  /** @invariant safeInteger(i) && safeInteger(n) && 0 <= i && i <= n && n === segmentItems.length && out.length === i && _itemSegments.length <= table.length + 1
   *  @invariant forall k in segmentItems: safeInteger(segmentItems[k]) && 0 <= segmentItems[k] && segmentItems[k] + 1 < _itemSegments.length */
  for (; i < n; i++) {
    const index = segmentItems[i]!
    out.push(table[index]!)
  }
  return out
}

/** @requires itemSegments.length <= hyphenWidths.length + 1
 *  @requires forall k in segmentItems: safeInteger(segmentItems[k]) && 0 <= segmentItems[k] && segmentItems[k] + 1 < itemSegments.length
 *  @ensures segmentItems.length < result.length */
function getHyphenRooms(hyphenWidths: Dense<number[]>, itemSegments: Dense<number[]>, segmentItems: Int32Array): Modifies<{}, Fresh<number[]>> {   // PAPER: annotation
  const rooms: number[] = []
  // PAPER: workaround (push-argument ternary/call): split ternary and ?? missing() out of rooms.push(...) so SinglePass tracks rooms.length === i + 1
  const n = segmentItems.length
  let i = 0
  /** @invariant safeInteger(i) && safeInteger(n) && 0 <= i && i <= n && n === segmentItems.length && rooms.length === i && itemSegments.length <= hyphenWidths.length + 1
   *  @invariant forall k in segmentItems: safeInteger(segmentItems[k]) && 0 <= segmentItems[k] && segmentItems[k] + 1 < itemSegments.length */
  for (; i < n; i++) {
    const index = segmentItems[i]!
    if (i === itemSegments[index]!) {
      rooms.push(0)
    } else {
      rooms.push(hyphenWidths[index]!)
    }
  }
  rooms.push(0)
  return rooms
}

// A soft hyphen, as a segment of any kind: Gecko drops soft hyphens from a text frame's text
// (IsDiscardable, nsTextFrameUtils.cpp:32-49).
function isSoftHyphenSegment(data: PreparedSegments, i: number): Modifies<{}, boolean> {   // PAPER: annotation
  const kind = (data.segmentFlags[i] ?? missing()) & KIND_BITS
  return kind === SOFT_HYPHEN || ((kind === ZERO_WIDTH_BREAK || kind === ZERO_WIDTH_GLUE) && (data.segments[i] ?? missing()).charCodeAt(0) === 0x00AD)
}

// What a line reads of the text around each object of width 0 where the engine places one though
// it sticks out of the line, as Gecko does an empty frame (ParagraphSegmentData;
// walkPreparedComplexLines has when it sticks out). Each item is a text frame.
// - The white space that ends the text before the object, read past the soft hyphens Gecko
//   drops. Gecko's line breaker leaves a break at the end of a text run that ends in a space or a
//   tab, whatever its advance (nsLineBreaker::Reset, nsLineBreaker.cpp:710-719; IsSegmentSpace,
//   nsLineBreaker.h:260-264), and the run's last frame breaks the line there where it ends past the
//   line's end without its own trailing spaces (nsTextFrame.cpp:11443-11456), which a tab isn't
//   among (gfxTextRun.cpp:1152-1160). So a collapsed space counts as that frame's own where it is
//   in the item right before the object; one in an item before that, as before an item of soft
//   hyphens alone, an empty frame, is inside the line's width. Preserved spaces that end their
//   item hang, which the line's width leaves out already. Preserved spaces before the soft hyphens
//   that end their item hang in Firefox and not here, so they aren't read as white space
//   (ENGINE_FOLLOWUPS.md).
// - Whether a line with a break before the object goes back to it. The break comes after white
//   space, after an atomic item (nsLineLayout.cpp:1057-1069) and after a soft hyphen that ends the
//   frame before the object, whatever the hyphen's width (HasSoftHyphenBefore,
//   nsTextFrame.cpp:11432-11439); other text leaves no break at its end, so the line's first break
//   is the one after the object, which stays. The break after a frame that sticks out doesn't count
//   as one that fits (nsLineLayout.cpp:1260), and the line remembers its last break that fits
//   (NotifyOptionalBreakPosition, :1506-1513), so a text frame or a span with a width that comes
//   next sticks out too and sends the line back to before the object (:1323-1334;
//   nsBlockFrame.cpp:5361-5379). The object stays where the line ends without going back: at the
//   paragraph's end, before an atomic item with a width, which moves down whole (:1337-1341), and
//   before unpadded text whose first piece has no width. A text frame that doesn't fit ends at its
//   first break, whether or not that fits (gfxTextRun::BreakAndMeasureText, gfxTextRun.cpp:1091-1099,
//   1177-1185), so its first piece is all of it on this line: a ZWSP, a hard break, preserved
//   spaces, which hang, or the collapsed space that starts the text's own node, trimmed where the
//   frame breaks after it (nsTextFrame.cpp:11202-11213). Padding is its span's width whatever the
//   text starts with. White space in a node of its own has no break inside, so its frame is whole
//   and keeps its width, as is a node of white space and soft hyphens. An item of soft hyphens
//   alone takes no room and is passed over, as is each object of width 0, which stays for the same
//   reason as the first: one answer serves a run of them, found from the paragraph's end back.
//   White space that ends the paragraph in a node of its own gets no frame
//   (nsCSSFrameConstructor.cpp:5278-5286), and after other text of its item, as after soft
//   hyphens, it is that frame's width.
type EmptyObjectFacts = { spaces: Dense<number[]>; returns: Uint8Array }

/** @requires 0 < items.length && starts.length === items.length && items.length < itemSegments.length
 *  @ensures data.widths.length <= result.spaces.length && data.widths.length <= result.returns.length */
function setEmptyObjectFacts(
  data: PreparedSegments,
  items: Array<RichInlineItem | RichInlineBox>,
  itemSegments: Dense<number[]>,
  segmentItems: Int32Array,
  source: string,
  starts: Dense<number[]>,
): Effects<{}, EmptyObjectFacts> {   // PAPER: annotation
  const { segmentFlags, widths, letterSpacing } = data
  const count = segmentFlags.length
  // PAPER: workaround (Fresh return effect erasure): Fresh<Dense<number[]>> from zeros(count) is not erased as local allocation in Effects postcondition check
  const spaces: Dense<number[]> = []
  /** @invariant safeInteger(i) && safeInteger(count) && 0 <= i && i <= count && spaces.length === i */
  for (let i = 0; i < count; i++) spaces.push(0)
  const returns = new Uint8Array(count)
  // The item whose white space ends the paragraph's text after other text of its own, or -1.
  let runStart = source.length
  while (runStart > 0 && isCollapsibleSpaceCode(source.charCodeAt(runStart - 1))) runStart--
  let endSpaceItem = -1
  if (runStart < source.length) {
    let index = starts.length - 1
    /** @invariant safeInteger(index) && 0 <= index && index < starts.length && starts.length === items.length && items.length < itemSegments.length */
    while (index > 0 && starts[index]! > runStart) index--
    if (itemSegments[index]! < itemSegments[index + 1]!) endSpaceItem = index
  }
  // Whether what follows an object keeps it on its line, for an object right before the item at
  // hand, from the paragraph's end back.
  let keeps = true
  /** @invariant safeInteger(index) && -1 <= index && index < items.length && items.length < itemSegments.length && spaces.length === segmentFlags.length && segmentFlags.length === widths.length && widths.length === data.widths.length && returns.length === widths.length && spaces !== widths && spaces !== data.widths && spaces !== itemSegments */
  for (let index = items.length - 1; index >= 0; index--) {
    const first = itemSegments[index]!
    const end = itemSegments[index + 1]!
    if (first >= end) continue
    const kind = (segmentFlags[first] ?? missing()) & KIND_BITS
    const item = items[index]!
    if (item.text === undefined || item.break === 'never') {
      if (widths[first] !== 0) {
        keeps = true
        continue
      }
      let before = first - 1
      /** @invariant safeInteger(first) && 0 <= first && first < spaces.length && spaces.length === segmentFlags.length && segmentFlags.length === widths.length && widths.length === data.widths.length && returns.length === widths.length && spaces !== widths && spaces !== data.widths && spaces !== itemSegments */
      while (before >= 0 && isSoftHyphenSegment(data, before)) before--
      const beforeKind = before < 0 ? TEXT : (segmentFlags[before] ?? missing()) & KIND_BITS
      let space = -1
      if (beforeKind === SPACE) space = segmentItems[before] === segmentItems[first - 1] ? (widths[before] ?? missing()) + (((segmentFlags[before] ?? missing()) & SPACED) !== 0 ? letterSpacing : 0) : 0
      else if (beforeKind === TAB || (beforeKind === PRESERVED_SPACE && segmentItems[before] !== segmentItems[before + 1])) space = 0
      spaces[first] = space
      const lastKind = first === 0 ? TEXT : (segmentFlags[first - 1] ?? missing()) & KIND_BITS
      if (!keeps && (space >= 0 || lastKind === OBJECT || lastKind === SOFT_HYPHEN)) returns[first] = 1
      continue
    }
    if (endSpaceItem === index) keeps = false
    let softHyphens = true
    let holdsSpace = false
    let establishesLine = false
    for (let i = first; i < end; i++) {
      if (isSoftHyphenSegment(data, i)) continue
      softHyphens = false
      if (((segmentFlags[i] ?? missing()) & KIND_BITS) === SPACE) holdsSpace = true
      else establishesLine = true
    }
    if (softHyphens) continue
    if ((item.extraWidth ?? 0) > 0 || (holdsSpace && !establishesLine)) keeps = false
    else if (kind === SPACE) keeps = true
    else keeps = (kind === ZERO_WIDTH_BREAK && !isSoftHyphenSegment(data, first)) || kind === HARD_BREAK || kind === PRESERVED_SPACE
  }
  return { spaces, returns }
}

// Finds the paragraph's line where nothing wraps it, which is taken without a walk at any width it
// fits: most paragraphs of a chat are one line. That is a premise. Blink, Gecko and WebKit each fit
// a line at prefixes of it, after each item, at each break opportunity and frame end, and after each
// run between two wrap opportunities (line_breaker.cc:1009-1147; gfxTextRun.cpp:1085-1109;
// InlineLineBuilder.cpp:538-604), and none lets text make a line narrower (ClampNegativeToZero,
// line_breaker.cc:1703; nsTextFrame.cpp:11272-11273; InlineLine.cpp:440), so where no item makes
// the line narrower its width only grows from item to item and the walkers take the same line. A
// paragraph with such an item, one of no advance under negative letter spacing or one with a
// negative extraWidth, has no such line and is walked (narrowsLine). Inside an item the premise's
// gap is left: under negative letter spacing a line can overflow at a break and come back under
// the line's width after it, where the text walkers end the line at the break and the paragraph
// takes it whole, so a paragraph of one item can take fewer lines than layoutWithLines() gives its
// text. Blink takes a text item whole where its shaped width fits (ShapingLineBreaker::ShapeLine,
// shaping_line_breaker.cc:281-297), which is that line; ENGINE_FOLLOWUPS.md, Negative letter
// spacing and hanging spaces, has the counts. The walk hands walkPreparedLinesRaw() a visitor of
// its own, which costs later walks of one-item CJK paragraphs 4-6% in Firefox 156 and a stream
// over a page of mostly such paragraphs 8% in Safari 27; the line stepped with no visitor was
// measured and left out (RESEARCH.md, Decisions Log, 2026-10-09, a loop of its own for the count
// of lines).
function findWholeLine(flow: InternalPreparedRichInline): InternalPreparedRichInline {
  // PAPER: the visitor's instance
  const lineCount = walkPreparedLinesRaw<{ "flow.wholeWidth": "any"; "flow.wholeStart": "any"; "flow.wholeEnd": "any" }>(flow.data, Number.POSITIVE_INFINITY, (width, startSegmentIndex, _startGraphemeIndex, endSegmentIndex) => {
    flow.wholeWidth = width
    flow.wholeStart = startSegmentIndex
    flow.wholeEnd = endSegmentIndex
  })
  if (lineCount !== 1) flow.wholeWidth = null
  return flow
}

// Whether an item of the paragraph takes less than no room on a line: its segments' widths, with
// the letter spacing after each one that takes it, add up to less than 0.
function narrowsLine(data: PreparedSegments, itemSegments: Dense<number[]>): boolean {
  const { widths, segmentFlags, letterSpacing } = data
  for (let index = 0; index + 1 < itemSegments.length; index++) {
    let width = 0
    const start = itemSegments[index]!
    const end = itemSegments[index + 1]!
    for (let i = start; i < end; i++) width += (widths[i] ?? missing()) + (((segmentFlags[i] ?? missing()) & SPACED) !== 0 ? letterSpacing : 0)
    if (width < 0) return true
  }
  return false
}

// Whether the paragraph's whole line fits `maxWidth`, as the walkers fit a line. The line functions
// hand it their width clamped at 0, as the walkers clamp the one they are handed. The line's width
// here is signed, and under 0 where letter spacing is more negative than the letters are wide:
// fitted against a width under 0 as given, such a paragraph would be one line down to its own
// width and walked under it, where the walkers can end a line that the whole fit takes
// (findWholeLine; RESEARCH.md, Decisions Log, 2026-10-09, rich inline's width).
function fitsWhole(flow: InternalPreparedRichInline, maxWidth: number): Effects<{ "@state": "any" }, number | null> {   // PAPER: annotation
  return flow.wholeWidth !== null && flow.wholeWidth <= maxWidth + getEngineProfile().lineFitEpsilon ? flow.wholeWidth : null
}

type AtomicMeasure = {
  width: number
  text: string
  textStart: number
  textEnd: number
}

// PAPER: workaround (sparse arrays / Map conversion): materialize and validate breakableLineStartExtrasMap after the main loop
/** @requires safeInteger(segmentCount) && 0 <= segmentCount && breakableFitAdvances.length === segmentCount
 *  @ensures result.length === segmentCount
 *  @ensures forall k in breakableFitAdvances: breakableFitAdvances[k] === null || result[k] === null || breakableFitAdvances[k].length <= result[k].length */
function checkBreakableLineStartExtras(
  breakableFitAdvances: Dense<(number[] | null)[]>,
  extras: Map<number, number[]>,
  segmentCount: number,
): Effects<{}, Dense<(number[] | null)[]>> {   // PAPER: annotation
  const res: Dense<(number[] | null)[]> = new Array<number[] | null>(segmentCount).fill(null)
  /** @invariant safeInteger(i) && safeInteger(segmentCount) && 0 <= i && i <= segmentCount && breakableFitAdvances.length === segmentCount && res.length === segmentCount && res !== breakableFitAdvances
   *  @invariant forall k in breakableFitAdvances: breakableFitAdvances[k] === null || res[k] === null || breakableFitAdvances[k].length <= res[k].length */
  for (let i = 0; i < segmentCount; i++) {
    const fit = breakableFitAdvances[i] ?? null
    const ext = extras.get(i) ?? null
    if (fit === null) {
      res[i] = null
    } else if (ext === null) {
      res[i] = null
    } else {
      if (fit.length > ext.length) throw new RangeError('extras')
      res[i] = ext
    }
  }
  return res
}

// PAPER: workaround (sparse arrays / Map conversion): materialize sourceUnitsMap after the main loop
/** @requires safeInteger(count) && 0 <= count
 *  @ensures result.length === count */
function materializeIndexedMap(map: Map<number, Dense<number[]>>, count: number): Effects<{}, Dense<(Dense<number[]> | null)[]>> {   // PAPER: annotation
  const out: Dense<(Dense<number[]> | null)[]> = []
  /** @invariant safeInteger(i) && safeInteger(count) && 0 <= i && i <= count && out.length === i */
  for (let i = 0; i < count; i++) out.push(map.get(i) ?? null)
  return out
}

/** @requires safeInteger(count) && count === analysis.flags.length && count <= analysis.starts.length && count <= analysis.texts.length && segments.length === 0
 *  @ensures result.widths.length === count
 *  @ensures result.items === undefined || result.items.insideExtras === null || result.widths.length <= result.items.insideExtras.length
 *  @ensures result.items === undefined || result.items.fillExtras === null || result.widths.length <= result.items.fillExtras.length */
function prepareSingleSegments(
  analysis: TextAnalysis,
  count: number,
  font: string,
  segments: Dense<string[]>,
  letterSpacing: number,
  profile: EngineProfile,
  language: string | null,
): Effects<{ "segments[*]": "extend"; fields: "any"; views: "grow"; "@state": "any" }, PreparedSegments> {   // PAPER: annotation
  const from = 0
  const prepared = measureAnalysis(analysis, from, count, font, segments, letterSpacing, profile, language, true, null, 0)
  // PAPER: workaround (object-literal field-read links): bind prepared.* to locals before constructing PreparedSegments instead of `{ ...measured, segments }`
  const widths = prepared.widths
  const segmentFlags = prepared.segmentFlags
  const breakableFitAdvances = prepared.breakableFitAdvances
  const breakableLineStartExtras = prepared.breakableLineStartExtras
  const lineStartExtras = prepared.lineStartExtras
  const lineEndTrims = prepared.lineEndTrims
  const overflowLineEndTrims = prepared.overflowLineEndTrims
  return {
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
    segments,
  }
}

/** @requires safeInteger(count) && count === analysis.flags.length && count <= analysis.starts.length && count <= analysis.texts.length
 *  @ensures result.widths.length === count */
function prepareSingleLineData(
  analysis: TextAnalysis,
  count: number,
  font: string,
  letterSpacing: number,
  profile: EngineProfile,
  language: string | null,
): Effects<{ fields: "any"; views: "grow"; "@state": "any" }, PreparedLineData> {   // PAPER: annotation
  const from = 0
  const prepared = measureAnalysis(analysis, from, count, font, null, letterSpacing, profile, language, false, null, 0)
  // PAPER: workaround (object-literal field-read links): bind prepared.* to locals before constructing PreparedLineData so SinglePass transfers field invariants
  const widths = prepared.widths
  const segmentFlags = prepared.segmentFlags
  const breakableFitAdvances = prepared.breakableFitAdvances
  const breakableLineStartExtras = prepared.breakableLineStartExtras
  const lineStartExtras = prepared.lineStartExtras
  const lineEndTrims = prepared.lineEndTrims
  const overflowLineEndTrims = prepared.overflowLineEndTrims
  return {
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
}

function measureAtomicItem(item: RichInlineItem, profile: EngineProfile, wordBreak: WordBreakMode, language: string | null): Effects<{ fields: "any"; views: "grow"; "@state": "any" }, AtomicMeasure> {   // PAPER: annotation
  let width = 0
  let text = ''
  let textStart = 0
  const ownAnalysis = analyzeText(item.text, profile, 'normal', wordBreak, language)
  const ownTexts = ownAnalysis.texts
  const ownCount = ownAnalysis.flags.length
  const ownData = prepareSingleLineData(ownAnalysis, ownCount, item.font, readLetterSpacing(item.letterSpacing, profile), profile, language)
  const start: LayoutCursor = { segmentIndex: 0, graphemeIndex: 0 }
  if (normalizePreparedLineStart(ownData, start)) width = stepPreparedLineGeometryFromStart(ownData, start, Number.POSITIVE_INFINITY) ?? missing()
  width += item.extraWidth ?? 0
  // The chip's text as a line of it paints it (buildLineTextFromRange).
  for (let i = 0; i < ownCount; i++) {
    const kind = ownData.segmentFlags[i]! & KIND_BITS
    const ownText = ownTexts[i]!
    if (kind !== SOFT_HYPHEN && kind !== HARD_BREAK && !((kind === ZERO_WIDTH_GLUE || kind === ZERO_WIDTH_BREAK) && ownText.charCodeAt(0) === 0x00AD)) text += ownText
  }
  while (isCollapsibleSpaceCode(item.text.charCodeAt(textStart))) textStart++
  let textEnd = item.text.length
  while (textEnd > textStart && isCollapsibleSpaceCode(item.text.charCodeAt(textEnd - 1))) textEnd--
  return { width, text, textStart, textEnd }
}

// PAPER: workaround (SinglePass CFG scaling): nested loops extracted from prepareRichInline to keep CFG verification under 60s
/** @requires safeInteger(index) && safeInteger(limit) && 0 <= index && index < limit && limit <= starts.length
 *  @ensures safeInteger(result) && index <= result && result < limit */
function findItemIndex(starts: Dense<number[]>, index: number, offset: number, limit: number): Effects<{}, number> {   // PAPER: annotation
  let i = index
  /** @invariant safeInteger(i) && safeInteger(index) && safeInteger(limit) && 0 <= index && index <= i && i < limit && limit <= starts.length */
  while (i < limit - 1 && starts[i + 1]! <= offset) i++
  return i
}

/** @requires safeInteger(index) && 0 <= index && itemSegments.length <= index + 1
 *  @ensures itemSegments.length === index + 1 */
function padItemSegments(itemSegments: Dense<number[]>, index: number, value: number): Effects<{ "itemSegments[*]": "extend" }, void> {   // PAPER: annotation
  /** @invariant safeInteger(index) && 0 <= index && itemSegments.length <= index + 1 */
  while (itemSegments.length <= index) itemSegments.push(value)
}

/** @requires safeInteger(from) && safeInteger(count) && 0 <= from && from < count && count <= analysis.starts.length
 *  @ensures safeInteger(result) && from < result && result <= count */
function findItemEnd(analysis: TextAnalysis, offsets: Int32Array, from: number, count: number, itemEnd: number): Effects<{}, number> {   // PAPER: annotation
  let to = from + 1
  /** @invariant safeInteger(from) && safeInteger(to) && safeInteger(count) && 0 <= from && from < to && to <= count && count <= analysis.starts.length */
  while (to < count && (offsets[analysis.starts[to]!] ?? missing()) < itemEnd) to++
  return to
}

/** @requires safeInteger(from) && safeInteger(to) && 0 <= from && from <= to && to <= flags.length
 *  @ensures safeInteger(result) && from <= result && result <= to */
function findFirstContent(flags: number[], from: number, to: number): Effects<{}, number> {   // PAPER: annotation
  let first = from
  /** @invariant safeInteger(from) && safeInteger(first) && safeInteger(to) && 0 <= from && from <= first && first <= to && to <= flags.length */
  while (first < to && ((flags[first]! & KIND_BITS) === SOFT_HYPHEN || (first === from && (flags[from]! & KIND_BITS) === SPACE))) first++
  return first
}

/** @requires safeInteger(spaces) && 1 <= spaces
 *  @ensures 1 <= result.length && result.length === spaces */
function equalAdvances(width: number, spaces: number): Effects<{}, number[]> {   // PAPER: annotation
  const advances: number[] = []
  let g = 0
  /** @invariant safeInteger(g) && safeInteger(spaces) && 0 <= g && g <= spaces && 1 <= spaces && advances.length === g */
  for (; g < spaces; g++) advances.push(width / spaces)
  return advances
}

/** @requires 1 <= advances.length
 *  @ensures 1 <= result.length && result.length === advances.length */
function adjustRichAdvances(advances: number[], spaced: boolean, holdsExtra: boolean, letterSpacing: number, extraWidth: number): Effects<{}, Dense<number[]>> {   // PAPER: annotation
  const len = advances.length
  const copy: Dense<number[]> = []
  let g = 0
  /** @invariant safeInteger(g) && safeInteger(len) && 0 <= g && g <= len && len === advances.length && copy.length === g */
  for (; g < len; g++) {
    const v = advances[g]!
    copy.push(v + (spaced ? letterSpacing : 0) + (holdsExtra && g === 0 ? extraWidth : 0))
  }
  return copy
}

function trimTextEnd(offsets: Int32Array, textEnd: number, itemEnd: number): Effects<{}, number> {   // PAPER: annotation
  while ((offsets[textEnd - 1] ?? missing()) >= itemEnd) textEnd--
  return textEnd
}

// PAPER: workaround (slice length / confined cache): delegate to zeros(count) instead of ZEROS.slice(0, count) so SinglePass proves result.length === count
/** @requires safeInteger(count) && 0 <= count
 *  @ensures result.length === count */
function zeroList(count: number): Modifies<{}, Fresh<Dense<number[]>>> {   // PAPER: annotation
  return zeros(count)
}

// How much of a padded item's extraWidth a line fits where it takes the item's opening, the
// white space, hard break or zero-width space that starts it, and no more of it; a line that goes
// on into the item fits all of it. Blink adds a span's start edge to the line when it opens
// (HandleOpenTag, line_breaker.cc:3957-3976), and only a test-only flag narrows the line for its
// cloned end edge (BoxDecorationBreakCloneLineBreaking, :454-461), so it fits half: the extraWidth
// isn't split by side (ENGINE_FOLLOWUPS.md). The items a line takes after the break it returns to
// stay on it where they are all trailable, white space with the tags of spans that open and close
// among it (RewindOverflow, :4332-4424), so Blink fits no edge of a span of only white space. Nor
// does it after preserved spaces that follow text in one item, which its return breaks before
// (HandleOverflow, :4163-4185, at the run's start that ShapingLineBreaker::ShapeLine breaks at,
// shaping_line_breaker.cc:490-495): the line then trails them, taking the open tag and white
// space or a forced break after them with no fit (HandleTrailingSpaces, :2426-2534). WebKit fits
// a box that opens in the content it places without its cloned end edge
// (placedClonedDecorationWidth, InlineLineBuilder.cpp:1501-1523), where a hard break or white
// space starts it, after the white space before it, which the line counts (the walker's line
// width holds it), but that content runs on past the inline box ends after a line break or white
// space (nextWrapOpportunity, InlineFormattingUtils.cpp:470-475, 530-538), so it fits the end
// edge too of an item of white space that ends there. Gecko fits a frame's whole width, its
// cloned end edge too (CanPlaceFrame, nsLineLayout.cpp:1217-1270).
/** @requires safeInteger(from) && safeInteger(to) && 0 <= from && from < to && to <= flags.length */
function getOpeningFit(flags: number[], from: number, to: number, extraWidth: number, afterTextSpaces: boolean, profile: EngineProfile): Effects<{}, number> {   // PAPER: annotation
  const fit = profile.paddedOpeningFit
  const firstKind = flags[from]! & KIND_BITS
  const opensWithWhiteSpace = firstKind === PRESERVED_SPACE || (firstKind === TAB && profile.hangTabs)
  const opensWithBreak = firstKind === HARD_BREAK || firstKind === ZERO_WIDTH_BREAK
  let whiteSpaceEnd = from
  /** @invariant safeInteger(whiteSpaceEnd) && safeInteger(from) && safeInteger(to) && 0 <= from && from <= whiteSpaceEnd && whiteSpaceEnd <= to && to <= flags.length */
  while (whiteSpaceEnd < to && ((flags[whiteSpaceEnd]! & KIND_BITS) === PRESERVED_SPACE || (flags[whiteSpaceEnd]! & KIND_BITS) === TAB)) whiteSpaceEnd++
  if (fit === 'start' && (opensWithWhiteSpace || opensWithBreak)) return afterTextSpaces || whiteSpaceEnd === to ? 0 : extraWidth / 2
  if (fit === 'placed' && (opensWithWhiteSpace || opensWithBreak)) {
    const onlyOpening = whiteSpaceEnd === to || (whiteSpaceEnd === to - 1 && (flags[whiteSpaceEnd]! & KIND_BITS) === HARD_BREAK)
    return onlyOpening ? extraWidth : extraWidth / 2
  }
  return extraWidth
}

// The width on a line of graphemes [from, to) of segment i, to its end where `to` is -1: a line
// starts or ends inside its first and its last segment only. Where they start the line
// (`startsLine`), the first of them adds what a line that starts with it does
// (breakableLineStartExtras), as the walker's line does.
/** @requires safeInteger(i) && 0 <= i && i < flow.data.widths.length */
function getPartWidth(flow: InternalPreparedRichInline, i: number, from: number, to: number, startsLine: boolean): Effects<{}, number> {   // PAPER: annotation
  const { breakableFitAdvances, breakableLineStartExtras, letterSpacing } = flow.data
  const advances = breakableFitAdvances[i] ?? null
  if (advances === null) throw new RangeError('missing value')
  if (to < 0) to = advances.length
  let w = 0
  for (let g = from; g < to; g++) w += (advances[g] ?? missing()) + letterSpacing
  const startExtras = startsLine && breakableLineStartExtras !== null ? (breakableLineStartExtras[i] ?? null) : null
  if (startExtras !== null) w += (startExtras[from] ?? missing())
  if (flow.data.items !== undefined) {
    if (from > 0) {
      if (flow.data.items.insideExtras !== null) w += flow.data.items.insideExtras[i]!
    } else if (flow.data.items.fillExtras !== null) {
      w += flow.data.items.fillExtras[i]!
    }
  }
  return w
}

// A line of a paragraph whose only item with segments has no extraWidth (onlyItem), as most of a
// chat's are: one fragment of that item, as wide as the line. Every segment is that item's, so a
// place in the paragraph is the same place in the item. A function of its own, which the walk and
// the stream call for such a paragraph: with it Safari 27 walked and streamed the chat demo's
// paragraphs 8.0% and 8.6% faster than with that line as a branch of createLine() and Chrome 154
// walked them 4.2% faster, and it cost Chrome's walk of items that are a word or a space each 5.3%
// and Firefox 156's walk of the demo's styled paragraphs 2.2% (RESEARCH.md, Rich Inline As One
// Paragraph; Decisions Log, 2026-10-08).
function createOnlyItemLine(
  flow: InternalPreparedRichInline,
  width: number,
  startSegmentIndex: number,
  startGraphemeIndex: number,
  endSegmentIndex: number,
  endGraphemeIndex: number,
): Modifies<{}, RichInlineLineRange> {   // PAPER: annotation
  const { onlyItem } = flow
  const ended = endSegmentIndex >= flow.data.widths.length
  return {
    fragments: [{
      itemIndex: onlyItem,
      gapBefore: 0,
      gapItemIndex: -1,
      occupiedWidth: width,
      start: { segmentIndex: startSegmentIndex, graphemeIndex: startGraphemeIndex },
      end: { segmentIndex: endSegmentIndex, graphemeIndex: endGraphemeIndex },
    }],
    width: Math.max(0, width),
    end: { itemIndex: ended ? flow.itemSegments.length - 1 : onlyItem, segmentIndex: ended ? 0 : endSegmentIndex, graphemeIndex: endGraphemeIndex },
  }
}

// A line of the paragraph from the text walkers' line: its segments cut into fragments where the
// item changes. A collapsed space at an item's start or end is no fragment's text but the gap
// before the next fragment on the line, as that item's white space made it. Each fragment's width
// is its segments' on this line, and the fragments add up to the line's width: what the line's
// width leaves out at its end comes out of the last fragments and the gaps before them, from the
// line's end back, as white space that hangs there, but never out of the edge of a padded item's
// opening, which the line paints whole (getOpeningFit), and what it adds, the hyphen of a soft
// hyphen the line ends at, goes to the last one. One loop over the line's segments: where a
// fragment or a gap starts, the paragraph's lists give where that fragment ends, so every other
// segment only adds its width. A line where no segment's width depends on the line (`bare`), as
// nearly every line of styled prose is, has a loop of its own that adds bare widths: in one loop
// with the widths that tabs, letter spacing, halts and a line's edges need, Chrome walked the chat
// demo's styled paragraphs about 19% slower and Safari 8% (two runs against one build). The widths
// of the two segments a line can start or end inside are found before the loops, and neither holds
// another loop or a search: a search for the item, or a call or a loop inside one for a width it
// rarely needs, cost Firefox a third to a half of a walk's time, and a loop inside for each
// fragment's widths 9% on items of one segment (RESEARCH.md, Rich Inline As One Paragraph).
function createLine(
  flow: InternalPreparedRichInline,
  width: number,
  startSegmentIndex: number,
  startGraphemeIndex: number,
  endSegmentIndex: number,
  endGraphemeIndex: number,
): Effects<{ "@state": "any" }, RichInlineLineRange> {   // PAPER: annotation
  const { data, itemSegments } = flow
  const { widths, segmentFlags, lineStartExtras, letterSpacing } = data
  const items = data.items
  if (items === undefined) throw new RangeError('missing value')   // PAPER: workaround (guarded linear refutation): SinglePass slotGuardTag does not refute linear body B in `guarded s p g B` via linear oracle
  const rawSegmentItems = flow.segmentItems
  if (rawSegmentItems === null) throw new RangeError('missing value')
  const segmentItems: Int32Array = rawSegmentItems
  const rawGapSegments = flow.gapSegments
  if (rawGapSegments === null) throw new RangeError('missing value')
  const gapSegments: Uint8Array = rawGapSegments
  const itemCount = itemSegments.length - 1
  const endItemIndex = endSegmentIndex >= widths.length ? itemCount : (segmentItems[endSegmentIndex] ?? missing())
  const end: RichInlineCursor = { itemIndex: endItemIndex, segmentIndex: endSegmentIndex - (itemSegments[endItemIndex] ?? missing()), graphemeIndex: endGraphemeIndex }
  const tabsInAppUnits = getEngineProfile().tabsInAppUnits
  const itemEndHalts = items.itemEndHalts
  const lastSegmentIndex = endGraphemeIndex > 0 ? endSegmentIndex : endSegmentIndex - 1
  if (startSegmentIndex > lastSegmentIndex) return { fragments: [], width: Math.max(0, width), end }
  if (!(Number.isSafeInteger(startSegmentIndex) && Number.isSafeInteger(lastSegmentIndex) && 0 <= startSegmentIndex && startSegmentIndex <= lastSegmentIndex && lastSegmentIndex < flow.data.widths.length)) throw new RangeError('missing value')   // PAPER: workaround (line-break.ts callback/stepper bounds): walkPreparedLinesRaw InternalLineVisitor and stepPreparedLineGeometryFromStart do not yet state segment bounds
  const firstPartWidth = startGraphemeIndex > 0 || startSegmentIndex === endSegmentIndex
    ? getPartWidth(flow, startSegmentIndex, startGraphemeIndex, startSegmentIndex < endSegmentIndex ? -1 : endGraphemeIndex, true) : 0
  const lastPartWidth = endGraphemeIndex > 0 && lastSegmentIndex > startSegmentIndex ? getPartWidth(flow, lastSegmentIndex, 0, endGraphemeIndex, false) : 0
  // Whether each of the line's segments is as wide on it as its width: in a paragraph of plain
  // widths, a line that starts and ends between segments and adds nothing at its start.
  const bare = flow.plainWidths && startGraphemeIndex === 0 && endGraphemeIndex === 0 && (lineStartExtras === null || lineStartExtras[startSegmentIndex] === 0)
  const fragments: RichInlineFragmentRange[] = []
  // The line's width so far, and the gap that waits for a fragment.
  let lineW = 0
  let gap = 0
  let gapItemIndex = -1
  // The last fragment made, its width so far, and the segment after its last.
  let fragment: RichInlineFragmentRange | null = null
  let occupiedWidth = 0
  let to = startSegmentIndex
  if (bare) {
    /** @invariant safeInteger(i) && safeInteger(lastSegmentIndex) && 0 <= i && i <= lastSegmentIndex + 1 && lastSegmentIndex < widths.length && widths !== fragments && itemSegments !== fragments */   // PAPER: annotation
    for (let i = startSegmentIndex; i <= lastSegmentIndex; i++) {
      if (i === to) {
        if (fragment !== null) fragment.occupiedWidth = occupiedWidth
        const itemIndex = segmentItems[i]!
        if (gapSegments[i]! !== 0) {
          gap = widths[i]!
          gapItemIndex = itemIndex
          to = i + 1
          continue
        }
        const first = itemSegments[itemIndex]!
        to = Math.min(itemSegments[itemIndex + 1]!, lastSegmentIndex + 1)
        if ((gapSegments[to - 1] ?? missing()) !== 0) to--
        fragment = { itemIndex, gapBefore: gap, gapItemIndex, occupiedWidth: 0, start: { segmentIndex: i - first, graphemeIndex: 0 }, end: { segmentIndex: to - first, graphemeIndex: 0 } }
        fragments.push(fragment)
        lineW += gap
        gap = 0
        gapItemIndex = -1
        occupiedWidth = 0
      }
      occupiedWidth += widths[i]!
      lineW += widths[i]!
    }
  } else {
    /** @invariant safeInteger(i) && safeInteger(lastSegmentIndex) && 0 <= i && i <= lastSegmentIndex + 1 && lastSegmentIndex < widths.length && data.segmentFlags.length === data.widths.length && data.widths !== fragments && widths !== fragments && itemSegments !== fragments */   // PAPER: annotation
    for (let i = startSegmentIndex; i <= lastSegmentIndex; i++) {
      if (i === to) {
        if (fragment !== null) fragment.occupiedWidth = occupiedWidth
        const itemIndex = segmentItems[i]!
        if (gapSegments[i]! !== 0) {
          // A collapsed space is no tab and no halted mark, and no line starts with one or ends inside one.
          gap = widths[i]! + (letterSpacing !== 0 && (segmentFlags[i]! & SPACED) !== 0 ? letterSpacing : 0)
          gapItemIndex = itemIndex
          to = i + 1
          continue
        }
        // The fragment's segments end at `to`: the item's on the line, less the collapsed space that ends it.
        const first = itemSegments[itemIndex]!
        to = Math.min(itemSegments[itemIndex + 1]!, lastSegmentIndex + 1)
        if ((gapSegments[to - 1] ?? missing()) !== 0) to--
        const endsInside = to > endSegmentIndex
        fragment = {
          itemIndex,
          gapBefore: gap,
          gapItemIndex,
          occupiedWidth: 0,
          start: { segmentIndex: i - first, graphemeIndex: i === startSegmentIndex ? startGraphemeIndex : 0 },
          end: { segmentIndex: (endsInside ? endSegmentIndex : to) - first, graphemeIndex: endsInside ? endGraphemeIndex : 0 },
        }
        fragments.push(fragment)
        lineW += gap
        gap = 0
        gapItemIndex = -1
        occupiedWidth = 0
      }
      // A segment's width on the line, with the letter spacing after each of its graphemes, as a
      // fragment's width counts it.
      let w: number
      if ((i > startSegmentIndex || startGraphemeIndex === 0) && i < endSegmentIndex) {
        const startExtra = i === startSegmentIndex && lineStartExtras !== null ? lineStartExtras[i]! : 0
        w = startExtra + ((segmentFlags[i]! & KIND_BITS) !== TAB ? widths[i]! : getItemTabAdvance(data, items, i, lineW + startExtra, tabsInAppUnits))
        if (letterSpacing !== 0 && (segmentFlags[i]! & SPACED) !== 0) w += letterSpacing
      } else {
        w = i === startSegmentIndex ? firstPartWidth : lastPartWidth
      }
      // A mark that ends its item was halted where the line went on after it: the line is then
      // narrower than its segments up to the mark (ParagraphSegmentData, itemEndHalts), since what
      // follows a halted mark fits in less than the halt. Premise: what follows a mark on its line
      // takes no less than no room. Its gap is an item after the mark whose letter spacing is more
      // negative than its letters are wide, where a mark that wasn't halted gives its halt to the
      // line's last fragment; the line's width and breaks are the walker's either way. The 1e-6px
      // is room for float error: the walker adds the same advances in another order, so where
      // nothing after a mark that wasn't halted takes room, the segments up to it can add up to
      // more than the line by a few units in the last place of the line's width (one is 6e-14px on
      // a line of 300px, 6e-11px on one of 280,000px), and the mark would read as halted, its halt
      // going to the line's last fragment.
      if (itemEndHalts !== null && itemEndHalts[i]! !== 0 && lineW + w - width > 1e-6) w -= itemEndHalts[i]!
      occupiedWidth += w
      lineW += w
    }
  }
  if (fragment !== null) fragment.occupiedWidth = occupiedWidth

  let rest = lineW - width
  if (rest < 0 && fragments.length > 0) fragments[fragments.length - 1]!.occupiedWidth -= rest
  const openingEdges = items.openingEdges
  /** @invariant safeInteger(k) && -1 <= k && k < fragments.length */
  for (let k = fragments.length - 1; k >= 0 && rest > 0; k--) {
    const last = fragments[k]!
    // The edge of a padded opening stays painted: it is the first segment of its item, so of a fragment.
    const edge = openingEdges === null || last.start.graphemeIndex > 0 ? 0 : (openingEdges[(itemSegments[last.itemIndex] ?? missing()) + last.start.segmentIndex] ?? missing())
    if (last.occupiedWidth > edge) {
      const part = Math.min(rest, last.occupiedWidth - edge)
      last.occupiedWidth -= part
      rest -= part
    }
    if (rest > 0 && last.gapBefore > 0) {
      const part = Math.min(rest, last.gapBefore)
      last.gapBefore -= part
      rest -= part
      // A gap taken whole is none, and so is one with under 1e-9px left, which could only be float
      // error. That needs a width the line leaves out, such as a mark's halt, to be as wide as the
      // gap to the last bits, which no rule makes it.
      if (last.gapBefore < 1e-9) {
        last.gapBefore = 0
        last.gapItemIndex = -1
      }
    }
  }
  return { fragments, width: Math.max(0, width), end }
}

// The paragraph's segment a cursor names, or the segment count for one past the last item.
/** @requires safeInteger(cursor.itemIndex) && 0 <= cursor.itemIndex */   // PAPER: annotation
function getSegmentIndex(flow: InternalPreparedRichInline, cursor: RichInlineCursor): number {
  const { itemSegments } = flow
  return cursor.itemIndex < itemSegments.length ? itemSegments[cursor.itemIndex]! + cursor.segmentIndex : flow.data.widths.length   // PAPER: guard removed
}

export function layoutNextRichInlineLineRange(
  prepared: PreparedRichInline,
  maxWidth: number,
  start: RichInlineCursor = RICH_INLINE_START_CURSOR,
): RichInlineLineRange | null {
  const flow = getInternalPreparedRichInline(prepared)
  const safeWidth = Math.max(0, maxWidth)
  // boundary check: validates caller-supplied RichInlineCursor (itemIndex, segmentIndex,
  // graphemeIndex, and breakableFitAdvances bounds) at the public streaming API boundary (#365).
  if (!(Number.isSafeInteger(start.itemIndex) && 0 <= start.itemIndex)) throw new RangeError('cursor item index out of range')
  if (!(Number.isSafeInteger(start.segmentIndex) && 0 <= start.segmentIndex)) throw new RangeError('cursor segment index out of range')
  if (!(Number.isSafeInteger(start.graphemeIndex) && 0 <= start.graphemeIndex)) throw new RangeError('cursor grapheme index out of range')
  const wholeWidth = start.itemIndex === 0 && start.segmentIndex === 0 && start.graphemeIndex === 0 ? fitsWhole(flow, safeWidth) : null
  if (wholeWidth !== null) {
    return flow.onlyItem >= 0 ? createOnlyItemLine(flow, wholeWidth, flow.wholeStart, 0, flow.wholeEnd, 0) : createLine(flow, wholeWidth, flow.wholeStart, 0, flow.wholeEnd, 0)
  }
  const lineEnd: LayoutCursor = { segmentIndex: getSegmentIndex(flow, start), graphemeIndex: start.graphemeIndex }
  const segmentAtStart = lineEnd.segmentIndex   // PAPER: a local copy for the check
  if (!(Number.isSafeInteger(segmentAtStart) && 0 <= segmentAtStart)) throw new RangeError('cursor segment index out of range')
  const data = flow.data   // PAPER: the handle through a local
  const breakableFitAdvances = data.breakableFitAdvances   // PAPER: keep array read link across branch
  if (lineEnd.graphemeIndex > 0) {
    if (segmentAtStart >= data.widths.length || segmentAtStart >= breakableFitAdvances.length) return null
    const advances = breakableFitAdvances[segmentAtStart]
    if (advances === undefined || advances === null || lineEnd.graphemeIndex >= advances.length) throw new RangeError('cursor grapheme index out of range')
  }
  if (!normalizePreparedLineStart(data, lineEnd)) return null
  const startSegmentIndex = lineEnd.segmentIndex
  const startGraphemeIndex = lineEnd.graphemeIndex
  const width = stepPreparedLineGeometryFromStart(data, lineEnd, safeWidth)   // PAPER: the handle through a local
  if (width === null) return null
  return flow.onlyItem >= 0 ? createOnlyItemLine(flow, width, startSegmentIndex, startGraphemeIndex, lineEnd.segmentIndex, lineEnd.graphemeIndex)
    : createLine(flow, width, startSegmentIndex, startGraphemeIndex, lineEnd.segmentIndex, lineEnd.graphemeIndex)
}

// Where units [from, to) of a paragraph's normalized text are in the text of the item that starts
// at `itemStart`, from the offset in the paragraph's text each unit comes from, where they aren't
// one stretch of it: Gecko removes a line feed between two ideographs, and white space after a bidi
// control that follows white space. Else null.
function getSourceUnits(offsets: Int32Array, from: number, to: number, itemStart: number): Effects<{}, Dense<number[]> | null> {   // PAPER: annotation
  if (to <= from || (offsets[to - 1] ?? missing()) - (offsets[from] ?? missing()) === to - 1 - from) return null
  const units: Dense<number[]> = []
  for (let unit = from; unit < to; unit++) units.push((offsets[unit] ?? missing()) - itemStart)
  return units
}

// Per frozen handle of a paragraph that is one text's handle, the three lists of where its
// segments are in the item's text (InternalPreparedRichInline), found when a line of it is
// first materialized. A handle keeps them itself; a frozen one can't take them, so they are
// kept beside it, as its segments' grapheme ends are (getGraphemeEnds): no line function writes
// to a frozen handle or to anything it holds, so one the app froze, or a copy of one in a store
// that freezes its state, materializes as any other. Kept beside every handle, the lookup took
// a pass that walks and materializes 3,000 of the chat demo's one-item paragraphs, each asked
// once, 35-47% longer with the handles out of the processor's caches and 7-25% with them in,
// and 40 of them over and over 1-9% (JavaScriptCore of bun 1.4.2, V8 15.4 and node 23.10's,
// SpiderMonkey 156, one build a process on the harness's stand-in Canvas, 2026-10-12). Found
// while preparing, the lists took such paragraphs 6-13% longer to prepare and count once in
// JavaScriptCore and 12-20% in V8, text seen before, and a third more heap a handle, for lines
// a long list mostly never paints; found again at every line, walking and materializing took
// 5-9 times as long, and over 100 times in a paragraph of 6,000 units.
type TextSources = { sourceStarts: Dense<number[]>; sourceEnds: Dense<number[]>; sourceUnits: Dense<(Dense<number[]> | null)[]> }
const textSources = new WeakMap<InternalPreparedRichInline, TextSources>()

// Per segment of a paragraph that is one text's handle, where its text starts and ends in the
// item's.
function findSegmentSources(flow: InternalPreparedRichInline): Effects<{ "flow.sourceStarts": "any"; "flow.sourceEnds": "any"; "flow.sourceUnits": "any"; "@state": "any" }, TextSources> {   // PAPER: annotation
  const { segments } = flow.data
  const offsets = alignToSource(flow.text, segments.join(''), getEngineProfile().lineBreakScan)
  const sourceStarts: Dense<number[]> = []
  const sourceEnds: Dense<number[]> = []
  const sourceUnits: Dense<(Dense<number[]> | null)[]> = []
  /** @invariant flow.data.segmentFlags.length === flow.data.widths.length && flow.data.widths !== sourceStarts && flow.data.widths !== sourceEnds && flow.data.widths !== sourceUnits && segments !== sourceStarts && segments !== sourceEnds && segments !== sourceUnits */   // PAPER: annotation
  for (let i = 0, at = 0; i < segments.length; at += segments[i++]!.length) {
    const end = (offsets[at + segments[i]!.length - 1] ?? missing()) + 1
    sourceStarts.push(offsets[at] ?? missing())
    sourceEnds.push(flow.text.charCodeAt(end - 1) === 0x0D && flow.text.charCodeAt(end) === 0x0A && segments[i] === '\n' ? end + 1 : end)
    sourceUnits.push(getSourceUnits(offsets, at, at + segments[i]!.length, 0))
  }
  const sources = { sourceStarts, sourceEnds, sourceUnits }
  if (Object.isFrozen(flow)) {
    textSources.set(flow, sources)
  } else {
    flow.sourceStarts = sourceStarts
    flow.sourceEnds = sourceEnds
    flow.sourceUnits = sourceUnits
  }
  return sources
}

// Where unit `unit` of a segment's text is in its item's text.
function getSourceOffset(sourceStarts: Dense<number[]>, sourceUnits: Dense<(Dense<number[]> | null)[]> | null, segmentIndex: number, unit: number): number {
  const units = sourceUnits === null ? null : sourceUnits[segmentIndex]
  if (units === undefined) throw new RangeError('missing value')
  if (units === null) return (sourceStarts[segmentIndex] ?? missing()) + unit
  // The segment's end, where a grapheme start past its last grapheme stops: just past its last unit.
  return units[unit] ?? (units.length > 0 ? units[units.length - 1]! + 1 : (sourceStarts[segmentIndex] ?? missing()))
}

// Bridge from cheap range walking to full fragment text. Lets callers do
// shrinkwrap/virtualization/probing work first, then only pay for text on the
// lines they actually render.
export function materializeRichInlineLineRange(
  prepared: PreparedRichInline,
  line: RichInlineLineRange,
): RichInlineLine {
  const flow = getInternalPreparedRichInline(prepared)
  // boundary check: validates caller-supplied line.end.itemIndex at the public API boundary (#365).
  if (!(Number.isSafeInteger(line.end.itemIndex) && 0 <= line.end.itemIndex)) throw new RangeError('cursor item index out of range')
  const { data, itemSegments } = flow
  let { sourceStarts, sourceEnds, sourceUnits } = flow
  if (sourceStarts === null) ({ sourceStarts, sourceEnds, sourceUnits } = textSources.get(flow) ?? findSegmentSources(flow))
  const lineEndSegmentIndex = getSegmentIndex(flow, line.end)
  const fragments: RichInlineFragment[] = []

  /** @invariant prepared.data.segmentFlags.length === prepared.data.widths.length && data.segmentFlags.length === data.widths.length && data.widths !== fragments && prepared.data.widths !== fragments */   // PAPER: annotation
  for (let i = 0; i < line.fragments.length; i++) {
    const fragment = line.fragments[i]!
    const itemIndex = fragment.itemIndex
    if (!(Number.isSafeInteger(itemIndex) && 0 <= itemIndex && itemIndex < itemSegments.length - 1)) throw new Error('Missing rich-text inline item for fragment')
    const first = itemSegments[itemIndex]!
    // A range kept from a longer paragraph can end past its item in this one: its text stops at the item's end.
    const itemEnd = itemSegments[itemIndex + 1]!
    const startSegmentIndex = Math.min(first + fragment.start.segmentIndex, itemEnd)
    const startGraphemeIndex = fragment.start.graphemeIndex
    const endSegmentIndex = Math.min(first + fragment.end.segmentIndex, itemEnd)
    const endGraphemeIndex = endSegmentIndex < itemEnd ? fragment.end.graphemeIndex : 0
    // Only the fragment a line ends with shows the hyphen of a soft hyphen it ends at.
    const endsLine = i === line.fragments.length - 1 && endSegmentIndex === lineEndSegmentIndex && endGraphemeIndex === line.end.graphemeIndex
    let sourceStart = startSegmentIndex < itemEnd ? (sourceStarts[startSegmentIndex] ?? missing()) : startSegmentIndex > first ? ((sourceEnds ?? missing())[startSegmentIndex - 1] ?? missing()) : 0
    if (startGraphemeIndex > 0 && startSegmentIndex < itemEnd) sourceStart = getSourceOffset(sourceStarts, sourceUnits, startSegmentIndex, getGraphemeStart(data, startSegmentIndex, startGraphemeIndex))
    let sourceEnd = sourceStart
    if (endGraphemeIndex > 0) sourceEnd = getSourceOffset(sourceStarts, sourceUnits, endSegmentIndex, getGraphemeStart(data, endSegmentIndex, endGraphemeIndex) - 1) + 1
    else if (endSegmentIndex > startSegmentIndex) sourceEnd = (sourceEnds ?? missing())[endSegmentIndex - 1] ?? missing()
    const materialized: InternalRichInlineFragment = {
      itemIndex: fragment.itemIndex,
      text: endsLine ? buildLineTextFromRange(data, startSegmentIndex, startGraphemeIndex, endSegmentIndex, endGraphemeIndex)
        : buildRangeText(data, startSegmentIndex, startGraphemeIndex, endSegmentIndex, endGraphemeIndex),
      gapBefore: fragment.gapBefore,
      gapItemIndex: fragment.gapItemIndex,
      occupiedWidth: fragment.occupiedWidth,
      start: fragment.start,
      end: fragment.end,
      sourceStart,
      sourceEnd,
    }
    fragments.push(materialized)
  }

  return {
    fragments,
    width: line.width,
    end: line.end,
  }
}

// PAPER: onLine's effect is the effect variable E: a caller states it as the instance, and
// the bound requires it to keep every location the paragraph reaches and allows any other change.
export function walkRichInlineLineRanges<E extends AtMost<{ "prepared.**": "keep"; else: "any" }>>(
  prepared: PreparedRichInline,
  maxWidth: number,
  onLine: (line: RichInlineLineRange) => Modifies<E, void>,   // PAPER
): number {
  const flow = getInternalPreparedRichInline(prepared)
  const safeWidth = Math.max(0, normalizeMaxWidth(maxWidth))
  const wholeWidth = fitsWhole(flow, safeWidth)
  if (wholeWidth !== null) {
    onLine(flow.onlyItem >= 0 ? createOnlyItemLine(flow, wholeWidth, flow.wholeStart, 0, flow.wholeEnd, 0) : createLine(flow, wholeWidth, flow.wholeStart, 0, flow.wholeEnd, 0))
    return 1
  }
  return walkPreparedLinesRaw<Join<E, { "@state": "any" }>>(flow.data, safeWidth, (width, startSegmentIndex, startGraphemeIndex, endSegmentIndex, endGraphemeIndex) => {   // PAPER: forwards E with confined module state
    onLine(flow.onlyItem >= 0 ? createOnlyItemLine(flow, width, startSegmentIndex, startGraphemeIndex, endSegmentIndex, endGraphemeIndex)
      : createLine(flow, width, startSegmentIndex, startGraphemeIndex, endSegmentIndex, endGraphemeIndex))
  })
}

export function measureRichInlineStats(
  prepared: PreparedRichInline,
  maxWidth: number,
): RichInlineStats {
  const flow = getInternalPreparedRichInline(prepared)
  const safeWidth = Math.max(0, normalizeMaxWidth(maxWidth))
  const wholeWidth = fitsWhole(flow, safeWidth)
  if (wholeWidth !== null) return { lineCount: 1, maxLineWidth: Math.max(0, wholeWidth) }
  const stats = { lineCount: 0, maxLineWidth: 0 }
  walkPreparedLinesRaw(flow.data, safeWidth, undefined, stats)
  return stats
}
