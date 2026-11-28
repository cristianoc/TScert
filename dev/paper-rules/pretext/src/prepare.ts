// Preparation's measurement phase: each segment of a text analysis measured in a font, with
// the facts the line walkers read at a line's edges. layout.ts and rich-inline.ts prepare
// through it, as they walk through line-break.ts.

import { missing } from './checked.js'
import { getHanKerningTrims, textMayHanKern, type HanKerningTrims } from './han-kerning.js'
import { findGraphemeEnds, type GraphemeTable } from './graphemes.js'
import { scriptClassFacts } from './generated/engine-break-data.js'
import { DEFAULT_IGNORABLE, getClass, hasProperty, lazyRegExp, unpackClasses, type ClassTable } from './line-breaks.js'
import {
  CONTROL,
  DROPPED,
  HARD_BREAK,
  KIND_BITS,
  ONE_CLUSTER,
  PRESERVED_SPACE,
  SOFT_HYPHEN,
  SPACE,
  SPACED,
  TAB,
  TEXT,
  UNBROKEN,
  ZERO_WIDTH_BREAK,
  ZERO_WIDTH_GLUE,
  type TextAnalysis,
} from './analysis.js'
import {
  type BreakableFitMode,
  type EngineProfile,
  type FontMeasurement,
  getCorrectedSegmentWidth,
  getEmojiCorrection,
  getExtraSpacings,
  getFollowingSpaceMetrics,
  getFontKanaKerning,
  getFontMeasurement,
  getFontSpaceKerning,
  getHyphenText,
  getKanaKerning,
  getSegmentFit,
  getSegmentMetrics,
  getSpaceKerning,
  getSpaceWidth,
  getTextWidth,
  kanaPairRe,
  noExtraSpacings,
  noSpaceKerning,
  textMayContainEmoji,
  type SegmentMetrics,
  zeros,
} from './measurement.js'
import type { PreparedLineBreakData } from './line-break.js'   // PAPER: annotation

// Text and spaces take letter spacing after each grapheme; a ZWSP takes none.
function countRenderedSpacingGraphemes(text: string, kind: number, graphemeTable: GraphemeTable): Effects<{ "@state": "any" }, number> {   // PAPER: annotation
  return kind === ZERO_WIDTH_BREAK ? 0 : findGraphemeEnds(graphemeTable, text, 0, text.length, null)
}

function addInternalLetterSpacing(width: number, graphemeCount: number, letterSpacing: number): Effects<{}, number> {   // PAPER: annotation
  return graphemeCount > 1 ? width + (graphemeCount - 1) * letterSpacing : width
}

// Code points that WebKit's FontCascade::characterRangeCodePath sends to the
// complex text path, stored as start/end pairs. So does a ZWJ after an emoji.
const complexTextPathRanges = [
  0x02E5, 0x02E9, 0x0300, 0x036F, 0x0591, 0x05BD, 0x05BF, 0x05CF, 0x0600, 0x109F,
  0x1100, 0x11FF, 0x135D, 0x135F, 0x1700, 0x18AF, 0x1900, 0x194F, 0x1980, 0x19DF,
  0x1A00, 0x1CFF, 0x1DC0, 0x1DFF, 0x20D0, 0x20FF, 0x26F9, 0x26F9, 0x2CEF, 0x2CF1,
  0x302A, 0x302F, 0x3099, 0x309C, 0xA67C, 0xA67D, 0xA6F0, 0xA6F1, 0xA800, 0xABFF,
  0xD7B0, 0xD7FF, 0xFE00, 0xFE0F, 0xFE20, 0xFE2F, 0x10A00, 0x10A5F, 0x11000, 0x110CF,
  0x11100, 0x111DF, 0x11200, 0x1124F, 0x112B0, 0x1137F, 0x11400, 0x114DF, 0x11580, 0x1165F,
  0x11680, 0x116CF, 0x11700, 0x11CBF, 0x16B00, 0x16B8F, 0x1E900, 0x1E95F, 0x1F1E6, 0x1F1FF,
  0x1F3FB, 0x1F3FF, 0xE0000, 0xE007F, 0xE0100, 0xE01EF,
] as const

const extendedPictographicRe = /\p{Extended_Pictographic}/u
const leadingCombiningMarkRe = lazyRegExp(String.raw`^\p{M}`, 'u')
// Decimal digits and the joiners of numbers, times and dates.
const numericRunRe = /^[\p{Nd}:\-/×,.+\u2013\u2014]+$/u
const controlCharacterRe = /^[\p{Cc}\u2028\u2029]$/u

function needsComplexTextPath(text: string): Effects<{}, boolean> {   // PAPER: annotation
  let previousIsEmoji = false
  for (let i = 0; i < text.length;) {
    const codePoint = text.codePointAt(i)!
    i += codePoint > 0xFFFF ? 2 : 1
    if (codePoint === 0x200D && previousIsEmoji) return true
    previousIsEmoji = codePoint > 0xFFFF && extendedPictographicRe.test(String.fromCodePoint(codePoint))
    for (let range = 0; range + 1 < complexTextPathRanges.length && codePoint >= complexTextPathRanges[range]!; range += 2) {
      if (codePoint <= complexTextPathRanges[range + 1]!) return true
    }
  }
  return false
}

// A character of the right-to-left blocks, whose letters have bidi class R or AL, as RLM
// has, or an explicit bidi control.
const mixedDirectionRe = /[\u0590-\u08FF\uFB1D-\uFDFF\uFE70-\uFEFF\u200F\u{10800}-\u{10FFF}\u{1E800}-\u{1EFFF}\u202A-\u202E\u2066-\u2069]/u

function isSpaceKind(kind: number): Effects<{}, boolean> {   // PAPER: annotation
  return kind === SPACE || kind === PRESERVED_SPACE
}

// Blink splits a text into script runs and shapes each apart (ScriptRunIterator,
// script_run_iterator.cc; HarfBuzzShaper::Shape, harfbuzz_shaper.cc:1063-1104). Two rules of
// the Chromium profile turn on the run a character is in: a word kerns with a space only
// where the two share a run (spaceSharesScriptRun), and the letters of a run in a script
// whose letters join take no letter spacing (getUnspacedGraphemes). Both read the runs
// through readScriptRuns, with a character's scripts as bits: Cyrillic, Greek, Latin, one bit
// for the seven scripts whose letters join, and one for every other script, so two scripts
// that share a bit read as one; a character of any script has all five. Cyrillic, Greek and
// Latin are in Blink's order for a Common character's extensions, by ICU script code with
// Latin last (GetScripts, :191-198), so a run's lowest bit is the script it resolves to. A
// character's scripts, and a few facts more in the bits above them, come from ICU's Script,
// Script_Extensions and bracket pairs as Chrome's build holds them, and Firefox's: a class
// for every code point ('chromium/script') and each class's bits (scriptClassFacts).
// scripts/generate-engine-break-data.ts has which scripts a character is given there, and
// what that leaves out.
export const OTHER_SCRIPT = 1
export const CYRILLIC_SCRIPT = 2
export const GREEK_SCRIPT = 4
export const LATIN_SCRIPT = 8
export const CURSIVE_SCRIPT = 16
export const ANY_SCRIPT = 31
// A mark that scripts list, as they do the Arabic vowel signs, is of any script itself and has
// those scripts in the next five bits. A Common character that no script lists takes them
// from such a mark right after it (FetchNextCharacter, :624-635), so a digit or a dotted circle
// that carries a fatha starts an Arabic run.
export const MARK_SCRIPTS_SHIFT = 5
export const TAKES_MARK_SCRIPTS = 1 << 10
// A character whose own script, whatever else lists it, is one whose letters join.
export const CURSIVE_LETTER = 1 << 11
// A paired bracket, and from this bit up a closing bracket's code less its opening bracket's.
export const OPENING_BRACKET = 1 << 12
export const CLOSING_BRACKET = 1 << 13
export const OPENING_BRACKET_SHIFT = 14

// Every code point's class, unpacked when a text first asks for a script.
let scriptClasses: ClassTable | null = null
function getScriptFacts(c: number): Effects<{ "@state": "any" }, number> {   // PAPER: annotation
  return scriptClassFacts[getClass(scriptClasses ??= unpackClasses('chromium/script'), c)] ?? missing()
}

// The facts of the character at text[i], with the scripts it has there, as Blink reads them
// (GetScripts, script_run_iterator.cc:118-215).
/** @requires safeInteger(i) && 0 <= i && i < text.length */
function getScriptFactsAt(text: string, i: number): Effects<{ "@state": "any" }, number> {   // PAPER: annotation
  const c = text.codePointAt(i)!
  const facts = getScriptFacts(c)
  const next = i + (c > 0xFFFF ? 2 : 1)
  if ((facts & TAKES_MARK_SCRIPTS) !== 0 && next < text.length) {
    const markScripts = getScriptFacts(text.codePointAt(next)!) >> MARK_SCRIPTS_SHIFT & ANY_SCRIPT
    if (markScripts !== 0) return facts & ~ANY_SCRIPT | markScripts
  }
  return facts
}

// Whether a text holds a character whose scripts are cursive, or a mark that gives them: no
// other text has a grapheme that takes no letter spacing. ASCII, which is Latin letters and
// Common characters, has neither.
function mayHoldCursive(text: string): Effects<{ "@state": "any" }, boolean> {   // PAPER: annotation
  for (let i = 0; i < text.length; i++) {
    if (text.charCodeAt(i) < 0x80) continue
    const facts = getScriptFacts(text.codePointAt(i)!)
    if ((facts & ANY_SCRIPT) === CURSIVE_SCRIPT || (facts >> MARK_SCRIPTS_SHIFT & ANY_SCRIPT) === CURSIVE_SCRIPT) return true
  }
  return false
}

// How far a text's script runs are read, the scripts the run there can be in, and each
// bracket open there: its opening character, then the script of the run it was opened in,
// 0 while that run goes on. Confined module scratch state reset at each measureAnalysis() call.
// PAPER: workaround (confined-state framing for ScriptRuns): hoist ScriptRuns into module-private @state so readScriptRuns frames against measureAnalysisInto's local/parameter arrays
let scriptRead: number = 0
let scriptMask: number = 31 // ANY_SCRIPT
const scriptOpenBrackets: number[] = []

function resetScriptRuns(): Effects<{ "@state": "any" }, void> {   // PAPER: annotation
  scriptRead = 0
  scriptMask = ANY_SCRIPT
  scriptOpenBrackets.splice(0)
}

// The scripts of the run text[to - 1] is in, read on from the last call as
// ScriptRunIterator::Consume reads them (script_run_iterator.cc:325-429): a run keeps the
// scripts its characters share and ends before one that shares none. A run of no script yet
// takes the script of the first character after it that has one, so the read goes on to that
// character. A closing bracket takes the script of the run its opening bracket is in, once
// that run has ended, among the last 32 opened, and closes the ones opened since; its own
// stays open, so a second closing bracket goes back to that run too (OpenBracket,
// CloseBracket and FixupStack, :431-489, :567-590).
/** @requires safeInteger(to) && to <= text.length */
function readScriptRuns(text: string, to: number): Effects<{ "@state": "any" }, number> {   // PAPER: annotation
  let read = scriptRead
  if (!(Number.isSafeInteger(read) && 0 <= read)) return scriptMask
  /** @invariant safeInteger(read) && 0 <= read && safeInteger(to) && to <= text.length */
  while (read < to || (scriptMask === ANY_SCRIPT && read < text.length)) {
    const c = text.codePointAt(read)!
    let nextRead: number
    if (c > 0xFFFF) nextRead = read + 2
    else nextRead = read + 1
    const facts = getScriptFactsAt(text, read)
    let scripts = facts & ANY_SCRIPT
    // No bracket's code is as low as a run's script.
    const opened = (facts & CLOSING_BRACKET) !== 0 ? scriptOpenBrackets.lastIndexOf(c - (facts >> OPENING_BRACKET_SHIFT)) : -1
    if (opened >= 0) {
      const saved = scriptOpenBrackets[opened + 1]
      if (saved !== undefined && saved !== 0) scripts = saved
      scriptOpenBrackets.splice(opened + 2)
    }
    if ((scriptMask & scripts) !== 0) {
      scriptMask &= scripts
    } else {
      // The run that ends resolves to its first script (ResolveCurrentScript, :639-642), which
      // the brackets opened in it take.
      /** @invariant safeInteger(k) && k < scriptOpenBrackets.length && safeInteger(nextRead) && 0 <= nextRead && safeInteger(to) && to <= text.length */
      for (let k = scriptOpenBrackets.length - 1; k > 0 && scriptOpenBrackets[k] === 0; k -= 2) {
        scriptOpenBrackets[k] = scriptMask & -scriptMask
      }
      scriptMask = scripts
    }
    if ((facts & OPENING_BRACKET) !== 0) {
      if (scriptOpenBrackets.length === 64) scriptOpenBrackets.splice(0, 2)
      scriptOpenBrackets.push(c, 0)
    }
    read = nextRead
  }
  scriptRead = read
  return scriptMask
}

// Whether the space before the text segment text[at..end) is in the script run of the segment's
// first character past default ignorables, the one it kerns with: a space joins the run of the
// text before it (ScriptRunIterator::MergeSets, :490-510). The nearest character before the
// space that has one script names that run, so the search back starts before the space, at
// text[at - 2], and ends there; a closing bracket, or a character of several scripts, takes its
// script from the runs before it, which are then read.
function spaceSharesScriptRun(text: string, at: number, end: number): Effects<{ "@state": "any" }, boolean> {   // PAPER: annotation
  if (!Number.isSafeInteger(at) || at < 0 || at >= text.length) return true   // PAPER: workaround (analysis.ts @ensures): TextAnalysis does not prove starts[mi] - ownStart + text.length <= own.length
  let scripts = getScriptFactsAt(text, at) & ANY_SCRIPT
  // A default ignorable with a script of its own, as U+3164, counts as the word's first letter.
  /** @invariant safeInteger(first) && safeInteger(at) && 0 <= at && at <= first && first < text.length && at < text.length */
  for (let first = at; scripts === ANY_SCRIPT && first + 1 < end && first + 1 < text.length && hasProperty(text.charCodeAt(first), DEFAULT_IGNORABLE); first++) scripts = getScriptFactsAt(text, first + 1) & ANY_SCRIPT
  if (scripts === ANY_SCRIPT) return true
  /** @invariant safeInteger(i) && safeInteger(at) && i < text.length && 0 <= at && at < text.length */
  for (let i = at - 2; i >= 0; i--) {
    if ((text.charCodeAt(i) & 0xFC00) === 0xDC00 && i > 0) i--
    const facts = getScriptFactsAt(text, i)
    if ((facts & CLOSING_BRACKET) !== 0) break
    const before = facts & ANY_SCRIPT
    if (before === ANY_SCRIPT) continue
    if ((before & (before - 1)) === 0) return (before & scripts) !== 0
    break
  }
  return (readScriptRuns(text, at) & scripts) !== 0
}

// The scripts whose letters join, Arabic, Syriac, N'Ko, Mandaic, Mongolian, Phags-pa and
// Hanifi Rohingya, take no letter spacing in Blink and Gecko, which name the same seven
// (IsCursiveScript, shape_result.cc:977-990; UnicodeProperties.h:350-355). Gecko asks the
// script of a cluster's first character (GetSpacingInternal, nsTextFrame.cpp:4202-4213), so
// digits and punctuation among the letters keep their spacing. Blink asks the script of the
// shaping run the cluster is in and spaces only its spaces (ComputeSpacing,
// shape_result_spacing.cc:103-131, behind the runtime flag
// IgnoreLetterSpacingInCursiveScripts): a run takes in the characters of no script after
// it, the ones that start the text, and the punctuation its script shares, so of an Arabic
// word, a space and `123.` only the space is spaced. That is Chrome since 149; 138 to 148
// don't space the run's spaces either, and before 138 every letter is spaced, which no
// version check here follows (ENGINE_FOLLOWUPS.md, Letter spacing). WebKit spaces every
// glyph with an advance. Chrome 154, Firefox 156 and webkit-host lay 67 strings out so
// (2026-10-03). The profile's unspacedCursive names the engine's rule. This gives the
// graphemes of the text segment text[start..end) that take no letter spacing, as ascending
// indices, or null without any: in Gecko, which is given no runs, those whose first
// character is a letter of a cursive script; in Blink those whose first character is in a
// run that resolves to one and isn't a no-break space. A rich item's text starts a run of
// its own (ENGINE_FOLLOWUPS.md, Letter spacing).
function getUnspacedGraphemes(text: string, start: number, end: number, graphemeTable: GraphemeTable, useRuns: boolean): Effects<{ "@state": "any" }, number[] | null> {   // PAPER: annotation
  if (!(Number.isSafeInteger(start) && Number.isSafeInteger(end) && 0 <= start && start <= end && end <= text.length)) return null   // PAPER: workaround (analysis.ts @ensures): TextAnalysis does not prove starts[mi] - ownStart + text.length <= own.length for findGraphemeEnds
  const ends = new Int32Array(end - start)
  const count = findGraphemeEnds(graphemeTable, text, start, end, ends)
  let unspaced: number[] | null = null
  /** @invariant safeInteger(g) && safeInteger(at) && safeInteger(count) && 0 <= g && g <= count && count <= ends.length */
  for (let g = 0, at = start; g < count; at = ends[g++]!) {
    if (at < 0 || at >= text.length) break
    const joins = !useRuns ? (getScriptFacts(text.codePointAt(at)!) & CURSIVE_LETTER) !== 0
      : readScriptRuns(text, at + 1) === CURSIVE_SCRIPT && text.charCodeAt(at) !== 0xA0
    if (joins) (unspaced ??= []).push(g)
  }
  return unspaced
}

// The lists of a rich-inline paragraph's handle that each item's measurement adds its segments

// to; `segmentFlags` has room for them from `widths.length` on.
export type ParagraphLists = {
  readonly widths: Dense<number[]>
  readonly segmentFlags: Uint8Array
  readonly breakableFitAdvances: Dense<(number[] | null)[]>
}

// PAPER: annotation
// What measureAnalysis() returns: a text's handle, or, for a rich-inline item, its paragraph's
// lists with the item's segments added, whose segmentFlags has room for the segments after
// them, beside the item's own other lists. Its fields are a handle's (PreparedLineData), whose
// invariant, one flags byte per segment, this type does not state.
export type MeasuredSegments = PreparedLineBreakData

// The functions from here to measureAnalysis() are its loop's. They are given what they read
// and not nested in it: nested, every call makes an object for the variables they read and
// one for each of them, in every engine. Where that object is as large as a handle,
// JavaScriptCore puts it in the handles' cells, one between each two, and Safari 27 ran
// layout() over 2,000 short labels 14-17% slower. Any object of 13 to 18 fields that every
// prepare() makes and drops lands there too: with one planted here, 11-13% slower.

// A WebKit text item runs to its next break opportunity, so it also owns any
// zero-width breaks before the space. The item is measured with one following
// U+0020 minus a space measured alone, which keeps the kerning between the item's
// end and that space. Under letter spacing both measurements hold the space's
// spacing (TextUtil::width over singleSpaceWidth, TextUtil.cpp:54-100, in WebKit
// 7625), so the item keeps that kerning there too. WebKit's item is never narrower
// than 0 (TextUtil.cpp:103), which the per-grapheme gap model does not represent.
// A soft hyphen before the space takes no kerning: on an RTL page WebKit needs
// about a hyphen's width more to fit such an item, and preparation cannot see the
// page direction. WebKit splits a text item where the bidi level changes before it
// measures it (breakAndComputeBidiLevels, InlineItemsBuilder.cpp:637-728), and
// format characters between a word and the space resolve with the space. Premise:
// the space resolves to the word's direction, so they stay in the word's item and
// the word keeps its kerning. Its gap is a space that resolves to the other
// direction, where Safari measures the word alone (ENGINE_FOLLOWUPS.md, Bidi
// levels, direction and script runs). Returns the zero-width breaks between the
// text and the space, or null when the text takes no kerning.
/** @requires safeInteger(analysisIndex) && safeInteger(to) && 0 <= analysisIndex && analysisIndex < to && to <= analysis.flags.length && to <= analysis.starts.length */
function getFollowingSpaceTail(analysis: TextAnalysis, analysisIndex: number, to: number): Effects<{}, string | null> {   // PAPER: annotation
  const { normalized, spaceSources, starts, flags } = analysis
  let next = analysisIndex + 1
  /** @invariant safeInteger(next) && safeInteger(to) && 0 <= next && next <= to && to <= flags.length && to <= starts.length */
  while (next < to && (flags[next]! & KIND_BITS) === ZERO_WIDTH_BREAK) next++
  if (next >= to) return null
  const nextKind = flags[next]! & KIND_BITS
  // A collapsed space's first source character: WebKit looks at the source after a text item.
  const spaceStart = starts[next]!
  if ((nextKind !== SPACE && nextKind !== PRESERVED_SPACE) || (spaceSources === null ? normalized.charCodeAt(spaceStart) : (spaceSources[spaceStart] ?? missing())) !== 0x20) return null
  return normalized.slice(starts[analysisIndex + 1], spaceStart)
}

// A zero-width break before the space ends the measured item, so only the
// item's kerning with the space is added to the text's own width.
function getTailKerning(item: string, measurement: FontMeasurement, spaceWidth: number): Effects<{ fields: "any" }, number> {   // PAPER: annotation
  return getFollowingSpaceMetrics(item, measurement).width - getSegmentMetrics(item, measurement).width - spaceWidth
}

// Pieces split by a soft hyphen are measured apart, but Blink and Gecko shape
// the unbroken text together: cursive joins, marks and kerning across the soft
// hyphen. Canvas shows how much narrower the neighbors measure joined than
// apart, which isolated widths can't show when proving that a hyphen overflows.
// A line counts it for the soft hyphens it passes, and in Gecko for the one it
// ends at (returnsFromUnfitHyphen in src/line-break.ts). WebKit's return fits each
// side as measured alone and takes none (unfitHyphenRetreat).
/** @requires safeInteger(analysisIndex) && safeInteger(to) && 0 <= analysisIndex && analysisIndex < to && to <= analysis.flags.length && to <= analysis.texts.length */
function getJoinedNarrowing(analysis: TextAnalysis, analysisIndex: number, to: number, before: string | null, beforeMetrics: SegmentMetrics | null, measurement: FontMeasurement, emojiCorrection: number, lineFitEpsilon: number): Effects<{ fields: "any"; "@state": "any" }, number> {   // PAPER: annotation
  if (before === null || beforeMetrics === null) return 0
  const { texts, flags } = analysis
  let next = analysisIndex + 1
  /** @invariant safeInteger(next) && safeInteger(to) && 0 <= next && next <= to && to <= flags.length && to <= texts.length */
  while (next < to && (flags[next]! & KIND_BITS) === SOFT_HYPHEN) next++
  if (next >= to || (flags[next]! & KIND_BITS) !== TEXT) return 0
  const after = texts[next]!
  const apart = getCorrectedSegmentWidth(before, beforeMetrics, measurement, emojiCorrection) + getTextWidth(after, measurement, emojiCorrection)
  const together = getTextWidth(before + after, measurement, emojiCorrection)
  return apart - together > lineFitEpsilon ? apart - together : 0
}

// PAPER: workaround (lazy null-prefix + disjunctive branch split): allocate null prefix by push and split on advances[idx] === null to establish shifted quantified invariant
/** @requires safeInteger(base) && safeInteger(count) && 0 <= base && 0 <= count && base + count <= advances.length
 *  @ensures result.length === count
 *  @ensures forall k in result: advances[base + k] === null || result[k] === null || advances[base + k].length <= result[k].length */
function emptyExtrasFor(advances: Dense<(number[] | null)[]>, base: number, count: number): Modifies<{}, Fresh<Dense<(number[] | null)[]>>> {   // PAPER: annotation
  const res: Dense<(number[] | null)[]> = []
  const nil: number[] | null = null
  let k = 0
  /** @invariant safeInteger(k) && safeInteger(base) && safeInteger(count) && 0 <= base && 0 <= k && k <= count && base + count <= advances.length && res.length === k
   *  @invariant forall j in res: advances[base + j] === null || res[j] === null || advances[base + j].length <= res[j].length */
  for (; k < count; k++) {
    const idx = base + k
    const a = advances[idx]
    if (a === null) {
      res.push(nil)
    } else {
      void a!
      res.push(nil)
    }
  }
  return res
}

// PAPER: workaround (zero-shift quantifier equivalence): copy extras[k] to res[0 + k] to convert shifted forall k in extras to unshifted forall i in advances
/** @requires safeInteger(base) && base === 0 && advances.length === extras.length
 *  @requires forall k in extras: advances[base + k] === null || extras[k] === null || advances[base + k].length <= extras[k].length
 *  @ensures result.length === advances.length
 *  @ensures forall i in advances: advances[i] === null || result[i] === null || advances[i].length <= result[i].length */
function alignSingleExtras(advances: (number[] | null)[], extras: (number[] | null)[], base: number): Effects<{}, Dense<(number[] | null)[]>> {   // PAPER: annotation
  const res: Dense<(number[] | null)[]> = new Array<number[] | null>(advances.length).fill(null)
  /** @invariant safeInteger(k) && safeInteger(base) && base === 0 && 0 <= k && k <= advances.length && advances.length === extras.length && res.length === advances.length
   *  @invariant forall j in extras: advances[base + j] === null || extras[j] === null || advances[base + j].length <= extras[j].length
   *  @invariant forall i in advances: advances[i] === null || res[i] === null || advances[i].length <= res[i].length */
  for (let k = 0; k < advances.length; k++) {
    const idx = base + k
    res[idx] = extras[k] ?? null
  }
  return res
}

// PAPER: workaround (dense-write pre-extension): pre-extend paragraph widths with push(0) so loop writes are in-bounds overwrites
/** @requires safeInteger(_base) && safeInteger(count) && 0 <= _base && 0 <= count && arr.length === _base
 *  @ensures arr.length - _base === count */
function extendZeros(arr: Dense<number[]>, _base: number, count: number): Effects<{ "arr[*]": "extend" }, void> {   // PAPER: annotation
  /** @invariant safeInteger(k) && safeInteger(_base) && safeInteger(count) && 0 <= k && k <= count && arr.length - _base === k */
  for (let k = 0; k < count; k++) arr.push(0)
}

// PAPER: workaround (SinglePass CFG scaling): nested loop in measureAnalysisInto explodes CFG verification past 60s
function sumExtraSpacings(extraSpacings: readonly number[], letterSpacing: number): Modifies<{}, number> {
  let sum = 0
  for (let k = 0; k < extraSpacings.length; k++) sum += extraSpacings[k]! * letterSpacing
  return sum
}

// PAPER: workaround (SinglePass CFG scaling): extracted from measureAnalysisInto's loop to avoid nested loops and branch merges blowing past 60s
/** @requires 1 <= advances.length
 *  @ensures result.length === advances.length */
function adjustFitAdvances(
  advances: Dense<number[]>,
  followingSpaceKerning: number,
  extraSpacings: readonly number[],
  unspaced: number[] | null,
  letterSpacing: number,
): Effects<{}, Dense<number[]>> {   // PAPER: annotation
  let fitAdvances: Dense<number[]> = advances
  if (followingSpaceKerning !== 0) {
    const copy = fitAdvances.slice()
    const idx = copy.length - 1
    copy[idx] = copy[idx]! + followingSpaceKerning
    fitAdvances = copy
  }
  if (extraSpacings.length !== 0) {
    const copy = fitAdvances.slice()
    if (extraSpacings.length > copy.length) throw new RangeError('index')
    /** @invariant copy.length === advances.length && extraSpacings.length <= copy.length */
    for (let k = 0; k < extraSpacings.length; k++) {
      copy[k] = copy[k]! + extraSpacings[k]! * letterSpacing
    }
    fitAdvances = copy
  }
  if (unspaced !== null) {
    const copy = fitAdvances.slice()
    /** @invariant copy.length === advances.length */
    for (let k = 0; k < unspaced.length; k++) {
      const idx = unspaced[k]!
      if (!(Number.isSafeInteger(idx) && 0 <= idx && idx < copy.length)) throw new RangeError('index')
      copy[idx] = copy[idx]! - letterSpacing
    }
    fitAdvances = copy
  }
  return fitAdvances
}

// A text segment's width as measured: alone, or together with the following space less
// that space, plus the item's kerning with a space that follows zero-width breaks. Apart
// from measureAnalysis()'s loop, whose code JavaScriptCore otherwise never optimizes fully
// on CJK text (RESEARCH.md, Keeping Work Bounded).
function getTextSegmentWidth(text: string, textMetrics: SegmentMetrics, measurement: FontMeasurement, emojiCorrection: number, followingSpaceWidth: number, followingSpaceKerning: number): Effects<{ fields: "any"; "@state": "any" }, number> {   // PAPER: annotation
  return getCorrectedSegmentWidth(text, textMetrics, measurement, emojiCorrection) - followingSpaceWidth + followingSpaceKerning
}

// Measures segments [from, to) of an analysis in a font, alone: all of a text's, or those of one
// item of a rich-inline paragraph (RESEARCH.md, Rich Inline As One Paragraph), where only the
// marks Blink halts and a run of U+3000 read the text around the item (getHanKerningTrims,
// addIdeographicSpaceHangs). Each segment's width, flags byte and advances go on the end of
// three lists: a text's own, or for an item its paragraph's, so an item is measured with no
// copy of its part of the analysis and no lists of its own to copy from. The handle returned
// holds those lists; what else it holds is the measured segments' alone, each list from the
// first of them.
/**
 * @requires safeInteger(from) && 0 <= from && from <= to && safeInteger(to) && to <= analysis.flags.length && to <= analysis.starts.length && to <= analysis.texts.length
 * @requires safeInteger(base) && 0 <= base && base <= 4294967295
 * @requires paragraph !== null || base === 0
 * @requires segments === null || segments.length === 0
 * @requires paragraph === null || paragraph.widths !== paragraph.breakableFitAdvances && paragraph.widths !== analysis.flags && paragraph.widths !== analysis.starts && paragraph.breakableFitAdvances !== analysis.texts
 * @requires paragraph === null || segments === null || paragraph.widths !== segments && paragraph.breakableFitAdvances !== segments
 * @requires paragraph === null || paragraph.widths.length === base && paragraph.breakableFitAdvances.length === base
 * @requires paragraph === null || forall i in paragraph.breakableFitAdvances: paragraph.breakableFitAdvances[i] === null || 1 <= paragraph.breakableFitAdvances[i].length
 * @ensures paragraph !== null || result.segmentFlags.length === result.widths.length
 * @ensures result.breakableFitAdvances.length === result.widths.length
 * @ensures paragraph !== null || result.widths.length === to - from
 * @ensures paragraph === null || result.widths.length - base === to - from
 * @ensures result.lineStartExtras === null || to - from <= result.lineStartExtras.length
 * @ensures result.lineEndTrims === null || to - from <= result.lineEndTrims.length
 * @ensures result.overflowLineEndTrims === null || to - from <= result.overflowLineEndTrims.length
 * @ensures result.breakableLineStartExtras === null || to - from <= result.breakableLineStartExtras.length
 * @ensures result.discretionaryHyphenContexts === null || to - from <= result.discretionaryHyphenContexts.length
 * @ensures forall i in result.breakableFitAdvances: result.breakableFitAdvances[i] === null || 1 <= result.breakableFitAdvances[i].length
 * @ensures paragraph !== null || result.breakableLineStartExtras === null || forall i in result.breakableFitAdvances: result.breakableFitAdvances[i] === null || result.breakableLineStartExtras[i] === null || result.breakableFitAdvances[i].length <= result.breakableLineStartExtras[i].length
 */
export function measureAnalysis(
  analysis: TextAnalysis,
  from: number,
  to: number,
  font: string,
  // Where each measured segment's text goes, or null.
  segments: string[] | null,
  letterSpacing: number,
  engineProfile: EngineProfile,
  language: string | null,
  // Whether text segments take emergency breaks between graphemes: an atomic rich item,
  // which is only laid out whole, takes none.
  overflowBreaks: boolean,
  // The paragraph's lists for a rich-inline item, null for a text.
  paragraph: ParagraphLists | null,
  // Where the first measured segment goes in the lists (0 for a text, paragraph.widths.length for an item).
  // PAPER: workaround (parameterized paragraph-vs-single split): split single-text vs paragraph-item entrypoints and pass base explicitly so loop invariants link widths/breakableFitAdvances to base
  base: number,
): Effects<{ "paragraph.widths[*]": "extend"; "paragraph.widths[#]": "any"; "paragraph.breakableFitAdvances[*]": "extend"; "segments[*]": "extend"; fields: "any"; views: "grow"; "@state": "any" }, MeasuredSegments> {   // PAPER: annotation
  if (paragraph === null) {
    const widths: Dense<number[]> = zeros(to - from)
    const segmentFlags: Uint8Array = new Uint8Array(to - from)
    const breakableFitAdvances: Dense<(number[] | null)[]> = []
    const res = measureAnalysisInto(analysis, from, to, font, segments, letterSpacing, engineProfile, language, overflowBreaks, widths, segmentFlags, breakableFitAdvances, base)
    const lineStartExtras = res.lineStartExtras
    const lineEndTrims = res.lineEndTrims
    const overflowLineEndTrims = res.overflowLineEndTrims
    const discretionaryHyphenContexts = res.discretionaryHyphenContexts
    const resExtras = res.breakableLineStartExtras
    const breakableLineStartExtras = resExtras !== null ? alignSingleExtras(breakableFitAdvances, resExtras, base) : null
    const prepared: MeasuredSegments = {   // PAPER: annotation
      widths,
      segmentFlags,
      simpleLineWalkFastPath: res.simpleLineWalkFastPath,
      simpleLineCountFastPath: res.simpleLineCountFastPath,
      breakableFitAdvances,
      letterSpacing: res.letterSpacing,
      discretionaryHyphenWidth: res.discretionaryHyphenWidth,
      discretionaryHyphenContexts,
      breakableLineStartExtras,
      lineStartExtras,
      lineEndTrims,
      overflowLineEndTrims,
      tabStopAdvance: res.tabStopAdvance,
      minimumTabAdvance: res.minimumTabAdvance,
    }
    return prepared
  }
  extendZeros(paragraph.widths, base, to - from)
  return measureAnalysisInto(analysis, from, to, font, segments, letterSpacing, engineProfile, language, overflowBreaks, paragraph.widths, paragraph.segmentFlags, paragraph.breakableFitAdvances, base)
}

/**
 * @requires safeInteger(from) && 0 <= from && from <= to && safeInteger(to) && to <= analysis.flags.length && to <= analysis.starts.length && to <= analysis.texts.length
 * @requires safeInteger(base) && 0 <= base && base <= 4294967295
 * @requires widths !== breakableFitAdvances && widths !== analysis.flags && widths !== analysis.starts && breakableFitAdvances !== analysis.texts
 * @requires widths.length === base && breakableFitAdvances.length === base
 * @requires forall i in breakableFitAdvances: breakableFitAdvances[i] === null || 1 <= breakableFitAdvances[i].length
 * @ensures widths.length - base === to - from && breakableFitAdvances.length === widths.length
 * @ensures result.lineStartExtras === null || to - from <= result.lineStartExtras.length
 * @ensures result.lineEndTrims === null || to - from <= result.lineEndTrims.length
 * @ensures result.overflowLineEndTrims === null || to - from <= result.overflowLineEndTrims.length
 * @ensures result.breakableLineStartExtras === null || result.breakableLineStartExtras.length === to - from
 * @ensures result.discretionaryHyphenContexts === null || to - from <= result.discretionaryHyphenContexts.length
 * @ensures forall i in breakableFitAdvances: breakableFitAdvances[i] === null || 1 <= breakableFitAdvances[i].length
 * @ensures result.breakableLineStartExtras === null || forall k in result.breakableLineStartExtras: breakableFitAdvances[base + k] === null || result.breakableLineStartExtras[k] === null || breakableFitAdvances[base + k].length <= result.breakableLineStartExtras[k].length
 */
export function measureParagraphAnalysis(
  analysis: TextAnalysis,
  from: number,
  to: number,
  font: string,
  letterSpacing: number,
  engineProfile: EngineProfile,
  language: string | null,
  widths: Dense<number[]>,
  segmentFlags: Uint8Array,
  breakableFitAdvances: Dense<(number[] | null)[]>,
  base: number,
): Effects<{ "widths[*]": "extend"; "widths[#]": "any"; "breakableFitAdvances[*]": "extend"; fields: "any"; views: "grow"; "@state": "any" }, MeasuredSegments> {   // PAPER: annotation
  extendZeros(widths, base, to - from)
  return measureAnalysisInto(analysis, from, to, font, null, letterSpacing, engineProfile, language, true, widths, segmentFlags, breakableFitAdvances, base)
}

/**
 * @requires safeInteger(from) && 0 <= from && from <= to && safeInteger(to) && to <= analysis.flags.length && to <= analysis.starts.length && to <= analysis.texts.length
 * @requires safeInteger(base) && 0 <= base && base <= 4294967295
 * @requires segments === null || segments.length === 0
 * @requires widths !== breakableFitAdvances && widths !== analysis.flags && widths !== analysis.starts && breakableFitAdvances !== analysis.texts
 * @requires segments === null || widths !== segments && breakableFitAdvances !== segments
 * @requires widths.length - base === to - from && breakableFitAdvances.length === base
 * @requires forall i in breakableFitAdvances: breakableFitAdvances[i] === null || 1 <= breakableFitAdvances[i].length
 * @ensures result.widths.length === widths.length && widths.length - base === to - from
 * @ensures result.breakableFitAdvances.length === result.widths.length && breakableFitAdvances.length === widths.length
 * @ensures result.lineStartExtras === null || to - from <= result.lineStartExtras.length
 * @ensures result.lineEndTrims === null || to - from <= result.lineEndTrims.length
 * @ensures result.overflowLineEndTrims === null || to - from <= result.overflowLineEndTrims.length
 * @ensures result.breakableLineStartExtras === null || result.breakableLineStartExtras.length === to - from
 * @ensures result.discretionaryHyphenContexts === null || to - from <= result.discretionaryHyphenContexts.length
 * @ensures forall i in result.breakableFitAdvances: result.breakableFitAdvances[i] === null || 1 <= result.breakableFitAdvances[i].length
 * @ensures forall i in breakableFitAdvances: breakableFitAdvances[i] === null || 1 <= breakableFitAdvances[i].length
 * @ensures result.breakableLineStartExtras === null || forall k in result.breakableLineStartExtras: breakableFitAdvances[base + k] === null || result.breakableLineStartExtras[k] === null || breakableFitAdvances[base + k].length <= result.breakableLineStartExtras[k].length
 */
function measureAnalysisInto(
  analysis: TextAnalysis,
  from: number,
  to: number,
  font: string,
  segments: string[] | null,
  letterSpacing: number,
  engineProfile: EngineProfile,
  language: string | null,
  overflowBreaks: boolean,
  widths: Dense<number[]>,
  segmentFlags: Uint8Array,
  breakableFitAdvances: Dense<(number[] | null)[]>,
  base: number,
): Effects<{ "widths[*]": "extend"; "widths[#]": "any"; "breakableFitAdvances[*]": "extend"; "segments[*]": "extend"; fields: "any"; views: "grow"; "@state": "any" }, MeasuredSegments> {   // PAPER: annotation
  const { normalized, texts, starts, flags } = analysis
  // The measured text and where it starts in the analysis's: what is asked of the whole text
  // is asked of it, and places in it count from its start.
  const ownStart = from === 0 || from === to ? 0 : starts[from]!
  const own = from === to ? '' : from === 0 && to === flags.length ? normalized : to === from + 1 ? texts[from]! : normalized.slice(ownStart, to < flags.length ? starts[to]! : normalized.length)
  const hasLetterSpacing = letterSpacing !== 0
  const fontMeasurement = getFontMeasurement(font, language, hasLetterSpacing)
  const emojiCorrection = textMayContainEmoji(own) ? getEmojiCorrection(font, fontMeasurement) : 0
  // Whether the text holds a U+0020. Only then can a space follow one of its text segments
  // (getFollowingSpaceTail), so a text of none, as most CJK paragraphs are, doesn't look for
  // one after each segment.
  const hasSpace = own.includes(' ')
  // The font's space, asked for only by a text that holds a space or a tab. A web font split by
  // unicode-range has the part with U+0020 loaded only once a text that holds a character of
  // that part was loaded for (document.fonts.load(font, text)), so a text of other characters
  // alone, a CJK label or one Cyrillic word, would measure the fallback font's space and the
  // font would keep it for every later text.
  const spaceWidth = hasSpace || own.includes('\t') ? getSpaceWidth(fontMeasurement) : 0
  // The advance between tab stops: eight spaces, each with its letter spacing where the
  // engine counts it (EngineProfile's letterSpaceTabStops). Gecko rounds the space and the
  // letter spacing to app units, sixtieths of a pixel, each on its own
  // (ComputeTabWidthAppUnits, nsTextFrame.cpp:3875-3906).
  const tabStopSpacing = engineProfile.letterSpaceTabStops ? letterSpacing : 0
  const tabStopAdvance = engineProfile.tabsInAppUnits
    ? (Math.round(spaceWidth * 60) + Math.round(tabStopSpacing * 60)) * 8 / 60
    : (spaceWidth + tabStopSpacing) * 8
  // The least a tab advances, measured at a text's first tab (EngineProfile's tabMinimumCharacter).
  let minimumTabAdvance = 0

  // The font's kerning with the space where words take Blink's kerning with the spaces beside
  // them, or null. Blink shapes nothing across a change of direction
  // (ShouldBreakShapingBeforeText, inline_node.cc:472-490), and which spaces share a word's
  // direction depends on the paragraph's, which preparation can't see, so text with a
  // right-to-left letter or an explicit bidi control takes none.
  let fontSpaceKerning = engineProfile.kernsAcrossCanvasWords && own.includes(' ') ? getFontSpaceKerning(fontMeasurement) : null
  if (fontSpaceKerning !== null && mixedDirectionRe.test(own)) fontSpaceKerning = null
  resetScriptRuns()
  const useUnspacedRuns = engineProfile.unspacedCursive === 'run'
  // What the word before a space adds to that space, the next segment.
  let spaceShare = 0

  // Whether the text may hold graphemes that take no letter spacing in this engine.
  const cursiveSpacing = hasLetterSpacing && engineProfile.unspacedCursive !== 'none' && mayHoldCursive(own)

  // Text of the simple walkers' kinds without letter spacing. They lay it out where
  // the scan breaks at every segment boundary, and layout() counts it with the
  // simple stepper where it doesn't (countPreparedLines).
  let simpleKinds = !hasLetterSpacing
  let breakableLineStartExtras: Dense<(number[] | null)[]> | null = null
  let discretionaryHyphenContexts: Dense<number[]> | null = null
  let previousJoinablePiece: string | null = null
  let previousJoinableMetrics: SegmentMetrics | null = null
  // WebKit's return from an unfit hyphen fits each side as measured alone (getJoinedNarrowing).
  const returnFitsEachSideAlone = engineProfile.unfitHyphenRetreat === 'full-width-or-first'

  // Each segment is stored at its index: `at` in the text's or the paragraph's three lists,
  // `mi - from` in the lists of the measured segments alone. Stored and not pushed, for V8:
  // once it has deoptimized at a push onto a paragraph's list, it compiles that push as a call
  // from then on, for texts too. With stores Chrome 154 prepares plain text again 4-9% faster
  // than with pushes on a page of mostly plain text whose first rich paragraphs are short, and
  // they cost about 1% of preparing a text again in Safari 27, 1.9% at most in one run
  // (RESEARCH.md, Keeping Work Bounded, JavaScript Engines, under A list made where it is
  // filled; Decisions Log, 2026-10-09, a paragraph's lists).
  let s = 0   // PAPER: workaround (shifted loop counter #397): 0-based counter s = mi - from so post-loop derives breakableLineStartExtras.length === to - from
  /**
   * @invariant safeInteger(mi) && safeInteger(from) && safeInteger(to) && safeInteger(base) && safeInteger(at) && safeInteger(s) && 0 <= from && from <= mi && mi <= to && to <= flags.length && starts.length === flags.length && flags.length <= texts.length && 0 <= base && base <= 4294967295 && s === mi - from && at === base + s && widths.length === base + (to - from) && breakableFitAdvances.length === at && widths !== breakableFitAdvances && breakableFitAdvances !== texts
   * @invariant discretionaryHyphenContexts === null || discretionaryHyphenContexts.length === to - from && widths !== discretionaryHyphenContexts && breakableFitAdvances !== discretionaryHyphenContexts
   * @invariant discretionaryHyphenContexts === null || breakableLineStartExtras === null || breakableLineStartExtras !== discretionaryHyphenContexts
   * @invariant segments === null || segments.length === s && widths !== segments && breakableFitAdvances !== segments
   * @invariant segments === null || breakableLineStartExtras === null || breakableLineStartExtras !== segments
   * @invariant breakableLineStartExtras === null || breakableLineStartExtras.length === s && breakableLineStartExtras !== breakableFitAdvances && breakableLineStartExtras !== widths && breakableLineStartExtras !== texts
   * @invariant forall i in breakableFitAdvances: breakableFitAdvances[i] === null || 1 <= breakableFitAdvances[i].length
   * @invariant breakableLineStartExtras === null || forall k in breakableLineStartExtras: breakableFitAdvances[base + k] === null || breakableLineStartExtras[k] === null || breakableFitAdvances[base + k].length <= breakableLineStartExtras[k].length
   */
  for (let mi = from, at = base; mi < to; mi++, at++, s++) {
    const text = texts[mi]!
    const segment = flags[mi]!
    const kind = segment & KIND_BITS
    let width = 0
    // Graphemes that take letter spacing after them.
    let spacingGraphemeCount = 0
    let fitTextMetrics: SegmentMetrics | null = null
    let fitFollowingSpaceTail: string | null = null
    let fitFollowingSpaceKerning = 0
    let fitExtraSpacings: readonly number[] = noExtraSpacings
    let fitUnspaced: number[] | null = null
    switch (kind) {
      case TEXT: {
        // A control the engine hides takes no advance, only letter spacing.
        if (engineProfile.hidesControlCharacters && controlCharacterRe.test(text)) {
          spacingGraphemeCount = 1
          break
        }
        // With an empty following-space tail, the text is measured together with the space,
        // so its kerned width costs no extra Canvas call, and other occurrences of the same
        // text measure it alone; with a zero-width tail, the item's kerning is added.
        const followingSpaceTail = engineProfile.measureTextWithFollowingSpace && hasSpace ? getFollowingSpaceTail(analysis, mi, to) : null
        const textMetrics = followingSpaceTail === '' ? getFollowingSpaceMetrics(text, fontMeasurement) : getSegmentMetrics(text, fontMeasurement)
        previousJoinablePiece = text
        previousJoinableMetrics = textMetrics
        let followingSpaceKerning = followingSpaceTail === null || followingSpaceTail === '' ? 0 : getTailKerning(text + followingSpaceTail, fontMeasurement, spaceWidth)
        if (fontSpaceKerning !== null && textMetrics.spaceKerning !== noSpaceKerning) {
          const spaceBefore = mi > from && isSpaceKind(flags[mi - 1]! & KIND_BITS)
          const spaceAfter = mi + 1 < to && isSpaceKind(flags[mi + 1]! & KIND_BITS)
          if (spaceBefore || spaceAfter) {
            const kerning = textMetrics.spaceKerning ?? getSpaceKerning(text, textMetrics, fontMeasurement, fontSpaceKerning)
            if (spaceAfter) {
              // Premise: a kerning that tightens the word and the space after it goes on the
              // space, which hangs, so a line that ends there has the word without it, as in
              // Blink under a text-align other than start and for text whose element has a
              // decoration or a background (NeedsAccurateEndPosition, line_breaker.cc:255-268).
              // One that widens stays on the word, whose end Blink finds in the run shaped
              // whole. In other text a line's last word is wider here than there by the
              // kerning, never narrower (RESEARCH.md, Kerning At Line Edges).
              followingSpaceKerning = Math.max(kerning.after, 0)
              spaceShare = Math.min(kerning.after, 0)
            }
            // The space takes its kerning with this word, and takes it along where it hangs: a
            // line that breaks between the two is shaped again without it
            // (shaping_line_breaker.cc:307-324). Preserved spaces that start the text or follow
            // a forced break are a Blink item of their own (inline_items_builder.cc:988-1034),
            // which kerns with nothing.
            if (spaceBefore && kerning.before !== 0 &&
              !((flags[mi - 1]! & KIND_BITS) === PRESERVED_SPACE && (mi === from + 1 || (flags[mi - 2]! & KIND_BITS) === HARD_BREAK)) &&
              spaceSharesScriptRun(own, starts[mi]! - ownStart, starts[mi]! - ownStart + text.length)) {
              widths[at - 1] = widths[at - 1]! + kerning.before
            }
          }
        }
        width = getTextSegmentWidth(text, textMetrics, fontMeasurement, emojiCorrection, followingSpaceTail === '' ? spaceWidth : 0, followingSpaceKerning)
        // The walkers put a gap after every grapheme of a spaced segment, so a grapheme
        // the engine gives none takes one back from its advance, here and in the advances
        // a break inside the segment falls by, and one whose glyphs WebKit gives more or
        // fewer takes the difference (EngineProfile's letterSpacesGlyphs), in text of its
        // complex path.
        let unspaced: number[] | null = null
        let extraSpacings = noExtraSpacings
        if (hasLetterSpacing) {
          spacingGraphemeCount = countRenderedSpacingGraphemes(text, kind, engineProfile.graphemeTable)
          if (cursiveSpacing) {
            unspaced = getUnspacedGraphemes(own, starts[mi]! - ownStart, starts[mi]! - ownStart + text.length, engineProfile.graphemeTable, useUnspacedRuns)
            if (unspaced !== null) width -= unspaced.length * letterSpacing
          }
          if (engineProfile.letterSpacesGlyphs) {
            extraSpacings = textMetrics.extraSpacings ??= needsComplexTextPath(text) ? getExtraSpacings(text, fontMeasurement) : noExtraSpacings
            width += sumExtraSpacings(extraSpacings, letterSpacing)
          }
        }
        // Under break-word, Blink retries an overflowing line with a break allowed between
        // any two graphemes (line_breaker.cc), WebKit searches the word's grapheme prefixes
        // (TextUtil::breakWord) and Gecko may wrap before any cluster (gfxTextRun.cpp:1069-1072),
        // so every text segment takes emergency grapheme breaks, unless it is one Gecko cluster
        // or an atomic item's.
        if (!overflowBreaks || (segment & ONE_CLUSTER) !== 0 || text.length === 1) break
        fitTextMetrics = textMetrics
        fitFollowingSpaceTail = followingSpaceTail
        fitFollowingSpaceKerning = followingSpaceKerning
        fitExtraSpacings = extraSpacings
        fitUnspaced = unspaced
        break
      }
      case SPACE:
      case PRESERVED_SPACE:
      case ZERO_WIDTH_BREAK:
        width = getTextWidth(text, fontMeasurement, emojiCorrection) + spaceShare
        spaceShare = 0
        if (hasLetterSpacing) spacingGraphemeCount = countRenderedSpacingGraphemes(text, kind, engineProfile.graphemeTable)
        break
      case TAB:
        if (engineProfile.letterSpaceTabs) spacingGraphemeCount = 1
        if (minimumTabAdvance === 0) minimumTabAdvance = getTextWidth(engineProfile.tabMinimumCharacter, fontMeasurement, emojiCorrection) / 2
        break
      case CONTROL: {
        width = getTextWidth(text, fontMeasurement, emojiCorrection)
        // NEL shares a WebKit text item with the text before it and with
        // combining marks after it, and the complex text path spaces it. Complex
        // text shares the item only when its direction matches the page's, which
        // preparation cannot see, so NEL next to complex text keeps its spacing.
        const nextText = mi + 1 < to ? texts[mi + 1]! : ''
        if (hasLetterSpacing && (
          (mi > from && (flags[mi - 1]! & KIND_BITS) === TEXT && needsComplexTextPath(texts[mi - 1]!)) ||
          (leadingCombiningMarkRe().test(nextText) && needsComplexTextPath(nextText))
        )) spacingGraphemeCount = 1
        break
      }
      case SOFT_HYPHEN:
      case ZERO_WIDTH_GLUE:
      case HARD_BREAK:
        break
    }
    if (kind !== TEXT && kind !== SPACE && kind !== ZERO_WIDTH_BREAK) simpleKinds = false
    if (kind !== TEXT && kind !== SOFT_HYPHEN) previousJoinablePiece = null
    const flagsByte = (segment & ~ONE_CLUSTER) | (hasLetterSpacing && spacingGraphemeCount > 0 ? SPACED : 0)
    segmentFlags[at] = flagsByte
    widths[at] = addInternalLetterSpacing(width, spacingGraphemeCount, letterSpacing)
    // PAPER: workaround (parallel push ordering): defer getSegmentFit out of switch and branch on breakableLineStartExtras === null so breakableFitAdvances.push and breakableLineStartExtras.push stay paired
    if (fitTextMetrics !== null) {
      const fitMode: BreakableFitMode = letterSpacing !== 0 ? 'segment-prefixes'
        : numericRunRe.test(text) ? 'pair-context'
        : fitTextMetrics.width < engineProfile.prefixFitMinWidth ? 'sum-graphemes'
        : engineProfile.cutWordFit
      const cachedFit = getSegmentFit(text, fitTextMetrics, fontMeasurement, emojiCorrection, fitMode, fitFollowingSpaceTail === '' ? spaceWidth : null)
      const origAdvances = cachedFit.advances
      if (origAdvances !== null) {
        // A difference from the advance, so it holds whatever the advances take below.
        const startExtras = cachedFit.lineStartExtras
        if (startExtras !== null) {
          // The cached advances are shared by every occurrence of this text; only
          // the final grapheme touches the following space.
          const fitAdvances = adjustFitAdvances(origAdvances, fitFollowingSpaceKerning, fitExtraSpacings, fitUnspaced, letterSpacing)
          if (breakableLineStartExtras === null) {
            breakableLineStartExtras = emptyExtrasFor(breakableFitAdvances, base, s)
            breakableFitAdvances.push(fitAdvances)
            breakableLineStartExtras.push(startExtras)
          } else {
            breakableFitAdvances.push(fitAdvances)
            breakableLineStartExtras.push(startExtras)
          }
        } else {
          const fitAdvances = adjustFitAdvances(origAdvances, fitFollowingSpaceKerning, fitExtraSpacings, fitUnspaced, letterSpacing)
          if (breakableLineStartExtras === null) {
            breakableFitAdvances.push(fitAdvances)
          } else {
            breakableFitAdvances.push(fitAdvances)
            const noExtras: number[] | null = null
            breakableLineStartExtras.push(noExtras)
          }
        }
      } else {
        const noFit: number[] | null = null
        if (breakableLineStartExtras === null) {
          breakableFitAdvances.push(noFit)
        } else {
          breakableFitAdvances.push(noFit)
          const noExtras: number[] | null = null
          breakableLineStartExtras.push(noExtras)
        }
      }
    } else {
      const noFit: number[] | null = null
      if (breakableLineStartExtras === null) {
        breakableFitAdvances.push(noFit)
      } else {
        breakableFitAdvances.push(noFit)
        const noExtras: number[] | null = null
        breakableLineStartExtras.push(noExtras)
      }
    }
    if (segments !== null) {
      // PAPER: workaround (disjunctive aliasing before push): split on breakableLineStartExtras === null so SinglePass discharges breakableLineStartExtras !== segments across segments.push
      if (breakableLineStartExtras === null) {
        segments.push(text)
      } else {
        segments.push(text)
      }
    }
    // Contexts for every segment of soft hyphens, whatever its kind here, one that is glue
    // too, where the scan gives no break after it: a handle with contexts is one whose lines
    // return from an unfit hyphen, measured below. One that is a zero-width break is marked
    // (DROPPED), which tells it from a zero-width space, and its text is the full walker's: the
    // simple walkers take every zero-width break for a zero-width space.
    if (kind !== TEXT && text.charCodeAt(0) === 0xAD) {
      if (kind === ZERO_WIDTH_BREAK) {
        segmentFlags[at] = flagsByte | DROPPED
        simpleKinds = false
      }
      discretionaryHyphenContexts ??= zeros(to - from)   // PAPER: workaround (dense-write pre-allocation): allocate full to - from zeros so discretionaryHyphenContexts writes are in-bounds overwrites
      discretionaryHyphenContexts[s] = returnFitsEachSideAlone ? 0 : getJoinedNarrowing(analysis, mi, to, previousJoinablePiece, previousJoinableMetrics, fontMeasurement, emojiCorrection, engineProfile.lineFitEpsilon)
    }
  }

  // The hyphen a chosen soft hyphen paints, which only a text that holds one asks for, with
  // the gap before it, plus the hyphen's own spacing where the engine letter-spaces it.
  const hyphenText = discretionaryHyphenContexts === null ? '-' : engineProfile.hyphenFromPrimaryFont ? getHyphenText(fontMeasurement) : '\u2010'
  const discretionaryHyphenWidth = getTextWidth(hyphenText, fontMeasurement, emojiCorrection) +
    (letterSpacing === 0 ? 0 : letterSpacing * (engineProfile.letterSpaceDiscretionaryHyphen ? 2 : 1))

  // A segment's width is its width between the text before and after it; one that starts
  // a line takes back the halt Blink gives its first character there.
  let hanKerning: HanKerningTrims = { widthTrims: null, lineStartExtras: null, lineEndTrims: null, overflowLineEndTrims: null }
  if (engineProfile.hanKerning && textMayHanKern(own)) {
    hanKerning = getHanKerningTrims(fontMeasurement, analysis, from, to)
    const trims = hanKerning.widthTrims
    if (trims !== null) {
      /** @invariant safeInteger(from) && safeInteger(to) && safeInteger(base) && safeInteger(i) && 0 <= from && from <= to && to <= flags.length && starts.length === flags.length && flags.length <= texts.length && 0 <= base && base <= 4294967295 && 0 <= i && widths.length - base === to - from && breakableFitAdvances.length === widths.length && widths !== breakableFitAdvances
       *  @invariant trims === null || i <= trims.length && trims.length <= to - from
       *  @invariant hanKerning.lineStartExtras === null || to - from <= hanKerning.lineStartExtras.length
       *  @invariant hanKerning.lineEndTrims === null || to - from <= hanKerning.lineEndTrims.length
       *  @invariant hanKerning.overflowLineEndTrims === null || to - from <= hanKerning.overflowLineEndTrims.length
       *  @invariant discretionaryHyphenContexts === null || to - from <= discretionaryHyphenContexts.length && discretionaryHyphenContexts !== widths
       *  @invariant breakableLineStartExtras === null || breakableLineStartExtras.length === to - from && breakableLineStartExtras !== widths
       *  @invariant forall j in breakableFitAdvances: breakableFitAdvances[j] === null || 1 <= breakableFitAdvances[j].length
       *  @invariant breakableLineStartExtras === null || forall k in breakableLineStartExtras: breakableFitAdvances[base + k] === null || breakableLineStartExtras[k] === null || breakableFitAdvances[base + k].length <= breakableLineStartExtras[k].length */
      for (let i = 0; i < trims.length; i++) {
        widths[base + i] = widths[base + i]! - trims[i]!
      }
    }
  }
  // The loop above has measured every segment in the font, so text in a font that has measured
  // no kana, as in one that has answered that it kerns none, isn't looked through for kana.
  // PAPER: workaround (fields-effect read hoisting): read hanKerning fields before addKanaKerning (Effects<{ fields: "any" }>) to preserve their length bounds
  let lineStartExtras = hanKerning.lineStartExtras
  let lineEndTrims = hanKerning.lineEndTrims
  const overflowLineEndTrims = hanKerning.overflowLineEndTrims
  if (engineProfile.kernsAcrossCanvasWords && fontMeasurement.measuredKana && fontMeasurement.kanaKerning !== null && kanaPairRe.test(own)) {
    const kanaKerning = getFontKanaKerning(fontMeasurement)
    if (kanaKerning !== null) lineStartExtras = addKanaKerning(lineStartExtras, widths, base, analysis, from, to, fontMeasurement, kanaKerning)
  }
  if (engineProfile.hangsIdeographicSpace && own.includes('\u3000')) {
    lineEndTrims = addIdeographicSpaceHangs(lineEndTrims, analysis, fontMeasurement, letterSpacing, discretionaryHyphenWidth, from, to)
  }
  const prepared: MeasuredSegments = {   // PAPER: annotation
    widths,
    segmentFlags,
    simpleLineWalkFastPath: simpleKinds && !analysis.hasUnbroken,
    simpleLineCountFastPath: simpleKinds,
    breakableFitAdvances,
    letterSpacing,
    discretionaryHyphenWidth,
    discretionaryHyphenContexts,
    breakableLineStartExtras,
    lineStartExtras,
    lineEndTrims,
    overflowLineEndTrims,
    tabStopAdvance,
    minimumTabAdvance,
  }
  return prepared
}

// Blink's layout shapes a run of one script in one call and takes katakana for hiragana, so
// that the two stay in one run (GetScriptForOpenType, script_run_iterator.cc:20-36), so a kana
// kerns with the kana after it in fonts that pair them, as Hiragino Sans and Hiragino Mincho
// ProN do (GPOS pair positioning). Canvas cuts the two apart and preparation measures segments
// apart, so each such pair's kerning (getKanaKerning) is added here, for a font that kerns
// kana (getFontKanaKerning). The adjustment sits on the pair's first glyph, and a line that
// breaks between the two is shaped again without it (ShapingLineBreaker::ShapeLine,
// shaping_line_breaker.cc:511-584): one that tightens the pair goes on the second kana's
// segment, which gives it back where it starts a line. One that widens it stays on the first
// kana's, since Blink looks for a line's end in the run shaped whole
// (shaping_line_breaker.cc:325-333), where the first kana has it. A segment cut between two of
// its kana takes the same in its advances (getSegmentFit). `widths` holds segments [from, to)
// of the analysis from `base`, a rich-inline item's in its paragraph's, and `extras` holds
// them from index 0; a kana that starts an item takes no kerning with the item before it.
/** @requires safeInteger(from) && safeInteger(to) && safeInteger(base) && 0 <= from && from <= to && to <= analysis.flags.length && to <= analysis.starts.length && 0 <= base && base + (to - from) <= widths.length
 *  @requires extras === null || to - from <= extras.length
 *  @requires kernings.length === 36481
 *  @ensures result === null || to - from <= result.length */
function addKanaKerning(extras: Dense<number[]> | null, widths: Dense<number[]>, base: number, analysis: TextAnalysis, from: number, to: number, measurement: FontMeasurement, kernings: Float64Array): Effects<{ "extras[#]": "any"; "widths[#]": "any"; fields: "any"; views: "grow" }, Dense<number[]> | null> {   // PAPER: annotation
  const { normalized, starts, flags } = analysis
  /** @invariant safeInteger(from) && safeInteger(to) && safeInteger(base) && safeInteger(i) && 0 <= from && from <= i && i <= to && to <= flags.length && starts.length === flags.length && 0 <= base && base + (to - from) <= widths.length
   *  @invariant extras === null || to - from <= extras.length */
  for (let i = from; i < to; i++) {
    if ((flags[i]! & KIND_BITS) !== TEXT) continue
    const start = starts[i]!
    const end = i + 1 < flags.length ? starts[i + 1]! : normalized.length
    const at = base + (i - from)
    /** @invariant safeInteger(from) && safeInteger(to) && safeInteger(base) && safeInteger(i) && safeInteger(at) && 0 <= from && from <= i && i < to && to <= flags.length && starts.length === flags.length && 0 <= base && base + (to - from) <= widths.length && at === base + (i - from)
     *  @invariant extras === null || to - from <= extras.length */
    for (let k = i > from ? start : start + 1; k < end; k++) {
      const kerning = getKanaKerning(normalized, start, k, measurement, kernings)
      if (kerning === 0) continue
      if (k > start) {
        widths[at] = widths[at]! + kerning
      } else if (kerning > 0 && i > from) {
        widths[at - 1] = widths[at - 1]! + kerning
      } else if (kerning < 0) {
        widths[at] = widths[at]! + kerning
        extras ??= zeros(to - from)
        extras[i - from] = extras[i - from]! - kerning
      }
    }
  }
  return extras
}

// Blink (Chrome 153) hangs a run of U+3000 that ends a line, as it hangs spaces: ShapingLineBreaker
// counts U+3000 as a breakable space (IsBreakableSpace, shaping_line_breaker.cc:38-41, with
// Character::IsOtherSpaceSeparator, character.h:156-158), so a line whose width runs out on
// the run ends after it and fits without it (shaping_line_breaker.cc:384-452), and the line
// breaker keeps the run as trailing space (HandleTrailingSpaces, line_breaker.cc:2447-2514),
// in normal and pre-wrap white space alike. A text segment that ends in such a run, where a
// line can end after it or a collapsible space follows, which hangs with it, drops the run
// and its letter spacing at a line end. The line then ends where the run starts
// (shaping_line_breaker.cc:490-493), so after a soft hyphen it ends with a hyphen
// (SetBreakOffset, shaping_line_breaker.cc:212-216), which has to fit. Gecko (Firefox 156)
// marks U+3000 as a space glyph, like SPACE (SetupClusterBoundaries, gfxFont.cpp:749-750), and
// BreakAndMeasureText fits a line without its trailing space glyphs (gfxTextRun.cpp:1152-1160,
// 1175), so Firefox hangs the run too. `trims` holds segments [from, to) of the analysis, a
// rich-inline item's in its paragraph's, from index 0. A run that ends an item hangs whatever
// the next item starts with, as the engines hang it wherever a line ends; a text's run before
// a ZWSP, a soft hyphen or a character no line starts with doesn't yet (ENGINE_FOLLOWUPS.md,
// Line edges).
/** @requires safeInteger(from) && safeInteger(to) && 0 <= from && from <= to && to <= analysis.flags.length && to <= analysis.starts.length
 *  @requires trims === null || to - from <= trims.length
 *  @ensures result === null || to - from <= result.length */
function addIdeographicSpaceHangs(
  trims: Dense<number[]> | null,
  analysis: TextAnalysis,
  measurement: FontMeasurement,
  letterSpacing: number,
  hyphenWidth: number,
  from: number,
  to: number,
): Effects<{ "trims[#]": "any"; fields: "any" }, Dense<number[]> | null> {   // PAPER: annotation
  const { normalized, starts, flags } = analysis
  /** @invariant safeInteger(from) && safeInteger(to) && safeInteger(i) && 0 <= from && from <= i && i <= to && to <= flags.length && starts.length === flags.length
   *  @invariant trims === null || to - from <= trims.length */
  for (let i = from; i < to; i++) {
    const end = i + 1 < flags.length ? starts[i + 1]! : normalized.length
    if ((flags[i]! & KIND_BITS) !== TEXT || normalized.charCodeAt(end - 1) !== 0x3000) continue
    if (i + 1 < to) {
      const next = flags[i + 1]! & KIND_BITS
      if (next !== HARD_BREAK && next !== SPACE && !(next === TEXT && (flags[i + 1]! & UNBROKEN) === 0)) continue
    }
    let start = end - 1
    while (start > starts[i]! && normalized.charCodeAt(start - 1) === 0x3000) start--
    const run = normalized.slice(start, end)
    const afterSoftHyphen = i > 0 && start === starts[i] && normalized.charCodeAt(start - 1) === 0xAD
    const hang = getSegmentMetrics(run, measurement).width + run.length * letterSpacing - (afterSoftHyphen ? hyphenWidth : 0)
    if (hang <= 0) continue
    trims ??= zeros(to - from)
    trims[i - from] = trims[i - from]! + hang
  }
  return trims
}
