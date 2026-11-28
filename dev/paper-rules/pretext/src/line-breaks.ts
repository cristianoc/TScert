// Break opportunities as Chrome and Safari find them: ports of Blink's and WebKit's
// line-break scans over their own pair tables and ICU line rules, which
// scripts/generate-engine-break-data.ts writes to src/generated/engine-break-data.ts.
// The tables' bundle cost is accepted (RESEARCH.md, Decisions Log, 2026-09-23).
//
// Sources, cited as file:line:
// - ICU 78.2 as vendored in Chromium 152, under third_party/icu/source/common. Chrome
//   153 runs the same code. apple-rbbi.cpp and apple-brkiter.cpp are Apple's
//   ICU-76142.5.1.200 sources, behind libicucore 78.1 on macOS 26.5.2 and macOS 27.
// - Blink in Chromium 152, under third_party/blink/renderer/platform/text/:
//   tbi.cc = text_break_iterator.cc, tbi.h = text_break_iterator.h,
//   tbi_icu.cc = text_break_iterator_icu.cc, gen.cc = character_property_data_generator.cc.
// - WebKit safari-7625.1.29.11-branch (Safari 27.0), under Source/. Only Safari 27's rules
//   are ported, not Safari 26's (RESEARCH.md, Decisions Log, 2026-09-16):
//   BP.h = WebCore/rendering/BreakablePositions.h,
//   IIB = WebCore/layout/formattingContexts/inline/InlineItemsBuilder.cpp,
//   IFU = WebCore/layout/formattingContexts/inline/InlineFormattingUtils.cpp,
//   TU = WebCore/layout/formattingContexts/inline/text/TextUtil.cpp,
//   TBI.h = WTF/wtf/text/TextBreakIterator.h, TBIICU.h = WTF/wtf/text/icu/TextBreakIteratorICU.h.
//
// Deliberate differences:
// - ICU runs forward from the start of the text, without its boundary cache, reverse
//   table or dictionary engines. Inside runs of Thai, Lao, Khmer and Myanmar letters,
//   Intl.Segmenter word boundaries stand in for the dictionaries.
// - Blink restarts ICU at each line start, which drops the context before the line
//   (tbi.h:159-163, tbi_icu.cc:771-810). These scans read each text once.
// - Chrome opens line_normal_cj.brk for zh content, and for content without a language
//   under a Chinese UI. The scan takes preparation's language, which on a page without one
//   is the language V8 shows as its default locale, Chrome's UI language (getBlinkLineBreaks).
//   Content-Language headers and an element's own lang aren't read.
// - WebKit splits items where bidi levels change (IIB:637-775), and swaps a Han-script
//   locale for the user's first Chinese language (FontDescription.cpp:74-83, 107-113).
//   Pretext resolves no bidi levels here and takes preparation's language as it is.

import { missing } from './checked.js'
import {
  appleQuoteRemaps,
  blinkLinePairsPacked,
  classMaps,
  classRemapsPacked,
  classRunsVarints,
  jointClassCount,
  ruleTables,
  webkitLinePairsPacked,
  type ClassMap,
  type RuleTable,
} from './generated/engine-break-data.js'

// What a scan marks at a position of its text, as bits. A line may start at a BREAK. The WebKit
// scan marks a FORCED_BREAK after a U+2028 or U+2029 that starts an item; the Gecko scan marks a
// CLUSTER_START where a cluster starts without a break, and a SOFT_HYPHEN_BREAK with the BREAK
// right after a soft hyphen. A rich-inline paragraph's analysis marks an ITEM_START where one of
// its items starts, which starts a segment whether or not a line may start there.
export const BREAK = 1
export const CLUSTER_START = 2
export const FORCED_BREAK = 4
export const SOFT_HYPHEN_BREAK = 8
export const ITEM_START = 16

// Page languages whose line-break rules differ in some engine. Every other
// language, an empty or missing one, and no document read as root.
type BreakLanguage = 'root' | 'ja' | 'ko' | 'zh'

// The primary language subtag, ASCII case-insensitively, up to `-`, `_` or the
// end. No allocation: preparation calls this once per text.
export function getBreakLanguage(tag: string | null): Effects<{}, BreakLanguage> {   // PAPER: annotation
  if (tag === null || tag.length < 2) return 'root'
  if (tag.length > 2 && tag.charCodeAt(2) !== 0x2D && tag.charCodeAt(2) !== 0x5F) return 'root'
  const first = tag.charCodeAt(0) | 0x20
  const second = tag.charCodeAt(1) | 0x20
  if (first === 0x6A && second === 0x61) return 'ja'
  if (first === 0x6B && second === 0x6F) return 'ko'
  if (first === 0x7A && second === 0x68) return 'zh'
  return 'root'
}

// The generated tables of bytes ship packed, in base64: the unpacked length, then runs of literal
// bytes, each followed by a copy of earlier bytes (length - 4, then distance back), every count a
// little-endian base-128 varint. Packing keeps the tables a page parses small; a page unpacks only
// its engine's tables.
/** @requires expectedLength === null || (safeInteger(expectedLength) && 0 <= expectedLength)
 *  @ensures expectedLength === null || (safeInteger(expectedLength) && result.length === expectedLength) */
function unpackTableWithLength(packed: string, expectedLength: number | null): Effects<{}, Uint8Array> {   // PAPER: annotation
  const input = atob(packed)
  let at = 0
  const varint = (): number => {
    let value = 0
    let scale = 1
    let byte: number
    do {
      byte = input.charCodeAt(at++)
      value += (byte & 0x7f) * scale
      scale *= 0x80
    } while (byte >= 0x80)
    return value
  }
  const bytes = new Uint8Array(varint())
  let out = 0
  while (at < input.length) {
    for (let n = varint(); n > 0; n--) bytes[out++] = input.charCodeAt(at++)
    if (at >= input.length) break
    const length = varint() + 4
    const from = out - varint()
    // A copy that overlaps the bytes it writes repeats them, so it goes one byte at a time.
    if (from + length <= out) {
      bytes.copyWithin(out, from, from + length)
    } else {
      if (!Number.isSafeInteger(from) || !Number.isSafeInteger(length) || from < 0 || length < 0 || length > bytes.length || from > bytes.length - length) {
        out = -1
        break
      }
      /** @invariant safeInteger(k) && safeInteger(from) && safeInteger(length) && 0 <= k && 0 <= from && from + length <= bytes.length */
      for (let k = 0; k < length; k++) bytes[out + k] = bytes[from + k]!
    }
    out += length
  }
  if (out !== bytes.length || (expectedLength !== null && bytes.length !== expectedLength)) {
    throw new Error('A packed table unpacked to the wrong length')
  }
  return bytes
}

export function unpackTable(packed: string): Effects<{}, Uint8Array> {   // PAPER: annotation
  return unpackTableWithLength(packed, null)
}

// The little-endian base-128 varints a table in base64 holds. Tables of varints ship without
// unpackTable's packing, which saves them nothing once the bundle is compressed.
export function unpackVarints(base64: string): Effects<{}, Int32Array> {   // PAPER: annotation
  const input = atob(base64)
  const values = new Int32Array(input.length)
  let count = 0
  for (let i = 0; i < input.length;) {
    let byte = input.charCodeAt(i++)
    let value = byte & 0x7f
    for (let shift = 7; byte >= 0x80; shift += 7) {
      byte = input.charCodeAt(i++)
      value |= (byte & 0x7f) << shift
    }
    values[count++] = value
  }
  return values.subarray(0, count)
}

// A code point's class in one of the generated maps, in two loads: `index` has, for every 256 code
// points up to U+10FFFF, their block of `values`. Code points that share a class through a whole
// block share one block.
/** @invariant this.index.length === 4352 */
export type ClassTable = {
  /** @stable */
  readonly index: Uint16Array
  readonly values: Uint8Array
}

/** @requires index.length === 4352 && safeInteger(c) && 0 <= c && c <= 0x10ffff */
export function getClassFrom(index: Uint16Array, values: Uint8Array, c: number): Effects<{}, number> {   // PAPER: annotation
  return values[(index[c >> 8]! << 8) | (c & 0xff)] ?? missing()
}

// For c in U+0000..U+10FFFF, which is every code point a scan decodes from UTF-16: `index` has no
// entry above that, where the engines' tries give their error value (unicode/ucptrie.h:615-620;
// getLineBreakClass in src/gecko-line-breaks.ts gives ICU4X's itself).
/** @requires safeInteger(c) && 0 <= c && c <= 0x10ffff */
export function getClass(table: ClassTable, c: number): Effects<{}, number> {   // PAPER: annotation
  return getClassFrom(table.index, table.values, c)
}

// The code point at text[i], in a surrogate pair ending before `end`, or the code unit itself.
/** @requires safeInteger(i) && 0 <= i && i < text.length && safeInteger(end) && end <= text.length
 *  @ensures safeInteger(result) && 0 <= result && result <= 0x10ffff */
export function readCodePoint(text: string, i: number, end: number): Effects<{}, number> {   // PAPER: annotation
  const c = text.charCodeAt(i)
  if (c >= 0xd800 && c <= 0xdbff && i + 1 < end) {
    const next = text.charCodeAt(i + 1)
    if (next >= 0xdc00 && next <= 0xdfff) return ((c - 0xd800) << 10) + (next - 0xdc00) + 0x10000
  }
  return c
}

// The maps ship as one list of runs over U+0000..U+10FFFF, each run a length - 1 and a joint class:
// the joint classes are the classes all the maps together tell apart, so code points that the
// engines class alike are stored once. `remap` has one map's class for each joint class, and
// `blocks` is how many blocks its table takes. Throws for a list that doesn't end at U+10FFFF, an
// empty one included.
export function unpackClassRuns(runs: Int32Array, remap: Uint8Array, blocks: number): Effects<{}, ClassTable> {   // PAPER: annotation
  const index = new Uint16Array(0x1100)
  const values = new Uint8Array(blocks << 8)
  // The block each class fills whole, once a run covers one.
  const whole = new Int32Array(0x100)
  whole.fill(-1)
  let count = 0
  let c = 0
  let end = 0
  let value = -1
  /** @invariant safeInteger(r) && safeInteger(value) && safeInteger(c) && safeInteger(end) && 0 <= r && -1 <= value && value < whole.length && whole.length === 256 && 0 <= c && 0 <= end && end <= 1114112 && index.length === 4352 */
  for (let r = 0; r <= runs.length; r += 2) {
    // Runs of joint classes that are one class in this map make one run, [c, end), written once
    // the next run's class differs or no run is left.
    let nextClass = -1
    if (r < runs.length) {
      if (r + 1 >= runs.length) return missing()
      const cls = runs[r + 1]!
      if (cls < 0 || cls >= remap.length) return missing()
      nextClass = remap[cls]!
    }
    if (nextClass !== value) {
      if (value >= 0) {
        /** @invariant safeInteger(r) && safeInteger(value) && safeInteger(nextClass) && safeInteger(c) && safeInteger(end) && 0 <= r && r <= runs.length && 0 <= value && value < whole.length && -1 <= nextClass && nextClass < whole.length && whole.length === 256 && 0 <= c && 0 <= end && end <= 1114112 && index.length === 4352 */
        while (c < end) {
          const block = c >> 8
          if ((c & 0xff) === 0 && end - c >= 0x100) {
            if (whole[value]! < 0) {
              whole[value] = count
              values.fill(value, count << 8, ++count << 8)
            }
            const endBlock = end >> 8
            index.fill(whole[value]!, block, endBlock)
            c = endBlock * 256
          } else {
            // A block that several runs share is its own: the first of them starts it.
            if ((c & 0xff) === 0) index[block] = count++
            const nextBlockStart = (block + 1) * 256
            const stop = end < nextBlockStart ? end : nextBlockStart
            const shift = (index[block]! - block) << 8
            values.fill(value, c + shift, stop + shift)
            c = stop
          }
        }
      }
      value = nextClass
    }
    if (runs.length - r < 2) break
    const runLen = runs[r]!
    if (runLen < 0 || runLen > 0x110000 - 1 - end) { end = -1; break }
    end += runLen + 1
  }
  if (end !== 0x110000) throw new Error('The class runs don\'t cover U+0000..U+10FFFF')
  return { index, values }
}

// The run list and the remaps, kept for the other maps the engine reads.
let classRuns: Int32Array | null = null
let classRemaps: Uint8Array | null = null

export function unpackClasses(map: ClassMap): Effects<{ "@state": "any" }, ClassTable> {   // PAPER: annotation
  const [row, blocks] = classMaps[map]
  const runs = classRuns ??= unpackVarints(classRunsVarints)
  classRemaps ??= unpackTable(classRemapsPacked)
  return unpackClassRuns(runs, classRemaps.subarray(row * jointClassCount), blocks)
}

// A regular expression built at its first use, for the ones most text never reaches. Where V8 or
// SpiderMonkey parses a literal with a \p{...} class of a general category or a script, it builds the
// class's set, in a function that never runs too, so each such literal costs every page as it loads.
// One that every text tests stays a literal (RESEARCH.md, Keeping Work Bounded, JavaScript Engines).
export function lazyRegExp(source: string, flags: string): () => RegExp {
  let built: RegExp | null = null
  return () => built ??= new RegExp(source, flags)
}

// Unicode properties the scans read with RegExp's \p{...}, as two bits per property and code point:
// whether it was tested, and whether the code point has it. A scan tests a property the first time it
// asks about a code point, so a page builds and runs only the tests its engine's scan makes. Code
// points below U+10000 keep their bits in one table, the others in a map.
const letterOrNumberRe = lazyRegExp(String.raw`^[\p{L}\p{N}]$`, 'u')
const markRe = lazyRegExp(String.raw`^\p{M}$`, 'u')
const punctuationRe = lazyRegExp(String.raw`^\p{P}$`, 'u')
const punctuationButDashOrConnectorRe = lazyRegExp(String.raw`^[\p{Ps}\p{Pe}\p{Pi}\p{Pf}\p{Po}]$`, 'u')
const defaultIgnorableRe = lazyRegExp(String.raw`^\p{Default_Ignorable_Code_Point}$`, 'u')
const emojiRe = lazyRegExp(String.raw`^\p{Emoji}$`, 'u')
const hangulRe = lazyRegExp(String.raw`^\p{sc=Hangul}$`, 'u')
export const LETTER_OR_NUMBER = 0
export const MARK = 1
export const PUNCTUATION = 2
export const PUNCTUATION_BUT_DASH_OR_CONNECTOR = 3
export const DEFAULT_IGNORABLE = 4
export const EMOJI = 5
export const HANGUL = 6
let bmpProperties: Uint16Array | null = null
const astralProperties = new Map<number, number>()

function testProperty(property: number, ch: string): Effects<{ "@state": "any" }, boolean> {   // PAPER: annotation
  switch (property) {
    case LETTER_OR_NUMBER: return letterOrNumberRe().test(ch)
    case MARK: return markRe().test(ch)
    case PUNCTUATION: return punctuationRe().test(ch)
    case PUNCTUATION_BUT_DASH_OR_CONNECTOR: return punctuationButDashOrConnectorRe().test(ch)
    case DEFAULT_IGNORABLE: return defaultIgnorableRe().test(ch)
    case EMOJI: return emojiRe().test(ch)
    case HANGUL: return hangulRe().test(ch)
    default: return false
  }
}

export function hasProperty(cp: number, property: number): Effects<{ "@state": "any" }, boolean> {   // PAPER: annotation
  const bmp = bmpProperties ??= new Uint16Array(0x10000)
  const has = 1 << (property * 2)
  let bits = Number.isSafeInteger(cp) && cp >= 0 && cp < bmp.length ? bmp[cp]! : astralProperties.get(cp) ?? 0
  if ((bits & has << 1) === 0) {
    bits |= has << 1 | (testProperty(property, String.fromCodePoint(cp)) ? has : 0)
    if (cp >= 0 && cp < bmp.length) bmp[cp] = bits
    else astralProperties.set(cp, bits)
  }
  return (bits & has) !== 0
}

// The scans read word boundaries only inside runs of Thai, Lao, Khmer and Myanmar
// letters, where no locale changes them. They ask for the segmenter only when such a
// run shows up (Chrome's and Safari's scans also in Tai Le, New Tai Lue, Tai Tham, Tai
// Viet and Ahom runs), so other text prepares without Intl.Segmenter.
let wordSegmenter: Intl.Segmenter | null = null

export function getWordSegmenter(): Effects<{ "@state": "any" }, Intl.Segmenter> {   // PAPER: annotation
  return wordSegmenter ??= new Intl.Segmenter(undefined, { granularity: 'word' })
}

export function clearWordSegmenter(): void {
  wordSegmenter = null
}

// --- ICU's rule-based iterator over compiled line rules ---

export const START_STATE = 1 // rbbi.cpp:48
const STOP_STATE = 0 // rbbi.cpp:51
const ACCEPTING_UNCONDITIONAL = 1 // rbbidata.h:127

// ICU's compiled rules (RBBIDataHeader, rbbidata.h:67-94) as the forward iterator reads them: the
// state table's sizes (RBBIStateTable, rbbidata.h:134-148), its rows of fAccepting, fLookAhead,
// fTagsIdx and fNextState[catCount] (rbbidata.h:98-125), 16 bits each, and the category of every
// code point, which ICU keeps in a UCPTrie.
export type BreakRules = {
  catCount: number
  dictCategoriesStart: number
  rowWidth: number
  rows: Uint16Array
  lookAheadResultsSize: number
  /** @stable */
  readonly classes: ClassTable
}

// A state table ships as its rows' differences from rows it repeats. The rows start as zeros or
// as `base`, another table's rows of the same shape. Then, for each row that differs from how it
// starts: the rows skipped since the last such row, how many rows back the row it copies is, or 0
// for none, how many cells differ after that, and for each the cells skipped since the last one
// and its value.
export function unpackStateRows(width: number, states: number, base: Uint16Array | null, differences: Int32Array): Effects<{}, Uint16Array> {   // PAPER: annotation
  const rows = new Uint16Array(states * width)
  if (base !== null) rows.set(base)
  /** @invariant safeInteger(i) && 0 <= i */
  for (let i = 0, row = -width; i < differences.length;) {
    if (differences.length - i < 3) return missing()
    row += (differences[i]! + 1) * width
    const back = differences[i + 1]! * width
    const count = differences[i + 2]!
    i += 3
    if (back > 0) rows.copyWithin(row, row - back, row - back + width)
    let at = row - 1
    /** @invariant safeInteger(i) && 0 <= i */
    for (let n = count; n > 0; n--) {
      if (differences.length - i < 2) return missing()
      at += 1 + differences[i]!
      rows[at] = differences[i + 1]!
      i += 2
    }
  }
  return rows
}

// A table's rows. The rows of the table they start from are unpacked for it and not kept.
function unpackTableRows(table: RuleTable): Effects<{}, Uint16Array> {   // PAPER: annotation
  const [catCount, , , states, base, differences] = ruleTables[table]
  return unpackStateRows(catCount + 3, states, base === null ? null : unpackTableRows(base), unpackVarints(differences))
}

const breakRules = new Map<RuleTable, BreakRules>()

// A line or character table's rules, unpacked the first time a scan asks for them.
/** @ensures result.classes.index.length === 4352 */
export function getBreakRules(table: RuleTable): Effects<{ "@state": "any" }, BreakRules> {   // PAPER: annotation
  let rules = breakRules.get(table)
  if (rules === undefined || rules.classes.index.length !== 0x1100) {
    const [catCount, dictCategoriesStart, lookAheadResultsSize] = ruleTables[table]
    const classes = unpackClasses(table)
    rules = {
      catCount, dictCategoriesStart, rowWidth: catCount + 3, rows: unpackTableRows(table), lookAheadResultsSize,
      classes,
    }
    breakRules.set(table, rules)
  }
  return rules
}

// Apple's quotation remap for a locale: code points the line rules read as another category
// (apple-rbbi.cpp:1061-1084).
type CategoryOverrides = {
  /** @stable */
  readonly chars: readonly number[]
  /** @stable */
  readonly categories: readonly number[]
}
const NO_OVERRIDES: CategoryOverrides = { chars: [], categories: [] }

// ICU's handleNext() (rbbi.cpp:779-952) from each boundary to the next over the whole text:
// flags[b] = 1 at every boundary 0 < b <= text.length, and at Intl.Segmenter word boundaries
// strictly inside each run of dictionary characters of a segment that ICU would give to a
// dictionary: one with a character in a dictionary category since its start (rbbi.cpp:854,
// rbbi_cache.cpp:486-489). The line rules say $dictionary = [$SA]. The text is read like
// utext_next32() over UTF-16 (utext.cpp:272-308), with unpaired surrogates as code points. ICU
// allocates the look-ahead slots uninitialized (rbbi.cpp:122-129) and never resets them between
// calls, since the rules read a slot only after setting it; here they start at -1 for each text.
/** @requires r.classes.index.length === 4352 */
export function markRuleBoundaries(r: BreakRules, text: string, flags: Uint8Array, overrides: CategoryOverrides = NO_OVERRIDES): Effects<{ "flags[*]": "grow"; "flags[#]": "any"; "@state": "any" }, void> {   // PAPER: annotation
  markRuleBoundariesWith(r, r.classes.index, r.classes.values, text, flags, overrides)
}

/** @requires classIndex.length === 4352 */
function markRuleBoundariesWith(r: BreakRules, classIndex: Uint16Array, classValues: Uint8Array, text: string, flags: Uint8Array, overrides: CategoryOverrides): Effects<{ "flags[*]": "grow"; "flags[#]": "any"; "@state": "any" }, void> {   // PAPER: annotation
  const rows = r.rows
  const width = r.rowWidth
  const dictionaryStart = r.dictCategoriesStart
  const length = text.length
  const matches = new Int32Array(r.lookAheadResultsSize).fill(-1)
  const overrideChars = overrides.chars
  const overrideCategories = overrides.categories
  const overrideCount = overrideChars.length < overrideCategories.length ? overrideChars.length : overrideCategories.length

  /** @invariant safeInteger(start) && 0 <= start && safeInteger(length) && length === text.length && safeInteger(overrideCount) && overrideCount <= overrideChars.length && overrideCount <= overrideCategories.length && classIndex.length === 4352 */
  for (let start = 0; start < length;) { // rbbi.cpp:809-813
    let dictionaryCharCount = 0
    let result = start
    let boundary = -1
    let pos = start
    let c = text.charCodeAt(pos++)
    if (c >= 0xd800 && c <= 0xdbff && pos < length) {
      const trail = text.charCodeAt(pos)
      if (trail >= 0xdc00 && trail <= 0xdfff) { pos++; c = ((c - 0xd800) << 10) + (trail - 0xdc00) + 0x10000 }
    }
    let atEnd = false
    let ended = false
    let row = START_STATE * width
    let category = 0

    /** @invariant safeInteger(start) && 0 <= start && safeInteger(boundary) && -1 <= boundary && safeInteger(result) && 0 <= result && result <= length && safeInteger(pos) && 0 <= pos && pos <= length && safeInteger(c) && 0 <= c && c <= 0x10ffff && safeInteger(length) && length === text.length && safeInteger(overrideCount) && overrideCount <= overrideChars.length && overrideCount <= overrideCategories.length && classIndex.length === 4352 */
    for (;;) {
      if (atEnd) { // rbbi.cpp:832-843
        if (ended) break
        ended = true
        category = 1
      } else { // rbbi.cpp:850-855, with Apple's overrides (apple-rbbi.cpp:1061-1084)
        let overridden = false
        /** @invariant safeInteger(i) && safeInteger(overrideCount) && 0 <= i && overrideCount <= overrideChars.length && overrideCount <= overrideCategories.length && classIndex.length === 4352 */
        for (let i = 0; i < overrideCount; i++) {
          if (c === overrideChars[i]) { category = overrideCategories[i]!; overridden = true; break }
        }
        if (!overridden) {
          category = getClassFrom(classIndex, classValues, c)
          if (category >= dictionaryStart) dictionaryCharCount++
        }
      }
      const state = rows[row + 3 + category] // rbbi.cpp:874-877
      if (state === undefined) throw new RangeError('missing value')
      row = state * width

      const accepting = rows[row] // rbbi.cpp:880-896
      if (accepting === undefined) throw new RangeError('missing value')
      if (accepting === ACCEPTING_UNCONDITIONAL) {
        result = pos
      } else if (accepting > ACCEPTING_UNCONDITIONAL) {
        const match = matches[accepting] ?? missing()
        if (Number.isSafeInteger(match) && match >= 0) {
          boundary = match
          break
        }
      }

      const rule = rows[row + 1] // rbbi.cpp:904-910
      if (rule === undefined) throw new RangeError('missing value')
      if (rule > ACCEPTING_UNCONDITIONAL) matches[rule] = pos

      if (state === STOP_STATE) break // rbbi.cpp:912-917

      if (!ended) { // rbbi.cpp:923-929
        if (pos >= length) {
          atEnd = true
        } else {
          c = text.charCodeAt(pos++)
          if (c >= 0xd800 && c <= 0xdbff && pos < length) {
            const trail = text.charCodeAt(pos)
            if (trail >= 0xdc00 && trail <= 0xdfff) { pos++; c = ((c - 0xd800) << 10) + (trail - 0xdc00) + 0x10000 }
          }
        }
      }
    }

    if (boundary < 0) {
      boundary = result
      if (result === start) { // rbbi.cpp:937-942
        boundary = start + 1
        if ((text.charCodeAt(start) & 0xfc00) === 0xd800 && boundary < length &&
          (text.charCodeAt(boundary) & 0xfc00) === 0xdc00) boundary++
      }
    }
    flags[boundary] = 1
    if (dictionaryCharCount > 0) markDictionaryWords(classIndex, classValues, dictionaryStart, text, start, boundary, flags)
    start = boundary // rbbi.cpp:945
  }
}

// --- Line tables ---

/** @requires classIndex.length === 4352 && safeInteger(start) && 0 <= start */
function markDictionaryWords(classIndex: Uint16Array, classValues: Uint8Array, dictionaryStart: number, text: string, start: number, end: number, flags: Uint8Array): Effects<{ "flags[*]": "grow"; "flags[#]": "any"; "@state": "any" }, void> {   // PAPER: annotation
  let runStart = -1
  /** @invariant safeInteger(i) && 0 <= i && classIndex.length === 4352 */
  for (let i = start; i <= end;) {
    let dictionary = false
    let next = i
    if (i < end && i < text.length) {
      const c = readCodePoint(text, i, text.length)
      if (c > 0xffff && i + 1 < text.length) next = i + 2
      else next = i + 1
      dictionary = getClassFrom(classIndex, classValues, c) >= dictionaryStart
    }
    if (dictionary) {
      if (runStart < 0) runStart = i
    } else if (runStart >= 0) {
      if (i - runStart > 1) {
        for (const segment of getWordSegmenter().segment(text.slice(runStart, i))) {
          if (segment.index > 0) flags[runStart + segment.index] = 1
        }
      }
      runStart = -1
    }
    if (next === i) break
    i = next
  }
}

const SPACE = 0x20
const TAB = 0x09
const LF = 0x0a
const ZWSP = 0x200b
const LINE_SEPARATOR = 0x2028
const PARAGRAPH_SEPARATOR = 0x2029
const IDEOGRAPHIC_SPACE = 0x3000

// --- Blink ---

const PAIR_TABLE_LENGTH = 6244

let blinkPairs: Uint8Array | null = null
let blinkDefaultLocale: string | undefined

/** @ensures result.length === 6244 */
function getBlinkPairs(): Effects<{ "@state": "any" }, Uint8Array> {   // PAPER: annotation
  if (blinkPairs === null || blinkPairs.length !== PAIR_TABLE_LENGTH) {
    blinkPairs = unpackTableWithLength(blinkLinePairsPacked, PAIR_TABLE_LENGTH)
  }
  return blinkPairs
}

// Blink's default language as Intl shows it (getBlinkLineBreaks), read once.
export function getBlinkDefaultLocale(): string {
  return blinkDefaultLocale ??= new Intl.DateTimeFormat().resolvedOptions().locale
}

const NO_BREAK = 0
const CAN_BREAK = 1
const UNKNOWN = 2

// tbi.h:203-205
function isBlinkBreakableSpace(c: number): Effects<{}, boolean> {   // PAPER: annotation
  return c === SPACE || c === TAB || c === LF
}

// Context::ShouldBreakFast, tbi.cc:216-260, with soft hyphens enabled (hyphens: manual).
// The pair table is Chromium's generated kFastLineBreakTable for U+0021..U+00FF
// (gen.cc:422-551).
/** @requires pairs.length === 6244 && safeInteger(last) && safeInteger(ch) */
function shouldBreakFast(pairs: Uint8Array, lastLast: number, last: number, ch: number): Effects<{}, number> {   // PAPER: annotation
  if (last < 0x21 || ch < 0x21) return NO_BREAK
  if (last === 0x2d) {
    if (ch <= 0x7f) {
      if (ch >= 0x30 && ch <= 0x39) {
        const lower = lastLast | 0x20
        return (lastLast >= 0x30 && lastLast <= 0x39) || (lower >= 0x61 && lower <= 0x7a) ? CAN_BREAK : NO_BREAK
      }
    } else {
      return UNKNOWN
    }
  }
  if (last <= 0xff && ch <= 0xff) {
    const x = ch - 0x21
    return (pairs[(last - 0x21) * 28 + (x >> 3)]! & (1 << (x & 7))) !== 0 ? CAN_BREAK : NO_BREAK
  }
  return UNKNOWN
}

// ShouldKeepAfterKeepAll, tbi.cc:157-165, per UTF-16 code unit.
/** @requires classIndex.length === 4352 && safeInteger(lastLast) && 0 <= lastLast && lastLast <= 0xffff && safeInteger(last) && 0 <= last && last <= 0xffff && safeInteger(ch) && 0 <= ch && ch <= 0xffff */
function shouldKeepAfterKeepAll(classIndex: Uint16Array, classValues: Uint8Array, dictionaryStart: number, lastLast: number, last: number, ch: number): Effects<{ "@state": "any" }, boolean> {   // PAPER: annotation
  const pre = hasProperty(last, MARK) ? lastLast : last
  return hasProperty(pre, LETTER_OR_NUMBER) && getClassFrom(classIndex, classValues, pre) < dictionaryStart &&
    hasProperty(ch, LETTER_OR_NUMBER) && getClassFrom(classIndex, classValues, ch) < dictionaryStart
}

// Where a line may start in text Blink collapsed as Pretext does: flags[i] = 1 for
// 0 < i < text.length. NextBreakablePosition (tbi.cc:270-387) for LineBreakType kNormal
// or kKeepAll and BreakSpaceType kAfterSpaceRun, asked at every offset. Each answer
// depends only on the two units before the offset, the unit at it, and whether ICU has
// a boundary there.
// Under line-break: auto, Chrome opens ICU's line iterator with the plain locale
// (line_breaker.cc:57-71 in core/layout/inline; LazyLineBreakIterator::LocaleWithKeyword,
// tbi.h:274-288; tbi_icu.cc:59-94), and ICU's break-iterator data picks the table by locale,
// falling back by truncation (brkiter.cpp:57-144, 433-452): data/brkitr/zh.txt:6 and
// zh_Hant.txt:6 map `line` to line_normal_cj.brk, and root.txt:8, ja.txt:6 and ko.txt:6 to
// line_normal.brk.
// Content without a language opens the table of Blink's default language, the renderer's
// --lang, which is Chrome's UI language (tbi_icu.cc:71-75, text_break_iterator_internal_icu.cc:31-45,
// platform/language.cc:94-99). Chrome also makes it the renderer's ICU default locale, which
// V8's Intl reads (ui/base/l10n/l10n_util.cc:392-398, chrome/app/chrome_main_delegate.cc:1474-1476),
// so preparation gives the scan that language from Intl for a page without one
// (getPreparationLanguage in src/measurement.ts); navigator.language follows the accept
// languages instead. Without a document the scan reads root.
/** @ensures result.length === text.length + 1 */
export function getBlinkLineBreaks(text: string, keepAll: boolean, language: string | null): Effects<{ "@state": "any" }, Uint8Array> {   // PAPER: annotation
  const length = text.length
  const breaks = new Uint8Array(length + 1)
  if (length < 2) return breaks
  const pairs = getBlinkPairs()
  const rules = getBreakRules(getBreakLanguage(language) === 'zh' ? 'chromium/line_normal_cj' : 'chromium/line_normal')
  const classIndex = rules.classes.index
  const classValues = rules.classes.values
  const dictionaryStart = rules.dictCategoriesStart
  let icu: Uint8Array | null = null
  let lastLast = 0
  let last = text.charCodeAt(0)
  /** @invariant safeInteger(i) && safeInteger(lastLast) && 0 <= lastLast && lastLast <= 0xffff && safeInteger(last) && 0 <= last && last <= 0xffff && safeInteger(length) && 1 <= i && length === text.length && pairs.length === 6244 && breaks.length === text.length + 1 && classIndex.length === 4352 */
  for (let i = 1; i < length; lastLast = last, last = text.charCodeAt(i), i++) {
    const ch = text.charCodeAt(i)
    if (isBlinkBreakableSpace(ch)) continue // tbi.cc:284-291
    if (isBlinkBreakableSpace(last)) { breaks[i] = 1; continue }
    const fast = shouldBreakFast(pairs, lastLast, last, ch)
    if (fast === CAN_BREAK) { breaks[i] = 1; continue } // tbi.cc:305-309
    if (keepAll && shouldKeepAfterKeepAll(classIndex, classValues, dictionaryStart, lastLast, last, ch)) continue // tbi.cc:338-344
    if (fast === NO_BREAK) continue // tbi.cc:346-348
    // tbi.cc:350-383: ICU's first boundary after i - 1 is i exactly when i is a boundary,
    // since the unit before it isn't a space here.
    if (icu === null) {
      icu = new Uint8Array(length + 1)
      markRuleBoundariesWith(rules, classIndex, classValues, text, icu, NO_OVERRIDES)
    }
    if (icu[i] === 1) breaks[i] = 1
  }
  return breaks
}

// --- WebKit ---

// BreakClass, BP.h:80-102. PI and PF mark opening and closing quotation marks, always
// together with QU.
const AL = 1
const ID = 2
const CM = 4
const OP = 8
const CP = 16
const CL = 32
const GL = 64
const QU = 128
const SP = 256
const PI = 512
const PF = 1024
const WEIRD = 32768

let webkitPairs: Uint8Array | null = null

/** @ensures result.length === 6244 */
function getWebKitPairs(): Effects<{ "@state": "any" }, Uint8Array> {   // PAPER: annotation
  if (webkitPairs === null || webkitPairs.length !== PAIR_TABLE_LENGTH) {
    webkitPairs = unpackTableWithLength(webkitLinePairsPacked, PAIR_TABLE_LENGTH)
  }
  return webkitPairs
}
type WebKitLineRules = {
  /** @stable */
  readonly rules: BreakRules
  readonly overrides: CategoryOverrides
}
const webkitLineRules = new Map<string, WebKitLineRules>()

// BP.h:125-139 with NoBreakSpaceBehavior::Normal.
function isWebKitBreakableSpace(c: number): Effects<{}, boolean> {   // PAPER: annotation
  return c === SPACE || c === LF || c === TAB || c === LINE_SEPARATOR || c === PARAGRAPH_SEPARATOR
}

function isASCIIDigit(c: number): Effects<{}, boolean> {   // PAPER: annotation
  return c >= 0x30 && c <= 0x39
}

function isASCIIAlpha(c: number): Effects<{}, boolean> {   // PAPER: annotation
  const lower = c | 0x20
  return lower >= 0x61 && lower <= 0x7a
}

// BP.h:330-539. The 0x3000..0x303F switch reads only the low five bits, so it answers for
// 0x3020..0x303F too.
function classify(c: number): Effects<{}, number> {   // PAPER: annotation
  switch (c >> 7) {
    case 0:
      switch (c >> 4) {
        case 0: return WEIRD
        case 1: return CM
        case 2: return c === 0x20 ? SP : c === 0x22 || c === 0x27 ? QU : c === 0x28 ? OP : c === 0x29 ? CP : WEIRD
        case 3: return c <= 0x39 ? AL : WEIRD
        case 4: return AL
        case 5: return c <= 0x5a ? AL : c === 0x5b ? OP : c === 0x5d ? CP : WEIRD
        case 6: return AL
        default: return c <= 0x7a ? AL : c === 0x7b ? OP : c === 0x7d ? CL : WEIRD
      }
    case 1:
      if (c === 0xa0) return GL
      if (c > 0xc0) return AL
      if (c === 0xa1 || c === 0xbf) return OP
      if (c === 0xab) return QU | PI
      if (c === 0xbb) return QU | PF
      return WEIRD
    case 2: case 3: case 4: return AL
    case 5: return c === 0x2c8 || c === 0x2cc || c === 0x2df ? WEIRD : AL
    case 6:
      if (c === 0x34f || (c >= 0x35c && c <= 0x362)) return GL
      if (c < 0x370) return CM
      if (c === 0x37e) return WEIRD
      return AL
    case 7: case 8: case 10: return AL
    case 9: return c >= 0x483 && c <= 0x489 ? CM : AL
    case 11:
      if (c <= 0x588 || c >= 0x5c8) return AL
      if (c >= 0x591 && c <= 0x5bd) return CM
      return c === 0x5bf || c === 0x5c1 || c === 0x5c2 || c === 0x5c4 || c === 0x5c5 || c === 0x5c7 ? CM : WEIRD
    case 64:
      if (c === 0x2018 || c === 0x201c) return QU | PI
      if (c === 0x2019 || c === 0x201d) return QU | PF
      return WEIRD
    default:
      if (c >= 0x2e80 && c <= 0xa4cf) {
        if ((c & 0xff00) === 0x3000) {
          if (c <= 0x303f) {
            switch (c & 0x1f) {
              case 0x01: case 0x02: case 0x09: case 0x0b: case 0x0d: case 0x0f: case 0x11: case 0x15: case 0x17:
              case 0x19: case 0x1b: case 0x1e: case 0x1f:
                return CL
              case 0x08: case 0x0a: case 0x0c: case 0x0e: case 0x10: case 0x16: case 0x14: case 0x18: case 0x1a:
              case 0x1d:
                return OP
              default:
                return WEIRD
            }
          }
          return WEIRD
        }
        if ((c & 0xfff0) === 0x31f0) return WEIRD
        if ((c & 0xfff8) === 0x3248) return AL
        if ((c & 0xffc0) === 0x4dc0) return AL
        if (c === 0xa015) return WEIRD
        return ID
      }
      if (c >= 0xac00 && c <= 0xd7af) return ID
      if (c >= 0xf900 && c <= 0xfaff) return ID
      return WEIRD
  }
}

// CachedLineBreakIteratorFactory (TBI.h:236-351) with two characters of prior context
// (TBI.h:239-290), and ubrk_following over the prior context followed by the text
// (TBIICU.h:99-124, 136-142).
/** @invariant safeInteger(this.priorLength) && 0 <= this.priorLength && this.priorLength <= 2 && safeInteger(this.last) */
type Factory = {
  /** @stable */
  readonly text: string
  readonly secondToLast: number
  /** @stable */
  readonly last: number
  // PriorContext::length counts trailing non-zero characters (TBI.h:277-283).
  /** @stable */
  readonly priorLength: number
  /** @stable */
  readonly line: WebKitLineRules
  nextBoundary: Int32Array | null
}

/** @requires safeInteger(priorLength) && 0 <= priorLength && priorLength <= 2 && safeInteger(last) */
function createFactory(text: string, line: WebKitLineRules, secondToLast: number, last: number, priorLength: number): Effects<{}, Factory> {   // PAPER: annotation
  return { text, secondToLast, last, priorLength, line, nextBoundary: null }
}

// The first ICU boundary after `location`, or -1. `location` is -1 only with a prior
// context; WebKit's unsigned arithmetic then lands on the last prior character
// (TBIICU.h:136-142).
/** @requires classIndex.length === 4352 && safeInteger(location) && -1 <= location
 *  @ensures safeInteger(result) */
function following(f: Factory, location: number, classIndex: Uint16Array, classValues: Uint8Array): Effects<{ "f.nextBoundary": "any"; "@state": "any" }, number> {   // PAPER: annotation
  const priorLength = f.priorLength
  let next = f.nextBoundary
  if (next === null) {
    const prior = priorLength === 2
      ? String.fromCharCode(f.secondToLast, f.last)
      : priorLength === 1 ? String.fromCharCode(f.last) : ''
    const text = prior + f.text
    const flags = new Uint8Array(text.length + 1)
    markRuleBoundariesWith(f.line.rules, classIndex, classValues, text, flags, f.line.overrides)
    const fresh = new Int32Array(text.length + 2)
    const freshLen = fresh.length
    fresh[freshLen - 1] = -1
    /** @invariant safeInteger(p) && safeInteger(freshLen) && -2 <= p && p <= freshLen - 2 && freshLen === fresh.length */
    for (let p = freshLen - 2; p >= 0; p--) fresh[p] = flags[p] === 1 ? p : fresh[p + 1]!
    next = f.nextBoundary = fresh
  }
  if (location >= next.length - priorLength - 1) return -1
  const o = location + priorLength + 1
  const b = next[o]!
  return b < 0 ? -1 : b - priorLength
}

// BP.h:142-255 for LineBreakRules::Normal, WordBreakBehavior::Normal and
// NoBreakSpaceBehavior::Normal. During the fast-forward over units where ICU agrees
// (BP.h:241-249) the characters before are not read again.
/** @requires pairs.length === 6244 && classIndex.length === 4352 && safeInteger(startPosition) && 0 <= startPosition
 *  @ensures safeInteger(result) && 0 <= result */
function nextBreakablePosition(pairs: Uint8Array, f: Factory, classIndex: Uint16Array, classValues: Uint8Array, startPosition: number): Effects<{ "f.nextBoundary": "any"; "@state": "any" }, number> {   // PAPER: annotation
  const s = f.text
  const length = s.length
  if (startPosition === 0 && f.priorLength === 0) {
    if (length <= 1) return length
    startPosition++
  }
  if (startPosition >= length) return length
  let beforeBefore = startPosition > 1 ? s.charCodeAt(startPosition - 2) : f.secondToLast
  let before = startPosition > 0 ? s.charCodeAt(startPosition - 1) : f.last
  let beforeType = 0
  let after = 0
  let afterType = 0
  let nextBreak = -1
  /** @invariant safeInteger(i) && safeInteger(length) && safeInteger(nextBreak) && safeInteger(before) && safeInteger(after) && 0 <= i && length === f.text.length && classIndex.length === 4352 */
  for (let i = startPosition; i < length; beforeBefore = before, before = after, beforeType = afterType, i++) {
    after = s.charCodeAt(i)
    afterType = 0
    if (isWebKitBreakableSpace(after)) return i
    // ASCII rapid lookup.
    if (before === 0x2d && isASCIIDigit(after)) {
      if (isASCIIDigit(beforeBefore) || isASCIIAlpha(beforeBefore)) return i
      continue
    }
    if (before <= 0xff && after <= 0xff) {
      if (before >= 0x21 && after >= 0x21) {
        const x = after - 0x21
        if ((pairs[(before - 0x21) * 28 + (x >> 3)]! & (1 << (x & 7))) !== 0) return i
      }
      continue
    }
    // Non-ASCII rapid lookup.
    if (beforeType === 0) beforeType = classify(before)
    afterType = classify(after)
    const pair = beforeType | afterType
    if ((pair & ~(SP | AL | QU | PI | PF)) === 0) continue
    if ((pair | AL) === (ID | AL)) return i
    if ((pair & (GL | QU)) !== 0 && (pair & WEIRD) === 0) {
      // A quotation mark next to East Asian text breaks before it when it opens and
      // after it when it closes (LB19a).
      if ((pair & ID) !== 0 && (pair & QU) !== 0 && ((afterType & PI) !== 0 || (beforeType & PF) !== 0)) return i
      continue
    }
    if (afterType === CM) {
      afterType = beforeType
      continue
    }
    if ((pair & WEIRD) === 0 && (pair & (CL | CP | OP)) !== 0) {
      if (afterType === CL || afterType === CP || beforeType === OP) continue
      if ((pair & ID) !== 0) return i
    }
    // ICU lookup.
    if (nextBreak < i) nextBreak = following(f, i - 1, classIndex, classValues)
    if (nextBreak >= 0 && i < nextBreak) {
      const max = nextBreak < length - 1 ? nextBreak : length - 1
      /** @invariant safeInteger(i) && safeInteger(length) && safeInteger(nextBreak) && safeInteger(max) && safeInteger(before) && safeInteger(after) && 0 <= i && i < length && max <= length - 1 && length === f.text.length */
      for (; i < max; beforeBefore = before, before = after, beforeType = afterType, i++) {
        const lookahead = s.charCodeAt(i + 1)
        if (lookahead <= 0xff && !isASCIIAlpha(lookahead)) break
      }
    }
    if (i === nextBreak && !isWebKitBreakableSpace(before)) return i
  }
  return length
}

// BP.h:258-274: keep-all breaks at spaces, before ZWSP and after U+3000, and with
// punctuation breaks after any punctuation but the text's last character.
/** @requires safeInteger(startPosition) && 0 <= startPosition
 *  @ensures safeInteger(result) && 0 <= result */
function nextBreakableSpace(s: string, startPosition: number, punctuationBreaks: boolean): Effects<{ "@state": "any" }, number> {   // PAPER: annotation
  /** @invariant safeInteger(i) && 0 <= i */
  for (let i = startPosition; i < s.length; i++) {
    const c = s.charCodeAt(i)
    if (isWebKitBreakableSpace(c) || c === ZWSP) return i
    if (c === IDEOGRAPHIC_SPACE) return i + 1
    if (punctuationBreaks && hasProperty(c, PUNCTUATION_BUT_DASH_OR_CONNECTOR) && i + 1 < s.length) return i + 1
  }
  return s.length
}

// ubrk_open(UBRK_LINE, locale) in libicucore (TBIICU.h:63-67): line_normal.brk for ja and
// ko, line_cj.brk for zh and line.brk otherwise, plus the locale's quotation remap
// (apple-brkiter.cpp:458-473, apple-rbbi.cpp:406-487), looked up with ICU's parent fallback
// under ICU's case: lowercase language, title-case script, uppercase region (uloc_getName).
const appleQuoteRemapTable: ReadonlyMap<string, readonly number[]> = new Map(Object.entries(appleQuoteRemaps))

/** @ensures result.rules.classes.index.length === 4352 */
export function getWebKitLineRules(language: string | null): Effects<{ "@state": "any" }, WebKitLineRules> {   // PAPER: annotation
  const locale = language ?? ''
  let line = webkitLineRules.get(locale)
  if (line !== undefined && line.rules.classes.index.length === 0x1100) return line
  const breakLanguage = getBreakLanguage(locale)
  const rules = getBreakRules(breakLanguage === 'ja' || breakLanguage === 'ko' ? 'apple/line_normal' : breakLanguage === 'zh' ? 'apple/line_cj' : 'apple/line')
  const subtags = locale.split(/[-_]/)
  let name = (subtags[0] ?? '').toLowerCase()
  for (let k = 1; k < subtags.length; k++) {
    const subtag = subtags[k]!
    name += '_' + (subtag.length === 4 ? subtag.charAt(0).toUpperCase() + subtag.slice(1).toLowerCase() : subtag.toUpperCase())
  }
  let remap = appleQuoteRemapTable.get(name)
  while (remap === undefined) {
    const cut = name.lastIndexOf('_')
    name = cut < 0 ? '' : name.slice(0, cut)
    remap = appleQuoteRemapTable.get(name)
  }
  const chars: number[] = []
  const categories: number[] = []
  /** @invariant safeInteger(k) && 0 <= k && chars.length === categories.length && rules.classes.index.length === 4352 */
  for (let k = 0; k < remap.length; k += 2) {
    chars.push(remap[k]!)
    categories.push(getClass(rules.classes, remap[k + 1] === 0 ? 0x7b : 0x7d))
  }
  line = { rules, overrides: { chars, categories } }
  webkitLineRules.set(locale, line)
  return line
}

const TEXT = 0
const WHITESPACE = 1
const SOFT_LINE_BREAK = 2

// Where a line may start in a text node's source: flags[i] = 1 for 0 < i < source.length.
// These are the soft wrap opportunities between the items InlineItemsBuilder::build
// makes (IIB:122-130), as the soft wrap index loop finds them (IFU:456-510): every item
// boundary that isn't next to a forced break. A U+2028 or U+2029 that starts an item
// forces a break after it, marked FORCED_BREAK; one that ICU's fast-forward passed stays
// inside a text item and doesn't.
/** @ensures result.length === source.length + 1 */
export function getWebKitLineBreaks(
  source: string,
  preserveNewlines: boolean,
  keepAll: boolean,
  language: string | null,
): Effects<{ "@state": "any" }, Uint8Array> {   // PAPER: annotation
  const pairs = getWebKitPairs()
  const line = getWebKitLineRules(language)
  const classIndex = line.rules.classes.index
  const classValues = line.rules.classes.values
  const f = createFactory(source, line, 0, 0, 0)
  const length = source.length
  const breaks = new Uint8Array(length + 1)
  // WebKit stores a text holding a code unit above U+00FF in 16 bits, where keep-all also
  // breaks after punctuation.
  let sixteenBit = false
  for (let i = 0; keepAll && i < length && !sixteenBit; i++) sixteenBit = source.charCodeAt(i) > 0xff
  let previousKind = -1
  // handleTextContent, IIB:924-1051, for hyphens manual and nbsp-mode normal.
  /** @invariant safeInteger(position) && 0 <= position && pairs.length === 6244 && classIndex.length === 4352 */
  for (let position = 0; position < length;) {
    let kind = WHITESPACE
    let end = position
    const c = source.charCodeAt(position)
    if (c === LINE_SEPARATOR || c === PARAGRAPH_SEPARATOR || (preserveNewlines && c === LF)) {
      // handleSegmentBreak, IIB:954-962.
      kind = SOFT_LINE_BREAK
      end++
      if (c !== LF) breaks[end] = FORCED_BREAK
    } else {
      // handleWhitespace, IIB:963-992, with moveToNextNonWhitespacePosition (IIB:55-73).
      /** @invariant safeInteger(end) && 0 <= end && pairs.length === 6244 && classIndex.length === 4352 */
      for (; end < length; end++) {
        const c = source.charCodeAt(end)
        if (c !== SPACE && c !== TAB && (preserveNewlines || c !== LF)) break
      }
      if (end === position) {
        // handleNonWhitespace, IIB:1012-1038, with moveToNextBreakablePosition (IIB:75-87),
        // TU:398-422 with line-break auto (LineMode Default, TU:450-466) and BP.h:287-300.
        kind = TEXT
        end = length
        /** @invariant safeInteger(p) && 0 <= p && pairs.length === 6244 && classIndex.length === 4352 */
        for (let p = position; p < length; p++) {
          const next = keepAll ? nextBreakableSpace(source, p, sixteenBit) : nextBreakablePosition(pairs, f, classIndex, classValues, p)
          if (next !== position) { end = next; break }
        }
      }
    }
    // IFU:336-355, 406-418: the scan split same-level items, and wrapping is allowed next
    // to white space.
    if (previousKind >= 0 && previousKind !== SOFT_LINE_BREAK && kind !== SOFT_LINE_BREAK) breaks[position] = 1
    previousKind = kind
    position = end
  }
  return breaks
}

// TU:374-396: whether a line may start where the next inline box starts, from a fresh
// factory on that box with the previous box's last two characters as prior context.
// hyphens: manual, so a trailing soft hyphen doesn't block the break. Keep-all reads no
// prior context (TU:403-407, BP.h:288-300): the box starts at a break only where it
// starts with a breakable space or ZWSP. The soft wrap index loop skips a soft line break
// item (IFU:456-510), a preserved line feed or a line or paragraph separator
// (IIB:954-962), so no break comes before one, and wrapping is allowed next to a
// white-space item (IFU:406-418), which a box's preserved spaces and tabs make
// (IIB:963-992).
export function getWebKitBreakBetweenItems(previous: string, next: string, keepAll: boolean, language: string | null): Effects<{ "@state": "any" }, boolean> {   // PAPER: annotation
  const last = previous.charCodeAt(previous.length - 1)
  const first = next.charCodeAt(0)
  if (first === LF || first === LINE_SEPARATOR || first === PARAGRAPH_SEPARATOR) return false
  if (last === SPACE || last === TAB || first === SPACE || first === TAB) return true
  if (keepAll) return nextBreakableSpace(next, 0, false) === 0
  const pairs = getWebKitPairs()
  const n = previous.length
  const secondToLast = n > 1 ? previous.charCodeAt(n - 2) : 0
  const lastChar = n > 0 ? previous.charCodeAt(n - 1) : 0
  const priorLength = lastChar === 0 ? 0 : secondToLast === 0 ? 1 : 2
  const line = getWebKitLineRules(language)
  const f = createFactory(next, line, secondToLast, lastChar, priorLength)
  return nextBreakablePosition(pairs, f, line.rules.classes.index, line.rules.classes.values, 0) === 0
}
