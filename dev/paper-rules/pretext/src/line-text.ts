import { findGraphemeEnds } from './graphemes.js'
import { HARD_BREAK, KIND_BITS, SOFT_HYPHEN, ZERO_WIDTH_BREAK, ZERO_WIDTH_GLUE } from './analysis.js'
import { isDiscretionaryLineEnd, type PreparedLineData } from './line-break.js'
import { getEngineProfile } from './measurement.js'

// A handle with each segment's text, which line text is built from: prepareWithSegments()'s, or
// a rich-inline paragraph's.
export type PreparedSegments = PreparedLineData & { readonly segments: readonly string[] }

// Per handle, the grapheme ends of each segment a line has started or ended inside.
const graphemeEndCaches = new WeakMap<PreparedSegments, Map<number, Int32Array>>()

function makeGraphemeEnds(segment: string): Effects<{ "@state": "any" }, Int32Array> {   // PAPER: annotation
  const ends = new Int32Array(segment.length)
  findGraphemeEnds(getEngineProfile().graphemeTable, segment, 0, segment.length, ends)
  return ends
}

// The offsets in a segment's text where its graphemes end, in order, then zeros.
export function getGraphemeEnds(prepared: PreparedSegments, segmentIndex: number): Effects<{ "@state": "any" }, Int32Array> {   // PAPER: annotation
  let cache = graphemeEndCaches.get(prepared)
  if (cache === undefined) {
    cache = new Map<number, Int32Array>()
    graphemeEndCaches.set(prepared, cache)
  }
  const cached = cache.get(segmentIndex)
  if (cached !== undefined) return cached
  const segment = prepared.segments[segmentIndex]
  if (segment === undefined) throw new RangeError('missing value')
  const ends = makeGraphemeEnds(segment)
  cache.set(segmentIndex, ends)
  return ends
}

// Where grapheme `graphemeIndex` of a segment starts in its text: its end past its last grapheme,
// where a range kept from a longer text stops.
export function getGraphemeStart(prepared: PreparedSegments, segmentIndex: number, graphemeIndex: number): Effects<{ "@state": "any" }, number> {   // PAPER: annotation
  if (graphemeIndex <= 0) return 0
  const ends = getGraphemeEnds(prepared, segmentIndex)
  // bounds bug: upstream reads ends[graphemeIndex - 1]!, which is undefined, returned as a
  // number, where a range kept from a longer text starts past the segment's last grapheme.
  const end = ends[graphemeIndex - 1] ?? 0
  return end === 0 ? ends.length : end
}

// The text of a range of `prepared`'s segments, with no hyphen: that of a rich-inline fragment its
// line goes on after.
export function buildRangeText(
  prepared: PreparedSegments,
  startSegmentIndex: number,
  startGraphemeIndex: number,
  endSegmentIndex: number,
  endGraphemeIndex: number,
): Effects<{ "@state": "any" }, string> {   // PAPER: annotation
  const { segmentFlags } = prepared
  // A range kept from a longer text, such as one prepared again since, can end
  // past this one, up to segment Infinity: its text stops at this text's end.
  const segmentCount = prepared.segments.length < segmentFlags.length ? prepared.segments.length : segmentFlags.length
  let text = ''
  if (Number.isSafeInteger(startSegmentIndex) && 0 <= startSegmentIndex) {
    /** @invariant safeInteger(i) && safeInteger(segmentCount) && 0 <= i && segmentCount <= prepared.segments.length && segmentCount <= segmentFlags.length */
    for (let i = startSegmentIndex; i < segmentCount && !(i >= endSegmentIndex); i++) {
      // A soft hyphen shows only as the hyphen of a line that ends at it, and one the
      // Gecko scan takes as a zero-width break never does.
      const kind = segmentFlags[i]! & KIND_BITS
      if (
        kind === SOFT_HYPHEN || kind === HARD_BREAK ||
        ((kind === ZERO_WIDTH_GLUE || kind === ZERO_WIDTH_BREAK) && prepared.segments[i]!.charCodeAt(0) === 0x00AD)
      ) continue
      if (i === startSegmentIndex && startGraphemeIndex > 0) {
        text += prepared.segments[i]!.slice(getGraphemeStart(prepared, i, startGraphemeIndex))
      } else {
        text += prepared.segments[i]!
      }
    }
  }

  if (endGraphemeIndex > 0 && Number.isSafeInteger(endSegmentIndex) && 0 <= endSegmentIndex && endSegmentIndex < segmentCount) {
    text += prepared.segments[endSegmentIndex]!.slice(
      getGraphemeStart(prepared, endSegmentIndex, startSegmentIndex === endSegmentIndex ? startGraphemeIndex : 0),
      getGraphemeStart(prepared, endSegmentIndex, endGraphemeIndex),
    )
  }

  return text
}

// A line's text: its range's, with a hyphen where it ends at a soft hyphen, whose width counted it.
export function buildLineTextFromRange(
  prepared: PreparedSegments,
  startSegmentIndex: number,
  startGraphemeIndex: number,
  endSegmentIndex: number,
  endGraphemeIndex: number,
): Effects<{ "@state": "any" }, string> {   // PAPER: annotation
  const text = buildRangeText(prepared, startSegmentIndex, startGraphemeIndex, endSegmentIndex, endGraphemeIndex)
  return isDiscretionaryLineEnd(prepared.segmentFlags, prepared.widths.length, endSegmentIndex, endGraphemeIndex) ? text + '-' : text
}
