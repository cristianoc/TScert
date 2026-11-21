// Pretext's normalizePreparedLineStart (line-break.ts) over its handle's type
// invariant, facts guarded by a field's null test (`this.lineStartExtras ===
// null || …`), which the function must give back at each return. The loop
// writes the cursor and calls a function of the module before its back edge;
// the front proposes each guarded fact at the loop's head as it proposes a
// fact over a field path (HeadInference.Fact.keptAcross), and the pass checks
// it on every edge.
type LayoutCursor = { segmentIndex: number; graphemeIndex: number }
function missing(): never {
  throw 'missing value'
}

export type PreparedLineBreakData = {
  widths: number[]



  segmentFlags: Uint8Array


  simpleLineWalkFastPath: boolean


  simpleLineCountFastPath: boolean
  breakableFitAdvances: (number[] | null)[]



  breakableLineStartExtras: (number[] | null)[] | null



  lineStartExtras: number[] | null



  lineEndTrims: number[] | null



  overflowLineEndTrims: number[] | null
  letterSpacing: number
  discretionaryHyphenWidth: number


  discretionaryHyphenContexts: number[] | null
  tabStopAdvance: number
  minimumTabAdvance: number
}

/** @invariant this.segmentFlags.length === this.widths.length
 *  @invariant this.breakableFitAdvances.length === this.widths.length
 *  @invariant this.lineStartExtras === null || this.lineStartExtras.length === this.widths.length
 *  @invariant this.lineEndTrims === null || this.lineEndTrims.length === this.widths.length
 *  @invariant this.overflowLineEndTrims === null || this.overflowLineEndTrims.length === this.widths.length
 *  @invariant this.discretionaryHyphenContexts === null || this.discretionaryHyphenContexts.length === this.widths.length */
export type PreparedLineData = PreparedLineBreakData & { items?: ParagraphSegmentData }

export type ParagraphSegmentData = {
  hyphenWidths: number[] | null
  tabStopAdvances: number[] | null
  minimumTabAdvances: number[] | null
  hyphenRooms: number[] | null
  itemEndHalts: number[] | null
  insideExtras: number[] | null
  fillExtras: number[] | null
  openingEdges: number[] | null
  emptyObjectSpaces: number[] | null
  emptyObjectReturns: Uint8Array | null
  hangEnds: Uint8Array | null
}


function consumesAtLineStart(flags: number): Modifies<{}, boolean> {
  const SPACE = 1
  const SOFT_HYPHEN = 3
  const KIND_BITS = 0x0F
  const DROPPED = 0x80
  const kind = flags & KIND_BITS
  return kind === SPACE || kind === SOFT_HYPHEN || (flags & DROPPED) !== 0
}

/** @requires safeInteger(cursor.segmentIndex) && 0 <= cursor.segmentIndex && safeInteger(cursor.graphemeIndex) && 0 <= cursor.graphemeIndex
 *  @ensures result === false || (safeInteger(cursor.segmentIndex) && 0 <= cursor.segmentIndex && cursor.segmentIndex < prepared.widths.length && safeInteger(cursor.graphemeIndex) && 0 <= cursor.graphemeIndex) */
export function normalizePreparedLineStart(
  prepared: PreparedLineData,
  cursor: LayoutCursor,
): Modifies<{ "cursor.*": "scalar" }, boolean> {
  const HARD_BREAK = 8
  const KIND_BITS = 0x0F
  const { segmentFlags } = prepared
  const segmentCount = prepared.widths.length
  let segmentIndex = cursor.segmentIndex
  if (segmentIndex >= segmentCount) return false
  if (cursor.graphemeIndex > 0) return true

  let atChunkStart = segmentIndex === 0 || ((segmentFlags[segmentIndex - 1] ?? missing()) & KIND_BITS) === HARD_BREAK
  /** @invariant safeInteger(segmentIndex) && 0 <= segmentIndex && segmentIndex < prepared.widths.length */
  while (true) {
    const flags = segmentFlags[segmentIndex]
    if (flags === undefined) throw 'missing value'
    if ((flags & KIND_BITS) === HARD_BREAK) {
      if (atChunkStart) {
        cursor.segmentIndex = segmentIndex
        cursor.graphemeIndex = 0
        return true
      }
      if (++segmentIndex >= segmentCount) return false
      cursor.segmentIndex = segmentIndex
      cursor.graphemeIndex = 0
      atChunkStart = true
    } else if (consumesAtLineStart(flags)) {
      if (++segmentIndex >= segmentCount) return false
    } else {
      cursor.segmentIndex = segmentIndex
      cursor.graphemeIndex = 0
      return true
    }
  }
}
