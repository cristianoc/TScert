// type-invariant-guarded-loop with a loop that replaces the handle's
// lineStartExtras by an empty array before its back edge: the guarded fact
// fails on that edge, and the function's return does not give back its
// parameter's type invariant; extraAt then reads past the array (NaN under
// Node).
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
): Modifies<{ "cursor.*": "scalar"; "prepared.lineStartExtras": "any" }, boolean> {
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
      prepared.lineStartExtras = []
    } else if (consumesAtLineStart(flags)) {
      if (++segmentIndex >= segmentCount) return false
    } else {
      cursor.segmentIndex = segmentIndex
      cursor.graphemeIndex = 0
      return true
    }
  }
}

export function extraAt(prepared: PreparedLineData, cursor: LayoutCursor): number {
  if (!normalizePreparedLineStart(prepared, cursor)) return 0
  const extras = prepared.lineStartExtras
  return extras === null ? 0 : extras[cursor.segmentIndex]! + 1
}
