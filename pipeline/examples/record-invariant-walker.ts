// A record invariant as a boundary contract (PROGRAM-TYPING.md, "Record
// invariants"), in the shape of pretext's `line-break.ts`:
// `PreparedLineBreakData` holds per-segment data in parallel, `widths` and
// the typed array `segmentFlags`, and its walkers (`countPreparedLines`,
// `walkPreparedLinesRaw`, `stepPreparedLineGeometryFromStart`) read
// `prepared.segmentFlags[i]!` below `prepared.widths.length`. The invariant
// `segmentFlags.length === widths.length` is each walker's precondition, its
// body assumes it and each call establishes it, and a fact of the result of
// `prepare`, which its return establishes from the arrays it builds, a view
// allocated at `widths.length`, whose construction states that element count.

/** @invariant this.segmentFlags.length === this.widths.length */
export type PreparedLineBreakData = {
  widths: number[];
  segmentFlags: Uint8Array;
};

export function prepare(texts: string[]): PreparedLineBreakData {
  const widths: number[] = [];
  for (const t of texts) widths.push(t.length);
  const segmentFlags = new Uint8Array(widths.length);
  for (let i = 0; i < widths.length; i++)
    segmentFlags[i] = widths[i]! === 0 ? 1 : 0;
  return { widths, segmentFlags };
}

/** @requires safeInteger(i) && 0 <= i */
function isBreak(prepared: PreparedLineBreakData, i: number): boolean {
  return i < prepared.widths.length && prepared.segmentFlags[i]! === 1;
}

export function countBreaks(prepared: PreparedLineBreakData): number {
  let n = 0;
  for (let i = 0; i < prepared.widths.length; i++) {
    if (prepared.segmentFlags[i]! === 1) n++;
  }
  return n;
}

export function layout(texts: string[]): number {
  const prepared = prepare(texts);
  return countBreaks(prepared) + (isBreak(prepared, 0) ? 1 : 0);
}
