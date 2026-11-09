// Reads bounded by a quantified precondition over an array's elements
// (ARITHMETIC.md, "Quantified clauses"): `forall i in ends: …` states of
// every index of `ends` below its length that its element is a safe integer
// at most `widths.length`, so an element read at a checked index bounds a
// read and a loop over `widths` (pretext's narrowsLine, rich-inline.ts), the
// clause's terms restated through a destructured path.

/** @requires safeInteger(k) && 0 <= k && k < ends.length
 * @requires forall i in ends: safeInteger(ends[i]) && 0 <= ends[i] && ends[i] < widths.length */
export function widthAt(widths: number[], ends: number[], k: number): number {
  return widths[ends[k]!]!;
}

/**
 * @requires safeInteger(k) && 0 <= k && k < ends.length
 * @requires forall i in ends: safeInteger(ends[i]) && 0 <= ends[i] && ends[i] <= widths.length
 */
export function sumUpTo(widths: number[], ends: number[], k: number): number {
  let total = 0;
  for (let i = 0; i < ends[k]!; i++) total += widths[i]!;
  return total;
}

export type Segments = {
  widths: number[];
  segmentFlags: Uint8Array;
  letterSpacing: number;
};

/**
 * @requires data.widths.length <= data.segmentFlags.length
 * @requires forall i in itemSegments: safeInteger(itemSegments[i]) && 0 <= itemSegments[i] && itemSegments[i] <= data.widths.length
 */
export function narrowsLine(data: Segments, itemSegments: number[]): boolean {
  const { widths, segmentFlags, letterSpacing } = data;
  for (let index = 0; index + 1 < itemSegments.length; index++) {
    let width = 0;
    for (let i = itemSegments[index]!; i < itemSegments[index + 1]!; i++)
      width += widths[i]! + ((segmentFlags[i]! & 4) !== 0 ? letterSpacing : 0);
    if (width < 0) return true;
  }
  return false;
}

/** @requires forall i in starts: 0 <= i && i < starts.length */
export function indicesOnly(starts: number[]): number {
  return starts.length;
}
