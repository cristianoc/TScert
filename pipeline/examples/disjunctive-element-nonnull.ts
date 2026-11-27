type Cursor = { segmentIndex: number; graphemeIndex: number };
type Handle = {
  widths: number[];
  advances: (number[] | null)[];
};

/**
 * @requires safeInteger(c.segmentIndex) && 0 <= c.segmentIndex && c.segmentIndex < h.advances.length
 * @requires safeInteger(c.graphemeIndex) && 0 <= c.graphemeIndex
 * @requires c.graphemeIndex === 0 || (h.advances[c.segmentIndex] !== null && c.graphemeIndex < h.advances[c.segmentIndex].length)
 */
export function disjunctiveRead(
  h: Handle,
  c: Cursor,
  overflow: boolean,
): number {
  const startAdvances: number[] | null | undefined = h.advances[c.segmentIndex];
  if (c.graphemeIndex > 0 || (overflow && startAdvances !== null)) {
    const fit = startAdvances!;
    return fit.length;
  }
  return 0;
}

/**
 * @requires h.advances.length === h.widths.length
 * @requires safeInteger(c.segmentIndex) && 0 <= c.segmentIndex && c.segmentIndex < h.widths.length
 * @requires safeInteger(c.graphemeIndex) && 0 <= c.graphemeIndex
 * @requires c.graphemeIndex === 0 || (h.advances[c.segmentIndex] !== null && c.graphemeIndex < h.advances[c.segmentIndex].length)
 * @requires safeInteger(i) && 0 <= i && i < h.widths.length
 */
export function mergedAtIndexNonNull(
  h: Handle,
  c: Cursor,
  i: number,
  overflow: boolean,
): number {
  const advances = h.advances;
  let start = 0;
  if (i === c.segmentIndex && c.graphemeIndex > 0) {
    start = c.graphemeIndex;
  } else if (overflow && advances[i] !== null) {
    start = 0;
  } else {
    return 0;
  }
  const fit = advances[i]!;
  return start + fit.length;
}

/**
 * @requires h.advances.length === h.widths.length
 * @requires safeInteger(endSeg) && 0 <= endSeg && endSeg <= h.widths.length
 * @requires safeInteger(endGraph) && 0 <= endGraph
 * @requires endGraph === 0 || endSeg < h.widths.length
 */
function readIfInside(h: Handle, endSeg: number, endGraph: number): number {
  if (endGraph > 0) return h.widths[endSeg]!;
  return 0;
}

/**
 * @requires h.advances.length === h.widths.length
 * @requires safeInteger(endSeg) && 0 <= endSeg && endSeg <= h.widths.length
 * @requires safeInteger(endGraph) && 0 <= endGraph
 * @requires endGraph === 0 || (h.advances[endSeg] !== null && endGraph < h.advances[endSeg].length)
 */
export function atIndexImpliesBounds(
  h: Handle,
  endSeg: number,
  endGraph: number,
): number {
  return readIfInside(h, endSeg, endGraph);
}
