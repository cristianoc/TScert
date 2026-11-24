type Cursor = { segmentIndex: number; graphemeIndex: number };
type Handle = { advances: (number[] | null)[] };

/**
 * @requires safeInteger(c.segmentIndex) && 0 <= c.segmentIndex && c.segmentIndex < h.advances.length
 * @requires safeInteger(c.graphemeIndex) && 0 <= c.graphemeIndex
 * @requires c.graphemeIndex === 0 || (h.advances[c.segmentIndex] !== null && c.graphemeIndex <= h.advances[c.segmentIndex].length)
 */
export function readPastLength(h: Handle, c: Cursor): number {
  const fitAdvances = h.advances[c.segmentIndex];
  if (c.graphemeIndex > 0) {
    if (fitAdvances === undefined || fitAdvances === null) return 0;
    const g = c.graphemeIndex + 1;
    // Unsafe when c.graphemeIndex === fitAdvances.length (g > fitAdvances.length):
    // fitAdvances[g - 1] reads undefined, and adding 1 produces NaN.
    return fitAdvances[g - 1]! + 1;
  }
  return 0;
}
