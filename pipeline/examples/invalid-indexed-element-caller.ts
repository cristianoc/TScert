type Cursor = { segmentIndex: number; graphemeIndex: number };
type Handle = { advances: (number[] | null)[] };

/**
 * @requires safeInteger(c.segmentIndex) && 0 <= c.segmentIndex && c.segmentIndex < h.advances.length
 * @requires safeInteger(c.graphemeIndex) && 0 <= c.graphemeIndex
 * @requires h.advances[c.segmentIndex] === null || c.graphemeIndex < h.advances[c.segmentIndex].length
 */
function readAt(h: Handle, c: Cursor): number {
  const adv = h.advances[c.segmentIndex];
  if (adv === undefined || adv === null) return 0;
  return adv[c.graphemeIndex]! + 1;
}

export function uncheckedCaller(h: Handle, seg: number, g: number): number {
  if (!(Number.isSafeInteger(seg) && 0 <= seg && seg < h.advances.length))
    return 0;
  if (!(Number.isSafeInteger(g) && 0 <= g)) return 0;
  return readAt(h, { segmentIndex: seg, graphemeIndex: g });
}
