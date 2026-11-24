type Cursor = { segmentIndex: number; graphemeIndex: number };
type Handle = { advances: (number[] | null)[] };
type Grid = { rows: number[][] };

/**
 * @requires safeInteger(c.segmentIndex) && 0 <= c.segmentIndex && c.segmentIndex < h.advances.length
 * @requires safeInteger(c.graphemeIndex) && 0 <= c.graphemeIndex
 * @requires h.advances[c.segmentIndex] === null || c.graphemeIndex < h.advances[c.segmentIndex].length
 */
export function guardedRead(h: Handle, c: Cursor): number {
  const adv = h.advances[c.segmentIndex];
  if (adv === undefined || adv === null) return 0;
  return adv[c.graphemeIndex]!;
}

/**
 * @requires safeInteger(c.segmentIndex) && 0 <= c.segmentIndex && c.segmentIndex < h.advances.length
 * @requires safeInteger(c.graphemeIndex) && 0 <= c.graphemeIndex
 * @requires c.graphemeIndex === 0 || (h.advances[c.segmentIndex] !== null && c.graphemeIndex < h.advances[c.segmentIndex].length)
 */
export function disjunctiveStep(h: Handle, c: Cursor): number {
  const adv = h.advances[c.segmentIndex];
  if (c.graphemeIndex > 0) {
    if (adv === undefined || adv === null) throw new RangeError("missing");
    const g = c.graphemeIndex + 1;
    return adv[g - 1]!;
  }
  return 0;
}

/**
 * @requires safeInteger(i) && safeInteger(j) && 0 <= i && i < g.rows.length && 0 <= j && j < g.rows[i].length
 */
export function gridRead(g: Grid, i: number, j: number): number {
  const row = g.rows[i];
  if (row === undefined) throw new RangeError("missing");
  return row[j]!;
}

export function checkedCaller(h: Handle, seg: number, g: number): number {
  if (!(Number.isSafeInteger(seg) && 0 <= seg && seg < h.advances.length))
    return 0;
  if (!(Number.isSafeInteger(g) && 0 <= g)) return 0;
  const c: Cursor = { segmentIndex: seg, graphemeIndex: g };
  if (g > 0) {
    const adv = h.advances[seg];
    if (adv === undefined || adv === null || g >= adv.length) return 0;
  }
  return disjunctiveStep(h, c);
}

/**
 * @requires safeInteger(c.segmentIndex) && 0 <= c.segmentIndex && c.segmentIndex < h.advances.length
 * @ensures safeInteger(c.segmentIndex) && 0 <= c.segmentIndex && c.segmentIndex < h.advances.length
 * @ensures safeInteger(c.graphemeIndex) && 0 <= c.graphemeIndex
 * @ensures c.graphemeIndex === 0 || (h.advances[c.segmentIndex] !== null && c.graphemeIndex < h.advances[c.segmentIndex].length)
 */
export function advanceOne(
  h: Handle,
  c: Cursor,
): Modifies<{ "c.graphemeIndex": "scalar" }, void> {
  const advances = h.advances;
  const seg = c.segmentIndex;
  const adv = advances[seg];
  if (adv !== undefined && adv !== null && 1 < adv.length) {
    c.graphemeIndex = 1;
  } else {
    c.graphemeIndex = 0;
  }
}

/**
 * @requires safeInteger(c.segmentIndex) && 0 <= c.segmentIndex && c.segmentIndex < h.advances.length
 */
export function advanceThenRead(h: Handle, c: Cursor): number {
  advanceOne(h, c);
  return disjunctiveStep(h, c);
}

/**
 * @requires safeInteger(c.segmentIndex) && 0 <= c.segmentIndex && c.segmentIndex < h.advances.length
 * @requires safeInteger(c.graphemeIndex) && 0 <= c.graphemeIndex
 * @requires c.graphemeIndex === 0 || (h.advances[c.segmentIndex] !== null && c.graphemeIndex < h.advances[c.segmentIndex].length)
 */
export function resetCursor(
  h: Handle,
  c: Cursor,
): Modifies<{ "c.graphemeIndex": "scalar" }, number> {
  const r = disjunctiveStep(h, c);
  c.graphemeIndex = 0;
  return r;
}

export function copiedCursorCaller(h: Handle, start: Cursor): number {
  if (start.segmentIndex === 0 && start.graphemeIndex === 0) return 0;
  const c: Cursor = {
    segmentIndex: start.segmentIndex,
    graphemeIndex: start.graphemeIndex,
  };
  const seg = c.segmentIndex;
  if (!(Number.isSafeInteger(seg) && 0 <= seg && seg < h.advances.length))
    return 0;
  const g = c.graphemeIndex;
  if (!(Number.isSafeInteger(g) && 0 <= g)) return 0;
  const advances = h.advances;
  if (g > 0) {
    const adv = advances[seg];
    if (adv === undefined || adv === null || g >= adv.length) return 0;
  }
  return resetCursor(h, c);
}
