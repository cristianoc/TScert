// Negative case for nested-path callback demand: `appendToProtected` pushes to
// `prepared.widths`, breaking `prepared.widths.length === prepared.segmentFlags.length`.
// Unsafe under Node: the next iteration reads past `prepared.segmentFlags` (NaN).
export interface PreparedData {
  widths: number[];
  segmentFlags: number[];
}

type Cursor = { i: number };

/** @requires prepared.widths.length === prepared.segmentFlags.length */
function walkRaw(
  prepared: PreparedData,
  onEntry: (width: number, flag: number) => void,
): number {
  const c: Cursor = { i: 0 };
  let total = 0;
  /** @invariant safeInteger(c.i) && 0 <= c.i && prepared.widths.length === prepared.segmentFlags.length */
  while (c.i < prepared.widths.length) {
    const w = prepared.widths[c.i]!;
    const f = prepared.segmentFlags[c.i]!;
    total += f;
    onEntry(w, f);
    c.i++;
  }
  return total;
}

/** @requires prepared.widths.length === prepared.segmentFlags.length */
export function appendToProtected(prepared: PreparedData): number {
  return walkRaw(prepared, (w, _f) => {
    if (prepared.widths.length < 2) prepared.widths.push(w);
  });
}
