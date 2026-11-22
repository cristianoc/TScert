// Negative case for adapting-closure demand forwarding: `appendAdapted` pushes
// to `prepared.widths`, violating `walkLines`'s forwarded demand.
// Unsafe under Node: the next iteration reads past `prepared.segmentFlags` (NaN).
export interface PreparedData {
  widths: number[];
  segmentFlags: number[];
}

export interface Line {
  width: number;
  flag: number;
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
function walkLines(
  prepared: PreparedData,
  visit: (line: Line) => void,
): number {
  return walkRaw(prepared, (w, f) => {
    visit({ width: w, flag: f });
  });
}

/** @requires prepared.widths.length === prepared.segmentFlags.length */
export function appendAdapted(prepared: PreparedData): number {
  return walkLines(prepared, (line) => {
    if (prepared.widths.length < 2) prepared.widths.push(line.width);
  });
}
