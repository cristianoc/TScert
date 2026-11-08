// A record given type `PreparedLineBreakData` by a cast, not by a return of
// a function stating its invariant: it carries no fact of
// `segmentFlags.length === widths.length`, so the walker's call, which
// requires it, is refused. The arrays differ, and the walker reads past the
// view's end (run under Node: `forged()` reads `undefined` at `number`).

/** @invariant this.segmentFlags.length === this.widths.length */
export type PreparedLineBreakData = {
  widths: number[];
  segmentFlags: Uint8Array;
};

function lastFlag(prepared: PreparedLineBreakData): number {
  let last = 0;
  for (let i = 0; i < prepared.widths.length; i++)
    last = prepared.segmentFlags[i]!;
  return last;
}

export function forged(): number {
  const prepared = {
    widths: [1, 2],
    segmentFlags: new Uint8Array(1),
  } as PreparedLineBreakData;
  return lastFlag(prepared);
}
