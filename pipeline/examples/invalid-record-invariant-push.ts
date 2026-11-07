// A function that appends to one array of a record it receives, then passes
// the record on: the `push` changes `widths.length`, so the invariant
// `segmentFlags.length === widths.length` the walker's call requires no
// longer holds, and the call is refused. The walker then reads past the
// view's end (run under Node: `appended({ widths: [1], segmentFlags: new
// Uint8Array(1) })` reads `undefined` at `number` at `i = 1`).

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

export function appended(prepared: PreparedLineBreakData): number {
  prepared.widths.push(0);
  return lastFlag(prepared);
}
