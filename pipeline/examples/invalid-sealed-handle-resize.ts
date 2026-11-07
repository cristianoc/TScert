// A function resizing one array of a handle it cast out, then passing the
// handle on: the `push` changes `widths.length`, so the handle's invariant
// the walker's call requires no longer holds, and the call is refused. The
// walker then reads past the view's end (run under Node: `grown` of a handle
// of one segment returns `undefined`, read at `number` at `i = 1`).

declare const preparedTextBrand: unique symbol;

/**
 * @invariant this.segmentFlags.length === this.widths.length
 * @representation PreparedLineBreakData
 */
export type PreparedText = {
  readonly [preparedTextBrand]: true;
};

type PreparedLineBreakData = { widths: number[]; segmentFlags: Uint8Array };

function lastFlag(prepared: PreparedText): number {
  const internal = prepared as PreparedText & PreparedLineBreakData;
  let last = 0;
  for (let i = 0; i < internal.widths.length; i++)
    last = internal.segmentFlags[i]!;
  return last;
}

export function grown(prepared: PreparedText): number {
  (prepared as PreparedLineBreakData).widths.push(0);
  return lastFlag(prepared);
}
