// A representation not meeting the handle's invariant, cast into the
// handle: the cast meets the representation, the cast's result carries no
// fact of `segmentFlags.length === widths.length`, and the walker's call,
// which requires it, is refused. The arrays differ, and the walker reads
// past the view's end (run under Node: `forged()` returns `undefined`, read
// at `number` at `i = 1`).

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

export function forged(): number {
  const data: PreparedLineBreakData = { widths: [1, 2], segmentFlags: new Uint8Array(1) };
  return lastFlag(data as unknown as PreparedText);
}
