// A handle forged by a cast from an object that is no representation: the
// cast into the handle, the obligation that its operand is a
// `PreparedLineBreakData`, is refused. The walker then reads a field the
// object lacks (run under Node: `forged()` throws a TypeError reading
// `length` of `undefined`).

declare const preparedTextBrand: unique symbol;

/**
 * @invariant this.segmentFlags.length === this.widths.length
 * @representation PreparedLineBreakData
 */
export type PreparedText = {
  readonly [preparedTextBrand]: true;
};

type PreparedLineBreakData = { widths: number[]; segmentFlags: Uint8Array };

function lastWidth(prepared: PreparedText): number {
  const internal = prepared as PreparedText & PreparedLineBreakData;
  return internal.widths.length;
}

export function forged(): number {
  const prepared = { lines: [1, 2] } as unknown as PreparedText;
  return lastWidth(prepared);
}
