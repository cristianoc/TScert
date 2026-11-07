// A builder casting arrays of different lengths into the handle: the cast
// in meets the representation, and the return, which states the handle's
// invariant `segmentFlags.length === widths.length`, is refused. The walker
// then reads past the view's end (run under Node: `layout(["a", "b"])`
// returns `undefined`, read at `number` at `i = 1`).

declare const preparedTextBrand: unique symbol;

/**
 * @invariant this.segmentFlags.length === this.widths.length
 * @representation PreparedLineBreakData
 */
export type PreparedText = {
  readonly [preparedTextBrand]: true;
};

type PreparedLineBreakData = { widths: number[]; segmentFlags: Uint8Array };

export function prepare(texts: string[]): PreparedText {
  const widths: number[] = [];
  for (const t of texts) widths.push(t.length);
  return { widths, segmentFlags: new Uint8Array(1) } satisfies PreparedLineBreakData as unknown as PreparedText;
}

function lastFlag(prepared: PreparedText): number {
  const internal = prepared as PreparedText & PreparedLineBreakData;
  let last = 0;
  for (let i = 0; i < internal.widths.length; i++)
    last = internal.segmentFlags[i]!;
  return last;
}

export function layout(texts: string[]): number {
  return lastFlag(prepare(texts));
}
