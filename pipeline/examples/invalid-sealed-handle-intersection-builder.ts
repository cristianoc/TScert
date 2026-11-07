// A handle whose representation is an intersection, its invariant over a
// field of each part: a builder casting a view one element short of `widths`
// into the handle meets the representation, and its return, stating the
// invariant, is refused. The walker then reads past the view's end (run
// under Node: `layout(["a", "b"])` returns `undefined`, read at `number` at
// `i = 1`).

declare const preparedTextBrand: unique symbol;

/**
 * @invariant this.segmentFlags.length === this.widths.length
 * @representation PreparedLineData
 */
export type PreparedText = {
  readonly [preparedTextBrand]: true;
};

type Widths = { widths: number[] };

type PreparedLineData = Widths & { segmentFlags: Uint8Array; items?: string[] };

export function prepare(texts: string[]): PreparedText {
  const widths: number[] = [];
  for (const t of texts) widths.push(t.length);
  return {
    widths,
    segmentFlags: new Uint8Array(1),
  } satisfies PreparedLineData as unknown as PreparedText;
}

function lastFlag(prepared: PreparedText): number {
  const internal = prepared as PreparedText & PreparedLineData;
  let last = 0;
  for (let i = 0; i < internal.widths.length; i++)
    last = internal.segmentFlags[i]!;
  return last;
}

export function layout(texts: string[]): number {
  return lastFlag(prepare(texts));
}
