// A builder allocating its view one element short of `widths`: the view's
// element count is `widths.length - 1`, so its return does not establish the
// invariant, and is refused. A walker then reads past the view's end (run
// under Node: `countBreaks(prepare(["a", "b"]))` reads `undefined` at
// `number` at `i = 1`).

/** @invariant this.segmentFlags.length === this.widths.length */
export type PreparedLineBreakData = {
  widths: number[];
  segmentFlags: Uint8Array;
};

export function prepare(texts: string[]): PreparedLineBreakData {
  const widths: number[] = [];
  for (const t of texts) widths.push(t.length);
  const segmentFlags = new Uint8Array(widths.length - 1);
  return { widths, segmentFlags };
}

export function countBreaks(prepared: PreparedLineBreakData): number {
  let n = 0;
  for (let i = 0; i < prepared.widths.length; i++) n = n + prepared.segmentFlags[i]!;
  return n;
}
