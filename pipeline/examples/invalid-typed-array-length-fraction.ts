// A view allocated at a fraction: ToIndex truncates `1.5` to `1`, so the
// view's element count is not the argument, and the construct signature
// stating `view(result) = n`, which requires a safe integer `n ≥ 0`, is not
// the construction's; its return does not establish the invariant, and is
// refused. A walker then reads past the view's end (run under Node:
// `countBreaks(prepare(["a", "b", "c"]))` reads `undefined` at `number` at
// `i = 1`).

/** @invariant 2 * this.segmentFlags.length === this.widths.length */
export type Halves = {
  widths: number[];
  segmentFlags: Uint8Array;
};

export function prepare(texts: string[]): Halves {
  const widths: number[] = [];
  for (const t of texts) widths.push(t.length);
  const half = widths.length / 2;
  const segmentFlags = new Uint8Array(half);
  return { widths, segmentFlags };
}

export function countBreaks(prepared: Halves): number {
  let n = 0;
  for (let i = 0; 2 * i < prepared.widths.length; i++) n = n + prepared.segmentFlags[i]!;
  return n;
}
