// A constructor returning a record whose arrays differ in length: `prepare`
// states the invariant of `PreparedLineBreakData` of its result, which its
// return does not establish, `segmentFlags` one element short, and is refused
// there. A walker reading below `widths.length` then reads past the view's
// end (run under Node: `countBreaks(prepare(["a"]))` reads `undefined` at
// `number` and returns 0 for a segment whose flag `undefined === 1` is not).

/** @invariant this.segmentFlags.length === this.widths.length */
export type PreparedLineBreakData = {
  widths: number[];
  segmentFlags: Uint8Array;
};

export function prepare(texts: string[]): PreparedLineBreakData {
  const widths: number[] = [];
  for (const t of texts) widths.push(t.length);
  return { widths, segmentFlags: new Uint8Array(0) };
}

export function countBreaks(prepared: PreparedLineBreakData): number {
  let n = 0;
  for (let i = 0; i < prepared.widths.length; i++) {
    const flag: number = prepared.segmentFlags[i]!;
    if (flag === 1) n++;
  }
  return n;
}
