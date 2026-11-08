// A typed array's length from its construction (PROGRAM-TYPING.md,
// "Typed arrays"): `new Uint8Array(n)` at a safe integer `n ≥ 0` states
// `view(result) = n` (its construct signature's postcondition), so a builder
// allocating the view at `widths.length` returns a record whose invariant
// equates the two, with no test of the view's length, and so do the other
// typed arrays the overlay states.

/** @invariant this.segmentFlags.length === this.widths.length && this.ends.length === this.widths.length */
export type PreparedLineBreakData = {
  widths: number[];
  segmentFlags: Uint8Array;
  ends: Int32Array;
};

export function prepare(texts: string[]): PreparedLineBreakData {
  const widths: number[] = [];
  for (const t of texts) widths.push(t.length);
  const segmentFlags = new Uint8Array(widths.length);
  const ends = new Int32Array(widths.length);
  for (let i = 0; i < widths.length; i++) {
    segmentFlags[i] = widths[i]! === 0 ? 1 : 0;
    ends[i] = widths[i]!;
  }
  return { widths, segmentFlags, ends };
}

export function sizes(texts: string[]): number {
  const a = new Uint16Array(texts.length);
  const b = new Float64Array(texts.length);
  let s = 0;
  for (let i = 0; i < a.length; i++) s = s + a[i]! + b[i]!;
  return s;
}

export function countBreaks(prepared: PreparedLineBreakData): number {
  let n = 0;
  for (let i = 0; i < prepared.widths.length; i++) {
    if (prepared.segmentFlags[i]! === 1) n = n + prepared.ends[i]!;
  }
  return n;
}
