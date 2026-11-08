// A loop whose body slices an element string and calls a function whose
// parameter type states an invariant: `slice` on `prepared.segments[i]!`
// keeps the heap, so the loop head keeps the invariant's length
// equalities, the call's precondition is met at each iteration, and the
// call, keeping the heap, keeps `i < prepared.segments.length` for the read
// after it (pretext's `buildRangeText`).

/** @invariant this.segments.length === this.widths.length */
export type Prepared = { widths: number[]; segments: string[] };

export function ends(prepared: Prepared, i: number): number {
  return prepared.widths.length + i;
}

export function buildText(prepared: Prepared): string {
  let text = "";
  for (let i = 0; i < prepared.segments.length; i++) {
    const e = ends(prepared, i);
    text += prepared.segments[i]!.slice(e);
  }
  return text;
}
