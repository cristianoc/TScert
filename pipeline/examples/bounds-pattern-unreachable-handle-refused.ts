// A handle's invariant across a callback that is never given the handle. The
// walker builds the handle itself from two arrays of equal length and hands
// the visitor only a number, so the visitor cannot change it, and `last` reads
// within `starts`. Safe.
// Gap: the visitor's stated effect, `{ values: "any"; spines: "grow" }`,
// covers the handle's fields and lets `widths` grow, so the invariant
// `starts.length === widths.length` is not kept for the call `last(h)` after
// the visit; no rule bounds a callback's effect by the locations it can reach.
// Pretext: line-break.ts walkPreparedLinesRaw, which passes its prepared
// handle to stepPreparedSimpleLineGeometry after onLine.
/** @invariant this.starts.length === this.widths.length */
type Handle = { widths: number[]; starts: number[] };
type Visitor = (w: number) => Modifies<{ values: "any"; spines: "grow" }, void>;

function last(h: Handle): number {
  if (h.widths.length === 0) return 0;
  return h.starts[h.widths.length - 1]!;
}

export function walk(visit: Visitor): number {
  const h: Handle = { widths: [3, 4], starts: [0, 3] };
  visit(h.widths.length);
  return last(h);
}
