// (O) at local storage (docs/drafts/readonly-frames-note/note.tex, "The
// rule"): a store into local storage no invariant's possible support reads
// is not constrained, so `spread` keeps the caller's writable array in a
// local record; a store into a local record an invariant may read is, so
// `boxed`'s record of type `Box`, whose invariant reads `items`, may not
// hold the caller's writable array.
/** @invariant safeInteger(this.count) && this.items.length === this.count */
export type Box = { readonly items: readonly number[]; readonly count: number };

export function size(b: Box): number {
  return b.count;
}

export function spread(xs: number[], visit: () => void): number {
  const keep = { xs };
  visit();
  return keep.xs.length;
}

export function boxed(xs: number[], visit: () => void): number {
  const box: Box = { items: xs, count: xs.length };
  visit();
  return box.count;
}
