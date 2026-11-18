// Two members of a module, each calling a visitor (Read-only frames,
// Proposition "Read-only reliance"): `walk` reads a handle passed in
// read-only, `first` a cursor it allocates and an array passed in writable.
// The frame at each visitor's call places each region in the module's
// protected region, outside it, or either, by the flow of its sites.
/** A handle: the widths a walker reads. */
export type H = { readonly widths: readonly number[] };

export function prepare(n: number): H {
  const widths: number[] = [];
  for (let i = 0; i < n; i++) widths.push(1);
  return { widths };
}

export function walk(h: H, visit: () => void): number {
  const w = h.widths;
  let sum = 0;
  for (let i = 0; i < w.length; i++) {
    visit();
    sum += w[i] ?? 0;
  }
  return sum;
}

export function first(xs: number[], visit: () => void): number {
  const c = { i: 0 };
  visit();
  return xs[c.i] ?? 0;
}
