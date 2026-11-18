// The walker's module of readonly-frame-walker, with `prepare` keeping the
// widths it exposes in a `Map` its caller passes: `cache.set` is the
// caller's map's method, so the caller may read the array back writable and
// truncate it under the walker (under Node, `prepare(3, m)` then `walk(h, ()
// => { m.get(3).length = 0; })` reads `undefined`, tests/node-runs.mts).
// A library method is read as that native's only of the module's own
// storage: here the call passes the array out writable, and (O) refuses its
// install into the handle.
/** A handle: the widths a walker reads. */
export type H = { readonly widths: readonly number[] };

export function prepare(n: number, cache: Map<number, number[]>): H {
  const widths: number[] = [];
  for (let i = 0; i < n; i++) widths.push(1);
  cache.set(n, widths);
  return { widths };
}

export function walk(h: H, visit: () => void): number {
  const w = h.widths;
  const n = w.length;
  let sum = 0;
  for (let i = 0; i < n; i++) {
    visit();
    sum += w[i] as number;
  }
  return sum;
}
