// The walker's module of readonly-frame-walker, with `prepare` keeping the
// widths it exposes in a module-private `WeakMap` keyed by the handle, as
// pretext's `findSegmentSources` does. `cache.set` is the standard
// library's, of the module's own storage: it passes nothing out, and the
// module's certificate holds.
/** A handle: the widths a walker reads. */
export type H = { readonly widths: readonly number[] };

const cache = new WeakMap<H, number[]>();

export function prepare(n: number): H {
  const widths: number[] = [];
  for (let i = 0; i < n; i++) widths.push(1);
  const h: H = { widths };
  cache.set(h, widths);
  return h;
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
