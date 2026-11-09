// Postfix updates inside an index, a binding held in a cell (ARITHMETIC.md,
// "Terms for bindings held in cells"): `xs[at++]!` reads at the old value
// while the cell holds the new one, pretext's `cache[cacheAt++]!` and
// `start = ends[i++]!` shapes.

/** @requires safeInteger(at) && 0 <= at && at + 1 < xs.length */
export function twoFrom(xs: number[], at: number): number {
  const first = xs[at++]!;
  const second = xs[at++]!;
  return first + second;
}

export function sumCache(cache: number[]): number {
  let cacheAt = 0;
  let s = 0;
  while (cacheAt < cache.length) s += cache[cacheAt++]!;
  return s;
}

export function spans(ends: number[]): number {
  let i = 0;
  let width = 0;
  while (i < ends.length) {
    const start = ends[i++]!;
    width += start;
  }
  return width;
}
