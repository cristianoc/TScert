// `slice()` copies its receiver (SOURCE-CONTRACTS.md, "Array slice
// copy"): a fresh array of the receiver's length, each present element the
// receiver's own value. So `i < xs.length` gives `i < ys.length`, and a read
// of the copy has the receiver's element type, an object for `rows`.
/** @requires safeInteger(i) && 0 <= i && i < xs.length */
export function at(xs: number[], i: number): number {
  const ys = xs.slice();
  return ys[i]!;
}

type Row = { readonly width: number };
/** @requires safeInteger(i) && 0 <= i && i < rows.length */
export function width(rows: readonly Row[], i: number): number {
  const copy = rows.slice();
  return copy[i]!.width;
}

// A copy of a sparse array has the receiver's length: `map` at a callback
// that may change any spine may leave holes, and its copy keeps them, an
// array of `unknown` at the receiver's length, so `i < ys.length` gives
// `within`'s precondition.
/** @requires safeInteger(i) && 0 <= i && i < zs.length */
function within(zs: readonly unknown[], i: number): number {
  return i;
}
export function mapped(xs: number[], f: (x: number) => number, i: number): number {
  const ys = xs.map((x) => f(x));
  if (!Number.isSafeInteger(i) || i < 0 || i >= ys.length) return 0;
  const zs = ys.slice();
  return within(zs, i);
}
