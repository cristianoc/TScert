// The walker's module of readonly-frame-walker, with a member that gives
// the handle's widths out writable: `prepare` keeps the array it exposes in
// a module binding, and `lastWidths` returns it at `number[]`, so a visitor
// may truncate the array `walk` reads (under Node, `walk(h, () => {
// lastWidths().length = 0; })` reads `undefined`, tests/node-runs.mts). The
// array's site is released, and (O) refuses its install into the handle.
/** A handle: the widths a walker reads. */
export type H = { readonly widths: readonly number[] };

let last: number[] = [];

export function prepare(n: number): H {
  const widths: number[] = [];
  for (let i = 0; i < n; i++) widths.push(1);
  last = widths;
  return { widths };
}

export function lastWidths(): number[] {
  return last;
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
