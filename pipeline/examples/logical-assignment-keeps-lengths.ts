// A logical assignment of a local in a loop keeps the facts of array lengths:
// `t ??= []` and `u ||= []` read the binding and on one path
// assign it, a write of no location, so `to <= xs.length` holds at the loop
// head and each read `xs[mi]` is in bounds (pretext's `trims ??= …`).
/** @requires safeInteger(from) && safeInteger(to) && 0 <= from && from <= to && to <= xs.length */
export function sum(xs: number[], from: number, to: number): number {
  let s = 0;
  let t: number[] | null = null;
  let u: number[] | null = null;
  for (let mi = from; mi < to; mi++) {
    t ??= [];
    u ||= [];
    s += xs[mi]!;
  }
  return s + (t === null ? 0 : t.length) + (u === null ? 0 : u.length);
}
