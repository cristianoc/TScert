// A body that pops is not within `stores: "grow"`: the store gets shorter
// (run under Node: `get([5], 0)` returns `undefined`).
function drop(xs: number[]): Modifies<{ values: "any"; stores: "grow" }, void> {
  xs.pop();
}

/** @requires safeInteger(i) && 0 <= i && i < xs.length */
export function get(xs: number[], i: number): number {
  drop(xs);
  return xs[i]!;
}
