// A call stated `spines: "grow"` keeps a lower bound of a length: `add`
// leaves every spine no shorter, so `i < xs.length`, established before the
// call, holds after it and the read `xs[i]` is in bounds.
function add(xs: number[]): Modifies<{ values: "any"; spines: "grow" }, void> {
  xs.push(1);
}

/** @requires safeInteger(i) && 0 <= i && i < xs.length */
export function get(xs: number[], i: number): number {
  add(xs);
  return xs[i]!;
}
