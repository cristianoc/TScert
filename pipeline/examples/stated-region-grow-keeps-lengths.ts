// A frame stating a store region beside `stores: "grow"` keeps a lower
// bound of the length of a store apart from the region (`region-call-grow`):
// `step` pops the array `runs.open` reads, its region, and pushes onto
// `out`, within grow outside the region. `get` allocates the record, so its
// literal's array is apart from `xs`, and `i < xs.length`, established
// before the call, holds after it.
type Runs = { /** @stable */ readonly open: number[] };

function step(
  runs: Runs,
  out: number[],
): Modifies<{ values: "any"; stores: "grow"; "runs.open[*]": "any" }, void> {
  runs.open.pop();
  out.push(1);
}

/** @requires safeInteger(i) && 0 <= i && i < xs.length */
export function get(xs: number[], i: number): number {
  const runs: Runs = { open: [] };
  step(runs, xs);
  return xs[i]!;
}
