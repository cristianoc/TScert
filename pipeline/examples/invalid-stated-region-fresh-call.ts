// Fresh array storage's boundary (FOOTPRINTS.md, "Fresh array storage"): a
// call's result is fresh only where its callee's signature states it,
// `Fresh<T>`, which the callee's own check establishes. `same` returns the
// array it is handed and states no fresh result, so `clear`'s pop of its
// result is refused at its regional check under a frame naming only
// `runs.open` (a control forges `Fresh` onto `same`, refused at `same`).
// Run under Node, `total([1, 2, 3])` reads past the end of the array the
// call empties and returns `NaN`.
type Runs = { /** @stable */ readonly open: number[] };

function same(xs: number[]): number[] {
  return xs;
}

function clear(runs: Runs, xs: number[]): Modifies<{ values: "any"; "runs.open[*]": "any" }, void> {
  same(xs).pop();
  runs.open.push(0);
}

export function total(xs: number[]): number {
  const runs: Runs = { open: [] };
  let sum = 0;
  for (let i = 0; i < xs.length; i++) {
    clear(runs, xs);
    sum += xs[i]!;
  }
  return sum;
}
