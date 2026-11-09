// The step-frame rule's rebasing boundary (FOOTPRINTS.md, "Argument-path
// store regions"): `scan` states the region of the array `runs.open` reads,
// but calls `take` with a record built around `other`, an array its frame
// does not name. The call's region reads a slot no entry path reaches, so
// it is rebased to every location, and `scan`'s regional check refuses it.
// Run under Node, `count([1, 2, 3])` relies on `scan` keeping `xs` and
// returns `NaN`.
type Runs = { /** @stable */ readonly open: number[] };

function take(runs: Runs): Modifies<{ values: "any"; "runs.open[*]": "any" }, void> {
  runs.open.pop();
}

function scan(runs: Runs, other: number[]): Modifies<{ values: "any"; "runs.open[*]": "any" }, void> {
  take({ open: other });
}

export function count(xs: number[]): number {
  const runs: Runs = { open: [] };
  let sum = 0;
  for (let i = 0; i < xs.length; i++) {
    scan(runs, xs);
    sum += xs[i]!;
  }
  return sum;
}
