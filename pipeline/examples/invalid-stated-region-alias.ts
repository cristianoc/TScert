// The step-frame rule's alias boundary (FOOTPRINTS.md, "Argument-path
// store regions"): `scan` clears the array `runs.open` reads by calling
// `clear`, whose frame rebases to `scan`'s region. `aliased` builds the
// record around `flags` itself, so the region is `flags`'s store: no
// separation keeps `i < flags.length` across `scan`, and the read after it
// is refused. Run under Node, `aliased([1, 2, 3])` returns `NaN`.
type Runs = { /** @stable */ readonly open: number[] };

function clear(runs: Runs): Modifies<{ values: "any"; "runs.open[*]": "any" }, void> {
  runs.open.splice(0);
}

function scan(runs: Runs): Modifies<{ values: "any"; "runs.open[*]": "any" }, void> {
  clear(runs);
}

export function aliased(flags: number[]): number {
  const runs: Runs = { open: flags };
  let sum = 0;
  for (let i = 0; i < flags.length; i++) {
    scan(runs);
    sum += flags[i]!;
  }
  return sum;
}
