// pretext's shape (measureAnalysis's merged graphemes): an accumulator held
// in a slot, `null` until a long string allocates it, grown by
// `(acc ??= []).push(g)` under a test, beside calls whose frames state
// `values: "any"`. The slot holds `null` or an array the body allocates at
// every point, a fact of the value that no call changes, so each `push`
// grows a store none of the entry heap's, rebased to no region.
type Runs = { /** @stable */ readonly open: number[] };

function note(runs: Runs, n: number): Modifies<{ values: "any"; "runs.open[*]": "any" }, void> {
  runs.open.push(n);
}

export function merged(runs: Runs, xs: string[]): Modifies<{ values: "any"; "runs.open[*]": "any" }, string[] | null> {
  let acc: string[] | null = null;
  for (let i = 0; i < xs.length; i++) {
    const g = xs[i]!;
    note(runs, g.length);
    if (g.length > 1) (acc ??= []).push(g);
    note(runs, i);
  }
  return acc;
}
