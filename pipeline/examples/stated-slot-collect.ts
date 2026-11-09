// A local written inside its statement, held in a slot (SOURCE-ELABORATION.md,
// "Slot or cell"): no closure mentions `acc`, so `acc ??= []` rebinds the
// slot within the expression, and the value `push` receives is the joined
// result of its arms. The slot holds `null` or an array the body allocates
// at every point, a fact of the value itself, so it survives `step`, whose
// frame states `values: "any"`, and the store `push` grows is none of the
// entry heap's, rebased to no region.
type Runs = { /** @stable */ readonly open: number[] };
function step(runs: Runs, s: string): Modifies<{ values: "any"; "runs.open[*]": "any" }, void> {
  runs.open.push(s.length);
}

export function collect(runs: Runs, xs: string[]): Modifies<{ values: "any"; "runs.open[*]": "any" }, string[] | null> {
  let acc: string[] | null = null;
  for (let i = 0; i < xs.length; i++) {
    const s = xs[i]!;
    step(runs, s);
    (acc ??= []).push(s);
  }
  return acc;
}
