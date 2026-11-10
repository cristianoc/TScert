// A join with an old store (FOOTPRINTS.md, "Fresh array storage"): `runs`
// holds a fresh array on one branch and the caller's `xs` on the other, so
// after the join its field has no fresh fact and `drain`'s
// `stores: "grow"` is refused at the call. Run under Node,
// `total([1, 2, 3])` reads past the end of the array the calls empty and
// returns `NaN`.
type Runs = { /** @stable */ readonly open: number[] };

function step(runs: Runs): Modifies<{ values: "any"; stores: "grow"; "runs.open[*]": "any" }, void> {
  runs.open.pop();
}

function drain(xs: number[], c: boolean): Modifies<{ values: "any"; stores: "grow" }, void> {
  const runs: Runs = c ? { open: [] } : { open: xs };
  step(runs);
}

export function total(xs: number[]): number {
  let sum = 0;
  for (let i = 0; i < xs.length; i++) {
    drain(xs, false);
    sum += xs[i]!;
  }
  return sum;
}
