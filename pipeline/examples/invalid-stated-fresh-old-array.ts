// A fresh record holding an old array (FOOTPRINTS.md, "Fresh array
// storage"): `drain` allocates `runs`, but its field holds the caller's
// `xs`, so the region `step` states on it is a store of the entry heap and
// `drain`'s `stores: "grow"` is refused at the call. Run under Node,
// `total([1, 2, 3])` relies on that statement to keep `i < xs.length`,
// reads past the end of the array the calls empty and returns `NaN`.
type Runs = { /** @stable */ readonly open: number[] };

function step(runs: Runs): Modifies<{ values: "any"; stores: "grow"; "runs.open[*]": "any" }, void> {
  runs.open.pop();
}

function drain(xs: number[]): Modifies<{ values: "any"; stores: "grow" }, void> {
  const runs: Runs = { open: xs };
  step(runs);
}

export function total(xs: number[]): number {
  let sum = 0;
  for (let i = 0; i < xs.length; i++) {
    drain(xs);
    sum += xs[i]!;
  }
  return sum;
}
