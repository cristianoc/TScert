// The regional certificate's boundary (FOOTPRINTS.md, "Fresh array
// storage"): `drain` receives its record, so the array its `@stable` field
// holds may be the caller's, and the region `step` states on it is no
// store `drain` allocated. `drain`'s statement, `stores: "grow"`, is
// refused at the call. Run under Node, `total([1, 2, 3])` relies on that
// statement to keep `i < xs.length` across `drain(runs)`, reads past the end
// of the array the calls empty and returns `NaN`.
type Runs = { /** @stable */ readonly open: number[] };

function step(runs: Runs): Modifies<{ values: "any"; stores: "grow"; "runs.open[*]": "any" }, void> {
  runs.open.pop();
}

function drain(runs: Runs): Modifies<{ values: "any"; stores: "grow" }, void> {
  step(runs);
}

export function total(xs: number[]): number {
  const runs: Runs = { open: xs };
  let sum = 0;
  for (let i = 0; i < xs.length; i++) {
    drain(runs);
    sum += xs[i]!;
  }
  return sum;
}
