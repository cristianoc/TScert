// Fresh array storage's boundary (FOOTPRINTS.md, "Fresh array storage"): a
// fresh record holding an old array. The record `box` is allocated in
// `drain`, but the array its field holds is the caller's `xs`, whose store
// is no fresh location, so `drain`'s pop is refused at its regional check
// under a frame naming only `runs.open`. Run under Node, `total([1, 2, 3])`
// reads past the end of the array the call empties and returns `NaN`.
type Runs = { /** @stable */ readonly open: number[] };
type Box = { items: number[] };

function drain(runs: Runs, xs: number[]): Modifies<{ values: "any"; "runs.open[*]": "any" }, void> {
  const box: Box = { items: xs };
  const items = box.items;
  items.pop();
  runs.open.push(0);
}

export function total(xs: number[]): number {
  const runs: Runs = { open: [] };
  let sum = 0;
  for (let i = 0; i < xs.length; i++) {
    drain(runs, xs);
    sum += xs[i]!;
  }
  return sum;
}
