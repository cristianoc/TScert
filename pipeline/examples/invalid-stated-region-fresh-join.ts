// Fresh array storage's boundary (FOOTPRINTS.md, "Fresh array storage"): a
// slot joining a fresh array and an old one. `acc` starts `null`, and where
// `take` holds it is assigned the caller's `xs`; the edge from that write
// carries a value not fresh, so the join after it states no freshness of
// `acc`, and `(acc ??= []).pop()` may pop
// `xs` and `drop` is refused at its regional check under a frame naming only
// `runs.open`. Run under Node, `total([1, 2, 3])` reads past the end of the
// array the call empties and returns `NaN`.
type Runs = { /** @stable */ readonly open: number[] };

function drop(runs: Runs, xs: number[], take: boolean): Modifies<{ values: "any"; "runs.open[*]": "any" }, void> {
  let acc: number[] | null = null;
  if (take) acc = xs;
  (acc ??= []).pop();
  runs.open.push(0);
}

export function total(xs: number[]): number {
  const runs: Runs = { open: [] };
  let sum = 0;
  for (let i = 0; i < xs.length; i++) {
    drop(runs, xs, true);
    sum += xs[i]!;
  }
  return sum;
}
