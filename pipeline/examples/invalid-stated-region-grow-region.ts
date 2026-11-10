// A frame stating a store region beside `stores: "grow"` keeps no fact
// about the region's own store: `open` is the array `runs.open` reads, which
// `step` pops, so `0 < open.length` is lost and `open[0]` is refused (run
// under Node: `first()` returns `undefined`).
type Runs = { /** @stable */ readonly open: number[] };

function step(
  runs: Runs,
  out: number[],
): Modifies<{ values: "any"; stores: "grow"; "runs.open[*]": "any" }, void> {
  runs.open.pop();
  out.push(1);
}

export function first(): number {
  const runs: Runs = { open: [1] };
  const open = runs.open;
  if (open.length === 0) return 0;
  step(runs, []);
  return open[0]!;
}
