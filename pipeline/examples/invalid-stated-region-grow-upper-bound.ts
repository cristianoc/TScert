// A frame stating a spine region beside `spines: "grow"` keeps no upper
// bound of a length outside the region: `step` pushes onto `xs`, so
// `xs.length <= ys.length` is lost and `ys[n - 1]` is refused (run under
// Node: `last([], [])` returns `undefined`).
type Runs = { /** @stable */ readonly open: number[] };

function step(
  runs: Runs,
  out: number[],
): Modifies<{ values: "any"; spines: "grow"; "runs.open[*]": "any" }, void> {
  runs.open.pop();
  out.push(1);
}

export function last(xs: number[], ys: number[]): number {
  const runs: Runs = { open: [] };
  if (xs.length > ys.length) return 0;
  step(runs, xs);
  const n = xs.length;
  if (n === 0) return 0;
  return ys[n - 1]!;
}
