// The store separation used by stated-region-nullable-apart, expressed
// through a mutable local and a branch. Copying `runs` into `chosen`
// transports its separation; the join guards it by the other edge's null.
// This exercises the same regional-call obligation with statement flow.
type Runs = { /** @stable */ readonly open: number[] };

function step(
  runs: Runs | null,
  out: number[],
): Modifies<{ values: "any"; stores: "grow"; "runs.open[*]": "any" }, number> {
  if (runs !== null) runs.open.pop();
  out.push(1);
  return out.length;
}

/** @requires safeInteger(to) && 0 <= to && to <= xs.length */
export function f(
  xs: number[],
  out: number[],
  to: number,
  use: boolean,
): number {
  const runs: Runs = { open: [] };
  let chosen: Runs | null = null;
  if (use) chosen = runs;
  let s = 0;
  /**
   * @invariant safeInteger(i) && safeInteger(to) && 0 <= i && to <= xs.length
   * @invariant chosen === null || xs !== chosen.open
   */
  for (let i = 0; i < to; i++) {
    step(chosen, out);
    s += xs[i]!;
  }
  return s;
}
