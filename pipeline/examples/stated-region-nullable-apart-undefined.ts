// The store separation used by stated-region-nullable-apart with an
// undefined alternative. Copy transport and the join supply its guard.
type Runs = { /** @stable */ readonly open: number[] };

function step(
  runs: Runs | undefined,
  out: number[],
): Modifies<{ values: "any"; stores: "grow"; "runs.open[*]": "any" }, number> {
  if (runs !== undefined) runs.open.pop();
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
  const chosen = use ? runs : undefined;
  let s = 0;
  /**
   * @invariant safeInteger(i) && safeInteger(to) && 0 <= i && to <= xs.length
   * @invariant chosen === undefined || xs !== chosen.open
   */
  for (let i = 0; i < to; i++) {
    step(chosen, out);
    s += xs[i]!;
  }
  return s;
}
