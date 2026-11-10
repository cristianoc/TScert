// A call of a function stating a store region keeps the lengths of arrays
// apart from the region wherever it stands (`region-call-keep`,
// `region-call-grow`): as a test's conjunct and as an assignment's right
// side. An element write of an array of arrays leaves every store no
// shorter, as one of an array of numbers does.
type Runs = { /** @stable */ readonly open: number[] };

function step(
  runs: Runs,
  out: number[],
): Modifies<{ values: "any"; stores: "grow"; "runs.open[*]": "any" }, number> {
  runs.open.pop();
  out.push(1);
  return out.length;
}

/** @requires safeInteger(i) && 0 <= i && i < xs.length */
export function tested(xs: number[], i: number, on: boolean): number {
  const runs: Runs = { open: [] };
  if (on && step(runs, xs) > 3) return 0;
  return xs[i]!;
}

/** @requires safeInteger(i) && 0 <= i && i < xs.length */
export function assigned(xs: number[], i: number): number {
  const runs: Runs = { open: [] };
  let n = 0;
  n = step(runs, xs);
  return xs[i]! + n;
}

/** @requires safeInteger(i) && 0 <= i && i < xs.length && safeInteger(j) && 0 <= j */
export function nested(xs: number[], rows: (number[] | null)[], i: number, j: number): number {
  if ((j & 0x7fffffff) !== j || j > rows.length) throw new RangeError("index");
  rows[j] = null;
  return xs[i]!;
}
