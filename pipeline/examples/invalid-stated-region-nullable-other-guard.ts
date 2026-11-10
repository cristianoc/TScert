// The valid fact `kept === null || xs !== passed.open` has a separation
// body naming the region actual `passed`, but its guard names `kept`.
// Here `kept` is null and `passed.open` aliases `xs`: the call pops `xs`.
// The guard cannot justify keeping `to <= xs.length` across that call.
// Under Node, console.log(f([1, 2], [], 2)) prints NaN.
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
export function f(xs: number[], out: number[], to: number): number {
  const runs: Runs = { open: xs };
  const kept: Runs | null = null;
  const passed = runs;
  let s = 0;
  /**
   * @invariant safeInteger(i) && safeInteger(to) && 0 <= i && to <= xs.length
   * @invariant kept === null || xs !== passed.open
   */
  for (let i = 0; i < to; i++) {
    step(passed, out);
    s += xs[i]!;
  }
  return s;
}
