// A valid guarded separation at entry names `chosen`. Assigning a record
// whose stable field aliases `xs` invalidates it before the regional call.
// Keeping the old separation would justify an unsafe read after the pop.
// Under Node, console.log(f([1], [], null)) prints undefined.
type Runs = { /** @stable */ readonly open: number[] };

function step(
  runs: Runs | null,
  out: number[],
): Modifies<{ values: "any"; stores: "grow"; "runs.open[*]": "any" }, number> {
  if (runs !== null) runs.open.pop();
  out.push(1);
  return out.length;
}

/**
 * @requires 0 < xs.length
 * @requires chosen === null || xs !== chosen.open
 */
export function f(xs: number[], out: number[], chosen: Runs | null): number {
  chosen = { open: xs };
  step(chosen, out);
  return xs[0]!;
}
