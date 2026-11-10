// A guarded separation that is false: `chosen` is `runs` or `null`, and
// `runs.open` is `xs` itself, so `chosen === null || xs !== chosen.open`
// fails where `use` is true. The declaration of `chosen` establishes the
// guarded separation on its `null` arm alone, so the loop invariant stating
// it is refused at the loop's entry.
// Run under Node: `f([1, 2], [], 2, true)` returns `NaN`, `xs[1]` read past
// the popped array's end.
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
export function f(xs: number[], out: number[], to: number, use: boolean): number {
  const runs: Runs = { open: xs };
  const chosen = use ? runs : null;
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
