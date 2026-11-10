// A guarded separation of another binding than the region position's:
// `xs !== kept.open` guarded by `kept === null` says nothing of `passed`,
// which `step`'s region `runs.open[*]` reads. Where `kept` is `null` and
// `passed` is `runs`, whose `open` is `xs`, the call pops `xs`; the regional
// rule takes a guarded separation only where its guard reads the region
// position's own binding, so `to <= xs.length` is not kept and `xs[i]!` is
// refused.
// Run under Node: `f([1, 2], [], 2, false)` returns `NaN`, `xs[1]` read past
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
  const kept = use ? runs : null;
  const passed = use ? null : runs;
  let s = 0;
  /**
   * @invariant safeInteger(i) && safeInteger(to) && 0 <= i && to <= xs.length
   * @invariant kept === null || xs !== kept.open
   */
  for (let i = 0; i < to; i++) {
    step(passed, out);
    s += xs[i]!;
  }
  return s;
}
