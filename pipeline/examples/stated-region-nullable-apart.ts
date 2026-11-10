// A region position holding a binding that may be `null`: `step`'s frame
// states the region `runs.open[*]`, and the loop passes `chosen`, which is
// `runs` or `null`. Where `chosen` is `null` the region selects no location;
// otherwise `xs !== chosen.open` places `xs` outside it. The loop invariant
// states the guarded separation `chosen === null || xs !== chosen.open`,
// which the declaration of `chosen` establishes from `xs !== runs.open`, the
// separation `region-alloc` gives the record's fresh array; it keeps
// `to <= xs.length` across the call.
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
  const runs: Runs = { open: [] };
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
