// A store separation read through a field that is not `@stable` is not kept
// across a write of that field: `box.open = xs` makes the field read `xs`'s
// array, so `xs !== box.open`, stated at entry, is false after it, and
// `step`'s region `box.open[*]` pops `xs`. Only a `@stable` field's location
// is kept across a field write (`stable-first`).
// Run under Node: `first([1], { open: [] }, [])` returns `undefined`.
type Box = { open: number[] };
type Runs = { /** @stable */ readonly open: number[] };

function step(
  runs: Runs,
  out: number[],
): Modifies<{ values: "any"; stores: "grow"; "runs.open[*]": "any" }, number> {
  runs.open.pop();
  out.push(1);
  return out.length;
}

/** @requires 0 < xs.length && xs !== box.open */
export function first(xs: number[], box: Box, out: number[]): number {
  box.open = xs;
  step(box, out);
  return xs[0]!;
}
