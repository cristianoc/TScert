// A length read through a `@stable` path survives a call whose frame names a
// store region: the frame at the caller's slots respects the length's support
// (its store at `grow`, the stable field kept by its contract), the region's
// store placed apart from it by the stated separation `analysis.flags !==
// runs.open` (FOOTPRINTS.md, "Support and respect").
type Runs = { read: number, /** @stable */ readonly open: number[] };
type Analysis = { /** @stable */ readonly flags: number[] };

function step(runs: Runs, at: number): Modifies<{ values: "any"; stores: "grow"; "runs.open[*]": "any" }, boolean> {
  runs.open.pop();
  runs.read = at;
  return runs.open.length > 0;
}

/** @requires safeInteger(to) && 0 <= to && to <= xs.length */
function use(xs: number[], to: number): number {
  return to > 0 ? xs[to - 1]! : 0;
}

/** @requires safeInteger(to) && 0 <= to && to <= analysis.flags.length && analysis.flags !== runs.open */
export function f(analysis: Analysis, runs: Runs, to: number): number {
  let s = 0;
  if (step(runs, 0)) s++;
  s += use(analysis.flags, to);
  return s;
}
