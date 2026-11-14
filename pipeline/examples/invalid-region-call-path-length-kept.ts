// The unsafe neighbour of `region-call-path-length-kept`: with no separation
// stated, `runs.open` may be `analysis.flags`, which the call shortens, so
// `to <= analysis.flags.length` does not survive it (run under Node with
// runs.open = analysis.flags = [1] and to = 1: `use` returns `undefined`, no
// number, and `f` NaN).
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

/** @requires safeInteger(to) && 0 <= to && to <= analysis.flags.length */
export function f(analysis: Analysis, runs: Runs, to: number): number {
  let s = 0;
  if (step(runs, 0)) s++;
  s += use(analysis.flags, to);
  return s;
}
