// A footprint checked by store regions (the regional walk after the
// footprint's own walk stops at `step`, whose region `runs.open[*]` lies
// outside `f`'s stated bound) refused at a loop head for a proposed fact
// the back edge does not establish (`runs.read`'s value, which `step`
// changes) leaves that fact out and runs again with the regional tables
// kept: only a refusal of the regional check itself drops them
// (`FilePlans.inferredNext`). The fresh field `runs.open` then rebases to
// no region at the call after the loop (pretext's `measureAnalysis`).
type Runs = { read: number; /** @stable */ readonly open: number[] };

function step(
  runs: Runs,
  at: number,
): Modifies<{ values: "any"; stores: "grow"; "runs.open[*]": "any" }, boolean> {
  runs.open.pop();
  runs.read = at;
  return runs.open.length > 0;
}

export function f(
  xs: number[],
): Modifies<{ values: "any"; stores: "grow" }, number> {
  const runs: Runs = { read: 0, open: [] };
  for (let i = 0; i < xs.length; i++) {
    xs[0] = i;
  }
  step(runs, 0);
  return 0;
}
