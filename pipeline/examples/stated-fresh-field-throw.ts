// A fresh field across a caught throw (FOOTPRINTS.md, "Fresh array
// storage"): `fail` throws; the handler receives `runs` as the throwing
// node holds it, and the field keeps its array on the throw, so the region
// `step` states on it after the `try` rebases to none.
type Runs = { /** @stable */ readonly open: number[] };

function fail(): number {
  throw new Error("fail");
}

function step(runs: Runs, out: number[]): Modifies<{ values: "any"; stores: "grow"; "runs.open[*]": "any" }, number> {
  runs.open.pop();
  out.push(1);
  return out.length;
}

export function f(xs: number[]): Modifies<{ values: "any"; stores: "grow" }, number> {
  const runs: Runs = { open: [] };
  try {
    fail();
  } catch {
    runs.open.push(0);
  }
  return step(runs, xs);
}
