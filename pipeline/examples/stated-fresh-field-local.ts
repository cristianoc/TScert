// A fresh store through one `@stable` field, the array bound to a local
// first (FOOTPRINTS.md, "Fresh array storage"): the record's field is
// initialized from a slot holding a fresh value.
type Runs = { /** @stable */ readonly open: number[] };

function step(runs: Runs, out: number[]): Modifies<{ values: "any"; stores: "grow"; "runs.open[*]": "any" }, number> {
  runs.open.pop();
  out.push(1);
  return out.length;
}

export function f(xs: number[]): Modifies<{ values: "any"; stores: "grow" }, number> {
  const open: number[] = [];
  const runs: Runs = { open };
  return step(runs, xs);
}
