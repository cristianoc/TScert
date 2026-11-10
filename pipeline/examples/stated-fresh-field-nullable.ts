// A fresh store through one `@stable` field at a nullable position
// (FOOTPRINTS.md, "Fresh array storage"): `maybe` is `runs` or `null`. The
// record's field is fresh, and `null` has no field, so the join keeps the
// fact; where `maybe` is `null` the region selects no store.
type Runs = { /** @stable */ readonly open: number[] };

function step(runs: Runs | null, out: number[]): Modifies<{ values: "any"; stores: "grow"; "runs.open[*]": "any" }, number> {
  if (runs !== null) runs.open.pop();
  out.push(1);
  return out.length;
}

export function f(xs: number[], c: boolean): Modifies<{ values: "any"; stores: "grow" }, number> {
  const runs: Runs = { open: [] };
  const maybe = c ? runs : null;
  return step(maybe, xs);
}
