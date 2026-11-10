// A fresh field whose array's contents change through an alias
// (FOOTPRINTS.md, "Fresh array storage"): `fill` grows and writes the array
// through `open`, a read of the stable field; the field still holds the
// same array, whose store the body allocated.
type Runs = { /** @stable */ readonly open: number[] };

function fill(runs: Runs): Modifies<{ values: "any"; stores: "grow"; "runs.open[*]": "any" }, void> {
  const open = runs.open;
  open.push(1);
  if (0 < open.length) open[0] = 2;
}

function step(runs: Runs, out: number[]): Modifies<{ values: "any"; stores: "grow"; "runs.open[*]": "any" }, number> {
  runs.open.pop();
  out.push(1);
  return out.length;
}

export function f(xs: number[]): Modifies<{ values: "any"; stores: "grow" }, number> {
  const runs: Runs = { open: [] };
  fill(runs);
  return step(runs, xs);
}
