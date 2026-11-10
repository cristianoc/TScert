// A fresh store through one `@stable` field (FOOTPRINTS.md, "Fresh array
// storage"): `f` allocates the record `runs` and the array its `@stable`
// field `open` holds, so the store `step`'s region `runs.open[*]` selects
// lies at or above the entry heap's length, and the region rebases to none.
// `f` changes the stores of its entry heap at most by `grow`.
type Runs = { /** @stable */ readonly open: number[] };

function step(runs: Runs, out: number[]): Modifies<{ values: "any"; stores: "grow"; "runs.open[*]": "any" }, number> {
  runs.open.pop();
  out.push(1);
  return out.length;
}

export function f(xs: number[]): Modifies<{ values: "any"; stores: "grow" }, number> {
  const runs: Runs = { open: [] };
  return step(runs, xs);
}
