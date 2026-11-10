// A fresh field across an escape (FOOTPRINTS.md, "Fresh array storage"):
// `keep` stores the record in the caller's array under a frame changing
// every value, and the record's `@stable` field keeps the array the body
// allocated, so the later region on it rebases to none.
type Runs = { /** @stable */ readonly open: number[] };

function keep(holder: Runs[], runs: Runs): Modifies<{ values: "any"; stores: "grow" }, void> {
  holder.push(runs);
}

function step(runs: Runs, out: number[]): Modifies<{ values: "any"; stores: "grow"; "runs.open[*]": "any" }, number> {
  runs.open.pop();
  out.push(1);
  return out.length;
}

export function f(holder: Runs[], xs: number[]): Modifies<{ values: "any"; stores: "grow" }, number> {
  const runs: Runs = { open: [] };
  keep(holder, runs);
  return step(runs, xs);
}
