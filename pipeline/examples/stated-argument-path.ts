// A frame stating a store region read through a `@stable` field
// (docs/drafts/stated-effects.md, §6.1): `readRuns` splices the array its
// record's `openBrackets` holds, changing value locations and that store
// alone, so it states `values: "any"` and the region
// `"runs.openBrackets[*]": "any"`, every other store kept. The field is
// stable, so the array the body reads is the one the region names at entry.
type Runs = { /** @stable */ readonly openBrackets: number[] };

export function readRuns(runs: Runs): Modifies<{ values: "any"; "runs.openBrackets[*]": "any" }, void> {
  runs.openBrackets.splice(0, 1);
}

export function closeAll(runs: Runs): Modifies<{ values: "any"; "runs.openBrackets[*]": "any" }, number> {
  const open = runs.openBrackets;
  open.pop();
  return open.length;
}
