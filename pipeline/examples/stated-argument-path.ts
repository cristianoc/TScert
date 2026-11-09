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

// A caller keeping a fact across the frame (§6.1): `i < flags.length` holds
// after `readRuns(runs)`, whose region is `runs.openBrackets`'s store, since
// the precondition states that array's store apart from `flags`'s
// (`flags !== runs.openBrackets`, ARITHMETIC.md, "Store separation"); the
// field is stable, so the separation holds at every call of the loop.
/** @requires flags !== runs.openBrackets */
export function measure(flags: number[], runs: Runs): number {
  let sum = 0;
  for (let i = 0; i < flags.length; i++) { readRuns(runs); sum += flags[i]!; }
  return sum;
}

// A caller establishing the precondition: the literal's fresh array is apart
// from every older array (`region-alloc`), read through the literal's field.
export function caller(flags: number[]): number {
  const runs: Runs = { openBrackets: [] };
  return measure(flags, runs);
}
