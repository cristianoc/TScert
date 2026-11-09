// A frame's store region allocated in the looping function
// (docs/drafts/stated-effects.md, §10): `runs.openBrackets` holds a fresh
// array, apart from `flags`'s store (`region-alloc`, read through the
// literal's field), and the field is stable, so `i < flags.length` is kept
// across every call of `readRuns`, whose frame changes that store alone.
type Runs = { /** @stable */ readonly openBrackets: number[] };

function readRuns(runs: Runs): Modifies<{ values: "any"; "runs.openBrackets[*]": "any" }, void> {
  runs.openBrackets.splice(0, 1);
}

export function measure(flags: number[]): number {
  const runs: Runs = { openBrackets: [] };
  let sum = 0;
  for (let i = 0; i < flags.length; i++) { readRuns(runs); sum += flags[i]!; }
  return sum;
}
