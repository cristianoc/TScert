// The central example's precondition refused where a caller cannot establish
// it (docs/drafts/stated-effects.md, §6.1): `measure` keeps
// `i < flags.length` across `readRuns`, whose frame changes the store
// `runs.openBrackets` holds, only where `flags !== runs.openBrackets`. Here
// the caller passes the same array as both, so the call is refused at its
// precondition. Run under Node, `aliased([1, 2, 3])` returns `NaN`: each
// splice shortens `flags`, and `flags[1]` reads `undefined`.
type Runs = { /** @stable */ readonly openBrackets: number[] };

function readRuns(runs: Runs): Modifies<{ values: "any"; "runs.openBrackets[*]": "any" }, void> {
  runs.openBrackets.splice(0, 1);
}

/** @requires flags !== runs.openBrackets */
function measure(flags: number[], runs: Runs): number {
  let sum = 0;
  for (let i = 0; i < flags.length; i++) { readRuns(runs); sum += flags[i]!; }
  return sum;
}

export function aliased(xs: number[]): number {
  return measure(xs, { openBrackets: xs });
}
