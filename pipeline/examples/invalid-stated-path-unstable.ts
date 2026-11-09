// A store region read through a field that is not `@stable`: the body can
// reassign the field, so the array it changes need not be the one the
// region names at entry. Refused at the unit's regional check. Run under
// Node, `swap(runs, xs)` with `runs = { openBrackets: [1] }` and
// `xs = [1, 2, 3]` pops `xs`, a store the frame keeps.
type Runs = { openBrackets: number[] };

export function swap(runs: Runs, xs: number[]): Modifies<{ values: "any"; "runs.openBrackets[*]": "any" }, void> {
  runs.openBrackets = xs;
  runs.openBrackets.pop();
}
