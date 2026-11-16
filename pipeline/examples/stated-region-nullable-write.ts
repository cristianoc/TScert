// The step-frame rule (FOOTPRINTS.md, "Argument-path spine regions") on a
// nullable record and an element write: at `runs = null` the path
// `runs.open` reads nothing and selects no spine; otherwise the body reads
// the stable field into `open` and writes an element of it, whose step
// frame (value-class locations and the written array's spine) rebases to
// the stated region.
type Runs = { /** @stable */ readonly open: number[] };

/** @requires safeInteger(k) */
export function mark(runs: Runs | null, k: number): Modifies<{ values: "any"; "runs.open[*]": "any" }, void> {
  if (runs !== null) {
    const open = runs.open;
    if (0 <= k && k < open.length) open[k] = 1;
  }
}
