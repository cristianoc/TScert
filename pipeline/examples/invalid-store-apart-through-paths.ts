// The record holds the parameter's own array, not a fresh one: the written
// invariant `analysis.flags !== runs.open` does not hold on entry. Each
// round's call pops that array, and the read at `to - 1` reads past it:
// `use` returns `undefined` at `number`, and the sum is `NaN` (run under
// Node).
type Runs = { read: number, /** @stable */ readonly open: number[] }
type Analysis = { /** @stable */ readonly flags: number[] }

function step(runs: Runs, at: number): Modifies<{ values: "any"; stores: "grow"; "runs.open[*]": "any" }, boolean> {
  runs.open.pop()
  runs.read = at
  return runs.open.length > 0
}

/** @requires safeInteger(to) && 0 <= to && to <= xs.length */
function use(xs: number[], to: number): number {
  return to > 0 ? xs[to - 1]! : 0
}

/** @requires safeInteger(to) && 0 <= to && to <= analysis.flags.length */
export function unguarded(analysis: Analysis, to: number): number {
  const { flags } = analysis
  const runs: Runs = { read: 0, open: flags }
  let s = 0
  /** @invariant safeInteger(mi) && safeInteger(to) && to <= flags.length && analysis.flags !== runs.open */
  for (let mi = 0; mi < to; mi++) {
    if (step(runs, mi)) s++
    s += use(analysis.flags, to)
  }
  return s
}
