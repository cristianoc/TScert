// A fresh array stored in a record is apart from an array read from a
// parameter before it was made. The pass states that separation over the
// slot the read gave; the loops' written invariants state it over the path
// `analysis.flags`, unguarded and under a guard that the second record may
// be `null`. The edges into the loops entail each from the stated one
// through the read link (ARITHMETIC.md, "Store separation").
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
  const runs: Runs = { read: 0, open: [] }
  let s = 0
  /** @invariant safeInteger(mi) && safeInteger(to) && to <= flags.length && analysis.flags !== runs.open */
  for (let mi = 0; mi < to; mi++) {
    if (step(runs, mi)) s++
    s += use(analysis.flags, to)
  }
  return s
}

/** @requires safeInteger(to) && 0 <= to && to <= analysis.flags.length */
export function guarded(analysis: Analysis, to: number, share: boolean): number {
  const { flags } = analysis
  const runs: Runs = { read: 0, open: [] }
  const shared = share ? runs : null
  let s = 0
  /**
   * @invariant safeInteger(mi) && safeInteger(to) && to <= flags.length
   * @invariant shared === null || analysis.flags !== shared.open
   */
  for (let mi = 0; mi < to; mi++) {
    if (shared !== null && step(shared, mi)) s++
    s += use(analysis.flags, to)
  }
  return s
}
