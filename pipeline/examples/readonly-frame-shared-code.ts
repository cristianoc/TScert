// Two exported walkers of one body (docs/drafts/framed-acceptance.md,
// "Milestone 2", "The crossings an entering step records"): both declare
// xs read-only, so position 0 is read-only in the meet of the declared
// shapes of the functions sharing the realized code (`readOnlyPositions`),
// and the crossing of xs at either entry protects its spine.
// xs.length === n across visit(i) needs the spine, outside storage, read
// as protected: the visitor's stated effect lets every spine change.
type Visitor = (i: number) => Modifies<{ values: "keep"; spines: "any" }, void>;

export function walk(xs: readonly number[], visit: Visitor): number {
  const n = xs.length;
  let s = 0;
  /** @invariant safeInteger(i) && 0 <= i && safeInteger(n) && xs.length === n */
  for (let i = 0; i < n; i++) {
    visit(i);
    s += xs[i]!;
  }
  return s;
}

export function walkAgain(xs: readonly number[], visit: Visitor): number {
  const n = xs.length;
  let s = 0;
  /** @invariant safeInteger(i) && 0 <= i && safeInteger(n) && xs.length === n */
  for (let i = 0; i < n; i++) {
    visit(i);
    s += xs[i]!;
  }
  return s;
}
