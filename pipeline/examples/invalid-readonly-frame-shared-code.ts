// Two exported walkers of one body (docs/drafts/framed-acceptance.md,
// "Milestone 2", "The crossings an entering step records"): walk declares
// xs read-only, walkAgain writable. Both enter the same realized code, so
// position 0 is not read-only in the meet of their declared shapes
// (`readOnlyPositions`): an entry records xs at the writable type, no
// crossing protects its spine, and xs.length === n across visit(i) is
// refused at both. A client calling walkAgain with an array it pops at
// the first visit makes the walker read past it (NaN under Node,
// tests/node-runs.mts).
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

export function walkAgain(xs: number[], visit: Visitor): number {
  const n = xs.length;
  let s = 0;
  /** @invariant safeInteger(i) && 0 <= i && safeInteger(n) && xs.length === n */
  for (let i = 0; i < n; i++) {
    visit(i);
    s += xs[i]!;
  }
  return s;
}
