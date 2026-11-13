// A guard the parameter's type refutes: `p` is typed without `null`, so the
// precondition `p === null || 1 <= p.xs.length` states `1 <= p.xs.length`
// and the read of the first element is below the length (ARITHMETIC.md,
// "Guarded clauses", `guard-typed`).
type L = { /** @stable */ readonly xs: number[] };
/** @requires p === null || 1 <= p.xs.length && p.xs.length <= 1000 */
export function first(p: L): number {
  return p.xs[0]!;
}
