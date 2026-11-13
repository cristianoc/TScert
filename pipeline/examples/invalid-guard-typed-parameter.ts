// The guard's parameter typed with `null`: the precondition holds of `p`
// null whatever `q` is, so the read of `q`'s first element is refused (run
// under Node: `first(null, { xs: [] })` returns `undefined` at `number`).
type L = { /** @stable */ readonly xs: number[] };
/** @requires p === null || 1 <= q.xs.length && q.xs.length <= 1000 */
export function first(p: L | null, q: L): number {
  return q.xs[0]!;
}
