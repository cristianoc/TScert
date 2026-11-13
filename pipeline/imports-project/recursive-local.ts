// A function whose loop body declares a constant holding a recursive arrow:
// the arrow's read of its own constant is that binding, not a name of the
// module.
export function depth(ns: readonly number[]): number {
  let total = 0;
  for (const n of ns) {
    const go = (k: number): number => (k <= 0 ? 0 : 1 + go(k - 1));
    total += go(n);
  }
  return total;
}
