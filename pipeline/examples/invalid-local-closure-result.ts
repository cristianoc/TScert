// A closure without a result annotation returns what its body returns, here
// `number | null`: a binding promising a number from its call is refused.
export function positive(x: number): number {
  const f = (y: number, keep: boolean) => (keep ? y : null);
  const z: number = f(x, true);
  return z;
}
