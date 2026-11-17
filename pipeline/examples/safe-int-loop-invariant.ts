// A loop invariant over bindings declared `SafeInt` with no
// `safeInteger(...)`: the clause reader reads a binding at its written
// annotation, and each write of `j` is a step checked at the binding's
// contract, the sum `j - 1` refined by its facts.
export function countDown(xs: number[]): number {
  const count: SafeInt = xs.length;
  let s = 0;
  /** @invariant j + 1 <= count && count === xs.length */
  for (let j: SafeInt = count - 1; j >= 0; j--) s += xs[j]!;
  return s;
}
