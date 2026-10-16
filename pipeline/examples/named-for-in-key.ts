// A key a `for...in` loop yields is read after a call, which may have removed
// it: the read may miss, and the refusal names why.
export function sum(v: { [k: string]: number }, log: () => void): number {
  let total = 0;
  for (const k in v) {
    log();
    total = total + v[k]!;
  }
  return total;
}
