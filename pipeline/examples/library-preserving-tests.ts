// Callbacks calling `Number`'s tests, which convert nothing and write
// nothing: each call states heap preservation, so `map`'s result is dense.
export function integral(ns: number[]): boolean[] {
  return ns.map((n) => Number.isFinite(n) && Number.isInteger(n) && Number.isSafeInteger(n));
}
