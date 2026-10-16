// TypeScript accepts this under --strict, but an absent numeric key reads
// undefined.
function assumePresent(x: { readonly [k: number]: string }, n: number): string {
  return x[n];
}
