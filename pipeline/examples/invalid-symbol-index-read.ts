// TypeScript accepts this under --strict, but an absent symbol key reads
// undefined.
function assumePresent(
  t: { readonly [k: symbol]: boolean },
  s: symbol,
): boolean {
  return t[s];
}
